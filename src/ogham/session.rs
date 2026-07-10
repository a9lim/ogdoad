//! Persistent evaluation session, worker, and source/statement depth guards.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalLine {
    pub canonical: String,
    pub value: Option<String>,
}

pub fn eval_to_string(world: &str, src: &str) -> OghamResult<String> {
    let mut session = OghamSession::new(world)?;
    let mut out = Vec::new();
    let mut pending = String::new();
    for line in src.lines() {
        let trimmed = line.trim();
        if pending.is_empty() && (trimmed.is_empty() || trimmed.starts_with("//")) {
            continue;
        }
        if pending.is_empty() {
            if let Some(rest) = trimmed.strip_prefix(":world ") {
                session.set_world(rest)?;
                continue;
            }
            if let Some(rest) = trimmed.strip_prefix(":fuel ") {
                let budget = rest
                    .trim()
                    .parse::<u128>()
                    .map_err(|_| parse_error("fuel budget must be a u128"))?;
                session.set_fuel_budget(budget);
                continue;
            }
            if let Some(rest) = trimmed.strip_prefix(":graph ") {
                let budget = rest
                    .trim()
                    .parse::<u128>()
                    .map_err(|_| parse_error("graph budget must be a u128"))?;
                session.set_graph_budget(budget);
                continue;
            }
        }
        if !pending.is_empty() {
            pending.push('\n');
        }
        pending.push_str(trimmed);
        if needs_continuation(&pending)? {
            continue;
        }
        if let Some(value) = session.eval_line(&pending)?.value {
            out.push(value);
        }
        pending.clear();
    }
    if !pending.is_empty() {
        if let Some(value) = session.eval_line(&pending)?.value {
            out.push(value);
        }
    }
    Ok(out.join("\n"))
}

enum WorkerReply<T> {
    Returned(T),
    Panicked(Box<dyn std::any::Any + Send + 'static>),
}

enum WorkerCommand {
    EvalLine {
        src: String,
        reply: mpsc::Sender<WorkerReply<OghamResult<EvalLine>>>,
    },
    SetWorld {
        decl: String,
        reply: mpsc::Sender<WorkerReply<OghamResult<()>>>,
    },
    SetFuelBudget {
        budget: u128,
        reply: mpsc::Sender<WorkerReply<()>>,
    },
    FuelBudget {
        reply: mpsc::Sender<WorkerReply<u128>>,
    },
    SetGraphBudget {
        budget: u128,
        reply: mpsc::Sender<WorkerReply<()>>,
    },
    GraphBudget {
        reply: mpsc::Sender<WorkerReply<u128>>,
    },
    WorldSummary {
        reply: mpsc::Sender<WorkerReply<String>>,
    },
    EnvSummary {
        reply: mpsc::Sender<WorkerReply<Vec<String>>>,
    },
    Shutdown,
}

pub struct OghamSession {
    worker: mpsc::Sender<WorkerCommand>,
    handle: Option<JoinHandle<()>>,
}

impl OghamSession {
    pub fn new(world_decl: &str) -> OghamResult<Self> {
        let (worker, commands) = mpsc::channel();
        let (initialized, initialization) = mpsc::channel();
        let decl = world_decl.to_string();
        let handle = std::thread::Builder::new()
            .name("ogham-eval".to_string())
            .stack_size(EVAL_STACK_BYTES)
            .spawn(move || {
                let world = catch_unwind(AssertUnwindSafe(|| World::from_decl(&decl)));
                let mut world = match world {
                    Ok(Ok(world)) => {
                        let _ = initialized.send(WorkerReply::Returned(Ok(())));
                        world
                    }
                    Ok(Err(err)) => {
                        let _ = initialized.send(WorkerReply::Returned(Err(err)));
                        return;
                    }
                    Err(payload) => {
                        let _ = initialized.send(WorkerReply::Panicked(payload));
                        return;
                    }
                };
                run_evaluation_worker(&mut world, commands);
            })
            .map_err(worker_spawn_error)?;
        match initialization
            .recv()
            .expect("ogham evaluation worker stopped before initialization")
        {
            WorkerReply::Returned(Ok(())) => Ok(OghamSession {
                worker,
                handle: Some(handle),
            }),
            WorkerReply::Returned(Err(err)) => {
                let _ = handle.join();
                Err(err)
            }
            WorkerReply::Panicked(payload) => {
                let _ = handle.join();
                resume_unwind(payload)
            }
        }
    }

    pub fn set_world(&mut self, world_decl: &str) -> OghamResult<()> {
        self.call_worker(|reply| WorkerCommand::SetWorld {
            decl: world_decl.to_string(),
            reply,
        })
    }

    pub fn eval_line(&mut self, src: &str) -> OghamResult<EvalLine> {
        self.call_worker(|reply| WorkerCommand::EvalLine {
            src: src.to_string(),
            reply,
        })
    }

    pub fn set_fuel_budget(&mut self, budget: u128) {
        self.call_worker(|reply| WorkerCommand::SetFuelBudget { budget, reply });
    }

    pub fn fuel_budget(&self) -> u128 {
        self.call_worker(|reply| WorkerCommand::FuelBudget { reply })
    }

    pub fn set_graph_budget(&mut self, budget: u128) {
        self.call_worker(|reply| WorkerCommand::SetGraphBudget { budget, reply });
    }

    pub fn graph_budget(&self) -> u128 {
        self.call_worker(|reply| WorkerCommand::GraphBudget { reply })
    }

    pub fn world_summary(&self) -> String {
        self.call_worker(|reply| WorkerCommand::WorldSummary { reply })
    }

    pub fn env_summary(&self) -> Vec<String> {
        self.call_worker(|reply| WorkerCommand::EnvSummary { reply })
    }

    fn call_worker<T>(
        &self,
        command: impl FnOnce(mpsc::Sender<WorkerReply<T>>) -> WorkerCommand,
    ) -> T {
        let (reply, response) = mpsc::channel();
        self.worker
            .send(command(reply))
            .expect("ogham evaluation worker stopped unexpectedly");
        match response
            .recv()
            .expect("ogham evaluation worker stopped before replying")
        {
            WorkerReply::Returned(value) => value,
            WorkerReply::Panicked(payload) => resume_unwind(payload),
        }
    }
}

impl Drop for OghamSession {
    fn drop(&mut self) {
        let _ = self.worker.send(WorkerCommand::Shutdown);
        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }
}

fn run_evaluation_worker(world: &mut World, commands: mpsc::Receiver<WorkerCommand>) {
    for command in commands {
        match command {
            WorkerCommand::EvalLine { src, reply } => {
                send_worker_reply(reply, || eval_line_in_world(world, &src));
            }
            WorkerCommand::SetWorld { decl, reply } => {
                send_worker_reply(reply, || {
                    *world = World::from_decl(&decl)?;
                    Ok(())
                });
            }
            WorkerCommand::SetFuelBudget { budget, reply } => {
                send_worker_reply(reply, || world.set_fuel_budget(budget));
            }
            WorkerCommand::FuelBudget { reply } => {
                send_worker_reply(reply, || world.fuel_budget());
            }
            WorkerCommand::SetGraphBudget { budget, reply } => {
                send_worker_reply(reply, || world.set_graph_budget(budget));
            }
            WorkerCommand::GraphBudget { reply } => {
                send_worker_reply(reply, || world.graph_budget());
            }
            WorkerCommand::WorldSummary { reply } => {
                send_worker_reply(reply, || world.summary());
            }
            WorkerCommand::EnvSummary { reply } => {
                send_worker_reply(reply, || world.env_summary());
            }
            WorkerCommand::Shutdown => break,
        }
    }
}

fn send_worker_reply<T>(reply: mpsc::Sender<WorkerReply<T>>, f: impl FnOnce() -> T) {
    let response = match catch_unwind(AssertUnwindSafe(f)) {
        Ok(value) => WorkerReply::Returned(value),
        Err(payload) => WorkerReply::Panicked(payload),
    };
    let _ = reply.send(response);
}

fn eval_line_in_world(world: &mut World, src: &str) -> OghamResult<EvalLine> {
    ensure_source_nesting_depth(src)?;
    if strip_comments(src)?.trim().is_empty() {
        return Ok(EvalLine {
            canonical: String::new(),
            value: None,
        });
    }
    let stmt = parse_statement(src)?;
    ensure_statement_depth(&stmt)?;
    let canonical = unparse_statement(&stmt);
    world.reset_fuel();
    let value = world.eval_statement(&stmt)?;
    Ok(EvalLine { canonical, value })
}

fn worker_spawn_error(err: std::io::Error) -> OghamError {
    OghamError::new(
        OghamErrorKind::Overflow,
        Span::point(0),
        format!("unable to allocate the {EVAL_STACK_BYTES}-byte evaluation stack: {err}"),
    )
}

pub(crate) fn ensure_source_nesting_depth(src: &str) -> OghamResult<()> {
    let src = strip_comments(src)?;
    let mut depth = 0_u128;
    for line in src.lines() {
        for ch in line.chars() {
            match ch {
                '(' | '[' | '{' => {
                    depth += 1;
                    if depth > AST_DEPTH_GUARD {
                        return Err(OghamError::new(
                            OghamErrorKind::Parse,
                            Span::point(0),
                            format!(
                                "source nesting exceeds the depth safety guard of {AST_DEPTH_GUARD} delimiters; the parser stack is bounded"
                            ),
                        ));
                    }
                }
                ')' | ']' | '}' => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    Ok(())
}

pub(crate) fn ensure_statement_depth(statement: &Statement) -> OghamResult<()> {
    enum SyntaxNode<'a> {
        Statement(&'a Statement),
        Expr(&'a Expr),
    }

    let mut pending = vec![(SyntaxNode::Statement(statement), 1_u128)];
    while let Some((node, depth)) = pending.pop() {
        if depth > AST_DEPTH_GUARD {
            return Err(OghamError::new(
                OghamErrorKind::Parse,
                Span::point(0),
                format!(
                    "statement syntax tree exceeds the depth safety guard of {AST_DEPTH_GUARD} nodes; recursive AST consumers require bounded input depth"
                ),
            ));
        }
        let child_depth = depth + 1;
        match node {
            SyntaxNode::Statement(Statement::Binding { expr, .. })
            | SyntaxNode::Statement(Statement::Expr(expr)) => {
                pending.push((SyntaxNode::Expr(expr), child_depth));
            }
            SyntaxNode::Statement(Statement::Seq { bindings, tail }) => {
                pending.push((SyntaxNode::Statement(tail), child_depth));
                pending.extend(
                    bindings
                        .iter()
                        .map(|binding| (SyntaxNode::Expr(&binding.expr), child_depth)),
                );
            }
            SyntaxNode::Expr(
                Expr::Int(_)
                | Expr::Bool(_)
                | Expr::Star(_)
                | Expr::Omega
                | Expr::Blade(_)
                | Expr::Up
                | Expr::Down
                | Expr::Dim
                | Expr::Ident(_),
            ) => {}
            SyntaxNode::Expr(Expr::Container(items)) => {
                pending.extend(
                    items
                        .iter()
                        .map(|item| (SyntaxNode::Expr(item), child_depth)),
                );
            }
            SyntaxNode::Expr(Expr::Apply { callee, args }) => {
                pending.push((SyntaxNode::Expr(callee), child_depth));
                pending.extend(args.iter().map(|arg| (SyntaxNode::Expr(arg), child_depth)));
            }
            SyntaxNode::Expr(Expr::Lambda { body, .. } | Expr::Index(body)) => {
                pending.push((SyntaxNode::Expr(body), child_depth));
            }
            SyntaxNode::Expr(Expr::Block { bindings, body }) => {
                pending.push((SyntaxNode::Expr(body), child_depth));
                pending.extend(
                    bindings
                        .iter()
                        .map(|binding| (SyntaxNode::Expr(&binding.expr), child_depth)),
                );
            }
            SyntaxNode::Expr(Expr::GameForm { left, right }) => {
                pending.extend(
                    left.iter()
                        .chain(right)
                        .map(|item| (SyntaxNode::Expr(item), child_depth)),
                );
            }
            SyntaxNode::Expr(Expr::Call { args, .. }) => {
                pending.extend(args.iter().map(|arg| (SyntaxNode::Expr(arg), child_depth)));
            }
            SyntaxNode::Expr(Expr::Unary { expr, .. }) => {
                pending.push((SyntaxNode::Expr(expr), child_depth));
            }
            SyntaxNode::Expr(Expr::Binary { lhs, rhs, .. })
            | SyntaxNode::Expr(Expr::Relation { lhs, rhs, .. }) => {
                pending.push((SyntaxNode::Expr(lhs), child_depth));
                pending.push((SyntaxNode::Expr(rhs), child_depth));
            }
            SyntaxNode::Expr(Expr::If {
                cond,
                then_expr,
                else_expr,
            }) => {
                pending.push((SyntaxNode::Expr(cond), child_depth));
                pending.push((SyntaxNode::Expr(then_expr), child_depth));
                pending.push((SyntaxNode::Expr(else_expr), child_depth));
            }
        }
    }
    Ok(())
}
