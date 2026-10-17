//! The public session handle: a persistent large-stack worker that owns a
//! single-threaded [`Session`].

use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::sync::mpsc;
use std::thread::JoinHandle;

use super::error::GrundyResult;
use super::session::Session;
use super::syntax::lex::needs_continuation;

/// The worker's stack: deep recursion in parsing, checking, and evaluation
/// is guarded by explicit limits well inside it.
pub const EVAL_STACK_BYTES: usize = 256 << 20;

type Job = Box<dyn FnOnce(&mut Session) + Send>;

/// Canonical source and optional rendered value for one input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalLine {
    /// The canonical rendering of the statement.
    pub canonical: String,
    /// The value's display, or `None` for a binding or declaration.
    pub value: Option<String>,
}

/// A persistent grundy session.
pub struct GrundySession {
    jobs: Option<mpsc::Sender<Job>>,
    handle: Option<JoinHandle<()>>,
}

impl Default for GrundySession {
    fn default() -> Self {
        GrundySession::new()
    }
}

impl GrundySession {
    /// Start a fresh session.
    pub fn new() -> GrundySession {
        let (jobs, receiver) = mpsc::channel::<Job>();
        let handle = std::thread::Builder::new()
            .name("grundy-eval".to_string())
            .stack_size(EVAL_STACK_BYTES)
            .spawn(move || {
                let mut session = Session::new();
                while let Ok(job) = receiver.recv() {
                    job(&mut session);
                }
            })
            .expect("spawn the grundy evaluation worker");
        GrundySession {
            jobs: Some(jobs),
            handle: Some(handle),
        }
    }

    fn run<R: Send + 'static>(&self, f: impl FnOnce(&mut Session) -> R + Send + 'static) -> R {
        let (reply, result) = mpsc::channel();
        let job: Job = Box::new(move |session| {
            let outcome = catch_unwind(AssertUnwindSafe(|| f(session)));
            let _ = reply.send(outcome);
        });
        self.jobs
            .as_ref()
            .expect("live worker")
            .send(job)
            .expect("the grundy worker is alive");
        match result.recv().expect("the grundy worker replies") {
            Ok(value) => value,
            Err(payload) => resume_unwind(payload),
        }
    }

    /// Evaluate one statement.
    pub fn eval_line(&mut self, src: &str) -> GrundyResult<EvalLine> {
        let src = src.to_string();
        self.run(move |session| {
            session.eval(&src).map(|out| EvalLine {
                canonical: out.echo,
                value: out.value,
            })
        })
    }

    /// The per-statement work budget.
    pub fn fuel(&self) -> u128 {
        self.run(|session| session.fuel)
    }

    /// Set the per-statement work budget.
    pub fn set_fuel(&mut self, fuel: u128) {
        self.run(move |session| session.fuel = fuel)
    }

    /// The node budget.
    pub fn graph_budget(&self) -> u128 {
        self.run(|session| session.graph_budget)
    }

    /// Set the node budget.
    pub fn set_graph_budget(&mut self, budget: u128) {
        self.run(move |session| session.graph_budget = budget)
    }

    /// The type of an expression, defaulted.
    pub fn type_of(&mut self, src: &str) -> GrundyResult<String> {
        let src = src.to_string();
        self.run(move |session| session.type_of(&src))
    }

    /// Every global binding with its type scheme.
    pub fn env(&self) -> Vec<(String, String)> {
        self.run(|session| session.env())
    }
}

impl Drop for GrundySession {
    fn drop(&mut self) {
        drop(self.jobs.take());
        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }
}

/// Evaluate a newline-delimited program, honoring `:fuel n` and `:graph n`
/// directives and multi-line continuation, and join the displayed values.
pub fn eval_to_string(src: &str) -> GrundyResult<String> {
    let mut session = GrundySession::new();
    let mut out = Vec::new();
    let mut pending = String::new();
    for line in src.lines() {
        let trimmed = line.trim();
        if pending.is_empty() {
            if trimmed.is_empty() || trimmed.starts_with("//") {
                continue;
            }
            if let Some(n) = trimmed
                .strip_prefix(":fuel ")
                .and_then(|n| n.trim().parse().ok())
            {
                session.set_fuel(n);
                continue;
            }
            if let Some(n) = trimmed
                .strip_prefix(":graph ")
                .and_then(|n| n.trim().parse().ok())
            {
                session.set_graph_budget(n);
                continue;
            }
        } else {
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
