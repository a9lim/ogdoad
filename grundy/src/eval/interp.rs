//! The evaluator over [`Core`]: an explicit-stack machine, so recursion
//! depth and expression nesting are counted on the heap rather than spent
//! from the host stack.

use std::collections::BTreeSet;
use std::rc::Rc;

use ogdoad::games::Game;
use ogdoad::scalar::{Omnific, Rational, Surreal};

use super::super::algebra::scalar::{AddOp, DivOp, MulOp, RemOp, ScalarV, SubOp};
use super::super::builtins::Builtin;
use super::super::core::{mentioned, visit_vars, CBind, CClause, CItem, CPat, Core, CtorRef, Lam};
use super::super::error::{err, GrundyError, GrundyErrorKind, GrundyResult, Span};
use super::super::games::form::{
    add_game_elements, build_game_form, form_outcome_cell, form_value_relation,
    game_element_regular_eq, materialize_regular_system, negate_game_element, FormV, SymbolicGame,
};
use super::super::games::game::{guard, GameV};
use super::super::syntax::ast::{BinaryOp, Mover, OutcomeCell, RelOp, StarIndex, UnaryOp};
use super::super::types::{DataRegistry, Ty, TyCon};
use super::super::worker::EVAL_STACK_BYTES;
use super::builtins::call_builtin;
use super::value::*;

/// Default work budget: closure calls plus produced list elements.
pub const DEFAULT_FUEL: u128 = 1 << 22;
/// Default node budget for every graph materialization and exploration.
pub const DEFAULT_GRAPH_BUDGET: u128 = 1 << 16;
/// The call-depth budget: closure frames live on the machine's own stack.
pub const DEPTH_LIMIT: usize = 4096;
/// How much of the worker's stack nested evaluations may use: the rest
/// covers the bounded host recursion inside one step (game algorithms, value
/// walks, one more nesting).
pub const NESTED_STACK_BYTES: usize = EVAL_STACK_BYTES / 2;

/// The evaluator.
pub struct Interp<'a> {
    /// Data declarations.
    pub data: &'a DataRegistry,
    /// Remaining fuel for the current statement.
    pub fuel: u128,
    /// The statement's fuel budget (for messages).
    pub fuel_budget: u128,
    /// The node budget.
    pub graph_budget: u128,
    depth: usize,
    /// The host stack position when the statement began.
    stack_base: usize,
}

impl super::super::games::game::Meter for Interp<'_> {
    fn remaining(&self) -> u128 {
        self.fuel
    }

    fn charge(&mut self, amount: u128) -> GrundyResult<()> {
        self.spend(amount)
    }
}

/// A place where evaluation is happening.
#[derive(Clone)]
pub struct Scope {
    /// Local bindings.
    pub env: Env,
    /// Captured globals.
    pub globals: Globals,
    /// The type instantiation.
    pub tenv: TEnv,
}

impl Scope {
    fn bind(&self, name: &str, value: Value) -> Scope {
        Scope {
            env: self.env.bind(name, value),
            globals: self.globals.clone(),
            tenv: self.tenv.clone(),
        }
    }

    fn lookup(&self, name: &str) -> Option<&Value> {
        self.env.get(name).or_else(|| self.globals.get(name))
    }
}

/// How many operator levels a quick expression may nest.
const QUICK_DEPTH: u8 = 4;

/// The machine's next move.
enum Step {
    /// Evaluate an expression.
    Eval(Rc<Core>, Scope),
    /// Apply a function; a call site's span labels the errors it raises.
    Apply(Value, Vec<Value>, Option<Span>),
    /// Hand a value to the top frame.
    Return(Value),
}

/// Work waiting on the machine's stack for one value. A frame holds the
/// expression it came from, so the parts still to run are reached from it.
enum Frame {
    /// A tuple's items so far.
    Tuple {
        node: Rc<Core>,
        done: Vec<Value>,
        scope: Scope,
    },
    /// A list's or brace form's items.
    Items(Box<Items>),
    /// A comprehension's output.
    Comp { out: Vec<Value> },
    /// A `for` clause's source list.
    CompSource {
        node: Rc<Core>,
        clause: usize,
        scope: Scope,
    },
    /// An `if` clause's guard.
    CompGuard {
        node: Rc<Core>,
        clause: usize,
        scope: Scope,
    },
    /// A `for` clause iterating its source.
    CompFor {
        node: Rc<Core>,
        clause: usize,
        items: Rc<Seq>,
        next: usize,
        scope: Scope,
    },
    /// A comprehension's head.
    CompHead,
    /// The first operand of a range, substitution, index, operator, or
    /// relation.
    Pair { node: Rc<Core>, scope: Scope },
    /// Its second operand.
    PairRhs { node: Rc<Core>, first: Value },
    /// A call's callee and arguments so far.
    Args {
        node: Rc<Core>,
        parts: Vec<Value>,
        scope: Scope,
    },
    /// A unary operand.
    Unary { node: Rc<Core> },
    /// The test of `and`, `or`, or `if`.
    Test { node: Rc<Core>, scope: Scope },
    /// A match's scrutinee.
    Match { node: Rc<Core>, scope: Scope },
    /// A `Let`'s value binding at `index`.
    Bind {
        node: Rc<Core>,
        index: usize,
        scope: Scope,
    },
    /// A closure's body, with the call site that labels its errors.
    Body { span: Option<Span> },
    /// `map`, `filter`, `fold`, `any`, or `all` walking its list.
    Each(Box<Each>),
}

impl Frame {
    /// The call site that labels errors raised beneath this frame.
    fn label(&self) -> Option<Span> {
        match self {
            Frame::Body { span } => *span,
            Frame::Each(each) => each.span,
            _ => None,
        }
    }
}

/// A list's or brace form's progress: the side, the item awaited, the
/// values so far, and a form's finished left side.
struct Items {
    node: Rc<Core>,
    right: bool,
    next: usize,
    done: Vec<Value>,
    left: Vec<Value>,
    scope: Scope,
}

/// A higher-order builtin's progress through its list.
struct Each {
    op: Builtin,
    f: Value,
    items: Rc<Seq>,
    next: usize,
    out: Vec<Value>,
    span: Option<Span>,
}

/// The comprehension driver's next move.
enum Visit {
    /// Enter a clause (the head past the last) under a scope.
    Enter(Rc<Core>, usize, Scope),
    /// Continue the innermost iteration.
    Next,
}

/// The items of a list, or of one side of a brace form.
fn side(node: &Core, right: bool) -> &[CItem] {
    match node {
        Core::List(items) => items,
        Core::Form(left, right_items, ..) => {
            if right {
                right_items
            } else {
                left
            }
        }
        _ => unreachable!("an items frame holds a list or form"),
    }
}

/// Whether an expression is quick: a leaf, or a tuple, operator, or
/// conditional over at most `depth` more levels of quick expressions. Quick
/// expressions run directly, in bounded host stack, without frames.
fn quick(node: &Core, depth: u8) -> bool {
    match node {
        Core::Int(..)
        | Core::Frac(..)
        | Core::Star(..)
        | Core::Omega(_)
        | Core::Up(..)
        | Core::Bool(_)
        | Core::Var(..)
        | Core::Builtin(..)
        | Core::Ctor(..)
        | Core::Lambda(_) => true,
        _ if depth == 0 => false,
        Core::Unary(_, a, _) => quick(a, depth - 1),
        Core::Range(a, b, ..)
        | Core::Subst(a, b, _)
        | Core::Index(a, b, _)
        | Core::Binary(_, a, b, _)
        | Core::Rel(_, a, b, _)
        | Core::And(a, b)
        | Core::Or(a, b) => quick(a, depth - 1) && quick(b, depth - 1),
        Core::If(c, a, b) => quick(c, depth - 1) && quick(a, depth - 1) && quick(b, depth - 1),
        Core::Tuple(items) => items.iter().all(|item| quick(item, depth - 1)),
        _ => false,
    }
}

/// Whether a negation is of `2¹²⁷`, the least Int's magnitude.
fn least_int(inner: &Core) -> bool {
    matches!(*inner, Core::Int(n, _) if n == 1 << 127)
}

/// The current host stack position.
fn stack_position() -> usize {
    let probe = 0_u8;
    std::hint::black_box(std::ptr::addr_of!(probe)) as usize
}

impl<'a> Interp<'a> {
    /// A fresh evaluator.
    pub fn new(data: &'a DataRegistry, fuel: u128, graph_budget: u128) -> Self {
        Interp {
            data,
            fuel,
            fuel_budget: fuel,
            graph_budget,
            depth: 0,
            stack_base: stack_position(),
        }
    }

    /// Spend fuel.
    pub fn spend(&mut self, amount: u128) -> GrundyResult<()> {
        if self.fuel < amount {
            self.fuel = 0;
            return Err(err(
                GrundyErrorKind::Fuel,
                format!(
                    "the statement exhausted its work budget of {}",
                    self.fuel_budget
                ),
            )
            .with_hint("raise it with `:fuel n`; budgets are never a value"));
        }
        self.fuel -= amount;
        Ok(())
    }

    /// Resolve a type through the runtime instantiation.
    pub fn resolve(&self, ty: &Ty, tenv: &TEnv) -> Ty {
        match ty {
            Ty::Var(v) => match tenv.get(v) {
                Some(bound) => self.resolve(bound, tenv),
                None => Ty::Var(*v),
            },
            Ty::Con(con, args) => Ty::Con(
                *con,
                args.iter().map(|arg| self.resolve(arg, tenv)).collect(),
            ),
            Ty::Fun(args, ret) => Ty::Fun(
                args.iter().map(|arg| self.resolve(arg, tenv)).collect(),
                Box::new(self.resolve(ret, tenv)),
            ),
        }
    }

    // ------------------------------------------------------------- statements

    /// Execute one binding, returning the names it binds.
    pub fn exec_bind(&mut self, bind: &CBind, scope: &Scope) -> GrundyResult<Vec<(String, Value)>> {
        match bind {
            CBind::Let {
                pat,
                expr,
                tparams,
                span,
            } => {
                if !tparams.is_empty() {
                    let CPat::Var(name) = pat else {
                        unreachable!("only variables generalize")
                    };
                    return Ok(vec![(name.clone(), {
                        let (env, depth) = capture(scope, &mentioned(expr))?;
                        Value::Generic(Rc::new(GenericV {
                            tparams: tparams.clone(),
                            body: PolyBody::Expr(expr.clone()),
                            env,
                            globals: scope.globals.clone(),
                            tenv: scope.tenv.clone(),
                            depth,
                        }))
                    })]);
                }
                let value = self.eval(expr, scope)?;
                self.bind_pattern(pat, *span, &value)
            }
            CBind::RecFns {
                names,
                lams,
                tparams,
            } => {
                let (env, depth) = capture(scope, &group_mentions(names, lams))?;
                if !tparams.is_empty() {
                    return Ok(names
                        .iter()
                        .enumerate()
                        .map(|(index, name)| {
                            (
                                name.clone(),
                                Value::Generic(Rc::new(GenericV {
                                    tparams: tparams.clone(),
                                    body: PolyBody::Group {
                                        names: names.clone(),
                                        lams: lams.clone(),
                                        index,
                                    },
                                    env: env.clone(),
                                    globals: scope.globals.clone(),
                                    tenv: scope.tenv.clone(),
                                    depth,
                                })),
                            )
                        })
                        .collect());
                }
                let group = Rc::new(RecGroup {
                    names: names.clone(),
                    lams: lams.clone(),
                    env,
                    globals: scope.globals.clone(),
                    tenv: scope.tenv.clone(),
                    depth,
                });
                Ok(group_members(&group))
            }
            CBind::RecForms {
                names,
                exprs,
                spans,
            } => self.exec_forms(names, exprs, spans, scope),
        }
    }

    /// Match a binding's pattern against its value.
    fn bind_pattern(
        &self,
        pat: &CPat,
        span: Span,
        value: &Value,
    ) -> GrundyResult<Vec<(String, Value)>> {
        let mut out = Vec::new();
        if !self.match_pat(pat, value, &mut out) {
            return Err(GrundyError::new(
                GrundyErrorKind::Pattern,
                span,
                "the binding pattern does not match the value",
            ));
        }
        Ok(out)
    }

    fn exec_forms(
        &mut self,
        names: &[String],
        exprs: &[Rc<Core>],
        spans: &[Span],
        scope: &Scope,
    ) -> GrundyResult<Vec<(String, Value)>> {
        let system: BTreeSet<&str> = names.iter().map(String::as_str).collect();
        let mut roots = Vec::new();
        for (expr, span) in exprs.iter().zip(spans) {
            let root = self
                .reduce_form(expr, names, &system, scope)
                .map_err(|e| e.at(*span))?;
            if let SymbolicGame::SystemRef(target) = root {
                return Err(unfounded(&names[roots.len()], &names[target]).at(*span));
            }
            roots.push(root);
        }
        let values = materialize_regular_system(names, roots, self.graph_budget)?;
        Ok(names
            .iter()
            .cloned()
            .zip(values.into_iter().map(|v| Value::Form(FormV(v))))
            .collect())
    }

    /// Reduce a game equation's right-hand side with the system's names
    /// symbolic. System names are guarded only when they sit directly as
    /// brace options (possibly inside nested braces). Its operands are
    /// nested evaluations.
    fn reduce_form(
        &mut self,
        expr: &Rc<Core>,
        names: &[String],
        system: &BTreeSet<&str>,
        scope: &Scope,
    ) -> GrundyResult<SymbolicGame> {
        match &**expr {
            Core::Var(name, _) if system.contains(name.as_str()) => {
                // A bare root reference is rejected by the caller; inside a
                // brace it is a guarded edge.
                let index = names.iter().position(|n| n == name).expect("system name");
                Ok(SymbolicGame::SystemRef(index))
            }
            Core::Form(left, right, _, _) => {
                let mut side = |items: &[CItem]| -> GrundyResult<Vec<SymbolicGame>> {
                    let mut out = Vec::new();
                    for item in items {
                        match item {
                            CItem::One(core) => {
                                out.push(self.reduce_form(core, names, system, scope)?)
                            }
                            CItem::Splice(core) => {
                                if mentions(core, system) {
                                    return Err(err(
                                        GrundyErrorKind::Unfounded,
                                        "a system name inside a splice is unguarded",
                                    )
                                    .with_hint("system names sit directly as brace options"));
                                }
                                for value in self.eval(core, scope)?.as_list().iter() {
                                    out.push(SymbolicGame::Value(as_form(value).0.clone()));
                                }
                            }
                        }
                    }
                    Ok(out)
                };
                let left = side(left)?;
                let right = side(right)?;
                Ok(SymbolicGame::Form { left, right })
            }
            other => {
                if mentions(other, system) {
                    return Err(err(
                        GrundyErrorKind::Unfounded,
                        "a system name is used outside a brace constructor",
                    )
                    .with_hint("guard it: `g =: {g |}`; other operators need the finished value"));
                }
                let value = self.eval(expr, scope)?;
                Ok(SymbolicGame::Value(as_form(&value).0.clone()))
            }
        }
    }

    // ---------------------------------------------------------- the machine

    /// Evaluate an expression.
    pub fn eval(&mut self, core: &Rc<Core>, scope: &Scope) -> GrundyResult<Value> {
        self.run(Step::Eval(core.clone(), scope.clone()))
    }

    /// Apply a function value.
    pub fn apply(&mut self, callee: &Value, args: Vec<Value>) -> GrundyResult<Value> {
        self.run(Step::Apply(callee.clone(), args, None))
    }

    /// Run the machine to a value. Its pending work lives in `stack`, not on
    /// the host stack: calls and nesting cost heap frames. Only an
    /// evaluation started from inside another (a ruleset's move function, a
    /// game equation's operand) nests host frames, and that is guarded by
    /// measured host stack.
    fn run(&mut self, mut step: Step) -> GrundyResult<Value> {
        self.guard_host_stack()?;
        let depth = self.depth;
        let mut stack = Vec::new();
        loop {
            let next = match step {
                Step::Eval(node, scope) => self.start(node, scope, &mut stack),
                Step::Apply(callee, args, span) => self.call(callee, args, span, &mut stack),
                Step::Return(value) if stack.is_empty() => return Ok(value),
                Step::Return(value) => self.resume(value, &mut stack),
            };
            match next {
                Ok(next) => step = next,
                Err(mut error) => {
                    // The innermost call site that has not yet labeled the
                    // error does.
                    for frame in stack.iter().rev() {
                        if let Some(span) = frame.label() {
                            error = error.at(span);
                        }
                    }
                    self.depth = depth;
                    return Err(error);
                }
            }
        }
    }

    /// Refuse a nested evaluation once the host stack it would grow is used
    /// past [`NESTED_STACK_BYTES`].
    fn guard_host_stack(&self) -> GrundyResult<()> {
        let used = self.stack_base.abs_diff(stack_position());
        if used > NESTED_STACK_BYTES {
            return Err(err(
                GrundyErrorKind::StackDepth,
                format!(
                    "nested evaluation exceeds the host stack guard of {} MiB",
                    NESTED_STACK_BYTES >> 20
                ),
            )
            .with_hint(
                "a ruleset's move function or a game equation's operand re-enters the evaluator on the host stack",
            ));
        }
        Ok(())
    }

    /// A quick expression's value, or `None` when it needs the machine.
    fn inline(&mut self, node: &Core, scope: &Scope) -> Option<GrundyResult<Value>> {
        if let Core::Var(name, span) = node {
            return Some(lookup(scope, name, *span));
        }
        quick(node, QUICK_DEPTH).then(|| self.quick_eval(node, scope))
    }

    /// Evaluate a quick expression directly.
    fn quick_eval(&mut self, node: &Core, scope: &Scope) -> GrundyResult<Value> {
        match node {
            Core::Unary(UnaryOp::Neg, inner, span) if least_int(inner) => {
                // `-2¹²⁷` is representable though `2¹²⁷` is not: read it as
                // `-(2¹²⁷ - 1) - 1`, so the least Int displays and re-reads.
                let Core::Int(n, ty) = &**inner else {
                    unreachable!("matched a literal")
                };
                let ty = self.resolve(ty, &scope.tenv);
                let magnitude = self.int_literal(n - 1, &ty)?;
                let negated = self.unary(UnaryOp::Neg, magnitude)?;
                let one = self.int_literal(1, &ty)?;
                self.binary(BinaryOp::Sub, negated, one)
                    .map_err(|e| e.at(*span))
            }
            Core::Unary(op, inner, span) => {
                let value = self.quick_eval(inner, scope)?;
                self.unary(*op, value).map_err(|e| e.at(*span))
            }
            Core::Range(a, b, ..)
            | Core::Subst(a, b, _)
            | Core::Index(a, b, _)
            | Core::Binary(_, a, b, _)
            | Core::Rel(_, a, b, _) => {
                let first = self.quick_eval(a, scope)?;
                let second = self.quick_eval(b, scope)?;
                self.pair(node, first, second)
            }
            Core::Tuple(items) => Ok(Value::tuple(
                items
                    .iter()
                    .map(|item| self.quick_eval(item, scope))
                    .collect::<GrundyResult<_>>()?,
            )),
            Core::And(test, _) | Core::Or(test, _) | Core::If(test, ..) => {
                let test = self.quick_eval(test, scope)?.as_bool();
                match branch(node, test) {
                    Ok(chosen) => self.quick_eval(chosen, scope),
                    Err(value) => Ok(Value::Bool(value)),
                }
            }
            leaf => self.leaf(leaf, scope),
        }
    }

    /// Evaluate a leaf: a literal, variable, builtin, constructor, or lambda.
    fn leaf(&mut self, node: &Core, scope: &Scope) -> GrundyResult<Value> {
        match node {
            Core::Int(n, ty) => {
                let ty = self.resolve(ty, &scope.tenv);
                self.int_literal(*n, &ty)
            }
            Core::Frac(num, den, ty) => {
                let ty = self.resolve(ty, &scope.tenv);
                self.frac_literal(*num, *den, &ty)
            }
            Core::Star(index, ty) => {
                let ty = self.resolve(ty, &scope.tenv);
                self.star_literal(index, &ty)
            }
            Core::Omega(ty) => match self.resolve(ty, &scope.tenv) {
                ty @ Ty::Con(TyCon::Mv, _) => super::super::algebra::omega_literal(&ty),
                Ty::Con(con, _) => Ok(Value::Scalar(ScalarV::omega(con)?)),
                other => Err(unresolved(&other)),
            },
            Core::Up(down, ty) => match self.resolve(ty, &scope.tenv) {
                Ty::Con(TyCon::Game, _) => Ok(Value::Game(GameV::up(*down, self)?)),
                Ty::Con(TyCon::Form, _) => {
                    let up = Game::up();
                    Ok(Value::Form(FormV::finite(if *down {
                        up.neg()
                    } else {
                        up
                    })))
                }
                other => Err(unresolved(&other)),
            },
            Core::Bool(b) => Ok(Value::Bool(*b)),
            Core::Var(name, span) => lookup(scope, name, *span),
            Core::Builtin(builtin, tys) => Ok(Value::Builtin(
                *builtin,
                tys.iter()
                    .map(|ty| self.resolve(ty, &scope.tenv))
                    .collect::<Vec<_>>()
                    .into(),
            )),
            Core::Ctor(ctor, arity) => Ok(if *arity == 0 {
                construct(ctor, Vec::new())?
            } else {
                Value::CtorFn(ctor.clone())
            }),
            Core::Lambda(lam) => {
                let (env, depth) = capture(scope, &lam.mentions)?;
                Ok(Value::Closure(Rc::new(Closure {
                    lam: lam.clone(),
                    env,
                    globals: scope.globals.clone(),
                    tenv: scope.tenv.clone(),
                    rec: None,
                    depth,
                })))
            }
            _ => unreachable!("not a leaf"),
        }
    }

    /// Begin evaluating an expression.
    fn start(
        &mut self,
        node: Rc<Core>,
        scope: Scope,
        stack: &mut Vec<Frame>,
    ) -> GrundyResult<Step> {
        // Each arm runs its quick parts directly and leaves a frame only for
        // a part that needs the machine.
        match &*node {
            Core::Inst(name, tys, span) => {
                let value = lookup(&scope, name, *span)?;
                let Value::Generic(generic) = value else {
                    return Ok(Step::Return(value));
                };
                // Instantiation re-runs the right-hand side at the types.
                let mut tenv = (*generic.tenv).clone();
                for (var, ty) in generic.tparams.iter().zip(tys) {
                    tenv.insert(*var, self.resolve(ty, &scope.tenv));
                }
                let tenv: TEnv = Rc::new(tenv);
                Ok(match &generic.body {
                    PolyBody::Expr(core) => Step::Eval(
                        core.clone(),
                        Scope {
                            env: generic.env.clone(),
                            globals: generic.globals.clone(),
                            tenv,
                        },
                    ),
                    PolyBody::Group { names, lams, index } => {
                        let group = Rc::new(RecGroup {
                            names: names.clone(),
                            lams: lams.clone(),
                            env: generic.env.clone(),
                            globals: generic.globals.clone(),
                            tenv,
                            depth: generic.depth,
                        });
                        Step::Return(group_members(&group).swap_remove(*index).1)
                    }
                })
            }
            Core::Tuple(_) => self.advance_tuple(node.clone(), Vec::new(), scope, stack),
            Core::List(_) | Core::Form(..) => self.advance_items(
                Box::new(Items {
                    node: node.clone(),
                    right: false,
                    next: 0,
                    done: Vec::new(),
                    left: Vec::new(),
                    scope,
                }),
                stack,
            ),
            Core::Comp(..) => {
                stack.push(Frame::Comp { out: Vec::new() });
                self.comprehend(Visit::Enter(node.clone(), 0, scope), stack)
            }
            Core::Range(first, ..)
            | Core::Subst(first, ..)
            | Core::Index(first, ..)
            | Core::Binary(_, first, ..)
            | Core::Rel(_, first, ..) => match self.inline(first, &scope) {
                Some(value) => self.second(node.clone(), value?, scope, stack),
                None => {
                    let first = first.clone();
                    stack.push(Frame::Pair {
                        node: node.clone(),
                        scope: scope.clone(),
                    });
                    Ok(Step::Eval(first, scope))
                }
            },
            Core::Call(..) => self.advance_args(node.clone(), Vec::new(), scope, stack),
            Core::Unary(..) if quick(&node, QUICK_DEPTH) => {
                self.quick_eval(&node, &scope).map(Step::Return)
            }
            Core::Unary(_, inner, _) => {
                let inner = inner.clone();
                stack.push(Frame::Unary { node: node.clone() });
                Ok(Step::Eval(inner, scope))
            }
            Core::And(test, _) | Core::Or(test, _) | Core::If(test, ..) => {
                match self.inline(test, &scope) {
                    Some(value) => Ok(choose(&node, value?.as_bool(), scope)),
                    None => {
                        let test = test.clone();
                        stack.push(Frame::Test {
                            node: node.clone(),
                            scope: scope.clone(),
                        });
                        Ok(Step::Eval(test, scope))
                    }
                }
            }
            Core::Match(scrutinee, ..) => match self.inline(scrutinee, &scope) {
                Some(value) => self.arm(&node, &value?, scope),
                None => {
                    let scrutinee = scrutinee.clone();
                    stack.push(Frame::Match {
                        node: node.clone(),
                        scope: scope.clone(),
                    });
                    Ok(Step::Eval(scrutinee, scope))
                }
            },
            Core::Let(..) => self.bind_from(node.clone(), 0, scope, stack),
            Core::Gen(name, ty, body) => {
                let ty = self.resolve(ty, &scope.tenv);
                let generator = super::super::algebra::generator(&ty)?;
                Ok(Step::Eval(body.clone(), scope.bind(name, generator)))
            }
            leaf => self.leaf(leaf, &scope).map(Step::Return),
        }
    }

    /// Hand a value to the top frame.
    fn resume(&mut self, value: Value, stack: &mut Vec<Frame>) -> GrundyResult<Step> {
        // A higher-order builtin stays on the stack while it works, so its
        // call site labels what it raises.
        if let Some(Frame::Each(_)) = stack.last() {
            return self.each(Some(value), stack);
        }
        match stack.pop().expect("a waiting frame") {
            Frame::Tuple {
                node,
                mut done,
                scope,
            } => {
                done.push(value);
                self.advance_tuple(node, done, scope, stack)
            }
            Frame::Items(mut items) => {
                match &side(&items.node, items.right)[items.next] {
                    CItem::One(_) => items.done.push(value),
                    CItem::Splice(_) => items.done.extend(value.as_list().iter().cloned()),
                }
                items.next += 1;
                self.advance_items(items, stack)
            }
            Frame::Comp { .. } | Frame::CompFor { .. } | Frame::Each(_) => {
                unreachable!("these frames are resumed in place")
            }
            Frame::CompSource {
                node,
                clause,
                scope,
            } => {
                stack.push(Frame::CompFor {
                    node,
                    clause,
                    items: value.into_list(),
                    next: 0,
                    scope,
                });
                self.comprehend(Visit::Next, stack)
            }
            Frame::CompGuard {
                node,
                clause,
                scope,
            } => {
                let visit = if value.as_bool() {
                    Visit::Enter(node, clause + 1, scope)
                } else {
                    Visit::Next
                };
                self.comprehend(visit, stack)
            }
            Frame::CompHead => {
                comprehension_output(stack).push(value);
                self.comprehend(Visit::Next, stack)
            }
            Frame::Pair { node, scope } => self.second(node, value, scope, stack),
            Frame::PairRhs { node, first } => self.pair(&node, first, value).map(Step::Return),
            Frame::Args {
                node,
                mut parts,
                scope,
            } => {
                parts.push(value);
                self.advance_args(node, parts, scope, stack)
            }
            Frame::Unary { node } => {
                let Core::Unary(op, _, span) = &*node else {
                    unreachable!("a unary frame holds a unary node")
                };
                self.unary(*op, value)
                    .map(Step::Return)
                    .map_err(|e| e.at(*span))
            }
            Frame::Test { node, scope } => Ok(choose(&node, value.as_bool(), scope)),
            Frame::Match { node, scope } => self.arm(&node, &value, scope),
            Frame::Bind {
                node,
                index,
                mut scope,
            } => {
                let Core::Let(binds, _) = &*node else {
                    unreachable!("a binding frame holds a let")
                };
                let CBind::Let { pat, span, .. } = &binds[index] else {
                    unreachable!("only value bindings wait for a value")
                };
                for (name, value) in self.bind_pattern(pat, *span, &value)? {
                    scope = scope.bind(&name, value);
                }
                self.bind_from(node, index + 1, scope, stack)
            }
            Frame::Body { .. } => {
                self.depth -= 1;
                Ok(Step::Return(value))
            }
        }
    }

    /// Apply a function value.
    fn call(
        &mut self,
        callee: Value,
        args: Vec<Value>,
        span: Option<Span>,
        stack: &mut Vec<Frame>,
    ) -> GrundyResult<Step> {
        let label = |error: GrundyError| match span {
            Some(span) => error.at(span),
            None => error,
        };
        match callee {
            Value::Closure(closure) => {
                self.spend(1).map_err(label)?;
                if self.depth >= DEPTH_LIMIT {
                    return Err(label(
                        err(
                            GrundyErrorKind::StackDepth,
                            format!(
                                "call depth exceeds its limit of {DEPTH_LIMIT} frames ({} fuel left)",
                                self.fuel
                            ),
                        )
                        .with_hint("call depth is a budget of its own, distinct from fuel"),
                    ));
                }
                let mut env = closure.env.clone();
                if let Some((group, _)) = &closure.rec {
                    for (name, value) in group_members(group) {
                        env = env.bind(name, value);
                    }
                }
                let lam = &closure.lam;
                for (pat, arg) in lam.params.iter().zip(args) {
                    let mut bound = Vec::new();
                    if !self.match_pat(pat, &arg, &mut bound) {
                        return Err(label(err(
                            GrundyErrorKind::Pattern,
                            "the argument does not match the parameter pattern",
                        )));
                    }
                    for (name, value) in bound {
                        env = env.bind(name, value);
                    }
                }
                let scope = Scope {
                    env,
                    globals: closure.globals.clone(),
                    tenv: closure.tenv.clone(),
                };
                stack.push(Frame::Body { span });
                self.depth += 1;
                Ok(Step::Eval(lam.body.clone(), scope))
            }
            Value::Builtin(
                op @ (Builtin::Map | Builtin::Filter | Builtin::Fold | Builtin::Any | Builtin::All),
                _,
            ) => {
                let mut args = args.into_iter();
                let f = args.next().expect("a function argument");
                let init = if op == Builtin::Fold {
                    args.next()
                } else {
                    None
                };
                let items = args.next().expect("a list argument").into_list();
                stack.push(Frame::Each(Box::new(Each {
                    op,
                    f,
                    items,
                    next: 0,
                    out: Vec::new(),
                    span,
                })));
                self.each(init, stack)
            }
            Value::Builtin(builtin, tys) => call_builtin(self, builtin, &tys, args)
                .map(Step::Return)
                .map_err(label),
            Value::CtorFn(ctor) => construct(&ctor, args).map(Step::Return).map_err(label),
            other => Err(label(internal(format!("applied a {}", other.kind_name())))),
        }
    }

    /// Step a higher-order builtin on top of the stack, given the value of
    /// its last application (a fold's accumulator to start).
    fn each(&mut self, value: Option<Value>, stack: &mut Vec<Frame>) -> GrundyResult<Step> {
        let Some(Frame::Each(each)) = stack.last_mut() else {
            unreachable!("a higher-order builtin's frame")
        };
        let mut acc = None;
        if let Some(value) = value {
            match each.op {
                Builtin::Map => each.out.push(value),
                Builtin::Filter => {
                    if value.as_bool() {
                        self.spend(1)?;
                        each.out.push(each.items[each.next - 1].clone());
                    }
                }
                Builtin::Fold => acc = Some(value),
                op => {
                    let want = op == Builtin::Any;
                    if value.as_bool() == want {
                        stack.pop();
                        return Ok(Step::Return(Value::Bool(want)));
                    }
                }
            }
        }
        if let Some(item) = each.items.get(each.next).cloned() {
            each.next += 1;
            if each.op == Builtin::Map {
                self.spend(1)?;
            }
            let args = match acc {
                Some(acc) => vec![acc, item],
                None => vec![item],
            };
            return Ok(Step::Apply(each.f.clone(), args, None));
        }
        let Some(Frame::Each(each)) = stack.pop() else {
            unreachable!("a higher-order builtin's frame")
        };
        Ok(Step::Return(match each.op {
            Builtin::Map | Builtin::Filter => Value::list(each.out),
            Builtin::Fold => acc.expect("a fold carries its accumulator"),
            op => Value::Bool(op == Builtin::All),
        }))
    }

    /// Run a tuple's remaining items.
    fn advance_tuple(
        &mut self,
        node: Rc<Core>,
        mut done: Vec<Value>,
        scope: Scope,
        stack: &mut Vec<Frame>,
    ) -> GrundyResult<Step> {
        let Core::Tuple(items) = &*node else {
            unreachable!("a tuple frame holds a tuple")
        };
        while let Some(item) = items.get(done.len()) {
            match self.inline(item, &scope) {
                Some(value) => done.push(value?),
                None => {
                    let item = item.clone();
                    stack.push(Frame::Tuple {
                        node: node.clone(),
                        done,
                        scope: scope.clone(),
                    });
                    return Ok(Step::Eval(item, scope));
                }
            }
        }
        Ok(Step::Return(Value::tuple(done)))
    }

    /// Run a call's remaining callee and arguments, then apply.
    fn advance_args(
        &mut self,
        node: Rc<Core>,
        mut parts: Vec<Value>,
        scope: Scope,
        stack: &mut Vec<Frame>,
    ) -> GrundyResult<Step> {
        let Core::Call(callee, args, span) = &*node else {
            unreachable!("an argument frame holds a call")
        };
        while let Some(part) = match parts.len() {
            0 => Some(callee),
            n => args.get(n - 1),
        } {
            match self.inline(part, &scope) {
                Some(value) => parts.push(value?),
                None => {
                    let part = part.clone();
                    stack.push(Frame::Args {
                        node: node.clone(),
                        parts,
                        scope: scope.clone(),
                    });
                    return Ok(Step::Eval(part, scope));
                }
            }
        }
        let callee = parts.remove(0);
        Ok(Step::Apply(callee, parts, Some(*span)))
    }

    /// Run a list's or brace form's remaining items, then build it.
    fn advance_items(
        &mut self,
        mut items: Box<Items>,
        stack: &mut Vec<Frame>,
    ) -> GrundyResult<Step> {
        loop {
            while let Some(item) = side(&items.node, items.right).get(items.next) {
                let (CItem::One(core) | CItem::Splice(core)) = item;
                let Some(value) = self.inline(core, &items.scope) else {
                    let (core, scope) = (core.clone(), items.scope.clone());
                    stack.push(Frame::Items(items));
                    return Ok(Step::Eval(core, scope));
                };
                let value = value?;
                match item {
                    CItem::One(_) => items.done.push(value),
                    CItem::Splice(_) => items.done.extend(value.as_list().iter().cloned()),
                }
                items.next += 1;
            }
            match &*items.node {
                Core::List(_) => return Ok(Step::Return(Value::list(items.done))),
                Core::Form(..) if !items.right => {
                    items.left = std::mem::take(&mut items.done);
                    items.right = true;
                    items.next = 0;
                }
                Core::Form(_, _, ty, span) => {
                    let ty = self.resolve(ty, &items.scope.tenv);
                    return self
                        .form(&items.left, &items.done, &ty, *span)
                        .map(Step::Return);
                }
                _ => unreachable!("an items frame holds a list or form"),
            }
        }
    }

    /// Build a brace form from its evaluated options.
    fn form(
        &mut self,
        left: &[Value],
        right: &[Value],
        ty: &Ty,
        span: Span,
    ) -> GrundyResult<Value> {
        match ty {
            Ty::Con(TyCon::Game, _) => {
                let games = |values: &[Value]| values.iter().map(as_game).collect::<Vec<_>>();
                Ok(Value::Game(GameV::form(&games(left), &games(right), self)?))
            }
            Ty::Con(TyCon::Form, _) => {
                let forms = |values: &[Value]| {
                    values
                        .iter()
                        .map(|value| as_form(value).0.clone())
                        .collect()
                };
                Ok(Value::Form(FormV(
                    build_game_form(forms(left), forms(right), self.graph_budget)
                        .map_err(|e| e.at(span))?,
                )))
            }
            other => Err(unresolved(other)),
        }
    }

    /// Drive the comprehension on top of the stack until it needs the
    /// machine or finishes.
    fn comprehend(&mut self, mut visit: Visit, stack: &mut Vec<Frame>) -> GrundyResult<Step> {
        loop {
            visit = match visit {
                Visit::Enter(node, clause, scope) => {
                    let Core::Comp(head, clauses) = &*node else {
                        unreachable!("a comprehension frame holds a comprehension")
                    };
                    match clauses.get(clause) {
                        None => {
                            self.spend(1)?;
                            let Some(value) = self.inline(head, &scope) else {
                                stack.push(Frame::CompHead);
                                return Ok(Step::Eval(head.clone(), scope));
                            };
                            comprehension_output(stack).push(value?);
                            Visit::Next
                        }
                        Some(CClause::If(guard)) => {
                            let Some(value) = self.inline(guard, &scope) else {
                                let guard = guard.clone();
                                stack.push(Frame::CompGuard {
                                    node: node.clone(),
                                    clause,
                                    scope: scope.clone(),
                                });
                                return Ok(Step::Eval(guard, scope));
                            };
                            if value?.as_bool() {
                                Visit::Enter(node.clone(), clause + 1, scope)
                            } else {
                                Visit::Next
                            }
                        }
                        Some(CClause::For(_, source)) => {
                            let Some(value) = self.inline(source, &scope) else {
                                let source = source.clone();
                                stack.push(Frame::CompSource {
                                    node: node.clone(),
                                    clause,
                                    scope: scope.clone(),
                                });
                                return Ok(Step::Eval(source, scope));
                            };
                            stack.push(Frame::CompFor {
                                node: node.clone(),
                                clause,
                                items: value?.into_list(),
                                next: 0,
                                scope,
                            });
                            Visit::Next
                        }
                    }
                }
                Visit::Next => match stack.last_mut() {
                    Some(Frame::CompFor {
                        node,
                        clause,
                        items,
                        next,
                        scope,
                    }) => {
                        let Core::Comp(_, clauses) = &**node else {
                            unreachable!("a comprehension frame holds a comprehension")
                        };
                        let CClause::For(pat, _) = &clauses[*clause] else {
                            unreachable!("an iteration frame holds a `for` clause")
                        };
                        let mut entered = None;
                        while entered.is_none() && *next < items.len() {
                            let mut bound = Vec::new();
                            if self.match_pat(pat, &items[*next], &mut bound) {
                                let mut inner = scope.clone();
                                for (name, value) in bound {
                                    inner = inner.bind(&name, value);
                                }
                                entered = Some(Visit::Enter(node.clone(), *clause + 1, inner));
                            }
                            *next += 1;
                        }
                        match entered {
                            Some(enter) => enter,
                            None => {
                                stack.pop();
                                Visit::Next
                            }
                        }
                    }
                    Some(Frame::Comp { .. }) => {
                        let Some(Frame::Comp { out }) = stack.pop() else {
                            unreachable!("a comprehension output")
                        };
                        return Ok(Step::Return(Value::list(out)));
                    }
                    _ => unreachable!("a comprehension's frames"),
                },
            };
        }
    }

    /// Run a pair's second operand, or finish it.
    fn second(
        &mut self,
        node: Rc<Core>,
        first: Value,
        scope: Scope,
        stack: &mut Vec<Frame>,
    ) -> GrundyResult<Step> {
        let (Core::Range(_, second, ..)
        | Core::Subst(_, second, _)
        | Core::Index(_, second, _)
        | Core::Binary(_, _, second, _)
        | Core::Rel(_, _, second, _)) = &*node
        else {
            unreachable!("a pair frame holds a binary node")
        };
        match self.inline(second, &scope) {
            Some(value) => self.pair(&node, first, value?).map(Step::Return),
            None => {
                let second = second.clone();
                stack.push(Frame::PairRhs { node, first });
                Ok(Step::Eval(second, scope))
            }
        }
    }

    /// Enter the first match arm that matches the value.
    fn arm(&mut self, node: &Core, value: &Value, scope: Scope) -> GrundyResult<Step> {
        let Core::Match(_, arms, span) = node else {
            unreachable!("a match frame holds a match")
        };
        for (pat, body) in arms {
            let mut bound = Vec::new();
            if self.match_pat(pat, value, &mut bound) {
                let mut inner = scope;
                for (name, value) in bound {
                    inner = inner.bind(&name, value);
                }
                return Ok(Step::Eval(body.clone(), inner));
            }
        }
        Err(GrundyError::new(
            GrundyErrorKind::Pattern,
            *span,
            "no match arm matches the value",
        )
        .with_hint("add a final `_ ↦ …` arm"))
    }

    /// Run a `Let`'s bindings from `index`, then its body.
    fn bind_from(
        &mut self,
        node: Rc<Core>,
        index: usize,
        mut scope: Scope,
        stack: &mut Vec<Frame>,
    ) -> GrundyResult<Step> {
        let Core::Let(binds, body) = &*node else {
            unreachable!("a binding frame holds a let")
        };
        for (index, bind) in binds.iter().enumerate().skip(index) {
            let bound = match bind {
                CBind::Let {
                    pat,
                    expr,
                    tparams,
                    span,
                } if tparams.is_empty() => match self.inline(expr, &scope) {
                    Some(value) => self.bind_pattern(pat, *span, &value?)?,
                    None => {
                        let expr = expr.clone();
                        stack.push(Frame::Bind {
                            node: node.clone(),
                            index,
                            scope: scope.clone(),
                        });
                        return Ok(Step::Eval(expr, scope));
                    }
                },
                bind => self.exec_bind(bind, &scope)?,
            };
            for (name, value) in bound {
                scope = scope.bind(&name, value);
            }
        }
        Ok(Step::Eval(body.clone(), scope))
    }

    /// Finish a two-operand expression.
    fn pair(&mut self, node: &Core, first: Value, second: Value) -> GrundyResult<Value> {
        match node {
            Core::Range(_, _, inclusive, span) => {
                let lo = first.as_int();
                let hi = second.as_int();
                let end = if *inclusive {
                    hi.checked_add(1)
                } else {
                    Some(hi)
                }
                .ok_or_else(|| err(GrundyErrorKind::Overflow, "range bound overflows").at(*span))?;
                let len = end.saturating_sub(lo).max(0);
                self.spend(len as u128).map_err(|e| e.at(*span))?;
                Ok(Value::list((lo..end).map(Value::Int).collect()))
            }
            Core::Subst(_, _, span) => {
                // Horner's rule: one product per coefficient, and composition
                // grows the accumulator to the product of the sizes.
                let p = size_of(&first).unwrap_or(1);
                let q = size_of(&second).unwrap_or(1);
                self.spend(p.saturating_mul(p).saturating_mul(q).saturating_mul(q))?;
                super::super::algebra::substitute(&first, &second).map_err(|e| e.at(*span))
            }
            Core::Index(_, _, span) => {
                let index = second.as_int();
                let items = first.as_list();
                usize::try_from(index)
                    .ok()
                    .and_then(|i| items.get(i))
                    .cloned()
                    .ok_or_else(|| {
                        GrundyError::new(
                            GrundyErrorKind::Domain,
                            *span,
                            format!("index {index} is outside a list of length {}", items.len()),
                        )
                    })
            }
            Core::Binary(op, _, _, span) => {
                self.binary(*op, first, second).map_err(|e| e.at(*span))
            }
            Core::Rel(op, _, _, span) => self
                .relation(*op, &first, &second)
                .map(Value::Bool)
                .map_err(|e| e.at(*span)),
            _ => unreachable!("a pair frame holds a binary node"),
        }
    }

    // ---------------------------------------------------------------- patterns

    /// Match a pattern, appending bindings. Returns whether it matched.
    pub fn match_pat(&self, pat: &CPat, value: &Value, out: &mut Vec<(String, Value)>) -> bool {
        match (pat, value) {
            (CPat::Wild, _) => true,
            (CPat::Var(name), _) => {
                out.push((name.clone(), value.clone()));
                true
            }
            (CPat::Int(n), Value::Int(m)) => n == m,
            (CPat::Bool(b), Value::Bool(c)) => b == c,
            (CPat::Tuple(items), Value::Tuple(values)) => {
                items.len() == values.len()
                    && items
                        .iter()
                        .zip(values.iter())
                        .all(|(item, value)| self.match_pat(item, value, out))
            }
            (CPat::List(items, rest), Value::List(values)) => {
                if values.len() < items.len() || (rest.is_none() && values.len() != items.len()) {
                    return false;
                }
                if !items
                    .iter()
                    .zip(values.iter())
                    .all(|(item, value)| self.match_pat(item, value, out))
                {
                    return false;
                }
                match rest {
                    Some(rest) => {
                        let tail = Value::list(values[items.len()..].to_vec());
                        self.match_pat(rest, &tail, out)
                    }
                    None => true,
                }
            }
            (CPat::Ctor(ctor, args), value) => match (ctor, value) {
                (CtorRef::Winner(w), Value::Winner(v)) => w == v,
                (CtorRef::None, Value::Option(None)) => true,
                (CtorRef::Some, Value::Option(Some(inner))) => self.match_pat(&args[0], inner, out),
                (CtorRef::Data(..), Value::Data(data)) => {
                    data.ctor == *ctor
                        && args
                            .iter()
                            .zip(&data.fields)
                            .all(|(arg, field)| self.match_pat(arg, field, out))
                }
                _ => false,
            },
            _ => false,
        }
    }

    // ---------------------------------------------------------------- literals

    fn int_literal(&mut self, n: u128, ty: &Ty) -> GrundyResult<Value> {
        if let Ty::Con(TyCon::Form, _) = ty {
            // The integer form n has n positions.
            guard(n)?;
            self.spend(n)?;
        }
        match ty {
            Ty::Con(TyCon::Int, _) => {
                Ok(Value::Int(i128::try_from(n).map_err(|_| {
                    err(GrundyErrorKind::Overflow, "literal exceeds i128")
                })?))
            }
            Ty::Con(TyCon::Game, _) => Ok(Value::Game(GameV::integer(to_i128(n)?, self)?)),
            Ty::Con(TyCon::Form, _) => Ok(Value::Form(FormV::finite(Game::integer(to_i128(n)?)))),
            Ty::Con(con, _) if ScalarV::zero(*con).is_some() => {
                Ok(Value::Scalar(ScalarV::int_literal(*con, n)?))
            }
            Ty::Con(..) => super::super::algebra::int_literal(ty, n),
            other => Err(unresolved(other)),
        }
    }

    fn frac_literal(&mut self, num: i128, den: u128, ty: &Ty) -> GrundyResult<Value> {
        if den == 0 {
            return Err(err(GrundyErrorKind::DivisionByZero, "zero denominator"));
        }
        match ty {
            Ty::Con(TyCon::Game, _) => Ok(Value::Game(GameV::dyadic(num, den, self)?)),
            Ty::Con(TyCon::Form, _) => {
                // Validate and size the dyadic as a Game, then present it.
                let birthday = GameV::dyadic(num, den, self)?.birthday();
                self.spend(birthday)?;
                let surreal = Surreal::from_rational(Rational::new(num, to_i128(den)?));
                Ok(Value::Form(FormV::finite(
                    Game::from_surreal(&surreal).expect("dyadic checked"),
                )))
            }
            Ty::Con(TyCon::Surreal, _) => Ok(Value::Scalar(ScalarV::Surreal(
                Surreal::from_rational(Rational::new(num, to_i128(den)?)),
            ))),
            Ty::Con(con, _) if ScalarV::zero(*con).is_some() => {
                let magnitude = ScalarV::int_literal(*con, num.unsigned_abs())?;
                let magnitude = if num < 0 { magnitude.neg() } else { magnitude };
                let denominator = ScalarV::int_literal(*con, den)?;
                Ok(Value::Scalar(magnitude.zip(&denominator, DivOp)?))
            }
            Ty::Con(..) => super::super::algebra::frac_literal(ty, num, den),
            other => Err(unresolved(other)),
        }
    }

    fn star_literal(&mut self, index: &StarIndex, ty: &Ty) -> GrundyResult<Value> {
        if let (Ty::Con(TyCon::Form, _), StarIndex::Finite(n)) = (ty, index) {
            // The nimber form *n has n(n+1)/2 option edges.
            guard(*n)?;
            self.spend(n.saturating_mul(n.saturating_add(1)) / 2)?;
        }
        let finite = || match index {
            StarIndex::Finite(n) => Ok(*n),
            _ => Err(err(
                GrundyErrorKind::Domain,
                "transfinite nimber games are outside the short games",
            )
            .with_hint("transfinite nimbers are Ordinal: `(*ω : Ordinal)`")),
        };
        match ty {
            Ty::Con(TyCon::Game, _) => Ok(Value::Game(GameV::nimber(finite()?, self)?)),
            Ty::Con(TyCon::Form, _) => Ok(Value::Form(FormV::finite(Game::nim_heap(finite()?)))),
            Ty::Con(con, _) if ScalarV::zero(*con).is_some() => {
                Ok(Value::Scalar(ScalarV::star_literal(*con, index)?))
            }
            Ty::Con(..) => super::super::algebra::star_literal(ty, index),
            other => Err(unresolved(other)),
        }
    }

    // --------------------------------------------------------------- operators

    fn unary(&mut self, op: UnaryOp, value: Value) -> GrundyResult<Value> {
        match (op, value) {
            (UnaryOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
            (UnaryOp::Neg, Value::Int(n)) => n
                .checked_neg()
                .map(Value::Int)
                .ok_or_else(|| err(GrundyErrorKind::Overflow, "negation overflows i128")),
            (UnaryOp::Neg, Value::Game(g)) => Ok(Value::Game(g.neg(self)?)),
            (UnaryOp::Neg, Value::Form(f)) => Ok(Value::Form(FormV(negate_game_element(
                f.0,
                self.graph_budget,
            )?))),
            (UnaryOp::Neg, Value::Scalar(s)) => Ok(Value::Scalar(s.neg())),
            (UnaryOp::Recip, Value::Scalar(s)) => Ok(Value::Scalar(s.inverse()?)),
            (op, value) => super::super::algebra::unary(op, &value),
        }
    }

    /// Apply an arithmetic or list operator.
    pub fn binary(&mut self, op: BinaryOp, lhs: Value, rhs: Value) -> GrundyResult<Value> {
        // Products of values that grow cost the product of their sizes, paid
        // before the work; their powers go through square-and-multiply so
        // every step pays.
        if let (Some(a), Some(b)) = (size_of(&lhs), size_of(&rhs)) {
            if matches!(
                op,
                BinaryOp::Mul | BinaryOp::Div | BinaryOp::Wedge | BinaryOp::Rem
            ) {
                self.spend(a.saturating_mul(b))?;
            }
        }
        if let (BinaryOp::Pow, Some(_), Value::Int(k)) = (op, size_of(&lhs), &rhs) {
            return self.power(lhs, *k);
        }
        let overflow = || {
            err(
                GrundyErrorKind::Overflow,
                "integer arithmetic overflows i128",
            )
        };
        match (op, &lhs, &rhs) {
            (BinaryOp::Concat, Value::List(a), Value::List(b)) => {
                self.spend((a.len() + b.len()) as u128)?;
                Ok(Value::list(a.iter().chain(b.iter()).cloned().collect()))
            }
            (BinaryOp::Add, Value::Int(a), Value::Int(b)) => {
                a.checked_add(*b).map(Value::Int).ok_or_else(overflow)
            }
            (BinaryOp::Sub, Value::Int(a), Value::Int(b)) => {
                a.checked_sub(*b).map(Value::Int).ok_or_else(overflow)
            }
            (BinaryOp::Mul, Value::Int(a), Value::Int(b)) => {
                a.checked_mul(*b).map(Value::Int).ok_or_else(overflow)
            }
            (BinaryOp::Rem, Value::Int(a), Value::Int(b)) => {
                if *b == 0 {
                    return Err(err(GrundyErrorKind::DivisionByZero, "remainder by zero"));
                }
                a.checked_rem_euclid(*b)
                    .map(Value::Int)
                    .ok_or_else(overflow)
            }
            (BinaryOp::Pow, Value::Int(a), Value::Int(k)) => {
                if *k < 0 {
                    return Err(err(
                        GrundyErrorKind::Domain,
                        "Int powers take a natural exponent",
                    )
                    .with_hint("negative powers leave the integers; use a field such as Surreal"));
                }
                match a {
                    0 => Ok(Value::Int(i128::from(*k == 0))),
                    1 => Ok(Value::Int(1)),
                    -1 => Ok(Value::Int(if k % 2 == 0 { 1 } else { -1 })),
                    // |a| ≥ 2 overflows i128 past the 127th power.
                    _ => u32::try_from(*k)
                        .ok()
                        .and_then(|k| a.checked_pow(k))
                        .map(Value::Int)
                        .ok_or_else(overflow),
                }
            }
            (BinaryOp::Add, Value::Game(a), Value::Game(b)) => Ok(Value::Game(a.add(b, self)?)),
            (BinaryOp::Sub, Value::Game(a), Value::Game(b)) => Ok(Value::Game(a.sub(b, self)?)),
            (BinaryOp::Add | BinaryOp::Sub, Value::Form(a), Value::Form(b)) => {
                Ok(Value::Form(FormV(add_game_elements(
                    a.0.clone(),
                    b.0.clone(),
                    op == BinaryOp::Sub,
                    self.graph_budget,
                )?)))
            }
            (BinaryOp::Add, Value::Scalar(a), Value::Scalar(b)) => {
                Ok(Value::Scalar(a.zip(b, AddOp)?))
            }
            (BinaryOp::Sub, Value::Scalar(a), Value::Scalar(b)) => {
                Ok(Value::Scalar(a.zip(b, SubOp)?))
            }
            (BinaryOp::Mul, Value::Scalar(a), Value::Scalar(b)) => {
                Ok(Value::Scalar(a.zip(b, MulOp)?))
            }
            (
                BinaryOp::Div,
                Value::Scalar(ScalarV::Omnific(a)),
                Value::Scalar(ScalarV::Omnific(b)),
            ) => self.omnific_divide(a, b),
            (BinaryOp::Div, Value::Scalar(a), Value::Scalar(b)) => {
                Ok(Value::Scalar(a.zip(b, DivOp)?))
            }
            (BinaryOp::Rem, Value::Scalar(a), Value::Scalar(b)) => {
                Ok(Value::Scalar(a.zip(b, RemOp)?))
            }
            (BinaryOp::Pow, Value::Scalar(a), Value::Int(k)) => Ok(Value::Scalar(a.power(*k)?)),
            (BinaryOp::Pow, Value::Scalar(a), Value::Scalar(e)) => {
                Ok(Value::Scalar(a.omega_pow(e)?))
            }
            _ => super::super::algebra::binary(op, &lhs, &rhs),
        }
    }

    /// Evaluate a relation.
    pub fn relation(&mut self, op: RelOp, lhs: &Value, rhs: &Value) -> GrundyResult<bool> {
        match (lhs, rhs) {
            (Value::Game(a), Value::Game(b)) => Ok(match op {
                RelOp::Eq => a.same(b),
                RelOp::Outcome(cell) => game_cell(a, b, self)? == cell,
                RelOp::Equiv => unreachable!("checker restricts `≡` to Form"),
                _ => order_relation(op, a.compare(b, self)?),
            }),
            (Value::Form(a), Value::Form(b)) => match op {
                RelOp::Equiv => Ok(game_element_regular_eq(&a.0, &b.0)),
                RelOp::Outcome(cell) => {
                    Ok(form_outcome_cell(&a.0, &b.0, self.graph_budget)? == cell)
                }
                _ => form_value_relation(op, &a.0, &b.0, self.graph_budget),
            },
            (Value::Int(a), Value::Int(b)) => Ok(order_relation(op, Some(a.cmp(b)))),
            (Value::Scalar(a), Value::Scalar(b)) => Ok(a.relation(op, b)),
            (Value::Poly(_) | Value::RatFunc(_) | Value::Mv(_), _) => {
                super::super::algebra::relation(op, lhs, rhs)
            }
            _ if op == RelOp::Eq => self.equal(lhs, rhs),
            _ => super::super::algebra::relation(op, lhs, rhs),
        }
    }

    /// `=` on containers is element-wise with each element's own `=`: Forms
    /// compare by value where the stopper theory licenses it, and
    /// multivectors only within one algebra.
    pub fn equal(&mut self, a: &Value, b: &Value) -> GrundyResult<bool> {
        let pairwise = |interp: &mut Self, xs: &[Value], ys: &[Value]| -> GrundyResult<bool> {
            if xs.len() != ys.len() {
                return Ok(false);
            }
            for (x, y) in xs.iter().zip(ys) {
                if !interp.equal(x, y)? {
                    return Ok(false);
                }
            }
            Ok(true)
        };
        match (a, b) {
            (Value::Tuple(x), Value::Tuple(y)) | (Value::List(x), Value::List(y)) => {
                pairwise(self, x, y)
            }
            (Value::Data(x), Value::Data(y)) => {
                Ok(x.ctor == y.ctor && pairwise(self, &x.fields, &y.fields)?)
            }
            (Value::Option(x), Value::Option(y)) => match (x, y) {
                (Some(x), Some(y)) => self.equal(x, y),
                (None, None) => Ok(true),
                _ => Ok(false),
            },
            (
                Value::Game(_)
                | Value::Form(_)
                | Value::Int(_)
                | Value::Scalar(_)
                | Value::Poly(_)
                | Value::RatFunc(_)
                | Value::Mv(_),
                _,
            ) => self.relation(RelOp::Eq, a, b),
            _ => Ok(values_equal(a, b)),
        }
    }
}

impl Interp<'_> {
    /// Exact omnific division, by long division on leading terms. An omnific
    /// quotient has no negative exponent and an integer constant term, so a
    /// step that needs a negative exponent, or a non-integral result, shows
    /// that no omnific quotient exists.
    fn omnific_divide(&mut self, a: &Omnific, b: &Omnific) -> GrundyResult<Value> {
        use ogdoad::scalar::Scalar as _;
        if b.is_zero() {
            return Err(err(GrundyErrorKind::DivisionByZero, "division by zero"));
        }
        let not_exact = || {
            err(
                GrundyErrorKind::NotInvertible,
                "the quotient is not an omnific integer",
            )
            .with_hint("omnific division is exact; its units are ±1")
        };
        let divisor = b.inner();
        let (lead_exp, lead_coef) = divisor.terms()[0].clone();
        let lead_inv = lead_coef.inv().expect("a leading coefficient is nonzero");
        let mut rem = a.inner().clone();
        let mut quot = Surreal::zero();
        while !rem.is_zero() {
            self.spend(divisor.terms().len() as u128)?;
            let (exp, coef) = rem.terms()[0].clone();
            let q_exp = exp.add(&lead_exp.neg());
            if q_exp.sign() == std::cmp::Ordering::Less {
                return Err(not_exact());
            }
            let term = Surreal::monomial(q_exp, coef.mul(&lead_inv));
            quot = quot.add(&term);
            rem = rem.add(&term.mul(divisor).neg());
        }
        Omnific::from_surreal(quot)
            .map(|q| Value::Scalar(ScalarV::Omnific(q)))
            .ok_or_else(not_exact)
    }

    /// `x ↑ k` by square-and-multiply; negative `k` inverts first.
    fn power(&mut self, base: Value, k: i128) -> GrundyResult<Value> {
        // A monomial's power is its coefficient's power, placed: the work is
        // the size of the result.
        let magnitude = k.unsigned_abs();
        match &base {
            Value::Poly(p) if k >= 0 => {
                if let Some(result) = p.monomial_power(magnitude, &mut |n| self.spend(n)) {
                    return Ok(Value::Poly(result?));
                }
            }
            Value::RatFunc(f) => {
                let inverted;
                let f = if k < 0 {
                    inverted = f.inverse()?;
                    &inverted
                } else {
                    f
                };
                if let Some(result) = f.monomial_power(magnitude, &mut |n| self.spend(n)) {
                    return Ok(Value::RatFunc(result?));
                }
            }
            _ => {}
        }
        let unit = one_like(&base)?;
        let mut base = if k < 0 {
            if let Value::Poly(_) = base {
                return Err(err(
                    GrundyErrorKind::NotInvertible,
                    "a negative power of a polynomial leaves the ring",
                )
                .with_hint("rational functions are `S(t)`"));
            }
            self.unary(UnaryOp::Recip, base)?
        } else {
            base
        };
        let mut k = k.unsigned_abs();
        let mut acc = unit;
        while k > 0 {
            if k & 1 == 1 {
                acc = self.binary(BinaryOp::Mul, acc, base.clone())?;
            }
            k >>= 1;
            if k > 0 {
                base = self.binary(BinaryOp::Mul, base.clone(), base)?;
            }
        }
        Ok(acc)
    }
}

/// A variable's value.
fn lookup(scope: &Scope, name: &str, span: Span) -> GrundyResult<Value> {
    scope
        .lookup(name)
        .cloned()
        .ok_or_else(|| internal(format!("unbound `{name}` at runtime")).at(span))
}

/// The branch a conditional takes on its test: an expression to run, or
/// the short-circuit value of `and`/`or`.
fn branch(node: &Core, test: bool) -> Result<&Rc<Core>, bool> {
    match (node, test) {
        (Core::And(_, rhs), true) | (Core::Or(_, rhs), false) => Ok(rhs),
        (Core::And(..), false) => Err(false),
        (Core::Or(..), true) => Err(true),
        (Core::If(_, then_branch, _), true) => Ok(then_branch),
        (Core::If(_, _, else_branch), false) => Ok(else_branch),
        _ => unreachable!("a test frame holds a conditional"),
    }
}

/// The machine's step after a conditional's test.
fn choose(node: &Core, test: bool, scope: Scope) -> Step {
    match branch(node, test) {
        Ok(chosen) => Step::Eval(chosen.clone(), scope),
        Err(value) => Step::Return(Value::Bool(value)),
    }
}

/// The output of the comprehension being driven: the nearest one, since
/// its inner frames are all its own clause iterations.
fn comprehension_output(stack: &mut [Frame]) -> &mut Vec<Value> {
    stack
        .iter_mut()
        .rev()
        .find_map(|frame| match frame {
            Frame::Comp { out } => Some(out),
            _ => None,
        })
        .expect("a comprehension output")
}

/// The size of a value whose arithmetic cost grows with it.
fn size_of(value: &Value) -> Option<u128> {
    match value {
        Value::Scalar(s @ (ScalarV::Surreal(_) | ScalarV::Omnific(_))) => Some(s.size()),
        Value::Poly(p) => Some(p.size()),
        Value::RatFunc(f) => Some(f.size()),
        Value::Mv(v) => Some(v.size()),
        _ => None,
    }
}

/// The unit of a sized value's ring.
fn one_like(value: &Value) -> GrundyResult<Value> {
    Ok(match value {
        Value::Scalar(s) => Value::Scalar(s.power(0)?),
        Value::Poly(p) => Value::Poly(p.one_like()),
        Value::RatFunc(f) => Value::RatFunc(f.one_like()),
        Value::Mv(v) => Value::Mv(v.one_like()),
        other => return Err(internal(format!("no unit for a {}", other.kind_name()))),
    })
}

/// The outcome cell of `a - b` for short games: no draws.
pub fn game_cell(
    a: &GameV,
    b: &GameV,
    meter: &mut impl super::super::games::game::Meter,
) -> GrundyResult<OutcomeCell> {
    let (left_first, right_first) = match a.compare(b, meter)? {
        Some(std::cmp::Ordering::Greater) => (Mover::Left, Mover::Left),
        Some(std::cmp::Ordering::Less) => (Mover::Right, Mover::Right),
        Some(std::cmp::Ordering::Equal) => (Mover::Right, Mover::Left),
        None => (Mover::Left, Mover::Right),
    };
    Ok(OutcomeCell {
        left_first,
        right_first,
    })
}

fn order_relation(op: RelOp, ordering: Option<std::cmp::Ordering>) -> bool {
    use std::cmp::Ordering::*;
    match op {
        RelOp::Eq => ordering == Some(Equal),
        RelOp::Lt => ordering == Some(Less),
        RelOp::Gt => ordering == Some(Greater),
        RelOp::Le => matches!(ordering, Some(Less | Equal)),
        RelOp::Ge => matches!(ordering, Some(Greater | Equal)),
        RelOp::Fuzzy => ordering.is_none(),
        RelOp::Equiv | RelOp::Outcome(_) => false,
    }
}

/// The members of a recursive group, each a closure that rebuilds the group
/// on call (no reference cycles).
pub fn group_members(group: &Rc<RecGroup>) -> Vec<(String, Value)> {
    group
        .names
        .iter()
        .enumerate()
        .map(|(index, name)| {
            (
                name.clone(),
                Value::Closure(Rc::new(Closure {
                    lam: group.lams[index].clone(),
                    env: group.env.clone(),
                    globals: group.globals.clone(),
                    tenv: group.tenv.clone(),
                    rec: Some((group.clone(), index)),
                    depth: group.depth.saturating_add(1),
                })),
            )
        })
        .collect()
}

/// Build a constructor value.
pub fn construct(ctor: &CtorRef, mut args: Vec<Value>) -> GrundyResult<Value> {
    Ok(match ctor {
        CtorRef::Winner(w) => Value::Winner(*w),
        CtorRef::None => Value::Option(None),
        CtorRef::Some => Value::Option(Some(Rc::new(args.pop().expect("one field")))),
        CtorRef::Data(..) => {
            let depth = guard_depth(args.iter().map(Value::depth).max().unwrap_or(0))?;
            Value::Data(Rc::new(DataV {
                ctor: ctor.clone(),
                fields: args,
                depth,
            }))
        }
    })
}

/// One level above `depth`, refused past the host guard.
fn guard_depth(depth: u32) -> GrundyResult<u32> {
    let depth = depth.saturating_add(1);
    if depth > MAX_VALUE_DEPTH {
        return Err(err(
            GrundyErrorKind::StackDepth,
            format!("the value would nest {depth} levels deep, past the host guard of {MAX_VALUE_DEPTH}"),
        )
        .with_hint("value depth is a host resource, distinct from fuel"));
    }
    Ok(depth)
}

/// The bindings of `env` a function body mentions, and the depth of a
/// function capturing them. Capturing only these keeps closures from holding
/// unrelated values and makes the captured environment what display shows.
fn capture(scope: &Scope, names: &[String]) -> GrundyResult<(Env, u32)> {
    let mut captured = Env::new();
    let mut depth = 0;
    for name in names {
        if let Some(value) = scope.env.get(name) {
            depth = depth.max(value.depth());
            captured = captured.bind(name.clone(), value.clone());
        } else if let Some(value) = scope.globals.get(name) {
            // Globals are shared by snapshot, but a closure over one still
            // nests through it.
            depth = depth.max(value.depth());
        }
    }
    Ok((captured, guard_depth(depth)?))
}

/// What a recursive group's members mention, less the members themselves.
fn group_mentions(names: &[String], lams: &[Rc<Lam>]) -> Vec<String> {
    let mut all: BTreeSet<&str> = lams
        .iter()
        .flat_map(|lam| lam.mentions.iter().map(String::as_str))
        .collect();
    for name in names {
        all.remove(name.as_str());
    }
    all.into_iter().map(String::from).collect()
}

/// Read a Game value.
pub fn as_game(value: &Value) -> GameV {
    match value {
        Value::Game(g) => g.clone(),
        other => panic!("expected a Game, found {}", other.kind_name()),
    }
}

/// Read a Form value.
pub fn as_form(value: &Value) -> &FormV {
    match value {
        Value::Form(f) => f,
        other => panic!("expected a Form, found {}", other.kind_name()),
    }
}

/// Whether an expression mentions any of the names (conservatively,
/// ignoring shadowing).
pub fn mentions(core: &Core, names: &BTreeSet<&str>) -> bool {
    let mut found = false;
    visit_vars(core, &mut |name| found |= names.contains(name));
    found
}

fn unfounded(equation: &str, name: &str) -> GrundyError {
    err(
        GrundyErrorKind::Unfounded,
        format!("game equation `{equation}` is `{name}` itself, unguarded by a brace constructor"),
    )
    .with_hint("guard it: `g =: {g |}`")
}

fn unresolved(ty: &Ty) -> GrundyError {
    internal(format!("a literal's type is unresolved at runtime: {ty:?}"))
}

/// An invariant violation: a well-typed program reached an impossible state.
pub fn internal(message: impl Into<String>) -> GrundyError {
    err(
        GrundyErrorKind::Domain,
        format!("internal: {}", message.into()),
    )
}

fn to_i128(n: u128) -> GrundyResult<i128> {
    i128::try_from(n).map_err(|_| err(GrundyErrorKind::Overflow, "literal exceeds i128"))
}
