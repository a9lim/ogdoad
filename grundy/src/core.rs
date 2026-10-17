//! The elaborated core language the evaluator runs.
//!
//! Every literal carries its resolved type (possibly a type parameter of an
//! enclosing generalized binding, resolved at runtime), and every reference
//! to a generalized binding carries its instantiation.

use std::rc::Rc;

use super::builtins::Builtin;
use super::error::Span;
use super::syntax::ast::{BinaryOp, Expr, RelOp, StarIndex, UnaryOp};
use super::types::{DataId, Ty, TyVar};

/// A reference to a constructor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CtorRef {
    /// A user data constructor: type id and constructor index.
    Data(DataId, u32),
    /// `Left`, `Right`, `Draw`.
    Winner(u8),
    /// `Some`.
    Some,
    /// `None`.
    None,
}

/// Elaborated patterns.
#[derive(Clone, Debug)]
pub enum CPat {
    /// `_`.
    Wild,
    /// A variable.
    Var(String),
    /// An integer.
    Int(i128),
    /// A Boolean.
    Bool(bool),
    /// A tuple.
    Tuple(Vec<CPat>),
    /// A constructor with argument patterns.
    Ctor(CtorRef, Vec<CPat>),
    /// A list with an optional rest pattern.
    List(Vec<CPat>, Option<Box<CPat>>),
}

/// A list or brace-side element.
#[derive(Clone, Debug)]
pub enum CItem {
    /// One element.
    One(Core),
    /// A spliced list.
    Splice(Core),
}

/// A comprehension clause.
#[derive(Clone, Debug)]
pub enum CClause {
    /// Iterate a list.
    For(CPat, Core),
    /// Keep elements satisfying a guard.
    If(Core),
}

/// A lambda.
#[derive(Debug)]
pub struct Lam {
    /// Parameter patterns.
    pub params: Vec<CPat>,
    /// The body.
    pub body: Core,
    /// The surface source, for display.
    pub source: Expr,
    /// Every variable name the body mentions: a superset of what a closure
    /// over it must capture.
    pub mentions: Vec<String>,
}

impl Lam {
    /// A lambda, recording the names its body mentions.
    pub fn new(params: Vec<CPat>, body: Core, source: Expr) -> Lam {
        let mentions = mentioned(&body);
        Lam {
            params,
            body,
            source,
            mentions,
        }
    }
}

/// The variable names an expression mentions, sorted and deduplicated.
pub fn mentioned(core: &Core) -> Vec<String> {
    let mut names = std::collections::BTreeSet::new();
    visit_vars(core, &mut |name| {
        names.insert(name.to_string());
    });
    names.into_iter().collect()
}

/// One elaborated binding in a sequence.
#[derive(Clone, Debug)]
pub enum CBind {
    /// `pat := e`, generalized over `tparams` when they are non-empty.
    Let {
        /// The pattern.
        pat: CPat,
        /// The right-hand side.
        expr: Core,
        /// Runtime type parameters.
        tparams: Vec<TyVar>,
        /// Source span of the binding.
        span: Span,
    },
    /// A run of recursive functions.
    RecFns {
        /// Names in the run.
        names: Vec<String>,
        /// Their lambdas.
        lams: Vec<Rc<Lam>>,
        /// Runtime type parameters shared by the group.
        tparams: Vec<TyVar>,
    },
    /// A run of guarded game equations.
    RecForms {
        /// Names in the run.
        names: Vec<String>,
        /// Their right-hand sides.
        exprs: Vec<Core>,
        /// Source spans.
        spans: Vec<Span>,
    },
}

/// Elaborated expressions.
#[derive(Clone, Debug)]
pub enum Core {
    /// A numeral at its type.
    Int(u128, Ty),
    /// A literal-shaped fraction at its type.
    Frac(i128, u128, Ty),
    /// A star literal at its type.
    Star(StarIndex, Ty),
    /// `ω` at its type.
    Omega(Ty),
    /// `up` (`down` when the flag is set) at its type.
    Up(bool, Ty),
    /// A Boolean.
    Bool(bool),
    /// A monomorphic variable.
    Var(String, Span),
    /// A generalized binding at an instantiation.
    Inst(String, Vec<Ty>, Span),
    /// A builtin at an instantiation.
    Builtin(Builtin, Vec<Ty>),
    /// A constructor (a function if it has fields).
    Ctor(CtorRef, usize),
    /// A tuple.
    Tuple(Vec<Core>),
    /// A list.
    List(Vec<CItem>),
    /// A comprehension.
    Comp(Box<Core>, Vec<CClause>),
    /// An Int range.
    Range(Box<Core>, Box<Core>, bool, Span),
    /// A brace form at `Game` or `Form`.
    Form(Vec<CItem>, Vec<CItem>, Ty, Span),
    /// A call.
    Call(Box<Core>, Vec<Core>, Span),
    /// Polynomial or rational-function evaluation/composition.
    Subst(Box<Core>, Box<Core>, Span),
    /// List indexing.
    Index(Box<Core>, Box<Core>, Span),
    /// A lambda.
    Lambda(Rc<Lam>),
    /// A unary operator.
    Unary(UnaryOp, Box<Core>, Span),
    /// An arithmetic or list operator.
    Binary(BinaryOp, Box<Core>, Box<Core>, Span),
    /// A relation.
    Rel(RelOp, Box<Core>, Box<Core>, Span),
    /// Short-circuit `and`.
    And(Box<Core>, Box<Core>),
    /// Short-circuit `or`.
    Or(Box<Core>, Box<Core>),
    /// A conditional.
    If(Box<Core>, Box<Core>, Box<Core>),
    /// A match.
    Match(Box<Core>, Vec<(CPat, Core)>, Span),
    /// A sequence of bindings scoped over a body.
    Let(Vec<CBind>, Box<Core>),
    /// Bind a type's named generator (`t` or `x`) over a body.
    Gen(String, Ty, Box<Core>),
}

/// Visit every variable reference in an expression.
pub fn visit_vars(core: &Core, f: &mut dyn FnMut(&str)) {
    let item = |item: &CItem, f: &mut dyn FnMut(&str)| match item {
        CItem::One(core) | CItem::Splice(core) => visit_vars(core, f),
    };
    match core {
        Core::Var(name, _) | Core::Inst(name, _, _) => f(name),
        Core::Int(..)
        | Core::Frac(..)
        | Core::Star(..)
        | Core::Omega(_)
        | Core::Up(..)
        | Core::Bool(_)
        | Core::Builtin(..)
        | Core::Ctor(..) => {}
        Core::Tuple(items) => items.iter().for_each(|i| visit_vars(i, f)),
        Core::List(items) => items.iter().for_each(|i| item(i, f)),
        Core::Comp(head, clauses) => {
            visit_vars(head, f);
            for clause in clauses {
                match clause {
                    CClause::For(_, source) => visit_vars(source, f),
                    CClause::If(guard) => visit_vars(guard, f),
                }
            }
        }
        Core::Range(a, b, ..)
        | Core::Subst(a, b, _)
        | Core::Index(a, b, _)
        | Core::Binary(_, a, b, _)
        | Core::Rel(_, a, b, _)
        | Core::And(a, b)
        | Core::Or(a, b) => {
            visit_vars(a, f);
            visit_vars(b, f);
        }
        Core::Form(left, right, ..) => {
            left.iter().chain(right).for_each(|i| item(i, f));
        }
        Core::Call(callee, args, _) => {
            visit_vars(callee, f);
            args.iter().for_each(|a| visit_vars(a, f));
        }
        Core::Lambda(lam) => visit_vars(&lam.body, f),
        Core::Unary(_, a, _) => visit_vars(a, f),
        Core::If(c, a, b) => {
            visit_vars(c, f);
            visit_vars(a, f);
            visit_vars(b, f);
        }
        Core::Match(scrutinee, arms, _) => {
            visit_vars(scrutinee, f);
            arms.iter().for_each(|(_, body)| visit_vars(body, f));
        }
        Core::Let(binds, body) => {
            for bind in binds {
                match bind {
                    CBind::Let { expr, .. } => visit_vars(expr, f),
                    CBind::RecFns { lams, .. } => {
                        lams.iter().for_each(|lam| visit_vars(&lam.body, f))
                    }
                    CBind::RecForms { exprs, .. } => exprs.iter().for_each(|e| visit_vars(e, f)),
                }
            }
            visit_vars(body, f);
        }
        Core::Gen(_, _, body) => visit_vars(body, f),
    }
}
