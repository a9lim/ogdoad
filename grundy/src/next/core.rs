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

impl CPat {
    /// Whether the pattern always matches (so a binding needs no check).
    pub fn irrefutable(&self) -> bool {
        match self {
            CPat::Wild | CPat::Var(_) => true,
            CPat::Tuple(items) => items.iter().all(CPat::irrefutable),
            _ => false,
        }
    }

    /// Variables bound by the pattern.
    pub fn binders(&self, out: &mut Vec<String>) {
        match self {
            CPat::Var(name) => out.push(name.clone()),
            CPat::Wild | CPat::Int(_) | CPat::Bool(_) => {}
            CPat::Tuple(items) | CPat::Ctor(_, items) => {
                items.iter().for_each(|item| item.binders(out))
            }
            CPat::List(items, rest) => {
                items.iter().for_each(|item| item.binders(out));
                if let Some(rest) = rest {
                    rest.binders(out);
                }
            }
        }
    }
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
