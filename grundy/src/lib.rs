//! grundy: a typed language for combinatorial games over Ogdoad.
//!
//! Positions are ordinary data and moves are functions; games arise by
//! exploring a ruleset from a position. Answers state their scope and
//! evidence: exact on finite objects, verified claims with re-checkable
//! certificates, and sampled answers typed `Bounded`. Ogdoad's scalar,
//! polynomial, and Clifford worlds are types that coexist in one program.
//!
//! `docs/spec.md` is the language contract and `docs/implementation.md`
//! describes the runtime. This workspace crate is unpublished and depends
//! only on Ogdoad's public Rust API.

#![warn(missing_docs)]

mod algebra;
mod builtins;
mod core;
mod display;
mod eval;
mod games;
mod session;
mod types;
mod worker;

/// Errors, spans, and stable error codes.
pub mod error;
/// Surface syntax: tokens, trees, parsing, and canonical rendering.
pub mod syntax;

pub use error::{GrundyError, GrundyErrorKind, GrundyResult, Span};
pub use syntax::lex::needs_continuation;
pub use syntax::parse::{parse_expr, parse_statement};
pub use syntax::unparse::{unparse_expr, unparse_stmt};
pub use worker::{eval_to_string, EvalLine, GrundySession};

/// The language version.
pub const GRUNDY_VERSION: &str = env!("CARGO_PKG_VERSION");

/// The builtin function names, for help screens and tooling.
pub fn builtin_names() -> Vec<&'static str> {
    builtins::Builtin::ALL.iter().map(|b| b.name()).collect()
}
