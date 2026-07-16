//! grundy, the small expression language over ogdoad scalar worlds.
//!
//! The language contract lives in `docs/spec.md` (in this crate); the runtime
//! architecture in `docs/implementation.md`. This crate is the pure Rust
//! parser/evaluator over the published `ogdoad` core — unpublished
//! (`publish = false`) while the language is pre-release, so the ogdoad crate
//! carries no grundy surface until the language ships.

pub mod ast;
pub mod error;
pub mod eval;
pub mod lex;
pub mod parse;
pub mod unparse;

pub use error::{GrundyError, GrundyErrorKind, GrundyResult, Span};
pub use eval::{eval_to_string, EvalLine, GrundySession, GRUNDY_VERSION, WORLD_MENU};
pub use lex::needs_continuation;
pub use parse::parse_statement;
pub use unparse::{unparse_expr, unparse_statement};
