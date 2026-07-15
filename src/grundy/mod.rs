//! grundy, the small expression language over ogdoad scalar worlds.
//!
//! The language contract lives in `docs/grundy/spec.md`; this module keeps the pure
//! Rust parser/evaluator independent of the optional PyO3 bindings.

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
