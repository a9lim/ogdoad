//! The grundy expression language over Ogdoad's scalar, Clifford, polynomial,
//! and game worlds.
//!
//! `docs/spec.md` is the language contract and `docs/implementation.md`
//! describes the runtime. This workspace crate is unpublished and depends only
//! on Ogdoad's public Rust API.

#![warn(missing_docs)]

/// Parsed syntax tree types.
pub mod ast;
/// Structured evaluator errors and result types.
pub mod error;
/// Evaluation entry points and fixed world metadata.
pub mod eval;
/// Tokenization and statement-continuation detection.
pub mod lex;
/// Parsing from source text to syntax trees.
pub mod parse;
/// Canonical source rendering for syntax trees.
pub mod unparse;

pub use error::{GrundyError, GrundyErrorKind, GrundyResult, Span};
pub use eval::{eval_to_string, EvalLine, GrundySession, GRUNDY_VERSION, WORLD_MENU};
pub use lex::needs_continuation;
pub use parse::parse_statement;
pub use unparse::{unparse_expr, unparse_statement};
