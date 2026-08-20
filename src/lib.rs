//! Clifford and Weyl algebras, quadratic forms, arithmetic, and combinatorial games.
//!
//! The pure-Rust core is generic over [`scalar::Scalar`]. Optional PyO3
//! bindings are available behind the `python` feature. The public API has five
//! pillars:
//!
//! - [`scalar`] provides exact, finite, valued, global, surreal, and ordinal
//!   coefficient models.
//! - [`clifford`] provides metrics, multivectors, products, versors, spinors,
//!   and geometric-algebra constructions.
//! - [`forms`] provides quadratic-form classification, Witt and Brauer theory,
//!   Springer decompositions, and local--global and integral arithmetic.
//! - [`games`] provides finite impartial, short partizan, misère, loopy,
//!   thermographic, and game-exterior constructions.
//! - [`weyl`] provides budgeted finite-support PBW Weyl algebras, certified
//!   Darboux coordinates, typed transformations and symbols, and rank-`n`
//!   sparse polynomial differential actions.
//!
//! Arbitrary partizan games form an abelian group, not a commutative scalar
//! ring; game-valued constructions therefore remain separate from the generic
//! Clifford engine. See the repository `README.md` for supported backends and
//! representation limits.

#![warn(missing_docs)]
// This crate is matrix/algebra-heavy throughout: linalg solves, Gram matrices,
// Witt/carry formulas, Dickson/symplectic reductions, and spinor reps all walk
// index-parallel arrays where explicit `for i in 0..n` reads clearer than the
// iterator-adapter rewrite (the body indexes several arrays by the same `i`,
// or reads `out[i-1]` while writing `out[i]`). `needless_range_loop` is a false
// positive at every one of those sites, so it is allowed crate-wide here rather
// than suppressed piecemeal at a dozen matrix modules.
#![allow(clippy::needless_range_loop)]

pub mod clifford;
pub mod forms;
pub mod games;
pub(crate) mod linalg;
pub mod scalar;
pub mod weyl;

#[cfg(feature = "python")]
mod py;
