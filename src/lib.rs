//! pleroma — Clifford algebras (with nilpotents) over the field-like
//! subclasses of combinatorial games.
//!
//! Pure-Rust math core (generic over the `Scalar` trait), with optional PyO3
//! bindings behind the `python` feature (abi3).
//!   - `scalar`    : the Scalar trait + an exact Rational for engine validation
//!   - `nimber`    : On_2 (characteristic 2) — exact nim-add/mul/inv, the novel backend
//!   - `surreal`   : Conway normal form scalars with recursive exponents (char 0)
//!   - `surcomplex`: adjoin i over any backend
//!   - `clifford`  : the multivector engine + versor/GA layer, generic over Scalar
//!   - `arf`       : the Arf invariant (the char-2 Clifford classifier)
//!   - `games`     : nim-multiplication as Conway's Turning-Corners game
//!   - `py`        : PyO3 per-backend bindings (feature = "python")
//!
//! See `NOTES.md` for the mathematical thread.

pub mod arf;
pub mod clifford;
pub mod games;
pub mod nimber;
pub mod scalar;
pub mod surcomplex;
pub mod surreal;

#[cfg(feature = "python")]
mod py;
