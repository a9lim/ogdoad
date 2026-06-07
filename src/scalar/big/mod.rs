//! **Big** — the transfinite worlds, where the number is allowed to be infinite.
//! Conway normal form / Hahn series `Σ ω^{exp}·coeff` with recursive exponents.
//!
//!   * [`surreal`] — `No`, the real-closed char-0 field. The transfinite mirror of
//!     ℚ/ℝ; coefficients are ℚ (the honest finite truncation), exponents are fully
//!     recursive surreals.
//!   * [`omnific`] — `Oz ⊂ No`, the omnific *integers*: the ring of integers of the
//!     surreals, the transfinite mirror of ℤ (and the surreal mirror of `Z_p`).
//!   * [`onag`] — transfinite (ordinal) **nimbers**: the char-2 sibling of
//!     [`surreal`]. Same CNF representation, but coefficients combine by XOR
//!     (nim-addition) — `surreal : nimber :: No : On₂` extended to the ordinals.
//!
//! `surreal` and `onag` share the descending-CNF shape (a `Vec<(exponent, coeff)>`
//! recursing on exponents); they differ only in the coefficient ring and its merge
//! (ordinary `+` vs nim `XOR`).

pub mod omnific;
pub mod onag;
pub mod surreal;

pub use omnific::*;
pub use onag::*;
pub use surreal::*;
