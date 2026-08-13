//! Quadratic-form invariants over supported finite fields of odd characteristic.
//!
//! Over a finite field `F_q` of odd characteristic a nondegenerate quadratic
//! form is classified completely by **dimension + discriminant** (det mod
//! squares): for each dimension there are exactly two classes, distinguished by
//! whether the discriminant is a square. So the classifier is essentially
//! `(dim, disc-class)`.
//!
//! The Hasse--Witt invariant is always `+1` because finite fields have trivial
//! Brauer group. [`hilbert_symbol`] also computes the corresponding finite-field
//! representation witness.

mod field;
mod invariants;

pub use field::*;
pub use invariants::*;

#[cfg(test)]
mod tests;
