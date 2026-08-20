//! Finite-support Weyl algebras in canonical PBW form.
//!
//! Given a finite free module with ordered basis `z_0,...,z_(m-1)` and an
//! alternating scalar-valued form `omega`, [`WeylAlgebra`] constructs
//!
//! ```text
//! T(V) / (z_i z_j - z_j z_i - omega[i][j]).
//! ```
//!
//! [`WeylAlgebra::standard`] is the usual rank-`n` algebra with generators
//! `x_0,...,x_(n-1),d_0,...,d_(n-1)` and relations
//! `[d_i,x_j] = delta_ij`. Elements are finite sparse sums in the PBW basis;
//! the algebra itself is infinite-dimensional. Positive characteristic is not
//! collapsed to the characteristic-zero differential-operator picture: the
//! larger center remains visible, and the polynomial action is documented as
//! non-faithful there.
//!
//! This is a separate public pillar from [`crate::clifford`]. It shares the
//! commutative [`crate::scalar::Scalar`] coefficient discipline, but a Weyl
//! monomial needs an exponent vector rather than a finite blade mask.

mod algebra;
mod differential;
mod element;
mod product;

pub use algebra::*;
pub use element::*;
