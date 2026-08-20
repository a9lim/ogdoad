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
//! Materialized products and rank-`n` sparse polynomial actions accept
//! [`WeylExpansionBudget`] bounds. The unbounded checked methods preserve the
//! original convenience surface; finite budgets are the authoritative path for
//! untrusted exponents and support sizes.
//!
//! On [`crate::scalar::ExactFieldScalar`] backends, certified Darboux reduction
//! exposes a standard Weyl factor and a central radical-polynomial factor.
//! [`WeylHomomorphism`], [`WeylAutomorphism`], and
//! [`WeylAntiAutomorphism`] keep ordinary and product-reversing maps distinct.
//! Bernstein/differential-order principal symbols, the constant Poisson bracket,
//! and [`HbarWeylAlgebra`] stay finite-support and budget-aware.
//! In positive characteristic, [`WeylCenterDescription`] certifies the enlarged
//! centre, [`WeylCentralFiber`] and [`WeylCentralCharacterModule`] keep finite
//! quotient dimensions explicit, and characteristic-two fibres have a checked
//! [`WeylCliffordFiber`] product oracle.
//!
//! This is a separate public pillar from [`crate::clifford`]. It shares the
//! commutative [`crate::scalar::Scalar`] coefficient discipline, but a Weyl
//! monomial needs an exponent vector rather than a finite blade mask.

mod algebra;
mod center;
mod clifford_fiber;
mod deformation;
mod differential;
mod element;
mod fiber;
mod normal_form;
mod polynomial;
mod product;
mod symbol;
mod transform;

pub use algebra::*;
pub use center::*;
pub use clifford_fiber::*;
pub use deformation::*;
pub use element::*;
pub use fiber::*;
pub use normal_form::*;
pub use polynomial::*;
pub use symbol::*;
pub use transform::*;
