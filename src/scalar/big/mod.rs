//! Represented transfinite scalar worlds in recursive normal form.
//!
//! - [`surreal`] stores finite-support Hahn/Conway normal forms with rational
//!   coefficients and recursive surreal exponents.
//! - [`omnific`] is the validated omnific-integer subring of that model.
//! - [`ordinal`] stores recursive Cantor normal forms and supplies ordinary
//!   ordinal arithmetic plus checked transfinite nim arithmetic.
//!
//! The surreal and ordinal backends share only the descending-term
//! canonicalizer. Their exponent orders, coefficient operations, multiplication,
//! and inverses remain distinct; ordinal-nimber negation is the characteristic-two
//! identity.

pub(crate) mod cnf;
pub mod omnific;
pub mod ordinal;
pub mod surreal;

pub use omnific::*;
pub use ordinal::*;
pub use surreal::*;
