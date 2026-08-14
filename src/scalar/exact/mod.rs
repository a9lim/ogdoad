//! Fixed-width exact characteristic-zero scalars.
//!
//! [`Rational`] represents reduced fractions over `i128`; [`Integer`] represents
//! `i128` integers. Both use checked arithmetic and panic when a result leaves
//! the carrier. They form the standard fraction-field pair `ℤ ⊂ ℚ` used by the
//! generic algebra and forms layers.

pub mod integer;
pub mod rational;

pub use integer::*;
pub use rational::*;
