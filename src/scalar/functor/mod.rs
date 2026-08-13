//! Generic scalar adjunctions.
//!
//!   * [`surcomplex`] — `Surcomplex<S>`: adjoin a root of `x² + 1` (carries
//!     `conj()`).
//!   * [`ramified`] — `Ramified<S, E>`: adjoin a root of the Eisenstein
//!     polynomial `xᴱ − ϖ` over a [`Valued`](crate::scalar::Valued) base.
//!   * [`laurent`] — `Laurent<S, K>`: adjoin a transcendental `t` with a fresh
//!     valuation (`v(t) = 1`), the formal Laurent field `S((t))`.
//!   * [`gauss`] — `Gauss<S>`: adjoin a transcendental `t` of valuation `0` whose
//!     residue is transcendental, the rational function field `S(t)` with the Gauss
//!     valuation. Its represented residue field is `k(t̄)` and its value group
//!     is inherited from the base.
//!
//! The two transcendental adjunctions differ in where `t` lands: `Laurent`'s
//! `t` is a uniformizer (extends the value group), `Gauss`'s `t` is a unit with
//! transcendental residue (extends the residue field).

pub mod gauss;
pub mod laurent;
pub mod ramified;
pub mod surcomplex;

pub use gauss::*;
pub use laurent::*;
pub use ramified::*;
pub use surcomplex::*;
