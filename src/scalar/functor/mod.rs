//! **Functors** — the ways to *grow* a coefficient world, orthogonal to the
//! "any number" place table. Each takes a backend `S` and builds a larger field
//! on top of it, rather than naming a concrete world of its own.
//!
//! Two binary axes organise them — *algebraic vs transcendental* (is the new
//! generator a root of a polynomial over `S`?) and *residue- vs value-extending*
//! (does it grow the residue field or the value group?) — and the four functors
//! fill all four corners of the square:
//!
//! |                 | residue-extending          | value-group-extending     |
//! |-----------------|----------------------------|---------------------------|
//! | **algebraic**   | [`Surcomplex`] (root of `x²+1`) | [`Ramified`] (root of `xᴱ−ϖ`) |
//! | **transcendental** | [`Gauss`] (adjoin `t`, `v(t)=0`) | [`Laurent`] (adjoin `t`, `v(t)=1`) |
//!
//!   * [`surcomplex`] — `Surcomplex<S>`: adjoin a root of `x² + 1` (carries
//!     `conj()`). The *unramified*, residue-extending algebraic flavour.
//!   * [`ramified`] — `Ramified<S, E>`: adjoin a root of the Eisenstein
//!     polynomial `xᴱ − ϖ` over a [`Valued`](crate::scalar::Valued) base. The
//!     *ramified*, value-group-extending algebraic flavour.
//!   * [`laurent`] — `Laurent<S, K>`: adjoin a transcendental `t` with a fresh
//!     valuation (`v(t) = 1`), the formal Laurent field `S((t))`.
//!   * [`gauss`] — `Gauss<S>`: adjoin a transcendental `t` of valuation `0` whose
//!     residue is transcendental, the rational function field `S(t)` with the Gauss
//!     valuation. Residue field `k(t̄)`, value group unchanged — the last corner.
//!
//! The two transcendental adjunctions differ only in where `t` lands: `Laurent`'s
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
