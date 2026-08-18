//! Witt, Brauer, and Brauer--Wall invariants of quadratic forms.
//!
//! * `class` defines [`WittClass`] for finite characteristic-two fields and the
//!   characteristic-indexed [`WittClassG`].
//! * `ring` provides tensor products, Pfister forms, and the first invariants of
//!   the fundamental-ideal filtration. The characteristic-two quadratic Witt
//!   group is a module, not this ring.
//! * `brauer_wall` computes graded Clifford classes over the supported real,
//!   complex, rational, finite-field, and function-field domains.
//! * `brauer_rational` computes rational two-torsion Hasse--Witt and Clifford
//!   Brauer classes.
//! * `centers` constructs full and even Clifford centers as discriminant
//!   quadratic etale algebras and compares them with Brauer--Wall coordinates.
//! * `cyclic` provides `Q/Z`-valued local invariants for unramified cyclic
//!   algebras and tame Kummer symbols.
//! * `milnor` exposes degree-at-most-two mod-two Milnor symbols, strict `e_n`
//!   maps, and rational/function-field residue maps.
//!
//! Child modules are re-exported through this module.

mod brauer_rational;
mod brauer_wall;
mod centers;
mod class;
mod cyclic;
mod milnor;
mod ring;

pub use brauer_rational::*;
pub use brauer_wall::*;
pub use centers::*;
pub use class::*;
pub use cyclic::*;
pub use milnor::*;
pub use ring::*;
