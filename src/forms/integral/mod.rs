//! Integral lattices: the arithmetic form world over `Z`.
//!
//! This submodule is the forms pillar's integral complement to field-valued
//! quadratic-form classification. It keeps the lattice object, ADE catalogue,
//! genus computation, and mass/Leech layer together. Children stay private
//! behind the flat re-export, like every other shelf; the parent `forms`
//! module re-exports the public items flat.

mod clifford_lattices;
mod codes;
pub(crate) mod diagonal;
mod discriminant;
mod fqm_witt;
mod genus;
mod kneser;
mod lattice;
mod mass_formula;
mod modular;
mod niemeier;
mod root_lattices;
mod theta;
mod weyl_versors;

#[cfg(test)]
mod coherence;

/// Whether `order` is a power of `p` (with `order == 1` = `p⁰` accepted). Shared by
/// the discriminant-form and finite-quadratic-module primary-component sweeps.
pub(crate) fn is_prime_power(order: u128, p: u128) -> bool {
    if order == 1 {
        return true;
    }
    let mut m = order;
    while m.is_multiple_of(p) {
        m /= p;
    }
    m == 1
}

pub use clifford_lattices::*;
pub use codes::*;
pub use discriminant::*;
pub use fqm_witt::*;
pub use genus::*;
pub use kneser::*;
pub use lattice::*;
pub use mass_formula::*;
pub use modular::*;
pub use niemeier::*;
pub use root_lattices::*;
pub use weyl_versors::*;
