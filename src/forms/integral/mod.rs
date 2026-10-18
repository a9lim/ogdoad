//! Integral lattices: the arithmetic form world over `Z`.
//!
//! This submodule is the forms pillar's integral complement to field-valued
//! quadratic-form classification. It keeps the lattice object, ADE catalogue,
//! genus computation, and mass/Leech layer together. Children stay private
//! behind the flat re-export, like every other shelf; the parent `forms`
//! module re-exports the public items flat.
//!
//! # Examples
//!
//! `E8` is the even unimodular lattice of rank 8 with 240 roots. Construction A
//! on the extended Hamming `[8,4,4]` code lands in the same genus with the same
//! theta series (by the classical uniqueness of even unimodular lattices in rank
//! 8, it is `E8` again). The Smith--Minkowski--Siegel mass of that genus is
//! `1/696729600`, the reciprocal of `|Aut(E8)|`, because the genus has one class.
//!
//! ```
//! use ogdoad::forms::{are_in_same_genus, e_8, extended_hamming_code, mass_even_unimodular};
//!
//! let e8 = e_8();
//! assert!(e8.is_even() && e8.is_unimodular() && e8.dim() == 8);
//! assert_eq!(e8.kissing_number(), Some(240)); // the roots
//! assert_eq!(e8.theta_series(3), Some(vec![1, 240, 2160])); // 1 + 240 q + 2160 q^2
//! assert_eq!(e8.automorphism_group_order(), Some(696_729_600)); // |W(E8)|
//! assert_eq!(mass_even_unimodular(8), Some((1, 696_729_600)));
//!
//! let from_code = extended_hamming_code().construction_a().unwrap();
//! assert!(are_in_same_genus(&from_code, &e8));
//! assert_eq!(from_code.theta_series(3), e8.theta_series(3));
//! ```

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
