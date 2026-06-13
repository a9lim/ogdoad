//! The 24 Niemeier classes and the rank-24 Siegel-Weil check.
//!
//! This module records the standard classification catalogue of positive-definite
//! even unimodular rank-24 lattices: the root-system type, the finite glue-code
//! index `[N:R]`, and the quotient `Aut(N)/W(R)` preserving the glue. The rooted
//! classes are represented by this exact catalogue rather than by 23 large Gram
//! matrices; the root lattice `R` is constructible, while the full overlattice is
//! represented by the uniqueness of the Niemeier class with that root system. The
//! Leech lattice remains the explicit Gram-constructor supplied by [`super::leech`].

use super::{
    delta, eisenstein_e4, mass_even_unimodular, modular_qexp_add, modular_qexp_mul,
    modular_qexp_scale, root_lattices, IntegralForm,
};
use crate::scalar::{Rational, Scalar};

/// An irreducible simply-laced root-system component.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum NiemeierComponentKind {
    A(usize),
    D(usize),
    E(usize),
}

impl NiemeierComponentKind {
    pub fn rank(self) -> usize {
        match self {
            NiemeierComponentKind::A(n)
            | NiemeierComponentKind::D(n)
            | NiemeierComponentKind::E(n) => n,
        }
    }

    pub fn coxeter_number(self) -> u128 {
        match self {
            NiemeierComponentKind::A(n) => (n + 1) as u128,
            NiemeierComponentKind::D(n) => (2 * n - 2) as u128,
            NiemeierComponentKind::E(6) => 12,
            NiemeierComponentKind::E(7) => 18,
            NiemeierComponentKind::E(8) => 30,
            NiemeierComponentKind::E(_) => panic!("unsupported exceptional root rank"),
        }
    }

    pub fn root_count(self) -> u128 {
        (self.rank() as u128)
            .checked_mul(self.coxeter_number())
            .expect("root count exceeds u128")
    }

    pub fn determinant(self) -> u128 {
        match self {
            NiemeierComponentKind::A(n) => (n + 1) as u128,
            NiemeierComponentKind::D(_) => 4,
            NiemeierComponentKind::E(6) => 3,
            NiemeierComponentKind::E(7) => 2,
            NiemeierComponentKind::E(8) => 1,
            NiemeierComponentKind::E(_) => panic!("unsupported exceptional root rank"),
        }
    }

    pub fn weyl_group_order(self) -> Option<u128> {
        match self {
            NiemeierComponentKind::A(n) => checked_factorial(n + 1),
            NiemeierComponentKind::D(n) => match n {
                0 | 1 => None,
                2 => checked_pow2(2),
                3 => checked_factorial(4),
                _ => checked_pow2(n - 1)?.checked_mul(checked_factorial(n)?),
            },
            NiemeierComponentKind::E(6) => Some(51_840),
            NiemeierComponentKind::E(7) => Some(2_903_040),
            NiemeierComponentKind::E(8) => Some(root_lattices::E8_WEYL_GROUP_ORDER),
            NiemeierComponentKind::E(_) => None,
        }
    }

    pub fn root_lattice(self) -> IntegralForm {
        match self {
            NiemeierComponentKind::A(n) => root_lattices::a_n(n),
            NiemeierComponentKind::D(n) => root_lattices::d_n(n),
            NiemeierComponentKind::E(6) => root_lattices::e_6(),
            NiemeierComponentKind::E(7) => root_lattices::e_7(),
            NiemeierComponentKind::E(8) => root_lattices::e_8(),
            NiemeierComponentKind::E(_) => panic!("unsupported exceptional root rank"),
        }
    }
}

/// A repeated irreducible component of a Niemeier root system.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NiemeierRootComponent {
    pub kind: NiemeierComponentKind,
    pub multiplicity: usize,
}

/// One class in the Niemeier genus.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NiemeierClass {
    label: &'static str,
    components: &'static [NiemeierRootComponent],
    coxeter_number: u128,
    glue_code_order: Option<u128>,
    automorphism_quotient_order: u128,
}

impl NiemeierClass {
    pub fn label(&self) -> &'static str {
        self.label
    }

    pub fn components(&self) -> &'static [NiemeierRootComponent] {
        self.components
    }

    pub fn coxeter_number(&self) -> u128 {
        self.coxeter_number
    }

    /// The index `[N:R]` of the root lattice in the Niemeier lattice. `None` is
    /// used only for Leech, whose root lattice has rank zero rather than finite
    /// index in the full lattice.
    pub fn glue_code_order(&self) -> Option<u128> {
        self.glue_code_order
    }

    /// The quotient `Aut(N)/W(R)`, i.e. the glue-preserving diagram automorphism
    /// factor `G1*G2` in Conway-Sloane's table.
    pub fn automorphism_quotient_order(&self) -> u128 {
        self.automorphism_quotient_order
    }

    pub fn root_rank(&self) -> usize {
        self.components
            .iter()
            .map(|c| c.kind.rank() * c.multiplicity)
            .sum()
    }

    pub fn root_count(&self) -> u128 {
        let mut out = 0u128;
        for component in self.components {
            let term = component
                .kind
                .root_count()
                .checked_mul(component.multiplicity as u128)
                .expect("root count exceeds u128");
            out = out.checked_add(term).expect("root count exceeds u128");
        }
        out
    }

    pub fn root_discriminant(&self) -> Option<u128> {
        if self.components.is_empty() {
            return None;
        }
        let mut out = 1u128;
        for component in self.components {
            for _ in 0..component.multiplicity {
                out = out.checked_mul(component.kind.determinant())?;
            }
        }
        Some(out)
    }

    pub fn reflection_group_order(&self) -> Option<u128> {
        let mut out = 1u128;
        for component in self.components {
            for _ in 0..component.multiplicity {
                out = out.checked_mul(component.kind.weyl_group_order()?)?;
            }
        }
        Some(out)
    }

    pub fn automorphism_group_order(&self) -> Option<u128> {
        if self.components.is_empty() {
            return Some(super::LEECH_AUT_ORDER);
        }
        self.reflection_group_order()?
            .checked_mul(self.automorphism_quotient_order)
    }

    /// The root sublattice `R`, not the full glued Niemeier overlattice.
    pub fn root_lattice(&self) -> Option<IntegralForm> {
        let mut out: Option<IntegralForm> = None;
        for component in self.components {
            for _ in 0..component.multiplicity {
                let lattice = component.kind.root_lattice();
                out = Some(match out {
                    Some(acc) => acc.direct_sum(&lattice),
                    None => lattice,
                });
            }
        }
        out
    }

    /// The scalar theta series of the rank-24 Niemeier lattice, using Venkov's
    /// weight-12 formula `theta_N = E4^3 + (#roots - 720) Delta`.
    pub fn theta_series(&self, terms: usize) -> Vec<Rational> {
        let e4 = eisenstein_e4(terms);
        let e4_cubed = modular_qexp_mul(&modular_qexp_mul(&e4, &e4, terms), &e4, terms);
        modular_qexp_add(
            &e4_cubed,
            &modular_qexp_scale(
                &delta(terms),
                Rational::from_int(self.root_count() as i128 - 720),
                terms,
            ),
            terms,
        )
    }
}

const fn c(kind: NiemeierComponentKind, multiplicity: usize) -> NiemeierRootComponent {
    NiemeierRootComponent { kind, multiplicity }
}

const LEECH: [NiemeierRootComponent; 0] = [];
const A1_24: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::A(1), 24)];
const A2_12: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::A(2), 12)];
const A3_8: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::A(3), 8)];
const A4_6: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::A(4), 6)];
const A5_4_D4: [NiemeierRootComponent; 2] = [
    c(NiemeierComponentKind::A(5), 4),
    c(NiemeierComponentKind::D(4), 1),
];
const D4_6: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::D(4), 6)];
const A6_4: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::A(6), 4)];
const A7_2_D5_2: [NiemeierRootComponent; 2] = [
    c(NiemeierComponentKind::A(7), 2),
    c(NiemeierComponentKind::D(5), 2),
];
const A8_3: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::A(8), 3)];
const A9_2_D6: [NiemeierRootComponent; 2] = [
    c(NiemeierComponentKind::A(9), 2),
    c(NiemeierComponentKind::D(6), 1),
];
const D6_4: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::D(6), 4)];
const E6_4: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::E(6), 4)];
const A11_D7_E6: [NiemeierRootComponent; 3] = [
    c(NiemeierComponentKind::A(11), 1),
    c(NiemeierComponentKind::D(7), 1),
    c(NiemeierComponentKind::E(6), 1),
];
const A12_2: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::A(12), 2)];
const D8_3: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::D(8), 3)];
const A15_D9: [NiemeierRootComponent; 2] = [
    c(NiemeierComponentKind::A(15), 1),
    c(NiemeierComponentKind::D(9), 1),
];
const A17_E7: [NiemeierRootComponent; 2] = [
    c(NiemeierComponentKind::A(17), 1),
    c(NiemeierComponentKind::E(7), 1),
];
const D10_E7_2: [NiemeierRootComponent; 2] = [
    c(NiemeierComponentKind::D(10), 1),
    c(NiemeierComponentKind::E(7), 2),
];
const D12_2: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::D(12), 2)];
const A24: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::A(24), 1)];
const D16_E8: [NiemeierRootComponent; 2] = [
    c(NiemeierComponentKind::D(16), 1),
    c(NiemeierComponentKind::E(8), 1),
];
const E8_3: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::E(8), 3)];
const D24: [NiemeierRootComponent; 1] = [c(NiemeierComponentKind::D(24), 1)];

/// The 24 Niemeier classes in Conway-Sloane table order.
pub const NIEMEIER_CLASSES: [NiemeierClass; 24] = [
    NiemeierClass {
        label: "Leech",
        components: &LEECH,
        coxeter_number: 0,
        glue_code_order: None,
        automorphism_quotient_order: 1,
    },
    NiemeierClass {
        label: "A_1^24",
        components: &A1_24,
        coxeter_number: 2,
        glue_code_order: Some(4_096),
        automorphism_quotient_order: 244_823_040,
    },
    NiemeierClass {
        label: "A_2^12",
        components: &A2_12,
        coxeter_number: 3,
        glue_code_order: Some(729),
        automorphism_quotient_order: 190_080,
    },
    NiemeierClass {
        label: "A_3^8",
        components: &A3_8,
        coxeter_number: 4,
        glue_code_order: Some(256),
        automorphism_quotient_order: 2_688,
    },
    NiemeierClass {
        label: "A_4^6",
        components: &A4_6,
        coxeter_number: 5,
        glue_code_order: Some(125),
        automorphism_quotient_order: 240,
    },
    NiemeierClass {
        label: "A_5^4 D_4",
        components: &A5_4_D4,
        coxeter_number: 6,
        glue_code_order: Some(72),
        automorphism_quotient_order: 48,
    },
    NiemeierClass {
        label: "D_4^6",
        components: &D4_6,
        coxeter_number: 6,
        glue_code_order: Some(64),
        automorphism_quotient_order: 2_160,
    },
    NiemeierClass {
        label: "A_6^4",
        components: &A6_4,
        coxeter_number: 7,
        glue_code_order: Some(49),
        automorphism_quotient_order: 24,
    },
    NiemeierClass {
        label: "A_7^2 D_5^2",
        components: &A7_2_D5_2,
        coxeter_number: 8,
        glue_code_order: Some(32),
        automorphism_quotient_order: 8,
    },
    NiemeierClass {
        label: "A_8^3",
        components: &A8_3,
        coxeter_number: 9,
        glue_code_order: Some(27),
        automorphism_quotient_order: 12,
    },
    NiemeierClass {
        label: "A_9^2 D_6",
        components: &A9_2_D6,
        coxeter_number: 10,
        glue_code_order: Some(20),
        automorphism_quotient_order: 4,
    },
    NiemeierClass {
        label: "D_6^4",
        components: &D6_4,
        coxeter_number: 10,
        glue_code_order: Some(16),
        automorphism_quotient_order: 24,
    },
    NiemeierClass {
        label: "E_6^4",
        components: &E6_4,
        coxeter_number: 12,
        glue_code_order: Some(9),
        automorphism_quotient_order: 48,
    },
    NiemeierClass {
        label: "A_11 D_7 E_6",
        components: &A11_D7_E6,
        coxeter_number: 12,
        glue_code_order: Some(12),
        automorphism_quotient_order: 2,
    },
    NiemeierClass {
        label: "A_12^2",
        components: &A12_2,
        coxeter_number: 13,
        glue_code_order: Some(13),
        automorphism_quotient_order: 4,
    },
    NiemeierClass {
        label: "D_8^3",
        components: &D8_3,
        coxeter_number: 14,
        glue_code_order: Some(8),
        automorphism_quotient_order: 6,
    },
    NiemeierClass {
        label: "A_15 D_9",
        components: &A15_D9,
        coxeter_number: 16,
        glue_code_order: Some(8),
        automorphism_quotient_order: 2,
    },
    NiemeierClass {
        label: "A_17 E_7",
        components: &A17_E7,
        coxeter_number: 18,
        glue_code_order: Some(6),
        automorphism_quotient_order: 2,
    },
    NiemeierClass {
        label: "D_10 E_7^2",
        components: &D10_E7_2,
        coxeter_number: 18,
        glue_code_order: Some(4),
        automorphism_quotient_order: 2,
    },
    NiemeierClass {
        label: "D_12^2",
        components: &D12_2,
        coxeter_number: 22,
        glue_code_order: Some(4),
        automorphism_quotient_order: 2,
    },
    NiemeierClass {
        label: "A_24",
        components: &A24,
        coxeter_number: 25,
        glue_code_order: Some(5),
        automorphism_quotient_order: 2,
    },
    NiemeierClass {
        label: "D_16 E_8",
        components: &D16_E8,
        coxeter_number: 30,
        glue_code_order: Some(2),
        automorphism_quotient_order: 1,
    },
    NiemeierClass {
        label: "E_8^3",
        components: &E8_3,
        coxeter_number: 30,
        glue_code_order: Some(1),
        automorphism_quotient_order: 6,
    },
    NiemeierClass {
        label: "D_24",
        components: &D24,
        coxeter_number: 46,
        glue_code_order: Some(2),
        automorphism_quotient_order: 1,
    },
];

pub fn niemeier_classes() -> &'static [NiemeierClass] {
    &NIEMEIER_CLASSES
}

pub fn niemeier_mass_sum() -> Option<Rational> {
    let mut out = Rational::zero();
    for class in niemeier_classes() {
        out = out.add(&Rational::new(
            1,
            i128::try_from(class.automorphism_group_order()?).ok()?,
        ));
    }
    Some(out)
}

pub fn niemeier_weighted_theta_average(terms: usize) -> Option<Vec<Rational>> {
    let (mass_num, mass_den) = mass_even_unimodular(24)?;
    let mass_inv = Rational::new(mass_den, mass_num);
    let mut out = vec![Rational::zero(); terms];
    for class in niemeier_classes() {
        let aut = i128::try_from(class.automorphism_group_order()?).ok()?;
        let scale = Rational::new(1, aut);
        for (dst, coeff) in out.iter_mut().zip(class.theta_series(terms)) {
            *dst = dst.add(&coeff.mul(&scale));
        }
    }
    for coeff in &mut out {
        *coeff = coeff.mul(&mass_inv);
    }
    Some(out)
}

fn checked_pow2(n: usize) -> Option<u128> {
    if n >= 128 {
        None
    } else {
        Some(1u128 << n)
    }
}

fn checked_factorial(n: usize) -> Option<u128> {
    let mut out = 1u128;
    for k in 2..=n {
        out = out.checked_mul(k as u128)?;
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::forms::{eisenstein_e12, qexp_from_int};
    use std::collections::BTreeSet;

    #[test]
    fn niemeier_catalogue_has_the_24_classes() {
        assert_eq!(niemeier_classes().len(), 24);
        let mut labels = BTreeSet::new();
        for class in niemeier_classes() {
            assert!(labels.insert(class.label()), "duplicate {}", class.label());
            if class.label() == "Leech" {
                assert_eq!(class.root_rank(), 0);
                assert_eq!(class.root_count(), 0);
                assert_eq!(class.glue_code_order(), None);
            } else {
                assert_eq!(class.root_rank(), 24, "{}", class.label());
                assert_eq!(
                    class.root_count(),
                    24 * class.coxeter_number(),
                    "{}",
                    class.label()
                );
                let glue = class.glue_code_order().unwrap();
                assert_eq!(
                    class.root_discriminant(),
                    Some(glue * glue),
                    "{}",
                    class.label()
                );
                for component in class.components() {
                    assert_eq!(
                        component.kind.coxeter_number(),
                        class.coxeter_number(),
                        "{}",
                        class.label()
                    );
                }
            }
        }
    }

    #[test]
    fn root_lattice_constructors_match_catalogue_data() {
        for class in niemeier_classes()
            .iter()
            .filter(|class| class.label() != "Leech")
        {
            let root = class.root_lattice().unwrap();
            assert_eq!(root.dim(), class.root_rank(), "{}", class.label());
            assert_eq!(
                root.determinant(),
                class.root_discriminant().unwrap() as i128,
                "{}",
                class.label()
            );
        }
    }

    #[test]
    fn automorphism_orders_match_the_known_anchor_cases() {
        let by_label = |label: &str| {
            niemeier_classes()
                .iter()
                .find(|class| class.label() == label)
                .unwrap()
        };
        assert_eq!(
            by_label("Leech").automorphism_group_order(),
            Some(super::super::LEECH_AUT_ORDER)
        );
        assert_eq!(
            by_label("A_1^24").automorphism_group_order(),
            2u128.pow(24).checked_mul(244_823_040)
        );
        assert_eq!(
            by_label("E_8^3").automorphism_group_order(),
            root_lattices::E8_WEYL_GROUP_ORDER
                .checked_mul(root_lattices::E8_WEYL_GROUP_ORDER)
                .and_then(|x| x.checked_mul(root_lattices::E8_WEYL_GROUP_ORDER))
                .and_then(|x| x.checked_mul(6))
        );
    }

    #[test]
    fn niemeier_theta_series_are_pinned_by_root_counts() {
        let leech = niemeier_classes()[0];
        assert_eq!(leech.theta_series(2), qexp_from_int(&[1, 0]));
        let d24 = niemeier_classes().last().unwrap();
        assert_eq!(d24.theta_series(2), qexp_from_int(&[1, 1_104]));
    }

    #[test]
    fn niemeier_mass_sum_is_the_rank24_mass() {
        let (num, den) = mass_even_unimodular(24).unwrap();
        assert_eq!(niemeier_mass_sum(), Some(Rational::new(num, den)));
    }

    #[test]
    fn niemeier_siegel_weil_average_is_e12() {
        let terms = 4;
        assert_eq!(
            niemeier_weighted_theta_average(terms),
            Some(eisenstein_e12(terms))
        );
    }
}
