//! ADE Weyl reflections realized by Clifford versors.
//!
//! A simply-laced root lattice has Gram matrix `G` with `G_ii = 2`. Feeding that
//! lattice into [`IntegralForm::clifford_metric`] makes each simple root a
//! grade-1 Clifford vector with square `2`, hence an invertible Pin versor. Its
//! twisted adjoint action is the root reflection
//!
//! ```text
//! s_i(e_j) = e_j - <e_j,e_i> e_i.
//! ```
//!
//! The report surface checks this action against the Cartan reflection matrix,
//! checks every simple reflection has determinant `-1` via the outermorphism
//! determinant, and forms the Coxeter versor `e_0 e_1 ... e_{n-1}` whose Pin
//! action has the expected Coxeter order.

use super::{IntegralForm, NiemeierComponentKind};
use crate::clifford::{determinant, versor_grade_parity, CliffordAlgebra, LinearMap, Multivector};
use crate::scalar::{Rational, Scalar};

/// The Clifford/Weyl report for one irreducible ADE component.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WeylVersorInvariants {
    pub kind: NiemeierComponentKind,
    pub rank: usize,
    pub weyl_group_order: u128,
    pub coxeter_number: u128,
    pub simple_reflections_match_cartan: bool,
    pub simple_reflection_determinants_are_minus_one: bool,
    pub coxeter_versor_order: u128,
    pub coxeter_order_matches: bool,
    pub coxeter_versor_grade_parity: Option<u128>,
}

fn r(n: i128) -> Rational {
    Rational::from_int(n)
}

fn rational_clifford(lattice: &IntegralForm) -> CliffordAlgebra<Rational> {
    let metric = lattice.clifford_metric();
    CliffordAlgebra::new(metric.q.len(), metric)
}

/// The simple-root versors `e_i` in the rational Clifford algebra of `lattice`.
pub fn weyl_simple_root_versors(lattice: &IntegralForm) -> Vec<Multivector<Rational>> {
    let alg = rational_clifford(lattice);
    (0..lattice.dim()).map(|i| alg.e(i)).collect()
}

/// The Cartan reflection matrix for the `i`-th simple root, as a grade-1
/// [`LinearMap`].
pub fn weyl_simple_reflection_map(lattice: &IntegralForm, i: usize) -> Option<LinearMap<Rational>> {
    let n = lattice.dim();
    if i >= n || lattice.gram()[i][i] != 2 {
        return None;
    }
    let mut cols = Vec::with_capacity(n);
    for j in 0..n {
        let mut col = vec![Rational::zero(); n];
        col[j] = Rational::one();
        col[i] = col[i].sub(&r(lattice.gram()[j][i]));
        cols.push(col);
    }
    Some(LinearMap::from_columns(cols))
}

/// All Cartan simple-reflection maps for `lattice`.
pub fn weyl_simple_reflection_maps(lattice: &IntegralForm) -> Option<Vec<LinearMap<Rational>>> {
    (0..lattice.dim())
        .map(|i| weyl_simple_reflection_map(lattice, i))
        .collect()
}

fn grade1_coords(
    alg: &CliffordAlgebra<Rational>,
    mv: &Multivector<Rational>,
) -> Option<Vec<Rational>> {
    let mut out = vec![Rational::zero(); alg.dim()];
    for (&mask, coeff) in mv.terms() {
        if mask == 0 || mask.count_ones() != 1 {
            return None;
        }
        let i = mask.trailing_zeros() as usize;
        if i >= alg.dim() {
            return None;
        }
        out[i] = coeff.clone();
    }
    Some(out)
}

/// The grade-1 linear map induced by the Pin twisted-adjoint action of `versor`.
pub fn weyl_versor_action_map(
    lattice: &IntegralForm,
    versor: &Multivector<Rational>,
) -> Option<LinearMap<Rational>> {
    let alg = rational_clifford(lattice);
    let mut cols = Vec::with_capacity(alg.dim());
    for i in 0..alg.dim() {
        let image = alg.twisted_sandwich(versor, &alg.e(i))?;
        cols.push(grade1_coords(&alg, &image)?);
    }
    Some(LinearMap::from_columns(cols))
}

fn simple_reflections_match_cartan(lattice: &IntegralForm) -> bool {
    let alg = rational_clifford(lattice);
    for i in 0..lattice.dim() {
        let Some(map) = weyl_simple_reflection_map(lattice, i) else {
            return false;
        };
        let versor = alg.e(i);
        for j in 0..lattice.dim() {
            let Some(image) = alg.reflect(&versor, &alg.e(j)) else {
                return false;
            };
            if image != map.image(&alg, j) {
                return false;
            }
        }
    }
    true
}

fn simple_reflection_determinants_are_minus_one(lattice: &IntegralForm) -> bool {
    let alg = rational_clifford(lattice);
    let Some(maps) = weyl_simple_reflection_maps(lattice) else {
        return false;
    };
    maps.iter().all(|f| determinant(&alg, f) == r(-1))
}

/// The Coxeter versor `e_0 e_1 ... e_{n-1}` for the simple-root order used by
/// the lattice constructor.
pub fn weyl_coxeter_versor(lattice: &IntegralForm) -> Option<Multivector<Rational>> {
    if lattice
        .gram()
        .iter()
        .enumerate()
        .any(|(i, row)| row[i] != 2)
    {
        return None;
    }
    let alg = rational_clifford(lattice);
    let mut out = alg.scalar(Rational::one());
    for i in 0..lattice.dim() {
        out = alg.mul(&out, &alg.e(i));
    }
    Some(out)
}

fn linear_map_order(map: &LinearMap<Rational>, max_order: u128) -> Option<u128> {
    let id = LinearMap::identity(map.n());
    let mut cur = id.clone();
    for k in 1..=max_order {
        cur = map.compose(&cur);
        if cur == id {
            return Some(k);
        }
    }
    None
}

/// The order of the Coxeter versor's Pin action, bounded by `max_order`.
pub fn weyl_coxeter_action_order(lattice: &IntegralForm, max_order: u128) -> Option<u128> {
    let c = weyl_coxeter_versor(lattice)?;
    let action = weyl_versor_action_map(lattice, &c)?;
    linear_map_order(&action, max_order)
}

/// Clifford-versor report for the irreducible ADE root component `kind`.
pub fn weyl_versor_report(kind: NiemeierComponentKind) -> Option<WeylVersorInvariants> {
    let lattice = kind.root_lattice()?;
    let coxeter_number = kind.coxeter_number()?;
    let coxeter_versor = weyl_coxeter_versor(&lattice)?;
    let coxeter_order = weyl_coxeter_action_order(&lattice, coxeter_number)?;
    Some(WeylVersorInvariants {
        kind,
        rank: kind.rank(),
        weyl_group_order: kind.weyl_group_order()?,
        coxeter_number,
        simple_reflections_match_cartan: simple_reflections_match_cartan(&lattice),
        simple_reflection_determinants_are_minus_one: simple_reflection_determinants_are_minus_one(
            &lattice,
        ),
        coxeter_versor_order: coxeter_order,
        coxeter_order_matches: coxeter_order == coxeter_number,
        coxeter_versor_grade_parity: versor_grade_parity(&coxeter_versor),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::forms::E8_WEYL_GROUP_ORDER;

    #[test]
    fn a2_simple_roots_act_as_cartan_reflections() {
        let report = weyl_versor_report(NiemeierComponentKind::A(2)).unwrap();
        assert_eq!(report.rank, 2);
        assert_eq!(report.weyl_group_order, 6);
        assert_eq!(report.coxeter_number, 3);
        assert!(report.simple_reflections_match_cartan);
        assert!(report.simple_reflection_determinants_are_minus_one);
        assert_eq!(report.coxeter_versor_order, 3);
        assert!(report.coxeter_order_matches);
        assert_eq!(report.coxeter_versor_grade_parity, Some(0));
    }

    #[test]
    fn d4_report_uses_weyl_order_not_full_diagram_automorphisms() {
        let report = weyl_versor_report(NiemeierComponentKind::D(4)).unwrap();
        assert_eq!(report.weyl_group_order, 192);
        assert_eq!(report.coxeter_number, 6);
        assert_eq!(report.coxeter_versor_order, 6);
        assert!(report.simple_reflections_match_cartan);
    }

    #[test]
    fn e8_coxeter_versor_has_order_30() {
        let report = weyl_versor_report(NiemeierComponentKind::E8).unwrap();
        assert_eq!(report.weyl_group_order, E8_WEYL_GROUP_ORDER);
        assert_eq!(report.coxeter_number, 30);
        assert_eq!(report.coxeter_versor_order, 30);
        assert!(report.coxeter_order_matches);
        assert!(report.simple_reflection_determinants_are_minus_one);
    }

    /// Sweeps past the `A_2`/`D_4`/`E_8` spot checks above: `E_6`/`E_7` plus a
    /// couple more `A_n`/`D_n` ranks, pinned against the standard Coxeter-number
    /// formulas `h(E_6) = 12`, `h(E_7) = 18`, `h(A_n) = n+1`, `h(D_n) = 2(n-1)`.
    #[test]
    fn e6_e7_and_more_ade_ranks_match_standard_coxeter_numbers() {
        let e6 = weyl_versor_report(NiemeierComponentKind::E6).unwrap();
        assert_eq!(e6.coxeter_number, 12);
        assert_eq!(e6.coxeter_versor_order, 12);
        assert!(e6.coxeter_order_matches);
        assert!(e6.simple_reflections_match_cartan);
        assert!(e6.simple_reflection_determinants_are_minus_one);

        let e7 = weyl_versor_report(NiemeierComponentKind::E7).unwrap();
        assert_eq!(e7.coxeter_number, 18);
        assert_eq!(e7.coxeter_versor_order, 18);
        assert!(e7.coxeter_order_matches);
        assert!(e7.simple_reflections_match_cartan);
        assert!(e7.simple_reflection_determinants_are_minus_one);

        for n in [3usize, 5] {
            let report = weyl_versor_report(NiemeierComponentKind::A(n)).unwrap();
            let h = n as u128 + 1;
            assert_eq!(report.coxeter_number, h, "A_{n} Coxeter number");
            assert_eq!(report.coxeter_versor_order, h);
            assert!(report.coxeter_order_matches);
            assert!(report.simple_reflections_match_cartan);
            assert!(report.simple_reflection_determinants_are_minus_one);
        }

        for n in [5usize, 6] {
            let report = weyl_versor_report(NiemeierComponentKind::D(n)).unwrap();
            let h = 2 * (n as u128 - 1);
            assert_eq!(report.coxeter_number, h, "D_{n} Coxeter number");
            assert_eq!(report.coxeter_versor_order, h);
            assert!(report.coxeter_order_matches);
            assert!(report.simple_reflections_match_cartan);
        }
    }
}
