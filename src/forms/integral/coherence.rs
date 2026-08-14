//! End-to-end coherence tests across the integral, Clifford, Witt, Brown, and
//! signature surfaces.  These tests deliberately start from one lattice and
//! ask independently implemented classifiers to recover the same invariants.

use crate::forms::{
    arf_nimber, bw_class_nimber, bw_class_rational, classify_rational, clifford_brauer_class,
    double_f2, extraspecial_group_nimber, genus_signature_mod8, hasse_brauer_class,
    rational_signed_discriminant_class, try_square_free, verify_milgram, BrauerWallClass,
    DiscriminantForm, ExtraspecialType, IntegralForm, Place,
};
use crate::scalar::{Nimber, Rational, Scalar};
use std::collections::BTreeSet;

fn a_n(n: usize) -> IntegralForm {
    crate::forms::a_n(n).expect("coherence zoo uses an in-domain A_n rank")
}

fn d_n(n: usize) -> IntegralForm {
    crate::forms::d_n(n).expect("coherence zoo uses an in-domain D_n rank")
}

fn rational_square_class(x: &Rational) -> i128 {
    try_square_free(
        x.numer()
            .checked_mul(x.denom())
            .expect("coherence zoo square classes fit i128"),
    )
    .expect("coherence zoo square-free reduction fits i128")
}

fn rational_diagonal_square_classes(lattice: &IntegralForm) -> Vec<i128> {
    crate::forms::as_diagonal(&lattice.clifford_metric())
        .expect("a rational symmetric metric diagonalizes")
        .q
        .iter()
        .filter(|x| !x.is_zero())
        .map(rational_square_class)
        .collect()
}

fn metric_f2_data(metric: &crate::clifford::Metric<Nimber>) -> (Vec<bool>, Vec<u128>) {
    let qd = metric.q().iter().map(|x| x.0 == 1).collect::<Vec<_>>();
    let mut bmat = vec![0u128; metric.dim()];
    for (&(i, j), value) in metric.b() {
        if value.0 == 1 {
            bmat[i] |= 1u128 << j;
            bmat[j] |= 1u128 << i;
        }
    }
    (qd, bmat)
}

#[test]
fn lattice_rational_clifford_brauer_and_signature_spine_commutes() {
    let zoo = [
        IntegralForm::diagonal(&[1]),
        IntegralForm::diagonal(&[3, -5]),
        IntegralForm::new(vec![vec![0, 1], vec![1, 0]]).unwrap(),
        a_n(2),
        a_n(3),
        d_n(4),
        crate::forms::e_6(),
        crate::forms::e_7(),
        crate::forms::e_8(),
    ];

    for lattice in zoo {
        let metric = lattice.clifford_metric();
        let classified = classify_rational(&metric).expect("zoo metric is classifiable over Q");
        let entries = rational_diagonal_square_classes(&lattice);
        let bw = bw_class_rational(&metric).expect("zoo metric has a Brauer-Wall class");

        assert_eq!(classified.dim, lattice.dim());
        assert_eq!(classified.radical_dim, 0);
        assert_eq!(classified.signature, lattice.signature());
        assert_eq!(
            classified.discriminant,
            try_square_free(lattice.determinant()).unwrap()
        );

        let hasse_places: BTreeSet<Place> = classified
            .local_hasse
            .iter()
            .filter_map(|x| (x.hasse == -1).then_some(x.place))
            .collect();
        assert_eq!(
            hasse_places,
            hasse_brauer_class(&entries)
                .expect("nondegenerate rational form")
                .ramified_places()
                .clone(),
        );
        assert_eq!(bw.dimension_parity(), (lattice.dim() % 2) as u128);
        assert_eq!(
            bw.signed_discriminant(),
            rational_signed_discriminant_class(&entries).unwrap()
        );
        assert_eq!(
            bw.clifford_brauer_class(),
            &clifford_brauer_class(&entries).unwrap()
        );

        let (positive, negative) = lattice.signature();
        let bott = (negative as i128 - positive as i128).rem_euclid(8) as u128;
        assert_eq!(bw.real_bott_index(), bott);
        assert_eq!(bw.real_class(), BrauerWallClass::Real(bott));
        assert_eq!(classified.real_closure.signature, (positive, negative));
    }
}

#[test]
fn even_lattice_discriminant_weil_brown_and_signature_spine_commutes() {
    let zoo = [
        a_n(1),
        a_n(2),
        a_n(3),
        d_n(4),
        d_n(8),
        crate::forms::e_6(),
        crate::forms::e_7(),
        crate::forms::e_8(),
    ];

    for lattice in zoo {
        let disc = DiscriminantForm::from_lattice(&lattice).expect("zoo lattice is even");
        let (positive, negative) = lattice.signature();
        let signature_mod8 = (positive as i128 - negative as i128).rem_euclid(8);

        assert_eq!(disc.milgram_signature_mod8_fqm(), Some(signature_mod8));
        assert_eq!(disc.milgram_signature_mod8(), Some(signature_mod8));
        assert_eq!(genus_signature_mod8(&lattice), Some(signature_mod8));
        assert_eq!(
            disc.weil_s_prefactor_phase_mod8(),
            Some((-signature_mod8).rem_euclid(8))
        );
        assert_eq!(
            disc.weil_s_recovers_milgram_phase_mod8(),
            Some(signature_mod8)
        );
        assert!(disc.verify_weil_relations());
        assert_eq!(verify_milgram(&lattice), Some(true));

        if disc.group().iter().all(|&d| d == 2) {
            assert_eq!(
                disc.brown_invariant().map(|x| x.beta),
                Some(signature_mod8 as u128),
            );
        } else {
            assert_eq!(disc.brown_invariant(), None);
        }
    }
}

#[test]
fn lattice_mod_two_arf_brown_witt_and_extraspecial_bridges_commute() {
    let zoo = [
        IntegralForm::new(vec![vec![0, 1], vec![1, 0]]).unwrap(),
        a_n(1),
        a_n(2),
        d_n(4),
    ];

    for lattice in zoo {
        let metric = lattice
            .clifford_metric_f2()
            .expect("coherence zoo contains only even lattices");
        let arf = arf_nimber(&metric).expect("lattice reduction is a pure F2 metric");
        let (qd, bmat) = metric_f2_data(&metric);
        let brown = double_f2(&qd, &bmat);

        assert_eq!(brown.beta, 4 * arf.arf);
        assert_eq!(brown.rank, arf.rank);
        assert_eq!(brown.radical_dim, arf.radical_dim);
        assert_eq!(brown.radical_anisotropic, arf.radical_anisotropic);

        if arf.radical_dim == 0 && arf.rank == metric.dim() && metric.dim() > 0 {
            assert_eq!(
                bw_class_nimber(&metric),
                Some(BrauerWallClass::Char2 {
                    field_degree: 1,
                    arf: arf.arf,
                })
            );
            let group = extraspecial_group_nimber(&metric).expect("nonsingular F2 metric");
            assert_eq!(
                group.extraspecial_type(),
                if arf.arf == 0 {
                    ExtraspecialType::Plus
                } else {
                    ExtraspecialType::Minus
                }
            );
        } else {
            assert_eq!(bw_class_nimber(&metric), None);
            assert!(extraspecial_group_nimber(&metric).is_err());
        }
    }

    assert!(IntegralForm::diagonal(&[1]).clifford_metric_f2().is_none());
}
