use ogdoad::scalar::{Fp, Nimber, Rational, Scalar};
use ogdoad::weyl::{
    WeylAlgebra, WeylCenterError, WeylCenterGeneratorKind, WeylFiberError, WeylRepresentationBudget,
};
use proptest::prelude::*;

mod common;
use common::proptest_config;

type F3 = Fp<3>;

const CASES: u32 = 24;

fn f3(value: i128) -> F3 {
    F3::from_int(value)
}

fn r(value: i128) -> Rational {
    Rational::from_int(value)
}

fn small_budget() -> WeylRepresentationBudget {
    WeylRepresentationBudget::new(256, 100_000, 20_000_000)
}

fn matrix_mul<S: Scalar>(left: &[Vec<S>], right: &[Vec<S>]) -> Vec<Vec<S>> {
    let dim = left.len();
    let mut product = vec![vec![S::zero(); dim]; dim];
    for row in 0..dim {
        for column in 0..dim {
            for inner in 0..dim {
                product[row][column] =
                    product[row][column].add(&left[row][inner].mul(&right[inner][column]));
            }
        }
    }
    product
}

#[test]
fn positive_characteristic_center_is_certified_in_source_coordinates() {
    let algebra = WeylAlgebra::from_commutator(vec![
        vec![f3(0), f3(1), f3(1)],
        vec![f3(-1), f3(0), f3(2)],
        vec![f3(-1), f3(-2), f3(0)],
    ])
    .unwrap();
    let center = algebra.positive_characteristic_center().unwrap();
    assert_eq!(center.characteristic(), 3);
    assert_eq!(center.decomposition().weyl_rank(), 1);
    assert_eq!(center.decomposition().central_rank(), 1);
    assert_eq!(center.generators().len(), 3);
    assert!(matches!(
        center.generators()[0].kind(),
        WeylCenterGeneratorKind::CharacteristicPower {
            normal_generator: 0,
            characteristic: 3,
        }
    ));
    assert!(matches!(
        center.generators()[2].kind(),
        WeylCenterGeneratorKind::Radical {
            radical_index: 0,
            normal_generator: 2,
        }
    ));
    for generator in center.generators() {
        assert!(algebra.is_central(generator.source_element()).unwrap());
    }
    assert_eq!(center.basis_over_center().rank_over_center(), Some(9));
    assert_eq!(
        center
            .basis_over_center()
            .materialize_source_with_budget(8, ogdoad::weyl::WeylExpansionBudget::unbounded(),)
            .unwrap_err(),
        WeylCenterError::BasisMaterializationLimit {
            required: Some(9),
            limit: 8,
        }
    );
    let basis = center
        .basis_over_center()
        .materialize_source_with_budget(9, ogdoad::weyl::WeylExpansionBudget::unbounded())
        .unwrap();
    assert_eq!(basis.len(), 9);
}

#[test]
fn radical_generators_remain_available_in_characteristic_zero() {
    let algebra = WeylAlgebra::from_commutator(vec![
        vec![r(0), r(2), r(0)],
        vec![r(-2), r(0), r(0)],
        vec![r(0), r(0), r(0)],
    ])
    .unwrap();
    let radicals = algebra.radical_generators().unwrap();
    assert_eq!(radicals.len(), 1);
    assert!(algebra.is_central(&radicals[0]).unwrap());
    assert_eq!(
        algebra.positive_characteristic_center().unwrap_err(),
        WeylCenterError::RequiresPositiveCharacteristic
    );
    assert!(!algebra.is_central(&algebra.generator(0)).unwrap());
}

#[test]
fn central_fiber_reduction_is_a_product_map() {
    let algebra = WeylAlgebra::<F3>::standard(1);
    let fiber = algebra
        .central_fiber(vec![f3(2), f3(1)], small_budget())
        .unwrap();
    assert_eq!(fiber.basis_dimension(), 9);
    assert_eq!(
        fiber.reduce(&algebra.pow(&algebra.x(0), 3)).unwrap(),
        fiber.reduce(&algebra.scalar(f3(2))).unwrap()
    );
    assert_eq!(
        fiber.reduce(&algebra.pow(&algebra.d(0), 3)).unwrap(),
        fiber.one()
    );

    let left = algebra.monomial(&[5, 2], f3(2)) + algebra.d(0);
    let right = algebra.monomial(&[1, 4], f3(1)) + algebra.x(0);
    let reduced_product = fiber.reduce(&algebra.mul(&left, &right)).unwrap();
    assert_eq!(
        reduced_product,
        fiber
            .checked_mul(
                &fiber.reduce(&left).unwrap(),
                &fiber.reduce(&right).unwrap()
            )
            .unwrap()
    );
    assert_eq!(
        fiber.lift(&fiber.reduce(&left).unwrap()).unwrap(),
        algebra.monomial(&[2, 2], f3(1)) + algebra.d(0)
    );
}

#[test]
fn split_central_character_module_has_exact_action_matrices() {
    let algebra = WeylAlgebra::<F3>::standard(1);
    // Frobenius is the identity on F_3, so values are their own p-th roots.
    let module = algebra
        .split_central_character_module(vec![f3(2), f3(1)], vec![f3(2), f3(1)], small_budget())
        .unwrap();
    assert_eq!(module.basis_dimension(), 3);
    assert!(module.verifies_defining_relations(small_budget()).unwrap());
    assert_eq!(module.basis_exponents(0), Some(vec![0]));
    assert_eq!(module.basis_exponents(2), Some(vec![2]));

    let left = algebra.pow(&(algebra.x(0) + algebra.d(0)), 2);
    let right = algebra.monomial(&[2, 1], f3(2)) + algebra.one();
    let product_matrix = module
        .action_matrix(&algebra.mul(&left, &right), small_budget())
        .unwrap();
    assert_eq!(
        product_matrix,
        matrix_mul(
            &module.action_matrix(&left, small_budget()).unwrap(),
            &module.action_matrix(&right, small_budget()).unwrap(),
        )
    );
}

#[test]
fn odd_characteristic_fiber_gets_full_matrix_certificate() {
    let algebra = WeylAlgebra::<F3>::standard(1);
    let certificate = algebra
        .odd_matrix_fiber_certificate(vec![f3(2), f3(1)], vec![f3(2), f3(1)], small_budget())
        .unwrap();
    assert_eq!(certificate.matrix_dimension(), 3);
    assert_eq!(certificate.algebra_dimension(), 9);
    assert_eq!(certificate.image_rank(), 9);
}

#[test]
fn rank_zero_fibres_are_the_scalar_algebra() {
    let odd = WeylAlgebra::<F3>::standard(0);
    let odd_fiber = odd.central_fiber(vec![], small_budget()).unwrap();
    assert_eq!(odd_fiber.basis_dimension(), 1);
    assert_eq!(odd_fiber.basis_element(0).unwrap().coefficients(), &[f3(1)]);
    assert_eq!(
        odd_fiber.reduce(&odd.scalar(f3(2))).unwrap().coefficients(),
        &[f3(2)]
    );

    let module = odd
        .split_central_character_module(vec![], vec![], small_budget())
        .unwrap();
    assert_eq!(module.basis_dimension(), 1);
    assert_eq!(
        module
            .action_matrix(&odd.scalar(f3(2)), small_budget())
            .unwrap(),
        vec![vec![f3(2)]]
    );

    let certificate = odd
        .odd_matrix_fiber_certificate(vec![], vec![], small_budget())
        .unwrap();
    assert_eq!(certificate.matrix_dimension(), 1);
    assert_eq!(certificate.algebra_dimension(), 1);
    assert_eq!(certificate.image_rank(), 1);

    let characteristic_two = WeylAlgebra::<Nimber>::standard(0);
    let bridge = characteristic_two
        .clifford_central_fiber(vec![], small_budget())
        .unwrap();
    assert_eq!(bridge.fiber().basis_dimension(), 1);
    assert!(bridge
        .products_agree(
            &characteristic_two.scalar(Nimber(7)),
            &characteristic_two.scalar(Nimber(11)),
        )
        .unwrap());
}

#[test]
fn characteristic_two_fiber_is_the_matching_clifford_algebra() {
    let algebra = WeylAlgebra::<Nimber>::standard(2);
    let values = vec![Nimber(2), Nimber(3), Nimber(4), Nimber(5)];
    let bridge = algebra
        .clifford_central_fiber(values.clone(), small_budget())
        .unwrap();
    assert_eq!(bridge.fiber().basis_dimension(), 16);
    assert_eq!(bridge.clifford_algebra().metric().q(), values);
    assert_eq!(
        bridge.clifford_algebra().metric().b().get(&(0, 2)),
        Some(&Nimber(1))
    );

    for (generator, value) in values.iter().copied().enumerate() {
        let square = algebra.pow(&algebra.generator(generator), 2);
        assert_eq!(
            bridge.weyl_to_clifford(&square).unwrap(),
            bridge.clifford_algebra().scalar(value)
        );
    }
    let left = algebra.monomial(&[3, 1, 2, 1], Nimber(7)) + algebra.d(1);
    let right = algebra.monomial(&[0, 2, 1, 3], Nimber(11)) + algebra.x(0);
    assert!(bridge.products_agree(&left, &right).unwrap());

    let clifford = bridge.weyl_to_clifford(&left).unwrap();
    let canonical = bridge.clifford_to_weyl(&clifford).unwrap();
    assert_eq!(
        bridge.fiber().reduce(&canonical).unwrap(),
        bridge.fiber().reduce(&left).unwrap()
    );
}

#[test]
fn fibre_boundaries_are_explicit() {
    let rational = WeylAlgebra::<Rational>::standard(1);
    assert_eq!(
        rational
            .central_fiber(vec![r(0), r(0)], small_budget())
            .unwrap_err(),
        WeylFiberError::RequiresPositiveCharacteristic
    );

    let f3_algebra = WeylAlgebra::<F3>::standard(2);
    assert_eq!(
        f3_algebra
            .central_fiber(vec![f3(0); 4], WeylRepresentationBudget::new(10, 100, 100),)
            .unwrap_err(),
        WeylFiberError::BasisDimensionLimit {
            required: Some(81),
            limit: 10,
        }
    );
    assert_eq!(
        f3_algebra
            .split_central_character_module(
                vec![f3(0); 4],
                vec![f3(0), f3(0), f3(0), f3(1)],
                small_budget(),
            )
            .unwrap_err(),
        WeylFiberError::RootMismatch { generator: 3 }
    );

    let f3_rank_one = WeylAlgebra::<F3>::standard(1);
    let fiber = f3_rank_one
        .central_fiber(vec![f3(0); 2], small_budget())
        .unwrap();
    assert_eq!(
        fiber.basis_element(9).unwrap_err(),
        WeylFiberError::FiberBasisIndexOutOfRange {
            index: 9,
            dimension: 9,
        }
    );
    assert_eq!(
        f3_rank_one
            .split_central_character_module(
                vec![f3(0); 2],
                vec![f3(0); 2],
                WeylRepresentationBudget::new(9, 17, 20_000),
            )
            .unwrap_err(),
        WeylFiberError::MatrixEntryLimit {
            required: 18,
            limit: 17,
        }
    );
    assert_eq!(
        f3_rank_one
            .odd_matrix_fiber_certificate(
                vec![f3(0); 2],
                vec![f3(0); 2],
                WeylRepresentationBudget::new(9, 81, 1_500),
            )
            .unwrap_err(),
        WeylFiberError::StepBudgetExceeded { limit: 1_500 }
    );
}

proptest! {
    #![proptest_config(proptest_config(CASES))]

    #[test]
    fn characteristic_two_clifford_oracle_agrees_on_random_rank_one_products(
        values in prop::array::uniform2(any::<u8>()),
        left_exp in prop::array::uniform2(0u8..=7),
        right_exp in prop::array::uniform2(0u8..=7),
        coefficients in prop::array::uniform2(any::<u8>()),
    ) {
        let algebra = WeylAlgebra::<Nimber>::standard(1);
        let bridge = algebra.clifford_central_fiber(
            values.map(|value| Nimber(value as u128)).to_vec(),
            small_budget(),
        ).unwrap();
        let left = algebra.monomial(
            &left_exp.map(u128::from),
            Nimber(coefficients[0] as u128),
        );
        let right = algebra.monomial(
            &right_exp.map(u128::from),
            Nimber(coefficients[1] as u128),
        );
        prop_assert!(bridge.products_agree(&left, &right).unwrap());
    }

    #[test]
    fn central_reduction_preserves_random_f3_products(
        central_values in prop::array::uniform2(0u8..=2),
        left_exp in prop::array::uniform2(0u8..=7),
        right_exp in prop::array::uniform2(0u8..=7),
    ) {
        let algebra = WeylAlgebra::<F3>::standard(1);
        let fiber = algebra.central_fiber(
            central_values.map(|value| f3(value as i128)).to_vec(),
            small_budget(),
        ).unwrap();
        let left = algebra.monomial(&left_exp.map(u128::from), f3(1));
        let right = algebra.monomial(&right_exp.map(u128::from), f3(2));
        prop_assert_eq!(
            fiber.reduce(&algebra.mul(&left, &right)).unwrap(),
            fiber.checked_mul(
                &fiber.reduce(&left).unwrap(),
                &fiber.reduce(&right).unwrap(),
            ).unwrap(),
        );
    }
}
