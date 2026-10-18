use ogdoad::scalar::{Fp, Nimber, Poly, Rational, Scalar};
use ogdoad::weyl::{
    SparsePolynomial, WeylAlgebra, WeylError, WeylExpansionBudget, WeylFiltration, WeylHomomorphism,
};
use proptest::prelude::*;

mod common;
use common::proptest_config;

const CASES: u32 = 24;

fn r(value: i128) -> Rational {
    Rational::from_int(value)
}

#[test]
fn darboux_tensor_decomposition_round_trips_and_exposes_the_radical() {
    let algebra = WeylAlgebra::from_commutator(vec![
        vec![r(0), r(2), r(3)],
        vec![r(-2), r(0), r(5)],
        vec![r(-3), r(-5), r(0)],
    ])
    .unwrap();
    let decomposition = algebra.darboux_decomposition().unwrap();
    assert_eq!(
        (decomposition.weyl_rank(), decomposition.central_rank()),
        (1, 1)
    );
    assert!(decomposition.certificate().verifies(
        &ogdoad::forms::SymplecticForm::from_gram(algebra.commutator_form().to_vec()).unwrap()
    ));

    let value =
        algebra.pow(&(algebra.generator(0) + algebra.generator(2)), 2) + algebra.scalar(r(7));
    let normal = decomposition.to_normal(&value).unwrap();
    assert_eq!(decomposition.from_normal(&normal).unwrap(), value);

    let other = algebra.generator(1) + algebra.monomial(&[1, 0, 1], r(-2));
    assert_eq!(
        decomposition
            .to_normal(&algebra.mul(&value, &other))
            .unwrap(),
        decomposition.normal_algebra().mul(
            &decomposition.to_normal(&value).unwrap(),
            &decomposition.to_normal(&other).unwrap(),
        )
    );

    let central = decomposition.central_generator(0).unwrap();
    for generator in 0..decomposition.normal_algebra().dim() {
        assert!(decomposition
            .normal_algebra()
            .commutator(
                &central,
                &decomposition.normal_algebra().generator(generator),
            )
            .is_zero());
    }
    let monomial = decomposition.normal_algebra().monomial(&[2, 3, 5], r(1));
    let (weyl, polynomial) = decomposition
        .split_monomial(monomial.terms().keys().next().unwrap())
        .unwrap();
    assert_eq!(weyl, &[2, 3]);
    assert_eq!(polynomial, &[5]);
}

#[test]
fn standard_automorphisms_preserve_products_and_round_trip() {
    let algebra = WeylAlgebra::<Rational>::standard(2);
    let left = algebra.pow(&(algebra.x(0) + algebra.d(1)), 2) + algebra.scalar(r(3));
    let right = algebra.mul(&algebra.d(0), &algebra.x(1)) - algebra.x(0);
    let product = algebra.mul(&left, &right);
    let automorphisms = vec![
        algebra.fourier_automorphism().unwrap(),
        algebra.scaling_automorphism(&[r(2), r(3)]).unwrap(),
        algebra
            .shear_automorphism(&[vec![r(1), r(2)], vec![r(2), r(-1)]])
            .unwrap(),
        algebra
            .translation_automorphism(&[r(2), r(-1), r(3), r(5)])
            .unwrap(),
        algebra.parity_automorphism().unwrap(),
    ];

    for automorphism in automorphisms {
        let mapped_left = automorphism.apply(&left).unwrap();
        let mapped_right = automorphism.apply(&right).unwrap();
        assert_eq!(
            automorphism.apply(&product).unwrap(),
            algebra.mul(&mapped_left, &mapped_right)
        );
        assert_eq!(automorphism.apply_inverse(&mapped_left).unwrap(), left);
        assert_eq!(automorphism.inverse().apply(&mapped_left).unwrap(), left);
    }

    let translation = algebra
        .translation_automorphism(&[r(1), r(0), r(0), r(0)])
        .unwrap();
    assert_eq!(
        translation.apply_with_budget(
            &algebra.pow(&algebra.x(0), 3),
            WeylExpansionBudget::new(2, 10_000),
        ),
        Err(WeylError::TermBudgetExceeded { limit: 2 })
    );
}

#[test]
fn transformation_validation_rejects_wrong_laws_and_parameters() {
    let algebra = WeylAlgebra::<Rational>::standard(1);
    let commutative = WeylAlgebra::from_commutator(vec![vec![r(0); 2]; 2]).unwrap();
    assert!(matches!(
        WeylHomomorphism::try_new(
            algebra.clone(),
            commutative,
            vec![vec![r(1), r(0)], vec![r(0), r(1)]],
            vec![r(0), r(0)],
        ),
        Err(WeylError::CommutatorNotPreserved { .. })
    ));
    assert_eq!(
        algebra.scaling_automorphism(&[r(0)]),
        Err(WeylError::NonUnitScale { index: 0 })
    );
    assert!(matches!(
        WeylAlgebra::<Rational>::standard(2)
            .shear_automorphism(&[vec![r(0), r(1)], vec![r(0), r(0)]]),
        Err(WeylError::ShearNotSymmetric { .. })
    ));
    assert_eq!(
        WeylAlgebra::<Rational>::standard(2).shear_automorphism(&[vec![r(0), r(0)]]),
        Err(WeylError::ShearRowCountMismatch {
            expected: 2,
            actual: 1,
        })
    );
}

#[test]
fn homomorphism_composition_direct_sum_and_embeddings_are_checked() {
    let algebra = WeylAlgebra::<Rational>::standard(1);
    let fourier = algebra.fourier_automorphism().unwrap();
    let translation = algebra.translation_automorphism(&[r(2), r(-3)]).unwrap();
    let composed = fourier.compose(&translation).unwrap();
    let value = algebra.pow(&(algebra.x(0) + algebra.d(0)), 3);
    assert_eq!(
        composed.apply(&value).unwrap(),
        fourier.apply(&translation.apply(&value).unwrap()).unwrap()
    );
    assert_eq!(
        composed
            .apply_inverse(&composed.apply(&value).unwrap())
            .unwrap(),
        value
    );

    let zero_line = WeylAlgebra::from_commutator(vec![vec![r(0)]]).unwrap();
    let left_embedding = WeylHomomorphism::left_direct_sum_embedding(&algebra, &zero_line).unwrap();
    let right_embedding =
        WeylHomomorphism::right_direct_sum_embedding(&algebra, &zero_line).unwrap();
    let target = left_embedding.target();
    let embedded_x = left_embedding.apply(&algebra.x(0)).unwrap();
    let embedded_c = right_embedding.apply(&zero_line.generator(0)).unwrap();
    assert!(target.commutator(&embedded_x, &embedded_c).is_zero());

    let summed = fourier
        .homomorphism()
        .direct_sum(&WeylHomomorphism::identity(&zero_line))
        .unwrap();
    assert_eq!(
        summed.apply(&embedded_x).unwrap(),
        left_embedding.apply(&algebra.d(0)).unwrap()
    );
}

#[test]
fn formal_adjoint_is_anti_multiplicative_and_involutive() {
    let algebra = WeylAlgebra::<Rational>::standard(2);
    let adjoint = algebra.formal_adjoint().unwrap();
    let left = algebra.x(0) + algebra.mul(&algebra.d(1), &algebra.x(1));
    let right = algebra.d(0) - algebra.pow(&algebra.x(1), 2);
    assert_eq!(
        adjoint.apply(&algebra.mul(&left, &right)).unwrap(),
        algebra.mul(
            &adjoint.apply(&right).unwrap(),
            &adjoint.apply(&left).unwrap(),
        )
    );
    assert_eq!(
        adjoint
            .inverse()
            .apply(&adjoint.apply(&left).unwrap())
            .unwrap(),
        left
    );
    let squared = adjoint.compose_anti(&adjoint).unwrap();
    assert_eq!(squared.apply(&left).unwrap(), left);
}

#[test]
fn characteristic_two_fourier_transform_keeps_the_scalar_sign_contract() {
    let algebra = WeylAlgebra::<Nimber>::standard(1);
    let fourier = algebra.fourier_automorphism().unwrap();
    assert_eq!(fourier.apply(&algebra.x(0)).unwrap(), algebra.d(0));
    assert_eq!(fourier.apply(&algebra.d(0)).unwrap(), algebra.x(0));
    assert_eq!(
        fourier
            .apply(&algebra.commutator(&algebra.d(0), &algebra.x(0)))
            .unwrap(),
        algebra.one()
    );
}

#[test]
fn filtrations_symbols_and_poisson_bracket_match_leading_products() {
    let algebra = WeylAlgebra::<Rational>::standard(1);
    let left = algebra.monomial(&[2, 1], r(1)) + algebra.x(0);
    let right = algebra.monomial(&[1, 2], r(1)) + algebra.d(0);
    assert_eq!(algebra.bernstein_degree(&left).unwrap(), Some(3));
    assert_eq!(algebra.differential_order(&left).unwrap(), Some(1));

    let left_symbol = algebra
        .principal_symbol(&left, WeylFiltration::Bernstein)
        .unwrap();
    let right_symbol = algebra
        .principal_symbol(&right, WeylFiltration::Bernstein)
        .unwrap();
    let product = algebra.mul(&left, &right);
    assert_eq!(
        algebra
            .principal_symbol(&product, WeylFiltration::Bernstein)
            .unwrap(),
        left_symbol.checked_mul(&right_symbol).unwrap()
    );

    let bracket = algebra
        .poisson_bracket(&left_symbol, &right_symbol)
        .unwrap();
    let commutator = algebra.commutator(&left, &right);
    assert_eq!(
        algebra
            .principal_symbol(&commutator, WeylFiltration::Bernstein)
            .unwrap(),
        bracket
    );
    assert_eq!(bracket, SparsePolynomial::monomial(&[2, 2], r(-3)));

    let x_symbol = SparsePolynomial::try_variable(2, 0).unwrap();
    let d_symbol = SparsePolynomial::try_variable(2, 1).unwrap();
    assert_eq!(
        algebra.poisson_bracket(&d_symbol, &x_symbol).unwrap(),
        SparsePolynomial::scalar(2, r(1))
    );
    assert_eq!(
        algebra.poisson_bracket(&x_symbol, &d_symbol).unwrap(),
        SparsePolynomial::scalar(2, r(-1))
    );

    let left_order_symbol = algebra
        .principal_symbol(&left, WeylFiltration::DifferentialOrder)
        .unwrap();
    let right_order_symbol = algebra
        .principal_symbol(&right, WeylFiltration::DifferentialOrder)
        .unwrap();
    assert_eq!(
        algebra
            .principal_symbol(&product, WeylFiltration::DifferentialOrder)
            .unwrap(),
        left_order_symbol.checked_mul(&right_order_symbol).unwrap()
    );
    assert_eq!(
        algebra
            .principal_symbol(&commutator, WeylFiltration::DifferentialOrder)
            .unwrap(),
        algebra
            .poisson_bracket(&left_order_symbol, &right_order_symbol)
            .unwrap()
    );
}

#[test]
fn differential_order_symbol_retains_position_coefficients() {
    let algebra = WeylAlgebra::<Rational>::standard(2);
    let value = algebra.monomial(&[5, 1, 2, 0], r(3))
        + algebra.monomial(&[100, 7, 1, 0], r(4))
        + algebra.x(1);
    assert_eq!(algebra.differential_order(&value).unwrap(), Some(2));
    assert_eq!(
        algebra
            .principal_symbol(&value, WeylFiltration::DifferentialOrder)
            .unwrap(),
        SparsePolynomial::monomial(&[5, 1, 2, 0], r(3))
    );
}

#[test]
fn sparse_derivatives_and_poisson_budgets_are_explicit() {
    let algebra = WeylAlgebra::<Rational>::standard(1);
    let polynomial = SparsePolynomial::monomial(&[4, 3], r(2));
    assert_eq!(
        polynomial.partial_derivative(0).unwrap(),
        SparsePolynomial::monomial(&[3, 3], r(8))
    );
    assert_eq!(
        algebra.poisson_bracket_with_budget(
            &polynomial,
            &polynomial,
            WeylExpansionBudget::new(10, 0),
        ),
        Err(WeylError::StepBudgetExceeded { limit: 0 })
    );
}

#[test]
fn constant_poisson_bracket_obeys_leibniz_and_jacobi_laws() {
    let algebra = WeylAlgebra::<Rational>::standard(2);
    let f = SparsePolynomial::monomial(&[2, 0, 1, 0], r(2))
        + SparsePolynomial::monomial(&[0, 1, 0, 2], r(1));
    let g = SparsePolynomial::monomial(&[1, 1, 0, 1], r(-3)) + SparsePolynomial::scalar(4, r(5));
    let h = SparsePolynomial::monomial(&[0, 2, 1, 0], r(4))
        + SparsePolynomial::monomial(&[1, 0, 0, 1], r(1));

    let gh = g.checked_mul(&h).unwrap();
    assert_eq!(
        algebra.poisson_bracket(&f, &gh).unwrap(),
        algebra
            .poisson_bracket(&f, &g)
            .unwrap()
            .checked_mul(&h)
            .unwrap()
            + g.checked_mul(&algebra.poisson_bracket(&f, &h).unwrap())
                .unwrap()
    );
    assert_eq!(
        algebra.poisson_bracket(&f, &g).unwrap(),
        -algebra.poisson_bracket(&g, &f).unwrap()
    );

    let jacobi = algebra
        .poisson_bracket(&f, &algebra.poisson_bracket(&g, &h).unwrap())
        .unwrap()
        + algebra
            .poisson_bracket(&g, &algebra.poisson_bracket(&h, &f).unwrap())
            .unwrap()
        + algebra
            .poisson_bracket(&h, &algebra.poisson_bracket(&f, &g).unwrap())
            .unwrap();
    assert!(jacobi.is_zero());
}

#[test]
fn hbar_deformation_specializes_to_commutative_and_weyl_products() {
    let algebra = WeylAlgebra::<Rational>::standard(1);
    let family = algebra.hbar_deformation();
    let deformation = family.deformation_algebra();
    let x = family.lift_element(&algebra.x(0)).unwrap();
    let d = family.lift_element(&algebra.d(0)).unwrap();
    let dx = deformation.mul(&d, &x);
    let xd_plus_hbar = deformation.mul(&x, &d) + deformation.scalar(Poly::t());
    assert_eq!(dx, xd_plus_hbar);

    let zero = family.specialize_zero_algebra();
    assert!(zero
        .commutator(&zero.generator(1), &zero.generator(0))
        .is_zero());
    assert_eq!(
        family.specialize_zero(&dx).unwrap(),
        zero.mul(&zero.generator(1), &zero.generator(0))
    );
    assert_eq!(family.specialize_one_algebra(), algebra);
    assert_eq!(
        family.specialize_one(&dx).unwrap(),
        algebra.mul(&algebra.d(0), &algebra.x(0))
    );

    let at_two = family.specialize_algebra_at(&r(2));
    assert_eq!(
        at_two.commutator(&at_two.generator(1), &at_two.generator(0)),
        at_two.scalar(r(2))
    );
}

proptest! {
    #![proptest_config(proptest_config(CASES))]

    #[test]
    fn arbitrary_four_dimensional_alternating_forms_get_verified_darboux_coordinates(
        entries in prop::array::uniform6(-3i128..=3),
    ) {
        let [a, b, c, d, e, f] = entries;
        let form = ogdoad::forms::SymplecticForm::from_gram(vec![
            vec![r(0), r(a), r(b), r(c)],
            vec![r(-a), r(0), r(d), r(e)],
            vec![r(-b), r(-d), r(0), r(f)],
            vec![r(-c), r(-e), r(-f), r(0)],
        ]).unwrap();
        let decomposition = form.darboux_decomposition().unwrap();
        prop_assert!(decomposition.verifies(&form));
        prop_assert_eq!(2 * decomposition.planes() + decomposition.radical_dim(), 4);
    }

    #[test]
    fn fourier_is_a_product_map_on_random_rank_one_monomials(
        left in prop::array::uniform2(0u8..=3),
        right in prop::array::uniform2(0u8..=3),
    ) {
        type F5 = Fp<5>;
        let algebra = WeylAlgebra::<F5>::standard(1);
        let fourier = algebra.fourier_automorphism().unwrap();
        let left = algebra.monomial(&left.map(u128::from), F5::from_int(2));
        let right = algebra.monomial(&right.map(u128::from), F5::from_int(3));
        prop_assert_eq!(
            fourier.apply(&algebra.mul(&left, &right)).unwrap(),
            algebra.mul(&fourier.apply(&left).unwrap(), &fourier.apply(&right).unwrap()),
        );
    }
}
