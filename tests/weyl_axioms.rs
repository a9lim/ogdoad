use ogdoad::forms::SymplecticForm;
use ogdoad::scalar::{Fp, Nimber, Poly, Rational, Scalar, Zp};
use ogdoad::weyl::{SparsePolynomial, WeylAlgebra, WeylElement, WeylError, WeylExpansionBudget};
use proptest::prelude::*;
use std::collections::BTreeMap;

mod common;
use common::proptest_config;

const CASES: u32 = 12;

fn r(value: i128) -> Rational {
    Rational::from_int(value)
}

fn add_oracle_term<S: Scalar>(
    terms: &mut BTreeMap<Vec<u128>, S>,
    exponents: Vec<u128>,
    coefficient: S,
) {
    if coefficient.is_zero() {
        return;
    }
    let entry = terms.entry(exponents.clone()).or_insert_with(S::zero);
    *entry = entry.add(&coefficient);
    if entry.is_zero() {
        terms.remove(&exponents);
    }
}

/// Literal adjacent-inversion reducer used only as a test oracle. It knows the
/// defining word relation `z_h z_g = z_g z_h + omega[h][g]`, but none of the
/// grouped-derivation or standard-pair product algorithms.
fn literal_reduce<S: Scalar>(algebra: &WeylAlgebra<S>, word: &[usize]) -> WeylElement<S> {
    fn recurse<S: Scalar>(algebra: &WeylAlgebra<S>, word: Vec<usize>) -> BTreeMap<Vec<u128>, S> {
        let Some(index) = word.windows(2).position(|pair| pair[0] > pair[1]) else {
            let mut exponents = vec![0u128; algebra.dim()];
            for generator in word {
                exponents[generator] += 1;
            }
            return BTreeMap::from([(exponents, S::one())]);
        };

        let higher = word[index];
        let lower = word[index + 1];
        let mut swapped = word.clone();
        swapped.swap(index, index + 1);
        let mut output = recurse(algebra, swapped);

        let commutator = &algebra.commutator_form()[higher][lower];
        if !commutator.is_zero() {
            let mut contracted = word;
            contracted.drain(index..=index + 1);
            for (exponents, coefficient) in recurse(algebra, contracted) {
                add_oracle_term(&mut output, exponents, coefficient.mul(commutator));
            }
        }
        output
    }

    recurse(algebra, word.to_vec())
        .into_iter()
        .fold(algebra.zero(), |sum, (exponents, coefficient)| {
            sum + algebra.monomial(&exponents, coefficient)
        })
}

fn monomial_word(exponents: &[u128]) -> Vec<usize> {
    exponents
        .iter()
        .enumerate()
        .flat_map(|(generator, count)| std::iter::repeat_n(generator, *count as usize))
        .collect()
}

fn rank_one_general<S: Scalar>() -> WeylAlgebra<S> {
    WeylAlgebra::from_commutator(vec![
        vec![S::zero(), S::one().neg()],
        vec![S::one(), S::zero()],
    ])
    .unwrap()
}

fn check_general_ring_laws<S: Scalar>(left: [u8; 2], middle: [u8; 2], right: [u8; 2]) {
    let algebra = rank_one_general::<S>();
    let make = |exponents: [u8; 2], constant: i128| {
        algebra.monomial(&exponents.map(u128::from), S::from_int(constant + 2))
            + algebra.scalar(S::from_int(constant))
    };
    let a = make(left, 1);
    let b = make(middle, -1);
    let c = make(right, 2);
    assert_eq!(
        algebra.mul(&algebra.mul(&a, &b), &c),
        algebra.mul(&a, &algebra.mul(&b, &c))
    );
    assert_eq!(
        algebra.mul(&a, &(b.clone() + c.clone())),
        algebra.mul(&a, &b) + algebra.mul(&a, &c)
    );
}

#[test]
fn standard_generators_satisfy_the_weyl_relations() {
    let algebra = WeylAlgebra::<Rational>::standard(2);
    for i in 0..2 {
        for j in 0..2 {
            let expected = if i == j {
                algebra.one()
            } else {
                algebra.zero()
            };
            assert_eq!(algebra.commutator(&algebra.d(i), &algebra.x(j)), expected);
            assert!(algebra.commutator(&algebra.x(i), &algebra.x(j)).is_zero());
            assert!(algebra.commutator(&algebra.d(i), &algebra.d(j)).is_zero());
        }
    }
}

#[test]
fn standard_product_returns_the_expected_pbw_expansion() {
    let algebra = WeylAlgebra::<Rational>::standard(1);
    let d_squared = algebra.pow(&algebra.d(0), 2);
    let x_cubed = algebra.pow(&algebra.x(0), 3);
    let product = algebra.mul(&d_squared, &x_cubed);

    // d^2 x^3 = x^3 d^2 + 6 x^2 d + 6 x.
    let expected = algebra.monomial(&[3, 2], r(1))
        + algebra.monomial(&[2, 1], r(6))
        + algebra.monomial(&[1, 0], r(6));
    assert_eq!(product, expected);
}

#[test]
fn optimized_standard_product_agrees_with_general_normal_ordering() {
    type F5 = Fp<5>;

    let standard = WeylAlgebra::<F5>::standard(2);
    let general = WeylAlgebra::from_commutator(standard.commutator_form().to_vec()).unwrap();
    let exponent_vectors: Vec<Vec<u128>> = (0u128..16)
        .map(|bits| (0..4).map(|index| (bits >> index) & 1).collect())
        .collect();

    for left in &exponent_vectors {
        for right in &exponent_vectors {
            let fast = standard.mul(
                &standard.monomial(left, F5::one()),
                &standard.monomial(right, F5::one()),
            );
            let oracle = general.mul(
                &general.monomial(left, F5::one()),
                &general.monomial(right, F5::one()),
            );
            assert_eq!(
                fast.terms(),
                oracle.terms(),
                "left={left:?}, right={right:?}"
            );
        }
    }
}

#[test]
fn general_alternating_product_is_associative() {
    let omega = vec![
        vec![r(0), r(2), r(3)],
        vec![r(-2), r(0), r(5)],
        vec![r(-3), r(-5), r(0)],
    ];
    let algebra = WeylAlgebra::from_commutator(omega).unwrap();
    let z0 = algebra.generator(0);
    let z1 = algebra.generator(1);
    let z2 = algebra.generator(2);
    let a = z0.clone() + algebra.scalar(r(2));
    let b = algebra.mul(&z1, &z0) - z2.clone();
    let c = algebra.pow(&(z2 + z1), 2);

    assert_eq!(
        algebra.mul(&algebra.mul(&a, &b), &c),
        algebra.mul(&a, &algebra.mul(&b, &c))
    );

    let monomials: Vec<_> = (0u128..8)
        .map(|bits| {
            let exponents: Vec<_> = (0..3).map(|index| (bits >> index) & 1).collect();
            algebra.monomial(&exponents, r(1))
        })
        .collect();
    for left in &monomials {
        for middle in &monomials {
            for right in &monomials {
                assert_eq!(
                    algebra.mul(&algebra.mul(left, middle), right),
                    algebra.mul(left, &algebra.mul(middle, right))
                );
            }
        }
    }
}

#[test]
fn symplectic_bridge_is_characteristic_two_faithful() {
    let form =
        SymplecticForm::from_gram(vec![vec![Nimber(0), Nimber(1)], vec![Nimber(1), Nimber(0)]])
            .unwrap();
    let algebra = WeylAlgebra::from_symplectic(&form);
    assert_eq!(
        algebra.commutator(&algebra.generator(0), &algebra.generator(1)),
        algebra.one()
    );
}

#[test]
fn radical_generators_are_central() {
    let algebra = WeylAlgebra::from_commutator(vec![
        vec![r(0), r(-1), r(0)],
        vec![r(1), r(0), r(0)],
        vec![r(0), r(0), r(0)],
    ])
    .unwrap();
    let radical = algebra.generator(2);
    for index in 0..3 {
        assert!(algebra
            .commutator(&radical, &algebra.generator(index))
            .is_zero());
    }
}

#[test]
fn characteristic_p_pth_powers_are_nonzero_and_central() {
    type F5 = Fp<5>;

    let algebra = WeylAlgebra::<F5>::standard(1);
    let x = algebra.x(0);
    let d = algebra.d(0);
    let x_to_p = algebra.pow(&x, 5);
    let d_to_p = algebra.pow(&d, 5);

    assert!(!x_to_p.is_zero());
    assert!(!d_to_p.is_zero());
    for generator in [&x, &d] {
        assert!(algebra.commutator(&x_to_p, generator).is_zero());
        assert!(algebra.commutator(&d_to_p, generator).is_zero());
    }
}

#[test]
fn standard_product_is_faithful_over_composite_characteristic_rings() {
    type Z4 = Zp<2, 2>;

    let algebra = WeylAlgebra::<Z4>::standard(1);
    let product = algebra.mul(
        &algebra.pow(&algebra.d(0), 2),
        &algebra.pow(&algebra.x(0), 2),
    );

    // d^2 x^2 = x^2 d^2 + 4 x d + 2, hence x^2 d^2 + 2 over Z/4.
    let expected =
        algebra.monomial(&[2, 2], Z4::one()) + algebra.monomial(&[0, 0], Z4::from_int(2));
    assert_eq!(product, expected);
}

#[test]
fn polynomial_action_is_a_multiplicative_representation() {
    let algebra = WeylAlgebra::<Rational>::standard(1);
    let polynomial = Poly::new(vec![r(1), r(2), r(3), r(-1)]);
    let x = algebra.x(0);
    let d = algebra.d(0);
    let dx = algebra.mul(&d, &x);

    let product_action = algebra.act_on_poly(&dx, &polynomial).unwrap();
    let nested_action = algebra
        .act_on_poly(&d, &algebra.act_on_poly(&x, &polynomial).unwrap())
        .unwrap();
    assert_eq!(product_action, nested_action);

    // d*x = x*d + 1 gives t*f'(t) + f(t).
    let expected = Poly::new(vec![r(1), r(4), r(9), r(-4)]);
    assert_eq!(product_action, expected);
}

#[test]
fn polynomial_action_is_not_claimed_faithful_in_positive_characteristic() {
    type F3 = Fp<3>;

    let algebra = WeylAlgebra::<F3>::standard(1);
    let d_cubed = algebra.pow(&algebra.d(0), 3);
    let polynomial = Poly::new((0..8).map(F3::from_int).collect());
    assert!(!d_cubed.is_zero());
    assert!(algebra
        .act_on_poly(&d_cubed, &polynomial)
        .unwrap()
        .is_zero());
}

#[test]
fn filtration_is_submultiplicative() {
    let algebra = WeylAlgebra::<Rational>::standard(1);
    let left = algebra.pow(&algebra.x(0), 2) + algebra.pow(&algebra.d(0), 3);
    let right = algebra.x(0) + algebra.pow(&algebra.d(0), 2);
    let product = algebra.mul(&left, &right);

    let left_degree = algebra.filtration_degree(&left).unwrap().unwrap();
    let right_degree = algebra.filtration_degree(&right).unwrap().unwrap();
    let product_degree = algebra.filtration_degree(&product).unwrap().unwrap();
    assert!(product_degree <= left_degree + right_degree);
    assert_eq!(algebra.filtration_degree(&algebra.zero()).unwrap(), None);
}

#[test]
fn represented_exponent_overflow_is_checked() {
    let algebra = WeylAlgebra::<Rational>::standard(1);
    let largest = algebra.monomial(&[u128::MAX, 0], r(1));
    assert_eq!(
        algebra.checked_mul(&largest, &algebra.x(0)),
        Err(WeylError::ExponentOverflow)
    );
}

#[test]
fn commutator_validation_and_rendering_are_canonical() {
    assert!(matches!(
        WeylAlgebra::<Rational>::from_commutator(vec![vec![r(0), r(1)], vec![r(-1)]]),
        Err(WeylError::NonSquareCommutator { row: 1, .. })
    ));
    assert_eq!(
        WeylAlgebra::<Rational>::from_commutator(vec![vec![r(1)]]),
        Err(WeylError::NonzeroDiagonal { index: 0 })
    );
    assert!(matches!(
        WeylAlgebra::<Rational>::from_commutator(vec![vec![r(0), r(1)], vec![r(1), r(0)]]),
        Err(WeylError::NotSkewSymmetric { left: 0, right: 1 })
    ));

    let algebra = WeylAlgebra::<Rational>::standard(1);
    let rendered = algebra.scalar(r(3)) + algebra.monomial(&[2, 1], r(-2));
    assert_eq!(rendered.to_string(), "3 - 2⋅z0↑2⋅z1");
}

#[test]
fn grouped_general_normalizer_handles_huge_appended_exponents() {
    let algebra = rank_one_general::<Rational>();
    let exponent = 1_000_000_000_000_000_000u128;
    let product = algebra
        .checked_mul_with_budget(
            &algebra.generator(1),
            &algebra.monomial(&[exponent, 0], r(1)),
            WeylExpansionBudget::new(4, 100),
        )
        .unwrap();
    let expected = algebra.monomial(&[exponent, 1], r(1))
        + algebra.monomial(&[exponent - 1, 0], r(exponent as i128));
    assert_eq!(product, expected);
}

#[test]
fn grouped_contractions_agree_with_words_across_multiple_higher_generators() {
    let algebra = WeylAlgebra::from_commutator(vec![
        vec![r(0), r(-2), r(-3)],
        vec![r(2), r(0), r(-5)],
        vec![r(3), r(5), r(0)],
    ])
    .unwrap();
    let left = [0, 2, 2];
    let right = [3, 0, 0];
    let mut word = monomial_word(&left);
    word.extend(monomial_word(&right));
    assert_eq!(
        algebra.mul(
            &algebra.monomial(&left, r(1)),
            &algebra.monomial(&right, r(1)),
        ),
        literal_reduce(&algebra, &word)
    );
}

#[test]
fn multiplication_reports_term_and_step_exhaustion_separately() {
    let algebra = WeylAlgebra::<Rational>::standard(1);
    let d3 = algebra.pow(&algebra.d(0), 3);
    let x3 = algebra.pow(&algebra.x(0), 3);
    assert_eq!(
        algebra.checked_mul_with_budget(&d3, &x3, WeylExpansionBudget::new(2, 10_000)),
        Err(WeylError::TermBudgetExceeded { limit: 2 })
    );
    assert_eq!(
        algebra.checked_mul_with_budget(
            &algebra.d(0),
            &algebra.x(0),
            WeylExpansionBudget::new(8, 0),
        ),
        Err(WeylError::StepBudgetExceeded { limit: 0 })
    );

    let x_plus_d = algebra.x(0) + algebra.d(0);
    assert_eq!(
        algebra.checked_pow_with_budget(&x_plus_d, 2, WeylExpansionBudget::new(1, 10_000)),
        Err(WeylError::TermBudgetExceeded { limit: 1 })
    );
    assert_eq!(
        algebra.checked_commutator_with_budget(
            &algebra.d(0),
            &algebra.x(0),
            WeylExpansionBudget::new(8, 0),
        ),
        Err(WeylError::StepBudgetExceeded { limit: 0 })
    );
}

#[test]
fn checked_constructors_and_base_change_preserve_boundaries() {
    assert_eq!(
        WeylAlgebra::<Rational>::try_standard(usize::MAX),
        Err(WeylError::StandardDimensionOverflow)
    );
    let general = rank_one_general::<Fp<2>>();
    assert_eq!(
        general.try_generator(2),
        Err(WeylError::GeneratorOutOfRange { index: 2, dim: 2 })
    );
    assert_eq!(general.try_x(0), Err(WeylError::RequiresStandard));
    assert_eq!(
        general.try_monomial(&[1], Fp::<2>::one()),
        Err(WeylError::MonomialDimensionMismatch {
            expected: 2,
            actual: 1
        })
    );

    let mapped = general.map(|coefficient| Nimber(coefficient.value()));
    let source = general.generator(0) + general.generator(1);
    let target = source.map_coefficients(|coefficient| Nimber(coefficient.value()));
    assert_eq!(
        mapped.commutator(&mapped.generator(1), &mapped.generator(0)),
        mapped.one()
    );
    assert_eq!(
        target,
        mapped.generator(0) + mapped.generator(1),
        "element base change preserves PBW support"
    );
}

#[test]
fn sparse_multivariate_polynomials_are_canonical_and_checked() {
    let left =
        SparsePolynomial::monomial(&[2, 0], r(3)) + SparsePolynomial::monomial(&[0, 1], r(1));
    let right =
        SparsePolynomial::monomial(&[1, 1], r(2)) - SparsePolynomial::monomial(&[0, 1], r(1));
    let product = left.checked_mul(&right).unwrap();
    let expected = SparsePolynomial::monomial(&[3, 1], r(6))
        - SparsePolynomial::monomial(&[2, 1], r(3))
        + SparsePolynomial::monomial(&[1, 2], r(2))
        - SparsePolynomial::monomial(&[0, 2], r(1));
    assert_eq!(product, expected);
    assert_eq!(product.total_degree(), Some(4));
    assert_eq!(SparsePolynomial::<Rational>::zero(2).total_degree(), None);
    assert_eq!(
        left.checked_mul_with_budget(&right, WeylExpansionBudget::new(1, 10_000)),
        Err(WeylError::TermBudgetExceeded { limit: 1 })
    );
    assert!(matches!(
        left.checked_add(&SparsePolynomial::scalar(1, r(1))),
        Err(WeylError::DimensionMismatch {
            expected: 2,
            actual: 1
        })
    ));
}

#[test]
fn rank_two_sparse_polynomial_action_is_multiplicative() {
    let algebra = WeylAlgebra::<Rational>::standard(2);
    let polynomial =
        SparsePolynomial::monomial(&[2, 3], r(1)) + SparsePolynomial::monomial(&[1, 0], r(2));
    let left = algebra.d(0) + algebra.x(1);
    let right = algebra.x(0) + algebra.d(1);
    let product = algebra.mul(&left, &right);

    let product_action = algebra.act_on_sparse_poly(&product, &polynomial).unwrap();
    let nested_action = algebra
        .act_on_sparse_poly(
            &left,
            &algebra.act_on_sparse_poly(&right, &polynomial).unwrap(),
        )
        .unwrap();
    assert_eq!(product_action, nested_action);

    let two_term_operator = algebra.x(0) + algebra.x(1);
    assert_eq!(
        algebra.act_on_sparse_poly_with_budget(
            &two_term_operator,
            &SparsePolynomial::scalar(2, r(1)),
            WeylExpansionBudget::new(1, 10_000),
        ),
        Err(WeylError::TermBudgetExceeded { limit: 1 })
    );
}

#[test]
fn sparse_action_carries_huge_degrees_without_dense_allocation() {
    type F5 = Fp<5>;

    let algebra = WeylAlgebra::<F5>::standard(1);
    let exponent = u128::MAX - 1;
    let polynomial = SparsePolynomial::monomial(&[exponent], F5::from_int(2));
    let derivative = algebra
        .act_on_sparse_poly_with_budget(&algebra.d(0), &polynomial, WeylExpansionBudget::new(2, 20))
        .unwrap();
    assert_eq!(
        derivative,
        SparsePolynomial::monomial(
            &[exponent - 1],
            F5::from_int(2).mul(&F5::from_u128(exponent)),
        )
    );
}

#[test]
fn rank_two_positive_characteristic_action_keeps_the_p_center_boundary() {
    type F3 = Fp<3>;

    let algebra = WeylAlgebra::<F3>::standard(2);
    let d0_cubed = algebra.pow(&algebra.d(0), 3);
    let polynomial = SparsePolynomial::monomial(&[7, 2], F3::one())
        + SparsePolynomial::monomial(&[4, 5], F3::from_int(2));
    assert!(!d0_cubed.is_zero());
    assert!(algebra
        .act_on_sparse_poly(&d0_cubed, &polynomial)
        .unwrap()
        .is_zero());
}

proptest! {
    #![proptest_config(proptest_config(CASES))]

    #[test]
    fn general_grouped_product_agrees_with_literal_word_reduction(
        omega01 in -2i128..=2,
        omega02 in -2i128..=2,
        omega12 in -2i128..=2,
        left in prop::array::uniform3(0u8..=1),
        right in prop::array::uniform3(0u8..=1),
    ) {
        let algebra = WeylAlgebra::from_commutator(vec![
            vec![r(0), r(omega01), r(omega02)],
            vec![r(-omega01), r(0), r(omega12)],
            vec![r(-omega02), r(-omega12), r(0)],
        ]).unwrap();
        let left = left.map(u128::from);
        let right = right.map(u128::from);
        let mut word = monomial_word(&left);
        word.extend(monomial_word(&right));
        let product = algebra.mul(
            &algebra.monomial(&left, r(1)),
            &algebra.monomial(&right, r(1)),
        );
        prop_assert_eq!(product, literal_reduce(&algebra, &word));
    }

    #[test]
    fn optimized_and_general_products_agree_beyond_squarefree_exponents(
        left in prop::array::uniform4(0u8..=3),
        right in prop::array::uniform4(0u8..=3),
    ) {
        type F5 = Fp<5>;
        let standard = WeylAlgebra::<F5>::standard(2);
        let general = WeylAlgebra::from_commutator(standard.commutator_form().to_vec()).unwrap();
        let left = left.map(u128::from);
        let right = right.map(u128::from);
        let fast = standard.mul(
            &standard.monomial(&left, F5::one()),
            &standard.monomial(&right, F5::one()),
        );
        let oracle = general.mul(
            &general.monomial(&left, F5::one()),
            &general.monomial(&right, F5::one()),
        );
        prop_assert_eq!(fast.terms(), oracle.terms());
    }

    #[test]
    fn general_product_is_associative_across_exact_characteristics(
        left in prop::array::uniform2(0u8..=2),
        middle in prop::array::uniform2(0u8..=2),
        right in prop::array::uniform2(0u8..=2),
    ) {
        check_general_ring_laws::<Rational>(left, middle, right);
        check_general_ring_laws::<Fp<5>>(left, middle, right);
        check_general_ring_laws::<Fp<2>>(left, middle, right);
        check_general_ring_laws::<Zp<2, 2>>(left, middle, right);
    }

    #[test]
    fn rank_two_polynomial_action_is_a_product_oracle(
        polynomial_exponents in prop::array::uniform2(0u8..=4),
        left in prop::array::uniform4(0u8..=2),
        right in prop::array::uniform4(0u8..=2),
    ) {
        type F5 = Fp<5>;
        let algebra = WeylAlgebra::<F5>::standard(2);
        let polynomial = SparsePolynomial::monomial(
            &polynomial_exponents.map(u128::from),
            F5::from_int(2),
        );
        let left = algebra.monomial(&left.map(u128::from), F5::one());
        let right = algebra.monomial(&right.map(u128::from), F5::from_int(3));
        let product = algebra.mul(&left, &right);
        prop_assert_eq!(
            algebra.act_on_sparse_poly(&product, &polynomial).unwrap(),
            algebra.act_on_sparse_poly(
                &left,
                &algebra.act_on_sparse_poly(&right, &polynomial).unwrap(),
            ).unwrap(),
        );
    }
}
