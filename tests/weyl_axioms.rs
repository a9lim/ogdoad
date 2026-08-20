use ogdoad::forms::SymplecticForm;
use ogdoad::scalar::{Fp, Nimber, Poly, Rational, Scalar, Zp};
use ogdoad::weyl::{WeylAlgebra, WeylError};

fn r(value: i128) -> Rational {
    Rational::from_int(value)
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
