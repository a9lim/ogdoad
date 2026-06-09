//! Property-based associativity/distributivity of the geometric product, over
//! random metrics and random multivectors, in both characteristic 0 (`Rational`)
//! and characteristic 2 (`Nimber`).
//!
//! The unit suite pins associativity on fixed cases; this fuzzes it. A bug in
//! `geom_product_blades` (sign handling, the polar/quadratic split, the general
//! bilinear `a` term) shows up as a random associativity failure here, with a
//! shrunk counterexample, instead of as a downstream classifier mystery.

use pleroma::clifford::{bits, CliffordAlgebra, Metric, Multivector};
use pleroma::scalar::{Nimber, Rational, Scalar};
use proptest::prelude::*;
use std::collections::BTreeMap;

const DIM: usize = 3;
const BLADES: usize = 1 << DIM; // 8

/// Build a multivector from coefficients indexed by blade mask `0..2^DIM`.
fn build_mv<S: Scalar>(alg: &CliffordAlgebra<S>, coeffs: &[S]) -> Multivector<S> {
    let mut mv = alg.zero();
    for (mask, c) in coeffs.iter().enumerate() {
        let blade = alg.blade(&bits(mask as u128));
        mv = alg.add(&mv, &alg.scalar_mul(c, &blade));
    }
    mv
}

/// Off-diagonal polar form `b` keyed `(i,j)` with `i<j`, from the three pair
/// values (dim 3).
fn b_map<S: Scalar>(v: [S; 3]) -> BTreeMap<(usize, usize), S> {
    let [v01, v02, v12] = v;
    BTreeMap::from([((0, 1), v01), ((0, 2), v02), ((1, 2), v12)])
}

fn check_associative_distributive<S: Scalar>(
    alg: &CliffordAlgebra<S>,
    a: &Multivector<S>,
    b: &Multivector<S>,
    c: &Multivector<S>,
) {
    // (ab)c = a(bc)
    let lhs = alg.mul(&alg.mul(a, b), c);
    let rhs = alg.mul(a, &alg.mul(b, c));
    assert_eq!(lhs, rhs, "geometric product not associative");
    // a(b+c) = ab + ac  and  (a+b)c = ac + bc
    let left = alg.mul(a, &alg.add(b, c));
    let left_expanded = alg.add(&alg.mul(a, b), &alg.mul(a, c));
    assert_eq!(left, left_expanded, "left distributivity");
    let right = alg.mul(&alg.add(a, b), c);
    let right_expanded = alg.add(&alg.mul(a, c), &alg.mul(b, c));
    assert_eq!(right, right_expanded, "right distributivity");
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    /// Characteristic 2, with an independent quadratic form `q` and polar form
    /// `b` (the nimber-backend point: `q ≠ b` must stay faithful).
    #[test]
    fn nimber_geometric_product_is_a_ring(
        q in prop::array::uniform3(any::<u128>()),
        bvals in prop::array::uniform3(any::<u128>()),
        ca in prop::array::uniform::<_, BLADES>(any::<u128>()),
        cb in prop::array::uniform::<_, BLADES>(any::<u128>()),
        cc in prop::array::uniform::<_, BLADES>(any::<u128>()),
    ) {
        let metric = Metric::new(
            q.iter().map(|&x| Nimber(x)).collect(),
            b_map(bvals.map(Nimber)),
        );
        let alg = CliffordAlgebra::new(DIM, metric);
        let mk = |c: [u128; BLADES]| build_mv(&alg, &c.map(Nimber));
        check_associative_distributive(&alg, &mk(ca), &mk(cb), &mk(cc));
    }

    /// Characteristic 0, diagonal metric, small rational coefficients.
    #[test]
    fn rational_geometric_product_is_a_ring(
        q in prop::array::uniform3(-3i128..=3),
        ca in prop::array::uniform::<_, BLADES>(-3i128..=3),
        cb in prop::array::uniform::<_, BLADES>(-3i128..=3),
        cc in prop::array::uniform::<_, BLADES>(-3i128..=3),
    ) {
        let metric = Metric::diagonal(q.iter().map(|&x| Rational::int(x)).collect());
        let alg = CliffordAlgebra::new(DIM, metric);
        let mk = |c: [i128; BLADES]| build_mv(&alg, &c.map(Rational::int));
        check_associative_distributive(&alg, &mk(ca), &mk(cb), &mk(cc));
    }
}
