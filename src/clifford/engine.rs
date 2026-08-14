//! The multivector engine, generic over any `Scalar` backend.
//!
//! ## Metric data — characteristic-faithful by design
//!
//! A blade is a `u128` bitmask over basis generators `e_0..e_127`. The product
//! is defined by three pieces of metric data:
//!
//!   * `q[i] = e_i²`, the quadratic diagonal;
//!   * `b[(i,j)] = e_i e_j + e_j e_i` for `i < j`, the polar form;
//!   * `a[(i,j)] = B(e_i,e_j)` for `i < j`, the in-order contraction of the
//!     general bilinear form used by the Chevalley product.
//!
//! The full bilinear form has `B(e_i,e_i) = q[i]`, `B(e_i,e_j) = a[(i,j)]`,
//! and `B(e_j,e_i) = b[(i,j)] - a[(i,j)]` for `i < j`. Ordinary `(q, b)`
//! metrics leave `a` empty. In characteristic two, the alternating polar data
//! `b` remains independent of the possibly nonzero quadratic diagonal `q`.
//!
//! A zero `q[i]` gives a null generator. Setting all `q`, `b`, and `a` entries
//! to zero gives the exterior algebra.
//!
//! ## Product
//!
//! Ordinary `(q, b)` products satisfy the reduction rules
//!
//! ```text
//!   e_i e_i  → q[i]                            (equal adjacent: contract)
//!   e_i e_j  → b[(j,i)] − e_j e_i   (i>j)      (out of order: swap, emit polar)
//! ```
//!
//! The minus sign goes through [`Scalar::neg`](crate::scalar::Scalar::neg), so
//! it becomes addition in characteristic two. General metrics use the
//! equivalent Chevalley contraction determined by `q`, `b`, and `a`.

mod algebra;
mod basis;
mod inverse;
mod metric;
mod multivector;
mod product;
mod terms;

pub use algebra::CliffordAlgebra;
pub(crate) use basis::grade_k_masks;
pub use basis::{bits, grade, MAX_BASIS_DIM};
pub use metric::Metric;
pub use multivector::Multivector;
pub(crate) use terms::add_term;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{Integer, Nimber, Ordinal, Rational, Scalar, Surreal};
    use std::collections::BTreeMap;

    fn r(n: i128) -> Rational {
        Rational::from_int(n)
    }

    #[test]
    #[should_panic(expected = "at most 128 generators")]
    fn algebra_dimension_must_fit_blade_mask() {
        let _ = CliffordAlgebra::new(129, Metric::<Rational>::grassmann(129));
    }

    #[test]
    #[should_panic(expected = "b-keys must satisfy i < j")]
    fn metric_rejects_reversed_or_diagonal_polar_keys() {
        let mut b = BTreeMap::new();
        b.insert((1usize, 0usize), r(1));
        let _ = Metric::new(vec![r(1), r(1)], b);
    }

    #[test]
    #[should_panic(expected = "generator index 2 out of range")]
    fn generator_index_must_be_in_the_algebra() {
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![r(1), r(1)]));
        let _ = alg.e(2);
    }

    #[test]
    fn complex_numbers_cl01() {
        let alg = CliffordAlgebra::new(1, Metric::diagonal(vec![r(-1)]));
        assert_eq!(alg.mul(&alg.e(0), &alg.e(0)), alg.scalar(r(-1)));
    }

    #[test]
    fn cl20_bivector_squares_to_minus_one() {
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![r(1), r(1)]));
        let e0 = alg.e(0);
        let e1 = alg.e(1);
        let e0e1 = alg.mul(&e0, &e1);
        let e1e0 = alg.mul(&e1, &e0);
        assert_eq!(e0e1, alg.scalar_mul(&r(-1), &e1e0));
        assert_eq!(alg.mul(&e0e1, &e0e1), alg.scalar(r(-1)));
    }

    #[test]
    fn orthogonal_blade_product_handles_repeated_indices_directly() {
        let metric = Metric::diagonal(vec![r(2), r(3), r(5)]);
        let mut expect = BTreeMap::new();
        // e_0e_1 · e_1e_2 = q_1 e_0e_2.
        expect.insert(0b101, r(3));
        assert_eq!(metric.geom_product_blades(0b011, 0b110), expect);

        let mut expect_scalar = BTreeMap::new();
        // e_0e_1 · e_0e_1 = -q_0q_1.
        expect_scalar.insert(0, r(-6));
        assert_eq!(metric.geom_product_blades(0b011, 0b011), expect_scalar);
    }

    #[test]
    fn grassmann_generators_are_nilpotent() {
        let alg = CliffordAlgebra::new(3, Metric::grassmann(3));
        for i in 0..3 {
            let ei = alg.e(i);
            assert!(alg.mul(&ei, &ei).is_zero(), "e{i}^2 should be 0");
        }
        let (e0, e1) = (alg.e(0), alg.e(1));
        assert_eq!(alg.mul(&e0, &e1), alg.wedge(&e0, &e1));
        assert_eq!(
            alg.mul(&e0, &e1),
            alg.scalar_mul(&r(-1), &alg.mul(&e1, &e0))
        );
    }

    #[test]
    fn multivector_operator_traits_forward_to_additive_and_wedge_ops() {
        let alg = CliffordAlgebra::new(3, Metric::grassmann(3));
        let e0 = alg.e(0);
        let e1 = alg.e(1);

        let sum = e0.clone() + e1.clone();
        assert_eq!(sum, alg.add(&e0, &e1));
        assert_eq!(sum - e1.clone(), e0);
        assert_eq!(-e1.clone(), alg.scalar_mul(&r(-1), &e1));

        let e01 = e0.clone() & e1.clone();
        assert_eq!(e01, alg.wedge(&e0, &e1));
        assert_eq!(
            e1 & e0,
            alg.scalar_mul(&r(-1), &alg.wedge(&alg.e(0), &alg.e(1)))
        );
    }

    #[test]
    fn nimber_orthogonal_is_commutative() {
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![Nimber(2), Nimber(3)]));
        let e0 = alg.e(0);
        let e1 = alg.e(1);
        assert_eq!(alg.mul(&e0, &e1), alg.mul(&e1, &e0));
        assert_eq!(alg.mul(&e0, &e0), alg.scalar(Nimber(2)));
    }

    #[test]
    fn nimber_offdiagonal_is_noncommutative() {
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), Nimber(1));
        let alg = CliffordAlgebra::new(2, Metric::new(vec![Nimber(0), Nimber(0)], b));
        let e0 = alg.e(0);
        let e1 = alg.e(1);
        let anti = alg.add(&alg.mul(&e0, &e1), &alg.mul(&e1, &e0));
        assert_eq!(anti, alg.scalar(Nimber(1)));
        assert_ne!(alg.mul(&e0, &e1), alg.mul(&e1, &e0));
    }

    fn assert_associative<S: Scalar>(alg: &CliffordAlgebra<S>, gens: &[Multivector<S>]) {
        for a in gens {
            for b in gens {
                for c in gens {
                    assert_eq!(alg.mul(&alg.mul(a, b), c), alg.mul(a, &alg.mul(b, c)));
                }
            }
        }
    }

    #[test]
    fn associativity_rational_nonorthogonal() {
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), r(1));
        b.insert((1usize, 2usize), r(-1));
        let alg = CliffordAlgebra::new(3, Metric::new(vec![r(1), r(-1), r(2)], b));
        let gens = [
            alg.e(0),
            alg.e(1),
            alg.e(2),
            alg.mul(&alg.e(0), &alg.e(1)),
            alg.add(&alg.e(0), &alg.scalar(r(3))),
        ];
        assert_associative(&alg, &gens);
    }

    #[test]
    fn associativity_nimber_nonorthogonal() {
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), Nimber(1));
        b.insert((0usize, 2usize), Nimber(3));
        let alg = CliffordAlgebra::new(3, Metric::new(vec![Nimber(2), Nimber(1), Nimber(0)], b));
        let gens = [
            alg.e(0),
            alg.e(1),
            alg.e(2),
            alg.mul(&alg.e(0), &alg.e(1)),
            alg.add(&alg.e(2), &alg.scalar(Nimber(5))),
        ];
        assert_associative(&alg, &gens);
    }

    #[test]
    fn reverse_is_metric_aware_on_nonorthogonal_blades() {
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), r(1));
        let alg = CliffordAlgebra::new(2, Metric::new(vec![r(1), r(1)], b));
        let e0 = alg.e(0);
        let e1 = alg.e(1);
        let e0e1 = alg.mul(&e0, &e1);

        assert_eq!(alg.reverse(&e0e1), alg.mul(&e1, &e0));
        assert_eq!(
            alg.reverse(&alg.mul(&e0, &e1)),
            alg.mul(&alg.reverse(&e1), &alg.reverse(&e0))
        );
    }

    #[test]
    fn ordinal_clifford_transfinite_squares_work() {
        let omega = Ordinal::omega();
        let omega_plus_one = omega.nim_add(&Ordinal::one());
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), Ordinal::one());
        let alg = CliffordAlgebra::new(
            2,
            Metric::new(vec![omega.clone(), omega_plus_one.clone()], b),
        );
        let e0 = alg.e(0);
        let e1 = alg.e(1);
        assert_eq!(alg.mul(&e0, &e0), alg.scalar(omega));
        assert_eq!(alg.mul(&e1, &e1), alg.scalar(omega_plus_one));
        assert_eq!(
            alg.add(&alg.mul(&e0, &e1), &alg.mul(&e1, &e0)),
            alg.scalar(Ordinal::one())
        );
        let gens = [
            e0.clone(),
            e1.clone(),
            alg.mul(&e0, &e1),
            alg.add(&e0, &alg.scalar(Ordinal::from_u128(3))),
        ];
        assert_associative(&alg, &gens);
    }

    #[test]
    fn vector_inverse() {
        let alg = CliffordAlgebra::new(3, Metric::diagonal(vec![r(1), r(1), r(1)]));
        let v = alg.e(0);
        let vi = alg.versor_inverse(&v).unwrap();
        assert_eq!(alg.mul(&v, &vi), alg.scalar(r(1)));
        assert_eq!(vi, v);

        let alg2 = CliffordAlgebra::new(1, Metric::diagonal(vec![r(2)]));
        let e0 = alg2.e(0);
        assert_eq!(
            alg2.mul(&e0, &alg2.versor_inverse(&e0).unwrap()),
            alg2.scalar(r(1))
        );

        let alg0 = CliffordAlgebra::new(1, Metric::<Rational>::grassmann(1));
        assert!(alg0.versor_inverse(&alg0.e(0)).is_none());
    }

    #[test]
    fn reflection_fixes_and_negates() {
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![r(1), r(1)]));
        let (e0, e1) = (alg.e(0), alg.e(1));
        assert_eq!(alg.reflect(&e1, &e0).unwrap(), e0);
        assert_eq!(alg.reflect(&e1, &e1).unwrap(), alg.scalar_mul(&r(-1), &e1));
    }

    #[test]
    fn rotor_preserves_norm() {
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![r(1), r(1)]));
        let rotor = alg.mul(&alg.e(0), &alg.e(1));
        let x = alg.add(
            &alg.scalar_mul(&r(3), &alg.e(0)),
            &alg.scalar_mul(&r(4), &alg.e(1)),
        );
        let rx = alg.sandwich(&rotor, &x).unwrap();
        assert_eq!(alg.norm2(&rx), alg.norm2(&x));
    }

    #[test]
    fn twisted_adjoint_matches_reflect_and_sandwich() {
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![r(1), r(1)]));
        let (e0, e1) = (alg.e(0), alg.e(1));
        let x = alg.add(&alg.scalar_mul(&r(3), &e0), &alg.scalar_mul(&r(4), &e1));
        assert_eq!(
            alg.twisted_sandwich(&e1, &x).unwrap(),
            alg.reflect(&e1, &x).unwrap()
        );
        let rotor = alg.mul(&e0, &e1);
        assert_eq!(
            alg.twisted_sandwich(&rotor, &x).unwrap(),
            alg.sandwich(&rotor, &x).unwrap()
        );
    }

    #[test]
    fn left_contraction_lowers_grade() {
        let alg = CliffordAlgebra::new(3, Metric::diagonal(vec![r(1), r(1), r(1)]));
        let e0 = alg.e(0);
        let e0e1 = alg.mul(&alg.e(0), &alg.e(1));
        assert_eq!(alg.left_contract(&e0, &e0e1), alg.e(1));
        let three = alg.scalar(r(3));
        assert_eq!(
            alg.left_contract(&three, &e0e1),
            alg.scalar_mul(&r(3), &e0e1)
        );
    }

    #[test]
    fn dual_of_vector_is_bivector_in_3d() {
        let alg = CliffordAlgebra::new(3, Metric::diagonal(vec![r(1), r(1), r(1)]));
        let d = alg.dual(&alg.e(0)).unwrap();
        assert!(!d.is_zero());
        assert_eq!(alg.grade_part(&d, 2), d);
    }

    #[test]
    fn grade_involution_signs() {
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![r(1), r(1)]));
        let v = alg.add(
            &alg.scalar(r(5)),
            &alg.add(&alg.e(0), &alg.mul(&alg.e(0), &alg.e(1))),
        );
        let expect = alg.add(
            &alg.scalar(r(5)),
            &alg.add(
                &alg.scalar_mul(&r(-1), &alg.e(0)),
                &alg.mul(&alg.e(0), &alg.e(1)),
            ),
        );
        assert_eq!(alg.grade_involution(&v), expect);
    }

    #[test]
    fn versor_over_surreal_metric() {
        let alg = CliffordAlgebra::new(
            2,
            Metric::diagonal(vec![Surreal::omega(), Surreal::epsilon()]),
        );
        let e0 = alg.e(0);
        let inv = alg.versor_inverse(&e0).unwrap();
        assert_eq!(alg.mul(&e0, &inv), alg.scalar(Surreal::one()));
    }

    #[test]
    fn even_subalgebra_of_cl30_is_quaternions() {
        let alg = CliffordAlgebra::new(3, Metric::diagonal(vec![r(1), r(1), r(1)]));
        let even = alg.even_subalgebra().unwrap();
        assert_eq!(even.dim(), 2);
        let (f0, f1) = (even.e(0), even.e(1));
        assert_eq!(even.mul(&f0, &f0), even.scalar(r(-1)));
        assert_eq!(even.mul(&f1, &f1), even.scalar(r(-1)));
        assert_eq!(
            even.mul(&f0, &f1),
            even.scalar_mul(&r(-1), &even.mul(&f1, &f0))
        );
    }

    #[test]
    fn even_subalgebra_generator_squares_follow_the_pivot_law_not_hardcoded_minus_one() {
        let alg = CliffordAlgebra::new(3, Metric::diagonal(vec![r(2), r(3), r(5)]));
        let even = alg.even_subalgebra().unwrap();
        assert_eq!(even.dim(), 2);
        let (f0, f1) = (even.e(0), even.e(1));
        // Pivot is q_p at the highest-index invertible generator: p=2, q_p=5.
        // f_0 = e_0 e_2 ⇒ f_0^2 = -q_0 q_2 = -10; f_1 = e_1 e_2 ⇒ f_1^2 = -q_1 q_2 = -15.
        assert_eq!(even.mul(&f0, &f0), even.scalar(r(-10)), "f0^2 != -q0*q_p");
        assert_eq!(even.mul(&f1, &f1), even.scalar(r(-15)), "f1^2 != -q1*q_p");
        // Distinct diagonal entries ensure the result uses the pivot square.
        assert_ne!(even.mul(&f0, &f0), even.scalar(r(-1)));
        assert_ne!(even.mul(&f1, &f1), even.scalar(r(-1)));
    }

    /// First documented `None`: a non-orthogonal metric (`b` or `a` nonempty)
    /// has no clean `Cl(Q)⁰ ≅ Cl(Q′)` presentation.
    #[test]
    fn even_subalgebra_none_on_nonorthogonal_metric() {
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), r(1));
        let alg_b = CliffordAlgebra::new(2, Metric::new(vec![r(1), r(1)], b));
        assert!(alg_b.even_subalgebra().is_none(), "nonzero b should reject");

        let mut a = BTreeMap::new();
        a.insert((0usize, 1usize), r(1));
        let alg_a = CliffordAlgebra::new(2, Metric::general(vec![r(1), r(1)], BTreeMap::new(), a));
        assert!(alg_a.even_subalgebra().is_none(), "nonzero a should reject");
    }

    #[test]
    fn even_subalgebra_none_when_no_generator_is_a_unit() {
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![Integer(2), Integer(4)]));
        assert!(alg.even_subalgebra().is_none());
    }

    #[test]
    fn even_part_projection() {
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![r(1), r(1)]));
        let v = alg.add(
            &alg.scalar(r(5)),
            &alg.add(
                &alg.scalar_mul(&r(2), &alg.e(0)),
                &alg.mul(&alg.e(0), &alg.e(1)),
            ),
        );
        let expect = alg.add(&alg.scalar(r(5)), &alg.mul(&alg.e(0), &alg.e(1)));
        assert_eq!(alg.even_part(&v), expect);
    }

    #[test]
    fn graded_tensor_blocks_are_orthogonal() {
        let left = CliffordAlgebra::new(1, Metric::diagonal(vec![r(1)]));
        let right = CliffordAlgebra::new(1, Metric::diagonal(vec![r(-1)]));
        let alg = left.graded_tensor(&right);
        assert_eq!(alg.dim(), 2);
        let e0 = alg.e(0);
        let e1 = alg.e(1);
        assert_eq!(alg.mul(&e0, &e0), alg.scalar(r(1)));
        assert_eq!(alg.mul(&e1, &e1), alg.scalar(r(-1)));
        assert_eq!(
            alg.mul(&e0, &e1),
            alg.scalar_mul(&r(-1), &alg.mul(&e1, &e0))
        );
        assert_eq!(alg.embed_first(&left.e(0)), e0);
        assert_eq!(alg.embed_second(&right.e(0), &left), e1);
    }

    #[test]
    fn general_product_reproduces_reduce_word_when_a_empty() {
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), r(1));
        b.insert((1usize, 2usize), r(-1));
        b.insert((0usize, 2usize), r(2));
        let m = Metric::new(vec![r(1), r(-1), r(2)], b);
        for ba in 0u128..8 {
            for bb in 0u128..8 {
                let word: Vec<usize> = bits(ba).into_iter().chain(bits(bb)).collect();
                assert_eq!(
                    m.geom_product_blades(ba, bb),
                    m.reduce_word(&word),
                    "mismatch on blades {ba:#b}·{bb:#b}"
                );
            }
        }
    }

    #[test]
    fn orthogonal_fast_product_reproduces_reduce_word() {
        let m = Metric::diagonal(vec![r(2), r(-3), r(0)]);
        assert!(m.is_orthogonal());
        for ba in 0u128..8 {
            for bb in 0u128..8 {
                let word: Vec<usize> = bits(ba).into_iter().chain(bits(bb)).collect();
                assert_eq!(
                    m.geom_product_blades(ba, bb),
                    m.reduce_word(&word),
                    "orthogonal fast-path mismatch on blades {ba:#b}·{bb:#b}"
                );
            }
        }
    }

    #[test]
    fn general_bilinear_in_order_contraction() {
        let mut a = BTreeMap::new();
        a.insert((0usize, 1usize), r(5));
        let alg = CliffordAlgebra::new(2, Metric::general(vec![r(1), r(1)], BTreeMap::new(), a));
        let (e0, e1) = (alg.e(0), alg.e(1));
        let blade = alg.wedge(&e0, &e1);
        assert_eq!(alg.mul(&e0, &e1), alg.add(&blade, &alg.scalar(r(5))));
        assert_eq!(alg.add(&alg.mul(&e0, &e1), &alg.mul(&e1, &e0)), alg.zero());
    }

    #[test]
    fn general_bilinear_gauge_transport_matches_reduce_word_oracle() {
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), r(1));
        b.insert((1usize, 2usize), r(-2));
        let mut a = BTreeMap::new();
        a.insert((0usize, 1usize), r(3));
        a.insert((0usize, 2usize), r(-1));
        a.insert((1usize, 2usize), r(4));
        let alg = CliffordAlgebra::new(3, Metric::general(vec![r(2), r(-1), r(5)], b, a));
        let ordinary = alg.ordinary_gauge_algebra();

        for ba in 0u128..8 {
            for bb in 0u128..8 {
                let a_blade = alg.blade(&bits(ba));
                let b_blade = alg.blade(&bits(bb));
                let lhs = alg.mul(&a_blade, &b_blade);
                assert_eq!(
                    alg.transport_gauge_to(&ordinary, &lhs).unwrap(),
                    ordinary.mul(
                        &alg.transport_gauge_to(&ordinary, &a_blade).unwrap(),
                        &alg.transport_gauge_to(&ordinary, &b_blade).unwrap()
                    ),
                    "gauge transport is not multiplicative on blades {ba:#b}·{bb:#b}"
                );

                let word: Vec<usize> = bits(ba).into_iter().chain(bits(bb)).collect();
                let mut source_word = alg.scalar(r(1));
                for &g in &word {
                    source_word = alg.mul(&source_word, &alg.e(g));
                }
                let in_ordinary = alg.transport_gauge_to(&ordinary, &source_word).unwrap();
                let expect = Multivector {
                    terms: ordinary.metric.reduce_word(&word),
                };
                assert_eq!(
                    in_ordinary, expect,
                    "gauge transport mismatch on blades {ba:#b}·{bb:#b}"
                );
            }
        }
    }

    #[test]
    fn reverse_is_gauge_transported_on_general_bilinear_metric() {
        let mut b = BTreeMap::new();
        b.insert((0usize, 2usize), r(1));
        let mut a = BTreeMap::new();
        a.insert((0usize, 1usize), r(3));
        a.insert((1usize, 2usize), r(-2));
        let alg = CliffordAlgebra::new(3, Metric::general(vec![r(1), r(-1), r(2)], b, a));
        let x = alg.add(&alg.e(0), &alg.mul(&alg.e(1), &alg.e(2)));
        let y = alg.add(&alg.scalar(r(2)), &alg.mul(&alg.e(0), &alg.e(1)));

        assert_eq!(
            alg.reverse(&alg.mul(&x, &y)),
            alg.mul(&alg.reverse(&y), &alg.reverse(&x))
        );
        assert_eq!(
            alg.reverse(&alg.reverse(&x)),
            x,
            "transported reverse should be involutive"
        );
    }

    #[test]
    fn associativity_general_bilinear_form() {
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), r(1));
        b.insert((1usize, 2usize), r(2));
        let mut a = BTreeMap::new();
        a.insert((0usize, 1usize), r(3));
        a.insert((0usize, 2usize), r(-1));
        let alg = CliffordAlgebra::new(3, Metric::general(vec![r(2), r(-1), r(1)], b, a));
        let gens = [
            alg.e(0),
            alg.e(1),
            alg.e(2),
            alg.mul(&alg.e(0), &alg.e(1)),
            alg.add(&alg.e(2), &alg.scalar(r(3))),
        ];
        assert_associative(&alg, &gens);

        let mut bn = BTreeMap::new();
        bn.insert((0usize, 1usize), Nimber(1));
        let mut an = BTreeMap::new();
        an.insert((0usize, 1usize), Nimber(2));
        an.insert((1usize, 2usize), Nimber(3));
        let algn = CliffordAlgebra::new(
            3,
            Metric::general(vec![Nimber(2), Nimber(1), Nimber(0)], bn, an),
        );
        let gensn = [
            algn.e(0),
            algn.e(1),
            algn.e(2),
            algn.mul(&algn.e(0), &algn.e(1)),
        ];
        assert_associative(&algn, &gensn);
    }

    // ── CliffordAlgebra::pow tests ────────────────────────────────────────────

    #[test]
    fn pow_zero_is_scalar_one() {
        // char 0
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![r(1), r(1)]));
        let e0 = alg.e(0);
        assert_eq!(alg.pow(&e0, 0), alg.scalar(r(1)));
        // char 2
        let algn = CliffordAlgebra::new(2, Metric::diagonal(vec![Nimber(1), Nimber(1)]));
        let ne0 = algn.e(0);
        assert_eq!(alg.pow(&e0, 0), alg.scalar(r(1)));
        assert_eq!(algn.pow(&ne0, 0), algn.scalar(Nimber(1)));
    }

    #[test]
    fn pow_one_is_identity() {
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![r(1), r(1)]));
        let e0 = alg.e(0);
        assert_eq!(alg.pow(&e0, 1), e0);

        let algn = CliffordAlgebra::new(2, Metric::diagonal(vec![Nimber(1), Nimber(1)]));
        let ne0 = algn.e(0);
        assert_eq!(algn.pow(&ne0, 1), ne0);
    }

    #[test]
    fn pow_e0_squared_equals_q0_char0() {
        // In Cl(p,q) over char 0, e0^2 = q[0] (the quadratic form value).
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![r(3), r(-1)]));
        let e0 = alg.e(0);
        // e0^2 should equal scalar(q[0]) = scalar(3)
        assert_eq!(alg.pow(&e0, 2), alg.scalar(r(3)));
    }

    #[test]
    fn pow_mixed_grade_element_char0() {
        // v = e0 + e1 in a 2D algebra; verify v^3 == v * v * v via three mul calls.
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![r(1), r(1)]));
        let v = alg.add(&alg.e(0), &alg.e(1));
        let v3_direct = alg.mul(&alg.mul(&v, &v), &v);
        assert_eq!(alg.pow(&v, 3), v3_direct);
    }

    #[test]
    fn pow_mixed_grade_element_char2() {
        // char-2 (Nimber): v = e0 + e1, verify pow(v,3) == v*v*v.
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![Nimber(1), Nimber(1)]));
        let v = alg.add(&alg.e(0), &alg.e(1));
        let v3_direct = alg.mul(&alg.mul(&v, &v), &v);
        assert_eq!(alg.pow(&v, 3), v3_direct);
    }
}
