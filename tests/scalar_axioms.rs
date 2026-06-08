//! Property-based commutative-ring axioms, run across every `Scalar` backend.
//!
//! The Clifford engine is generic over `Scalar` and *assumes* a commutative
//! ring; these proptests are the safety net under that assumption. One generic
//! [`ring_axioms`] checker is fed randomized triples from each backend's own
//! strategy, so a regression in any backend's arithmetic surfaces here rather
//! than as a mysterious geometric-product failure.

use pleroma::scalar::{
    Fp, Integer, Nimber, Poly, Rational, RationalFunction, Scalar, Surcomplex, Surreal,
};
use proptest::prelude::*;

/// Every commutative-ring law, checked on one triple `(a, b, c)`.
fn ring_axioms<S: Scalar>(a: &S, b: &S, c: &S) {
    // (R, +) is an abelian group
    assert!(a.add(b).add(c) == a.add(&b.add(c)), "+ associative");
    assert!(a.add(b) == b.add(a), "+ commutative");
    assert!(a.add(&S::zero()) == *a, "0 is the additive identity");
    assert!(a.add(&a.neg()).is_zero(), "−a is the additive inverse");

    // (R, ·) is a commutative monoid
    assert!(a.mul(b).mul(c) == a.mul(&b.mul(c)), "· associative");
    assert!(a.mul(b) == b.mul(a), "· commutative");
    assert!(a.mul(&S::one()) == *a, "1 is the multiplicative identity");

    // distributivity, both sides (· need not be symmetric in the engine sense,
    // but the scalar ring is genuinely commutative)
    assert!(
        a.mul(&b.add(c)) == a.mul(b).add(&a.mul(c)),
        "left distributive"
    );
    assert!(
        a.add(b).mul(c) == a.mul(c).add(&b.mul(c)),
        "right distributive"
    );

    // derived subtraction is consistent with negate-then-add
    assert!(a.sub(b) == a.add(&b.neg()), "a − b = a + (−b)");

    // inverse round-trips wherever it exists
    if let Some(ai) = a.inv() {
        assert!(a.mul(&ai) == S::one(), "a · a⁻¹ = 1");
        assert!(ai.mul(a) == S::one(), "a⁻¹ · a = 1");
    }
}

// --- per-backend element strategies (small, to keep arithmetic exact) ---

fn nimbers() -> impl Strategy<Value = Nimber> {
    // any element of F_{2^64} ⊂ F_{2^128}; spans many nim-subfields
    any::<u64>().prop_map(|x| Nimber(x as u128))
}

fn integers() -> impl Strategy<Value = Integer> {
    (-1000i128..1000).prop_map(Integer)
}

fn rationals() -> impl Strategy<Value = Rational> {
    (-40i128..40, 1i128..40).prop_map(|(n, d)| Rational::new(n, d))
}

fn fp7() -> impl Strategy<Value = Fp<7>> {
    any::<i64>().prop_map(|x| Fp::<7>::new(x as i128))
}

/// Small surreals: a handful of monomials `ω^e · (p/q)` with `e ∈ [−2,2]`.
fn surreals() -> impl Strategy<Value = Surreal> {
    prop::collection::vec((-2i128..=2, -4i128..=4, 1i128..=4), 0..3).prop_map(|terms| {
        terms.into_iter().fold(Surreal::zero(), |acc, (e, p, q)| {
            acc.add(&Surreal::monomial(
                Surreal::from_int(e),
                Rational::new(p, q),
            ))
        })
    })
}

fn surcomplexes() -> impl Strategy<Value = Surcomplex<Surreal>> {
    (surreals(), surreals()).prop_map(|(re, im)| Surcomplex::new(re, im))
}

/// Small rational functions over `F_7`: `num/den` with `num, den` of degree < 3,
/// the denominator forced nonzero. `F_q(t)` is exact, so — unlike the local
/// precision models — it belongs in this exact-ring fuzz.
fn rational_functions() -> impl Strategy<Value = RationalFunction<Fp<7>>> {
    let coeffs = || prop::collection::vec((0i128..7).prop_map(Fp::<7>::new), 0..3);
    (coeffs(), coeffs()).prop_map(|(num, den)| {
        let den = if Poly::new(den.clone()).is_zero() {
            vec![Fp::<7>::new(1)]
        } else {
            den
        };
        RationalFunction::new(num, den)
    })
}

macro_rules! axiom_suite {
    ($name:ident, $ty:ty, $strat:expr) => {
        proptest! {
            #![proptest_config(ProptestConfig::with_cases(256))]
            #[test]
            fn $name(a in $strat, b in $strat, c in $strat) {
                ring_axioms::<$ty>(&a, &b, &c);
            }
        }
    };
}

axiom_suite!(nimber_ring_axioms, Nimber, nimbers());
axiom_suite!(integer_ring_axioms, Integer, integers());
axiom_suite!(rational_ring_axioms, Rational, rationals());
axiom_suite!(fp7_field_axioms, Fp<7>, fp7());
axiom_suite!(surreal_ring_axioms, Surreal, surreals());
axiom_suite!(surcomplex_ring_axioms, Surcomplex<Surreal>, surcomplexes());
axiom_suite!(
    rational_function_field_axioms,
    RationalFunction<Fp<7>>,
    rational_functions()
);
