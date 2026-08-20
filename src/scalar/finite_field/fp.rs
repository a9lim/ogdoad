//! Prime fields `F_p` for any prime `p`, including `p = 2`.
//!
//! These fields support the generic scalar and forms algorithms. In odd
//! characteristic, quadratic-form classification uses dimension and
//! discriminant; in characteristic two, signs collapse because `−1 = 1`.
//!
//! ## The const-generic modulus
//!
//! `Scalar::zero()`/`one()` take no `self`, so the modulus cannot live in the
//! value alone. We carry it in the **type**: `Fp<P>` is the field of `P`
//! elements. A different prime is a different type — exactly the per-backend,
//! no-mixing discipline the rest of the crate already uses (you cannot
//! accidentally add an `Fp<3>` to an `Fp<5>`). `P` must be prime. Constructors
//! and scalar entry points without an existing operand validate that boundary;
//! arithmetic between existing values relies on the private-field invariant and
//! does not repeat trial division on every operation.
//!
//! For odd `P`, `neg` is genuine negation (`P − a ≠ a` for `a ≠ 0`); for
//! `P = 2`, negation is the identity.

use crate::scalar::{is_prime_u128, Scalar};
use std::fmt;

/// An element of the prime field `F_P` (invariant: `0 ≤ value < P`).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Fp<const P: u128>(u128);

pub(crate) fn add_mod<const P: u128>(a: u128, b: u128) -> u128 {
    debug_assert!(P > 0 && a < P && b < P);
    if a >= P - b {
        a - (P - b)
    } else {
        a + b
    }
}

pub(crate) fn mul_mod<const P: u128>(mut a: u128, mut b: u128) -> u128 {
    debug_assert!(P > 0 && a < P && b < P);
    if let Some(product) = a.checked_mul(b) {
        return product % P;
    }
    let mut acc = 0u128;
    while b > 0 {
        if b & 1 == 1 {
            acc = add_mod::<P>(acc, a);
        }
        b >>= 1;
        if b > 0 {
            a = add_mod::<P>(a, a);
        }
    }
    acc
}

impl<const P: u128> Fp<P> {
    /// Whether `P` is prime.
    pub fn modulus_is_prime() -> bool {
        is_prime_u128(P)
    }

    /// Validate that `P` is prime, panicking otherwise.
    pub fn assert_supported_params() {
        assert!(Self::modulus_is_prime(), "Fp<P> needs prime P, got {P}");
    }

    /// Reduce an unsigned integer into `F_P`.
    pub fn from_u128(n: u128) -> Self {
        Self::assert_supported_params();
        Fp(n % P)
    }

    /// The canonical representative in `[0, P)`.
    pub fn value(self) -> u128 {
        self.0
    }
}

impl<const P: u128> fmt::Display for Fp<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<const P: u128> fmt::Debug for Fp<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<const P: u128> Scalar for Fp<P> {
    const REASSOCIATION_IS_EXACT: bool = true;

    fn zero() -> Self {
        Self::assert_supported_params();
        Fp(0)
    }
    fn one() -> Self {
        Self::assert_supported_params();
        Fp(1 % P)
    }
    fn add(&self, rhs: &Self) -> Self {
        Fp(add_mod::<P>(self.0, rhs.0))
    }
    fn neg(&self) -> Self {
        if self.0 == 0 {
            Fp(0)
        } else {
            Fp(P - self.0)
        }
    }
    fn mul(&self, rhs: &Self) -> Self {
        Fp(mul_mod::<P>(self.0, rhs.0))
    }
    fn characteristic() -> u128 {
        Self::assert_supported_params();
        P
    }
    fn inv(&self) -> Option<Self> {
        if self.0 == 0 {
            return None;
        }
        Some(self.pow(P - 2))
    }
    fn is_zero(&self) -> bool {
        self.0 == 0
    }
    /// Faster direct construction; semantically identical to the default double-and-add.
    fn from_int(n: i128) -> Self {
        Self::assert_supported_params();
        let v = if n >= 0 {
            (n as u128) % P
        } else {
            let r = n.unsigned_abs() % P;
            if r == 0 {
                0
            } else {
                P - r
            }
        };
        Fp(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clifford::{CliffordAlgebra, Metric};

    fn elems<const P: u128>() -> Vec<Fp<P>> {
        (0..P).map(Fp::<P>::from_u128).collect()
    }

    fn check_field_axioms<const P: u128>() {
        let es = elems::<P>();
        for &a in &es {
            for &b in &es {
                // commutativity
                assert_eq!(a.add(&b), b.add(&a));
                assert_eq!(a.mul(&b), b.mul(&a));
                for &c in &es {
                    // associativity + distributivity
                    assert_eq!(a.add(&b).add(&c), a.add(&b.add(&c)));
                    assert_eq!(a.mul(&b).mul(&c), a.mul(&b.mul(&c)));
                    assert_eq!(a.mul(&b.add(&c)), a.mul(&b).add(&a.mul(&c)));
                }
            }
            // additive identity/inverse
            assert_eq!(a.add(&Fp::<P>::zero()), a);
            assert_eq!(a.add(&a.neg()), Fp::<P>::zero());
            // multiplicative inverse for nonzero
            if !a.is_zero() {
                let ai = a.inv().expect("nonzero is invertible in a field");
                assert_eq!(a.mul(&ai), Fp::<P>::one());
            } else {
                assert!(a.inv().is_none());
            }
        }
    }

    #[test]
    fn field_axioms_f5_f7() {
        check_field_axioms::<5>();
        check_field_axioms::<7>();
        check_field_axioms::<13>();
    }

    #[test]
    fn inverse_matches_brute_force() {
        for a in elems::<11>() {
            let brute = elems::<11>()
                .into_iter()
                .find(|b| a.mul(b) == Fp::<11>::one());
            assert_eq!(a.inv(), brute);
        }
    }

    #[test]
    fn negation_is_genuine() {
        // unlike nimbers, neg is a real negation: −1 = P−1 ≠ 1 for odd P.
        let one = Fp::<5>::one();
        assert_eq!(one.neg(), Fp::<5>::from_u128(4));
        assert_ne!(one.neg(), one);
        assert_eq!(Fp::<5>::from_int(-1), Fp::<5>::from_u128(4));
        assert_eq!(Fp::<5>::characteristic(), 5);
    }

    #[test]
    fn clifford_over_f3_monomorphises() {
        // Cl over F_3 with q = [1, 2]: real antisymmetry (−1 = 2), and
        // (e0e1)² = −(q0 q1) = −2 = 1 (mod 3).
        let alg = CliffordAlgebra::new(
            2,
            Metric::diagonal(vec![Fp::<3>::from_u128(1), Fp::<3>::from_u128(2)]),
        );
        let (e0, e1) = (alg.e(0), alg.e(1));
        assert_eq!(alg.mul(&e0, &e0), alg.scalar(Fp::<3>::from_u128(1)));
        assert_eq!(alg.mul(&e1, &e1), alg.scalar(Fp::<3>::from_u128(2)));
        // e0 e1 = −(e1 e0), and −1 = 2 in F_3
        assert_eq!(
            alg.mul(&e0, &e1),
            alg.scalar_mul(&Fp::<3>::from_int(-1), &alg.mul(&e1, &e0))
        );
        // (e0e1)² = 1
        let e0e1 = alg.mul(&e0, &e1);
        assert_eq!(alg.mul(&e0e1, &e0e1), alg.scalar(Fp::<3>::from_u128(1)));
    }

    #[test]
    fn composite_modulus_is_rejected() {
        assert!(std::panic::catch_unwind(Fp::<4>::one).is_err());
        assert!(std::panic::catch_unwind(|| Fp::<9>::from_int(2)).is_err());
    }

    #[test]
    fn arithmetic_reuses_the_valid_operand_invariant() {
        // Every public constructor validates P. Once values exist, their private
        // representation proves both the prime parameter and reduced payload,
        // so arithmetic can stay on the hot path without changing results.
        for a in 0..257u128 {
            for b in 0..257u128 {
                let a = Fp::<257>::from_u128(a);
                let b = Fp::<257>::from_u128(b);
                assert_eq!(a.add(&b).value(), (a.value() + b.value()) % 257);
                assert_eq!(a.mul(&b).value(), (a.value() * b.value()) % 257);
            }
        }
    }
}
