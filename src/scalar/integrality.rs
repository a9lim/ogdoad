//! The (field, ring of integers) pairing, made **structural**.
//!
//! The "any number" table in [`scalar`](crate::scalar) is organised around one
//! recurring relationship: almost every field ships beside its **ring of
//! integers** — `ℚ`/`ℤ`, `No`/`Oz`, `Q_p`/`Z_p`, `Q_q`/`W_N(F_q)`. Until now
//! that pairing lived only in doc comments. These two traits promote it to the
//! type system, so the relationship is checkable rather than merely described:
//!
//!   * [`HasFractionField`] — a ring `R` knows its field of fractions and the
//!     canonical embedding `R ↪ Frac(R)`.
//!   * [`HasRingOfIntegers`] — a field `K` knows its ring of integers (the
//!     valuation / integrality subring) and the integrality test `K → R ∪ {⊥}`.
//!
//! They are linked: `HasRingOfIntegers::Int` is bounded by
//! `HasFractionField<Frac = Self>`, so the ring of integers of `K` is a ring
//! whose fraction field is `K` again. That closes the loop at the type level, and
//! the generic round-trip law `frac ∘ int = id` (an embedded ring element is
//! integral and recovers itself) is exercised in [`tests`] for every pair.
//!
//! ## What is and isn't paired
//!
//! The four pairs above are exactly the table rows where the field and its ring
//! of integers are **distinct backends**. The [`Laurent`](crate::scalar::Laurent)
//! functor is the one case where they share a type: the ring of integers `F_q[[t]]`
//! of `F_q((t))` is the valuation subring (`Laurent::is_integral`, valuation `≥ 0`)
//! *inside* the same `Laurent<S, K>`, not a separate world — so it stays outside
//! this trait pairing, honestly, rather than pointing `Int` at itself.

use crate::scalar::{Integer, Omnific, Qp, Qq, Rational, Scalar, Surreal, WittVec, Zp};

/// A (commutative) ring that knows its field of fractions.
pub trait HasFractionField: Scalar {
    /// The field of fractions `Frac(R)`.
    type Frac: Scalar;
    /// The canonical ring embedding `R ↪ Frac(R)`.
    fn to_fraction(&self) -> Self::Frac;
}

/// A field that knows its ring of integers — the valuation / integrality subring.
pub trait HasRingOfIntegers: Scalar {
    /// The ring of integers, itself a ring whose fraction field is `Self`.
    type Int: HasFractionField<Frac = Self>;
    /// Whether this element lies in the ring of integers.
    fn is_integral(&self) -> bool;
    /// This element as a ring-of-integers element, or `None` if it is not integral.
    fn to_integer(&self) -> Option<Self::Int>;
}

// ───────────────────────── ℤ ⊂ ℚ ─────────────────────────

impl HasFractionField for Integer {
    type Frac = Rational;
    fn to_fraction(&self) -> Rational {
        Rational::int(self.0)
    }
}

impl HasRingOfIntegers for Rational {
    type Int = Integer;
    fn is_integral(&self) -> bool {
        self.is_integer()
    }
    fn to_integer(&self) -> Option<Integer> {
        if self.is_integer() {
            Some(Integer(self.numer()))
        } else {
            None
        }
    }
}

// ───────────────────────── Oz ⊂ No ─────────────────────────

impl HasFractionField for Omnific {
    type Frac = Surreal;
    fn to_fraction(&self) -> Surreal {
        self.inner().clone()
    }
}

impl HasRingOfIntegers for Surreal {
    type Int = Omnific;
    fn is_integral(&self) -> bool {
        Omnific::from_surreal(self.clone()).is_some()
    }
    fn to_integer(&self) -> Option<Omnific> {
        Omnific::from_surreal(self.clone())
    }
}

// ───────────────────────── Z_p ⊂ Q_p ─────────────────────────

impl<const P: u128, const K: u128> HasFractionField for Zp<P, K> {
    type Frac = Qp<P, K>;
    fn to_fraction(&self) -> Qp<P, K> {
        Qp::from_i128(self.0 as i128)
    }
}

impl<const P: u128, const K: u128> HasRingOfIntegers for Qp<P, K> {
    type Int = Zp<P, K>;
    fn is_integral(&self) -> bool {
        // valuation ≥ 0 (zero has valuation +∞, hence integral).
        self.valuation().map_or(true, |v| v >= 0)
    }
    fn to_integer(&self) -> Option<Zp<P, K>> {
        let Some(v) = self.valuation() else {
            return Some(Zp(0)); // zero
        };
        if v < 0 {
            return None;
        }
        // residue = unit · p^v  (mod p^k)
        let m = Qp::<P, K>::modulus();
        let mut acc = self.unit() % m;
        for _ in 0..v {
            acc = (acc.wrapping_mul(P)) % m;
        }
        Some(Zp(acc))
    }
}

// ───────────────────────── W_N(F_q) ⊂ Q_q ─────────────────────────

impl<const P: u128, const N: usize, const F: usize> HasFractionField for WittVec<P, N, F> {
    type Frac = Qq<P, N, F>;
    fn to_fraction(&self) -> Qq<P, N, F> {
        Qq::from_witt(*self)
    }
}

impl<const P: u128, const N: usize, const F: usize> HasRingOfIntegers for Qq<P, N, F> {
    type Int = WittVec<P, N, F>;
    fn is_integral(&self) -> bool {
        self.valuation().map_or(true, |v| v >= 0)
    }
    fn to_integer(&self) -> Option<WittVec<P, N, F>> {
        let Some(v) = self.valuation() else {
            return Some(WittVec::zero()); // zero
        };
        if v < 0 {
            return None;
        }
        // ring element = unit · p^v  in W_N(F_q)
        let p = WittVec::<P, N, F>::from_int(P as i128);
        let mut acc = self.unit();
        for _ in 0..v {
            acc = acc.mul(&p);
        }
        Some(acc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::Debug;

    /// The pairing law in one shot: a ring element embeds to an integral field
    /// element that recovers itself (`frac ∘ int = id`), and a non-integral field
    /// element is correctly rejected.
    fn assert_pairs<R>(r: &R)
    where
        R: HasFractionField + PartialEq + Debug,
        R::Frac: HasRingOfIntegers<Int = R>,
    {
        let x = r.to_fraction();
        assert!(
            x.is_integral(),
            "embedded ring element must be integral: {x:?}"
        );
        assert_eq!(
            x.to_integer().as_ref(),
            Some(r),
            "frac∘int round-trip failed"
        );
    }

    #[test]
    fn integer_rational_pairing() {
        for n in -6i128..=6 {
            assert_pairs(&Integer(n));
        }
        // a genuine fraction is not integral
        let half = Rational::new(1, 2);
        assert!(!half.is_integral());
        assert_eq!(half.to_integer(), None);
        // an integer-valued rational is
        assert!(Rational::int(4).is_integral());
        assert_eq!(Rational::int(4).to_integer(), Some(Integer(4)));
    }

    #[test]
    fn omnific_surreal_pairing() {
        assert_pairs(&Omnific::from_int(3));
        assert_pairs(&Omnific::omega()); // ω is an omnific integer
        assert_pairs(&Omnific::from_surreal(Surreal::omega_pow(Surreal::from_int(2))).unwrap());
        // ε and a fractional number are not integral surreals
        assert!(!Surreal::epsilon().is_integral());
        assert_eq!(Surreal::epsilon().to_integer(), None);
        assert!(!Surreal::from_rational(Rational::new(1, 2)).is_integral());
    }

    #[test]
    fn zp_qp_pairing() {
        for r in 0..27u128 {
            assert_pairs(&Zp::<3, 3>(r));
        }
        // 1/p is a genuine fraction: valuation -1, not integral.
        let inv_p = Qp::<3, 3>::from_p_power(-1);
        assert!(!inv_p.is_integral());
        assert_eq!(inv_p.to_integer(), None);
        // p itself IS integral and lands on Zp(p).
        let p = Qp::<3, 3>::from_i128(3);
        assert!(p.is_integral());
        assert_eq!(p.to_integer(), Some(Zp::<3, 3>(3)));
    }

    #[test]
    fn wittvec_qq_pairing() {
        // W_2(F_4) ⊂ Q_4: every ring element round-trips through the fraction field.
        for code in 0..16u128 {
            assert_pairs(&WittVec::<2, 2, 2>([code & 3, (code >> 2) & 3]));
        }
        // 1/p is not integral in Q_4.
        let inv_p = Qq::<2, 4, 2>::from_p_power(-1);
        assert!(!inv_p.is_integral());
        assert_eq!(inv_p.to_integer(), None);
        // a Witt unit with genuine F_4 residue is integral and recovers itself.
        let u = WittVec::<2, 4, 2>([1, 1]);
        assert!(u.to_fraction().is_integral());
        assert_eq!(u.to_fraction().to_integer(), Some(u));
    }
}
