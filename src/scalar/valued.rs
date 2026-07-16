//! The [`Valued`] trait: a scalar carrying a discrete valuation and a canonical
//! uniformizer.
//!
//! Every backend in the **non-Archimedean local** part of the "any number" table
//! already exposes an *inherent* `valuation()` and a way to name its prime element
//! ([`Qp`]/[`Qq`] via `from_p_power(1)`,
//! [`Laurent`] via `t()`). This trait promotes that shared
//! shape to the type system so the [`Ramified`](crate::scalar::Ramified)
//! ramified-extension functor can fold a *generic* base valuation — it adjoins a
//! uniformizer `π` with `πᴱ = ϖ`, and `ϖ = S::uniformizer()` is exactly the datum
//! it needs from the base field.
//!
//! Deliberately **not** a [`Scalar`] supertrait (same reasoning as the operator
//! manifest): only the discretely-valued local fields are `Valued`. The exact
//! Archimedean worlds (`Rational`, `Surreal`) carry no canonical uniformizer and
//! are intentionally left out. The rings of integers (`Zp`, `WittVec`) are also
//! left out: a `Ramified` base must be a *field* so its `inv` is total on
//! nonzero.

use crate::scalar::tropical::{MinPlus, Tropical};
use crate::scalar::{Laurent, Qp, Qq, Scalar};

/// A scalar with a discrete valuation `v : K → ℤ ∪ {∞}` and a canonical
/// uniformizer `ϖ` (the valuation-`1` element). The valuation here is the same
/// one each backend exposes inherently; this trait just makes it generic.
///
/// # The valuation is the (lax) tropicalization
///
/// Read into the min-plus semiring [`Tropical<MinPlus>`](crate::scalar::Tropical),
/// the valuation [`v`](Valued::valuation) is exactly the **tropicalization** map
/// `τ : K → 𝕋` of [`tropicalize`] — a homomorphism of multiplicative monoids that
/// is *lax* (subadditive) for addition (Bridge J, Lemma J.1):
///
/// ```text
/// v(x·y)   = v(x) + v(y)                        (the tropical ⊗ — strict)
/// v(x + y) ≥ min(v(x), v(y))                    (the tropical ⊕ — lax)
/// v(x + y) = min(v(x), v(y))   if v(x) ≠ v(y)   (strict off the vanishing locus)
/// ```
///
/// So the whole `Valued` stack already *is* the tropicalization the games pillar
/// computes unnamed in thermography — the same `(min, +)` algebra on the *place*
/// axis. "Is the tropicalization" is meant **laxly**: no discretely-valued field
/// admits a strict additive homomorphism onto `𝕋` (the vanishing locus, e.g.
/// `v(1 + (−1)) = ∞ ≠ 0`); strictness is restored only by the tropical hyperfield
/// [Viro 2010], or by taking the three lines above as the *definition* of a
/// valuation [Maclagan–Sturmfels Ch. 2].
pub trait Valued: Scalar {
    /// The valuation of this element, or `None` for zero (valuation `+∞`).
    fn valuation(&self) -> Option<i128>;

    /// The canonical uniformizer `ϖ` — the prime element of valuation `1`
    /// (`p` for `Qp`/`Qq`, `t` for `Laurent`).
    fn uniformizer() -> Self;
}

/// The **tropicalization** `τ(x) = v(x)` of a valued field, into the min-plus
/// tropical semiring (`None`/zero ↦ `∞`, the `⊕`-identity). This is the thin
/// adaptor naming the map the `Valued` trait already computes; see the trait docs
/// for the lax-homomorphism laws it satisfies (Bridge J).
pub fn tropicalize<K: Valued>(x: &K) -> Tropical<MinPlus> {
    match x.valuation() {
        Some(v) => Tropical::int(v),
        None => Tropical::infinity(),
    }
}

impl<const P: u128, const K: u128> Valued for Qp<P, K> {
    fn valuation(&self) -> Option<i128> {
        // Inherent `Qp::valuation` shadows this trait method in method-call
        // position, so this delegates rather than recursing.
        Qp::valuation(self)
    }
    fn uniformizer() -> Self {
        Qp::from_p_power(1)
    }
}

impl<const P: u128, const N: usize, const F: usize> Valued for Qq<P, N, F> {
    fn valuation(&self) -> Option<i128> {
        Qq::valuation(self)
    }
    fn uniformizer() -> Self {
        Qq::from_p_power(1)
    }
}

impl<S: Scalar, const K: usize> Valued for Laurent<S, K> {
    fn valuation(&self) -> Option<i128> {
        Laurent::valuation(self)
    }
    fn uniformizer() -> Self {
        Laurent::t()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{Fp, Rational};

    #[test]
    fn uniformizers_have_valuation_one() {
        assert_eq!(Qp::<5, 4>::uniformizer().valuation(), Some(1));
        assert_eq!(Qq::<3, 4, 2>::uniformizer().valuation(), Some(1));
        assert_eq!(Laurent::<Rational, 6>::uniformizer().valuation(), Some(1));
        assert_eq!(Laurent::<Fp<7>, 6>::uniformizer().valuation(), Some(1));
    }

    #[test]
    fn zero_valuation_is_none() {
        assert_eq!(<Qp<5, 4> as Valued>::valuation(&Qp::zero()), None);
        assert_eq!(
            <Laurent<Rational, 6> as Valued>::valuation(&Laurent::zero()),
            None
        );
    }

    #[test]
    fn trait_valuation_matches_inherent() {
        let x = Qp::<5, 4>::from_int(50); // 2·5²  ⇒ valuation 2
        assert_eq!(<Qp<5, 4> as Valued>::valuation(&x), x.valuation());
        assert_eq!(<Qp<5, 4> as Valued>::valuation(&x), Some(2));
    }

    // --- Bridge J: the valuation is the (lax) tropicalization (Lemma J.1) ---

    /// `τ(x·y) = τ(x) ⊗ τ(y)` — multiplicativity, exact, zero included (J.1(i)).
    #[test]
    fn tropicalize_is_multiplicative() {
        type Q = Qp<5, 8>;
        let samples = [
            Q::from_int(1),
            Q::from_int(5),      // val 1
            Q::from_int(50),     // val 2
            Q::from_int(7),      // val 0 unit
            Q::from_p_power(-1), // val −1
            Q::zero(),           // val ∞
        ];
        for x in &samples {
            for y in &samples {
                assert_eq!(
                    tropicalize(&x.mul(y)),
                    tropicalize(x).mul(&tropicalize(y)),
                    "τ(xy) ≠ τ(x)⊗τ(y)"
                );
            }
        }
    }

    /// The `⊕`-internal subadditivity `τ(x+y) ⊕ (τx ⊕ τy) = τx ⊕ τy` (J.1(ii)),
    /// truncation-safe: a deep cancellation that renders the sum as `0` gives
    /// `τ = ∞` on the left and the identity still holds.
    #[test]
    fn tropicalize_is_subadditive() {
        type Q = Qp<5, 8>;
        let samples = [
            Q::from_int(1),
            Q::from_int(5),
            Q::from_int(6), // 1 + 5, val 0
            Q::from_int(25),
            Q::from_int(-1),
            Q::zero(),
        ];
        for x in &samples {
            for y in &samples {
                let s = tropicalize(x).add(&tropicalize(y)); // min(v x, v y)
                assert_eq!(tropicalize(&x.add(y)).add(&s), s, "subadditivity J.1(ii)");
            }
        }
    }

    /// Equality off the tropical vanishing locus: `τx ≠ τy ⇒ τ(x+y) = τx ⊕ τy`
    /// (J.1(iii)) — exact even in the capped models (the leading term survives).
    #[test]
    fn tropicalize_equality_off_vanishing_locus() {
        type Q = Qp<5, 8>;
        let samples = [
            Q::from_int(1),
            Q::from_int(5),
            Q::from_int(25),
            Q::from_int(7),
            Q::from_p_power(-1),
        ];
        for x in &samples {
            for y in &samples {
                if tropicalize(x) != tropicalize(y) {
                    assert_eq!(
                        tropicalize(&x.add(y)),
                        tropicalize(x).add(&tropicalize(y)),
                        "off the vanishing locus the min is strict"
                    );
                }
            }
        }
    }

    /// The adaptor is genuinely generic across the discretely-valued legs.
    #[test]
    fn tropicalize_is_generic_over_legs() {
        assert_eq!(
            tropicalize(&Qq::<3, 4, 2>::from_p_power(1)),
            Tropical::int(1)
        );
        assert_eq!(tropicalize(&Laurent::<Fp<7>, 6>::t()), Tropical::int(1));
        assert!(tropicalize(&Qp::<5, 4>::zero()).is_infinity());
    }
}
