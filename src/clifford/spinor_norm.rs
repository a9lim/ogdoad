//! The spinor norm `N: O(Q) → F*/F*²` and the Dickson grade parity — the two
//! invariants that, together, pin down a versor's place in the Pin/Spin tower,
//! **in characteristic ≠ 2**.
//!
//! `forms::char2` already classifies isometries in characteristic 2 by the
//! **Dickson invariant** (`SO(Q) = ker D`). The companion across the *other*
//! characteristics is the **spinor norm**: the Pin map sends a versor
//! `v = v₁⋯v_k` (a product of vectors) to the composite of the reflections in the
//! `v_i`; the cokernel over a general field is measured by the spinor norm map
//! `O(Q) → F*/F*²`. Concretely, in characteristic ≠ 2, `N(v) = ∏ q(v_i) = ⟨v ṽ⟩₀`
//! read modulo squares IS that invariant, and the pair `(Dickson parity, spinor
//! norm)` is what separates the four cosets `Pin/Spin × ±` of `O(Q)` there.
//!
//! ## The characteristic-2 caveat (pinned)
//!
//! In characteristic 2 the codomain is **not** `F*/F*²`. There `x ↦ x²` is the
//! Frobenius (a bijection on a perfect field), so every element is a square and
//! `F*/F*²` is trivial — the multiplicative spinor norm collapses. The correct
//! char-2 spinor norm (Wall/Dye) is **additive**, valued in `F/℘(F)` (the
//! Artin–Schreier group, `℘(x) = x² + x`) — the very group the Arf invariant is
//! pushed into by the field trace (`scalar::nim_trace`) — and it is defined as
//! `Σ Q(vᵢ) mod ℘` over a *vector* factorization `v = v₁⋯v_k`: an ADDITIVE
//! combination of the individual `Q(vᵢ)`, not a function of the raw product `N(v)`.
//!
//! **`N(v)` cannot be reduced into that additive invariant.** `N` is a product
//! (`∏ q(vᵢ)`), and there is no map from `(F*, ·)` to the additive group `F/℘(F)`
//! that recovers `Σ Q(vᵢ) mod ℘` from it — so "reduce `N(v)` mod ℘" is not a
//! meaningful operation, let alone the classifying one. Concretely: the versor
//! `w = v·v = Q(v)·1` represents the identity map (a double reflection), so its
//! honest invariant must be the zero coset for *every* choice of `v`. But
//! `N(w) = Q(v)²`, and `x² ≡ x mod ℘` for every `x` (since `℘(x) = x² + x ∈ ℘(F)`)
//! — so naively reading `N(w)`'s class mod ℘ gives the class of `Q(v)`, which
//! varies with `v` and is generically nonzero. The recipe is not even
//! well-defined on `O(Q)`, let alone equal to the Wall/Dye invariant.
//!
//! So in characteristic 2 this module exposes only the **raw** norm `⟨v ṽ⟩₀`
//! (correct as a bare element of `F`, with no invariant meaning attached) and
//! [`versor_grade_parity`] (Dickson). The honest additive char-2 spinor-norm
//! invariant is **not implemented** here — computing it needs a witnessed vector
//! factorization of `v`, which this module does not track.

use crate::clifford::{CliffordAlgebra, Multivector};
use crate::scalar::Scalar;

/// The **Dickson invariant** of a versor: its ℤ₂-grade parity. `0` for an even
/// versor (a rotor, in `SO`), `1` for an odd versor (an odd number of reflections).
/// `None` if the multivector is not of homogeneous grade parity — hence not a
/// versor — or is zero. Generic over the scalar (the char-2 `Nimber` specialisation
/// `forms::dickson_of_versor` delegates here).
pub fn versor_grade_parity<S: Scalar>(v: &Multivector<S>) -> Option<u128> {
    let mut parity: Option<u128> = None;
    for &blade in v.terms.keys() {
        let p = (blade.count_ones() % 2) as u128;
        match parity {
            None => parity = Some(p),
            Some(q) if q != p => return None,
            _ => {}
        }
    }
    parity
}

/// The classification of a versor: its raw spinor norm `⟨v ṽ⟩₀ ∈ F` together with
/// its Dickson grade parity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VersorInvariants<S: Scalar> {
    /// The raw spinor norm `N(v) = ⟨v ṽ⟩₀ = ∏ q(vᵢ)`. In characteristic ≠ 2 its
    /// class in `F*/F*²` is the honest spinor-norm invariant. In characteristic
    /// 2 this raw (multiplicative) value is NOT the classifying invariant — see
    /// the module docs — and no reduction of it is; treat it as a bare element
    /// of `F` with no invariant meaning attached there.
    pub spinor_norm: S,
    /// The Dickson invariant (grade parity): `0` in `SO`, `1` an odd reflection.
    pub dickson: u128,
}

impl<S: Scalar> CliffordAlgebra<S> {
    /// The **raw spinor norm** `N(v) = ⟨v ṽ⟩₀` of a versor `v`, returned as a field
    /// element: `Some(N)` iff `v ṽ` is a pure invertible scalar (the same
    /// invertibility gate as [`versor_inverse`](CliffordAlgebra::versor_inverse) —
    /// literally shared, via `pure_scalar_norm`); `None` if `v` is not a simple
    /// invertible versor. For `v = v₁⋯v_k` this equals `∏ q(vᵢ)`. In
    /// characteristic ≠ 2, reduce it modulo squares to get the classifying
    /// spinor-norm invariant. In characteristic 2 this raw value is **not** the
    /// classifying invariant and has no valid "modulo ℘" reduction — see the
    /// module docs for why, and [`versor_grade_parity`] for the char-2 invariant
    /// that IS trustworthy (Dickson).
    pub fn spinor_norm(&self, v: &Multivector<S>) -> Option<S> {
        self.pure_scalar_norm(v)
    }

    /// Classify a versor by `(spinor norm, Dickson parity)`. `None` if `v` is not a
    /// versor (mixed grade parity, or `v ṽ` not scalar).
    pub fn classify_versor(&self, v: &Multivector<S>) -> Option<VersorInvariants<S>> {
        let dickson = versor_grade_parity(v)?;
        let spinor_norm = self.spinor_norm(v)?;
        Some(VersorInvariants {
            spinor_norm,
            dickson,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clifford::Metric;
    use crate::scalar::{Nimber, Rational};

    fn cl3() -> CliffordAlgebra<Rational> {
        // Cl(3,0) over ℚ: q = [1,1,1], orthonormal.
        CliffordAlgebra::new(
            3,
            Metric::diagonal(vec![Rational::one(), Rational::one(), Rational::one()]),
        )
    }

    #[test]
    fn spinor_norm_of_a_reflection_is_q_of_the_vector() {
        let alg = cl3();
        // a unit reflection vector e0: N = q0 = 1.
        assert_eq!(alg.spinor_norm(&alg.e(0)), Some(Rational::one()));
        // a non-unit vector v = e0 + e1: N = q0 + q1 = 2 (a nonsquare class in ℚ).
        let v = alg.add(&alg.e(0), &alg.e(1));
        assert_eq!(alg.spinor_norm(&v), Some(Rational::from_int(2)));
    }

    #[test]
    fn spinor_norm_is_multiplicative_on_versors() {
        let alg = cl3();
        let v = alg.add(&alg.e(0), &alg.e(1)); // N = 2
        let w = alg.e(2); // N = 1
        let vw = alg.mul(&v, &w);
        let nv = alg.spinor_norm(&v).unwrap();
        let nw = alg.spinor_norm(&w).unwrap();
        let nvw = alg.spinor_norm(&vw).unwrap();
        assert_eq!(nvw, nv.mul(&nw)); // N(vw) = N(v)·N(w)
    }

    #[test]
    fn dickson_parity_counts_reflections_mod_two() {
        let alg = cl3();
        let scalar_one = alg.scalar(Rational::one());
        let e0 = alg.e(0);
        let e0e1 = alg.mul(&alg.e(0), &alg.e(1));
        let e0e1e2 = alg.mul(&e0e1, &alg.e(2));
        assert_eq!(versor_grade_parity(&scalar_one), Some(0)); // identity rotor
        assert_eq!(versor_grade_parity(&e0), Some(1)); // 1 reflection
        assert_eq!(versor_grade_parity(&e0e1), Some(0)); // 2 reflections (rotor)
        assert_eq!(versor_grade_parity(&e0e1e2), Some(1)); // 3 reflections
                                                           // mixed grade parity ⇒ not a versor
        let mixed = alg.add(&e0, &e0e1);
        assert_eq!(versor_grade_parity(&mixed), None);
        assert_eq!(alg.classify_versor(&mixed), None);
    }

    #[test]
    fn classify_versor_bundles_both() {
        let alg = cl3();
        let e0e1 = alg.mul(&alg.e(0), &alg.e(1));
        let c = alg.classify_versor(&e0e1).unwrap();
        assert_eq!(c.dickson, 0); // a rotor
        assert_eq!(c.spinor_norm, Rational::one()); // q0·q1 = 1
    }

    #[test]
    fn null_homogeneous_elements_are_not_versors() {
        let alg = CliffordAlgebra::<Rational>::new(1, Metric::grassmann(1));
        let e0 = alg.e(0);
        assert_eq!(versor_grade_parity(&e0), Some(1));
        assert_eq!(alg.spinor_norm(&e0), None);
        assert_eq!(alg.classify_versor(&e0), None);
    }

    #[test]
    fn generic_parity_agrees_with_char2_dickson() {
        // The generic versor_grade_parity reproduces forms::dickson_of_versor on the
        // Nimber backend — the char-2 Dickson is this same grade parity.
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![Nimber(1), Nimber(1)]));
        let e0 = alg.e(0);
        let e0e1 = alg.mul(&alg.e(0), &alg.e(1));
        assert_eq!(
            versor_grade_parity(&e0),
            crate::forms::dickson_of_versor(&alg, &e0)
        );
        assert_eq!(
            versor_grade_parity(&e0e1),
            crate::forms::dickson_of_versor(&alg, &e0e1)
        );
    }

    /// Pins the CURRENT (honest, non-classifying-in-char-2) behavior of
    /// `spinor_norm`/`classify_versor` over `Nimber`: the method returns the raw
    /// `⟨v ṽ⟩₀`, not the Wall/Dye additive invariant (see the module docs for why
    /// no such reduction exists). No claim here that these values classify
    /// anything — only that this is what the code returns today.
    #[test]
    fn char2_spinor_norm_and_classify_versor_pin_current_behavior() {
        // A lone reflection generator: N(e0) = q0, Dickson = 1 (odd).
        let alg1 = CliffordAlgebra::new(1, Metric::diagonal(vec![Nimber(1)]));
        let e0 = alg1.e(0);
        assert_eq!(alg1.spinor_norm(&e0), Some(Nimber(1)));
        let c1 = alg1.classify_versor(&e0).unwrap();
        assert_eq!(c1.dickson, 1);
        assert_eq!(c1.spinor_norm, Nimber(1));

        // A rotor e0*e1 on a nonorthogonal char-2 metric ({e0,e1} = 1): even
        // Dickson parity, raw norm N(rotor) = 1 (computed from the same
        // v * reverse(v) gate `pure_scalar_norm` shares with `versor_inverse`).
        let mut b = std::collections::BTreeMap::new();
        b.insert((0usize, 1usize), Nimber(1));
        let alg2 = CliffordAlgebra::new(2, Metric::new(vec![Nimber(1), Nimber(1)], b));
        let rotor = alg2.mul(&alg2.e(0), &alg2.e(1));
        assert_eq!(alg2.spinor_norm(&rotor), Some(Nimber(1)));
        let c2 = alg2.classify_versor(&rotor).unwrap();
        assert_eq!(c2.dickson, 0);
        assert_eq!(c2.spinor_norm, Nimber(1));
    }
}
