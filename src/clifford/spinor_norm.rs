//! Raw multiplicative versor norms and grade parity.
//!
//! For a simple invertible versor `v = v₁⋯v_k`, the raw norm
//! `⟨v reverse(v)⟩₀ = ∏ q(v_i)`. Over a field of characteristic other than
//! two, its class modulo squares is the classical spinor norm. In
//! characteristic two, this
//! raw product is not the additive Wall/Dye invariant and must not be reduced
//! modulo Artin--Schreier elements. This module exposes grade parity there;
//! [`crate::forms::char2_spinor_norm`] implements the matrix invariant, and
//! [`crate::forms::factor_char2_isometry`] returns exact vector-symmetry
//! certificates on the symmetry-generated domain.

use crate::clifford::{CliffordAlgebra, Multivector};
use crate::scalar::Scalar;

/// The ℤ₂-grade parity of a nonzero homogeneous-parity multivector. For a
/// witnessed versor this is its Dickson/reflection parity: `0` for even and
/// `1` for odd. `None` means zero or mixed parity and therefore rules out a
/// versor, but `Some` alone does not establish versor membership.
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

/// Raw norm and grade-parity data for a versor candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VersorInvariants<S: Scalar> {
    /// The raw spinor norm `N(v) = ⟨v ṽ⟩₀ = ∏ q(vᵢ)`. Over a field of
    /// characteristic other than two, its class in `F*/F*²` is the classical
    /// spinor norm. In characteristic two this raw multiplicative value is not
    /// the classifying invariant.
    pub spinor_norm: S,
    /// Grade parity: for a witnessed versor, `0` is even and `1` is odd.
    pub dickson: u128,
}

impl<S: Scalar> VersorInvariants<S> {
    /// Returns the same representation as [`std::fmt::Display`].
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl<S: Scalar> std::fmt::Display for VersorInvariants<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // The spinor norm is rendered as a bare field element (its own Display),
        // not reduced mod squares or mod ℘ — see the module docs for why no such
        // reduction is valid in characteristic 2.
        write!(
            f,
            "VersorInvariants(spinor_norm={}, dickson={})",
            self.spinor_norm, self.dickson
        )
    }
}

impl<S: Scalar> CliffordAlgebra<S> {
    /// The raw norm `N(v) = ⟨v ṽ⟩₀`, returned when `v ṽ` is a pure invertible
    /// scalar. This scalar-norm gate does not by itself prove that `v` belongs
    /// to the Clifford group. For a witnessed versor `v = v₁⋯v_k`, the result
    /// equals `∏ q(vᵢ)`. Over an appropriate field of characteristic other than
    /// two, reduce it modulo squares to get the classical spinor-norm invariant.
    /// In characteristic two this raw value is **not** the
    /// classifying invariant and has no valid "modulo ℘" reduction — see the
    /// module docs for why, and [`versor_grade_parity`] for the char-2 invariant
    /// that IS trustworthy (Dickson).
    pub fn spinor_norm(&self, v: &Multivector<S>) -> Option<S> {
        self.pure_scalar_norm(v)
    }

    /// Bundles raw norm and grade parity for a versor candidate. Returns `None`
    /// for mixed parity or when `v ṽ` is not a pure invertible scalar. Success
    /// does not independently prove that `v` normalizes the vector space.
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
        assert_eq!(c.to_string(), "VersorInvariants(spinor_norm=1, dickson=0)");
        assert_eq!(c.display(), c.to_string());
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

    #[test]
    fn char2_spinor_norm_is_raw_multiplicative_value() {
        // A lone reflection generator: N(e0) = q0, Dickson = 1 (odd).
        let alg1 = CliffordAlgebra::new(1, Metric::diagonal(vec![Nimber(1)]));
        let e0 = alg1.e(0);
        assert_eq!(alg1.spinor_norm(&e0), Some(Nimber(1)));
        let c1 = alg1.classify_versor(&e0).unwrap();
        assert_eq!(c1.dickson, 1);
        assert_eq!(c1.spinor_norm, Nimber(1));
        // the raw norm renders plainly (via Nimber's own Display, "*1") — no
        // implied reduction mod ℘, since none exists (see the module docs).
        assert_eq!(
            c1.to_string(),
            "VersorInvariants(spinor_norm=*1, dickson=1)"
        );

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
