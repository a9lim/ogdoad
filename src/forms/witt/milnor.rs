//! Bridge N.1 — Milnor's exact sequence: the Springer residues assembled globally.
//!
//! The shipped Springer engine (`springer/`) computes per-place residue buckets and
//! the local–global layer decides per-form isotropy, but the Witt-**group**-level
//! global statement is assembled nowhere. Milnor's exact sequence supplies it
//! (Milnor–Husemoller, *Symmetric Bilinear Forms*, Ch. IV; Lam, GSM 67, Ch. IX):
//!
//! ```text
//! 0 → W(ℤ) → W(ℚ) →∂ ⊕_p W(F_p) → 0        (exact)
//! ```
//!
//! The kernel `W(ℤ) ≅ ℤ` is detected by the **signature**; for odd `p`, the boundary
//! `∂_p` is the **second Springer residue** lifted from `LocalResidueForm` buckets to
//! Witt classes. For `p = 2`, Milnor's hand-defined boundary lands in
//! `W(F₂) ≅ ℤ/2`: a diagonal line contributes exactly when its `2`-adic valuation is
//! odd (the residue unit is then the unique nonzero element of `F₂`). So
//! `(signature, (∂_p)_p)` is a *complete* invariant of `W(ℚ)`: two rational diagonal
//! forms are Witt-equivalent over `ℚ` iff they share a signature and all residues —
//! the sequence ties three pillar surfaces together (the Springer residues, the
//! global field layer, and the integral pillar's signature).
//!
//! **Claim level:** standard math (Milnor; Lam GSM 67, Ch. IX) made computational.
//! The residue is computed directly from the `i128` entries (`v_p`, the Legendre
//! symbol, and the signed-discriminant square class), matching the
//! [`finite_odd_witt`](crate::forms::finite_odd_witt) convention, so it is **exact**;
//! `springer_decompose_qp` on the capped `Q_p` model is the cross-check oracle.
//!
//! **The `∂₂` boundary (load-bearing).** `∂₂` (residue characteristic 2) is **not**
//! Springer's second residue — Milnor defines it by hand in Ch. IV. This module uses
//! the crate's existing char-2 [`WittClassG`] carrier as the `W(F₂) ≅ ℤ/2` target:
//! `Char2 { field_degree: 1, arf }`, with `arf` the parity of odd dyadic valuation
//! lines. The char-2 constant fields of `F_q(t)` are a separate matter (the
//! Aravire–Jacob layer in `springer/char2.rs`).

use crate::forms::local_global::padic::{legendre, relevant_primes, unit_part, val_p};
use crate::forms::WittClassG;
use std::collections::BTreeMap;

/// The second residue `∂_p⟨a_1,…,a_n⟩` at an **odd** prime `p`, as a Witt class over
/// `F_p`. It collects the residue units of the entries of **odd** `p`-valuation and
/// returns the Witt class of `⟂ ⟨ū_i⟩` over `F_p`, using the multiplicativity of the
/// Legendre symbol (so no product overflows): `∏ (u_i | p)` times the
/// `(−1)^{m(m−1)/2}` signed-discriminant correction gives the square class.
fn second_residue_at(entries: &[i128], p: u128) -> WittClassG {
    let pi = p as i128;
    let mut leg_prod: i128 = 1; // ∏ (u_i | p) over odd-valuation entries
    let mut m: i128 = 0; // dimension of the residue form
    for &a in entries {
        if val_p(a, pi) % 2 == 1 {
            leg_prod *= legendre(unit_part(a, pi), pi);
            m += 1;
        }
    }
    let leg_neg1 = legendre(-1, pi); // (−1 | p): +1 iff p ≡ 1 (mod 4)
    let signed_leg = if ((m * (m - 1) / 2) & 1) == 1 {
        leg_prod * leg_neg1
    } else {
        leg_prod
    };
    WittClassG::OddChar {
        field_order: p,
        kappa: if leg_neg1 == 1 { 0 } else { 1 },
        e0: (m & 1) as u128,
        sclass: if signed_leg == 1 { 0 } else { 1 },
    }
}

/// Milnor's hand-defined dyadic residue `∂₂ : W(ℚ) → W(F₂) ≅ ℤ/2`.
/// Since every odd unit reduces to `1 ∈ F₂`, only the parity of entries with odd
/// `2`-adic valuation survives.
fn dyadic_residue_at(entries: &[i128]) -> WittClassG {
    let arf = entries.iter().filter(|&&a| val_p(a, 2) % 2 == 1).count() as u128 & 1;
    WittClassG::Char2 {
        field_degree: 1,
        arf,
    }
}

/// Whether a Witt class over `F_p` is the zero class (even dimension and square signed
/// discriminant ⇒ hyperbolic).
fn is_zero_residue(w: &WittClassG) -> bool {
    matches!(
        w,
        WittClassG::OddChar {
            e0: 0,
            sclass: 0,
            ..
        } | WittClassG::Char2 { arf: 0, .. }
    )
}

/// The image of the rational diagonal form `⟨a_1,…,a_n⟩` (nonzero `i128` entries)
/// under the Milnor map `W(ℚ) → ℤ ⊕ ⊕_p W(F_p)`: the **signature** `(#positive −
/// #negative)` and the nonzero residues `∂_p`, keyed by prime. Zero residues are
/// omitted, so the map of an everywhere-good integral form is empty.
///
/// `None` if any entry is zero (a radical — the form is degenerate). Two forms with
/// equal `global_residues` are Witt-equivalent over `ℚ`; a difference at any prime,
/// or in the signature, witnesses inequivalence.
pub fn global_residues(entries: &[i128]) -> Option<(i128, BTreeMap<u128, WittClassG>)> {
    if entries.contains(&0) {
        return None;
    }
    let signature: i128 = entries.iter().map(|&a| a.signum()).sum();
    let mut residues = BTreeMap::new();
    for p in relevant_primes(entries) {
        let w = if p == 2 {
            dyadic_residue_at(entries)
        } else {
            second_residue_at(entries, p)
        };
        if !is_zero_residue(&w) {
            residues.insert(p, w);
        }
    }
    Some((signature, residues))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clifford::Metric;
    use crate::forms::{springer_decompose_qp, try_is_isotropic_q};
    use crate::scalar::Qp;

    /// `∂₅` via the capped `Q₅` Springer engine: the Witt class of the odd-valuation
    /// (parity-1) residue layer, built independently of the `i128` route.
    fn springer_residue_q5(entries: &[i128]) -> WittClassG {
        type Q5 = Qp<5, 6>;
        let metric = Metric::diagonal(entries.iter().map(|&a| Q5::from_i128(a)).collect());
        let decomp = springer_decompose_qp(&metric).unwrap();
        let mut dim = 0usize;
        let mut disc_sq = true; // running square class of the residue discriminant
        for form in decomp.parity_layer(1) {
            dim += form.dim;
            disc_sq = disc_sq == form.disc_is_square; // XNOR of square classes
        }
        let m = dim as i128;
        let leg_neg1 = legendre(-1, 5); // +1 (5 ≡ 1 mod 4)
        let signed_sq = if ((m * (m - 1) / 2) & 1) == 1 && leg_neg1 != 1 {
            !disc_sq
        } else {
            disc_sq
        };
        WittClassG::OddChar {
            field_order: 5,
            kappa: if leg_neg1 == 1 { 0 } else { 1 },
            e0: (dim & 1) as u128,
            sclass: if signed_sq { 0 } else { 1 },
        }
    }

    fn f2_class(arf: u128) -> WittClassG {
        WittClassG::Char2 {
            field_degree: 1,
            arf,
        }
    }

    #[test]
    fn second_residue_matches_springer_over_q5() {
        // The exact i128 residue and the capped-Q₅ Springer residue agree on forms
        // exercising even/odd valuations and square/nonsquare units at 5.
        for entries in [
            vec![1, 5],
            vec![2, 10],
            vec![3, 15, 5],
            vec![1, 1],
            vec![7, 5, 25, 2],
        ] {
            assert_eq!(
                second_residue_at(&entries, 5),
                springer_residue_q5(&entries),
                "∂₅ mismatch on {entries:?}"
            );
        }
    }

    #[test]
    fn dyadic_residue_is_milnors_hand_boundary() {
        // Over F_2 every odd unit reduces to 1, so ∂_2 only sees the parity of
        // odd 2-adic valuation lines.
        assert_eq!(dyadic_residue_at(&[1]), f2_class(0));
        assert_eq!(dyadic_residue_at(&[2]), f2_class(1));
        assert_eq!(dyadic_residue_at(&[-2]), f2_class(1));
        assert_eq!(dyadic_residue_at(&[1, 2]), f2_class(1));
        assert_eq!(dyadic_residue_at(&[2, -2]), f2_class(0));
    }

    #[test]
    fn global_residues_include_the_dyadic_cell() {
        for (entries, signature) in [(&[2i128][..], 1), (&[1, 2], 2), (&[-2], -1)] {
            let (sig, res) = global_residues(entries).unwrap();
            assert_eq!(sig, signature);
            assert_eq!(res.get(&2), Some(&f2_class(1)), "entries={entries:?}");
        }

        let (sig, res) = global_residues(&[2, -2]).unwrap();
        assert_eq!(sig, 0);
        assert!(
            res.is_empty(),
            "the hyperbolic pair <2,-2> has zero residues"
        );

        let (_, mixed) = global_residues(&[6]).unwrap();
        assert_eq!(
            mixed.keys().copied().collect::<Vec<_>>(),
            vec![2, 3],
            "<6> has both dyadic and odd-prime residues"
        );
    }

    #[test]
    fn residues_have_finite_support_at_dividing_primes() {
        // ∂_p = 0 for p ∤ ∏ a_i: ⟨1,1,1⟩ has no odd residues.
        let (sig, res) = global_residues(&[1, 1, 1]).unwrap();
        assert_eq!(sig, 3);
        assert!(res.is_empty());
        // ⟨3, 5⟩: residues exactly at 3 and 5 (each an odd-valuation unit line).
        let (sig, res) = global_residues(&[3, 5]).unwrap();
        assert_eq!(sig, 2);
        assert_eq!(res.keys().copied().collect::<Vec<_>>(), vec![3, 5]);
    }

    #[test]
    fn radical_entry_is_rejected() {
        assert_eq!(global_residues(&[1, 0, 2]), None);
    }

    #[test]
    fn witt_invariants_are_square_and_hyperbolic_stable() {
        // ⟨3⟩ ≅ ⟨12⟩ (12 = 3·4, a square multiple) and adding a hyperbolic plane
        // ⟨1,−1⟩ changes nothing — all three share signature and residues.
        let base = global_residues(&[3]).unwrap();
        assert_eq!(global_residues(&[12]).unwrap(), base);
        assert_eq!(global_residues(&[3, 1, -1]).unwrap(), base);
        // Same at the dyadic prime: ⟨2⟩ ≅ ⟨8⟩, and ⟨1,-1⟩ is still hyperbolic.
        let dyadic = global_residues(&[2]).unwrap();
        assert_eq!(global_residues(&[8]).unwrap(), dyadic);
        assert_eq!(global_residues(&[2, 1, -1]).unwrap(), dyadic);
    }

    #[test]
    fn residues_distinguish_inequivalent_forms() {
        // ⟨1⟩ and ⟨3⟩ have equal signature but differ at p = 3 ⇒ not Witt-equivalent.
        let one = global_residues(&[1]).unwrap();
        let three = global_residues(&[3]).unwrap();
        assert_eq!(one.0, three.0, "same signature");
        assert_ne!(one.1, three.1, "different residue at 3");
        // Cross-check with Hasse–Minkowski: ⟨1,−3⟩ is anisotropic over ℚ (3 is not a
        // square), so ⟨1⟩ ⊥ ⟨−3⟩ is not hyperbolic — they are genuinely inequivalent.
        assert_eq!(try_is_isotropic_q(&[1, -3]), Some(false));

        // Same signature, dyadic residue differs: ⟨1⟩ and ⟨2⟩ are not equivalent.
        let two = global_residues(&[2]).unwrap();
        assert_eq!(one.0, two.0, "same signature");
        assert_ne!(one.1, two.1, "different dyadic residue");
        assert_eq!(try_is_isotropic_q(&[1, -2]), Some(false));
    }

    #[test]
    fn reconstruction_agrees_with_hasse_minkowski() {
        // Equal residues + equal signature ⇒ Witt-equivalent ⇒ a ⊥ (−b) hyperbolic,
        // hence isotropic. ⟨3⟩ vs ⟨12⟩: ⟨3,−12⟩ is isotropic (x = 2y).
        assert_eq!(
            global_residues(&[3]).unwrap(),
            global_residues(&[12]).unwrap()
        );
        assert_eq!(try_is_isotropic_q(&[3, -12]), Some(true));

        // ⟨3,5⟩ vs ⟨12,45⟩ (entrywise square multiples): same residues at 3 and 5,
        // and ⟨3,5,−12,−45⟩ is isotropic ((x,z) = (2,1): 3·4 − 12 = 0).
        assert_eq!(
            global_residues(&[3, 5]).unwrap(),
            global_residues(&[12, 45]).unwrap()
        );
        assert_eq!(try_is_isotropic_q(&[3, 5, -12, -45]), Some(true));

        // Dyadic reconstruction: ⟨2⟩ vs ⟨8⟩ differ by a square multiple, so the
        // difference form is isotropic; ⟨2⟩ vs ⟨1⟩ has a dyadic-residue mismatch.
        assert_eq!(
            global_residues(&[2]).unwrap(),
            global_residues(&[8]).unwrap()
        );
        assert_eq!(try_is_isotropic_q(&[2, -8]), Some(true));
        assert_ne!(
            global_residues(&[2]).unwrap(),
            global_residues(&[1]).unwrap()
        );
        assert_eq!(try_is_isotropic_q(&[2, -1]), Some(false));
    }
}
