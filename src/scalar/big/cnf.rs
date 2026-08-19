//! Descending-term canonicalization shared by the transfinite backends.
//!
//! `surreal` (`No`) and `ordinal` (`On₂`) both store a number as a descending
//! Conway-normal-form / Hahn series — `Vec<(exponent, coeff)>` with *recursive*
//! exponents, kept strictly descending with like powers merged and zero
//! coefficients dropped. That merge is [`merge_descending`], parameterized by the
//! **three** primitives where the two worlds actually differ:
//!
//!   1. **how exponents are ordered** — `No`'s *value* order (`a < b ⇔ b−a > 0`;
//!      `ω−1 < ω` even though it is structurally *longer*) vs
//!      the ordinal *lexicographic* order (coefficients are positive naturals, so
//!      structure and value agree);
//!   2. **how like coefficients combine** — ordinary `ℚ` addition vs nim `XOR`;
//!   3. **which coefficients are zero**.
//!
//! This is deliberately not a shared `Cnf<C>` type: the exponent ordering
//! is field-dependent for `No` and lexicographic for `On₂`, and everything built
//! on top of it diverges accordingly. The ordinal-nimber backend has
//! characteristic-two negation, while the surreal backend has ordinary additive
//! inverses.

use std::cmp::Ordering;

/// Sort a raw `(exponent, coeff)` list into canonical descending CNF: order by
/// exponent (descending) via `exp_cmp`, merge adjacent like exponents with
/// `coeff_merge`, and drop terms whose coefficient `coeff_is_zero`.
///
/// `exp_cmp` must be a total order consistent with equality of exponents
/// (`exp_cmp(a, b) == Equal` ⟺ `a` and `b` are the same exponent), so the
/// post-sort adjacency check correctly groups like powers.
pub(crate) fn merge_descending<E, C>(
    mut raw: Vec<(E, C)>,
    exp_cmp: impl Fn(&E, &E) -> Ordering,
    coeff_merge: impl Fn(&C, &C) -> C,
    coeff_is_zero: impl Fn(&C) -> bool,
) -> Vec<(E, C)> {
    raw.sort_by(|a, b| exp_cmp(&b.0, &a.0)); // descending by exponent
    let mut out: Vec<(E, C)> = Vec::new();
    for (exp, coeff) in raw {
        if let Some(last) = out.last_mut() {
            if exp_cmp(&last.0, &exp) == Ordering::Equal {
                last.1 = coeff_merge(&last.1, &coeff);
                continue;
            }
        }
        out.push((exp, coeff));
    }
    out.retain(|(_, c)| !coeff_is_zero(c));
    out
}

/// Merge two already-canonical descending term slices in linear time.
pub(crate) fn merge_canonical<E: Clone, C: Clone>(
    left: &[(E, C)],
    right: &[(E, C)],
    exp_cmp: impl Fn(&E, &E) -> Ordering,
    coeff_merge: impl Fn(&C, &C) -> C,
    coeff_is_zero: impl Fn(&C) -> bool,
) -> Vec<(E, C)> {
    let mut out = Vec::with_capacity(left.len() + right.len());
    let (mut i, mut j) = (0usize, 0usize);
    while i < left.len() && j < right.len() {
        match exp_cmp(&left[i].0, &right[j].0) {
            Ordering::Greater => {
                out.push(left[i].clone());
                i += 1;
            }
            Ordering::Less => {
                out.push(right[j].clone());
                j += 1;
            }
            Ordering::Equal => {
                let coefficient = coeff_merge(&left[i].1, &right[j].1);
                if !coeff_is_zero(&coefficient) {
                    out.push((left[i].0.clone(), coefficient));
                }
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&left[i..]);
    out.extend_from_slice(&right[j..]);
    out
}
