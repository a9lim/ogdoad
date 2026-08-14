//! Fit an `F_2` quadratic form to a finite point set.
//!
//! This is not a classifier (that is [`char2`](crate::forms::char2)'s Arf): it is
//! a bounded diagnostic for Boolean data. Given a subset `S ⊆ F₂^k`,
//! [`fit_f2_quadratic`] decides whether `S` is the zero set of a quadratic form
//! and, if so, returns the form and its
//! [Arf data](crate::forms::ArfInvariants). The polar rank distinguishes a genuine
//! quadratic term from an affine-linear zero set.

use crate::forms::{arf_f2, ArfInvariants};

/// The result of fitting a quadratic form to a subset of F₂^k.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuadricFit {
    /// Constant term: false ⇒ `0 ∈ set` (form through the origin); true ⇒ affine
    /// offset (`set = {Q = 1}` for the homogeneous part below).
    pub constant: bool,
    /// Diagonal q_i (the linear/`x_i` coefficients = squares over F₂).
    pub qd: Vec<bool>,
    /// Polar form bmat (the `x_i x_j` coefficients), as adjacency rows.
    pub bmat: Vec<u128>,
    /// Arf classification of the homogeneous quadratic part.
    pub arf: ArfInvariants,
}

impl QuadricFit {
    /// Whether the fitted form has genuine quadratic content (nonzero polar form
    /// rank). `false` ⇒ the set is an affine flat / linear condition, no quadratic
    /// refinement.
    pub fn is_genuinely_quadratic(&self) -> bool {
        self.arf.rank > 0
    }

    /// The win-bias bit of the **fitted set itself** — `arf.arf` XOR `constant`.
    ///
    /// [`arf`](Self::arf)`.arf` is the Arf invariant of the *homogeneous* quadratic
    /// part `Q₀` alone; it is not by itself the bias of `set`, because the fit may
    /// carry a nonzero [`constant`](Self::constant) (`set = {Q₀ = 1}` rather than
    /// `{Q₀ = 0}`), and the zero-count bias flips with that offset (e.g. `Q₀ = x₀x₁`
    /// has zero set `{00,01,10}`, 3 points, while `1 + Q₀` has zero set `{11}`, 1
    /// point — same homogeneous Arf, opposite bias). `bias()` is the corrected bit:
    /// on a **nonsingular** fit ([`arf`](Self::arf)`.radical_dim == 0`, which forces
    /// the ambient dimension `k` even),
    ///
    /// ```text
    /// |set| = 2^(k-1) + (-1)^bias * 2^(k/2 - 1)
    /// ```
    ///
    /// so `bias() == 0` means `set` is larger than the half-size baseline
    /// `2^(k-1)`, `bias() == 1` means smaller. Degenerate fits
    /// (`radical_dim != 0`) have no such closed-form count; `bias()` still
    /// computes the XOR, but callers relying on the count formula must check
    /// [`is_genuinely_quadratic`](Self::is_genuinely_quadratic) / `radical_dim`
    /// first.
    pub fn bias(&self) -> u128 {
        self.arf.arf ^ (self.constant as u128)
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for QuadricFit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "QuadricFit(quadratic={}, constant={}, rank={}, arf={}, radical_dim={}, bias={})",
            self.is_genuinely_quadratic(),
            self.constant,
            self.arf.rank,
            self.arf.arf,
            self.arf.radical_dim,
            if self.arf.radical_dim == 0 {
                self.bias().to_string()
            } else {
                "n/a (degenerate)".to_string()
            },
        )
    }
}

/// Try to fit a quadratic form `Q(x) = c ⊕ Σ q_i x_i ⊕ Σ_{i<j} b_ij x_i x_j` over
/// F₂ on `k` variables whose zero set is exactly `set` (a list of bitmask points
/// of F₂^k). Returns `None` if no quadratic form has that zero set, or if `set`
/// contains a point outside `F₂^k` (i.e. with a bit set at position `>= k`). The
/// unique Boolean algebraic normal form is computed by a fast Mobius transform on
/// the truth table; fitting succeeds exactly when every coefficient of degree `> 2`
/// vanishes.
///
/// This is the instrument both game probes feed their P-positions into: it answers
/// "is this P-set a quadric, and if so what is its Arf (win-bias)?", and
/// distinguishes a genuine quadric ([`QuadricFit::is_genuinely_quadratic`]) from a
/// mere affine subspace (the XOR-linear case normal play already produces).
pub fn fit_f2_quadratic(set: &[u128], k: usize) -> Option<QuadricFit> {
    const MAX_ANF_DIM: usize = 20;
    assert!(
        k <= MAX_ANF_DIM,
        "fit_f2_quadratic is exponential in k; max supported k is {MAX_ANF_DIM}"
    );
    let n = 1usize << k;
    let domain_mask = if k == 0 { 0 } else { (1u128 << k) - 1 };
    if set.iter().any(|&v| v & !domain_mask != 0) {
        return None;
    }

    // Truth table for the target function Q(v): zero on `set`, one off it.
    let mut coeffs = vec![true; n];
    for &v in set {
        coeffs[v as usize] = false;
    }

    // Mobius transform: truth table -> algebraic normal form coefficients.
    for i in 0..k {
        let bit = 1usize << i;
        for mask in 0..n {
            if mask & bit != 0 {
                coeffs[mask] ^= coeffs[mask ^ bit];
            }
        }
    }

    if coeffs
        .iter()
        .enumerate()
        .any(|(mask, &c)| c && mask.count_ones() > 2)
    {
        return None;
    }

    let constant = coeffs[0];
    let qd: Vec<bool> = (0..k).map(|i| coeffs[1usize << i]).collect();
    let mut bmat = vec![0u128; k];
    for i in 0..k {
        for j in (i + 1)..k {
            if coeffs[(1usize << i) | (1usize << j)] {
                bmat[i] |= 1 << j;
                bmat[j] |= 1 << i;
            }
        }
    }
    let arf = arf_f2(k, &qd, &bmat);
    Some(QuadricFit {
        constant,
        qd,
        bmat,
        arf,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    // Evaluate a fitted form Q at v and return Q(v) ∈ {false,true}.
    fn eval_fit(fit: &QuadricFit, v: u128) -> bool {
        let mut acc = fit.constant;
        for i in 0..fit.qd.len() {
            if fit.qd[i] && v & (1 << i) != 0 {
                acc ^= true;
            }
        }
        for i in 0..fit.qd.len() {
            for j in (i + 1)..fit.qd.len() {
                if fit.bmat[i] & (1 << j) != 0 && v & (1 << i) != 0 && v & (1 << j) != 0 {
                    acc ^= true;
                }
            }
        }
        acc
    }

    #[test]
    fn fit_recovers_known_quadrics() {
        // hyperbolic Q = x0 x1: zero set {00,01,10}; genuine quadric, Arf 0.
        let h = fit_f2_quadratic(&[0, 1, 2], 2).unwrap();
        assert!(h.is_genuinely_quadratic());
        assert_eq!(h.arf.arf, 0);
        assert!(!h.constant);
        // anisotropic Q = x0²+x0x1+x1²: zero set {00}; Arf 1.
        let a = fit_f2_quadratic(&[0], 2).unwrap();
        assert!(a.is_genuinely_quadratic());
        assert_eq!(a.arf.arf, 1);
        // a LINEAR condition x0⊕x1=0: zero set {00,11}; a quadric but rank 0
        // (affine flat), i.e. NOT genuinely quadratic.
        let lin = fit_f2_quadratic(&[0, 3], 2).unwrap();
        assert!(!lin.is_genuinely_quadratic());
        assert_eq!(lin.arf.rank, 0);
    }

    #[test]
    fn display_shows_bias_only_for_nonsingular_fits() {
        // hyperbolic Q = x0 x1: nonsingular (radical_dim 0) ⇒ bias is honest.
        let h = fit_f2_quadratic(&[0, 1, 2], 2).unwrap();
        assert_eq!(h.arf.radical_dim, 0);
        assert_eq!(
            h.to_string(),
            "QuadricFit(quadratic=true, constant=false, rank=2, arf=0, radical_dim=0, bias=0)"
        );
        assert_eq!(h.display(), h.to_string());

        // anisotropic Q = x0²+x0x1+x1²: also nonsingular, Arf 1.
        let a = fit_f2_quadratic(&[0], 2).unwrap();
        assert_eq!(a.arf.radical_dim, 0);
        assert_eq!(
            a.to_string(),
            "QuadricFit(quadratic=true, constant=false, rank=2, arf=1, radical_dim=0, bias=1)"
        );

        // the LINEAR condition x0⊕x1=0 is a degenerate fit (rank 0, full radical):
        // the closed-form bias count doesn't apply, so the render must say so
        // rather than print a bare (misleading) bit.
        let lin = fit_f2_quadratic(&[0, 3], 2).unwrap();
        assert_eq!(lin.arf.radical_dim, 2);
        assert_eq!(
            lin.to_string(),
            "QuadricFit(quadratic=false, constant=false, rank=0, arf=0, radical_dim=2, bias=n/a (degenerate))"
        );
    }

    #[test]
    fn fit_supports_high_dimensional_quadratic_coefficient_layout() {
        let set: Vec<u128> = (0..(1u128 << 16)).collect();
        let fit = fit_f2_quadratic(&set, 16).unwrap();
        assert_eq!(fit.qd.len(), 16);
        assert_eq!(fit.arf.rank, 0);
        assert!(!fit.constant);
    }

    #[test]
    fn quadric_count_and_roundtrip_over_f2_cubed() {
        // Over F₂³ there are 2^(1+3+3) = 128 quadratic forms but 2^8 = 256 subsets,
        // so exactly 128 subsets are quadrics — and each fit must reproduce its set.
        let mut count = 0;
        for s in 0u128..(1 << 8) {
            let set: Vec<u128> = (0..8u128).filter(|&v| s & (1 << v) != 0).collect();
            if let Some(fit) = fit_f2_quadratic(&set, 3) {
                count += 1;
                let recovered: Vec<u128> = (0..8u128).filter(|&v| !eval_fit(&fit, v)).collect();
                assert_eq!(recovered, set, "fit did not reproduce its own set");
            }
        }
        assert_eq!(count, 128, "expected exactly 2^7 quadrics over F₂³");
    }

    #[test]
    fn cubic_truth_table_is_rejected() {
        // Q(v) = x0 x1 x2 has zero set all points except 111; it is not quadratic.
        let set: Vec<u128> = (0..8u128).filter(|&v| v != 7).collect();
        assert!(fit_f2_quadratic(&set, 3).is_none());
    }

    #[test]
    fn point_outside_domain_returns_none_not_panic() {
        // k=2 ⇒ domain is {00,01,10,11}; bit 2 set is out of F_2^2.
        assert_eq!(fit_f2_quadratic(&[0, 1, 4], 2), None);
    }

    #[test]
    fn bias_matches_brute_force_zero_count_on_nonsingular_forms_up_to_k4() {
        // For every nonsingular F₂ quadratic form Q on F₂^k (k ≤ 4 — odd k never
        // has a nonsingular alternating polar form, so those iterations just find
        // nothing to check), fit both Q's own zero set (constant=false) and its
        // complement (constant=true, same homogeneous Q) and check bias() = arf ⊕
        // constant against a brute-forced zero count via the closed form pinned in
        // `QuadricFit::bias`'s doc: |set| = 2^(k-1) + (-1)^bias * 2^(k/2-1).
        for k in 1usize..=4 {
            let pair_count = k * (k - 1) / 2;
            for qd_bits in 0u128..(1 << k) {
                let qd: Vec<bool> = (0..k).map(|i| qd_bits & (1 << i) != 0).collect();
                for bmat_bits in 0u128..(1u128 << pair_count) {
                    let mut bmat = vec![0u128; k];
                    let mut idx = 0;
                    for i in 0..k {
                        for j in (i + 1)..k {
                            if bmat_bits & (1 << idx) != 0 {
                                bmat[i] |= 1 << j;
                                bmat[j] |= 1 << i;
                            }
                            idx += 1;
                        }
                    }
                    let arf = arf_f2(k, &qd, &bmat);
                    if arf.radical_dim != 0 {
                        continue; // the count formula only holds when nonsingular
                    }

                    let probe = QuadricFit {
                        constant: false,
                        qd: qd.clone(),
                        bmat: bmat.clone(),
                        arf: arf.clone(),
                    };
                    let expected = |bias: u128| -> i128 {
                        let base = 1i128 << (k - 1);
                        let swing = 1i128 << (k / 2 - 1);
                        if bias == 0 {
                            base + swing
                        } else {
                            base - swing
                        }
                    };

                    let zero_set: Vec<u128> = (0..(1u128 << k))
                        .filter(|&v| !eval_fit(&probe, v))
                        .collect();
                    let fit0 = fit_f2_quadratic(&zero_set, k).unwrap();
                    assert!(!fit0.constant);
                    assert_eq!(zero_set.len() as i128, expected(fit0.bias()));

                    let complement: Vec<u128> = (0..(1u128 << k))
                        .filter(|v| !zero_set.contains(v))
                        .collect();
                    let fit1 = fit_f2_quadratic(&complement, k).unwrap();
                    assert!(fit1.constant);
                    assert_eq!(complement.len() as i128, expected(fit1.bias()));
                }
            }
        }
    }
}
