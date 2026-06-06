//! Transfinite (ordinal) nimbers — the char-2 mirror of the surreal backend,
//! and the closure the shipped `Nimber(u64)` backend cannot reach.
//!
//! The finite nimbers form `⋃ₙ F_{2^{2^n}}` — the quadratic closure of `F₂` — but
//! this is **not** algebraically closed: it contains `F_{2^d}` only for `d` a
//! power of two, so it misses `F₈` (degree 3), `F₃₂` (degree 5), …. Conway's
//! theorem (ONAG ch. 6) is that the proper class of *all ordinals* under
//! nim-addition and nim-multiplication is an algebraically closed field of
//! characteristic 2, and the algebraic closure of `F₂` already appears among the
//! ordinals below `ω^{ω^ω}`. The first infinite ordinal `ω` supplies the missing
//! cube roots: **`ω³ = 2`** (ω is the nim-cube-root of the nimber 2), which has
//! no solution in any finite layer, so `F₂(ω)` jumps past the 2-power tower and
//! brings in `F₈`.
//!
//! An `Ordinal` is stored in Cantor normal form `Σ ω^{βᵢ}·cᵢ` (`βᵢ` descending
//! ordinals, `cᵢ` finite), mirroring `surreal.rs` — and like there, every
//! operation recurses only on the strictly-simpler *exponents*, which is the
//! termination argument.
//!
//! ## Status (honest scope)
//!
//! * **nim-addition is complete and exact**: like-`ω`-power coefficients combine
//!   by XOR (so `α ⊕ α = 0`, `ω ⊕ 1 = ω+1`), giving the genuine transfinite
//!   characteristic-2 additive group.
//! * **nim-multiplication is partial**: finite × finite delegates to the proven
//!   `nimber::nim_mul`; any infinite operand returns `None`. The general ordinal
//!   nim-product (Conway ONAG ch. 6 / Lenstra, *Nim multiplication*, 1978) is
//!   intricate and **staged**, not implemented here. The landmark it must
//!   reproduce — `ω ⊗ ω ⊗ ω = 2` — is recorded as the target; we do not hardcode
//!   `ω ⊗ ω`, whose value is not asserted without the reference worked through.

use crate::nimber::nim_mul;
use std::cmp::Ordering;
use std::fmt;

/// An ordinal `< ε₀`-ish in Cantor normal form: `Σ ω^{exp}·coeff`, exponents
/// strictly descending, coefficients nonzero finite naturals.
#[derive(Clone, PartialEq, Eq)]
pub struct Ordinal {
    terms: Vec<(Ordinal, u64)>,
}

fn canonicalize(mut raw: Vec<(Ordinal, u64)>) -> Vec<(Ordinal, u64)> {
    raw.sort_by(|a, b| b.0.cmp(&a.0)); // descending by exponent
    let mut out: Vec<(Ordinal, u64)> = Vec::new();
    for (exp, coeff) in raw {
        if let Some(last) = out.last_mut() {
            if last.0 == exp {
                last.1 ^= coeff; // nim-addition of coefficients = XOR
                continue;
            }
        }
        out.push((exp, coeff));
    }
    out.retain(|(_, c)| *c != 0);
    out
}

impl Ordinal {
    /// The ordinal `0`.
    pub fn zero() -> Self {
        Ordinal { terms: Vec::new() }
    }

    /// A finite ordinal / nimber `n`.
    pub fn from_u64(n: u64) -> Self {
        if n == 0 {
            Ordinal::zero()
        } else {
            Ordinal {
                terms: vec![(Ordinal::zero(), n)],
            }
        }
    }

    /// A single monomial `ω^exp · coeff`.
    pub fn monomial(exp: Ordinal, coeff: u64) -> Self {
        if coeff == 0 {
            Ordinal::zero()
        } else {
            Ordinal {
                terms: vec![(exp, coeff)],
            }
        }
    }

    /// `ω^exp` (coefficient 1).
    pub fn omega_pow(exp: Ordinal) -> Self {
        Ordinal::monomial(exp, 1)
    }

    /// `ω`, the first infinite ordinal.
    pub fn omega() -> Self {
        Ordinal::omega_pow(Ordinal::from_u64(1))
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn terms(&self) -> &[(Ordinal, u64)] {
        &self.terms
    }

    /// The ordinal order (lexicographic on descending CNF terms).
    pub fn cmp(&self, other: &Ordinal) -> Ordering {
        for ((e1, c1), (e2, c2)) in self.terms.iter().zip(other.terms.iter()) {
            match e1.cmp(e2) {
                Ordering::Equal => {}
                ord => return ord,
            }
            match c1.cmp(c2) {
                Ordering::Equal => {}
                ord => return ord,
            }
        }
        // shared prefix equal: the longer CNF is the larger ordinal
        self.terms.len().cmp(&other.terms.len())
    }

    /// Nim-addition: XOR the coefficients of like `ω`-powers. Complete and exact.
    pub fn nim_add(&self, other: &Ordinal) -> Ordinal {
        let mut raw = self.terms.clone();
        raw.extend(other.terms.iter().cloned());
        Ordinal {
            terms: canonicalize(raw),
        }
    }

    /// True iff this ordinal is finite (a single `ω^0` term, or zero), returning
    /// the finite nimber value.
    pub fn as_finite(&self) -> Option<u64> {
        match self.terms.as_slice() {
            [] => Some(0),
            [(exp, c)] if exp.is_zero() => Some(*c),
            _ => None,
        }
    }

    /// Nim-multiplication. **Partial**: exact for finite × finite (via the proven
    /// `nim_mul`); `None` when either operand is infinite (the general ordinal
    /// nim-product is staged — see the module docs). nim-multiplication is the
    /// research-hard half; this is the honest boundary.
    pub fn nim_mul(&self, other: &Ordinal) -> Option<Ordinal> {
        match (self.as_finite(), other.as_finite()) {
            (Some(a), Some(b)) => Some(Ordinal::from_u64(nim_mul(a, b))),
            _ => None,
        }
    }
}

fn fmt_exp(e: &Ordinal) -> String {
    if e.is_zero() {
        String::new()
    } else if *e == Ordinal::from_u64(1) {
        "ω".to_string()
    } else if e.terms.len() == 1 && e.terms[0].0.is_zero() {
        format!("ω^{}", e.terms[0].1) // ω^k for a finite exponent k
    } else {
        format!("ω^({:?})", e)
    }
}

impl fmt::Debug for Ordinal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.terms.is_empty() {
            return write!(f, "0");
        }
        let parts: Vec<String> = self
            .terms
            .iter()
            .map(|(e, c)| {
                let base = fmt_exp(e);
                if base.is_empty() {
                    format!("{}", c) // finite term
                } else if *c == 1 {
                    base
                } else {
                    format!("{}·{}", base, c)
                }
            })
            .collect();
        write!(f, "{}", parts.join(" + "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fin(n: u64) -> Ordinal {
        Ordinal::from_u64(n)
    }

    #[test]
    fn cantor_normal_form_ordering() {
        let one = fin(1);
        let omega = Ordinal::omega(); // ω
        let omega_times_2 = Ordinal::monomial(one.clone(), 2); // ω·2
        let omega_sq = Ordinal::omega_pow(fin(2)); // ω²
        let omega_omega = Ordinal::omega_pow(Ordinal::omega()); // ω^ω
        assert_eq!(one.cmp(&omega), Ordering::Less);
        assert_eq!(omega.cmp(&omega_times_2), Ordering::Less);
        assert_eq!(omega_times_2.cmp(&omega_sq), Ordering::Less);
        assert_eq!(omega_sq.cmp(&omega_omega), Ordering::Less);
        // ω^ω dominates every ω^n
        assert_eq!(
            omega_omega.cmp(&Ordinal::omega_pow(fin(100))),
            Ordering::Greater
        );
    }

    #[test]
    fn nim_add_is_xor_below_omega() {
        for a in 0..16u64 {
            for b in 0..16u64 {
                assert_eq!(fin(a).nim_add(&fin(b)), fin(a ^ b));
            }
        }
    }

    #[test]
    fn self_inverse_and_cancellation() {
        let omega = Ordinal::omega();
        // ω ⊕ ω = 0
        assert!(omega.nim_add(&omega).is_zero());
        // (ω·3) ⊕ (ω·3) = 0
        let w3 = Ordinal::monomial(fin(1), 3);
        assert!(w3.nim_add(&w3).is_zero());
        // (ω + 1) ⊕ 1 = ω
        let w_plus_1 = omega.nim_add(&fin(1));
        assert_eq!(w_plus_1.nim_add(&fin(1)), omega);
        // ω·2 ⊕ ω = ω·3  (coefficients XOR: 2 ⊕ 1 = 3)
        let w2 = Ordinal::monomial(fin(1), 2);
        assert_eq!(w2.nim_add(&omega), Ordinal::monomial(fin(1), 3));
    }

    #[test]
    fn additive_group_axioms_with_infinite_terms() {
        let a = Ordinal::omega().nim_add(&fin(2)); // ω + 2
        let b = Ordinal::omega_pow(fin(2)).nim_add(&fin(1)); // ω² + 1
        let c = Ordinal::monomial(fin(1), 5); // ω·5
                                              // associativity + commutativity
        assert_eq!(a.nim_add(&b).nim_add(&c), a.nim_add(&b.nim_add(&c)));
        assert_eq!(a.nim_add(&b), b.nim_add(&a));
        // identity + self-inverse
        assert_eq!(a.nim_add(&Ordinal::zero()), a);
        assert!(a.nim_add(&a).is_zero());
    }

    #[test]
    fn finite_nim_mul_agrees_with_nimber() {
        for a in 0..16u64 {
            for b in 0..16u64 {
                assert_eq!(fin(a).nim_mul(&fin(b)), Some(fin(nim_mul(a, b))));
            }
        }
    }

    #[test]
    fn infinite_nim_mul_is_staged() {
        // The research-hard half: ω ⊗ ω is not implemented (would need the full
        // Conway/Lenstra ordinal product). The landmark target is ω³ = 2.
        let omega = Ordinal::omega();
        assert_eq!(omega.nim_mul(&omega), None);
        assert_eq!(omega.nim_mul(&fin(3)), None);
        // finite operands still multiply
        assert_eq!(fin(2).nim_mul(&fin(2)), Some(fin(3))); // 2 ⊗ 2 = 3
    }

    #[test]
    fn display_reads_as_cnf() {
        assert_eq!(format!("{:?}", Ordinal::omega()), "ω");
        assert_eq!(format!("{:?}", Ordinal::monomial(fin(1), 3)), "ω·3");
        assert_eq!(format!("{:?}", Ordinal::omega_pow(fin(2))), "ω^2");
        assert_eq!(format!("{:?}", Ordinal::omega().nim_add(&fin(1))), "ω + 1");
        assert_eq!(format!("{:?}", fin(5)), "5");
    }
}
