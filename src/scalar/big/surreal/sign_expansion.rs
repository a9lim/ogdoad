//! The **sign expansion** of a surreal — the ±-path from the root `0` to `x` in
//! the surreal tree. Finite for dyadics (the exact tree walk) and, over the
//! representable subclass, transfinite (Gonshor): every ordinal is all-pluses,
//! `ε = ω⁻¹` is `+(−)^ω`. The [`SignExpansion`] type run-length-encodes the
//! (possibly transfinite) sequence, and its length is the birthday.
//!
//! `as_ordinal` also lives here: recognising the surreals that *are* ordinals is
//! exactly recognising the all-plus sign expansions.

use super::simplicity::simplest_in_cut;
use super::Surreal;
use crate::scalar::{Ordinal, Rational, Scalar};
use std::cmp::Ordering;

impl Surreal {
    /// The **sign expansion** of a *dyadic* surreal: the sequence of left/right
    /// turns (`true = +`, `false = −`) on the path from the root `0` to `x` in
    /// the surreal tree. Its length is exactly the
    /// [birthday](Self::dyadic_birthday). `None` for non-dyadics (`1/3`,
    /// `ω`, `ε`, …), whose sign expansions are transfinite and so not finitely
    /// listable here. Inverse of [`from_sign_expansion`](Self::from_sign_expansion).
    ///
    /// Examples: `0 ↦ []`, `1 ↦ [+]`, `2 ↦ [+,+]`, `½ ↦ [+,−]`, `¾ ↦ [+,−,+]`.
    pub fn sign_expansion(&self) -> Option<Vec<bool>> {
        if !self.is_dyadic() {
            return None;
        }
        let x = self.as_rational().unwrap();
        let (mut lo, mut hi): (Option<Rational>, Option<Rational>) = (None, None);
        let mut signs = Vec::new();
        loop {
            let v = simplest_in_cut(&lo, &hi);
            match x.cmp(&v) {
                Ordering::Equal => break,
                Ordering::Greater => {
                    signs.push(true);
                    lo = Some(v);
                }
                Ordering::Less => {
                    signs.push(false);
                    hi = Some(v);
                }
            }
        }
        Some(signs)
    }

    /// The dyadic surreal with the given finite sign expansion (`true = +`), by
    /// walking the surreal tree. The empty sequence is `0`. Inverse of
    /// [`sign_expansion`](Self::sign_expansion).
    pub fn from_sign_expansion(signs: &[bool]) -> Surreal {
        let (mut lo, mut hi): (Option<Rational>, Option<Rational>) = (None, None);
        for &s in signs {
            let v = simplest_in_cut(&lo, &hi);
            if s {
                lo = Some(v);
            } else {
                hi = Some(v);
            }
        }
        Surreal::from_rational(simplest_in_cut(&lo, &hi))
    }

    /// This surreal as a (non-negative) **ordinal**, if it is one: an ordinal is
    /// exactly a surreal whose CNF has all non-negative ordinal exponents and
    /// positive *integer* coefficients (so the surreal value equals the Cantor
    /// normal form). Covers `0`, every natural, `ω`, `ω·n`, `ω^k`, and the
    /// transfinite `ω^ω`, `ω^{ω^ω}`, …. `None` for anything with a negative or
    /// fractional coefficient (`ω−1`, `½ω`) or a non-ordinal exponent (`√ω =
    /// ω^{1/2}`). Recurses only on the strictly-simpler exponents.
    pub fn as_ordinal(&self) -> Option<Ordinal> {
        let mut result = Ordinal::zero();
        for (e, c) in &self.terms {
            if !c.is_integer() || c.sign() != Ordering::Greater {
                return None; // coefficient must be a positive natural
            }
            if e.sign() == Ordering::Less {
                return None; // exponent must be ≥ 0 to be an ordinal power
            }
            let eord = e.as_ordinal()?; // recursion: exponent is strictly simpler
                                        // terms are descending, so ord_add appends in CNF order.
            result = result.ord_add(&Ordinal::monomial(eord, c.numer() as u128));
        }
        Some(result)
    }

    /// The surreal equal to a (non-negative) **ordinal** — the inverse of
    /// [`as_ordinal`](Self::as_ordinal). An ordinal `Σ ω^{βᵢ}·cᵢ` in Cantor normal
    /// form maps to the surreal with the *same* CNF, each exponent converted
    /// recursively (the recursion is on strictly-simpler ordinals, matching the
    /// surreal "recurse only on exponents" discipline). Round-trips:
    /// `from_ordinal(o).as_ordinal() == Some(o)`.
    pub fn from_ordinal(o: &Ordinal) -> Surreal {
        let mut acc = Surreal::zero();
        for (exp, c) in o.terms() {
            let exp_s = Surreal::from_ordinal(exp); // strictly-simpler exponent
            acc = acc.add(&Surreal::monomial(exp_s, Rational::int(*c as i128)));
        }
        acc
    }

    /// Reconstruct a surreal from its (possibly transfinite) **sign expansion** —
    /// the inverse of [`transfinite_sign_expansion`](Self::transfinite_sign_expansion)
    /// on the same representable subclass, and the transfinite analogue of
    /// [`from_sign_expansion`](Self::from_sign_expansion). `None` outside the
    /// subclass. Round-trips:
    /// `from_transfinite_sign_expansion(x.transfinite_sign_expansion()?) == Some(x)`.
    pub fn from_transfinite_sign_expansion(se: &SignExpansion) -> Option<Surreal> {
        let runs = se.runs();
        // empty ↦ 0
        if runs.is_empty() {
            return Some(Surreal::zero());
        }
        // all-finite runs ↦ the exact dyadic tree walk.
        if let Some(signs) = se.as_finite() {
            return Some(Surreal::from_sign_expansion(&signs));
        }
        // a single transfinite run of one sign ↦ ±(the ordinal of that length):
        // α-many pluses is the ordinal α, α-many minuses its negation.
        if runs.len() == 1 {
            let (sign, len) = &runs[0];
            let s = Surreal::from_ordinal(len);
            return Some(if *sign { s } else { s.neg() });
        }
        // ε = ω⁻¹ ↦ `+(−)^ω` (the one pinned infinitesimal).
        if runs.len() == 2 {
            let ((s0, l0), (s1, l1)) = (&runs[0], &runs[1]);
            if *s0 && !*s1 && *l0 == Ordinal::from_u128(1) && *l1 == Ordinal::omega() {
                return Some(Surreal::epsilon());
            }
        }
        None
    }

    /// The **(possibly transfinite) sign expansion** over the *representable
    /// subclass* — the run-length-encoded ±-sequence whose length is the
    /// birthday. Confident Gonshor cases: `0` (empty); dyadics (the exact finite
    /// path); every non-negative ordinal `α` ↦ `α` pluses, and its negative ↦
    /// `α` minuses (covers `ω`, `ω·n`, `ω^ω`, …); and `ε = ω⁻¹ ↦ +(−)^ω`.
    /// Returns `None` outside that subclass — the honest boundary: `√ω`,
    /// `ω−1`, `½ω`, mixed ordinal+infinitesimal — rather than emitting an
    /// unverified interleaving.
    pub fn transfinite_sign_expansion(&self) -> Option<SignExpansion> {
        if self.is_zero() {
            return Some(SignExpansion { runs: Vec::new() });
        }
        // Dyadic / finite: the exact tree walk, run-length encoded.
        if let Some(signs) = self.sign_expansion() {
            return Some(SignExpansion::from_finite(&signs));
        }
        // A non-negative ordinal is α pluses; its negation, α minuses.
        if let Some(alpha) = self.as_ordinal() {
            if !alpha.is_zero() {
                return Some(SignExpansion {
                    runs: vec![(true, alpha)],
                });
            }
        }
        if let Some(alpha) = self.neg().as_ordinal() {
            if !alpha.is_zero() {
                return Some(SignExpansion {
                    runs: vec![(false, alpha)],
                });
            }
        }
        // ε = ω⁻¹ : one plus, then ω minuses (Gonshor). The one confident
        // infinitesimal; ω^{-k} for k ≥ 2 and rational multiples are out of scope.
        if *self == Surreal::epsilon() {
            return Some(SignExpansion {
                runs: vec![(true, Ordinal::from_u128(1)), (false, Ordinal::omega())],
            });
        }
        None
    }

    /// The **birthday** as an [`Ordinal`]. Dyadics use the fast finite path;
    /// otherwise the birthday is the ordinal *length* of the
    /// [transfinite sign expansion](Self::transfinite_sign_expansion) — so
    /// `ω ↦ ω`, `ω+1 ↦ ω+1`, `ε ↦ ω`, `ω^ω ↦ ω^ω`. `None` outside the
    /// representable subclass (`√ω`, …).
    pub fn birthday_ordinal(&self) -> Option<Ordinal> {
        if let Some(b) = self.dyadic_birthday() {
            return Some(Ordinal::from_u128(b));
        }
        Some(self.transfinite_sign_expansion()?.length())
    }
}

/// A (possibly transfinite) sign expansion as **runs**: `(sign, length)` pairs,
/// `true = +`, lengths ordinals. A finite expansion is just runs with finite
/// lengths; `ω`-many pluses is a single run `(true, ω)`. The total length (the
/// ordinary ordinal sum of the run lengths) is the surreal's birthday.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignExpansion {
    runs: Vec<(bool, Ordinal)>,
}

impl SignExpansion {
    /// Build a sign expansion from run data, normalizing away zero-length runs and
    /// merging adjacent runs with the same sign.
    pub fn from_runs(runs: Vec<(bool, Ordinal)>) -> Self {
        let mut normalized: Vec<(bool, Ordinal)> = Vec::new();
        for (sign, len) in runs {
            if len.is_zero() {
                continue;
            }
            if let Some(last) = normalized.last_mut() {
                if last.0 == sign {
                    last.1 = last.1.ord_add(&len);
                    continue;
                }
            }
            normalized.push((sign, len));
        }
        SignExpansion { runs: normalized }
    }

    /// The runs `(sign, length)`, left to right.
    pub fn runs(&self) -> &[(bool, Ordinal)] {
        &self.runs
    }

    /// The total ordinal length = the birthday (ordinary ordinal sum of runs).
    pub fn length(&self) -> Ordinal {
        let mut len = Ordinal::zero();
        for (_, l) in &self.runs {
            len = len.ord_add(l);
        }
        len
    }

    /// Run-length-encode a finite ±-sequence (`true = +`).
    pub fn from_finite(signs: &[bool]) -> Self {
        let mut runs: Vec<(bool, Ordinal)> = Vec::new();
        for &s in signs {
            if let Some(last) = runs.last_mut() {
                if last.0 == s {
                    last.1 = last.1.ord_add(&Ordinal::from_u128(1));
                    continue;
                }
            }
            runs.push((s, Ordinal::from_u128(1)));
        }
        SignExpansion { runs }
    }

    /// The flat ±-sequence, when every run length is finite; `None` if any run
    /// is transfinite (e.g. `ω`-many signs).
    pub fn as_finite(&self) -> Option<Vec<bool>> {
        let mut out = Vec::new();
        for (s, l) in &self.runs {
            let n = l.as_finite()?;
            for _ in 0..n {
                out.push(*s);
            }
        }
        Some(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(n: i128, d: i128) -> Surreal {
        Surreal::from_rational(Rational::new(n, d))
    }

    #[test]
    fn from_ordinal_inverts_as_ordinal() {
        // ordinal-valued surreals round-trip through the ordinal and back.
        let cases = [
            Surreal::from_int(0),
            Surreal::from_int(5),
            Surreal::omega(),                                          // ω
            Surreal::omega().add(&Surreal::from_int(1)),               // ω+1
            Surreal::monomial(Surreal::from_int(1), Rational::int(3)), // ω·3
            Surreal::omega_pow(Surreal::from_int(2)),                  // ω²
            Surreal::omega_pow(Surreal::omega()),                      // ω^ω
        ];
        for s in &cases {
            let o = s.as_ordinal().expect("ordinal-valued");
            assert_eq!(
                &Surreal::from_ordinal(&o),
                s,
                "from_ordinal∘as_ordinal ≠ id: {s:?}"
            );
        }
    }

    #[test]
    fn sign_expansion_from_runs_normalizes() {
        let se = SignExpansion::from_runs(vec![
            (true, Ordinal::from_u128(1)),
            (true, Ordinal::zero()),
            (true, Ordinal::from_u128(2)),
            (false, Ordinal::from_u128(1)),
        ]);
        assert_eq!(
            se.runs(),
            &[
                (true, Ordinal::from_u128(3)),
                (false, Ordinal::from_u128(1))
            ]
        );
        assert_eq!(se.as_finite(), Some(vec![true, true, true, false]));
    }

    #[test]
    fn transfinite_sign_expansion_round_trips() {
        // The full round trip across the representable subclass: dyadic, ordinal,
        // negative-ordinal, and the pinned infinitesimal ε — each recovered from
        // its (run-length) sign expansion, and the length matches the birthday.
        let cases = [
            Surreal::zero(),
            Surreal::from_int(1),
            Surreal::from_int(-1),
            Surreal::from_int(2),
            rat(1, 2),
            rat(1, 2).neg(),
            rat(3, 4),
            rat(3, 4).neg(),
            Surreal::omega(),                                          // ω
            Surreal::omega().add(&Surreal::from_int(1)),               // ω+1
            Surreal::monomial(Surreal::from_int(1), Rational::int(3)), // ω·3
            Surreal::omega_pow(Surreal::from_int(2)),                  // ω²
            Surreal::omega_pow(Surreal::omega()),                      // ω^ω
            Surreal::omega().neg(),                                    // −ω
            Surreal::epsilon(),                                        // ε
        ];
        for s in &cases {
            let se = s.transfinite_sign_expansion().expect("representable");
            assert_eq!(
                Surreal::from_transfinite_sign_expansion(&se).as_ref(),
                Some(s),
                "sign-expansion round trip failed: {s:?}"
            );
            assert_eq!(
                se.length(),
                s.birthday_ordinal().unwrap(),
                "length ≠ birthday: {s:?}"
            );
        }
    }
}
