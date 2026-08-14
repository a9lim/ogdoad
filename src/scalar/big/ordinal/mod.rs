//! Recursive ordinals with ordinary Cantor arithmetic and checked nim arithmetic.
//!
//! [`Ordinal`] stores a finite Cantor normal form `Σ ω^{βᵢ}cᵢ`. The
//! `cantor` operations are ordinary, noncommutative ordinal sum and product. The
//! `nim` operations use characteristic-two
//! addition and Conway--Lenstra--DiMuro multiplication.
//!
//! Conway's ordinal nimbers form an algebraically closed characteristic-two
//! field; the algebraic closure of `F₂` lies below `ω^(ω^ω)` (Conway, *ONAG*,
//! ch. 6; Lenstra, *Nim multiplication*; DiMuro, arXiv:1108.0962). This backend
//! represents only finite recursive CNFs and implements multiplication on the
//! `< ω^(ω^ω)` segment subject to a checked Kummer-data boundary.
//!
//! Nim-addition is total. [`Ordinal::nim_mul`], [`Ordinal::nim_pow`],
//! [`Ordinal::checked_inv`], and [`Ordinal::checked_sqrt`] return `None` when an
//! operand leaves the represented segment or a carry needs a Lenstra-excess row
//! beyond the source-backed table through prime `727`. The universal `0/1/4`
//! excess rule remains open; table rows and their certificates establish only the
//! encoded finite window. See `docs/OPEN.md`.

mod cantor;
mod nim;
mod subfield;
mod support;
mod tower;

use crate::scalar::{nim_inv, nim_sqrt, Scalar};
use std::cmp::Ordering;
use std::fmt;

/// An ordinal below `ε₀`, represented by a finite Cantor normal form
/// `Σ ω^{exp}·coeff` with descending exponents and nonzero `u128` coefficients.
#[derive(Clone, PartialEq, Eq)]
pub struct Ordinal {
    terms: Vec<(Ordinal, u128)>,
}

impl Ordinal {
    /// The ordinal `0`.
    pub fn zero() -> Self {
        Ordinal { terms: Vec::new() }
    }

    /// A finite ordinal / nimber `n` — a **representation** constructor.
    ///
    /// **Representation constructor vs ℤ-embedding:**
    /// `Ordinal::from_u128(n)` says "the ordinal *n*", treating the u128 as a
    /// non-negative ordinal directly. The ℤ-embedding `Scalar::from_int(n)` is
    /// `n mod 2` for this characteristic-2 world (the unique unital ring
    /// homomorphism ℤ → On₂). Do NOT use `from_u128` to embed integers.
    pub fn from_u128(n: u128) -> Self {
        if n == 0 {
            Ordinal::zero()
        } else {
            Ordinal {
                terms: vec![(Ordinal::zero(), n)],
            }
        }
    }

    /// A single monomial `ω^exp · coeff`.
    pub fn monomial(exp: Ordinal, coeff: u128) -> Self {
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
        Ordinal::omega_pow(Ordinal::from_u128(1))
    }

    /// Whether this is the zero ordinal.
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// Canonical Cantor-normal-form terms, in descending exponent order.
    pub fn terms(&self) -> &[(Ordinal, u128)] {
        &self.terms
    }

    /// The nimber/game-value fuzzy relation: distinct ordinal nimbers are
    /// incomparable as games, regardless of their CNF address order.
    pub fn fuzzy(&self, other: &Self) -> bool {
        self != other
    }

    /// The ordinal order (lexicographic on descending CNF terms).
    // Inherent value-order, deliberately kept off `std::cmp::Ord`: orders and
    // operators are opt-in here, not blanket trait impls (see AGENTS.md). The
    // ordinal (lex) order also differs from the nim-value structure on the same
    // CNF, so a single std `Ord` impl would be ambiguous.
    #[allow(clippy::should_implement_trait)]
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

    /// True iff this ordinal is finite (a single `ω^0` term, or zero), returning
    /// the finite nimber value.
    pub fn as_finite(&self) -> Option<u128> {
        match self.terms.as_slice() {
            [] => Some(0),
            [(exp, c)] if exp.is_zero() => Some(*c),
            _ => None,
        }
    }

    /// Checked power via square-and-multiply over [`nim_mul`](Self::nim_mul).
    ///
    /// `nim_pow(x, 0)` returns `Some(one())` regardless of `x` (including zero,
    /// which is the convention `x^0 = 1` in rings). `None` propagates whenever
    /// any intermediate [`nim_mul`](Self::nim_mul) call returns `None` — i.e.
    /// whenever a product escapes the verified Kummer boundary (`≥ ω^(ω^ω)` or
    /// a carry past the certified prime table).
    ///
    /// Use this instead of `Scalar::mul`-based iteration when an explicit
    /// `Option` boundary is needed, consistent with the deliberate omission of
    /// owned `*` and `^` on `Ordinal`.
    pub fn nim_pow(&self, mut k: u128) -> Option<Ordinal> {
        if k == 0 {
            return Some(Ordinal::from_u128(1));
        }
        let mut acc = Ordinal::from_u128(1);
        let mut base = self.clone();
        loop {
            if k & 1 == 1 {
                acc = acc.nim_mul(&base)?;
            }
            k >>= 1;
            if k == 0 {
                break;
            }
            base = base.nim_mul(&base)?;
        }
        Some(acc)
    }

    /// Checked square root on represented finite subfields.
    ///
    /// Every element of `F_{2^m}` has the unique square root `x^(2^(m-1))`, the
    /// inverse of Frobenius. Finite nimbers delegate to the total `u128` backend;
    /// transfinite values first detect their minimal represented finite subfield,
    /// then apply checked Frobenius squaring `m - 1` times. `None` reports the same
    /// honest boundary as [`finite_subfield_degree`](Self::finite_subfield_degree)
    /// and [`nim_mul`](Self::nim_mul): an input outside the represented segment or an
    /// intermediate Kummer carry beyond the certified excess table.
    pub fn checked_sqrt(&self) -> Option<Ordinal> {
        if let Some(x) = self.as_finite() {
            return Some(Ordinal::from_u128(nim_sqrt(x)));
        }
        let degree = self.finite_subfield_degree()?;
        let mut root = self.clone();
        for _ in 1..degree {
            root = root.nim_mul(&root)?;
        }
        (root.nim_mul(&root).as_ref() == Some(self)).then_some(root)
    }

    /// Checked multiplicative inverse on represented finite subfields. Finite
    /// nimbers use the `u128` backend; detected finite ordinal-nimber fields use
    /// the Frobenius formula `x^(2^m-2)` inside their minimal `F_{2^m}`.
    pub fn checked_inv(&self) -> Option<Ordinal> {
        if self.is_zero() {
            return None;
        }
        if let Some(x) = self.as_finite() {
            return nim_inv(x).map(Ordinal::from_u128);
        }
        let degree = self.finite_subfield_degree()?;
        let one = Ordinal::from_u128(1);
        let mut acc = one.clone();
        let mut power = self.clone();
        for _ in 1..degree {
            power = power.nim_mul(&power)?;
            acc = acc.nim_mul(&power)?;
        }
        (self.nim_mul(&acc).as_ref() == Some(&one)).then_some(acc)
    }
}

pub use subfield::{ordinal_common_finite_subfield_degree, ordinal_finite_subfield_degree};

impl Scalar for Ordinal {
    fn zero() -> Self {
        Ordinal::zero()
    }

    fn one() -> Self {
        Ordinal::from_u128(1)
    }

    fn add(&self, rhs: &Self) -> Self {
        self.nim_add(rhs)
    }

    fn neg(&self) -> Self {
        self.clone()
    }

    fn mul(&self, rhs: &Self) -> Self {
        self.nim_mul(rhs).unwrap_or_else(|| {
            panic!(
                "Ordinal::mul escaped the represented nim-product tower: left={self:?}, right={rhs:?}"
            )
        })
    }

    fn characteristic() -> u128 {
        2
    }

    fn inv(&self) -> Option<Self> {
        self.checked_inv()
    }
}

/// The omega-power base `ω↑exp` in canonical grundy syntax
/// (`grundy/docs/spec.md` §12). Empty for a
/// finite (exponent-0) term, bare `ω` for exponent 1, `ω↑k` for a plain finite
/// exponent `k`, and `ω↑(…)` for any compound ordinal exponent.
fn fmt_exp(e: &Ordinal) -> String {
    if e.is_zero() {
        String::new()
    } else if *e == Ordinal::from_u128(1) {
        "ω".to_string()
    } else if e.terms.len() == 1 && e.terms[0].0.is_zero() {
        format!("ω↑{}", e.terms[0].1) // ω↑k for a finite exponent k
    } else {
        format!("ω↑({})", fmt_cnf(e)) // ω↑(…) for a compound ordinal exponent
    }
}

/// The bare (un-starred) CNF body, e.g. `ω↑2 + ω⋅3 + 5` — the canonical inside
/// of a star-literal. Terms join with ` + `; the omega-power and its coefficient
/// join with `⋅` (U+22C5).
///
/// Deliberately `base⋅coeff` (`ω⋅3`, the base first), the reverse of the
/// crate-wide `coeff⋅label` rule (`Multivector`/`Poly`, `grundy/docs/spec.md`
/// §12). Not a drift to fix: CNF is conventionally written `ω^β·n`, and ordinal
/// multiplication is non-commutative, so `base⋅coeff` (not `coeff⋅base`)
/// carries real meaning here.
fn fmt_cnf(x: &Ordinal) -> String {
    let parts: Vec<String> = x
        .terms
        .iter()
        .map(|(e, c)| {
            let base = fmt_exp(e);
            if base.is_empty() {
                format!("{c}") // finite term
            } else if *c == 1 {
                base
            } else {
                format!("{base}⋅{c}")
            }
        })
        .collect();
    parts.join(" + ")
}

impl fmt::Display for Ordinal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.terms.is_empty() {
            return write!(f, "*0"); // the zero nimber
        }
        // A bare star applies only to a finite value (`*5`) or bare ω (`*ω`);
        // every compound ordinal index takes parens (`*(ω + 1)`, `*(ω↑2)`).
        let bare =
            (self.terms.len() == 1 && self.terms[0].0.is_zero()) || *self == Ordinal::omega();
        if bare {
            write!(f, "*{}", fmt_cnf(self))
        } else {
            write!(f, "*({})", fmt_cnf(self))
        }
    }
}

impl fmt::Debug for Ordinal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fin(n: u128) -> Ordinal {
        Ordinal::from_u128(n)
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
    fn fuzzy_is_distinctness_not_cnf_order() {
        assert!(!Ordinal::omega().fuzzy(&Ordinal::omega()));
        assert!(Ordinal::omega().fuzzy(&fin(7)));
    }

    #[test]
    fn display_reads_as_cnf() {
        // Canonical grundy syntax: star-wrapped, bare star only for finite/bare-ω.
        assert_eq!(format!("{:?}", Ordinal::omega()), "*ω");
        assert_eq!(format!("{:?}", Ordinal::monomial(fin(1), 3)), "*(ω⋅3)");
        assert_eq!(format!("{:?}", Ordinal::omega_pow(fin(2))), "*(ω↑2)");
        assert_eq!(
            format!("{:?}", Ordinal::omega().nim_add(&fin(1))),
            "*(ω + 1)"
        );
        assert_eq!(format!("{:?}", fin(5)), "*5");
        assert_eq!(format!("{:?}", Ordinal::zero()), "*0");
        // ω↑(ω): a bare-ω exponent parenthesizes.
        assert_eq!(
            format!("{:?}", Ordinal::omega_pow(Ordinal::omega())),
            "*(ω↑(ω))"
        );
    }

    #[test]
    fn scalar_impl_matches_checked_nim_arithmetic() {
        let w = Ordinal::omega();
        let one = Ordinal::one();
        assert_eq!(w.add(&one), w.nim_add(&one));
        assert_eq!(w.neg(), w);
        assert_eq!(w.mul(&w).mul(&w), fin(2)); // ω^3 = 2
        assert_eq!(Ordinal::characteristic(), 2);
    }

    #[test]
    fn checked_inverse_covers_finite_and_f64_subfield() {
        let three = fin(3);
        assert_eq!(three.mul(&three.inv().unwrap()), Ordinal::one());

        let w_plus_1 = Ordinal::omega().nim_add(&fin(1));
        let inv = w_plus_1.inv().expect("ω+1 lies in the enumerated F_64");
        assert_eq!(w_plus_1.mul(&inv), Ordinal::one());
    }

    #[test]
    fn checked_square_root_covers_finite_and_transfinite_subfields() {
        for value in [0, 1, 2, 3, 16, u128::MAX] {
            let x = fin(value);
            let root = x.checked_sqrt().unwrap();
            assert_eq!(root, fin(nim_sqrt(value)));
            assert_eq!(root.nim_mul(&root), Some(x));
        }

        let omega = Ordinal::omega();
        let chi5 = Ordinal::omega_pow(omega.clone());
        for x in [omega.clone(), omega.nim_add(&fin(1)), chi5] {
            let root = x
                .checked_sqrt()
                .expect("sample lies in the supported tower");
            assert_eq!(root.nim_mul(&root), Some(x));
        }
    }

    #[test]
    fn checked_square_root_refuses_outside_represented_segment() {
        let out_of_range = Ordinal::omega_pow(Ordinal::omega_pow(Ordinal::omega()));
        assert_eq!(out_of_range.checked_sqrt(), None);
    }

    #[test]
    #[should_panic(expected = "Ordinal::mul escaped the represented nim-product tower")]
    fn scalar_mul_panics_past_verified_tower() {
        let out_of_range = Ordinal::omega_pow(Ordinal::omega_pow(Ordinal::omega()));
        let _ = out_of_range.mul(&Ordinal::omega());
    }

    // ── nim_pow tests ─────────────────────────────────────────────────────────

    #[test]
    fn nim_pow_zero_is_one() {
        // x^0 = 1 regardless of x.
        assert_eq!(Ordinal::omega().nim_pow(0), Some(fin(1)));
        assert_eq!(fin(0).nim_pow(0), Some(fin(1)));
        assert_eq!(fin(5).nim_pow(0), Some(fin(1)));
    }

    #[test]
    fn nim_pow_omega_cubed_is_two() {
        // Conway: ω is the nim cube root of 2, so ω^3 = 2 (= *2 in ordinal display).
        let omega = Ordinal::omega();
        assert_eq!(omega.nim_pow(3), Some(fin(2)));
    }

    #[test]
    fn nim_pow_propagates_none_on_escape() {
        // ω^(ω^ω) is outside the verified Kummer boundary; any multiplication
        // involving it should return None.
        let out_of_range = Ordinal::omega_pow(Ordinal::omega_pow(Ordinal::omega()));
        assert_eq!(out_of_range.nim_pow(2), None);
    }
}
