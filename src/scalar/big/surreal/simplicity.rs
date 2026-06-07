//! The `{L|R}` / **simplicity** bridge for surreals: dyadic recognition,
//! birthdays, the `simplest_*` cut selectors, and `floor`/`frac` (the bridge to
//! the omnific integers `Oz`). All of it is the dyadic/finite-rational face of a
//! surreal — the part a short partizan game can reach.
//!
//! The free helpers here (`simplest_in_cut` and friends) compute "the shallowest
//! surreal-tree node in a cut"; `simplest_in_cut` is `pub(super)` because the
//! sibling [`sign_expansion`](super::sign_expansion) module walks the same cuts.

use super::Surreal;
use crate::scalar::{Rational, Scalar};
use std::cmp::Ordering;

impl Surreal {
    /// This surreal as a finite rational, if it is one — a single constant
    /// (`ω⁰`) term, or zero. `None` for anything carrying an `ω`-term
    /// (infinite/infinitesimal), which no short game can reach.
    pub fn as_rational(&self) -> Option<Rational> {
        match self.terms.as_slice() {
            [] => Some(Rational::zero()),
            [(e, c)] if e.is_zero() => Some(c.clone()),
            _ => None,
        }
    }

    /// This surreal as a dyadic rational `num / 2^k` — exactly the values a short
    /// partizan game can take ([`crate::games::Game::number_value`]). Returns
    /// `(num, k)` with `num` odd whenever `k > 0`. `None` for non-dyadics.
    pub fn as_dyadic(&self) -> Option<(i128, u32)> {
        let q = self.as_rational()?;
        let den = q.denom();
        if den & (den - 1) != 0 {
            return None; // denominator is not a power of two
        }
        Some((q.numer(), den.trailing_zeros()))
    }

    /// True iff this surreal is a dyadic rational.
    pub fn is_dyadic(&self) -> bool {
        self.as_dyadic().is_some()
    }

    /// The birthday of a dyadic rational — the day it is born in the surreal
    /// construction (`0`↦0, `±n`↦n, `½`↦2, `¼`/`¾`↦3, …), equal to the
    /// [birthday](crate::games::Game::birthday) of its canonical game. `None`
    /// for non-dyadics, whose birthday is an infinite ordinal outside this
    /// finite-support representation.
    pub fn dyadic_birthday(&self) -> Option<u128> {
        let (num, k) = self.as_dyadic()?;
        Some(birthday_dyadic(num, k))
    }

    /// The simplest surreal strictly greater than `self` — the value of `{self|}`
    /// — when `self` is a finite rational. `None` if `self` carries an `ω`-term.
    pub fn simplest_above(&self) -> Option<Surreal> {
        let q = self.as_rational()?;
        let v = if q.sign() == Ordering::Less {
            Rational::zero() // 0 is the simplest number above any negative
        } else {
            Rational::int(q.floor() + 1) // the least integer strictly above q ≥ 0
        };
        Some(Surreal::from_rational(v))
    }

    /// The simplest surreal strictly less than `self` — the value of `{|self}` —
    /// when `self` is a finite rational. `None` if `self` carries an `ω`-term.
    pub fn simplest_below(&self) -> Option<Surreal> {
        Some(self.neg().simplest_above()?.neg())
    }

    /// The unique simplest surreal strictly between `a` and `b` (Conway's
    /// simplicity theorem), realised when that value is dyadic — i.e. when `a`
    /// and `b` are finite rationals with `a < b`. The result is always dyadic.
    /// `None` if either endpoint carries an `ω`-term or `a ≥ b`.
    pub fn simplest_between(a: &Surreal, b: &Surreal) -> Option<Surreal> {
        let (qa, qb) = (a.as_rational()?, b.as_rational()?);
        if qa.cmp(&qb) != Ordering::Less {
            return None;
        }
        Some(Surreal::from_rational(simplest_rational_between(qa, qb)))
    }

    /// The **floor** ⌊x⌋ — the greatest omnific integer ≤ `x`, as a `Surreal`.
    /// Concretely: keep every infinite term (`ω`-exponent `> 0`, any rational
    /// coefficient), floor the finite constant, and drop every infinitesimal
    /// term (`ω`-exponent `< 0`). If the finite constant is already an integer,
    /// a negative infinitesimal tail borrows one from that integer part. The
    /// result is always an omnific integer ([`crate::scalar::Omnific`]);
    /// `Omnific::floor` wraps it as one. Satisfies `⌊x⌋ ≤ x < ⌊x⌋ + 1`.
    pub fn floor(&self) -> Surreal {
        let mut terms: Vec<(Surreal, Rational)> = Vec::new();
        let mut constant = Rational::zero();
        let mut saw_constant = false;
        let mut infinitesimal_sign = Ordering::Equal;
        for (e, c) in &self.terms {
            match e.sign() {
                Ordering::Greater => terms.push((e.clone(), c.clone())), // infinite term kept
                Ordering::Equal => {
                    constant = c.clone();
                    saw_constant = true;
                }
                Ordering::Less if infinitesimal_sign == Ordering::Equal => {
                    infinitesimal_sign = c.sign();
                }
                Ordering::Less => {} // lower infinitesimals are dominated
            }
        }
        let mut f = constant.floor();
        if (!saw_constant || constant.is_integer()) && infinitesimal_sign == Ordering::Less {
            f -= 1;
        }
        if f != 0 {
            terms.push((Surreal::zero(), Rational::int(f)));
        }
        // terms stay strictly descending (a subset of self's, same order)
        Surreal { terms }
    }

    /// The **fractional part** `x − ⌊x⌋`, always in `[0, 1)` (it may be an
    /// infinitesimal-carrying value such as `½ + ε`).
    pub fn frac(&self) -> Surreal {
        self.sub(&self.floor())
    }
}

/// The simplest dyadic strictly **below** `h` (the value of the cut `{|h}`).
fn simplest_below_rat(h: &Rational) -> Rational {
    if h.sign() == Ordering::Greater {
        Rational::zero() // 0 is the simplest number below any positive
    } else {
        let f = h.floor();
        if Rational::int(f).cmp(h) == Ordering::Less {
            Rational::int(f) // h non-integer: ⌊h⌋ is the closest-to-0 integer below it
        } else {
            Rational::int(f - 1) // h an integer: the next integer down
        }
    }
}

/// The simplest dyadic strictly **above** `l` (the value of the cut `{l|}`).
fn simplest_above_rat(l: &Rational) -> Rational {
    simplest_below_rat(&l.neg()).neg()
}

/// The simplest dyadic strictly inside the open cut `(lo, hi)`; `None` bounds are
/// `∓∞`. This is the surreal-tree node selected at each step of a sign-expansion
/// walk — shared with [`sign_expansion`](super::sign_expansion).
pub(super) fn simplest_in_cut(lo: &Option<Rational>, hi: &Option<Rational>) -> Rational {
    match (lo, hi) {
        (None, None) => Rational::zero(),
        (None, Some(h)) => simplest_below_rat(h),
        (Some(l), None) => simplest_above_rat(l),
        (Some(l), Some(h)) => simplest_rational_between(l.clone(), h.clone()),
    }
}

/// Strip factors of two from a dyadic `num / 2^k` to put it in lowest terms.
fn reduce_dyadic(mut num: i128, mut k: u32) -> (i128, u32) {
    while k > 0 && num % 2 == 0 {
        num /= 2;
        k -= 1;
    }
    (num, k)
}

/// Birthday of the dyadic `num / 2^k` via the canonical `{L|R}` recursion: an
/// integer `n` is born on day `|n|`; a non-integer dyadic on `1 +` the later of
/// its two nearest-dyadic options at `±1/2^k`.
fn birthday_dyadic(num: i128, k: u32) -> u128 {
    if k == 0 {
        return num.unsigned_abs();
    }
    let (ln, lk) = reduce_dyadic(num - 1, k);
    let (rn, rk) = reduce_dyadic(num + 1, k);
    1 + birthday_dyadic(ln, lk).max(birthday_dyadic(rn, rk))
}

/// The simplest dyadic strictly between two rationals `a < b` (the shallowest
/// node of the surreal tree inside the interval).
fn simplest_rational_between(a: Rational, b: Rational) -> Rational {
    // Reflect so the descent only handles the non-negative spine.
    if b.sign() != Ordering::Greater {
        return simplest_rational_between(b.neg(), a.neg()).neg();
    }
    if a.sign() == Ordering::Less {
        return Rational::zero(); // a < 0 < b: 0 is the root, simplest of all
    }
    // 0 ≤ a < b. The least integer strictly above a:
    let c = a.floor() + 1;
    if Rational::int(c).cmp(&b) == Ordering::Less {
        return Rational::int(c); // an integer lives in (a,b); c is closest to 0
    }
    // a and b lie inside one open unit interval (m, m+1).
    let m = a.floor();
    let off = Rational::int(m);
    off.add(&simplest_in_unit(a.sub(&off), b.sub(&off)))
}

/// The shallowest dyadic in `(a, b)` with `0 ≤ a < b ≤ 1`, by binary
/// subdivision of the unit interval.
fn simplest_in_unit(a: Rational, b: Rational) -> Rational {
    let half = Rational::new(1, 2);
    let mut lo = Rational::zero();
    let mut hi = Rational::one();
    loop {
        let mid = lo.add(&hi).mul(&half);
        let below_b = mid.cmp(&b) == Ordering::Less;
        let above_a = a.cmp(&mid) == Ordering::Less;
        if above_a && below_b {
            return mid;
        } else if !above_a {
            lo = mid; // mid ≤ a: search the upper half
        } else {
            hi = mid; // mid ≥ b: search the lower half
        }
    }
}
