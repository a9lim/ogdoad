//! κ-local arithmetic and the Artin–Schreier normal form (ASNF) layer.
//!
//! These are crate-private helpers for the Aravire–Jacob decomposition engine
//! in [`super`]. Nothing here is part of the public API.

use crate::forms::function_field_char2::{hensel_series, inverse_mod, ps_eval_poly, strip_factor};
use crate::forms::{artin_schreier_class_finite, FiniteChar2Field, FunctionFieldPlace};
use crate::scalar::{Poly, RationalFunction, Scalar};
use std::collections::BTreeMap;

// ───────────────────────── κ-local arithmetic at a place ─────────────────────────

/// `x^e` in any `Scalar` field by square-and-multiply (used for `F_q` square roots
/// at `∞`, where `√z = z^{q/2}` since Frobenius is the squaring map).
pub(super) fn s_pow<S: Scalar>(x: &S, mut e: u128) -> S {
    let mut base = x.clone();
    let mut acc = S::one();
    while e > 0 {
        if e & 1 == 1 {
            acc = acc.mul(&base);
        }
        base = base.mul(&base);
        e >>= 1;
    }
    acc
}

/// `a · b` in the residue field `κ` at `place`.
pub(super) fn kmul<S: FiniteChar2Field>(
    a: &Poly<S>,
    b: &Poly<S>,
    place: &FunctionFieldPlace<S>,
) -> Poly<S> {
    match place {
        FunctionFieldPlace::Finite(p) => a.mul_mod(b, p),
        FunctionFieldPlace::Infinite => Poly::constant(a.coeff(0).mul(&b.coeff(0))),
    }
}

/// `√z` in `κ` at `place`: `z^{|κ|/2}` (Frobenius inverse; `κ` is a perfect finite
/// field of char 2, so the square root is unique).
pub(super) fn kappa_sqrt<S: FiniteChar2Field>(
    z: &Poly<S>,
    place: &FunctionFieldPlace<S>,
) -> Poly<S> {
    match place {
        FunctionFieldPlace::Finite(p) => {
            let d = p.degree().expect("a place modulus has degree ≥ 1") as u128;
            let order = S::field_order().pow(
                d.try_into()
                    .expect("place degree fits the platform exponent type"),
            ); // |κ| = q^{deg P}
            z.pow_mod(order / 2, p)
        }
        FunctionFieldPlace::Infinite => Poly::constant(s_pow(&z.coeff(0), S::field_order() / 2)),
    }
}

/// `Tr_{κ/F₂}(z) ∈ {0,1}` at `place` (the `W_q(κ) ≅ F₂` Arf class of `[1, z]`).
pub(super) fn trace_at<S: FiniteChar2Field>(z: &Poly<S>, place: &FunctionFieldPlace<S>) -> u128 {
    use crate::forms::function_field_char2::trace_kappa_to_f2;
    match place {
        FunctionFieldPlace::Finite(p) => trace_kappa_to_f2(z, p),
        FunctionFieldPlace::Infinite => artin_schreier_class_finite(z.coeff(0)),
    }
}

// ───────────────────────── local Laurent expansion ─────────────────────────

/// `v(a)` (the `π`-adic valuation) at `place`; `None` iff `a = 0`.
pub(super) fn valuation<S: FiniteChar2Field>(
    a: &RationalFunction<S>,
    place: &FunctionFieldPlace<S>,
) -> Option<i128> {
    if a.is_zero() {
        return None;
    }
    match place {
        FunctionFieldPlace::Finite(p) => {
            let (mn, _) = strip_factor(a.num().clone(), p);
            let (md, _) = strip_factor(a.den().clone(), p);
            Some(mn as i128 - md as i128)
        }
        FunctionFieldPlace::Infinite => Some(
            a.den().degree().expect("nonzero den") as i128
                - a.num().degree().expect("nonzero num") as i128,
        ),
    }
}

/// Laurent coefficients of `a = num/den` at the finite place `P`, for the inclusive
/// exponent range `[n_lo, n_hi]` (`out[k]` = coefficient of `π^{n_lo+k}`, `π = P`).
fn laurent_finite<S: FiniteChar2Field>(
    num: &Poly<S>,
    den: &Poly<S>,
    p: &Poly<S>,
    n_lo: i128,
    n_hi: i128,
) -> Vec<Poly<S>> {
    let len = (n_hi - n_lo + 1) as usize;
    if num.is_zero() {
        return vec![Poly::zero(); len];
    }
    let (mn, ncof) = strip_factor(num.clone(), p);
    let (md, e) = strip_factor(den.clone(), p);
    let val = mn as i128 - md as i128;
    let hi_i = n_hi - val; // need power-series digits g_0 .. g_{hi_i}
    if hi_i < 0 {
        return vec![Poly::zero(); len];
    }
    let count = (hi_i + 1) as usize;
    let mut pmod = Poly::one();
    for _ in 0..count {
        pmod = pmod.mul(p);
    }
    let e_inv = inverse_mod(&e, &pmod);
    let b = ncof.mul(&e_inv).rem(&pmod); // g mod P^count
    let t = hensel_series(p, count);
    let coeffs = ps_eval_poly(&b, &t, count, p); // g(T(u)) in κ[[u]]
    let mut out = Vec::with_capacity(len);
    for n in n_lo..=n_hi {
        let i = n - val;
        if i < 0 || (i as usize) >= coeffs.len() {
            out.push(Poly::zero());
        } else {
            out.push(coeffs[i as usize].clone());
        }
    }
    out
}

/// Laurent coefficients of `a = num/den` at `∞` (`π = 1/t`), inclusive range
/// `[n_lo, n_hi]`. `a = π^v · (Ñ/D̃)` with `Ñ, D̃` the coefficient-reversed
/// polynomials; the unit `Ñ·D̃⁻¹` is expanded as an `F_q[[π]]` power series.
fn laurent_infinite<S: FiniteChar2Field>(
    num: &Poly<S>,
    den: &Poly<S>,
    n_lo: i128,
    n_hi: i128,
) -> Vec<Poly<S>> {
    let len = (n_hi - n_lo + 1) as usize;
    if num.is_zero() {
        return vec![Poly::zero(); len];
    }
    let dn = num.degree().expect("nonzero num") as i128;
    let dd = den.degree().expect("nonzero den") as i128;
    let val = dd - dn;
    let hi_i = n_hi - val;
    if hi_i < 0 {
        return vec![Poly::zero(); len];
    }
    let prec = (hi_i + 1) as usize;
    let nt: Vec<S> = num.coeffs().iter().rev().cloned().collect(); // Ñ
    let dt: Vec<S> = den.coeffs().iter().rev().cloned().collect(); // D̃ (dt[0] = lead den ≠ 0)
    let d0_inv = dt[0].inv().expect("lead(den) inverts");
    let mut binv = vec![S::zero(); prec]; // D̃⁻¹
    binv[0] = d0_inv;
    for i in 1..prec {
        let mut acc = S::zero();
        for j in 1..=i {
            if j < dt.len() {
                acc = acc.add(&dt[j].mul(&binv[i - j]));
            }
        }
        binv[i] = acc.mul(&d0_inv); // char 2: −d0⁻¹·acc = d0⁻¹·acc
    }
    let mut g = vec![S::zero(); prec]; // Ñ · D̃⁻¹
    for (i, gi) in g.iter_mut().enumerate() {
        let mut acc = S::zero();
        for j in 0..=i {
            if j < nt.len() {
                acc = acc.add(&nt[j].mul(&binv[i - j]));
            }
        }
        *gi = acc;
    }
    let mut out = Vec::with_capacity(len);
    for n in n_lo..=n_hi {
        let i = n - val;
        if i < 0 || (i as usize) >= prec {
            out.push(Poly::zero());
        } else {
            out.push(Poly::constant(g[i as usize]));
        }
    }
    out
}

/// Laurent coefficients of `a` at `place`, inclusive range `[n_lo, n_hi]`.
pub(super) fn laurent<S: FiniteChar2Field>(
    a: &RationalFunction<S>,
    place: &FunctionFieldPlace<S>,
    n_lo: i128,
    n_hi: i128,
) -> Vec<Poly<S>> {
    match place {
        FunctionFieldPlace::Finite(p) => laurent_finite(a.num(), a.den(), p, n_lo, n_hi),
        FunctionFieldPlace::Infinite => laurent_infinite(a.num(), a.den(), n_lo, n_hi),
    }
}

// ───────────────────────── the Artin–Schreier normal form ─────────────────────────

/// Reduce a `≤ 0`-degree Laurent tail `c = Σ_{n ≤ 0} c_n π^n` (given as a sparse map
/// over `[lo, 0]`) modulo `℘(K_v)`: clear even negative poles bottom-up, leaving a
/// `κ`-constant and odd negative poles. Returns `(Tr_{κ/F₂}(c₀), R_π map)`.
pub(super) fn asnf<S: FiniteChar2Field>(
    coeffs: &BTreeMap<i128, Poly<S>>,
    lo: i128,
    place: &FunctionFieldPlace<S>,
) -> (u128, BTreeMap<usize, Poly<S>>) {
    let mut m = coeffs.clone();
    let mut n = lo;
    while n < 0 {
        if n & 1 == 0 {
            // even negative power: subtract ℘(√c_n · π^{n/2}) to kill it
            if let Some(v) = m.get(&n).cloned() {
                if !v.is_zero() {
                    let s = kappa_sqrt(&v, place);
                    m.insert(n, Poly::zero());
                    let half = n / 2;
                    let cur = m.get(&half).cloned().unwrap_or_else(Poly::zero);
                    m.insert(half, cur.add(&s));
                }
            }
        }
        n += 1;
    }
    let eps = m.get(&0).map(|v| trace_at(v, place)).unwrap_or(0);
    let mut r = BTreeMap::new();
    for (k, v) in &m {
        if *k < 0 && (k & 1 == 1) && !v.is_zero() {
            r.insert((-k) as usize, v.clone());
        }
    }
    (eps, r)
}

/// Merge `k ↦ v` into a sparse `R_π` map (κ-addition; drop a coefficient that cancels).
pub(super) fn merge_psi<S: FiniteChar2Field>(
    psi: &mut BTreeMap<usize, Poly<S>>,
    k: usize,
    v: Poly<S>,
) {
    let cur = psi.get(&k).cloned().unwrap_or_else(Poly::zero);
    let sum = cur.add(&v);
    if sum.is_zero() {
        psi.remove(&k);
    } else {
        psi.insert(k, sum);
    }
}

/// The local AS class of `c ∈ F_q(t)` at `place`: `(Tr_{κ/F₂}(c₀), R_π map)`.
/// `c ∈ ℘(K_v)` iff this is `(0, ∅)`.
pub(super) fn local_as_class<S: FiniteChar2Field>(
    c: &RationalFunction<S>,
    place: &FunctionFieldPlace<S>,
) -> (u128, BTreeMap<usize, Poly<S>>) {
    match valuation(c, place) {
        None => (0, BTreeMap::new()), // c = 0 ∈ ℘(K_v)
        Some(v) => {
            let lo = std::cmp::min(v, 0);
            let coeffs = laurent(c, place, lo, 0);
            let mut map = BTreeMap::new();
            for n in lo..=0 {
                let cc = coeffs[(n - lo) as usize].clone();
                if !cc.is_zero() {
                    map.insert(n, cc);
                }
            }
            asnf(&map, lo, place)
        }
    }
}

/// Whether `c ∈ ℘(K_v)` at `place` (the local Artin–Schreier triviality test).
pub(super) fn local_is_pe<S: FiniteChar2Field>(
    c: &RationalFunction<S>,
    place: &FunctionFieldPlace<S>,
) -> bool {
    let (e, r) = local_as_class(c, place);
    e == 0 && r.is_empty()
}

pub(super) fn dpoly<S: Scalar>(p: &Poly<S>) -> Poly<S> {
    let cs = p.coeffs();
    if cs.len() <= 1 {
        return Poly::zero();
    }
    let mut out = vec![S::zero(); cs.len() - 1];
    for (i, c) in cs.iter().enumerate().skip(1) {
        if i & 1 == 1 {
            out[i - 1] = c.clone();
        }
    }
    Poly::new(out)
}

pub(super) fn rational_derivative_is_zero<S: FiniteChar2Field>(f: &RationalFunction<S>) -> bool {
    dpoly(f.num())
        .mul(f.den())
        .add(&f.num().mul(&dpoly(f.den())))
        .is_zero()
}

/// Whether `f ∈ K_v²` in the completion at `place`.
pub(super) fn local_is_square<S: FiniteChar2Field>(
    f: &RationalFunction<S>,
    place: &FunctionFieldPlace<S>,
) -> bool {
    let Some(v) = valuation(f, place) else {
        return true;
    };
    if v & 1 != 0 {
        return false;
    }
    rational_derivative_is_zero(f)
}
