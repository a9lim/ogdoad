//! Finite-subfield detection for represented ordinal nimbers.
//!
//! Every element of the source-verified tower below `ω^(ω^ω)` is algebraic over
//! `F_2`, hence belongs to a unique finite subfield `F_{2^m}`. This module detects
//! that `m` from the represented generator support and then minimizes it by the
//! Frobenius fixed-field test `x^(2^d) = x`.

use super::Ordinal;
use crate::scalar::nim_degree;

impl Ordinal {
    /// Minimal `m` such that this represented ordinal nimber lies in `F_{2^m}`.
    ///
    /// Returns `None` outside the staged segment (`>= ω^(ω^ω)`) or when the
    /// needed Kummer excess is past the verified table.
    pub fn finite_subfield_degree(&self) -> Option<u128> {
        ordinal_finite_subfield_degree(self)
    }
}

/// Minimal `m` such that `x` lies in the represented finite nim-subfield
/// `F_{2^m}`.
pub fn ordinal_finite_subfield_degree(x: &Ordinal) -> Option<u128> {
    if x.is_zero() {
        return Some(1);
    }
    let bound = degree_bound(x)?;
    minimize_degree_by_frobenius(x, bound)
}

/// Minimal common finite subfield degree containing every value in `values`.
pub fn ordinal_common_finite_subfield_degree<'a>(
    values: impl IntoIterator<Item = &'a Ordinal>,
) -> Option<u128> {
    values
        .into_iter()
        .try_fold(1u128, |acc, x| lcm(acc, ordinal_finite_subfield_degree(x)?))
}

fn degree_bound(x: &Ordinal) -> Option<u128> {
    x.terms().iter().try_fold(1u128, |acc, (exp, coeff)| {
        let coeff_degree = nim_degree(*coeff);
        let exp_degree = degree_bound_for_exponent(exp)?;
        lcm(acc, lcm(coeff_degree, exp_degree)?)
    })
}

fn degree_bound_for_exponent(exp: &Ordinal) -> Option<u128> {
    exp.terms().iter().try_fold(1u128, |acc, (place, coeff)| {
        let m = place.as_finite()?;
        let p = super::tower::place_prime(m);
        base_digits(*coeff, p)
            .into_iter()
            .enumerate()
            .filter(|&(_, digit)| digit != 0)
            .try_fold(acc, |inner, (k, _)| {
                lcm(inner, generator_degree(p, k as u128)?)
            })
    })
}

fn generator_degree(p: u128, level: u128) -> Option<u128> {
    let alpha = super::tower::alpha_ordinal(p)?;
    let alpha_degree = ordinal_finite_subfield_degree(&alpha)?;
    alpha_degree.checked_mul(checked_pow(p, level + 1)?)
}

fn minimize_degree_by_frobenius(x: &Ordinal, bound: u128) -> Option<u128> {
    let mut degree = bound;
    for p in prime_factors(bound) {
        while degree.is_multiple_of(p) {
            let candidate = degree / p;
            if frobenius_fixed(x, candidate)? {
                degree = candidate;
            } else {
                break;
            }
        }
    }
    Some(degree)
}

fn frobenius_fixed(x: &Ordinal, degree: u128) -> Option<bool> {
    let mut y = x.clone();
    for _ in 0..degree {
        y = y.nim_mul(&y)?;
    }
    Some(&y == x)
}

fn base_digits(mut value: u128, base: u128) -> Vec<u128> {
    let mut digits = Vec::new();
    while value > 0 {
        digits.push(value % base);
        value /= base;
    }
    digits
}

fn checked_pow(base: u128, exp: u128) -> Option<u128> {
    let mut acc = 1u128;
    for _ in 0..exp {
        acc = acc.checked_mul(base)?;
    }
    Some(acc)
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn lcm(a: u128, b: u128) -> Option<u128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    (a / gcd(a, b)).checked_mul(b)
}

fn prime_factors(mut n: u128) -> Vec<u128> {
    let mut factors = Vec::new();
    let mut d = 2u128;
    while d <= n / d {
        if n.is_multiple_of(d) {
            factors.push(d);
            while n.is_multiple_of(d) {
                n /= d;
            }
        }
        d += if d == 2 { 1 } else { 2 };
    }
    if n > 1 {
        factors.push(n);
    }
    factors
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fin(n: u128) -> Ordinal {
        Ordinal::from_u128(n)
    }

    #[test]
    fn finite_values_reuse_nimber_degrees() {
        assert_eq!(ordinal_finite_subfield_degree(&fin(0)), Some(1));
        assert_eq!(ordinal_finite_subfield_degree(&fin(1)), Some(1));
        assert_eq!(ordinal_finite_subfield_degree(&fin(2)), Some(2));
        assert_eq!(ordinal_finite_subfield_degree(&fin(16)), Some(8));
    }

    #[test]
    fn detects_first_ordinal_windows() {
        let omega = Ordinal::omega();
        let chi5 = Ordinal::omega_pow(Ordinal::omega());
        let chi7 = Ordinal::omega_pow(Ordinal::omega_pow(fin(2)));

        assert_eq!(ordinal_finite_subfield_degree(&omega), Some(6));
        assert_eq!(
            ordinal_finite_subfield_degree(&omega.nim_add(&fin(1))),
            Some(6)
        );
        assert_eq!(
            ordinal_finite_subfield_degree(&Ordinal::omega_pow(fin(3))),
            Some(18)
        );
        assert_eq!(ordinal_finite_subfield_degree(&chi5), Some(20));
        assert_eq!(ordinal_finite_subfield_degree(&chi7), Some(42));
    }

    #[test]
    fn common_degree_is_the_compositum_degree() {
        let omega = Ordinal::omega();
        let sixteen = fin(16);
        assert_eq!(
            ordinal_common_finite_subfield_degree([&omega, &sixteen]),
            Some(24)
        );
    }

    #[test]
    fn outside_staged_segment_returns_none() {
        let outside = Ordinal::omega_pow(Ordinal::omega_pow(Ordinal::omega()));
        assert_eq!(ordinal_finite_subfield_degree(&outside), None);
    }

    #[test]
    fn inverse_uses_detected_finite_subfields() {
        let chi5 = Ordinal::omega_pow(Ordinal::omega());
        let inv = chi5.checked_inv().unwrap();
        assert_eq!(chi5.nim_mul(&inv), Some(fin(1)));
    }
}
