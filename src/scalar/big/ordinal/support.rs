//! Integer-factor and generator-coordinate helpers shared inside the ordinal tower.
//!
//! These are implementation details of the represented Conway--DiMuro segment,
//! kept together so tower multiplication and finite-subfield detection use one
//! prime/place convention and one checked fixed-width arithmetic boundary.

use crate::scalar::is_prime_u128;

/// The prime governing exponent-place `omega^m`: the `(m+2)`-th prime, with 2
/// excluded because the finite Fermat tower is handled by the `u128` nimber core.
pub(super) fn place_prime(m: u128) -> u128 {
    let mut count = 0u128;
    let mut n = 2u128;
    loop {
        n += 1;
        if is_prime_u128(n) {
            count += 1;
            if count == m + 1 {
                return n;
            }
        }
    }
}

/// The zero-based ordinal-tower place of an odd prime.
pub(super) fn odd_prime_place(p: u128) -> Option<u128> {
    if p == 2 || !is_prime_u128(p) {
        return None;
    }
    let mut place = 0u128;
    loop {
        let q = place_prime(place);
        if q == p {
            return Some(place);
        }
        if q > p {
            return None;
        }
        place += 1;
    }
}

fn smallest_prime_factor(n: u128) -> Option<u128> {
    if n < 2 {
        return None;
    }
    if n.is_multiple_of(2) {
        return Some(2);
    }
    let mut d = 3u128;
    while d <= n / d {
        if n.is_multiple_of(d) {
            return Some(d);
        }
        d += 2;
    }
    Some(n)
}

/// Split `h = r*g`, where `r` is the full power of `h`'s smallest prime factor.
pub(super) fn smallest_prime_power_factor(h: u128) -> Option<(u128, u128)> {
    if h <= 1 {
        return None;
    }
    let p = smallest_prime_factor(h)?;
    let mut r = 1u128;
    let mut g = h;
    while g.is_multiple_of(p) {
        r = r.checked_mul(p)?;
        g /= p;
    }
    Some((r, g))
}

/// Recognize a positive prime power `q = p^n`.
pub(super) fn prime_power(q: u128) -> Option<(u128, u128)> {
    if q < 2 {
        return None;
    }
    let p = smallest_prime_factor(q)?;
    let mut n = 0u128;
    let mut rest = q;
    while rest.is_multiple_of(p) {
        n += 1;
        rest /= p;
    }
    (rest == 1).then_some((p, n))
}

pub(super) fn checked_pow(base: u128, exp: u128) -> Option<u128> {
    let mut acc = 1u128;
    for _ in 0..exp {
        acc = acc.checked_mul(base)?;
    }
    Some(acc)
}

/// Base-`base` digits, least-significant first and without trailing zeros.
pub(super) fn base_digits(mut value: u128, base: u128) -> Vec<u128> {
    let mut digits = Vec::new();
    while value > 0 {
        digits.push(value % base);
        value /= base;
    }
    digits
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn factor_helpers_share_one_prime_power_convention() {
        assert_eq!(smallest_prime_power_factor(360), Some((8, 45)));
        assert_eq!(prime_power(125), Some((5, 3)));
        assert_eq!(prime_power(75), None);
        assert_eq!(checked_pow(5, 3), Some(125));
    }

    #[test]
    fn prime_places_round_trip() {
        for (place, prime) in [(0, 3), (1, 5), (2, 7), (6, 19), (17, 67)] {
            assert_eq!(place_prime(place), prime);
            assert_eq!(odd_prime_place(prime), Some(place));
        }
    }
}
