//! Numeric finite-field invariants: level, Pythagoras number, and u-invariant.
//!
//! [`finite_field_numeric_invariants`] reports the three invariants uniformly
//! for supported prime fields and extension fields.  The production path uses
//! the finite-field theorems, so its cost is independent of the field order;
//! the small exhaustive searches below remain independent test oracles and
//! support [`is_sum_of_n_squares`]'s prime-field membership query.
//!
//! Every finite field has level `1` or `2`, Pythagoras number at most `2`, and
//! quadratic u-invariant `2`. In characteristic two, the u-invariant uses
//! regular quadratic forms (not a diagonal symmetric-bilinear proxy). For comparison,
//! formally-real ℝ has level `∞` (no finite `n`), `u(ℝ) = ∞`, Pythagoras number
//! `1`; and `u(Q_p) = 4`.
//!
//! Public entry points return `None` for unsupported field parameters.

use crate::scalar::{ExactFieldScalar, Fp, Fpn};
use std::collections::BTreeSet;
use std::fmt;

/// The scalar metadata needed by the numeric finite-field invariants.
///
/// This deliberately lives in the forms pillar rather than widening
/// [`crate::scalar::FiniteField`]: prime fields and extension fields both need
/// the report, while the scalar analysis trait has a different Galois-oriented
/// contract.
pub trait FiniteFieldInvariantField: ExactFieldScalar + Copy {
    /// Characteristic prime.
    fn characteristic_prime() -> u128;

    /// Absolute degree over the prime field.
    fn absolute_degree() -> usize;

    /// Field order, or `None` when the parameters are unsupported.
    fn field_order_checked() -> Option<u128>;
}

impl<const P: u128> FiniteFieldInvariantField for Fp<P> {
    fn characteristic_prime() -> u128 {
        P
    }

    fn absolute_degree() -> usize {
        1
    }

    fn field_order_checked() -> Option<u128> {
        Fp::<P>::modulus_is_prime().then_some(P)
    }
}

impl<const P: u128, const N: usize> FiniteFieldInvariantField for Fpn<P, N> {
    fn characteristic_prime() -> u128 {
        P
    }

    fn absolute_degree() -> usize {
        N
    }

    fn field_order_checked() -> Option<u128> {
        Fpn::<P, N>::field_order_checked()
    }
}

/// Numeric invariants of a supported finite field.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FiniteFieldNumericInvariants {
    /// Characteristic prime `p`.
    pub characteristic: u128,
    /// Absolute degree `n` in `F_{p^n}`.
    pub absolute_degree: usize,
    /// Field order `q = p^n`.
    pub field_order: u128,
    /// Level `s(F_q)`, the least number of squares summing to `-1`.
    pub level: usize,
    /// Pythagoras number `p(F_q)`.
    pub pythagoras_number: usize,
    /// Quadratic u-invariant. In characteristic two this means regular
    /// quadratic forms.
    pub u_invariant: usize,
}

impl FiniteFieldNumericInvariants {
    /// Returns the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for FiniteFieldNumericInvariants {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FiniteFieldNumericInvariants(characteristic={}, absolute_degree={}, field_order={}, level={}, pythagoras_number={}, u_invariant={})",
            self.characteristic,
            self.absolute_degree,
            self.field_order,
            self.level,
            self.pythagoras_number,
            self.u_invariant,
        )
    }
}

/// Level, Pythagoras number, and quadratic u-invariant of a supported finite
/// field.
///
/// For odd `q`, the level is `1` exactly when `q = 1 (mod 4)` and otherwise
/// `2`; the Pythagoras number and u-invariant are both `2`. For even `q`, every
/// element is a square, so the first two invariants are `1`, while the regular
/// quadratic u-invariant is `2`.
pub fn finite_field_numeric_invariants<F: FiniteFieldInvariantField>(
) -> Option<FiniteFieldNumericInvariants> {
    let characteristic = F::characteristic_prime();
    let absolute_degree = F::absolute_degree();
    let field_order = F::field_order_checked()?;
    let even = characteristic == 2;
    Some(FiniteFieldNumericInvariants {
        characteristic,
        absolute_degree,
        field_order,
        level: if even || field_order % 4 == 1 { 1 } else { 2 },
        pythagoras_number: if even { 1 } else { 2 },
        u_invariant: 2,
    })
}

/// The level of a supported finite field.
pub fn level_finite<F: FiniteFieldInvariantField>() -> Option<usize> {
    finite_field_numeric_invariants::<F>().map(|report| report.level)
}

/// The Pythagoras number of a supported finite field.
pub fn pythagoras_number_finite<F: FiniteFieldInvariantField>() -> Option<usize> {
    finite_field_numeric_invariants::<F>().map(|report| report.pythagoras_number)
}

/// The quadratic u-invariant of a supported finite field. In characteristic
/// two this means regular quadratic forms.
pub fn u_invariant_finite<F: FiniteFieldInvariantField>() -> Option<usize> {
    finite_field_numeric_invariants::<F>().map(|report| report.u_invariant)
}

/// The squares of `F_P` (as residues in `[0, P)`).
fn squares_mod<const P: u128>() -> Vec<u128> {
    (0..P).map(|x| (x * x) % P).collect()
}

/// The set of elements of `F_P` that are sums of exactly `n` squares
/// (`n = 0` is `{0}`).
fn sums_of_n_squares<const P: u128>(n: usize) -> BTreeSet<u128> {
    if n == 0 {
        return BTreeSet::from([0]);
    }
    let squares = squares_mod::<P>();
    let mut cur: BTreeSet<u128> = squares.iter().copied().collect();
    for _ in 1..n {
        let mut next = BTreeSet::new();
        for &a in &cur {
            for &s in &squares {
                next.insert((a + s) % P);
            }
        }
        cur = next;
    }
    cur
}

/// Is `x` a sum of exactly `n` squares in `F_P`?
pub fn is_sum_of_n_squares<const P: u128>(x: Fp<P>, n: usize) -> bool {
    sums_of_n_squares::<P>(n).contains(&(x.value() % P))
}

/// The **level (Stufe)** `s(F_P)`: the least `n` with `−1` a sum of `n` squares,
/// or `None` if `P` is not prime. A finite field has level `1` (iff `−1` is a
/// square: char 2, or `p ≡ 1 mod 4`) or `2`. (ℝ has level `∞` — no finite `n`.)
pub fn level<const P: u128>() -> Option<usize> {
    level_finite::<Fp<P>>()
}

/// The **Pythagoras number** `p(F_P)`: the least `n` such that every sum of
/// squares is already a sum of `n` squares (the sum-of-squares set stabilizes).
/// `None` if `P` is not prime. `≤ 2` for finite fields.
pub fn pythagoras_number<const P: u128>() -> Option<usize> {
    pythagoras_number_finite::<Fp<P>>()
}

/// Whether some `code`-indexed nonzero vector isotropes the diagonal form `qs`
/// over `F_P` (brute force over `F_P^dim`).
#[cfg(test)]
fn is_anisotropic<const P: u128>(qs: &[u128]) -> bool {
    let dim = qs.len();
    let mut total = 1u128;
    for _ in 0..dim {
        total *= P;
    }
    for code in 1..total {
        // skip the all-zero vector (code 0)
        let mut c = code;
        let mut s = 0u128;
        for &q in qs {
            let xi = c % P;
            c /= P;
            s = (s + q * ((xi * xi) % P)) % P;
        }
        if s == 0 {
            return false; // a nontrivial zero ⇒ isotropic
        }
    }
    true
}

/// Does some diagonal form of dimension `dim` with entries in `F_P*` stay
/// anisotropic?
#[cfg(test)]
fn exists_anisotropic_form<const P: u128>(dim: usize) -> bool {
    let mut total = 1u128;
    for _ in 0..dim {
        total *= P - 1;
    }
    for code in 0..total {
        let mut c = code;
        let mut qs = Vec::with_capacity(dim);
        for _ in 0..dim {
            qs.push(1 + c % (P - 1)); // an entry in [1, P-1] = F_P*
            c /= P - 1;
        }
        if is_anisotropic::<P>(&qs) {
            return true;
        }
    }
    false
}

/// The **u-invariant** `u(F_P)`: the largest dimension of an anisotropic form.
/// `Some(2)` for every prime field, using regular quadratic forms in
/// characteristic two. Returns `None` for non-prime `P`. For comparison
/// `u(ℝ) = ∞`, `u(Q_p) = 4`.
pub fn u_invariant<const P: u128>() -> Option<usize> {
    u_invariant_finite::<Fp<P>>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn level_of_finite_fields() {
        // level 1 ⇔ −1 is a square (char 2, or p ≡ 1 mod 4); else level 2.
        assert_eq!(level::<2>(), Some(1)); // char 2: −1 = 1 is a square
        assert_eq!(level::<3>(), Some(2)); // 3 ≡ 3 mod 4
        assert_eq!(level::<5>(), Some(1)); // 5 ≡ 1 mod 4, −1 = 4 = 2²
        assert_eq!(level::<7>(), Some(2)); // 7 ≡ 3 mod 4
        assert_eq!(level::<13>(), Some(1)); // 13 ≡ 1 mod 4
        assert_eq!(level::<9>(), None); // not prime
    }

    #[test]
    fn pythagoras_number_of_finite_fields() {
        assert_eq!(pythagoras_number::<2>(), Some(1)); // every element a square
        assert_eq!(pythagoras_number::<3>(), Some(2));
        assert_eq!(pythagoras_number::<5>(), Some(2));
        assert_eq!(pythagoras_number::<7>(), Some(2));
    }

    #[test]
    fn u_invariant_of_finite_fields_is_two() {
        assert_eq!(u_invariant::<3>(), Some(2));
        assert_eq!(u_invariant::<5>(), Some(2));
        assert_eq!(u_invariant::<7>(), Some(2));
        assert_eq!(u_invariant::<2>(), Some(2));
    }

    #[test]
    fn sum_of_squares_spot_checks() {
        assert!(is_sum_of_n_squares::<3>(Fp::<3>::from_u128(2), 2)); // 2 = 1 + 1
        assert!(!is_sum_of_n_squares::<3>(Fp::<3>::from_u128(2), 1)); // 2 is not a square mod 3
        assert!(is_sum_of_n_squares::<5>(Fp::<5>::from_u128(4), 1)); // 4 = 2²
    }

    #[test]
    fn extension_field_reports_use_field_order_not_characteristic_alone() {
        let f4 = finite_field_numeric_invariants::<Fpn<2, 2>>().unwrap();
        assert_eq!((f4.level, f4.pythagoras_number, f4.u_invariant), (1, 1, 2));
        assert_eq!((f4.absolute_degree, f4.field_order), (2, 4));

        let f9 = finite_field_numeric_invariants::<Fpn<3, 2>>().unwrap();
        assert_eq!((f9.level, f9.pythagoras_number, f9.u_invariant), (1, 2, 2));
        let f27 = finite_field_numeric_invariants::<Fpn<3, 3>>().unwrap();
        assert_eq!(
            (f27.level, f27.pythagoras_number, f27.u_invariant),
            (2, 2, 2)
        );
    }

    #[test]
    fn degree_one_extension_and_prime_reports_agree() {
        assert_eq!(
            finite_field_numeric_invariants::<Fp<5>>(),
            finite_field_numeric_invariants::<Fpn<5, 1>>()
        );
    }

    #[test]
    fn formula_reports_agree_with_small_prime_field_searches() {
        for (p, expected_level, expected_pythagoras) in [(2, 1, 1), (3, 2, 2), (5, 1, 2), (7, 2, 2)]
        {
            let searched_level = (1..=4)
                .find(|&n| match p {
                    2 => sums_of_n_squares::<2>(n).contains(&1),
                    3 => sums_of_n_squares::<3>(n).contains(&2),
                    5 => sums_of_n_squares::<5>(n).contains(&4),
                    7 => sums_of_n_squares::<7>(n).contains(&6),
                    _ => unreachable!(),
                })
                .unwrap();
            assert_eq!(searched_level, expected_level);
            assert_eq!(level_runtime_for_test(p), Some(expected_level));
            assert_eq!(pythagoras_runtime_for_test(p), Some(expected_pythagoras));
        }
        assert!(exists_anisotropic_form::<3>(2));
        assert!(!exists_anisotropic_form::<3>(3));
    }

    fn level_runtime_for_test(p: u128) -> Option<usize> {
        match p {
            2 => level::<2>(),
            3 => level::<3>(),
            5 => level::<5>(),
            7 => level::<7>(),
            _ => None,
        }
    }

    fn pythagoras_runtime_for_test(p: u128) -> Option<usize> {
        match p {
            2 => searched_pythagoras::<2>(),
            3 => searched_pythagoras::<3>(),
            5 => searched_pythagoras::<5>(),
            7 => searched_pythagoras::<7>(),
            _ => None,
        }
    }

    fn searched_pythagoras<const P: u128>() -> Option<usize> {
        if !Fp::<P>::modulus_is_prime() {
            return None;
        }
        let mut previous = sums_of_n_squares::<P>(1);
        for n in 1..=(P as usize + 1) {
            let next = sums_of_n_squares::<P>(n + 1);
            if next == previous {
                return Some(n);
            }
            previous = next;
        }
        None
    }

    #[test]
    fn unsupported_field_parameters_return_none() {
        assert_eq!(finite_field_numeric_invariants::<Fp<9>>(), None);
        assert_eq!(finite_field_numeric_invariants::<Fpn<9, 2>>(), None);
        assert_eq!(finite_field_numeric_invariants::<Fpn<3, 0>>(), None);
    }

    #[test]
    fn numeric_report_has_canonical_display() {
        let report = finite_field_numeric_invariants::<Fpn<3, 2>>().unwrap();
        assert_eq!(
            report.to_string(),
            "FiniteFieldNumericInvariants(characteristic=3, absolute_degree=2, field_order=9, level=1, pythagoras_number=2, u_invariant=2)"
        );
        assert_eq!(report.display(), report.to_string());
    }
}
