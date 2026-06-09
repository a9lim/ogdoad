//! Exact scalar modular forms for the full modular group.
//!
//! This tiny layer is deliberately q-expansion based. The identities used by
//! the lattice tests are exact finite-dimensional statements in
//! `M_*(SL_2(Z)) = C[E4,E6]`; no floating point or numerical fitting is involved.

use crate::linalg::field::inverse_matrix;
use crate::scalar::{Rational, Scalar};

fn sigma_power(n: usize, power: u32) -> i128 {
    let mut out = 0i128;
    for d in 1..=n {
        if n.is_multiple_of(d) {
            out = out
                .checked_add((d as i128).pow(power))
                .expect("divisor-power sum exceeds i128");
        }
    }
    out
}

fn qexp_add(a: &[Rational], b: &[Rational], terms: usize) -> Vec<Rational> {
    (0..terms)
        .map(|i| a[i].add(&b[i]))
        .collect::<Vec<Rational>>()
}

fn qexp_sub(a: &[Rational], b: &[Rational], terms: usize) -> Vec<Rational> {
    (0..terms)
        .map(|i| a[i].sub(&b[i]))
        .collect::<Vec<Rational>>()
}

fn qexp_scale(a: &[Rational], c: Rational, terms: usize) -> Vec<Rational> {
    (0..terms).map(|i| a[i].mul(&c)).collect()
}

fn qexp_mul(a: &[Rational], b: &[Rational], terms: usize) -> Vec<Rational> {
    let mut out = vec![Rational::zero(); terms];
    for (i, ai) in a.iter().enumerate().take(terms) {
        if ai.is_zero() {
            continue;
        }
        for (j, bj) in b.iter().enumerate().take(terms - i) {
            if bj.is_zero() {
                continue;
            }
            out[i + j] = out[i + j].add(&ai.mul(bj));
        }
    }
    out
}

fn qexp_pow(base: &[Rational], exp: usize, terms: usize) -> Vec<Rational> {
    let mut out = vec![Rational::zero(); terms];
    if terms == 0 {
        return out;
    }
    out[0] = Rational::one();
    for _ in 0..exp {
        out = qexp_mul(&out, base, terms);
    }
    out
}

/// Convert exact integer q-expansion coefficients to rational coefficients.
pub fn qexp_from_i128(coeffs: &[i128]) -> Vec<Rational> {
    coeffs.iter().map(|&x| Rational::int(x)).collect()
}

/// `E4 = 1 + 240 * sum sigma_3(n) q^n`.
pub fn eisenstein_e4(terms: usize) -> Vec<Rational> {
    let mut out = vec![Rational::zero(); terms];
    if terms == 0 {
        return out;
    }
    out[0] = Rational::one();
    for (n, coeff) in out.iter_mut().enumerate().skip(1) {
        *coeff = Rational::int(
            240i128
                .checked_mul(sigma_power(n, 3))
                .expect("E4 coefficient exceeds i128"),
        );
    }
    out
}

/// `E6 = 1 - 504 * sum sigma_5(n) q^n`.
pub fn eisenstein_e6(terms: usize) -> Vec<Rational> {
    let mut out = vec![Rational::zero(); terms];
    if terms == 0 {
        return out;
    }
    out[0] = Rational::one();
    for (n, coeff) in out.iter_mut().enumerate().skip(1) {
        *coeff = Rational::int(
            -504i128
                .checked_mul(sigma_power(n, 5))
                .expect("E6 coefficient exceeds i128"),
        );
    }
    out
}

/// The cusp form `Delta = (E4^3 - E6^2) / 1728`.
pub fn delta(terms: usize) -> Vec<Rational> {
    let e4 = eisenstein_e4(terms);
    let e6 = eisenstein_e6(terms);
    let e4_3 = qexp_pow(&e4, 3, terms);
    let e6_2 = qexp_pow(&e6, 2, terms);
    qexp_scale(
        &qexp_sub(&e4_3, &e6_2, terms),
        Rational::new(1, 1728),
        terms,
    )
}

/// The monomial basis `{E4^a E6^b : 4a + 6b = weight}`.
pub fn mk_basis(weight: usize, terms: usize) -> Vec<Vec<Rational>> {
    if terms == 0 {
        return Vec::new();
    }
    if weight == 0 {
        let mut one = vec![Rational::zero(); terms];
        one[0] = Rational::one();
        return vec![one];
    }
    let e4 = eisenstein_e4(terms);
    let e6 = eisenstein_e6(terms);
    let mut basis = Vec::new();
    for b in 0..=weight / 6 {
        let rem = weight - 6 * b;
        if rem.is_multiple_of(4) {
            let a = rem / 4;
            let e4a = qexp_pow(&e4, a, terms);
            let e6b = qexp_pow(&e6, b, terms);
            basis.push(qexp_mul(&e4a, &e6b, terms));
        }
    }
    basis
}

/// Identify a q-expansion as a modular form of the given weight in the
/// `E4`/`E6` basis. The first `dim M_k` coefficients solve for the coordinates;
/// all supplied coefficients through `terms` are then checked exactly.
pub fn as_modular_form(
    q_expansion: &[Rational],
    weight: usize,
    terms: usize,
) -> Option<Vec<Rational>> {
    if q_expansion.len() < terms {
        return None;
    }
    let basis = mk_basis(weight, terms);
    let dim = basis.len();
    if dim == 0 {
        return (0..terms).all(|i| q_expansion[i].is_zero()).then(Vec::new);
    }
    if terms < dim {
        return None;
    }
    let mut matrix = vec![vec![Rational::zero(); dim]; dim];
    for row in 0..dim {
        for col in 0..dim {
            matrix[row][col] = basis[col][row].clone();
        }
    }
    let inv = inverse_matrix(matrix)?;
    let mut coords = vec![Rational::zero(); dim];
    for row in 0..dim {
        for col in 0..dim {
            coords[row] = coords[row].add(&inv[row][col].mul(&q_expansion[col]));
        }
    }
    for i in 0..terms {
        let mut got = Rational::zero();
        for (coord, b) in coords.iter().zip(&basis) {
            got = got.add(&coord.mul(&b[i]));
        }
        if got != q_expansion[i] {
            return None;
        }
    }
    Some(coords)
}

/// Exact q-expansion addition, exported for tests and small formula checks.
pub fn modular_qexp_add(a: &[Rational], b: &[Rational], terms: usize) -> Vec<Rational> {
    qexp_add(a, b, terms)
}

/// Exact q-expansion subtraction, exported for tests and small formula checks.
pub fn modular_qexp_sub(a: &[Rational], b: &[Rational], terms: usize) -> Vec<Rational> {
    qexp_sub(a, b, terms)
}

/// Exact q-expansion multiplication, exported for tests and small formula checks.
pub fn modular_qexp_mul(a: &[Rational], b: &[Rational], terms: usize) -> Vec<Rational> {
    qexp_mul(a, b, terms)
}

/// Exact scalar multiplication of a q-expansion.
pub fn modular_qexp_scale(a: &[Rational], c: Rational, terms: usize) -> Vec<Rational> {
    qexp_scale(a, c, terms)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eisenstein_series_start_with_standard_coefficients() {
        assert_eq!(
            eisenstein_e4(5),
            qexp_from_i128(&[1, 240, 2160, 6720, 17520])
        );
        assert_eq!(
            eisenstein_e6(4),
            qexp_from_i128(&[1, -504, -16632, -122976])
        );
        assert_eq!(delta(4), qexp_from_i128(&[0, 1, -24, 252]));
    }

    #[test]
    fn modular_identification_solves_exact_coordinates() {
        let e4 = eisenstein_e4(5);
        assert_eq!(as_modular_form(&e4, 4, 5), Some(vec![Rational::one()]));

        let e4_squared = modular_qexp_mul(&e4, &e4, 5);
        assert_eq!(
            as_modular_form(&e4_squared, 8, 5),
            Some(vec![Rational::one()])
        );

        let e4_cubed = modular_qexp_mul(&e4_squared, &e4, 3);
        let leech_form = modular_qexp_sub(
            &e4_cubed,
            &modular_qexp_scale(&delta(3), Rational::int(720), 3),
            3,
        );
        assert_eq!(
            as_modular_form(&leech_form, 12, 3),
            Some(vec![Rational::new(7, 12), Rational::new(5, 12)])
        );
    }
}
