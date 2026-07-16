//! Shared exact diagonalization routines for integral Gram matrices, plus the
//! p-adic valuation / unit-residue primitives the genus, fqm_witt, and
//! discriminant-form engines all need over exact `Rational` arithmetic.

use crate::scalar::{Rational, Scalar};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DegenerateBehavior {
    /// Stop when the remaining active block is the radical.
    StopAtRadical,
    /// Treat a radical as an internal invariant violation.
    RequireNonsingular,
}

/// Exact rational division `a / b`, shared by every exact-rational reduction in
/// the integral layer (congruence diagonalization, the genus Jordan splitting).
pub(crate) fn rdiv(a: &Rational, b: &Rational) -> Rational {
    a.mul(
        &b.inv()
            .expect("division by zero rational in exact lattice arithmetic"),
    )
}

// --- p-adic valuation / unit-residue helpers, shared by genus.rs, fqm_witt.rs,
// and discriminant/form.rs ---

/// The `p`-adic valuation of a nonzero `i128`.
pub(crate) fn v_p_i128(mut x: i128, p: i128) -> i128 {
    debug_assert!(x != 0);
    let mut k = 0i128;
    while x % p == 0 {
        x /= p;
        k += 1;
    }
    k
}

/// `x` with every factor of `p` divided out.
pub(crate) fn unit_part_i128(mut x: i128, p: i128) -> i128 {
    while x % p == 0 {
        x /= p;
    }
    x
}

/// The `p`-adic valuation of a nonzero rational `num/den`.
pub(crate) fn rat_val(r: &Rational, p: i128) -> i128 {
    debug_assert!(!r.is_zero());
    v_p_i128(r.numer(), p) - v_p_i128(r.denom(), p)
}

/// The `p`-adic unit residue `num*den mod p` of a nonzero rational `r`, for odd
/// `p` (`den` and `den⁻¹` share a Legendre symbol, so `num*den` stands in for
/// `num/den`). This is the raw residue; callers deciding the actual square class
/// feed it through their own local-square-class test (`try_is_square_qp`).
pub(crate) fn odd_unit_residue(r: &Rational, p: i128) -> i128 {
    let a = unit_part_i128(r.numer(), p).rem_euclid(p);
    let b = unit_part_i128(r.denom(), p).rem_euclid(p);
    (a * b).rem_euclid(p)
}

/// The 2-adic unit residue `u mod 8` of a nonzero rational `r = num/den` whose
/// 2-adic valuation is even (so `r / 2^val` is a unit). Uses `odd⁻¹ ≡ odd
/// (mod 8)`.
pub(crate) fn unit_mod8(r: &Rational) -> i128 {
    let a = unit_part_i128(r.numer(), 2).rem_euclid(8);
    let b = unit_part_i128(r.denom(), 2).rem_euclid(8);
    (a * b).rem_euclid(8)
}

/// `x mod modulus`, represented in `[0, modulus)` (`modulus > 0`).
pub(crate) fn rational_mod_int(x: Rational, modulus: i128) -> Rational {
    debug_assert!(modulus > 0);
    let den = x.denom();
    let mden = den
        .checked_mul(modulus)
        .expect("rational modulus exceeds i128");
    Rational::new(x.numer().rem_euclid(mden), den)
}

/// Diagonal entries reached by exact rational congruence diagonalization.
///
/// When every active diagonal entry is zero but an off-diagonal entry remains,
/// the basis shear `e_r <- e_r + e_s` creates a nonzero diagonal pivot. This is
/// the common Jacobi/Sylvester step used by the signature, genus, and
/// discriminant layers.
pub(crate) fn rational_congruence_diagonal(
    gram: &[Vec<i128>],
    degenerate: DegenerateBehavior,
) -> Vec<Rational> {
    let n = gram.len();
    let mut a: Vec<Vec<Rational>> = gram
        .iter()
        .map(|row| row.iter().map(|&x| Rational::from_int(x)).collect())
        .collect();
    let mut active: Vec<usize> = (0..n).collect();
    let mut out = Vec::with_capacity(n);
    while !active.is_empty() {
        if !active.iter().any(|&r| !a[r][r].is_zero()) {
            let mut pair = None;
            'find: for (ai, &r) in active.iter().enumerate() {
                for &s in &active[ai + 1..] {
                    if !a[r][s].is_zero() {
                        pair = Some((r, s));
                        break 'find;
                    }
                }
            }
            let Some((r, s)) = pair else {
                match degenerate {
                    DegenerateBehavior::StopAtRadical => break,
                    DegenerateBehavior::RequireNonsingular => {
                        panic!("nondegenerate form has a nonzero entry")
                    }
                }
            };
            for &c in &active {
                a[r][c] = a[r][c].add(&a[s][c].clone());
            }
            for &rr in &active {
                a[rr][r] = a[rr][r].add(&a[rr][s].clone());
            }
        }
        let Some(i) = active.iter().copied().find(|&r| !a[r][r].is_zero()) else {
            match degenerate {
                DegenerateBehavior::StopAtRadical => break,
                DegenerateBehavior::RequireNonsingular => panic!("a diagonal pivot now exists"),
            }
        };
        let pivot = a[i][i].clone();
        out.push(pivot.clone());
        let rest: Vec<usize> = active.iter().copied().filter(|&r| r != i).collect();
        for &r in &rest {
            for &s in &rest {
                let corr = rdiv(&a[r][i].mul(&a[i][s]), &pivot);
                a[r][s] = a[r][s].sub(&corr);
            }
        }
        active = rest;
    }
    out
}

pub(crate) fn signature_from_diagonal(diag: &[Rational]) -> (usize, usize) {
    let (mut pos, mut neg) = (0usize, 0usize);
    for d in diag {
        match d.sign() {
            std::cmp::Ordering::Greater => pos += 1,
            std::cmp::Ordering::Less => neg += 1,
            std::cmp::Ordering::Equal => {}
        }
    }
    (pos, neg)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn v_p_and_unit_part_agree_on_known_factorizations() {
        assert_eq!(v_p_i128(12, 2), 2); // 12 = 2^2 * 3
        assert_eq!(unit_part_i128(12, 2), 3);
        assert_eq!(v_p_i128(-12, 2), 2);
        assert_eq!(unit_part_i128(-12, 2), -3);
        assert_eq!(v_p_i128(27, 3), 3); // 27 = 3^3
        assert_eq!(unit_part_i128(27, 3), 1);
    }

    #[test]
    fn rat_val_is_signed_valuation_difference() {
        assert_eq!(rat_val(&Rational::new(12, 1), 2), 2);
        assert_eq!(rat_val(&Rational::new(1, 12), 2), -2);
        assert_eq!(rat_val(&Rational::new(3, 4), 2), -2);
    }

    #[test]
    fn odd_unit_residue_and_unit_mod8_match_known_units() {
        // 12/1 = 2^2 * 3: the odd unit residue mod 3 is 3 mod 3 = 0's coprime
        // slice, so check a genuinely odd-unit rational instead: 5/7 mod 3.
        assert_eq!(
            odd_unit_residue(&Rational::new(5, 7), 3),
            (5i128 * 7).rem_euclid(3)
        );
        // 3/1 has 2-adic unit part 3 (valuation 0); residue mod 8 is 3.
        assert_eq!(unit_mod8(&Rational::new(3, 1)), 3);
        // 12/1 = 2^2 * 3; unit part after stripping 2's is 3, residue mod 8 is 3.
        assert_eq!(unit_mod8(&Rational::new(12, 1)), 3);
    }

    #[test]
    fn rational_mod_int_reduces_into_the_half_open_interval() {
        assert_eq!(
            rational_mod_int(Rational::new(5, 2), 2),
            Rational::new(1, 2)
        );
        assert_eq!(
            rational_mod_int(Rational::new(-1, 2), 2),
            Rational::new(3, 2)
        );
        assert_eq!(
            rational_mod_int(Rational::new(4, 1), 2),
            Rational::new(0, 1)
        );
    }

    #[test]
    fn rdiv_recovers_exact_quotient() {
        assert_eq!(
            rdiv(&Rational::new(6, 1), &Rational::new(3, 1)),
            Rational::new(2, 1)
        );
    }
}
