//! Unit-pivot linear algebra over `Scalar` backends.
//!
//! A `Scalar` may be a field, a local ring, or a precision model. These kernels
//! therefore pivot only on entries whose [`Scalar::inv`] exists. Over a field this
//! is ordinary Gauss-Jordan elimination; over a ring these routines return
//! `None` when a required nonunit pivot appears.

use crate::scalar::Scalar;

/// Rank of a row-major matrix by unit-pivot elimination.
///
/// Returns `None` when a nonzero residual matrix remains after all available
/// unit pivots have been exhausted. Over a field this is ordinary matrix rank;
/// over a ring it succeeds only when unit pivots suffice.
pub(crate) fn unit_pivot_rank<S: Scalar>(mut m: Vec<Vec<S>>) -> Option<usize> {
    let nrows = m.len();
    let ncols = m.first().map_or(0, Vec::len);
    if m.iter().any(|row| row.len() != ncols) {
        return None;
    }

    let mut row = 0;
    for col in 0..ncols {
        let Some((piv, pinv)) = (row..nrows).find_map(|r| m[r][col].inv().map(|pinv| (r, pinv)))
        else {
            continue;
        };
        m.swap(row, piv);
        for c in 0..ncols {
            m[row][c] = m[row][c].mul(&pinv);
        }
        for r in 0..nrows {
            if r == row {
                continue;
            }
            let factor = m[r][col].clone();
            if factor.is_zero() {
                continue;
            }
            for c in 0..ncols {
                m[r][c] = m[r][c].sub(&factor.mul(&m[row][c]));
            }
        }
        row += 1;
        if row == nrows {
            break;
        }
    }
    if (row..nrows).any(|r| (0..ncols).any(|c| !m[r][c].is_zero())) {
        return None;
    }
    Some(row)
}

/// Solve the square system `A x = b` by unit-pivot Gauss--Jordan elimination.
///
/// Returns `None` if some pivot column has no invertible entry. Panics if `A`
/// is not square with the same number of rows as `b`.
pub(crate) fn solve<S: Scalar>(mut a: Vec<Vec<S>>, mut b: Vec<S>) -> Option<Vec<S>> {
    let n = b.len();
    // Always-on, not debug-only (matches `linalg/integer.rs`): the O(n) shape
    // check is dwarfed by the O(n^3) elimination below at every call site, so
    // gating it on `debug_assertions` buys no real performance and costs a
    // release-build safety check.
    assert_eq!(a.len(), n, "solve expects a square matrix");
    for row in &a {
        assert_eq!(row.len(), n, "solve expects a square matrix");
    }
    for col in 0..n {
        let (piv, inv) = (col..n).find_map(|r| a[r][col].inv().map(|inv| (r, inv)))?;
        a.swap(col, piv);
        b.swap(col, piv);
        for k in col..n {
            a[col][k] = a[col][k].mul(&inv);
        }
        b[col] = b[col].mul(&inv);
        for r in 0..n {
            if r == col {
                continue;
            }
            let f = a[r][col].clone();
            if f.is_zero() {
                continue;
            }
            for k in col..n {
                a[r][k] = a[r][k].sub(&f.mul(&a[col][k]));
            }
            b[r] = b[r].sub(&f.mul(&b[col]));
        }
    }
    Some(b)
}

/// Invert a square row-major matrix by unit-pivot Gauss--Jordan elimination.
///
/// Returns `None` if some pivot column has no invertible entry. Panics if the
/// matrix is not square.
pub(crate) fn inverse_matrix<S: Scalar>(mut m: Vec<Vec<S>>) -> Option<Vec<Vec<S>>> {
    let n = m.len();
    // Always-on; see the same-cost note in `solve` above.
    for row in &m {
        assert_eq!(row.len(), n, "inverse_matrix expects a square matrix");
    }
    let mut inv: Vec<Vec<S>> = (0..n)
        .map(|r| {
            (0..n)
                .map(|c| if r == c { S::one() } else { S::zero() })
                .collect()
        })
        .collect();
    for col in 0..n {
        let (piv, pinv) = (col..n).find_map(|r| m[r][col].inv().map(|pinv| (r, pinv)))?;
        m.swap(col, piv);
        inv.swap(col, piv);
        for c in 0..n {
            m[col][c] = m[col][c].mul(&pinv);
            inv[col][c] = inv[col][c].mul(&pinv);
        }
        for r in 0..n {
            if r == col {
                continue;
            }
            let factor = m[r][col].clone();
            if factor.is_zero() {
                continue;
            }
            for c in 0..n {
                m[r][c] = m[r][c].sub(&factor.mul(&m[col][c]));
                inv[r][c] = inv[r][c].sub(&factor.mul(&inv[col][c]));
            }
        }
    }
    Some(inv)
}

/// A basis of the right nullspace `{x : Mx = 0}` of a row-major matrix with
/// `ncols` columns.
///
/// Columns without an available unit pivot remain free while elimination
/// continues through later columns. Returns `None` if a nonzero residual row
/// remains after all unit pivots are exhausted. Over a field this is ordinary
/// nullspace elimination; over a ring it succeeds only when unit pivots suffice.
pub(crate) fn unit_pivot_nullspace<S: Scalar>(
    mut m: Vec<Vec<S>>,
    ncols: usize,
) -> Option<Vec<Vec<S>>> {
    let nrows = m.len();
    let mut pivot_cols: Vec<usize> = Vec::new();
    let mut row = 0;
    for col in 0..ncols {
        let Some((piv, pinv)) = (row..nrows).find_map(|r| m[r][col].inv().map(|pinv| (r, pinv)))
        else {
            // No unit pivot here yet; leave the column alone and let a later
            // column try. Whether that was actually safe is checked once,
            // after the loop, against the leftover (never-pivoted) rows.
            continue;
        };
        m.swap(row, piv);
        for c in 0..ncols {
            m[row][c] = m[row][c].mul(&pinv);
        }
        for r in 0..nrows {
            if r == row {
                continue;
            }
            let f = m[r][col].clone();
            if f.is_zero() {
                continue;
            }
            for c in 0..ncols {
                let sub = f.mul(&m[row][c]);
                m[r][c] = m[r][c].sub(&sub);
            }
        }
        pivot_cols.push(col);
        row += 1;
        if row == nrows {
            break;
        }
    }
    if (row..nrows).any(|r| (0..ncols).any(|c| !m[r][c].is_zero())) {
        return None;
    }
    let mut basis = Vec::new();
    for fc in (0..ncols).filter(|c| !pivot_cols.contains(c)) {
        let mut x = vec![S::zero(); ncols];
        x[fc] = S::one();
        for (ri, &pc) in pivot_cols.iter().enumerate() {
            x[pc] = m[ri][fc].neg();
        }
        basis.push(x);
    }
    Some(basis)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{Integer, Rational};

    fn r(n: i128) -> Rational {
        Rational::from_int(n)
    }

    #[test]
    fn nullspace_over_fields_still_finds_free_columns() {
        let basis = unit_pivot_nullspace(vec![vec![r(1), r(2), r(3)]], 3).unwrap();
        assert_eq!(
            basis,
            vec![vec![r(-2), r(1), r(0)], vec![r(-3), r(0), r(1)]]
        );
    }

    #[test]
    fn rank_handles_rectangular_field_matrices() {
        assert_eq!(
            unit_pivot_rank(vec![vec![r(1), r(2), r(3)], vec![r(2), r(4), r(6)]]),
            Some(1)
        );
        assert_eq!(unit_pivot_rank::<Rational>(vec![]), Some(0));
        assert_eq!(unit_pivot_rank(vec![vec![r(1)], vec![r(0), r(1)]]), None);
    }

    #[test]
    fn nullspace_returns_none_on_required_nonunit_pivot() {
        let m = vec![vec![Integer(0), Integer(2), Integer(-2)]];
        assert!(unit_pivot_nullspace(m, 3).is_none());
    }

    // Column 0 has no unit pivot (2 is not a unit in `Integer`), but skipping
    // it and pivoting on column 1's unit `1`
    // finds the kernel without ever dividing by the nonunit.
    #[test]
    fn nullspace_skips_a_nonunit_column_when_a_later_column_pivots() {
        let m = vec![vec![Integer(2), Integer(1)]];
        let basis = unit_pivot_nullspace(m, 2).unwrap();
        assert_eq!(basis, vec![vec![Integer(1), Integer(-2)]]);
    }

    fn dot<S: Scalar>(row: &[S], x: &[S]) -> S {
        row.iter()
            .zip(x)
            .fold(S::zero(), |acc, (a, b)| acc.add(&a.mul(b)))
    }

    // A two-row regression for the same bug: column 0 is skipped (4 and 6 are
    // both nonunits in `Integer`), and clearing it correctly depends on later
    // pivots sweeping the *whole* row, not just columns from the pivot
    // onward — an elimination that only updated columns >= the pivot column
    // would leave column 0 stale in row 1 and hand back a vector that isn't
    // actually in the kernel. Multiplying the returned basis through the
    // source matrix is the check that would have caught that.
    #[test]
    fn nullspace_basis_vectors_are_verified_against_the_source_matrix() {
        let m = vec![
            vec![Integer(4), Integer(1), Integer(0)],
            vec![Integer(6), Integer(1), Integer(1)],
        ];
        let basis = unit_pivot_nullspace(m.clone(), 3).unwrap();
        assert!(!basis.is_empty());
        for x in &basis {
            for row in &m {
                assert!(
                    dot(row, x).is_zero(),
                    "basis vector {x:?} is not in the kernel of row {row:?}"
                );
            }
        }
    }

    #[test]
    fn solve_round_trip_recovers_the_solution() {
        let a = vec![vec![r(2), r(1)], vec![r(1), r(3)]];
        let b = vec![r(5), r(10)];
        let x = solve(a.clone(), b.clone()).unwrap();
        for (row, bi) in a.iter().zip(&b) {
            assert_eq!(&dot(row, &x), bi);
        }
    }

    #[test]
    fn solve_returns_none_for_a_singular_matrix() {
        let a = vec![vec![r(1), r(2)], vec![r(2), r(4)]];
        let b = vec![r(1), r(2)];
        assert!(solve(a, b).is_none());
    }

    #[test]
    fn inverse_matrix_round_trip_recovers_the_identity() {
        let m = vec![vec![r(2), r(1)], vec![r(1), r(3)]];
        let inv = inverse_matrix(m.clone()).unwrap();
        for i in 0..m.len() {
            for j in 0..m.len() {
                let entry = (0..m.len()).fold(r(0), |acc, k| acc.add(&m[i][k].mul(&inv[k][j])));
                assert_eq!(entry, if i == j { r(1) } else { r(0) });
            }
        }
    }

    #[test]
    fn inverse_matrix_returns_none_for_a_singular_matrix() {
        let m = vec![vec![r(1), r(2)], vec![r(2), r(4)]];
        assert!(inverse_matrix(m).is_none());
    }
}
