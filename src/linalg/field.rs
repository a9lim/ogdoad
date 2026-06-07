//! Unit-pivot linear algebra over `Scalar` backends.
//!
//! A `Scalar` may be a field, a local ring, or a precision model. These kernels
//! therefore pivot only on entries whose [`Scalar::inv`] exists. Over a field this
//! is ordinary Gauss-Jordan elimination; over a ring it gives the unit-visible
//! part and returns `None` when a required nonunit pivot appears.

use crate::scalar::Scalar;

/// Solve `A x = b` by Gauss-Jordan elimination.
pub(crate) fn solve<S: Scalar>(mut a: Vec<Vec<S>>, mut b: Vec<S>) -> Option<Vec<S>> {
    let n = b.len();
    debug_assert_eq!(a.len(), n, "solve expects a square matrix");
    for row in &a {
        debug_assert_eq!(row.len(), n, "solve expects a square matrix");
    }
    for col in 0..n {
        let piv = (col..n).find(|&r| a[r][col].inv().is_some())?;
        a.swap(col, piv);
        b.swap(col, piv);
        let inv = a[col][col].inv().expect("pivot was checked invertible");
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

/// Invert a square row-major matrix by Gauss-Jordan elimination.
pub(crate) fn inverse_matrix<S: Scalar>(mut m: Vec<Vec<S>>) -> Option<Vec<Vec<S>>> {
    let n = m.len();
    for row in &m {
        debug_assert_eq!(row.len(), n, "inverse_matrix expects a square matrix");
    }
    let mut inv: Vec<Vec<S>> = (0..n)
        .map(|r| {
            (0..n)
                .map(|c| if r == c { S::one() } else { S::zero() })
                .collect()
        })
        .collect();
    for col in 0..n {
        let piv = (col..n).find(|&r| m[r][col].inv().is_some())?;
        m.swap(col, piv);
        inv.swap(col, piv);
        let pinv = m[col][col].inv()?;
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

/// A basis of the right nullspace `{ x : M x = 0 }` of a row-major matrix with
/// `ncols` columns.
pub(crate) fn unit_pivot_nullspace<S: Scalar>(mut m: Vec<Vec<S>>, ncols: usize) -> Vec<Vec<S>> {
    let nrows = m.len();
    let mut pivot_cols: Vec<usize> = Vec::new();
    let mut row = 0;
    for col in 0..ncols {
        let Some(piv) = (row..nrows).find(|&r| m[r][col].inv().is_some()) else {
            continue;
        };
        m.swap(row, piv);
        let pinv = m[row][col].inv().expect("pivot is invertible");
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
    let mut basis = Vec::new();
    for fc in (0..ncols).filter(|c| !pivot_cols.contains(c)) {
        let mut x = vec![S::zero(); ncols];
        x[fc] = S::one();
        for (ri, &pc) in pivot_cols.iter().enumerate() {
            x[pc] = m[ri][fc].neg();
        }
        basis.push(x);
    }
    basis
}
