//! Characteristic-2 finite-field row kernels.

use crate::scalar::{nim_add, nim_inv, nim_mul};

/// Rank of a matrix over the nim-field `F_{2^128}`, stored as raw `u128`
/// nimbers.
pub(crate) fn nim_rank(mut rows: Vec<Vec<u128>>) -> usize {
    let nrows = rows.len();
    if nrows == 0 {
        return 0;
    }
    let ncols = rows[0].len();
    let mut pr = 0usize;
    for col in 0..ncols {
        let Some(p) = (pr..nrows).find(|&r| rows[r][col] != 0) else {
            continue;
        };
        rows.swap(pr, p);
        let inv = nim_inv(rows[pr][col]).expect("nonzero nimber is invertible");
        for c in col..ncols {
            rows[pr][c] = nim_mul(rows[pr][c], inv);
        }
        for r in 0..nrows {
            if r != pr && rows[r][col] != 0 {
                let f = rows[r][col];
                for c in col..ncols {
                    rows[r][c] = nim_add(rows[r][c], nim_mul(f, rows[pr][c]));
                }
            }
        }
        pr += 1;
        if pr == nrows {
            break;
        }
    }
    pr
}
