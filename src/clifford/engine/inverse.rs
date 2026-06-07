use super::algebra::CliffordAlgebra;
use super::multivector::Multivector;
use crate::linalg::field;
use crate::scalar::Scalar;
use std::collections::BTreeMap;

impl<S: Scalar> CliffordAlgebra<S> {
    /// The **general multivector inverse** `v⁻¹` (two-sided), for any element.
    pub fn multivector_inverse(&self, v: &Multivector<S>) -> Option<Multivector<S>> {
        if v.is_zero() {
            return None;
        }
        let n = 1usize << self.dim;
        let mut mat = vec![vec![S::zero(); n]; n];
        for col in 0..n {
            let mut t = BTreeMap::new();
            t.insert(col as u128, S::one());
            let prod = self.mul(v, &Multivector { terms: t });
            for (&blade, c) in &prod.terms {
                mat[blade as usize][col] = c.clone();
            }
        }
        let mut rhs = vec![S::zero(); n];
        rhs[0] = S::one();
        let x = field::solve(mat, rhs)?;
        let mut terms = BTreeMap::new();
        for (bm, c) in x.into_iter().enumerate() {
            if !c.is_zero() {
                terms.insert(bm as u128, c);
            }
        }
        Some(Multivector { terms })
    }
}
