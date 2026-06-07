use super::basis::bits;
use crate::scalar::Scalar;
use std::collections::BTreeMap;

/// A multivector: blade-mask → coefficient (zeros never stored).
#[derive(Clone, Debug, PartialEq)]
pub struct Multivector<S: Scalar> {
    pub terms: BTreeMap<u128, S>,
}

impl<S: Scalar> Multivector<S> {
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// Human-readable form, e.g. `3 + 2*e0 + 1*e0e1`.
    pub fn display(&self) -> String {
        if self.terms.is_empty() {
            return "0".to_string();
        }
        let one = S::one();
        let neg_one = S::one().neg();
        let mut parts = Vec::new();
        for (&blade, coeff) in &self.terms {
            if blade == 0 {
                parts.push(format!("{:?}", coeff));
                continue;
            }
            let label: String = bits(blade).iter().map(|i| format!("e{}", i)).collect();
            if *coeff == one {
                parts.push(label);
            } else if *coeff == neg_one {
                parts.push(format!("-{}", label));
            } else {
                parts.push(format!("{:?}*{}", coeff, label));
            }
        }
        parts.join(" + ")
    }
}
