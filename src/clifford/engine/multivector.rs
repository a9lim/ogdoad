use super::basis::{bits, wedge_sign};
use super::terms::merge;
use crate::scalar::Scalar;
use std::collections::BTreeMap;
use std::ops::{Add, BitXor, Neg, Sub};

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

impl<S: Scalar> Add for Multivector<S> {
    type Output = Multivector<S>;

    fn add(self, rhs: Multivector<S>) -> Multivector<S> {
        let mut terms = self.terms;
        merge(&mut terms, rhs.terms);
        Multivector { terms }
    }
}

impl<S: Scalar> Neg for Multivector<S> {
    type Output = Multivector<S>;

    fn neg(self) -> Multivector<S> {
        let terms = self
            .terms
            .into_iter()
            .map(|(blade, coeff)| (blade, coeff.neg()))
            .filter(|(_, coeff)| !coeff.is_zero())
            .collect();
        Multivector { terms }
    }
}

impl<S: Scalar> Sub for Multivector<S> {
    type Output = Multivector<S>;

    fn sub(self, mut rhs: Multivector<S>) -> Multivector<S> {
        for coeff in rhs.terms.values_mut() {
            *coeff = coeff.neg();
        }
        let mut terms = self.terms;
        merge(&mut terms, rhs.terms);
        Multivector { terms }
    }
}

impl<S: Scalar> BitXor for Multivector<S> {
    type Output = Multivector<S>;

    fn bitxor(self, rhs: Multivector<S>) -> Multivector<S> {
        let mut out: BTreeMap<u128, S> = BTreeMap::new();
        for (&ba, ca) in &self.terms {
            for (&bb, cb) in &rhs.terms {
                if ba & bb != 0 {
                    continue;
                }
                let blade = ba | bb;
                let coeff = ca.mul(cb).mul(&wedge_sign::<S>(ba, bb));
                if coeff.is_zero() {
                    continue;
                }
                let e = out.entry(blade).or_insert_with(S::zero);
                *e = e.add(&coeff);
                if e.is_zero() {
                    out.remove(&blade);
                }
            }
        }
        Multivector { terms: out }
    }
}
