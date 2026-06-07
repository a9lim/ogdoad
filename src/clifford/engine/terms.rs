use crate::scalar::Scalar;
use std::collections::BTreeMap;

pub(super) fn scale<S: Scalar>(mut terms: BTreeMap<u128, S>, s: &S) -> BTreeMap<u128, S> {
    if s.is_zero() {
        return BTreeMap::new();
    }
    for v in terms.values_mut() {
        *v = v.mul(s);
    }
    terms.retain(|_, v| !v.is_zero());
    terms
}

pub(super) fn merge<S: Scalar>(into: &mut BTreeMap<u128, S>, other: BTreeMap<u128, S>) {
    for (blade, coeff) in other {
        let e = into.entry(blade).or_insert_with(S::zero);
        *e = e.add(&coeff);
        if e.is_zero() {
            into.remove(&blade);
        }
    }
}
