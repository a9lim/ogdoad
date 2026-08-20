use super::algebra::{WeylAlgebra, WeylError};
use super::element::{add_term, WeylElement, WeylMonomial};
use crate::scalar::Scalar;
use std::collections::BTreeMap;

pub(super) fn embed_nat<S: Scalar>(value: u128) -> S {
    let mut remaining = value;
    let mut base = S::one();
    let mut output = S::zero();
    while remaining > 0 {
        if remaining & 1 == 1 {
            output = output.add(&base);
        }
        remaining >>= 1;
        if remaining > 0 {
            base = base.add(&base);
        }
    }
    output
}

pub(super) fn multiply<S: Scalar>(
    algebra: &WeylAlgebra<S>,
    left: &WeylElement<S>,
    right: &WeylElement<S>,
) -> Result<WeylElement<S>, WeylError> {
    let mut output = BTreeMap::new();
    for (left_monomial, left_coefficient) in &left.terms {
        for (right_monomial, right_coefficient) in &right.terms {
            let scalar = left_coefficient.mul(right_coefficient);
            if scalar.is_zero() {
                continue;
            }
            let product = match algebra.standard_pairs {
                Some(pairs) => standard_monomial_product(
                    pairs,
                    left_monomial.exponents(),
                    right_monomial.exponents(),
                )?,
                None => general_monomial_product(
                    algebra,
                    left_monomial.exponents(),
                    right_monomial.exponents(),
                )?,
            };
            for (monomial, coefficient) in product {
                add_term(&mut output, monomial, scalar.mul(&coefficient));
            }
        }
    }
    Ok(WeylElement {
        dim: algebra.dim(),
        terms: output,
    })
}

fn general_monomial_product<S: Scalar>(
    algebra: &WeylAlgebra<S>,
    left: &[u128],
    right: &[u128],
) -> Result<BTreeMap<WeylMonomial, S>, WeylError> {
    let mut terms = BTreeMap::from([(WeylMonomial::new(left.to_vec()), S::one())]);
    for (generator, &count) in right.iter().enumerate() {
        if count == 0 {
            continue;
        }
        let can_contract = ((generator + 1)..algebra.dim())
            .any(|higher| !algebra.commutator[higher][generator].is_zero());
        if !can_contract {
            let mut shifted = BTreeMap::new();
            for (monomial, coefficient) in terms {
                let mut exponents = monomial.exponents.into_vec();
                exponents[generator] = exponents[generator]
                    .checked_add(count)
                    .ok_or(WeylError::ExponentOverflow)?;
                add_term(&mut shifted, WeylMonomial::new(exponents), coefficient);
            }
            terms = shifted;
            continue;
        }
        for _ in 0..count {
            terms = append_generator(algebra, terms, generator)?;
        }
    }
    Ok(terms)
}

fn append_generator<S: Scalar>(
    algebra: &WeylAlgebra<S>,
    terms: BTreeMap<WeylMonomial, S>,
    generator: usize,
) -> Result<BTreeMap<WeylMonomial, S>, WeylError> {
    let mut output = BTreeMap::new();
    for (monomial, coefficient) in terms {
        let exponents = monomial.exponents.into_vec();

        let mut uncontracted = exponents.clone();
        uncontracted[generator] = uncontracted[generator]
            .checked_add(1)
            .ok_or(WeylError::ExponentOverflow)?;
        add_term(
            &mut output,
            WeylMonomial::new(uncontracted),
            coefficient.clone(),
        );

        for higher in (generator + 1)..algebra.dim() {
            let multiplicity = exponents[higher];
            let commutator = &algebra.commutator[higher][generator];
            if multiplicity == 0 || commutator.is_zero() {
                continue;
            }
            let mut contracted = exponents.clone();
            contracted[higher] -= 1;
            let contraction = coefficient
                .mul(&embed_nat::<S>(multiplicity))
                .mul(commutator);
            add_term(&mut output, WeylMonomial::new(contracted), contraction);
        }
    }
    Ok(output)
}

fn standard_monomial_product<S: Scalar>(
    pairs: usize,
    left: &[u128],
    right: &[u128],
) -> Result<BTreeMap<WeylMonomial, S>, WeylError> {
    let dim = pairs * 2;
    let mut partial = BTreeMap::from([(WeylMonomial::new(vec![0; dim]), S::one())]);
    for i in 0..pairs {
        let normal_ordered = normal_order_pair::<S>(left[pairs + i], right[i]);
        let mut next = BTreeMap::new();
        for (partial_monomial, partial_coefficient) in partial {
            for &(right_x, left_d, ref pair_coefficient) in &normal_ordered {
                let mut exponents = partial_monomial.exponents.to_vec();
                exponents[i] = left[i]
                    .checked_add(right_x)
                    .ok_or(WeylError::ExponentOverflow)?;
                exponents[pairs + i] = left_d
                    .checked_add(right[pairs + i])
                    .ok_or(WeylError::ExponentOverflow)?;
                add_term(
                    &mut next,
                    WeylMonomial::new(exponents),
                    partial_coefficient.mul(pair_coefficient),
                );
            }
        }
        partial = next;
    }
    Ok(partial)
}

/// Canonically normal-order `d^left_d * x^right_x` without division. Iterating
/// through the smaller exponent keeps the recurrence proportional to the number
/// of possible contraction orders and works over arbitrary characteristic.
fn normal_order_pair<S: Scalar>(left_d: u128, right_x: u128) -> Vec<(u128, u128, S)> {
    if left_d <= right_x {
        let mut terms = BTreeMap::from([((right_x, 0u128), S::one())]);
        for _ in 0..left_d {
            let mut next = BTreeMap::new();
            for ((x_power, d_power), coefficient) in terms {
                add_pair_term(&mut next, (x_power, d_power + 1), coefficient.clone());
                if x_power > 0 {
                    add_pair_term(
                        &mut next,
                        (x_power - 1, d_power),
                        coefficient.mul(&embed_nat::<S>(x_power)),
                    );
                }
            }
            terms = next;
        }
        terms
            .into_iter()
            .map(|((x_power, d_power), coefficient)| (x_power, d_power, coefficient))
            .collect()
    } else {
        let mut terms = BTreeMap::from([((0u128, left_d), S::one())]);
        for _ in 0..right_x {
            let mut next = BTreeMap::new();
            for ((x_power, d_power), coefficient) in terms {
                add_pair_term(&mut next, (x_power + 1, d_power), coefficient.clone());
                if d_power > 0 {
                    add_pair_term(
                        &mut next,
                        (x_power, d_power - 1),
                        coefficient.mul(&embed_nat::<S>(d_power)),
                    );
                }
            }
            terms = next;
        }
        terms
            .into_iter()
            .map(|((x_power, d_power), coefficient)| (x_power, d_power, coefficient))
            .collect()
    }
}

fn add_pair_term<S: Scalar>(
    terms: &mut BTreeMap<(u128, u128), S>,
    powers: (u128, u128),
    coefficient: S,
) {
    if coefficient.is_zero() {
        return;
    }
    let entry = terms.entry(powers).or_insert_with(S::zero);
    *entry = entry.add(&coefficient);
    if entry.is_zero() {
        terms.remove(&powers);
    }
}
