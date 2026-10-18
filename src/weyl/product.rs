use super::algebra::{ExpansionTracker, WeylAlgebra, WeylError};
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

fn gcd(mut left: u128, mut right: u128) -> u128 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}

/// Compute the image of `binomial(n,k)` in `S` without dividing in `S` and
/// without materializing the possibly enormous host integer. Exact denominator
/// cancellation leaves a list of `u128` numerator factors, each of which enters
/// through the canonical natural-number embedding.
fn binomial_in_scalar<S: Scalar>(
    n: u128,
    k: u128,
    tracker: &mut ExpansionTracker,
) -> Result<S, WeylError> {
    debug_assert!(k <= n);
    let k = k.min(n - k);
    if k == 0 {
        return Ok(S::one());
    }
    tracker.charge(k)?;
    let length = usize::try_from(k).map_err(|_| WeylError::ExpansionIndexOverflow)?;
    let start = n - k + 1;
    let mut numerators: Vec<u128> = (0..length).map(|offset| start + offset as u128).collect();

    for denominator in 2..=k {
        let mut remainder = denominator;
        for numerator in &mut numerators {
            tracker.charge(1)?;
            let divisor = gcd(*numerator, remainder);
            *numerator /= divisor;
            remainder /= divisor;
            if remainder == 1 {
                break;
            }
        }
        debug_assert_eq!(remainder, 1, "binomial denominator cancels exactly");
    }

    let mut output = S::one();
    for factor in numerators {
        if factor != 1 {
            tracker.charge(1)?;
            output = output.mul(&embed_nat::<S>(factor));
        }
    }
    Ok(output)
}

fn tracked_add_term<S: Scalar>(
    terms: &mut BTreeMap<WeylMonomial, S>,
    monomial: WeylMonomial,
    coefficient: S,
    tracker: &mut ExpansionTracker,
) -> Result<(), WeylError> {
    tracker.charge(1)?;
    add_term(terms, monomial, coefficient);
    tracker.ensure_terms(terms.len())
}

pub(super) fn multiply<S: Scalar>(
    algebra: &WeylAlgebra<S>,
    left: &WeylElement<S>,
    right: &WeylElement<S>,
    tracker: &mut ExpansionTracker,
) -> Result<WeylElement<S>, WeylError> {
    let mut output = BTreeMap::new();
    for (left_monomial, left_coefficient) in &left.terms {
        for (right_monomial, right_coefficient) in &right.terms {
            tracker.charge(1)?;
            let scalar = left_coefficient.mul(right_coefficient);
            if scalar.is_zero() {
                continue;
            }
            let product = match algebra.standard_pairs {
                Some(pairs) => standard_monomial_product(
                    pairs,
                    left_monomial.exponents(),
                    right_monomial.exponents(),
                    tracker,
                )?,
                None => general_monomial_product(
                    algebra,
                    left_monomial.exponents(),
                    right_monomial.exponents(),
                    tracker,
                )?,
            };
            for (monomial, coefficient) in product {
                tracked_add_term(&mut output, monomial, scalar.mul(&coefficient), tracker)?;
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
    tracker: &mut ExpansionTracker,
) -> Result<BTreeMap<WeylMonomial, S>, WeylError> {
    let mut terms = BTreeMap::from([(WeylMonomial::new(left.to_vec()), S::one())]);
    tracker.ensure_terms(terms.len())?;
    for (generator, &count) in right.iter().enumerate() {
        if count == 0 {
            continue;
        }
        let mut shifted = BTreeMap::new();
        for (monomial, coefficient) in terms {
            let expansion =
                append_generator_power(algebra, monomial.exponents(), generator, count, tracker)?;
            for (expanded, expansion_coefficient) in expansion {
                tracked_add_term(
                    &mut shifted,
                    expanded,
                    coefficient.mul(&expansion_coefficient),
                    tracker,
                )?;
            }
        }
        terms = shifted;
    }
    Ok(terms)
}

/// Normal-order `z^a * z_generator^count` in one grouped step.
///
/// Writing `delta(P) = [P,z_generator]`, the central-commutator relation gives
///
/// `P z^count = sum_k binomial(count,k) z^(count-k) delta^k(P)`.
///
/// Consequently the loop is bounded by the total exponent available for
/// contraction among higher generators, rather than by `count`. This is the
/// important large-exponent boundary: `z_1 z_0^N` takes constant contraction
/// depth even when `N` is close to `u128::MAX`.
fn append_generator_power<S: Scalar>(
    algebra: &WeylAlgebra<S>,
    exponents: &[u128],
    generator: usize,
    count: u128,
    tracker: &mut ExpansionTracker,
) -> Result<BTreeMap<WeylMonomial, S>, WeylError> {
    let available = ((generator + 1)..algebra.dim()).fold(0u128, |total, higher| {
        if algebra.commutator[higher][generator].is_zero() {
            total
        } else {
            total.saturating_add(exponents[higher]).min(count)
        }
    });

    if available == 0 {
        let mut shifted = exponents.to_vec();
        shifted[generator] = shifted[generator]
            .checked_add(count)
            .ok_or(WeylError::ExponentOverflow)?;
        let output = BTreeMap::from([(WeylMonomial::new(shifted), S::one())]);
        tracker.ensure_terms(output.len())?;
        return Ok(output);
    }

    let mut output = BTreeMap::new();
    let mut derivatives = BTreeMap::from([(WeylMonomial::new(exponents.to_vec()), S::one())]);
    tracker.ensure_terms(derivatives.len())?;

    for contraction_order in 0..=available {
        let binomial = binomial_in_scalar::<S>(count, contraction_order, tracker)?;
        if !binomial.is_zero() {
            for (derivative, coefficient) in &derivatives {
                let mut normalized = derivative.exponents.to_vec();
                normalized[generator] = normalized[generator]
                    .checked_add(count - contraction_order)
                    .ok_or(WeylError::ExponentOverflow)?;
                tracked_add_term(
                    &mut output,
                    WeylMonomial::new(normalized),
                    binomial.mul(coefficient),
                    tracker,
                )?;
            }
        }

        if contraction_order == available {
            break;
        }
        let mut next = BTreeMap::new();
        for (derivative, coefficient) in derivatives {
            for higher in (generator + 1)..algebra.dim() {
                let multiplicity = derivative.exponents[higher];
                let commutator = &algebra.commutator[higher][generator];
                if multiplicity == 0 || commutator.is_zero() {
                    continue;
                }
                let mut contracted = derivative.exponents.to_vec();
                contracted[higher] -= 1;
                let contraction = coefficient
                    .mul(&embed_nat::<S>(multiplicity))
                    .mul(commutator);
                tracked_add_term(
                    &mut next,
                    WeylMonomial::new(contracted),
                    contraction,
                    tracker,
                )?;
            }
        }
        derivatives = next;
        if derivatives.is_empty() {
            break;
        }
    }
    Ok(output)
}

fn standard_monomial_product<S: Scalar>(
    pairs: usize,
    left: &[u128],
    right: &[u128],
    tracker: &mut ExpansionTracker,
) -> Result<BTreeMap<WeylMonomial, S>, WeylError> {
    let dim = pairs * 2;
    let mut partial = BTreeMap::from([(WeylMonomial::new(vec![0; dim]), S::one())]);
    tracker.ensure_terms(partial.len())?;
    for i in 0..pairs {
        let normal_ordered = normal_order_pair::<S>(left[pairs + i], right[i], tracker)?;
        let mut next = BTreeMap::new();
        for (partial_monomial, partial_coefficient) in partial {
            for &(right_x, left_d, ref pair_coefficient) in &normal_ordered {
                tracker.charge(1)?;
                let mut exponents = partial_monomial.exponents.to_vec();
                exponents[i] = left[i]
                    .checked_add(right_x)
                    .ok_or(WeylError::ExponentOverflow)?;
                exponents[pairs + i] = left_d
                    .checked_add(right[pairs + i])
                    .ok_or(WeylError::ExponentOverflow)?;
                tracked_add_term(
                    &mut next,
                    WeylMonomial::new(exponents),
                    partial_coefficient.mul(pair_coefficient),
                    tracker,
                )?;
            }
        }
        partial = next;
    }
    Ok(partial)
}

/// Canonically normal-order `d^left_d * x^right_x` without division. Iterating
/// through the smaller exponent keeps the recurrence proportional to the number
/// of possible contraction orders and works over arbitrary characteristic.
fn normal_order_pair<S: Scalar>(
    left_d: u128,
    right_x: u128,
    tracker: &mut ExpansionTracker,
) -> Result<Vec<(u128, u128, S)>, WeylError> {
    let terms = if left_d <= right_x {
        let mut terms = BTreeMap::from([((right_x, 0u128), S::one())]);
        tracker.ensure_terms(terms.len())?;
        for _ in 0..left_d {
            tracker.charge(1)?;
            let mut next = BTreeMap::new();
            for ((x_power, d_power), coefficient) in terms {
                tracked_add_pair_term(
                    &mut next,
                    (x_power, d_power + 1),
                    coefficient.clone(),
                    tracker,
                )?;
                if x_power > 0 {
                    tracked_add_pair_term(
                        &mut next,
                        (x_power - 1, d_power),
                        coefficient.mul(&embed_nat::<S>(x_power)),
                        tracker,
                    )?;
                }
            }
            terms = next;
        }
        terms
    } else {
        let mut terms = BTreeMap::from([((0u128, left_d), S::one())]);
        tracker.ensure_terms(terms.len())?;
        for _ in 0..right_x {
            tracker.charge(1)?;
            let mut next = BTreeMap::new();
            for ((x_power, d_power), coefficient) in terms {
                tracked_add_pair_term(
                    &mut next,
                    (x_power + 1, d_power),
                    coefficient.clone(),
                    tracker,
                )?;
                if d_power > 0 {
                    tracked_add_pair_term(
                        &mut next,
                        (x_power, d_power - 1),
                        coefficient.mul(&embed_nat::<S>(d_power)),
                        tracker,
                    )?;
                }
            }
            terms = next;
        }
        terms
    };
    Ok(terms
        .into_iter()
        .map(|((x_power, d_power), coefficient)| (x_power, d_power, coefficient))
        .collect())
}

fn tracked_add_pair_term<S: Scalar>(
    terms: &mut BTreeMap<(u128, u128), S>,
    powers: (u128, u128),
    coefficient: S,
    tracker: &mut ExpansionTracker,
) -> Result<(), WeylError> {
    tracker.charge(1)?;
    if coefficient.is_zero() {
        return Ok(());
    }
    let entry = terms.entry(powers).or_insert_with(S::zero);
    *entry = entry.add(&coefficient);
    if entry.is_zero() {
        terms.remove(&powers);
    }
    tracker.ensure_terms(terms.len())
}
