use super::algebra::{ExpansionTracker, WeylAlgebra, WeylError, WeylExpansionBudget};
use super::element::WeylElement;
use super::polynomial::{tracked_add_term, SparseMonomial, SparsePolynomial};
use super::product::embed_nat;
use crate::scalar::{Poly, Scalar};
use std::collections::BTreeMap;

fn falling_factorial<S: Scalar>(
    top: u128,
    order: u128,
    tracker: &mut ExpansionTracker,
) -> Result<S, WeylError> {
    debug_assert!(order <= top);
    if order == 0 {
        return Ok(S::one());
    }

    // The canonical integer embedding kills every multiple of the ring
    // characteristic. Detecting one in the interval avoids enormous derivative
    // loops in finite characteristic without assuming that the coefficient
    // world is a field.
    let characteristic = S::characteristic();
    let bottom = top - order + 1;
    if characteristic > 0 && top / characteristic > (bottom - 1) / characteristic {
        return Ok(S::zero());
    }

    tracker.charge(order)?;
    let mut coefficient = S::one();
    for offset in 0..order {
        coefficient = coefficient.mul(&embed_nat::<S>(top - offset));
        if coefficient.is_zero() {
            break;
        }
    }
    Ok(coefficient)
}

impl<S: Scalar> WeylAlgebra<S> {
    /// Apply an element of the standard rank-`n` Weyl algebra to a sparse
    /// polynomial in `n` variables, with `x_i` acting by multiplication by
    /// `t_i` and `d_i` by formal partial differentiation.
    pub fn act_on_sparse_poly(
        &self,
        operator: &WeylElement<S>,
        polynomial: &SparsePolynomial<S>,
    ) -> Result<SparsePolynomial<S>, WeylError> {
        self.act_on_sparse_poly_with_budget(operator, polynomial, WeylExpansionBudget::unbounded())
    }

    /// Standard rank-`n` polynomial action under one explicit expansion
    /// budget. In positive characteristic this representation is deliberately
    /// not claimed faithful.
    pub fn act_on_sparse_poly_with_budget(
        &self,
        operator: &WeylElement<S>,
        polynomial: &SparsePolynomial<S>,
        budget: WeylExpansionBudget,
    ) -> Result<SparsePolynomial<S>, WeylError> {
        self.validate_element(operator)?;
        let pairs = self.standard_pairs.ok_or(WeylError::RequiresStandard)?;
        if polynomial.dim != pairs {
            return Err(WeylError::DimensionMismatch {
                expected: pairs,
                actual: polynomial.dim,
            });
        }

        let mut tracker = ExpansionTracker::new(budget);
        tracker.ensure_terms(polynomial.terms.len())?;
        let mut output = BTreeMap::new();
        for (operator_monomial, operator_coefficient) in &operator.terms {
            for (polynomial_monomial, polynomial_coefficient) in &polynomial.terms {
                tracker.charge(1)?;
                let mut coefficient = operator_coefficient.mul(polynomial_coefficient);
                let mut exponents = polynomial_monomial.exponents.to_vec();
                let mut vanishes = false;

                for variable in 0..pairs {
                    let x_power = operator_monomial.exponents()[variable];
                    let d_power = operator_monomial.exponents()[pairs + variable];
                    let polynomial_power = exponents[variable];
                    if d_power > polynomial_power {
                        vanishes = true;
                        break;
                    }
                    let derivative =
                        falling_factorial::<S>(polynomial_power, d_power, &mut tracker)?;
                    coefficient = coefficient.mul(&derivative);
                    if coefficient.is_zero() {
                        vanishes = true;
                        break;
                    }
                    exponents[variable] = polynomial_power
                        .checked_sub(d_power)
                        .and_then(|remaining| remaining.checked_add(x_power))
                        .ok_or(WeylError::ExponentOverflow)?;
                }

                if !vanishes {
                    tracked_add_term(
                        &mut output,
                        SparseMonomial::new(exponents),
                        coefficient,
                        &mut tracker,
                    )?;
                }
            }
        }
        Ok(SparsePolynomial {
            dim: pairs,
            terms: output,
        })
    }

    /// Apply an element of the standard rank-one Weyl algebra to dense `S[t]`.
    ///
    /// This compatibility representation is backed by the sparse rank-one
    /// action. It respects multiplication over every scalar backend, but is not
    /// faithful in positive characteristic: `d^p` acts as zero in
    /// characteristic `p` while remaining a nonzero central Weyl element.
    pub fn act_on_poly(
        &self,
        operator: &WeylElement<S>,
        polynomial: &Poly<S>,
    ) -> Result<Poly<S>, WeylError> {
        self.validate_element(operator)?;
        if self.standard_pairs != Some(1) {
            return Err(WeylError::RequiresStandardRankOne);
        }

        let mut sparse_terms = BTreeMap::new();
        for (degree, coefficient) in polynomial.coeffs().iter().enumerate() {
            if !coefficient.is_zero() {
                sparse_terms.insert(
                    SparseMonomial::new(vec![degree as u128]),
                    coefficient.clone(),
                );
            }
        }
        let sparse = SparsePolynomial {
            dim: 1,
            terms: sparse_terms,
        };
        let acted = self.act_on_sparse_poly(operator, &sparse)?;
        let maximum_degree = acted
            .terms
            .keys()
            .map(|monomial| monomial.exponents[0])
            .max();
        let Some(maximum_degree) = maximum_degree else {
            return Ok(Poly::zero());
        };
        let maximum_degree =
            usize::try_from(maximum_degree).map_err(|_| WeylError::PolynomialDegreeOverflow)?;
        let length = maximum_degree
            .checked_add(1)
            .ok_or(WeylError::PolynomialDegreeOverflow)?;
        let mut coefficients = vec![S::zero(); length];
        for (monomial, coefficient) in acted.terms {
            let degree = usize::try_from(monomial.exponents[0])
                .map_err(|_| WeylError::PolynomialDegreeOverflow)?;
            coefficients[degree] = coefficient;
        }
        Ok(Poly::new(coefficients))
    }
}
