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
    ///
    /// # Examples
    ///
    /// In rank two, `d_0 x_1` sends `t_0^2 t_1^3 + 2 t_0` to
    /// `2 t_0 t_1^4 + 2 t_1`; a budget smaller than the two-term polynomial
    /// is refused with an error:
    ///
    /// ```
    /// use ogdoad::scalar::{Rational, Scalar};
    /// use ogdoad::weyl::{SparsePolynomial, WeylAlgebra, WeylError, WeylExpansionBudget};
    ///
    /// let r = Rational::from_int;
    /// let weyl = WeylAlgebra::<Rational>::standard(2);
    /// let operator = weyl.mul(&weyl.d(0), &weyl.x(1));
    /// let term = |exponents: &[u128], c| SparsePolynomial::monomial(exponents, r(c));
    /// let f = term(&[2, 3], 1) + term(&[1, 0], 2);
    /// let expected = term(&[1, 4], 2) + term(&[0, 1], 2);
    /// let budget = WeylExpansionBudget::new(32, 1_000);
    /// assert_eq!(weyl.act_on_sparse_poly_with_budget(&operator, &f, budget), Ok(expected));
    /// assert_eq!(
    ///     weyl.act_on_sparse_poly_with_budget(&operator, &f, WeylExpansionBudget::new(1, 1_000)),
    ///     Err(WeylError::TermBudgetExceeded { limit: 1 })
    /// );
    /// ```
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
    ///
    /// # Examples
    ///
    /// `x` multiplies by `t` and `d` differentiates, so `x d` is the Euler
    /// operator `t d/dt` and `[d, x]` acts as the identity:
    ///
    /// ```
    /// use ogdoad::scalar::{Poly, Rational, Scalar};
    /// use ogdoad::weyl::WeylAlgebra;
    ///
    /// let r = Rational::from_int;
    /// let weyl = WeylAlgebra::<Rational>::standard(1);
    /// let f = Poly::new(vec![r(1), r(2), r(3)]); // 1 + 2t + 3t^2
    /// let euler = weyl.mul(&weyl.x(0), &weyl.d(0));
    /// assert_eq!(weyl.act_on_poly(&euler, &f).unwrap(), Poly::new(vec![r(0), r(2), r(6)]));
    /// let identity = weyl.commutator(&weyl.d(0), &weyl.x(0));
    /// assert_eq!(weyl.act_on_poly(&identity, &f).unwrap(), f);
    /// ```
    ///
    /// Over `F_3` the action is not faithful: `d^3` is a nonzero central
    /// element, yet `d^3 t^k = k(k-1)(k-2) t^(k-3)` vanishes because three
    /// consecutive integers include a multiple of 3 (spot-checked here for
    /// `k < 9`):
    ///
    /// ```
    /// use ogdoad::scalar::{Fp, Poly, Scalar};
    /// use ogdoad::weyl::WeylAlgebra;
    ///
    /// let weyl = WeylAlgebra::<Fp<3>>::standard(1);
    /// let d3 = weyl.pow(&weyl.d(0), 3);
    /// assert!(!d3.is_zero() && weyl.is_central(&d3).unwrap());
    /// for k in 0..9 {
    ///     let t_k = Poly::monomial(k, Fp::<3>::one());
    ///     assert!(weyl.act_on_poly(&d3, &t_k).unwrap().is_zero());
    /// }
    /// ```
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
