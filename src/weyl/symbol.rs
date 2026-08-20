use super::algebra::{ExpansionTracker, WeylAlgebra, WeylError, WeylExpansionBudget};
use super::element::{WeylElement, WeylMonomial};
use super::polynomial::{tracked_add_term, SparseMonomial, SparsePolynomial};
use super::product::embed_nat;
use crate::scalar::Scalar;
use std::collections::BTreeMap;

/// A standard filtration on a PBW Weyl algebra.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WeylFiltration {
    /// Every generator has degree one.
    Bernstein,
    /// Standard `x_i` have degree zero and `d_i` have degree one.
    DifferentialOrder,
}

impl<S: Scalar> WeylAlgebra<S> {
    /// Maximum Bernstein degree, with every PBW generator assigned degree one.
    pub fn bernstein_degree(&self, element: &WeylElement<S>) -> Result<Option<u128>, WeylError> {
        self.filtration_degree(element)
    }

    /// Maximum differential order in a standard Weyl presentation.
    pub fn differential_order(&self, element: &WeylElement<S>) -> Result<Option<u128>, WeylError> {
        self.filtered_degree(element, WeylFiltration::DifferentialOrder)
    }

    /// Degree in the selected filtration; zero has no degree.
    pub fn filtered_degree(
        &self,
        element: &WeylElement<S>,
        filtration: WeylFiltration,
    ) -> Result<Option<u128>, WeylError> {
        self.validate_element(element)?;
        let pairs = match filtration {
            WeylFiltration::Bernstein => None,
            WeylFiltration::DifferentialOrder => {
                Some(self.standard_pairs.ok_or(WeylError::RequiresStandard)?)
            }
        };
        element.terms.keys().try_fold(None, |maximum, monomial| {
            let degree = filtered_monomial_degree(monomial, filtration, pairs)?;
            Ok(Some(maximum.map_or(degree, |old: u128| old.max(degree))))
        })
    }

    /// Principal symbol in the commutative polynomial ring on the PBW
    /// generators. For differential order this retains the position exponents
    /// while selecting terms with maximal total `d` exponent.
    pub fn principal_symbol(
        &self,
        element: &WeylElement<S>,
        filtration: WeylFiltration,
    ) -> Result<SparsePolynomial<S>, WeylError> {
        let Some(degree) = self.filtered_degree(element, filtration)? else {
            return Ok(SparsePolynomial::zero(self.dim()));
        };
        let pairs = match filtration {
            WeylFiltration::Bernstein => None,
            WeylFiltration::DifferentialOrder => {
                Some(self.standard_pairs.ok_or(WeylError::RequiresStandard)?)
            }
        };
        let mut terms = BTreeMap::new();
        for (monomial, coefficient) in &element.terms {
            if filtered_monomial_degree(monomial, filtration, pairs)? == degree {
                terms.insert(
                    SparseMonomial::new(monomial.exponents().to_vec()),
                    coefficient.clone(),
                );
            }
        }
        Ok(SparsePolynomial {
            dim: self.dim(),
            terms,
        })
    }

    /// Constant Poisson bracket associated with this algebra's alternating
    /// commutator form.
    pub fn poisson_bracket(
        &self,
        left: &SparsePolynomial<S>,
        right: &SparsePolynomial<S>,
    ) -> Result<SparsePolynomial<S>, WeylError> {
        self.poisson_bracket_with_budget(left, right, WeylExpansionBudget::unbounded())
    }

    /// Constant Poisson bracket under one term/work expansion budget.
    ///
    /// The convention is `{z_i,z_j} = omega[i][j]`, so for a standard algebra
    /// `{d_i,x_j} = delta_ij`, matching the leading Weyl commutator.
    pub fn poisson_bracket_with_budget(
        &self,
        left: &SparsePolynomial<S>,
        right: &SparsePolynomial<S>,
        budget: WeylExpansionBudget,
    ) -> Result<SparsePolynomial<S>, WeylError> {
        if left.dim != self.dim() {
            return Err(WeylError::DimensionMismatch {
                expected: self.dim(),
                actual: left.dim,
            });
        }
        if right.dim != self.dim() {
            return Err(WeylError::DimensionMismatch {
                expected: self.dim(),
                actual: right.dim,
            });
        }
        let mut tracker = ExpansionTracker::new(budget);
        let mut terms = BTreeMap::new();
        for (left_monomial, left_coefficient) in &left.terms {
            for (right_monomial, right_coefficient) in &right.terms {
                for left_variable in 0..self.dim() {
                    let left_power = left_monomial.exponents[left_variable];
                    if left_power == 0 {
                        continue;
                    }
                    for right_variable in 0..self.dim() {
                        let right_power = right_monomial.exponents[right_variable];
                        let omega = &self.commutator[left_variable][right_variable];
                        if right_power == 0 || omega.is_zero() {
                            continue;
                        }
                        tracker.charge(1)?;
                        let mut exponents = Vec::with_capacity(self.dim());
                        for variable in 0..self.dim() {
                            let left_reduced = left_monomial.exponents[variable]
                                - u128::from(variable == left_variable);
                            let right_reduced = right_monomial.exponents[variable]
                                - u128::from(variable == right_variable);
                            exponents.push(
                                left_reduced
                                    .checked_add(right_reduced)
                                    .ok_or(WeylError::ExponentOverflow)?,
                            );
                        }
                        let coefficient = left_coefficient
                            .mul(right_coefficient)
                            .mul(&embed_nat::<S>(left_power))
                            .mul(&embed_nat::<S>(right_power))
                            .mul(omega);
                        tracked_add_term(
                            &mut terms,
                            SparseMonomial::new(exponents),
                            coefficient,
                            &mut tracker,
                        )?;
                    }
                }
            }
        }
        Ok(SparsePolynomial {
            dim: self.dim(),
            terms,
        })
    }
}

fn filtered_monomial_degree(
    monomial: &WeylMonomial,
    filtration: WeylFiltration,
    standard_pairs: Option<usize>,
) -> Result<u128, WeylError> {
    let exponents = match filtration {
        WeylFiltration::Bernstein => monomial.exponents(),
        WeylFiltration::DifferentialOrder => {
            &monomial.exponents()[standard_pairs.expect("checked standard filtration")..]
        }
    };
    exponents.iter().try_fold(0u128, |degree, exponent| {
        degree
            .checked_add(*exponent)
            .ok_or(WeylError::ExponentOverflow)
    })
}
