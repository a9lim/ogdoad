use super::algebra::{ExpansionTracker, WeylError, WeylExpansionBudget};
use super::product::embed_nat;
use crate::scalar::Scalar;
use std::collections::BTreeMap;
use std::fmt;
use std::ops::{Add, Neg, Sub};

/// One commutative monomial `t_0^a_0 ... t_(n-1)^a_(n-1)`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SparseMonomial {
    pub(crate) exponents: Box<[u128]>,
}

impl SparseMonomial {
    pub(crate) fn new(exponents: Vec<u128>) -> Self {
        Self {
            exponents: exponents.into_boxed_slice(),
        }
    }

    /// The ordered multidegree.
    pub fn exponents(&self) -> &[u128] {
        &self.exponents
    }

    /// Total degree, or `None` if its `u128` sum overflows.
    pub fn total_degree(&self) -> Option<u128> {
        self.exponents
            .iter()
            .try_fold(0u128, |degree, exponent| degree.checked_add(*exponent))
    }

    fn is_scalar(&self) -> bool {
        self.exponents.iter().all(|exponent| *exponent == 0)
    }

    fn label(&self) -> String {
        self.exponents
            .iter()
            .enumerate()
            .filter_map(|(index, exponent)| match exponent {
                0 => None,
                1 => Some(format!("t{index}")),
                exponent => Some(format!("t{index}↑{exponent}")),
            })
            .collect::<Vec<_>>()
            .join("⋅")
    }
}

/// A finite-support commutative polynomial in a fixed number of variables.
///
/// Multidegrees use the same checked `u128` payload as Weyl PBW monomials, but
/// this is a distinct commutative type: multiplying two terms only adds their
/// exponent vectors. Zero coefficients are never stored.
#[derive(Clone, Debug, PartialEq)]
pub struct SparsePolynomial<S: Scalar> {
    pub(crate) dim: usize,
    pub(crate) terms: BTreeMap<SparseMonomial, S>,
}

impl<S: Scalar> SparsePolynomial<S> {
    /// The zero polynomial in `dim` variables.
    pub fn zero(dim: usize) -> Self {
        Self {
            dim,
            terms: BTreeMap::new(),
        }
    }

    /// A scalar polynomial in `dim` variables.
    pub fn scalar(dim: usize, coefficient: S) -> Self {
        let mut terms = BTreeMap::new();
        if !coefficient.is_zero() {
            terms.insert(SparseMonomial::new(vec![0; dim]), coefficient);
        }
        Self { dim, terms }
    }

    /// One monomial; its variable dimension is inferred from the exponent
    /// vector.
    pub fn monomial(exponents: &[u128], coefficient: S) -> Self {
        let mut terms = BTreeMap::new();
        if !coefficient.is_zero() {
            terms.insert(SparseMonomial::new(exponents.to_vec()), coefficient);
        }
        Self {
            dim: exponents.len(),
            terms,
        }
    }

    /// One polynomial variable `t_index` in a fixed dimension.
    pub fn try_variable(dim: usize, index: usize) -> Result<Self, WeylError> {
        if index >= dim {
            return Err(WeylError::GeneratorOutOfRange { index, dim });
        }
        let mut exponents = vec![0; dim];
        exponents[index] = 1;
        Ok(Self::monomial(&exponents, S::one()))
    }

    /// The number of polynomial variables.
    pub fn dim(&self) -> usize {
        self.dim
    }

    /// Canonical nonzero sparse terms.
    pub fn terms(&self) -> &BTreeMap<SparseMonomial, S> {
        &self.terms
    }

    /// Number of nonzero monomials.
    pub fn term_count(&self) -> usize {
        self.terms.len()
    }

    /// Whether this polynomial is zero.
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// Maximum total degree, `None` for zero or when a carried multidegree sum
    /// exceeds `u128`.
    pub fn total_degree(&self) -> Option<u128> {
        let mut maximum = None;
        for monomial in self.terms.keys() {
            let degree = monomial.total_degree()?;
            maximum = Some(maximum.map_or(degree, |old: u128| old.max(degree)));
        }
        maximum
    }

    /// Add two polynomials after checking their variable dimensions.
    pub fn checked_add(&self, other: &Self) -> Result<Self, WeylError> {
        if self.dim != other.dim {
            return Err(WeylError::DimensionMismatch {
                expected: self.dim,
                actual: other.dim,
            });
        }
        let mut terms = self.terms.clone();
        for (monomial, coefficient) in &other.terms {
            add_term(&mut terms, monomial.clone(), coefficient.clone());
        }
        Ok(Self {
            dim: self.dim,
            terms,
        })
    }

    /// Checked commutative multiplication without a finite expansion budget.
    pub fn checked_mul(&self, other: &Self) -> Result<Self, WeylError> {
        self.checked_mul_with_budget(other, WeylExpansionBudget::unbounded())
    }

    /// Checked commutative multiplication under explicit materialization
    /// bounds.
    pub fn checked_mul_with_budget(
        &self,
        other: &Self,
        budget: WeylExpansionBudget,
    ) -> Result<Self, WeylError> {
        if self.dim != other.dim {
            return Err(WeylError::DimensionMismatch {
                expected: self.dim,
                actual: other.dim,
            });
        }
        let mut tracker = ExpansionTracker::new(budget);
        let mut terms = BTreeMap::new();
        for (left, left_coefficient) in &self.terms {
            for (right, right_coefficient) in &other.terms {
                tracker.charge(1)?;
                let exponents = left
                    .exponents
                    .iter()
                    .zip(right.exponents.iter())
                    .map(|(left, right)| {
                        left.checked_add(*right).ok_or(WeylError::ExponentOverflow)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                tracked_add_term(
                    &mut terms,
                    SparseMonomial::new(exponents),
                    left_coefficient.mul(right_coefficient),
                    &mut tracker,
                )?;
            }
        }
        Ok(Self {
            dim: self.dim,
            terms,
        })
    }

    /// Formal partial derivative with respect to `t_index`.
    pub fn partial_derivative(&self, index: usize) -> Result<Self, WeylError> {
        if index >= self.dim {
            return Err(WeylError::GeneratorOutOfRange {
                index,
                dim: self.dim,
            });
        }
        let terms = self
            .terms
            .iter()
            .filter_map(|(monomial, coefficient)| {
                let power = monomial.exponents[index];
                if power == 0 {
                    return None;
                }
                let mut exponents = monomial.exponents.to_vec();
                exponents[index] -= 1;
                let derivative = coefficient.mul(&embed_nat::<S>(power));
                (!derivative.is_zero()).then(|| (SparseMonomial::new(exponents), derivative))
            })
            .collect();
        Ok(Self {
            dim: self.dim,
            terms,
        })
    }

    /// Map coefficients through a caller-supplied scalar homomorphism.
    pub fn map_coefficients<T: Scalar>(&self, f: impl Fn(&S) -> T) -> SparsePolynomial<T> {
        SparsePolynomial {
            dim: self.dim,
            terms: self
                .terms
                .iter()
                .filter_map(|(monomial, coefficient)| {
                    let mapped = f(coefficient);
                    (!mapped.is_zero()).then(|| (monomial.clone(), mapped))
                })
                .collect(),
        }
    }

    /// Canonical human-readable representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

pub(crate) fn add_term<S: Scalar>(
    terms: &mut BTreeMap<SparseMonomial, S>,
    monomial: SparseMonomial,
    coefficient: S,
) {
    if coefficient.is_zero() {
        return;
    }
    let entry = terms.entry(monomial.clone()).or_insert_with(S::zero);
    *entry = entry.add(&coefficient);
    if entry.is_zero() {
        terms.remove(&monomial);
    }
}

pub(crate) fn tracked_add_term<S: Scalar>(
    terms: &mut BTreeMap<SparseMonomial, S>,
    monomial: SparseMonomial,
    coefficient: S,
    tracker: &mut ExpansionTracker,
) -> Result<(), WeylError> {
    tracker.charge(1)?;
    add_term(terms, monomial, coefficient);
    tracker.ensure_terms(terms.len())
}

impl<S: Scalar> fmt::Display for SparsePolynomial<S> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.terms.is_empty() {
            return write!(formatter, "{}", S::zero());
        }
        let one = S::one();
        let neg_one = one.neg();
        let mut parts = Vec::with_capacity(self.terms.len());
        for (monomial, coefficient) in &self.terms {
            if monomial.is_scalar() {
                parts.push(coefficient.to_string());
                continue;
            }
            let label = monomial.label();
            if coefficient == &one {
                parts.push(label);
            } else if coefficient == &neg_one {
                parts.push(format!("-{label}"));
            } else {
                parts.push(crate::scalar::poly::attach_coeff(coefficient, &label));
            }
        }

        let mut output = String::new();
        for (index, part) in parts.iter().enumerate() {
            if let Some(magnitude) = part.strip_prefix('-') {
                if index == 0 {
                    output.push('-');
                } else {
                    output.push_str(" - ");
                }
                output.push_str(magnitude);
            } else {
                if index != 0 {
                    output.push_str(" + ");
                }
                output.push_str(part);
            }
        }
        formatter.write_str(&output)
    }
}

impl<S: Scalar> Add for SparsePolynomial<S> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.checked_add(&rhs)
            .expect("cannot add sparse polynomials with different dimensions")
    }
}

impl<S: Scalar> Neg for SparsePolynomial<S> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            dim: self.dim,
            terms: self
                .terms
                .into_iter()
                .map(|(monomial, coefficient)| (monomial, coefficient.neg()))
                .filter(|(_, coefficient)| !coefficient.is_zero())
                .collect(),
        }
    }
}

impl<S: Scalar> Sub for SparsePolynomial<S> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}
