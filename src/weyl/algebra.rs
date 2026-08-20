use super::element::{add_term, WeylElement, WeylMonomial};
use crate::forms::SymplecticForm;
use crate::scalar::Scalar;
use std::collections::BTreeMap;
use std::fmt;

/// A checked failure while constructing or operating on a finite-support Weyl
/// algebra.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WeylError {
    /// Doubling the requested standard rank exceeded the host dimension type.
    StandardDimensionOverflow,
    /// Adding two generator dimensions exceeded the host dimension type.
    DirectSumDimensionOverflow,
    /// A commutator matrix row does not have the matrix dimension.
    NonSquareCommutator {
        /// The offending row.
        row: usize,
        /// The required row length.
        expected: usize,
        /// The actual row length.
        actual: usize,
    },
    /// An alternating commutator form must have zero diagonal.
    NonzeroDiagonal {
        /// The offending diagonal index.
        index: usize,
    },
    /// The two off-diagonal entries are not additive inverses.
    NotSkewSymmetric {
        /// First generator index.
        left: usize,
        /// Second generator index.
        right: usize,
    },
    /// An algebraic object belongs to a different generator/variable dimension.
    DimensionMismatch {
        /// The algebra's generator dimension.
        expected: usize,
        /// The supplied dimension.
        actual: usize,
    },
    /// A generator index lies outside the algebra's ordered generating set.
    GeneratorOutOfRange {
        /// The requested generator index.
        index: usize,
        /// The algebra's generator dimension.
        dim: usize,
    },
    /// A standard position or differential generator was requested from a
    /// general alternating presentation.
    RequiresStandard,
    /// A PBW monomial exponent vector has the wrong generator dimension.
    MonomialDimensionMismatch {
        /// The algebra's generator dimension.
        expected: usize,
        /// The supplied exponent-vector dimension.
        actual: usize,
    },
    /// Adding PBW exponents exceeded the fixed-width `u128` payload.
    ExponentOverflow,
    /// A materialized multiplication or action crossed its caller-supplied
    /// sparse-term budget.
    TermBudgetExceeded {
        /// Maximum permitted simultaneous sparse terms.
        limit: usize,
    },
    /// A materialized multiplication or action crossed its caller-supplied
    /// elementary-work budget.
    StepBudgetExceeded {
        /// Maximum permitted charged work steps.
        limit: u128,
    },
    /// A combinatorial expansion index cannot be represented by the host
    /// collection dimension type.
    ExpansionIndexOverflow,
    /// An affine-linear map has the wrong number of target-coordinate rows.
    LinearMapRowMismatch {
        /// Required number of target-coordinate rows.
        expected: usize,
        /// Supplied number of rows.
        actual: usize,
    },
    /// A row of an affine-linear map has the wrong source dimension.
    LinearMapColumnMismatch {
        /// Offending target-coordinate row.
        row: usize,
        /// Required source dimension.
        expected: usize,
        /// Supplied row length.
        actual: usize,
    },
    /// An affine translation vector has the wrong source dimension.
    TranslationDimensionMismatch {
        /// Required source dimension.
        expected: usize,
        /// Supplied translation length.
        actual: usize,
    },
    /// Images of a source generator pair do not preserve its commutator.
    CommutatorNotPreserved {
        /// First source generator.
        left: usize,
        /// Second source generator.
        right: usize,
    },
    /// Images of a generator pair do not reverse its commutator as required by
    /// an anti-homomorphism.
    CommutatorNotReversed {
        /// First source generator.
        left: usize,
        /// Second source generator.
        right: usize,
    },
    /// Two maps cannot compose because the intermediate Weyl contexts differ.
    MapContextMismatch,
    /// An automorphism candidate does not have a square invertible linear part.
    NonInvertibleLinearPart,
    /// An automorphism candidate has different source and target algebras.
    NotEndomorphism,
    /// A coordinate embedding names an unavailable target generator.
    EmbeddingIndexOutOfRange {
        /// Requested target generator.
        index: usize,
        /// Target generator dimension.
        dim: usize,
    },
    /// A coordinate embedding repeats a target generator.
    DuplicateEmbeddingIndex {
        /// Repeated target generator.
        index: usize,
    },
    /// A coordinate embedding supplies the wrong number of target indices.
    EmbeddingDimensionMismatch {
        /// Required number of source-coordinate images.
        expected: usize,
        /// Supplied number of indices.
        actual: usize,
    },
    /// A standard scaling supplies the wrong number of unit parameters.
    ScaleDimensionMismatch {
        /// Required standard rank.
        expected: usize,
        /// Supplied number of scales.
        actual: usize,
    },
    /// A standard scaling parameter is not a represented unit.
    NonUnitScale {
        /// Standard pair whose scale is not invertible.
        index: usize,
    },
    /// A standard shear matrix has the wrong number of rows.
    ShearRowCountMismatch {
        /// Required standard rank.
        expected: usize,
        /// Supplied number of rows.
        actual: usize,
    },
    /// A standard shear matrix has a row of the wrong length.
    ShearDimensionMismatch {
        /// Offending row.
        row: usize,
        /// Required standard rank.
        expected: usize,
        /// Supplied row length.
        actual: usize,
    },
    /// A standard shear matrix is not symmetric.
    ShearNotSymmetric {
        /// First matrix coordinate.
        left: usize,
        /// Second matrix coordinate.
        right: usize,
    },
    /// A polynomial action was requested outside the standard rank-one algebra.
    RequiresStandardRankOne,
    /// A PBW `x` exponent cannot be represented as a host polynomial degree.
    PolynomialDegreeOverflow,
}

impl fmt::Display for WeylError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StandardDimensionOverflow => {
                formatter.write_str("standard Weyl generator dimension exceeds usize")
            }
            Self::DirectSumDimensionOverflow => {
                formatter.write_str("direct-sum Weyl generator dimension exceeds usize")
            }
            Self::NonSquareCommutator {
                row,
                expected,
                actual,
            } => write!(
                formatter,
                "commutator row {row} has length {actual}, expected {expected}"
            ),
            Self::NonzeroDiagonal { index } => {
                write!(
                    formatter,
                    "commutator diagonal entry ({index},{index}) is nonzero"
                )
            }
            Self::NotSkewSymmetric { left, right } => write!(
                formatter,
                "commutator entries ({left},{right}) and ({right},{left}) are not additive inverses"
            ),
            Self::DimensionMismatch { expected, actual } => write!(
                formatter,
                "Weyl object dimension mismatch: expected {expected}, got {actual}"
            ),
            Self::GeneratorOutOfRange { index, dim } => {
                write!(
                    formatter,
                    "Weyl generator index {index} is outside dimension {dim}"
                )
            }
            Self::RequiresStandard => {
                formatter.write_str("operation requires a standard Weyl algebra")
            }
            Self::MonomialDimensionMismatch { expected, actual } => write!(
                formatter,
                "Weyl monomial has {actual} exponents, expected {expected}"
            ),
            Self::ExponentOverflow => formatter.write_str("Weyl PBW exponent exceeds u128"),
            Self::TermBudgetExceeded { limit } => {
                write!(formatter, "Weyl expansion exceeds its {limit}-term budget")
            }
            Self::StepBudgetExceeded { limit } => {
                write!(formatter, "Weyl expansion exceeds its {limit}-step budget")
            }
            Self::ExpansionIndexOverflow => {
                formatter.write_str("Weyl expansion index exceeds usize")
            }
            Self::LinearMapRowMismatch { expected, actual } => write!(
                formatter,
                "Weyl linear map has {actual} target rows, expected {expected}"
            ),
            Self::LinearMapColumnMismatch {
                row,
                expected,
                actual,
            } => write!(
                formatter,
                "Weyl linear-map row {row} has length {actual}, expected {expected}"
            ),
            Self::TranslationDimensionMismatch { expected, actual } => write!(
                formatter,
                "Weyl translation has length {actual}, expected {expected}"
            ),
            Self::CommutatorNotPreserved { left, right } => write!(
                formatter,
                "Weyl map does not preserve the commutator of generators {left} and {right}"
            ),
            Self::CommutatorNotReversed { left, right } => write!(
                formatter,
                "Weyl anti-map does not reverse the commutator of generators {left} and {right}"
            ),
            Self::MapContextMismatch => {
                formatter.write_str("Weyl maps have different intermediate contexts")
            }
            Self::NonInvertibleLinearPart => {
                formatter.write_str("Weyl affine map has no invertible linear part")
            }
            Self::NotEndomorphism => {
                formatter.write_str("Weyl automorphism requires equal source and target algebras")
            }
            Self::EmbeddingIndexOutOfRange { index, dim } => write!(
                formatter,
                "Weyl embedding index {index} is outside target dimension {dim}"
            ),
            Self::DuplicateEmbeddingIndex { index } => {
                write!(formatter, "Weyl embedding repeats target index {index}")
            }
            Self::EmbeddingDimensionMismatch { expected, actual } => write!(
                formatter,
                "Weyl embedding supplies {actual} indices, expected {expected}"
            ),
            Self::ScaleDimensionMismatch { expected, actual } => write!(
                formatter,
                "Weyl scaling supplies {actual} parameters, expected {expected}"
            ),
            Self::NonUnitScale { index } => {
                write!(formatter, "Weyl scaling parameter {index} is not a unit")
            }
            Self::ShearRowCountMismatch { expected, actual } => write!(
                formatter,
                "Weyl shear has {actual} rows, expected {expected}"
            ),
            Self::ShearDimensionMismatch {
                row,
                expected,
                actual,
            } => write!(
                formatter,
                "Weyl shear row {row} has size {actual}, expected {expected}"
            ),
            Self::ShearNotSymmetric { left, right } => write!(
                formatter,
                "Weyl shear entries ({left},{right}) and ({right},{left}) differ"
            ),
            Self::RequiresStandardRankOne => {
                formatter.write_str("polynomial action requires the standard rank-one Weyl algebra")
            }
            Self::PolynomialDegreeOverflow => {
                formatter.write_str("Weyl action produces a polynomial degree outside usize")
            }
        }
    }
}

impl std::error::Error for WeylError {}

/// Caller-supplied bounds for a materialized Weyl expansion.
///
/// `max_terms` bounds every intermediate and final sparse map, while
/// `max_steps` bounds charged normal-order, coefficient, and term-combination
/// work across the whole public operation. The unbounded value preserves the
/// original checked API; callers handling untrusted exponents should supply a
/// finite budget.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WeylExpansionBudget {
    /// Maximum simultaneous sparse terms in an intermediate or output value.
    pub max_terms: usize,
    /// Maximum charged elementary work steps.
    pub max_steps: u128,
}

impl WeylExpansionBudget {
    /// Construct explicit sparse-term and work-step bounds.
    pub const fn new(max_terms: usize, max_steps: u128) -> Self {
        Self {
            max_terms,
            max_steps,
        }
    }

    /// The compatibility budget used by the original checked API.
    pub const fn unbounded() -> Self {
        Self::new(usize::MAX, u128::MAX)
    }
}

#[derive(Debug)]
pub(crate) struct ExpansionTracker {
    budget: WeylExpansionBudget,
    steps: u128,
}

impl ExpansionTracker {
    pub(crate) fn new(budget: WeylExpansionBudget) -> Self {
        Self { budget, steps: 0 }
    }

    pub(crate) fn charge(&mut self, steps: u128) -> Result<(), WeylError> {
        self.steps = self
            .steps
            .checked_add(steps)
            .filter(|used| *used <= self.budget.max_steps)
            .ok_or(WeylError::StepBudgetExceeded {
                limit: self.budget.max_steps,
            })?;
        Ok(())
    }

    pub(crate) fn ensure_terms(&self, terms: usize) -> Result<(), WeylError> {
        if terms > self.budget.max_terms {
            return Err(WeylError::TermBudgetExceeded {
                limit: self.budget.max_terms,
            });
        }
        Ok(())
    }
}

/// A finite-support PBW Weyl algebra over `S`.
///
/// The context stores the alternating matrix `omega[i][j] = [z_i,z_j]`.
/// `standard_pairs` is only an optimization/layout marker; algebra equality is
/// determined by the commutator form itself.
#[derive(Clone, Debug)]
pub struct WeylAlgebra<S: Scalar> {
    pub(crate) commutator: Vec<Vec<S>>,
    pub(crate) standard_pairs: Option<usize>,
}

impl<S: Scalar> PartialEq for WeylAlgebra<S> {
    fn eq(&self, other: &Self) -> bool {
        self.commutator == other.commutator
    }
}

impl<S: Scalar> WeylAlgebra<S> {
    /// Construct from an alternating commutator matrix
    /// `omega[i][j] = [z_i,z_j]`.
    pub fn from_commutator(commutator: Vec<Vec<S>>) -> Result<Self, WeylError> {
        let dim = commutator.len();
        for (row_index, row) in commutator.iter().enumerate() {
            if row.len() != dim {
                return Err(WeylError::NonSquareCommutator {
                    row: row_index,
                    expected: dim,
                    actual: row.len(),
                });
            }
        }
        for i in 0..dim {
            if !commutator[i][i].is_zero() {
                return Err(WeylError::NonzeroDiagonal { index: i });
            }
            for j in (i + 1)..dim {
                if commutator[i][j] != commutator[j][i].neg() {
                    return Err(WeylError::NotSkewSymmetric { left: i, right: j });
                }
            }
        }
        Ok(Self {
            commutator,
            standard_pairs: None,
        })
    }

    /// Construct from an already validated alternating form.
    pub fn from_symplectic(form: &SymplecticForm<S>) -> Self {
        Self {
            commutator: form.gram().to_vec(),
            standard_pairs: None,
        }
    }

    /// Construct the standard rank-`pairs` Weyl algebra with generator order
    /// `x_0,...,x_(n-1),d_0,...,d_(n-1)` and `[d_i,x_j] = delta_ij`.
    pub fn try_standard(pairs: usize) -> Result<Self, WeylError> {
        let dim = pairs
            .checked_mul(2)
            .ok_or(WeylError::StandardDimensionOverflow)?;
        let mut commutator = vec![vec![S::zero(); dim]; dim];
        for i in 0..pairs {
            commutator[pairs + i][i] = S::one();
            commutator[i][pairs + i] = S::one().neg();
        }
        Ok(Self {
            commutator,
            standard_pairs: Some(pairs),
        })
    }

    /// Construct a standard algebra, panicking only if its host dimension
    /// cannot be represented. Use [`Self::try_standard`] for untrusted ranks.
    pub fn standard(pairs: usize) -> Self {
        Self::try_standard(pairs).expect("standard Weyl generator dimension exceeds usize")
    }

    /// The number of ordered generators.
    pub fn dim(&self) -> usize {
        self.commutator.len()
    }

    /// The number of standard `(x_i,d_i)` pairs, or `None` for a general
    /// alternating presentation.
    pub fn standard_pairs(&self) -> Option<usize> {
        self.standard_pairs
    }

    /// The alternating matrix `omega[i][j] = [z_i,z_j]`.
    pub fn commutator_form(&self) -> &[Vec<S>] {
        &self.commutator
    }

    /// The additive identity.
    pub fn zero(&self) -> WeylElement<S> {
        WeylElement {
            dim: self.dim(),
            terms: BTreeMap::new(),
        }
    }

    /// Embed a scalar as a constant PBW element.
    pub fn scalar(&self, scalar: S) -> WeylElement<S> {
        let mut terms = BTreeMap::new();
        if !scalar.is_zero() {
            terms.insert(WeylMonomial::new(vec![0; self.dim()]), scalar);
        }
        WeylElement {
            dim: self.dim(),
            terms,
        }
    }

    /// The multiplicative identity.
    pub fn one(&self) -> WeylElement<S> {
        self.scalar(S::one())
    }

    /// One ordered generator `z_i`.
    pub fn try_generator(&self, index: usize) -> Result<WeylElement<S>, WeylError> {
        if index >= self.dim() {
            return Err(WeylError::GeneratorOutOfRange {
                index,
                dim: self.dim(),
            });
        }
        let mut exponents = vec![0; self.dim()];
        exponents[index] = 1;
        self.try_monomial(&exponents, S::one())
    }

    /// One ordered generator `z_i`, panicking on an invalid index. Use
    /// [`Self::try_generator`] for untrusted indices.
    pub fn generator(&self, index: usize) -> WeylElement<S> {
        self.try_generator(index)
            .expect("Weyl generator index out of range")
    }

    /// The standard position generator `x_i`.
    pub fn try_x(&self, index: usize) -> Result<WeylElement<S>, WeylError> {
        let pairs = self.standard_pairs.ok_or(WeylError::RequiresStandard)?;
        if index >= pairs {
            return Err(WeylError::GeneratorOutOfRange { index, dim: pairs });
        }
        self.try_generator(index)
    }

    /// The standard position generator `x_i`, panicking outside a standard
    /// presentation or on an invalid pair index.
    pub fn x(&self, index: usize) -> WeylElement<S> {
        self.try_x(index)
            .expect("x(i) requires a valid standard Weyl generator")
    }

    /// The standard differential generator `d_i`.
    pub fn try_d(&self, index: usize) -> Result<WeylElement<S>, WeylError> {
        let pairs = self.standard_pairs.ok_or(WeylError::RequiresStandard)?;
        if index >= pairs {
            return Err(WeylError::GeneratorOutOfRange { index, dim: pairs });
        }
        self.try_generator(pairs + index)
    }

    /// The standard differential generator `d_i`, panicking outside a standard
    /// presentation or on an invalid pair index.
    pub fn d(&self, index: usize) -> WeylElement<S> {
        self.try_d(index)
            .expect("d(i) requires a valid standard Weyl generator")
    }

    /// Construct one PBW monomial with a scalar coefficient.
    pub fn try_monomial(
        &self,
        exponents: &[u128],
        coefficient: S,
    ) -> Result<WeylElement<S>, WeylError> {
        if exponents.len() != self.dim() {
            return Err(WeylError::MonomialDimensionMismatch {
                expected: self.dim(),
                actual: exponents.len(),
            });
        }
        let mut terms = BTreeMap::new();
        if !coefficient.is_zero() {
            terms.insert(WeylMonomial::new(exponents.to_vec()), coefficient);
        }
        Ok(WeylElement {
            dim: self.dim(),
            terms,
        })
    }

    /// Construct one PBW monomial, panicking on a dimension mismatch. Use
    /// [`Self::try_monomial`] for untrusted exponent vectors.
    pub fn monomial(&self, exponents: &[u128], coefficient: S) -> WeylElement<S> {
        self.try_monomial(exponents, coefficient)
            .expect("Weyl monomial exponent vector has the wrong dimension")
    }

    /// Map the commutator presentation through a scalar homomorphism supplied
    /// by the caller. The standard layout marker is preserved.
    pub fn map<T: Scalar>(&self, f: impl Fn(&S) -> T) -> WeylAlgebra<T> {
        WeylAlgebra {
            commutator: self
                .commutator
                .iter()
                .map(|row| row.iter().map(&f).collect())
                .collect(),
            standard_pairs: self.standard_pairs,
        }
    }

    /// Orthogonal direct sum of commutator presentations.
    ///
    /// The generator order is all generators of `self`, followed by all
    /// generators of `other`. Even when both inputs use the optimized standard
    /// layout, this concatenated order is represented as a general alternating
    /// presentation because it is `x,d,x,d`, not the standard `x,x,d,d` order.
    pub fn try_direct_sum(&self, other: &Self) -> Result<Self, WeylError> {
        let left_dim = self.dim();
        let right_dim = other.dim();
        let dim = left_dim
            .checked_add(right_dim)
            .ok_or(WeylError::DirectSumDimensionOverflow)?;
        let mut commutator = vec![vec![S::zero(); dim]; dim];
        for (row, source_row) in self.commutator.iter().enumerate() {
            for (column, coefficient) in source_row.iter().enumerate() {
                commutator[row][column] = coefficient.clone();
            }
        }
        for (row, source_row) in other.commutator.iter().enumerate() {
            for (column, coefficient) in source_row.iter().enumerate() {
                commutator[left_dim + row][left_dim + column] = coefficient.clone();
            }
        }
        Ok(Self {
            commutator,
            standard_pairs: None,
        })
    }

    /// Orthogonal direct sum, panicking only when the host dimension overflows.
    /// Use [`Self::try_direct_sum`] for untrusted dimensions.
    pub fn direct_sum(&self, other: &Self) -> Self {
        self.try_direct_sum(other)
            .expect("direct-sum Weyl generator dimension exceeds usize")
    }

    pub(crate) fn validate_element(&self, element: &WeylElement<S>) -> Result<(), WeylError> {
        if element.dim != self.dim() {
            return Err(WeylError::DimensionMismatch {
                expected: self.dim(),
                actual: element.dim,
            });
        }
        Ok(())
    }

    /// Add two elements after checking their context dimension.
    pub fn add(
        &self,
        left: &WeylElement<S>,
        right: &WeylElement<S>,
    ) -> Result<WeylElement<S>, WeylError> {
        self.validate_element(left)?;
        self.validate_element(right)?;
        let mut terms = left.terms.clone();
        for (monomial, coefficient) in &right.terms {
            add_term(&mut terms, monomial.clone(), coefficient.clone());
        }
        Ok(WeylElement {
            dim: self.dim(),
            terms,
        })
    }

    /// Multiply every coefficient by `scalar`.
    pub fn scalar_mul(
        &self,
        scalar: &S,
        element: &WeylElement<S>,
    ) -> Result<WeylElement<S>, WeylError> {
        self.validate_element(element)?;
        if scalar.is_zero() {
            return Ok(self.zero());
        }
        Ok(WeylElement {
            dim: self.dim(),
            terms: element
                .terms
                .iter()
                .filter_map(|(monomial, coefficient)| {
                    let scaled = scalar.mul(coefficient);
                    (!scaled.is_zero()).then(|| (monomial.clone(), scaled))
                })
                .collect(),
        })
    }

    /// Checked PBW multiplication. This is the authoritative fixed-width path:
    /// exponent overflow is returned rather than wrapped.
    pub fn checked_mul(
        &self,
        left: &WeylElement<S>,
        right: &WeylElement<S>,
    ) -> Result<WeylElement<S>, WeylError> {
        self.checked_mul_with_budget(left, right, WeylExpansionBudget::unbounded())
    }

    /// Checked PBW multiplication under explicit materialization bounds.
    pub fn checked_mul_with_budget(
        &self,
        left: &WeylElement<S>,
        right: &WeylElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<WeylElement<S>, WeylError> {
        self.validate_element(left)?;
        self.validate_element(right)?;
        let mut tracker = ExpansionTracker::new(budget);
        super::product::multiply(self, left, right, &mut tracker)
    }

    /// PBW multiplication, panicking only if the checked fixed-width exponent
    /// boundary is crossed. Use [`Self::checked_mul`] when exponents are
    /// untrusted.
    pub fn mul(&self, left: &WeylElement<S>, right: &WeylElement<S>) -> WeylElement<S> {
        self.checked_mul(left, right)
            .expect("Weyl multiplication exceeds its represented exponent boundary")
    }

    /// Checked square-and-multiply power.
    pub fn checked_pow(
        &self,
        value: &WeylElement<S>,
        exponent: u128,
    ) -> Result<WeylElement<S>, WeylError> {
        self.checked_pow_with_budget(value, exponent, WeylExpansionBudget::unbounded())
    }

    /// Checked square-and-multiply power under one shared expansion budget.
    pub fn checked_pow_with_budget(
        &self,
        value: &WeylElement<S>,
        mut exponent: u128,
        budget: WeylExpansionBudget,
    ) -> Result<WeylElement<S>, WeylError> {
        self.validate_element(value)?;
        let mut tracker = ExpansionTracker::new(budget);
        self.pow_with_tracker(value, &mut exponent, &mut tracker)
    }

    pub(crate) fn pow_with_tracker(
        &self,
        value: &WeylElement<S>,
        exponent: &mut u128,
        tracker: &mut ExpansionTracker,
    ) -> Result<WeylElement<S>, WeylError> {
        let mut accumulator = self.one();
        let mut base = value.clone();
        while *exponent > 0 {
            if *exponent & 1 == 1 {
                accumulator = super::product::multiply(self, &accumulator, &base, tracker)?;
            }
            *exponent >>= 1;
            if *exponent > 0 {
                base = super::product::multiply(self, &base, &base, tracker)?;
            }
        }
        Ok(accumulator)
    }

    /// Power, with the same convenience-boundary policy as [`Self::mul`].
    pub fn pow(&self, value: &WeylElement<S>, exponent: u128) -> WeylElement<S> {
        self.checked_pow(value, exponent)
            .expect("Weyl power exceeds its represented exponent boundary")
    }

    /// The Lie commutator `[left,right] = left*right - right*left`.
    pub fn checked_commutator(
        &self,
        left: &WeylElement<S>,
        right: &WeylElement<S>,
    ) -> Result<WeylElement<S>, WeylError> {
        self.checked_commutator_with_budget(left, right, WeylExpansionBudget::unbounded())
    }

    /// Checked Lie commutator under one shared expansion budget.
    pub fn checked_commutator_with_budget(
        &self,
        left: &WeylElement<S>,
        right: &WeylElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<WeylElement<S>, WeylError> {
        self.validate_element(left)?;
        self.validate_element(right)?;
        let mut tracker = ExpansionTracker::new(budget);
        let lr = super::product::multiply(self, left, right, &mut tracker)?;
        let rl = super::product::multiply(self, right, left, &mut tracker)?;
        let mut terms = lr.terms;
        for (monomial, coefficient) in rl.terms {
            tracker.charge(1)?;
            add_term(&mut terms, monomial, coefficient.neg());
            tracker.ensure_terms(terms.len())?;
        }
        Ok(WeylElement {
            dim: self.dim(),
            terms,
        })
    }

    /// The Lie commutator, with the convenience-boundary policy of [`Self::mul`].
    pub fn commutator(&self, left: &WeylElement<S>, right: &WeylElement<S>) -> WeylElement<S> {
        self.checked_commutator(left, right)
            .expect("Weyl commutator exceeds its represented exponent boundary")
    }

    /// The maximum total PBW degree among nonzero terms; `None` for zero.
    pub fn filtration_degree(&self, element: &WeylElement<S>) -> Result<Option<u128>, WeylError> {
        self.validate_element(element)?;
        element.terms.keys().try_fold(None, |maximum, monomial| {
            let degree = monomial.total_degree().ok_or(WeylError::ExponentOverflow)?;
            Ok(Some(maximum.map_or(degree, |old: u128| old.max(degree))))
        })
    }
}
