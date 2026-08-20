use super::element::{add_term, WeylElement, WeylMonomial};
use crate::forms::SymplecticForm;
use crate::scalar::Scalar;
use std::collections::BTreeMap;
use std::fmt;

/// A checked failure while constructing or operating on a finite-support Weyl
/// algebra.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WeylError {
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
    /// An element or monomial belongs to a different generator dimension.
    DimensionMismatch {
        /// The algebra's generator dimension.
        expected: usize,
        /// The supplied dimension.
        actual: usize,
    },
    /// Adding PBW exponents exceeded the fixed-width `u128` payload.
    ExponentOverflow,
    /// A polynomial action was requested outside the standard rank-one algebra.
    RequiresStandardRankOne,
    /// A PBW `x` exponent cannot be represented as a host polynomial degree.
    PolynomialDegreeOverflow,
}

impl fmt::Display for WeylError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
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
                "Weyl generator dimension mismatch: expected {expected}, got {actual}"
            ),
            Self::ExponentOverflow => formatter.write_str("Weyl PBW exponent exceeds u128"),
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
    pub fn standard(pairs: usize) -> Self {
        let dim = pairs
            .checked_mul(2)
            .expect("standard Weyl generator dimension exceeds usize");
        let mut commutator = vec![vec![S::zero(); dim]; dim];
        for i in 0..pairs {
            commutator[pairs + i][i] = S::one();
            commutator[i][pairs + i] = S::one().neg();
        }
        Self {
            commutator,
            standard_pairs: Some(pairs),
        }
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
    pub fn generator(&self, index: usize) -> WeylElement<S> {
        assert!(index < self.dim(), "Weyl generator index out of range");
        let mut exponents = vec![0; self.dim()];
        exponents[index] = 1;
        self.monomial(&exponents, S::one())
    }

    /// The standard position generator `x_i`.
    pub fn x(&self, index: usize) -> WeylElement<S> {
        let pairs = self
            .standard_pairs
            .expect("x(i) requires a standard Weyl algebra");
        assert!(index < pairs, "Weyl x generator index out of range");
        self.generator(index)
    }

    /// The standard differential generator `d_i`.
    pub fn d(&self, index: usize) -> WeylElement<S> {
        let pairs = self
            .standard_pairs
            .expect("d(i) requires a standard Weyl algebra");
        assert!(index < pairs, "Weyl d generator index out of range");
        self.generator(pairs + index)
    }

    /// Construct one PBW monomial with a scalar coefficient.
    pub fn monomial(&self, exponents: &[u128], coefficient: S) -> WeylElement<S> {
        assert_eq!(
            exponents.len(),
            self.dim(),
            "Weyl monomial exponent vector has the wrong dimension"
        );
        let mut terms = BTreeMap::new();
        if !coefficient.is_zero() {
            terms.insert(WeylMonomial::new(exponents.to_vec()), coefficient);
        }
        WeylElement {
            dim: self.dim(),
            terms,
        }
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
        self.validate_element(left)?;
        self.validate_element(right)?;
        super::product::multiply(self, left, right)
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
        mut exponent: u128,
    ) -> Result<WeylElement<S>, WeylError> {
        self.validate_element(value)?;
        let mut accumulator = self.one();
        let mut base = value.clone();
        while exponent > 0 {
            if exponent & 1 == 1 {
                accumulator = self.checked_mul(&accumulator, &base)?;
            }
            exponent >>= 1;
            if exponent > 0 {
                base = self.checked_mul(&base, &base)?;
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
        let lr = self.checked_mul(left, right)?;
        let rl = self.checked_mul(right, left)?;
        Ok(lr - rl)
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
