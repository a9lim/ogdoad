use super::{WeylAlgebra, WeylElement, WeylError, WeylExpansionBudget, WeylMonomial};
use crate::scalar::{ExactFieldScalar, Scalar};
use std::collections::BTreeMap;
use std::fmt;

/// Caller-supplied materialization limits for finite central fibres and their
/// exact matrix representations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WeylRepresentationBudget {
    /// Maximum dimension of any materialized vector-space basis.
    pub max_basis_dimension: usize,
    /// Maximum total scalar entries in a materialized matrix family or
    /// certificate matrix.
    pub max_matrix_entries: usize,
    /// Maximum charged scalar/matrix work steps.
    pub max_steps: u128,
}

impl WeylRepresentationBudget {
    /// Construct explicit basis, matrix-storage, and work limits.
    pub const fn new(
        max_basis_dimension: usize,
        max_matrix_entries: usize,
        max_steps: u128,
    ) -> Self {
        Self {
            max_basis_dimension,
            max_matrix_entries,
            max_steps,
        }
    }
}

/// Failure while constructing or using a finite central-character fibre.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WeylFiberError {
    /// A checked operation in the ambient PBW algebra failed.
    Weyl(WeylError),
    /// The construction requires the standard `x_0,...,x_n,d_0,...,d_n`
    /// presentation.
    RequiresStandard,
    /// The construction requires a field of positive characteristic.
    RequiresPositiveCharacteristic,
    /// The Clifford bridge requires characteristic two.
    RequiresCharacteristicTwo,
    /// The matrix-algebra certificate requires odd positive characteristic.
    RequiresOddCharacteristic,
    /// The central-character vector has the wrong generator dimension.
    CharacterDimensionMismatch {
        /// Required number of values.
        expected: usize,
        /// Supplied number of values.
        actual: usize,
    },
    /// The splitting-root vector has the wrong generator dimension.
    RootDimensionMismatch {
        /// Required number of roots.
        expected: usize,
        /// Supplied number of roots.
        actual: usize,
    },
    /// A supplied splitting root does not have the advertised characteristic
    /// power.
    RootMismatch {
        /// Standard generator whose root failed verification.
        generator: usize,
    },
    /// A finite basis crossed the caller-supplied dimension limit.
    BasisDimensionLimit {
        /// Required dimension when it fits `u128`.
        required: Option<u128>,
        /// Authorized host dimension.
        limit: usize,
    },
    /// Matrix storage size overflowed the host dimension type.
    MatrixEntryOverflow,
    /// Matrix storage crossed the caller-supplied entry limit.
    MatrixEntryLimit {
        /// Required scalar entries.
        required: usize,
        /// Authorized scalar entries.
        limit: usize,
    },
    /// Matrix evaluation crossed the caller-supplied work limit.
    StepBudgetExceeded {
        /// Authorized charged work steps.
        limit: u128,
    },
    /// A reduced element belongs to a different central fibre.
    FiberContextMismatch,
    /// A reduced element has the wrong dense coefficient length.
    FiberCoefficientDimensionMismatch {
        /// Required fibre dimension.
        expected: usize,
        /// Supplied coefficient length.
        actual: usize,
    },
    /// A reduced PBW basis index lies outside the finite fibre dimension.
    FiberBasisIndexOutOfRange {
        /// Requested zero-based basis index.
        index: usize,
        /// Finite fibre dimension.
        dimension: usize,
    },
    /// The generated module matrices failed a defining Weyl or central
    /// relation.
    ModuleRelationMismatch,
    /// The odd-characteristic fibre action was not full rank.
    MatrixCertificateRankDeficient {
        /// Computed image rank.
        rank: usize,
        /// Required full matrix-algebra dimension.
        expected: usize,
    },
    /// Exact unit-pivot elimination unexpectedly failed on a field-gated
    /// certificate matrix.
    MatrixCertificateEliminationFailed,
    /// The Clifford bridge cannot represent this many generators with its
    /// fixed blade mask.
    CliffordDimensionLimit {
        /// Requested generator dimension.
        dim: usize,
        /// Maximum Clifford generator dimension.
        limit: usize,
    },
    /// A multivector supplied to the Clifford bridge contains a blade outside
    /// the bridged generator dimension.
    CliffordBladeOutOfRange {
        /// Offending blade mask.
        blade: u128,
        /// Bridged generator dimension.
        dim: usize,
    },
}

impl fmt::Display for WeylFiberError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Weyl(error) => write!(formatter, "Weyl fibre operation failed: {error}"),
            Self::RequiresStandard => {
                formatter.write_str("central fibres require a standard Weyl presentation")
            }
            Self::RequiresPositiveCharacteristic => {
                formatter.write_str("central fibres require positive characteristic")
            }
            Self::RequiresCharacteristicTwo => {
                formatter.write_str("the Weyl-Clifford fibre bridge requires characteristic two")
            }
            Self::RequiresOddCharacteristic => formatter
                .write_str("the matrix-algebra fibre certificate requires odd characteristic"),
            Self::CharacterDimensionMismatch { expected, actual } => write!(
                formatter,
                "central character has {actual} values, expected {expected}"
            ),
            Self::RootDimensionMismatch { expected, actual } => write!(
                formatter,
                "central-character splitting data has {actual} roots, expected {expected}"
            ),
            Self::RootMismatch { generator } => write!(
                formatter,
                "splitting root for Weyl generator {generator} has the wrong characteristic power"
            ),
            Self::BasisDimensionLimit { required, limit } => match required {
                Some(required) => write!(
                    formatter,
                    "central-fibre basis dimension {required} exceeds limit {limit}"
                ),
                None => write!(
                    formatter,
                    "central-fibre basis dimension exceeds u128 and limit {limit}"
                ),
            },
            Self::MatrixEntryOverflow => {
                formatter.write_str("central-fibre matrix storage exceeds usize")
            }
            Self::MatrixEntryLimit { required, limit } => write!(
                formatter,
                "central-fibre matrix storage needs {required} entries, above limit {limit}"
            ),
            Self::StepBudgetExceeded { limit } => write!(
                formatter,
                "central-fibre matrix evaluation exceeds its {limit}-step budget"
            ),
            Self::FiberContextMismatch => {
                formatter.write_str("central-fibre elements belong to different characters")
            }
            Self::FiberCoefficientDimensionMismatch { expected, actual } => write!(
                formatter,
                "central-fibre element has {actual} coefficients, expected {expected}"
            ),
            Self::FiberBasisIndexOutOfRange { index, dimension } => write!(
                formatter,
                "central-fibre basis index {index} is outside dimension {dimension}"
            ),
            Self::ModuleRelationMismatch => {
                formatter.write_str("central-character module fails a defining relation")
            }
            Self::MatrixCertificateRankDeficient { rank, expected } => write!(
                formatter,
                "central-fibre matrix image has rank {rank}, expected {expected}"
            ),
            Self::MatrixCertificateEliminationFailed => formatter.write_str(
                "unit-pivot elimination failed while certifying the central-fibre matrix image",
            ),
            Self::CliffordDimensionLimit { dim, limit } => write!(
                formatter,
                "Weyl-Clifford fibre dimension {dim} exceeds blade limit {limit}"
            ),
            Self::CliffordBladeOutOfRange { blade, dim } => write!(
                formatter,
                "Clifford blade mask {blade} has a generator outside dimension {dim}"
            ),
        }
    }
}

impl std::error::Error for WeylFiberError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Weyl(error) => Some(error),
            _ => None,
        }
    }
}

impl From<WeylError> for WeylFiberError {
    fn from(error: WeylError) -> Self {
        Self::Weyl(error)
    }
}

#[derive(Debug)]
struct RepresentationTracker {
    limit: u128,
    steps: u128,
}

impl RepresentationTracker {
    fn new(limit: u128) -> Self {
        Self { limit, steps: 0 }
    }

    fn charge(&mut self, steps: u128) -> Result<(), WeylFiberError> {
        self.steps = self
            .steps
            .checked_add(steps)
            .filter(|used| *used <= self.limit)
            .ok_or(WeylFiberError::StepBudgetExceeded { limit: self.limit })?;
        Ok(())
    }
}

/// A dense element of the finite quotient obtained by fixing every
/// characteristic-power central generator in a standard Weyl algebra.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylCentralFiberElement<S: ExactFieldScalar> {
    characteristic: u128,
    generator_dim: usize,
    central_values: Vec<S>,
    coefficients: Vec<S>,
}

impl<S: ExactFieldScalar> WeylCentralFiberElement<S> {
    /// Dense coefficients in little-endian base-`p` PBW basis order.
    pub fn coefficients(&self) -> &[S] {
        &self.coefficients
    }

    /// Whether every reduced coefficient is zero.
    pub fn is_zero(&self) -> bool {
        self.coefficients.iter().all(Scalar::is_zero)
    }
}

/// Bounded central fibre
///
/// ```text
/// A_n / (z_i^p - chi_i),
/// ```
///
/// represented on the PBW basis `0 <= exponent_i < p`. Construction is
/// field-gated and requires the standard nondegenerate presentation.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylCentralFiber<S: ExactFieldScalar> {
    algebra: WeylAlgebra<S>,
    characteristic: u128,
    central_values: Vec<S>,
    basis_dimension: usize,
}

impl<S: ExactFieldScalar> WeylCentralFiber<S> {
    /// Construct a bounded standard central fibre. Values are ordered as all
    /// `x_i^p`, followed by all `d_i^p`.
    pub fn try_new(
        algebra: &WeylAlgebra<S>,
        central_values: Vec<S>,
        budget: WeylRepresentationBudget,
    ) -> Result<Self, WeylFiberError> {
        algebra
            .standard_pairs()
            .ok_or(WeylFiberError::RequiresStandard)?;
        let characteristic = S::characteristic();
        if characteristic == 0 {
            return Err(WeylFiberError::RequiresPositiveCharacteristic);
        }
        if central_values.len() != algebra.dim() {
            return Err(WeylFiberError::CharacterDimensionMismatch {
                expected: algebra.dim(),
                actual: central_values.len(),
            });
        }
        let basis_dimension =
            bounded_basis_dimension(characteristic, algebra.dim(), budget.max_basis_dimension)?;
        Ok(Self {
            algebra: algebra.clone(),
            characteristic,
            central_values,
            basis_dimension,
        })
    }

    /// Ambient standard Weyl algebra.
    pub fn algebra(&self) -> &WeylAlgebra<S> {
        &self.algebra
    }

    /// Positive field characteristic.
    pub fn characteristic(&self) -> u128 {
        self.characteristic
    }

    /// Values of `z_i^p` in standard generator order.
    pub fn central_values(&self) -> &[S] {
        &self.central_values
    }

    /// Vector-space dimension `p^(2n)` of the finite fibre.
    pub fn basis_dimension(&self) -> usize {
        self.basis_dimension
    }

    /// Additive identity of this fibre.
    pub fn zero(&self) -> WeylCentralFiberElement<S> {
        self.element_from_coefficients(vec![S::zero(); self.basis_dimension])
            .expect("fresh zero coefficients have the fibre dimension")
    }

    /// Multiplicative identity of this fibre.
    pub fn one(&self) -> WeylCentralFiberElement<S> {
        let mut coefficients = vec![S::zero(); self.basis_dimension];
        coefficients[0] = S::one();
        self.element_from_coefficients(coefficients)
            .expect("fresh identity coefficients have the fibre dimension")
    }

    /// One reduced PBW basis element by little-endian base-`p` index.
    pub fn basis_element(
        &self,
        index: usize,
    ) -> Result<WeylCentralFiberElement<S>, WeylFiberError> {
        if index >= self.basis_dimension {
            return Err(WeylFiberError::FiberBasisIndexOutOfRange {
                index,
                dimension: self.basis_dimension,
            });
        }
        let mut coefficients = vec![S::zero(); self.basis_dimension];
        coefficients[index] = S::one();
        self.element_from_coefficients(coefficients)
    }

    /// Reduced image of one standard Weyl generator.
    pub fn generator(&self, index: usize) -> Result<WeylCentralFiberElement<S>, WeylFiberError> {
        self.reduce(&self.algebra.try_generator(index)?)
    }

    /// Construct a checked dense fibre element.
    pub fn element_from_coefficients(
        &self,
        coefficients: Vec<S>,
    ) -> Result<WeylCentralFiberElement<S>, WeylFiberError> {
        if coefficients.len() != self.basis_dimension {
            return Err(WeylFiberError::FiberCoefficientDimensionMismatch {
                expected: self.basis_dimension,
                actual: coefficients.len(),
            });
        }
        Ok(WeylCentralFiberElement {
            characteristic: self.characteristic,
            generator_dim: self.algebra.dim(),
            central_values: self.central_values.clone(),
            coefficients,
        })
    }

    /// Reduce a finite PBW element using `z_i^p = chi_i`.
    pub fn reduce(
        &self,
        element: &WeylElement<S>,
    ) -> Result<WeylCentralFiberElement<S>, WeylFiberError> {
        self.algebra.validate_element(element)?;
        let mut coefficients = vec![S::zero(); self.basis_dimension];
        for (monomial, coefficient) in element.terms() {
            let mut reduced_coefficient = coefficient.clone();
            let mut index = 0usize;
            let mut stride = 1usize;
            for (generator, exponent) in monomial.exponents().iter().copied().enumerate() {
                let quotient = exponent / self.characteristic;
                let remainder = exponent % self.characteristic;
                reduced_coefficient =
                    reduced_coefficient.mul(&self.central_values[generator].pow(quotient));
                let digit = usize::try_from(remainder)
                    .expect("a represented fibre dimension forces base-p digits into usize");
                index += digit * stride;
                stride *= usize::try_from(self.characteristic)
                    .expect("a represented fibre dimension forces p into usize");
            }
            coefficients[index] = coefficients[index].add(&reduced_coefficient);
        }
        self.element_from_coefficients(coefficients)
    }

    /// Lift a reduced element to its canonical PBW representative with all
    /// exponents below the characteristic.
    pub fn lift(
        &self,
        element: &WeylCentralFiberElement<S>,
    ) -> Result<WeylElement<S>, WeylFiberError> {
        self.validate_element(element)?;
        let mut terms = BTreeMap::new();
        for (index, coefficient) in element.coefficients.iter().enumerate() {
            if coefficient.is_zero() {
                continue;
            }
            terms.insert(
                WeylMonomial::new(decode_index(index, self.characteristic, self.algebra.dim())),
                coefficient.clone(),
            );
        }
        Ok(WeylElement {
            dim: self.algebra.dim(),
            terms,
        })
    }

    /// Multiply two reduced fibre elements through the independently checked
    /// ambient PBW product and central reduction.
    pub fn checked_mul_with_budget(
        &self,
        left: &WeylCentralFiberElement<S>,
        right: &WeylCentralFiberElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<WeylCentralFiberElement<S>, WeylFiberError> {
        let left = self.lift(left)?;
        let right = self.lift(right)?;
        let product = self
            .algebra
            .checked_mul_with_budget(&left, &right, budget)?;
        self.reduce(&product)
    }

    /// Multiply two reduced fibre elements without a finite PBW expansion cap.
    pub fn checked_mul(
        &self,
        left: &WeylCentralFiberElement<S>,
        right: &WeylCentralFiberElement<S>,
    ) -> Result<WeylCentralFiberElement<S>, WeylFiberError> {
        self.checked_mul_with_budget(left, right, WeylExpansionBudget::unbounded())
    }

    fn validate_element(&self, element: &WeylCentralFiberElement<S>) -> Result<(), WeylFiberError> {
        if element.characteristic != self.characteristic
            || element.generator_dim != self.algebra.dim()
            || element.central_values != self.central_values
        {
            return Err(WeylFiberError::FiberContextMismatch);
        }
        if element.coefficients.len() != self.basis_dimension {
            return Err(WeylFiberError::FiberCoefficientDimensionMismatch {
                expected: self.basis_dimension,
                actual: element.coefficients.len(),
            });
        }
        Ok(())
    }
}

/// Exact split central-character module on truncated polynomials
/// `S[t_0,...,t_(n-1)]/(t_i^p)`.
///
/// Supplied roots `alpha_i`, `beta_i` are verified against the advertised
/// central values. Then `x_i = alpha_i + t_i` and
/// `d_i = beta_i + partial_i`, giving a `p^n`-dimensional representation.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylCentralCharacterModule<S: ExactFieldScalar> {
    algebra: WeylAlgebra<S>,
    characteristic: u128,
    central_values: Vec<S>,
    splitting_roots: Vec<S>,
    basis_dimension: usize,
    generator_matrices: Vec<Vec<Vec<S>>>,
}

impl<S: ExactFieldScalar> WeylCentralCharacterModule<S> {
    /// Construct and certify the split module. Values and roots use standard
    /// generator order: all positions, then all momenta.
    pub fn try_new(
        algebra: &WeylAlgebra<S>,
        central_values: Vec<S>,
        splitting_roots: Vec<S>,
        budget: WeylRepresentationBudget,
    ) -> Result<Self, WeylFiberError> {
        let mut tracker = RepresentationTracker::new(budget.max_steps);
        Self::try_new_with_tracker(
            algebra,
            central_values,
            splitting_roots,
            budget,
            &mut tracker,
        )
    }

    fn try_new_with_tracker(
        algebra: &WeylAlgebra<S>,
        central_values: Vec<S>,
        splitting_roots: Vec<S>,
        budget: WeylRepresentationBudget,
        tracker: &mut RepresentationTracker,
    ) -> Result<Self, WeylFiberError> {
        let pairs = algebra
            .standard_pairs()
            .ok_or(WeylFiberError::RequiresStandard)?;
        let characteristic = S::characteristic();
        if characteristic == 0 {
            return Err(WeylFiberError::RequiresPositiveCharacteristic);
        }
        if central_values.len() != algebra.dim() {
            return Err(WeylFiberError::CharacterDimensionMismatch {
                expected: algebra.dim(),
                actual: central_values.len(),
            });
        }
        if splitting_roots.len() != algebra.dim() {
            return Err(WeylFiberError::RootDimensionMismatch {
                expected: algebra.dim(),
                actual: splitting_roots.len(),
            });
        }
        for generator in 0..algebra.dim() {
            if splitting_roots[generator].pow(characteristic) != central_values[generator] {
                return Err(WeylFiberError::RootMismatch { generator });
            }
        }
        let basis_dimension =
            bounded_basis_dimension(characteristic, pairs, budget.max_basis_dimension)?;
        require_matrix_entries(
            algebra
                .dim()
                .checked_mul(basis_dimension)
                .and_then(|entries| entries.checked_mul(basis_dimension))
                .ok_or(WeylFiberError::MatrixEntryOverflow)?,
            budget.max_matrix_entries,
        )?;
        let generator_matrices =
            module_generator_matrices(pairs, characteristic, basis_dimension, &splitting_roots);
        let module = Self {
            algebra: algebra.clone(),
            characteristic,
            central_values,
            splitting_roots,
            basis_dimension,
            generator_matrices,
        };
        if !module.verifies_defining_relations_with_tracker(tracker)? {
            return Err(WeylFiberError::ModuleRelationMismatch);
        }
        Ok(module)
    }

    /// Ambient standard Weyl algebra.
    pub fn algebra(&self) -> &WeylAlgebra<S> {
        &self.algebra
    }

    /// Positive field characteristic.
    pub fn characteristic(&self) -> u128 {
        self.characteristic
    }

    /// Values of every `z_i^p` in standard generator order.
    pub fn central_values(&self) -> &[S] {
        &self.central_values
    }

    /// Verified characteristic roots used to split the central character.
    pub fn splitting_roots(&self) -> &[S] {
        &self.splitting_roots
    }

    /// Module dimension `p^n`.
    pub fn basis_dimension(&self) -> usize {
        self.basis_dimension
    }

    /// Truncated-polynomial exponent vector at one module basis index.
    pub fn basis_exponents(&self, index: usize) -> Option<Vec<u128>> {
        (index < self.basis_dimension).then(|| {
            decode_index(
                index,
                self.characteristic,
                self.algebra.standard_pairs().expect("module is standard"),
            )
        })
    }

    /// Exact row-major generator action matrices. Matrix columns are images of
    /// basis vectors.
    pub fn generator_matrices(&self) -> &[Vec<Vec<S>>] {
        &self.generator_matrices
    }

    /// Evaluate one PBW element as an exact module action matrix under the
    /// supplied storage and work limits.
    pub fn action_matrix(
        &self,
        element: &WeylElement<S>,
        budget: WeylRepresentationBudget,
    ) -> Result<Vec<Vec<S>>, WeylFiberError> {
        self.algebra.validate_element(element)?;
        require_matrix_entries(
            self.basis_dimension
                .checked_mul(self.basis_dimension)
                .ok_or(WeylFiberError::MatrixEntryOverflow)?,
            budget.max_matrix_entries,
        )?;
        let mut tracker = RepresentationTracker::new(budget.max_steps);
        self.action_matrix_with_tracker(element, &mut tracker)
    }

    /// Independently verify all generator commutators and characteristic powers
    /// against the advertised central character.
    pub fn verifies_defining_relations(
        &self,
        budget: WeylRepresentationBudget,
    ) -> Result<bool, WeylFiberError> {
        let matrix_entries = self
            .basis_dimension
            .checked_mul(self.basis_dimension)
            .ok_or(WeylFiberError::MatrixEntryOverflow)?;
        require_matrix_entries(matrix_entries, budget.max_matrix_entries)?;
        let mut tracker = RepresentationTracker::new(budget.max_steps);
        self.verifies_defining_relations_with_tracker(&mut tracker)
    }

    fn verifies_defining_relations_with_tracker(
        &self,
        tracker: &mut RepresentationTracker,
    ) -> Result<bool, WeylFiberError> {
        let identity = identity_matrix::<S>(self.basis_dimension);
        for generator in 0..self.algebra.dim() {
            let power = matrix_pow(
                &self.generator_matrices[generator],
                self.characteristic,
                tracker,
            )?;
            if power != matrix_scale(&identity, &self.central_values[generator]) {
                return Ok(false);
            }
        }
        for left in 0..self.algebra.dim() {
            for right in 0..self.algebra.dim() {
                let lr = matrix_mul(
                    &self.generator_matrices[left],
                    &self.generator_matrices[right],
                    tracker,
                )?;
                let rl = matrix_mul(
                    &self.generator_matrices[right],
                    &self.generator_matrices[left],
                    tracker,
                )?;
                let commutator = matrix_sub(&lr, &rl);
                let expected =
                    matrix_scale(&identity, &self.algebra.commutator_form()[left][right]);
                if commutator != expected {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    fn action_matrix_with_tracker(
        &self,
        element: &WeylElement<S>,
        tracker: &mut RepresentationTracker,
    ) -> Result<Vec<Vec<S>>, WeylFiberError> {
        let mut output = zero_matrix::<S>(self.basis_dimension);
        let identity = identity_matrix::<S>(self.basis_dimension);
        for (monomial, coefficient) in element.terms() {
            let mut scalar = coefficient.clone();
            let mut image = identity.clone();
            for generator in 0..self.algebra.dim() {
                let exponent = monomial.exponents()[generator];
                let quotient = exponent / self.characteristic;
                let remainder = exponent % self.characteristic;
                scalar = scalar.mul(&self.central_values[generator].pow(quotient));
                if remainder != 0 {
                    let power =
                        matrix_pow(&self.generator_matrices[generator], remainder, tracker)?;
                    image = matrix_mul(&image, &power, tracker)?;
                }
            }
            tracker.charge(
                u128::try_from(self.basis_dimension)
                    .ok()
                    .and_then(|dim| dim.checked_mul(dim))
                    .ok_or(WeylFiberError::StepBudgetExceeded {
                        limit: tracker.limit,
                    })?,
            )?;
            matrix_add_scaled_in_place(&mut output, &image, &scalar);
        }
        Ok(output)
    }
}

/// Exact certificate that a supported split odd-characteristic central fibre
/// acts as the full matrix algebra on its `p^n`-dimensional module.
#[derive(Clone, Debug, PartialEq)]
pub struct OddWeylMatrixFiberCertificate<S: ExactFieldScalar> {
    fiber: WeylCentralFiber<S>,
    module: WeylCentralCharacterModule<S>,
    image_rank: usize,
}

impl<S: ExactFieldScalar> OddWeylMatrixFiberCertificate<S> {
    /// Certified finite central fibre.
    pub fn fiber(&self) -> &WeylCentralFiber<S> {
        &self.fiber
    }

    /// Exact splitting module whose action supplies the matrix map.
    pub fn module(&self) -> &WeylCentralCharacterModule<S> {
        &self.module
    }

    /// Rank of the flattened images of the reduced PBW basis.
    pub fn image_rank(&self) -> usize {
        self.image_rank
    }

    /// Matrix size `p^n`.
    pub fn matrix_dimension(&self) -> usize {
        self.module.basis_dimension()
    }

    /// Dimension `p^(2n)` of both the fibre and the full matrix algebra.
    pub fn algebra_dimension(&self) -> usize {
        self.fiber.basis_dimension()
    }
}

impl<S: ExactFieldScalar> WeylAlgebra<S> {
    /// Construct a bounded central fibre with values in standard generator
    /// order.
    pub fn central_fiber(
        &self,
        central_values: Vec<S>,
        budget: WeylRepresentationBudget,
    ) -> Result<WeylCentralFiber<S>, WeylFiberError> {
        WeylCentralFiber::try_new(self, central_values, budget)
    }

    /// Construct a certified split central-character module.
    pub fn split_central_character_module(
        &self,
        central_values: Vec<S>,
        splitting_roots: Vec<S>,
        budget: WeylRepresentationBudget,
    ) -> Result<WeylCentralCharacterModule<S>, WeylFiberError> {
        WeylCentralCharacterModule::try_new(self, central_values, splitting_roots, budget)
    }

    /// Certify a supported split odd-characteristic central fibre as a full
    /// matrix algebra by exact rank of all reduced PBW basis images.
    pub fn odd_matrix_fiber_certificate(
        &self,
        central_values: Vec<S>,
        splitting_roots: Vec<S>,
        budget: WeylRepresentationBudget,
    ) -> Result<OddWeylMatrixFiberCertificate<S>, WeylFiberError> {
        let characteristic = S::characteristic();
        if characteristic == 0 || characteristic == 2 {
            return Err(WeylFiberError::RequiresOddCharacteristic);
        }
        let mut tracker = RepresentationTracker::new(budget.max_steps);
        let module = WeylCentralCharacterModule::try_new_with_tracker(
            self,
            central_values.clone(),
            splitting_roots,
            budget,
            &mut tracker,
        )?;
        let fiber = self.central_fiber(central_values, budget)?;
        let matrix_dimension = module.basis_dimension();
        let algebra_dimension = matrix_dimension
            .checked_mul(matrix_dimension)
            .ok_or(WeylFiberError::MatrixEntryOverflow)?;
        if fiber.basis_dimension() != algebra_dimension {
            return Err(WeylFiberError::ModuleRelationMismatch);
        }
        let certificate_entries = algebra_dimension
            .checked_mul(algebra_dimension)
            .ok_or(WeylFiberError::MatrixEntryOverflow)?;
        require_matrix_entries(certificate_entries, budget.max_matrix_entries)?;
        let mut flattened_images = Vec::with_capacity(algebra_dimension);
        for index in 0..algebra_dimension {
            let representative = fiber.lift(&fiber.basis_element(index)?)?;
            let matrix = module.action_matrix_with_tracker(&representative, &mut tracker)?;
            flattened_images.push(matrix.into_iter().flatten().collect());
        }
        let elimination_steps = u128::try_from(algebra_dimension)
            .ok()
            .and_then(|dimension| dimension.checked_pow(3))
            .ok_or(WeylFiberError::StepBudgetExceeded {
                limit: budget.max_steps,
            })?;
        tracker.charge(elimination_steps)?;
        let image_rank = crate::linalg::field::unit_pivot_rank(flattened_images)
            .ok_or(WeylFiberError::MatrixCertificateEliminationFailed)?;
        if image_rank != algebra_dimension {
            return Err(WeylFiberError::MatrixCertificateRankDeficient {
                rank: image_rank,
                expected: algebra_dimension,
            });
        }
        Ok(OddWeylMatrixFiberCertificate {
            fiber,
            module,
            image_rank,
        })
    }
}

fn bounded_basis_dimension(
    characteristic: u128,
    exponent: usize,
    limit: usize,
) -> Result<usize, WeylFiberError> {
    let dimension =
        (0..exponent).try_fold(1u128, |dimension, _| dimension.checked_mul(characteristic));
    let Some(dimension) = dimension else {
        return Err(WeylFiberError::BasisDimensionLimit {
            required: None,
            limit,
        });
    };
    let dimension_usize =
        usize::try_from(dimension).map_err(|_| WeylFiberError::BasisDimensionLimit {
            required: Some(dimension),
            limit,
        })?;
    if dimension_usize > limit {
        return Err(WeylFiberError::BasisDimensionLimit {
            required: Some(dimension),
            limit,
        });
    }
    Ok(dimension_usize)
}

fn require_matrix_entries(required: usize, limit: usize) -> Result<(), WeylFiberError> {
    if required > limit {
        return Err(WeylFiberError::MatrixEntryLimit { required, limit });
    }
    Ok(())
}

fn decode_index(mut index: usize, characteristic: u128, digits: usize) -> Vec<u128> {
    if digits == 0 {
        return Vec::new();
    }
    let base = usize::try_from(characteristic)
        .expect("a materialized characteristic-power basis forces p into usize");
    (0..digits)
        .map(|_| {
            let digit = index % base;
            index /= base;
            digit as u128
        })
        .collect()
}

fn module_generator_matrices<S: Scalar>(
    pairs: usize,
    characteristic: u128,
    basis_dimension: usize,
    roots: &[S],
) -> Vec<Vec<Vec<S>>> {
    if pairs == 0 {
        return Vec::new();
    }
    let base = usize::try_from(characteristic)
        .expect("a materialized characteristic-power basis forces p into usize");
    let mut matrices = vec![zero_matrix::<S>(basis_dimension); 2 * pairs];
    let mut stride = 1usize;
    for variable in 0..pairs {
        for column in 0..basis_dimension {
            let degree = (column / stride) % base;
            matrices[variable][column][column] =
                matrices[variable][column][column].add(&roots[variable]);
            if degree + 1 < base {
                let row = column + stride;
                matrices[variable][row][column] = matrices[variable][row][column].add(&S::one());
            }

            let differential = pairs + variable;
            matrices[differential][column][column] =
                matrices[differential][column][column].add(&roots[differential]);
            if degree > 0 {
                let row = column - stride;
                matrices[differential][row][column] = matrices[differential][row][column]
                    .add(&super::product::embed_nat::<S>(degree as u128));
            }
        }
        stride *= base;
    }
    matrices
}

fn zero_matrix<S: Scalar>(dimension: usize) -> Vec<Vec<S>> {
    vec![vec![S::zero(); dimension]; dimension]
}

fn identity_matrix<S: Scalar>(dimension: usize) -> Vec<Vec<S>> {
    let mut matrix = zero_matrix::<S>(dimension);
    for index in 0..dimension {
        matrix[index][index] = S::one();
    }
    matrix
}

fn matrix_scale<S: Scalar>(matrix: &[Vec<S>], scalar: &S) -> Vec<Vec<S>> {
    matrix
        .iter()
        .map(|row| row.iter().map(|entry| entry.mul(scalar)).collect())
        .collect()
}

fn matrix_add_scaled_in_place<S: Scalar>(target: &mut [Vec<S>], source: &[Vec<S>], scalar: &S) {
    for row in 0..target.len() {
        for column in 0..target.len() {
            target[row][column] = target[row][column].add(&source[row][column].mul(scalar));
        }
    }
}

fn matrix_sub<S: Scalar>(left: &[Vec<S>], right: &[Vec<S>]) -> Vec<Vec<S>> {
    (0..left.len())
        .map(|row| {
            (0..left.len())
                .map(|column| left[row][column].sub(&right[row][column]))
                .collect()
        })
        .collect()
}

fn matrix_mul<S: Scalar>(
    left: &[Vec<S>],
    right: &[Vec<S>],
    tracker: &mut RepresentationTracker,
) -> Result<Vec<Vec<S>>, WeylFiberError> {
    let dimension = left.len();
    let work = u128::try_from(dimension)
        .ok()
        .and_then(|dimension| dimension.checked_pow(3))
        .ok_or(WeylFiberError::StepBudgetExceeded {
            limit: tracker.limit,
        })?;
    tracker.charge(work)?;
    let mut product = zero_matrix::<S>(dimension);
    for row in 0..dimension {
        for column in 0..dimension {
            for inner in 0..dimension {
                product[row][column] =
                    product[row][column].add(&left[row][inner].mul(&right[inner][column]));
            }
        }
    }
    Ok(product)
}

fn matrix_pow<S: Scalar>(
    matrix: &[Vec<S>],
    mut exponent: u128,
    tracker: &mut RepresentationTracker,
) -> Result<Vec<Vec<S>>, WeylFiberError> {
    let mut accumulator = identity_matrix::<S>(matrix.len());
    if exponent == 0 {
        return Ok(accumulator);
    }
    let mut base = matrix.to_vec();
    while exponent > 0 {
        if exponent & 1 == 1 {
            accumulator = matrix_mul(&accumulator, &base, tracker)?;
        }
        exponent >>= 1;
        if exponent > 0 {
            base = matrix_mul(&base, &base, tracker)?;
        }
    }
    Ok(accumulator)
}
