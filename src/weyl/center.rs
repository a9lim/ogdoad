use super::{
    WeylAlgebra, WeylDarbouxDecomposition, WeylDarbouxError, WeylElement, WeylError,
    WeylExpansionBudget,
};
use crate::scalar::{ExactFieldScalar, Scalar};
use std::fmt;

/// Failure while describing or materializing the centre of a Weyl algebra.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WeylCenterError {
    /// Darboux reduction or coordinate transport failed.
    Darboux(WeylDarbouxError),
    /// A checked Weyl operation failed.
    Weyl(WeylError),
    /// The characteristic-`p` centre was requested in characteristic zero.
    RequiresPositiveCharacteristic,
    /// The requested basis index lies past the represented finite rank.
    BasisIndexOutOfRange {
        /// Requested zero-based basis index.
        index: u128,
        /// Rank of the Weyl algebra as a module over its centre.
        rank: u128,
    },
    /// A complete basis was requested with a smaller caller-supplied cap.
    BasisMaterializationLimit {
        /// Required number of basis elements when representable as `u128`.
        required: Option<u128>,
        /// Maximum number of elements authorized by the caller.
        limit: usize,
    },
    /// A theoretically central generator failed the independent commutator
    /// check.
    CentralityCertificateMismatch {
        /// Index in the returned centre-generator list.
        generator: usize,
    },
}

impl fmt::Display for WeylCenterError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Darboux(error) => {
                write!(formatter, "Weyl centre Darboux reduction failed: {error}")
            }
            Self::Weyl(error) => write!(formatter, "Weyl centre operation failed: {error}"),
            Self::RequiresPositiveCharacteristic => formatter
                .write_str("the characteristic-p Weyl centre requires positive characteristic"),
            Self::BasisIndexOutOfRange { index, rank } => {
                write!(
                    formatter,
                    "centre-basis index {index} is outside rank {rank}"
                )
            }
            Self::BasisMaterializationLimit { required, limit } => match required {
                Some(required) => write!(
                    formatter,
                    "materializing the centre basis needs {required} elements, above limit {limit}"
                ),
                None => write!(
                    formatter,
                    "the centre-basis rank exceeds u128 and cannot fit limit {limit}"
                ),
            },
            Self::CentralityCertificateMismatch { generator } => write!(
                formatter,
                "reported Weyl centre generator {generator} does not commute with every generator"
            ),
        }
    }
}

impl std::error::Error for WeylCenterError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Darboux(error) => Some(error),
            Self::Weyl(error) => Some(error),
            _ => None,
        }
    }
}

impl From<WeylDarbouxError> for WeylCenterError {
    fn from(error: WeylDarbouxError) -> Self {
        Self::Darboux(error)
    }
}

impl From<WeylError> for WeylCenterError {
    fn from(error: WeylError) -> Self {
        Self::Weyl(error)
    }
}

/// The mathematical source of a reported central generator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WeylCenterGeneratorKind {
    /// The characteristic power of a noncommutative Darboux generator.
    CharacteristicPower {
        /// Generator index in the Darboux presentation.
        normal_generator: usize,
        /// Positive field characteristic used as the exponent.
        characteristic: u128,
    },
    /// A linear generator spanning the radical of the commutator form.
    Radical {
        /// Index in the certified radical basis.
        radical_index: usize,
        /// Generator index in the Darboux presentation.
        normal_generator: usize,
    },
}

/// One independently checked generator of a characteristic-`p` Weyl centre.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylCenterGenerator<S: Scalar> {
    kind: WeylCenterGeneratorKind,
    normal_element: WeylElement<S>,
    source_element: WeylElement<S>,
}

impl<S: Scalar> WeylCenterGenerator<S> {
    /// Why this element belongs to the centre.
    pub fn kind(&self) -> &WeylCenterGeneratorKind {
        &self.kind
    }

    /// Generator in Darboux-plus-radical coordinates.
    pub fn normal_element(&self) -> &WeylElement<S> {
        &self.normal_element
    }

    /// The same generator transported to the original Weyl presentation.
    pub fn source_element(&self) -> &WeylElement<S> {
        &self.source_element
    }
}

/// Lazy PBW basis of a positive-characteristic Weyl algebra over its centre.
///
/// In Darboux coordinates the radical variables already lie in the centre, and
/// every paired exponent is reduced to `0 <= exponent < p`. Basis index digits
/// are little-endian base `p` in the paired generator order. The exact rank is
/// `p^(2r)` when that integer fits `u128`; individual `u128` indices remain
/// usable even when the mathematical rank is larger.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylCenterBasis<S: ExactFieldScalar> {
    decomposition: WeylDarbouxDecomposition<S>,
    characteristic: u128,
    paired_generators: usize,
    rank: Option<u128>,
}

impl<S: ExactFieldScalar> WeylCenterBasis<S> {
    /// Positive field characteristic bounding every paired PBW exponent.
    pub fn characteristic(&self) -> u128 {
        self.characteristic
    }

    /// Number of noncentral Darboux generators whose reduced exponents index
    /// the basis.
    pub fn paired_generators(&self) -> usize {
        self.paired_generators
    }

    /// Exact module rank `p^(2r)`, or `None` when it exceeds `u128`.
    pub fn rank_over_center(&self) -> Option<u128> {
        self.rank
    }

    /// Return a PBW basis monomial in Darboux coordinates by lazy base-`p`
    /// index.
    pub fn normal_element_at(&self, index: u128) -> Result<WeylElement<S>, WeylCenterError> {
        if let Some(rank) = self.rank {
            if index >= rank {
                return Err(WeylCenterError::BasisIndexOutOfRange { index, rank });
            }
        }
        let mut remaining = index;
        let mut exponents = vec![0; self.decomposition.normal_algebra().dim()];
        for exponent in exponents.iter_mut().take(self.paired_generators) {
            *exponent = remaining % self.characteristic;
            remaining /= self.characteristic;
        }
        // If rank overflowed u128, every represented index is necessarily below
        // the mathematical rank. Otherwise the range check above consumed all
        // digits.
        self.decomposition
            .normal_algebra()
            .try_monomial(&exponents, S::one())
            .map_err(Into::into)
    }

    /// Transport one lazy centre-basis element into the original presentation.
    pub fn source_element_at_with_budget(
        &self,
        index: u128,
        budget: WeylExpansionBudget,
    ) -> Result<WeylElement<S>, WeylCenterError> {
        let normal = self.normal_element_at(index)?;
        self.decomposition
            .from_normal_with_budget(&normal, budget)
            .map_err(Into::into)
    }

    /// Transport one lazy centre-basis element without a finite expansion cap.
    pub fn source_element_at(&self, index: u128) -> Result<WeylElement<S>, WeylCenterError> {
        self.source_element_at_with_budget(index, WeylExpansionBudget::unbounded())
    }

    /// Materialize the complete source-coordinate basis when it fits both the
    /// represented rank and the caller's element cap. The expansion budget is
    /// applied independently to each coordinate transport.
    pub fn materialize_source_with_budget(
        &self,
        max_elements: usize,
        expansion_budget: WeylExpansionBudget,
    ) -> Result<Vec<WeylElement<S>>, WeylCenterError> {
        let Some(rank) = self.rank else {
            return Err(WeylCenterError::BasisMaterializationLimit {
                required: None,
                limit: max_elements,
            });
        };
        let rank_usize =
            usize::try_from(rank).map_err(|_| WeylCenterError::BasisMaterializationLimit {
                required: Some(rank),
                limit: max_elements,
            })?;
        if rank_usize > max_elements {
            return Err(WeylCenterError::BasisMaterializationLimit {
                required: Some(rank),
                limit: max_elements,
            });
        }
        (0..rank)
            .map(|index| self.source_element_at_with_budget(index, expansion_budget))
            .collect()
    }
}

/// Certified characteristic-`p` centre data in both Darboux and original
/// coordinates.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylCenterDescription<S: ExactFieldScalar> {
    decomposition: WeylDarbouxDecomposition<S>,
    characteristic: u128,
    generators: Vec<WeylCenterGenerator<S>>,
    basis: WeylCenterBasis<S>,
}

impl<S: ExactFieldScalar> WeylCenterDescription<S> {
    /// Positive field characteristic.
    pub fn characteristic(&self) -> u128 {
        self.characteristic
    }

    /// Certified Darboux tensor presentation used for the centre description.
    pub fn decomposition(&self) -> &WeylDarbouxDecomposition<S> {
        &self.decomposition
    }

    /// Characteristic powers followed by radical linear generators.
    pub fn generators(&self) -> &[WeylCenterGenerator<S>] {
        &self.generators
    }

    /// Lazy finite PBW basis over the centre.
    pub fn basis_over_center(&self) -> &WeylCenterBasis<S> {
        &self.basis
    }
}

impl<S: Scalar> WeylAlgebra<S> {
    /// Check whether an element commutes with every ordered generator under one
    /// shared multiplication budget. For a generated associative algebra this
    /// is exactly the generic centrality check.
    pub fn is_central_with_budget(
        &self,
        element: &WeylElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<bool, WeylError> {
        self.validate_element(element)?;
        let mut tracker = super::algebra::ExpansionTracker::new(budget);
        for index in 0..self.dim() {
            let generator = self.generator(index);
            let left = super::product::multiply(self, element, &generator, &mut tracker)?;
            let right = super::product::multiply(self, &generator, element, &mut tracker)?;
            if left != right {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Check centrality without a finite expansion cap.
    pub fn is_central(&self, element: &WeylElement<S>) -> Result<bool, WeylError> {
        self.is_central_with_budget(element, WeylExpansionBudget::unbounded())
    }
}

impl<S: ExactFieldScalar> WeylAlgebra<S> {
    /// Return the transported linear radical generators supplied by the
    /// certified Darboux decomposition. This field-gated operation is available
    /// in every characteristic.
    pub fn radical_generators_with_budget(
        &self,
        budget: WeylExpansionBudget,
    ) -> Result<Vec<WeylElement<S>>, WeylCenterError> {
        let decomposition = self.darboux_decomposition()?;
        (0..decomposition.central_rank())
            .map(|index| {
                let normal = decomposition.central_generator(index)?;
                decomposition
                    .from_normal_with_budget(&normal, budget)
                    .map_err(Into::into)
            })
            .collect()
    }

    /// Return certified radical generators without a finite expansion cap.
    pub fn radical_generators(&self) -> Result<Vec<WeylElement<S>>, WeylCenterError> {
        self.radical_generators_with_budget(WeylExpansionBudget::unbounded())
    }

    /// Describe the full centre in positive characteristic and independently
    /// verify every reported generator against the original presentation.
    pub fn positive_characteristic_center_with_budget(
        &self,
        budget: WeylExpansionBudget,
    ) -> Result<WeylCenterDescription<S>, WeylCenterError> {
        let characteristic = S::characteristic();
        if characteristic == 0 {
            return Err(WeylCenterError::RequiresPositiveCharacteristic);
        }
        let decomposition = self.darboux_decomposition()?;
        let paired_generators = 2 * decomposition.weyl_rank();
        let mut generators = Vec::with_capacity(paired_generators + decomposition.central_rank());

        for normal_generator in 0..paired_generators {
            let mut exponents = vec![0; decomposition.normal_algebra().dim()];
            exponents[normal_generator] = characteristic;
            let normal_element = decomposition
                .normal_algebra()
                .try_monomial(&exponents, S::one())?;
            let source_element = decomposition.from_normal_with_budget(&normal_element, budget)?;
            generators.push(WeylCenterGenerator {
                kind: WeylCenterGeneratorKind::CharacteristicPower {
                    normal_generator,
                    characteristic,
                },
                normal_element,
                source_element,
            });
        }
        for radical_index in 0..decomposition.central_rank() {
            let normal_generator = paired_generators + radical_index;
            let normal_element = decomposition
                .normal_algebra()
                .try_generator(normal_generator)?;
            let source_element = decomposition.from_normal_with_budget(&normal_element, budget)?;
            generators.push(WeylCenterGenerator {
                kind: WeylCenterGeneratorKind::Radical {
                    radical_index,
                    normal_generator,
                },
                normal_element,
                source_element,
            });
        }

        for (generator, entry) in generators.iter().enumerate() {
            if !self.is_central_with_budget(entry.source_element(), budget)? {
                return Err(WeylCenterError::CentralityCertificateMismatch { generator });
            }
        }

        let rank =
            (0..paired_generators).try_fold(1u128, |rank, _| rank.checked_mul(characteristic));
        let basis = WeylCenterBasis {
            decomposition: decomposition.clone(),
            characteristic,
            paired_generators,
            rank,
        };
        Ok(WeylCenterDescription {
            decomposition,
            characteristic,
            generators,
            basis,
        })
    }

    /// Describe the positive-characteristic centre without a finite expansion
    /// cap.
    pub fn positive_characteristic_center(
        &self,
    ) -> Result<WeylCenterDescription<S>, WeylCenterError> {
        self.positive_characteristic_center_with_budget(WeylExpansionBudget::unbounded())
    }
}
