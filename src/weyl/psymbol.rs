//! Characteristic-`p` symbol presentations and transported central fibres.
//!
//! A standard central fibre with relations
//!
//! ```text
//! [d_i, x_j] = delta_ij,  x_i^p = a_i,  d_i^p = b_i
//! ```
//!
//! is the tensor product of the `p`-symbol algebras `S_(a_i,b_i)`.  The
//! Azumaya and Brauer-group interpretation is cited mathematics (Wodzicki,
//! *Algebras of p-symbols, noncommutative p-residue, and the Brauer group*);
//! this module supplies executable presentations and independently checked
//! residue, cyclic-factor, coordinate-transport, and Darboux-fibre data.

use super::element::add_term;
use super::{
    OddWeylMatrixFiberCertificate, WeylAlgebra, WeylAutomorphism, WeylCentralCharacterModule,
    WeylCentralFiber, WeylCentralFiberElement, WeylDarbouxDecomposition, WeylDarbouxError,
    WeylElement, WeylError, WeylExpansionBudget, WeylFiberError, WeylMonomial,
    WeylRepresentationBudget,
};
use crate::scalar::ExactFieldScalar;
use std::collections::BTreeMap;
use std::fmt;

/// Failure while constructing or checking a characteristic-`p` symbol surface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WeylPSymbolError {
    /// A bounded central-fibre operation failed.
    Fiber(WeylFiberError),
    /// An ambient PBW operation failed.
    Weyl(WeylError),
    /// Certified Darboux coordinate construction failed.
    Darboux(WeylDarbouxError),
    /// A requested symbol pair is outside the standard Weyl rank.
    PairOutOfRange {
        /// Requested zero-based pair index.
        pair: usize,
        /// Available number of symbol pairs.
        pairs: usize,
    },
    /// Cyclic conversion requires an invertible `d_i^p` parameter.
    NonInvertibleCyclicParameter {
        /// Symbol pair whose momentum parameter is not a unit.
        pair: usize,
    },
    /// Paired characteristic-power values have the wrong length.
    PairedCharacterDimensionMismatch {
        /// Required `2r` values.
        expected: usize,
        /// Supplied number of values.
        actual: usize,
    },
    /// Linear radical-character values have the wrong length.
    RadicalCharacterDimensionMismatch {
        /// Required number of radical values.
        expected: usize,
        /// Supplied number of values.
        actual: usize,
    },
    /// Pulling a central character through an automorphism did not reduce to a
    /// scalar as the centrality theorem requires.
    CharacterPullbackNotScalar {
        /// Generator whose characteristic power failed the scalar check.
        generator: usize,
    },
    /// A purported cyclic-factor presentation failed one of its defining
    /// relations under exact fibre multiplication.
    CyclicRelationMismatch {
        /// Symbol pair whose relation failed.
        pair: usize,
    },
}

impl fmt::Display for WeylPSymbolError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Fiber(error) => write!(formatter, "Weyl p-symbol fibre failed: {error}"),
            Self::Weyl(error) => write!(formatter, "Weyl p-symbol PBW operation failed: {error}"),
            Self::Darboux(error) => {
                write!(formatter, "Weyl p-symbol Darboux transport failed: {error}")
            }
            Self::PairOutOfRange { pair, pairs } => {
                write!(
                    formatter,
                    "Weyl p-symbol pair {pair} is outside rank {pairs}"
                )
            }
            Self::NonInvertibleCyclicParameter { pair } => write!(
                formatter,
                "Weyl p-symbol pair {pair} has a noninvertible momentum parameter"
            ),
            Self::PairedCharacterDimensionMismatch { expected, actual } => write!(
                formatter,
                "paired Weyl character has {actual} values, expected {expected}"
            ),
            Self::RadicalCharacterDimensionMismatch { expected, actual } => write!(
                formatter,
                "radical Weyl character has {actual} values, expected {expected}"
            ),
            Self::CharacterPullbackNotScalar { generator } => write!(
                formatter,
                "the pulled-back characteristic power of Weyl generator {generator} is not scalar"
            ),
            Self::CyclicRelationMismatch { pair } => write!(
                formatter,
                "the cyclic presentation of Weyl p-symbol pair {pair} failed its relations"
            ),
        }
    }
}

impl std::error::Error for WeylPSymbolError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Fiber(error) => Some(error),
            Self::Weyl(error) => Some(error),
            Self::Darboux(error) => Some(error),
            _ => None,
        }
    }
}

impl From<WeylFiberError> for WeylPSymbolError {
    fn from(error: WeylFiberError) -> Self {
        Self::Fiber(error)
    }
}

impl From<WeylError> for WeylPSymbolError {
    fn from(error: WeylError) -> Self {
        Self::Weyl(error)
    }
}

impl From<WeylDarbouxError> for WeylPSymbolError {
    fn from(error: WeylDarbouxError) -> Self {
        Self::Darboux(error)
    }
}

/// One rank-one `p`-symbol factor `S_(a,b)` in a standard central fibre.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylPSymbolPair<S: ExactFieldScalar> {
    pair: usize,
    position_power: S,
    momentum_power: S,
}

impl<S: ExactFieldScalar> WeylPSymbolPair<S> {
    /// Pair index in the standard Weyl presentation.
    pub fn pair(&self) -> usize {
        self.pair
    }

    /// Central value `a = x_i^p`.
    pub fn position_power(&self) -> &S {
        &self.position_power
    }

    /// Central value `b = d_i^p`.
    pub fn momentum_power(&self) -> &S {
        &self.momentum_power
    }
}

/// Executable `p`-symbol presentation of a bounded standard central fibre.
///
/// The fibre remains the sole multiplication engine. This wrapper records its
/// tensor factors and adds theorem-shaped operations whose results are checked
/// against that engine.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylPSymbolPresentation<S: ExactFieldScalar> {
    fiber: WeylCentralFiber<S>,
    pairs: Vec<WeylPSymbolPair<S>>,
}

impl<S: ExactFieldScalar> WeylPSymbolPresentation<S> {
    /// View an existing bounded standard fibre as a tensor product of
    /// rank-one `p`-symbols.
    pub fn from_fiber(fiber: WeylCentralFiber<S>) -> Self {
        let pairs = fiber
            .algebra()
            .standard_pairs()
            .expect("a central fibre is constructed only for a standard algebra");
        let data = (0..pairs)
            .map(|pair| WeylPSymbolPair {
                pair,
                position_power: fiber.central_values()[pair].clone(),
                momentum_power: fiber.central_values()[pairs + pair].clone(),
            })
            .collect();
        Self { fiber, pairs: data }
    }

    /// Construct a bounded standard fibre and its `p`-symbol view together.
    pub fn try_new(
        algebra: &WeylAlgebra<S>,
        central_values: Vec<S>,
        budget: WeylRepresentationBudget,
    ) -> Result<Self, WeylPSymbolError> {
        Ok(Self::from_fiber(
            algebra.central_fiber(central_values, budget)?,
        ))
    }

    /// Underlying bounded central fibre.
    pub fn fiber(&self) -> &WeylCentralFiber<S> {
        &self.fiber
    }

    /// Positive coefficient characteristic `p`.
    pub fn characteristic(&self) -> u128 {
        self.fiber.characteristic()
    }

    /// Ordered rank-one symbol factors.
    pub fn pairs(&self) -> &[WeylPSymbolPair<S>] {
        &self.pairs
    }

    /// Tensor rank, equal to the standard Weyl rank.
    pub fn tensor_rank(&self) -> usize {
        self.pairs.len()
    }

    /// Brauer-theoretic report for this tensor presentation. Without a matrix
    /// certificate this records only the cited `p`-symbol interpretation; it
    /// does not assert that the represented fibre splits over `S`.
    pub fn brauer_report(&self) -> WeylFiberBrauerReport<S> {
        WeylFiberBrauerReport {
            characteristic: self.characteristic(),
            factors: self.pairs.clone(),
            evidence: WeylFiberBrauerEvidence::PSymbolPresentation,
        }
    }

    /// Upgrade the Brauer report with an exact full-matrix certificate after
    /// checking that it belongs to this same central fibre.
    pub fn brauer_report_with_matrix_certificate(
        &self,
        certificate: &OddWeylMatrixFiberCertificate<S>,
    ) -> Result<WeylFiberBrauerReport<S>, WeylPSymbolError> {
        if certificate.fiber() != &self.fiber {
            return Err(WeylFiberError::FiberContextMismatch.into());
        }
        Ok(WeylFiberBrauerReport {
            characteristic: self.characteristic(),
            factors: self.pairs.clone(),
            evidence: WeylFiberBrauerEvidence::SplitMatrixCertificate {
                matrix_dimension: certificate.matrix_dimension(),
                image_rank: certificate.image_rank(),
            },
        })
    }

    /// Tensor noncommutative `p`-residue: the coefficient of the reduced PBW
    /// monomial whose `2n` exponents are all `p-1`.
    pub fn p_residue(&self, element: &WeylCentralFiberElement<S>) -> Result<S, WeylPSymbolError> {
        // Lifting is the authoritative context validation.
        self.fiber.lift(element)?;
        Ok(element
            .coefficients()
            .last()
            .cloned()
            .expect("every bounded fibre has the scalar basis element"))
    }

    /// Compare the tensor `p`-residue with exact matrix trace on a verified
    /// split module. With the source convention, `residue = (-1)^n trace`.
    pub fn split_matrix_trace_matches_residue(
        &self,
        module: &WeylCentralCharacterModule<S>,
        element: &WeylCentralFiberElement<S>,
        budget: WeylRepresentationBudget,
    ) -> Result<bool, WeylPSymbolError> {
        if module.algebra() != self.fiber.algebra()
            || module.central_values() != self.fiber.central_values()
        {
            return Err(WeylFiberError::FiberContextMismatch.into());
        }
        let representative = self.fiber.lift(element)?;
        let matrix = module.action_matrix(&representative, budget)?;
        let trace = (0..matrix.len()).fold(S::zero(), |sum, index| sum.add(&matrix[index][index]));
        let residue = self.p_residue(element)?;
        let expected = if self.tensor_rank().is_multiple_of(2) {
            trace
        } else {
            trace.neg()
        };
        Ok(residue == expected)
    }

    /// Convert one factor `S_(a,b)` with invertible `b` to the cyclic
    /// presentation `(b,c]`, `c = a*b`, and independently verify all relations.
    pub fn cyclic_factor(
        &self,
        pair: usize,
        representation_budget: WeylRepresentationBudget,
        expansion_budget: WeylExpansionBudget,
    ) -> Result<WeylCyclicPSymbolFactor<S>, WeylPSymbolError> {
        let data = self
            .pairs
            .get(pair)
            .ok_or(WeylPSymbolError::PairOutOfRange {
                pair,
                pairs: self.pairs.len(),
            })?;
        data.momentum_power
            .inv()
            .ok_or(WeylPSymbolError::NonInvertibleCyclicParameter { pair })?;

        let algebra = WeylAlgebra::<S>::standard(1);
        let fiber = algebra.central_fiber(
            vec![data.position_power.clone(), data.momentum_power.clone()],
            representation_budget,
        )?;
        let x = algebra.x(0);
        let d = algebra.d(0);
        let eta_pbw = algebra.checked_mul_with_budget(&x, &d, expansion_budget)?;
        let eta = fiber.reduce(&eta_pbw)?;
        let zeta = fiber.reduce(&d)?;
        let c = data.position_power.mul(&data.momentum_power);

        let zeta_power = fiber.reduce(&algebra.checked_pow_with_budget(
            &d,
            self.characteristic(),
            expansion_budget,
        )?)?;
        let eta_power = fiber.reduce(&algebra.checked_pow_with_budget(
            &eta_pbw,
            self.characteristic(),
            expansion_budget,
        )?)?;
        let eta_plus_c = fiber.reduce(&algebra.add(&eta_pbw, &algebra.scalar(c.clone()))?)?;
        let zeta_eta =
            fiber.reduce(&algebra.checked_mul_with_budget(&d, &eta_pbw, expansion_budget)?)?;
        let eta_plus_one = algebra.add(&eta_pbw, &algebra.one())?;
        let eta_one_zeta = fiber.reduce(&algebra.checked_mul_with_budget(
            &eta_plus_one,
            &d,
            expansion_budget,
        )?)?;
        let zeta_scalar = fiber.reduce(&algebra.scalar(data.momentum_power.clone()))?;

        if zeta_power != zeta_scalar || eta_power != eta_plus_c || zeta_eta != eta_one_zeta {
            return Err(WeylPSymbolError::CyclicRelationMismatch { pair });
        }

        Ok(WeylCyclicPSymbolFactor {
            pair,
            characteristic: self.characteristic(),
            position_power: data.position_power.clone(),
            momentum_power: data.momentum_power.clone(),
            artin_schreier_parameter: c,
            eta,
            zeta,
        })
    }
}

/// Evidence level carried by a Weyl central-fibre Brauer report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WeylFiberBrauerEvidence {
    /// The fibre has an executable tensor presentation by `p`-symbols. Its
    /// `p`-torsion Brauer interpretation is cited, not internally proved.
    PSymbolPresentation,
    /// Exact action of the whole fibre has full rank in a matrix algebra.
    SplitMatrixCertificate {
        /// Matrix size `p^n`.
        matrix_dimension: usize,
        /// Exact rank of the flattened PBW-basis images.
        image_rank: usize,
    },
}

/// Claim-disciplined Brauer report for a bounded Weyl central fibre.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylFiberBrauerReport<S: ExactFieldScalar> {
    characteristic: u128,
    factors: Vec<WeylPSymbolPair<S>>,
    evidence: WeylFiberBrauerEvidence,
}

impl<S: ExactFieldScalar> WeylFiberBrauerReport<S> {
    /// Positive characteristic `p` of the represented class.
    pub fn characteristic(&self) -> u128 {
        self.characteristic
    }

    /// Ordered `p`-symbol tensor factors representing the class.
    pub fn factors(&self) -> &[WeylPSymbolPair<S>] {
        &self.factors
    }

    /// Whether this is a cited presentation or an exact split certificate.
    pub fn evidence(&self) -> &WeylFiberBrauerEvidence {
        &self.evidence
    }

    /// `Some(true)` only for an exact full-matrix certificate; otherwise the
    /// split question remains uncomputed rather than being reported false.
    pub fn is_split(&self) -> Option<bool> {
        match self.evidence {
            WeylFiberBrauerEvidence::PSymbolPresentation => None,
            WeylFiberBrauerEvidence::SplitMatrixCertificate { .. } => Some(true),
        }
    }
}

/// Independently checked cyclic presentation `(b,c]` of one `p`-symbol factor.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylCyclicPSymbolFactor<S: ExactFieldScalar> {
    pair: usize,
    characteristic: u128,
    position_power: S,
    momentum_power: S,
    artin_schreier_parameter: S,
    eta: WeylCentralFiberElement<S>,
    zeta: WeylCentralFiberElement<S>,
}

impl<S: ExactFieldScalar> WeylCyclicPSymbolFactor<S> {
    /// Original symbol-pair index.
    pub fn pair(&self) -> usize {
        self.pair
    }

    /// Positive characteristic `p`.
    pub fn characteristic(&self) -> u128 {
        self.characteristic
    }

    /// Original `a = x_i^p` parameter.
    pub fn position_power(&self) -> &S {
        &self.position_power
    }

    /// Cyclic multiplicative parameter `b = d_i^p`.
    pub fn momentum_power(&self) -> &S {
        &self.momentum_power
    }

    /// Artin--Schreier parameter `c = a*b` in `(b,c]`.
    pub fn artin_schreier_parameter(&self) -> &S {
        &self.artin_schreier_parameter
    }

    /// Checked cyclic generator `eta = x_i d_i`, satisfying `eta^p=eta+c`.
    pub fn eta(&self) -> &WeylCentralFiberElement<S> {
        &self.eta
    }

    /// Checked cyclic generator `zeta = d_i`, satisfying `zeta^p=b`.
    pub fn zeta(&self) -> &WeylCentralFiberElement<S> {
        &self.zeta
    }
}

/// Exact pullback of a standard central character through a Weyl automorphism.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylCentralCharacterPullback<S: ExactFieldScalar> {
    automorphism: WeylAutomorphism<S>,
    original_values: Vec<S>,
    pulled_back_values: Vec<S>,
}

impl<S: ExactFieldScalar> WeylCentralCharacterPullback<S> {
    /// Automorphism inducing the centre map.
    pub fn automorphism(&self) -> &WeylAutomorphism<S> {
        &self.automorphism
    }

    /// Original values of the standard characteristic-power generators.
    pub fn original_values(&self) -> &[S] {
        &self.original_values
    }

    /// Values after pullback `chi(phi(z_i)^p)`.
    pub fn pulled_back_values(&self) -> &[S] {
        &self.pulled_back_values
    }
}

impl<S: ExactFieldScalar> WeylAutomorphism<S> {
    /// Pull a positive-characteristic central character back through this
    /// automorphism by reducing every `phi(z_i)^p` in the supplied fibre.
    ///
    /// Computing in the Weyl algebra automatically retains the characteristic-
    /// two quadratic correction for mixed symplectic coordinates.
    pub fn pullback_central_character(
        &self,
        central_values: Vec<S>,
        representation_budget: WeylRepresentationBudget,
        expansion_budget: WeylExpansionBudget,
    ) -> Result<WeylCentralCharacterPullback<S>, WeylPSymbolError> {
        let fiber = self
            .algebra()
            .central_fiber(central_values.clone(), representation_budget)?;
        let characteristic = fiber.characteristic();
        let mut pulled_back_values = Vec::with_capacity(self.algebra().dim());
        for generator in 0..self.algebra().dim() {
            let image = self.homomorphism().generator_image(generator)?;
            let power =
                self.algebra()
                    .checked_pow_with_budget(image, characteristic, expansion_budget)?;
            let reduced = fiber.reduce(&power)?;
            if reduced
                .coefficients()
                .iter()
                .skip(1)
                .any(|coefficient| !coefficient.is_zero())
            {
                return Err(WeylPSymbolError::CharacterPullbackNotScalar { generator });
            }
            pulled_back_values.push(reduced.coefficients()[0].clone());
        }
        Ok(WeylCentralCharacterPullback {
            automorphism: self.clone(),
            original_values: central_values,
            pulled_back_values,
        })
    }
}

/// Reduced element of a Darboux-transported central fibre.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylTransportedCentralFiberElement<S: ExactFieldScalar> {
    source_algebra: WeylAlgebra<S>,
    paired_values: Vec<S>,
    radical_values: Vec<S>,
    paired_element: WeylCentralFiberElement<S>,
}

impl<S: ExactFieldScalar> WeylTransportedCentralFiberElement<S> {
    /// Dense coefficients in the transported reduced PBW basis.
    pub fn coefficients(&self) -> &[S] {
        self.paired_element.coefficients()
    }

    /// Whether every reduced coefficient is zero.
    pub fn is_zero(&self) -> bool {
        self.paired_element.is_zero()
    }
}

/// Bounded central fibre of an arbitrary exact-field alternating presentation.
///
/// Darboux coordinates split the algebra into a standard paired factor and a
/// central radical-polynomial factor. `paired_values` fix the `p`-th powers of
/// the `2r` paired generators; `radical_values` fix the central radical
/// generators themselves. The finite basis therefore has dimension `p^(2r)`.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylTransportedCentralFiber<S: ExactFieldScalar> {
    decomposition: WeylDarbouxDecomposition<S>,
    paired_fiber: WeylCentralFiber<S>,
    radical_values: Vec<S>,
}

impl<S: ExactFieldScalar> WeylTransportedCentralFiber<S> {
    /// Construct a bounded fibre in certified Darboux coordinates.
    pub fn try_new(
        algebra: &WeylAlgebra<S>,
        paired_values: Vec<S>,
        radical_values: Vec<S>,
        budget: WeylRepresentationBudget,
    ) -> Result<Self, WeylPSymbolError> {
        let decomposition = algebra.darboux_decomposition()?;
        let paired_dim = 2 * decomposition.weyl_rank();
        if paired_values.len() != paired_dim {
            return Err(WeylPSymbolError::PairedCharacterDimensionMismatch {
                expected: paired_dim,
                actual: paired_values.len(),
            });
        }
        if radical_values.len() != decomposition.central_rank() {
            return Err(WeylPSymbolError::RadicalCharacterDimensionMismatch {
                expected: decomposition.central_rank(),
                actual: radical_values.len(),
            });
        }
        let paired_algebra = WeylAlgebra::<S>::standard(decomposition.weyl_rank());
        let paired_fiber = paired_algebra.central_fiber(paired_values, budget)?;
        Ok(Self {
            decomposition,
            paired_fiber,
            radical_values,
        })
    }

    /// Certified source-to-Darboux decomposition.
    pub fn decomposition(&self) -> &WeylDarbouxDecomposition<S> {
        &self.decomposition
    }

    /// Underlying paired `p`-symbol fibre.
    pub fn paired_fiber(&self) -> &WeylCentralFiber<S> {
        &self.paired_fiber
    }

    /// Values assigned to the linear central radical generators.
    pub fn radical_values(&self) -> &[S] {
        &self.radical_values
    }

    /// Finite vector-space dimension `p^(2r)`.
    pub fn basis_dimension(&self) -> usize {
        self.paired_fiber.basis_dimension()
    }

    /// `p`-symbol presentation of the paired factor.
    pub fn psymbol_presentation(&self) -> WeylPSymbolPresentation<S> {
        WeylPSymbolPresentation::from_fiber(self.paired_fiber.clone())
    }

    /// Reduce a source-coordinate PBW element under finite coordinate-transport
    /// bounds and the fixed paired/radical central character.
    pub fn reduce_with_budget(
        &self,
        element: &WeylElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<WeylTransportedCentralFiberElement<S>, WeylPSymbolError> {
        let normal = self.decomposition.to_normal_with_budget(element, budget)?;
        let paired_dim = 2 * self.decomposition.weyl_rank();
        let mut paired_terms = BTreeMap::new();
        for (monomial, coefficient) in normal.terms() {
            let (paired_exponents, radical_exponents) =
                self.decomposition.split_monomial(monomial)?;
            let mut reduced_coefficient = coefficient.clone();
            for (value, exponent) in self.radical_values.iter().zip(radical_exponents) {
                reduced_coefficient = reduced_coefficient.mul(&value.pow(*exponent));
            }
            add_term(
                &mut paired_terms,
                WeylMonomial::new(paired_exponents.to_vec()),
                reduced_coefficient,
            );
        }
        let paired = WeylElement {
            dim: paired_dim,
            terms: paired_terms,
        };
        let paired_element = self.paired_fiber.reduce(&paired)?;
        Ok(self.wrap(paired_element))
    }

    /// Reduce without a finite coordinate-transport cap.
    pub fn reduce(
        &self,
        element: &WeylElement<S>,
    ) -> Result<WeylTransportedCentralFiberElement<S>, WeylPSymbolError> {
        self.reduce_with_budget(element, WeylExpansionBudget::unbounded())
    }

    /// Canonically lift a reduced element back to source PBW coordinates.
    pub fn lift_with_budget(
        &self,
        element: &WeylTransportedCentralFiberElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<WeylElement<S>, WeylPSymbolError> {
        self.validate_element(element)?;
        let paired = self.paired_fiber.lift(&element.paired_element)?;
        let mut normal_terms = BTreeMap::new();
        for (monomial, coefficient) in paired.terms() {
            let mut exponents = monomial.exponents().to_vec();
            exponents.resize(self.decomposition.normal_algebra().dim(), 0);
            normal_terms.insert(WeylMonomial::new(exponents), coefficient.clone());
        }
        let normal = WeylElement {
            dim: self.decomposition.normal_algebra().dim(),
            terms: normal_terms,
        };
        Ok(self
            .decomposition
            .from_normal_with_budget(&normal, budget)?)
    }

    /// Canonically lift without a finite coordinate-transport cap.
    pub fn lift(
        &self,
        element: &WeylTransportedCentralFiberElement<S>,
    ) -> Result<WeylElement<S>, WeylPSymbolError> {
        self.lift_with_budget(element, WeylExpansionBudget::unbounded())
    }

    /// Reduced image of one source generator.
    pub fn generator(
        &self,
        index: usize,
    ) -> Result<WeylTransportedCentralFiberElement<S>, WeylPSymbolError> {
        self.reduce(&self.decomposition.source_algebra().try_generator(index)?)
    }

    /// Multiply two transported elements through the paired `p`-symbol engine.
    pub fn checked_mul_with_budget(
        &self,
        left: &WeylTransportedCentralFiberElement<S>,
        right: &WeylTransportedCentralFiberElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<WeylTransportedCentralFiberElement<S>, WeylPSymbolError> {
        self.validate_element(left)?;
        self.validate_element(right)?;
        Ok(self.wrap(self.paired_fiber.checked_mul_with_budget(
            &left.paired_element,
            &right.paired_element,
            budget,
        )?))
    }

    /// Independently compare paired-fibre multiplication with multiplication
    /// after lifting to the original source presentation.
    pub fn products_agree_with_source(
        &self,
        left: &WeylTransportedCentralFiberElement<S>,
        right: &WeylTransportedCentralFiberElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<bool, WeylPSymbolError> {
        let paired_product = self.checked_mul_with_budget(left, right, budget)?;
        let source_left = self.lift_with_budget(left, budget)?;
        let source_right = self.lift_with_budget(right, budget)?;
        let source_product = self
            .decomposition
            .source_algebra()
            .checked_mul_with_budget(&source_left, &source_right, budget)?;
        Ok(paired_product == self.reduce_with_budget(&source_product, budget)?)
    }

    fn wrap(
        &self,
        paired_element: WeylCentralFiberElement<S>,
    ) -> WeylTransportedCentralFiberElement<S> {
        WeylTransportedCentralFiberElement {
            source_algebra: self.decomposition.source_algebra().clone(),
            paired_values: self.paired_fiber.central_values().to_vec(),
            radical_values: self.radical_values.clone(),
            paired_element,
        }
    }

    fn validate_element(
        &self,
        element: &WeylTransportedCentralFiberElement<S>,
    ) -> Result<(), WeylPSymbolError> {
        if element.source_algebra != *self.decomposition.source_algebra()
            || element.paired_values != self.paired_fiber.central_values()
            || element.radical_values != self.radical_values
        {
            return Err(WeylFiberError::FiberContextMismatch.into());
        }
        self.paired_fiber.lift(&element.paired_element)?;
        Ok(())
    }
}

impl<S: ExactFieldScalar> WeylAlgebra<S> {
    /// Construct the `p`-symbol presentation of a bounded standard fibre.
    pub fn psymbol_presentation(
        &self,
        central_values: Vec<S>,
        budget: WeylRepresentationBudget,
    ) -> Result<WeylPSymbolPresentation<S>, WeylPSymbolError> {
        WeylPSymbolPresentation::try_new(self, central_values, budget)
    }

    /// Construct a bounded central fibre through certified Darboux coordinates.
    pub fn transported_central_fiber(
        &self,
        paired_values: Vec<S>,
        radical_values: Vec<S>,
        budget: WeylRepresentationBudget,
    ) -> Result<WeylTransportedCentralFiber<S>, WeylPSymbolError> {
        WeylTransportedCentralFiber::try_new(self, paired_values, radical_values, budget)
    }
}
