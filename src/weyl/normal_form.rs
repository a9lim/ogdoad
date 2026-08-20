use super::{
    WeylAlgebra, WeylElement, WeylError, WeylExpansionBudget, WeylHomomorphism, WeylMonomial,
};
use crate::forms::{DarbouxDecomposition, DarbouxError, SymplecticForm};
use crate::scalar::ExactFieldScalar;
use std::fmt;

/// Failure while constructing the Darboux tensor presentation of a Weyl
/// algebra.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WeylDarbouxError {
    /// The underlying alternating form could not produce a certified exact-field
    /// Darboux basis.
    Darboux(DarbouxError),
    /// A coordinate transport unexpectedly failed the checked Weyl-map laws.
    Transport(WeylError),
}

impl fmt::Display for WeylDarbouxError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Darboux(error) => write!(formatter, "Darboux reduction failed: {error}"),
            Self::Transport(error) => write!(formatter, "Darboux transport failed: {error}"),
        }
    }
}

impl std::error::Error for WeylDarbouxError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Darboux(error) => Some(error),
            Self::Transport(error) => Some(error),
        }
    }
}

impl From<DarbouxError> for WeylDarbouxError {
    fn from(error: DarbouxError) -> Self {
        Self::Darboux(error)
    }
}

impl From<WeylError> for WeylDarbouxError {
    fn from(error: WeylError) -> Self {
        Self::Transport(error)
    }
}

/// A certified presentation
///
/// ```text
/// A(V, omega) ~= A_r(S) tensor S[c_0,...,c_(s-1)]
/// ```
///
/// for an exact-field alternating form. The normal algebra orders generators as
/// all `x_i`, all `d_i`, then the central radical generators `c_j`. Its PBW
/// monomial therefore reads literally as a tensor monomial. `to_normal` and
/// `from_normal` are checked inverse linear Weyl homomorphisms.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylDarbouxDecomposition<S: ExactFieldScalar> {
    source: WeylAlgebra<S>,
    normal: WeylAlgebra<S>,
    certificate: DarbouxDecomposition<S>,
    to_normal: WeylHomomorphism<S>,
    from_normal: WeylHomomorphism<S>,
}

impl<S: ExactFieldScalar> WeylDarbouxDecomposition<S> {
    /// Original alternating presentation.
    pub fn source_algebra(&self) -> &WeylAlgebra<S> {
        &self.source
    }

    /// Darboux-plus-central tensor presentation.
    pub fn normal_algebra(&self) -> &WeylAlgebra<S> {
        &self.normal
    }

    /// Underlying form-level basis certificate.
    pub fn certificate(&self) -> &DarbouxDecomposition<S> {
        &self.certificate
    }

    /// Rank of the noncommutative standard Weyl factor.
    pub fn weyl_rank(&self) -> usize {
        self.certificate.planes()
    }

    /// Number of central polynomial variables.
    pub fn central_rank(&self) -> usize {
        self.certificate.radical_dim()
    }

    /// Checked source-to-normal homomorphism.
    pub fn to_normal_map(&self) -> &WeylHomomorphism<S> {
        &self.to_normal
    }

    /// Checked normal-to-source homomorphism.
    pub fn from_normal_map(&self) -> &WeylHomomorphism<S> {
        &self.from_normal
    }

    /// Transport an original PBW element into tensor coordinates.
    pub fn to_normal(&self, element: &WeylElement<S>) -> Result<WeylElement<S>, WeylError> {
        self.to_normal.apply(element)
    }

    /// Transport an original PBW element into tensor coordinates under a
    /// finite expansion budget.
    pub fn to_normal_with_budget(
        &self,
        element: &WeylElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<WeylElement<S>, WeylError> {
        self.to_normal.apply_with_budget(element, budget)
    }

    /// Transport a tensor-coordinate PBW element back to the original
    /// presentation.
    pub fn from_normal(&self, element: &WeylElement<S>) -> Result<WeylElement<S>, WeylError> {
        self.from_normal.apply(element)
    }

    /// Transport a tensor-coordinate PBW element back under a finite expansion
    /// budget.
    pub fn from_normal_with_budget(
        &self,
        element: &WeylElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<WeylElement<S>, WeylError> {
        self.from_normal.apply_with_budget(element, budget)
    }

    /// Position generator `x_i` in the normal Weyl factor.
    pub fn x(&self, index: usize) -> Result<WeylElement<S>, WeylError> {
        if index >= self.weyl_rank() {
            return Err(WeylError::GeneratorOutOfRange {
                index,
                dim: self.weyl_rank(),
            });
        }
        self.normal.try_generator(index)
    }

    /// Differential generator `d_i` in the normal Weyl factor.
    pub fn d(&self, index: usize) -> Result<WeylElement<S>, WeylError> {
        if index >= self.weyl_rank() {
            return Err(WeylError::GeneratorOutOfRange {
                index,
                dim: self.weyl_rank(),
            });
        }
        self.normal.try_generator(self.weyl_rank() + index)
    }

    /// Central radical generator `c_i` in the polynomial tensor factor.
    pub fn central_generator(&self, index: usize) -> Result<WeylElement<S>, WeylError> {
        if index >= self.central_rank() {
            return Err(WeylError::GeneratorOutOfRange {
                index,
                dim: self.central_rank(),
            });
        }
        self.normal.try_generator(2 * self.weyl_rank() + index)
    }

    /// Split a normal PBW exponent vector into the standard Weyl and central
    /// polynomial factors.
    pub fn split_monomial<'a>(
        &self,
        monomial: &'a WeylMonomial,
    ) -> Result<(&'a [u128], &'a [u128]), WeylError> {
        if monomial.exponents().len() != self.normal.dim() {
            return Err(WeylError::MonomialDimensionMismatch {
                expected: self.normal.dim(),
                actual: monomial.exponents().len(),
            });
        }
        Ok(monomial.exponents().split_at(2 * self.weyl_rank()))
    }
}

impl<S: ExactFieldScalar> WeylAlgebra<S> {
    /// Compute the certified Darboux tensor presentation of this alternating
    /// commutator algebra.
    pub fn darboux_decomposition(&self) -> Result<WeylDarbouxDecomposition<S>, WeylDarbouxError> {
        let form = SymplecticForm::from_gram(self.commutator.clone())
            .expect("a Weyl commutator presentation is alternating");
        let certificate = form.darboux_decomposition()?;
        let paired = WeylAlgebra::<S>::standard(certificate.planes());
        let central_dim = certificate.radical_dim();
        let central = WeylAlgebra::from_commutator(vec![vec![S::zero(); central_dim]; central_dim])
            .expect("the zero commutator matrix is alternating");
        let normal = if central_dim == 0 {
            paired
        } else {
            paired.try_direct_sum(&central)?
        };
        debug_assert_eq!(normal.commutator_form(), certificate.canonical_gram());

        let to_normal = WeylHomomorphism::try_new(
            self.clone(),
            normal.clone(),
            certificate.inverse_basis_matrix().to_vec(),
            vec![S::zero(); self.dim()],
        )?;
        let from_normal = WeylHomomorphism::try_new(
            normal.clone(),
            self.clone(),
            certificate.basis_matrix().to_vec(),
            vec![S::zero(); normal.dim()],
        )?;
        Ok(WeylDarbouxDecomposition {
            source: self.clone(),
            normal,
            certificate,
            to_normal,
            from_normal,
        })
    }
}
