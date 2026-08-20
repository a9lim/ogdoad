use super::{WeylAlgebra, WeylElement, WeylError};
use crate::scalar::{Poly, Scalar};

/// The polynomial `hbar` deformation of a Weyl algebra.
///
/// Coefficients live in `S[hbar]` and generator relations are
///
/// ```text
/// [z_i,z_j] = hbar * omega[i][j].
/// ```
///
/// Specialization at `hbar = 0` is the commutative polynomial algebra on the
/// generators; specialization at `hbar = 1` recovers the original Weyl
/// presentation. This is a polynomial deformation, not an analytic or formal
/// power-series completion.
#[derive(Clone, Debug, PartialEq)]
pub struct HbarWeylAlgebra<S: Scalar> {
    base: WeylAlgebra<S>,
    deformation: WeylAlgebra<Poly<S>>,
}

impl<S: Scalar> HbarWeylAlgebra<S> {
    /// Construct the `hbar`-scaled commutator family.
    pub fn new(base: &WeylAlgebra<S>) -> Self {
        let commutator = base
            .commutator_form()
            .iter()
            .map(|row| {
                row.iter()
                    .map(|coefficient| Poly::monomial(1, coefficient.clone()))
                    .collect()
            })
            .collect();
        let deformation = WeylAlgebra::from_commutator(commutator)
            .expect("multiplying an alternating form by hbar keeps it alternating");
        Self {
            base: base.clone(),
            deformation,
        }
    }

    /// Original `hbar = 1` Weyl algebra.
    pub fn base_algebra(&self) -> &WeylAlgebra<S> {
        &self.base
    }

    /// Weyl algebra over `S[hbar]` with scaled commutator form.
    pub fn deformation_algebra(&self) -> &WeylAlgebra<Poly<S>> {
        &self.deformation
    }

    /// The coefficient-ring indeterminate `hbar`.
    pub fn hbar(&self) -> Poly<S> {
        Poly::t()
    }

    /// Embed a base Weyl element with coefficient polynomials of degree zero.
    pub fn lift_element(
        &self,
        element: &WeylElement<S>,
    ) -> Result<WeylElement<Poly<S>>, WeylError> {
        self.base.validate_element(element)?;
        Ok(element.map_coefficients(|coefficient| Poly::constant(coefficient.clone())))
    }

    /// Specialize the deformation algebra at an arbitrary represented scalar.
    pub fn specialize_algebra_at(&self, hbar: &S) -> WeylAlgebra<S> {
        self.deformation.map(|coefficient| coefficient.eval(hbar))
    }

    /// Specialize a deformation element at an arbitrary represented scalar.
    pub fn specialize_element_at(
        &self,
        element: &WeylElement<Poly<S>>,
        hbar: &S,
    ) -> Result<WeylElement<S>, WeylError> {
        self.deformation.validate_element(element)?;
        Ok(element.map_coefficients(|coefficient| coefficient.eval(hbar)))
    }

    /// Commutative specialization at `hbar = 0`.
    pub fn specialize_zero_algebra(&self) -> WeylAlgebra<S> {
        self.specialize_algebra_at(&S::zero())
    }

    /// Original Weyl specialization at `hbar = 1`.
    pub fn specialize_one_algebra(&self) -> WeylAlgebra<S> {
        self.specialize_algebra_at(&S::one())
    }

    /// Specialize an element at `hbar = 0`.
    pub fn specialize_zero(
        &self,
        element: &WeylElement<Poly<S>>,
    ) -> Result<WeylElement<S>, WeylError> {
        self.specialize_element_at(element, &S::zero())
    }

    /// Specialize an element at `hbar = 1`.
    pub fn specialize_one(
        &self,
        element: &WeylElement<Poly<S>>,
    ) -> Result<WeylElement<S>, WeylError> {
        self.specialize_element_at(element, &S::one())
    }
}

impl<S: Scalar> WeylAlgebra<S> {
    /// Construct the polynomial `hbar` deformation of this commutator algebra.
    pub fn hbar_deformation(&self) -> HbarWeylAlgebra<S> {
        HbarWeylAlgebra::new(self)
    }
}
