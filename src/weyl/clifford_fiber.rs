use super::{
    WeylAlgebra, WeylCentralFiber, WeylCentralFiberElement, WeylElement, WeylExpansionBudget,
    WeylFiberError, WeylRepresentationBudget,
};
use crate::clifford::{CliffordAlgebra, Metric, Multivector, MAX_BASIS_DIM};
use crate::scalar::ExactFieldScalar;

/// Checked identification of a standard characteristic-two Weyl central fibre
/// with a Clifford algebra on the same ordered generators.
///
/// For central values `x_i^2 = a_i`, `d_i^2 = b_i`, the Clifford quadratic
/// diagonal is `(a_0,...,a_n,b_0,...,b_n)` and its polar form has
/// `B(x_i,d_j) = delta_ij`. In characteristic two the Weyl commutator is the
/// Clifford anticommutator, while the reduced PBW exponents are exactly blade
/// bits.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylCliffordFiber<S: ExactFieldScalar> {
    fiber: WeylCentralFiber<S>,
    clifford: CliffordAlgebra<S>,
}

impl<S: ExactFieldScalar> WeylCliffordFiber<S> {
    /// Construct the bounded bridge from values in standard generator order.
    pub fn try_new(
        algebra: &WeylAlgebra<S>,
        central_values: Vec<S>,
        budget: WeylRepresentationBudget,
    ) -> Result<Self, WeylFiberError> {
        if S::characteristic() != 2 {
            return Err(WeylFiberError::RequiresCharacteristicTwo);
        }
        let pairs = algebra
            .standard_pairs()
            .ok_or(WeylFiberError::RequiresStandard)?;
        if algebra.dim() > MAX_BASIS_DIM {
            return Err(WeylFiberError::CliffordDimensionLimit {
                dim: algebra.dim(),
                limit: MAX_BASIS_DIM,
            });
        }
        let fiber = WeylCentralFiber::try_new(algebra, central_values.clone(), budget)?;
        let polar = (0..pairs).map(|pair| ((pair, pairs + pair), S::one()));
        let clifford = CliffordAlgebra::new(algebra.dim(), Metric::new(central_values, polar));
        Ok(Self { fiber, clifford })
    }

    /// Finite reduced Weyl fibre.
    pub fn fiber(&self) -> &WeylCentralFiber<S> {
        &self.fiber
    }

    /// Clifford algebra with matching squares and polar form.
    pub fn clifford_algebra(&self) -> &CliffordAlgebra<S> {
        &self.clifford
    }

    /// Convert a reduced PBW fibre element to the corresponding Clifford
    /// multivector.
    pub fn fiber_to_clifford(
        &self,
        element: &WeylCentralFiberElement<S>,
    ) -> Result<Multivector<S>, WeylFiberError> {
        // `lift` supplies the complete fibre-context and coefficient-length
        // validation before the shared index/blade representation is used.
        self.fiber.lift(element)?;
        let terms = element
            .coefficients()
            .iter()
            .enumerate()
            .filter(|(_, coefficient)| !coefficient.is_zero())
            .map(|(blade, coefficient)| (blade as u128, coefficient.clone()))
            .collect();
        Ok(Multivector { terms })
    }

    /// Convert a Clifford multivector to the reduced PBW fibre.
    pub fn clifford_to_fiber(
        &self,
        multivector: &Multivector<S>,
    ) -> Result<WeylCentralFiberElement<S>, WeylFiberError> {
        let mut coefficients = vec![S::zero(); self.fiber.basis_dimension()];
        for (&blade, coefficient) in multivector.terms() {
            if self.clifford.dim() < MAX_BASIS_DIM && blade >> self.clifford.dim() != 0 {
                return Err(WeylFiberError::CliffordBladeOutOfRange {
                    blade,
                    dim: self.clifford.dim(),
                });
            }
            let index =
                usize::try_from(blade).map_err(|_| WeylFiberError::CliffordBladeOutOfRange {
                    blade,
                    dim: self.clifford.dim(),
                })?;
            if index >= coefficients.len() {
                return Err(WeylFiberError::CliffordBladeOutOfRange {
                    blade,
                    dim: self.clifford.dim(),
                });
            }
            coefficients[index] = coefficient.clone();
        }
        self.fiber.element_from_coefficients(coefficients)
    }

    /// Reduce an ambient Weyl element and identify it with a Clifford
    /// multivector.
    pub fn weyl_to_clifford(
        &self,
        element: &WeylElement<S>,
    ) -> Result<Multivector<S>, WeylFiberError> {
        self.fiber_to_clifford(&self.fiber.reduce(element)?)
    }

    /// Return the canonical reduced PBW representative of a Clifford
    /// multivector.
    pub fn clifford_to_weyl(
        &self,
        multivector: &Multivector<S>,
    ) -> Result<WeylElement<S>, WeylFiberError> {
        self.fiber.lift(&self.clifford_to_fiber(multivector)?)
    }

    /// Independently compare reduced Weyl multiplication with the Clifford
    /// geometric product for two ambient PBW elements.
    pub fn products_agree_with_budget(
        &self,
        left: &WeylElement<S>,
        right: &WeylElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<bool, WeylFiberError> {
        let left_fiber = self.fiber.reduce(left)?;
        let right_fiber = self.fiber.reduce(right)?;
        let weyl_product = self
            .fiber
            .checked_mul_with_budget(&left_fiber, &right_fiber, budget)?;
        let clifford_left = self.fiber_to_clifford(&left_fiber)?;
        let clifford_right = self.fiber_to_clifford(&right_fiber)?;
        let clifford_product = self.clifford.mul(&clifford_left, &clifford_right);
        Ok(self.fiber_to_clifford(&weyl_product)? == clifford_product)
    }

    /// Compare the two multiplication engines without a finite PBW expansion
    /// cap.
    pub fn products_agree(
        &self,
        left: &WeylElement<S>,
        right: &WeylElement<S>,
    ) -> Result<bool, WeylFiberError> {
        self.products_agree_with_budget(left, right, WeylExpansionBudget::unbounded())
    }
}

impl<S: ExactFieldScalar> WeylAlgebra<S> {
    /// Construct the bounded characteristic-two Clifford central-fibre bridge.
    pub fn clifford_central_fiber(
        &self,
        central_values: Vec<S>,
        budget: WeylRepresentationBudget,
    ) -> Result<WeylCliffordFiber<S>, WeylFiberError> {
        WeylCliffordFiber::try_new(self, central_values, budget)
    }
}
