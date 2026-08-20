//! Selected monomorphic Python bindings for the finite-support Weyl pillar.
//!
//! Rational and Nimber algebras/elements remain separate Python classes. Every
//! materializing product, transformation, centre transport, finite fibre, and
//! module action keeps the Rust budget and error distinctions visible.

use super::scalars::{
    parse_nimber, parse_rational, wrap_nimber, wrap_rational, PyNimber, PyRational,
};
use crate::scalar::{Nimber, Rational};
use crate::weyl::{WeylAlgebra, WeylElement, WeylExpansionBudget, WeylRepresentationBudget};
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use std::sync::Arc;

fn expansion_budget(max_terms: Option<usize>, max_steps: Option<u128>) -> WeylExpansionBudget {
    WeylExpansionBudget::new(
        max_terms.unwrap_or(usize::MAX),
        max_steps.unwrap_or(u128::MAX),
    )
}

macro_rules! weyl_backend {
    (
        $alg:ident,
        $element:ident,
        $alg_name:literal,
        $element_name:literal,
        $scalar:ty,
        $py_scalar:ty,
        $parse:path,
        $wrap:path
    ) => {
        #[pyclass(name = $alg_name, module = "ogdoad", from_py_object)]
        #[derive(Clone)]
        pub(crate) struct $alg {
            inner: Arc<WeylAlgebra<$scalar>>,
        }

        impl $alg {
            fn wrap_element(&self, inner: WeylElement<$scalar>) -> $element {
                $element {
                    algebra: self.inner.clone(),
                    inner,
                }
            }

            fn require_element(&self, element: &$element) -> PyResult<()> {
                if *self.inner != *element.algebra {
                    return Err(PyValueError::new_err(
                        "Weyl element belongs to a different commutator context",
                    ));
                }
                Ok(())
            }

            fn parse_scalars(items: Vec<Bound<'_, PyAny>>) -> PyResult<Vec<$scalar>> {
                items.iter().map($parse).collect()
            }

            fn parse_matrix(rows: Vec<Vec<Bound<'_, PyAny>>>) -> PyResult<Vec<Vec<$scalar>>> {
                rows.into_iter().map(Self::parse_scalars).collect()
            }

            fn wrap_matrix(matrix: Vec<Vec<$scalar>>) -> Vec<Vec<$py_scalar>> {
                matrix
                    .into_iter()
                    .map(|row| row.into_iter().map($wrap).collect())
                    .collect()
            }
        }

        #[pymethods]
        impl $alg {
            /// Construct the standard rank-n Weyl algebra with generator order
            /// all positions followed by all momenta.
            #[new]
            fn new(pairs: usize) -> PyResult<Self> {
                WeylAlgebra::<$scalar>::try_standard(pairs)
                    .map(|inner| Self {
                        inner: Arc::new(inner),
                    })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Construct from an alternating commutator matrix.
            #[staticmethod]
            fn from_commutator(rows: Vec<Vec<Bound<'_, PyAny>>>) -> PyResult<Self> {
                WeylAlgebra::from_commutator(Self::parse_matrix(rows)?)
                    .map(|inner| Self {
                        inner: Arc::new(inner),
                    })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Number of ordered PBW generators.
            fn dim(&self) -> usize {
                self.inner.dim()
            }

            /// Standard Weyl rank, or None for a general alternating
            /// presentation.
            fn standard_pairs(&self) -> Option<usize> {
                self.inner.standard_pairs()
            }

            /// Alternating commutator matrix in generator order.
            fn commutator_form(&self) -> Vec<Vec<$py_scalar>> {
                Self::wrap_matrix(self.inner.commutator_form().to_vec())
            }

            /// Additive identity.
            fn zero(&self) -> $element {
                self.wrap_element(self.inner.zero())
            }

            /// Multiplicative identity.
            fn one(&self) -> $element {
                self.wrap_element(self.inner.one())
            }

            /// Embed a scalar constant.
            fn scalar(&self, value: &Bound<'_, PyAny>) -> PyResult<$element> {
                Ok(self.wrap_element(self.inner.scalar($parse(value)?)))
            }

            /// Return one ordered generator.
            fn generator(&self, index: usize) -> PyResult<$element> {
                self.inner
                    .try_generator(index)
                    .map(|element| self.wrap_element(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Return a standard position generator.
            fn x(&self, index: usize) -> PyResult<$element> {
                self.inner
                    .try_x(index)
                    .map(|element| self.wrap_element(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Return a standard differential generator.
            fn d(&self, index: usize) -> PyResult<$element> {
                self.inner
                    .try_d(index)
                    .map(|element| self.wrap_element(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Construct one checked PBW monomial.
            fn monomial(
                &self,
                exponents: Vec<u128>,
                coefficient: &Bound<'_, PyAny>,
            ) -> PyResult<$element> {
                self.inner
                    .try_monomial(&exponents, $parse(coefficient)?)
                    .map(|element| self.wrap_element(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Multiply under optional sparse-term and charged-work limits.
            #[pyo3(signature = (left, right, max_terms=None, max_steps=None))]
            fn mul(
                &self,
                left: &$element,
                right: &$element,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(left)?;
                self.require_element(right)?;
                self.inner
                    .checked_mul_with_budget(
                        &left.inner,
                        &right.inner,
                        expansion_budget(max_terms, max_steps),
                    )
                    .map(|element| self.wrap_element(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Compute a power under optional sparse-term and charged-work
            /// limits.
            #[pyo3(signature = (value, exponent, max_terms=None, max_steps=None))]
            fn pow(
                &self,
                value: &$element,
                exponent: u128,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(value)?;
                self.inner
                    .checked_pow_with_budget(
                        &value.inner,
                        exponent,
                        expansion_budget(max_terms, max_steps),
                    )
                    .map(|element| self.wrap_element(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Lie commutator under optional sparse-term and charged-work
            /// limits.
            #[pyo3(signature = (left, right, max_terms=None, max_steps=None))]
            fn commutator(
                &self,
                left: &$element,
                right: &$element,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(left)?;
                self.require_element(right)?;
                self.inner
                    .checked_commutator_with_budget(
                        &left.inner,
                        &right.inner,
                        expansion_budget(max_terms, max_steps),
                    )
                    .map(|element| self.wrap_element(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Check commutation with every generator under optional expansion
            /// limits.
            #[pyo3(signature = (value, max_terms=None, max_steps=None))]
            fn is_central(
                &self,
                value: &$element,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<bool> {
                self.require_element(value)?;
                self.inner
                    .is_central_with_budget(
                        &value.inner,
                        expansion_budget(max_terms, max_steps),
                    )
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Certified linear radical generators in source coordinates.
            #[pyo3(signature = (max_terms=None, max_steps=None))]
            fn radical_generators(
                &self,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<Vec<$element>> {
                self.inner
                    .radical_generators_with_budget(expansion_budget(max_terms, max_steps))
                    .map(|generators| {
                        generators
                            .into_iter()
                            .map(|element| self.wrap_element(element))
                            .collect()
                    })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Certified characteristic-p centre generators in source
            /// coordinates. Characteristic-zero backends raise ValueError.
            #[pyo3(signature = (max_terms=None, max_steps=None))]
            fn center_generators(
                &self,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<Vec<$element>> {
                self.inner
                    .positive_characteristic_center_with_budget(expansion_budget(
                        max_terms,
                        max_steps,
                    ))
                    .map(|center| {
                        center
                            .generators()
                            .iter()
                            .map(|generator| {
                                self.wrap_element(generator.source_element().clone())
                            })
                            .collect()
                    })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Apply the standard Fourier automorphism.
            #[pyo3(signature = (value, max_terms=None, max_steps=None))]
            fn fourier(
                &self,
                value: &$element,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(value)?;
                self.inner
                    .fourier_automorphism()
                    .and_then(|map| {
                        map.apply_with_budget(
                            &value.inner,
                            expansion_budget(max_terms, max_steps),
                        )
                    })
                    .map(|element| self.wrap_element(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Apply the formal-adjoint anti-automorphism.
            #[pyo3(signature = (value, max_terms=None, max_steps=None))]
            fn formal_adjoint(
                &self,
                value: &$element,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(value)?;
                self.inner
                    .formal_adjoint()
                    .and_then(|map| {
                        map.apply_with_budget(
                            &value.inner,
                            expansion_budget(max_terms, max_steps),
                        )
                    })
                    .map(|element| self.wrap_element(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Reduce an element modulo `z_i^p = central_values[i]` and return
            /// its canonical PBW representative.
            fn central_reduce(
                &self,
                value: &$element,
                central_values: Vec<Bound<'_, PyAny>>,
                max_basis_dimension: usize,
            ) -> PyResult<$element> {
                self.require_element(value)?;
                let fiber = self
                    .inner
                    .central_fiber(
                        Self::parse_scalars(central_values)?,
                        WeylRepresentationBudget::new(max_basis_dimension, 0, 0),
                    )
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                let reduced = fiber
                    .reduce(&value.inner)
                    .and_then(|element| fiber.lift(&element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                Ok(self.wrap_element(reduced))
            }

            /// Compare the characteristic-two central reduction with the
            /// independent Clifford product oracle.
            #[pyo3(signature = (left, right, central_values, max_basis_dimension, max_terms=None, max_steps=None))]
            fn clifford_fiber_products_agree(
                &self,
                left: &$element,
                right: &$element,
                central_values: Vec<Bound<'_, PyAny>>,
                max_basis_dimension: usize,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<bool> {
                self.require_element(left)?;
                self.require_element(right)?;
                self.inner
                    .clifford_central_fiber(
                        Self::parse_scalars(central_values)?,
                        WeylRepresentationBudget::new(max_basis_dimension, 0, 0),
                    )
                    .and_then(|bridge| {
                        bridge.products_agree_with_budget(
                            &left.inner,
                            &right.inner,
                            expansion_budget(max_terms, max_steps),
                        )
                    })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Exact generator matrices for a bounded split central-character
            /// module. Roots must satisfy `root[i]^p = central_values[i]`.
            fn central_character_generator_matrices(
                &self,
                central_values: Vec<Bound<'_, PyAny>>,
                splitting_roots: Vec<Bound<'_, PyAny>>,
                max_basis_dimension: usize,
                max_matrix_entries: usize,
                max_steps: u128,
            ) -> PyResult<Vec<Vec<Vec<$py_scalar>>>> {
                self.inner
                    .split_central_character_module(
                        Self::parse_scalars(central_values)?,
                        Self::parse_scalars(splitting_roots)?,
                        WeylRepresentationBudget::new(
                            max_basis_dimension,
                            max_matrix_entries,
                            max_steps,
                        ),
                    )
                    .map(|module| {
                        module
                            .generator_matrices()
                            .iter()
                            .cloned()
                            .map(Self::wrap_matrix)
                            .collect()
                    })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            fn __repr__(&self) -> String {
                match self.inner.standard_pairs() {
                    Some(pairs) => format!("{}(standard_pairs={pairs})", $alg_name),
                    None => format!("{}(dim={})", $alg_name, self.inner.dim()),
                }
            }
        }

        #[pyclass(name = $element_name, module = "ogdoad", from_py_object)]
        #[derive(Clone)]
        pub(crate) struct $element {
            algebra: Arc<WeylAlgebra<$scalar>>,
            inner: WeylElement<$scalar>,
        }

        impl $element {
            fn require_same_context(&self, other: &Self) -> PyResult<()> {
                if *self.algebra != *other.algebra {
                    return Err(PyValueError::new_err(
                        "Weyl elements belong to different commutator contexts",
                    ));
                }
                Ok(())
            }

            fn wrapped(&self, inner: WeylElement<$scalar>) -> Self {
                Self {
                    algebra: self.algebra.clone(),
                    inner,
                }
            }
        }

        #[pymethods]
        impl $element {
            /// Number of ordered PBW generators.
            fn dim(&self) -> usize {
                self.inner.dim()
            }

            /// Number of nonzero PBW terms.
            fn term_count(&self) -> usize {
                self.inner.term_count()
            }

            /// Whether this is the additive identity.
            fn is_zero(&self) -> bool {
                self.inner.is_zero()
            }

            /// Canonical sparse terms as `(exponents, coefficient)` pairs.
            fn terms(&self) -> Vec<(Vec<u128>, $py_scalar)> {
                self.inner
                    .terms()
                    .iter()
                    .map(|(monomial, coefficient)| {
                        (monomial.exponents().to_vec(), $wrap(coefficient.clone()))
                    })
                    .collect()
            }

            /// Owning monomorphic Weyl context.
            fn algebra(&self) -> $alg {
                $alg {
                    inner: self.algebra.clone(),
                }
            }

            /// Scalar multiplication without changing the Weyl context.
            fn scale(&self, scalar: &Bound<'_, PyAny>) -> PyResult<Self> {
                self.algebra
                    .scalar_mul(&$parse(scalar)?, &self.inner)
                    .map(|element| self.wrapped(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Budgeted multiplication convenience on the element itself.
            #[pyo3(signature = (other, max_terms=None, max_steps=None))]
            fn mul(
                &self,
                other: &Self,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<Self> {
                self.require_same_context(other)?;
                self.algebra
                    .checked_mul_with_budget(
                        &self.inner,
                        &other.inner,
                        expansion_budget(max_terms, max_steps),
                    )
                    .map(|element| self.wrapped(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Budgeted PBW power.
            #[pyo3(signature = (exponent, max_terms=None, max_steps=None))]
            fn pow(
                &self,
                exponent: u128,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<Self> {
                self.algebra
                    .checked_pow_with_budget(
                        &self.inner,
                        exponent,
                        expansion_budget(max_terms, max_steps),
                    )
                    .map(|element| self.wrapped(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            fn __add__(&self, other: &Self) -> PyResult<Self> {
                self.require_same_context(other)?;
                self.algebra
                    .add(&self.inner, &other.inner)
                    .map(|element| self.wrapped(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            fn __sub__(&self, other: &Self) -> PyResult<Self> {
                self.require_same_context(other)?;
                self.algebra
                    .add(&self.inner, &(-other.inner.clone()))
                    .map(|element| self.wrapped(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            fn __neg__(&self) -> Self {
                self.wrapped(-self.inner.clone())
            }

            fn __mul__(&self, other: &Self) -> PyResult<Self> {
                self.mul(other, None, None)
            }

            fn __pow__(&self, exponent: u128, modulus: Option<&Bound<'_, PyAny>>) -> PyResult<Self> {
                if modulus.is_some() {
                    return Err(PyValueError::new_err("Weyl power does not take a modulus"));
                }
                self.pow(exponent, None, None)
            }

            fn __eq__(&self, other: &Self) -> bool {
                *self.algebra == *other.algebra && self.inner == other.inner
            }

            fn __repr__(&self) -> String {
                self.inner.to_string()
            }

            fn __str__(&self) -> String {
                self.inner.to_string()
            }
        }
    };
}

weyl_backend!(
    PyRationalWeylAlgebra,
    PyRationalWeylElement,
    "RationalWeylAlgebra",
    "RationalWeylElement",
    Rational,
    PyRational,
    parse_rational,
    wrap_rational
);

weyl_backend!(
    PyNimberWeylAlgebra,
    PyNimberWeylElement,
    "NimberWeylAlgebra",
    "NimberWeylElement",
    Nimber,
    PyNimber,
    parse_nimber,
    wrap_nimber
);

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyRationalWeylAlgebra>()?;
    module.add_class::<PyRationalWeylElement>()?;
    module.add_class::<PyNimberWeylAlgebra>()?;
    module.add_class::<PyNimberWeylElement>()?;
    Ok(())
}
