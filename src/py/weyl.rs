//! Selected monomorphic Python bindings for the finite-support Weyl pillar.
//!
//! Rational, Fp3, and Nimber algebras/elements remain separate Python classes.
//! Every materializing product, transformation, centre transport, finite
//! fibre, and module action keeps the Rust budget and error distinctions
//! visible.

use super::scalars::{
    parse_fp3, parse_nimber, parse_rational, wrap_fp3, wrap_nimber, wrap_rational, PyFp3, PyNimber,
    PyRational,
};
use crate::scalar::{Fp, Nimber, Rational};
use crate::weyl::{
    SparsePolynomial, WeylAlgebra, WeylAutomorphism, WeylElement, WeylExpansionBudget,
    WeylFiltration, WeylHomomorphism, WeylPSymbolPresentation, WeylRepresentationBudget,
};
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use std::sync::Arc;

type F3 = Fp<3>;

fn expansion_budget(max_terms: Option<usize>, max_steps: Option<u128>) -> WeylExpansionBudget {
    WeylExpansionBudget::new(
        max_terms.unwrap_or(usize::MAX),
        max_steps.unwrap_or(u128::MAX),
    )
}

fn filtration(name: &str) -> PyResult<WeylFiltration> {
    match name {
        "bernstein" => Ok(WeylFiltration::Bernstein),
        "differential" | "differential_order" => Ok(WeylFiltration::DifferentialOrder),
        _ => Err(PyValueError::new_err(
            "Weyl filtration must be 'bernstein' or 'differential_order'",
        )),
    }
}

macro_rules! weyl_backend {
    (
        $alg:ident,
        $element:ident,
        $poly:ident,
        $psymbol:ident,
        $alg_name:literal,
        $element_name:literal,
        $poly_name:literal,
        $psymbol_name:literal,
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

            fn wrap_polynomial(&self, inner: SparsePolynomial<$scalar>) -> $poly {
                $poly { inner }
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


            fn wrap_scalars(values: Vec<$scalar>) -> Vec<$py_scalar> {
                values.into_iter().map($wrap).collect()
            }

            fn pullback_values(
                &self,
                map: WeylAutomorphism<$scalar>,
                central_values: Vec<Bound<'_, PyAny>>,
                max_basis_dimension: usize,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<Vec<$py_scalar>> {
                map.pullback_central_character(
                    Self::parse_scalars(central_values)?,
                    WeylRepresentationBudget::new(max_basis_dimension, 0, 0),
                    expansion_budget(max_terms, max_steps),
                )
                .map(|report| Self::wrap_scalars(report.pulled_back_values().to_vec()))
                .map_err(|error| PyValueError::new_err(error.to_string()))
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

            /// Direct sum with another Weyl commutator context.
            fn direct_sum(&self, other: &Self) -> PyResult<Self> {
                self.inner
                    .try_direct_sum(&other.inner)
                    .map(|inner| Self {
                        inner: Arc::new(inner),
                    })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Apply a checked affine-linear homomorphism into `target`.
            #[pyo3(signature = (target, value, linear, translation, max_terms=None, max_steps=None))]
            fn affine_map_to(
                &self,
                target: &Self,
                value: &$element,
                linear: Vec<Vec<Bound<'_, PyAny>>>,
                translation: Vec<Bound<'_, PyAny>>,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(value)?;
                WeylHomomorphism::try_new(
                    (*self.inner).clone(),
                    (*target.inner).clone(),
                    Self::parse_matrix(linear)?,
                    Self::parse_scalars(translation)?,
                )
                .and_then(|map| {
                    map.apply_with_budget(
                        &value.inner,
                        expansion_budget(max_terms, max_steps),
                    )
                })
                .map(|inner| target.wrap_element(inner))
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

            /// Bernstein filtration degree; None for zero.
            fn bernstein_degree(&self, value: &$element) -> PyResult<Option<u128>> {
                self.require_element(value)?;
                self.inner
                    .bernstein_degree(&value.inner)
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Differential-operator order; None for zero.
            fn differential_order(&self, value: &$element) -> PyResult<Option<u128>> {
                self.require_element(value)?;
                self.inner
                    .differential_order(&value.inner)
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Principal symbol for the named filtration.
            fn principal_symbol(
                &self,
                value: &$element,
                filtration_name: &str,
            ) -> PyResult<$poly> {
                self.require_element(value)?;
                self.inner
                    .principal_symbol(&value.inner, filtration(filtration_name)?)
                    .map(|inner| self.wrap_polynomial(inner))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Constant Poisson bracket of two commutative Weyl symbols.
            #[pyo3(signature = (left, right, max_terms=None, max_steps=None))]
            fn poisson_bracket(
                &self,
                left: &$poly,
                right: &$poly,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$poly> {
                self.inner
                    .poisson_bracket_with_budget(
                        &left.inner,
                        &right.inner,
                        expansion_budget(max_terms, max_steps),
                    )
                    .map(|inner| self.wrap_polynomial(inner))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Apply a standard Weyl operator to a sparse multivariate
            /// polynomial.
            #[pyo3(signature = (operator, polynomial, max_terms=None, max_steps=None))]
            fn act_on_sparse_polynomial(
                &self,
                operator: &$element,
                polynomial: &$poly,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$poly> {
                self.require_element(operator)?;
                self.inner
                    .act_on_sparse_poly_with_budget(
                        &operator.inner,
                        &polynomial.inner,
                        expansion_budget(max_terms, max_steps),
                    )
                    .map(|inner| self.wrap_polynomial(inner))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Multiply in the polynomial hbar deformation and specialize the
            /// result at the supplied scalar value.
            #[pyo3(signature = (left, right, hbar, max_terms=None, max_steps=None))]
            fn hbar_product(
                &self,
                left: &$element,
                right: &$element,
                hbar: &Bound<'_, PyAny>,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(left)?;
                self.require_element(right)?;
                let family = self.inner.hbar_deformation();
                let left = family
                    .lift_element(&left.inner)
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                let right = family
                    .lift_element(&right.inner)
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                let product = family
                    .deformation_algebra()
                    .checked_mul_with_budget(
                        &left,
                        &right,
                        expansion_budget(max_terms, max_steps),
                    )
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                family
                    .specialize_element_at(&product, &$parse(hbar)?)
                    .map(|inner| self.wrap_element(inner))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Commute in the polynomial hbar deformation and specialize the
            /// result at the supplied scalar value.
            #[pyo3(signature = (left, right, hbar, max_terms=None, max_steps=None))]
            fn hbar_commutator(
                &self,
                left: &$element,
                right: &$element,
                hbar: &Bound<'_, PyAny>,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(left)?;
                self.require_element(right)?;
                let family = self.inner.hbar_deformation();
                let left = family
                    .lift_element(&left.inner)
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                let right = family
                    .lift_element(&right.inner)
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                let commutator = family
                    .deformation_algebra()
                    .checked_commutator_with_budget(
                        &left,
                        &right,
                        expansion_budget(max_terms, max_steps),
                    )
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                family
                    .specialize_element_at(&commutator, &$parse(hbar)?)
                    .map(|inner| self.wrap_element(inner))
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

            /// Exact rank over the characteristic-p centre, or None when the
            /// represented rank exceeds u128.
            fn center_rank_over_center(&self) -> PyResult<Option<u128>> {
                self.inner
                    .positive_characteristic_center()
                    .map(|center| center.basis_over_center().rank_over_center())
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// One lazy PBW basis element over the characteristic-p centre,
            /// transported to source coordinates.
            #[pyo3(signature = (index, max_terms=None, max_steps=None))]
            fn center_basis_element(
                &self,
                index: u128,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.inner
                    .positive_characteristic_center_with_budget(expansion_budget(
                        max_terms,
                        max_steps,
                    ))
                    .and_then(|center| {
                        center.basis_over_center().source_element_at_with_budget(
                            index,
                            expansion_budget(max_terms, max_steps),
                        )
                    })
                    .map(|inner| self.wrap_element(inner))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// `(Weyl rank, radical rank)` of the certified Darboux tensor
            /// presentation.
            fn darboux_ranks(&self) -> PyResult<(usize, usize)> {
                self.inner
                    .darboux_decomposition()
                    .map(|decomposition| {
                        (decomposition.weyl_rank(), decomposition.central_rank())
                    })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Transport a source element into certified Darboux-plus-radical
            /// coordinates, returning its normal algebra and element together.
            #[pyo3(signature = (value, max_terms=None, max_steps=None))]
            fn darboux_to_normal(
                &self,
                value: &$element,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<(Self, $element)> {
                self.require_element(value)?;
                let decomposition = self
                    .inner
                    .darboux_decomposition()
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                let normal = decomposition
                    .to_normal_with_budget(
                        &value.inner,
                        expansion_budget(max_terms, max_steps),
                    )
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                let algebra = Self {
                    inner: Arc::new(decomposition.normal_algebra().clone()),
                };
                let element = algebra.wrap_element(normal);
                Ok((algebra, element))
            }

            /// Transport an element of this algebra's certified Darboux normal
            /// presentation back to source coordinates.
            #[pyo3(signature = (value, max_terms=None, max_steps=None))]
            fn darboux_from_normal(
                &self,
                value: &$element,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                let decomposition = self
                    .inner
                    .darboux_decomposition()
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                if *value.algebra != *decomposition.normal_algebra() {
                    return Err(PyValueError::new_err(
                        "Weyl element does not belong to this Darboux normal context",
                    ));
                }
                decomposition
                    .from_normal_with_budget(
                        &value.inner,
                        expansion_budget(max_terms, max_steps),
                    )
                    .map(|inner| self.wrap_element(inner))
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

            /// Apply the inverse standard Fourier automorphism.
            #[pyo3(signature = (value, max_terms=None, max_steps=None))]
            fn fourier_inverse(
                &self,
                value: &$element,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(value)?;
                self.inner
                    .fourier_automorphism()
                    .and_then(|map| {
                        map.inverse().apply_with_budget(
                            &value.inner,
                            expansion_budget(max_terms, max_steps),
                        )
                    })
                    .map(|element| self.wrap_element(element))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Apply standard diagonal symplectic scaling.
            #[pyo3(signature = (value, scales, max_terms=None, max_steps=None))]
            fn scaling(
                &self,
                value: &$element,
                scales: Vec<Bound<'_, PyAny>>,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(value)?;
                self.inner
                    .scaling_automorphism(&Self::parse_scalars(scales)?)
                    .and_then(|map| {
                        map.apply_with_budget(
                            &value.inner,
                            expansion_budget(max_terms, max_steps),
                        )
                    })
                    .map(|inner| self.wrap_element(inner))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Apply a symmetric momentum shear `d -> d + A*x`.
            #[pyo3(signature = (value, shear, max_terms=None, max_steps=None))]
            fn shear(
                &self,
                value: &$element,
                shear: Vec<Vec<Bound<'_, PyAny>>>,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(value)?;
                self.inner
                    .shear_automorphism(&Self::parse_matrix(shear)?)
                    .and_then(|map| {
                        map.apply_with_budget(
                            &value.inner,
                            expansion_budget(max_terms, max_steps),
                        )
                    })
                    .map(|inner| self.wrap_element(inner))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Apply scalar translation of every standard generator.
            #[pyo3(signature = (value, translation, max_terms=None, max_steps=None))]
            fn translation(
                &self,
                value: &$element,
                translation: Vec<Bound<'_, PyAny>>,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(value)?;
                self.inner
                    .translation_automorphism(&Self::parse_scalars(translation)?)
                    .and_then(|map| {
                        map.apply_with_budget(
                            &value.inner,
                            expansion_budget(max_terms, max_steps),
                        )
                    })
                    .map(|inner| self.wrap_element(inner))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Apply the parity automorphism `z_i -> -z_i`.
            #[pyo3(signature = (value, max_terms=None, max_steps=None))]
            fn parity(
                &self,
                value: &$element,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(value)?;
                self.inner
                    .parity_automorphism()
                    .and_then(|map| {
                        map.apply_with_budget(
                            &value.inner,
                            expansion_budget(max_terms, max_steps),
                        )
                    })
                    .map(|inner| self.wrap_element(inner))
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

            /// Pull a central character back through the Fourier automorphism.
            #[pyo3(signature = (central_values, max_basis_dimension, max_terms=None, max_steps=None))]
            fn fourier_central_character(
                &self,
                central_values: Vec<Bound<'_, PyAny>>,
                max_basis_dimension: usize,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<Vec<$py_scalar>> {
                let map = self
                    .inner
                    .fourier_automorphism()
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                self.pullback_values(
                    map,
                    central_values,
                    max_basis_dimension,
                    max_terms,
                    max_steps,
                )
            }

            /// Pull a central character back through diagonal scaling.
            #[pyo3(signature = (central_values, scales, max_basis_dimension, max_terms=None, max_steps=None))]
            fn scaling_central_character(
                &self,
                central_values: Vec<Bound<'_, PyAny>>,
                scales: Vec<Bound<'_, PyAny>>,
                max_basis_dimension: usize,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<Vec<$py_scalar>> {
                let map = self
                    .inner
                    .scaling_automorphism(&Self::parse_scalars(scales)?)
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                self.pullback_values(
                    map,
                    central_values,
                    max_basis_dimension,
                    max_terms,
                    max_steps,
                )
            }

            /// Pull a central character back through a symmetric momentum
            /// shear, retaining the characteristic-two quadratic correction.
            #[pyo3(signature = (central_values, shear, max_basis_dimension, max_terms=None, max_steps=None))]
            fn shear_central_character(
                &self,
                central_values: Vec<Bound<'_, PyAny>>,
                shear: Vec<Vec<Bound<'_, PyAny>>>,
                max_basis_dimension: usize,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<Vec<$py_scalar>> {
                let map = self
                    .inner
                    .shear_automorphism(&Self::parse_matrix(shear)?)
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                self.pullback_values(
                    map,
                    central_values,
                    max_basis_dimension,
                    max_terms,
                    max_steps,
                )
            }

            /// Pull a central character back through scalar translation.
            #[pyo3(signature = (central_values, translation, max_basis_dimension, max_terms=None, max_steps=None))]
            fn translation_central_character(
                &self,
                central_values: Vec<Bound<'_, PyAny>>,
                translation: Vec<Bound<'_, PyAny>>,
                max_basis_dimension: usize,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<Vec<$py_scalar>> {
                let map = self
                    .inner
                    .translation_automorphism(&Self::parse_scalars(translation)?)
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                self.pullback_values(
                    map,
                    central_values,
                    max_basis_dimension,
                    max_terms,
                    max_steps,
                )
            }

            /// Construct the characteristic-p symbol presentation of a
            /// standard central fibre.
            fn psymbol(
                &self,
                central_values: Vec<Bound<'_, PyAny>>,
                max_basis_dimension: usize,
            ) -> PyResult<$psymbol> {
                self.inner
                    .psymbol_presentation(
                        Self::parse_scalars(central_values)?,
                        WeylRepresentationBudget::new(max_basis_dimension, 0, 0),
                    )
                    .map(|inner| $psymbol {
                        algebra: self.inner.clone(),
                        inner,
                    })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Reduce through the certified Darboux fibre of an arbitrary
            /// alternating presentation and return the canonical source lift.
            #[pyo3(signature = (value, paired_values, radical_values, max_basis_dimension, max_terms=None, max_steps=None))]
            fn transported_central_reduce(
                &self,
                value: &$element,
                paired_values: Vec<Bound<'_, PyAny>>,
                radical_values: Vec<Bound<'_, PyAny>>,
                max_basis_dimension: usize,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<$element> {
                self.require_element(value)?;
                let fiber = self
                    .inner
                    .transported_central_fiber(
                        Self::parse_scalars(paired_values)?,
                        Self::parse_scalars(radical_values)?,
                        WeylRepresentationBudget::new(max_basis_dimension, 0, 0),
                    )
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                let reduced = fiber
                    .reduce_with_budget(
                        &value.inner,
                        expansion_budget(max_terms, max_steps),
                    )
                    .and_then(|element| {
                        fiber.lift_with_budget(
                            &element,
                            expansion_budget(max_terms, max_steps),
                        )
                    })
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                Ok(self.wrap_element(reduced))
            }

            /// Compare a transported-fibre product with multiplication in the
            /// original alternating presentation.
            #[allow(clippy::too_many_arguments)]
            #[pyo3(signature = (left, right, paired_values, radical_values, max_basis_dimension, max_terms=None, max_steps=None))]
            fn transported_fiber_products_agree(
                &self,
                left: &$element,
                right: &$element,
                paired_values: Vec<Bound<'_, PyAny>>,
                radical_values: Vec<Bound<'_, PyAny>>,
                max_basis_dimension: usize,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<bool> {
                self.require_element(left)?;
                self.require_element(right)?;
                let fiber = self
                    .inner
                    .transported_central_fiber(
                        Self::parse_scalars(paired_values)?,
                        Self::parse_scalars(radical_values)?,
                        WeylRepresentationBudget::new(max_basis_dimension, 0, 0),
                    )
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                let budget = expansion_budget(max_terms, max_steps);
                let left = fiber
                    .reduce_with_budget(&left.inner, budget)
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                let right = fiber
                    .reduce_with_budget(&right.inner, budget)
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                fiber
                    .products_agree_with_source(&left, &right, budget)
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

        #[pyclass(name = $poly_name, module = "ogdoad", from_py_object)]
        #[derive(Clone)]
        pub(crate) struct $poly {
            inner: SparsePolynomial<$scalar>,
        }

        #[pymethods]
        impl $poly {
            /// Construct the zero polynomial in `dim` variables.
            #[new]
            fn new(dim: usize) -> Self {
                Self {
                    inner: SparsePolynomial::zero(dim),
                }
            }

            /// Construct a scalar polynomial in `dim` variables.
            #[staticmethod]
            fn scalar(dim: usize, coefficient: &Bound<'_, PyAny>) -> PyResult<Self> {
                Ok(Self {
                    inner: SparsePolynomial::scalar(dim, $parse(coefficient)?),
                })
            }

            /// Construct one sparse monomial.
            #[staticmethod]
            fn monomial(
                exponents: Vec<u128>,
                coefficient: &Bound<'_, PyAny>,
            ) -> PyResult<Self> {
                Ok(Self {
                    inner: SparsePolynomial::monomial(&exponents, $parse(coefficient)?),
                })
            }

            /// Construct one variable in a fixed-dimensional polynomial ring.
            #[staticmethod]
            fn variable(dim: usize, index: usize) -> PyResult<Self> {
                SparsePolynomial::try_variable(dim, index)
                    .map(|inner| Self { inner })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Number of polynomial variables.
            fn dim(&self) -> usize {
                self.inner.dim()
            }

            /// Number of nonzero monomials.
            fn term_count(&self) -> usize {
                self.inner.term_count()
            }

            /// Whether this is the zero polynomial.
            fn is_zero(&self) -> bool {
                self.inner.is_zero()
            }

            /// Maximum total degree, or None for zero/overflow.
            fn total_degree(&self) -> Option<u128> {
                self.inner.total_degree()
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

            /// Formal partial derivative in one variable.
            fn partial_derivative(&self, index: usize) -> PyResult<Self> {
                self.inner
                    .partial_derivative(index)
                    .map(|inner| Self { inner })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Scalar multiplication.
            fn scale(&self, scalar: &Bound<'_, PyAny>) -> PyResult<Self> {
                self.inner
                    .checked_mul(&SparsePolynomial::scalar(
                        self.inner.dim(),
                        $parse(scalar)?,
                    ))
                    .map(|inner| Self { inner })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Budgeted commutative multiplication.
            #[pyo3(signature = (other, max_terms=None, max_steps=None))]
            fn mul(
                &self,
                other: &Self,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<Self> {
                self.inner
                    .checked_mul_with_budget(
                        &other.inner,
                        expansion_budget(max_terms, max_steps),
                    )
                    .map(|inner| Self { inner })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            fn __add__(&self, other: &Self) -> PyResult<Self> {
                self.inner
                    .checked_add(&other.inner)
                    .map(|inner| Self { inner })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            fn __sub__(&self, other: &Self) -> PyResult<Self> {
                self.inner
                    .checked_add(&(-other.inner.clone()))
                    .map(|inner| Self { inner })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            fn __neg__(&self) -> Self {
                Self {
                    inner: -self.inner.clone(),
                }
            }

            fn __mul__(&self, other: &Self) -> PyResult<Self> {
                self.mul(other, None, None)
            }

            fn __eq__(&self, other: &Self) -> bool {
                self.inner == other.inner
            }

            fn __repr__(&self) -> String {
                self.inner.to_string()
            }

            fn __str__(&self) -> String {
                self.inner.to_string()
            }
        }

        #[pyclass(name = $psymbol_name, module = "ogdoad", from_py_object)]
        #[derive(Clone)]
        pub(crate) struct $psymbol {
            algebra: Arc<WeylAlgebra<$scalar>>,
            inner: WeylPSymbolPresentation<$scalar>,
        }

        #[pymethods]
        impl $psymbol {
            /// Positive characteristic `p`.
            fn characteristic(&self) -> u128 {
                self.inner.characteristic()
            }

            /// Number of rank-one p-symbol tensor factors.
            fn tensor_rank(&self) -> usize {
                self.inner.tensor_rank()
            }

            /// Ordered `(x_i^p, d_i^p)` parameter pairs.
            fn pairs(&self) -> Vec<($py_scalar, $py_scalar)> {
                self.inner
                    .pairs()
                    .iter()
                    .map(|pair| {
                        (
                            $wrap(pair.position_power().clone()),
                            $wrap(pair.momentum_power().clone()),
                        )
                    })
                    .collect()
            }

            /// Split status: None for a cited p-symbol presentation without a
            /// full-matrix certificate.
            fn brauer_split(&self) -> Option<bool> {
                self.inner.brauer_report().is_split()
            }

            /// Certify that this odd-characteristic p-symbol tensor product is
            /// a full matrix algebra using exact rank of every reduced PBW
            /// basis image.
            fn certify_split(
                &self,
                splitting_roots: Vec<Bound<'_, PyAny>>,
                max_basis_dimension: usize,
                max_matrix_entries: usize,
                max_steps: u128,
            ) -> PyResult<bool> {
                let certificate = self
                    .algebra
                    .odd_matrix_fiber_certificate(
                        self.inner.fiber().central_values().to_vec(),
                        $alg::parse_scalars(splitting_roots)?,
                        WeylRepresentationBudget::new(
                            max_basis_dimension,
                            max_matrix_entries,
                            max_steps,
                        ),
                    )
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                self.inner
                    .brauer_report_with_matrix_certificate(&certificate)
                    .map(|report| report.is_split() == Some(true))
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Tensor noncommutative p-residue of an ambient PBW element after
            /// central reduction.
            fn p_residue(&self, value: &$element) -> PyResult<$py_scalar> {
                if *value.algebra != *self.algebra {
                    return Err(PyValueError::new_err(
                        "Weyl element belongs to a different p-symbol context",
                    ));
                }
                self.inner
                    .fiber()
                    .reduce(&value.inner)
                    .map_err(|error| PyValueError::new_err(error.to_string()))
                    .and_then(|element| {
                        self.inner
                            .p_residue(&element)
                            .map($wrap)
                            .map_err(|error| PyValueError::new_err(error.to_string()))
                    })
            }

            /// Check `p_residue = (-1)^rank * matrix_trace` on an exact split
            /// central-character module.
            fn split_trace_matches_residue(
                &self,
                value: &$element,
                splitting_roots: Vec<Bound<'_, PyAny>>,
                max_basis_dimension: usize,
                max_matrix_entries: usize,
                max_steps: u128,
            ) -> PyResult<bool> {
                if *value.algebra != *self.algebra {
                    return Err(PyValueError::new_err(
                        "Weyl element belongs to a different p-symbol context",
                    ));
                }
                let module = self
                    .algebra
                    .split_central_character_module(
                        self.inner.fiber().central_values().to_vec(),
                        $alg::parse_scalars(splitting_roots)?,
                        WeylRepresentationBudget::new(
                            max_basis_dimension,
                            max_matrix_entries,
                            max_steps,
                        ),
                    )
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                let reduced = self
                    .inner
                    .fiber()
                    .reduce(&value.inner)
                    .map_err(|error| PyValueError::new_err(error.to_string()))?;
                self.inner
                    .split_matrix_trace_matches_residue(
                        &module,
                        &reduced,
                        WeylRepresentationBudget::new(
                            max_basis_dimension,
                            max_matrix_entries,
                            max_steps,
                        ),
                    )
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            /// Verify and return the cyclic parameters `(b,c]` for one factor,
            /// where `c = x_i^p*d_i^p`.
            #[pyo3(signature = (pair, max_basis_dimension, max_terms=None, max_steps=None))]
            fn cyclic_factor(
                &self,
                pair: usize,
                max_basis_dimension: usize,
                max_terms: Option<usize>,
                max_steps: Option<u128>,
            ) -> PyResult<($py_scalar, $py_scalar)> {
                self.inner
                    .cyclic_factor(
                        pair,
                        WeylRepresentationBudget::new(max_basis_dimension, 0, 0),
                        expansion_budget(max_terms, max_steps),
                    )
                    .map(|factor| {
                        (
                            $wrap(factor.momentum_power().clone()),
                            $wrap(factor.artin_schreier_parameter().clone()),
                        )
                    })
                    .map_err(|error| PyValueError::new_err(error.to_string()))
            }

            fn __repr__(&self) -> String {
                format!(
                    "{}(characteristic={}, tensor_rank={})",
                    $psymbol_name,
                    self.inner.characteristic(),
                    self.inner.tensor_rank(),
                )
            }
        }
    };
}

weyl_backend!(
    PyRationalWeylAlgebra,
    PyRationalWeylElement,
    PyRationalSparsePolynomial,
    PyRationalWeylPSymbol,
    "RationalWeylAlgebra",
    "RationalWeylElement",
    "RationalSparsePolynomial",
    "RationalWeylPSymbol",
    Rational,
    PyRational,
    parse_rational,
    wrap_rational
);

weyl_backend!(
    PyFp3WeylAlgebra,
    PyFp3WeylElement,
    PyFp3SparsePolynomial,
    PyFp3WeylPSymbol,
    "Fp3WeylAlgebra",
    "Fp3WeylElement",
    "Fp3SparsePolynomial",
    "Fp3WeylPSymbol",
    F3,
    PyFp3,
    parse_fp3,
    wrap_fp3
);

weyl_backend!(
    PyNimberWeylAlgebra,
    PyNimberWeylElement,
    PyNimberSparsePolynomial,
    PyNimberWeylPSymbol,
    "NimberWeylAlgebra",
    "NimberWeylElement",
    "NimberSparsePolynomial",
    "NimberWeylPSymbol",
    Nimber,
    PyNimber,
    parse_nimber,
    wrap_nimber
);

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyRationalWeylAlgebra>()?;
    module.add_class::<PyRationalWeylElement>()?;
    module.add_class::<PyRationalSparsePolynomial>()?;
    module.add_class::<PyRationalWeylPSymbol>()?;
    module.add_class::<PyFp3WeylAlgebra>()?;
    module.add_class::<PyFp3WeylElement>()?;
    module.add_class::<PyFp3SparsePolynomial>()?;
    module.add_class::<PyFp3WeylPSymbol>()?;
    module.add_class::<PyNimberWeylAlgebra>()?;
    module.add_class::<PyNimberWeylElement>()?;
    module.add_class::<PyNimberSparsePolynomial>()?;
    module.add_class::<PyNimberWeylPSymbol>()?;
    Ok(())
}
