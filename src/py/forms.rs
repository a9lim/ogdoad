//! Python bindings for quadratic and bilinear form invariants across all
//! characteristics, together with Witt, local--global, Hermitian, symplectic,
//! integral-lattice, modular-form, and Brauer--Wall operations.

use super::engine::{
    F16Algebra, F25Algebra, F27Algebra, F4Algebra, F8Algebra, F9Algebra, Fp11Algebra,
    Fp11RationalFunctionAlgebra, Fp13Algebra, Fp13RationalFunctionAlgebra, Fp2Algebra, Fp3Algebra,
    Fp3RationalFunctionAlgebra, Fp5Algebra, Fp5RationalFunctionAlgebra, Fp7Algebra,
    Fp7RationalFunctionAlgebra, LaurentF25_6Algebra, LaurentF27_6Algebra, LaurentF9_6Algebra,
    LaurentFp11_6Algebra, LaurentFp13_6Algebra, LaurentFp3_6Algebra, LaurentFp5_6Algebra,
    LaurentFp7_6Algebra, NimberAlgebra, NimberMV, OrdinalAlgebra, Qp11_4Algebra, Qp13_4Algebra,
    Qp2_4Algebra, Qp3_4Algebra, Qp5_4Algebra, Qp7_4Algebra, Qq2_4_2Algebra, Qq2_4_3Algebra,
    Qq2_4_4Algebra, Qq3_4_2Algebra, Qq3_4_3Algebra, Qq5_4_2Algebra, RamifiedQp11_4E2Algebra,
    RamifiedQp11_4E3Algebra, RamifiedQp13_4E2Algebra, RamifiedQp13_4E3Algebra,
    RamifiedQp2_4E2Algebra, RamifiedQp2_4E3Algebra, RamifiedQp3_4E2Algebra, RamifiedQp3_4E3Algebra,
    RamifiedQp5_4E2Algebra, RamifiedQp5_4E3Algebra, RamifiedQp7_4E2Algebra, RamifiedQp7_4E3Algebra,
    RationalAlgebra, SurcomplexAlgebra, SurrealAlgebra,
};
use super::scalars::{
    parse_qp11_4, parse_qp13_4, parse_qp2_4, parse_qp3_4, parse_qp5_4, parse_qp7_4, parse_qq2_4_2,
    parse_qq2_4_3, parse_qq2_4_4, parse_qq3_4_2, parse_qq3_4_3, parse_qq5_4_2, parse_rational,
    parse_surcomplex, parse_surreal, wrap_fp11_rational_function, wrap_fp13_rational_function,
    wrap_fp3_rational_function, wrap_fp5_rational_function, wrap_fp7_rational_function,
    wrap_rational, wrap_surreal, PyRational, PySurreal,
};
use crate::clifford::{CliffordAlgebra, Metric};
use crate::forms::{
    Char2LocalDecomp, Char2QuadForm, FiniteChar2Field, FiniteHermitianForm, FiniteOddField,
    FunctionFieldPlace, HermitianForm, IntegralForm, SymplecticForm, WittClass, WittClassError,
    WittClassG,
};
use crate::scalar::{
    ExactFieldScalar, Fp, Fpn, Laurent, Nimber, Ordinal, Poly, Qp, Qq, Ramified, Rational,
    RationalFunction, ResidueField, Scalar, Surcomplex, Surreal, WittVec,
};
use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyTuple};
use pyo3::IntoPyObjectExt;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

fn parse_rational_vec(items: Vec<Bound<'_, PyAny>>) -> PyResult<Vec<Rational>> {
    items.iter().map(parse_rational).collect()
}

#[pyclass(name = "ArfInvariants", module = "ogdoad")]
struct PyArfInvariants {
    inner: crate::forms::ArfInvariants,
}

#[pymethods]
impl PyArfInvariants {
    #[getter]
    fn arf(&self) -> u128 {
        self.inner.arf
    }
    #[getter]
    fn rank(&self) -> usize {
        self.inner.rank
    }
    #[getter]
    fn radical_dim(&self) -> usize {
        self.inner.radical_dim
    }
    #[getter]
    fn radical_anisotropic(&self) -> bool {
        self.inner.radical_anisotropic
    }
    #[getter]
    fn o_type(&self) -> String {
        self.inner.o_type().to_string()
    }
    fn __repr__(&self) -> String {
        format!(
            "ArfInvariants(arf={}, type={}, rank={}, radical_dim={}, radical_anisotropic={})",
            self.inner.arf,
            self.inner.o_type(),
            self.inner.rank,
            self.inner.radical_dim,
            self.inner.radical_anisotropic,
        )
    }
}

#[pyclass(name = "BrownInvariants", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyBrownInvariants {
    inner: crate::forms::BrownInvariants,
}

#[pymethods]
impl PyBrownInvariants {
    #[getter]
    fn beta(&self) -> u128 {
        self.inner.beta
    }
    #[getter]
    fn rank(&self) -> usize {
        self.inner.rank
    }
    #[getter]
    fn radical_dim(&self) -> usize {
        self.inner.radical_dim
    }
    #[getter]
    fn radical_anisotropic(&self) -> bool {
        self.inner.radical_anisotropic
    }
    fn __repr__(&self) -> String {
        format!(
            "BrownInvariants(beta={}, rank={}, radical_dim={}, radical_anisotropic={})",
            self.inner.beta,
            self.inner.rank,
            self.inner.radical_dim,
            self.inner.radical_anisotropic
        )
    }
}

fn wrap_brown_result(inner: crate::forms::BrownInvariants) -> PyBrownInvariants {
    PyBrownInvariants { inner }
}

#[pyclass(name = "QuadricFit", module = "ogdoad")]
pub(crate) struct PyQuadricFit {
    inner: crate::forms::QuadricFit,
}

pub(crate) fn wrap_quadric_fit(inner: crate::forms::QuadricFit) -> PyQuadricFit {
    PyQuadricFit { inner }
}

#[pymethods]
impl PyQuadricFit {
    #[getter]
    fn constant(&self) -> bool {
        self.inner.constant
    }
    #[getter]
    fn diagonal(&self) -> Vec<bool> {
        self.inner.qd.clone()
    }
    #[getter]
    fn polar_rows(&self) -> Vec<u128> {
        self.inner.bmat.clone()
    }
    fn arf(&self) -> PyArfInvariants {
        PyArfInvariants {
            inner: self.inner.arf.clone(),
        }
    }
    fn is_genuinely_quadratic(&self) -> bool {
        self.inner.is_genuinely_quadratic()
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

/// Arf invariant (the char-2 Clifford classifier) of a nimber algebra.
#[pyfunction]
fn arf_nimber(alg: &NimberAlgebra) -> PyResult<PyArfInvariants> {
    let inner = crate::forms::arf_nimber(&alg.inner.metric).ok_or_else(|| {
        PyValueError::new_err("Arf invariant is undefined for general-bilinear metrics")
    })?;
    Ok(PyArfInvariants { inner })
}

/// Arf invariant of an ordinal-nimber Clifford metric when all coefficients
/// lie in a detected represented finite subfield.
#[pyfunction]
fn arf_ordinal_finite(alg: &OrdinalAlgebra) -> PyResult<PyArfInvariants> {
    let inner = crate::forms::arf_ordinal_finite(&alg.inner.metric).ok_or_else(|| {
        PyValueError::new_err(
            "ordinal Arf invariant is only implemented on detected finite ordinal-nimber windows",
        )
    })?;
    Ok(PyArfInvariants { inner })
}

/// Fit an F₂ quadratic form to a subset of `F_2^k`, returning the recovered
/// coefficients and Arf data if the set is a quadric.
#[pyfunction]
fn fit_f2_quadratic(set: Vec<u128>, k: usize) -> PyResult<Option<PyQuadricFit>> {
    const MAX_ANF_DIM: usize = 20;
    if k > MAX_ANF_DIM {
        return Err(PyValueError::new_err(format!(
            "fit_f2_quadratic is exponential in k; max supported k is {MAX_ANF_DIM}"
        )));
    }
    let domain_mask = if k == 0 { 0 } else { (1u128 << k) - 1 };
    if set.iter().any(|&v| v & !domain_mask != 0) {
        return Err(PyValueError::new_err(format!(
            "point outside F_2^{k} in fit_f2_quadratic input"
        )));
    }
    Ok(crate::forms::fit_f2_quadratic(&set, k).map(|inner| PyQuadricFit { inner }))
}

/// Raw Arf reduction over `F_2`: `qd` is the diagonal bit vector and `bmat`
/// packs the alternating polar rows as bitmasks.
#[pyfunction]
fn arf_f2(n: usize, qd: Vec<bool>, bmat: Vec<u128>) -> PyResult<PyArfInvariants> {
    if qd.len() != n || bmat.len() != n {
        return Err(PyValueError::new_err(
            "arf_f2 needs qd and bmat lengths equal to n",
        ));
    }
    if n > u128::BITS as usize {
        return Err(PyValueError::new_err("arf_f2 supports n <= 128"));
    }
    let domain_mask = if n == 0 {
        0
    } else if n >= u128::BITS as usize {
        u128::MAX
    } else {
        (1u128 << n) - 1
    };
    if bmat.iter().any(|&row| row & !domain_mask != 0) {
        return Err(PyValueError::new_err(
            "arf_f2 polar rows contain bits outside the n-dimensional domain",
        ));
    }
    Ok(PyArfInvariants {
        inner: crate::forms::arf_f2(n, &qd, &bmat),
    })
}

fn extraspecial_error(err: crate::forms::ExtraspecialError) -> PyErr {
    PyValueError::new_err(err.to_string())
}

#[pyclass(name = "ExtraspecialElement", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyExtraspecialElement {
    inner: crate::forms::ExtraspecialElement,
}

#[pymethods]
impl PyExtraspecialElement {
    #[new]
    fn new(central: bool, vector: u128) -> Self {
        PyExtraspecialElement {
            inner: crate::forms::ExtraspecialElement::new(central, vector),
        }
    }
    #[getter]
    fn central(&self) -> bool {
        self.inner.central()
    }
    #[getter]
    fn vector(&self) -> u128 {
        self.inner.vector()
    }
    fn __eq__(&self, other: &PyExtraspecialElement) -> bool {
        self.inner == other.inner
    }
    fn __repr__(&self) -> String {
        format!(
            "ExtraspecialElement(central={}, vector={})",
            self.inner.central(),
            self.inner.vector()
        )
    }
}

fn wrap_extraspecial_element(inner: crate::forms::ExtraspecialElement) -> PyExtraspecialElement {
    PyExtraspecialElement { inner }
}

#[pyclass(name = "Extraspecial2Group", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyExtraspecial2Group {
    inner: crate::forms::Extraspecial2Group,
}

#[pymethods]
impl PyExtraspecial2Group {
    #[new]
    fn new(qd: Vec<bool>, bmat: Vec<u128>) -> PyResult<Self> {
        crate::forms::Extraspecial2Group::from_f2(qd, bmat)
            .map(|inner| PyExtraspecial2Group { inner })
            .map_err(extraspecial_error)
    }
    #[staticmethod]
    fn from_nimber_algebra(alg: &NimberAlgebra) -> PyResult<Self> {
        crate::forms::Extraspecial2Group::from_nimber_metric(&alg.inner.metric)
            .map(|inner| PyExtraspecial2Group { inner })
            .map_err(extraspecial_error)
    }
    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim()
    }
    fn order_exponent(&self) -> usize {
        self.inner.order_exponent()
    }
    fn order_u128(&self) -> Option<u128> {
        self.inner.order_u128()
    }
    fn arf(&self) -> PyArfInvariants {
        PyArfInvariants {
            inner: self.inner.arf().clone(),
        }
    }
    fn extraspecial_type(&self) -> String {
        self.inner.extraspecial_type().to_string()
    }
    fn heisenberg_weil_representation(&self) -> Option<PyHeisenbergWeilRepresentation> {
        self.inner
            .heisenberg_weil_representation()
            .map(|inner| PyHeisenbergWeilRepresentation { inner })
    }
    fn identity(&self) -> PyExtraspecialElement {
        wrap_extraspecial_element(self.inner.identity())
    }
    fn central_generator(&self) -> PyExtraspecialElement {
        wrap_extraspecial_element(self.inner.central_generator())
    }
    fn generator(&self, i: usize) -> Option<PyExtraspecialElement> {
        self.inner.generator(i).map(wrap_extraspecial_element)
    }
    fn element(&self, central: bool, vector: u128) -> Option<PyExtraspecialElement> {
        self.inner
            .element(central, vector)
            .map(wrap_extraspecial_element)
    }
    fn contains(&self, x: &PyExtraspecialElement) -> bool {
        self.inner.contains(&x.inner)
    }
    fn q_value(&self, vector: u128) -> Option<bool> {
        self.inner.q_value(vector)
    }
    fn polar_value(&self, u: u128, v: u128) -> Option<bool> {
        self.inner.polar_value(u, v)
    }
    fn cocycle_value(&self, u: u128, v: u128) -> Option<bool> {
        self.inner.cocycle_value(u, v)
    }
    fn multiply(
        &self,
        x: &PyExtraspecialElement,
        y: &PyExtraspecialElement,
    ) -> Option<PyExtraspecialElement> {
        self.inner
            .multiply(&x.inner, &y.inner)
            .map(wrap_extraspecial_element)
    }
    fn inverse(&self, x: &PyExtraspecialElement) -> Option<PyExtraspecialElement> {
        self.inner.inverse(&x.inner).map(wrap_extraspecial_element)
    }
    fn square(&self, x: &PyExtraspecialElement) -> Option<PyExtraspecialElement> {
        self.inner.square(&x.inner).map(wrap_extraspecial_element)
    }
    fn commutator(
        &self,
        x: &PyExtraspecialElement,
        y: &PyExtraspecialElement,
    ) -> Option<PyExtraspecialElement> {
        self.inner
            .commutator(&x.inner, &y.inner)
            .map(wrap_extraspecial_element)
    }
    fn __eq__(&self, other: &PyExtraspecial2Group) -> bool {
        self.inner == other.inner
    }
    fn __repr__(&self) -> String {
        format!(
            "Extraspecial2Group(dim={}, order_exponent={}, type={})",
            self.inner.dim(),
            self.inner.order_exponent(),
            self.inner.extraspecial_type()
        )
    }
}

#[pyclass(
    name = "HeisenbergWeilRepresentation",
    module = "ogdoad",
    from_py_object
)]
#[derive(Clone)]
struct PyHeisenbergWeilRepresentation {
    inner: crate::forms::HeisenbergWeilRepresentation,
}

fn wrap_complex_matrix(rows: Vec<Vec<crate::forms::Complex64>>) -> Vec<Vec<PyComplex64>> {
    rows.into_iter()
        .map(|row| row.into_iter().map(wrap_complex64).collect())
        .collect()
}

#[pymethods]
impl PyHeisenbergWeilRepresentation {
    fn group(&self) -> PyExtraspecial2Group {
        PyExtraspecial2Group {
            inner: self.inner.group().clone(),
        }
    }
    #[getter]
    fn rank(&self) -> usize {
        self.inner.rank()
    }
    fn quotient_dim(&self) -> usize {
        self.inner.quotient_dim()
    }
    fn hilbert_dim_u128(&self) -> Option<u128> {
        self.inner.hilbert_dim_u128()
    }
    fn symplectic_basis(&self) -> Vec<u128> {
        self.inner.symplectic_basis().to_vec()
    }
    fn basis_coordinates(&self, vector: u128) -> Option<u128> {
        self.inner.basis_coordinates(vector)
    }
    fn apply_to_basis_state(
        &self,
        x: &PyExtraspecialElement,
        ket: u128,
    ) -> Option<(PyComplex64, u128)> {
        self.inner
            .apply_to_basis_state(&x.inner, ket)
            .map(|(phase, target)| (wrap_complex64(phase), target))
    }
    fn matrix(&self, x: &PyExtraspecialElement) -> Option<Vec<Vec<PyComplex64>>> {
        self.inner.matrix(&x.inner).map(wrap_complex_matrix)
    }
    fn transvection_intertwiner(&self, a: u128) -> Option<Vec<Vec<PyComplex64>>> {
        self.inner
            .transvection_intertwiner(a)
            .map(wrap_complex_matrix)
    }
    fn verify_transvection_intertwines(&self, a: u128) -> bool {
        self.inner.verify_transvection_intertwines(a)
    }
    fn __repr__(&self) -> String {
        format!(
            "HeisenbergWeilRepresentation(quotient_dim={}, rank={}, hilbert_dim={})",
            self.inner.quotient_dim(),
            self.inner.rank(),
            self.inner
                .hilbert_dim_u128()
                .map_or_else(|| "overflow".to_string(), |n| n.to_string())
        )
    }
}

#[pyfunction]
fn extraspecial_group_f2(qd: Vec<bool>, bmat: Vec<u128>) -> PyResult<PyExtraspecial2Group> {
    crate::forms::extraspecial_group_f2(qd, bmat)
        .map(|inner| PyExtraspecial2Group { inner })
        .map_err(extraspecial_error)
}

#[pyfunction]
fn extraspecial_group_nimber(alg: &NimberAlgebra) -> PyResult<PyExtraspecial2Group> {
    crate::forms::extraspecial_group_nimber(&alg.inner.metric)
        .map(|inner| PyExtraspecial2Group { inner })
        .map_err(extraspecial_error)
}

#[pyfunction]
fn heisenberg_weil_representation_f2(
    qd: Vec<bool>,
    bmat: Vec<u128>,
) -> PyResult<PyHeisenbergWeilRepresentation> {
    crate::forms::heisenberg_weil_representation_f2(qd, bmat)
        .map(|inner| PyHeisenbergWeilRepresentation { inner })
        .map_err(extraspecial_error)
}

#[pyfunction]
fn heisenberg_weil_representation_nimber(
    alg: &NimberAlgebra,
) -> PyResult<PyHeisenbergWeilRepresentation> {
    crate::forms::heisenberg_weil_representation_nimber(&alg.inner.metric)
        .map(|inner| PyHeisenbergWeilRepresentation { inner })
        .map_err(extraspecial_error)
}

fn f2_domain_mask(n: usize, name: &str) -> PyResult<u128> {
    if n > u128::BITS as usize {
        return Err(PyValueError::new_err(format!("{name} supports n <= 128")));
    }
    Ok(if n == 0 {
        0
    } else if n >= u128::BITS as usize {
        u128::MAX
    } else {
        (1u128 << n) - 1
    })
}

fn validate_f2_rows(name: &str, n: usize, rows: &[u128]) -> PyResult<()> {
    let domain_mask = f2_domain_mask(n, name)?;
    if rows.iter().any(|&row| row & !domain_mask != 0) {
        return Err(PyValueError::new_err(format!(
            "{name} polar rows contain bits outside the n-dimensional domain"
        )));
    }
    Ok(())
}

#[pyfunction]
fn brown_f2(n: usize, q4: Vec<u128>, bmat: Vec<u128>) -> PyResult<PyBrownInvariants> {
    if q4.len() != n || bmat.len() != n {
        return Err(PyValueError::new_err(
            "brown_f2 needs q4 and bmat lengths equal to n",
        ));
    }
    validate_f2_rows("brown_f2", n, &bmat)?;
    Ok(wrap_brown_result(crate::forms::brown_f2(n, &q4, &bmat)))
}

#[pyfunction]
fn double_f2(qd: Vec<bool>, bmat: Vec<u128>) -> PyResult<PyBrownInvariants> {
    if qd.len() != bmat.len() {
        return Err(PyValueError::new_err(
            "double_f2 needs qd and bmat lengths to match",
        ));
    }
    validate_f2_rows("double_f2", qd.len(), &bmat)?;
    Ok(wrap_brown_result(crate::forms::double_f2(&qd, &bmat)))
}

fn validate_gold_args(m: usize) -> PyResult<()> {
    if !m.is_power_of_two() || m > 128 {
        return Err(PyValueError::new_err(
            "Gold form needs m a positive power of two <= 128",
        ));
    }
    Ok(())
}

/// The Arf data of the Gold form `Q_a(x)=Tr(x^(1+2^a))` on the nim subfield
/// `F_{2^m}`.
#[pyfunction]
fn gold_form_arf(m: usize, a: usize) -> PyResult<PyArfInvariants> {
    validate_gold_args(m)?;
    let metric = crate::forms::gold_form(m, a);
    crate::forms::arf_nimber(&metric)
        .map(|inner| PyArfInvariants { inner })
        .ok_or_else(|| PyValueError::new_err("Gold form unexpectedly failed Arf classification"))
}

/// The Gold form as a `NimberAlgebra`, so Python can inspect the underlying
/// Clifford product as well as its Arf invariant. Python exposes the Rust
/// `Metric<Nimber>` as the corresponding Clifford algebra because `Metric<T>`
/// is not a Python value type on its own.
#[pyfunction]
fn gold_form(m: usize, a: usize) -> PyResult<NimberAlgebra> {
    validate_gold_args(m)?;
    let metric = crate::forms::gold_form(m, a);
    Ok(NimberAlgebra {
        inner: Arc::new(CliffordAlgebra::new(metric.q.len(), metric)),
    })
}

fn prime_trace_metric<const P: u128>() -> Metric<Fp<P>> {
    Metric::diagonal(vec![Fp::<P>::one()])
}

macro_rules! trace_twisted_alg {
    ($py:ident, $power:ident, $alg:ident, $ext:ty) => {{
        let metric = crate::forms::trace_twisted_form::<$ext>($power);
        $alg {
            inner: Arc::new(CliffordAlgebra::new(metric.q.len(), metric)),
        }
        .into_py_any($py)
    }};
}

macro_rules! prime_trace_alg {
    ($py:ident, $alg:ident, $p:literal) => {{
        let metric = prime_trace_metric::<$p>();
        $alg {
            inner: Arc::new(CliffordAlgebra::new(metric.q.len(), metric)),
        }
        .into_py_any($py)
    }};
}

/// The Frobenius-twisted trace form `Q_k(x)=Tr(x*sigma^k(x))` of a fixed
/// Python-exposed finite field `F_{p^degree}`, returned as a Clifford algebra
/// over its prime field.
#[pyfunction]
#[pyo3(signature = (p, degree, power=1))]
fn trace_twisted_form(py: Python<'_>, p: u128, degree: usize, power: usize) -> PyResult<Py<PyAny>> {
    match (p, degree) {
        (2, 1) => prime_trace_alg!(py, Fp2Algebra, 2),
        (3, 1) => prime_trace_alg!(py, Fp3Algebra, 3),
        (5, 1) => prime_trace_alg!(py, Fp5Algebra, 5),
        (7, 1) => prime_trace_alg!(py, Fp7Algebra, 7),
        (11, 1) => prime_trace_alg!(py, Fp11Algebra, 11),
        (13, 1) => prime_trace_alg!(py, Fp13Algebra, 13),
        (2, 2) => trace_twisted_alg!(py, power, Fp2Algebra, Fpn<2, 2>),
        (2, 3) => trace_twisted_alg!(py, power, Fp2Algebra, Fpn<2, 3>),
        (2, 4) => trace_twisted_alg!(py, power, Fp2Algebra, Fpn<2, 4>),
        (3, 2) => trace_twisted_alg!(py, power, Fp3Algebra, Fpn<3, 2>),
        (3, 3) => trace_twisted_alg!(py, power, Fp3Algebra, Fpn<3, 3>),
        (5, 2) => trace_twisted_alg!(py, power, Fp5Algebra, Fpn<5, 2>),
        _ => Err(PyValueError::new_err(
            "unsupported finite field; expected one of F_p, F4, F8, F16, F9, F25, F27",
        )),
    }
}

fn finite_values_from_indices<F: FiniteOddField>(entries: &[u128], name: &str) -> PyResult<Vec<F>> {
    F::ensure_supported().ok_or_else(unsupported_finite_field_err)?;
    let order = F::field_order();
    entries
        .iter()
        .enumerate()
        .map(|(i, &x)| {
            if x < order {
                Ok(F::from_index(x))
            } else {
                Err(PyValueError::new_err(format!(
                    "{name}[{i}]={x} is outside F_{order}"
                )))
            }
        })
        .collect()
}

macro_rules! transfer_base_alg {
    ($py:ident, $entries:ident, $alg:ident, $field:ty) => {{
        let entries = finite_values_from_indices::<$field>(&$entries, "entries")?;
        let metric = Metric::diagonal(entries);
        $alg {
            inner: Arc::new(CliffordAlgebra::new(metric.q.len(), metric)),
        }
        .into_py_any($py)
    }};
}

macro_rules! transfer_ext_alg {
    ($py:ident, $entries:ident, $alg:ident, $ext:ty) => {{
        let entries = finite_values_from_indices::<$ext>(&$entries, "entries")?;
        let metric = crate::forms::transfer_diagonal::<$ext>(&entries);
        $alg {
            inner: Arc::new(CliffordAlgebra::new(metric.q.len(), metric)),
        }
        .into_py_any($py)
    }};
}

#[pyfunction]
#[pyo3(signature = (p, degree, entries))]
fn transfer_diagonal(
    py: Python<'_>,
    p: u128,
    degree: usize,
    entries: Vec<u128>,
) -> PyResult<Py<PyAny>> {
    match (p, degree) {
        (3, 1) => transfer_base_alg!(py, entries, Fp3Algebra, Fp<3>),
        (5, 1) => transfer_base_alg!(py, entries, Fp5Algebra, Fp<5>),
        (7, 1) => transfer_base_alg!(py, entries, Fp7Algebra, Fp<7>),
        (11, 1) => transfer_base_alg!(py, entries, Fp11Algebra, Fp<11>),
        (13, 1) => transfer_base_alg!(py, entries, Fp13Algebra, Fp<13>),
        (3, 2) => transfer_ext_alg!(py, entries, Fp3Algebra, Fpn<3, 2>),
        (3, 3) => transfer_ext_alg!(py, entries, Fp3Algebra, Fpn<3, 3>),
        (5, 2) => transfer_ext_alg!(py, entries, Fp5Algebra, Fpn<5, 2>),
        _ => Err(PyValueError::new_err(
            "transfer_diagonal supports odd finite fields F_3, F_5, F_7, F_11, F_13, F_9, F_25, F_27",
        )),
    }
}

/// The Arf invariant of the characteristic-2 twisted trace form over the fixed
/// Python-exposed finite fields `F_2`, `F_4`, `F_8`, and `F_16`.
#[pyfunction]
#[pyo3(signature = (degree, power=1))]
fn trace_form_arf(degree: usize, power: usize) -> PyResult<PyArfInvariants> {
    let inner = match degree {
        1 => crate::forms::arf_nimber(&Metric::diagonal(vec![Nimber(1)])),
        2 => crate::forms::trace_form_arf::<Fpn<2, 2>>(power),
        3 => crate::forms::trace_form_arf::<Fpn<2, 3>>(power),
        4 => crate::forms::trace_form_arf::<Fpn<2, 4>>(power),
        _ => {
            return Err(PyValueError::new_err(
                "characteristic-2 trace-form Arf supports degree 1..=4",
            ))
        }
    }
    .ok_or_else(|| PyValueError::new_err("trace-form Arf classification failed"))?;
    Ok(PyArfInvariants { inner })
}

// ---------------------------------------------------------------------------
// Char-0 classifier
// ---------------------------------------------------------------------------

#[pyclass(name = "BaseField", module = "ogdoad", from_py_object)]
#[derive(Clone, Copy)]
struct PyBaseField {
    inner: crate::forms::BaseField,
}

fn base_field_name(base: crate::forms::BaseField) -> &'static str {
    match base {
        crate::forms::BaseField::R => "R",
        crate::forms::BaseField::C => "C",
        crate::forms::BaseField::H => "H",
    }
}

fn wrap_base_field(inner: crate::forms::BaseField) -> PyBaseField {
    PyBaseField { inner }
}

fn parse_base_field(obj: &Bound<'_, PyAny>) -> PyResult<crate::forms::BaseField> {
    if let Ok(base) = obj.cast::<PyBaseField>() {
        return Ok(base.borrow().inner);
    }
    Err(PyTypeError::new_err("expected BaseField"))
}

#[pymethods]
impl PyBaseField {
    #[staticmethod]
    fn r() -> Self {
        wrap_base_field(crate::forms::BaseField::R)
    }

    #[staticmethod]
    fn c() -> Self {
        wrap_base_field(crate::forms::BaseField::C)
    }

    #[staticmethod]
    fn h() -> Self {
        wrap_base_field(crate::forms::BaseField::H)
    }

    #[getter]
    fn name(&self) -> &'static str {
        base_field_name(self.inner)
    }

    #[getter]
    fn is_real(&self) -> bool {
        self.inner == crate::forms::BaseField::R
    }

    #[getter]
    fn is_complex(&self) -> bool {
        self.inner == crate::forms::BaseField::C
    }

    #[getter]
    fn is_quaternionic(&self) -> bool {
        self.inner == crate::forms::BaseField::H
    }

    fn __str__(&self) -> &'static str {
        base_field_name(self.inner)
    }

    fn __repr__(&self) -> String {
        format!("BaseField.{}", base_field_name(self.inner))
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        matches!(parse_base_field(other), Ok(base) if base == self.inner)
    }
}

#[pyclass(name = "RationalPlace", module = "ogdoad", from_py_object)]
#[derive(Clone, Copy)]
struct PyRationalPlace {
    inner: crate::forms::Place,
}

fn wrap_rational_place(inner: crate::forms::Place) -> PyRationalPlace {
    PyRationalPlace { inner }
}

fn parse_rational_place(obj: &Bound<'_, PyAny>) -> PyResult<crate::forms::Place> {
    if let Ok(place) = obj.cast::<PyRationalPlace>() {
        return Ok(place.borrow().inner);
    }
    Err(PyTypeError::new_err("expected RationalPlace"))
}

fn parse_rational_place_arg(place: Option<&Bound<'_, PyAny>>) -> PyResult<crate::forms::Place> {
    match place {
        None => Ok(crate::forms::Place::Real),
        Some(obj) => parse_rational_place(obj),
    }
}

#[pymethods]
impl PyRationalPlace {
    #[staticmethod]
    fn real() -> Self {
        wrap_rational_place(crate::forms::Place::Real)
    }

    #[staticmethod]
    fn prime(p: u128) -> Self {
        wrap_rational_place(crate::forms::Place::Prime(p))
    }

    #[getter]
    fn name(&self) -> String {
        place_name(self.inner)
    }

    #[getter]
    fn is_real(&self) -> bool {
        self.inner == crate::forms::Place::Real
    }

    #[getter]
    fn is_prime(&self) -> bool {
        matches!(self.inner, crate::forms::Place::Prime(_))
    }

    #[getter]
    fn prime_value(&self) -> Option<u128> {
        match self.inner {
            crate::forms::Place::Real => None,
            crate::forms::Place::Prime(p) => Some(p),
        }
    }

    fn __str__(&self) -> String {
        self.inner.to_string()
    }

    // `__repr__` keeps the enum-style `RationalPlace.Real`/`RationalPlace.Prime(p)`
    // framing on purpose (mirrors `BaseField`'s repr convention) — the core
    // Display ("R"/"Q_p", exposed via `display()`) is the terse form meant for
    // embedding inside other records' renders, and already matches `__str__`.
    fn display(&self) -> String {
        self.inner.to_string()
    }

    fn __repr__(&self) -> String {
        match self.inner {
            crate::forms::Place::Real => "RationalPlace.Real".to_string(),
            crate::forms::Place::Prime(p) => format!("RationalPlace.Prime({p})"),
        }
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        matches!(parse_rational_place(other), Ok(place) if place == self.inner)
    }
}

#[pyclass(name = "CliffordInvariants", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyCliffordInvariants {
    inner: crate::forms::CliffordInvariants,
}

#[pymethods]
impl PyCliffordInvariants {
    #[getter]
    fn base(&self) -> PyBaseField {
        wrap_base_field(self.inner.base)
    }
    #[getter]
    fn matrix_dim(&self) -> u128 {
        self.inner.matrix_dim
    }
    #[getter]
    fn doubled(&self) -> bool {
        self.inner.doubled
    }
    #[getter]
    fn radical_dim(&self) -> usize {
        self.inner.radical_dim
    }
    #[getter]
    fn ground(&self) -> PyBaseField {
        wrap_base_field(self.inner.ground)
    }
    #[getter]
    fn signature(&self) -> (usize, usize) {
        self.inner.signature
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(
    name = "RationalPlaceInvariant",
    module = "ogdoad",
    skip_from_py_object
)]
#[derive(Clone)]
struct PyRationalPlaceInvariant {
    inner: crate::forms::RationalPlaceInvariant,
}

#[pymethods]
impl PyRationalPlaceInvariant {
    #[getter]
    fn place(&self) -> PyRationalPlace {
        wrap_rational_place(self.inner.place)
    }
    #[getter]
    fn hasse(&self) -> i128 {
        self.inner.hasse
    }
    fn __repr__(&self) -> String {
        format!(
            "RationalPlaceInvariant(place={}, hasse={:+})",
            place_name(self.inner.place),
            self.inner.hasse
        )
    }
}

#[pyclass(name = "RationalCliffordInvariants", module = "ogdoad")]
struct PyRationalCliffordInvariants {
    inner: crate::forms::RationalCliffordInvariants,
}

fn place_name(place: crate::forms::Place) -> String {
    match place {
        crate::forms::Place::Real => "R".to_string(),
        crate::forms::Place::Prime(p) => format!("Q_{p}"),
    }
}

#[pymethods]
impl PyRationalCliffordInvariants {
    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim
    }
    #[getter]
    fn radical_dim(&self) -> usize {
        self.inner.radical_dim
    }
    #[getter]
    fn discriminant(&self) -> i128 {
        self.inner.discriminant
    }
    #[getter]
    fn signature(&self) -> (usize, usize) {
        self.inner.signature
    }
    #[getter]
    fn local_hasse(&self) -> Vec<PyRationalPlaceInvariant> {
        self.inner
            .local_hasse
            .iter()
            .cloned()
            .map(|inner| PyRationalPlaceInvariant { inner })
            .collect()
    }
    #[getter]
    fn real_closure(&self) -> PyCliffordInvariants {
        PyCliffordInvariants {
            inner: self.inner.real_closure.clone(),
        }
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(name = "FiniteFieldInvariants", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyFiniteFieldInvariants {
    inner: crate::forms::FiniteFieldInvariants,
}

#[pymethods]
impl PyFiniteFieldInvariants {
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            crate::forms::FiniteFieldInvariants::Odd(_) => "odd",
            crate::forms::FiniteFieldInvariants::Char2(_) => "char2",
        }
    }
    #[getter]
    fn odd(&self) -> Option<PyOddCharInvariants> {
        match &self.inner {
            crate::forms::FiniteFieldInvariants::Odd(inner) => {
                Some(PyOddCharInvariants { inner: *inner })
            }
            crate::forms::FiniteFieldInvariants::Char2(_) => None,
        }
    }
    #[getter]
    fn char2(&self) -> Option<PyArfInvariants> {
        match &self.inner {
            crate::forms::FiniteFieldInvariants::Odd(_) => None,
            crate::forms::FiniteFieldInvariants::Char2(inner) => Some(PyArfInvariants {
                inner: inner.clone(),
            }),
        }
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        format!("FiniteFieldInvariants::{}", self.inner.display())
    }
}

#[pyclass(
    name = "FiniteFieldNumericInvariants",
    module = "ogdoad",
    skip_from_py_object
)]
#[derive(Clone)]
struct PyFiniteFieldNumericInvariants {
    inner: crate::forms::FiniteFieldNumericInvariants,
}

#[pymethods]
impl PyFiniteFieldNumericInvariants {
    #[getter]
    fn characteristic(&self) -> u128 {
        self.inner.characteristic
    }
    #[getter]
    fn absolute_degree(&self) -> usize {
        self.inner.absolute_degree
    }
    #[getter]
    fn field_order(&self) -> u128 {
        self.inner.field_order
    }
    #[getter]
    fn level(&self) -> usize {
        self.inner.level
    }
    #[getter]
    fn pythagoras_number(&self) -> usize {
        self.inner.pythagoras_number
    }
    #[getter]
    fn u_invariant(&self) -> usize {
        self.inner.u_invariant
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

/// Classify a surreal Clifford algebra on the exact-square real-table subdomain
/// as a matrix algebra over ℝ/ℂ/ℍ. Symmetric metrics are diagonalized when possible.
#[pyfunction]
fn classify_surreal(alg: &SurrealAlgebra) -> PyResult<PyCliffordInvariants> {
    crate::forms::classify_surreal(&alg.inner.metric)
        .map(|t| PyCliffordInvariants { inner: t })
        .ok_or_else(|| {
            PyValueError::new_err(
                "classifier could not diagonalize this metric or needs an unrepresented square root",
            )
        })
}

/// Rust-name helper: signature `(positive, negative, radical)` over represented `Surreal`.
#[pyfunction]
fn surreal_signature(alg: &SurrealAlgebra) -> PyResult<(usize, usize, usize)> {
    crate::forms::surreal_signature(&alg.inner.metric).ok_or_else(|| {
        PyValueError::new_err(
            "surreal signature needs a diagonalizable metric with represented exact square classes",
        )
    })
}

/// Classify a surcomplex Clifford algebra on the exact-square complex-table
/// subdomain. Symmetric metrics are diagonalized when possible.
#[pyfunction]
fn classify_surcomplex(alg: &SurcomplexAlgebra) -> PyResult<PyCliffordInvariants> {
    crate::forms::classify_surcomplex(&alg.inner.metric)
        .map(|t| PyCliffordInvariants { inner: t })
        .ok_or_else(|| {
            PyValueError::new_err(
                "classifier could not diagonalize this metric or needs an unrepresented square root",
            )
        })
}

/// Rust-name helper: `(nonzero_rank, radical_dim)` over represented `Surcomplex<Surreal>`.
#[pyfunction]
fn surcomplex_rank(alg: &SurcomplexAlgebra) -> PyResult<(usize, usize)> {
    crate::forms::surcomplex_rank(&alg.inner.metric).ok_or_else(|| {
        PyValueError::new_err(
            "surcomplex rank needs a diagonalizable metric with represented exact square roots",
        )
    })
}

/// Classify a rational Clifford algebra by the genuine rational invariants:
/// dimension/radical, discriminant square-class, signature, and local Hasse signs.
#[pyfunction]
fn classify_rational(alg: &RationalAlgebra) -> PyResult<PyRationalCliffordInvariants> {
    crate::forms::classify_rational(&alg.inner.metric)
        .map(|inner| PyRationalCliffordInvariants { inner })
        .ok_or_else(|| {
            PyValueError::new_err(
                "rational classifier could not diagonalize this metric or overflowed bounded i128 arithmetic",
            )
        })
}

/// Are two surreal-scalar forms isometric on the exact-square real-table
/// subdomain? Symmetric metrics are diagonalized when possible.
#[pyfunction]
fn isometric_real(a: &SurrealAlgebra, b: &SurrealAlgebra) -> PyResult<bool> {
    crate::forms::isometric_real(&a.inner.metric, &b.inner.metric).ok_or_else(|| {
        PyValueError::new_err(
            "surreal isometry could not diagonalize a metric or needs an unrepresented square root",
        )
    })
}

/// Are two rational forms isometric by the Hasse-Minkowski invariant package?
#[pyfunction]
fn isometric_rational(a: &RationalAlgebra, b: &RationalAlgebra) -> PyResult<bool> {
    crate::forms::isometric_rational(&a.inner.metric, &b.inner.metric).ok_or_else(|| {
        PyValueError::new_err(
            "rational isometry could not diagonalize a metric or overflowed bounded i128 arithmetic",
        )
    })
}

/// Are two surcomplex-scalar forms isometric on the exact-square complex-table
/// subdomain?
#[pyfunction]
fn isometric_surcomplex(a: &SurcomplexAlgebra, b: &SurcomplexAlgebra) -> PyResult<bool> {
    crate::forms::isometric_surcomplex(&a.inner.metric, &b.inner.metric).ok_or_else(|| {
        PyValueError::new_err(
            "surcomplex isometry could not diagonalize a metric or needs an unrepresented square root",
        )
    })
}

/// Are two nim-field characteristic-2 forms isometric by the implemented
/// Arf/radical invariant?
#[pyfunction]
fn isometric_nimber(a: &NimberAlgebra, b: &NimberAlgebra) -> PyResult<bool> {
    crate::forms::isometric_nimber(&a.inner.metric, &b.inner.metric)
        .ok_or_else(|| PyValueError::new_err("nimber isometry needs a non-general-bilinear metric"))
}

/// Classify a real Clifford algebra directly from its signature `(p, q, r)`
/// (`p` plus-squares, `q` minus-squares, `r` null/radical dimensions) — the
/// 8-fold table, no metric needed. Complement to `classify_surreal`.
#[pyfunction]
#[pyo3(signature = (p, q, r=0))]
fn classify_real(p: usize, q: usize, r: usize) -> PyCliffordInvariants {
    PyCliffordInvariants {
        inner: crate::forms::classify_real(p, q, r),
    }
}

/// Classify a complex Clifford algebra directly from `(n, r)` (`n` nondegenerate
/// dimensions, `r` null/radical) — the 2-fold table. Complement to
/// `classify_surcomplex`.
#[pyfunction]
#[pyo3(signature = (n, r=0))]
fn classify_complex(n: usize, r: usize) -> PyCliffordInvariants {
    PyCliffordInvariants {
        inner: crate::forms::classify_complex(n, r),
    }
}

// ---------------------------------------------------------------------------
// Witt group + Dickson invariant
// ---------------------------------------------------------------------------

#[pyclass(name = "WittClassError", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyWittClassError {
    inner: WittClassError,
}

fn wrap_witt_class_error(inner: WittClassError) -> PyWittClassError {
    PyWittClassError { inner }
}

fn parse_witt_class_error(obj: &Bound<'_, PyAny>) -> PyResult<WittClassError> {
    if let Ok(err) = obj.cast::<PyWittClassError>() {
        return Ok(err.borrow().inner);
    }
    Err(PyTypeError::new_err("expected WittClassError"))
}

fn witt_class_error_name(err: &WittClassError) -> &'static str {
    match err {
        WittClassError::GeneralBilinearMetric => "GeneralBilinearMetric",
        WittClassError::Singular { .. } => "Singular",
    }
}

#[pymethods]
impl PyWittClassError {
    #[staticmethod]
    fn general_bilinear_metric() -> Self {
        wrap_witt_class_error(WittClassError::GeneralBilinearMetric)
    }

    #[staticmethod]
    fn singular(radical_dim: usize, radical_anisotropic: bool) -> Self {
        wrap_witt_class_error(WittClassError::Singular {
            radical_dim,
            radical_anisotropic,
        })
    }

    #[getter]
    fn name(&self) -> &'static str {
        witt_class_error_name(&self.inner)
    }

    #[getter]
    fn is_general_bilinear_metric(&self) -> bool {
        matches!(self.inner, WittClassError::GeneralBilinearMetric)
    }

    #[getter]
    fn is_singular(&self) -> bool {
        matches!(self.inner, WittClassError::Singular { .. })
    }

    #[getter]
    fn radical_dim(&self) -> Option<usize> {
        match self.inner {
            WittClassError::GeneralBilinearMetric => None,
            WittClassError::Singular { radical_dim, .. } => Some(radical_dim),
        }
    }

    #[getter]
    fn radical_anisotropic(&self) -> Option<bool> {
        match self.inner {
            WittClassError::GeneralBilinearMetric => None,
            WittClassError::Singular {
                radical_anisotropic,
                ..
            } => Some(radical_anisotropic),
        }
    }

    fn __repr__(&self) -> String {
        match self.inner {
            WittClassError::GeneralBilinearMetric => {
                "WittClassError.GeneralBilinearMetric".to_string()
            }
            WittClassError::Singular {
                radical_dim,
                radical_anisotropic,
            } => format!(
                "WittClassError.Singular(radical_dim={radical_dim}, radical_anisotropic={radical_anisotropic})"
            ),
        }
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        matches!(parse_witt_class_error(other), Ok(err) if err == self.inner)
    }
}

#[pyclass(name = "WittClass", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyWittClass {
    inner: WittClass,
}

#[pymethods]
impl PyWittClass {
    #[new]
    #[pyo3(signature = (arf=0, field_degree=1))]
    fn new(arf: u128, field_degree: u128) -> PyResult<Self> {
        if arf > 1 {
            return Err(PyValueError::new_err("WittClass arf must be 0 or 1"));
        }
        check_positive_field_degree(field_degree)?;
        let inner = WittClass::new(field_degree, arf)
            .ok_or_else(|| PyValueError::new_err("WittClass parameters out of domain"))?;
        Ok(PyWittClass { inner })
    }
    #[staticmethod]
    fn zero() -> PyWittClass {
        PyWittClass {
            inner: WittClass::zero_f2(),
        }
    }
    #[staticmethod]
    fn try_from_metric(alg: &NimberAlgebra) -> PyResult<PyWittClass> {
        WittClass::try_from_metric(&alg.inner.metric)
            .map(|inner| PyWittClass { inner })
            .map_err(|err| PyValueError::new_err(format!("Witt class is undefined: {err:?}")))
    }
    #[staticmethod]
    fn try_from_metric_error(alg: &NimberAlgebra) -> Option<PyWittClassError> {
        WittClass::try_from_metric(&alg.inner.metric)
            .err()
            .map(wrap_witt_class_error)
    }
    #[getter]
    fn arf(&self) -> u128 {
        self.inner.arf()
    }
    #[getter]
    fn field_degree(&self) -> u128 {
        self.inner.field_degree()
    }
    fn __add__(&self, other: &PyWittClass) -> PyResult<PyWittClass> {
        self.inner
            .try_add(&other.inner)
            .map(|inner| PyWittClass { inner })
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }
    fn __neg__(&self) -> PyWittClass {
        PyWittClass {
            inner: self.inner.neg(),
        }
    }
    fn is_hyperbolic(&self) -> bool {
        self.inner.is_hyperbolic()
    }
    fn anisotropic_dim(&self) -> usize {
        self.inner.anisotropic_dim()
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __eq__(&self, other: &PyWittClass) -> bool {
        self.inner == other.inner
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

/// The Witt class (in `W_q ≅ ℤ/2`) of a nimber Clifford metric.
#[pyfunction]
fn witt_class(alg: &NimberAlgebra) -> PyResult<PyWittClass> {
    WittClass::try_from_metric(&alg.inner.metric)
        .map(|inner| PyWittClass { inner })
        .map_err(|err| PyValueError::new_err(format!("Witt class is undefined: {err:?}")))
}

/// The typed Rust `WittClassError` for a nimber metric, or `None` if the class exists.
#[pyfunction]
fn witt_class_error(alg: &NimberAlgebra) -> Option<PyWittClassError> {
    WittClass::try_from_metric(&alg.inner.metric)
        .err()
        .map(wrap_witt_class_error)
}

/// The Dickson invariant of an orthogonal matrix over the nim-field (the char-2
/// determinant replacement; `0` ⇒ rotation/SO, `1` ⇒ reflection).
#[pyfunction]
fn dickson_matrix(g: Vec<Vec<u128>>) -> u128 {
    crate::forms::dickson_matrix(&g)
}

/// The Dickson invariant of a nimber Clifford versor (= its grade parity).
#[pyfunction]
fn dickson_of_versor(v: &NimberMV) -> PyResult<u128> {
    crate::forms::dickson_of_versor(&v.alg, &v.mv)
        .ok_or_else(|| PyValueError::new_err("not an invertible homogeneous versor"))
}

#[pyclass(
    name = "Char2SymmetryFactorization",
    module = "ogdoad",
    skip_from_py_object
)]
#[derive(Clone)]
struct PyChar2SymmetryFactorization {
    degree: usize,
    matrix: Vec<Vec<u128>>,
    factors: Vec<Vec<u128>>,
    dickson: u128,
    clifford_verified: bool,
    rendered: String,
}

#[pymethods]
impl PyChar2SymmetryFactorization {
    #[getter]
    fn degree(&self) -> usize {
        self.degree
    }
    #[getter]
    fn matrix(&self) -> Vec<Vec<u128>> {
        self.matrix.clone()
    }
    #[getter]
    fn factors(&self) -> Vec<Vec<u128>> {
        self.factors.clone()
    }
    #[getter]
    fn factor_count(&self) -> usize {
        self.factors.len()
    }
    #[getter]
    fn dickson(&self) -> u128 {
        self.dickson
    }
    #[getter]
    fn clifford_verified(&self) -> bool {
        self.clifford_verified
    }
    fn display(&self) -> String {
        self.rendered.clone()
    }
    fn __repr__(&self) -> String {
        self.rendered.clone()
    }
}

// ---------------------------------------------------------------------------
// Alternating and Hermitian forms (the "form + involution" siblings)
// ---------------------------------------------------------------------------

#[pyclass(name = "SymplecticInvariants", module = "ogdoad")]
struct PySymplecticInvariants {
    inner: crate::forms::SymplecticInvariants,
}

#[pymethods]
impl PySymplecticInvariants {
    #[getter]
    fn rank(&self) -> usize {
        self.inner.rank
    }
    #[getter]
    fn radical_dim(&self) -> usize {
        self.inner.radical_dim
    }
    fn planes(&self) -> usize {
        self.inner.planes()
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

fn rational_gram(gram: Vec<Vec<i128>>) -> Vec<Vec<Rational>> {
    gram.into_iter()
        .map(|row| row.into_iter().map(Rational::from_int).collect())
        .collect()
}

#[pyclass(name = "SymplecticForm", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PySymplecticForm {
    inner: SymplecticForm<Rational>,
}

#[pymethods]
impl PySymplecticForm {
    #[staticmethod]
    fn from_gram(gram: Vec<Vec<i128>>) -> PyResult<Self> {
        SymplecticForm::from_gram(rational_gram(gram))
            .map(|inner| PySymplecticForm { inner })
            .ok_or_else(|| PyValueError::new_err("Gram matrix must be square and alternating"))
    }
    #[staticmethod]
    fn hyperbolic(r: usize) -> PySymplecticForm {
        PySymplecticForm {
            inner: SymplecticForm::hyperbolic(r),
        }
    }
    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim()
    }
    fn direct_sum(&self, other: &PySymplecticForm) -> PySymplecticForm {
        PySymplecticForm {
            inner: self.inner.direct_sum(&other.inner),
        }
    }
    fn classify(&self) -> PyResult<PySymplecticInvariants> {
        self.inner
            .classify()
            .map(|inner| PySymplecticInvariants { inner })
            .ok_or_else(|| {
                PyValueError::new_err("classification needs a unit pivot over this scalar")
            })
    }
    fn __repr__(&self) -> String {
        format!("SymplecticForm(dim={})", self.inner.dim())
    }
}

/// Classify an integer/rational alternating Gram matrix: complete invariant
/// `(rank, radical_dim)`.
#[pyfunction]
fn classify_symplectic(gram: Vec<Vec<i128>>) -> PyResult<PySymplecticInvariants> {
    crate::forms::classify_symplectic(rational_gram(gram))
        .map(|inner| PySymplecticInvariants { inner })
        .ok_or_else(|| PyValueError::new_err("Gram matrix must be square and alternating"))
}

/// The same alternating-form classifier over the nimber backend, where
/// alternating means symmetric with zero diagonal because `-1 = 1`.
#[pyfunction]
fn classify_symplectic_nimber(gram: Vec<Vec<u128>>) -> PyResult<PySymplecticInvariants> {
    let gram: Vec<Vec<Nimber>> = gram
        .into_iter()
        .map(|row| row.into_iter().map(Nimber).collect())
        .collect();
    crate::forms::classify_symplectic(gram)
        .map(|inner| PySymplecticInvariants { inner })
        .ok_or_else(|| PyValueError::new_err("Nimber Gram matrix must be square and alternating"))
}

#[pyclass(name = "HermitianSignature", module = "ogdoad")]
struct PyHermitianSignature {
    inner: crate::forms::HermitianSignature,
}

#[pymethods]
impl PyHermitianSignature {
    #[getter]
    fn pos(&self) -> usize {
        self.inner.pos
    }
    #[getter]
    fn neg(&self) -> usize {
        self.inner.neg
    }
    #[getter]
    fn radical(&self) -> usize {
        self.inner.radical
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(name = "HermitianForm", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyHermitianForm {
    inner: HermitianForm<Surreal>,
}

fn parse_surcomplex_gram(
    gram: Vec<Vec<Bound<'_, PyAny>>>,
) -> PyResult<Vec<Vec<Surcomplex<Surreal>>>> {
    let n = gram.len();
    let mut out = Vec::with_capacity(n);
    for row in &gram {
        if row.len() != n {
            return Err(PyValueError::new_err("Gram matrix must be square"));
        }
        let mut r = Vec::with_capacity(n);
        for x in row {
            r.push(parse_surcomplex(x)?);
        }
        out.push(r);
    }
    Ok(out)
}

#[pymethods]
impl PyHermitianForm {
    #[staticmethod]
    fn from_gram(gram: Vec<Vec<Bound<'_, PyAny>>>) -> PyResult<Self> {
        HermitianForm::from_gram(parse_surcomplex_gram(gram)?)
            .map(|inner| PyHermitianForm { inner })
            .ok_or_else(|| PyValueError::new_err("Gram matrix must be Hermitian"))
    }
    #[staticmethod]
    fn from_skew(gram: Vec<Vec<Bound<'_, PyAny>>>) -> PyResult<PyHermitianForm> {
        HermitianForm::from_skew(parse_surcomplex_gram(gram)?)
            .map(|inner| PyHermitianForm { inner })
            .ok_or_else(|| PyValueError::new_err("Gram matrix must be skew-Hermitian"))
    }
    #[staticmethod]
    fn diagonal(reals: Vec<Bound<'_, PyAny>>) -> PyResult<PyHermitianForm> {
        let mut ds = Vec::with_capacity(reals.len());
        for x in &reals {
            ds.push(parse_surreal(x)?);
        }
        Ok(PyHermitianForm {
            inner: HermitianForm::diagonal(ds),
        })
    }
    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim()
    }
    fn direct_sum(&self, other: &PyHermitianForm) -> PyHermitianForm {
        PyHermitianForm {
            inner: self.inner.direct_sum(&other.inner),
        }
    }
    fn diagonalize(&self) -> Vec<PySurreal> {
        self.inner
            .diagonalize()
            .into_iter()
            .map(wrap_surreal)
            .collect()
    }
    fn signature(&self) -> PyHermitianSignature {
        PyHermitianSignature {
            inner: self.inner.signature(|x| x.sign()),
        }
    }
    /// Restrict `h` over `Surcomplex/Surreal` to the ordinary quadratic form
    /// `q(v)=h(v,v)` over `Surreal`, doubling the dimension.
    fn restrict_scalars(&self) -> PyResult<SurrealAlgebra> {
        let metric = self
            .inner
            .restrict_scalars()
            .map_err(|err| PyValueError::new_err(err.to_string()))?;
        Ok(SurrealAlgebra {
            inner: Arc::new(CliffordAlgebra::new(metric.dim(), metric)),
        })
    }
    fn __repr__(&self) -> String {
        format!("HermitianForm(dim={})", self.inner.dim())
    }
}

#[pyclass(name = "FiniteHermitianInvariants", module = "ogdoad")]
struct PyFiniteHermitianInvariants {
    inner: crate::forms::FiniteHermitianInvariants,
}

#[pymethods]
impl PyFiniteHermitianInvariants {
    #[getter]
    fn rank(&self) -> usize {
        self.inner.rank
    }
    #[getter]
    fn radical_dim(&self) -> usize {
        self.inner.radical_dim
    }
    #[getter]
    fn characteristic(&self) -> u128 {
        self.inner.characteristic
    }
    #[getter]
    fn base_degree(&self) -> usize {
        self.inner.base_degree
    }
    #[getter]
    fn extension_degree(&self) -> usize {
        self.inner.extension_degree
    }
    #[getter]
    fn base_field_order(&self) -> Option<u128> {
        self.inner.base_field_order
    }
    #[getter]
    fn extension_field_order(&self) -> Option<u128> {
        self.inner.extension_field_order
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

fn unsupported_finite_hermitian_field_err() -> PyErr {
    PyValueError::new_err("supported finite Hermitian fields: F_4/F_2, F_16/F_4, F_9/F_3, F_25/F_5")
}

fn parse_fpn_index<const P: u128, const N: usize>(x: u128, name: &str) -> PyResult<Fpn<P, N>> {
    if !Fpn::<P, N>::is_supported_field() {
        return Err(unsupported_finite_hermitian_field_err());
    }
    let order = Fpn::<P, N>::field_order();
    if x >= order {
        return Err(PyValueError::new_err(format!(
            "{name}={x} is outside F_{order}"
        )));
    }
    let mut digits = [0u128; N];
    let mut y = x;
    for d in digits.iter_mut() {
        *d = y % P;
        y /= P;
    }
    Ok(Fpn::<P, N>::from_coeffs(&digits))
}

fn parse_fpn_gram<const P: u128, const N: usize>(
    gram: &[Vec<u128>],
) -> PyResult<Vec<Vec<Fpn<P, N>>>> {
    let n = gram.len();
    let mut out = Vec::with_capacity(n);
    for (i, row) in gram.iter().enumerate() {
        if row.len() != n {
            return Err(PyValueError::new_err("Gram matrix must be square"));
        }
        let mut parsed = Vec::with_capacity(n);
        for (j, &x) in row.iter().enumerate() {
            parsed.push(parse_fpn_index::<P, N>(x, &format!("gram[{i}][{j}]"))?);
        }
        out.push(parsed);
    }
    Ok(out)
}

fn finite_hermitian_form_fpn<const P: u128, const N: usize>(
    gram: &[Vec<u128>],
) -> PyResult<FiniteHermitianForm<Fpn<P, N>>> {
    FiniteHermitianForm::from_gram(parse_fpn_gram::<P, N>(gram)?).ok_or_else(|| {
        PyValueError::new_err("Gram matrix must be Hermitian for F_{p^(2k)}/F_{p^k}")
    })
}

macro_rules! with_finite_hermitian_form {
    ($p:expr, $degree:expr, $gram:expr, |$form:ident| $body:expr) => {{
        match ($p, $degree) {
            (2, 2) => {
                let $form = finite_hermitian_form_fpn::<2, 2>($gram)?;
                $body
            }
            (2, 4) => {
                let $form = finite_hermitian_form_fpn::<2, 4>($gram)?;
                $body
            }
            (3, 2) => {
                let $form = finite_hermitian_form_fpn::<3, 2>($gram)?;
                $body
            }
            (5, 2) => {
                let $form = finite_hermitian_form_fpn::<5, 2>($gram)?;
                $body
            }
            _ => return Err(unsupported_finite_hermitian_field_err()),
        }
    }};
}

#[pyclass(name = "FiniteHermitianForm", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyFiniteHermitianForm {
    p: u128,
    degree: usize,
    gram: Vec<Vec<u128>>,
}

#[pymethods]
impl PyFiniteHermitianForm {
    #[new]
    fn new(p: u128, degree: usize, gram: Vec<Vec<u128>>) -> PyResult<Self> {
        with_finite_hermitian_form!(p, degree, &gram, |form| {
            let _ = form;
            Ok(PyFiniteHermitianForm { p, degree, gram })
        })
    }
    #[staticmethod]
    fn diagonal(p: u128, degree: usize, entries: Vec<u128>) -> PyResult<Self> {
        let n = entries.len();
        let mut gram = vec![vec![0u128; n]; n];
        for (i, x) in entries.into_iter().enumerate() {
            gram[i][i] = x;
        }
        PyFiniteHermitianForm::new(p, degree, gram)
    }
    #[getter]
    fn p(&self) -> u128 {
        self.p
    }
    #[getter]
    fn degree(&self) -> usize {
        self.degree
    }
    #[getter]
    fn gram(&self) -> Vec<Vec<u128>> {
        self.gram.clone()
    }
    #[getter]
    fn dim(&self) -> usize {
        self.gram.len()
    }
    fn direct_sum(&self, other: &PyFiniteHermitianForm) -> PyResult<PyFiniteHermitianForm> {
        if self.p != other.p || self.degree != other.degree {
            return Err(PyTypeError::new_err(
                "finite Hermitian forms must live over the same field",
            ));
        }
        let n = self.dim();
        let m = other.dim();
        let mut gram = vec![vec![0u128; n + m]; n + m];
        for i in 0..n {
            for j in 0..n {
                gram[i][j] = self.gram[i][j];
            }
        }
        for i in 0..m {
            for j in 0..m {
                gram[n + i][n + j] = other.gram[i][j];
            }
        }
        PyFiniteHermitianForm::new(self.p, self.degree, gram)
    }
    fn classify(&self) -> PyResult<PyFiniteHermitianInvariants> {
        with_finite_hermitian_form!(self.p, self.degree, &self.gram, |form| {
            Ok(PyFiniteHermitianInvariants {
                inner: form.classify(),
            })
        })
    }
    /// Restrict this Hermitian form to an ordinary quadratic algebra over its
    /// fixed field.  The concrete return type is `Fp2Algebra`, `F4Algebra`,
    /// `Fp3Algebra`, or `Fp5Algebra`, preserving backend separation.
    fn restrict_scalars(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        macro_rules! restrict_into {
            ($p:literal, $degree:literal, $alg:ident) => {{
                let form = finite_hermitian_form_fpn::<$p, $degree>(&self.gram)?;
                let metric = form
                    .restrict_scalars()
                    .map_err(|err| PyValueError::new_err(err.to_string()))?;
                $alg {
                    inner: Arc::new(CliffordAlgebra::new(metric.dim(), metric)),
                }
                .into_py_any(py)
            }};
        }

        match (self.p, self.degree) {
            (2, 2) => restrict_into!(2, 2, Fp2Algebra),
            (2, 4) => restrict_into!(2, 4, F4Algebra),
            (3, 2) => restrict_into!(3, 2, Fp3Algebra),
            (5, 2) => restrict_into!(5, 2, Fp5Algebra),
            _ => Err(unsupported_finite_hermitian_field_err()),
        }
    }
    fn __repr__(&self) -> String {
        format!(
            "FiniteHermitianForm(F_{}^{}, dim={})",
            self.p,
            self.degree,
            self.dim()
        )
    }
}

// ---------------------------------------------------------------------------
// Odd-characteristic classifier (the trichotomy's third leg)
// ---------------------------------------------------------------------------

fn finite_diag<F: FiniteOddField>(q: &[i128]) -> Metric<F> {
    Metric::diagonal(q.iter().map(|&x| F::from_int(x)).collect())
}

fn unsupported_finite_field_err() -> PyErr {
    PyValueError::new_err("supported odd finite fields: F_3, F_5, F_7, F_11, F_13, F_9, F_25, F_27")
}

fn finite_field_order(p: u128, degree: usize) -> PyResult<u128> {
    match (p, degree) {
        (3, 1) => Ok(3),
        (5, 1) => Ok(5),
        (7, 1) => Ok(7),
        (11, 1) => Ok(11),
        (13, 1) => Ok(13),
        (3, 2) => Ok(9),
        (5, 2) => Ok(25),
        (3, 3) => Ok(27),
        _ => Err(unsupported_finite_field_err()),
    }
}

fn unsupported_char2_finite_field_err() -> PyErr {
    PyValueError::new_err("supported characteristic-2 finite fields: F_2, F_4, F_8, F_16")
}

fn char2_finite_field_order(degree: usize) -> PyResult<u128> {
    match degree {
        1 => Ok(2),
        2 => Ok(4),
        3 => Ok(8),
        4 => Ok(16),
        _ => Err(unsupported_char2_finite_field_err()),
    }
}

fn finite_char2_metric<F: FiniteChar2Field>(
    q: &[u128],
    b: &BTreeMap<(usize, usize), u128>,
) -> PyResult<Metric<F>> {
    F::ensure_supported().ok_or_else(unsupported_char2_finite_field_err)?;
    let order = F::field_order();
    let dim = q.len();
    let qv = q
        .iter()
        .map(|&x| {
            if x < order {
                Ok(F::from_index(x))
            } else {
                Err(PyValueError::new_err(format!(
                    "field element index {x} is outside F_{order}"
                )))
            }
        })
        .collect::<PyResult<Vec<_>>>()?;
    let mut bm = BTreeMap::new();
    for (&(i, j), &x) in b {
        if i == j {
            return Err(PyValueError::new_err("b-keys must be off-diagonal"));
        }
        if i >= dim || j >= dim {
            return Err(PyValueError::new_err("b-key index out of range"));
        }
        if x >= order {
            return Err(PyValueError::new_err(format!(
                "field element index {x} is outside F_{order}"
            )));
        }
        let key = if i < j { (i, j) } else { (j, i) };
        bm.insert(key, F::from_index(x));
    }
    Ok(Metric::new(qv, bm))
}

macro_rules! with_finite_char2_metric {
    ($degree:expr, $q:expr, $b:expr, |$metric:ident| $body:expr) => {{
        with_finite_char2_field!($degree, |Field| {
            let $metric = finite_char2_metric::<Field>($q, $b)?;
            $body
        })
    }};
}

macro_rules! with_finite_char2_metrics {
    ($degree:expr, $q1:expr, $b1:expr, $q2:expr, $b2:expr, |$m1:ident, $m2:ident| $body:expr) => {{
        with_finite_char2_field!($degree, |Field| {
            let $m1 = finite_char2_metric::<Field>($q1, $b1)?;
            let $m2 = finite_char2_metric::<Field>($q2, $b2)?;
            $body
        })
    }};
}

macro_rules! with_finite_odd_metric {
    ($p:expr, $degree:expr, $q:expr, |$metric:ident| $body:expr) => {{
        with_finite_odd_field!($p, $degree, |Field| {
            let $metric = finite_diag::<Field>($q);
            $body
        })
    }};
}

macro_rules! with_finite_odd_metrics {
    ($p:expr, $degree:expr, $q1:expr, $q2:expr, |$m1:ident, $m2:ident| $body:expr) => {{
        with_finite_odd_field!($p, $degree, |Field| {
            let $m1 = finite_diag::<Field>($q1);
            let $m2 = finite_diag::<Field>($q2);
            $body
        })
    }};
}

macro_rules! with_finite_odd_value {
    ($p:expr, $degree:expr, $x:expr, |$value:ident| $body:expr) => {{
        with_finite_odd_field!($p, $degree, |Field| {
            let $value = <Field as crate::scalar::Scalar>::from_int($x);
            $body
        })
    }};
}

macro_rules! with_finite_odd_field {
    ($p:expr, $degree:expr, |$field:ident| $body:expr) => {{
        match ($p, $degree) {
            (3, 1) => {
                type $field = Fp<3>;
                $body
            }
            (5, 1) => {
                type $field = Fp<5>;
                $body
            }
            (7, 1) => {
                type $field = Fp<7>;
                $body
            }
            (11, 1) => {
                type $field = Fp<11>;
                $body
            }
            (13, 1) => {
                type $field = Fp<13>;
                $body
            }
            (3, 2) => {
                type $field = Fpn<3, 2>;
                $body
            }
            (5, 2) => {
                type $field = Fpn<5, 2>;
                $body
            }
            (3, 3) => {
                type $field = Fpn<3, 3>;
                $body
            }
            _ => return Err(unsupported_finite_field_err()),
        }
    }};
}

macro_rules! with_finite_char2_field {
    ($degree:expr, |$field:ident| $body:expr) => {{
        match $degree {
            1 => {
                type $field = Fpn<2, 1>;
                $body
            }
            2 => {
                type $field = Fpn<2, 2>;
                $body
            }
            3 => {
                type $field = Fpn<2, 3>;
                $body
            }
            4 => {
                type $field = Fpn<2, 4>;
                $body
            }
            _ => return Err(unsupported_char2_finite_field_err()),
        }
    }};
}

macro_rules! with_supported_finite_field {
    ($p:expr, $degree:expr, |$field:ident| $body:expr) => {{
        if $p == 2 {
            with_finite_char2_field!($degree, |$field| $body)
        } else {
            with_finite_odd_field!($p, $degree, |$field| $body)
        }
    }};
}

type PyFFPoly = Vec<u128>;
type PyFFRationalFunction = (PyFFPoly, PyFFPoly);

#[pyclass(name = "FunctionFieldPlace", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyFunctionFieldPlace {
    field_order: u128,
    polynomial: Option<PyFFPoly>,
    // Rendered from the core `FunctionFieldPlace` at construction time (`∞` or
    // the place polynomial's own Display), since this struct is a per-field
    // erasure of the generic core value. `__repr__` keeps its fuller
    // `FunctionFieldPlace(F_q, ...)` framing on purpose — the core Display is
    // the terse form meant for embedding inside other records' renders.
    rendered: String,
}

#[pymethods]
impl PyFunctionFieldPlace {
    #[getter]
    fn field_order(&self) -> u128 {
        self.field_order
    }
    #[getter]
    fn kind(&self) -> &'static str {
        if self.polynomial.is_some() {
            "finite"
        } else {
            "infinite"
        }
    }
    #[getter]
    fn polynomial(&self) -> Option<PyFFPoly> {
        self.polynomial.clone()
    }
    #[getter]
    fn degree(&self) -> Option<usize> {
        self.polynomial.as_ref().map(|p| p.len().saturating_sub(1))
    }
    fn is_infinite(&self) -> bool {
        self.polynomial.is_none()
    }
    fn display(&self) -> String {
        self.rendered.clone()
    }
    fn __repr__(&self) -> String {
        match &self.polynomial {
            Some(poly) => format!(
                "FunctionFieldPlace(F_{}, finite={poly:?})",
                self.field_order
            ),
            None => format!("FunctionFieldPlace(F_{}, infinity)", self.field_order),
        }
    }
}

#[pyclass(name = "FunctionFieldAdelicIsotropy", module = "ogdoad")]
struct PyFunctionFieldAdelicIsotropy {
    local: Vec<PyFunctionFieldLocalIsotropy>,
    // Rendered from the core `FFAdelicIsotropy` at construction time, since
    // this struct is a per-field erasure of the generic core value. The core
    // type's own name is `FFAdelicIsotropy`; swap in the pyclass name so
    // Python users see the name they imported.
    rendered: String,
}

#[pyclass(
    name = "FunctionFieldLocalIsotropy",
    module = "ogdoad",
    skip_from_py_object
)]
#[derive(Clone)]
struct PyFunctionFieldLocalIsotropy {
    place: PyFunctionFieldPlace,
    is_isotropic: bool,
}

#[pymethods]
impl PyFunctionFieldLocalIsotropy {
    #[getter]
    fn place(&self) -> PyFunctionFieldPlace {
        self.place.clone()
    }
    #[getter]
    fn is_isotropic(&self) -> bool {
        self.is_isotropic
    }
    fn __repr__(&self) -> String {
        format!(
            "FunctionFieldLocalIsotropy(place={}, is_isotropic={})",
            self.place.__repr__(),
            self.is_isotropic
        )
    }
}

#[pymethods]
impl PyFunctionFieldAdelicIsotropy {
    #[getter]
    fn local(&self) -> Vec<PyFunctionFieldLocalIsotropy> {
        self.local.clone()
    }
    fn is_global(&self) -> bool {
        self.local.iter().all(|row| row.is_isotropic)
    }
    fn display(&self) -> String {
        self.rendered
            .replacen("FFAdelicIsotropy", "FunctionFieldAdelicIsotropy", 1)
    }
    fn __repr__(&self) -> String {
        self.display()
    }
}

fn finite_field_index<F: FiniteOddField>(x: F) -> u128 {
    (0..F::field_order())
        .find(|&i| F::from_index(i) == x)
        .expect("finite-field element must be enumerated by from_index")
}

fn ff_poly_indices<F: FiniteOddField>(poly: &Poly<F>) -> PyFFPoly {
    poly.coeffs()
        .iter()
        .copied()
        .map(finite_field_index::<F>)
        .collect()
}

fn parse_ff_poly<F: FiniteOddField>(coeffs: &[u128], name: &str) -> PyResult<Poly<F>> {
    F::ensure_supported().ok_or_else(unsupported_finite_field_err)?;
    let order = F::field_order();
    coeffs
        .iter()
        .enumerate()
        .map(|(i, &x)| {
            if x < order {
                Ok(F::from_index(x))
            } else {
                Err(PyValueError::new_err(format!(
                    "{name}[{i}]={x} is outside F_{order}"
                )))
            }
        })
        .collect::<PyResult<Vec<_>>>()
        .map(Poly::new)
}

fn parse_ff_rational_function<F: FiniteOddField>(
    raw: &PyFFRationalFunction,
    name: &str,
) -> PyResult<RationalFunction<F>> {
    let num = parse_ff_poly::<F>(&raw.0, &format!("{name}.num"))?;
    let den = parse_ff_poly::<F>(&raw.1, &format!("{name}.den"))?;
    if den.is_zero() {
        return Err(PyValueError::new_err(format!(
            "{name} denominator must be nonzero"
        )));
    }
    Ok(RationalFunction::new(
        num.coeffs().to_vec(),
        den.coeffs().to_vec(),
    ))
}

fn parse_ff_rational_functions<F: FiniteOddField>(
    entries: &[PyFFRationalFunction],
) -> PyResult<Vec<RationalFunction<F>>> {
    entries
        .iter()
        .enumerate()
        .map(|(i, raw)| parse_ff_rational_function::<F>(raw, &format!("entries[{i}]")))
        .collect()
}

fn ensure_ff_nonzero<F: ExactFieldScalar>(x: &RationalFunction<F>, name: &str) -> PyResult<()> {
    if x.is_zero() {
        Err(PyValueError::new_err(format!("{name} must be nonzero")))
    } else {
        Ok(())
    }
}

fn parse_ff_place<F: FiniteOddField>(poly: Option<PyFFPoly>) -> PyResult<FunctionFieldPlace<F>> {
    match poly {
        None => Ok(FunctionFieldPlace::Infinite),
        Some(coeffs) => {
            let place = parse_ff_poly::<F>(&coeffs, "place")?;
            if place.degree().is_none_or(|d| d == 0) {
                return Err(PyValueError::new_err(
                    "finite function-field place must have positive degree",
                ));
            }
            if place.leading() != Some(&F::one()) {
                return Err(PyValueError::new_err(
                    "finite function-field place must be monic",
                ));
            }
            if crate::forms::monic_irreducible_factors(&place) != vec![place.clone()] {
                return Err(PyValueError::new_err(
                    "finite function-field place must be irreducible",
                ));
            }
            Ok(FunctionFieldPlace::Finite(place))
        }
    }
}

fn wrap_ff_place<F: FiniteOddField>(place: FunctionFieldPlace<F>) -> PyFunctionFieldPlace {
    let rendered = place.to_string();
    PyFunctionFieldPlace {
        field_order: F::field_order(),
        polynomial: match place {
            FunctionFieldPlace::Infinite => None,
            FunctionFieldPlace::Finite(poly) => Some(ff_poly_indices(&poly)),
        },
        rendered,
    }
}

fn wrap_ff_adeles<F: FiniteOddField>(
    inner: crate::forms::FFAdelicIsotropy<F>,
) -> PyFunctionFieldAdelicIsotropy {
    let rendered = inner.to_string();
    PyFunctionFieldAdelicIsotropy {
        local: inner
            .local
            .into_iter()
            .map(|(place, is_isotropic)| PyFunctionFieldLocalIsotropy {
                place: wrap_ff_place(place),
                is_isotropic,
            })
            .collect(),
        rendered,
    }
}

fn finite_char2_field_index<F: FiniteChar2Field>(x: F) -> u128 {
    (0..F::field_order())
        .find(|&i| F::from_index(i) == x)
        .expect("finite char-2 field element must be enumerated by from_index")
}

fn parse_char2_matrix<F: FiniteChar2Field>(matrix: &[Vec<u128>]) -> PyResult<Vec<Vec<F>>> {
    F::ensure_supported().ok_or_else(unsupported_char2_finite_field_err)?;
    let order = F::field_order();
    matrix
        .iter()
        .map(|row| {
            row.iter()
                .map(|&value| {
                    if value < order {
                        Ok(F::from_index(value))
                    } else {
                        Err(PyValueError::new_err(format!(
                            "field element index {value} is outside F_{order}"
                        )))
                    }
                })
                .collect()
        })
        .collect()
}

fn wrap_char2_factorization<F: FiniteChar2Field>(
    degree: usize,
    certificate: crate::forms::Char2SymmetryFactorization<F>,
) -> PyChar2SymmetryFactorization {
    let matrix = certificate
        .matrix()
        .iter()
        .map(|row| {
            row.iter()
                .copied()
                .map(finite_char2_field_index::<F>)
                .collect()
        })
        .collect();
    let factors = certificate
        .factors()
        .iter()
        .map(|root| {
            root.iter()
                .copied()
                .map(finite_char2_field_index::<F>)
                .collect()
        })
        .collect();
    PyChar2SymmetryFactorization {
        degree,
        matrix,
        factors,
        dickson: certificate.dickson(),
        clifford_verified: certificate.verifies_clifford_action(),
        rendered: certificate.display(),
    }
}

/// The additive characteristic-two spinor norm of an isometry of `F_{2^degree}`.
#[pyfunction]
#[pyo3(signature = (q, b, matrix, degree=1))]
fn char2_spinor_norm(
    q: Vec<u128>,
    b: BTreeMap<(usize, usize), u128>,
    matrix: Vec<Vec<u128>>,
    degree: usize,
) -> PyResult<u128> {
    with_finite_char2_metric!(degree, &q, &b, |metric| {
        let parsed = parse_char2_matrix::<Field>(&matrix)?;
        crate::forms::char2_spinor_norm(&metric, &parsed)
            .map_err(|error| PyValueError::new_err(error.to_string()))
    })
}

/// Certify a vector-symmetry factorization of an isometry of `F_{2^degree}`.
#[pyfunction]
#[pyo3(signature = (q, b, matrix, degree=1))]
fn factor_char2_isometry(
    q: Vec<u128>,
    b: BTreeMap<(usize, usize), u128>,
    matrix: Vec<Vec<u128>>,
    degree: usize,
) -> PyResult<PyChar2SymmetryFactorization> {
    with_finite_char2_metric!(degree, &q, &b, |metric| {
        let parsed = parse_char2_matrix::<Field>(&matrix)?;
        crate::forms::factor_char2_isometry(&metric, &parsed)
            .map(|certificate| wrap_char2_factorization(degree, certificate))
            .map_err(|error| PyValueError::new_err(error.to_string()))
    })
}

fn char2_ff_poly_indices<F: FiniteChar2Field>(poly: &Poly<F>) -> PyFFPoly {
    poly.coeffs()
        .iter()
        .copied()
        .map(finite_char2_field_index::<F>)
        .collect()
}

fn parse_char2_ff_poly<F: FiniteChar2Field>(coeffs: &[u128], name: &str) -> PyResult<Poly<F>> {
    F::ensure_supported().ok_or_else(unsupported_char2_finite_field_err)?;
    let order = F::field_order();
    coeffs
        .iter()
        .enumerate()
        .map(|(i, &x)| {
            if x < order {
                Ok(F::from_index(x))
            } else {
                Err(PyValueError::new_err(format!(
                    "{name}[{i}]={x} is outside F_{order}"
                )))
            }
        })
        .collect::<PyResult<Vec<_>>>()
        .map(Poly::new)
}

fn parse_char2_ff_rational_function<F: FiniteChar2Field>(
    raw: &PyFFRationalFunction,
    name: &str,
) -> PyResult<RationalFunction<F>> {
    let num = parse_char2_ff_poly::<F>(&raw.0, &format!("{name}.num"))?;
    let den = parse_char2_ff_poly::<F>(&raw.1, &format!("{name}.den"))?;
    if den.is_zero() {
        return Err(PyValueError::new_err(format!(
            "{name} denominator must be nonzero"
        )));
    }
    Ok(RationalFunction::new(
        num.coeffs().to_vec(),
        den.coeffs().to_vec(),
    ))
}

fn parse_char2_ff_blocks<F: FiniteChar2Field>(
    blocks: &[(PyFFRationalFunction, PyFFRationalFunction)],
) -> PyResult<Vec<(RationalFunction<F>, RationalFunction<F>)>> {
    blocks
        .iter()
        .enumerate()
        .map(|(i, (a, b))| {
            Ok((
                parse_char2_ff_rational_function::<F>(a, &format!("blocks[{i}].a"))?,
                parse_char2_ff_rational_function::<F>(b, &format!("blocks[{i}].b"))?,
            ))
        })
        .collect()
}

fn parse_char2_ff_rational_functions<F: FiniteChar2Field>(
    entries: &[PyFFRationalFunction],
    name: &str,
) -> PyResult<Vec<RationalFunction<F>>> {
    entries
        .iter()
        .enumerate()
        .map(|(i, raw)| parse_char2_ff_rational_function::<F>(raw, &format!("{name}[{i}]")))
        .collect()
}

fn parse_char2_ff_form<F: FiniteChar2Field>(
    blocks: &[(PyFFRationalFunction, PyFFRationalFunction)],
    singular: &[PyFFRationalFunction],
) -> PyResult<Char2QuadForm<F>> {
    Ok(Char2QuadForm::new(
        parse_char2_ff_blocks::<F>(blocks)?,
        parse_char2_ff_rational_functions::<F>(singular, "singular")?,
    ))
}

fn parse_char2_ff_place<F: FiniteChar2Field>(
    poly: Option<PyFFPoly>,
) -> PyResult<FunctionFieldPlace<F>> {
    match poly {
        None => Ok(FunctionFieldPlace::Infinite),
        Some(coeffs) => {
            let place = parse_char2_ff_poly::<F>(&coeffs, "place")?;
            if place.degree().is_none_or(|d| d == 0) {
                return Err(PyValueError::new_err(
                    "finite function-field place must have positive degree",
                ));
            }
            if place.leading() != Some(&F::one()) {
                return Err(PyValueError::new_err(
                    "finite function-field place must be monic",
                ));
            }
            if crate::forms::char2_monic_irreducible_factors(&place) != vec![place.clone()] {
                return Err(PyValueError::new_err(
                    "finite function-field place must be irreducible",
                ));
            }
            Ok(FunctionFieldPlace::Finite(place))
        }
    }
}

fn wrap_char2_ff_place<F: FiniteChar2Field>(place: FunctionFieldPlace<F>) -> PyFunctionFieldPlace {
    let rendered = place.to_string();
    PyFunctionFieldPlace {
        field_order: F::field_order(),
        polynomial: match place {
            FunctionFieldPlace::Infinite => None,
            FunctionFieldPlace::Finite(poly) => Some(char2_ff_poly_indices(&poly)),
        },
        rendered,
    }
}

#[pyclass(name = "Char2LocalDecomp", module = "ogdoad")]
struct PyChar2LocalDecomp {
    field_order: u128,
    phi0: u128,
    psi: Vec<PyChar2PsiTerm>,
    phi1: u128,
    // Rendered from the core `Char2LocalDecomp` at construction time, since
    // this struct is a per-field erasure of the generic core value (renders
    // ψ coefficients via `Poly`'s own Display, not an index dump).
    rendered: String,
}

#[pyclass(name = "Char2PsiTerm", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyChar2PsiTerm {
    field_order: u128,
    pole_order: usize,
    coefficient: PyFFPoly,
}

#[pymethods]
impl PyChar2PsiTerm {
    #[getter]
    fn field_order(&self) -> u128 {
        self.field_order
    }
    #[getter]
    fn pole_order(&self) -> usize {
        self.pole_order
    }
    #[getter]
    fn coefficient(&self) -> PyFFPoly {
        self.coefficient.clone()
    }
    fn __repr__(&self) -> String {
        format!(
            "Char2PsiTerm(F_{}, pole_order={}, coefficient={:?})",
            self.field_order, self.pole_order, self.coefficient
        )
    }
}

#[pymethods]
impl PyChar2LocalDecomp {
    #[getter]
    fn field_order(&self) -> u128 {
        self.field_order
    }
    #[getter]
    fn phi0(&self) -> u128 {
        self.phi0
    }
    #[getter]
    fn psi(&self) -> Vec<PyChar2PsiTerm> {
        self.psi.clone()
    }
    #[getter]
    fn phi1(&self) -> u128 {
        self.phi1
    }
    fn display(&self) -> String {
        self.rendered.clone()
    }
    fn __repr__(&self) -> String {
        self.rendered.clone()
    }
}

fn wrap_char2_local_decomp<F: FiniteChar2Field>(inner: Char2LocalDecomp<F>) -> PyChar2LocalDecomp {
    let rendered = inner.to_string();
    PyChar2LocalDecomp {
        field_order: F::field_order(),
        phi0: inner.phi0,
        psi: inner
            .psi
            .into_iter()
            .map(|(pole_order, poly)| PyChar2PsiTerm {
                field_order: F::field_order(),
                pole_order,
                coefficient: char2_ff_poly_indices(&poly),
            })
            .collect(),
        phi1: inner.phi1,
        rendered,
    }
}

#[pyclass(name = "OddCharInvariants", module = "ogdoad")]
struct PyOddCharInvariants {
    inner: crate::forms::OddCharInvariants,
}

#[pymethods]
impl PyOddCharInvariants {
    #[getter]
    fn p(&self) -> u128 {
        self.inner.p
    }
    #[getter]
    fn field_order(&self) -> u128 {
        self.inner.field_order
    }
    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim
    }
    #[getter]
    fn radical_dim(&self) -> usize {
        self.inner.radical_dim
    }
    #[getter]
    fn disc_is_square(&self) -> bool {
        self.inner.disc_is_square
    }
    #[getter]
    fn hasse(&self) -> i128 {
        self.inner.hasse
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(name = "OddFiniteFieldForm", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyOddFiniteFieldForm {
    p: u128,
    degree: usize,
    q: Vec<i128>,
}

#[pymethods]
impl PyOddFiniteFieldForm {
    #[new]
    #[pyo3(signature = (p, q, degree=1))]
    fn new(p: u128, q: Vec<i128>, degree: usize) -> PyResult<Self> {
        finite_field_order(p, degree)?;
        Ok(PyOddFiniteFieldForm { p, degree, q })
    }

    #[getter]
    fn p(&self) -> u128 {
        self.p
    }

    #[getter]
    fn degree(&self) -> usize {
        self.degree
    }

    #[getter]
    fn field_order(&self) -> PyResult<u128> {
        finite_field_order(self.p, self.degree)
    }

    #[getter]
    fn diagonal(&self) -> Vec<i128> {
        self.q.clone()
    }

    fn classify(&self) -> PyResult<PyOddCharInvariants> {
        let res = with_finite_odd_metric!(self.p, self.degree, &self.q, |m| {
            crate::forms::classify_finite_odd(&m)
        });
        res.map(|inner| PyOddCharInvariants { inner })
            .ok_or_else(|| PyValueError::new_err("non-diagonal metric"))
    }

    fn classify_unified(&self) -> PyResult<PyFiniteFieldInvariants> {
        let res = with_finite_odd_metric!(self.p, self.degree, &self.q, |m| {
            crate::forms::classify_finite_odd(&m)
        });
        res.map(|inner| PyFiniteFieldInvariants {
            inner: crate::forms::FiniteFieldInvariants::Odd(inner),
        })
        .ok_or_else(|| PyValueError::new_err("non-diagonal metric"))
    }

    fn witt_class(&self) -> PyResult<PyWittClassG> {
        let res = with_finite_odd_metric!(self.p, self.degree, &self.q, |m| {
            crate::forms::finite_odd_witt(&m)
        });
        res.map(|inner| PyWittClassG { inner })
            .ok_or_else(|| PyValueError::new_err("non-diagonal metric"))
    }

    fn witt_decompose(&self) -> PyResult<PyOddWittDecomp> {
        let d = with_finite_odd_metric!(self.p, self.degree, &self.q, |m| {
            crate::forms::witt_decompose_finite_odd(&m)
        })
        .ok_or_else(|| PyValueError::new_err("non-diagonal metric"))?;
        Ok(wrap_odd_witt_decomp(d))
    }

    fn is_isometric(&self, other: &PyOddFiniteFieldForm) -> PyResult<bool> {
        if self.p != other.p || self.degree != other.degree {
            return Err(PyValueError::new_err(
                "isometry needs both forms over the same finite field",
            ));
        }
        with_finite_odd_metrics!(self.p, self.degree, &self.q, &other.q, |m1, m2| {
            crate::forms::isometric_finite_odd(&m1, &m2)
                .ok_or_else(|| PyValueError::new_err("non-diagonal metric"))
        })
    }
    fn isometric_to(&self, other: &PyOddFiniteFieldForm) -> PyResult<bool> {
        self.is_isometric(other)
    }

    fn is_square(&self, x: i128) -> PyResult<bool> {
        Ok(with_finite_odd_value!(self.p, self.degree, x, |value| {
            crate::forms::is_square_finite(value)
        }))
    }

    /// Discriminant square-class representative as a finite-field element index.
    fn discriminant(&self) -> PyResult<u128> {
        with_finite_odd_field!(self.p, self.degree, |F| {
            let metric = finite_diag::<F>(&self.q);
            crate::forms::discriminant_finite_odd(&metric)
                .map(finite_field_index::<F>)
                .ok_or_else(|| PyValueError::new_err("non-diagonal metric"))
        })
    }

    fn hasse_invariant(&self) -> PyResult<i128> {
        with_finite_odd_metric!(self.p, self.degree, &self.q, |m| {
            crate::forms::hasse_invariant_finite_odd(&m)
                .ok_or_else(|| PyValueError::new_err("non-diagonal metric"))
        })
    }

    fn e_staircase(&self) -> PyResult<PyEnStaircase> {
        let s = with_finite_odd_metric!(self.p, self.degree, &self.q, |m| {
            crate::forms::e_staircase_finite_odd(&m)
        })
        .ok_or_else(|| PyValueError::new_err("non-diagonal metric"))?;
        Ok(wrap_en_staircase(s))
    }

    fn bw_class(&self) -> PyResult<PyBrauerWallClass> {
        let res = with_finite_odd_metric!(self.p, self.degree, &self.q, |m| {
            crate::forms::bw_class_finite_odd(&m)
        });
        res.map(|inner| PyBrauerWallClass { inner })
            .ok_or_else(|| PyValueError::new_err("non-diagonal metric"))
    }

    fn __repr__(&self) -> PyResult<String> {
        Ok(format!(
            "OddFiniteFieldForm(F_{}, diagonal={:?})",
            self.field_order()?,
            self.q
        ))
    }
}

#[pyclass(name = "Char2FiniteFieldForm", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyChar2FiniteFieldForm {
    degree: usize,
    q: Vec<u128>,
    b: BTreeMap<(usize, usize), u128>,
}

#[pymethods]
impl PyChar2FiniteFieldForm {
    #[new]
    #[pyo3(signature = (q, b=None, degree=1))]
    fn new(q: Vec<u128>, b: Option<Bound<'_, PyDict>>, degree: usize) -> PyResult<Self> {
        let order = char2_finite_field_order(degree)?;
        let dim = q.len();
        if let Some(&x) = q.iter().find(|&&x| x >= order) {
            return Err(PyValueError::new_err(format!(
                "field element index {x} is outside F_{order}"
            )));
        }
        let mut bm = BTreeMap::new();
        if let Some(d) = b {
            for (k, v) in d.iter() {
                let (i, j): (usize, usize) = k.extract()?;
                if i == j {
                    return Err(PyValueError::new_err("b-keys must be off-diagonal"));
                }
                if i >= dim || j >= dim {
                    return Err(PyValueError::new_err("b-key index out of range"));
                }
                let x: u128 = v.extract()?;
                if x >= order {
                    return Err(PyValueError::new_err(format!(
                        "field element index {x} is outside F_{order}"
                    )));
                }
                let key = if i < j { (i, j) } else { (j, i) };
                bm.insert(key, x);
            }
        }
        Ok(PyChar2FiniteFieldForm { degree, q, b: bm })
    }

    #[getter]
    fn degree(&self) -> usize {
        self.degree
    }

    #[getter]
    fn field_order(&self) -> PyResult<u128> {
        char2_finite_field_order(self.degree)
    }

    #[getter]
    fn diagonal(&self) -> Vec<u128> {
        self.q.clone()
    }

    #[getter]
    fn polar(&self) -> BTreeMap<(usize, usize), u128> {
        self.b.clone()
    }

    fn classify(&self) -> PyResult<PyArfInvariants> {
        let res = with_finite_char2_metric!(self.degree, &self.q, &self.b, |m| {
            crate::forms::arf_fpn_char2(&m)
        });
        res.map(|inner| PyArfInvariants { inner })
            .ok_or_else(|| PyValueError::new_err("metric is outside finite char-2 Arf scope"))
    }

    fn classify_unified(&self) -> PyResult<PyFiniteFieldInvariants> {
        let res = with_finite_char2_metric!(self.degree, &self.q, &self.b, |m| {
            crate::forms::arf_fpn_char2(&m)
        });
        res.map(|inner| PyFiniteFieldInvariants {
            inner: crate::forms::FiniteFieldInvariants::Char2(inner),
        })
        .ok_or_else(|| PyValueError::new_err("metric is outside finite char-2 Arf scope"))
    }

    fn witt_class(&self) -> PyResult<PyWittClassG> {
        let res = with_finite_char2_metric!(self.degree, &self.q, &self.b, |m| {
            crate::forms::ClassifyWitt::witt_class(&m)
        });
        res.map(|inner| PyWittClassG { inner })
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }

    fn bw_class(&self) -> PyResult<PyBrauerWallClass> {
        let res = with_finite_char2_metric!(self.degree, &self.q, &self.b, |m| {
            crate::forms::ClassifyBrauerWall::bw_class(&m)
        });
        res.map(|inner| PyBrauerWallClass { inner })
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }

    fn is_isometric(&self, other: &PyChar2FiniteFieldForm) -> PyResult<bool> {
        if self.degree != other.degree {
            return Err(PyValueError::new_err(
                "isometry needs both forms over the same finite char-2 field",
            ));
        }
        with_finite_char2_metrics!(
            self.degree,
            &self.q,
            &self.b,
            &other.q,
            &other.b,
            |m1, m2| {
                crate::forms::ClassifyIsometry::isometric(&m1, &m2)
                    .map_err(|e| PyValueError::new_err(e.to_string()))
            }
        )
    }
    fn isometric_to(&self, other: &PyChar2FiniteFieldForm) -> PyResult<bool> {
        self.is_isometric(other)
    }

    fn __repr__(&self) -> PyResult<String> {
        Ok(format!(
            "Char2FiniteFieldForm(F_{}, q={:?}, b={:?})",
            self.field_order()?,
            self.q,
            self.b
        ))
    }
}

#[pyclass(name = "Char2FunctionFieldForm", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyChar2FunctionFieldForm {
    degree: usize,
    blocks: Vec<(PyFFRationalFunction, PyFFRationalFunction)>,
    singular: Vec<PyFFRationalFunction>,
}

#[pymethods]
impl PyChar2FunctionFieldForm {
    #[new]
    #[pyo3(signature = (blocks, singular=None, degree=1))]
    fn new(
        blocks: Vec<(PyFFRationalFunction, PyFFRationalFunction)>,
        singular: Option<Vec<PyFFRationalFunction>>,
        degree: usize,
    ) -> PyResult<Self> {
        char2_finite_field_order(degree)?;
        let singular = singular.unwrap_or_default();
        with_finite_char2_field!(degree, |F| {
            parse_char2_ff_form::<F>(&blocks, &singular)?;
            Ok(Self {
                degree,
                blocks,
                singular,
            })
        })
    }
    #[staticmethod]
    #[pyo3(signature = (blocks, degree=1))]
    fn from_blocks(
        blocks: Vec<(PyFFRationalFunction, PyFFRationalFunction)>,
        degree: usize,
    ) -> PyResult<Self> {
        Self::new(blocks, None, degree)
    }

    #[getter]
    fn degree(&self) -> usize {
        self.degree
    }

    #[getter]
    fn field_order(&self) -> PyResult<u128> {
        char2_finite_field_order(self.degree)
    }

    #[getter]
    fn blocks(&self) -> Vec<(PyFFRationalFunction, PyFFRationalFunction)> {
        self.blocks.clone()
    }

    #[getter]
    fn singular(&self) -> Vec<PyFFRationalFunction> {
        self.singular.clone()
    }

    fn rank(&self) -> usize {
        2 * self.blocks.len() + self.singular.len()
    }

    fn relevant_places(&self) -> PyResult<Vec<PyFunctionFieldPlace>> {
        with_finite_char2_field!(self.degree, |F| {
            let form = parse_char2_ff_form::<F>(&self.blocks, &self.singular)?;
            Ok(crate::forms::artin_schreier_form_places(&form)
                .into_iter()
                .map(wrap_char2_ff_place::<F>)
                .collect())
        })
    }

    #[pyo3(signature = (place=None))]
    fn decompose_at(&self, place: Option<PyFFPoly>) -> PyResult<PyChar2LocalDecomp> {
        with_finite_char2_field!(self.degree, |F| {
            let form = parse_char2_ff_form::<F>(&self.blocks, &self.singular)?;
            let place = parse_char2_ff_place::<F>(place)?;
            Ok(wrap_char2_local_decomp(
                crate::forms::springer_decompose_local_char2(&form, &place),
            ))
        })
    }

    #[pyo3(signature = (place=None))]
    fn local_anisotropic_dim(&self, place: Option<PyFFPoly>) -> PyResult<Option<usize>> {
        with_finite_char2_field!(self.degree, |F| {
            let form = parse_char2_ff_form::<F>(&self.blocks, &self.singular)?;
            let place = parse_char2_ff_place::<F>(place)?;
            Ok(crate::forms::local_anisotropic_dim_char2(&form, &place))
        })
    }

    #[pyo3(signature = (place=None))]
    fn is_isotropic_at_place(&self, place: Option<PyFFPoly>) -> PyResult<Option<bool>> {
        with_finite_char2_field!(self.degree, |F| {
            let form = parse_char2_ff_form::<F>(&self.blocks, &self.singular)?;
            let place = parse_char2_ff_place::<F>(place)?;
            Ok(crate::forms::local_is_isotropic_char2(&form, &place))
        })
    }

    fn is_isotropic(&self) -> PyResult<Option<bool>> {
        with_finite_char2_field!(self.degree, |F| {
            let form = parse_char2_ff_form::<F>(&self.blocks, &self.singular)?;
            Ok(crate::forms::is_isotropic_global_char2(&form))
        })
    }

    fn __repr__(&self) -> PyResult<String> {
        Ok(format!(
            "Char2FunctionFieldForm(F_{}, blocks={:?}, singular={:?})",
            self.field_order()?,
            self.blocks,
            self.singular
        ))
    }
}

/// Distinct monic irreducible factors of a polynomial over `F_{p^degree}`.
/// Coefficients are finite-field element indices, low degree first.
#[pyfunction]
#[pyo3(signature = (p, poly, degree=1))]
fn monic_irreducible_factors(p: u128, poly: PyFFPoly, degree: usize) -> PyResult<Vec<PyFFPoly>> {
    with_finite_odd_field!(p, degree, |F| {
        let poly = parse_ff_poly::<F>(&poly, "poly")?;
        Ok(crate::forms::monic_irreducible_factors(&poly)
            .iter()
            .map(ff_poly_indices::<F>)
            .collect())
    })
}

/// Checked relevant places for a diagonal form over `F_{p^degree}(t)`. Each entry
/// is `(numerator_coeffs, denominator_coeffs)`, with coefficients as field indices.
#[pyfunction]
#[pyo3(signature = (p, entries, degree=1))]
fn try_relevant_places_ff(
    p: u128,
    entries: Vec<PyFFRationalFunction>,
    degree: usize,
) -> PyResult<Option<Vec<PyFunctionFieldPlace>>> {
    with_finite_odd_field!(p, degree, |F| {
        let entries = parse_ff_rational_functions::<F>(&entries)?;
        Ok(
            crate::forms::try_relevant_places_ff(&entries).map(|places| {
                places
                    .into_iter()
                    .map(wrap_ff_place::<F>)
                    .collect::<Vec<_>>()
            }),
        )
    })
}

/// Checked valuation of an element of `F_{p^degree}(t)` at a place. `place=None`
/// means the degree place at infinity; otherwise pass a monic irreducible
/// polynomial's coefficients.
#[pyfunction]
#[pyo3(signature = (p, a, place=None, degree=1))]
fn try_valuation_at_ff(
    p: u128,
    a: PyFFRationalFunction,
    place: Option<PyFFPoly>,
    degree: usize,
) -> PyResult<Option<i128>> {
    with_finite_odd_field!(p, degree, |F| {
        let a = parse_ff_rational_function::<F>(&a, "a")?;
        let place = parse_ff_place::<F>(place)?;
        Ok(crate::forms::try_valuation_at_ff(&a, &place))
    })
}

/// Checked local squarehood at `place`.
#[pyfunction]
#[pyo3(signature = (p, a, place=None, degree=1))]
fn try_is_local_square_ff(
    p: u128,
    a: PyFFRationalFunction,
    place: Option<PyFFPoly>,
    degree: usize,
) -> PyResult<Option<bool>> {
    with_finite_odd_field!(p, degree, |F| {
        let a = parse_ff_rational_function::<F>(&a, "a")?;
        let place = parse_ff_place::<F>(place)?;
        Ok(crate::forms::try_is_local_square_ff(&a, &place))
    })
}

/// Whether a nonzero element is a global square in `F_{p^degree}(t)`.
#[pyfunction]
#[pyo3(signature = (p, x, degree=1))]
fn is_global_square_ff(p: u128, x: PyFFRationalFunction, degree: usize) -> PyResult<bool> {
    with_finite_odd_field!(p, degree, |F| {
        let x = parse_ff_rational_function::<F>(&x, "x")?;
        Ok(crate::forms::is_global_square_ff(&x))
    })
}

/// Checked Hilbert symbol `(a,b)_v` over `F_{p^degree}(t)` at `place`.
#[pyfunction]
#[pyo3(signature = (p, a, b, place=None, degree=1))]
fn try_hilbert_symbol_ff(
    p: u128,
    a: PyFFRationalFunction,
    b: PyFFRationalFunction,
    place: Option<PyFFPoly>,
    degree: usize,
) -> PyResult<Option<i128>> {
    with_finite_odd_field!(p, degree, |F| {
        let a = parse_ff_rational_function::<F>(&a, "a")?;
        let b = parse_ff_rational_function::<F>(&b, "b")?;
        let place = parse_ff_place::<F>(place)?;
        Ok(crate::forms::try_hilbert_symbol_ff(&a, &b, &place))
    })
}

/// Checked Hasse invariant of a diagonal form over `F_{p^degree}(t)` at `place`.
#[pyfunction]
#[pyo3(signature = (p, entries, place=None, degree=1))]
fn try_hasse_at_place_ff(
    p: u128,
    entries: Vec<PyFFRationalFunction>,
    place: Option<PyFFPoly>,
    degree: usize,
) -> PyResult<Option<i128>> {
    with_finite_odd_field!(p, degree, |F| {
        let entries = parse_ff_rational_functions::<F>(&entries)?;
        let place = parse_ff_place::<F>(place)?;
        Ok(crate::forms::try_hasse_at_place_ff(&entries, &place))
    })
}

/// Checked Hilbert reciprocity product `prod_v (a,b)_v` over all places of `F_q(t)`.
#[pyfunction]
#[pyo3(signature = (p, a, b, degree=1))]
fn try_hilbert_reciprocity_product_ff(
    p: u128,
    a: PyFFRationalFunction,
    b: PyFFRationalFunction,
    degree: usize,
) -> PyResult<Option<i128>> {
    with_finite_odd_field!(p, degree, |F| {
        let a = parse_ff_rational_function::<F>(&a, "a")?;
        let b = parse_ff_rational_function::<F>(&b, "b")?;
        Ok(crate::forms::try_hilbert_reciprocity_product_ff(&a, &b))
    })
}

/// Checked ramified places of the quaternion algebra `(a,b)` over `F_q(t)`.
#[pyfunction]
#[pyo3(signature = (p, a, b, degree=1))]
fn try_ramified_places_ff(
    p: u128,
    a: PyFFRationalFunction,
    b: PyFFRationalFunction,
    degree: usize,
) -> PyResult<Option<Vec<PyFunctionFieldPlace>>> {
    with_finite_odd_field!(p, degree, |F| {
        let a = parse_ff_rational_function::<F>(&a, "a")?;
        let b = parse_ff_rational_function::<F>(&b, "b")?;
        Ok(crate::forms::try_ramified_places_ff(&a, &b).map(|places| {
            places
                .into_iter()
                .map(wrap_ff_place::<F>)
                .collect::<Vec<_>>()
        }))
    })
}

/// Checked local isotropy of a diagonal form over the completion of `F_q(t)` at `place`.
#[pyfunction]
#[pyo3(signature = (p, entries, place=None, degree=1))]
fn try_is_isotropic_at_place_ff(
    p: u128,
    entries: Vec<PyFFRationalFunction>,
    place: Option<PyFFPoly>,
    degree: usize,
) -> PyResult<Option<bool>> {
    with_finite_odd_field!(p, degree, |F| {
        let entries = parse_ff_rational_functions::<F>(&entries)?;
        let place = parse_ff_place::<F>(place)?;
        Ok(crate::forms::try_is_isotropic_at_place_ff(&entries, &place))
    })
}

/// Checked global Hasse-Minkowski isotropy of a diagonal form over `F_q(t)`.
#[pyfunction]
#[pyo3(signature = (p, entries, degree=1))]
fn try_is_isotropic_ff(
    p: u128,
    entries: Vec<PyFFRationalFunction>,
    degree: usize,
) -> PyResult<Option<bool>> {
    with_finite_odd_field!(p, degree, |F| {
        let entries = parse_ff_rational_functions::<F>(&entries)?;
        Ok(crate::forms::try_is_isotropic_ff(&entries))
    })
}

/// Checked per-place Hasse-Minkowski breakdown for a diagonal form over `F_q(t)`.
#[pyfunction]
#[pyo3(signature = (p, entries, degree=1))]
fn try_isotropy_over_ff_adeles(
    p: u128,
    entries: Vec<PyFFRationalFunction>,
    degree: usize,
) -> PyResult<Option<PyFunctionFieldAdelicIsotropy>> {
    with_finite_odd_field!(p, degree, |F| {
        let entries = parse_ff_rational_functions::<F>(&entries)?;
        Ok(crate::forms::try_isotropy_over_ff_adeles(&entries).map(wrap_ff_adeles))
    })
}

#[pyfunction]
#[pyo3(signature = (p, n, a, b, place=None, degree=1))]
fn try_tame_symbol_exponent_ff(
    p: u128,
    n: u128,
    a: PyFFRationalFunction,
    b: PyFFRationalFunction,
    place: Option<PyFFPoly>,
    degree: usize,
) -> PyResult<Option<u128>> {
    with_finite_odd_field!(p, degree, |F| {
        let a = parse_ff_rational_function::<F>(&a, "a")?;
        let b = parse_ff_rational_function::<F>(&b, "b")?;
        let place = parse_ff_place::<F>(place)?;
        Ok(crate::forms::try_tame_symbol_exponent_ff(n, &a, &b, &place))
    })
}

#[pyfunction]
#[pyo3(signature = (p, n, a, b, place=None, degree=1))]
fn try_tame_symbol_invariant_ff(
    p: u128,
    n: u128,
    a: PyFFRationalFunction,
    b: PyFFRationalFunction,
    place: Option<PyFFPoly>,
    degree: usize,
) -> PyResult<Option<PyRational>> {
    with_finite_odd_field!(p, degree, |F| {
        let a = parse_ff_rational_function::<F>(&a, "a")?;
        let b = parse_ff_rational_function::<F>(&b, "b")?;
        let place = parse_ff_place::<F>(place)?;
        Ok(crate::forms::try_tame_symbol_invariant_ff(n, &a, &b, &place).map(wrap_rational))
    })
}

#[pyfunction]
#[pyo3(signature = (p, n, a, b, degree=1))]
fn tame_symbol_invariants_ff(
    p: u128,
    n: u128,
    a: PyFFRationalFunction,
    b: PyFFRationalFunction,
    degree: usize,
) -> PyResult<Option<Vec<(PyFunctionFieldPlace, PyRational)>>> {
    with_finite_odd_field!(p, degree, |F| {
        let a = parse_ff_rational_function::<F>(&a, "a")?;
        let b = parse_ff_rational_function::<F>(&b, "b")?;
        Ok(
            crate::forms::tame_symbol_invariants_ff(n, &a, &b).map(|invs| {
                invs.into_iter()
                    .map(|(place, inv)| (wrap_ff_place::<F>(place), wrap_rational(inv)))
                    .collect()
            }),
        )
    })
}

#[pyfunction]
#[pyo3(signature = (p, n, a, b, degree=1))]
fn tame_symbol_invariant_sum_ff(
    p: u128,
    n: u128,
    a: PyFFRationalFunction,
    b: PyFFRationalFunction,
    degree: usize,
) -> PyResult<Option<PyRational>> {
    with_finite_odd_field!(p, degree, |F| {
        let a = parse_ff_rational_function::<F>(&a, "a")?;
        let b = parse_ff_rational_function::<F>(&b, "b")?;
        Ok(crate::forms::tame_symbol_invariant_sum_ff(n, &a, &b).map(wrap_rational))
    })
}

#[pyfunction]
#[pyo3(signature = (p, n, a, degree=1))]
fn constant_extension_invariants(
    p: u128,
    n: u128,
    a: PyFFRationalFunction,
    degree: usize,
) -> PyResult<Option<Vec<(PyFunctionFieldPlace, PyRational)>>> {
    with_finite_odd_field!(p, degree, |F| {
        let a = parse_ff_rational_function::<F>(&a, "a")?;
        Ok(
            crate::forms::constant_extension_invariants(n, &a).map(|invs| {
                invs.into_iter()
                    .map(|(place, inv)| (wrap_ff_place::<F>(place), wrap_rational(inv)))
                    .collect()
            }),
        )
    })
}

#[pyfunction]
#[pyo3(signature = (p, n, a, degree=1))]
fn constant_extension_invariant_sum(
    p: u128,
    n: u128,
    a: PyFFRationalFunction,
    degree: usize,
) -> PyResult<Option<PyRational>> {
    with_finite_odd_field!(p, degree, |F| {
        let a = parse_ff_rational_function::<F>(&a, "a")?;
        Ok(crate::forms::constant_extension_invariant_sum(n, &a).map(wrap_rational))
    })
}

/// Distinct monic irreducible factors over `F_{2^degree}`. Coefficients are
/// finite-field element indices, low degree first.
#[pyfunction]
#[pyo3(signature = (poly, degree=1))]
fn char2_monic_irreducible_factors(poly: PyFFPoly, degree: usize) -> PyResult<Vec<PyFFPoly>> {
    with_finite_char2_field!(degree, |F| {
        let poly = parse_char2_ff_poly::<F>(&poly, "poly")?;
        Ok(crate::forms::char2_monic_irreducible_factors(&poly)
            .iter()
            .map(char2_ff_poly_indices::<F>)
            .collect())
    })
}

/// Artin-Schreier symbol `s_v(a,b) ∈ {0,1}` over `F_{2^degree}(t)` at `place`.
/// `place=None` means the degree place at infinity.
#[pyfunction]
#[pyo3(signature = (a, b, place=None, degree=1))]
fn as_symbol_at(
    a: PyFFRationalFunction,
    b: PyFFRationalFunction,
    place: Option<PyFFPoly>,
    degree: usize,
) -> PyResult<u128> {
    with_finite_char2_field!(degree, |F| {
        let a = parse_char2_ff_rational_function::<F>(&a, "a")?;
        let b = parse_char2_ff_rational_function::<F>(&b, "b")?;
        ensure_ff_nonzero(&b, "b")?;
        let place = parse_char2_ff_place::<F>(place)?;
        Ok(crate::forms::artin_schreier_symbol_at(&a, &b, &place))
    })
}

/// Places that can carry a nontrivial Artin-Schreier symbol for `[a,b)`.
#[pyfunction]
#[pyo3(signature = (a, b, degree=1))]
fn as_symbol_places(
    a: PyFFRationalFunction,
    b: PyFFRationalFunction,
    degree: usize,
) -> PyResult<Vec<PyFunctionFieldPlace>> {
    with_finite_char2_field!(degree, |F| {
        let a = parse_char2_ff_rational_function::<F>(&a, "a")?;
        let b = parse_char2_ff_rational_function::<F>(&b, "b")?;
        ensure_ff_nonzero(&b, "b")?;
        Ok(crate::forms::artin_schreier_symbol_places(&a, &b)
            .into_iter()
            .map(wrap_char2_ff_place::<F>)
            .collect())
    })
}

/// Weil reciprocity sum `sum_v s_v(a,b) ∈ F_2` over all places of `F_{2^degree}(t)`.
#[pyfunction]
#[pyo3(signature = (a, b, degree=1))]
fn as_symbol_reciprocity_sum(
    a: PyFFRationalFunction,
    b: PyFFRationalFunction,
    degree: usize,
) -> PyResult<u128> {
    with_finite_char2_field!(degree, |F| {
        let a = parse_char2_ff_rational_function::<F>(&a, "a")?;
        let b = parse_char2_ff_rational_function::<F>(&b, "b")?;
        ensure_ff_nonzero(&b, "b")?;
        Ok(crate::forms::artin_schreier_reciprocity_sum(&a, &b))
    })
}

/// Places where the characteristic-2 cyclic algebra `[a,b)` ramifies.
#[pyfunction]
#[pyo3(signature = (a, b, degree=1))]
fn as_symbol_ramified_places(
    a: PyFFRationalFunction,
    b: PyFFRationalFunction,
    degree: usize,
) -> PyResult<Vec<PyFunctionFieldPlace>> {
    with_finite_char2_field!(degree, |F| {
        let a = parse_char2_ff_rational_function::<F>(&a, "a")?;
        let b = parse_char2_ff_rational_function::<F>(&b, "b")?;
        ensure_ff_nonzero(&b, "b")?;
        Ok(crate::forms::artin_schreier_ramified_places(&a, &b)
            .into_iter()
            .map(wrap_char2_ff_place::<F>)
            .collect())
    })
}

/// Whether `f ∈ F_{2^degree}(t)` is globally Artin-Schreier trivial (`f = x²+x`).
#[pyfunction]
#[pyo3(signature = (f, degree=1))]
fn global_is_pe(f: PyFFRationalFunction, degree: usize) -> PyResult<bool> {
    with_finite_char2_field!(degree, |F| {
        let f = parse_char2_ff_rational_function::<F>(&f, "f")?;
        Ok(crate::forms::global_is_pe(&f))
    })
}

/// Relevant places for a characteristic-2 quadratic form over `F_{2^degree}(t)`.
#[pyfunction]
fn relevant_places_char2(form: &PyChar2FunctionFieldForm) -> PyResult<Vec<PyFunctionFieldPlace>> {
    form.relevant_places()
}

/// Aravire-Jacob local decomposition of a characteristic-2 form at `place`.
#[pyfunction]
#[pyo3(signature = (form, place=None))]
fn springer_decompose_local_char2(
    form: &PyChar2FunctionFieldForm,
    place: Option<PyFFPoly>,
) -> PyResult<PyChar2LocalDecomp> {
    form.decompose_at(place)
}

/// Local anisotropic dimension of a characteristic-2 form at `place`.
#[pyfunction]
#[pyo3(signature = (form, place=None))]
fn local_anisotropic_dim_char2(
    form: &PyChar2FunctionFieldForm,
    place: Option<PyFFPoly>,
) -> PyResult<Option<usize>> {
    form.local_anisotropic_dim(place)
}

/// Local isotropy of a characteristic-2 form at `place`.
#[pyfunction]
#[pyo3(signature = (form, place=None))]
fn local_is_isotropic_char2(
    form: &PyChar2FunctionFieldForm,
    place: Option<PyFFPoly>,
) -> PyResult<Option<bool>> {
    form.is_isotropic_at_place(place)
}

/// Global Hasse-Minkowski isotropy over `F_{2^degree}(t)`.
#[pyfunction]
fn is_isotropic_global_char2(form: &PyChar2FunctionFieldForm) -> PyResult<Option<bool>> {
    form.is_isotropic()
}

fn char2_witt_from_arf(arf: crate::forms::ArfInvariants, field_degree: u128) -> Option<WittClassG> {
    (arf.radical_dim == 0).then_some(WittClassG::Char2 {
        field_degree,
        arf: arf.arf,
    })
}

fn char2_bw_from_arf(
    arf: crate::forms::ArfInvariants,
    field_degree: u128,
) -> Option<crate::forms::BrauerWallClass> {
    (arf.radical_dim == 0).then_some(crate::forms::BrauerWallClass::Char2 {
        field_degree,
        arf: arf.arf,
    })
}

macro_rules! classify_odd_finite_alg {
    ($py:ident, $alg:ident, $ty:ty) => {
        if let Ok(a) = $alg.cast::<$ty>() {
            let a = a.borrow();
            if let Some(inner) = crate::forms::classify_finite_odd(&a.inner.metric) {
                return PyOddCharInvariants { inner }.into_py_any($py);
            }
            return Err(PyValueError::new_err(
                "finite odd-characteristic classification needs a diagonalizable metric",
            ));
        }
    };
}

macro_rules! classify_char2_finite_alg {
    ($py:ident, $alg:ident, $ty:ty, $field_degree:expr) => {
        if let Ok(a) = $alg.cast::<$ty>() {
            let a = a.borrow();
            if let Some(inner) = crate::forms::arf_char2(&a.inner.metric) {
                return PyArfInvariants { inner }.into_py_any($py);
            }
            return Err(PyValueError::new_err(
                "finite characteristic-2 classification needs a non-general-bilinear metric",
            ));
        }
    };
}

macro_rules! classify_odd_finite_alg_class {
    ($alg:ident, $ty:ty) => {
        if let Ok(a) = $alg.cast::<$ty>() {
            let a = a.borrow();
            return crate::forms::classify_finite_odd(&a.inner.metric)
                .map(|inner| PyFiniteFieldInvariants {
                    inner: crate::forms::FiniteFieldInvariants::Odd(inner),
                })
                .ok_or_else(|| {
                    PyValueError::new_err(
                        "finite odd-characteristic classification needs a diagonalizable metric",
                    )
                });
        }
    };
}

macro_rules! classify_char2_finite_alg_class {
    ($alg:ident, $ty:ty, $field_degree:expr) => {
        if let Ok(a) = $alg.cast::<$ty>() {
            let a = a.borrow();
            return crate::forms::arf_char2(&a.inner.metric)
                .map(|inner| PyFiniteFieldInvariants {
                    inner: crate::forms::FiniteFieldInvariants::Char2(inner),
                })
                .ok_or_else(|| {
                    PyValueError::new_err(
                        "finite characteristic-2 classification needs a non-general-bilinear metric",
                    )
                });
        }
    };
}

macro_rules! witt_odd_finite_alg {
    ($alg:ident, $ty:ty) => {
        if let Ok(a) = $alg.cast::<$ty>() {
            let a = a.borrow();
            return crate::forms::finite_odd_witt(&a.inner.metric)
                .map(|inner| PyWittClassG { inner })
                .ok_or_else(|| {
                    PyValueError::new_err(
                        "finite odd-characteristic Witt class needs a diagonalizable metric",
                    )
                });
        }
    };
}

macro_rules! witt_char2_finite_alg {
    ($alg:ident, $ty:ty, $field_degree:expr) => {
        if let Ok(a) = $alg.cast::<$ty>() {
            let a = a.borrow();
            return crate::forms::arf_char2(&a.inner.metric)
                .and_then(|arf| char2_witt_from_arf(arf, $field_degree))
                .map(|inner| PyWittClassG { inner })
                .ok_or_else(|| {
                    PyValueError::new_err(
                        "finite characteristic-2 Witt class needs a nonsingular metric",
                    )
                });
        }
    };
}

macro_rules! witt_decompose_odd_finite_alg {
    ($py:ident, $alg:ident, $ty:ty) => {
        if let Ok(a) = $alg.cast::<$ty>() {
            let a = a.borrow();
            let inner = crate::forms::witt_decompose_finite_odd(&a.inner.metric).ok_or_else(|| {
                PyValueError::new_err(
                    "finite odd-characteristic Witt decomposition needs a diagonalizable metric",
                )
            })?;
            return wrap_odd_witt_decomp(inner).into_py_any($py);
        }
    };
}

macro_rules! witt_decompose_char2_finite_alg {
    ($py:ident, $alg:ident, $ty:ty, $field_degree:expr) => {
        if let Ok(a) = $alg.cast::<$ty>() {
            let a = a.borrow();
            let arf = crate::forms::arf_char2(&a.inner.metric).ok_or_else(|| {
                PyValueError::new_err(
                    "finite characteristic-2 Witt decomposition needs a non-general-bilinear metric",
                )
            })?;
            let inner = crate::forms::Char2WittDecomp::from_arf($field_degree, &arf);
            return PyChar2WittDecomp { inner }.into_py_any($py);
        }
    };
}

macro_rules! bw_odd_finite_alg {
    ($alg:ident, $ty:ty) => {
        if let Ok(a) = $alg.cast::<$ty>() {
            let a = a.borrow();
            return crate::forms::bw_class_finite_odd(&a.inner.metric)
                .map(|inner| PyBrauerWallClass { inner })
                .ok_or_else(|| {
                    PyValueError::new_err(
                        "finite odd-characteristic Brauer-Wall class needs a diagonalizable metric",
                    )
                });
        }
    };
}

macro_rules! bw_char2_finite_alg {
    ($alg:ident, $ty:ty, $field_degree:expr) => {
        if let Ok(a) = $alg.cast::<$ty>() {
            let a = a.borrow();
            return crate::forms::arf_char2(&a.inner.metric)
                .and_then(|arf| char2_bw_from_arf(arf, $field_degree))
                .map(|inner| PyBrauerWallClass { inner })
                .ok_or_else(|| {
                    PyValueError::new_err(
                        "finite characteristic-2 Brauer-Wall class needs a nonsingular metric",
                    )
                });
        }
    };
}

macro_rules! isometric_odd_finite_alg {
    ($a:ident, $b:ident, $ty:ty) => {
        if let (Ok(a), Ok(b)) = ($a.cast::<$ty>(), $b.cast::<$ty>()) {
            let (a, b) = (a.borrow(), b.borrow());
            return crate::forms::isometric_finite_odd(&a.inner.metric, &b.inner.metric)
                .ok_or_else(|| {
                    PyValueError::new_err(
                        "finite odd-characteristic isometry needs diagonalizable metrics",
                    )
                });
        }
    };
}

macro_rules! isometric_char2_finite_alg {
    ($a:ident, $b:ident, $ty:ty, $field_degree:expr) => {
        if let (Ok(a), Ok(b)) = ($a.cast::<$ty>(), $b.cast::<$ty>()) {
            let (a, b) = (a.borrow(), b.borrow());
            return crate::forms::isometric_finite_char2(&a.inner.metric, &b.inner.metric)
                .ok_or_else(|| {
                    PyValueError::new_err(
                        "finite characteristic-2 isometry needs non-general-bilinear metrics",
                    )
                });
        }
    };
}

macro_rules! finite_algebra_cases {
    ($char2:ident, $odd:ident, $($args:tt)*) => {
        $char2!($($args)* Fp2Algebra, 1u128);
        $odd!($($args)* Fp3Algebra);
        $odd!($($args)* Fp5Algebra);
        $odd!($($args)* Fp7Algebra);
        $odd!($($args)* Fp11Algebra);
        $odd!($($args)* Fp13Algebra);
        $char2!($($args)* F4Algebra, 2u128);
        $char2!($($args)* F8Algebra, 3u128);
        $char2!($($args)* F16Algebra, 4u128);
        $odd!($($args)* F9Algebra);
        $odd!($($args)* F25Algebra);
        $odd!($($args)* F27Algebra);
    };
}

#[pyfunction]
fn classify_finite_algebra(py: Python<'_>, alg: Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
    finite_algebra_cases!(classify_char2_finite_alg, classify_odd_finite_alg, py, alg,);
    Err(PyTypeError::new_err(
        "expected one of the fixed finite-field Algebra classes",
    ))
}

#[pyfunction]
fn classify_finite_algebra_unified(alg: Bound<'_, PyAny>) -> PyResult<PyFiniteFieldInvariants> {
    finite_algebra_cases!(
        classify_char2_finite_alg_class,
        classify_odd_finite_alg_class,
        alg,
    );
    Err(PyTypeError::new_err(
        "expected one of the fixed finite-field Algebra classes",
    ))
}

#[pyfunction]
fn witt_finite_algebra(alg: Bound<'_, PyAny>) -> PyResult<PyWittClassG> {
    finite_algebra_cases!(witt_char2_finite_alg, witt_odd_finite_alg, alg,);
    Err(PyTypeError::new_err(
        "expected one of the fixed finite-field Algebra classes",
    ))
}

/// Constructive Witt decomposition for every fixed finite-field algebra.
/// Odd-characteristic inputs return `OddWittDecomp`; characteristic-two inputs
/// return `Char2WittDecomp` with the defective-form caveat preserved.
#[pyfunction]
fn witt_decompose_finite_algebra(py: Python<'_>, alg: Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
    finite_algebra_cases!(
        witt_decompose_char2_finite_alg,
        witt_decompose_odd_finite_alg,
        py,
        alg,
    );
    Err(PyTypeError::new_err(
        "expected one of the fixed finite-field Algebra classes",
    ))
}

#[pyfunction]
fn bw_class_finite_algebra(alg: Bound<'_, PyAny>) -> PyResult<PyBrauerWallClass> {
    finite_algebra_cases!(bw_char2_finite_alg, bw_odd_finite_alg, alg,);
    Err(PyTypeError::new_err(
        "expected one of the fixed finite-field Algebra classes",
    ))
}

#[pyfunction]
fn isometric_finite_algebra(a: Bound<'_, PyAny>, b: Bound<'_, PyAny>) -> PyResult<bool> {
    finite_algebra_cases!(isometric_char2_finite_alg, isometric_odd_finite_alg, a, b,);
    Err(PyTypeError::new_err(
        "expected two fixed finite-field Algebra classes over the same field",
    ))
}

#[pyclass(name = "WittClassG", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyWittClassG {
    inner: WittClassG,
}

fn check_bit(name: &str, value: u128) -> PyResult<()> {
    if value <= 1 {
        Ok(())
    } else {
        Err(PyValueError::new_err(format!("{name} must be 0 or 1")))
    }
}

fn check_positive_field_degree(field_degree: u128) -> PyResult<()> {
    if field_degree == 0 {
        Err(PyValueError::new_err(
            "char-2 field_degree must be positive",
        ))
    } else {
        Ok(())
    }
}

#[pymethods]
impl PyWittClassG {
    #[staticmethod]
    fn char0(p: usize, q: usize) -> PyWittClassG {
        PyWittClassG {
            inner: WittClassG::char0(p, q),
        }
    }
    #[staticmethod]
    fn char0_signature(signature: i128) -> PyWittClassG {
        PyWittClassG {
            inner: WittClassG::Char0 { signature },
        }
    }
    #[staticmethod]
    fn oddchar_zero(field_order: u128, kappa: u128) -> PyResult<PyWittClassG> {
        check_bit("kappa", kappa)?;
        Ok(PyWittClassG {
            inner: WittClassG::oddchar_zero(field_order, kappa),
        })
    }
    #[staticmethod]
    fn oddchar_one(field_order: u128, kappa: u128) -> PyResult<PyWittClassG> {
        check_bit("kappa", kappa)?;
        Ok(PyWittClassG {
            inner: WittClassG::oddchar_one(field_order, kappa),
        })
    }
    #[staticmethod]
    fn oddchar(field_order: u128, kappa: u128, e0: u128, sclass: u128) -> PyResult<PyWittClassG> {
        check_bit("kappa", kappa)?;
        check_bit("e0", e0)?;
        check_bit("sclass", sclass)?;
        Ok(PyWittClassG {
            inner: WittClassG::OddChar {
                field_order,
                kappa,
                e0,
                sclass,
            },
        })
    }
    #[staticmethod]
    #[pyo3(signature = (arf, field_degree=1))]
    fn char2(arf: u128, field_degree: u128) -> PyResult<PyWittClassG> {
        check_bit("arf", arf)?;
        check_positive_field_degree(field_degree)?;
        Ok(PyWittClassG {
            inner: WittClassG::Char2 { field_degree, arf },
        })
    }
    #[staticmethod]
    fn try_char2_from_metric(alg: &NimberAlgebra) -> PyResult<PyWittClassG> {
        WittClassG::try_char2_from_metric(&alg.inner.metric)
            .map(|inner| PyWittClassG { inner })
            .map_err(|err| {
                PyValueError::new_err(format!("char-2 Witt class is undefined: {err:?}"))
            })
    }
    #[staticmethod]
    fn try_char2_from_metric_error(alg: &NimberAlgebra) -> Option<PyWittClassError> {
        WittClassG::try_char2_from_metric(&alg.inner.metric)
            .err()
            .map(wrap_witt_class_error)
    }
    fn kind(&self) -> &'static str {
        match self.inner {
            WittClassG::Char0 { .. } => "char0",
            WittClassG::OddChar { .. } => "oddchar",
            WittClassG::Char2 { .. } => "char2",
        }
    }
    fn signature(&self) -> Option<i128> {
        match self.inner {
            WittClassG::Char0 { signature } => Some(signature),
            _ => None,
        }
    }
    fn field_order(&self) -> Option<u128> {
        match self.inner {
            WittClassG::OddChar { field_order, .. } => Some(field_order),
            _ => None,
        }
    }
    fn field_degree(&self) -> Option<u128> {
        match self.inner {
            WittClassG::Char2 { field_degree, .. } => Some(field_degree),
            _ => None,
        }
    }
    fn kappa(&self) -> Option<u128> {
        match self.inner {
            WittClassG::OddChar { kappa, .. } => Some(kappa),
            _ => None,
        }
    }
    fn e0(&self) -> Option<u128> {
        match self.inner {
            WittClassG::OddChar { e0, .. } => Some(e0),
            _ => None,
        }
    }
    fn sclass(&self) -> Option<u128> {
        match self.inner {
            WittClassG::OddChar { sclass, .. } => Some(sclass),
            _ => None,
        }
    }
    fn arf(&self) -> Option<u128> {
        match self.inner {
            WittClassG::Char2 { arf, .. } => Some(arf),
            _ => None,
        }
    }
    fn __add__(&self, other: &PyWittClassG) -> PyResult<PyWittClassG> {
        self.inner
            .try_add(&other.inner)
            .map(|inner| PyWittClassG { inner })
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }
    /// The Witt-ring product (tensor of forms). Defined on the characteristic-zero
    /// and odd-characteristic legs; raises `ValueError` for characteristic two,
    /// where `W_q` is a module rather than a ring.
    fn __mul__(&self, other: &PyWittClassG) -> PyResult<PyWittClassG> {
        self.inner
            .try_mul(&other.inner)
            .map(|inner| PyWittClassG { inner })
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }
    fn __eq__(&self, other: &PyWittClassG) -> bool {
        self.inner == other.inner
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        format!("WittClassG::{}", self.inner.display())
    }
}

#[pyclass(name = "RealWittDecomp", module = "ogdoad")]
struct PyRealWittDecomp {
    inner: crate::forms::RealWittDecomp,
}

#[pyclass(name = "Char2WittDecomp", module = "ogdoad")]
struct PyChar2WittDecomp {
    inner: crate::forms::Char2WittDecomp,
}

#[pymethods]
impl PyChar2WittDecomp {
    #[getter]
    fn field_degree(&self) -> u128 {
        self.inner.field_degree
    }
    #[getter]
    fn witt_index(&self) -> usize {
        self.inner.witt_index
    }
    #[getter]
    fn core_anisotropic_dim(&self) -> usize {
        self.inner.core_anisotropic_dim
    }
    #[getter]
    fn radical_dim(&self) -> usize {
        self.inner.radical_dim
    }
    #[getter]
    fn radical_anisotropic(&self) -> bool {
        self.inner.radical_anisotropic
    }
    #[getter]
    fn arf(&self) -> u128 {
        self.inner.arf
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pymethods]
impl PyRealWittDecomp {
    #[getter]
    fn witt_index(&self) -> usize {
        self.inner.witt_index
    }
    #[getter]
    fn anisotropic_pos(&self) -> usize {
        self.inner.anisotropic_pos
    }
    #[getter]
    fn anisotropic_neg(&self) -> usize {
        self.inner.anisotropic_neg
    }
    #[getter]
    fn radical_dim(&self) -> usize {
        self.inner.radical_dim
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

fn wrap_real_witt_decomp(inner: crate::forms::RealWittDecomp) -> PyRealWittDecomp {
    PyRealWittDecomp { inner }
}

#[pyclass(name = "OddWittDecomp", module = "ogdoad")]
struct PyOddWittDecomp {
    inner: crate::forms::OddWittDecomp,
}

#[pymethods]
impl PyOddWittDecomp {
    #[getter]
    fn p(&self) -> u128 {
        self.inner.p
    }
    #[getter]
    fn field_order(&self) -> u128 {
        self.inner.field_order
    }
    #[getter]
    fn witt_index(&self) -> usize {
        self.inner.witt_index
    }
    #[getter]
    fn anisotropic_dim(&self) -> usize {
        self.inner.anisotropic_dim
    }
    #[getter]
    fn anisotropic_disc_is_square(&self) -> bool {
        self.inner.anisotropic_disc_is_square
    }
    #[getter]
    fn radical_dim(&self) -> usize {
        self.inner.radical_dim
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

fn wrap_odd_witt_decomp(inner: crate::forms::OddWittDecomp) -> PyOddWittDecomp {
    PyOddWittDecomp { inner }
}

#[pyclass(name = "EnStaircase", module = "ogdoad")]
struct PyEnStaircase {
    inner: crate::forms::EnStaircase,
}

#[pymethods]
impl PyEnStaircase {
    #[getter]
    fn e0(&self) -> u128 {
        self.inner.e0
    }
    #[getter]
    fn e1(&self) -> u128 {
        self.inner.e1
    }
    #[getter]
    fn e2(&self) -> i128 {
        self.inner.e2
    }
    #[getter]
    fn stabilizes_at(&self) -> usize {
        self.inner.stabilizes_at
    }
    fn __repr__(&self) -> String {
        format!(
            "EnStaircase(e0={}, e1={}, e2={}, stabilizes_at={})",
            self.inner.e0, self.inner.e1, self.inner.e2, self.inner.stabilizes_at
        )
    }
}

fn wrap_en_staircase(inner: crate::forms::EnStaircase) -> PyEnStaircase {
    PyEnStaircase { inner }
}

/// Artin-Schreier class `Tr_{F_{2^degree}/F_2}(x)` for supported char-2 finite
/// fields (`degree=1..4`), with `x` encoded as a finite-field element index.
#[pyfunction]
#[pyo3(signature = (x, degree=1))]
fn artin_schreier_class_finite(x: u128, degree: usize) -> PyResult<u128> {
    let order = char2_finite_field_order(degree)?;
    if x >= order {
        return Err(PyValueError::new_err(format!(
            "field element index {x} is outside F_{order}"
        )));
    }
    with_finite_char2_field!(degree, |F| {
        Ok(crate::forms::artin_schreier_class_finite(
            <F as FiniteChar2Field>::from_index(x),
        ))
    })
}

fn unsupported_prime_field_err() -> PyErr {
    PyValueError::new_err("supported prime fields: F_2, F_3, F_5, F_7, F_11, F_13")
}

fn unsupported_odd_prime_field_err() -> PyErr {
    PyValueError::new_err("supported odd prime fields: F_3, F_5, F_7, F_11, F_13")
}

fn numeric_invariants_for_field<F: crate::forms::FiniteFieldInvariantField>(
) -> PyResult<crate::forms::FiniteFieldNumericInvariants> {
    crate::forms::finite_field_numeric_invariants::<F>()
        .ok_or_else(|| PyValueError::new_err("unsupported finite-field parameters"))
}

fn sum_of_squares_for_prime<const P: u128>(x: i128, n: usize) -> PyResult<bool> {
    Ok(crate::forms::is_sum_of_n_squares::<P>(
        Fp::<P>::from_int(x),
        n,
    ))
}

fn hilbert_symbol_prime<const P: u128>(a: i128, b: i128) -> PyResult<i128> {
    Ok(crate::forms::hilbert_symbol::<P>(
        Fp::<P>::from_int(a),
        Fp::<P>::from_int(b),
    ))
}

/// Numeric finite-field invariants for `F_{p^degree}`.
#[pyfunction]
#[pyo3(signature = (p, degree=1))]
fn finite_field_numeric_invariants(
    p: u128,
    degree: usize,
) -> PyResult<PyFiniteFieldNumericInvariants> {
    with_supported_finite_field!(p, degree, |F| {
        Ok(PyFiniteFieldNumericInvariants {
            inner: numeric_invariants_for_field::<F>()?,
        })
    })
}

/// The level/Stufe of `F_{p^degree}`: the least `n` for which `-1` is a sum of
/// `n` squares.
#[pyfunction]
#[pyo3(signature = (p, degree=1))]
fn level(p: u128, degree: usize) -> PyResult<usize> {
    with_supported_finite_field!(p, degree, |F| {
        Ok(numeric_invariants_for_field::<F>()?.level)
    })
}

/// The Pythagoras number of `F_{p^degree}`.
#[pyfunction]
#[pyo3(signature = (p, degree=1))]
fn pythagoras_number(p: u128, degree: usize) -> PyResult<usize> {
    with_supported_finite_field!(p, degree, |F| {
        Ok(numeric_invariants_for_field::<F>()?.pythagoras_number)
    })
}

/// The quadratic u-invariant of `F_{p^degree}`. Characteristic two uses regular
/// quadratic forms.
#[pyfunction]
#[pyo3(signature = (p, degree=1))]
fn u_invariant(p: u128, degree: usize) -> PyResult<usize> {
    with_supported_finite_field!(p, degree, |F| {
        Ok(numeric_invariants_for_field::<F>()?.u_invariant)
    })
}

/// Is `x` a sum of exactly `n` squares in the prime field `F_p`?
#[pyfunction]
fn is_sum_of_n_squares(p: u128, x: i128, n: usize) -> PyResult<bool> {
    match p {
        2 => sum_of_squares_for_prime::<2>(x, n),
        3 => sum_of_squares_for_prime::<3>(x, n),
        5 => sum_of_squares_for_prime::<5>(x, n),
        7 => sum_of_squares_for_prime::<7>(x, n),
        11 => sum_of_squares_for_prime::<11>(x, n),
        13 => sum_of_squares_for_prime::<13>(x, n),
        _ => Err(unsupported_prime_field_err()),
    }
}

/// The Rust finite-prime-field Hilbert symbol `(a,b)` over `F_p`; supported odd
/// primes: 3, 5, 7, 11, 13.
#[pyfunction]
fn hilbert_symbol(p: u128, a: i128, b: i128) -> PyResult<i128> {
    match p {
        3 => hilbert_symbol_prime::<3>(a, b),
        5 => hilbert_symbol_prime::<5>(a, b),
        7 => hilbert_symbol_prime::<7>(a, b),
        11 => hilbert_symbol_prime::<11>(a, b),
        13 => hilbert_symbol_prime::<13>(a, b),
        _ => Err(unsupported_odd_prime_field_err()),
    }
}

/// Are two ordinal-nimber metrics isometric on the detected finite ordinal windows?
#[pyfunction]
fn isometric_ordinal_finite(a: &OrdinalAlgebra, b: &OrdinalAlgebra) -> PyResult<bool> {
    <Ordinal as crate::forms::ClassifyIsometry>::isometric(&a.inner.metric, &b.inner.metric)
        .map_err(|e| PyValueError::new_err(e.to_string()))
}

/// The unified Witt class of a nonsingular ordinal-nimber metric on the detected
/// finite ordinal windows.
#[pyfunction]
fn ordinal_witt(alg: &OrdinalAlgebra) -> PyResult<PyWittClassG> {
    <Ordinal as crate::forms::ClassifyWitt>::witt_class(&alg.inner.metric)
        .map(|inner| PyWittClassG { inner })
        .map_err(|e| PyValueError::new_err(e.to_string()))
}

/// Witt decomposition of a surreal form on the exact-square real-table subdomain.
#[pyfunction]
fn witt_decompose_real(alg: &SurrealAlgebra) -> PyResult<PyRealWittDecomp> {
    let d = crate::forms::witt_decompose_real(&alg.inner.metric).ok_or_else(|| {
        PyValueError::new_err("metric is outside the exact-square real-table subdomain")
    })?;
    Ok(wrap_real_witt_decomp(d))
}

// ---------------------------------------------------------------------------
// Non-Archimedean Springer decomposition (surreal)
// ---------------------------------------------------------------------------

#[pyclass(name = "ResidueForm", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyResidueForm {
    valuation: PySurreal,
    valuation_repr: String,
    signature: (usize, usize),
}

#[pymethods]
impl PyResidueForm {
    #[getter]
    fn valuation(&self) -> PySurreal {
        self.valuation.clone()
    }
    #[getter]
    fn signature(&self) -> (usize, usize) {
        self.signature
    }
    fn __repr__(&self) -> String {
        format!(
            "ResidueForm(valuation={}, signature={:?})",
            self.valuation_repr, self.signature
        )
    }
}

fn wrap_residue_form(rf: crate::forms::ResidueForm) -> PyResidueForm {
    let valuation_repr = format!("{:?}", rf.valuation);
    PyResidueForm {
        valuation: wrap_surreal(rf.valuation),
        valuation_repr,
        signature: rf.signature,
    }
}

#[pyclass(name = "SpringerDecomp", module = "ogdoad")]
struct PySpringerDecomp {
    #[pyo3(get)]
    graded: Vec<PyResidueForm>,
    #[pyo3(get)]
    radical_dim: usize,
    #[pyo3(get)]
    total_signature: (usize, usize),
    // Rendered from the core `SpringerDecomp` at construction time, since this
    // struct is a per-field erasure of the generic core value (no `inner` to
    // delegate to directly).
    rendered: String,
}

#[pymethods]
impl PySpringerDecomp {
    fn display_layers(&self) -> Vec<(String, (usize, usize))> {
        self.graded
            .iter()
            .map(|g| (g.valuation_repr.clone(), g.signature))
            .collect()
    }
    fn display(&self) -> String {
        self.rendered.clone()
    }
    fn __repr__(&self) -> String {
        self.rendered.clone()
    }
}

#[pyclass(name = "LocalResidueForm", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyLocalResidueForm {
    valuation: i128,
    dim: usize,
    disc_is_square: bool,
}

#[pymethods]
impl PyLocalResidueForm {
    #[getter]
    fn valuation(&self) -> i128 {
        self.valuation
    }
    #[getter]
    fn dim(&self) -> usize {
        self.dim
    }
    #[getter]
    fn disc_is_square(&self) -> bool {
        self.disc_is_square
    }
    fn __repr__(&self) -> String {
        format!(
            "LocalResidueForm(valuation={}, dim={}, disc_is_square={})",
            self.valuation, self.dim, self.disc_is_square
        )
    }
}

fn wrap_local_residue_form(g: crate::forms::LocalResidueForm) -> PyLocalResidueForm {
    PyLocalResidueForm {
        valuation: g.valuation,
        dim: g.dim,
        disc_is_square: g.disc_is_square,
    }
}

#[pyclass(name = "LocalSpringerDecomp", module = "ogdoad")]
struct PyLocalSpringerDecomp {
    #[pyo3(get)]
    graded: Vec<PyLocalResidueForm>,
    #[pyo3(get)]
    radical_dim: usize,
    // Rendered from the core `LocalSpringerDecomp` at construction time, since
    // this struct is a per-field erasure of the generic core value.
    rendered: String,
}

#[pymethods]
impl PyLocalSpringerDecomp {
    /// The residue layers whose valuation has parity `0` or `1`.
    fn parity_layer(&self, parity: u128) -> Vec<PyLocalResidueForm> {
        self.graded
            .iter()
            .filter(|g| g.valuation.rem_euclid(2) as u128 == parity)
            .cloned()
            .collect()
    }

    fn display(&self) -> String {
        self.rendered.clone()
    }
    fn __repr__(&self) -> String {
        self.rendered.clone()
    }
}

fn wrap_local_springer_decomp(d: crate::forms::LocalSpringerDecomp) -> PyLocalSpringerDecomp {
    let rendered = d.to_string();
    PyLocalSpringerDecomp {
        graded: d.graded.into_iter().map(wrap_local_residue_form).collect(),
        radical_dim: d.radical_dim,
        rendered,
    }
}

/// The non-Archimedean Springer decomposition of a surreal form: diagonalizes
/// first, then reads the ω-adic valuation filtration into residue ℝ-signatures.
#[pyfunction]
fn springer_decompose(alg: &SurrealAlgebra) -> PyResult<PySpringerDecomp> {
    let d = crate::forms::springer_decompose(&alg.inner.metric).ok_or_else(|| {
        PyValueError::new_err("Springer decomposition could not diagonalize this metric")
    })?;
    let rendered = d.to_string();
    Ok(PySpringerDecomp {
        graded: d.graded.into_iter().map(wrap_residue_form).collect(),
        radical_dim: d.radical_dim,
        total_signature: d.total_signature,
        rendered,
    })
}

fn springer_local_metric<K>(metric: &Metric<K>) -> PyResult<PyLocalSpringerDecomp>
where
    K: ResidueField,
    K::Residue: FiniteOddField,
{
    let decomp = crate::forms::springer_decompose_local(metric).ok_or_else(|| {
        PyValueError::new_err(
            "Springer local decomposition needs odd supported residue field and a diagonal metric",
        )
    })?;
    Ok(wrap_local_springer_decomp(decomp))
}

/// Rust-name generic Springer dispatcher over the fixed Python local algebra set.
#[pyfunction]
fn springer_decompose_local(alg: Bound<'_, PyAny>) -> PyResult<PyLocalSpringerDecomp> {
    macro_rules! try_local {
        ($ty:ty) => {
            if let Ok(a) = alg.cast::<$ty>() {
                let a = a.borrow();
                return springer_local_metric(&a.inner.metric);
            }
        };
    }

    try_local!(Qp2_4Algebra);
    try_local!(Qp3_4Algebra);
    try_local!(Qp5_4Algebra);
    try_local!(Qp7_4Algebra);
    try_local!(Qp11_4Algebra);
    try_local!(Qp13_4Algebra);

    try_local!(Qq2_4_2Algebra);
    try_local!(Qq2_4_3Algebra);
    try_local!(Qq2_4_4Algebra);
    try_local!(Qq3_4_2Algebra);
    try_local!(Qq5_4_2Algebra);
    try_local!(Qq3_4_3Algebra);

    try_local!(LaurentFp3_6Algebra);
    try_local!(LaurentFp5_6Algebra);
    try_local!(LaurentFp7_6Algebra);
    try_local!(LaurentFp11_6Algebra);
    try_local!(LaurentFp13_6Algebra);
    try_local!(LaurentF9_6Algebra);
    try_local!(LaurentF25_6Algebra);
    try_local!(LaurentF27_6Algebra);

    try_local!(RamifiedQp2_4E2Algebra);
    try_local!(RamifiedQp3_4E2Algebra);
    try_local!(RamifiedQp5_4E2Algebra);
    try_local!(RamifiedQp7_4E2Algebra);
    try_local!(RamifiedQp11_4E2Algebra);
    try_local!(RamifiedQp13_4E2Algebra);
    try_local!(RamifiedQp2_4E3Algebra);
    try_local!(RamifiedQp3_4E3Algebra);
    try_local!(RamifiedQp5_4E3Algebra);
    try_local!(RamifiedQp7_4E3Algebra);
    try_local!(RamifiedQp11_4E3Algebra);
    try_local!(RamifiedQp13_4E3Algebra);

    Err(PyTypeError::new_err(
        "springer_decompose_local expects a fixed Qp/Qq/Laurent/Ramified local algebra",
    ))
}

fn qp4_metric<const P: u128>(entries: Vec<(i128, i128)>) -> PyResult<Metric<Qp<P, 4>>> {
    let mut q = Vec::with_capacity(entries.len());
    for (idx, entry) in entries.into_iter().enumerate() {
        let rational = parse_q_pair(entry, &format!("entry {idx}"))?;
        q.push(Qp::<P, 4>::from_rational(&rational));
    }
    Ok(Metric::diagonal(q))
}

/// Springer decomposition over the fixed Python p-adic slice `Q_p` at precision
/// `4`. Entries are diagonal rational coefficients as `(num, den)` pairs.
/// Supported primes match the fixed p-adic scalar classes: 2, 3, 5, 7, 11, 13.
/// The theorem layer itself rejects residue characteristic 2.
#[pyfunction]
fn springer_decompose_qp(p: u128, entries: Vec<(i128, i128)>) -> PyResult<PyLocalSpringerDecomp> {
    let decomp = match p {
        2 => crate::forms::springer_decompose_qp(&qp4_metric::<2>(entries)?),
        3 => crate::forms::springer_decompose_qp(&qp4_metric::<3>(entries)?),
        5 => crate::forms::springer_decompose_qp(&qp4_metric::<5>(entries)?),
        7 => crate::forms::springer_decompose_qp(&qp4_metric::<7>(entries)?),
        11 => crate::forms::springer_decompose_qp(&qp4_metric::<11>(entries)?),
        13 => crate::forms::springer_decompose_qp(&qp4_metric::<13>(entries)?),
        _ => {
            return Err(PyValueError::new_err(
                "supported fixed Qp4 primes are 2, 3, 5, 7, 11, and 13",
            ));
        }
    }
    .ok_or_else(|| {
        PyValueError::new_err(
            "Springer decomposition needs odd residue characteristic and a diagonal metric",
        )
    })?;
    Ok(wrap_local_springer_decomp(decomp))
}

fn ramified_qp4_e_metric<const P: u128, const E: usize>(
    entries: Vec<Vec<i128>>,
) -> PyResult<Metric<Ramified<Qp<P, 4>, E>>> {
    let mut q = Vec::with_capacity(entries.len());
    for (idx, components) in entries.into_iter().enumerate() {
        if components.len() > E {
            return Err(PyValueError::new_err(format!(
                "entry {idx} has {} components; RamifiedQp{P}_4_E{E} expects at most {E}",
                components.len(),
            )));
        }
        q.push(Ramified::<Qp<P, 4>, E>::new(
            components.into_iter().map(Qp::<P, 4>::from_int).collect(),
        ));
    }
    Ok(Metric::diagonal(q))
}

/// Springer decomposition over the fixed ramified quadratic p-adic slice
/// `Q_p(pi)` with `pi^2 = p`, base precision `4`, and
/// `p ∈ {3, 5, 7, 11, 13}`. Entries are diagonal coefficients encoded as
/// component lists `[a0, a1]`, meaning `a0 + a1*pi` with integer `Qp*_4`
/// components. The residue-characteristic-2 case is intentionally rejected by
/// Springer's odd-residue theorem boundary.
#[pyfunction]
fn springer_decompose_ramified_qp4_e2(
    p: u128,
    entries: Vec<Vec<i128>>,
) -> PyResult<PyLocalSpringerDecomp> {
    let decomp = match p {
        3 => crate::forms::springer_decompose_local(&ramified_qp4_e_metric::<3, 2>(entries)?),
        5 => crate::forms::springer_decompose_local(&ramified_qp4_e_metric::<5, 2>(entries)?),
        7 => crate::forms::springer_decompose_local(&ramified_qp4_e_metric::<7, 2>(entries)?),
        11 => crate::forms::springer_decompose_local(&ramified_qp4_e_metric::<11, 2>(entries)?),
        13 => crate::forms::springer_decompose_local(&ramified_qp4_e_metric::<13, 2>(entries)?),
        _ => {
            return Err(PyValueError::new_err(
                "supported fixed ramified Qp4 E2 Springer primes are 3, 5, 7, 11, and 13",
            ));
        }
    }
    .ok_or_else(|| {
        PyValueError::new_err(
            "Springer decomposition needs odd supported residue field and a diagonal metric",
        )
    })?;
    Ok(wrap_local_springer_decomp(decomp))
}

/// Springer decomposition over the fixed ramified cubic p-adic slice
/// `Q_p(pi)` with `pi^3 = p`, base precision `4`, and
/// `p ∈ {3, 5, 7, 11, 13}`. Entries are diagonal coefficients encoded as
/// component lists `[a0, a1, a2]`, meaning `a0 + a1*pi + a2*pi^2` with integer
/// `Qp*_4` components. The residue-characteristic-2 case is intentionally
/// rejected by Springer's odd-residue theorem boundary.
#[pyfunction]
fn springer_decompose_ramified_qp4_e3(
    p: u128,
    entries: Vec<Vec<i128>>,
) -> PyResult<PyLocalSpringerDecomp> {
    let decomp = match p {
        3 => crate::forms::springer_decompose_local(&ramified_qp4_e_metric::<3, 3>(entries)?),
        5 => crate::forms::springer_decompose_local(&ramified_qp4_e_metric::<5, 3>(entries)?),
        7 => crate::forms::springer_decompose_local(&ramified_qp4_e_metric::<7, 3>(entries)?),
        11 => crate::forms::springer_decompose_local(&ramified_qp4_e_metric::<11, 3>(entries)?),
        13 => crate::forms::springer_decompose_local(&ramified_qp4_e_metric::<13, 3>(entries)?),
        _ => {
            return Err(PyValueError::new_err(
                "supported fixed ramified Qp4 E3 Springer primes are 3, 5, 7, 11, and 13",
            ));
        }
    }
    .ok_or_else(|| {
        PyValueError::new_err(
            "Springer decomposition needs odd supported residue field and a diagonal metric",
        )
    })?;
    Ok(wrap_local_springer_decomp(decomp))
}

fn witt_coords4<const P: u128, const F: usize>(
    coords: &[u128],
    label: &str,
) -> PyResult<[u128; F]> {
    if coords.len() != F {
        return Err(PyValueError::new_err(format!(
            "{label} expected exactly {F} unramified-ring coordinates"
        )));
    }
    let modulus = WittVec::<P, 4, F>::modulus();
    let mut out = [0u128; F];
    for (i, &coord) in coords.iter().enumerate() {
        out[i] = coord % modulus;
    }
    Ok(out)
}

fn qq4_metric<const P: u128, const F: usize>(
    entries: Vec<(Vec<u128>, i128)>,
) -> PyResult<Metric<Qq<P, 4, F>>> {
    let mut q = Vec::with_capacity(entries.len());
    for (idx, (coords, valuation)) in entries.into_iter().enumerate() {
        let label = format!("entry {idx}");
        let w = WittVec::<P, 4, F>(witt_coords4::<P, F>(&coords, &label)?);
        q.push(Qq::<P, 4, F>::from_witt(w).mul(&Qq::<P, 4, F>::from_p_power(valuation)));
    }
    Ok(Metric::diagonal(q))
}

/// Springer decomposition over the fixed Python unramified p-adic slice `Q_q` at
/// precision `4`. Entries are diagonal coefficients encoded as
/// `(witt_coords, valuation)`, i.e. `p^valuation * WittVec(witt_coords)`.
/// Supported fixed scalar cells are `(p, residue_degree) = (2,2), (2,3), (2,4),
/// (3,2), (5,2), (3,3)`. The theorem layer itself rejects residue characteristic
/// `2`, so the meaningful Springer cases here are `(3,2)`, `(5,2)`, and `(3,3)`.
#[pyfunction]
fn springer_decompose_qq(
    p: u128,
    residue_degree: usize,
    entries: Vec<(Vec<u128>, i128)>,
) -> PyResult<PyLocalSpringerDecomp> {
    let decomp = match (p, residue_degree) {
        (2, 2) => crate::forms::springer_decompose_qq(&qq4_metric::<2, 2>(entries)?),
        (2, 3) => crate::forms::springer_decompose_qq(&qq4_metric::<2, 3>(entries)?),
        (2, 4) => crate::forms::springer_decompose_qq(&qq4_metric::<2, 4>(entries)?),
        (3, 2) => crate::forms::springer_decompose_qq(&qq4_metric::<3, 2>(entries)?),
        (5, 2) => crate::forms::springer_decompose_qq(&qq4_metric::<5, 2>(entries)?),
        (3, 3) => crate::forms::springer_decompose_qq(&qq4_metric::<3, 3>(entries)?),
        _ => {
            return Err(PyValueError::new_err(
                "supported fixed Qq4 cells are (2,2), (2,3), (2,4), (3,2), (5,2), and (3,3)",
            ));
        }
    }
    .ok_or_else(|| {
        PyValueError::new_err(
            "Springer decomposition needs odd residue characteristic and a diagonal metric",
        )
    })?;
    Ok(wrap_local_springer_decomp(decomp))
}

fn finite_ext_from_index<const P: u128, const N: usize>(
    code: u128,
    label: &str,
) -> PyResult<Fpn<P, N>> {
    if code >= Fpn::<P, N>::field_order() {
        return Err(PyValueError::new_err(format!(
            "{label} field element index {code} is outside F_{}",
            Fpn::<P, N>::field_order()
        )));
    }
    let mut coeffs = Vec::with_capacity(N);
    let mut x = code;
    for _ in 0..N {
        coeffs.push(x % P);
        x /= P;
    }
    Ok(Fpn::<P, N>::from_coeffs(&coeffs))
}

fn laurent_fp6_metric<const P: u128>(entries: Vec<(Vec<u128>, i128)>) -> Metric<Laurent<Fp<P>, 6>> {
    Metric::diagonal(
        entries
            .into_iter()
            .map(|(coeffs, valuation)| {
                Laurent::<Fp<P>, 6>::from_coeffs(
                    coeffs.into_iter().map(Fp::<P>::from_u128).collect(),
                    valuation,
                )
            })
            .collect(),
    )
}

fn laurent_fpn6_metric<const P: u128, const N: usize>(
    entries: Vec<(Vec<u128>, i128)>,
) -> PyResult<Metric<Laurent<Fpn<P, N>, 6>>> {
    let mut q = Vec::with_capacity(entries.len());
    for (idx, (coeffs, valuation)) in entries.into_iter().enumerate() {
        let mut parsed = Vec::with_capacity(coeffs.len());
        for (j, code) in coeffs.into_iter().enumerate() {
            parsed.push(finite_ext_from_index::<P, N>(
                code,
                &format!("entry {idx} coefficient {j}"),
            )?);
        }
        q.push(Laurent::<Fpn<P, N>, 6>::from_coeffs(parsed, valuation));
    }
    Ok(Metric::diagonal(q))
}

/// Springer decomposition over fixed equal-characteristic local fields `F_q((t))`
/// at Laurent precision `6`. Entries are diagonal coefficients encoded as
/// `(field_element_indices, valuation)`, i.e. `t^valuation * Σ c_i t^i`, where
/// each `c_i` is an element index in the residue field. Supported odd residue
/// fields are `F_3`, `F_5`, `F_7`, `F_11`, `F_13`, `F_9`, `F_25`, and `F_27`.
#[pyfunction]
fn springer_decompose_laurent(
    p: u128,
    degree: usize,
    entries: Vec<(Vec<u128>, i128)>,
) -> PyResult<PyLocalSpringerDecomp> {
    let decomp = match (p, degree) {
        (3, 1) => crate::forms::springer_decompose_laurent(&laurent_fp6_metric::<3>(entries)),
        (5, 1) => crate::forms::springer_decompose_laurent(&laurent_fp6_metric::<5>(entries)),
        (7, 1) => crate::forms::springer_decompose_laurent(&laurent_fp6_metric::<7>(entries)),
        (11, 1) => crate::forms::springer_decompose_laurent(&laurent_fp6_metric::<11>(entries)),
        (13, 1) => crate::forms::springer_decompose_laurent(&laurent_fp6_metric::<13>(entries)),
        (3, 2) => crate::forms::springer_decompose_laurent(&laurent_fpn6_metric::<3, 2>(entries)?),
        (5, 2) => crate::forms::springer_decompose_laurent(&laurent_fpn6_metric::<5, 2>(entries)?),
        (3, 3) => crate::forms::springer_decompose_laurent(&laurent_fpn6_metric::<3, 3>(entries)?),
        _ => {
            return Err(PyValueError::new_err(
                "supported fixed Laurent6 residue fields are F3, F5, F7, F11, F13, F9, F25, and F27",
            ));
        }
    }
    .ok_or_else(|| {
        PyValueError::new_err(
            "Springer decomposition needs odd supported residue field and a diagonal metric",
        )
    })?;
    Ok(wrap_local_springer_decomp(decomp))
}

// ---------------------------------------------------------------------------
// Witt ring + cohomological invariant staircase (eₙ)
// ---------------------------------------------------------------------------

/// The real cohomological invariant `eₙ` of a form of signature `σ` over `ℝ`:
/// `Some((σ/2ⁿ) mod 2)` if the form is in `Iⁿ` (i.e. `2ⁿ | σ`), else `None`. The
/// staircase reads the 2-adic expansion of the signature (the infinite ℝ tower).
#[pyfunction]
fn e_real(signature: i128, n: usize) -> Option<u128> {
    crate::forms::e_real(signature, n)
}

// ---------------------------------------------------------------------------
// p-adic Hilbert symbol + Hasse–Minkowski over Q
// ---------------------------------------------------------------------------

/// The Hilbert symbol `(a, b)_p` over `Q_p` (`p`-adic). Unlike the finite-field
/// Hilbert symbol (always `+1`), this is genuinely nontrivial — e.g. `(−1,−1)_2 = −1`.
#[pyfunction]
fn hilbert_symbol_qp(a: i128, b: i128, p: u128) -> PyResult<i128> {
    crate::forms::try_hilbert_symbol_qp(a, b, p).ok_or_else(|| {
        PyValueError::new_err(
            "Hilbert symbol needs prime p <= i128::MAX, nonzero arguments, and bounded square classes",
        )
    })
}

/// The Hilbert symbol `(a, b)_∞` over `ℝ` (`−1` iff both are negative).
#[pyfunction]
fn hilbert_symbol_real(a: i128, b: i128) -> i128 {
    crate::forms::hilbert_symbol_real(a, b)
}

/// Is the integer `n` a square in `Q_p`?
#[pyfunction]
fn is_square_qp(n: i128, p: u128) -> PyResult<bool> {
    crate::forms::try_is_square_qp(n, p)
        .ok_or_else(|| PyValueError::new_err("Q_p square test needs prime p <= i128::MAX"))
}

fn try_local_isotropic_at_p(entries: &[i128], p: u128) -> Option<bool> {
    crate::forms::try_is_square_qp(1, p)?;
    if entries.contains(&0) {
        return Some(true);
    }
    crate::forms::try_is_isotropic_at_p(entries, p)
}

/// Local isotropy of a diagonal integer form over `Q_p`.
#[pyfunction]
fn is_isotropic_at_p(entries: Vec<i128>, p: u128) -> PyResult<bool> {
    try_local_isotropic_at_p(&entries, p).ok_or_else(|| {
        PyValueError::new_err(
            "local Q_p isotropy needs prime p <= i128::MAX and bounded square classes",
        )
    })
}

/// Is the diagonal rational/integer form `⟨a₁,…,aₙ⟩` isotropic over `Q`? By the
/// **Hasse–Minkowski** principle (isotropic over `ℝ` and every `Q_p`). E.g.
/// `⟨1,1,1⟩` is anisotropic, `⟨1,1,-1⟩` isotropic, `⟨1,1,-3⟩` anisotropic.
#[pyfunction]
fn is_isotropic_q(entries: Vec<i128>) -> PyResult<bool> {
    crate::forms::try_is_isotropic_q(&entries).ok_or_else(|| {
        PyValueError::new_err("rational isotropy overflowed bounded i128 arithmetic")
    })
}

/// The Hilbert symbol at an arbitrary place of `Q`: omit `place` for the real
/// place, otherwise pass a typed `RationalPlace`.
#[pyfunction]
#[pyo3(signature = (a, b, place=None))]
fn hilbert_symbol_at(a: i128, b: i128, place: Option<Bound<'_, PyAny>>) -> PyResult<i128> {
    match parse_rational_place_arg(place.as_ref())? {
        crate::forms::Place::Real => Ok(crate::forms::hilbert_symbol_real(a, b)),
        crate::forms::Place::Prime(p) => crate::forms::try_hilbert_symbol_qp(a, b, p).ok_or_else(|| {
            PyValueError::new_err(
                "Hilbert symbol needs prime p <= i128::MAX, nonzero arguments, and bounded square classes",
            )
        }),
    }
}

/// Hasse invariant of a nondegenerate diagonal integer form at a place of `Q`.
/// Omit `place` for the real place, otherwise pass a typed `RationalPlace`.
#[pyfunction]
#[pyo3(signature = (entries, place=None))]
fn hasse_at_place(entries: Vec<i128>, place: Option<Bound<'_, PyAny>>) -> PyResult<i128> {
    if entries.contains(&0) {
        return Err(PyValueError::new_err(
            "Hasse invariant at a place needs nonzero diagonal entries",
        ));
    }
    let place = parse_rational_place_arg(place.as_ref())?;
    let mut h = 1i128;
    for i in 0..entries.len() {
        for j in (i + 1)..entries.len() {
            h *= match place {
                crate::forms::Place::Real => crate::forms::hilbert_symbol_real(entries[i], entries[j]),
                crate::forms::Place::Prime(p) => {
                    crate::forms::try_hilbert_symbol_qp(entries[i], entries[j], p).ok_or_else(|| {
                        PyValueError::new_err(
                            "Hilbert symbol needs prime p <= i128::MAX, nonzero arguments, and bounded square classes",
                        )
                    })?
                }
            };
        }
    }
    Ok(h)
}

/// The Hilbert-symbol product `∏_v (a, b)_v` over all places of `ℚ`, for `a, b ∈
/// ℚ^*` passed as `(num, den)` pairs. Equal to `+1` for all `a, b` — Hilbert
/// reciprocity, the multiplicative analogue of the adelic product formula.
#[pyfunction]
fn hilbert_product(a: (i128, i128), b: (i128, i128)) -> PyResult<i128> {
    let a = parse_q_pair(a, "first rational")?;
    let b = parse_q_pair(b, "second rational")?;
    crate::forms::hilbert_product(&a, &b).ok_or_else(|| {
        PyValueError::new_err("Hilbert product overflowed bounded rational square classes")
    })
}

fn parse_q_pair(raw: (i128, i128), name: &str) -> PyResult<Rational> {
    Rational::try_new(raw.0, raw.1).ok_or_else(|| {
        PyValueError::new_err(format!(
            "{name} has zero denominator or overflowed bounded i128"
        ))
    })
}

/// Integer-entry Hilbert reciprocity product `prod_v (a,b)_v`.
#[pyfunction]
fn hilbert_reciprocity_product(a: i128, b: i128) -> PyResult<i128> {
    if a == 0 || b == 0 {
        return Err(PyValueError::new_err(
            "Hilbert reciprocity product needs nonzero arguments",
        ));
    }
    crate::forms::try_hilbert_reciprocity_product(a, b).ok_or_else(|| {
        PyValueError::new_err(
            "Hilbert reciprocity product needs nonzero arguments and bounded square classes",
        )
    })
}

/// Local Brauer invariants `inv_v(a,b) ∈ {0, 1/2}` of the quaternion algebra
/// `(a,b)` over `Q`, returned as typed `(RationalPlace, invariant)` pairs.
#[pyfunction]
fn brauer_local_invariants(
    a: (i128, i128),
    b: (i128, i128),
) -> PyResult<Vec<(PyRationalPlace, PyRational)>> {
    let a = parse_q_pair(a, "first rational")?;
    let b = parse_q_pair(b, "second rational")?;
    Ok(crate::forms::brauer_local_invariants(&a, &b)
        .ok_or_else(|| {
            PyValueError::new_err("Brauer local invariants overflowed bounded square classes")
        })?
        .into_iter()
        .map(|(place, inv)| (wrap_rational_place(place), wrap_rational(inv)))
        .collect())
}

/// Sum of local Brauer invariants of `(a,b)` over `Q`; reciprocity says it is an
/// integer, i.e. `0` in `Q/Z`.
#[pyfunction]
fn brauer_invariant_sum(a: (i128, i128), b: (i128, i128)) -> PyResult<PyRational> {
    let a = parse_q_pair(a, "first rational")?;
    let b = parse_q_pair(b, "second rational")?;
    crate::forms::brauer_invariant_sum(&a, &b)
        .map(wrap_rational)
        .ok_or_else(|| {
            PyValueError::new_err("Brauer invariant sum overflowed bounded square classes")
        })
}

#[pyclass(name = "Brauer2Class", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyBrauer2Class {
    inner: crate::forms::Brauer2Class,
}

#[pymethods]
impl PyBrauer2Class {
    #[staticmethod]
    fn split() -> PyBrauer2Class {
        PyBrauer2Class {
            inner: crate::forms::Brauer2Class::split(),
        }
    }
    #[staticmethod]
    fn quaternion(a: i128, b: i128) -> PyResult<PyBrauer2Class> {
        crate::forms::Brauer2Class::quaternion(a, b)
            .map(|inner| PyBrauer2Class { inner })
            .ok_or_else(|| PyValueError::new_err("quaternion class needs nonzero i128 entries"))
    }
    fn is_split(&self) -> bool {
        self.inner.is_split()
    }
    fn ramified_places(&self) -> Vec<PyRationalPlace> {
        self.inner
            .ramified_places()
            .iter()
            .copied()
            .map(wrap_rational_place)
            .collect()
    }
    fn local_invariant(&self, place: &Bound<'_, PyAny>) -> PyResult<PyRational> {
        Ok(wrap_rational(
            self.inner.local_invariant(parse_rational_place(place)?),
        ))
    }
    fn satisfies_reciprocity(&self) -> bool {
        self.inner.satisfies_reciprocity()
    }
    fn __add__(&self, other: &PyBrauer2Class) -> PyBrauer2Class {
        PyBrauer2Class {
            inner: self.inner.add(&other.inner),
        }
    }
    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        matches!(other.cast::<PyBrauer2Class>(), Ok(c) if c.borrow().inner == self.inner)
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyfunction]
fn hasse_brauer_class(entries: Vec<i128>) -> PyResult<PyBrauer2Class> {
    crate::forms::hasse_brauer_class(&entries)
        .map(|inner| PyBrauer2Class { inner })
        .ok_or_else(|| {
            PyValueError::new_err("hasse_brauer_class needs nonzero i128 diagonal entries")
        })
}

#[pyfunction]
fn clifford_brauer_class(entries: Vec<i128>) -> PyResult<PyBrauer2Class> {
    crate::forms::clifford_brauer_class(&entries)
        .map(|inner| PyBrauer2Class { inner })
        .ok_or_else(|| {
            PyValueError::new_err("clifford_brauer_class needs nonzero i128 diagonal entries")
        })
}

#[pyclass(name = "BrauerClass", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyBrauerClass {
    inner: crate::forms::BrauerClass,
}

fn parse_brauer_local_entries(
    entries: Vec<Bound<'_, PyAny>>,
) -> PyResult<Vec<(crate::forms::Place, Rational)>> {
    entries
        .into_iter()
        .enumerate()
        .map(|(i, item)| {
            let tuple = item.cast::<PyTuple>().map_err(|_| {
                PyTypeError::new_err(format!(
                    "BrauerClass.from_local entry {i} must be a (RationalPlace, Rational) tuple"
                ))
            })?;
            if tuple.len() != 2 {
                return Err(PyValueError::new_err(format!(
                    "BrauerClass.from_local entry {i} must have length 2"
                )));
            }
            let place = parse_rational_place(&tuple.get_item(0)?)?;
            let inv = parse_rational(&tuple.get_item(1)?)?;
            Ok((place, inv))
        })
        .collect()
}

#[pymethods]
impl PyBrauerClass {
    #[staticmethod]
    fn split() -> PyBrauerClass {
        PyBrauerClass {
            inner: crate::forms::BrauerClass::split(),
        }
    }
    #[staticmethod]
    fn from_local(entries: Vec<Bound<'_, PyAny>>) -> PyResult<PyBrauerClass> {
        Ok(PyBrauerClass {
            inner: crate::forms::BrauerClass::from_local(parse_brauer_local_entries(entries)?),
        })
    }
    #[staticmethod]
    fn from_two_torsion(class: &PyBrauer2Class) -> PyBrauerClass {
        PyBrauerClass {
            inner: crate::forms::BrauerClass::from_two_torsion(&class.inner),
        }
    }
    fn is_split(&self) -> bool {
        self.inner.is_split()
    }
    fn local(&self) -> Vec<(PyRationalPlace, PyRational)> {
        self.inner
            .local()
            .iter()
            .map(|(&place, inv)| (wrap_rational_place(place), wrap_rational(inv.clone())))
            .collect()
    }
    fn local_invariant(&self, place: &Bound<'_, PyAny>) -> PyResult<PyRational> {
        Ok(wrap_rational(
            self.inner.local_invariant(parse_rational_place(place)?),
        ))
    }
    fn invariant_sum(&self) -> PyRational {
        wrap_rational(self.inner.invariant_sum())
    }
    fn two_torsion_places(&self) -> Option<Vec<PyRationalPlace>> {
        self.inner.two_torsion().map(|places: BTreeSet<_>| {
            places
                .into_iter()
                .map(wrap_rational_place)
                .collect::<Vec<_>>()
        })
    }
    fn __add__(&self, other: &PyBrauerClass) -> PyBrauerClass {
        PyBrauerClass {
            inner: self.inner.add(&other.inner),
        }
    }
    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        matches!(other.cast::<PyBrauerClass>(), Ok(c) if c.borrow().inner == self.inner)
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(name = "RationalBrauerWallClass", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyRationalBrauerWallClass {
    inner: crate::forms::RationalBrauerWallClass,
}

#[pymethods]
impl PyRationalBrauerWallClass {
    #[staticmethod]
    fn split() -> PyRationalBrauerWallClass {
        PyRationalBrauerWallClass {
            inner: crate::forms::RationalBrauerWallClass::split(),
        }
    }

    #[staticmethod]
    fn from_parts(
        dimension_parity: u128,
        signed_discriminant: i128,
        clifford_brauer_class: &PyBrauer2Class,
    ) -> PyResult<PyRationalBrauerWallClass> {
        crate::forms::RationalBrauerWallClass::from_parts(
            dimension_parity,
            signed_discriminant,
            clifford_brauer_class.inner.clone(),
        )
        .map(|inner| PyRationalBrauerWallClass { inner })
        .ok_or_else(|| {
            PyValueError::new_err(
                "RationalBrauerWallClass needs parity 0/1 and nonzero i128 discriminant",
            )
        })
    }

    fn is_split(&self) -> bool {
        self.inner.is_split()
    }

    #[getter]
    fn dimension_parity(&self) -> u128 {
        self.inner.dimension_parity()
    }

    #[getter]
    fn signed_discriminant(&self) -> i128 {
        self.inner.signed_discriminant()
    }

    #[getter]
    fn clifford_brauer_class(&self) -> PyBrauer2Class {
        PyBrauer2Class {
            inner: self.inner.clifford_brauer_class().clone(),
        }
    }

    fn real_bott_index(&self) -> u128 {
        self.inner.real_bott_index()
    }

    fn real_class(&self) -> PyBrauerWallClass {
        PyBrauerWallClass {
            inner: self.inner.real_class(),
        }
    }

    fn zero_like(&self) -> PyRationalBrauerWallClass {
        PyRationalBrauerWallClass {
            inner: self.inner.zero_like(),
        }
    }

    fn __add__(&self, other: &PyRationalBrauerWallClass) -> PyResult<PyRationalBrauerWallClass> {
        self.inner
            .try_add(&other.inner)
            .map(|inner| PyRationalBrauerWallClass { inner })
            .ok_or_else(|| PyValueError::new_err("rational Brauer-Wall addition overflowed"))
    }

    fn __eq__(&self, other: &PyRationalBrauerWallClass) -> bool {
        self.inner == other.inner
    }

    fn __repr__(&self) -> String {
        let places = self
            .inner
            .clifford_brauer_class()
            .ramified_places()
            .iter()
            .copied()
            .map(place_name)
            .collect::<Vec<_>>();
        format!(
            "RationalBrauerWallClass(parity={}, signed_discriminant={}, clifford_ramified={places:?}, real_bott_index={})",
            self.inner.dimension_parity(),
            self.inner.signed_discriminant(),
            self.inner.real_bott_index()
        )
    }
}

#[derive(Clone)]
enum PyFunctionFieldBrauer2Inner {
    F3(crate::forms::FunctionFieldBrauer2Class<Fp<3>>),
    F5(crate::forms::FunctionFieldBrauer2Class<Fp<5>>),
    F7(crate::forms::FunctionFieldBrauer2Class<Fp<7>>),
    F11(crate::forms::FunctionFieldBrauer2Class<Fp<11>>),
    F13(crate::forms::FunctionFieldBrauer2Class<Fp<13>>),
}

#[pyclass(name = "FunctionFieldBrauer2Class", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyFunctionFieldBrauer2Class {
    inner: PyFunctionFieldBrauer2Inner,
}

macro_rules! ff_brauer2_match {
    ($value:expr, |$inner:ident, $field:ident| $body:expr) => {
        match $value {
            PyFunctionFieldBrauer2Inner::F3($inner) => {
                type $field = Fp<3>;
                $body
            }
            PyFunctionFieldBrauer2Inner::F5($inner) => {
                type $field = Fp<5>;
                $body
            }
            PyFunctionFieldBrauer2Inner::F7($inner) => {
                type $field = Fp<7>;
                $body
            }
            PyFunctionFieldBrauer2Inner::F11($inner) => {
                type $field = Fp<11>;
                $body
            }
            PyFunctionFieldBrauer2Inner::F13($inner) => {
                type $field = Fp<13>;
                $body
            }
        }
    };
}

#[pymethods]
impl PyFunctionFieldBrauer2Class {
    #[staticmethod]
    fn split(field_order: u128) -> PyResult<Self> {
        let inner = match field_order {
            3 => PyFunctionFieldBrauer2Inner::F3(crate::forms::FunctionFieldBrauer2Class::split()),
            5 => PyFunctionFieldBrauer2Inner::F5(crate::forms::FunctionFieldBrauer2Class::split()),
            7 => PyFunctionFieldBrauer2Inner::F7(crate::forms::FunctionFieldBrauer2Class::split()),
            11 => {
                PyFunctionFieldBrauer2Inner::F11(crate::forms::FunctionFieldBrauer2Class::split())
            }
            13 => {
                PyFunctionFieldBrauer2Inner::F13(crate::forms::FunctionFieldBrauer2Class::split())
            }
            _ => return Err(unsupported_odd_prime_field_err()),
        };
        Ok(PyFunctionFieldBrauer2Class { inner })
    }
    #[getter]
    fn field_order(&self) -> u128 {
        ff_brauer2_match!(&self.inner, |_inner, Field| Field::field_order())
    }
    fn is_split(&self) -> bool {
        ff_brauer2_match!(&self.inner, |inner, _Field| inner.is_split())
    }
    fn ramified_places(&self) -> Vec<PyFunctionFieldPlace> {
        ff_brauer2_match!(&self.inner, |inner, Field| inner
            .ramified_places()
            .iter()
            .cloned()
            .map(wrap_ff_place::<Field>)
            .collect())
    }
    fn satisfies_reciprocity(&self) -> bool {
        ff_brauer2_match!(&self.inner, |inner, _Field| inner.satisfies_reciprocity())
    }
    fn __add__(&self, other: &PyFunctionFieldBrauer2Class) -> PyResult<Self> {
        let inner = match (&self.inner, &other.inner) {
            (PyFunctionFieldBrauer2Inner::F3(a), PyFunctionFieldBrauer2Inner::F3(b)) => {
                PyFunctionFieldBrauer2Inner::F3(a.add(b))
            }
            (PyFunctionFieldBrauer2Inner::F5(a), PyFunctionFieldBrauer2Inner::F5(b)) => {
                PyFunctionFieldBrauer2Inner::F5(a.add(b))
            }
            (PyFunctionFieldBrauer2Inner::F7(a), PyFunctionFieldBrauer2Inner::F7(b)) => {
                PyFunctionFieldBrauer2Inner::F7(a.add(b))
            }
            (PyFunctionFieldBrauer2Inner::F11(a), PyFunctionFieldBrauer2Inner::F11(b)) => {
                PyFunctionFieldBrauer2Inner::F11(a.add(b))
            }
            (PyFunctionFieldBrauer2Inner::F13(a), PyFunctionFieldBrauer2Inner::F13(b)) => {
                PyFunctionFieldBrauer2Inner::F13(a.add(b))
            }
            _ => {
                return Err(PyTypeError::new_err(
                    "function-field Brauer classes use different base fields",
                ))
            }
        };
        Ok(PyFunctionFieldBrauer2Class { inner })
    }
    fn __eq__(&self, other: &PyFunctionFieldBrauer2Class) -> bool {
        match (&self.inner, &other.inner) {
            (PyFunctionFieldBrauer2Inner::F3(a), PyFunctionFieldBrauer2Inner::F3(b)) => a == b,
            (PyFunctionFieldBrauer2Inner::F5(a), PyFunctionFieldBrauer2Inner::F5(b)) => a == b,
            (PyFunctionFieldBrauer2Inner::F7(a), PyFunctionFieldBrauer2Inner::F7(b)) => a == b,
            (PyFunctionFieldBrauer2Inner::F11(a), PyFunctionFieldBrauer2Inner::F11(b)) => a == b,
            (PyFunctionFieldBrauer2Inner::F13(a), PyFunctionFieldBrauer2Inner::F13(b)) => a == b,
            _ => false,
        }
    }
    fn display(&self) -> String {
        ff_brauer2_match!(&self.inner, |inner, _Field| inner.display())
    }
    fn __repr__(&self) -> String {
        self.display()
    }
}

#[derive(Clone)]
enum PyFunctionFieldBrauerWallInner {
    F3(crate::forms::FunctionFieldBrauerWallClass<Fp<3>>),
    F5(crate::forms::FunctionFieldBrauerWallClass<Fp<5>>),
    F7(crate::forms::FunctionFieldBrauerWallClass<Fp<7>>),
    F11(crate::forms::FunctionFieldBrauerWallClass<Fp<11>>),
    F13(crate::forms::FunctionFieldBrauerWallClass<Fp<13>>),
}

#[pyclass(
    name = "FunctionFieldBrauerWallClass",
    module = "ogdoad",
    from_py_object
)]
#[derive(Clone)]
struct PyFunctionFieldBrauerWallClass {
    inner: PyFunctionFieldBrauerWallInner,
}

macro_rules! ff_bw_match {
    ($value:expr, |$inner:ident, $field:ident| $body:expr) => {
        match $value {
            PyFunctionFieldBrauerWallInner::F3($inner) => {
                type $field = Fp<3>;
                $body
            }
            PyFunctionFieldBrauerWallInner::F5($inner) => {
                type $field = Fp<5>;
                $body
            }
            PyFunctionFieldBrauerWallInner::F7($inner) => {
                type $field = Fp<7>;
                $body
            }
            PyFunctionFieldBrauerWallInner::F11($inner) => {
                type $field = Fp<11>;
                $body
            }
            PyFunctionFieldBrauerWallInner::F13($inner) => {
                type $field = Fp<13>;
                $body
            }
        }
    };
}

#[pymethods]
impl PyFunctionFieldBrauerWallClass {
    #[staticmethod]
    fn split(field_order: u128) -> PyResult<Self> {
        let inner = match field_order {
            3 => PyFunctionFieldBrauerWallInner::F3(
                crate::forms::FunctionFieldBrauerWallClass::split(),
            ),
            5 => PyFunctionFieldBrauerWallInner::F5(
                crate::forms::FunctionFieldBrauerWallClass::split(),
            ),
            7 => PyFunctionFieldBrauerWallInner::F7(
                crate::forms::FunctionFieldBrauerWallClass::split(),
            ),
            11 => PyFunctionFieldBrauerWallInner::F11(
                crate::forms::FunctionFieldBrauerWallClass::split(),
            ),
            13 => PyFunctionFieldBrauerWallInner::F13(
                crate::forms::FunctionFieldBrauerWallClass::split(),
            ),
            _ => return Err(unsupported_odd_prime_field_err()),
        };
        Ok(PyFunctionFieldBrauerWallClass { inner })
    }
    #[getter]
    fn field_order(&self) -> u128 {
        ff_bw_match!(&self.inner, |_inner, Field| Field::field_order())
    }
    fn is_split(&self) -> bool {
        ff_bw_match!(&self.inner, |inner, _Field| inner.is_split())
    }
    #[getter]
    fn dimension_parity(&self) -> u128 {
        ff_bw_match!(&self.inner, |inner, _Field| inner.dimension_parity())
    }
    #[getter]
    fn signed_discriminant(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        match &self.inner {
            PyFunctionFieldBrauerWallInner::F3(inner) => {
                wrap_fp3_rational_function(inner.signed_discriminant().clone()).into_py_any(py)
            }
            PyFunctionFieldBrauerWallInner::F5(inner) => {
                wrap_fp5_rational_function(inner.signed_discriminant().clone()).into_py_any(py)
            }
            PyFunctionFieldBrauerWallInner::F7(inner) => {
                wrap_fp7_rational_function(inner.signed_discriminant().clone()).into_py_any(py)
            }
            PyFunctionFieldBrauerWallInner::F11(inner) => {
                wrap_fp11_rational_function(inner.signed_discriminant().clone()).into_py_any(py)
            }
            PyFunctionFieldBrauerWallInner::F13(inner) => {
                wrap_fp13_rational_function(inner.signed_discriminant().clone()).into_py_any(py)
            }
        }
    }
    #[getter]
    fn clifford_brauer_class(&self) -> PyFunctionFieldBrauer2Class {
        let inner = match &self.inner {
            PyFunctionFieldBrauerWallInner::F3(inner) => {
                PyFunctionFieldBrauer2Inner::F3(inner.clifford_brauer_class().clone())
            }
            PyFunctionFieldBrauerWallInner::F5(inner) => {
                PyFunctionFieldBrauer2Inner::F5(inner.clifford_brauer_class().clone())
            }
            PyFunctionFieldBrauerWallInner::F7(inner) => {
                PyFunctionFieldBrauer2Inner::F7(inner.clifford_brauer_class().clone())
            }
            PyFunctionFieldBrauerWallInner::F11(inner) => {
                PyFunctionFieldBrauer2Inner::F11(inner.clifford_brauer_class().clone())
            }
            PyFunctionFieldBrauerWallInner::F13(inner) => {
                PyFunctionFieldBrauer2Inner::F13(inner.clifford_brauer_class().clone())
            }
        };
        PyFunctionFieldBrauer2Class { inner }
    }
    fn zero_like(&self) -> Self {
        let inner = match &self.inner {
            PyFunctionFieldBrauerWallInner::F3(inner) => {
                PyFunctionFieldBrauerWallInner::F3(inner.zero_like())
            }
            PyFunctionFieldBrauerWallInner::F5(inner) => {
                PyFunctionFieldBrauerWallInner::F5(inner.zero_like())
            }
            PyFunctionFieldBrauerWallInner::F7(inner) => {
                PyFunctionFieldBrauerWallInner::F7(inner.zero_like())
            }
            PyFunctionFieldBrauerWallInner::F11(inner) => {
                PyFunctionFieldBrauerWallInner::F11(inner.zero_like())
            }
            PyFunctionFieldBrauerWallInner::F13(inner) => {
                PyFunctionFieldBrauerWallInner::F13(inner.zero_like())
            }
        };
        PyFunctionFieldBrauerWallClass { inner }
    }
    fn __add__(&self, other: &PyFunctionFieldBrauerWallClass) -> PyResult<Self> {
        let inner = match (&self.inner, &other.inner) {
            (PyFunctionFieldBrauerWallInner::F3(a), PyFunctionFieldBrauerWallInner::F3(b)) => {
                a.try_add(b).map(PyFunctionFieldBrauerWallInner::F3)
            }
            (PyFunctionFieldBrauerWallInner::F5(a), PyFunctionFieldBrauerWallInner::F5(b)) => {
                a.try_add(b).map(PyFunctionFieldBrauerWallInner::F5)
            }
            (PyFunctionFieldBrauerWallInner::F7(a), PyFunctionFieldBrauerWallInner::F7(b)) => {
                a.try_add(b).map(PyFunctionFieldBrauerWallInner::F7)
            }
            (PyFunctionFieldBrauerWallInner::F11(a), PyFunctionFieldBrauerWallInner::F11(b)) => {
                a.try_add(b).map(PyFunctionFieldBrauerWallInner::F11)
            }
            (PyFunctionFieldBrauerWallInner::F13(a), PyFunctionFieldBrauerWallInner::F13(b)) => {
                a.try_add(b).map(PyFunctionFieldBrauerWallInner::F13)
            }
            _ => {
                return Err(PyTypeError::new_err(
                    "function-field Brauer-Wall classes use different base fields",
                ))
            }
        }
        .ok_or_else(|| {
            PyValueError::new_err(
                "function-field Brauer-Wall addition left the exact classification surface",
            )
        })?;
        Ok(PyFunctionFieldBrauerWallClass { inner })
    }
    fn __eq__(&self, other: &PyFunctionFieldBrauerWallClass) -> bool {
        match (&self.inner, &other.inner) {
            (PyFunctionFieldBrauerWallInner::F3(a), PyFunctionFieldBrauerWallInner::F3(b)) => {
                a == b
            }
            (PyFunctionFieldBrauerWallInner::F5(a), PyFunctionFieldBrauerWallInner::F5(b)) => {
                a == b
            }
            (PyFunctionFieldBrauerWallInner::F7(a), PyFunctionFieldBrauerWallInner::F7(b)) => {
                a == b
            }
            (PyFunctionFieldBrauerWallInner::F11(a), PyFunctionFieldBrauerWallInner::F11(b)) => {
                a == b
            }
            (PyFunctionFieldBrauerWallInner::F13(a), PyFunctionFieldBrauerWallInner::F13(b)) => {
                a == b
            }
            _ => false,
        }
    }
    fn display(&self) -> String {
        ff_bw_match!(&self.inner, |inner, _Field| inner.display())
    }
    fn __repr__(&self) -> String {
        self.display()
    }
}

macro_rules! bw_function_field_alg_case {
    ($alg:ident, $ty:ty, $variant:ident) => {
        if let Ok(a) = $alg.cast::<$ty>() {
            let a = a.borrow();
            return crate::forms::bw_class_function_field(&a.inner.metric)
                .map(|inner| PyFunctionFieldBrauerWallClass {
                    inner: PyFunctionFieldBrauerWallInner::$variant(inner),
                })
                .ok_or_else(|| {
                    PyValueError::new_err(
                        "function-field Brauer-Wall class needs a diagonalizable metric inside the exact place-symbol surface",
                    )
                });
        }
    };
}

/// Brauer-Wall class of a fixed odd-characteristic function-field algebra.
#[pyfunction]
fn bw_class_function_field(alg: Bound<'_, PyAny>) -> PyResult<PyFunctionFieldBrauerWallClass> {
    bw_function_field_alg_case!(alg, Fp3RationalFunctionAlgebra, F3);
    bw_function_field_alg_case!(alg, Fp5RationalFunctionAlgebra, F5);
    bw_function_field_alg_case!(alg, Fp7RationalFunctionAlgebra, F7);
    bw_function_field_alg_case!(alg, Fp11RationalFunctionAlgebra, F11);
    bw_function_field_alg_case!(alg, Fp13RationalFunctionAlgebra, F13);
    Err(PyTypeError::new_err(
        "expected an Fp{3,5,7,11,13}RationalFunctionAlgebra",
    ))
}

fn qp_to_qq_base_for_cyclic<const P: u128, const N: usize, const K: u128>(
    x: Qp<P, K>,
) -> Qq<P, N, 1> {
    debug_assert_eq!(N as u128, K, "Python fixed Qq/Qp precisions must match");
    match x.valuation() {
        None => Qq::<P, N, 1>::zero(),
        Some(v) => {
            Qq::<P, N, 1>::from_p_power(v).mul(&Qq::from_witt(WittVec::<P, N, 1>([x.unit()])))
        }
    }
}

#[pyfunction]
fn cyclic_algebra_invariant(
    p: u128,
    degree: usize,
    a: &Bound<'_, PyAny>,
) -> PyResult<Option<PyRational>> {
    macro_rules! dispatch {
        ($parse:ident, $p:literal, $f:literal) => {{
            let base = qp_to_qq_base_for_cyclic::<$p, 4, 4>($parse(a)?);
            Ok(crate::forms::cyclic_algebra_invariant::<Qq<$p, 4, $f>>(&base).map(wrap_rational))
        }};
    }

    match (p, degree) {
        (2, 2) => dispatch!(parse_qp2_4, 2, 2),
        (2, 3) => dispatch!(parse_qp2_4, 2, 3),
        (2, 4) => dispatch!(parse_qp2_4, 2, 4),
        (3, 2) => dispatch!(parse_qp3_4, 3, 2),
        (3, 3) => dispatch!(parse_qp3_4, 3, 3),
        (5, 2) => dispatch!(parse_qp5_4, 5, 2),
        _ => Err(PyValueError::new_err(
            "supported cyclic Qq legs: Qq2_4_2, Qq2_4_3, Qq2_4_4, Qq3_4_2, Qq3_4_3, Qq5_4_2",
        )),
    }
}

#[pyfunction]
#[pyo3(signature = (p, n, a, b, degree=1))]
fn tame_symbol_exponent(
    p: u128,
    n: u128,
    a: &Bound<'_, PyAny>,
    b: &Bound<'_, PyAny>,
    degree: usize,
) -> PyResult<Option<u128>> {
    macro_rules! dispatch {
        ($parse:ident) => {{
            let a = $parse(a)?;
            let b = $parse(b)?;
            Ok(crate::forms::tame_symbol_exponent(n, &a, &b))
        }};
    }

    match (p, degree) {
        (2, 1) => dispatch!(parse_qp2_4),
        (3, 1) => dispatch!(parse_qp3_4),
        (5, 1) => dispatch!(parse_qp5_4),
        (7, 1) => dispatch!(parse_qp7_4),
        (11, 1) => dispatch!(parse_qp11_4),
        (13, 1) => dispatch!(parse_qp13_4),
        (2, 2) => dispatch!(parse_qq2_4_2),
        (2, 3) => dispatch!(parse_qq2_4_3),
        (2, 4) => dispatch!(parse_qq2_4_4),
        (3, 2) => dispatch!(parse_qq3_4_2),
        (3, 3) => dispatch!(parse_qq3_4_3),
        (5, 2) => dispatch!(parse_qq5_4_2),
        _ => Err(PyValueError::new_err(
            "supported tame-symbol local fields: Qp*_4 for p in {2,3,5,7,11,13}, plus Qq2_4_{2,3,4}, Qq3_4_{2,3}, Qq5_4_2",
        )),
    }
}

#[pyfunction]
#[pyo3(signature = (p, n, a, b, degree=1))]
fn tame_symbol_invariant(
    p: u128,
    n: u128,
    a: &Bound<'_, PyAny>,
    b: &Bound<'_, PyAny>,
    degree: usize,
) -> PyResult<Option<PyRational>> {
    macro_rules! dispatch {
        ($parse:ident) => {{
            let a = $parse(a)?;
            let b = $parse(b)?;
            Ok(crate::forms::tame_symbol_invariant(n, &a, &b).map(wrap_rational))
        }};
    }

    match (p, degree) {
        (2, 1) => dispatch!(parse_qp2_4),
        (3, 1) => dispatch!(parse_qp3_4),
        (5, 1) => dispatch!(parse_qp5_4),
        (7, 1) => dispatch!(parse_qp7_4),
        (11, 1) => dispatch!(parse_qp11_4),
        (13, 1) => dispatch!(parse_qp13_4),
        (2, 2) => dispatch!(parse_qq2_4_2),
        (2, 3) => dispatch!(parse_qq2_4_3),
        (2, 4) => dispatch!(parse_qq2_4_4),
        (3, 2) => dispatch!(parse_qq3_4_2),
        (3, 3) => dispatch!(parse_qq3_4_3),
        (5, 2) => dispatch!(parse_qq5_4_2),
        _ => Err(PyValueError::new_err(
            "supported tame-symbol local fields: Qp*_4 for p in {2,3,5,7,11,13}, plus Qq2_4_{2,3,4}, Qq3_4_{2,3}, Qq5_4_2",
        )),
    }
}

type PyGlobalResidues = (i128, Vec<(u128, PyWittClassG)>);
type PyFunctionFieldMilnorResidues = (PyWittClassG, Vec<(PyFunctionFieldPlace, PyWittClassG)>);

#[pyfunction]
fn global_residues(entries: Vec<i128>) -> Option<PyGlobalResidues> {
    crate::forms::global_residues(&entries).map(|(signature, residues)| {
        (
            signature,
            residues
                .into_iter()
                .map(|(p, inner)| (p, PyWittClassG { inner }))
                .collect(),
        )
    })
}

#[pyfunction]
#[pyo3(signature = (p, entries, degree=1))]
fn global_residues_ff(
    p: u128,
    entries: Vec<PyFFRationalFunction>,
    degree: usize,
) -> PyResult<Option<PyFunctionFieldMilnorResidues>> {
    with_finite_odd_field!(p, degree, |F| {
        let entries = parse_ff_rational_functions::<F>(&entries)?;
        Ok(
            crate::forms::global_residues_ff(&entries).map(|(constant, residues)| {
                (
                    PyWittClassG { inner: constant },
                    residues
                        .into_iter()
                        .map(|(place, inner)| (wrap_ff_place::<F>(place), PyWittClassG { inner }))
                        .collect(),
                )
            }),
        )
    })
}

/// The per-place isotropy breakdown of a `ℚ`-form (rank ≥ 3): isotropy at `ℝ` and
/// at each relevant prime. `is_global()` (isotropic everywhere) equals
/// `is_isotropic_q` (Hasse–Minkowski).
#[pyclass(name = "AdelicIsotropy", module = "ogdoad")]
struct PyAdelicIsotropy {
    inner: crate::forms::AdelicIsotropy,
}

#[pymethods]
impl PyAdelicIsotropy {
    /// Isotropy over the Archimedean completion `ℝ`.
    #[getter]
    fn real(&self) -> bool {
        self.inner.real
    }
    /// Isotropy over `Q_p` at each relevant prime, as a `{p: bool}` dict.
    #[getter]
    fn local(&self) -> std::collections::BTreeMap<u128, bool> {
        self.inner.local.clone()
    }
    /// Isotropic over `ℚ` iff isotropic at every place (the local–global principle).
    fn is_global(&self) -> bool {
        self.inner.is_global()
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

/// The adelic Hasse–Minkowski decomposition of a diagonal integer form of **rank
/// ≥ 3**: isotropy at `ℝ` and each relevant prime. Errors on rank ≤ 2 (there
/// isotropy is a global-square condition — use `is_isotropic_q`).
#[pyfunction]
fn isotropy_over_adeles(entries: Vec<i128>) -> PyResult<PyAdelicIsotropy> {
    if entries.len() < 3 {
        return Err(PyValueError::new_err(
            "adelic isotropy decomposition needs rank ≥ 3 (use is_isotropic_q for rank ≤ 2)",
        ));
    }
    Ok(PyAdelicIsotropy {
        inner: crate::forms::isotropy_over_adeles(&entries).ok_or_else(|| {
            PyValueError::new_err("adelic isotropy overflowed bounded square classes")
        })?,
    })
}

// ---------------------------------------------------------------------------
// Binary codes, integral lattices, discriminant forms, and modular q-expansions
// ---------------------------------------------------------------------------

#[pyclass(name = "Complex64", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyComplex64 {
    inner: crate::forms::Complex64,
}

#[pymethods]
impl PyComplex64 {
    #[new]
    fn new(re: f64, im: f64) -> Self {
        PyComplex64 {
            inner: crate::forms::Complex64 { re, im },
        }
    }
    #[staticmethod]
    fn zero() -> Self {
        PyComplex64 {
            inner: crate::forms::Complex64::zero(),
        }
    }
    #[staticmethod]
    fn one() -> Self {
        PyComplex64 {
            inner: crate::forms::Complex64::one(),
        }
    }
    #[staticmethod]
    fn cis(theta: f64) -> Self {
        PyComplex64 {
            inner: crate::forms::Complex64::cis(theta),
        }
    }
    #[staticmethod]
    fn eighth_root(k: i128) -> Self {
        PyComplex64 {
            inner: crate::forms::Complex64::eighth_root(k),
        }
    }
    #[getter]
    fn re(&self) -> f64 {
        self.inner.re
    }
    #[getter]
    fn im(&self) -> f64 {
        self.inner.im
    }
    fn abs(&self) -> f64 {
        self.inner.abs()
    }
    fn __add__(&self, rhs: &PyComplex64) -> PyComplex64 {
        PyComplex64 {
            inner: self.inner.add(&rhs.inner),
        }
    }
    fn __sub__(&self, rhs: &PyComplex64) -> PyComplex64 {
        PyComplex64 {
            inner: self.inner.sub(&rhs.inner),
        }
    }
    fn __mul__(&self, rhs: &PyComplex64) -> PyComplex64 {
        PyComplex64 {
            inner: self.inner.mul(&rhs.inner),
        }
    }
    fn scale(&self, c: f64) -> PyComplex64 {
        PyComplex64 {
            inner: self.inner.scale(c),
        }
    }
    fn approx_eq(&self, rhs: &PyComplex64, tol: f64) -> bool {
        self.inner.approx_eq(&rhs.inner, tol)
    }
    fn __repr__(&self) -> String {
        format!("Complex64(re={}, im={})", self.inner.re, self.inner.im)
    }
}

fn wrap_complex64(z: crate::forms::Complex64) -> PyComplex64 {
    PyComplex64 { inner: z }
}

#[pyclass(name = "GaussSum", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyGaussSum {
    inner: crate::forms::GaussSum,
}

#[pymethods]
impl PyGaussSum {
    #[new]
    fn new(re: f64, im: f64) -> Self {
        PyGaussSum {
            inner: crate::forms::GaussSum { re, im },
        }
    }
    #[getter]
    fn re(&self) -> f64 {
        self.inner.re
    }
    #[getter]
    fn im(&self) -> f64 {
        self.inner.im
    }
    fn abs(&self) -> f64 {
        self.inner.abs()
    }
    fn phase_mod8(&self, tol: f64) -> Option<i128> {
        self.inner.phase_mod8(tol)
    }
    fn __repr__(&self) -> String {
        format!("GaussSum(re={}, im={})", self.inner.re, self.inner.im)
    }
}

#[pyclass(name = "BinaryCode", module = "ogdoad", from_py_object)]
#[derive(Clone)]
pub(crate) struct PyBinaryCode {
    inner: crate::forms::BinaryCode,
}

pub(crate) fn wrap_binary_code(inner: crate::forms::BinaryCode) -> PyBinaryCode {
    PyBinaryCode { inner }
}

#[pymethods]
impl PyBinaryCode {
    #[new]
    fn new(n: usize, generators: Vec<Vec<u8>>) -> PyResult<Self> {
        crate::forms::BinaryCode::new(n, generators)
            .map(|inner| PyBinaryCode { inner })
            .ok_or_else(|| {
                PyValueError::new_err("binary code generators must have length n and entries 0/1")
            })
    }
    #[staticmethod]
    fn repetition(n: usize) -> PyResult<Self> {
        crate::forms::repetition_code(n)
            .map(|inner| PyBinaryCode { inner })
            .ok_or_else(|| PyValueError::new_err("repetition code requires n > 0"))
    }
    #[staticmethod]
    fn reed_muller(order: usize, variables: usize) -> PyResult<Self> {
        crate::forms::reed_muller_code(order, variables)
            .map(|inner| PyBinaryCode { inner })
            .ok_or_else(|| {
                PyValueError::new_err(
                    "Reed-Muller code requires order <= variables and an allocatable generator matrix",
                )
            })
    }
    #[staticmethod]
    fn type_i_z2() -> Self {
        PyBinaryCode {
            inner: crate::forms::type_i_z2_code(),
        }
    }
    #[staticmethod]
    fn type_i_z2_plus_e8() -> Self {
        PyBinaryCode {
            inner: crate::forms::type_i_z2_plus_e8_code(),
        }
    }
    #[staticmethod]
    fn hamming() -> Self {
        PyBinaryCode {
            inner: crate::forms::hamming_code(),
        }
    }
    #[staticmethod]
    fn extended_hamming() -> Self {
        PyBinaryCode {
            inner: crate::forms::extended_hamming_code(),
        }
    }
    #[staticmethod]
    fn type_ii_e8_sum() -> Self {
        PyBinaryCode {
            inner: crate::forms::type_ii_e8_sum_code(),
        }
    }
    #[staticmethod]
    fn type_ii_len16() -> Self {
        PyBinaryCode {
            inner: crate::forms::type_ii_len16_code(),
        }
    }
    #[staticmethod]
    fn golay() -> Self {
        PyBinaryCode {
            inner: crate::forms::golay_code(),
        }
    }
    fn len(&self) -> usize {
        self.inner.len()
    }
    fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
    fn dim(&self) -> usize {
        self.inner.dim()
    }
    fn generators(&self) -> Vec<Vec<u8>> {
        self.inner.generators().to_vec()
    }
    fn size(&self) -> Option<u128> {
        self.inner.size()
    }
    fn dual(&self) -> PyBinaryCode {
        PyBinaryCode {
            inner: self.inner.dual(),
        }
    }
    fn direct_sum(&self, other: &PyBinaryCode) -> PyBinaryCode {
        PyBinaryCode {
            inner: self.inner.direct_sum(&other.inner),
        }
    }
    fn contains(&self, other: &PyBinaryCode) -> bool {
        self.inner.contains(&other.inner)
    }
    fn is_self_dual(&self) -> bool {
        self.inner.is_self_dual()
    }
    fn is_self_orthogonal(&self) -> bool {
        self.inner.is_self_orthogonal()
    }
    fn is_doubly_even(&self) -> bool {
        self.inner.is_doubly_even()
    }
    fn minimum_distance(&self) -> Option<usize> {
        self.inner.minimum_distance()
    }
    fn weight_enumerator(&self) -> Vec<i128> {
        self.inner.weight_enumerator()
    }
    fn macwilliams_transform(&self) -> Vec<i128> {
        self.inner.macwilliams_transform()
    }
    fn construction_a(&self) -> Option<PyIntegralForm> {
        self.inner
            .construction_a()
            .map(|inner| PyIntegralForm { inner })
    }
    fn construction_b(&self) -> Option<PyIntegralForm> {
        self.inner
            .construction_b()
            .map(|inner| PyIntegralForm { inner })
    }
    #[staticmethod]
    fn construction_d(codes: Vec<PyBinaryCode>) -> Option<PyIntegralForm> {
        let codes: Vec<_> = codes.into_iter().map(|code| code.inner).collect();
        crate::forms::construction_d(&codes).map(|inner| PyIntegralForm { inner })
    }
    fn theta_series_via_weight_enumerator(&self, terms: usize) -> Option<Vec<i128>> {
        self.inner.theta_series_via_weight_enumerator(terms)
    }
    fn __repr__(&self) -> String {
        format!(
            "BinaryCode(n={}, dim={}, generators={:?})",
            self.inner.len(),
            self.inner.dim(),
            self.inner.generators()
        )
    }
}

#[pyfunction]
fn repetition_code(n: usize) -> PyResult<PyBinaryCode> {
    PyBinaryCode::repetition(n)
}

#[pyfunction]
fn reed_muller_code(order: usize, variables: usize) -> PyResult<PyBinaryCode> {
    PyBinaryCode::reed_muller(order, variables)
}

#[pyfunction]
fn type_i_z2_code() -> PyBinaryCode {
    PyBinaryCode::type_i_z2()
}

#[pyfunction]
fn type_i_z2_plus_e8_code() -> PyBinaryCode {
    PyBinaryCode::type_i_z2_plus_e8()
}

#[pyfunction]
fn hamming_code() -> PyBinaryCode {
    PyBinaryCode::hamming()
}

#[pyfunction]
fn extended_hamming_code() -> PyBinaryCode {
    PyBinaryCode::extended_hamming()
}

#[pyfunction]
fn type_ii_e8_sum_code() -> PyBinaryCode {
    PyBinaryCode::type_ii_e8_sum()
}

#[pyfunction]
fn type_ii_len16_code() -> PyBinaryCode {
    PyBinaryCode::type_ii_len16()
}

#[pyfunction]
fn golay_code() -> PyBinaryCode {
    PyBinaryCode::golay()
}

#[pyfunction]
fn extended_golay_generator_rows() -> Vec<Vec<u8>> {
    crate::forms::extended_golay_generator_rows()
}

#[pyfunction]
fn construction_d(codes: Vec<PyBinaryCode>) -> Option<PyIntegralForm> {
    PyBinaryCode::construction_d(codes)
}

#[pyfunction]
fn barnes_wall_16() -> PyIntegralForm {
    PyIntegralForm {
        inner: crate::forms::barnes_wall_16(),
    }
}

#[pyclass(
    name = "CliffordBarnesWall16Report",
    module = "ogdoad",
    skip_from_py_object
)]
#[derive(Clone)]
struct PyCliffordBarnesWall16Report {
    inner: crate::forms::CliffordBarnesWall16Invariants,
}

#[pymethods]
impl PyCliffordBarnesWall16Report {
    #[getter]
    fn lattice(&self) -> PyIntegralForm {
        PyIntegralForm {
            inner: self.inner.lattice.clone(),
        }
    }
    #[getter]
    fn construction_d_lattice(&self) -> PyIntegralForm {
        PyIntegralForm {
            inner: self.inner.construction_d_lattice.clone(),
        }
    }
    #[getter]
    fn spinor_dimension(&self) -> usize {
        self.inner.spinor_dimension
    }
    #[getter]
    fn row_divisor(&self) -> i128 {
        self.inner.row_divisor
    }
    #[getter]
    fn quadratic_phase_row_count(&self) -> usize {
        self.inner.quadratic_phase_row_count
    }
    #[getter]
    fn coordinate_weight_row_count(&self) -> usize {
        self.inner.coordinate_weight_row_count
    }
    #[getter]
    fn matches_construction_d(&self) -> bool {
        self.inner.matches_construction_d
    }
    #[getter]
    fn automorphism_group_order(&self) -> u128 {
        self.inner.automorphism_group_order
    }
    #[getter]
    fn full_clifford_group_order(&self) -> u128 {
        self.inner.full_clifford_group_order
    }
    #[getter]
    fn automorphism_index_in_clifford_group(&self) -> u128 {
        self.inner.automorphism_index_in_clifford_group
    }
    fn determinant(&self) -> i128 {
        self.inner.determinant()
    }
    fn minimum(&self) -> Option<i128> {
        self.inner.minimum()
    }
    fn kissing_number(&self) -> Option<usize> {
        self.inner.kissing_number()
    }
    fn recorded_group_orders_are_consistent(&self) -> bool {
        self.inner.recorded_group_orders_are_consistent()
    }
    // The pyclass name is "CliffordBarnesWall16Report"; the core type is
    // `CliffordBarnesWall16Invariants` — swap the leading name so Python users
    // see the name they imported.
    fn display(&self) -> String {
        self.inner.display().replacen(
            "CliffordBarnesWall16Invariants",
            "CliffordBarnesWall16Report",
            1,
        )
    }
    fn __repr__(&self) -> String {
        self.display()
    }
}

#[pyfunction]
fn clifford_barnes_wall_16_numerator_rows() -> Vec<Vec<i128>> {
    crate::forms::clifford_barnes_wall_16_numerator_rows()
}

#[pyfunction]
fn clifford_barnes_wall_16() -> PyIntegralForm {
    PyIntegralForm {
        inner: crate::forms::clifford_barnes_wall_16(),
    }
}

#[pyfunction]
fn clifford_barnes_wall_16_report() -> PyCliffordBarnesWall16Report {
    PyCliffordBarnesWall16Report {
        inner: crate::forms::clifford_barnes_wall_16_report(),
    }
}

fn prime_code_from_rows<const P: u128>(
    n: usize,
    generators: Vec<Vec<u128>>,
) -> PyResult<crate::forms::PrimeCode<P>> {
    crate::forms::PrimeCode::<P>::new(n, generators).ok_or_else(|| {
        PyValueError::new_err(format!(
            "prime code generators must have length n and entries in F_{P}; P must be an odd prime"
        ))
    })
}

macro_rules! with_prime_code {
    ($p:expr, $n:expr, $generators:expr, |$code:ident| $body:expr) => {{
        match $p {
            3 => {
                let $code = prime_code_from_rows::<3>($n, $generators)?;
                $body
            }
            5 => {
                let $code = prime_code_from_rows::<5>($n, $generators)?;
                $body
            }
            7 => {
                let $code = prime_code_from_rows::<7>($n, $generators)?;
                $body
            }
            11 => {
                let $code = prime_code_from_rows::<11>($n, $generators)?;
                $body
            }
            13 => {
                let $code = prime_code_from_rows::<13>($n, $generators)?;
                $body
            }
            _ => {
                return Err(PyValueError::new_err(
                    "supported odd prime code fields: F_3, F_5, F_7, F_11, F_13",
                ))
            }
        }
    }};
}

fn wrap_prime_code<const P: u128>(inner: crate::forms::PrimeCode<P>) -> PyPrimeCode {
    PyPrimeCode {
        p: P,
        n: inner.len(),
        generators: inner.generators().to_vec(),
    }
}

type PyCompleteWeightEnumerator = Vec<(Vec<usize>, i128)>;

#[pyclass(name = "PrimeCode", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyPrimeCode {
    p: u128,
    n: usize,
    generators: Vec<Vec<u128>>,
}

#[pymethods]
impl PyPrimeCode {
    #[new]
    fn new(p: u128, n: usize, generators: Vec<Vec<u128>>) -> PyResult<Self> {
        with_prime_code!(p, n, generators, |code| {
            Ok(PyPrimeCode {
                p,
                n: code.len(),
                generators: code.generators().to_vec(),
            })
        })
    }
    #[staticmethod]
    fn ternary_golay() -> Self {
        wrap_prime_code(crate::forms::ternary_golay_code())
    }
    #[getter]
    fn p(&self) -> u128 {
        self.p
    }
    fn len(&self) -> usize {
        self.n
    }
    fn is_empty(&self) -> bool {
        self.n == 0
    }
    fn dim(&self) -> PyResult<usize> {
        with_prime_code!(self.p, self.n, self.generators.clone(), |code| {
            Ok(code.dim())
        })
    }
    fn generators(&self) -> Vec<Vec<u128>> {
        self.generators.clone()
    }
    fn size(&self) -> PyResult<Option<u128>> {
        with_prime_code!(self.p, self.n, self.generators.clone(), |code| {
            Ok(code.size())
        })
    }
    fn dual(&self) -> PyResult<PyPrimeCode> {
        with_prime_code!(self.p, self.n, self.generators.clone(), |code| {
            Ok(wrap_prime_code(code.dual()))
        })
    }
    fn direct_sum(&self, other: &PyPrimeCode) -> PyResult<PyPrimeCode> {
        if self.p != other.p {
            return Err(PyTypeError::new_err(
                "prime codes must live over the same F_p",
            ));
        }
        match self.p {
            3 => {
                let a = prime_code_from_rows::<3>(self.n, self.generators.clone())?;
                let b = prime_code_from_rows::<3>(other.n, other.generators.clone())?;
                Ok(wrap_prime_code(a.direct_sum(&b)))
            }
            5 => {
                let a = prime_code_from_rows::<5>(self.n, self.generators.clone())?;
                let b = prime_code_from_rows::<5>(other.n, other.generators.clone())?;
                Ok(wrap_prime_code(a.direct_sum(&b)))
            }
            7 => {
                let a = prime_code_from_rows::<7>(self.n, self.generators.clone())?;
                let b = prime_code_from_rows::<7>(other.n, other.generators.clone())?;
                Ok(wrap_prime_code(a.direct_sum(&b)))
            }
            11 => {
                let a = prime_code_from_rows::<11>(self.n, self.generators.clone())?;
                let b = prime_code_from_rows::<11>(other.n, other.generators.clone())?;
                Ok(wrap_prime_code(a.direct_sum(&b)))
            }
            13 => {
                let a = prime_code_from_rows::<13>(self.n, self.generators.clone())?;
                let b = prime_code_from_rows::<13>(other.n, other.generators.clone())?;
                Ok(wrap_prime_code(a.direct_sum(&b)))
            }
            _ => Err(PyValueError::new_err(
                "supported odd prime code fields: F_3, F_5, F_7, F_11, F_13",
            )),
        }
    }
    fn contains(&self, other: &PyPrimeCode) -> PyResult<bool> {
        if self.p != other.p {
            return Ok(false);
        }
        match self.p {
            3 => {
                let a = prime_code_from_rows::<3>(self.n, self.generators.clone())?;
                let b = prime_code_from_rows::<3>(other.n, other.generators.clone())?;
                Ok(a.contains(&b))
            }
            5 => {
                let a = prime_code_from_rows::<5>(self.n, self.generators.clone())?;
                let b = prime_code_from_rows::<5>(other.n, other.generators.clone())?;
                Ok(a.contains(&b))
            }
            7 => {
                let a = prime_code_from_rows::<7>(self.n, self.generators.clone())?;
                let b = prime_code_from_rows::<7>(other.n, other.generators.clone())?;
                Ok(a.contains(&b))
            }
            11 => {
                let a = prime_code_from_rows::<11>(self.n, self.generators.clone())?;
                let b = prime_code_from_rows::<11>(other.n, other.generators.clone())?;
                Ok(a.contains(&b))
            }
            13 => {
                let a = prime_code_from_rows::<13>(self.n, self.generators.clone())?;
                let b = prime_code_from_rows::<13>(other.n, other.generators.clone())?;
                Ok(a.contains(&b))
            }
            _ => Ok(false),
        }
    }
    fn is_self_dual(&self) -> PyResult<bool> {
        with_prime_code!(self.p, self.n, self.generators.clone(), |code| {
            Ok(code.is_self_dual())
        })
    }
    fn is_self_orthogonal(&self) -> PyResult<bool> {
        with_prime_code!(self.p, self.n, self.generators.clone(), |code| {
            Ok(code.is_self_orthogonal())
        })
    }
    fn minimum_distance(&self) -> PyResult<Option<usize>> {
        with_prime_code!(self.p, self.n, self.generators.clone(), |code| {
            Ok(code.minimum_distance())
        })
    }
    fn weight_enumerator(&self) -> PyResult<Vec<i128>> {
        with_prime_code!(self.p, self.n, self.generators.clone(), |code| {
            Ok(code.weight_enumerator())
        })
    }
    fn complete_weight_enumerator(&self) -> PyResult<Option<PyCompleteWeightEnumerator>> {
        with_prime_code!(self.p, self.n, self.generators.clone(), |code| {
            Ok(code
                .complete_weight_enumerator()
                .map(|map| map.into_iter().collect()))
        })
    }
    fn macwilliams_transform(&self) -> PyResult<Option<Vec<i128>>> {
        with_prime_code!(self.p, self.n, self.generators.clone(), |code| {
            Ok(code.macwilliams_transform())
        })
    }
    fn construction_a(&self) -> PyResult<Option<PyIntegralForm>> {
        with_prime_code!(self.p, self.n, self.generators.clone(), |code| {
            Ok(code.construction_a().map(|inner| PyIntegralForm { inner }))
        })
    }
    fn __repr__(&self) -> String {
        format!(
            "PrimeCode(p={}, n={}, dim={}, generators={:?})",
            self.p,
            self.n,
            self.generators.len(),
            self.generators
        )
    }
}

#[pyfunction]
fn ternary_golay_code() -> PyPrimeCode {
    PyPrimeCode::ternary_golay()
}

#[pyfunction]
fn d16_plus() -> PyIntegralForm {
    PyIntegralForm {
        inner: crate::forms::d16_plus(),
    }
}

#[pyclass(name = "ScaleSymbol", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyScaleSymbol {
    inner: crate::forms::ScaleSymbol,
}

#[pymethods]
impl PyScaleSymbol {
    #[getter]
    fn scale(&self) -> u128 {
        self.inner.scale
    }
    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim
    }
    #[getter]
    fn sign(&self) -> i128 {
        self.inner.sign
    }
    #[getter]
    fn det_mod8(&self) -> i128 {
        self.inner.det_mod8
    }
    #[getter]
    fn type_ii(&self) -> bool {
        self.inner.type_ii
    }
    #[getter]
    fn oddity(&self) -> i128 {
        self.inner.oddity
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(name = "Genus", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyGenus {
    inner: crate::forms::Genus,
}

#[pymethods]
impl PyGenus {
    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim
    }
    #[getter]
    fn signature(&self) -> (usize, usize) {
        self.inner.signature
    }
    #[getter]
    fn det(&self) -> i128 {
        self.inner.det
    }
    fn primes(&self) -> Vec<u128> {
        self.inner.primes()
    }
    fn symbol_at(&self, p: u128) -> Vec<PyScaleSymbol> {
        self.inner
            .symbol_at(p)
            .iter()
            .cloned()
            .map(|inner| PyScaleSymbol { inner })
            .collect()
    }
    fn canonical_symbol_at(&self, p: u128) -> Vec<PyScaleSymbol> {
        self.inner
            .canonical_symbol_at(p)
            .into_iter()
            .map(|inner| PyScaleSymbol { inner })
            .collect()
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(name = "KneserNeighbor", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyKneserNeighbor {
    inner: crate::forms::KneserNeighbor,
}

#[pymethods]
impl PyKneserNeighbor {
    #[getter]
    fn prime(&self) -> u128 {
        self.inner.prime
    }
    #[getter]
    fn line(&self) -> Vec<u128> {
        self.inner.line.clone()
    }
    #[getter]
    fn lattice(&self) -> PyIntegralForm {
        PyIntegralForm {
            inner: self.inner.lattice.clone(),
        }
    }
    fn __repr__(&self) -> String {
        format!(
            "KneserNeighbor(p={}, line={:?}, dim={})",
            self.inner.prime,
            self.inner.line,
            self.inner.lattice.dim()
        )
    }
}

#[pyclass(name = "KneserMassClass", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyKneserMassClass {
    inner: crate::forms::KneserMassRecord,
}

#[pymethods]
impl PyKneserMassClass {
    #[getter]
    fn label(&self) -> &'static str {
        self.inner.label
    }
    #[getter]
    fn automorphism_group_order(&self) -> u128 {
        self.inner.automorphism_group_order
    }
    // The pyclass name is "KneserMassClass"; the core type is
    // `KneserMassRecord` — swap the leading name so Python users see the name
    // they imported.
    fn display(&self) -> String {
        self.inner
            .display()
            .replacen("KneserMassRecord", "KneserMassClass", 1)
    }
    fn __repr__(&self) -> String {
        self.display()
    }
}

#[pyclass(name = "KneserMassReport", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyKneserMassReport {
    inner: crate::forms::KneserMassInvariants,
}

#[pymethods]
impl PyKneserMassReport {
    #[getter]
    fn rank(&self) -> usize {
        self.inner.rank
    }
    #[getter]
    fn prime(&self) -> u128 {
        self.inner.prime
    }
    #[getter]
    fn seed_label(&self) -> &'static str {
        self.inner.seed_label
    }
    #[getter]
    fn generated_neighbor_count(&self) -> usize {
        self.inner.generated_neighbor_count
    }
    #[getter]
    fn generated_class_labels(&self) -> Vec<&'static str> {
        self.inner.generated_class_labels()
    }
    #[getter]
    fn classes(&self) -> Vec<PyKneserMassClass> {
        self.inner
            .classes
            .iter()
            .cloned()
            .map(|inner| PyKneserMassClass { inner })
            .collect()
    }
    #[getter]
    fn mass(&self) -> (i128, i128) {
        self.inner.mass
    }
    #[getter]
    fn mass_sum(&self) -> (i128, i128) {
        self.inner.mass_sum
    }
    #[getter]
    fn mass_closed(&self) -> bool {
        self.inner.mass_closed
    }
    // The pyclass name is "KneserMassReport"; the core type is
    // `KneserMassInvariants` — swap the leading name so Python users see the
    // name they imported.
    fn display(&self) -> String {
        self.inner
            .display()
            .replacen("KneserMassInvariants", "KneserMassReport", 1)
    }
    fn __repr__(&self) -> String {
        self.display()
    }
}

#[pyclass(name = "WeylVersorReport", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyWeylVersorReport {
    inner: crate::forms::WeylVersorInvariants,
}

#[pymethods]
impl PyWeylVersorReport {
    #[getter]
    fn kind(&self) -> String {
        self.inner.kind.to_string()
    }
    #[getter]
    fn rank(&self) -> usize {
        self.inner.rank
    }
    #[getter]
    fn weyl_group_order(&self) -> u128 {
        self.inner.weyl_group_order
    }
    #[getter]
    fn coxeter_number(&self) -> u128 {
        self.inner.coxeter_number
    }
    #[getter]
    fn simple_reflections_match_cartan(&self) -> bool {
        self.inner.simple_reflections_match_cartan
    }
    #[getter]
    fn simple_reflection_determinants_are_minus_one(&self) -> bool {
        self.inner.simple_reflection_determinants_are_minus_one
    }
    #[getter]
    fn coxeter_versor_order(&self) -> u128 {
        self.inner.coxeter_versor_order
    }
    #[getter]
    fn coxeter_order_matches(&self) -> bool {
        self.inner.coxeter_order_matches
    }
    #[getter]
    fn coxeter_versor_grade_parity(&self) -> Option<u128> {
        self.inner.coxeter_versor_grade_parity
    }
    fn display(&self) -> String {
        self.inner
            .display()
            .replacen("WeylVersorInvariants", "WeylVersorReport", 1)
    }
    fn __repr__(&self) -> String {
        self.display()
    }
}

#[pyclass(name = "IntegralForm", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyIntegralForm {
    inner: IntegralForm,
}

fn check_lattice_vec(l: &IntegralForm, v: &[i128], name: &str) -> PyResult<()> {
    if v.len() != l.dim() {
        Err(PyValueError::new_err(format!(
            "{name} has length {}, expected {}",
            v.len(),
            l.dim()
        )))
    } else {
        Ok(())
    }
}

#[pymethods]
impl PyIntegralForm {
    #[new]
    fn new(gram: Vec<Vec<i128>>) -> PyResult<Self> {
        IntegralForm::new(gram)
            .map(|inner| PyIntegralForm { inner })
            .ok_or_else(|| PyValueError::new_err("Gram matrix must be square and symmetric"))
    }
    #[staticmethod]
    fn diagonal(diag: Vec<i128>) -> PyIntegralForm {
        PyIntegralForm {
            inner: IntegralForm::diagonal(&diag),
        }
    }
    #[staticmethod]
    fn a(n: usize) -> PyResult<PyIntegralForm> {
        crate::forms::a_n(n)
            .map(|inner| PyIntegralForm { inner })
            .ok_or_else(|| PyValueError::new_err("A_n requires n >= 1"))
    }
    #[staticmethod]
    fn d(n: usize) -> PyResult<PyIntegralForm> {
        crate::forms::d_n(n)
            .map(|inner| PyIntegralForm { inner })
            .ok_or_else(|| PyValueError::new_err("D_n requires n >= 2"))
    }
    #[staticmethod]
    fn e6() -> PyIntegralForm {
        PyIntegralForm {
            inner: crate::forms::e_6(),
        }
    }
    #[staticmethod]
    fn e7() -> PyIntegralForm {
        PyIntegralForm {
            inner: crate::forms::e_7(),
        }
    }
    #[staticmethod]
    fn e8() -> PyIntegralForm {
        PyIntegralForm {
            inner: crate::forms::e_8(),
        }
    }
    #[staticmethod]
    fn leech() -> PyIntegralForm {
        PyIntegralForm {
            inner: crate::forms::leech(),
        }
    }
    #[getter]
    fn dim(&self) -> usize {
        self.inner.dim()
    }
    #[getter]
    fn gram(&self) -> Vec<Vec<i128>> {
        self.inner.gram().to_vec()
    }
    fn inner(&self, x: Vec<i128>, y: Vec<i128>) -> PyResult<i128> {
        check_lattice_vec(&self.inner, &x, "x")?;
        check_lattice_vec(&self.inner, &y, "y")?;
        Ok(self.inner.inner(&x, &y))
    }
    fn norm(&self, x: Vec<i128>) -> PyResult<i128> {
        check_lattice_vec(&self.inner, &x, "x")?;
        Ok(self.inner.norm(&x))
    }
    fn determinant(&self) -> i128 {
        self.inner.determinant()
    }
    fn is_unimodular(&self) -> bool {
        self.inner.is_unimodular()
    }
    fn is_even(&self) -> bool {
        self.inner.is_even()
    }
    fn is_positive_definite(&self) -> bool {
        self.inner.is_positive_definite()
    }
    fn signature(&self) -> (usize, usize) {
        self.inner.signature()
    }
    fn invariant_factors(&self) -> Vec<i128> {
        self.inner.invariant_factors()
    }
    fn level(&self) -> Option<i128> {
        self.inner.level()
    }
    fn direct_sum(&self, other: &PyIntegralForm) -> PyIntegralForm {
        PyIntegralForm {
            inner: self.inner.direct_sum(&other.inner),
        }
    }
    fn clifford_metric(&self) -> RationalAlgebra {
        let metric = self.inner.clifford_metric();
        RationalAlgebra {
            inner: Arc::new(CliffordAlgebra::new(metric.q.len(), metric)),
        }
    }
    fn clifford_metric_f2(&self) -> Option<NimberAlgebra> {
        self.inner.clifford_metric_f2().map(|metric| NimberAlgebra {
            inner: Arc::new(CliffordAlgebra::new(metric.q.len(), metric)),
        })
    }
    fn theta_series(&self, terms: usize) -> Option<Vec<i128>> {
        self.inner.theta_series(terms)
    }
    fn theta_series_level4(&self, terms: usize) -> Option<Vec<i128>> {
        self.inner.theta_series_level4(terms)
    }
    fn short_vectors(&self, bound: i128) -> Option<Vec<Vec<i128>>> {
        self.inner.short_vectors(bound)
    }
    fn minimum(&self) -> Option<i128> {
        self.inner.minimum()
    }
    fn minimal_vectors(&self) -> Option<Vec<Vec<i128>>> {
        self.inner.minimal_vectors()
    }
    fn kissing_number(&self) -> Option<usize> {
        self.inner.kissing_number()
    }
    fn automorphism_group_order(&self) -> Option<u128> {
        self.inner.automorphism_group_order()
    }
    fn automorphism_group_order_bounded(&self, node_budget: u128) -> Option<u128> {
        self.inner.automorphism_group_order_bounded(node_budget)
    }
    fn genus(&self) -> Option<PyGenus> {
        crate::forms::Genus::from_lattice(&self.inner).map(|inner| PyGenus { inner })
    }
    fn kneser_neighbor(&self, p: u128, line: Vec<u128>) -> Option<PyIntegralForm> {
        crate::forms::kneser_neighbor(&self.inner, p, &line).map(|inner| PyIntegralForm { inner })
    }
    fn kneser_neighbors(&self, p: u128, max_lines: u128) -> Option<Vec<PyKneserNeighbor>> {
        crate::forms::kneser_neighbors(&self.inner, p, max_lines).map(|neighbors| {
            neighbors
                .into_iter()
                .map(|inner| PyKneserNeighbor { inner })
                .collect()
        })
    }
    fn __repr__(&self) -> String {
        format!("IntegralForm(gram={:?})", self.inner.gram())
    }
}

#[pyclass(name = "FqmValueCount", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyFqmValueCount {
    inner: crate::forms::FqmValueCount,
}

#[pymethods]
impl PyFqmValueCount {
    #[getter]
    fn numer(&self) -> i128 {
        self.inner.numer
    }
    #[getter]
    fn denom(&self) -> i128 {
        self.inner.denom
    }
    #[getter]
    fn count(&self) -> u128 {
        self.inner.count
    }
    fn value(&self) -> PyRational {
        wrap_rational(Rational::new(self.inner.numer, self.inner.denom))
    }
    fn __repr__(&self) -> String {
        format!(
            "FqmValueCount(value={}/{}, count={})",
            self.inner.numer, self.inner.denom, self.inner.count
        )
    }
}

#[pyclass(name = "FqmPrimaryWittClass", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyFqmPrimaryWittClass {
    inner: crate::forms::FqmPrimaryWittClass,
}

#[pymethods]
impl PyFqmPrimaryWittClass {
    #[getter]
    fn prime(&self) -> u128 {
        self.inner.prime
    }
    #[getter]
    fn order(&self) -> u128 {
        self.inner.order
    }
    #[getter]
    fn core_order(&self) -> u128 {
        self.inner.core_order
    }
    #[getter]
    fn core_group(&self) -> Vec<u128> {
        self.inner.core_group.clone()
    }
    #[getter]
    fn core_exponent(&self) -> u128 {
        self.inner.core_exponent
    }
    #[getter]
    fn phase_mod8(&self) -> i128 {
        self.inner.phase_mod8
    }
    #[getter]
    fn q_value_counts(&self) -> Vec<PyFqmValueCount> {
        self.inner
            .q_value_counts
            .iter()
            .cloned()
            .map(|inner| PyFqmValueCount { inner })
            .collect()
    }
    #[getter]
    fn normal_form(&self) -> Vec<i128> {
        self.inner.normal_form.clone()
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(name = "FqmWittClass", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyFqmWittClass {
    inner: crate::forms::FqmWittClass,
}

#[pymethods]
impl PyFqmWittClass {
    #[getter]
    fn order(&self) -> u128 {
        self.inner.order
    }
    #[getter]
    fn phase_mod8(&self) -> i128 {
        self.inner.phase_mod8
    }
    #[getter]
    fn primary(&self) -> Vec<PyFqmPrimaryWittClass> {
        self.inner
            .primary
            .iter()
            .cloned()
            .map(|inner| PyFqmPrimaryWittClass { inner })
            .collect()
    }
    fn is_trivial(&self) -> bool {
        self.inner.is_trivial()
    }
    fn __eq__(&self, other: &PyFqmWittClass) -> bool {
        self.inner == other.inner
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(
    name = "NikulinPrimaryExistenceInvariants",
    module = "ogdoad",
    skip_from_py_object
)]
#[derive(Clone)]
struct PyNikulinPrimaryExistenceInvariants {
    inner: crate::forms::NikulinPrimaryExistenceInvariants,
}

#[pymethods]
impl PyNikulinPrimaryExistenceInvariants {
    #[getter]
    fn prime(&self) -> u128 {
        self.inner.prime
    }
    #[getter]
    fn order(&self) -> u128 {
        self.inner.order
    }
    #[getter]
    fn length(&self) -> usize {
        self.inner.length
    }
    #[getter]
    fn equality_case(&self) -> bool {
        self.inner.equality_case
    }
    #[getter]
    fn even_two_primary(&self) -> bool {
        self.inner.even_two_primary
    }
    #[getter]
    fn p_adic_discriminant(&self) -> Option<PyRational> {
        self.inner.p_adic_discriminant.clone().map(wrap_rational)
    }
    #[getter]
    fn determinant_condition_holds(&self) -> Option<bool> {
        self.inner.determinant_condition_holds
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(
    name = "NikulinExistenceObstruction",
    module = "ogdoad",
    skip_from_py_object
)]
#[derive(Clone)]
struct PyNikulinExistenceObstruction {
    inner: crate::forms::NikulinExistenceObstruction,
}

#[pymethods]
impl PyNikulinExistenceObstruction {
    fn kind(&self) -> &'static str {
        match self.inner {
            crate::forms::NikulinExistenceObstruction::SignatureCongruence { .. } => {
                "signature_congruence"
            }
            crate::forms::NikulinExistenceObstruction::RankTooSmall { .. } => "rank_too_small",
            crate::forms::NikulinExistenceObstruction::OddPrimeDeterminant { .. } => {
                "odd_prime_determinant"
            }
            crate::forms::NikulinExistenceObstruction::TwoAdicDeterminant { .. } => {
                "two_adic_determinant"
            }
        }
    }
    fn required_mod8(&self) -> Option<i128> {
        match self.inner {
            crate::forms::NikulinExistenceObstruction::SignatureCongruence {
                required_mod8,
                ..
            } => Some(required_mod8),
            _ => None,
        }
    }
    fn module_phase_mod8(&self) -> Option<i128> {
        match self.inner {
            crate::forms::NikulinExistenceObstruction::SignatureCongruence {
                module_phase_mod8,
                ..
            } => Some(module_phase_mod8),
            _ => None,
        }
    }
    fn prime(&self) -> Option<u128> {
        match self.inner {
            crate::forms::NikulinExistenceObstruction::RankTooSmall { prime, .. }
            | crate::forms::NikulinExistenceObstruction::OddPrimeDeterminant { prime, .. } => {
                Some(prime)
            }
            _ => None,
        }
    }
    fn rank(&self) -> Option<usize> {
        match self.inner {
            crate::forms::NikulinExistenceObstruction::RankTooSmall { rank, .. } => Some(rank),
            _ => None,
        }
    }
    fn length(&self) -> Option<usize> {
        match self.inner {
            crate::forms::NikulinExistenceObstruction::RankTooSmall { length, .. } => Some(length),
            _ => None,
        }
    }
    fn signed_order(&self) -> Option<i128> {
        match self.inner {
            crate::forms::NikulinExistenceObstruction::OddPrimeDeterminant {
                signed_order, ..
            } => Some(signed_order),
            _ => None,
        }
    }
    fn order(&self) -> Option<u128> {
        match self.inner {
            crate::forms::NikulinExistenceObstruction::TwoAdicDeterminant { order, .. } => {
                Some(order)
            }
            _ => None,
        }
    }
    fn p_adic_discriminant(&self) -> Option<PyRational> {
        match &self.inner {
            crate::forms::NikulinExistenceObstruction::OddPrimeDeterminant {
                p_adic_discriminant,
                ..
            }
            | crate::forms::NikulinExistenceObstruction::TwoAdicDeterminant {
                p_adic_discriminant,
                ..
            } => Some(wrap_rational(p_adic_discriminant.clone())),
            _ => None,
        }
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(
    name = "NikulinExistenceInvariants",
    module = "ogdoad",
    skip_from_py_object
)]
#[derive(Clone)]
struct PyNikulinExistenceInvariants {
    inner: crate::forms::NikulinExistenceInvariants,
}

#[pymethods]
impl PyNikulinExistenceInvariants {
    #[getter]
    fn signature(&self) -> (usize, usize) {
        self.inner.signature
    }
    #[getter]
    fn rank(&self) -> usize {
        self.inner.rank
    }
    #[getter]
    fn module_phase_mod8(&self) -> i128 {
        self.inner.module_phase_mod8
    }
    #[getter]
    fn primary(&self) -> Vec<PyNikulinPrimaryExistenceInvariants> {
        self.inner
            .primary
            .iter()
            .cloned()
            .map(|inner| PyNikulinPrimaryExistenceInvariants { inner })
            .collect()
    }
    #[getter]
    fn obstruction(&self) -> Option<PyNikulinExistenceObstruction> {
        self.inner
            .obstruction
            .clone()
            .map(|inner| PyNikulinExistenceObstruction { inner })
    }
    fn exists(&self) -> bool {
        self.inner.exists()
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(name = "FiniteQuadraticModule", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyFiniteQuadraticModule {
    inner: crate::forms::FiniteQuadraticModule,
}

#[pymethods]
impl PyFiniteQuadraticModule {
    #[new]
    fn new(cyclic_factors: Vec<u128>, q_values_mod2: Vec<Bound<'_, PyAny>>) -> PyResult<Self> {
        let q_values_mod2 = q_values_mod2
            .iter()
            .map(parse_rational)
            .collect::<PyResult<Vec<_>>>()?;
        crate::forms::FiniteQuadraticModule::new(cyclic_factors, q_values_mod2)
            .map(|inner| PyFiniteQuadraticModule { inner })
            .ok_or_else(|| {
                PyValueError::new_err("invalid, singular, or over-budget finite quadratic module")
            })
    }
    #[staticmethod]
    fn cyclic(order: u128, generator_q: &Bound<'_, PyAny>) -> PyResult<Self> {
        crate::forms::FiniteQuadraticModule::cyclic(order, parse_rational(generator_q)?)
            .map(|inner| PyFiniteQuadraticModule { inner })
            .ok_or_else(|| {
                PyValueError::new_err(
                    "invalid, singular, or over-budget cyclic finite quadratic module",
                )
            })
    }
    fn direct_sum(&self, other: &PyFiniteQuadraticModule) -> Option<Self> {
        self.inner
            .direct_sum(&other.inner)
            .map(|inner| PyFiniteQuadraticModule { inner })
    }
    #[getter]
    fn order(&self) -> u128 {
        self.inner.order()
    }
    #[getter]
    fn cyclic_factors(&self) -> Vec<u128> {
        self.inner.cyclic_factors().to_vec()
    }
    #[getter]
    fn q_values_mod2(&self) -> Vec<PyRational> {
        self.inner
            .q_values_mod2()
            .iter()
            .cloned()
            .map(wrap_rational)
            .collect()
    }
    fn witt_class(&self) -> Option<PyFqmWittClass> {
        self.inner
            .witt_class()
            .map(|inner| PyFqmWittClass { inner })
    }
    fn nikulin_existence_report(
        &self,
        signature: (usize, usize),
    ) -> Option<PyNikulinExistenceInvariants> {
        self.inner
            .nikulin_existence_report(signature)
            .map(|inner| PyNikulinExistenceInvariants { inner })
    }
    fn nikulin_even_lattice_exists(&self, signature: (usize, usize)) -> Option<bool> {
        self.inner.nikulin_even_lattice_exists(signature)
    }
    fn __eq__(&self, other: &PyFiniteQuadraticModule) -> bool {
        self.inner == other.inner
    }
    fn __repr__(&self) -> String {
        let values = self
            .inner
            .q_values_mod2()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        format!(
            "FiniteQuadraticModule(cyclic_factors={:?}, q_values_mod2={values:?})",
            self.inner.cyclic_factors()
        )
    }
}

#[pyclass(name = "DiscriminantForm", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyDiscriminantForm {
    inner: crate::forms::DiscriminantForm,
}

fn check_disc_vec(d: &crate::forms::DiscriminantForm, v: &[i128], name: &str) -> PyResult<()> {
    let dim = d.gram_inv().len();
    if v.len() != dim {
        Err(PyValueError::new_err(format!(
            "{name} has length {}, expected {}",
            v.len(),
            dim
        )))
    } else {
        Ok(())
    }
}

#[pymethods]
impl PyDiscriminantForm {
    #[staticmethod]
    fn from_lattice(lattice: &PyIntegralForm) -> Option<Self> {
        crate::forms::DiscriminantForm::from_lattice(&lattice.inner)
            .map(|inner| PyDiscriminantForm { inner })
    }
    #[getter]
    fn group(&self) -> Vec<i128> {
        self.inner.group().to_vec()
    }
    #[getter]
    fn reps(&self) -> Vec<Vec<i128>> {
        self.inner.reps().to_vec()
    }
    #[getter]
    fn gram_inv(&self) -> Vec<Vec<PyRational>> {
        self.inner
            .gram_inv()
            .iter()
            .map(|row| row.iter().cloned().map(wrap_rational).collect())
            .collect()
    }
    fn quadratic_value_mod2(&self, y: Vec<i128>) -> PyResult<PyRational> {
        check_disc_vec(&self.inner, &y, "y")?;
        Ok(wrap_rational(self.inner.quadratic_value_mod2(&y)))
    }
    fn bilinear_value_mod1(&self, y: Vec<i128>, z: Vec<i128>) -> PyResult<PyRational> {
        check_disc_vec(&self.inner, &y, "y")?;
        check_disc_vec(&self.inner, &z, "z")?;
        Ok(wrap_rational(self.inner.bilinear_value_mod1(&y, &z)))
    }
    fn gauss_sum(&self) -> PyGaussSum {
        PyGaussSum {
            inner: self.inner.gauss_sum(),
        }
    }
    fn milgram_signature_mod8(&self) -> Option<i128> {
        self.inner.milgram_signature_mod8()
    }
    fn brown_invariant(&self) -> Option<PyBrownInvariants> {
        self.inner.brown_invariant().map(wrap_brown_result)
    }
    fn is_isomorphic(&self, other: &PyDiscriminantForm) -> Option<bool> {
        self.inner.is_isomorphic(&other.inner)
    }
    fn is_isomorphic_bounded(&self, other: &PyDiscriminantForm, node_budget: u128) -> Option<bool> {
        self.inner.is_isomorphic_bounded(&other.inner, node_budget)
    }
    fn fqm_witt_class(&self) -> Option<PyFqmWittClass> {
        self.inner
            .fqm_witt_class()
            .map(|inner| PyFqmWittClass { inner })
    }
    fn is_fqm_witt_equivalent(&self, other: &PyDiscriminantForm) -> Option<bool> {
        self.inner.is_fqm_witt_equivalent(&other.inner)
    }
    fn nikulin_existence_report(
        &self,
        signature: (usize, usize),
    ) -> Option<PyNikulinExistenceInvariants> {
        self.inner
            .nikulin_existence_report(signature)
            .map(|inner| PyNikulinExistenceInvariants { inner })
    }
    fn nikulin_even_lattice_exists(&self, signature: (usize, usize)) -> Option<bool> {
        self.inner.nikulin_even_lattice_exists(signature)
    }
    fn weil_t(&self) -> Vec<PyComplex64> {
        self.inner
            .weil_t()
            .into_iter()
            .map(wrap_complex64)
            .collect()
    }
    fn weil_s_prefactor_phase_mod8(&self) -> Option<i128> {
        self.inner.weil_s_prefactor_phase_mod8()
    }
    fn weil_s_recovers_milgram_phase_mod8(&self) -> Option<i128> {
        self.inner.weil_s_recovers_milgram_phase_mod8()
    }
    fn weil_s(&self) -> Option<Vec<Vec<PyComplex64>>> {
        self.inner.weil_s().map(|rows| {
            rows.into_iter()
                .map(|row| row.into_iter().map(wrap_complex64).collect())
                .collect()
        })
    }
    fn verify_weil_relations(&self) -> bool {
        self.inner.verify_weil_relations()
    }
    fn __repr__(&self) -> String {
        format!(
            "DiscriminantForm(group={:?}, reps={:?})",
            self.inner.group(),
            self.inner.reps()
        )
    }
}

#[pyclass(name = "OddDiscriminantForm", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyOddDiscriminantForm {
    inner: crate::forms::OddDiscriminantForm,
}

fn check_odd_disc_vec(
    d: &crate::forms::OddDiscriminantForm,
    v: &[i128],
    name: &str,
) -> PyResult<()> {
    let dim = d.gram_inv().len();
    if v.len() != dim {
        Err(PyValueError::new_err(format!(
            "{name} has length {}, expected {}",
            v.len(),
            dim
        )))
    } else {
        Ok(())
    }
}

#[pymethods]
impl PyOddDiscriminantForm {
    #[staticmethod]
    fn from_lattice(lattice: &PyIntegralForm) -> Option<Self> {
        crate::forms::OddDiscriminantForm::from_lattice(&lattice.inner)
            .map(|inner| PyOddDiscriminantForm { inner })
    }
    #[getter]
    fn group(&self) -> Vec<i128> {
        self.inner.group().to_vec()
    }
    #[getter]
    fn reps(&self) -> Vec<Vec<i128>> {
        self.inner.reps().to_vec()
    }
    #[getter]
    fn gram_inv(&self) -> Vec<Vec<PyRational>> {
        self.inner
            .gram_inv()
            .iter()
            .map(|row| row.iter().cloned().map(wrap_rational).collect())
            .collect()
    }
    fn quadratic_value_mod1(&self, y: Vec<i128>) -> PyResult<PyRational> {
        check_odd_disc_vec(&self.inner, &y, "y")?;
        Ok(wrap_rational(self.inner.quadratic_value_mod1(&y)))
    }
    fn bilinear_value_mod1(&self, y: Vec<i128>, z: Vec<i128>) -> PyResult<PyRational> {
        check_odd_disc_vec(&self.inner, &y, "y")?;
        check_odd_disc_vec(&self.inner, &z, "z")?;
        Ok(wrap_rational(self.inner.bilinear_value_mod1(&y, &z)))
    }
    fn gauss_sum(&self) -> PyGaussSum {
        PyGaussSum {
            inner: self.inner.gauss_sum(),
        }
    }
    fn gauss_phase_mod8(&self) -> Option<i128> {
        self.inner.gauss_phase_mod8()
    }
    fn __repr__(&self) -> String {
        format!(
            "OddDiscriminantForm(group={:?}, reps={:?})",
            self.inner.group(),
            self.inner.reps()
        )
    }
}

#[pyclass(name = "OddMilgramReport", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyOddMilgramReport {
    inner: crate::forms::OddMilgramInvariants,
}

#[pymethods]
impl PyOddMilgramReport {
    #[getter]
    fn signature_mod8(&self) -> i128 {
        self.inner.signature_mod8
    }
    #[getter]
    fn oddity_mod8(&self) -> i128 {
        self.inner.oddity_mod8
    }
    #[getter]
    fn p_excess_mod8(&self) -> i128 {
        self.inner.p_excess_mod8
    }
    #[getter]
    fn corrected_signature_mod8(&self) -> i128 {
        self.inner.corrected_signature_mod8
    }
    #[getter]
    fn genus_signature_mod8(&self) -> i128 {
        self.inner.genus_signature_mod8
    }
    fn verified(&self) -> bool {
        self.inner.verified()
    }
    // The pyclass name is "OddMilgramReport"; the core type is
    // `OddMilgramInvariants` — swap the leading name so Python users see the
    // name they imported.
    fn display(&self) -> String {
        self.inner
            .display()
            .replacen("OddMilgramInvariants", "OddMilgramReport", 1)
    }
    fn __repr__(&self) -> String {
        self.display()
    }
}

#[pyfunction]
fn verify_milgram(lattice: &PyIntegralForm) -> Option<bool> {
    crate::forms::verify_milgram(&lattice.inner)
}

#[pyfunction]
fn odd_milgram_report(lattice: &PyIntegralForm) -> Option<PyOddMilgramReport> {
    crate::forms::odd_milgram_report(&lattice.inner).map(|inner| PyOddMilgramReport { inner })
}

#[pyfunction]
fn verify_odd_milgram(lattice: &PyIntegralForm) -> Option<bool> {
    crate::forms::verify_odd_milgram(&lattice.inner)
}

#[pyfunction]
fn genus_signature_mod8(lattice: &PyIntegralForm) -> Option<i128> {
    crate::forms::genus_signature_mod8(&lattice.inner)
}

#[pyfunction]
fn a_n(n: usize) -> PyResult<PyIntegralForm> {
    PyIntegralForm::a(n)
}

#[pyfunction]
fn d_n(n: usize) -> PyResult<PyIntegralForm> {
    PyIntegralForm::d(n)
}

#[pyfunction]
fn e_6() -> PyIntegralForm {
    PyIntegralForm::e6()
}

#[pyfunction]
fn e_7() -> PyIntegralForm {
    PyIntegralForm::e7()
}

#[pyfunction]
fn e_8() -> PyIntegralForm {
    PyIntegralForm::e8()
}

#[pyfunction]
fn leech() -> PyIntegralForm {
    PyIntegralForm::leech()
}

#[pyfunction]
fn coxeter_number(lattice: &PyIntegralForm) -> Option<i128> {
    crate::forms::coxeter_number(&lattice.inner)
}

#[pyfunction]
fn is_root_lattice(lattice: &PyIntegralForm) -> bool {
    crate::forms::is_root_lattice(&lattice.inner)
}

#[pyfunction]
fn are_in_same_genus(a: &PyIntegralForm, b: &PyIntegralForm) -> bool {
    crate::forms::are_in_same_genus(&a.inner, &b.inner)
}

#[pyfunction]
fn mass_even_unimodular(n: u128) -> Option<(i128, i128)> {
    crate::forms::mass_even_unimodular(n)
}

#[pyfunction]
fn isotropic_lines_mod_p(
    lattice: &PyIntegralForm,
    p: u128,
    max_lines: u128,
) -> Option<Vec<Vec<u128>>> {
    crate::forms::isotropic_lines_mod_p(&lattice.inner, p, max_lines)
}

#[pyfunction]
fn kneser_neighbor(lattice: &PyIntegralForm, p: u128, line: Vec<u128>) -> Option<PyIntegralForm> {
    crate::forms::kneser_neighbor(&lattice.inner, p, &line).map(|inner| PyIntegralForm { inner })
}

#[pyfunction]
fn kneser_neighbors(
    lattice: &PyIntegralForm,
    p: u128,
    max_lines: u128,
) -> Option<Vec<PyKneserNeighbor>> {
    crate::forms::kneser_neighbors(&lattice.inner, p, max_lines).map(|neighbors| {
        neighbors
            .into_iter()
            .map(|inner| PyKneserNeighbor { inner })
            .collect()
    })
}

#[pyfunction]
fn even_unimodular_kneser_report(rank: usize) -> Option<PyKneserMassReport> {
    crate::forms::even_unimodular_kneser_report(rank).map(|inner| PyKneserMassReport { inner })
}

#[pyfunction]
fn weyl_versor_report(family: &str, rank: usize) -> PyResult<Option<PyWeylVersorReport>> {
    let kind = match family {
        "A" | "a" => {
            if rank < 1 {
                return Err(PyValueError::new_err("A_n requires rank >= 1"));
            }
            crate::forms::NiemeierComponentKind::A(rank)
        }
        "D" | "d" => {
            if rank < 2 {
                return Err(PyValueError::new_err("D_n requires rank >= 2"));
            }
            crate::forms::NiemeierComponentKind::D(rank)
        }
        "E" | "e" => match rank {
            6 => crate::forms::NiemeierComponentKind::E6,
            7 => crate::forms::NiemeierComponentKind::E7,
            8 => crate::forms::NiemeierComponentKind::E8,
            _ => {
                return Err(PyValueError::new_err(
                    "E_n is supported only for n = 6, 7, 8",
                ))
            }
        },
        _ => {
            return Err(PyValueError::new_err(
                "family must be one of 'A', 'D', or 'E'",
            ))
        }
    };
    Ok(crate::forms::weyl_versor_report(kind).map(|inner| PyWeylVersorReport { inner }))
}

#[pyfunction]
fn leech_aut_order() -> u128 {
    crate::forms::LEECH_AUT_ORDER
}

#[pyclass(name = "NiemeierRootComponent", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyNiemeierRootComponent {
    inner: crate::forms::NiemeierRootComponent,
}

#[pymethods]
impl PyNiemeierRootComponent {
    #[getter]
    fn kind(&self) -> String {
        self.inner.kind.to_string()
    }
    #[getter]
    fn family(&self) -> &'static str {
        match self.inner.kind {
            crate::forms::NiemeierComponentKind::A(_) => "A",
            crate::forms::NiemeierComponentKind::D(_) => "D",
            crate::forms::NiemeierComponentKind::E6
            | crate::forms::NiemeierComponentKind::E7
            | crate::forms::NiemeierComponentKind::E8 => "E",
        }
    }
    #[getter]
    fn rank(&self) -> usize {
        self.inner.kind.rank()
    }
    #[getter]
    fn multiplicity(&self) -> usize {
        self.inner.multiplicity
    }
    fn coxeter_number(&self) -> Option<u128> {
        self.inner.kind.coxeter_number()
    }
    fn root_count(&self) -> Option<u128> {
        self.inner
            .kind
            .root_count()?
            .checked_mul(self.inner.multiplicity as u128)
    }
    fn determinant(&self) -> Option<u128> {
        self.inner.kind.determinant()
    }
    fn weyl_group_order(&self) -> Option<u128> {
        self.inner.kind.weyl_group_order()
    }
    fn root_lattice(&self) -> Option<PyIntegralForm> {
        self.inner
            .kind
            .root_lattice()
            .map(|inner| PyIntegralForm { inner })
    }
    fn __repr__(&self) -> String {
        format!(
            "NiemeierRootComponent(kind={}, multiplicity={})",
            self.inner.kind, self.inner.multiplicity
        )
    }
}

#[pyclass(name = "NiemeierRecord", module = "ogdoad", skip_from_py_object)]
#[derive(Clone)]
struct PyNiemeierRecord {
    inner: crate::forms::NiemeierRecord,
}

#[pymethods]
impl PyNiemeierRecord {
    #[getter]
    fn label(&self) -> &'static str {
        self.inner.label()
    }
    #[getter]
    fn components(&self) -> Vec<PyNiemeierRootComponent> {
        self.inner
            .components()
            .iter()
            .copied()
            .map(|inner| PyNiemeierRootComponent { inner })
            .collect()
    }
    #[getter]
    fn coxeter_number(&self) -> u128 {
        self.inner.coxeter_number()
    }
    #[getter]
    fn glue_code_order(&self) -> Option<u128> {
        self.inner.glue_code_order()
    }
    #[getter]
    fn automorphism_quotient_order(&self) -> u128 {
        self.inner.automorphism_quotient_order()
    }
    fn root_rank(&self) -> usize {
        self.inner.root_rank()
    }
    fn root_count(&self) -> u128 {
        self.inner.root_count()
    }
    fn root_discriminant(&self) -> Option<u128> {
        self.inner.root_discriminant()
    }
    fn reflection_group_order(&self) -> Option<u128> {
        self.inner.reflection_group_order()
    }
    fn automorphism_group_order(&self) -> Option<u128> {
        self.inner.automorphism_group_order()
    }
    fn root_lattice(&self) -> Option<PyIntegralForm> {
        self.inner
            .root_lattice()
            .map(|inner| PyIntegralForm { inner })
    }
    fn theta_series(&self, terms: usize) -> Vec<PyRational> {
        self.inner
            .theta_series(terms)
            .into_iter()
            .map(wrap_rational)
            .collect()
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyfunction]
fn niemeier_classes() -> Vec<PyNiemeierRecord> {
    crate::forms::niemeier_classes()
        .iter()
        .copied()
        .map(|inner| PyNiemeierRecord { inner })
        .collect()
}

#[pyfunction]
fn niemeier_mass_sum() -> Option<PyRational> {
    crate::forms::niemeier_mass_sum().map(wrap_rational)
}

#[pyfunction]
fn niemeier_weighted_theta_average(terms: usize) -> Option<Vec<PyRational>> {
    crate::forms::niemeier_weighted_theta_average(terms)
        .map(|values| values.into_iter().map(wrap_rational).collect())
}

#[pyfunction]
fn qexp_from_int(coeffs: Vec<i128>) -> Vec<PyRational> {
    crate::forms::qexp_from_int(&coeffs)
        .into_iter()
        .map(wrap_rational)
        .collect()
}

#[pyfunction]
fn eisenstein_e4(terms: usize) -> Vec<PyRational> {
    crate::forms::eisenstein_e4(terms)
        .into_iter()
        .map(wrap_rational)
        .collect()
}

#[pyfunction]
fn eisenstein_e6(terms: usize) -> Vec<PyRational> {
    crate::forms::eisenstein_e6(terms)
        .into_iter()
        .map(wrap_rational)
        .collect()
}

#[pyfunction]
fn eisenstein_e12(terms: usize) -> Vec<PyRational> {
    crate::forms::eisenstein_e12(terms)
        .into_iter()
        .map(wrap_rational)
        .collect()
}

#[pyfunction]
fn delta(terms: usize) -> Vec<PyRational> {
    crate::forms::delta(terms)
        .into_iter()
        .map(wrap_rational)
        .collect()
}

#[pyfunction]
fn mk_basis(weight: usize, terms: usize) -> Vec<Vec<PyRational>> {
    crate::forms::mk_basis(weight, terms)
        .into_iter()
        .map(|row| row.into_iter().map(wrap_rational).collect())
        .collect()
}

#[pyfunction]
fn as_modular_form(
    q_expansion: Vec<Bound<'_, PyAny>>,
    weight: usize,
    terms: usize,
) -> PyResult<Option<Vec<PyRational>>> {
    let q_expansion = parse_rational_vec(q_expansion)?;
    Ok(crate::forms::as_modular_form(&q_expansion, weight, terms)
        .map(|coords| coords.into_iter().map(wrap_rational).collect()))
}

#[pyfunction]
fn modular_qexp_add(
    a: Vec<Bound<'_, PyAny>>,
    b: Vec<Bound<'_, PyAny>>,
    terms: usize,
) -> PyResult<Vec<PyRational>> {
    let a = parse_rational_vec(a)?;
    let b = parse_rational_vec(b)?;
    Ok(crate::forms::modular_qexp_add(&a, &b, terms)
        .into_iter()
        .map(wrap_rational)
        .collect())
}

#[pyfunction]
fn modular_qexp_sub(
    a: Vec<Bound<'_, PyAny>>,
    b: Vec<Bound<'_, PyAny>>,
    terms: usize,
) -> PyResult<Vec<PyRational>> {
    let a = parse_rational_vec(a)?;
    let b = parse_rational_vec(b)?;
    Ok(crate::forms::modular_qexp_sub(&a, &b, terms)
        .into_iter()
        .map(wrap_rational)
        .collect())
}

#[pyfunction]
fn modular_qexp_mul(
    a: Vec<Bound<'_, PyAny>>,
    b: Vec<Bound<'_, PyAny>>,
    terms: usize,
) -> PyResult<Vec<PyRational>> {
    let a = parse_rational_vec(a)?;
    let b = parse_rational_vec(b)?;
    Ok(crate::forms::modular_qexp_mul(&a, &b, terms)
        .into_iter()
        .map(wrap_rational)
        .collect())
}

#[pyfunction]
fn modular_qexp_scale(
    a: Vec<Bound<'_, PyAny>>,
    c: &Bound<'_, PyAny>,
    terms: usize,
) -> PyResult<Vec<PyRational>> {
    let a = parse_rational_vec(a)?;
    let c = parse_rational(c)?;
    Ok(crate::forms::modular_qexp_scale(&a, c, terms)
        .into_iter()
        .map(wrap_rational)
        .collect())
}

// ---------------------------------------------------------------------------
// Brauer–Wall group
// ---------------------------------------------------------------------------

#[pyclass(name = "BrauerWallClass", module = "ogdoad", from_py_object)]
#[derive(Clone)]
struct PyBrauerWallClass {
    inner: crate::forms::BrauerWallClass,
}

#[pymethods]
impl PyBrauerWallClass {
    #[staticmethod]
    fn real(index: u128) -> PyBrauerWallClass {
        PyBrauerWallClass {
            inner: crate::forms::BrauerWallClass::Real(index % 8),
        }
    }
    #[staticmethod]
    fn complex(parity: u128) -> PyResult<PyBrauerWallClass> {
        check_bit("parity", parity)?;
        Ok(PyBrauerWallClass {
            inner: crate::forms::BrauerWallClass::Complex(parity),
        })
    }
    #[staticmethod]
    fn oddchar(
        field_order: u128,
        kappa: u128,
        e0: u128,
        sclass: u128,
    ) -> PyResult<PyBrauerWallClass> {
        check_bit("kappa", kappa)?;
        check_bit("e0", e0)?;
        check_bit("sclass", sclass)?;
        Ok(PyBrauerWallClass {
            inner: crate::forms::BrauerWallClass::OddChar {
                field_order,
                kappa,
                e0,
                sclass,
            },
        })
    }
    #[staticmethod]
    #[pyo3(signature = (arf, field_degree=1))]
    fn char2(arf: u128, field_degree: u128) -> PyResult<PyBrauerWallClass> {
        check_bit("arf", arf)?;
        check_positive_field_degree(field_degree)?;
        Ok(PyBrauerWallClass {
            inner: crate::forms::BrauerWallClass::Char2 { field_degree, arf },
        })
    }
    fn kind(&self) -> &'static str {
        match self.inner {
            crate::forms::BrauerWallClass::Real(_) => "real",
            crate::forms::BrauerWallClass::Complex(_) => "complex",
            crate::forms::BrauerWallClass::OddChar { .. } => "oddchar",
            crate::forms::BrauerWallClass::Char2 { .. } => "char2",
        }
    }
    fn index(&self) -> Option<u128> {
        match self.inner {
            crate::forms::BrauerWallClass::Real(s) => Some(s),
            _ => None,
        }
    }
    fn parity(&self) -> Option<u128> {
        match self.inner {
            crate::forms::BrauerWallClass::Complex(p) => Some(p),
            _ => None,
        }
    }
    fn field_order(&self) -> Option<u128> {
        match self.inner {
            crate::forms::BrauerWallClass::OddChar { field_order, .. } => Some(field_order),
            _ => None,
        }
    }
    fn field_degree(&self) -> Option<u128> {
        match self.inner {
            crate::forms::BrauerWallClass::Char2 { field_degree, .. } => Some(field_degree),
            _ => None,
        }
    }
    fn kappa(&self) -> Option<u128> {
        match self.inner {
            crate::forms::BrauerWallClass::OddChar { kappa, .. } => Some(kappa),
            _ => None,
        }
    }
    fn e0(&self) -> Option<u128> {
        match self.inner {
            crate::forms::BrauerWallClass::OddChar { e0, .. } => Some(e0),
            _ => None,
        }
    }
    fn sclass(&self) -> Option<u128> {
        match self.inner {
            crate::forms::BrauerWallClass::OddChar { sclass, .. } => Some(sclass),
            _ => None,
        }
    }
    fn arf(&self) -> Option<u128> {
        match self.inner {
            crate::forms::BrauerWallClass::Char2 { arf, .. } => Some(arf),
            _ => None,
        }
    }
    fn zero_like(&self) -> PyBrauerWallClass {
        PyBrauerWallClass {
            inner: self.inner.zero_like(),
        }
    }
    fn __add__(&self, other: &PyBrauerWallClass) -> PyResult<PyBrauerWallClass> {
        self.inner
            .try_add(&other.inner)
            .map(|inner| PyBrauerWallClass { inner })
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }
    fn __eq__(&self, other: &PyBrauerWallClass) -> bool {
        self.inner == other.inner
    }
    fn display(&self) -> String {
        self.inner.display()
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

/// The Brauer–Wall class of a surreal Clifford algebra on the exact-square
/// real-table subdomain: the Bott index `s = (q − p) mod 8`.
#[pyfunction]
fn bw_class_real(alg: &SurrealAlgebra) -> PyResult<PyBrauerWallClass> {
    crate::forms::bw_class_real(&alg.inner.metric)
        .map(|c| PyBrauerWallClass { inner: c })
        .ok_or_else(|| {
            PyValueError::new_err("metric is outside the exact-square real-table subdomain")
        })
}

/// The Brauer–Wall class of a surcomplex (complex) Clifford algebra in
/// `BW(ℂ) ≅ ℤ/2` (the dimension parity).
#[pyfunction]
fn bw_class_complex(alg: &SurcomplexAlgebra) -> PyResult<PyBrauerWallClass> {
    crate::forms::bw_class_complex(&alg.inner.metric)
        .map(|c| PyBrauerWallClass { inner: c })
        .ok_or_else(|| PyValueError::new_err("Brauer–Wall class needs a diagonal metric"))
}

/// The rational Brauer-Wall class of a rational Clifford algebra, projected to
/// dimension parity, signed discriminant, and the ungraded Clifford Brauer class.
#[pyfunction]
fn bw_class_rational(alg: &RationalAlgebra) -> PyResult<PyRationalBrauerWallClass> {
    crate::forms::bw_class_rational(&alg.inner.metric)
        .map(|inner| PyRationalBrauerWallClass { inner })
        .ok_or_else(|| {
            PyValueError::new_err(
                "rational Brauer-Wall class needs a diagonalizable metric with bounded i128 square classes",
            )
        })
}

/// The Brauer-Wall class of a nonsingular nimber Clifford algebra in
/// `BW(F_{2^m}) ≅ W_q(F_{2^m}) ≅ Z/2` (the Arf/Witt class).
#[pyfunction]
fn bw_class_nimber(alg: &NimberAlgebra) -> PyResult<PyBrauerWallClass> {
    crate::forms::bw_class_nimber(&alg.inner.metric)
        .map(|c| PyBrauerWallClass { inner: c })
        .ok_or_else(|| {
            PyValueError::new_err(
                "char-2 Brauer-Wall class needs a nonsingular non-general-bilinear nimber metric",
            )
        })
}

/// The Brauer-Wall class of a nonsingular ordinal-nimber Clifford metric on the
/// detected finite ordinal windows.
#[pyfunction]
fn bw_class_ordinal(alg: &OrdinalAlgebra) -> PyResult<PyBrauerWallClass> {
    <Ordinal as crate::forms::ClassifyBrauerWall>::bw_class(&alg.inner.metric)
        .map(|inner| PyBrauerWallClass { inner })
        .map_err(|e| PyValueError::new_err(e.to_string()))
}

pub(crate) fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyArfInvariants>()?;
    m.add_class::<PyBrownInvariants>()?;
    m.add_class::<PyQuadricFit>()?;
    m.add_class::<PyExtraspecialElement>()?;
    m.add_class::<PyExtraspecial2Group>()?;
    m.add_class::<PyHeisenbergWeilRepresentation>()?;
    m.add_class::<PyBaseField>()?;
    m.add_class::<PyRationalPlace>()?;
    m.add_class::<PyCliffordInvariants>()?;
    m.add_class::<PyRationalPlaceInvariant>()?;
    m.add_class::<PyRationalCliffordInvariants>()?;
    m.add_class::<PyFiniteFieldInvariants>()?;
    m.add_class::<PyFiniteFieldNumericInvariants>()?;
    m.add_class::<PyChar2SymmetryFactorization>()?;
    m.add_class::<PyWittClassError>()?;
    m.add_class::<PyWittClass>()?;
    m.add_class::<PyOddCharInvariants>()?;
    m.add_class::<PyOddFiniteFieldForm>()?;
    m.add_class::<PyChar2FiniteFieldForm>()?;
    m.add_class::<PyFunctionFieldPlace>()?;
    m.add_class::<PyFunctionFieldLocalIsotropy>()?;
    m.add_class::<PyFunctionFieldAdelicIsotropy>()?;
    m.add_class::<PyChar2PsiTerm>()?;
    m.add_class::<PyChar2LocalDecomp>()?;
    m.add_class::<PyChar2FunctionFieldForm>()?;
    m.add_class::<PyWittClassG>()?;
    m.add_class::<PySymplecticInvariants>()?;
    m.add_class::<PySymplecticForm>()?;
    m.add_class::<PyHermitianSignature>()?;
    m.add_class::<PyHermitianForm>()?;
    m.add_class::<PyFiniteHermitianInvariants>()?;
    m.add_class::<PyFiniteHermitianForm>()?;
    m.add_class::<PyResidueForm>()?;
    m.add_class::<PySpringerDecomp>()?;
    m.add_class::<PyLocalResidueForm>()?;
    m.add_class::<PyLocalSpringerDecomp>()?;
    m.add_class::<PyBrauer2Class>()?;
    m.add_class::<PyBrauerClass>()?;
    m.add_class::<PyRationalBrauerWallClass>()?;
    m.add_class::<PyFunctionFieldBrauer2Class>()?;
    m.add_class::<PyFunctionFieldBrauerWallClass>()?;
    m.add_class::<PyBrauerWallClass>()?;
    m.add_class::<PyRealWittDecomp>()?;
    m.add_class::<PyOddWittDecomp>()?;
    m.add_class::<PyChar2WittDecomp>()?;
    m.add_class::<PyEnStaircase>()?;
    m.add_class::<PyAdelicIsotropy>()?;
    m.add_class::<PyComplex64>()?;
    m.add_class::<PyGaussSum>()?;
    m.add_class::<PyBinaryCode>()?;
    m.add_class::<PyCliffordBarnesWall16Report>()?;
    m.add_class::<PyPrimeCode>()?;
    m.add_class::<PyIntegralForm>()?;
    m.add_class::<PyFiniteQuadraticModule>()?;
    m.add_class::<PyFqmValueCount>()?;
    m.add_class::<PyFqmPrimaryWittClass>()?;
    m.add_class::<PyFqmWittClass>()?;
    m.add_class::<PyNikulinPrimaryExistenceInvariants>()?;
    m.add_class::<PyNikulinExistenceObstruction>()?;
    m.add_class::<PyNikulinExistenceInvariants>()?;
    m.add_class::<PyNiemeierRootComponent>()?;
    m.add_class::<PyNiemeierRecord>()?;
    m.add_class::<PyScaleSymbol>()?;
    m.add_class::<PyGenus>()?;
    m.add_class::<PyKneserNeighbor>()?;
    m.add_class::<PyKneserMassClass>()?;
    m.add_class::<PyKneserMassReport>()?;
    m.add_class::<PyWeylVersorReport>()?;
    m.add_class::<PyDiscriminantForm>()?;
    m.add_class::<PyOddDiscriminantForm>()?;
    m.add_class::<PyOddMilgramReport>()?;
    m.add("AUTO_NODE_BUDGET", crate::forms::AUTO_NODE_BUDGET)?;
    m.add("E8_WEYL_GROUP_ORDER", crate::forms::E8_WEYL_GROUP_ORDER)?;
    m.add("D16_PLUS_AUT_ORDER", crate::forms::D16_PLUS_AUT_ORDER)?;
    m.add(
        "BW16_AUTOMORPHISM_GROUP_ORDER",
        crate::forms::BW16_AUTOMORPHISM_GROUP_ORDER,
    )?;
    m.add(
        "BW16_REAL_CLIFFORD_GROUP_ORDER",
        crate::forms::BW16_REAL_CLIFFORD_GROUP_ORDER,
    )?;
    m.add(
        "BW16_AUTOMORPHISM_INDEX_IN_CLIFFORD_GROUP",
        crate::forms::BW16_AUTOMORPHISM_INDEX_IN_CLIFFORD_GROUP,
    )?;
    m.add("LEECH_AUT_ORDER", crate::forms::LEECH_AUT_ORDER)?;
    m.add(
        "HEISENBERG_WEIL_MATRIX_RANK_CAP",
        crate::forms::HEISENBERG_WEIL_MATRIX_RANK_CAP,
    )?;
    m.add_function(wrap_pyfunction!(arf_nimber, m)?)?;
    m.add_function(wrap_pyfunction!(arf_ordinal_finite, m)?)?;
    m.add_function(wrap_pyfunction!(fit_f2_quadratic, m)?)?;
    m.add_function(wrap_pyfunction!(arf_f2, m)?)?;
    m.add_function(wrap_pyfunction!(extraspecial_group_f2, m)?)?;
    m.add_function(wrap_pyfunction!(extraspecial_group_nimber, m)?)?;
    m.add_function(wrap_pyfunction!(heisenberg_weil_representation_f2, m)?)?;
    m.add_function(wrap_pyfunction!(heisenberg_weil_representation_nimber, m)?)?;
    m.add_function(wrap_pyfunction!(brown_f2, m)?)?;
    m.add_function(wrap_pyfunction!(double_f2, m)?)?;
    m.add_function(wrap_pyfunction!(gold_form_arf, m)?)?;
    m.add_function(wrap_pyfunction!(gold_form, m)?)?;
    m.add_function(wrap_pyfunction!(trace_twisted_form, m)?)?;
    m.add_function(wrap_pyfunction!(transfer_diagonal, m)?)?;
    m.add_function(wrap_pyfunction!(trace_form_arf, m)?)?;
    m.add_function(wrap_pyfunction!(classify_surreal, m)?)?;
    m.add_function(wrap_pyfunction!(classify_surcomplex, m)?)?;
    m.add_function(wrap_pyfunction!(classify_rational, m)?)?;
    m.add_function(wrap_pyfunction!(surreal_signature, m)?)?;
    m.add_function(wrap_pyfunction!(surcomplex_rank, m)?)?;
    m.add_function(wrap_pyfunction!(isometric_real, m)?)?;
    m.add_function(wrap_pyfunction!(isometric_rational, m)?)?;
    m.add_function(wrap_pyfunction!(isometric_surcomplex, m)?)?;
    m.add_function(wrap_pyfunction!(isometric_nimber, m)?)?;
    m.add_function(wrap_pyfunction!(classify_finite_algebra, m)?)?;
    m.add_function(wrap_pyfunction!(classify_finite_algebra_unified, m)?)?;
    m.add_function(wrap_pyfunction!(witt_finite_algebra, m)?)?;
    m.add_function(wrap_pyfunction!(witt_decompose_finite_algebra, m)?)?;
    m.add_function(wrap_pyfunction!(bw_class_finite_algebra, m)?)?;
    m.add_function(wrap_pyfunction!(bw_class_function_field, m)?)?;
    m.add_function(wrap_pyfunction!(isometric_finite_algebra, m)?)?;
    m.add_function(wrap_pyfunction!(monic_irreducible_factors, m)?)?;
    m.add_function(wrap_pyfunction!(try_relevant_places_ff, m)?)?;
    m.add_function(wrap_pyfunction!(try_valuation_at_ff, m)?)?;
    m.add_function(wrap_pyfunction!(try_is_local_square_ff, m)?)?;
    m.add_function(wrap_pyfunction!(is_global_square_ff, m)?)?;
    m.add_function(wrap_pyfunction!(try_hilbert_symbol_ff, m)?)?;
    m.add_function(wrap_pyfunction!(try_hasse_at_place_ff, m)?)?;
    m.add_function(wrap_pyfunction!(try_hilbert_reciprocity_product_ff, m)?)?;
    m.add_function(wrap_pyfunction!(try_ramified_places_ff, m)?)?;
    m.add_function(wrap_pyfunction!(try_is_isotropic_at_place_ff, m)?)?;
    m.add_function(wrap_pyfunction!(try_is_isotropic_ff, m)?)?;
    m.add_function(wrap_pyfunction!(try_isotropy_over_ff_adeles, m)?)?;
    m.add_function(wrap_pyfunction!(try_tame_symbol_exponent_ff, m)?)?;
    m.add_function(wrap_pyfunction!(try_tame_symbol_invariant_ff, m)?)?;
    m.add_function(wrap_pyfunction!(tame_symbol_invariants_ff, m)?)?;
    m.add_function(wrap_pyfunction!(tame_symbol_invariant_sum_ff, m)?)?;
    m.add_function(wrap_pyfunction!(constant_extension_invariants, m)?)?;
    m.add_function(wrap_pyfunction!(constant_extension_invariant_sum, m)?)?;
    m.add_function(wrap_pyfunction!(char2_monic_irreducible_factors, m)?)?;
    m.add_function(wrap_pyfunction!(as_symbol_at, m)?)?;
    m.add_function(wrap_pyfunction!(as_symbol_places, m)?)?;
    m.add_function(wrap_pyfunction!(as_symbol_reciprocity_sum, m)?)?;
    m.add_function(wrap_pyfunction!(as_symbol_ramified_places, m)?)?;
    m.add_function(wrap_pyfunction!(global_is_pe, m)?)?;
    m.add_function(wrap_pyfunction!(relevant_places_char2, m)?)?;
    m.add_function(wrap_pyfunction!(springer_decompose_local_char2, m)?)?;
    m.add_function(wrap_pyfunction!(local_anisotropic_dim_char2, m)?)?;
    m.add_function(wrap_pyfunction!(local_is_isotropic_char2, m)?)?;
    m.add_function(wrap_pyfunction!(is_isotropic_global_char2, m)?)?;
    m.add_function(wrap_pyfunction!(classify_real, m)?)?;
    m.add_function(wrap_pyfunction!(classify_complex, m)?)?;
    m.add_function(wrap_pyfunction!(hilbert_symbol_at, m)?)?;
    m.add_function(wrap_pyfunction!(hasse_at_place, m)?)?;
    m.add_function(wrap_pyfunction!(hilbert_product, m)?)?;
    m.add_function(wrap_pyfunction!(hilbert_reciprocity_product, m)?)?;
    m.add_function(wrap_pyfunction!(brauer_local_invariants, m)?)?;
    m.add_function(wrap_pyfunction!(brauer_invariant_sum, m)?)?;
    m.add_function(wrap_pyfunction!(hasse_brauer_class, m)?)?;
    m.add_function(wrap_pyfunction!(clifford_brauer_class, m)?)?;
    m.add_function(wrap_pyfunction!(cyclic_algebra_invariant, m)?)?;
    m.add_function(wrap_pyfunction!(tame_symbol_exponent, m)?)?;
    m.add_function(wrap_pyfunction!(tame_symbol_invariant, m)?)?;
    m.add_function(wrap_pyfunction!(global_residues, m)?)?;
    m.add_function(wrap_pyfunction!(global_residues_ff, m)?)?;
    m.add_function(wrap_pyfunction!(isotropy_over_adeles, m)?)?;
    m.add_function(wrap_pyfunction!(repetition_code, m)?)?;
    m.add_function(wrap_pyfunction!(reed_muller_code, m)?)?;
    m.add_function(wrap_pyfunction!(type_i_z2_code, m)?)?;
    m.add_function(wrap_pyfunction!(type_i_z2_plus_e8_code, m)?)?;
    m.add_function(wrap_pyfunction!(hamming_code, m)?)?;
    m.add_function(wrap_pyfunction!(extended_hamming_code, m)?)?;
    m.add_function(wrap_pyfunction!(type_ii_e8_sum_code, m)?)?;
    m.add_function(wrap_pyfunction!(type_ii_len16_code, m)?)?;
    m.add_function(wrap_pyfunction!(golay_code, m)?)?;
    m.add_function(wrap_pyfunction!(extended_golay_generator_rows, m)?)?;
    m.add_function(wrap_pyfunction!(construction_d, m)?)?;
    m.add_function(wrap_pyfunction!(barnes_wall_16, m)?)?;
    m.add_function(wrap_pyfunction!(clifford_barnes_wall_16_numerator_rows, m)?)?;
    m.add_function(wrap_pyfunction!(clifford_barnes_wall_16, m)?)?;
    m.add_function(wrap_pyfunction!(clifford_barnes_wall_16_report, m)?)?;
    m.add_function(wrap_pyfunction!(ternary_golay_code, m)?)?;
    m.add_function(wrap_pyfunction!(d16_plus, m)?)?;
    m.add_function(wrap_pyfunction!(a_n, m)?)?;
    m.add_function(wrap_pyfunction!(d_n, m)?)?;
    m.add_function(wrap_pyfunction!(e_6, m)?)?;
    m.add_function(wrap_pyfunction!(e_7, m)?)?;
    m.add_function(wrap_pyfunction!(e_8, m)?)?;
    m.add_function(wrap_pyfunction!(leech, m)?)?;
    m.add_function(wrap_pyfunction!(coxeter_number, m)?)?;
    m.add_function(wrap_pyfunction!(is_root_lattice, m)?)?;
    m.add_function(wrap_pyfunction!(are_in_same_genus, m)?)?;
    m.add_function(wrap_pyfunction!(mass_even_unimodular, m)?)?;
    m.add_function(wrap_pyfunction!(isotropic_lines_mod_p, m)?)?;
    m.add_function(wrap_pyfunction!(kneser_neighbor, m)?)?;
    m.add_function(wrap_pyfunction!(kneser_neighbors, m)?)?;
    m.add_function(wrap_pyfunction!(even_unimodular_kneser_report, m)?)?;
    m.add_function(wrap_pyfunction!(weyl_versor_report, m)?)?;
    m.add_function(wrap_pyfunction!(leech_aut_order, m)?)?;
    m.add_function(wrap_pyfunction!(niemeier_classes, m)?)?;
    m.add_function(wrap_pyfunction!(niemeier_mass_sum, m)?)?;
    m.add_function(wrap_pyfunction!(niemeier_weighted_theta_average, m)?)?;
    m.add_function(wrap_pyfunction!(verify_milgram, m)?)?;
    m.add_function(wrap_pyfunction!(odd_milgram_report, m)?)?;
    m.add_function(wrap_pyfunction!(verify_odd_milgram, m)?)?;
    m.add_function(wrap_pyfunction!(genus_signature_mod8, m)?)?;
    m.add_function(wrap_pyfunction!(qexp_from_int, m)?)?;
    m.add_function(wrap_pyfunction!(eisenstein_e4, m)?)?;
    m.add_function(wrap_pyfunction!(eisenstein_e6, m)?)?;
    m.add_function(wrap_pyfunction!(eisenstein_e12, m)?)?;
    m.add_function(wrap_pyfunction!(delta, m)?)?;
    m.add_function(wrap_pyfunction!(mk_basis, m)?)?;
    m.add_function(wrap_pyfunction!(as_modular_form, m)?)?;
    m.add_function(wrap_pyfunction!(modular_qexp_add, m)?)?;
    m.add_function(wrap_pyfunction!(modular_qexp_sub, m)?)?;
    m.add_function(wrap_pyfunction!(modular_qexp_mul, m)?)?;
    m.add_function(wrap_pyfunction!(modular_qexp_scale, m)?)?;
    m.add_function(wrap_pyfunction!(witt_class, m)?)?;
    m.add_function(wrap_pyfunction!(witt_class_error, m)?)?;
    m.add_function(wrap_pyfunction!(dickson_matrix, m)?)?;
    m.add_function(wrap_pyfunction!(dickson_of_versor, m)?)?;
    m.add_function(wrap_pyfunction!(char2_spinor_norm, m)?)?;
    m.add_function(wrap_pyfunction!(factor_char2_isometry, m)?)?;
    m.add_function(wrap_pyfunction!(classify_symplectic, m)?)?;
    m.add_function(wrap_pyfunction!(classify_symplectic_nimber, m)?)?;
    m.add_function(wrap_pyfunction!(witt_decompose_real, m)?)?;
    m.add_function(wrap_pyfunction!(isometric_ordinal_finite, m)?)?;
    m.add_function(wrap_pyfunction!(ordinal_witt, m)?)?;
    m.add_function(wrap_pyfunction!(artin_schreier_class_finite, m)?)?;
    m.add_function(wrap_pyfunction!(finite_field_numeric_invariants, m)?)?;
    m.add_function(wrap_pyfunction!(level, m)?)?;
    m.add_function(wrap_pyfunction!(pythagoras_number, m)?)?;
    m.add_function(wrap_pyfunction!(u_invariant, m)?)?;
    m.add_function(wrap_pyfunction!(is_sum_of_n_squares, m)?)?;
    m.add_function(wrap_pyfunction!(hilbert_symbol, m)?)?;
    m.add_function(wrap_pyfunction!(springer_decompose, m)?)?;
    m.add_function(wrap_pyfunction!(springer_decompose_local, m)?)?;
    m.add_function(wrap_pyfunction!(springer_decompose_qp, m)?)?;
    m.add_function(wrap_pyfunction!(springer_decompose_ramified_qp4_e2, m)?)?;
    m.add_function(wrap_pyfunction!(springer_decompose_ramified_qp4_e3, m)?)?;
    m.add_function(wrap_pyfunction!(springer_decompose_qq, m)?)?;
    m.add_function(wrap_pyfunction!(springer_decompose_laurent, m)?)?;
    m.add_function(wrap_pyfunction!(e_real, m)?)?;
    m.add_function(wrap_pyfunction!(hilbert_symbol_qp, m)?)?;
    m.add_function(wrap_pyfunction!(hilbert_symbol_real, m)?)?;
    m.add_function(wrap_pyfunction!(is_square_qp, m)?)?;
    m.add_function(wrap_pyfunction!(is_isotropic_at_p, m)?)?;
    m.add_function(wrap_pyfunction!(is_isotropic_q, m)?)?;
    m.add_function(wrap_pyfunction!(bw_class_real, m)?)?;
    m.add_function(wrap_pyfunction!(bw_class_complex, m)?)?;
    m.add_function(wrap_pyfunction!(bw_class_rational, m)?)?;
    m.add_function(wrap_pyfunction!(bw_class_nimber, m)?)?;
    m.add_function(wrap_pyfunction!(bw_class_ordinal, m)?)?;
    Ok(())
}
