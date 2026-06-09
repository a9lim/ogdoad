//! Python bindings for the GA engine: the `backend!` macro that stamps out one
//! `<World>Algebra` / `<World>MV` pyclass pair per scalar backend, the runtime
//! invocations, and conformal GA (`Cga`). The generated structs and their
//! fields are `pub(crate)` so the classifier bindings in [`super::forms`] and the
//! game-exterior binding in [`super::games`] can read `.inner` / `.mv`.

use super::scalars::{
    parse_adele, parse_f16, parse_f25, parse_f27, parse_f4, parse_f8, parse_f9, parse_fp11,
    parse_fp11_poly, parse_fp11_rational_function, parse_fp13, parse_fp13_poly,
    parse_fp13_rational_function, parse_fp2, parse_fp2_poly, parse_fp2_rational_function,
    parse_fp3, parse_fp3_poly, parse_fp3_rational_function, parse_fp5, parse_fp5_poly,
    parse_fp5_rational_function, parse_fp7, parse_fp7_poly, parse_fp7_rational_function,
    parse_gauss_qp11_4, parse_gauss_qp13_4, parse_gauss_qp2_4, parse_gauss_qp3_4,
    parse_gauss_qp5_4, parse_gauss_qp7_4, parse_integer, parse_laurent_f25_6, parse_laurent_f27_6,
    parse_laurent_f9_6, parse_laurent_fp11_6, parse_laurent_fp13_6, parse_laurent_fp3_6,
    parse_laurent_fp5_6, parse_laurent_fp7_6, parse_laurent_rational_6, parse_nimber,
    parse_nimber_poly, parse_nimber_rational_function, parse_omnific, parse_ordinal, parse_qp11_4,
    parse_qp13_4, parse_qp2_4, parse_qp3_4, parse_qp5_4, parse_qp7_4, parse_qq2_4_2, parse_qq2_4_3,
    parse_qq2_4_4, parse_qq3_4_2, parse_qq3_4_3, parse_qq5_4_2, parse_ramified_qp11_4_e2,
    parse_ramified_qp11_4_e3, parse_ramified_qp13_4_e2, parse_ramified_qp13_4_e3,
    parse_ramified_qp2_4_e2, parse_ramified_qp2_4_e3, parse_ramified_qp3_4_e2,
    parse_ramified_qp3_4_e3, parse_ramified_qp5_4_e2, parse_ramified_qp5_4_e3,
    parse_ramified_qp7_4_e2, parse_ramified_qp7_4_e3, parse_rational, parse_surcomplex,
    parse_surreal, parse_witt_vec2_4_2, parse_witt_vec2_4_3, parse_witt_vec2_4_4,
    parse_witt_vec3_4_2, parse_witt_vec3_4_3, parse_witt_vec5_4_2, parse_zp11_4, parse_zp13_4,
    parse_zp2_4, parse_zp3_4, parse_zp5_4, parse_zp7_4, wrap_adele, wrap_f16, wrap_f25, wrap_f27,
    wrap_f4, wrap_f8, wrap_f9, wrap_fp11, wrap_fp11_poly, wrap_fp11_rational_function, wrap_fp13,
    wrap_fp13_poly, wrap_fp13_rational_function, wrap_fp2, wrap_fp2_poly,
    wrap_fp2_rational_function, wrap_fp3, wrap_fp3_poly, wrap_fp3_rational_function, wrap_fp5,
    wrap_fp5_poly, wrap_fp5_rational_function, wrap_fp7, wrap_fp7_poly, wrap_fp7_rational_function,
    wrap_gauss_qp11_4, wrap_gauss_qp13_4, wrap_gauss_qp2_4, wrap_gauss_qp3_4, wrap_gauss_qp5_4,
    wrap_gauss_qp7_4, wrap_integer, wrap_laurent_f25_6, wrap_laurent_f27_6, wrap_laurent_f9_6,
    wrap_laurent_fp11_6, wrap_laurent_fp13_6, wrap_laurent_fp3_6, wrap_laurent_fp5_6,
    wrap_laurent_fp7_6, wrap_laurent_rational_6, wrap_nimber, wrap_nimber_poly,
    wrap_nimber_rational_function, wrap_omnific, wrap_ordinal, wrap_qp11_4, wrap_qp13_4,
    wrap_qp2_4, wrap_qp3_4, wrap_qp5_4, wrap_qp7_4, wrap_qq2_4_2, wrap_qq2_4_3, wrap_qq2_4_4,
    wrap_qq3_4_2, wrap_qq3_4_3, wrap_qq5_4_2, wrap_ramified_qp11_4_e2, wrap_ramified_qp11_4_e3,
    wrap_ramified_qp13_4_e2, wrap_ramified_qp13_4_e3, wrap_ramified_qp2_4_e2,
    wrap_ramified_qp2_4_e3, wrap_ramified_qp3_4_e2, wrap_ramified_qp3_4_e3, wrap_ramified_qp5_4_e2,
    wrap_ramified_qp5_4_e3, wrap_ramified_qp7_4_e2, wrap_ramified_qp7_4_e3, wrap_rational,
    wrap_surcomplex, wrap_surreal, wrap_witt_vec2_4_2, wrap_witt_vec2_4_3, wrap_witt_vec2_4_4,
    wrap_witt_vec3_4_2, wrap_witt_vec3_4_3, wrap_witt_vec5_4_2, wrap_zp11_4, wrap_zp13_4,
    wrap_zp2_4, wrap_zp3_4, wrap_zp5_4, wrap_zp7_4, PyAdele, PyF16, PyF25, PyF27, PyF4, PyF8, PyF9,
    PyFp11, PyFp11Poly, PyFp11RationalFunction, PyFp13, PyFp13Poly, PyFp13RationalFunction, PyFp2,
    PyFp2Poly, PyFp2RationalFunction, PyFp3, PyFp3Poly, PyFp3RationalFunction, PyFp5, PyFp5Poly,
    PyFp5RationalFunction, PyFp7, PyFp7Poly, PyFp7RationalFunction, PyGaussQp11_4, PyGaussQp13_4,
    PyGaussQp2_4, PyGaussQp3_4, PyGaussQp5_4, PyGaussQp7_4, PyInteger, PyLaurentF25_6,
    PyLaurentF27_6, PyLaurentF9_6, PyLaurentFp11_6, PyLaurentFp13_6, PyLaurentFp3_6,
    PyLaurentFp5_6, PyLaurentFp7_6, PyLaurentRational6, PyNimber, PyNimberPoly,
    PyNimberRationalFunction, PyOmnific, PyOrdinal, PyQp11_4, PyQp13_4, PyQp2_4, PyQp3_4, PyQp5_4,
    PyQp7_4, PyQq2_4_2, PyQq2_4_3, PyQq2_4_4, PyQq3_4_2, PyQq3_4_3, PyQq5_4_2, PyRamifiedQp11_4E2,
    PyRamifiedQp11_4E3, PyRamifiedQp13_4E2, PyRamifiedQp13_4E3, PyRamifiedQp2_4E2,
    PyRamifiedQp2_4E3, PyRamifiedQp3_4E2, PyRamifiedQp3_4E3, PyRamifiedQp5_4E2, PyRamifiedQp5_4E3,
    PyRamifiedQp7_4E2, PyRamifiedQp7_4E3, PyRational, PySurcomplex, PySurreal, PyWittVec2_4_2,
    PyWittVec2_4_3, PyWittVec2_4_4, PyWittVec3_4_2, PyWittVec3_4_3, PyWittVec5_4_2, PyZp11_4,
    PyZp13_4, PyZp2_4, PyZp3_4, PyZp5_4, PyZp7_4,
};
use crate::clifford::{
    Cga, CliffordAlgebra, DividedPowerAlgebra, DpVector, LinearMap, Metric, Multivector,
    MAX_BASIS_DIM,
};
use crate::scalar::{
    Adele, Fp, Fpn, Gauss, Integer, Laurent, Nimber, Omnific, Ordinal, Poly, Qp, Qq, Ramified,
    Rational, RationalFunction, Scalar, Surcomplex, Surreal, WittVec, Zp,
};
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::PyDict;
use pyo3::IntoPyObjectExt;
use std::collections::BTreeMap;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::Arc;
use std::sync::Mutex;

static PANIC_HOOK_LOCK: Mutex<()> = Mutex::new(());

fn panic_payload_message(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "Rust operation panicked".to_string()
    }
}

fn scalar_boundary<T>(f: impl FnOnce() -> T) -> PyResult<T> {
    let _guard = PANIC_HOOK_LOCK
        .lock()
        .map_err(|_| PyValueError::new_err("panic hook lock poisoned"))?;
    let old_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = catch_unwind(AssertUnwindSafe(f));
    std::panic::set_hook(old_hook);
    result.map_err(|payload| {
        PyValueError::new_err(format!(
            "operation escaped the represented scalar boundary: {}",
            panic_payload_message(payload)
        ))
    })
}

#[pyclass(name = "SpinorRep", module = "pleroma")]
struct PySpinorRep {
    idempotent: Py<PyAny>,
    basis: Py<PyAny>,
    gen_matrices: Py<PyAny>,
    is_left_regular: bool,
    diagonalized_metric: Py<PyAny>,
    orthogonal_basis_in_original: Py<PyAny>,
    basis_dim: usize,
    generator_count: usize,
}

#[pymethods]
impl PySpinorRep {
    #[getter]
    fn idempotent(&self, py: Python<'_>) -> Py<PyAny> {
        self.idempotent.clone_ref(py)
    }
    #[getter]
    fn basis(&self, py: Python<'_>) -> Py<PyAny> {
        self.basis.clone_ref(py)
    }
    #[getter]
    fn gen_matrices(&self, py: Python<'_>) -> Py<PyAny> {
        self.gen_matrices.clone_ref(py)
    }
    #[getter]
    fn is_left_regular(&self) -> bool {
        self.is_left_regular
    }
    #[getter]
    fn diagonalized_metric(&self, py: Python<'_>) -> Py<PyAny> {
        self.diagonalized_metric.clone_ref(py)
    }
    #[getter]
    fn orthogonal_basis_in_original(&self, py: Python<'_>) -> Py<PyAny> {
        self.orthogonal_basis_in_original.clone_ref(py)
    }
    fn __repr__(&self) -> String {
        format!(
            "SpinorRep(basis_dim={}, generators={}, is_left_regular={})",
            self.basis_dim, self.generator_count, self.is_left_regular
        )
    }
}

#[pyclass(name = "LazySpinorRep", module = "pleroma")]
struct PyLazySpinorRep {
    algebra: Py<PyAny>,
}

#[pymethods]
impl PyLazySpinorRep {
    #[getter]
    fn algebra(&self, py: Python<'_>) -> Py<PyAny> {
        self.algebra.clone_ref(py)
    }

    /// Apply left multiplication by generator `e_i` to a sparse module vector.
    fn apply_generator(
        &self,
        py: Python<'_>,
        i: usize,
        v: Bound<'_, PyAny>,
    ) -> PyResult<Py<PyAny>> {
        Ok(self
            .algebra
            .bind(py)
            .call_method1("apply_generator", (i, v))?
            .unbind())
    }

    /// Apply left multiplication by the vector `Σ coeffs[i] e_i`.
    fn apply_vector(
        &self,
        py: Python<'_>,
        coeffs: Vec<Bound<'_, PyAny>>,
        v: Bound<'_, PyAny>,
    ) -> PyResult<Py<PyAny>> {
        Ok(self
            .algebra
            .bind(py)
            .call_method1("apply_vector", (coeffs, v))?
            .unbind())
    }

    fn __repr__(&self) -> String {
        "LazySpinorRep()".to_string()
    }
}

#[pyclass(name = "VersorClass", module = "pleroma")]
struct PyVersorClass {
    spinor_norm: Py<PyAny>,
    dickson: u128,
}

#[pymethods]
impl PyVersorClass {
    #[getter]
    fn spinor_norm(&self, py: Python<'_>) -> Py<PyAny> {
        self.spinor_norm.clone_ref(py)
    }
    #[getter]
    fn dickson(&self) -> u128 {
        self.dickson
    }
    fn __repr__(&self) -> String {
        format!("VersorClass(dickson={})", self.dickson)
    }
}

fn prime_field_identity_linear_map(py: Python<'_>, p: u128) -> PyResult<Py<PyAny>> {
    match p {
        2 => Fp2LinearMap {
            inner: LinearMap::<Fp<2>>::identity(1),
        }
        .into_py_any(py),
        3 => Fp3LinearMap {
            inner: LinearMap::<Fp<3>>::identity(1),
        }
        .into_py_any(py),
        5 => Fp5LinearMap {
            inner: LinearMap::<Fp<5>>::identity(1),
        }
        .into_py_any(py),
        7 => Fp7LinearMap {
            inner: LinearMap::<Fp<7>>::identity(1),
        }
        .into_py_any(py),
        11 => Fp11LinearMap {
            inner: LinearMap::<Fp<11>>::identity(1),
        }
        .into_py_any(py),
        13 => Fp13LinearMap {
            inner: LinearMap::<Fp<13>>::identity(1),
        }
        .into_py_any(py),
        _ => Err(PyValueError::new_err(
            "unsupported prime field; expected p in {2,3,5,7,11,13}",
        )),
    }
}

/// Rust-name fixed-dispatch constructor for the base-field Galois `LinearMap`.
#[pyfunction]
#[pyo3(signature = (p, degree, power=1))]
fn galois_linear_map(py: Python<'_>, p: u128, degree: usize, power: usize) -> PyResult<Py<PyAny>> {
    match (p, degree) {
        (_, 1) => prime_field_identity_linear_map(py, p),
        (2, 2) => Fp2LinearMap {
            inner: crate::clifford::galois_linear_map::<Fpn<2, 2>>(power),
        }
        .into_py_any(py),
        (2, 3) => Fp2LinearMap {
            inner: crate::clifford::galois_linear_map::<Fpn<2, 3>>(power),
        }
        .into_py_any(py),
        (2, 4) => Fp2LinearMap {
            inner: crate::clifford::galois_linear_map::<Fpn<2, 4>>(power),
        }
        .into_py_any(py),
        (3, 2) => Fp3LinearMap {
            inner: crate::clifford::galois_linear_map::<Fpn<3, 2>>(power),
        }
        .into_py_any(py),
        (3, 3) => Fp3LinearMap {
            inner: crate::clifford::galois_linear_map::<Fpn<3, 3>>(power),
        }
        .into_py_any(py),
        (5, 2) => Fp5LinearMap {
            inner: crate::clifford::galois_linear_map::<Fpn<5, 2>>(power),
        }
        .into_py_any(py),
        _ => Err(PyValueError::new_err(
            "unsupported finite field; expected one of F_p, F4, F8, F16, F9, F25, F27",
        )),
    }
}

/// Rust-name fixed-dispatch constructor for the base-field Frobenius `LinearMap`.
#[pyfunction]
fn frobenius_linear_map(py: Python<'_>, p: u128, degree: usize) -> PyResult<Py<PyAny>> {
    galois_linear_map(py, p, degree, 1)
}

/// Rust-name constructor for the represented nimber-subfield Frobenius `LinearMap`.
#[pyfunction]
#[pyo3(signature = (m, power=1))]
fn nimber_subfield_frobenius_linear_map(
    py: Python<'_>,
    m: usize,
    power: usize,
) -> PyResult<Py<PyAny>> {
    if !m.is_power_of_two() || m > 128 {
        return Err(PyValueError::new_err(
            "nimber subfield degree m must be a power of two <= 128",
        ));
    }
    Fp2LinearMap {
        inner: crate::clifford::nimber_subfield_frobenius_linear_map(m, power),
    }
    .into_py_any(py)
}

/// Ascending generator indices in a blade mask.
#[pyfunction]
fn bits(mask: u128) -> Vec<usize> {
    crate::clifford::bits(mask)
}

/// The grade of a blade mask.
#[pyfunction]
fn grade(mask: u128) -> usize {
    crate::clifford::grade(mask)
}

// ---------------------------------------------------------------------------
// Algebra + multivector, one pair per backend
// ---------------------------------------------------------------------------

macro_rules! backend {
    (
        $alg:ident,
        $alg_name:literal,
        $mv:ident,
        $mv_name:literal,
        $lm:ident,
        $lm_name:literal,
        $scalar:ty,
        $parse:path,
        $scalar_py:ty,
        $wrap:path
    ) => {
        #[pyclass(name = $alg_name, module = "pleroma", from_py_object)]
        #[derive(Clone)]
        pub(crate) struct $alg {
            pub(crate) inner: Arc<CliffordAlgebra<$scalar>>,
        }

        #[pyclass(name = $lm_name, module = "pleroma", from_py_object)]
        #[derive(Clone)]
        pub(crate) struct $lm {
            pub(crate) inner: LinearMap<$scalar>,
        }

        #[pymethods]
        impl $lm {
            /// Rust-name constructor for a column-major `LinearMap`.
            #[staticmethod]
            fn from_columns(cols: Vec<Vec<Bound<'_, PyAny>>>) -> PyResult<Self> {
                Ok($lm {
                    inner: $lm::parse_columns(cols)?,
                })
            }

            /// Rust-name constructor for the identity map on `n` generators.
            #[staticmethod]
            fn identity(n: usize) -> Self {
                $lm {
                    inner: LinearMap::<$scalar>::identity(n),
                }
            }

            #[getter]
            fn n(&self) -> usize {
                self.inner.n
            }

            #[getter]
            fn cols(&self) -> Vec<Vec<$scalar_py>> {
                self.columns_py()
            }

            /// Rust-name `LinearMap::image`: return `f(e_i)` as a grade-1
            /// multivector in the given algebra.
            fn image(&self, alg: &$alg, i: usize) -> PyResult<$mv> {
                alg.ensure_linear_map(&self.inner)?;
                if i >= alg.inner.dim {
                    return Err(PyValueError::new_err("linear-map image index out of range"));
                }
                Ok($mv {
                    alg: alg.inner.clone(),
                    mv: scalar_boundary(|| self.inner.image(&alg.inner, i))?,
                })
            }

            /// Rust-name `LinearMap::compose`: `self ∘ inner`.
            fn compose(&self, inner: &$lm) -> PyResult<$lm> {
                if self.inner.n != inner.inner.n {
                    return Err(PyValueError::new_err("dimension mismatch in compose"));
                }
                Ok($lm {
                    inner: scalar_boundary(|| self.inner.compose(&inner.inner))?,
                })
            }

            fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
                if let Ok(o) = other.cast::<$lm>() {
                    self.inner == o.borrow().inner
                } else {
                    false
                }
            }

            fn __repr__(&self) -> String {
                format!("{}(n={})", $lm_name, self.inner.n)
            }
        }

        impl $lm {
            fn parse_columns(cols: Vec<Vec<Bound<'_, PyAny>>>) -> PyResult<LinearMap<$scalar>> {
                let n = cols.len();
                let mut parsed: Vec<Vec<$scalar>> = Vec::with_capacity(n);
                for col in &cols {
                    if col.len() != n {
                        return Err(PyValueError::new_err(
                            "LinearMap must be square: n columns of length n",
                        ));
                    }
                    let mut out = Vec::with_capacity(n);
                    for x in col {
                        out.push($parse(x)?);
                    }
                    parsed.push(out);
                }
                Ok(LinearMap::from_columns(parsed))
            }

            fn columns_py(&self) -> Vec<Vec<$scalar_py>> {
                self.inner
                    .cols
                    .iter()
                    .map(|col| col.iter().cloned().map($wrap).collect())
                    .collect()
            }
        }

        #[pymethods]
        impl $alg {
            #[new]
            #[pyo3(signature = (q, b=None, a=None))]
            fn new(
                q: Vec<Bound<'_, PyAny>>,
                b: Option<Bound<'_, PyDict>>,
                a: Option<Bound<'_, PyDict>>,
            ) -> PyResult<Self> {
                let mut qv: Vec<$scalar> = Vec::with_capacity(q.len());
                for item in &q {
                    qv.push($parse(item)?);
                }
                let dim = qv.len();
                if dim > MAX_BASIS_DIM {
                    return Err(PyValueError::new_err(format!(
                        "algebra dimension must be <= {MAX_BASIS_DIM}"
                    )));
                }
                let mut bm: BTreeMap<(usize, usize), $scalar> = BTreeMap::new();
                if let Some(d) = b {
                    for (k, v) in d.iter() {
                        let (i, j): (usize, usize) = k.extract()?;
                        if i == j {
                            return Err(PyValueError::new_err("b-keys must be off-diagonal"));
                        }
                        if i >= dim || j >= dim {
                            return Err(PyValueError::new_err("b-key index out of range"));
                        }
                        let key = if i < j { (i, j) } else { (j, i) };
                        bm.insert(key, $parse(&v)?);
                    }
                }
                // `a` (the in-order / asymmetric contraction) is keyed (i,j) with
                // i<j; it promotes the algebra to a general bilinear form.
                let mut am: BTreeMap<(usize, usize), $scalar> = BTreeMap::new();
                if let Some(d) = a {
                    for (k, v) in d.iter() {
                        let (i, j): (usize, usize) = k.extract()?;
                        if i >= j {
                            return Err(PyValueError::new_err("a-keys must satisfy i < j"));
                        }
                        if j >= dim {
                            return Err(PyValueError::new_err("a-key index out of range"));
                        }
                        am.insert((i, j), $parse(&v)?);
                    }
                }
                let metric = Metric::general(qv, bm, am);
                Ok($alg {
                    inner: Arc::new(CliffordAlgebra::new(dim, metric)),
                })
            }

            #[getter]
            fn dim(&self) -> usize {
                self.inner.dim
            }

            /// Rust-name constructor for a general-bilinear metric algebra.
            #[staticmethod]
            #[pyo3(signature = (q, b=None, a=None))]
            fn general(
                q: Vec<Bound<'_, PyAny>>,
                b: Option<Bound<'_, PyDict>>,
                a: Option<Bound<'_, PyDict>>,
            ) -> PyResult<Self> {
                Self::new(q, b, a)
            }

            /// Rust-name constructor for the fully-null Grassmann/exterior metric.
            #[staticmethod]
            fn grassmann(n: usize) -> PyResult<Self> {
                if n > MAX_BASIS_DIM {
                    return Err(PyValueError::new_err(format!(
                        "algebra dimension must be <= {MAX_BASIS_DIM}"
                    )));
                }
                let metric = Metric::grassmann(n);
                Ok($alg {
                    inner: Arc::new(CliffordAlgebra::new(n, metric)),
                })
            }

            /// Diagonal quadratic entries `q[i] = e_i^2`.
            fn q(&self) -> Vec<$scalar_py> {
                self.inner.metric.q.iter().cloned().map($wrap).collect()
            }

            /// Nonzero polar entries `(i, j, value)` with `i < j`.
            fn b_terms(&self) -> Vec<(usize, usize, $scalar_py)> {
                self.inner
                    .metric
                    .b
                    .iter()
                    .filter(|(_, v)| !v.is_zero())
                    .map(|(&(i, j), v)| (i, j, $wrap(v.clone())))
                    .collect()
            }

            /// Nonzero upper/in-order contraction entries `(i, j, value)` with `i < j`.
            fn a_terms(&self) -> Vec<(usize, usize, $scalar_py)> {
                self.inner
                    .metric
                    .a
                    .iter()
                    .filter(|(_, v)| !v.is_zero())
                    .map(|(&(i, j), v)| (i, j, $wrap(v.clone())))
                    .collect()
            }

            /// Rust-name metric map, restricted to this same Python backend.
            fn map(&self, py: Python<'_>, f: Bound<'_, PyAny>) -> PyResult<$alg> {
                let apply = |coeff: &$scalar| -> PyResult<$scalar> {
                    let py_coeff = $wrap(coeff.clone()).into_py_any(py)?;
                    let mapped = f.call1((py_coeff,))?;
                    $parse(&mapped)
                };
                let q = self
                    .inner
                    .metric
                    .q
                    .iter()
                    .map(&apply)
                    .collect::<PyResult<Vec<_>>>()?;
                let mut b = BTreeMap::new();
                for (&key, coeff) in &self.inner.metric.b {
                    b.insert(key, apply(coeff)?);
                }
                let mut a = BTreeMap::new();
                for (&key, coeff) in &self.inner.metric.a {
                    a.insert(key, apply(coeff)?);
                }
                let metric = Metric::general(q, b, a);
                Ok($alg {
                    inner: Arc::new(CliffordAlgebra::new(self.inner.dim, metric)),
                })
            }

            /// Rust-name helper: `q[i]`, or zero outside the represented diagonal.
            fn q_val(&self, i: usize) -> $scalar_py {
                $wrap(self.inner.metric.q_val(i))
            }

            /// Rust-name helper: whether the metric has any upper/in-order
            /// contraction terms and therefore needs the general product path.
            fn has_upper(&self) -> bool {
                self.inner.metric.has_upper()
            }

            /// Rust-name helper: whether this basis is orthogonal.
            fn is_orthogonal(&self) -> bool {
                self.inner.metric.is_orthogonal()
            }

            /// The graded (super) tensor product self ⊗̂ other ≅ Cl(self ⟂ other).
            fn graded_tensor(&self, other: &$alg) -> PyResult<$alg> {
                if self.inner.dim + other.inner.dim > MAX_BASIS_DIM {
                    return Err(PyValueError::new_err(format!(
                        "graded tensor dimension exceeds {MAX_BASIS_DIM}"
                    )));
                }
                Ok($alg {
                    inner: Arc::new(self.inner.graded_tensor(&other.inner)),
                })
            }

            /// The tensor square `Cl ⊗̂ Cl`, used by the exterior Hopf coproduct.
            fn tensor_square(&self) -> PyResult<$alg> {
                if self.inner.dim * 2 > MAX_BASIS_DIM {
                    return Err(PyValueError::new_err(format!(
                        "tensor square dimension exceeds {MAX_BASIS_DIM}"
                    )));
                }
                Ok($alg {
                    inner: Arc::new(crate::clifford::tensor_square(&self.inner)),
                })
            }

            /// Embed a multivector of the first graded-tensor factor into this
            /// target algebra.
            fn embed_first(&self, mv: &$mv) -> PyResult<$mv> {
                if mv.alg.dim > self.inner.dim {
                    return Err(PyValueError::new_err(
                        "source multivector dimension exceeds target algebra dimension",
                    ));
                }
                Ok($mv {
                    alg: self.inner.clone(),
                    mv: self.inner.embed_first(&mv.mv),
                })
            }

            /// Embed a multivector of the second graded-tensor factor into this
            /// target algebra by shifting its blade masks by `shift`.
            fn embed_second(&self, mv: &$mv, shift: usize) -> PyResult<$mv> {
                if shift + mv.alg.dim > self.inner.dim {
                    return Err(PyValueError::new_err(
                        "shifted source multivector dimension exceeds target algebra dimension",
                    ));
                }
                Ok($mv {
                    alg: self.inner.clone(),
                    mv: scalar_boundary(|| self.inner.embed_second(&mv.mv, shift))?,
                })
            }

            /// Tensor product of diagonal quadratic-form representatives:
            /// `<a_i> tensor <b_j> = <a_i b_j>`. This is the Witt-ring
            /// multiplication on representatives, distinct from the Clifford
            /// graded tensor product.
            fn tensor_form(&self, other: &$alg) -> PyResult<$alg> {
                let metric = scalar_boundary(|| {
                    crate::forms::tensor_form(&self.inner.metric, &other.inner.metric)
                })?
                .ok_or_else(|| {
                    PyValueError::new_err(
                        "tensor_form needs diagonal form representatives (empty b and a)",
                    )
                })?;
                Ok($alg {
                    inner: Arc::new(CliffordAlgebra::new(metric.q.len(), metric)),
                })
            }

            /// Membership in the fundamental ideal I: for a diagonal representative,
            /// the nondegenerate rank is even.
            fn in_fundamental_ideal(&self) -> PyResult<bool> {
                scalar_boundary(|| crate::forms::in_fundamental_ideal(&self.inner.metric))?
                    .ok_or_else(|| {
                        PyValueError::new_err(
                            "in_fundamental_ideal needs a diagonal form representative",
                        )
                    })
            }

            /// The 1-fold Pfister form `<<a>> = <1, -a>` over this scalar backend.
            #[staticmethod]
            fn pfister1(scale: &Bound<'_, PyAny>) -> PyResult<$alg> {
                let scale = $parse(scale)?;
                let metric = scalar_boundary(|| crate::forms::pfister1(&scale))?;
                Ok($alg {
                    inner: Arc::new(CliffordAlgebra::new(metric.q.len(), metric)),
                })
            }

            /// The n-fold Pfister form `<<a_1,...,a_n>>` over this scalar backend.
            /// The empty product is `<1>`.
            #[staticmethod]
            fn pfister(scales: Vec<Bound<'_, PyAny>>) -> PyResult<$alg> {
                let mut parsed = Vec::with_capacity(scales.len());
                for scale in &scales {
                    parsed.push($parse(scale)?);
                }
                let metric = scalar_boundary(|| crate::forms::pfister(&parsed))?;
                Ok($alg {
                    inner: Arc::new(CliffordAlgebra::new(metric.q.len(), metric)),
                })
            }

            /// Projective geometric algebra `Cl(n,0,1)`: one null ideal/projective
            /// direction followed by `n` unit directions.
            #[staticmethod]
            fn pga(n: usize) -> PyResult<$alg> {
                if n >= MAX_BASIS_DIM {
                    return Err(PyValueError::new_err(format!(
                        "PGA total dimension must be <= {MAX_BASIS_DIM}"
                    )));
                }
                Ok($alg {
                    inner: Arc::new(crate::clifford::pga::<$scalar>(n)),
                })
            }

            /// The even subalgebra as a Clifford algebra one dimension smaller
            /// (orthogonal metrics with a non-null generator only).
            fn even_subalgebra(&self) -> PyResult<$alg> {
                self.inner
                    .even_subalgebra()
                    .map(|a| $alg { inner: Arc::new(a) })
                    .ok_or_else(|| {
                        PyValueError::new_err(
                            "even subalgebra needs an orthogonal metric with a non-null generator",
                        )
                    })
            }
            fn gen(&self, i: usize) -> PyResult<$mv> {
                if i >= self.inner.dim {
                    return Err(PyValueError::new_err("generator index out of range"));
                }
                Ok($mv {
                    alg: self.inner.clone(),
                    mv: self.inner.gen(i),
                })
            }
            fn blade(&self, gens: Vec<usize>) -> PyResult<$mv> {
                let mut seen = std::collections::BTreeSet::new();
                for &g in &gens {
                    if g >= self.inner.dim {
                        return Err(PyValueError::new_err("blade generator index out of range"));
                    }
                    if !seen.insert(g) {
                        return Err(PyValueError::new_err("blade expects distinct generators"));
                    }
                }
                Ok($mv {
                    alg: self.inner.clone(),
                    mv: self.inner.blade(&gens),
                })
            }
            fn scalar(&self, s: &Bound<'_, PyAny>) -> PyResult<$mv> {
                Ok($mv {
                    alg: self.inner.clone(),
                    mv: self.inner.scalar($parse(s)?),
                })
            }
            fn zero(&self) -> $mv {
                $mv {
                    alg: self.inner.clone(),
                    mv: self.inner.zero(),
                }
            }
            fn pseudoscalar(&self) -> $mv {
                $mv {
                    alg: self.inner.clone(),
                    mv: self.inner.pseudoscalar(),
                }
            }

            /// The symmetric Gram matrix of the quadratic form, using
            /// `b/2` off-diagonal. Undefined in characteristic 2.
            fn gram(&self) -> PyResult<Vec<Vec<$scalar_py>>> {
                crate::forms::gram(&self.inner.metric)
                    .map(|rows| {
                        rows.into_iter()
                            .map(|row| row.into_iter().map($wrap).collect())
                            .collect()
                    })
                    .ok_or_else(|| {
                        PyValueError::new_err(
                            "Gram matrix needs 2 invertible; in characteristic 2 use the polar form directly",
                        )
                    })
            }

            /// Congruence-diagonalize the symmetric form, if possible. Returns
            /// `None` in characteristic 2 or when a needed pivot is a nonunit.
            fn diagonalize(&self) -> PyResult<$alg> {
                let metric = scalar_boundary(|| crate::forms::diagonalize(&self.inner.metric))?
                    .ok_or_else(|| {
                        PyValueError::new_err(
                            "metric is not diagonalizable in this scalar world",
                        )
                    })?;
                Ok($alg {
                    inner: Arc::new(CliffordAlgebra::new(metric.q.len(), metric)),
                })
            }

            /// Return this metric unchanged if already diagonal, otherwise
            /// congruence-diagonalize it.
            fn as_diagonal(&self) -> PyResult<$alg> {
                let metric = scalar_boundary(|| crate::forms::as_diagonal(&self.inner.metric))?
                    .ok_or_else(|| {
                        PyValueError::new_err(
                            "metric is not diagonalizable in this scalar world",
                        )
                    })?;
                Ok($alg {
                    inner: Arc::new(CliffordAlgebra::new(metric.q.len(), metric)),
                })
            }

            /// The determinant of a `LinearMap`: the scalar by which its
            /// outermorphism scales the pseudoscalar. Char-faithful (the char-2
            /// determinant over nimbers).
            fn determinant(&self, lm: &$lm) -> PyResult<$scalar_py> {
                self.ensure_linear_map(&lm.inner)?;
                Ok($wrap(scalar_boundary(|| {
                    crate::clifford::determinant(&self.inner, &lm.inner)
                })?))
            }

            /// The trace of a `LinearMap` (`= tr Λ¹f`).
            fn trace(&self, lm: &$lm) -> PyResult<$scalar_py> {
                self.ensure_linear_map(&lm.inner)?;
                Ok($wrap(scalar_boundary(|| {
                    crate::clifford::trace(&self.inner, &lm.inner)
                })?))
            }

            /// The trace of the exterior power `Λ^k f`.
            fn exterior_power_trace(&self, lm: &$lm, k: usize) -> PyResult<$scalar_py> {
                self.ensure_linear_map(&lm.inner)?;
                Ok($wrap(scalar_boundary(|| {
                    crate::clifford::exterior_power_trace(&self.inner, &lm.inner, k)
                })?))
            }

            /// The characteristic polynomial `det(t·I − f)` via exterior-power
            /// traces, as coefficients in descending degree `[1, −c₁, …, (−1)ⁿcₙ]`
            /// (`cₖ = tr Λᵏf`). Char-faithful.
            fn char_poly(&self, lm: &$lm) -> PyResult<Vec<$scalar_py>> {
                self.ensure_linear_map(&lm.inner)?;
                Ok(scalar_boundary(|| crate::clifford::char_poly(&self.inner, &lm.inner))?
                    .into_iter()
                    .map($wrap)
                    .collect())
            }

            /// The inverse `LinearMap`, if it is invertible over this scalar world.
            fn inverse_outermorphism(&self, lm: &$lm) -> PyResult<Option<$lm>> {
                self.ensure_linear_map(&lm.inner)?;
                Ok(scalar_boundary(|| crate::clifford::inverse_outermorphism(&lm.inner))?
                    .map(|inner| $lm { inner }))
            }

            /// Apply the outermorphism of a `LinearMap` to a multivector:
            /// `f(a∧b) = f(a)∧f(b)`.
            fn apply_outermorphism(&self, lm: &$lm, mv: &$mv) -> PyResult<$mv> {
                self.ensure_mv(mv)?;
                self.ensure_linear_map(&lm.inner)?;
                Ok($mv {
                    alg: self.inner.clone(),
                    mv: scalar_boundary(|| {
                        crate::clifford::apply_outermorphism(&self.inner, &lm.inner, &mv.mv)
                    })?,
                })
            }

            /// Full concrete spinor data as a named `SpinorRep` record.
            /// Supports nondegenerate characteristic-0 metrics and nonsingular
            /// characteristic-2 nimber metrics; rejects general-bilinear metrics.
            /// `diagonalized_metric` is returned as `(q, b_terms)` when present,
            /// where `b_terms` contains `(i, j, value)` entries.
            fn spinor_rep(&self, py: Python<'_>) -> PyResult<PySpinorRep> {
                let rep = scalar_boundary(|| crate::clifford::spinor_rep(&self.inner))?.ok_or_else(|| {
	                    PyValueError::new_err(
	                        "spinor_rep needs a supported nondegenerate metric with no general-bilinear a-part",
	                    )
                })?;
                let is_left_regular = rep.is_left_regular;
                let diagonalized_metric: Option<(
                    Vec<$scalar_py>,
                    Vec<(usize, usize, $scalar_py)>,
                )> = rep.diagonalized_metric.map(|metric| {
                    (
                        metric.q.into_iter().map($wrap).collect(),
                        metric
                            .b
                            .into_iter()
                            .map(|((i, j), coeff)| (i, j, $wrap(coeff)))
                            .collect(),
                    )
                });
                let orthogonal_basis_in_original: Option<Vec<Vec<$scalar_py>>> =
                    rep.orthogonal_basis_in_original.map(|matrix| {
                        matrix
                            .into_iter()
                            .map(|row| row.into_iter().map($wrap).collect())
                            .collect()
                    });
                let idempotent = $mv {
                    alg: self.inner.clone(),
                    mv: rep.idempotent,
                };
                let basis: Vec<$mv> = rep
                    .basis
                    .into_iter()
                    .map(|mv| $mv {
                        alg: self.inner.clone(),
                        mv,
                    })
                    .collect();
                let gen_matrices: Vec<Vec<Vec<$scalar_py>>> = rep
                    .gen_matrices
                    .into_iter()
                    .map(|m| {
                        m.into_iter()
                            .map(|row| row.into_iter().map($wrap).collect())
                            .collect()
                    })
                    .collect();
                let basis_dim = basis.len();
                let generator_count = gen_matrices.len();
                Ok(PySpinorRep {
                    idempotent: idempotent.into_py_any(py)?,
                    basis: basis.into_py_any(py)?,
                    gen_matrices: gen_matrices.into_py_any(py)?,
                    is_left_regular,
                    diagonalized_metric: diagonalized_metric.into_py_any(py)?,
                    orthogonal_basis_in_original: orthogonal_basis_in_original.into_py_any(py)?,
                    basis_dim,
                    generator_count,
                })
            }

            /// Apply the lazy left-regular spinor action of generator `e_i` to a
            /// sparse module vector. This reaches dimensions where explicit
            /// `spinor_rep()` matrices are intentionally capped.
            fn apply_generator(&self, i: usize, v: &$mv) -> PyResult<$mv> {
                self.ensure_mv(v)?;
                let rep = scalar_boundary(|| crate::clifford::lazy_spinor_rep(&self.inner))?
                    .ok_or_else(|| {
                        PyValueError::new_err(
                            "lazy_spinor_rep needs a supported nondegenerate metric with no general-bilinear a-part",
                        )
                    })?;
                let mv = scalar_boundary(|| rep.apply_generator(i, &v.mv))?
                    .ok_or_else(|| PyValueError::new_err("generator index out of range"))?;
                Ok($mv {
                    alg: self.inner.clone(),
                    mv,
                })
            }

            /// Build the Rust `LazySpinorRep` façade for this backend.
            fn lazy_spinor_rep(&self, py: Python<'_>) -> PyResult<PyLazySpinorRep> {
                scalar_boundary(|| crate::clifford::lazy_spinor_rep(&self.inner))?
                    .ok_or_else(|| {
                        PyValueError::new_err(
                            "lazy_spinor_rep needs a supported nondegenerate metric with no general-bilinear a-part",
                        )
                    })?;
                Ok(PyLazySpinorRep {
                    algebra: self.clone().into_py_any(py)?,
                })
            }

            /// Apply the lazy left-regular spinor action of a vector
            /// `Σ coeffs[i] e_i` to a sparse module vector.
            fn apply_vector(
                &self,
                coeffs: Vec<Bound<'_, PyAny>>,
                v: &$mv,
            ) -> PyResult<$mv> {
                self.ensure_mv(v)?;
                let mut parsed = Vec::with_capacity(coeffs.len());
                for coeff in &coeffs {
                    parsed.push($parse(coeff)?);
                }
                let rep = scalar_boundary(|| crate::clifford::lazy_spinor_rep(&self.inner))?
                    .ok_or_else(|| {
                        PyValueError::new_err(
                            "lazy_spinor_rep needs a supported nondegenerate metric with no general-bilinear a-part",
                        )
                    })?;
                let mv = scalar_boundary(|| rep.apply_vector(&parsed, &v.mv))?
                    .ok_or_else(|| PyValueError::new_err("coefficient length must equal algebra dimension"))?;
                Ok($mv {
                    alg: self.inner.clone(),
                    mv,
                })
            }

            fn __repr__(&self) -> String {
                format!("{}(dim={})", $alg_name, self.inner.dim)
            }
        }

        impl $alg {
            fn ensure_mv(&self, mv: &$mv) -> PyResult<()> {
                if self.inner.as_ref() == mv.alg.as_ref() {
                    Ok(())
                } else {
                    Err(PyValueError::new_err(
                        "multivector belongs to a different Clifford algebra",
                    ))
                }
            }

            fn ensure_linear_map(&self, lm: &LinearMap<$scalar>) -> PyResult<()> {
                if lm.n != self.inner.dim {
                    return Err(PyValueError::new_err(format!(
                        "linear-map dimension {} does not match algebra dimension {}",
                        lm.n,
                        self.inner.dim
                    )));
                }
                Ok(())
            }
        }

        #[pyclass(name = $mv_name, module = "pleroma", from_py_object)]
        #[derive(Clone)]
        pub(crate) struct $mv {
            pub(crate) alg: Arc<CliffordAlgebra<$scalar>>,
            pub(crate) mv: Multivector<$scalar>,
        }

        impl $mv {
            fn ensure_same_algebra(&self, other: &$mv) -> PyResult<()> {
                if self.alg.as_ref() == other.alg.as_ref() {
                    Ok(())
                } else {
                    Err(PyValueError::new_err(
                        "multivectors belong to different Clifford algebras",
                    ))
                }
            }
        }

        #[pymethods]
        impl $mv {
            fn __add__(&self, other: &$mv) -> PyResult<$mv> {
                self.ensure_same_algebra(other)?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: self.alg.add(&self.mv, &other.mv),
                })
            }
            fn __sub__(&self, other: &$mv) -> PyResult<$mv> {
                self.ensure_same_algebra(other)?;
                let neg_one = <$scalar as Scalar>::one().neg();
                let neg = scalar_boundary(|| self.alg.scalar_mul(&neg_one, &other.mv))?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.add(&self.mv, &neg))?,
                })
            }
            fn __neg__(&self) -> PyResult<$mv> {
                let neg_one = <$scalar as Scalar>::one().neg();
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.scalar_mul(&neg_one, &self.mv))?,
                })
            }
            fn __mul__(&self, other: &Bound<'_, PyAny>) -> PyResult<$mv> {
                if let Ok(o) = other.cast::<$mv>() {
                    let other = o.borrow();
                    self.ensure_same_algebra(&other)?;
                    return Ok($mv {
                        alg: self.alg.clone(),
                        mv: scalar_boundary(|| self.alg.mul(&self.mv, &other.mv))?,
                    });
                }
                let s = $parse(other)?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.scalar_mul(&s, &self.mv))?,
                })
            }
            fn __rmul__(&self, other: &Bound<'_, PyAny>) -> PyResult<$mv> {
                let s = $parse(other)?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.scalar_mul(&s, &self.mv))?,
                })
            }
            fn __pow__(&self, n: u128, _modulo: Option<&Bound<'_, PyAny>>) -> PyResult<$mv> {
                let acc = scalar_boundary(|| {
                    let mut acc = self.alg.scalar(<$scalar as Scalar>::one());
                    let mut base = self.mv.clone();
                    let mut e = n;
                    while e > 0 {
                        if e & 1 == 1 {
                            acc = self.alg.mul(&acc, &base);
                        }
                        e >>= 1;
                        if e > 0 {
                            base = self.alg.mul(&base, &base);
                        }
                    }
                    acc
                })?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: acc,
                })
            }
            /// Exterior (wedge) product; also bound to the `^` operator.
            fn wedge(&self, other: &$mv) -> PyResult<$mv> {
                self.ensure_same_algebra(other)?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.wedge(&self.mv, &other.mv))?,
                })
            }
            fn __xor__(&self, other: &$mv) -> PyResult<$mv> {
                self.wedge(other)
            }
            fn reverse(&self) -> PyResult<$mv> {
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.reverse(&self.mv))?,
                })
            }
            /// `~v` is reversion.
            fn __invert__(&self) -> PyResult<$mv> {
                self.reverse()
            }
            fn grade_part(&self, k: usize) -> $mv {
                $mv {
                    alg: self.alg.clone(),
                    mv: self.alg.grade_part(&self.mv, k),
                }
            }
            fn grade_involution(&self) -> PyResult<$mv> {
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.grade_involution(&self.mv))?,
                })
            }
            /// Versor inverse v⁻¹ = ṽ/(v ṽ); errors if v isn't an invertible versor.
            fn versor_inverse(&self) -> PyResult<$mv> {
                scalar_boundary(|| self.alg.versor_inverse(&self.mv))?
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| PyValueError::new_err("not an invertible versor"))
            }
            /// The **general multivector inverse** (any invertible element, not
            /// just a versor) via the left-multiplication matrix. Errors if the
            /// element is a zero divisor / non-invertible.
            fn multivector_inverse(&self) -> PyResult<$mv> {
                scalar_boundary(|| self.alg.multivector_inverse(&self.mv))?
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| PyValueError::new_err("not invertible (zero divisor)"))
            }
            /// The **Cayley transform** `(1−B)(1+B)⁻¹` of this bivector — the exact
            /// rational map from the Lie algebra (bivectors) to the Spin group
            /// (rotors). Errors if `1+B` is not invertible.
            fn cayley(&self) -> PyResult<$mv> {
                scalar_boundary(|| self.alg.cayley(&self.mv))?
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| PyValueError::new_err("1+B not invertible"))
            }
            /// The inverse Cayley transform — a rotor back to its bivector
            /// generator (same involutive formula). Errors if `1+R` is singular.
            fn cayley_inverse(&self) -> PyResult<$mv> {
                scalar_boundary(|| self.alg.cayley_inverse(&self.mv))?
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| PyValueError::new_err("1+R not invertible"))
            }
            /// Sandwich self · x · self⁻¹ (rotor/versor action; untwisted).
            fn sandwich(&self, x: &$mv) -> PyResult<$mv> {
                self.ensure_same_algebra(x)?;
                scalar_boundary(|| self.alg.sandwich(&self.mv, &x.mv))?
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| PyValueError::new_err("not an invertible versor"))
            }
            /// Twisted adjoint (Pin/Spin action) α(self) · x · self⁻¹ — the correct
            /// versor action; for an odd versor it gives a genuine reflection.
            fn twisted_sandwich(&self, x: &$mv) -> PyResult<$mv> {
                self.ensure_same_algebra(x)?;
                scalar_boundary(|| self.alg.twisted_sandwich(&self.mv, &x.mv))?
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| PyValueError::new_err("not an invertible versor"))
            }
            /// Projection onto the even subalgebra (sum of even-grade blades).
            fn even_part(&self) -> PyResult<$mv> {
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.even_part(&self.mv))?,
                })
            }
            /// The exterior-Hopf coproduct Δ, returned as a multivector over the
            /// graded tensor square `Cl ⊗̂ Cl` (a tensor `e_T ⊗ e_U` is the blade
            /// `T | (U << dim)`).
            fn coproduct(&self) -> PyResult<$mv> {
                if self.alg.dim * 2 > MAX_BASIS_DIM {
                    return Err(PyValueError::new_err(format!(
                        "coproduct tensor encoding needs 2*dim <= {MAX_BASIS_DIM}"
                    )));
                }
                let tensor = self.alg.graded_tensor(&self.alg);
                let co = scalar_boundary(|| crate::clifford::coproduct(&self.alg, &self.mv))?;
                Ok($mv {
                    alg: Arc::new(tensor),
                    mv: co,
                })
            }
            /// The exterior-Hopf antipode (the grade involution `(−1)^k`).
            fn antipode(&self) -> PyResult<$mv> {
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| crate::clifford::antipode(&self.alg, &self.mv))?,
                })
            }
            /// The exterior-Hopf counit (the scalar part).
            fn counit(&self) -> PyResult<$scalar_py> {
                Ok($wrap(scalar_boundary(|| {
                    crate::clifford::counit(&self.alg, &self.mv)
                })?))
            }
            /// `exp(self)` for a nilpotent multivector — the terminating series
            /// `Σ selfᵏ/k!`. Errors if `self` is not nilpotent (a rotational motor,
            /// needing transcendental cos/sin).
            fn exp_nilpotent(&self) -> PyResult<$mv> {
                scalar_boundary(|| crate::clifford::exp_nilpotent(&self.alg, &self.mv))?
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| {
                        PyValueError::new_err("not nilpotent — would need a transcendental exp")
                    })
            }
            /// Reflect x in the hyperplane ⊥ self (self must be an invertible vector).
            fn reflect(&self, x: &$mv) -> PyResult<$mv> {
                self.ensure_same_algebra(x)?;
                scalar_boundary(|| self.alg.reflect(&self.mv, &x.mv))?
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| PyValueError::new_err("not an invertible vector"))
            }
            fn left_contract(&self, other: &$mv) -> PyResult<$mv> {
                self.ensure_same_algebra(other)?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.left_contract(&self.mv, &other.mv))?,
                })
            }
            fn right_contract(&self, other: &$mv) -> PyResult<$mv> {
                self.ensure_same_algebra(other)?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.right_contract(&self.mv, &other.mv))?,
                })
            }
            /// `<<` is left contraction, `>>` is right contraction.
            fn __lshift__(&self, other: &$mv) -> PyResult<$mv> {
                self.left_contract(other)
            }
            fn __rshift__(&self, other: &$mv) -> PyResult<$mv> {
                self.right_contract(other)
            }
            fn dual(&self) -> PyResult<$mv> {
                scalar_boundary(|| self.alg.dual(&self.mv))?
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| {
                        PyValueError::new_err("pseudoscalar not invertible (degenerate metric)")
                    })
            }
            /// The undual v ↦ v·I (inverse of `dual`).
            fn undual(&self) -> PyResult<$mv> {
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.undual(&self.mv))?,
                })
            }
            /// The Clifford (main) conjugate: reversion ∘ grade involution.
            fn clifford_conjugate(&self) -> PyResult<$mv> {
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.clifford_conjugate(&self.mv))?,
                })
            }
            /// The scalar product ⟨a b⟩₀ (grade-0 part of the geometric product).
            fn scalar_product(&self, other: &$mv) -> PyResult<$scalar_py> {
                self.ensure_same_algebra(other)?;
                Ok($wrap(scalar_boundary(|| {
                    self.alg.scalar_product(&self.mv, &other.mv)
                })?))
            }
            /// The commutator product [a,b] = ab − ba (no ½; char-faithful).
            fn commutator(&self, other: &$mv) -> PyResult<$mv> {
                self.ensure_same_algebra(other)?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.commutator(&self.mv, &other.mv))?,
                })
            }
            /// The anticommutator product {a,b} = ab + ba (no ½; char-faithful).
            fn anticommutator(&self, other: &$mv) -> PyResult<$mv> {
                self.ensure_same_algebra(other)?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.anticommutator(&self.mv, &other.mv))?,
                })
            }
            /// The regressive (meet) product a ∨ b — intersection dual to the
            /// wedge. Errors if the pseudoscalar is not invertible.
            fn meet(&self, other: &$mv) -> PyResult<$mv> {
                self.ensure_same_algebra(other)?;
                scalar_boundary(|| self.alg.meet(&self.mv, &other.mv))?
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| {
                        PyValueError::new_err("pseudoscalar not invertible (degenerate metric)")
                    })
            }
            /// Whether this multivector is a blade (a decomposable homogeneous
            /// element — a wedge of vectors).
            fn is_blade(&self) -> bool {
                crate::clifford::is_blade(&self.alg, &self.mv)
            }
            /// A basis of the blade subspace `{x : x ∧ A = 0}`, as coefficient
            /// rows over the algebra generators `e0, e1, ...`. Scalars return an
            /// empty basis; errors for zero or mixed-grade multivectors.
            fn blade_subspace(&self) -> PyResult<Vec<Vec<$scalar_py>>> {
                scalar_boundary(|| crate::clifford::blade_subspace(&self.alg, &self.mv))?
                    .map(|basis| {
                        basis
                            .into_iter()
                            .map(|row| row.into_iter().map($wrap).collect())
                            .collect()
                    })
                    .ok_or_else(|| {
                        PyValueError::new_err(
                            "blade_subspace needs a nonzero homogeneous multivector",
                        )
                    })
            }
            /// Factor a blade into the grade-1 vectors whose wedge is it; errors
            /// if it is not a blade.
            fn factor_blade(&self) -> PyResult<Vec<$mv>> {
                scalar_boundary(|| crate::clifford::factor_blade(&self.alg, &self.mv))?
                    .map(|vs| {
                        vs.into_iter()
                            .map(|mv| $mv {
                                alg: self.alg.clone(),
                                mv,
                            })
                            .collect()
                    })
                    .ok_or_else(|| PyValueError::new_err("not a blade (not decomposable)"))
            }
            fn norm2(&self) -> PyResult<$scalar_py> {
                Ok($wrap(scalar_boundary(|| self.alg.norm2(&self.mv))?))
            }
            /// The Dickson / grade parity of a homogeneous-parity versor candidate:
            /// `0` for even, `1` for odd, `None` for zero or mixed parity.
            fn versor_grade_parity(&self) -> Option<u128> {
                crate::clifford::versor_grade_parity(&self.mv)
            }
            /// Raw spinor norm `<v reverse(v)>_0`; errors when `v` is not an
            /// invertible simple versor. Reduce this scalar modulo squares (char != 2)
            /// or Artin-Schreier (char 2) in the caller's field when needed.
            fn spinor_norm(&self) -> PyResult<$scalar_py> {
                scalar_boundary(|| self.alg.spinor_norm(&self.mv))?
                    .map($wrap)
                    .ok_or_else(|| PyValueError::new_err("not an invertible simple versor"))
            }
            /// Classify a versor as a named `VersorClass` record.
            fn classify_versor(&self, py: Python<'_>) -> PyResult<PyVersorClass> {
                let class = scalar_boundary(|| self.alg.classify_versor(&self.mv))?
                    .ok_or_else(|| PyValueError::new_err("not an invertible simple versor"))?;
                Ok(PyVersorClass {
                    spinor_norm: $wrap(class.spinor_norm).into_py_any(py)?,
                    dickson: class.dickson,
                })
            }
            fn scalar_part(&self) -> PyResult<$scalar_py> {
                Ok($wrap(scalar_boundary(|| self.alg.scalar_part(&self.mv))?))
            }
            /// Division: by a scalar, or by a versor (multiply by its inverse).
            fn __truediv__(&self, other: &Bound<'_, PyAny>) -> PyResult<$mv> {
                if let Ok(o) = other.cast::<$mv>() {
                    let other = o.borrow();
                    self.ensure_same_algebra(&other)?;
                    let oinv = scalar_boundary(|| self.alg.versor_inverse(&other.mv))?
                        .ok_or_else(|| PyValueError::new_err("divisor not an invertible versor"))?;
                    return Ok($mv {
                        alg: self.alg.clone(),
                        mv: scalar_boundary(|| self.alg.mul(&self.mv, &oinv))?,
                    });
                }
                let s = $parse(other)?;
                let sinv = <$scalar as Scalar>::inv(&s)
                    .ok_or_else(|| PyValueError::new_err("scalar has no representable inverse"))?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: scalar_boundary(|| self.alg.scalar_mul(&sinv, &self.mv))?,
                })
            }
            #[getter]
            fn terms(&self) -> Vec<(u128, $scalar_py)> {
                self.mv
                    .terms
                    .iter()
                    .map(|(&mask, coeff)| (mask, $wrap(coeff.clone())))
                    .collect()
            }
            fn is_zero(&self) -> bool {
                self.mv.is_zero()
            }
            fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
                if let Ok(o) = other.cast::<$mv>() {
                    let other = o.borrow();
                    self.alg.as_ref() == other.alg.as_ref() && self.mv == other.mv
                } else {
                    false
                }
            }
            fn __repr__(&self) -> String {
                self.mv.display()
            }
        }
    };
}

backend!(
    NimberAlgebra,
    "NimberAlgebra",
    NimberMV,
    "NimberMV",
    NimberLinearMap,
    "NimberLinearMap",
    Nimber,
    parse_nimber,
    PyNimber,
    wrap_nimber
);
backend!(
    Fp2Algebra,
    "Fp2Algebra",
    Fp2MV,
    "Fp2MV",
    Fp2LinearMap,
    "Fp2LinearMap",
    Fp<2>,
    parse_fp2,
    PyFp2,
    wrap_fp2
);
backend!(
    Fp3Algebra,
    "Fp3Algebra",
    Fp3MV,
    "Fp3MV",
    Fp3LinearMap,
    "Fp3LinearMap",
    Fp<3>,
    parse_fp3,
    PyFp3,
    wrap_fp3
);
backend!(
    Fp5Algebra,
    "Fp5Algebra",
    Fp5MV,
    "Fp5MV",
    Fp5LinearMap,
    "Fp5LinearMap",
    Fp<5>,
    parse_fp5,
    PyFp5,
    wrap_fp5
);
backend!(
    Fp7Algebra,
    "Fp7Algebra",
    Fp7MV,
    "Fp7MV",
    Fp7LinearMap,
    "Fp7LinearMap",
    Fp<7>,
    parse_fp7,
    PyFp7,
    wrap_fp7
);
backend!(
    Fp11Algebra,
    "Fp11Algebra",
    Fp11MV,
    "Fp11MV",
    Fp11LinearMap,
    "Fp11LinearMap",
    Fp<11>,
    parse_fp11,
    PyFp11,
    wrap_fp11
);
backend!(
    Fp13Algebra,
    "Fp13Algebra",
    Fp13MV,
    "Fp13MV",
    Fp13LinearMap,
    "Fp13LinearMap",
    Fp<13>,
    parse_fp13,
    PyFp13,
    wrap_fp13
);
backend!(
    F4Algebra,
    "F4Algebra",
    F4MV,
    "F4MV",
    F4LinearMap,
    "F4LinearMap",
    Fpn<2, 2>,
    parse_f4,
    PyF4,
    wrap_f4
);
backend!(
    F8Algebra,
    "F8Algebra",
    F8MV,
    "F8MV",
    F8LinearMap,
    "F8LinearMap",
    Fpn<2, 3>,
    parse_f8,
    PyF8,
    wrap_f8
);
backend!(
    F16Algebra,
    "F16Algebra",
    F16MV,
    "F16MV",
    F16LinearMap,
    "F16LinearMap",
    Fpn<2, 4>,
    parse_f16,
    PyF16,
    wrap_f16
);
backend!(
    F9Algebra,
    "F9Algebra",
    F9MV,
    "F9MV",
    F9LinearMap,
    "F9LinearMap",
    Fpn<3, 2>,
    parse_f9,
    PyF9,
    wrap_f9
);
backend!(
    F25Algebra,
    "F25Algebra",
    F25MV,
    "F25MV",
    F25LinearMap,
    "F25LinearMap",
    Fpn<5, 2>,
    parse_f25,
    PyF25,
    wrap_f25
);
backend!(
    F27Algebra,
    "F27Algebra",
    F27MV,
    "F27MV",
    F27LinearMap,
    "F27LinearMap",
    Fpn<3, 3>,
    parse_f27,
    PyF27,
    wrap_f27
);
backend!(
    Zp2_4Algebra,
    "Zp2_4Algebra",
    Zp2_4MV,
    "Zp2_4MV",
    Zp2_4LinearMap,
    "Zp2_4LinearMap",
    Zp<2, 4>,
    parse_zp2_4,
    PyZp2_4,
    wrap_zp2_4
);
backend!(
    Zp3_4Algebra,
    "Zp3_4Algebra",
    Zp3_4MV,
    "Zp3_4MV",
    Zp3_4LinearMap,
    "Zp3_4LinearMap",
    Zp<3, 4>,
    parse_zp3_4,
    PyZp3_4,
    wrap_zp3_4
);
backend!(
    Zp5_4Algebra,
    "Zp5_4Algebra",
    Zp5_4MV,
    "Zp5_4MV",
    Zp5_4LinearMap,
    "Zp5_4LinearMap",
    Zp<5, 4>,
    parse_zp5_4,
    PyZp5_4,
    wrap_zp5_4
);
backend!(
    Zp7_4Algebra,
    "Zp7_4Algebra",
    Zp7_4MV,
    "Zp7_4MV",
    Zp7_4LinearMap,
    "Zp7_4LinearMap",
    Zp<7, 4>,
    parse_zp7_4,
    PyZp7_4,
    wrap_zp7_4
);
backend!(
    Zp11_4Algebra,
    "Zp11_4Algebra",
    Zp11_4MV,
    "Zp11_4MV",
    Zp11_4LinearMap,
    "Zp11_4LinearMap",
    Zp<11, 4>,
    parse_zp11_4,
    PyZp11_4,
    wrap_zp11_4
);
backend!(
    Zp13_4Algebra,
    "Zp13_4Algebra",
    Zp13_4MV,
    "Zp13_4MV",
    Zp13_4LinearMap,
    "Zp13_4LinearMap",
    Zp<13, 4>,
    parse_zp13_4,
    PyZp13_4,
    wrap_zp13_4
);
backend!(
    Qp2_4Algebra,
    "Qp2_4Algebra",
    Qp2_4MV,
    "Qp2_4MV",
    Qp2_4LinearMap,
    "Qp2_4LinearMap",
    Qp<2, 4>,
    parse_qp2_4,
    PyQp2_4,
    wrap_qp2_4
);
backend!(
    Qp3_4Algebra,
    "Qp3_4Algebra",
    Qp3_4MV,
    "Qp3_4MV",
    Qp3_4LinearMap,
    "Qp3_4LinearMap",
    Qp<3, 4>,
    parse_qp3_4,
    PyQp3_4,
    wrap_qp3_4
);
backend!(
    Qp5_4Algebra,
    "Qp5_4Algebra",
    Qp5_4MV,
    "Qp5_4MV",
    Qp5_4LinearMap,
    "Qp5_4LinearMap",
    Qp<5, 4>,
    parse_qp5_4,
    PyQp5_4,
    wrap_qp5_4
);
backend!(
    Qp7_4Algebra,
    "Qp7_4Algebra",
    Qp7_4MV,
    "Qp7_4MV",
    Qp7_4LinearMap,
    "Qp7_4LinearMap",
    Qp<7, 4>,
    parse_qp7_4,
    PyQp7_4,
    wrap_qp7_4
);
backend!(
    Qp11_4Algebra,
    "Qp11_4Algebra",
    Qp11_4MV,
    "Qp11_4MV",
    Qp11_4LinearMap,
    "Qp11_4LinearMap",
    Qp<11, 4>,
    parse_qp11_4,
    PyQp11_4,
    wrap_qp11_4
);
backend!(
    Qp13_4Algebra,
    "Qp13_4Algebra",
    Qp13_4MV,
    "Qp13_4MV",
    Qp13_4LinearMap,
    "Qp13_4LinearMap",
    Qp<13, 4>,
    parse_qp13_4,
    PyQp13_4,
    wrap_qp13_4
);
backend!(
    WittVec2_4_2Algebra,
    "WittVec2_4_2Algebra",
    WittVec2_4_2MV,
    "WittVec2_4_2MV",
    WittVec2_4_2LinearMap,
    "WittVec2_4_2LinearMap",
    WittVec<2, 4, 2>,
    parse_witt_vec2_4_2,
    PyWittVec2_4_2,
    wrap_witt_vec2_4_2
);
backend!(
    WittVec2_4_3Algebra,
    "WittVec2_4_3Algebra",
    WittVec2_4_3MV,
    "WittVec2_4_3MV",
    WittVec2_4_3LinearMap,
    "WittVec2_4_3LinearMap",
    WittVec<2, 4, 3>,
    parse_witt_vec2_4_3,
    PyWittVec2_4_3,
    wrap_witt_vec2_4_3
);
backend!(
    WittVec2_4_4Algebra,
    "WittVec2_4_4Algebra",
    WittVec2_4_4MV,
    "WittVec2_4_4MV",
    WittVec2_4_4LinearMap,
    "WittVec2_4_4LinearMap",
    WittVec<2, 4, 4>,
    parse_witt_vec2_4_4,
    PyWittVec2_4_4,
    wrap_witt_vec2_4_4
);
backend!(
    WittVec3_4_2Algebra,
    "WittVec3_4_2Algebra",
    WittVec3_4_2MV,
    "WittVec3_4_2MV",
    WittVec3_4_2LinearMap,
    "WittVec3_4_2LinearMap",
    WittVec<3, 4, 2>,
    parse_witt_vec3_4_2,
    PyWittVec3_4_2,
    wrap_witt_vec3_4_2
);
backend!(
    WittVec5_4_2Algebra,
    "WittVec5_4_2Algebra",
    WittVec5_4_2MV,
    "WittVec5_4_2MV",
    WittVec5_4_2LinearMap,
    "WittVec5_4_2LinearMap",
    WittVec<5, 4, 2>,
    parse_witt_vec5_4_2,
    PyWittVec5_4_2,
    wrap_witt_vec5_4_2
);
backend!(
    WittVec3_4_3Algebra,
    "WittVec3_4_3Algebra",
    WittVec3_4_3MV,
    "WittVec3_4_3MV",
    WittVec3_4_3LinearMap,
    "WittVec3_4_3LinearMap",
    WittVec<3, 4, 3>,
    parse_witt_vec3_4_3,
    PyWittVec3_4_3,
    wrap_witt_vec3_4_3
);
backend!(
    Qq2_4_2Algebra,
    "Qq2_4_2Algebra",
    Qq2_4_2MV,
    "Qq2_4_2MV",
    Qq2_4_2LinearMap,
    "Qq2_4_2LinearMap",
    Qq<2, 4, 2>,
    parse_qq2_4_2,
    PyQq2_4_2,
    wrap_qq2_4_2
);
backend!(
    Qq2_4_3Algebra,
    "Qq2_4_3Algebra",
    Qq2_4_3MV,
    "Qq2_4_3MV",
    Qq2_4_3LinearMap,
    "Qq2_4_3LinearMap",
    Qq<2, 4, 3>,
    parse_qq2_4_3,
    PyQq2_4_3,
    wrap_qq2_4_3
);
backend!(
    Qq2_4_4Algebra,
    "Qq2_4_4Algebra",
    Qq2_4_4MV,
    "Qq2_4_4MV",
    Qq2_4_4LinearMap,
    "Qq2_4_4LinearMap",
    Qq<2, 4, 4>,
    parse_qq2_4_4,
    PyQq2_4_4,
    wrap_qq2_4_4
);
backend!(
    Qq3_4_2Algebra,
    "Qq3_4_2Algebra",
    Qq3_4_2MV,
    "Qq3_4_2MV",
    Qq3_4_2LinearMap,
    "Qq3_4_2LinearMap",
    Qq<3, 4, 2>,
    parse_qq3_4_2,
    PyQq3_4_2,
    wrap_qq3_4_2
);
backend!(
    Qq5_4_2Algebra,
    "Qq5_4_2Algebra",
    Qq5_4_2MV,
    "Qq5_4_2MV",
    Qq5_4_2LinearMap,
    "Qq5_4_2LinearMap",
    Qq<5, 4, 2>,
    parse_qq5_4_2,
    PyQq5_4_2,
    wrap_qq5_4_2
);
backend!(
    Qq3_4_3Algebra,
    "Qq3_4_3Algebra",
    Qq3_4_3MV,
    "Qq3_4_3MV",
    Qq3_4_3LinearMap,
    "Qq3_4_3LinearMap",
    Qq<3, 4, 3>,
    parse_qq3_4_3,
    PyQq3_4_3,
    wrap_qq3_4_3
);
backend!(
    LaurentRational6Algebra,
    "LaurentRational_6Algebra",
    LaurentRational6MV,
    "LaurentRational_6MV",
    LaurentRational6LinearMap,
    "LaurentRational_6LinearMap",
    Laurent<Rational, 6>,
    parse_laurent_rational_6,
    PyLaurentRational6,
    wrap_laurent_rational_6
);
backend!(
    LaurentFp3_6Algebra,
    "LaurentFp3_6Algebra",
    LaurentFp3_6MV,
    "LaurentFp3_6MV",
    LaurentFp3_6LinearMap,
    "LaurentFp3_6LinearMap",
    Laurent<Fp<3>, 6>,
    parse_laurent_fp3_6,
    PyLaurentFp3_6,
    wrap_laurent_fp3_6
);
backend!(
    LaurentFp5_6Algebra,
    "LaurentFp5_6Algebra",
    LaurentFp5_6MV,
    "LaurentFp5_6MV",
    LaurentFp5_6LinearMap,
    "LaurentFp5_6LinearMap",
    Laurent<Fp<5>, 6>,
    parse_laurent_fp5_6,
    PyLaurentFp5_6,
    wrap_laurent_fp5_6
);
backend!(
    LaurentFp7_6Algebra,
    "LaurentFp7_6Algebra",
    LaurentFp7_6MV,
    "LaurentFp7_6MV",
    LaurentFp7_6LinearMap,
    "LaurentFp7_6LinearMap",
    Laurent<Fp<7>, 6>,
    parse_laurent_fp7_6,
    PyLaurentFp7_6,
    wrap_laurent_fp7_6
);
backend!(
    LaurentFp11_6Algebra,
    "LaurentFp11_6Algebra",
    LaurentFp11_6MV,
    "LaurentFp11_6MV",
    LaurentFp11_6LinearMap,
    "LaurentFp11_6LinearMap",
    Laurent<Fp<11>, 6>,
    parse_laurent_fp11_6,
    PyLaurentFp11_6,
    wrap_laurent_fp11_6
);
backend!(
    LaurentFp13_6Algebra,
    "LaurentFp13_6Algebra",
    LaurentFp13_6MV,
    "LaurentFp13_6MV",
    LaurentFp13_6LinearMap,
    "LaurentFp13_6LinearMap",
    Laurent<Fp<13>, 6>,
    parse_laurent_fp13_6,
    PyLaurentFp13_6,
    wrap_laurent_fp13_6
);
backend!(
    LaurentF9_6Algebra,
    "LaurentF9_6Algebra",
    LaurentF9_6MV,
    "LaurentF9_6MV",
    LaurentF9_6LinearMap,
    "LaurentF9_6LinearMap",
    Laurent<Fpn<3, 2>, 6>,
    parse_laurent_f9_6,
    PyLaurentF9_6,
    wrap_laurent_f9_6
);
backend!(
    LaurentF25_6Algebra,
    "LaurentF25_6Algebra",
    LaurentF25_6MV,
    "LaurentF25_6MV",
    LaurentF25_6LinearMap,
    "LaurentF25_6LinearMap",
    Laurent<Fpn<5, 2>, 6>,
    parse_laurent_f25_6,
    PyLaurentF25_6,
    wrap_laurent_f25_6
);
backend!(
    LaurentF27_6Algebra,
    "LaurentF27_6Algebra",
    LaurentF27_6MV,
    "LaurentF27_6MV",
    LaurentF27_6LinearMap,
    "LaurentF27_6LinearMap",
    Laurent<Fpn<3, 3>, 6>,
    parse_laurent_f27_6,
    PyLaurentF27_6,
    wrap_laurent_f27_6
);
backend!(
    RamifiedQp2_4E2Algebra,
    "RamifiedQp2_4_E2Algebra",
    RamifiedQp2_4E2MV,
    "RamifiedQp2_4_E2MV",
    RamifiedQp2_4E2LinearMap,
    "RamifiedQp2_4_E2LinearMap",
    Ramified<Qp<2, 4>, 2>,
    parse_ramified_qp2_4_e2,
    PyRamifiedQp2_4E2,
    wrap_ramified_qp2_4_e2
);
backend!(
    RamifiedQp3_4E2Algebra,
    "RamifiedQp3_4_E2Algebra",
    RamifiedQp3_4E2MV,
    "RamifiedQp3_4_E2MV",
    RamifiedQp3_4E2LinearMap,
    "RamifiedQp3_4_E2LinearMap",
    Ramified<Qp<3, 4>, 2>,
    parse_ramified_qp3_4_e2,
    PyRamifiedQp3_4E2,
    wrap_ramified_qp3_4_e2
);
backend!(
    RamifiedQp5_4E2Algebra,
    "RamifiedQp5_4_E2Algebra",
    RamifiedQp5_4E2MV,
    "RamifiedQp5_4_E2MV",
    RamifiedQp5_4E2LinearMap,
    "RamifiedQp5_4_E2LinearMap",
    Ramified<Qp<5, 4>, 2>,
    parse_ramified_qp5_4_e2,
    PyRamifiedQp5_4E2,
    wrap_ramified_qp5_4_e2
);
backend!(
    RamifiedQp7_4E2Algebra,
    "RamifiedQp7_4_E2Algebra",
    RamifiedQp7_4E2MV,
    "RamifiedQp7_4_E2MV",
    RamifiedQp7_4E2LinearMap,
    "RamifiedQp7_4_E2LinearMap",
    Ramified<Qp<7, 4>, 2>,
    parse_ramified_qp7_4_e2,
    PyRamifiedQp7_4E2,
    wrap_ramified_qp7_4_e2
);
backend!(
    RamifiedQp11_4E2Algebra,
    "RamifiedQp11_4_E2Algebra",
    RamifiedQp11_4E2MV,
    "RamifiedQp11_4_E2MV",
    RamifiedQp11_4E2LinearMap,
    "RamifiedQp11_4_E2LinearMap",
    Ramified<Qp<11, 4>, 2>,
    parse_ramified_qp11_4_e2,
    PyRamifiedQp11_4E2,
    wrap_ramified_qp11_4_e2
);
backend!(
    RamifiedQp13_4E2Algebra,
    "RamifiedQp13_4_E2Algebra",
    RamifiedQp13_4E2MV,
    "RamifiedQp13_4_E2MV",
    RamifiedQp13_4E2LinearMap,
    "RamifiedQp13_4_E2LinearMap",
    Ramified<Qp<13, 4>, 2>,
    parse_ramified_qp13_4_e2,
    PyRamifiedQp13_4E2,
    wrap_ramified_qp13_4_e2
);
backend!(
    RamifiedQp2_4E3Algebra,
    "RamifiedQp2_4_E3Algebra",
    RamifiedQp2_4E3MV,
    "RamifiedQp2_4_E3MV",
    RamifiedQp2_4E3LinearMap,
    "RamifiedQp2_4_E3LinearMap",
    Ramified<Qp<2, 4>, 3>,
    parse_ramified_qp2_4_e3,
    PyRamifiedQp2_4E3,
    wrap_ramified_qp2_4_e3
);
backend!(
    RamifiedQp3_4E3Algebra,
    "RamifiedQp3_4_E3Algebra",
    RamifiedQp3_4E3MV,
    "RamifiedQp3_4_E3MV",
    RamifiedQp3_4E3LinearMap,
    "RamifiedQp3_4_E3LinearMap",
    Ramified<Qp<3, 4>, 3>,
    parse_ramified_qp3_4_e3,
    PyRamifiedQp3_4E3,
    wrap_ramified_qp3_4_e3
);
backend!(
    RamifiedQp5_4E3Algebra,
    "RamifiedQp5_4_E3Algebra",
    RamifiedQp5_4E3MV,
    "RamifiedQp5_4_E3MV",
    RamifiedQp5_4E3LinearMap,
    "RamifiedQp5_4_E3LinearMap",
    Ramified<Qp<5, 4>, 3>,
    parse_ramified_qp5_4_e3,
    PyRamifiedQp5_4E3,
    wrap_ramified_qp5_4_e3
);
backend!(
    RamifiedQp7_4E3Algebra,
    "RamifiedQp7_4_E3Algebra",
    RamifiedQp7_4E3MV,
    "RamifiedQp7_4_E3MV",
    RamifiedQp7_4E3LinearMap,
    "RamifiedQp7_4_E3LinearMap",
    Ramified<Qp<7, 4>, 3>,
    parse_ramified_qp7_4_e3,
    PyRamifiedQp7_4E3,
    wrap_ramified_qp7_4_e3
);
backend!(
    RamifiedQp11_4E3Algebra,
    "RamifiedQp11_4_E3Algebra",
    RamifiedQp11_4E3MV,
    "RamifiedQp11_4_E3MV",
    RamifiedQp11_4E3LinearMap,
    "RamifiedQp11_4_E3LinearMap",
    Ramified<Qp<11, 4>, 3>,
    parse_ramified_qp11_4_e3,
    PyRamifiedQp11_4E3,
    wrap_ramified_qp11_4_e3
);
backend!(
    RamifiedQp13_4E3Algebra,
    "RamifiedQp13_4_E3Algebra",
    RamifiedQp13_4E3MV,
    "RamifiedQp13_4_E3MV",
    RamifiedQp13_4E3LinearMap,
    "RamifiedQp13_4_E3LinearMap",
    Ramified<Qp<13, 4>, 3>,
    parse_ramified_qp13_4_e3,
    PyRamifiedQp13_4E3,
    wrap_ramified_qp13_4_e3
);
backend!(
    GaussQp2_4Algebra,
    "GaussQp2_4Algebra",
    GaussQp2_4MV,
    "GaussQp2_4MV",
    GaussQp2_4LinearMap,
    "GaussQp2_4LinearMap",
    Gauss<Qp<2, 4>>,
    parse_gauss_qp2_4,
    PyGaussQp2_4,
    wrap_gauss_qp2_4
);
backend!(
    GaussQp3_4Algebra,
    "GaussQp3_4Algebra",
    GaussQp3_4MV,
    "GaussQp3_4MV",
    GaussQp3_4LinearMap,
    "GaussQp3_4LinearMap",
    Gauss<Qp<3, 4>>,
    parse_gauss_qp3_4,
    PyGaussQp3_4,
    wrap_gauss_qp3_4
);
backend!(
    GaussQp5_4Algebra,
    "GaussQp5_4Algebra",
    GaussQp5_4MV,
    "GaussQp5_4MV",
    GaussQp5_4LinearMap,
    "GaussQp5_4LinearMap",
    Gauss<Qp<5, 4>>,
    parse_gauss_qp5_4,
    PyGaussQp5_4,
    wrap_gauss_qp5_4
);
backend!(
    GaussQp7_4Algebra,
    "GaussQp7_4Algebra",
    GaussQp7_4MV,
    "GaussQp7_4MV",
    GaussQp7_4LinearMap,
    "GaussQp7_4LinearMap",
    Gauss<Qp<7, 4>>,
    parse_gauss_qp7_4,
    PyGaussQp7_4,
    wrap_gauss_qp7_4
);
backend!(
    GaussQp11_4Algebra,
    "GaussQp11_4Algebra",
    GaussQp11_4MV,
    "GaussQp11_4MV",
    GaussQp11_4LinearMap,
    "GaussQp11_4LinearMap",
    Gauss<Qp<11, 4>>,
    parse_gauss_qp11_4,
    PyGaussQp11_4,
    wrap_gauss_qp11_4
);
backend!(
    GaussQp13_4Algebra,
    "GaussQp13_4Algebra",
    GaussQp13_4MV,
    "GaussQp13_4MV",
    GaussQp13_4LinearMap,
    "GaussQp13_4LinearMap",
    Gauss<Qp<13, 4>>,
    parse_gauss_qp13_4,
    PyGaussQp13_4,
    wrap_gauss_qp13_4
);
// Exact function-field row over the main char-2 finite field: F_{2^128}[t].
backend!(
    NimberPolyAlgebra,
    "NimberPolyAlgebra",
    NimberPolyMV,
    "NimberPolyMV",
    NimberPolyLinearMap,
    "NimberPolyLinearMap",
    Poly<Nimber>,
    parse_nimber_poly,
    PyNimberPoly,
    wrap_nimber_poly
);
// Its fraction field F_{2^128}(t), the exact global function-field scalar.
backend!(
    NimberRationalFunctionAlgebra,
    "NimberRationalFunctionAlgebra",
    NimberRationalFunctionMV,
    "NimberRationalFunctionMV",
    NimberRationalFunctionLinearMap,
    "NimberRationalFunctionLinearMap",
    RationalFunction<Nimber>,
    parse_nimber_rational_function,
    PyNimberRationalFunction,
    wrap_nimber_rational_function
);
backend!(
    Fp2PolyAlgebra,
    "Fp2PolyAlgebra",
    Fp2PolyMV,
    "Fp2PolyMV",
    Fp2PolyLinearMap,
    "Fp2PolyLinearMap",
    Poly<Fp<2>>,
    parse_fp2_poly,
    PyFp2Poly,
    wrap_fp2_poly
);
backend!(
    Fp2RationalFunctionAlgebra,
    "Fp2RationalFunctionAlgebra",
    Fp2RationalFunctionMV,
    "Fp2RationalFunctionMV",
    Fp2RationalFunctionLinearMap,
    "Fp2RationalFunctionLinearMap",
    RationalFunction<Fp<2>>,
    parse_fp2_rational_function,
    PyFp2RationalFunction,
    wrap_fp2_rational_function
);
backend!(
    Fp3PolyAlgebra,
    "Fp3PolyAlgebra",
    Fp3PolyMV,
    "Fp3PolyMV",
    Fp3PolyLinearMap,
    "Fp3PolyLinearMap",
    Poly<Fp<3>>,
    parse_fp3_poly,
    PyFp3Poly,
    wrap_fp3_poly
);
backend!(
    Fp3RationalFunctionAlgebra,
    "Fp3RationalFunctionAlgebra",
    Fp3RationalFunctionMV,
    "Fp3RationalFunctionMV",
    Fp3RationalFunctionLinearMap,
    "Fp3RationalFunctionLinearMap",
    RationalFunction<Fp<3>>,
    parse_fp3_rational_function,
    PyFp3RationalFunction,
    wrap_fp3_rational_function
);
backend!(
    Fp5PolyAlgebra,
    "Fp5PolyAlgebra",
    Fp5PolyMV,
    "Fp5PolyMV",
    Fp5PolyLinearMap,
    "Fp5PolyLinearMap",
    Poly<Fp<5>>,
    parse_fp5_poly,
    PyFp5Poly,
    wrap_fp5_poly
);
backend!(
    Fp5RationalFunctionAlgebra,
    "Fp5RationalFunctionAlgebra",
    Fp5RationalFunctionMV,
    "Fp5RationalFunctionMV",
    Fp5RationalFunctionLinearMap,
    "Fp5RationalFunctionLinearMap",
    RationalFunction<Fp<5>>,
    parse_fp5_rational_function,
    PyFp5RationalFunction,
    wrap_fp5_rational_function
);
backend!(
    Fp7PolyAlgebra,
    "Fp7PolyAlgebra",
    Fp7PolyMV,
    "Fp7PolyMV",
    Fp7PolyLinearMap,
    "Fp7PolyLinearMap",
    Poly<Fp<7>>,
    parse_fp7_poly,
    PyFp7Poly,
    wrap_fp7_poly
);
backend!(
    Fp7RationalFunctionAlgebra,
    "Fp7RationalFunctionAlgebra",
    Fp7RationalFunctionMV,
    "Fp7RationalFunctionMV",
    Fp7RationalFunctionLinearMap,
    "Fp7RationalFunctionLinearMap",
    RationalFunction<Fp<7>>,
    parse_fp7_rational_function,
    PyFp7RationalFunction,
    wrap_fp7_rational_function
);
backend!(
    Fp11PolyAlgebra,
    "Fp11PolyAlgebra",
    Fp11PolyMV,
    "Fp11PolyMV",
    Fp11PolyLinearMap,
    "Fp11PolyLinearMap",
    Poly<Fp<11>>,
    parse_fp11_poly,
    PyFp11Poly,
    wrap_fp11_poly
);
backend!(
    Fp11RationalFunctionAlgebra,
    "Fp11RationalFunctionAlgebra",
    Fp11RationalFunctionMV,
    "Fp11RationalFunctionMV",
    Fp11RationalFunctionLinearMap,
    "Fp11RationalFunctionLinearMap",
    RationalFunction<Fp<11>>,
    parse_fp11_rational_function,
    PyFp11RationalFunction,
    wrap_fp11_rational_function
);
backend!(
    Fp13PolyAlgebra,
    "Fp13PolyAlgebra",
    Fp13PolyMV,
    "Fp13PolyMV",
    Fp13PolyLinearMap,
    "Fp13PolyLinearMap",
    Poly<Fp<13>>,
    parse_fp13_poly,
    PyFp13Poly,
    wrap_fp13_poly
);
backend!(
    Fp13RationalFunctionAlgebra,
    "Fp13RationalFunctionAlgebra",
    Fp13RationalFunctionMV,
    "Fp13RationalFunctionMV",
    Fp13RationalFunctionLinearMap,
    "Fp13RationalFunctionLinearMap",
    RationalFunction<Fp<13>>,
    parse_fp13_rational_function,
    PyFp13RationalFunction,
    wrap_fp13_rational_function
);
// Exact ℚ backend: exposed for Rust parity and for rational Clifford/lattice bridges.
backend!(
    RationalAlgebra,
    "RationalAlgebra",
    RationalMV,
    "RationalMV",
    RationalLinearMap,
    "RationalLinearMap",
    Rational,
    parse_rational,
    PyRational,
    wrap_rational
);
backend!(
    AdeleAlgebra,
    "AdeleAlgebra",
    AdeleMV,
    "AdeleMV",
    AdeleLinearMap,
    "AdeleLinearMap",
    Adele,
    parse_adele,
    PyAdele,
    wrap_adele
);
backend!(
    SurrealAlgebra,
    "SurrealAlgebra",
    SurrealMV,
    "SurrealMV",
    SurrealLinearMap,
    "SurrealLinearMap",
    Surreal,
    parse_surreal,
    PySurreal,
    wrap_surreal
);
backend!(
    SurcomplexAlgebra,
    "SurcomplexAlgebra",
    SurcomplexMV,
    "SurcomplexMV",
    SurcomplexLinearMap,
    "SurcomplexLinearMap",
    Surcomplex<Surreal>,
    parse_surcomplex,
    PySurcomplex,
    wrap_surcomplex
);
// ℤ-coefficient backend: the home of the exterior algebra of the game group.
backend!(
    IntegerAlgebra,
    "IntegerAlgebra",
    IntegerMV,
    "IntegerMV",
    IntegerLinearMap,
    "IntegerLinearMap",
    Integer,
    parse_integer,
    PyInteger,
    wrap_integer
);
// Omnific-integer backend: the surreal mirror of ℤ — exterior algebra over a
// transfinite ring (ω-scale coefficients).
backend!(
    OmnificAlgebra,
    "OmnificAlgebra",
    OmnificMV,
    "OmnificMV",
    OmnificLinearMap,
    "OmnificLinearMap",
    Omnific,
    parse_omnific,
    PyOmnific,
    wrap_omnific
);
// Transfinite ordinal nimber backend: exact inside the source-verified checked
// Kummer tower, with Rust returning `None` / panicking on escapes depending on API.
backend!(
    OrdinalAlgebra,
    "OrdinalAlgebra",
    OrdinalMV,
    "OrdinalMV",
    OrdinalLinearMap,
    "OrdinalLinearMap",
    Ordinal,
    parse_ordinal,
    PyOrdinal,
    wrap_ordinal
);

macro_rules! divided_power_backend {
    ($alg:ident, $alg_name:literal, $vec:ident, $vec_name:literal, $scalar:ty, $parse:path, $scalar_py:ty, $wrap:path) => {
        #[pyclass(name = $alg_name, module = "pleroma", from_py_object)]
        #[derive(Clone)]
        struct $alg {
            inner: Arc<DividedPowerAlgebra>,
        }

        #[pyclass(name = $vec_name, module = "pleroma", from_py_object)]
        #[derive(Clone)]
        struct $vec {
            alg: Arc<DividedPowerAlgebra>,
            vec: DpVector<$scalar>,
        }

        impl $alg {
            fn wrap(&self, vec: DpVector<$scalar>) -> $vec {
                $vec {
                    alg: self.inner.clone(),
                    vec,
                }
            }

            fn ensure_vec(&self, x: &$vec) -> PyResult<()> {
                if self.inner.as_ref() == x.alg.as_ref() {
                    Ok(())
                } else {
                    Err(PyValueError::new_err(
                        "divided-power vector belongs to a different algebra",
                    ))
                }
            }
        }

        #[pymethods]
        impl $alg {
            #[new]
            fn new(dim: usize) -> Self {
                $alg {
                    inner: Arc::new(DividedPowerAlgebra::new(dim)),
                }
            }
            #[getter]
            fn dim(&self) -> usize {
                self.inner.dim
            }
            fn zero(&self) -> $vec {
                self.wrap(self.inner.zero::<$scalar>())
            }
            fn one(&self) -> $vec {
                self.wrap(self.inner.one::<$scalar>())
            }
            fn scalar(&self, s: &Bound<'_, PyAny>) -> PyResult<$vec> {
                Ok(self.wrap(self.inner.scalar::<$scalar>($parse(s)?)))
            }
            fn divided_power(&self, i: usize, k: u128) -> PyResult<$vec> {
                if i >= self.inner.dim {
                    return Err(PyValueError::new_err("generator index out of range"));
                }
                Ok(self.wrap(self.inner.divided_power::<$scalar>(i, k)))
            }
            fn gen(&self, i: usize) -> PyResult<$vec> {
                if i >= self.inner.dim {
                    return Err(PyValueError::new_err("generator index out of range"));
                }
                Ok(self.wrap(self.inner.gen::<$scalar>(i)))
            }
            fn monomial(&self, alpha: Vec<u128>, coeff: &Bound<'_, PyAny>) -> PyResult<$vec> {
                if alpha.len() > self.inner.dim {
                    return Err(PyValueError::new_err("multidegree longer than dim"));
                }
                Ok(self.wrap(self.inner.monomial::<$scalar>(&alpha, $parse(coeff)?)))
            }
            fn add(&self, x: &$vec, y: &$vec) -> PyResult<$vec> {
                self.ensure_vec(x)?;
                self.ensure_vec(y)?;
                Ok(self.wrap(self.inner.add(&x.vec, &y.vec)))
            }
            fn scalar_mul(&self, s: &Bound<'_, PyAny>, x: &$vec) -> PyResult<$vec> {
                self.ensure_vec(x)?;
                let s = $parse(s)?;
                Ok(self.wrap(scalar_boundary(|| self.inner.scalar_mul(&s, &x.vec))?))
            }
            fn mul(&self, x: &$vec, y: &$vec) -> PyResult<$vec> {
                self.ensure_vec(x)?;
                self.ensure_vec(y)?;
                Ok(self.wrap(scalar_boundary(|| self.inner.mul(&x.vec, &y.vec))?))
            }
            fn coproduct(&self, x: &$vec) -> PyResult<Vec<(Vec<u128>, Vec<u128>, $scalar_py)>> {
                self.ensure_vec(x)?;
                Ok(self
                    .inner
                    .coproduct(&x.vec)
                    .into_iter()
                    .map(|((left, right), coeff)| (left, right, $wrap(coeff)))
                    .collect())
            }
            fn counit(&self, x: &$vec) -> PyResult<$scalar_py> {
                self.ensure_vec(x)?;
                Ok($wrap(self.inner.counit(&x.vec)))
            }
            fn antipode(&self, x: &$vec) -> PyResult<$vec> {
                self.ensure_vec(x)?;
                Ok(self.wrap(scalar_boundary(|| self.inner.antipode(&x.vec))?))
            }
            fn __repr__(&self) -> String {
                format!("{}(dim={})", $alg_name, self.inner.dim)
            }
        }

        impl $vec {
            fn ensure_same_algebra(&self, other: &$vec) -> PyResult<()> {
                if self.alg.as_ref() == other.alg.as_ref() {
                    Ok(())
                } else {
                    Err(PyValueError::new_err(
                        "divided-power vectors belong to different algebras",
                    ))
                }
            }

            fn wrap(&self, vec: DpVector<$scalar>) -> $vec {
                $vec {
                    alg: self.alg.clone(),
                    vec,
                }
            }
        }

        #[pymethods]
        impl $vec {
            #[getter]
            fn terms(&self) -> Vec<(Vec<u128>, $scalar_py)> {
                self.vec
                    .terms
                    .iter()
                    .map(|(degree, coeff)| (degree.clone(), $wrap(coeff.clone())))
                    .collect()
            }
            fn is_zero(&self) -> bool {
                self.vec.terms.is_empty()
            }
            fn __add__(&self, other: &$vec) -> PyResult<$vec> {
                self.ensure_same_algebra(other)?;
                Ok(self.wrap(self.alg.add(&self.vec, &other.vec)))
            }
            fn __sub__(&self, other: &$vec) -> PyResult<$vec> {
                self.ensure_same_algebra(other)?;
                let neg_one = <$scalar as Scalar>::one().neg();
                let neg = scalar_boundary(|| self.alg.scalar_mul(&neg_one, &other.vec))?;
                Ok(self.wrap(scalar_boundary(|| self.alg.add(&self.vec, &neg))?))
            }
            fn __neg__(&self) -> PyResult<$vec> {
                let neg_one = <$scalar as Scalar>::one().neg();
                Ok(self.wrap(scalar_boundary(|| {
                    self.alg.scalar_mul(&neg_one, &self.vec)
                })?))
            }
            fn __mul__(&self, other: &$vec) -> PyResult<$vec> {
                self.ensure_same_algebra(other)?;
                Ok(self.wrap(scalar_boundary(|| self.alg.mul(&self.vec, &other.vec))?))
            }
            fn scale(&self, s: &Bound<'_, PyAny>) -> PyResult<$vec> {
                let s = $parse(s)?;
                Ok(self.wrap(scalar_boundary(|| self.alg.scalar_mul(&s, &self.vec))?))
            }
            fn __rmul__(&self, s: &Bound<'_, PyAny>) -> PyResult<$vec> {
                self.scale(s)
            }
            fn coproduct(&self) -> Vec<(Vec<u128>, Vec<u128>, $scalar_py)> {
                self.alg
                    .coproduct(&self.vec)
                    .into_iter()
                    .map(|((left, right), coeff)| (left, right, $wrap(coeff)))
                    .collect()
            }
            fn counit(&self) -> $scalar_py {
                $wrap(self.alg.counit(&self.vec))
            }
            fn antipode(&self) -> PyResult<$vec> {
                Ok(self.wrap(scalar_boundary(|| self.alg.antipode(&self.vec))?))
            }
            fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
                if let Ok(o) = other.cast::<$vec>() {
                    let other = o.borrow();
                    self.alg.as_ref() == other.alg.as_ref() && self.vec == other.vec
                } else {
                    false
                }
            }
            fn __repr__(&self) -> String {
                format!("{:?}", self.vec)
            }
        }
    };
}

divided_power_backend!(
    NimberDividedPowerAlgebra,
    "NimberDividedPowerAlgebra",
    NimberDpVector,
    "NimberDpVector",
    Nimber,
    parse_nimber,
    PyNimber,
    wrap_nimber
);
divided_power_backend!(
    Fp2DividedPowerAlgebra,
    "Fp2DividedPowerAlgebra",
    Fp2DpVector,
    "Fp2DpVector",
    Fp<2>,
    parse_fp2,
    PyFp2,
    wrap_fp2
);
divided_power_backend!(
    Fp3DividedPowerAlgebra,
    "Fp3DividedPowerAlgebra",
    Fp3DpVector,
    "Fp3DpVector",
    Fp<3>,
    parse_fp3,
    PyFp3,
    wrap_fp3
);
divided_power_backend!(
    Fp5DividedPowerAlgebra,
    "Fp5DividedPowerAlgebra",
    Fp5DpVector,
    "Fp5DpVector",
    Fp<5>,
    parse_fp5,
    PyFp5,
    wrap_fp5
);
divided_power_backend!(
    Fp7DividedPowerAlgebra,
    "Fp7DividedPowerAlgebra",
    Fp7DpVector,
    "Fp7DpVector",
    Fp<7>,
    parse_fp7,
    PyFp7,
    wrap_fp7
);
divided_power_backend!(
    Fp11DividedPowerAlgebra,
    "Fp11DividedPowerAlgebra",
    Fp11DpVector,
    "Fp11DpVector",
    Fp<11>,
    parse_fp11,
    PyFp11,
    wrap_fp11
);
divided_power_backend!(
    Fp13DividedPowerAlgebra,
    "Fp13DividedPowerAlgebra",
    Fp13DpVector,
    "Fp13DpVector",
    Fp<13>,
    parse_fp13,
    PyFp13,
    wrap_fp13
);
divided_power_backend!(
    F4DividedPowerAlgebra,
    "F4DividedPowerAlgebra",
    F4DpVector,
    "F4DpVector",
    Fpn<2, 2>,
    parse_f4,
    PyF4,
    wrap_f4
);
divided_power_backend!(
    F8DividedPowerAlgebra,
    "F8DividedPowerAlgebra",
    F8DpVector,
    "F8DpVector",
    Fpn<2, 3>,
    parse_f8,
    PyF8,
    wrap_f8
);
divided_power_backend!(
    F16DividedPowerAlgebra,
    "F16DividedPowerAlgebra",
    F16DpVector,
    "F16DpVector",
    Fpn<2, 4>,
    parse_f16,
    PyF16,
    wrap_f16
);
divided_power_backend!(
    F9DividedPowerAlgebra,
    "F9DividedPowerAlgebra",
    F9DpVector,
    "F9DpVector",
    Fpn<3, 2>,
    parse_f9,
    PyF9,
    wrap_f9
);
divided_power_backend!(
    F25DividedPowerAlgebra,
    "F25DividedPowerAlgebra",
    F25DpVector,
    "F25DpVector",
    Fpn<5, 2>,
    parse_f25,
    PyF25,
    wrap_f25
);
divided_power_backend!(
    F27DividedPowerAlgebra,
    "F27DividedPowerAlgebra",
    F27DpVector,
    "F27DpVector",
    Fpn<3, 3>,
    parse_f27,
    PyF27,
    wrap_f27
);
divided_power_backend!(
    Zp2_4DividedPowerAlgebra,
    "Zp2_4DividedPowerAlgebra",
    Zp2_4DpVector,
    "Zp2_4DpVector",
    Zp<2, 4>,
    parse_zp2_4,
    PyZp2_4,
    wrap_zp2_4
);
divided_power_backend!(
    Zp3_4DividedPowerAlgebra,
    "Zp3_4DividedPowerAlgebra",
    Zp3_4DpVector,
    "Zp3_4DpVector",
    Zp<3, 4>,
    parse_zp3_4,
    PyZp3_4,
    wrap_zp3_4
);
divided_power_backend!(
    Zp5_4DividedPowerAlgebra,
    "Zp5_4DividedPowerAlgebra",
    Zp5_4DpVector,
    "Zp5_4DpVector",
    Zp<5, 4>,
    parse_zp5_4,
    PyZp5_4,
    wrap_zp5_4
);
divided_power_backend!(
    Zp7_4DividedPowerAlgebra,
    "Zp7_4DividedPowerAlgebra",
    Zp7_4DpVector,
    "Zp7_4DpVector",
    Zp<7, 4>,
    parse_zp7_4,
    PyZp7_4,
    wrap_zp7_4
);
divided_power_backend!(
    Zp11_4DividedPowerAlgebra,
    "Zp11_4DividedPowerAlgebra",
    Zp11_4DpVector,
    "Zp11_4DpVector",
    Zp<11, 4>,
    parse_zp11_4,
    PyZp11_4,
    wrap_zp11_4
);
divided_power_backend!(
    Zp13_4DividedPowerAlgebra,
    "Zp13_4DividedPowerAlgebra",
    Zp13_4DpVector,
    "Zp13_4DpVector",
    Zp<13, 4>,
    parse_zp13_4,
    PyZp13_4,
    wrap_zp13_4
);
divided_power_backend!(
    Qp2_4DividedPowerAlgebra,
    "Qp2_4DividedPowerAlgebra",
    Qp2_4DpVector,
    "Qp2_4DpVector",
    Qp<2, 4>,
    parse_qp2_4,
    PyQp2_4,
    wrap_qp2_4
);
divided_power_backend!(
    Qp3_4DividedPowerAlgebra,
    "Qp3_4DividedPowerAlgebra",
    Qp3_4DpVector,
    "Qp3_4DpVector",
    Qp<3, 4>,
    parse_qp3_4,
    PyQp3_4,
    wrap_qp3_4
);
divided_power_backend!(
    Qp5_4DividedPowerAlgebra,
    "Qp5_4DividedPowerAlgebra",
    Qp5_4DpVector,
    "Qp5_4DpVector",
    Qp<5, 4>,
    parse_qp5_4,
    PyQp5_4,
    wrap_qp5_4
);
divided_power_backend!(
    Qp7_4DividedPowerAlgebra,
    "Qp7_4DividedPowerAlgebra",
    Qp7_4DpVector,
    "Qp7_4DpVector",
    Qp<7, 4>,
    parse_qp7_4,
    PyQp7_4,
    wrap_qp7_4
);
divided_power_backend!(
    Qp11_4DividedPowerAlgebra,
    "Qp11_4DividedPowerAlgebra",
    Qp11_4DpVector,
    "Qp11_4DpVector",
    Qp<11, 4>,
    parse_qp11_4,
    PyQp11_4,
    wrap_qp11_4
);
divided_power_backend!(
    Qp13_4DividedPowerAlgebra,
    "Qp13_4DividedPowerAlgebra",
    Qp13_4DpVector,
    "Qp13_4DpVector",
    Qp<13, 4>,
    parse_qp13_4,
    PyQp13_4,
    wrap_qp13_4
);
divided_power_backend!(
    WittVec2_4_2DividedPowerAlgebra,
    "WittVec2_4_2DividedPowerAlgebra",
    WittVec2_4_2DpVector,
    "WittVec2_4_2DpVector",
    WittVec<2, 4, 2>,
    parse_witt_vec2_4_2,
    PyWittVec2_4_2,
    wrap_witt_vec2_4_2
);
divided_power_backend!(
    WittVec2_4_3DividedPowerAlgebra,
    "WittVec2_4_3DividedPowerAlgebra",
    WittVec2_4_3DpVector,
    "WittVec2_4_3DpVector",
    WittVec<2, 4, 3>,
    parse_witt_vec2_4_3,
    PyWittVec2_4_3,
    wrap_witt_vec2_4_3
);
divided_power_backend!(
    WittVec2_4_4DividedPowerAlgebra,
    "WittVec2_4_4DividedPowerAlgebra",
    WittVec2_4_4DpVector,
    "WittVec2_4_4DpVector",
    WittVec<2, 4, 4>,
    parse_witt_vec2_4_4,
    PyWittVec2_4_4,
    wrap_witt_vec2_4_4
);
divided_power_backend!(
    WittVec3_4_2DividedPowerAlgebra,
    "WittVec3_4_2DividedPowerAlgebra",
    WittVec3_4_2DpVector,
    "WittVec3_4_2DpVector",
    WittVec<3, 4, 2>,
    parse_witt_vec3_4_2,
    PyWittVec3_4_2,
    wrap_witt_vec3_4_2
);
divided_power_backend!(
    WittVec5_4_2DividedPowerAlgebra,
    "WittVec5_4_2DividedPowerAlgebra",
    WittVec5_4_2DpVector,
    "WittVec5_4_2DpVector",
    WittVec<5, 4, 2>,
    parse_witt_vec5_4_2,
    PyWittVec5_4_2,
    wrap_witt_vec5_4_2
);
divided_power_backend!(
    WittVec3_4_3DividedPowerAlgebra,
    "WittVec3_4_3DividedPowerAlgebra",
    WittVec3_4_3DpVector,
    "WittVec3_4_3DpVector",
    WittVec<3, 4, 3>,
    parse_witt_vec3_4_3,
    PyWittVec3_4_3,
    wrap_witt_vec3_4_3
);
divided_power_backend!(
    Qq2_4_2DividedPowerAlgebra,
    "Qq2_4_2DividedPowerAlgebra",
    Qq2_4_2DpVector,
    "Qq2_4_2DpVector",
    Qq<2, 4, 2>,
    parse_qq2_4_2,
    PyQq2_4_2,
    wrap_qq2_4_2
);
divided_power_backend!(
    Qq2_4_3DividedPowerAlgebra,
    "Qq2_4_3DividedPowerAlgebra",
    Qq2_4_3DpVector,
    "Qq2_4_3DpVector",
    Qq<2, 4, 3>,
    parse_qq2_4_3,
    PyQq2_4_3,
    wrap_qq2_4_3
);
divided_power_backend!(
    Qq2_4_4DividedPowerAlgebra,
    "Qq2_4_4DividedPowerAlgebra",
    Qq2_4_4DpVector,
    "Qq2_4_4DpVector",
    Qq<2, 4, 4>,
    parse_qq2_4_4,
    PyQq2_4_4,
    wrap_qq2_4_4
);
divided_power_backend!(
    Qq3_4_2DividedPowerAlgebra,
    "Qq3_4_2DividedPowerAlgebra",
    Qq3_4_2DpVector,
    "Qq3_4_2DpVector",
    Qq<3, 4, 2>,
    parse_qq3_4_2,
    PyQq3_4_2,
    wrap_qq3_4_2
);
divided_power_backend!(
    Qq5_4_2DividedPowerAlgebra,
    "Qq5_4_2DividedPowerAlgebra",
    Qq5_4_2DpVector,
    "Qq5_4_2DpVector",
    Qq<5, 4, 2>,
    parse_qq5_4_2,
    PyQq5_4_2,
    wrap_qq5_4_2
);
divided_power_backend!(
    Qq3_4_3DividedPowerAlgebra,
    "Qq3_4_3DividedPowerAlgebra",
    Qq3_4_3DpVector,
    "Qq3_4_3DpVector",
    Qq<3, 4, 3>,
    parse_qq3_4_3,
    PyQq3_4_3,
    wrap_qq3_4_3
);
divided_power_backend!(
    LaurentRational6DividedPowerAlgebra,
    "LaurentRational_6DividedPowerAlgebra",
    LaurentRational6DpVector,
    "LaurentRational_6DpVector",
    Laurent<Rational, 6>,
    parse_laurent_rational_6,
    PyLaurentRational6,
    wrap_laurent_rational_6
);
divided_power_backend!(
    LaurentFp3_6DividedPowerAlgebra,
    "LaurentFp3_6DividedPowerAlgebra",
    LaurentFp3_6DpVector,
    "LaurentFp3_6DpVector",
    Laurent<Fp<3>, 6>,
    parse_laurent_fp3_6,
    PyLaurentFp3_6,
    wrap_laurent_fp3_6
);
divided_power_backend!(
    LaurentFp5_6DividedPowerAlgebra,
    "LaurentFp5_6DividedPowerAlgebra",
    LaurentFp5_6DpVector,
    "LaurentFp5_6DpVector",
    Laurent<Fp<5>, 6>,
    parse_laurent_fp5_6,
    PyLaurentFp5_6,
    wrap_laurent_fp5_6
);
divided_power_backend!(
    LaurentFp7_6DividedPowerAlgebra,
    "LaurentFp7_6DividedPowerAlgebra",
    LaurentFp7_6DpVector,
    "LaurentFp7_6DpVector",
    Laurent<Fp<7>, 6>,
    parse_laurent_fp7_6,
    PyLaurentFp7_6,
    wrap_laurent_fp7_6
);
divided_power_backend!(
    LaurentFp11_6DividedPowerAlgebra,
    "LaurentFp11_6DividedPowerAlgebra",
    LaurentFp11_6DpVector,
    "LaurentFp11_6DpVector",
    Laurent<Fp<11>, 6>,
    parse_laurent_fp11_6,
    PyLaurentFp11_6,
    wrap_laurent_fp11_6
);
divided_power_backend!(
    LaurentFp13_6DividedPowerAlgebra,
    "LaurentFp13_6DividedPowerAlgebra",
    LaurentFp13_6DpVector,
    "LaurentFp13_6DpVector",
    Laurent<Fp<13>, 6>,
    parse_laurent_fp13_6,
    PyLaurentFp13_6,
    wrap_laurent_fp13_6
);
divided_power_backend!(
    LaurentF9_6DividedPowerAlgebra,
    "LaurentF9_6DividedPowerAlgebra",
    LaurentF9_6DpVector,
    "LaurentF9_6DpVector",
    Laurent<Fpn<3, 2>, 6>,
    parse_laurent_f9_6,
    PyLaurentF9_6,
    wrap_laurent_f9_6
);
divided_power_backend!(
    LaurentF25_6DividedPowerAlgebra,
    "LaurentF25_6DividedPowerAlgebra",
    LaurentF25_6DpVector,
    "LaurentF25_6DpVector",
    Laurent<Fpn<5, 2>, 6>,
    parse_laurent_f25_6,
    PyLaurentF25_6,
    wrap_laurent_f25_6
);
divided_power_backend!(
    LaurentF27_6DividedPowerAlgebra,
    "LaurentF27_6DividedPowerAlgebra",
    LaurentF27_6DpVector,
    "LaurentF27_6DpVector",
    Laurent<Fpn<3, 3>, 6>,
    parse_laurent_f27_6,
    PyLaurentF27_6,
    wrap_laurent_f27_6
);
divided_power_backend!(
    RamifiedQp2_4E2DividedPowerAlgebra,
    "RamifiedQp2_4_E2DividedPowerAlgebra",
    RamifiedQp2_4E2DpVector,
    "RamifiedQp2_4_E2DpVector",
    Ramified<Qp<2, 4>, 2>,
    parse_ramified_qp2_4_e2,
    PyRamifiedQp2_4E2,
    wrap_ramified_qp2_4_e2
);
divided_power_backend!(
    RamifiedQp3_4E2DividedPowerAlgebra,
    "RamifiedQp3_4_E2DividedPowerAlgebra",
    RamifiedQp3_4E2DpVector,
    "RamifiedQp3_4_E2DpVector",
    Ramified<Qp<3, 4>, 2>,
    parse_ramified_qp3_4_e2,
    PyRamifiedQp3_4E2,
    wrap_ramified_qp3_4_e2
);
divided_power_backend!(
    RamifiedQp5_4E2DividedPowerAlgebra,
    "RamifiedQp5_4_E2DividedPowerAlgebra",
    RamifiedQp5_4E2DpVector,
    "RamifiedQp5_4_E2DpVector",
    Ramified<Qp<5, 4>, 2>,
    parse_ramified_qp5_4_e2,
    PyRamifiedQp5_4E2,
    wrap_ramified_qp5_4_e2
);
divided_power_backend!(
    RamifiedQp7_4E2DividedPowerAlgebra,
    "RamifiedQp7_4_E2DividedPowerAlgebra",
    RamifiedQp7_4E2DpVector,
    "RamifiedQp7_4_E2DpVector",
    Ramified<Qp<7, 4>, 2>,
    parse_ramified_qp7_4_e2,
    PyRamifiedQp7_4E2,
    wrap_ramified_qp7_4_e2
);
divided_power_backend!(
    RamifiedQp11_4E2DividedPowerAlgebra,
    "RamifiedQp11_4_E2DividedPowerAlgebra",
    RamifiedQp11_4E2DpVector,
    "RamifiedQp11_4_E2DpVector",
    Ramified<Qp<11, 4>, 2>,
    parse_ramified_qp11_4_e2,
    PyRamifiedQp11_4E2,
    wrap_ramified_qp11_4_e2
);
divided_power_backend!(
    RamifiedQp13_4E2DividedPowerAlgebra,
    "RamifiedQp13_4_E2DividedPowerAlgebra",
    RamifiedQp13_4E2DpVector,
    "RamifiedQp13_4_E2DpVector",
    Ramified<Qp<13, 4>, 2>,
    parse_ramified_qp13_4_e2,
    PyRamifiedQp13_4E2,
    wrap_ramified_qp13_4_e2
);
divided_power_backend!(
    RamifiedQp2_4E3DividedPowerAlgebra,
    "RamifiedQp2_4_E3DividedPowerAlgebra",
    RamifiedQp2_4E3DpVector,
    "RamifiedQp2_4_E3DpVector",
    Ramified<Qp<2, 4>, 3>,
    parse_ramified_qp2_4_e3,
    PyRamifiedQp2_4E3,
    wrap_ramified_qp2_4_e3
);
divided_power_backend!(
    RamifiedQp3_4E3DividedPowerAlgebra,
    "RamifiedQp3_4_E3DividedPowerAlgebra",
    RamifiedQp3_4E3DpVector,
    "RamifiedQp3_4_E3DpVector",
    Ramified<Qp<3, 4>, 3>,
    parse_ramified_qp3_4_e3,
    PyRamifiedQp3_4E3,
    wrap_ramified_qp3_4_e3
);
divided_power_backend!(
    RamifiedQp5_4E3DividedPowerAlgebra,
    "RamifiedQp5_4_E3DividedPowerAlgebra",
    RamifiedQp5_4E3DpVector,
    "RamifiedQp5_4_E3DpVector",
    Ramified<Qp<5, 4>, 3>,
    parse_ramified_qp5_4_e3,
    PyRamifiedQp5_4E3,
    wrap_ramified_qp5_4_e3
);
divided_power_backend!(
    RamifiedQp7_4E3DividedPowerAlgebra,
    "RamifiedQp7_4_E3DividedPowerAlgebra",
    RamifiedQp7_4E3DpVector,
    "RamifiedQp7_4_E3DpVector",
    Ramified<Qp<7, 4>, 3>,
    parse_ramified_qp7_4_e3,
    PyRamifiedQp7_4E3,
    wrap_ramified_qp7_4_e3
);
divided_power_backend!(
    RamifiedQp11_4E3DividedPowerAlgebra,
    "RamifiedQp11_4_E3DividedPowerAlgebra",
    RamifiedQp11_4E3DpVector,
    "RamifiedQp11_4_E3DpVector",
    Ramified<Qp<11, 4>, 3>,
    parse_ramified_qp11_4_e3,
    PyRamifiedQp11_4E3,
    wrap_ramified_qp11_4_e3
);
divided_power_backend!(
    RamifiedQp13_4E3DividedPowerAlgebra,
    "RamifiedQp13_4_E3DividedPowerAlgebra",
    RamifiedQp13_4E3DpVector,
    "RamifiedQp13_4_E3DpVector",
    Ramified<Qp<13, 4>, 3>,
    parse_ramified_qp13_4_e3,
    PyRamifiedQp13_4E3,
    wrap_ramified_qp13_4_e3
);
divided_power_backend!(
    GaussQp2_4DividedPowerAlgebra,
    "GaussQp2_4DividedPowerAlgebra",
    GaussQp2_4DpVector,
    "GaussQp2_4DpVector",
    Gauss<Qp<2, 4>>,
    parse_gauss_qp2_4,
    PyGaussQp2_4,
    wrap_gauss_qp2_4
);
divided_power_backend!(
    GaussQp3_4DividedPowerAlgebra,
    "GaussQp3_4DividedPowerAlgebra",
    GaussQp3_4DpVector,
    "GaussQp3_4DpVector",
    Gauss<Qp<3, 4>>,
    parse_gauss_qp3_4,
    PyGaussQp3_4,
    wrap_gauss_qp3_4
);
divided_power_backend!(
    GaussQp5_4DividedPowerAlgebra,
    "GaussQp5_4DividedPowerAlgebra",
    GaussQp5_4DpVector,
    "GaussQp5_4DpVector",
    Gauss<Qp<5, 4>>,
    parse_gauss_qp5_4,
    PyGaussQp5_4,
    wrap_gauss_qp5_4
);
divided_power_backend!(
    GaussQp7_4DividedPowerAlgebra,
    "GaussQp7_4DividedPowerAlgebra",
    GaussQp7_4DpVector,
    "GaussQp7_4DpVector",
    Gauss<Qp<7, 4>>,
    parse_gauss_qp7_4,
    PyGaussQp7_4,
    wrap_gauss_qp7_4
);
divided_power_backend!(
    GaussQp11_4DividedPowerAlgebra,
    "GaussQp11_4DividedPowerAlgebra",
    GaussQp11_4DpVector,
    "GaussQp11_4DpVector",
    Gauss<Qp<11, 4>>,
    parse_gauss_qp11_4,
    PyGaussQp11_4,
    wrap_gauss_qp11_4
);
divided_power_backend!(
    GaussQp13_4DividedPowerAlgebra,
    "GaussQp13_4DividedPowerAlgebra",
    GaussQp13_4DpVector,
    "GaussQp13_4DpVector",
    Gauss<Qp<13, 4>>,
    parse_gauss_qp13_4,
    PyGaussQp13_4,
    wrap_gauss_qp13_4
);
divided_power_backend!(
    NimberPolyDividedPowerAlgebra,
    "NimberPolyDividedPowerAlgebra",
    NimberPolyDpVector,
    "NimberPolyDpVector",
    Poly<Nimber>,
    parse_nimber_poly,
    PyNimberPoly,
    wrap_nimber_poly
);
divided_power_backend!(
    NimberRationalFunctionDividedPowerAlgebra,
    "NimberRationalFunctionDividedPowerAlgebra",
    NimberRationalFunctionDpVector,
    "NimberRationalFunctionDpVector",
    RationalFunction<Nimber>,
    parse_nimber_rational_function,
    PyNimberRationalFunction,
    wrap_nimber_rational_function
);
divided_power_backend!(
    Fp2PolyDividedPowerAlgebra,
    "Fp2PolyDividedPowerAlgebra",
    Fp2PolyDpVector,
    "Fp2PolyDpVector",
    Poly<Fp<2>>,
    parse_fp2_poly,
    PyFp2Poly,
    wrap_fp2_poly
);
divided_power_backend!(
    Fp2RationalFunctionDividedPowerAlgebra,
    "Fp2RationalFunctionDividedPowerAlgebra",
    Fp2RationalFunctionDpVector,
    "Fp2RationalFunctionDpVector",
    RationalFunction<Fp<2>>,
    parse_fp2_rational_function,
    PyFp2RationalFunction,
    wrap_fp2_rational_function
);
divided_power_backend!(
    Fp3PolyDividedPowerAlgebra,
    "Fp3PolyDividedPowerAlgebra",
    Fp3PolyDpVector,
    "Fp3PolyDpVector",
    Poly<Fp<3>>,
    parse_fp3_poly,
    PyFp3Poly,
    wrap_fp3_poly
);
divided_power_backend!(
    Fp3RationalFunctionDividedPowerAlgebra,
    "Fp3RationalFunctionDividedPowerAlgebra",
    Fp3RationalFunctionDpVector,
    "Fp3RationalFunctionDpVector",
    RationalFunction<Fp<3>>,
    parse_fp3_rational_function,
    PyFp3RationalFunction,
    wrap_fp3_rational_function
);
divided_power_backend!(
    Fp5PolyDividedPowerAlgebra,
    "Fp5PolyDividedPowerAlgebra",
    Fp5PolyDpVector,
    "Fp5PolyDpVector",
    Poly<Fp<5>>,
    parse_fp5_poly,
    PyFp5Poly,
    wrap_fp5_poly
);
divided_power_backend!(
    Fp5RationalFunctionDividedPowerAlgebra,
    "Fp5RationalFunctionDividedPowerAlgebra",
    Fp5RationalFunctionDpVector,
    "Fp5RationalFunctionDpVector",
    RationalFunction<Fp<5>>,
    parse_fp5_rational_function,
    PyFp5RationalFunction,
    wrap_fp5_rational_function
);
divided_power_backend!(
    Fp7PolyDividedPowerAlgebra,
    "Fp7PolyDividedPowerAlgebra",
    Fp7PolyDpVector,
    "Fp7PolyDpVector",
    Poly<Fp<7>>,
    parse_fp7_poly,
    PyFp7Poly,
    wrap_fp7_poly
);
divided_power_backend!(
    Fp7RationalFunctionDividedPowerAlgebra,
    "Fp7RationalFunctionDividedPowerAlgebra",
    Fp7RationalFunctionDpVector,
    "Fp7RationalFunctionDpVector",
    RationalFunction<Fp<7>>,
    parse_fp7_rational_function,
    PyFp7RationalFunction,
    wrap_fp7_rational_function
);
divided_power_backend!(
    Fp11PolyDividedPowerAlgebra,
    "Fp11PolyDividedPowerAlgebra",
    Fp11PolyDpVector,
    "Fp11PolyDpVector",
    Poly<Fp<11>>,
    parse_fp11_poly,
    PyFp11Poly,
    wrap_fp11_poly
);
divided_power_backend!(
    Fp11RationalFunctionDividedPowerAlgebra,
    "Fp11RationalFunctionDividedPowerAlgebra",
    Fp11RationalFunctionDpVector,
    "Fp11RationalFunctionDpVector",
    RationalFunction<Fp<11>>,
    parse_fp11_rational_function,
    PyFp11RationalFunction,
    wrap_fp11_rational_function
);
divided_power_backend!(
    Fp13PolyDividedPowerAlgebra,
    "Fp13PolyDividedPowerAlgebra",
    Fp13PolyDpVector,
    "Fp13PolyDpVector",
    Poly<Fp<13>>,
    parse_fp13_poly,
    PyFp13Poly,
    wrap_fp13_poly
);
divided_power_backend!(
    Fp13RationalFunctionDividedPowerAlgebra,
    "Fp13RationalFunctionDividedPowerAlgebra",
    Fp13RationalFunctionDpVector,
    "Fp13RationalFunctionDpVector",
    RationalFunction<Fp<13>>,
    parse_fp13_rational_function,
    PyFp13RationalFunction,
    wrap_fp13_rational_function
);
divided_power_backend!(
    RationalDividedPowerAlgebra,
    "RationalDividedPowerAlgebra",
    RationalDpVector,
    "RationalDpVector",
    Rational,
    parse_rational,
    PyRational,
    wrap_rational
);
divided_power_backend!(
    AdeleDividedPowerAlgebra,
    "AdeleDividedPowerAlgebra",
    AdeleDpVector,
    "AdeleDpVector",
    Adele,
    parse_adele,
    PyAdele,
    wrap_adele
);
divided_power_backend!(
    SurrealDividedPowerAlgebra,
    "SurrealDividedPowerAlgebra",
    SurrealDpVector,
    "SurrealDpVector",
    Surreal,
    parse_surreal,
    PySurreal,
    wrap_surreal
);
divided_power_backend!(
    SurcomplexDividedPowerAlgebra,
    "SurcomplexDividedPowerAlgebra",
    SurcomplexDpVector,
    "SurcomplexDpVector",
    Surcomplex<Surreal>,
    parse_surcomplex,
    PySurcomplex,
    wrap_surcomplex
);
divided_power_backend!(
    IntegerDividedPowerAlgebra,
    "IntegerDividedPowerAlgebra",
    IntegerDpVector,
    "IntegerDpVector",
    Integer,
    parse_integer,
    PyInteger,
    wrap_integer
);
divided_power_backend!(
    OmnificDividedPowerAlgebra,
    "OmnificDividedPowerAlgebra",
    OmnificDpVector,
    "OmnificDpVector",
    Omnific,
    parse_omnific,
    PyOmnific,
    wrap_omnific
);
divided_power_backend!(
    OrdinalDividedPowerAlgebra,
    "OrdinalDividedPowerAlgebra",
    OrdinalDpVector,
    "OrdinalDpVector",
    Ordinal,
    parse_ordinal,
    PyOrdinal,
    wrap_ordinal
);

// ---------------------------------------------------------------------------
// Conformal geometric algebra over bound characteristic-zero worlds
// ---------------------------------------------------------------------------

macro_rules! cga_backend {
    ($py:ident, $name:literal, $scalar:ty, $mv:ident, $scalar_py:ty, $parse:path, $wrap:path) => {
        #[pyclass(name = $name, module = "pleroma")]
        struct $py {
            inner: Cga<$scalar>,
        }

        impl $py {
            fn wrap(&self, mv: Multivector<$scalar>) -> $mv {
                $mv {
                    alg: Arc::new(self.inner.alg.clone()),
                    mv,
                }
            }
        }

        #[pymethods]
        impl $py {
            #[new]
            fn new(n: usize) -> Self {
                $py { inner: Cga::new(n) }
            }
            #[getter]
            fn n(&self) -> usize {
                self.inner.n
            }
            #[getter]
            fn dim(&self) -> usize {
                self.inner.alg.dim
            }
            fn n_o(&self) -> $mv {
                self.wrap(self.inner.n_o())
            }
            fn n_inf(&self) -> $mv {
                self.wrap(self.inner.n_inf())
            }
            /// Lift a Euclidean point to the null cone: `up(p) = n_o + p + ½|p|² n_∞`.
            fn up(&self, p: Vec<Bound<'_, PyAny>>) -> PyResult<$mv> {
                let mut pv = Vec::with_capacity(p.len());
                for x in &p {
                    pv.push($parse(x)?);
                }
                Ok(self.wrap(self.inner.up(&pv)))
            }
            /// Recover a Euclidean point from a null vector (`None` if not normalizable).
            fn down(&self, x: &$mv) -> Option<Vec<$scalar_py>> {
                self.inner
                    .down(&x.mv)
                    .map(|v| v.into_iter().map($wrap).collect())
            }
            /// The conformal inner product `x · y` (= `−½|p−q|²` on lifted points).
            fn inner(&self, x: &$mv, y: &$mv) -> $scalar_py {
                $wrap(self.inner.inner(&x.mv, &y.mv))
            }
            /// The sphere of squared radius `r2` about center `c`.
            fn sphere(&self, c: Vec<Bound<'_, PyAny>>, r2: &Bound<'_, PyAny>) -> PyResult<$mv> {
                let mut cv = Vec::with_capacity(c.len());
                for x in &c {
                    cv.push($parse(x)?);
                }
                Ok(self.wrap(self.inner.sphere(&cv, &$parse(r2)?)))
            }
            /// The plane `{x : x·normal = d}`.
            fn plane(&self, normal: Vec<Bound<'_, PyAny>>, d: &Bound<'_, PyAny>) -> PyResult<$mv> {
                let mut nv = Vec::with_capacity(normal.len());
                for x in &normal {
                    nv.push($parse(x)?);
                }
                Ok(self.wrap(self.inner.plane(&nv, &$parse(d)?)))
            }
            /// The point pair / oriented join `a ∧ b`.
            fn point_pair(&self, a: &$mv, b: &$mv) -> $mv {
                self.wrap(self.inner.point_pair(&a.mv, &b.mv))
            }
            /// The IPNS meet (intersection) `x ∧ y`.
            fn meet(&self, x: &$mv, y: &$mv) -> $mv {
                self.wrap(self.inner.meet(&x.mv, &y.mv))
            }
        }
    };
}

cga_backend!(
    PySurrealCga,
    "SurrealCga",
    Surreal,
    SurrealMV,
    PySurreal,
    parse_surreal,
    wrap_surreal
);
cga_backend!(
    PyRationalCga,
    "RationalCga",
    Rational,
    RationalMV,
    PyRational,
    parse_rational,
    wrap_rational
);
cga_backend!(
    PyAdeleCga,
    "AdeleCga",
    Adele,
    AdeleMV,
    PyAdele,
    parse_adele,
    wrap_adele
);
cga_backend!(
    PySurcomplexCga,
    "SurcomplexCga",
    Surcomplex<Surreal>,
    SurcomplexMV,
    PySurcomplex,
    parse_surcomplex,
    wrap_surcomplex
);
cga_backend!(PyQp2_4Cga, "Qp2_4Cga", Qp<2, 4>, Qp2_4MV, PyQp2_4, parse_qp2_4, wrap_qp2_4);
cga_backend!(PyQp3_4Cga, "Qp3_4Cga", Qp<3, 4>, Qp3_4MV, PyQp3_4, parse_qp3_4, wrap_qp3_4);
cga_backend!(PyQp5_4Cga, "Qp5_4Cga", Qp<5, 4>, Qp5_4MV, PyQp5_4, parse_qp5_4, wrap_qp5_4);
cga_backend!(PyQp7_4Cga, "Qp7_4Cga", Qp<7, 4>, Qp7_4MV, PyQp7_4, parse_qp7_4, wrap_qp7_4);
cga_backend!(
    PyQp11_4Cga,
    "Qp11_4Cga",
    Qp<11, 4>,
    Qp11_4MV,
    PyQp11_4,
    parse_qp11_4,
    wrap_qp11_4
);
cga_backend!(
    PyQp13_4Cga,
    "Qp13_4Cga",
    Qp<13, 4>,
    Qp13_4MV,
    PyQp13_4,
    parse_qp13_4,
    wrap_qp13_4
);
cga_backend!(
    PyQq2_4_2Cga,
    "Qq2_4_2Cga",
    Qq<2, 4, 2>,
    Qq2_4_2MV,
    PyQq2_4_2,
    parse_qq2_4_2,
    wrap_qq2_4_2
);
cga_backend!(
    PyQq2_4_3Cga,
    "Qq2_4_3Cga",
    Qq<2, 4, 3>,
    Qq2_4_3MV,
    PyQq2_4_3,
    parse_qq2_4_3,
    wrap_qq2_4_3
);
cga_backend!(
    PyQq2_4_4Cga,
    "Qq2_4_4Cga",
    Qq<2, 4, 4>,
    Qq2_4_4MV,
    PyQq2_4_4,
    parse_qq2_4_4,
    wrap_qq2_4_4
);
cga_backend!(
    PyQq3_4_2Cga,
    "Qq3_4_2Cga",
    Qq<3, 4, 2>,
    Qq3_4_2MV,
    PyQq3_4_2,
    parse_qq3_4_2,
    wrap_qq3_4_2
);
cga_backend!(
    PyQq5_4_2Cga,
    "Qq5_4_2Cga",
    Qq<5, 4, 2>,
    Qq5_4_2MV,
    PyQq5_4_2,
    parse_qq5_4_2,
    wrap_qq5_4_2
);
cga_backend!(
    PyQq3_4_3Cga,
    "Qq3_4_3Cga",
    Qq<3, 4, 3>,
    Qq3_4_3MV,
    PyQq3_4_3,
    parse_qq3_4_3,
    wrap_qq3_4_3
);
cga_backend!(
    PyLaurentRational6Cga,
    "LaurentRational6Cga",
    Laurent<Rational, 6>,
    LaurentRational6MV,
    PyLaurentRational6,
    parse_laurent_rational_6,
    wrap_laurent_rational_6
);
cga_backend!(
    PyRamifiedQp2_4E2Cga,
    "RamifiedQp2_4_E2Cga",
    Ramified<Qp<2, 4>, 2>,
    RamifiedQp2_4E2MV,
    PyRamifiedQp2_4E2,
    parse_ramified_qp2_4_e2,
    wrap_ramified_qp2_4_e2
);
cga_backend!(
    PyRamifiedQp3_4E2Cga,
    "RamifiedQp3_4_E2Cga",
    Ramified<Qp<3, 4>, 2>,
    RamifiedQp3_4E2MV,
    PyRamifiedQp3_4E2,
    parse_ramified_qp3_4_e2,
    wrap_ramified_qp3_4_e2
);
cga_backend!(
    PyRamifiedQp5_4E2Cga,
    "RamifiedQp5_4_E2Cga",
    Ramified<Qp<5, 4>, 2>,
    RamifiedQp5_4E2MV,
    PyRamifiedQp5_4E2,
    parse_ramified_qp5_4_e2,
    wrap_ramified_qp5_4_e2
);
cga_backend!(
    PyRamifiedQp7_4E2Cga,
    "RamifiedQp7_4_E2Cga",
    Ramified<Qp<7, 4>, 2>,
    RamifiedQp7_4E2MV,
    PyRamifiedQp7_4E2,
    parse_ramified_qp7_4_e2,
    wrap_ramified_qp7_4_e2
);
cga_backend!(
    PyRamifiedQp11_4E2Cga,
    "RamifiedQp11_4_E2Cga",
    Ramified<Qp<11, 4>, 2>,
    RamifiedQp11_4E2MV,
    PyRamifiedQp11_4E2,
    parse_ramified_qp11_4_e2,
    wrap_ramified_qp11_4_e2
);
cga_backend!(
    PyRamifiedQp13_4E2Cga,
    "RamifiedQp13_4_E2Cga",
    Ramified<Qp<13, 4>, 2>,
    RamifiedQp13_4E2MV,
    PyRamifiedQp13_4E2,
    parse_ramified_qp13_4_e2,
    wrap_ramified_qp13_4_e2
);
cga_backend!(
    PyRamifiedQp2_4E3Cga,
    "RamifiedQp2_4_E3Cga",
    Ramified<Qp<2, 4>, 3>,
    RamifiedQp2_4E3MV,
    PyRamifiedQp2_4E3,
    parse_ramified_qp2_4_e3,
    wrap_ramified_qp2_4_e3
);
cga_backend!(
    PyRamifiedQp3_4E3Cga,
    "RamifiedQp3_4_E3Cga",
    Ramified<Qp<3, 4>, 3>,
    RamifiedQp3_4E3MV,
    PyRamifiedQp3_4E3,
    parse_ramified_qp3_4_e3,
    wrap_ramified_qp3_4_e3
);
cga_backend!(
    PyRamifiedQp5_4E3Cga,
    "RamifiedQp5_4_E3Cga",
    Ramified<Qp<5, 4>, 3>,
    RamifiedQp5_4E3MV,
    PyRamifiedQp5_4E3,
    parse_ramified_qp5_4_e3,
    wrap_ramified_qp5_4_e3
);
cga_backend!(
    PyRamifiedQp7_4E3Cga,
    "RamifiedQp7_4_E3Cga",
    Ramified<Qp<7, 4>, 3>,
    RamifiedQp7_4E3MV,
    PyRamifiedQp7_4E3,
    parse_ramified_qp7_4_e3,
    wrap_ramified_qp7_4_e3
);
cga_backend!(
    PyRamifiedQp11_4E3Cga,
    "RamifiedQp11_4_E3Cga",
    Ramified<Qp<11, 4>, 3>,
    RamifiedQp11_4E3MV,
    PyRamifiedQp11_4E3,
    parse_ramified_qp11_4_e3,
    wrap_ramified_qp11_4_e3
);
cga_backend!(
    PyRamifiedQp13_4E3Cga,
    "RamifiedQp13_4_E3Cga",
    Ramified<Qp<13, 4>, 3>,
    RamifiedQp13_4E3MV,
    PyRamifiedQp13_4E3,
    parse_ramified_qp13_4_e3,
    wrap_ramified_qp13_4_e3
);
cga_backend!(
    PyGaussQp2_4Cga,
    "GaussQp2_4Cga",
    Gauss<Qp<2, 4>>,
    GaussQp2_4MV,
    PyGaussQp2_4,
    parse_gauss_qp2_4,
    wrap_gauss_qp2_4
);
cga_backend!(
    PyGaussQp3_4Cga,
    "GaussQp3_4Cga",
    Gauss<Qp<3, 4>>,
    GaussQp3_4MV,
    PyGaussQp3_4,
    parse_gauss_qp3_4,
    wrap_gauss_qp3_4
);
cga_backend!(
    PyGaussQp5_4Cga,
    "GaussQp5_4Cga",
    Gauss<Qp<5, 4>>,
    GaussQp5_4MV,
    PyGaussQp5_4,
    parse_gauss_qp5_4,
    wrap_gauss_qp5_4
);
cga_backend!(
    PyGaussQp7_4Cga,
    "GaussQp7_4Cga",
    Gauss<Qp<7, 4>>,
    GaussQp7_4MV,
    PyGaussQp7_4,
    parse_gauss_qp7_4,
    wrap_gauss_qp7_4
);
cga_backend!(
    PyGaussQp11_4Cga,
    "GaussQp11_4Cga",
    Gauss<Qp<11, 4>>,
    GaussQp11_4MV,
    PyGaussQp11_4,
    parse_gauss_qp11_4,
    wrap_gauss_qp11_4
);
cga_backend!(
    PyGaussQp13_4Cga,
    "GaussQp13_4Cga",
    Gauss<Qp<13, 4>>,
    GaussQp13_4MV,
    PyGaussQp13_4,
    parse_gauss_qp13_4,
    wrap_gauss_qp13_4
);

pub(crate) fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PySpinorRep>()?;
    m.add_class::<PyLazySpinorRep>()?;
    m.add_class::<PyVersorClass>()?;
    m.add_class::<NimberAlgebra>()?;
    m.add_class::<NimberMV>()?;
    m.add_class::<NimberLinearMap>()?;
    m.add_class::<Fp2Algebra>()?;
    m.add_class::<Fp2MV>()?;
    m.add_class::<Fp2LinearMap>()?;
    m.add_class::<Fp3Algebra>()?;
    m.add_class::<Fp3MV>()?;
    m.add_class::<Fp3LinearMap>()?;
    m.add_class::<Fp5Algebra>()?;
    m.add_class::<Fp5MV>()?;
    m.add_class::<Fp5LinearMap>()?;
    m.add_class::<Fp7Algebra>()?;
    m.add_class::<Fp7MV>()?;
    m.add_class::<Fp7LinearMap>()?;
    m.add_class::<Fp11Algebra>()?;
    m.add_class::<Fp11MV>()?;
    m.add_class::<Fp11LinearMap>()?;
    m.add_class::<Fp13Algebra>()?;
    m.add_class::<Fp13MV>()?;
    m.add_class::<Fp13LinearMap>()?;
    m.add_class::<F4Algebra>()?;
    m.add_class::<F4MV>()?;
    m.add_class::<F4LinearMap>()?;
    m.add_class::<F8Algebra>()?;
    m.add_class::<F8MV>()?;
    m.add_class::<F8LinearMap>()?;
    m.add_class::<F16Algebra>()?;
    m.add_class::<F16MV>()?;
    m.add_class::<F16LinearMap>()?;
    m.add_class::<F9Algebra>()?;
    m.add_class::<F9MV>()?;
    m.add_class::<F9LinearMap>()?;
    m.add_class::<F25Algebra>()?;
    m.add_class::<F25MV>()?;
    m.add_class::<F25LinearMap>()?;
    m.add_class::<F27Algebra>()?;
    m.add_class::<F27MV>()?;
    m.add_class::<F27LinearMap>()?;
    m.add_class::<Zp2_4Algebra>()?;
    m.add_class::<Zp2_4MV>()?;
    m.add_class::<Zp2_4LinearMap>()?;
    m.add_class::<Zp3_4Algebra>()?;
    m.add_class::<Zp3_4MV>()?;
    m.add_class::<Zp3_4LinearMap>()?;
    m.add_class::<Zp5_4Algebra>()?;
    m.add_class::<Zp5_4MV>()?;
    m.add_class::<Zp5_4LinearMap>()?;
    m.add_class::<Zp7_4Algebra>()?;
    m.add_class::<Zp7_4MV>()?;
    m.add_class::<Zp7_4LinearMap>()?;
    m.add_class::<Zp11_4Algebra>()?;
    m.add_class::<Zp11_4MV>()?;
    m.add_class::<Zp11_4LinearMap>()?;
    m.add_class::<Zp13_4Algebra>()?;
    m.add_class::<Zp13_4MV>()?;
    m.add_class::<Zp13_4LinearMap>()?;
    m.add_class::<Qp2_4Algebra>()?;
    m.add_class::<Qp2_4MV>()?;
    m.add_class::<Qp2_4LinearMap>()?;
    m.add_class::<Qp3_4Algebra>()?;
    m.add_class::<Qp3_4MV>()?;
    m.add_class::<Qp3_4LinearMap>()?;
    m.add_class::<Qp5_4Algebra>()?;
    m.add_class::<Qp5_4MV>()?;
    m.add_class::<Qp5_4LinearMap>()?;
    m.add_class::<Qp7_4Algebra>()?;
    m.add_class::<Qp7_4MV>()?;
    m.add_class::<Qp7_4LinearMap>()?;
    m.add_class::<Qp11_4Algebra>()?;
    m.add_class::<Qp11_4MV>()?;
    m.add_class::<Qp11_4LinearMap>()?;
    m.add_class::<Qp13_4Algebra>()?;
    m.add_class::<Qp13_4MV>()?;
    m.add_class::<Qp13_4LinearMap>()?;
    m.add_class::<WittVec2_4_2Algebra>()?;
    m.add_class::<WittVec2_4_2MV>()?;
    m.add_class::<WittVec2_4_2LinearMap>()?;
    m.add_class::<WittVec2_4_3Algebra>()?;
    m.add_class::<WittVec2_4_3MV>()?;
    m.add_class::<WittVec2_4_3LinearMap>()?;
    m.add_class::<WittVec2_4_4Algebra>()?;
    m.add_class::<WittVec2_4_4MV>()?;
    m.add_class::<WittVec2_4_4LinearMap>()?;
    m.add_class::<WittVec3_4_2Algebra>()?;
    m.add_class::<WittVec3_4_2MV>()?;
    m.add_class::<WittVec3_4_2LinearMap>()?;
    m.add_class::<WittVec5_4_2Algebra>()?;
    m.add_class::<WittVec5_4_2MV>()?;
    m.add_class::<WittVec5_4_2LinearMap>()?;
    m.add_class::<WittVec3_4_3Algebra>()?;
    m.add_class::<WittVec3_4_3MV>()?;
    m.add_class::<WittVec3_4_3LinearMap>()?;
    m.add_class::<Qq2_4_2Algebra>()?;
    m.add_class::<Qq2_4_2MV>()?;
    m.add_class::<Qq2_4_2LinearMap>()?;
    m.add_class::<Qq2_4_3Algebra>()?;
    m.add_class::<Qq2_4_3MV>()?;
    m.add_class::<Qq2_4_3LinearMap>()?;
    m.add_class::<Qq2_4_4Algebra>()?;
    m.add_class::<Qq2_4_4MV>()?;
    m.add_class::<Qq2_4_4LinearMap>()?;
    m.add_class::<Qq3_4_2Algebra>()?;
    m.add_class::<Qq3_4_2MV>()?;
    m.add_class::<Qq3_4_2LinearMap>()?;
    m.add_class::<Qq5_4_2Algebra>()?;
    m.add_class::<Qq5_4_2MV>()?;
    m.add_class::<Qq5_4_2LinearMap>()?;
    m.add_class::<Qq3_4_3Algebra>()?;
    m.add_class::<Qq3_4_3MV>()?;
    m.add_class::<Qq3_4_3LinearMap>()?;
    m.add_class::<LaurentRational6Algebra>()?;
    m.add_class::<LaurentRational6MV>()?;
    m.add_class::<LaurentRational6LinearMap>()?;
    m.add_class::<LaurentFp3_6Algebra>()?;
    m.add_class::<LaurentFp3_6MV>()?;
    m.add_class::<LaurentFp3_6LinearMap>()?;
    m.add_class::<LaurentFp5_6Algebra>()?;
    m.add_class::<LaurentFp5_6MV>()?;
    m.add_class::<LaurentFp5_6LinearMap>()?;
    m.add_class::<LaurentFp7_6Algebra>()?;
    m.add_class::<LaurentFp7_6MV>()?;
    m.add_class::<LaurentFp7_6LinearMap>()?;
    m.add_class::<LaurentFp11_6Algebra>()?;
    m.add_class::<LaurentFp11_6MV>()?;
    m.add_class::<LaurentFp11_6LinearMap>()?;
    m.add_class::<LaurentFp13_6Algebra>()?;
    m.add_class::<LaurentFp13_6MV>()?;
    m.add_class::<LaurentFp13_6LinearMap>()?;
    m.add_class::<LaurentF9_6Algebra>()?;
    m.add_class::<LaurentF9_6MV>()?;
    m.add_class::<LaurentF9_6LinearMap>()?;
    m.add_class::<LaurentF25_6Algebra>()?;
    m.add_class::<LaurentF25_6MV>()?;
    m.add_class::<LaurentF25_6LinearMap>()?;
    m.add_class::<LaurentF27_6Algebra>()?;
    m.add_class::<LaurentF27_6MV>()?;
    m.add_class::<LaurentF27_6LinearMap>()?;
    m.add_class::<RamifiedQp2_4E2Algebra>()?;
    m.add_class::<RamifiedQp2_4E2MV>()?;
    m.add_class::<RamifiedQp2_4E2LinearMap>()?;
    m.add_class::<RamifiedQp3_4E2Algebra>()?;
    m.add_class::<RamifiedQp3_4E2MV>()?;
    m.add_class::<RamifiedQp3_4E2LinearMap>()?;
    m.add_class::<RamifiedQp5_4E2Algebra>()?;
    m.add_class::<RamifiedQp5_4E2MV>()?;
    m.add_class::<RamifiedQp5_4E2LinearMap>()?;
    m.add_class::<RamifiedQp7_4E2Algebra>()?;
    m.add_class::<RamifiedQp7_4E2MV>()?;
    m.add_class::<RamifiedQp7_4E2LinearMap>()?;
    m.add_class::<RamifiedQp11_4E2Algebra>()?;
    m.add_class::<RamifiedQp11_4E2MV>()?;
    m.add_class::<RamifiedQp11_4E2LinearMap>()?;
    m.add_class::<RamifiedQp13_4E2Algebra>()?;
    m.add_class::<RamifiedQp13_4E2MV>()?;
    m.add_class::<RamifiedQp13_4E2LinearMap>()?;
    m.add_class::<RamifiedQp2_4E3Algebra>()?;
    m.add_class::<RamifiedQp2_4E3MV>()?;
    m.add_class::<RamifiedQp2_4E3LinearMap>()?;
    m.add_class::<RamifiedQp3_4E3Algebra>()?;
    m.add_class::<RamifiedQp3_4E3MV>()?;
    m.add_class::<RamifiedQp3_4E3LinearMap>()?;
    m.add_class::<RamifiedQp5_4E3Algebra>()?;
    m.add_class::<RamifiedQp5_4E3MV>()?;
    m.add_class::<RamifiedQp5_4E3LinearMap>()?;
    m.add_class::<RamifiedQp7_4E3Algebra>()?;
    m.add_class::<RamifiedQp7_4E3MV>()?;
    m.add_class::<RamifiedQp7_4E3LinearMap>()?;
    m.add_class::<RamifiedQp11_4E3Algebra>()?;
    m.add_class::<RamifiedQp11_4E3MV>()?;
    m.add_class::<RamifiedQp11_4E3LinearMap>()?;
    m.add_class::<RamifiedQp13_4E3Algebra>()?;
    m.add_class::<RamifiedQp13_4E3MV>()?;
    m.add_class::<RamifiedQp13_4E3LinearMap>()?;
    m.add_class::<GaussQp2_4Algebra>()?;
    m.add_class::<GaussQp2_4MV>()?;
    m.add_class::<GaussQp2_4LinearMap>()?;
    m.add_class::<GaussQp3_4Algebra>()?;
    m.add_class::<GaussQp3_4MV>()?;
    m.add_class::<GaussQp3_4LinearMap>()?;
    m.add_class::<GaussQp5_4Algebra>()?;
    m.add_class::<GaussQp5_4MV>()?;
    m.add_class::<GaussQp5_4LinearMap>()?;
    m.add_class::<GaussQp7_4Algebra>()?;
    m.add_class::<GaussQp7_4MV>()?;
    m.add_class::<GaussQp7_4LinearMap>()?;
    m.add_class::<GaussQp11_4Algebra>()?;
    m.add_class::<GaussQp11_4MV>()?;
    m.add_class::<GaussQp11_4LinearMap>()?;
    m.add_class::<GaussQp13_4Algebra>()?;
    m.add_class::<GaussQp13_4MV>()?;
    m.add_class::<GaussQp13_4LinearMap>()?;
    m.add_class::<NimberPolyAlgebra>()?;
    m.add_class::<NimberPolyMV>()?;
    m.add_class::<NimberPolyLinearMap>()?;
    m.add_class::<NimberRationalFunctionAlgebra>()?;
    m.add_class::<NimberRationalFunctionMV>()?;
    m.add_class::<NimberRationalFunctionLinearMap>()?;
    m.add_class::<Fp2PolyAlgebra>()?;
    m.add_class::<Fp2PolyMV>()?;
    m.add_class::<Fp2PolyLinearMap>()?;
    m.add_class::<Fp2RationalFunctionAlgebra>()?;
    m.add_class::<Fp2RationalFunctionMV>()?;
    m.add_class::<Fp2RationalFunctionLinearMap>()?;
    m.add_class::<Fp3PolyAlgebra>()?;
    m.add_class::<Fp3PolyMV>()?;
    m.add_class::<Fp3PolyLinearMap>()?;
    m.add_class::<Fp3RationalFunctionAlgebra>()?;
    m.add_class::<Fp3RationalFunctionMV>()?;
    m.add_class::<Fp3RationalFunctionLinearMap>()?;
    m.add_class::<Fp5PolyAlgebra>()?;
    m.add_class::<Fp5PolyMV>()?;
    m.add_class::<Fp5PolyLinearMap>()?;
    m.add_class::<Fp5RationalFunctionAlgebra>()?;
    m.add_class::<Fp5RationalFunctionMV>()?;
    m.add_class::<Fp5RationalFunctionLinearMap>()?;
    m.add_class::<Fp7PolyAlgebra>()?;
    m.add_class::<Fp7PolyMV>()?;
    m.add_class::<Fp7PolyLinearMap>()?;
    m.add_class::<Fp7RationalFunctionAlgebra>()?;
    m.add_class::<Fp7RationalFunctionMV>()?;
    m.add_class::<Fp7RationalFunctionLinearMap>()?;
    m.add_class::<Fp11PolyAlgebra>()?;
    m.add_class::<Fp11PolyMV>()?;
    m.add_class::<Fp11PolyLinearMap>()?;
    m.add_class::<Fp11RationalFunctionAlgebra>()?;
    m.add_class::<Fp11RationalFunctionMV>()?;
    m.add_class::<Fp11RationalFunctionLinearMap>()?;
    m.add_class::<Fp13PolyAlgebra>()?;
    m.add_class::<Fp13PolyMV>()?;
    m.add_class::<Fp13PolyLinearMap>()?;
    m.add_class::<Fp13RationalFunctionAlgebra>()?;
    m.add_class::<Fp13RationalFunctionMV>()?;
    m.add_class::<Fp13RationalFunctionLinearMap>()?;
    m.add_class::<RationalAlgebra>()?;
    m.add_class::<RationalMV>()?;
    m.add_class::<RationalLinearMap>()?;
    m.add_class::<AdeleAlgebra>()?;
    m.add_class::<AdeleMV>()?;
    m.add_class::<AdeleLinearMap>()?;
    m.add_class::<SurrealAlgebra>()?;
    m.add_class::<SurrealMV>()?;
    m.add_class::<SurrealLinearMap>()?;
    m.add_class::<SurcomplexAlgebra>()?;
    m.add_class::<SurcomplexMV>()?;
    m.add_class::<SurcomplexLinearMap>()?;
    m.add_class::<IntegerAlgebra>()?;
    m.add_class::<IntegerMV>()?;
    m.add_class::<IntegerLinearMap>()?;
    m.add_class::<OmnificAlgebra>()?;
    m.add_class::<OmnificMV>()?;
    m.add_class::<OmnificLinearMap>()?;
    m.add_class::<OrdinalAlgebra>()?;
    m.add_class::<OrdinalMV>()?;
    m.add_class::<OrdinalLinearMap>()?;
    m.add_class::<NimberDividedPowerAlgebra>()?;
    m.add_class::<NimberDpVector>()?;
    m.add_class::<Fp2DividedPowerAlgebra>()?;
    m.add_class::<Fp2DpVector>()?;
    m.add_class::<Fp3DividedPowerAlgebra>()?;
    m.add_class::<Fp3DpVector>()?;
    m.add_class::<Fp5DividedPowerAlgebra>()?;
    m.add_class::<Fp5DpVector>()?;
    m.add_class::<Fp7DividedPowerAlgebra>()?;
    m.add_class::<Fp7DpVector>()?;
    m.add_class::<Fp11DividedPowerAlgebra>()?;
    m.add_class::<Fp11DpVector>()?;
    m.add_class::<Fp13DividedPowerAlgebra>()?;
    m.add_class::<Fp13DpVector>()?;
    m.add_class::<F4DividedPowerAlgebra>()?;
    m.add_class::<F4DpVector>()?;
    m.add_class::<F8DividedPowerAlgebra>()?;
    m.add_class::<F8DpVector>()?;
    m.add_class::<F16DividedPowerAlgebra>()?;
    m.add_class::<F16DpVector>()?;
    m.add_class::<F9DividedPowerAlgebra>()?;
    m.add_class::<F9DpVector>()?;
    m.add_class::<F25DividedPowerAlgebra>()?;
    m.add_class::<F25DpVector>()?;
    m.add_class::<F27DividedPowerAlgebra>()?;
    m.add_class::<F27DpVector>()?;
    m.add_class::<Zp2_4DividedPowerAlgebra>()?;
    m.add_class::<Zp2_4DpVector>()?;
    m.add_class::<Zp3_4DividedPowerAlgebra>()?;
    m.add_class::<Zp3_4DpVector>()?;
    m.add_class::<Zp5_4DividedPowerAlgebra>()?;
    m.add_class::<Zp5_4DpVector>()?;
    m.add_class::<Zp7_4DividedPowerAlgebra>()?;
    m.add_class::<Zp7_4DpVector>()?;
    m.add_class::<Zp11_4DividedPowerAlgebra>()?;
    m.add_class::<Zp11_4DpVector>()?;
    m.add_class::<Zp13_4DividedPowerAlgebra>()?;
    m.add_class::<Zp13_4DpVector>()?;
    m.add_class::<Qp2_4DividedPowerAlgebra>()?;
    m.add_class::<Qp2_4DpVector>()?;
    m.add_class::<Qp3_4DividedPowerAlgebra>()?;
    m.add_class::<Qp3_4DpVector>()?;
    m.add_class::<Qp5_4DividedPowerAlgebra>()?;
    m.add_class::<Qp5_4DpVector>()?;
    m.add_class::<Qp7_4DividedPowerAlgebra>()?;
    m.add_class::<Qp7_4DpVector>()?;
    m.add_class::<Qp11_4DividedPowerAlgebra>()?;
    m.add_class::<Qp11_4DpVector>()?;
    m.add_class::<Qp13_4DividedPowerAlgebra>()?;
    m.add_class::<Qp13_4DpVector>()?;
    m.add_class::<WittVec2_4_2DividedPowerAlgebra>()?;
    m.add_class::<WittVec2_4_2DpVector>()?;
    m.add_class::<WittVec2_4_3DividedPowerAlgebra>()?;
    m.add_class::<WittVec2_4_3DpVector>()?;
    m.add_class::<WittVec2_4_4DividedPowerAlgebra>()?;
    m.add_class::<WittVec2_4_4DpVector>()?;
    m.add_class::<WittVec3_4_2DividedPowerAlgebra>()?;
    m.add_class::<WittVec3_4_2DpVector>()?;
    m.add_class::<WittVec5_4_2DividedPowerAlgebra>()?;
    m.add_class::<WittVec5_4_2DpVector>()?;
    m.add_class::<WittVec3_4_3DividedPowerAlgebra>()?;
    m.add_class::<WittVec3_4_3DpVector>()?;
    m.add_class::<Qq2_4_2DividedPowerAlgebra>()?;
    m.add_class::<Qq2_4_2DpVector>()?;
    m.add_class::<Qq2_4_3DividedPowerAlgebra>()?;
    m.add_class::<Qq2_4_3DpVector>()?;
    m.add_class::<Qq2_4_4DividedPowerAlgebra>()?;
    m.add_class::<Qq2_4_4DpVector>()?;
    m.add_class::<Qq3_4_2DividedPowerAlgebra>()?;
    m.add_class::<Qq3_4_2DpVector>()?;
    m.add_class::<Qq5_4_2DividedPowerAlgebra>()?;
    m.add_class::<Qq5_4_2DpVector>()?;
    m.add_class::<Qq3_4_3DividedPowerAlgebra>()?;
    m.add_class::<Qq3_4_3DpVector>()?;
    m.add_class::<LaurentRational6DividedPowerAlgebra>()?;
    m.add_class::<LaurentRational6DpVector>()?;
    m.add_class::<LaurentFp3_6DividedPowerAlgebra>()?;
    m.add_class::<LaurentFp3_6DpVector>()?;
    m.add_class::<LaurentFp5_6DividedPowerAlgebra>()?;
    m.add_class::<LaurentFp5_6DpVector>()?;
    m.add_class::<LaurentFp7_6DividedPowerAlgebra>()?;
    m.add_class::<LaurentFp7_6DpVector>()?;
    m.add_class::<LaurentFp11_6DividedPowerAlgebra>()?;
    m.add_class::<LaurentFp11_6DpVector>()?;
    m.add_class::<LaurentFp13_6DividedPowerAlgebra>()?;
    m.add_class::<LaurentFp13_6DpVector>()?;
    m.add_class::<LaurentF9_6DividedPowerAlgebra>()?;
    m.add_class::<LaurentF9_6DpVector>()?;
    m.add_class::<LaurentF25_6DividedPowerAlgebra>()?;
    m.add_class::<LaurentF25_6DpVector>()?;
    m.add_class::<LaurentF27_6DividedPowerAlgebra>()?;
    m.add_class::<LaurentF27_6DpVector>()?;
    m.add_class::<RamifiedQp2_4E2DividedPowerAlgebra>()?;
    m.add_class::<RamifiedQp2_4E2DpVector>()?;
    m.add_class::<RamifiedQp3_4E2DividedPowerAlgebra>()?;
    m.add_class::<RamifiedQp3_4E2DpVector>()?;
    m.add_class::<RamifiedQp5_4E2DividedPowerAlgebra>()?;
    m.add_class::<RamifiedQp5_4E2DpVector>()?;
    m.add_class::<RamifiedQp7_4E2DividedPowerAlgebra>()?;
    m.add_class::<RamifiedQp7_4E2DpVector>()?;
    m.add_class::<RamifiedQp11_4E2DividedPowerAlgebra>()?;
    m.add_class::<RamifiedQp11_4E2DpVector>()?;
    m.add_class::<RamifiedQp13_4E2DividedPowerAlgebra>()?;
    m.add_class::<RamifiedQp13_4E2DpVector>()?;
    m.add_class::<RamifiedQp2_4E3DividedPowerAlgebra>()?;
    m.add_class::<RamifiedQp2_4E3DpVector>()?;
    m.add_class::<RamifiedQp3_4E3DividedPowerAlgebra>()?;
    m.add_class::<RamifiedQp3_4E3DpVector>()?;
    m.add_class::<RamifiedQp5_4E3DividedPowerAlgebra>()?;
    m.add_class::<RamifiedQp5_4E3DpVector>()?;
    m.add_class::<RamifiedQp7_4E3DividedPowerAlgebra>()?;
    m.add_class::<RamifiedQp7_4E3DpVector>()?;
    m.add_class::<RamifiedQp11_4E3DividedPowerAlgebra>()?;
    m.add_class::<RamifiedQp11_4E3DpVector>()?;
    m.add_class::<RamifiedQp13_4E3DividedPowerAlgebra>()?;
    m.add_class::<RamifiedQp13_4E3DpVector>()?;
    m.add_class::<GaussQp2_4DividedPowerAlgebra>()?;
    m.add_class::<GaussQp2_4DpVector>()?;
    m.add_class::<GaussQp3_4DividedPowerAlgebra>()?;
    m.add_class::<GaussQp3_4DpVector>()?;
    m.add_class::<GaussQp5_4DividedPowerAlgebra>()?;
    m.add_class::<GaussQp5_4DpVector>()?;
    m.add_class::<GaussQp7_4DividedPowerAlgebra>()?;
    m.add_class::<GaussQp7_4DpVector>()?;
    m.add_class::<GaussQp11_4DividedPowerAlgebra>()?;
    m.add_class::<GaussQp11_4DpVector>()?;
    m.add_class::<GaussQp13_4DividedPowerAlgebra>()?;
    m.add_class::<GaussQp13_4DpVector>()?;
    m.add_class::<NimberPolyDividedPowerAlgebra>()?;
    m.add_class::<NimberPolyDpVector>()?;
    m.add_class::<NimberRationalFunctionDividedPowerAlgebra>()?;
    m.add_class::<NimberRationalFunctionDpVector>()?;
    m.add_class::<Fp2PolyDividedPowerAlgebra>()?;
    m.add_class::<Fp2PolyDpVector>()?;
    m.add_class::<Fp2RationalFunctionDividedPowerAlgebra>()?;
    m.add_class::<Fp2RationalFunctionDpVector>()?;
    m.add_class::<Fp3PolyDividedPowerAlgebra>()?;
    m.add_class::<Fp3PolyDpVector>()?;
    m.add_class::<Fp3RationalFunctionDividedPowerAlgebra>()?;
    m.add_class::<Fp3RationalFunctionDpVector>()?;
    m.add_class::<Fp5PolyDividedPowerAlgebra>()?;
    m.add_class::<Fp5PolyDpVector>()?;
    m.add_class::<Fp5RationalFunctionDividedPowerAlgebra>()?;
    m.add_class::<Fp5RationalFunctionDpVector>()?;
    m.add_class::<Fp7PolyDividedPowerAlgebra>()?;
    m.add_class::<Fp7PolyDpVector>()?;
    m.add_class::<Fp7RationalFunctionDividedPowerAlgebra>()?;
    m.add_class::<Fp7RationalFunctionDpVector>()?;
    m.add_class::<Fp11PolyDividedPowerAlgebra>()?;
    m.add_class::<Fp11PolyDpVector>()?;
    m.add_class::<Fp11RationalFunctionDividedPowerAlgebra>()?;
    m.add_class::<Fp11RationalFunctionDpVector>()?;
    m.add_class::<Fp13PolyDividedPowerAlgebra>()?;
    m.add_class::<Fp13PolyDpVector>()?;
    m.add_class::<Fp13RationalFunctionDividedPowerAlgebra>()?;
    m.add_class::<Fp13RationalFunctionDpVector>()?;
    m.add_class::<RationalDividedPowerAlgebra>()?;
    m.add_class::<RationalDpVector>()?;
    m.add_class::<AdeleDividedPowerAlgebra>()?;
    m.add_class::<AdeleDpVector>()?;
    m.add_class::<SurrealDividedPowerAlgebra>()?;
    m.add_class::<SurrealDpVector>()?;
    m.add_class::<SurcomplexDividedPowerAlgebra>()?;
    m.add_class::<SurcomplexDpVector>()?;
    m.add_class::<IntegerDividedPowerAlgebra>()?;
    m.add_class::<IntegerDpVector>()?;
    m.add_class::<OmnificDividedPowerAlgebra>()?;
    m.add_class::<OmnificDpVector>()?;
    m.add_class::<OrdinalDividedPowerAlgebra>()?;
    m.add_class::<OrdinalDpVector>()?;
    m.add_class::<PySurrealCga>()?;
    m.add_class::<PyRationalCga>()?;
    m.add_class::<PyAdeleCga>()?;
    m.add_class::<PySurcomplexCga>()?;
    m.add_class::<PyQp2_4Cga>()?;
    m.add_class::<PyQp3_4Cga>()?;
    m.add_class::<PyQp5_4Cga>()?;
    m.add_class::<PyQp7_4Cga>()?;
    m.add_class::<PyQp11_4Cga>()?;
    m.add_class::<PyQp13_4Cga>()?;
    m.add_class::<PyQq2_4_2Cga>()?;
    m.add_class::<PyQq2_4_3Cga>()?;
    m.add_class::<PyQq2_4_4Cga>()?;
    m.add_class::<PyQq3_4_2Cga>()?;
    m.add_class::<PyQq5_4_2Cga>()?;
    m.add_class::<PyQq3_4_3Cga>()?;
    m.add_class::<PyLaurentRational6Cga>()?;
    m.add_class::<PyRamifiedQp2_4E2Cga>()?;
    m.add_class::<PyRamifiedQp3_4E2Cga>()?;
    m.add_class::<PyRamifiedQp5_4E2Cga>()?;
    m.add_class::<PyRamifiedQp7_4E2Cga>()?;
    m.add_class::<PyRamifiedQp11_4E2Cga>()?;
    m.add_class::<PyRamifiedQp13_4E2Cga>()?;
    m.add_class::<PyRamifiedQp2_4E3Cga>()?;
    m.add_class::<PyRamifiedQp3_4E3Cga>()?;
    m.add_class::<PyRamifiedQp5_4E3Cga>()?;
    m.add_class::<PyRamifiedQp7_4E3Cga>()?;
    m.add_class::<PyRamifiedQp11_4E3Cga>()?;
    m.add_class::<PyRamifiedQp13_4E3Cga>()?;
    m.add_class::<PyGaussQp2_4Cga>()?;
    m.add_class::<PyGaussQp3_4Cga>()?;
    m.add_class::<PyGaussQp5_4Cga>()?;
    m.add_class::<PyGaussQp7_4Cga>()?;
    m.add_class::<PyGaussQp11_4Cga>()?;
    m.add_class::<PyGaussQp13_4Cga>()?;
    m.add_function(wrap_pyfunction!(galois_linear_map, m)?)?;
    m.add_function(wrap_pyfunction!(frobenius_linear_map, m)?)?;
    m.add_function(wrap_pyfunction!(nimber_subfield_frobenius_linear_map, m)?)?;
    m.add_function(wrap_pyfunction!(bits, m)?)?;
    m.add_function(wrap_pyfunction!(grade, m)?)?;
    Ok(())
}
