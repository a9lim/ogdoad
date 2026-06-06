//! PyO3 bindings — per-backend classes.
//!
//! Each scalar world (nimber / surreal / surcomplex) gets its own scalar type,
//! `<World>Algebra`, and `<World>MV` multivector. The Algebra/MV pair is
//! stamped out by the `backend!` macro, monomorphising the same verified
//! generic engine to the concrete scalar type — so there is no runtime
//! dispatch and no way to mix scalar worlds in one algebra.

use crate::cga::Cga;
use crate::clifford::{CliffordAlgebra, Metric, Multivector};
use crate::fp::Fp;
use crate::nimber::Nimber;
use crate::omnific::Omnific;
use crate::onag::Ordinal;
use crate::partizan::Game;
use crate::scalar::{Integer, Rational, Scalar};
use crate::surcomplex::Surcomplex;
use crate::surreal::Surreal;
use crate::witt::{WittClass, WittClassG};
use pyo3::basic::CompareOp;
use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyDict;
use pyo3::IntoPyObjectExt;
use std::collections::BTreeMap;
use std::sync::Arc;

// ---------------------------------------------------------------------------
// Scalar pyclasses + parsers
// ---------------------------------------------------------------------------

#[pyclass(name = "Nimber", module = "pleroma", from_py_object)]
#[derive(Clone)]
struct PyNimber {
    inner: Nimber,
}

#[pymethods]
impl PyNimber {
    #[new]
    fn new(value: u64) -> Self {
        PyNimber {
            inner: Nimber(value),
        }
    }
    #[getter]
    fn value(&self) -> u64 {
        self.inner.0
    }
    fn __add__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyNimber> {
        Ok(PyNimber {
            inner: self.inner.add(&parse_nimber(other)?),
        })
    }
    fn __radd__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyNimber> {
        self.__add__(other)
    }
    fn __mul__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        // defer to the other operand (e.g. a multivector's __rmul__) if it isn't a scalar
        match parse_nimber(other) {
            Ok(o) => PyNimber {
                inner: self.inner.mul(&o),
            }
            .into_py_any(py),
            Err(_) => Ok(py.NotImplemented()),
        }
    }
    fn __rmul__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyNimber> {
        Ok(PyNimber {
            inner: self.inner.mul(&parse_nimber(other)?),
        })
    }
    fn inv(&self) -> PyResult<PyNimber> {
        self.inner
            .inv()
            .map(|n| PyNimber { inner: n })
            .ok_or_else(|| PyValueError::new_err("*0 has no inverse"))
    }
    fn __truediv__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyNimber> {
        let o = parse_nimber(other)?;
        let oi = o
            .inv()
            .ok_or_else(|| PyValueError::new_err("division by *0"))?;
        Ok(PyNimber {
            inner: self.inner.mul(&oi),
        })
    }
    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        matches!(parse_nimber(other), Ok(n) if n == self.inner)
    }
    fn __hash__(&self) -> u64 {
        self.inner.0
    }
    fn __repr__(&self) -> String {
        format!("{:?}", self.inner)
    }
}

fn parse_nimber(obj: &Bound<'_, PyAny>) -> PyResult<Nimber> {
    if let Ok(n) = obj.cast::<PyNimber>() {
        return Ok(n.borrow().inner);
    }
    if let Ok(v) = obj.extract::<u64>() {
        return Ok(Nimber(v));
    }
    Err(PyTypeError::new_err("expected Nimber or non-negative int"))
}

#[pyclass(name = "Surreal", module = "pleroma", from_py_object)]
#[derive(Clone)]
struct PySurreal {
    inner: Surreal,
}

#[pymethods]
impl PySurreal {
    fn __add__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurreal> {
        Ok(PySurreal {
            inner: self.inner.add(&parse_surreal(other)?),
        })
    }
    fn __radd__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurreal> {
        self.__add__(other)
    }
    fn __sub__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurreal> {
        Ok(PySurreal {
            inner: self.inner.sub(&parse_surreal(other)?),
        })
    }
    fn __rsub__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurreal> {
        Ok(PySurreal {
            inner: parse_surreal(other)?.sub(&self.inner),
        })
    }
    fn __mul__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        match parse_surreal(other) {
            Ok(o) => PySurreal {
                inner: self.inner.mul(&o),
            }
            .into_py_any(py),
            Err(_) => Ok(py.NotImplemented()),
        }
    }
    fn __rmul__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurreal> {
        Ok(PySurreal {
            inner: self.inner.mul(&parse_surreal(other)?),
        })
    }
    fn __neg__(&self) -> PySurreal {
        PySurreal {
            inner: self.inner.neg(),
        }
    }
    fn inv(&self) -> PyResult<PySurreal> {
        self.inner
            .inv()
            .map(|s| PySurreal { inner: s })
            .ok_or_else(|| {
                PyValueError::new_err(
                    "only monomials (coeff·ω^e) have a finite-support surreal inverse",
                )
            })
    }
    fn __truediv__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurreal> {
        let o = parse_surreal(other)?;
        let oi = o
            .inv()
            .ok_or_else(|| PyValueError::new_err("divisor has no finite-support inverse"))?;
        Ok(PySurreal {
            inner: self.inner.mul(&oi),
        })
    }
    fn __pow__(&self, n: u32, _modulo: Option<&Bound<'_, PyAny>>) -> PySurreal {
        let mut acc = Surreal::one();
        for _ in 0..n {
            acc = acc.mul(&self.inner);
        }
        PySurreal { inner: acc }
    }
    fn __richcmp__(&self, other: &Bound<'_, PyAny>, op: CompareOp) -> PyResult<bool> {
        Ok(op.matches(self.inner.cmp(&parse_surreal(other)?)))
    }
    fn __repr__(&self) -> String {
        format!("{:?}", self.inner)
    }
}

fn parse_surreal(obj: &Bound<'_, PyAny>) -> PyResult<Surreal> {
    if let Ok(s) = obj.cast::<PySurreal>() {
        return Ok(s.borrow().inner.clone());
    }
    if let Ok(v) = obj.extract::<i128>() {
        return Ok(Surreal::from_int(v));
    }
    Err(PyTypeError::new_err("expected Surreal or int"))
}

#[pyclass(name = "Surcomplex", module = "pleroma", from_py_object)]
#[derive(Clone)]
struct PySurcomplex {
    inner: Surcomplex<Surreal>,
}

#[pymethods]
impl PySurcomplex {
    #[new]
    #[pyo3(signature = (re, im=None))]
    fn new(re: &Bound<'_, PyAny>, im: Option<&Bound<'_, PyAny>>) -> PyResult<Self> {
        let r = parse_surreal(re)?;
        let i = match im {
            Some(x) => parse_surreal(x)?,
            None => Surreal::zero(),
        };
        Ok(PySurcomplex {
            inner: Surcomplex::new(r, i),
        })
    }
    #[staticmethod]
    fn i() -> PySurcomplex {
        PySurcomplex {
            inner: Surcomplex::i(),
        }
    }
    #[getter]
    fn re(&self) -> PySurreal {
        PySurreal {
            inner: self.inner.re.clone(),
        }
    }
    #[getter]
    fn im(&self) -> PySurreal {
        PySurreal {
            inner: self.inner.im.clone(),
        }
    }
    fn conj(&self) -> PySurcomplex {
        PySurcomplex {
            inner: self.inner.conj(),
        }
    }
    fn __add__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurcomplex> {
        Ok(PySurcomplex {
            inner: self.inner.add(&parse_surcomplex(other)?),
        })
    }
    fn __radd__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurcomplex> {
        self.__add__(other)
    }
    fn __sub__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurcomplex> {
        Ok(PySurcomplex {
            inner: self.inner.sub(&parse_surcomplex(other)?),
        })
    }
    fn __mul__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        match parse_surcomplex(other) {
            Ok(o) => PySurcomplex {
                inner: self.inner.mul(&o),
            }
            .into_py_any(py),
            Err(_) => Ok(py.NotImplemented()),
        }
    }
    fn __rmul__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurcomplex> {
        Ok(PySurcomplex {
            inner: self.inner.mul(&parse_surcomplex(other)?),
        })
    }
    fn __neg__(&self) -> PySurcomplex {
        PySurcomplex {
            inner: self.inner.neg(),
        }
    }
    fn inv(&self) -> PyResult<PySurcomplex> {
        self.inner
            .inv()
            .map(|s| PySurcomplex { inner: s })
            .ok_or_else(|| {
                PyValueError::new_err("inverse needs an invertible norm a²+b² (a monomial surreal)")
            })
    }
    fn __truediv__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurcomplex> {
        let o = parse_surcomplex(other)?;
        let oi = o
            .inv()
            .ok_or_else(|| PyValueError::new_err("divisor has no representable inverse"))?;
        Ok(PySurcomplex {
            inner: self.inner.mul(&oi),
        })
    }
    fn __pow__(&self, n: u32, _modulo: Option<&Bound<'_, PyAny>>) -> PySurcomplex {
        let mut acc = Surcomplex::<Surreal>::one();
        for _ in 0..n {
            acc = acc.mul(&self.inner);
        }
        PySurcomplex { inner: acc }
    }
    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        matches!(parse_surcomplex(other), Ok(x) if x == self.inner)
    }
    fn __repr__(&self) -> String {
        if self.inner.im.is_zero() {
            format!("{:?}", self.inner.re)
        } else {
            format!("{:?} + ({:?})i", self.inner.re, self.inner.im)
        }
    }
}

fn parse_surcomplex(obj: &Bound<'_, PyAny>) -> PyResult<Surcomplex<Surreal>> {
    if let Ok(s) = obj.cast::<PySurcomplex>() {
        return Ok(s.borrow().inner.clone());
    }
    if let Ok(s) = obj.cast::<PySurreal>() {
        return Ok(Surcomplex::new(s.borrow().inner.clone(), Surreal::zero()));
    }
    if let Ok(v) = obj.extract::<i128>() {
        return Ok(Surcomplex::new(Surreal::from_int(v), Surreal::zero()));
    }
    Err(PyTypeError::new_err("expected Surcomplex, Surreal, or int"))
}

#[pyclass(name = "Integer", module = "pleroma", from_py_object)]
#[derive(Clone)]
struct PyInteger {
    inner: Integer,
}

#[pymethods]
impl PyInteger {
    #[new]
    fn new(value: i64) -> Self {
        PyInteger {
            inner: Integer(value),
        }
    }
    #[getter]
    fn value(&self) -> i64 {
        self.inner.0
    }
    fn __add__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyInteger> {
        Ok(PyInteger {
            inner: self.inner.add(&parse_integer(other)?),
        })
    }
    fn __radd__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyInteger> {
        self.__add__(other)
    }
    fn __sub__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyInteger> {
        Ok(PyInteger {
            inner: self.inner.sub(&parse_integer(other)?),
        })
    }
    fn __neg__(&self) -> PyInteger {
        PyInteger {
            inner: self.inner.neg(),
        }
    }
    fn __mul__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        match parse_integer(other) {
            Ok(o) => PyInteger {
                inner: self.inner.mul(&o),
            }
            .into_py_any(py),
            Err(_) => Ok(py.NotImplemented()),
        }
    }
    fn __rmul__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyInteger> {
        Ok(PyInteger {
            inner: self.inner.mul(&parse_integer(other)?),
        })
    }
    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        matches!(parse_integer(other), Ok(n) if n == self.inner)
    }
    fn __repr__(&self) -> String {
        format!("{:?}", self.inner)
    }
}

fn parse_integer(obj: &Bound<'_, PyAny>) -> PyResult<Integer> {
    if let Ok(n) = obj.cast::<PyInteger>() {
        return Ok(n.borrow().inner);
    }
    if let Ok(v) = obj.extract::<i64>() {
        return Ok(Integer(v));
    }
    Err(PyTypeError::new_err("expected Integer or int"))
}

fn wrap_integer(i: Integer) -> PyInteger {
    PyInteger { inner: i }
}

fn wrap_nimber(n: Nimber) -> PyNimber {
    PyNimber { inner: n }
}
fn wrap_surreal(s: Surreal) -> PySurreal {
    PySurreal { inner: s }
}
fn wrap_surcomplex(s: Surcomplex<Surreal>) -> PySurcomplex {
    PySurcomplex { inner: s }
}

// --- Omnific integers Oz: the surreal integers, a transfinite ring ----------

#[pyclass(name = "Omnific", module = "pleroma", from_py_object)]
#[derive(Clone)]
struct PyOmnific {
    inner: Omnific,
}

#[pymethods]
impl PyOmnific {
    #[new]
    fn new(value: i128) -> Self {
        PyOmnific {
            inner: Omnific::from_int(value),
        }
    }
    /// The underlying surreal value.
    fn surreal(&self) -> PySurreal {
        PySurreal {
            inner: self.inner.inner().clone(),
        }
    }
    fn __add__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyOmnific> {
        Ok(PyOmnific {
            inner: self.inner.add(&parse_omnific(other)?),
        })
    }
    fn __radd__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyOmnific> {
        self.__add__(other)
    }
    fn __sub__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyOmnific> {
        Ok(PyOmnific {
            inner: self.inner.sub(&parse_omnific(other)?),
        })
    }
    fn __neg__(&self) -> PyOmnific {
        PyOmnific {
            inner: self.inner.neg(),
        }
    }
    fn __mul__(&self, py: Python<'_>, other: &Bound<'_, PyAny>) -> PyResult<Py<PyAny>> {
        match parse_omnific(other) {
            Ok(o) => PyOmnific {
                inner: self.inner.mul(&o),
            }
            .into_py_any(py),
            Err(_) => Ok(py.NotImplemented()),
        }
    }
    fn __rmul__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyOmnific> {
        Ok(PyOmnific {
            inner: self.inner.mul(&parse_omnific(other)?),
        })
    }
    fn inv(&self) -> PyResult<PyOmnific> {
        self.inner
            .inv()
            .map(|o| PyOmnific { inner: o })
            .ok_or_else(|| PyValueError::new_err("Oz is a ring: only ±1 are invertible"))
    }
    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        matches!(parse_omnific(other), Ok(o) if o == self.inner)
    }
    fn __repr__(&self) -> String {
        format!("{:?}", self.inner.inner())
    }
}

fn parse_omnific(obj: &Bound<'_, PyAny>) -> PyResult<Omnific> {
    if let Ok(o) = obj.cast::<PyOmnific>() {
        return Ok(o.borrow().inner.clone());
    }
    if let Ok(s) = obj.cast::<PySurreal>() {
        return Omnific::from_surreal(s.borrow().inner.clone())
            .ok_or_else(|| PyValueError::new_err("surreal is not an omnific integer"));
    }
    if let Ok(v) = obj.extract::<i128>() {
        return Ok(Omnific::from_int(v));
    }
    Err(PyTypeError::new_err(
        "expected Omnific, omnific Surreal, or int",
    ))
}

fn wrap_omnific(o: Omnific) -> PyOmnific {
    PyOmnific { inner: o }
}

/// The omnific integer `n`.
#[pyfunction]
fn omnific(n: i128) -> PyOmnific {
    PyOmnific {
        inner: Omnific::from_int(n),
    }
}

/// `ω` as an omnific integer.
#[pyfunction]
fn omnific_omega() -> PyOmnific {
    PyOmnific {
        inner: Omnific::omega(),
    }
}

// ---------------------------------------------------------------------------
// Algebra + multivector, one pair per backend
// ---------------------------------------------------------------------------

macro_rules! backend {
    ($alg:ident, $alg_name:literal, $mv:ident, $mv_name:literal, $scalar:ty, $parse:path, $scalar_py:ty, $wrap:path) => {
        #[pyclass(name = $alg_name, module = "pleroma", from_py_object)]
        #[derive(Clone)]
        struct $alg {
            inner: Arc<CliffordAlgebra<$scalar>>,
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
                let mut bm: BTreeMap<(usize, usize), $scalar> = BTreeMap::new();
                if let Some(d) = b {
                    for (k, v) in d.iter() {
                        let (i, j): (usize, usize) = k.extract()?;
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
                        am.insert((i, j), $parse(&v)?);
                    }
                }
                let dim = qv.len();
                let metric = Metric::general(qv, bm, am);
                Ok($alg {
                    inner: Arc::new(CliffordAlgebra::new(dim, metric)),
                })
            }

            #[getter]
            fn dim(&self) -> usize {
                self.inner.dim
            }

            /// The graded (super) tensor product self ⊗̂ other ≅ Cl(self ⟂ other).
            fn graded_tensor(&self, other: &$alg) -> $alg {
                $alg {
                    inner: Arc::new(self.inner.graded_tensor(&other.inner)),
                }
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
            fn gen(&self, i: usize) -> $mv {
                $mv {
                    alg: self.inner.clone(),
                    mv: self.inner.gen(i),
                }
            }
            fn blade(&self, gens: Vec<usize>) -> $mv {
                $mv {
                    alg: self.inner.clone(),
                    mv: self.inner.blade(&gens),
                }
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

            /// The determinant of a linear map given column-major (`matrix[i]` =
            /// the image of `e_i`): the scalar by which its outermorphism scales
            /// the pseudoscalar. Char-faithful (the char-2 determinant over nimbers).
            fn determinant(&self, matrix: Vec<Vec<Bound<'_, PyAny>>>) -> PyResult<$scalar_py> {
                let n = matrix.len();
                let mut cols: Vec<Vec<$scalar>> = Vec::with_capacity(n);
                for col in &matrix {
                    if col.len() != n {
                        return Err(PyValueError::new_err(
                            "matrix must be square (n columns of length n)",
                        ));
                    }
                    let mut c = Vec::with_capacity(n);
                    for x in col {
                        c.push($parse(x)?);
                    }
                    cols.push(c);
                }
                let lm = crate::outermorphism::LinearMap::from_columns(cols);
                Ok($wrap(crate::outermorphism::determinant(&self.inner, &lm)))
            }

            /// Apply the outermorphism of a (column-major) linear map to a
            /// multivector: `f(a∧b) = f(a)∧f(b)`.
            fn outermorphism(&self, matrix: Vec<Vec<Bound<'_, PyAny>>>, mv: &$mv) -> PyResult<$mv> {
                let n = matrix.len();
                let mut cols: Vec<Vec<$scalar>> = Vec::with_capacity(n);
                for col in &matrix {
                    if col.len() != n {
                        return Err(PyValueError::new_err(
                            "matrix must be square (n columns of length n)",
                        ));
                    }
                    let mut c = Vec::with_capacity(n);
                    for x in col {
                        c.push($parse(x)?);
                    }
                    cols.push(c);
                }
                let lm = crate::outermorphism::LinearMap::from_columns(cols);
                Ok($mv {
                    alg: self.inner.clone(),
                    mv: crate::outermorphism::apply_outermorphism(&self.inner, &lm, &mv.mv),
                })
            }

            /// A concrete spinor representation: `(idempotent, basis, gen_matrices)`
            /// realizing the classification on column spinors. Nondegenerate
            /// orthogonal char-0 metrics only.
            #[allow(clippy::type_complexity)]
            fn spinor_rep(&self) -> PyResult<($mv, Vec<$mv>, Vec<Vec<Vec<$scalar_py>>>)> {
                let rep = crate::spinor::spinor_rep(&self.inner).ok_or_else(|| {
                    PyValueError::new_err(
                        "spinor_rep needs a nondegenerate orthogonal characteristic-0 metric",
                    )
                })?;
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
                Ok((idempotent, basis, gen_matrices))
            }

            fn __repr__(&self) -> String {
                format!("{}(dim={})", $alg_name, self.inner.dim)
            }
        }

        #[pyclass(name = $mv_name, module = "pleroma", from_py_object)]
        #[derive(Clone)]
        struct $mv {
            alg: Arc<CliffordAlgebra<$scalar>>,
            mv: Multivector<$scalar>,
        }

        #[pymethods]
        impl $mv {
            fn __add__(&self, other: &$mv) -> $mv {
                $mv {
                    alg: self.alg.clone(),
                    mv: self.alg.add(&self.mv, &other.mv),
                }
            }
            fn __sub__(&self, other: &$mv) -> $mv {
                let neg_one = <$scalar as Scalar>::one().neg();
                let neg = self.alg.scalar_mul(&neg_one, &other.mv);
                $mv {
                    alg: self.alg.clone(),
                    mv: self.alg.add(&self.mv, &neg),
                }
            }
            fn __neg__(&self) -> $mv {
                let neg_one = <$scalar as Scalar>::one().neg();
                $mv {
                    alg: self.alg.clone(),
                    mv: self.alg.scalar_mul(&neg_one, &self.mv),
                }
            }
            fn __mul__(&self, other: &Bound<'_, PyAny>) -> PyResult<$mv> {
                if let Ok(o) = other.cast::<$mv>() {
                    return Ok($mv {
                        alg: self.alg.clone(),
                        mv: self.alg.mul(&self.mv, &o.borrow().mv),
                    });
                }
                let s = $parse(other)?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: self.alg.scalar_mul(&s, &self.mv),
                })
            }
            fn __rmul__(&self, other: &Bound<'_, PyAny>) -> PyResult<$mv> {
                let s = $parse(other)?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: self.alg.scalar_mul(&s, &self.mv),
                })
            }
            fn __pow__(&self, n: u32, _modulo: Option<&Bound<'_, PyAny>>) -> $mv {
                let mut acc = self.alg.scalar(<$scalar as Scalar>::one());
                for _ in 0..n {
                    acc = self.alg.mul(&acc, &self.mv);
                }
                $mv {
                    alg: self.alg.clone(),
                    mv: acc,
                }
            }
            /// Exterior (wedge) product; also bound to the `^` operator.
            fn wedge(&self, other: &$mv) -> $mv {
                $mv {
                    alg: self.alg.clone(),
                    mv: self.alg.wedge(&self.mv, &other.mv),
                }
            }
            fn __xor__(&self, other: &$mv) -> $mv {
                self.wedge(other)
            }
            fn reverse(&self) -> $mv {
                $mv {
                    alg: self.alg.clone(),
                    mv: self.alg.reverse(&self.mv),
                }
            }
            /// `~v` is reversion.
            fn __invert__(&self) -> $mv {
                self.reverse()
            }
            fn grade(&self, k: u32) -> $mv {
                $mv {
                    alg: self.alg.clone(),
                    mv: self.alg.grade_part(&self.mv, k),
                }
            }
            fn grade_involution(&self) -> $mv {
                $mv {
                    alg: self.alg.clone(),
                    mv: self.alg.grade_involution(&self.mv),
                }
            }
            /// Versor inverse v⁻¹ = ṽ/(v ṽ); errors if v isn't an invertible versor.
            fn inverse(&self) -> PyResult<$mv> {
                self.alg
                    .versor_inverse(&self.mv)
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| PyValueError::new_err("not an invertible versor"))
            }
            /// Sandwich self · x · self⁻¹ (rotor/versor action; untwisted).
            fn sandwich(&self, x: &$mv) -> PyResult<$mv> {
                self.alg
                    .sandwich(&self.mv, &x.mv)
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| PyValueError::new_err("not an invertible versor"))
            }
            /// Twisted adjoint (Pin/Spin action) α(self) · x · self⁻¹ — the correct
            /// versor action; for an odd versor it gives a genuine reflection.
            fn twisted_sandwich(&self, x: &$mv) -> PyResult<$mv> {
                self.alg
                    .twisted_sandwich(&self.mv, &x.mv)
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| PyValueError::new_err("not an invertible versor"))
            }
            /// Projection onto the even subalgebra (sum of even-grade blades).
            fn even_part(&self) -> $mv {
                $mv {
                    alg: self.alg.clone(),
                    mv: self.alg.even_part(&self.mv),
                }
            }
            /// The exterior-Hopf coproduct Δ, returned as a multivector over the
            /// graded tensor square `Cl ⊗̂ Cl` (a tensor `e_T ⊗ e_U` is the blade
            /// `T | (U << dim)`).
            fn coproduct(&self) -> $mv {
                let tensor = self.alg.graded_tensor(&self.alg);
                let co = crate::hopf::coproduct(&self.alg, &self.mv);
                $mv {
                    alg: Arc::new(tensor),
                    mv: co,
                }
            }
            /// The exterior-Hopf antipode (the grade involution `(−1)^k`).
            fn antipode(&self) -> $mv {
                $mv {
                    alg: self.alg.clone(),
                    mv: crate::hopf::antipode(&self.alg, &self.mv),
                }
            }
            /// The exterior-Hopf counit (the scalar part).
            fn counit(&self) -> $scalar_py {
                $wrap(crate::hopf::counit(&self.alg, &self.mv))
            }
            /// `exp(self)` for a nilpotent multivector — the terminating series
            /// `Σ selfᵏ/k!`. Errors if `self` is not nilpotent (a rotational motor,
            /// needing transcendental cos/sin).
            fn exp_nilpotent(&self) -> PyResult<$mv> {
                crate::cga::exp_nilpotent(&self.alg, &self.mv)
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
                self.alg
                    .reflect(&self.mv, &x.mv)
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| PyValueError::new_err("not an invertible vector"))
            }
            fn left_contract(&self, other: &$mv) -> $mv {
                $mv {
                    alg: self.alg.clone(),
                    mv: self.alg.left_contract(&self.mv, &other.mv),
                }
            }
            fn right_contract(&self, other: &$mv) -> $mv {
                $mv {
                    alg: self.alg.clone(),
                    mv: self.alg.right_contract(&self.mv, &other.mv),
                }
            }
            /// `<<` is left contraction, `>>` is right contraction.
            fn __lshift__(&self, other: &$mv) -> $mv {
                self.left_contract(other)
            }
            fn __rshift__(&self, other: &$mv) -> $mv {
                self.right_contract(other)
            }
            fn dual(&self) -> PyResult<$mv> {
                self.alg
                    .dual(&self.mv)
                    .map(|mv| $mv {
                        alg: self.alg.clone(),
                        mv,
                    })
                    .ok_or_else(|| {
                        PyValueError::new_err("pseudoscalar not invertible (degenerate metric)")
                    })
            }
            fn norm2(&self) -> $scalar_py {
                $wrap(self.alg.norm2(&self.mv))
            }
            fn scalar_part(&self) -> $scalar_py {
                $wrap(self.alg.scalar_part(&self.mv))
            }
            /// Division: by a scalar, or by a versor (multiply by its inverse).
            fn __truediv__(&self, other: &Bound<'_, PyAny>) -> PyResult<$mv> {
                if let Ok(o) = other.cast::<$mv>() {
                    let oinv = self
                        .alg
                        .versor_inverse(&o.borrow().mv)
                        .ok_or_else(|| PyValueError::new_err("divisor not an invertible versor"))?;
                    return Ok($mv {
                        alg: self.alg.clone(),
                        mv: self.alg.mul(&self.mv, &oinv),
                    });
                }
                let s = $parse(other)?;
                let sinv = <$scalar as Scalar>::inv(&s)
                    .ok_or_else(|| PyValueError::new_err("scalar has no representable inverse"))?;
                Ok($mv {
                    alg: self.alg.clone(),
                    mv: self.alg.scalar_mul(&sinv, &self.mv),
                })
            }
            fn is_zero(&self) -> bool {
                self.mv.is_zero()
            }
            fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
                if let Ok(o) = other.cast::<$mv>() {
                    self.mv == o.borrow().mv
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
    Nimber,
    parse_nimber,
    PyNimber,
    wrap_nimber
);
backend!(
    SurrealAlgebra,
    "SurrealAlgebra",
    SurrealMV,
    "SurrealMV",
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
    Omnific,
    parse_omnific,
    PyOmnific,
    wrap_omnific
);

// ---------------------------------------------------------------------------
// Surreal builders
// ---------------------------------------------------------------------------

#[pyfunction]
fn omega() -> PySurreal {
    PySurreal {
        inner: Surreal::omega(),
    }
}

#[pyfunction]
fn epsilon() -> PySurreal {
    PySurreal {
        inner: Surreal::epsilon(),
    }
}

#[pyfunction]
fn omega_pow(exp: &Bound<'_, PyAny>) -> PyResult<PySurreal> {
    Ok(PySurreal {
        inner: Surreal::omega_pow(parse_surreal(exp)?),
    })
}

#[pyfunction]
fn rational(num: i128, den: i128) -> PyResult<PySurreal> {
    if den == 0 {
        return Err(PyValueError::new_err("zero denominator"));
    }
    Ok(PySurreal {
        inner: Surreal::from_rational(Rational::new(num, den)),
    })
}

#[pyfunction]
fn surreal(n: i128) -> PySurreal {
    PySurreal {
        inner: Surreal::from_int(n),
    }
}

#[pyclass(name = "ArfResult", module = "pleroma")]
struct PyArfResult {
    inner: crate::arf::ArfResult,
}

#[pymethods]
impl PyArfResult {
    #[getter]
    fn arf(&self) -> u8 {
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
    fn o_type(&self) -> &'static str {
        self.inner.o_type
    }
    fn __repr__(&self) -> String {
        format!(
            "ArfResult(arf={}, type={}, rank={}, radical_dim={}, radical_anisotropic={})",
            self.inner.arf,
            self.inner.o_type,
            self.inner.rank,
            self.inner.radical_dim,
            self.inner.radical_anisotropic,
        )
    }
}

/// Arf invariant (the char-2 Clifford classifier) of a nimber algebra whose
/// metric has F₂ entries.
#[pyfunction]
fn arf_invariant(alg: &NimberAlgebra) -> PyArfResult {
    PyArfResult {
        inner: crate::arf::arf_invariant(&alg.inner.metric),
    }
}

/// Nim-multiplication via Conway's Turning-Corners game recurrence (the
/// game-theoretic definition; equals the algebraic nim-product).
#[pyfunction]
fn nim_mul_mex(x: u64, y: u64) -> u64 {
    crate::games::nim_mul_mex(x, y)
}

// ---------------------------------------------------------------------------
// Char-0 classifier
// ---------------------------------------------------------------------------

#[pyclass(name = "CliffordType", module = "pleroma")]
struct PyCliffordType {
    inner: crate::classify::CliffordType,
}

#[pymethods]
impl PyCliffordType {
    #[getter]
    fn base(&self) -> String {
        format!("{:?}", self.inner.base)
    }
    #[getter]
    fn matrix_dim(&self) -> usize {
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
    fn signature(&self) -> (usize, usize) {
        self.inner.signature
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

/// Classify a surreal Clifford algebra (the genuine real classification) as a
/// matrix algebra over ℝ/ℂ/ℍ. Diagonal metrics only.
#[pyfunction]
fn classify_surreal(alg: &SurrealAlgebra) -> PyResult<PyCliffordType> {
    crate::classify::classify_surreal(&alg.inner.metric)
        .map(|t| PyCliffordType { inner: t })
        .ok_or_else(|| PyValueError::new_err("classifier needs a diagonal (orthogonal) metric"))
}

/// Classify a surcomplex Clifford algebra (the 2-fold complex classification).
/// Diagonal metrics only.
#[pyfunction]
fn classify_surcomplex(alg: &SurcomplexAlgebra) -> PyResult<PyCliffordType> {
    crate::classify::classify_surcomplex(&alg.inner.metric)
        .map(|t| PyCliffordType { inner: t })
        .ok_or_else(|| PyValueError::new_err("classifier needs a diagonal (orthogonal) metric"))
}

// ---------------------------------------------------------------------------
// Witt group + Dickson invariant
// ---------------------------------------------------------------------------

#[pyclass(name = "WittClass", module = "pleroma", from_py_object)]
#[derive(Clone)]
struct PyWittClass {
    inner: WittClass,
}

#[pymethods]
impl PyWittClass {
    #[getter]
    fn arf(&self) -> u8 {
        self.inner.arf
    }
    fn add(&self, other: &PyWittClass) -> PyWittClass {
        PyWittClass {
            inner: self.inner.add(&other.inner),
        }
    }
    fn __add__(&self, other: &PyWittClass) -> PyWittClass {
        self.add(other)
    }
    fn is_hyperbolic(&self) -> bool {
        self.inner.is_hyperbolic()
    }
    fn anisotropic_dim(&self) -> usize {
        self.inner.anisotropic_dim()
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
fn witt_class(alg: &NimberAlgebra) -> PyWittClass {
    PyWittClass {
        inner: WittClass::from_metric(&alg.inner.metric),
    }
}

/// The Dickson invariant of an orthogonal matrix over the nim-field (the char-2
/// determinant replacement; `0` ⇒ rotation/SO, `1` ⇒ reflection).
#[pyfunction]
fn dickson_matrix(g: Vec<Vec<u64>>) -> u8 {
    crate::arf::dickson_matrix(&g)
}

/// The Dickson invariant of a nimber Clifford versor (= its grade parity).
#[pyfunction]
fn dickson_of_versor(v: &NimberMV) -> PyResult<u8> {
    crate::arf::dickson_of_versor(&v.mv)
        .ok_or_else(|| PyValueError::new_err("not a versor (mixed grade parity)"))
}

// ---------------------------------------------------------------------------
// Nim field operations (the Artin–Schreier ↔ Arf bridge)
// ---------------------------------------------------------------------------

/// Nim square root (inverse Frobenius); always defined in char 2.
#[pyfunction]
fn nim_sqrt(x: u64) -> u64 {
    crate::nimber::nim_sqrt(x)
}

/// Field trace F_{2^m} → F₂ — the map the Arf invariant is read through and the
/// obstruction to solving `y²+y=c`.
#[pyfunction]
fn nim_trace(x: u64, m: u32) -> u64 {
    crate::nimber::nim_trace(x, m)
}

/// Solve the Artin–Schreier equation `y²+y=c` in F_{2^m} (`None` iff Tr(c)≠0).
#[pyfunction]
fn nim_solve_artin_schreier(c: u64, m: u32) -> Option<u64> {
    crate::nimber::nim_solve_artin_schreier(c, m)
}

/// Whether `y²+y=c` is solvable in F_{2^m} — i.e. `Tr(c)=0`.
#[pyfunction]
fn nim_is_artin_schreier_solvable(c: u64, m: u32) -> bool {
    crate::nimber::nim_is_artin_schreier_solvable(c, m)
}

// ---------------------------------------------------------------------------
// Partizan games + the exterior algebra of the game group
// ---------------------------------------------------------------------------

#[pyclass(name = "Game", module = "pleroma", from_py_object)]
#[derive(Clone)]
struct PyGame {
    inner: Game,
}

#[pymethods]
impl PyGame {
    #[staticmethod]
    fn zero() -> PyGame {
        PyGame {
            inner: Game::zero(),
        }
    }
    #[staticmethod]
    fn star() -> PyGame {
        PyGame {
            inner: Game::star(),
        }
    }
    #[staticmethod]
    fn up() -> PyGame {
        PyGame { inner: Game::up() }
    }
    #[staticmethod]
    fn integer(n: i64) -> PyGame {
        PyGame {
            inner: Game::integer(n),
        }
    }
    #[staticmethod]
    fn switch(a: i64, b: i64) -> PyGame {
        PyGame {
            inner: Game::switch(a, b),
        }
    }
    fn __add__(&self, other: &PyGame) -> PyGame {
        PyGame {
            inner: self.inner.add(&other.inner),
        }
    }
    fn __neg__(&self) -> PyGame {
        PyGame {
            inner: self.inner.neg(),
        }
    }
    fn __sub__(&self, other: &PyGame) -> PyGame {
        PyGame {
            inner: self.inner.add(&other.inner.neg()),
        }
    }
    fn le(&self, other: &PyGame) -> bool {
        self.inner.le(&other.inner)
    }
    fn __eq__(&self, other: &PyGame) -> bool {
        self.inner.eq(&other.inner)
    }
    fn fuzzy(&self, other: &PyGame) -> bool {
        self.inner.fuzzy(&other.inner)
    }
    fn birthday(&self) -> u32 {
        self.inner.birthday()
    }
    fn is_number(&self) -> bool {
        self.inner.is_number()
    }
    fn times_int(&self, n: i64) -> PyGame {
        PyGame {
            inner: self.inner.times_int(n),
        }
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(name = "GameExterior", module = "pleroma")]
struct PyGameExterior {
    alg: Arc<CliffordAlgebra<Integer>>,
    gens: Vec<Game>,
}

#[pymethods]
impl PyGameExterior {
    #[new]
    fn new(gens: Vec<PyGame>) -> Self {
        let games: Vec<Game> = gens.iter().map(|g| g.inner.clone()).collect();
        let n = games.len();
        PyGameExterior {
            alg: Arc::new(CliffordAlgebra::new(n, Metric::grassmann(n))),
            gens: games,
        }
    }
    #[getter]
    fn dim(&self) -> usize {
        self.gens.len()
    }
    /// The grade-1 generator e_i (an `IntegerMV`) standing for game g_i.
    fn generator(&self, i: usize) -> IntegerMV {
        IntegerMV {
            alg: self.alg.clone(),
            mv: self.alg.gen(i),
        }
    }
    /// The game g_i a generator stands for.
    fn game(&self, i: usize) -> PyGame {
        PyGame {
            inner: self.gens[i].clone(),
        }
    }
    /// Map a grade-1 element Σ c_i e_i back to the game Σ c_i·g_i (the module map
    /// Λ¹ → game group). Errors if the multivector is not purely grade 1.
    fn value_of_grade1(&self, mv: &IntegerMV) -> PyResult<PyGame> {
        let mut acc = Game::zero();
        for (&blade, coeff) in &mv.mv.terms {
            if blade.count_ones() != 1 {
                return Err(PyValueError::new_err("expected a grade-1 element"));
            }
            let idx = blade.trailing_zeros() as usize;
            acc = acc.add(&self.gens[idx].times_int(coeff.0));
        }
        Ok(PyGame { inner: acc })
    }
}

// ---------------------------------------------------------------------------
// Transfinite (ordinal) nimbers
// ---------------------------------------------------------------------------

#[pyclass(name = "Ordinal", module = "pleroma", from_py_object)]
#[derive(Clone)]
struct PyOrdinal {
    inner: Ordinal,
}

#[pymethods]
impl PyOrdinal {
    #[new]
    fn new(n: u64) -> Self {
        PyOrdinal {
            inner: Ordinal::from_u64(n),
        }
    }
    /// `ω`, the first infinite ordinal nimber.
    #[staticmethod]
    fn omega() -> PyOrdinal {
        PyOrdinal {
            inner: Ordinal::omega(),
        }
    }
    /// `ω^exp` (coefficient 1).
    #[staticmethod]
    fn omega_pow(exp: &PyOrdinal) -> PyOrdinal {
        PyOrdinal {
            inner: Ordinal::omega_pow(exp.inner.clone()),
        }
    }
    /// `ω^exp · coeff`.
    #[staticmethod]
    fn monomial(exp: &PyOrdinal, coeff: u64) -> PyOrdinal {
        PyOrdinal {
            inner: Ordinal::monomial(exp.inner.clone(), coeff),
        }
    }
    /// Nim-addition (complete and exact): XOR of like-`ω`-power coefficients.
    fn nim_add(&self, other: &PyOrdinal) -> PyOrdinal {
        PyOrdinal {
            inner: self.inner.nim_add(&other.inner),
        }
    }
    /// Nim-multiplication (partial): exact for finite × finite; `None` when either
    /// operand is infinite (the general ordinal product is staged).
    fn nim_mul(&self, other: &PyOrdinal) -> Option<PyOrdinal> {
        self.inner
            .nim_mul(&other.inner)
            .map(|o| PyOrdinal { inner: o })
    }
    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }
    /// The finite nimber value, if this ordinal is finite.
    fn as_finite(&self) -> Option<u64> {
        self.inner.as_finite()
    }
    fn __richcmp__(&self, other: &PyOrdinal, op: CompareOp) -> bool {
        op.matches(self.inner.cmp(&other.inner))
    }
    fn __repr__(&self) -> String {
        format!("{:?}", self.inner)
    }
}

// ---------------------------------------------------------------------------
// Odd-characteristic classifier (the trichotomy's third leg)
// ---------------------------------------------------------------------------

fn fp_diag<const P: u64>(q: &[i64]) -> Metric<Fp<P>> {
    Metric::diagonal(q.iter().map(|&x| Fp::<P>::new(x)).collect())
}

#[pyclass(name = "OddCharType", module = "pleroma")]
struct PyOddCharType {
    inner: crate::disc::OddCharType,
}

#[pymethods]
impl PyOddCharType {
    #[getter]
    fn p(&self) -> u64 {
        self.inner.p
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
    fn hasse(&self) -> i8 {
        self.inner.hasse
    }
    fn __repr__(&self) -> String {
        self.inner.display()
    }
}

#[pyclass(name = "WittClassG", module = "pleroma", from_py_object)]
#[derive(Clone)]
struct PyWittClassG {
    inner: WittClassG,
}

#[pymethods]
impl PyWittClassG {
    fn add(&self, other: &PyWittClassG) -> PyWittClassG {
        PyWittClassG {
            inner: self.inner.add(&other.inner),
        }
    }
    fn __add__(&self, other: &PyWittClassG) -> PyWittClassG {
        self.add(other)
    }
    fn __eq__(&self, other: &PyWittClassG) -> bool {
        self.inner == other.inner
    }
    fn __repr__(&self) -> String {
        match self.inner {
            WittClassG::Char0 { signature } => format!("WittClassG::Char0(signature={signature})"),
            WittClassG::OddChar { kappa, e0, sclass } => {
                format!("WittClassG::OddChar(kappa={kappa}, e0={e0}, sclass={sclass})")
            }
            WittClassG::Char2 { arf } => format!("WittClassG::Char2(arf={arf})"),
        }
    }
}

/// Classify a diagonal odd-characteristic form `q` over `F_p` (dimension +
/// discriminant + Hasse). Supported primes: 3, 5, 7, 11, 13.
#[pyfunction]
fn classify_oddchar(p: u64, q: Vec<i64>) -> PyResult<PyOddCharType> {
    let res = match p {
        3 => crate::disc::classify_oddchar(&fp_diag::<3>(&q)),
        5 => crate::disc::classify_oddchar(&fp_diag::<5>(&q)),
        7 => crate::disc::classify_oddchar(&fp_diag::<7>(&q)),
        11 => crate::disc::classify_oddchar(&fp_diag::<11>(&q)),
        13 => crate::disc::classify_oddchar(&fp_diag::<13>(&q)),
        _ => return Err(PyValueError::new_err("supported primes: 3, 5, 7, 11, 13")),
    };
    res.map(|t| PyOddCharType { inner: t })
        .ok_or_else(|| PyValueError::new_err("non-diagonal metric"))
}

/// The odd-characteristic Witt class of a diagonal form `q` over `F_p`.
#[pyfunction]
fn oddchar_witt(p: u64, q: Vec<i64>) -> PyResult<PyWittClassG> {
    let res = match p {
        3 => crate::disc::oddchar_witt(&fp_diag::<3>(&q)),
        5 => crate::disc::oddchar_witt(&fp_diag::<5>(&q)),
        7 => crate::disc::oddchar_witt(&fp_diag::<7>(&q)),
        11 => crate::disc::oddchar_witt(&fp_diag::<11>(&q)),
        13 => crate::disc::oddchar_witt(&fp_diag::<13>(&q)),
        _ => return Err(PyValueError::new_err("supported primes: 3, 5, 7, 11, 13")),
    };
    res.map(|w| PyWittClassG { inner: w })
        .ok_or_else(|| PyValueError::new_err("non-diagonal metric"))
}

/// Is `x` a square mod `p`? (Euler's criterion.) Supported primes: 3, 5, 7, 11, 13.
#[pyfunction]
fn is_square_mod(p: u64, x: i64) -> PyResult<bool> {
    Ok(match p {
        3 => crate::disc::is_square(Fp::<3>::new(x)),
        5 => crate::disc::is_square(Fp::<5>::new(x)),
        7 => crate::disc::is_square(Fp::<7>::new(x)),
        11 => crate::disc::is_square(Fp::<11>::new(x)),
        13 => crate::disc::is_square(Fp::<13>::new(x)),
        _ => return Err(PyValueError::new_err("supported primes: 3, 5, 7, 11, 13")),
    })
}

/// The Hasse–Witt invariant of a diagonal form `q` over `F_p` (always +1 over a
/// finite field). Supported primes: 3, 5, 7, 11, 13.
#[pyfunction]
fn hasse_invariant(p: u64, q: Vec<i64>) -> PyResult<i8> {
    let res = match p {
        3 => crate::disc::hasse_invariant(&fp_diag::<3>(&q)),
        5 => crate::disc::hasse_invariant(&fp_diag::<5>(&q)),
        7 => crate::disc::hasse_invariant(&fp_diag::<7>(&q)),
        11 => crate::disc::hasse_invariant(&fp_diag::<11>(&q)),
        13 => crate::disc::hasse_invariant(&fp_diag::<13>(&q)),
        _ => return Err(PyValueError::new_err("supported primes: 3, 5, 7, 11, 13")),
    };
    res.ok_or_else(|| PyValueError::new_err("non-diagonal metric"))
}

// ---------------------------------------------------------------------------
// Non-Archimedean Springer decomposition (surreal)
// ---------------------------------------------------------------------------

#[pyclass(name = "SpringerDecomp", module = "pleroma")]
struct PySpringerDecomp {
    #[pyo3(get)]
    graded: Vec<(String, (usize, usize))>,
    #[pyo3(get)]
    radical_dim: usize,
    #[pyo3(get)]
    total_signature: (usize, usize),
}

#[pymethods]
impl PySpringerDecomp {
    fn __repr__(&self) -> String {
        format!(
            "SpringerDecomp(graded={:?}, radical_dim={}, total_signature={:?})",
            self.graded, self.radical_dim, self.total_signature
        )
    }
}

/// The non-Archimedean Springer decomposition of a diagonal surreal form: its
/// ω-adic valuation filtration into residue ℝ-signatures.
#[pyfunction]
fn springer_decompose(alg: &SurrealAlgebra) -> PyResult<PySpringerDecomp> {
    let d = crate::springer::springer_decompose(&alg.inner.metric)
        .ok_or_else(|| PyValueError::new_err("Springer decomposition needs a diagonal metric"))?;
    let graded = d
        .graded
        .iter()
        .map(|rf| (format!("{:?}", rf.valuation), rf.signature))
        .collect();
    Ok(PySpringerDecomp {
        graded,
        radical_dim: d.radical_dim,
        total_signature: d.total_signature,
    })
}

// ---------------------------------------------------------------------------
// Conformal geometric algebra over the surreals
// ---------------------------------------------------------------------------

#[pyclass(name = "Cga", module = "pleroma")]
struct PyCga {
    inner: Cga<Surreal>,
}

impl PyCga {
    fn wrap(&self, mv: Multivector<Surreal>) -> SurrealMV {
        SurrealMV {
            alg: Arc::new(self.inner.alg.clone()),
            mv,
        }
    }
}

#[pymethods]
impl PyCga {
    #[new]
    fn new(n: usize) -> Self {
        PyCga { inner: Cga::new(n) }
    }
    #[getter]
    fn n(&self) -> usize {
        self.inner.n
    }
    #[getter]
    fn dim(&self) -> usize {
        self.inner.alg.dim
    }
    fn n_o(&self) -> SurrealMV {
        self.wrap(self.inner.n_o())
    }
    fn n_inf(&self) -> SurrealMV {
        self.wrap(self.inner.n_inf())
    }
    /// Lift a Euclidean point to the null cone: `up(p) = n_o + p + ½|p|² n_∞`.
    fn up(&self, p: Vec<Bound<'_, PyAny>>) -> PyResult<SurrealMV> {
        let mut pv = Vec::with_capacity(p.len());
        for x in &p {
            pv.push(parse_surreal(x)?);
        }
        Ok(self.wrap(self.inner.up(&pv)))
    }
    /// Recover a Euclidean point from a null vector (`None` if not normalizable).
    fn down(&self, x: &SurrealMV) -> Option<Vec<PySurreal>> {
        self.inner
            .down(&x.mv)
            .map(|v| v.into_iter().map(|s| PySurreal { inner: s }).collect())
    }
    /// The conformal inner product `x · y` (= `−½|p−q|²` on lifted points).
    fn inner(&self, x: &SurrealMV, y: &SurrealMV) -> PySurreal {
        PySurreal {
            inner: self.inner.inner(&x.mv, &y.mv),
        }
    }
    /// The sphere of squared radius `r2` about center `c`.
    fn sphere(&self, c: Vec<Bound<'_, PyAny>>, r2: &Bound<'_, PyAny>) -> PyResult<SurrealMV> {
        let mut cv = Vec::with_capacity(c.len());
        for x in &c {
            cv.push(parse_surreal(x)?);
        }
        Ok(self.wrap(self.inner.sphere(&cv, &parse_surreal(r2)?)))
    }
    /// The plane `{x : x·normal = d}`.
    fn plane(&self, normal: Vec<Bound<'_, PyAny>>, d: &Bound<'_, PyAny>) -> PyResult<SurrealMV> {
        let mut nv = Vec::with_capacity(normal.len());
        for x in &normal {
            nv.push(parse_surreal(x)?);
        }
        Ok(self.wrap(self.inner.plane(&nv, &parse_surreal(d)?)))
    }
    /// The point pair / oriented join `a ∧ b`.
    fn point_pair(&self, a: &SurrealMV, b: &SurrealMV) -> SurrealMV {
        self.wrap(self.inner.point_pair(&a.mv, &b.mv))
    }
    /// The IPNS meet (intersection) `x ∧ y`.
    fn meet(&self, x: &SurrealMV, y: &SurrealMV) -> SurrealMV {
        self.wrap(self.inner.meet(&x.mv, &y.mv))
    }
}

#[pyfunction]
fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

#[pymodule]
fn pleroma(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyNimber>()?;
    m.add_class::<NimberAlgebra>()?;
    m.add_class::<NimberMV>()?;
    m.add_class::<PySurreal>()?;
    m.add_class::<SurrealAlgebra>()?;
    m.add_class::<SurrealMV>()?;
    m.add_class::<PySurcomplex>()?;
    m.add_class::<SurcomplexAlgebra>()?;
    m.add_class::<SurcomplexMV>()?;
    m.add_class::<PyInteger>()?;
    m.add_class::<IntegerAlgebra>()?;
    m.add_class::<IntegerMV>()?;
    // Omnific-integer backend (Oz)
    m.add_class::<PyOmnific>()?;
    m.add_class::<OmnificAlgebra>()?;
    m.add_class::<OmnificMV>()?;
    m.add_function(wrap_pyfunction!(omnific, m)?)?;
    m.add_function(wrap_pyfunction!(omnific_omega, m)?)?;
    m.add_function(wrap_pyfunction!(omega, m)?)?;
    m.add_function(wrap_pyfunction!(epsilon, m)?)?;
    m.add_function(wrap_pyfunction!(omega_pow, m)?)?;
    m.add_function(wrap_pyfunction!(rational, m)?)?;
    m.add_function(wrap_pyfunction!(surreal, m)?)?;
    m.add_class::<PyArfResult>()?;
    m.add_function(wrap_pyfunction!(arf_invariant, m)?)?;
    m.add_function(wrap_pyfunction!(nim_mul_mex, m)?)?;
    // char-0 classifier
    m.add_class::<PyCliffordType>()?;
    m.add_function(wrap_pyfunction!(classify_surreal, m)?)?;
    m.add_function(wrap_pyfunction!(classify_surcomplex, m)?)?;
    // Witt group + Dickson invariant
    m.add_class::<PyWittClass>()?;
    m.add_function(wrap_pyfunction!(witt_class, m)?)?;
    m.add_function(wrap_pyfunction!(dickson_matrix, m)?)?;
    m.add_function(wrap_pyfunction!(dickson_of_versor, m)?)?;
    // nim field ops (Artin–Schreier ↔ Arf)
    m.add_function(wrap_pyfunction!(nim_sqrt, m)?)?;
    m.add_function(wrap_pyfunction!(nim_trace, m)?)?;
    m.add_function(wrap_pyfunction!(nim_solve_artin_schreier, m)?)?;
    m.add_function(wrap_pyfunction!(nim_is_artin_schreier_solvable, m)?)?;
    // partizan games + the exterior algebra of the game group
    m.add_class::<PyGame>()?;
    m.add_class::<PyGameExterior>()?;
    // transfinite (ordinal) nimbers
    m.add_class::<PyOrdinal>()?;
    // odd-characteristic classifier (the trichotomy's third leg)
    m.add_class::<PyOddCharType>()?;
    m.add_class::<PyWittClassG>()?;
    m.add_function(wrap_pyfunction!(classify_oddchar, m)?)?;
    m.add_function(wrap_pyfunction!(oddchar_witt, m)?)?;
    m.add_function(wrap_pyfunction!(is_square_mod, m)?)?;
    m.add_function(wrap_pyfunction!(hasse_invariant, m)?)?;
    // non-Archimedean Springer decomposition
    m.add_class::<PySpringerDecomp>()?;
    m.add_function(wrap_pyfunction!(springer_decompose, m)?)?;
    // conformal geometric algebra (surreal)
    m.add_class::<PyCga>()?;
    m.add_function(wrap_pyfunction!(version, m)?)?;
    Ok(())
}
