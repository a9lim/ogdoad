//! PyO3 bindings — per-backend classes.
//!
//! Each scalar world (nimber / surreal / surcomplex) gets its own scalar type,
//! `<World>Algebra`, and `<World>MV` multivector. The Algebra/MV pair is
//! stamped out by the `backend!` macro, monomorphising the same verified
//! generic engine to the concrete scalar type — so there is no runtime
//! dispatch and no way to mix scalar worlds in one algebra.

use crate::clifford::{CliffordAlgebra, Metric, Multivector};
use crate::nimber::Nimber;
use crate::scalar::{Rational, Scalar};
use crate::surcomplex::Surcomplex;
use crate::surreal::Surreal;
use pyo3::basic::CompareOp;
use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyDict;
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
        PyNimber { inner: Nimber(value) }
    }
    #[getter]
    fn value(&self) -> u64 {
        self.inner.0
    }
    fn __add__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyNimber> {
        Ok(PyNimber { inner: self.inner.add(&parse_nimber(other)?) })
    }
    fn __radd__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyNimber> {
        self.__add__(other)
    }
    fn __mul__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyNimber> {
        Ok(PyNimber { inner: self.inner.mul(&parse_nimber(other)?) })
    }
    fn __rmul__(&self, other: &Bound<'_, PyAny>) -> PyResult<PyNimber> {
        self.__mul__(other)
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
        Ok(PySurreal { inner: self.inner.add(&parse_surreal(other)?) })
    }
    fn __radd__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurreal> {
        self.__add__(other)
    }
    fn __sub__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurreal> {
        Ok(PySurreal { inner: self.inner.sub(&parse_surreal(other)?) })
    }
    fn __rsub__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurreal> {
        Ok(PySurreal { inner: parse_surreal(other)?.sub(&self.inner) })
    }
    fn __mul__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurreal> {
        Ok(PySurreal { inner: self.inner.mul(&parse_surreal(other)?) })
    }
    fn __rmul__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurreal> {
        self.__mul__(other)
    }
    fn __neg__(&self) -> PySurreal {
        PySurreal { inner: self.inner.neg() }
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
        Ok(PySurcomplex { inner: Surcomplex::new(r, i) })
    }
    #[staticmethod]
    fn i() -> PySurcomplex {
        PySurcomplex { inner: Surcomplex::i() }
    }
    #[getter]
    fn re(&self) -> PySurreal {
        PySurreal { inner: self.inner.re.clone() }
    }
    #[getter]
    fn im(&self) -> PySurreal {
        PySurreal { inner: self.inner.im.clone() }
    }
    fn conj(&self) -> PySurcomplex {
        PySurcomplex { inner: self.inner.conj() }
    }
    fn __add__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurcomplex> {
        Ok(PySurcomplex { inner: self.inner.add(&parse_surcomplex(other)?) })
    }
    fn __radd__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurcomplex> {
        self.__add__(other)
    }
    fn __sub__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurcomplex> {
        Ok(PySurcomplex { inner: self.inner.sub(&parse_surcomplex(other)?) })
    }
    fn __mul__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurcomplex> {
        Ok(PySurcomplex { inner: self.inner.mul(&parse_surcomplex(other)?) })
    }
    fn __rmul__(&self, other: &Bound<'_, PyAny>) -> PyResult<PySurcomplex> {
        self.__mul__(other)
    }
    fn __neg__(&self) -> PySurcomplex {
        PySurcomplex { inner: self.inner.neg() }
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

// ---------------------------------------------------------------------------
// Algebra + multivector, one pair per backend
// ---------------------------------------------------------------------------

macro_rules! backend {
    ($alg:ident, $alg_name:literal, $mv:ident, $mv_name:literal, $scalar:ty, $parse:path) => {
        #[pyclass(name = $alg_name, module = "pleroma", from_py_object)]
        #[derive(Clone)]
        struct $alg {
            inner: Arc<CliffordAlgebra<$scalar>>,
        }

        #[pymethods]
        impl $alg {
            #[new]
            #[pyo3(signature = (q, b=None))]
            fn new(q: Vec<Bound<'_, PyAny>>, b: Option<Bound<'_, PyDict>>) -> PyResult<Self> {
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
                let dim = qv.len();
                let metric = Metric { q: qv, b: bm };
                Ok($alg { inner: Arc::new(CliffordAlgebra::new(dim, metric)) })
            }

            #[getter]
            fn dim(&self) -> usize {
                self.inner.dim
            }
            fn gen(&self, i: usize) -> $mv {
                $mv { alg: self.inner.clone(), mv: self.inner.gen(i) }
            }
            fn blade(&self, gens: Vec<usize>) -> $mv {
                $mv { alg: self.inner.clone(), mv: self.inner.blade(&gens) }
            }
            fn scalar(&self, s: &Bound<'_, PyAny>) -> PyResult<$mv> {
                Ok($mv { alg: self.inner.clone(), mv: self.inner.scalar($parse(s)?) })
            }
            fn zero(&self) -> $mv {
                $mv { alg: self.inner.clone(), mv: self.inner.zero() }
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
                $mv { alg: self.alg.clone(), mv: self.alg.add(&self.mv, &other.mv) }
            }
            fn __sub__(&self, other: &$mv) -> $mv {
                let neg_one = <$scalar as Scalar>::one().neg();
                let neg = self.alg.scalar_mul(&neg_one, &other.mv);
                $mv { alg: self.alg.clone(), mv: self.alg.add(&self.mv, &neg) }
            }
            fn __neg__(&self) -> $mv {
                let neg_one = <$scalar as Scalar>::one().neg();
                $mv { alg: self.alg.clone(), mv: self.alg.scalar_mul(&neg_one, &self.mv) }
            }
            fn __mul__(&self, other: &Bound<'_, PyAny>) -> PyResult<$mv> {
                if let Ok(o) = other.cast::<$mv>() {
                    return Ok($mv {
                        alg: self.alg.clone(),
                        mv: self.alg.mul(&self.mv, &o.borrow().mv),
                    });
                }
                let s = $parse(other)?;
                Ok($mv { alg: self.alg.clone(), mv: self.alg.scalar_mul(&s, &self.mv) })
            }
            fn __rmul__(&self, other: &Bound<'_, PyAny>) -> PyResult<$mv> {
                let s = $parse(other)?;
                Ok($mv { alg: self.alg.clone(), mv: self.alg.scalar_mul(&s, &self.mv) })
            }
            fn __pow__(&self, n: u32, _modulo: Option<&Bound<'_, PyAny>>) -> $mv {
                let mut acc = self.alg.scalar(<$scalar as Scalar>::one());
                for _ in 0..n {
                    acc = self.alg.mul(&acc, &self.mv);
                }
                $mv { alg: self.alg.clone(), mv: acc }
            }
            /// Exterior (wedge) product; also bound to the `^` operator.
            fn wedge(&self, other: &$mv) -> $mv {
                $mv { alg: self.alg.clone(), mv: self.alg.wedge(&self.mv, &other.mv) }
            }
            fn __xor__(&self, other: &$mv) -> $mv {
                self.wedge(other)
            }
            fn reverse(&self) -> $mv {
                $mv { alg: self.alg.clone(), mv: self.alg.reverse(&self.mv) }
            }
            fn grade(&self, k: u32) -> $mv {
                $mv { alg: self.alg.clone(), mv: self.alg.grade_part(&self.mv, k) }
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

backend!(NimberAlgebra, "NimberAlgebra", NimberMV, "NimberMV", Nimber, parse_nimber);
backend!(SurrealAlgebra, "SurrealAlgebra", SurrealMV, "SurrealMV", Surreal, parse_surreal);
backend!(
    SurcomplexAlgebra,
    "SurcomplexAlgebra",
    SurcomplexMV,
    "SurcomplexMV",
    Surcomplex<Surreal>,
    parse_surcomplex
);

// ---------------------------------------------------------------------------
// Surreal builders
// ---------------------------------------------------------------------------

#[pyfunction]
fn omega() -> PySurreal {
    PySurreal { inner: Surreal::omega() }
}

#[pyfunction]
fn epsilon() -> PySurreal {
    PySurreal { inner: Surreal::epsilon() }
}

#[pyfunction]
fn omega_pow(exp: &Bound<'_, PyAny>) -> PyResult<PySurreal> {
    Ok(PySurreal { inner: Surreal::omega_pow(parse_surreal(exp)?) })
}

#[pyfunction]
fn rational(num: i128, den: i128) -> PyResult<PySurreal> {
    if den == 0 {
        return Err(PyValueError::new_err("zero denominator"));
    }
    Ok(PySurreal { inner: Surreal::from_rational(Rational::new(num, den)) })
}

#[pyfunction]
fn surreal(n: i128) -> PySurreal {
    PySurreal { inner: Surreal::from_int(n) }
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
    m.add_function(wrap_pyfunction!(omega, m)?)?;
    m.add_function(wrap_pyfunction!(epsilon, m)?)?;
    m.add_function(wrap_pyfunction!(omega_pow, m)?)?;
    m.add_function(wrap_pyfunction!(rational, m)?)?;
    m.add_function(wrap_pyfunction!(surreal, m)?)?;
    m.add_function(wrap_pyfunction!(version, m)?)?;
    Ok(())
}
