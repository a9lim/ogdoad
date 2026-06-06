//! PyO3 bindings — per-backend classes.
//!
//! Each scalar world (nimber / surreal / surcomplex) gets its own scalar type,
//! `<World>Algebra`, and `<World>MV` multivector. The Algebra/MV pair is
//! stamped out by the `backend!` macro, monomorphising the same verified
//! generic engine to the concrete scalar type — so there is no runtime
//! dispatch and no way to mix scalar worlds in one algebra.

use crate::clifford::{CliffordAlgebra, Metric, Multivector};
use crate::nimber::Nimber;
use crate::partizan::Game;
use crate::scalar::{Integer, Rational, Scalar};
use crate::surcomplex::Surcomplex;
use crate::surreal::Surreal;
use crate::witt::WittClass;
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
    m.add_function(wrap_pyfunction!(version, m)?)?;
    Ok(())
}
