//! Clifford algebras as values: an `Algebra(S)` carries its metric, and a
//! multivector carries its algebra. A grade-0 value built from a literal is
//! algebra-free until it meets one.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::rc::Rc;

use ogdoad::clifford::{CliffordAlgebra, Metric, Multivector};
use ogdoad::scalar::{Fp, Fpn, Integer, Nimber, Omnific, Ordinal, Scalar, Surreal};

use super::super::error::{err, GrundyError, GrundyErrorKind, GrundyResult};
use super::super::eval::value::Value;
use super::super::types::TyCon;
use super::scalar::{GScalar, ScalarV};

/// Coefficient scalars usable in Clifford algebras.
pub trait CScalar: Scalar + 'static {
    /// The type constructor.
    const CON: TyCon;
    /// Read a grundy value.
    fn from_value(value: &Value) -> Option<Self>;
    /// Write a grundy value.
    fn to_value(&self) -> Value;
    /// Checked multivector product (ordinal nimbers can escape the tower).
    fn product(
        alg: &CliffordAlgebra<Self>,
        a: &Multivector<Self>,
        b: &Multivector<Self>,
    ) -> GrundyResult<Multivector<Self>> {
        Ok(alg.mul(a, b))
    }
    /// Checked scalar inverse.
    fn scalar_inverse(s: &Self) -> GrundyResult<Self> {
        if s.is_zero() {
            return Err(err(GrundyErrorKind::DivisionByZero, "division by zero"));
        }
        s.inv().ok_or_else(|| {
            err(
                GrundyErrorKind::NotInvertible,
                "the scalar is not invertible",
            )
        })
    }
}

macro_rules! cscalar_via_scalarv {
    ($($ty:ty => $variant:ident),*) => {$(
        impl CScalar for $ty {
            const CON: TyCon = <$ty as GScalar>::CON;
            fn from_value(value: &Value) -> Option<Self> {
                match value {
                    Value::Scalar(ScalarV::$variant(x)) => Some(x.clone()),
                    _ => None,
                }
            }
            fn to_value(&self) -> Value {
                Value::Scalar(ScalarV::$variant(self.clone()))
            }
            fn scalar_inverse(s: &Self) -> GrundyResult<Self> {
                GScalar::inverse(s)
            }
        }
    )*};
}

cscalar_via_scalarv!(
    Nimber => Nimber,
    Surreal => Surreal,
    Omnific => Omnific,
    Fp<2> => F2,
    Fp<3> => F3,
    Fp<5> => F5,
    Fp<7> => F7,
    Fpn<2, 2> => F4,
    Fpn<2, 3> => F8,
    Fpn<2, 4> => F16,
    Fpn<3, 2> => F9,
    Fpn<3, 3> => F27,
    Fpn<5, 2> => F25
);

impl CScalar for Ordinal {
    const CON: TyCon = TyCon::Ordinal;
    fn from_value(value: &Value) -> Option<Self> {
        match value {
            Value::Scalar(ScalarV::Ordinal(x)) => Some(x.clone()),
            _ => None,
        }
    }
    fn to_value(&self) -> Value {
        Value::Scalar(ScalarV::Ordinal(self.clone()))
    }
    fn product(
        alg: &CliffordAlgebra<Self>,
        a: &Multivector<Self>,
        b: &Multivector<Self>,
    ) -> GrundyResult<Multivector<Self>> {
        catch_unwind(AssertUnwindSafe(|| alg.mul(a, b))).map_err(|_| {
            err(
                GrundyErrorKind::KummerEscape,
                "ordinal nim arithmetic past the represented Kummer tower",
            )
            .with_hint("supported below ω^(ω^ω) when Kummer carries use primes ≤ 727")
        })
    }
    fn scalar_inverse(s: &Self) -> GrundyResult<Self> {
        GScalar::inverse(s)
    }
}

impl CScalar for Integer {
    const CON: TyCon = TyCon::Int;
    fn from_value(value: &Value) -> Option<Self> {
        match value {
            Value::Int(n) => Some(Integer(*n)),
            _ => None,
        }
    }
    fn to_value(&self) -> Value {
        Value::Int(self.0)
    }
}

/// The algebra two operands share, and the algebra their result keeps.
type Common<S> = (Rc<CliffordAlgebra<S>>, Option<Rc<CliffordAlgebra<S>>>);

/// A multivector with its algebra (`None` for an algebra-free scalar).
#[derive(Clone)]
pub struct MvData<S: CScalar> {
    /// The algebra, once the value has met one.
    pub alg: Option<Rc<CliffordAlgebra<S>>>,
    /// The coefficients.
    pub v: Multivector<S>,
}

fn scalar_algebra<S: CScalar>() -> CliffordAlgebra<S> {
    CliffordAlgebra::new(0, Metric::diagonal(Vec::new()))
}

fn mismatch() -> GrundyError {
    err(
        GrundyErrorKind::AlgebraMismatch,
        "multivectors from different Clifford algebras",
    )
    .with_hint("build both from one algebra's basis")
}

impl<S: CScalar> MvData<S> {
    /// An algebra-free scalar.
    pub fn scalar(s: S) -> MvData<S> {
        MvData {
            alg: None,
            v: scalar_algebra::<S>().scalar(s),
        }
    }

    fn common(&self, other: &MvData<S>) -> GrundyResult<Common<S>> {
        match (&self.alg, &other.alg) {
            (Some(a), Some(b)) => {
                if Rc::ptr_eq(a, b) || **a == **b {
                    Ok((a.clone(), Some(a.clone())))
                } else {
                    Err(mismatch())
                }
            }
            (Some(a), None) | (None, Some(a)) => Ok((a.clone(), Some(a.clone()))),
            (None, None) => Ok((Rc::new(scalar_algebra()), None)),
        }
    }

    /// The grade-0 coefficient if the value is purely scalar.
    pub fn as_scalar(&self) -> Option<S> {
        match self.v.terms().len() {
            0 => Some(S::zero()),
            1 => self.v.terms().get(&0).cloned(),
            _ => None,
        }
    }

    /// `+`
    pub fn add(&self, other: &MvData<S>) -> GrundyResult<MvData<S>> {
        let (alg, keep) = self.common(other)?;
        Ok(MvData {
            v: alg.add(&self.v, &other.v),
            alg: keep,
        })
    }

    /// Unary `-`.
    pub fn neg(&self) -> MvData<S> {
        let alg = self
            .alg
            .clone()
            .unwrap_or_else(|| Rc::new(scalar_algebra()));
        MvData {
            v: alg.scalar_mul(&S::one().neg(), &self.v),
            alg: self.alg.clone(),
        }
    }

    /// `⋅`
    pub fn mul(&self, other: &MvData<S>) -> GrundyResult<MvData<S>> {
        let (alg, keep) = self.common(other)?;
        Ok(MvData {
            v: S::product(&alg, &self.v, &other.v)?,
            alg: keep,
        })
    }

    /// `∧`
    pub fn wedge(&self, other: &MvData<S>) -> GrundyResult<MvData<S>> {
        let (alg, keep) = self.common(other)?;
        Ok(MvData {
            v: alg.wedge(&self.v, &other.v),
            alg: keep,
        })
    }

    /// Reciprocal.
    pub fn inverse(&self) -> GrundyResult<MvData<S>> {
        if let Some(s) = self.as_scalar() {
            let alg = self
                .alg
                .clone()
                .unwrap_or_else(|| Rc::new(scalar_algebra()));
            return Ok(MvData {
                v: alg.scalar(S::scalar_inverse(&s)?),
                alg: self.alg.clone(),
            });
        }
        let alg = self.alg.clone().expect("a non-scalar has an algebra");
        let inverse = alg.multivector_inverse(&self.v).ok_or_else(|| {
            err(
                GrundyErrorKind::NotInvertible,
                "the multivector is not invertible",
            )
        })?;
        Ok(MvData {
            v: inverse,
            alg: self.alg.clone(),
        })
    }

    /// `/`
    pub fn div(&self, other: &MvData<S>) -> GrundyResult<MvData<S>> {
        if other.v.is_zero() {
            return Err(err(GrundyErrorKind::DivisionByZero, "division by zero"));
        }
        self.mul(&other.inverse()?)
    }

    fn need_alg(&self) -> Rc<CliffordAlgebra<S>> {
        self.alg
            .clone()
            .unwrap_or_else(|| Rc::new(scalar_algebra()))
    }

    /// The reverse.
    pub fn rev(&self) -> GrundyResult<MvData<S>> {
        let alg = self.need_alg();
        if alg.metric().has_upper() {
            return Err(err(
                GrundyErrorKind::GeneralMetric,
                "reverse is undefined for a general bilinear metric",
            )
            .with_hint("reverse is undefined for the Chevalley construction"));
        }
        Ok(MvData {
            v: alg.reverse(&self.v),
            alg: self.alg.clone(),
        })
    }

    /// The grade-`k` part.
    pub fn grade(&self, k: i128) -> GrundyResult<MvData<S>> {
        let k =
            usize::try_from(k).map_err(|_| err(GrundyErrorKind::Domain, "grades are natural"))?;
        let alg = self.need_alg();
        Ok(MvData {
            v: alg.grade_part(&self.v, k),
            alg: self.alg.clone(),
        })
    }

    /// The even part.
    pub fn even(&self) -> MvData<S> {
        let alg = self.need_alg();
        MvData {
            v: alg.even_part(&self.v),
            alg: self.alg.clone(),
        }
    }

    /// The dual.
    pub fn dual(&self) -> GrundyResult<MvData<S>> {
        let alg = self.need_alg();
        if alg.metric().has_upper() {
            return Err(err(
                GrundyErrorKind::GeneralMetric,
                "dual is undefined for a general bilinear metric",
            ));
        }
        let dual = alg.dual(&self.v).ok_or_else(|| {
            err(
                GrundyErrorKind::NotInvertible,
                "the pseudoscalar is not invertible",
            )
        })?;
        Ok(MvData {
            v: dual,
            alg: self.alg.clone(),
        })
    }

    /// The coefficient of `e_i`.
    pub fn component(&self, i: i128) -> GrundyResult<S> {
        let dim = self.alg.as_ref().map_or(0, |alg| alg.dim());
        let index = usize::try_from(i)
            .ok()
            .filter(|&i| i < dim)
            .ok_or_else(|| {
                err(
                    GrundyErrorKind::BladeIndex,
                    format!("index {i} is outside dimension {dim}"),
                )
            })?;
        Ok(self
            .v
            .terms()
            .get(&(1u128 << index))
            .cloned()
            .unwrap_or_else(S::zero))
    }

    /// The scalar part.
    pub fn scalar_part(&self) -> S {
        self.v.terms().get(&0).cloned().unwrap_or_else(S::zero)
    }
}

macro_rules! clifford_enums {
    ($($variant:ident($ty:ty)),* $(,)?) => {
        /// A Clifford algebra over one backend.
        #[derive(Clone)]
        pub enum AlgebraV {
            $(
                #[doc = stringify!($ty)]
                $variant(Rc<CliffordAlgebra<$ty>>),
            )*
        }

        /// A multivector over one backend.
        #[derive(Clone)]
        pub enum MvV {
            $(
                #[doc = stringify!($ty)]
                $variant(MvData<$ty>),
            )*
        }

        impl MvV {
            /// An algebra-free scalar from a coefficient value.
            pub fn from_scalar(value: &Value) -> Option<MvV> {
                $(if let Some(s) = <$ty as CScalar>::from_value(value) {
                    return Some(MvV::$variant(MvData::scalar(s)));
                })*
                None
            }

            /// Apply a same-backend binary operation.
            pub fn zip(&self, other: &MvV, op: MvOp) -> GrundyResult<MvV> {
                match (self, other) {
                    $((MvV::$variant(a), MvV::$variant(b)) => Ok(MvV::$variant(match op {
                        MvOp::Add => a.add(b)?,
                        MvOp::Sub => a.add(&b.neg())?,
                        MvOp::Mul => a.mul(b)?,
                        MvOp::Div => a.div(b)?,
                        MvOp::Wedge => a.wedge(b)?,
                    })),)*
                    _ => unreachable!("multivector backends differ"),
                }
            }

            /// Apply a unary operation.
            pub fn map(&self, op: MvUnary) -> GrundyResult<MvV> {
                match self {
                    $(MvV::$variant(a) => Ok(MvV::$variant(match op {
                        MvUnary::Neg => a.neg(),
                        MvUnary::Inverse => a.inverse()?,
                        MvUnary::Rev => a.rev()?,
                        MvUnary::Grade(k) => a.grade(k)?,
                        MvUnary::Even => a.even(),
                        MvUnary::Dual => a.dual()?,
                    })),)*
                }
            }

            /// The coefficient of `e_i`.
            pub fn component(&self, i: i128) -> GrundyResult<Value> {
                match self {
                    $(MvV::$variant(a) => Ok(a.component(i)?.to_value()),)*
                }
            }

            /// The scalar part.
            pub fn scalar_part(&self) -> Value {
                match self {
                    $(MvV::$variant(a) => a.scalar_part().to_value(),)*
                }
            }

            /// The algebra, if the value has met one.
            pub fn algebra(&self) -> Option<AlgebraV> {
                match self {
                    $(MvV::$variant(a) => a.alg.clone().map(AlgebraV::$variant),)*
                }
            }

            /// The coefficient type.
            pub fn con(&self) -> TyCon {
                match self {
                    $(MvV::$variant(_) => <$ty as CScalar>::CON,)*
                }
            }

            /// Whether the value is zero.
            pub fn is_zero(&self) -> bool {
                match self {
                    $(MvV::$variant(a) => a.v.is_zero(),)*
                }
            }

            /// The algebra-free unit of this backend.
            pub fn one_like(&self) -> MvV {
                match self {
                    $(MvV::$variant(_) => MvV::$variant(MvData::scalar(<$ty>::one())),)*
                }
            }

            /// The term count, for work accounting.
            pub fn size(&self) -> u128 {
                match self {
                    $(MvV::$variant(a) => a.v.terms().len().max(1) as u128,)*
                }
            }

            /// Whether any blade term is present.
            pub fn has_blades(&self) -> bool {
                match self {
                    $(MvV::$variant(a) => a.v.terms().keys().any(|mask| *mask != 0),)*
                }
            }
        }

        impl fmt::Display for MvV {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self {
                    $(MvV::$variant(a) => write!(f, "{}", a.v),)*
                }
            }
        }

        impl AlgebraV {
            /// Build an algebra from metric data given as values.
            pub fn build(
                con: TyCon,
                q: &[Value],
                b: &[((usize, usize), Value)],
                a: &[((usize, usize), Value)],
            ) -> GrundyResult<AlgebraV> {
                $(if con == <$ty as CScalar>::CON {
                    let read = |v: &Value| <$ty as CScalar>::from_value(v).expect("typed coefficient");
                    let q: Vec<$ty> = q.iter().map(read).collect();
                    let dim = q.len();
                    if dim > 128 {
                        return Err(err(GrundyErrorKind::DimMismatch, "Clifford dimension is at most 128"));
                    }
                    for ((i, j), _) in b.iter().chain(a) {
                        if *i >= dim || *j >= dim || i == j {
                            return Err(err(GrundyErrorKind::BladeIndex, format!("metric pair ({i}, {j}) is outside dimension {dim}")));
                        }
                    }
                    let b: Vec<((usize, usize), $ty)> = b.iter().map(|(k, v)| (*k, read(v))).collect();
                    let a: BTreeMap<(usize, usize), $ty> = a.iter().map(|(k, v)| (*k, read(v))).collect();
                    let metric = if a.is_empty() {
                        Metric::new(q, b)
                    } else {
                        Metric::general(q, b, a)
                    };
                    return Ok(AlgebraV::$variant(Rc::new(CliffordAlgebra::new(dim, metric))));
                })*
                Err(err(GrundyErrorKind::Type, "not a Clifford coefficient type"))
            }

            /// The Grassmann algebra of a dimension.
            pub fn grassmann(con: TyCon, dim: usize) -> GrundyResult<AlgebraV> {
                $(if con == <$ty as CScalar>::CON {
                    return Ok(AlgebraV::$variant(Rc::new(CliffordAlgebra::new(dim, Metric::grassmann(dim)))));
                })*
                Err(err(GrundyErrorKind::Type, "not a Clifford coefficient type"))
            }

            /// The dimension.
            pub fn dim(&self) -> usize {
                match self {
                    $(AlgebraV::$variant(alg) => alg.dim(),)*
                }
            }

            /// The coefficient type.
            pub fn con(&self) -> TyCon {
                match self {
                    $(AlgebraV::$variant(_) => <$ty as CScalar>::CON,)*
                }
            }

            /// The basis vectors `e0 … e(n-1)`.
            pub fn basis(&self) -> Vec<MvV> {
                match self {
                    $(AlgebraV::$variant(alg) => (0..alg.dim())
                        .map(|i| MvV::$variant(MvData { alg: Some(alg.clone()), v: alg.e(i) }))
                        .collect(),)*
                }
            }

            /// `Σ xs[i]⋅e_i`.
            pub fn vector(&self, xs: &[Value]) -> GrundyResult<MvV> {
                if xs.len() != self.dim() {
                    return Err(err(
                        GrundyErrorKind::DimMismatch,
                        format!("{} coordinates for dimension {}", xs.len(), self.dim()),
                    ));
                }
                match self {
                    $(AlgebraV::$variant(alg) => {
                        let mut acc = alg.zero();
                        for (i, x) in xs.iter().enumerate() {
                            let s = <$ty as CScalar>::from_value(x).expect("typed coefficient");
                            acc = alg.add(&acc, &alg.scalar_mul(&s, &alg.e(i)));
                        }
                        Ok(MvV::$variant(MvData { alg: Some(alg.clone()), v: acc }))
                    })*
                }
            }

            /// The metric as `(q, b, a)` values, for display.
            pub fn metric_values(&self) -> (Vec<Value>, Vec<((usize, usize), Value)>, Vec<((usize, usize), Value)>) {
                match self {
                    $(AlgebraV::$variant(alg) => {
                        let m = alg.metric();
                        (
                            m.q().iter().map(CScalar::to_value).collect(),
                            m.b().iter().map(|(k, v)| (*k, v.to_value())).collect(),
                            m.a().iter().map(|(k, v)| (*k, v.to_value())).collect(),
                        )
                    })*
                }
            }
        }
    };
}

clifford_enums! {
    Int(Integer),
    Nimber(Nimber),
    Ordinal(Ordinal),
    Surreal(Surreal),
    Omnific(Omnific),
    F2(Fp<2>),
    F3(Fp<3>),
    F5(Fp<5>),
    F7(Fp<7>),
    F4(Fpn<2, 2>),
    F8(Fpn<2, 3>),
    F16(Fpn<2, 4>),
    F9(Fpn<3, 2>),
    F27(Fpn<3, 3>),
    F25(Fpn<5, 2>),
}

/// Binary multivector operations.
#[derive(Clone, Copy)]
pub enum MvOp {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `⋅`
    Mul,
    /// `/`
    Div,
    /// `∧`
    Wedge,
}

/// Unary multivector operations.
#[derive(Clone, Copy)]
pub enum MvUnary {
    /// `-`
    Neg,
    /// `/`
    Inverse,
    /// `rev`
    Rev,
    /// `grade(·, k)`
    Grade(i128),
    /// `even`
    Even,
    /// `dual`
    Dual,
}

impl MvV {
    /// The structural order.
    pub fn key_cmp(&self, other: &MvV) -> Ordering {
        self.to_string().cmp(&other.to_string())
    }
}
