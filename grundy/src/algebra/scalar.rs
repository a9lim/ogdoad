//! Scalar types: the coefficient worlds of 0.3.6, now coexisting as types.

use std::cmp::Ordering;
use std::fmt;

use ogdoad::scalar::{FiniteField, Fp, Fpn, Nimber, Omnific, Ordinal, Scalar, Surreal};

use super::super::error::{err, GrundyErrorKind, GrundyResult};
use super::super::syntax::ast::{CnfExponent, CnfTerm, RelOp, StarIndex};
use super::super::types::TyCon;

/// The ordinal a structural CNF denotes.
pub fn cnf_to_ordinal(terms: &[CnfTerm]) -> Ordinal {
    let mut out = Ordinal::from_u128(0);
    for term in terms {
        let piece = match &term.exponent {
            None => Ordinal::from_u128(term.coefficient),
            Some(exponent) => Ordinal::monomial(cnf_exponent_ordinal(exponent), term.coefficient),
        };
        out = out.nim_add(&piece);
    }
    out
}

/// The ordinal a CNF exponent denotes.
pub fn cnf_exponent_ordinal(exponent: &CnfExponent) -> Ordinal {
    match exponent {
        CnfExponent::Finite(n) => Ordinal::from_u128(*n),
        CnfExponent::Omega => Ordinal::omega(),
        CnfExponent::Cnf(terms) => cnf_to_ordinal(terms),
    }
}

/// The exponent of one CNF term (zero for a finite term).
pub fn cnf_term_exponent(term: &CnfTerm) -> Ordinal {
    match &term.exponent {
        None => Ordinal::from_u128(0),
        Some(exponent) => cnf_exponent_ordinal(exponent),
    }
}

/// Per-backend literal and partiality behavior.
pub trait GScalar: Scalar + Sized + 'static {
    /// The type constructor.
    const CON: TyCon;
    /// A numeral (only for types with integer literals).
    fn int_literal(_n: u128) -> GrundyResult<Self> {
        Err(err(GrundyErrorKind::Type, "no integer literals"))
    }
    /// A star literal (only for nimber types).
    fn star_literal(_index: &StarIndex) -> GrundyResult<Self> {
        Err(err(GrundyErrorKind::Type, "no star literals"))
    }
    /// `ω` (only for the surreal family).
    fn omega() -> GrundyResult<Self> {
        Err(err(GrundyErrorKind::Type, "no `ω`"))
    }
    /// Multiplicative inverse with an attributable failure.
    fn inverse(&self) -> GrundyResult<Self> {
        if self.is_zero() {
            return Err(err(GrundyErrorKind::DivisionByZero, "division by zero"));
        }
        self.inv()
            .ok_or_else(|| err(GrundyErrorKind::NotInvertible, "not invertible"))
    }
    /// `a / b`.
    fn divide(&self, rhs: &Self) -> GrundyResult<Self> {
        Ok(self.mul(&rhs.inverse()?))
    }
    /// `a % b`.
    fn remainder(&self, _rhs: &Self) -> GrundyResult<Self> {
        Err(err(GrundyErrorKind::Type, "no remainder"))
    }
    /// The partial order, where the type has one.
    fn compare(&self, _rhs: &Self) -> Option<Ordering> {
        None
    }
    /// Checked product.
    fn times(&self, rhs: &Self) -> GrundyResult<Self> {
        Ok(self.mul(rhs))
    }
    /// Checked power by a natural exponent.
    fn power(&self, mut k: u128) -> GrundyResult<Self> {
        let mut acc = Self::one();
        let mut x = self.clone();
        while k > 0 {
            if k & 1 == 1 {
                acc = acc.times(&x)?;
            }
            k >>= 1;
            if k > 0 {
                x = x.times(&x)?;
            }
        }
        Ok(acc)
    }
    /// Whether the order is the nimber antichain (`∥` means `≠`).
    fn antichain() -> bool {
        false
    }
}

fn kummer_escape() -> super::super::error::GrundyError {
    err(
        GrundyErrorKind::KummerEscape,
        "ordinal nim arithmetic past the represented Kummer tower",
    )
    .with_hint("supported below ω^(ω^ω) when Kummer carries use primes ≤ 727")
}

fn modulus_error() -> super::super::error::GrundyError {
    err(GrundyErrorKind::Modulus, "moduli here are monic ω-powers")
        .with_hint("`% ω↑2` truncates the CNF below it; every nonzero constant is a unit")
}

impl GScalar for Nimber {
    const CON: TyCon = TyCon::Nimber;
    fn star_literal(index: &StarIndex) -> GrundyResult<Self> {
        match index {
            StarIndex::Finite(n) => Ok(Nimber(*n)),
            _ => Err(err(
                GrundyErrorKind::Domain,
                "transfinite star literals are Ordinal nimbers",
            )
            .with_hint("annotate: `(*ω : Ordinal)`")),
        }
    }
    fn antichain() -> bool {
        true
    }
}

impl GScalar for Ordinal {
    const CON: TyCon = TyCon::Ordinal;
    fn star_literal(index: &StarIndex) -> GrundyResult<Self> {
        Ok(match index {
            StarIndex::Finite(n) => Ordinal::from_u128(*n),
            StarIndex::Omega => Ordinal::omega(),
            StarIndex::Cnf(terms) => cnf_to_ordinal(terms),
        })
    }
    fn inverse(&self) -> GrundyResult<Self> {
        if self.is_zero() {
            return Err(err(GrundyErrorKind::DivisionByZero, "division by zero"));
        }
        self.checked_inv().ok_or_else(kummer_escape)
    }
    fn times(&self, rhs: &Self) -> GrundyResult<Self> {
        self.nim_mul(rhs).ok_or_else(kummer_escape)
    }
    fn power(&self, k: u128) -> GrundyResult<Self> {
        self.nim_pow(k).ok_or_else(kummer_escape)
    }
    fn antichain() -> bool {
        true
    }
}

impl GScalar for Surreal {
    const CON: TyCon = TyCon::Surreal;
    fn int_literal(n: u128) -> GrundyResult<Self> {
        Ok(Surreal::from_int(to_i128(n)?))
    }
    fn omega() -> GrundyResult<Self> {
        Ok(Surreal::omega())
    }
    fn inverse(&self) -> GrundyResult<Self> {
        if self.is_zero() {
            return Err(err(GrundyErrorKind::DivisionByZero, "division by zero"));
        }
        self.inv().ok_or_else(|| {
            err(
                GrundyErrorKind::NotInvertible,
                "only CNF monomials invert exactly; 1/(ω+1) is an infinite Hahn series",
            )
        })
    }
    fn remainder(&self, rhs: &Self) -> GrundyResult<Self> {
        if rhs.is_zero() {
            return Err(err(GrundyErrorKind::DivisionByZero, "division by zero"));
        }
        self.rem(rhs).ok_or_else(modulus_error)
    }
    fn compare(&self, rhs: &Self) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}

impl GScalar for Omnific {
    const CON: TyCon = TyCon::Omnific;
    fn int_literal(n: u128) -> GrundyResult<Self> {
        Ok(Omnific::from_int(to_i128(n)?))
    }
    fn omega() -> GrundyResult<Self> {
        Ok(Omnific::omega())
    }
    fn remainder(&self, rhs: &Self) -> GrundyResult<Self> {
        if rhs.is_zero() {
            return Err(err(GrundyErrorKind::DivisionByZero, "division by zero"));
        }
        self.rem(rhs).ok_or_else(modulus_error)
    }
    fn compare(&self, rhs: &Self) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}

macro_rules! fp_scalars {
    ($($p:literal),*) => {$(
        impl GScalar for Fp<$p> {
            const CON: TyCon = TyCon::Fp($p);
            fn int_literal(n: u128) -> GrundyResult<Self> {
                Ok(Fp::<$p>::from_u128(n))
            }
        }
    )*};
}

macro_rules! fpn_scalars {
    ($(($p:literal, $n:literal)),*) => {$(
        impl GScalar for Fpn<$p, $n> {
            const CON: TyCon = TyCon::Fpn($p, $n);
            fn int_literal(n: u128) -> GrundyResult<Self> {
                Ok(Fpn::<$p, $n>::constant(n))
            }
        }
    )*};
}

fp_scalars!(2, 3, 5, 7);
fpn_scalars!((2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (5, 2));

fn to_i128(n: u128) -> GrundyResult<i128> {
    i128::try_from(n).map_err(|_| err(GrundyErrorKind::Overflow, "literal exceeds i128"))
}

macro_rules! scalar_enum {
    ($($variant:ident($ty:ty)),* $(,)?) => {
        /// A scalar value of one backend.
        #[derive(Clone, PartialEq)]
        pub enum ScalarV {
            $(
                #[doc = stringify!($ty)]
                $variant($ty),
            )*
        }

        impl ScalarV {
            /// The type constructor of the backend.
            pub fn con(&self) -> TyCon {
                match self {
                    $(ScalarV::$variant(_) => <$ty as GScalar>::CON,)*
                }
            }

            /// Apply a same-backend binary operation.
            pub fn zip(
                &self,
                rhs: &ScalarV,
                op: impl ScalarBinOp,
            ) -> GrundyResult<ScalarV> {
                match (self, rhs) {
                    $((ScalarV::$variant(a), ScalarV::$variant(b)) => op.apply(a, b).map(ScalarV::$variant),)*
                    _ => Err(err(GrundyErrorKind::Type, "scalar backends differ")),
                }
            }

            /// Apply a unary operation.
            pub fn map(&self, op: impl ScalarUnOp) -> GrundyResult<ScalarV> {
                match self {
                    $(ScalarV::$variant(a) => op.apply(a).map(ScalarV::$variant),)*
                }
            }

            /// Compare same-backend values.
            pub fn compare(&self, rhs: &ScalarV) -> Option<Ordering> {
                match (self, rhs) {
                    $((ScalarV::$variant(a), ScalarV::$variant(b)) => GScalar::compare(a, b),)*
                    _ => None,
                }
            }

            /// Whether the backend's order is the nimber antichain.
            pub fn antichain(&self) -> bool {
                match self {
                    $(ScalarV::$variant(_) => <$ty as GScalar>::antichain(),)*
                }
            }

            /// Build a scalar of a type from an integer literal.
            pub fn int_literal(con: TyCon, n: u128) -> GrundyResult<ScalarV> {
                $(if con == <$ty as GScalar>::CON {
                    return <$ty as GScalar>::int_literal(n).map(ScalarV::$variant);
                })*
                Err(err(GrundyErrorKind::Type, "not a scalar type"))
            }

            /// Build a scalar of a type from a star literal.
            pub fn star_literal(con: TyCon, index: &StarIndex) -> GrundyResult<ScalarV> {
                $(if con == <$ty as GScalar>::CON {
                    return <$ty as GScalar>::star_literal(index).map(ScalarV::$variant);
                })*
                Err(err(GrundyErrorKind::Type, "not a scalar type"))
            }

            /// `ω` at a type.
            pub fn omega(con: TyCon) -> GrundyResult<ScalarV> {
                $(if con == <$ty as GScalar>::CON {
                    return <$ty as GScalar>::omega().map(ScalarV::$variant);
                })*
                Err(err(GrundyErrorKind::Type, "not a scalar type"))
            }

            /// Zero at a type.
            pub fn zero(con: TyCon) -> Option<ScalarV> {
                $(if con == <$ty as GScalar>::CON {
                    return Some(ScalarV::$variant(<$ty as Scalar>::zero()));
                })*
                None
            }
        }

        impl fmt::Display for ScalarV {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self {
                    $(ScalarV::$variant(x) => write!(f, "{x}"),)*
                }
            }
        }
    };
}

scalar_enum! {
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

/// A unary scalar operation, generic over the backend.
pub trait ScalarUnOp {
    /// Apply it.
    fn apply<S: GScalar>(&self, a: &S) -> GrundyResult<S>;
}

/// Negation.
pub struct NegOp;
impl ScalarUnOp for NegOp {
    fn apply<S: GScalar>(&self, a: &S) -> GrundyResult<S> {
        Ok(Scalar::neg(a))
    }
}

/// Reciprocal.
pub struct InvOp;
impl ScalarUnOp for InvOp {
    fn apply<S: GScalar>(&self, a: &S) -> GrundyResult<S> {
        a.inverse()
    }
}

/// Natural power.
pub struct PowOp(pub u128);
impl ScalarUnOp for PowOp {
    fn apply<S: GScalar>(&self, a: &S) -> GrundyResult<S> {
        a.power(self.0)
    }
}

/// A binary scalar operation, generic over the backend.
pub trait ScalarBinOp {
    /// Apply it.
    fn apply<S: GScalar>(&self, a: &S, b: &S) -> GrundyResult<S>;
}

/// `+`
pub struct AddOp;
impl ScalarBinOp for AddOp {
    fn apply<S: GScalar>(&self, a: &S, b: &S) -> GrundyResult<S> {
        Ok(a.add(b))
    }
}

/// `-`
pub struct SubOp;
impl ScalarBinOp for SubOp {
    fn apply<S: GScalar>(&self, a: &S, b: &S) -> GrundyResult<S> {
        Ok(a.sub(b))
    }
}

/// `⋅`
pub struct MulOp;
impl ScalarBinOp for MulOp {
    fn apply<S: GScalar>(&self, a: &S, b: &S) -> GrundyResult<S> {
        a.times(b)
    }
}

/// `/`
pub struct DivOp;
impl ScalarBinOp for DivOp {
    fn apply<S: GScalar>(&self, a: &S, b: &S) -> GrundyResult<S> {
        a.divide(b)
    }
}

/// `%`
pub struct RemOp;
impl ScalarBinOp for RemOp {
    fn apply<S: GScalar>(&self, a: &S, b: &S) -> GrundyResult<S> {
        a.remainder(b)
    }
}

impl ScalarV {
    /// Negation.
    pub fn neg(&self) -> ScalarV {
        self.map(NegOp).expect("negation is total")
    }

    /// Reciprocal.
    pub fn inverse(&self) -> GrundyResult<ScalarV> {
        self.map(InvOp)
    }

    /// Power by an Int exponent (negative exponents invert).
    pub fn power(&self, k: i128) -> GrundyResult<ScalarV> {
        let base = if k < 0 { self.inverse()? } else { self.clone() };
        base.map(PowOp(k.unsigned_abs()))
    }

    /// `ω↑s` (Surreal exponents only; the base must be exactly `ω`).
    pub fn omega_pow(&self, exponent: &ScalarV) -> GrundyResult<ScalarV> {
        match (self, exponent) {
            (ScalarV::Surreal(base), ScalarV::Surreal(exponent)) => {
                if *base != Surreal::omega() {
                    return Err(err(
                        GrundyErrorKind::Domain,
                        "a Surreal exponent needs the base `ω`",
                    )
                    .with_hint("exponents are Int, except `ω↑s` in Surreal"));
                }
                Ok(ScalarV::Surreal(Surreal::omega_pow(exponent.clone())))
            }
            _ => Err(err(GrundyErrorKind::Type, "`ω↑s` is a Surreal constructor")),
        }
    }

    /// A relation, given the type has `Ord`.
    pub fn relation(&self, op: RelOp, rhs: &ScalarV) -> bool {
        if self.antichain() {
            let equal = self == rhs;
            return match op {
                RelOp::Eq | RelOp::Le | RelOp::Ge => equal,
                RelOp::Lt | RelOp::Gt => false,
                RelOp::Fuzzy => !equal,
                RelOp::Equiv | RelOp::Outcome(_) => false,
            };
        }
        let ordering = self.compare(rhs);
        match op {
            RelOp::Eq => self == rhs,
            RelOp::Lt => ordering == Some(Ordering::Less),
            RelOp::Gt => ordering == Some(Ordering::Greater),
            RelOp::Le => matches!(ordering, Some(Ordering::Less | Ordering::Equal)),
            RelOp::Ge => matches!(ordering, Some(Ordering::Greater | Ordering::Equal)),
            RelOp::Fuzzy => ordering.is_none(),
            RelOp::Equiv | RelOp::Outcome(_) => false,
        }
    }

    /// The structural total order used for `Key` normalization.
    pub fn key_cmp(&self, rhs: &ScalarV) -> Ordering {
        self.con().cmp(&rhs.con()).then_with(|| {
            self.compare(rhs)
                .unwrap_or_else(|| self.to_string().cmp(&rhs.to_string()))
        })
    }
}

/// The Frobenius endomorphism of a finite field element.
pub fn frobenius(value: &ScalarV) -> GrundyResult<ScalarV> {
    Ok(match value {
        ScalarV::Nimber(x) => ScalarV::Nimber(x.frobenius()),
        ScalarV::F2(_) | ScalarV::F3(_) | ScalarV::F5(_) | ScalarV::F7(_) => value.clone(),
        ScalarV::F4(x) => ScalarV::F4(x.frobenius()),
        ScalarV::F8(x) => ScalarV::F8(x.frobenius()),
        ScalarV::F16(x) => ScalarV::F16(x.frobenius()),
        ScalarV::F9(x) => ScalarV::F9(x.frobenius()),
        ScalarV::F27(x) => ScalarV::F27(x.frobenius()),
        ScalarV::F25(x) => ScalarV::F25(x.frobenius()),
        _ => return Err(err(GrundyErrorKind::Type, "Frobenius needs a finite field")),
    })
}

/// The absolute trace of a finite field element down to its prime field.
pub fn trace(value: &ScalarV) -> GrundyResult<ScalarV> {
    Ok(match value {
        ScalarV::F2(_) | ScalarV::F3(_) | ScalarV::F5(_) | ScalarV::F7(_) => value.clone(),
        ScalarV::F4(x) => ScalarV::F4(x.relative_trace(1)),
        ScalarV::F8(x) => ScalarV::F8(x.relative_trace(1)),
        ScalarV::F16(x) => ScalarV::F16(x.relative_trace(1)),
        ScalarV::F9(x) => ScalarV::F9(x.relative_trace(1)),
        ScalarV::F27(x) => ScalarV::F27(x.relative_trace(1)),
        ScalarV::F25(x) => ScalarV::F25(x.relative_trace(1)),
        _ => return Err(err(GrundyErrorKind::Type, "the trace needs a finite field")),
    })
}
