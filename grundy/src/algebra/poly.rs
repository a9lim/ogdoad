//! Polynomial rings `S[t]` and rational-function fields `S(t)` as types.

use std::cmp::Ordering;
use std::fmt;

use ogdoad::scalar::{Fp, HasRingOfIntegers, Integer, Poly, Rational, RationalFunction, Scalar};

use super::super::error::{err, GrundyErrorKind, GrundyResult};
use super::super::types::TyCon;
use super::scalar::{GScalar, ScalarV};

/// A polynomial over one coefficient backend.
#[derive(Clone, PartialEq)]
pub enum PolyV {
    /// `F2[t]`
    F2(Poly<Fp<2>>),
    /// `F3[t]`
    F3(Poly<Fp<3>>),
    /// `F5[t]`
    F5(Poly<Fp<5>>),
    /// `F7[t]`
    F7(Poly<Fp<7>>),
    /// `Int[t]`
    Int(Poly<Integer>),
}

/// A rational function over one prime field.
#[derive(Clone, PartialEq)]
pub enum RatFuncV {
    /// `F2(t)`
    F2(RationalFunction<Fp<2>>),
    /// `F3(t)`
    F3(RationalFunction<Fp<3>>),
    /// `F5(t)`
    F5(RationalFunction<Fp<5>>),
    /// `F7(t)`
    F7(RationalFunction<Fp<7>>),
}

macro_rules! poly_dispatch {
    ($value:expr, $p:ident => $body:expr) => {
        match $value {
            PolyV::F2($p) => $body,
            PolyV::F3($p) => $body,
            PolyV::F5($p) => $body,
            PolyV::F7($p) => $body,
            PolyV::Int($p) => $body,
        }
    };
}

macro_rules! poly_zip {
    ($a:expr, $b:expr, ($x:ident, $y:ident) => $body:expr) => {
        match ($a, $b) {
            (PolyV::F2($x), PolyV::F2($y)) => PolyV::F2($body),
            (PolyV::F3($x), PolyV::F3($y)) => PolyV::F3($body),
            (PolyV::F5($x), PolyV::F5($y)) => PolyV::F5($body),
            (PolyV::F7($x), PolyV::F7($y)) => PolyV::F7($body),
            (PolyV::Int($x), PolyV::Int($y)) => PolyV::Int($body),
            _ => unreachable!("polynomial rings differ"),
        }
    };
}

macro_rules! ratfunc_zip {
    ($a:expr, $b:expr, ($x:ident, $y:ident) => $body:expr) => {
        match ($a, $b) {
            (RatFuncV::F2($x), RatFuncV::F2($y)) => RatFuncV::F2($body),
            (RatFuncV::F3($x), RatFuncV::F3($y)) => RatFuncV::F3($body),
            (RatFuncV::F5($x), RatFuncV::F5($y)) => RatFuncV::F5($body),
            (RatFuncV::F7($x), RatFuncV::F7($y)) => RatFuncV::F7($body),
            _ => unreachable!("rational-function fields differ"),
        }
    };
}

fn division_by_zero() -> super::super::error::GrundyError {
    err(
        GrundyErrorKind::DivisionByZero,
        "polynomial division by zero",
    )
}

impl PolyV {
    /// The coefficient type.
    pub fn coefficient_con(&self) -> TyCon {
        match self {
            PolyV::F2(_) => TyCon::Fp(2),
            PolyV::F3(_) => TyCon::Fp(3),
            PolyV::F5(_) => TyCon::Fp(5),
            PolyV::F7(_) => TyCon::Fp(7),
            PolyV::Int(_) => TyCon::Int,
        }
    }

    /// The constant polynomial of a coefficient at a ring.
    pub fn constant(scalar: TyCon, n: u128) -> GrundyResult<PolyV> {
        Ok(match scalar {
            TyCon::Fp(2) => PolyV::F2(Poly::constant(Fp::<2>::int_literal(n)?)),
            TyCon::Fp(3) => PolyV::F3(Poly::constant(Fp::<3>::int_literal(n)?)),
            TyCon::Fp(5) => PolyV::F5(Poly::constant(Fp::<5>::int_literal(n)?)),
            TyCon::Fp(7) => PolyV::F7(Poly::constant(Fp::<7>::int_literal(n)?)),
            TyCon::Int => PolyV::Int(Poly::constant(Integer(
                i128::try_from(n)
                    .map_err(|_| err(GrundyErrorKind::Overflow, "literal exceeds i128"))?,
            ))),
            _ => {
                return Err(err(
                    GrundyErrorKind::Type,
                    "not a polynomial coefficient type",
                ))
            }
        })
    }

    /// A constant from a prime-field scalar.
    pub fn from_scalar(scalar: &ScalarV) -> GrundyResult<PolyV> {
        Ok(match scalar {
            ScalarV::F2(x) => PolyV::F2(Poly::constant(*x)),
            ScalarV::F3(x) => PolyV::F3(Poly::constant(*x)),
            ScalarV::F5(x) => PolyV::F5(Poly::constant(*x)),
            ScalarV::F7(x) => PolyV::F7(Poly::constant(*x)),
            _ => return Err(err(GrundyErrorKind::Type, "not a polynomial coefficient")),
        })
    }

    /// The indeterminate `t`.
    pub fn t(scalar: TyCon) -> GrundyResult<PolyV> {
        Ok(match scalar {
            TyCon::Fp(2) => PolyV::F2(Poly::t()),
            TyCon::Fp(3) => PolyV::F3(Poly::t()),
            TyCon::Fp(5) => PolyV::F5(Poly::t()),
            TyCon::Fp(7) => PolyV::F7(Poly::t()),
            TyCon::Int => PolyV::Int(Poly::t()),
            _ => {
                return Err(err(
                    GrundyErrorKind::Type,
                    "not a polynomial coefficient type",
                ))
            }
        })
    }

    /// `+`
    pub fn add(&self, rhs: &PolyV) -> PolyV {
        poly_zip!(self, rhs, (a, b) => a.add(b))
    }

    /// `-`
    pub fn sub(&self, rhs: &PolyV) -> PolyV {
        poly_zip!(self, rhs, (a, b) => a.sub(b))
    }

    /// Unary `-`.
    pub fn neg(&self) -> PolyV {
        match self {
            PolyV::F2(p) => PolyV::F2(p.neg()),
            PolyV::F3(p) => PolyV::F3(p.neg()),
            PolyV::F5(p) => PolyV::F5(p.neg()),
            PolyV::F7(p) => PolyV::F7(p.neg()),
            PolyV::Int(p) => PolyV::Int(p.neg()),
        }
    }

    /// `⋅`
    pub fn mul(&self, rhs: &PolyV) -> PolyV {
        poly_zip!(self, rhs, (a, b) => a.mul(b))
    }

    /// The unit of this polynomial's ring.
    pub fn one_like(&self) -> PolyV {
        match self {
            PolyV::F2(_) => PolyV::F2(Poly::one()),
            PolyV::F3(_) => PolyV::F3(Poly::one()),
            PolyV::F5(_) => PolyV::F5(Poly::one()),
            PolyV::F7(_) => PolyV::F7(Poly::one()),
            PolyV::Int(_) => PolyV::Int(Poly::one()),
        }
    }

    fn divrem(&self, rhs: &PolyV) -> GrundyResult<(PolyV, PolyV)> {
        if poly_dispatch!(rhs, p => p.is_zero()) {
            return Err(division_by_zero());
        }
        if let PolyV::Int(divisor) = rhs {
            if divisor.leading() != Some(&Integer(1)) {
                return Err(err(
                    GrundyErrorKind::Modulus,
                    "Int[t] divides only by monic polynomials",
                )
                .with_hint("`Int[t]` is not a field; make the divisor monic"));
            }
        }
        Ok(match (self, rhs) {
            (PolyV::F2(a), PolyV::F2(b)) => {
                let (q, r) = a.divrem(b);
                (PolyV::F2(q), PolyV::F2(r))
            }
            (PolyV::F3(a), PolyV::F3(b)) => {
                let (q, r) = a.divrem(b);
                (PolyV::F3(q), PolyV::F3(r))
            }
            (PolyV::F5(a), PolyV::F5(b)) => {
                let (q, r) = a.divrem(b);
                (PolyV::F5(q), PolyV::F5(r))
            }
            (PolyV::F7(a), PolyV::F7(b)) => {
                let (q, r) = a.divrem(b);
                (PolyV::F7(q), PolyV::F7(r))
            }
            (PolyV::Int(a), PolyV::Int(b)) => {
                let (q, r) = a.divrem(b);
                (PolyV::Int(q), PolyV::Int(r))
            }
            _ => unreachable!("polynomial rings differ"),
        })
    }

    /// Exact division.
    pub fn div(&self, rhs: &PolyV) -> GrundyResult<PolyV> {
        let (q, r) = self.divrem(rhs)?;
        if r.is_zero() {
            Ok(q)
        } else {
            Err(err(
                GrundyErrorKind::NotInvertible,
                format!("polynomial exact division failed with remainder {r}"),
            ))
        }
    }

    /// `%`
    pub fn rem(&self, rhs: &PolyV) -> GrundyResult<PolyV> {
        Ok(self.divrem(rhs)?.1)
    }

    /// The coefficient count, for work accounting.
    pub fn size(&self) -> u128 {
        poly_dispatch!(self, p => p.coeffs().len().max(1) as u128)
    }

    /// Whether the polynomial is zero.
    pub fn is_zero(&self) -> bool {
        poly_dispatch!(self, p => p.is_zero())
    }

    /// The degree (`E_Domain` for zero).
    pub fn degree(&self) -> GrundyResult<i128> {
        poly_dispatch!(self, p => p.degree())
            .map(|d| d as i128)
            .ok_or_else(|| err(GrundyErrorKind::Domain, "the zero polynomial has no degree"))
    }

    /// The coefficient of `t↑i`.
    pub fn coefficient(&self, i: usize) -> Coefficient {
        match self {
            PolyV::F2(p) => Coefficient::Scalar(ScalarV::F2(p.coeff(i))),
            PolyV::F3(p) => Coefficient::Scalar(ScalarV::F3(p.coeff(i))),
            PolyV::F5(p) => Coefficient::Scalar(ScalarV::F5(p.coeff(i))),
            PolyV::F7(p) => Coefficient::Scalar(ScalarV::F7(p.coeff(i))),
            PolyV::Int(p) => Coefficient::Int(p.coeff(i).0),
        }
    }

    /// Evaluate at a coefficient.
    pub fn eval(&self, at: &Coefficient) -> GrundyResult<Coefficient> {
        Ok(match (self, at) {
            (PolyV::F2(p), Coefficient::Scalar(ScalarV::F2(x))) => {
                Coefficient::Scalar(ScalarV::F2(p.eval(x)))
            }
            (PolyV::F3(p), Coefficient::Scalar(ScalarV::F3(x))) => {
                Coefficient::Scalar(ScalarV::F3(p.eval(x)))
            }
            (PolyV::F5(p), Coefficient::Scalar(ScalarV::F5(x))) => {
                Coefficient::Scalar(ScalarV::F5(p.eval(x)))
            }
            (PolyV::F7(p), Coefficient::Scalar(ScalarV::F7(x))) => {
                Coefficient::Scalar(ScalarV::F7(p.eval(x)))
            }
            (PolyV::Int(p), Coefficient::Int(x)) => {
                // Horner in checked i128.
                let mut acc: i128 = 0;
                for c in p.coeffs().iter().rev() {
                    acc = acc
                        .checked_mul(*x)
                        .and_then(|v| v.checked_add(c.0))
                        .ok_or_else(|| {
                            err(GrundyErrorKind::Overflow, "evaluation overflows i128")
                        })?;
                }
                Coefficient::Int(acc)
            }
            _ => unreachable!("evaluation point type checked"),
        })
    }

    /// Compose `self(inner)`.
    pub fn compose(&self, inner: &PolyV) -> PolyV {
        poly_zip!(self, inner, (a, b) => a.compose(b))
    }

    /// The greatest common divisor: monic over fields, positive primitive
    /// over `Int[t]`.
    pub fn gcd(&self, rhs: &PolyV) -> GrundyResult<PolyV> {
        Ok(match (self, rhs) {
            (PolyV::Int(a), PolyV::Int(b)) => PolyV::Int(integer_gcd(a, b)?),
            _ => poly_zip!(self, rhs, (a, b) => a.gcd(b)),
        })
    }

    /// The structural order.
    pub fn key_cmp(&self, other: &PolyV) -> Ordering {
        self.to_string().cmp(&other.to_string())
    }
}

/// A polynomial coefficient: a prime-field scalar or an Int.
pub enum Coefficient {
    /// A prime-field element.
    Scalar(ScalarV),
    /// An integer.
    Int(i128),
}

fn integer_gcd(a: &Poly<Integer>, b: &Poly<Integer>) -> GrundyResult<Poly<Integer>> {
    let to_q =
        |p: &Poly<Integer>| Poly::new(p.coeffs().iter().map(|c| Rational::from_int(c.0)).collect());
    let g: Poly<Rational> = to_q(a).gcd(&to_q(b));
    if g.is_zero() {
        return Ok(Poly::zero());
    }
    let overflow = || {
        err(
            GrundyErrorKind::Overflow,
            "Int[t] gcd coefficient exceeds i128",
        )
    };
    let mut scale: i128 = 1;
    for c in g.coeffs() {
        let d = c.denom();
        let common = gcd_i128(scale, d);
        scale = scale
            .checked_div(common)
            .and_then(|s| s.checked_mul(d))
            .ok_or_else(overflow)?;
    }
    let mut coeffs: Vec<i128> = Vec::new();
    for c in g.coeffs() {
        coeffs.push(
            c.numer()
                .checked_mul(scale / c.denom())
                .ok_or_else(overflow)?,
        );
    }
    let content = coeffs.iter().fold(0, |acc, c| gcd_i128(acc, *c));
    if content > 1 {
        coeffs.iter_mut().for_each(|c| *c /= content);
    }
    if coeffs.last().is_some_and(|c| *c < 0) {
        for c in &mut coeffs {
            *c = c.checked_neg().ok_or_else(overflow)?;
        }
    }
    Ok(Poly::new(coeffs.into_iter().map(Integer).collect()))
}

fn gcd_i128(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a as i128
}

impl fmt::Display for PolyV {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        poly_dispatch!(self, p => write!(f, "{p}"))
    }
}

impl RatFuncV {
    /// The coefficient type.
    pub fn coefficient_con(&self) -> TyCon {
        match self {
            RatFuncV::F2(_) => TyCon::Fp(2),
            RatFuncV::F3(_) => TyCon::Fp(3),
            RatFuncV::F5(_) => TyCon::Fp(5),
            RatFuncV::F7(_) => TyCon::Fp(7),
        }
    }

    /// The constant at a field from an integer literal.
    pub fn constant(scalar: TyCon, n: u128) -> GrundyResult<RatFuncV> {
        Ok(match scalar {
            TyCon::Fp(2) => RatFuncV::F2(RationalFunction::from_base(Fp::<2>::int_literal(n)?)),
            TyCon::Fp(3) => RatFuncV::F3(RationalFunction::from_base(Fp::<3>::int_literal(n)?)),
            TyCon::Fp(5) => RatFuncV::F5(RationalFunction::from_base(Fp::<5>::int_literal(n)?)),
            TyCon::Fp(7) => RatFuncV::F7(RationalFunction::from_base(Fp::<7>::int_literal(n)?)),
            _ => return Err(err(GrundyErrorKind::Type, "not a rational-function field")),
        })
    }

    /// The indeterminate `t`.
    pub fn t(scalar: TyCon) -> GrundyResult<RatFuncV> {
        Ok(match scalar {
            TyCon::Fp(2) => RatFuncV::F2(RationalFunction::t()),
            TyCon::Fp(3) => RatFuncV::F3(RationalFunction::t()),
            TyCon::Fp(5) => RatFuncV::F5(RationalFunction::t()),
            TyCon::Fp(7) => RatFuncV::F7(RationalFunction::t()),
            _ => return Err(err(GrundyErrorKind::Type, "not a rational-function field")),
        })
    }

    /// `+`
    pub fn add(&self, rhs: &RatFuncV) -> RatFuncV {
        ratfunc_zip!(self, rhs, (a, b) => Scalar::add(a, b))
    }

    /// `-`
    pub fn sub(&self, rhs: &RatFuncV) -> RatFuncV {
        ratfunc_zip!(self, rhs, (a, b) => Scalar::sub(a, b))
    }

    /// `⋅`
    pub fn mul(&self, rhs: &RatFuncV) -> RatFuncV {
        ratfunc_zip!(self, rhs, (a, b) => Scalar::mul(a, b))
    }

    /// Unary `-`.
    pub fn neg(&self) -> RatFuncV {
        match self {
            RatFuncV::F2(x) => RatFuncV::F2(Scalar::neg(x)),
            RatFuncV::F3(x) => RatFuncV::F3(Scalar::neg(x)),
            RatFuncV::F5(x) => RatFuncV::F5(Scalar::neg(x)),
            RatFuncV::F7(x) => RatFuncV::F7(Scalar::neg(x)),
        }
    }

    /// Reciprocal.
    pub fn inverse(&self) -> GrundyResult<RatFuncV> {
        let zero = err(GrundyErrorKind::DivisionByZero, "division by zero");
        Ok(match self {
            RatFuncV::F2(x) => RatFuncV::F2(x.inv().ok_or(zero)?),
            RatFuncV::F3(x) => RatFuncV::F3(x.inv().ok_or(zero)?),
            RatFuncV::F5(x) => RatFuncV::F5(x.inv().ok_or(zero)?),
            RatFuncV::F7(x) => RatFuncV::F7(x.inv().ok_or(zero)?),
        })
    }

    /// `/`
    pub fn div(&self, rhs: &RatFuncV) -> GrundyResult<RatFuncV> {
        Ok(self.mul(&rhs.inverse()?))
    }

    /// The unit of this rational function's field.
    pub fn one_like(&self) -> RatFuncV {
        match self {
            RatFuncV::F2(_) => RatFuncV::F2(Scalar::one()),
            RatFuncV::F3(_) => RatFuncV::F3(Scalar::one()),
            RatFuncV::F5(_) => RatFuncV::F5(Scalar::one()),
            RatFuncV::F7(_) => RatFuncV::F7(Scalar::one()),
        }
    }

    /// Evaluate at a field element (`E_DivisionByZero` at a pole).
    pub fn eval(&self, at: &ScalarV) -> GrundyResult<ScalarV> {
        let pole = || err(GrundyErrorKind::DivisionByZero, "the point is a pole");
        macro_rules! at {
            ($f:expr, $x:expr, $variant:ident) => {{
                let den = $f.den().eval($x);
                if den.is_zero() {
                    return Err(pole());
                }
                ScalarV::$variant($f.num().eval($x).mul(&den.inv().expect("nonzero")))
            }};
        }
        Ok(match (self, at) {
            (RatFuncV::F2(f), ScalarV::F2(x)) => at!(f, x, F2),
            (RatFuncV::F3(f), ScalarV::F3(x)) => at!(f, x, F3),
            (RatFuncV::F5(f), ScalarV::F5(x)) => at!(f, x, F5),
            (RatFuncV::F7(f), ScalarV::F7(x)) => at!(f, x, F7),
            _ => unreachable!("evaluation point type checked"),
        })
    }

    /// Compose `self(inner)`.
    pub fn compose(&self, inner: &RatFuncV) -> GrundyResult<RatFuncV> {
        macro_rules! compose {
            ($f:expr, $g:expr, $variant:ident) => {{
                let substitute = |p: &Poly<_>| {
                    p.coeffs().iter().rev().fold(
                        RationalFunction::from_base(Scalar::zero()),
                        |acc: RationalFunction<_>, c| {
                            Scalar::add(&Scalar::mul(&acc, $g), &RationalFunction::from_base(*c))
                        },
                    )
                };
                let num = substitute($f.num());
                let den = substitute($f.den());
                let inv = den.inv().ok_or_else(|| {
                    err(
                        GrundyErrorKind::DivisionByZero,
                        "the composition has a zero denominator",
                    )
                })?;
                RatFuncV::$variant(Scalar::mul(&num, &inv))
            }};
        }
        Ok(match (self, inner) {
            (RatFuncV::F2(f), RatFuncV::F2(g)) => compose!(f, g, F2),
            (RatFuncV::F3(f), RatFuncV::F3(g)) => compose!(f, g, F3),
            (RatFuncV::F5(f), RatFuncV::F5(g)) => compose!(f, g, F5),
            (RatFuncV::F7(f), RatFuncV::F7(g)) => compose!(f, g, F7),
            _ => unreachable!("fields differ"),
        })
    }

    /// The numerator and denominator sizes, for work accounting.
    pub fn size(&self) -> u128 {
        match self {
            RatFuncV::F2(x) => (x.num().coeffs().len() + x.den().coeffs().len()) as u128,
            RatFuncV::F3(x) => (x.num().coeffs().len() + x.den().coeffs().len()) as u128,
            RatFuncV::F5(x) => (x.num().coeffs().len() + x.den().coeffs().len()) as u128,
            RatFuncV::F7(x) => (x.num().coeffs().len() + x.den().coeffs().len()) as u128,
        }
    }

    /// Whether the rational function lies in `F_p[t]`.
    pub fn integral(&self) -> bool {
        match self {
            RatFuncV::F2(x) => HasRingOfIntegers::is_integral(x),
            RatFuncV::F3(x) => HasRingOfIntegers::is_integral(x),
            RatFuncV::F5(x) => HasRingOfIntegers::is_integral(x),
            RatFuncV::F7(x) => HasRingOfIntegers::is_integral(x),
        }
    }

    /// The structural order.
    pub fn key_cmp(&self, other: &RatFuncV) -> Ordering {
        self.to_string().cmp(&other.to_string())
    }
}

impl fmt::Display for RatFuncV {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RatFuncV::F2(x) => write!(f, "{x}"),
            RatFuncV::F3(x) => write!(f, "{x}"),
            RatFuncV::F5(x) => write!(f, "{x}"),
            RatFuncV::F7(x) => write!(f, "{x}"),
        }
    }
}
