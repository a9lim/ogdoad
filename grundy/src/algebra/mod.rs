//! Algebraic worlds as types: scalars, polynomials, rational functions, and
//! Clifford algebras.

pub mod clifford;
pub mod poly;
pub mod scalar;

pub use clifford::{AlgebraV, MvV};
pub use poly::{PolyV, RatFuncV};
pub use scalar::ScalarV;

use ogdoad::scalar::{nim_trace, FiniteField, Fpn, Nimber};

use super::builtins::Builtin;
use super::error::{err, GrundyErrorKind, GrundyResult};
use super::eval::interp::Interp;
use super::eval::value::Value;
use super::syntax::ast::{BinaryOp, RelOp, StarIndex, UnaryOp};
use super::types::{Ty, TyCon};
use clifford::{MvOp, MvUnary};
use poly::Coefficient;
use scalar::DivOp;

fn internal(what: &str) -> super::error::GrundyError {
    err(GrundyErrorKind::Domain, format!("internal: {what}"))
}

fn scalar_con(ty: &Ty) -> Option<TyCon> {
    match ty {
        Ty::Con(_, args) => match args.first() {
            Some(Ty::Con(con, _)) => Some(*con),
            _ => None,
        },
        _ => None,
    }
}

fn coefficient_value(c: Coefficient) -> Value {
    match c {
        Coefficient::Scalar(s) => Value::Scalar(s),
        Coefficient::Int(n) => Value::Int(n),
    }
}

/// Evaluate or compose a polynomial or rational function.
pub fn substitute(callee: &Value, arg: &Value) -> GrundyResult<Value> {
    match (callee, arg) {
        (Value::Poly(p), Value::Poly(q)) => Ok(Value::Poly(p.compose(q))),
        (Value::Poly(p), Value::Scalar(s)) => {
            Ok(coefficient_value(p.eval(&Coefficient::Scalar(s.clone()))?))
        }
        (Value::Poly(p), Value::Int(n)) => Ok(coefficient_value(p.eval(&Coefficient::Int(*n))?)),
        (Value::RatFunc(f), Value::RatFunc(g)) => Ok(Value::RatFunc(f.compose(g)?)),
        (Value::RatFunc(f), Value::Scalar(s)) => Ok(Value::Scalar(f.eval(s)?)),
        _ => Err(internal("substitution of these values")),
    }
}

/// The named generator of a type: `t` for `S[t]` and `S(t)`, `x` for the
/// extension fields.
pub fn generator(ty: &Ty) -> GrundyResult<Value> {
    match ty {
        Ty::Con(TyCon::Poly, _) => Ok(Value::Poly(PolyV::t(
            scalar_con(ty).ok_or_else(|| internal("ring"))?,
        )?)),
        Ty::Con(TyCon::RatFunc, _) => Ok(Value::RatFunc(RatFuncV::t(
            scalar_con(ty).ok_or_else(|| internal("field"))?,
        )?)),
        Ty::Con(TyCon::Fpn(p, n), _) => Ok(Value::Scalar(match (p, n) {
            (2, 2) => ScalarV::F4(Fpn::<2, 2>::generator()),
            (2, 3) => ScalarV::F8(Fpn::<2, 3>::generator()),
            (2, 4) => ScalarV::F16(Fpn::<2, 4>::generator()),
            (3, 2) => ScalarV::F9(Fpn::<3, 2>::generator()),
            (3, 3) => ScalarV::F27(Fpn::<3, 3>::generator()),
            (5, 2) => ScalarV::F25(Fpn::<5, 2>::generator()),
            _ => return Err(internal("extension field")),
        })),
        _ => Err(internal("a generator for this type")),
    }
}

/// An integer literal at an algebra type.
pub fn int_literal(ty: &Ty, n: u128) -> GrundyResult<Value> {
    match ty {
        Ty::Con(TyCon::Poly, _) => Ok(Value::Poly(PolyV::constant(
            scalar_con(ty).ok_or_else(|| internal("ring"))?,
            n,
        )?)),
        Ty::Con(TyCon::RatFunc, _) => Ok(Value::RatFunc(RatFuncV::constant(
            scalar_con(ty).ok_or_else(|| internal("field"))?,
            n,
        )?)),
        Ty::Con(TyCon::Mv, args) => {
            let coefficient = match &args[0] {
                Ty::Con(TyCon::Int, _) => Value::Int(
                    i128::try_from(n)
                        .map_err(|_| err(GrundyErrorKind::Overflow, "literal exceeds i128"))?,
                ),
                Ty::Con(con, _) => Value::Scalar(ScalarV::int_literal(*con, n)?),
                _ => return Err(internal("unresolved coefficient type")),
            };
            mv_scalar(&coefficient)
        }
        _ => Err(internal("an integer literal at this type")),
    }
}

fn mv_scalar(coefficient: &Value) -> GrundyResult<Value> {
    MvV::from_scalar(coefficient)
        .map(Value::Mv)
        .ok_or_else(|| err(GrundyErrorKind::Type, "not a Clifford coefficient type"))
}

/// A fraction literal at an algebra type.
pub fn frac_literal(ty: &Ty, num: i128, den: u128) -> GrundyResult<Value> {
    let fraction = |con: TyCon| -> GrundyResult<ScalarV> {
        let magnitude = ScalarV::int_literal(con, num.unsigned_abs())?;
        let magnitude = if num < 0 { magnitude.neg() } else { magnitude };
        magnitude.zip(&ScalarV::int_literal(con, den)?, DivOp)
    };
    match ty {
        Ty::Con(TyCon::Poly, _) => Ok(Value::Poly(PolyV::from_scalar(&fraction(
            scalar_con(ty).ok_or_else(|| internal("ring"))?,
        )?)?)),
        Ty::Con(TyCon::RatFunc, _) => {
            let con = scalar_con(ty).ok_or_else(|| internal("field"))?;
            let numerator = RatFuncV::constant(con, num.unsigned_abs())?;
            let numerator = if num < 0 { numerator.neg() } else { numerator };
            Ok(Value::RatFunc(
                numerator.div(&RatFuncV::constant(con, den)?)?,
            ))
        }
        Ty::Con(TyCon::Mv, _) => {
            let con = scalar_con(ty).ok_or_else(|| internal("coefficient"))?;
            mv_scalar(&Value::Scalar(fraction(con)?))
        }
        _ => Err(internal("a fraction literal at this type")),
    }
}

/// A star literal at an algebra type.
pub fn star_literal(ty: &Ty, index: &StarIndex) -> GrundyResult<Value> {
    match ty {
        Ty::Con(TyCon::Mv, _) => {
            let con = scalar_con(ty).ok_or_else(|| internal("coefficient"))?;
            mv_scalar(&Value::Scalar(ScalarV::star_literal(con, index)?))
        }
        _ => Err(internal("a star literal at this type")),
    }
}

/// A unary operator on algebra values.
pub fn unary(op: UnaryOp, value: &Value) -> GrundyResult<Value> {
    match (op, value) {
        (UnaryOp::Neg, Value::Poly(p)) => Ok(Value::Poly(p.neg())),
        (UnaryOp::Neg, Value::RatFunc(f)) => Ok(Value::RatFunc(f.neg())),
        (UnaryOp::Recip, Value::RatFunc(f)) => Ok(Value::RatFunc(f.inverse()?)),
        (UnaryOp::Recip, Value::Poly(p)) => {
            Ok(Value::Poly(PolyV::constant(poly_con(p), 1)?.div(p)?))
        }
        (UnaryOp::Neg, Value::Mv(v)) => Ok(Value::Mv(v.map(MvUnary::Neg)?)),
        (UnaryOp::Recip, Value::Mv(v)) => Ok(Value::Mv(v.map(MvUnary::Inverse)?)),
        _ => Err(internal("this unary operator")),
    }
}

fn poly_con(p: &PolyV) -> TyCon {
    match p {
        PolyV::F2(_) => TyCon::Fp(2),
        PolyV::F3(_) => TyCon::Fp(3),
        PolyV::F5(_) => TyCon::Fp(5),
        PolyV::F7(_) => TyCon::Fp(7),
        PolyV::Int(_) => TyCon::Int,
    }
}

/// A binary operator on algebra values.
pub fn binary(op: BinaryOp, lhs: &Value, rhs: &Value) -> GrundyResult<Value> {
    match (op, lhs, rhs) {
        (BinaryOp::Add, Value::Poly(a), Value::Poly(b)) => Ok(Value::Poly(a.add(b))),
        (BinaryOp::Sub, Value::Poly(a), Value::Poly(b)) => Ok(Value::Poly(a.sub(b))),
        (BinaryOp::Mul, Value::Poly(a), Value::Poly(b)) => Ok(Value::Poly(a.mul(b))),
        (BinaryOp::Div, Value::Poly(a), Value::Poly(b)) => Ok(Value::Poly(a.div(b)?)),
        (BinaryOp::Rem, Value::Poly(a), Value::Poly(b)) => Ok(Value::Poly(a.rem(b)?)),
        (BinaryOp::Add, Value::RatFunc(a), Value::RatFunc(b)) => Ok(Value::RatFunc(a.add(b))),
        (BinaryOp::Sub, Value::RatFunc(a), Value::RatFunc(b)) => Ok(Value::RatFunc(a.sub(b))),
        (BinaryOp::Mul, Value::RatFunc(a), Value::RatFunc(b)) => Ok(Value::RatFunc(a.mul(b))),
        (BinaryOp::Div, Value::RatFunc(a), Value::RatFunc(b)) => Ok(Value::RatFunc(a.div(b)?)),
        (BinaryOp::Add, Value::Mv(a), Value::Mv(b)) => Ok(Value::Mv(a.zip(b, MvOp::Add)?)),
        (BinaryOp::Sub, Value::Mv(a), Value::Mv(b)) => Ok(Value::Mv(a.zip(b, MvOp::Sub)?)),
        (BinaryOp::Mul, Value::Mv(a), Value::Mv(b)) => Ok(Value::Mv(a.zip(b, MvOp::Mul)?)),
        (BinaryOp::Div, Value::Mv(a), Value::Mv(b)) => Ok(Value::Mv(a.zip(b, MvOp::Div)?)),
        (BinaryOp::Wedge, Value::Mv(a), Value::Mv(b)) => Ok(Value::Mv(a.zip(b, MvOp::Wedge)?)),
        _ => Err(internal("this binary operator")),
    }
}

/// A relation on algebra values (only `=`; these types have no order).
pub fn relation(op: RelOp, lhs: &Value, rhs: &Value) -> GrundyResult<bool> {
    match (op, lhs, rhs) {
        (RelOp::Eq, Value::Poly(a), Value::Poly(b)) => Ok(a == b),
        (RelOp::Eq, Value::RatFunc(a), Value::RatFunc(b)) => Ok(a == b),
        (RelOp::Eq, Value::Mv(a), Value::Mv(b)) => Ok(a.equals(b)),
        _ => Err(internal("this relation")),
    }
}

fn mv_of(value: &Value) -> &MvV {
    match value {
        Value::Mv(v) => v,
        other => panic!("expected a multivector, found {}", other.kind_name()),
    }
}

fn algebra_of(value: &Value) -> &AlgebraV {
    match value {
        Value::Algebra(a) => a,
        other => panic!("expected an algebra, found {}", other.kind_name()),
    }
}

fn poly_of(value: &Value) -> &PolyV {
    match value {
        Value::Poly(p) => p,
        other => panic!("expected a polynomial, found {}", other.kind_name()),
    }
}

fn metric_pairs(value: &Value) -> GrundyResult<Vec<((usize, usize), Value)>> {
    value
        .as_list()
        .iter()
        .map(|entry| {
            let Value::Tuple(parts) = entry else {
                unreachable!("typed pair")
            };
            let Value::Tuple(ij) = &parts[0] else {
                unreachable!("typed index pair")
            };
            let index = |v: &Value| {
                usize::try_from(v.as_int())
                    .map_err(|_| err(GrundyErrorKind::BladeIndex, "metric indices are natural"))
            };
            Ok(((index(&ij[0])?, index(&ij[1])?), parts[1].clone()))
        })
        .collect()
}

fn coefficient_con(ty: &Ty) -> GrundyResult<TyCon> {
    match ty {
        Ty::Con(con, _) => Ok(*con),
        _ => Err(internal("an unresolved coefficient type")),
    }
}

/// Algebra builtins.
pub fn call(
    interp: &mut Interp<'_>,
    builtin: Builtin,
    tys: &[Ty],
    args: Vec<Value>,
) -> GrundyResult<Value> {
    let _ = interp;
    use Builtin as B;
    match builtin {
        B::Deg => Ok(Value::Int(poly_of(&args[0]).degree()?)),
        B::Coef => {
            let i = usize::try_from(args[1].as_int())
                .map_err(|_| err(GrundyErrorKind::Domain, "coefficient indices are natural"))?;
            Ok(coefficient_value(poly_of(&args[0]).coefficient(i)))
        }
        B::Gcd => Ok(Value::Poly(poly_of(&args[0]).gcd(poly_of(&args[1]))?)),
        B::Integral => Ok(Value::Bool(match &args[0] {
            Value::Scalar(ScalarV::Surreal(s)) => ogdoad::scalar::HasRingOfIntegers::is_integral(s),
            Value::RatFunc(f) => f.integral(),
            Value::Int(_) | Value::Scalar(ScalarV::Omnific(_)) | Value::Poly(_) => true,
            other => return Err(internal(&format!("integral of a {}", other.kind_name()))),
        })),
        B::Frob => match &args[0] {
            Value::Scalar(ScalarV::Nimber(x)) => Ok(Value::Scalar(ScalarV::Nimber(x.frobenius()))),
            Value::Scalar(s) => Ok(Value::Scalar(scalar::frobenius(s)?)),
            other => Err(internal(&format!("frob of a {}", other.kind_name()))),
        },
        B::Tr => match &args[0] {
            Value::Scalar(ScalarV::Nimber(_)) => Err(err(
                GrundyErrorKind::Domain,
                "a nimber trace names its subfield",
            )
            .with_hint("`nimtr(x, m)` traces F_{2^128} to F_{2^m}")),
            Value::Scalar(s) => Ok(Value::Scalar(scalar::trace(s)?)),
            other => Err(internal(&format!("tr of a {}", other.kind_name()))),
        },
        B::NimTr => {
            let Value::Scalar(ScalarV::Nimber(x)) = &args[0] else {
                unreachable!("typed Nimber")
            };
            let m = args[1].as_int();
            if m <= 0 {
                return Err(err(
                    GrundyErrorKind::Domain,
                    "the nimber trace degree is positive",
                ));
            }
            Ok(Value::Scalar(ScalarV::Nimber(Nimber(nim_trace(
                x.0, m as u128,
            )))))
        }
        B::Clifford => {
            let con = coefficient_con(&tys[0])?;
            Ok(Value::Algebra(AlgebraV::build(
                con,
                args[0].as_list(),
                &[],
                &[],
            )?))
        }
        B::CliffordMetric => {
            let con = coefficient_con(&tys[0])?;
            Ok(Value::Algebra(AlgebraV::build(
                con,
                args[0].as_list(),
                &metric_pairs(&args[1])?,
                &metric_pairs(&args[2])?,
            )?))
        }
        B::Grassmann => {
            let con = coefficient_con(&tys[0])?;
            let dim = usize::try_from(args[0].as_int())
                .ok()
                .filter(|d| *d <= 128)
                .ok_or_else(|| {
                    err(
                        GrundyErrorKind::DimMismatch,
                        "Clifford dimension is 0 to 128",
                    )
                })?;
            Ok(Value::Algebra(AlgebraV::grassmann(con, dim)?))
        }
        B::Basis => Ok(Value::list(
            algebra_of(&args[0])
                .basis()
                .into_iter()
                .map(Value::Mv)
                .collect(),
        )),
        B::Vector => Ok(Value::Mv(algebra_of(&args[0]).vector(args[1].as_list())?)),
        B::Dim => Ok(Value::Int(algebra_of(&args[0]).dim() as i128)),
        B::Rev => Ok(Value::Mv(mv_of(&args[0]).map(MvUnary::Rev)?)),
        B::Even => Ok(Value::Mv(mv_of(&args[0]).map(MvUnary::Even)?)),
        B::Dual => Ok(Value::Mv(mv_of(&args[0]).map(MvUnary::Dual)?)),
        B::Grade => Ok(Value::Mv(
            mv_of(&args[0]).map(MvUnary::Grade(args[1].as_int()))?,
        )),
        B::Component => mv_of(&args[0]).component(args[1].as_int()),
        B::ScalarPart => Ok(mv_of(&args[0]).scalar_part()),
        _ => unreachable!("not an algebra builtin"),
    }
}
