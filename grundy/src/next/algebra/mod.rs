//! Algebraic worlds as types: scalars, polynomials, rational functions, and
//! Clifford algebras.

pub mod scalar;

pub use scalar::ScalarV;

use std::cmp::Ordering;

/// A polynomial value (filled in by the algebra stage).
#[derive(Clone)]
pub enum PolyV {}

/// A rational-function value (filled in by the algebra stage).
#[derive(Clone)]
pub enum RatFuncV {}

/// A Clifford algebra value (filled in by the algebra stage).
#[derive(Clone)]
pub enum AlgebraV {}

/// A multivector value (filled in by the algebra stage).
#[derive(Clone)]
pub enum MvV {}

impl PolyV {
    /// The structural order.
    pub fn key_cmp(&self, _other: &PolyV) -> Ordering {
        match *self {}
    }
}

impl RatFuncV {
    /// The structural order.
    pub fn key_cmp(&self, _other: &RatFuncV) -> Ordering {
        match *self {}
    }
}

impl MvV {
    /// The structural order.
    pub fn key_cmp(&self, _other: &MvV) -> Ordering {
        match *self {}
    }
}

use super::error::{err, GrundyErrorKind, GrundyResult};
use super::eval::value::Value;
use super::syntax::ast::{BinaryOp, RelOp, StarIndex, UnaryOp};
use super::types::Ty;

fn not_yet(what: &str) -> super::error::GrundyError {
    err(
        GrundyErrorKind::Domain,
        format!("internal: {what} is not available for this type"),
    )
}

/// Evaluate or compose a polynomial or rational function.
pub fn substitute(_callee: &Value, _arg: &Value) -> GrundyResult<Value> {
    Err(not_yet("substitution"))
}

/// The named generator of a type (`t` or `x`).
pub fn generator(_ty: &Ty) -> GrundyResult<Value> {
    Err(not_yet("a generator"))
}

/// An integer literal at an algebra type.
pub fn int_literal(_ty: &Ty, _n: u128) -> GrundyResult<Value> {
    Err(not_yet("an integer literal"))
}

/// A fraction literal at an algebra type.
pub fn frac_literal(_ty: &Ty, _num: i128, _den: u128) -> GrundyResult<Value> {
    Err(not_yet("a fraction literal"))
}

/// A star literal at an algebra type.
pub fn star_literal(_ty: &Ty, _index: &StarIndex) -> GrundyResult<Value> {
    Err(not_yet("a star literal"))
}

/// A unary operator on algebra values.
pub fn unary(_op: UnaryOp, _value: &Value) -> GrundyResult<Value> {
    Err(not_yet("this operator"))
}

/// A binary operator on algebra values.
pub fn binary(_op: BinaryOp, _lhs: &Value, _rhs: &Value) -> GrundyResult<Value> {
    Err(not_yet("this operator"))
}

/// A relation on algebra values.
pub fn relation(_op: RelOp, _lhs: &Value, _rhs: &Value) -> GrundyResult<bool> {
    Err(not_yet("this relation"))
}
