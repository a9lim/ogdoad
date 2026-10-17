//! Witnesses, claims, and bounded answers (filled in by the claims stage).

use super::super::builtins::Builtin;
use super::super::error::{err, GrundyErrorKind, GrundyResult};
use super::super::eval::interp::Interp;
use super::super::eval::value::Value;

/// Evidence data awaiting verification.
pub struct WitnessV;
/// A verified claim.
pub struct ClaimV;
/// A bounded answer.
pub struct BoundedV;
/// A sampled misère quotient.
pub struct QuotientV;

/// Evidence builtins.
pub fn call(_interp: &mut Interp<'_>, builtin: Builtin, _args: Vec<Value>) -> GrundyResult<Value> {
    Err(err(
        GrundyErrorKind::Domain,
        format!("internal: `{}` is not implemented yet", builtin.name()),
    ))
}
