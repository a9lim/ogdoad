//! Crate-private linear algebra kernels shared by the math pillars.
//!
//! These routines are deliberately internal: they encode the row-reduction
//! conventions the public modules rely on, while keeping user-facing APIs in the
//! scalar, Clifford, forms, and games pillars.

pub(crate) mod f2;
pub(crate) mod field;
pub(crate) mod integer;
