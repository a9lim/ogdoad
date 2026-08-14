//! Quadratic forms and their invariants.
//!
//! The primary organization follows the characteristic of the scalar field:
//!
//! * [`char0`] classifies real, complex, and rational forms on each backend's
//!   documented exact domain.
//! * [`oddchar`] classifies forms over supported finite fields of odd
//!   characteristic by dimension and discriminant.
//! * [`char2`] provides Arf, Brown, Dickson, and extraspecial-group invariants.
//!
//! [`classify`] dispatches to these implementations from the scalar type.
//! [`witt`] contains Witt and Brauer--Wall classes, [`springer`] contains valued-
//! field residue decompositions, [`local_global`] contains reciprocity and
//! isotropy criteria, and [`integral`] contains lattices and finite quadratic
//! modules. [`symplectic`] and [`hermitian`] cover alternating and Hermitian forms;
//! [`trace_form`] constructs trace and transfer forms from field extensions.
//!
//! Public items from each child module are re-exported here.

pub mod char0;
pub mod char2;
pub mod classify;
pub mod diagonalize;
pub mod equivalence;
pub mod field_invariants;
pub mod hermitian;
pub mod integral;
pub mod local_global;
pub mod oddchar;
pub mod quadric_fit;
pub mod springer;
pub mod symplectic;
pub mod trace_form;
pub mod witt;

pub use char0::*;
pub use char2::*;
pub use classify::*;
pub use diagonalize::*;
pub use equivalence::*;
pub use field_invariants::*;
pub use hermitian::*;
pub use integral::*;
pub use local_global::*;
pub use oddchar::*;
pub use quadric_fit::*;
pub use springer::*;
pub use symplectic::*;
pub use trace_form::*;
pub use witt::*;
