//! Local-global quadratic-form machinery.
//!
//! The scalar pillar names the local and global coefficient worlds. This
//! submodule keeps the corresponding form-theoretic local-global layer together:
//! Hilbert symbols and Hasse-Minkowski over `Q`, the adelic rational facade, and
//! the odd- and characteristic-2 function-field mirrors. Children stay private
//! behind the flat re-export, like every other shelf; the parent `forms` module
//! re-exports the public items flat.

mod adelic;
mod function_field;
// `pub(crate)`: `springer/char2/` imports this engine's crate-private helpers
// through the module path (the coupling documented in the pillar AGENTS.md).
pub(crate) mod function_field_char2;
mod global_field;
mod padic;

pub use adelic::*;
pub use function_field::*;
pub use function_field_char2::*;
pub use global_field::*;
pub use padic::*;
