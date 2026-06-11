//! Characteristic-2 quadratic-form invariants.
//!
//! Characteristic 2 has two different but adjacent invariants:
//!
//! * `arf` classifies the quadratic form / Clifford algebra through the Arf
//!   invariant.
//! * `dickson` classifies orthogonal transformations by the Dickson invariant,
//!   the determinant replacement in characteristic 2.
//! * `brown` lifts the `ℤ/2` Arf bit to the `ℤ/8` Brown invariant of a
//!   `ℤ/4`-valued quadratic refinement — the char-2 cell of the mod-8 spine
//!   (Bridge M), with `β(2q′) = 4·Arf(q′)`.
//!
//! plus `field`, the [`FiniteChar2Field`] capability trait — the additive
//! (Artin–Schreier) mirror of [`FiniteOddField`](crate::forms::FiniteOddField)
//! that the char-2 local–global layer is generic over.
//!
//! The public exports stay flat (`forms::arf_invariant`,
//! `forms::dickson_matrix`, `forms::FiniteChar2Field`, …), matching the rest of the
//! forms pillar.

mod arf;
mod brown;
mod dickson;
mod field;

pub use arf::*;
pub(crate) use arf::{
    arf_nimber_at_degree, min_field_degree, nimber_metric_max_val, ordinal_to_nimber_metric,
};
pub(crate) use brown::beta_from_gauss;
pub use brown::*;
pub use dickson::*;
pub use field::*;
