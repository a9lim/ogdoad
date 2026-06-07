//! The scalar interface every Clifford backend implements.
//!
//! A Clifford algebra needs a *commutative ring* of scalars. The whole point of
//! this project is that combinatorial games only supply such a ring on their
//! field-like subclasses — nimbers, surreals, surcomplex — so each of those is a
//! `Scalar` impl, and the multivector engine in `clifford/` is written once,
//! generic over this trait.
//!
//! This module is the trait; every coefficient world is a descendant module,
//! re-exported flat (`scalar::Nimber`, `scalar::Surreal`, …) so public paths stay
//! shallow regardless of how deep the family tree goes.
//!
//! # The "any number" table
//!
//! The backends are grouped by *place* — the kind of number — and almost every
//! field ships with its **ring of integers**, the same (field, ring) pattern four
//! times over:
//!
//! | place | field | ring of integers | residue |
//! |---|---|---|---|
//! | [`exact`]        — Archimedean | `Rational` ℚ    | `Integer` ℤ   | — |
//! | [`big`]          — transfinite | `Surreal` No    | `Omnific` Oz  | ≈ℝ |
//! | [`small`]        — p-adic      | `Qp` Q_p        | `Zp` Z_p      | F_p |
//! | [`finite_field`] — finite      | `Fpn` F_{p^n}   | `WittVec` W_n | F_q |
//! | [`finite_field`] — char-2 nim  | `Nimber` F_2¹²⁸ | (Witt / F₂)   | F₂ |
//!
//! Two backends sit *orthogonal* to the table:
//!   * [`Surcomplex`] is `Surcomplex<S>` — a generic *i-adjunction functor* over
//!     any backend, not a concrete world; it lives at the pillar root.
//!   * [`onag`](big::onag)'s ordinal nimbers are the **char-2 mirror of the
//!     surreals** — the transfinite "big" number in characteristic 2 — so they sit
//!     in [`big`] alongside `Surreal`/`Omnific`, not with the finite nim-field.
//!
//! The characteristic trichotomy that organises [`crate::forms`] cuts *across*
//! this table (char 0 in `exact`/`big`/`small`, char 2 in `nimber`/`onag`, odd and
//! even in `finite_field`); the two pillars are complementary views of the same
//! backends.

pub mod big;
pub mod exact;
pub mod finite_field;
pub mod small;
pub mod surcomplex;

pub use big::*;
pub use exact::*;
pub use finite_field::*;
pub use small::*;
pub use surcomplex::*;

use std::fmt::Debug;

pub trait Scalar: Clone + PartialEq + Debug {
    fn zero() -> Self;
    fn one() -> Self;
    fn add(&self, rhs: &Self) -> Self;
    fn neg(&self) -> Self;
    fn mul(&self, rhs: &Self) -> Self;

    /// Ring characteristic: 0 for characteristic-0 domains, a positive additive
    /// order of `1` for finite fields and finite quotient rings (`Z/p^k`,
    /// truncated Witt vectors, etc.). The engine itself gets signs from
    /// [`Scalar::neg`]; callers that care about characteristic must distinguish
    /// fields from local rings separately.
    fn characteristic() -> u128;

    /// Multiplicative inverse, or `None` if not invertible (zero) or not
    /// finitely representable in this backend (e.g. a non-monomial surreal,
    /// whose inverse is an infinite Hahn series).
    fn inv(&self) -> Option<Self>;

    fn is_zero(&self) -> bool {
        *self == Self::zero()
    }

    fn sub(&self, rhs: &Self) -> Self {
        self.add(&rhs.neg())
    }
}
