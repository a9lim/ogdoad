//! **Small** — the non-Archimedean (p-adic) local world, where the number is
//! allowed to be infinitely *close*. The p-adic mirror of `exact/`, and the
//! `Omnific ⊂ Surreal` relation reflected through a finite prime:
//!
//!   * [`qp`] — `Q_p`, the p-adic field (capped-relative precision model). The
//!     "small" mirror of [`Rational`](crate::scalar::Rational): char 0, `inv`
//!     total on nonzero, `1/p` exists. The empty cell the round-out pass filled.
//!   * [`zp`] — `Z_p`, the p-adic integers to precision `k` (= `Z/p^k`): the ring
//!     of integers of `Q_p`, a *local ring* (`p` is a non-unit). The "small"
//!     mirror of [`Integer`](crate::scalar::Integer) / [`Omnific`](crate::scalar::Omnific).
//!
//! `(Q_p, Z_p)` is the third instance of the (field, ring of integers) pattern;
//! `Z_p`'s residue field is `F_p`, linking this place to `finite_field/`.

pub mod qp;
pub mod zp;

pub use qp::*;
pub use zp::*;
