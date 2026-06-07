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
//!   * [`qq`] — `Q_q = Frac(W_N(F_q))`, the **unramified extension** of `Q_p` of
//!     residue degree `F`: the field of fractions of the Witt vectors. It is to
//!     [`WittVec`](crate::scalar::WittVec) what `Q_p` is to `Z_p`, and `Q_q` for
//!     `F = 1` is `Q_p`. Completes the (field, ring of integers) pairing on the
//!     unramified leg.
//!
//! `(Q_p, Z_p)` is the third instance of the (field, ring of integers) pattern;
//! `Z_p`'s residue field is `F_p`, linking this place to `finite_field/`. The
//! unramified `(Q_q, W_N(F_q))` is its residue-degree-`F` lift, with residue field
//! `F_q` — the ring of integers `WittVec` living over in `finite_field/`.

pub mod qp;
pub mod qq;
pub mod zp;

pub use qp::*;
pub use qq::*;
pub use zp::*;
