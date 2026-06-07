//! **Finite fields** — the residue worlds, where the field is finite. The whole
//! char trichotomy's finite leg, plus the unramified ring of integers that mirrors
//! `Z_p`:
//!
//!   * [`fp`] — `F_p`, the prime fields (odd characteristic): the residue field of
//!     `Z_p`, and the base of every extension here.
//!   * [`fpn`] — `F_{p^n}`, finite extension fields via a `(p,n)`-keyed reduction
//!     polynomial. Completes the odd-char tower *and* the char-2 odd-degree fields
//!     the nimbers cannot reach (`F_8`, `F_32`, …).
//!   * [`nimber`] — `On₂` truncated to `F_{2^128}`: the char-2 nim-field where
//!     `add = XOR` and `mul` is the coin-turning game product. The main char-2
//!     backend; the only finite field that is also a game-value field.
//!   * [`wittvec`] — `W_N(F_q)`, the truncated Witt vectors `(Z/p^N)[t]/(f̃)`: the
//!     unramified ring of integers over the residue field `F_q`. The char-p mirror
//!     of `Z_p` (which is `W(F_p)`) — completing the (field, ring of integers)
//!     pattern in positive characteristic.
//!
//! [`nimber`] and [`fpn`] share a finite-field analysis toolkit (Frobenius orbit,
//! degree, minimal polynomial, relative trace/norm, multiplicative order, discrete
//! log). That shared algorithm is the [`FiniteField`] trait below; the per-backend
//! impls supply only the Frobenius map, the field shape, and the group order.

pub mod fp;
pub mod fpn;
pub mod nimber;
pub mod wittvec;

pub use fp::*;
pub use fpn::*;
pub use nimber::*;
pub use wittvec::*;
