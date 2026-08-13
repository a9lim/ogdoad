//! Capped-relative non-Archimedean local models.
//!
//!   * [`qp`] — `Q_p`, with signed valuation and `K` significant base-`p` digits.
//!   * [`zp`] — `Z_p`, the p-adic integers to precision `k` (= `Z/p^k`): the ring
//!     of integers model, an exact finite local ring.
//!   * [`qq`] — `Q_q = Frac(W_N(F_q))`, the **unramified extension** of `Q_p` of
//!     residue degree `F`, represented through truncated Witt vectors.
//!
//! [`analytic`] provides checked square tests, Hensel-lifted roots, and
//! Teichmüller representatives. `Qp` and `Qq` are precision models rather than
//! exact rings; cancellation may lose terms beyond the retained window.

pub mod analytic;
pub mod qp;
pub mod qq;
pub mod zp;

pub use qp::*;
pub use qq::*;
pub use zp::*;
