//! **The global place** — the adele ring `A_Q`, the one scalar world that lives at
//! *every* place of `ℚ` at once.
//!
//! The rest of the "any number" table is organized *by place*: [`exact`] is the
//! Archimedean place `ℝ`, [`small`] is one prime place `Q_p` at a time. The adele
//! ring is modeled as the **restricted product** `∏'_v Q_v` over all of them
//! simultaneously. In this repo it is a finite-precision scalar model for the
//! local–global passage, not a complete exact implementation of the analytic
//! adele ring.
//!
//! Two types:
//!   * [`LocalQp`] — a **runtime-prime** `p`-adic cell (the const-generic `Qp<P,K>`
//!     can't sit in a prime-indexed map, so the adele needs this).
//!   * [`Adele`] — the restricted-product [`Scalar`](crate::scalar::Scalar), with
//!     the diagonal embedding `ℚ ↪ A_Q`, the idele group, and the product formula.
//!
//! The local–global *theorems* it carries (Hilbert reciprocity, adelic
//! Hasse–Minkowski, the Brauer fundamental exact sequence) live one layer up in
//! [`forms::adelic`](crate::forms::adelic), where the `forms::padic` Hilbert-symbol
//! machinery is.
//!
//! [`exact`]: crate::scalar::exact
//! [`small`]: crate::scalar::small

pub mod adele;
pub mod local_qp;

pub use adele::*;
pub use local_qp::*;
