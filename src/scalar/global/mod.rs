//! Global-field and represented local--global scalar models.
//!
//! [`Adele`] is a finite-diagonal, capped-relative model of rational adeles. It
//! is not the full analytic restricted product: finite components are eventually
//! equal to one diagonal rational, and the Archimedean component is rational.
//!
//! Two types:
//!   * [`LocalQp`] — a **runtime-prime** `p`-adic cell (the const-generic `Qp<P,K>`
//!     can't sit in a prime-indexed map, so the adele needs this).
//!   * [`Adele`] — the represented [`Scalar`](crate::scalar::Scalar), with a
//!     diagonal `ℚ` embedding and represented idele/product-formula operations.
//!
//! The local–global *theorems* it carries (Hilbert reciprocity, adelic
//! Hasse–Minkowski, the Brauer fundamental exact sequence) live one layer up in
//! [`forms::adelic`](crate::forms), where the `forms::padic` Hilbert-symbol
//! machinery is.
//!
//! [`RationalFunction`] is the exact global function field `F_q(t)`. It has one
//! valuation per place rather than a distinguished [`Valued`](crate::scalar::Valued)
//! structure; [`forms::function_field`](crate::forms) supplies the place-specific
//! arithmetic.

pub mod adele;
pub mod function_field;
pub mod local_qp;

pub use adele::*;
pub use function_field::*;
pub use local_qp::*;
