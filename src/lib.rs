//! pleroma — Clifford algebras (with nilpotents) over the field-like
//! subclasses of combinatorial games.
//!
//! Pure-Rust math core (generic over the `Scalar` trait), with optional PyO3
//! bindings behind the `python` feature (abi3). The source is organised into
//! four pillars plus the bindings:
//!
//!   - [`scalar`]   — the coefficient worlds: the `Scalar` trait, exact
//!                    `Rational`/`Integer`, game-adjacent nimber/surreal
//!                    backends, finite fields, p-adic/local functors, and the
//!                    adelic precision model.
//!   - [`clifford`] — the multivector engine (Metric + general bilinear form +
//!                    geometric product), generic over `Scalar`, plus the GA
//!                    layer: outermorphisms, the exterior Hopf algebra,
//!                    conformal/projective GA, and spinor modules.
//!   - [`forms`]    — quadratic forms and their invariants across the
//!                    characteristic trichotomy: char-0 / odd-char / char-2
//!                    classifiers, Witt/Brauer-Wall utilities, Springer
//!                    decompositions, and rational local-global helpers.
//!   - [`games`]    — combinatorial game theory: coin-turning & Tartan
//!                    products, normal-, misère-, and loopy finite-game probes,
//!                    plus short partizan games and the exterior algebra of the
//!                    game group.
//!   - `py`         — PyO3 per-backend bindings (feature = "python").
//!
//! See `NOTES.md` for the mathematical thread and `AGENTS.md` for the layout.

pub mod clifford;
pub mod forms;
pub mod games;
pub(crate) mod linalg;
pub mod scalar;

#[cfg(feature = "python")]
mod py;
