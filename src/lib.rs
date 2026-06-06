//! pleroma — Clifford algebras (with nilpotents) over the field-like
//! subclasses of combinatorial games.
//!
//! Pure-Rust math core (generic over the `Scalar` trait), with optional PyO3
//! bindings behind the `python` feature (abi3).
//!   - `scalar`    : the Scalar trait + an exact Rational for engine validation
//!   - `nimber`    : On_2 (characteristic 2) — exact nim-add/mul/inv, the novel backend
//!   - `surreal`   : Conway normal form scalars with recursive exponents (char 0)
//!   - `surcomplex`: adjoin i over any backend
//!   - `omnific`   : the omnific integers Oz — the surreal integers, a transfinite ring
//!   - `onag`      : transfinite (ordinal) nimbers — On₂ closure; nim-add full, nim-mul staged
//!   - `clifford`  : the multivector engine + versor/GA layer, generic over Scalar
//!   - `outermorphism`: lift a grade-1 linear map to all grades; determinant via I
//!   - `hopf`      : the exterior Hopf algebra — coproduct, counit, antipode
//!   - `cga`       : conformal & projective GA (surreal ∞/ε radii; exact nilpotent motors)
//!   - `arf`       : the Arf invariant (the char-2 Clifford classifier)
//!   - `classify`  : the char-0 Clifford classifier (Cl(p,q) → matrix algebra)
//!   - `fp`        : prime fields F_p (odd characteristic) — the trichotomy's third leg
//!   - `disc`      : odd-char classifier (discriminant + Hasse) — the third invariant
//!   - `games`     : nim-mult as Turning-Corners; general coin-turning + Tartan products
//!   - `kernel`    : normal-play outcomes of any finite game graph (Win/Loss/Draw)
//!   - `misere`    : misère-play outcomes — where disjunctive sums go non-linear
//!   - `spinor`    : concrete minimal left ideals (spinor modules) + generator matrices
//!   - `springer`  : non-Archimedean Springer/valuation decomposition over the surreals
//!   - `witt`      : the Witt group of quadratic forms over a nim-field (ℤ/2)
//!   - `partizan`  : short partizan games + the exterior algebra of the game group
//!   - `py`        : PyO3 per-backend bindings (feature = "python")
//!
//! See `NOTES.md` for the mathematical thread.

pub mod arf;
pub mod cga;
pub mod classify;
pub mod clifford;
pub mod disc;
pub mod fp;
pub mod games;
pub mod hopf;
pub mod kernel;
pub mod misere;
pub mod nimber;
pub mod omnific;
pub mod onag;
pub mod outermorphism;
pub mod partizan;
pub mod scalar;
pub mod spinor;
pub mod springer;
pub mod surcomplex;
pub mod surreal;
pub mod witt;

#[cfg(feature = "python")]
mod py;
