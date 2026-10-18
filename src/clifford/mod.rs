//! The Clifford / geometric-algebra pillar.
//!
//! Two layers, deliberately separated:
//!
//!   * [`engine`] — the associative-algebra core: the `Metric` (carrying the
//!     quadratic form `q`, polar form `b`, and possibly nonzero asymmetric
//!     contraction `a` independently), the `Multivector` /
//!     `CliffordAlgebra` types, and the geometric product itself. This is the
//!     "associative algebra from a general bilinear form" primitive.
//!   * [`versor`] — the geometry built on top: versors and the Pin sandwich
//!     action, reflections, contractions, the pseudoscalar dual, grade
//!     involution, the spinor norm, and the even subalgebra.
//!
//! On top of those sit the structured-algebra modules: [`outermorphism`]
//! (lift a linear map to all grades; determinant via the pseudoscalar),
//! [`hopf`] (the exterior Hopf algebra) with its char-faithful symmetric mirror
//! [`divided_power`] (the divided power algebra `Γ`, dual to `Sym`),
//! [`cga`] (conformal & projective GA), and [`spinor`] (concrete left-ideal /
//! left-regular spinor modules).
//!
//! Public types and free functions are re-exported from this module. Inherent
//! operations remain methods on their context types, such as
//! `alg.sandwich(…)` and `cga.up(…)`.
//!
//! # Examples
//!
//! The quaternions are the Clifford algebra of a negative-definite plane over
//! the rationals: `i = e₀`, `j = e₁`, `k = e₀e₁`.
//!
//! ```
//! use ogdoad::clifford::{CliffordAlgebra, Metric};
//! use ogdoad::scalar::{Rational, Scalar};
//!
//! let r = Rational::from_int;
//! let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![r(-1), r(-1)]));
//! let (i, j) = (alg.e(0), alg.e(1));
//! let k = alg.mul(&i, &j);
//! let minus_one = alg.scalar(r(-1));
//! assert_eq!(alg.mul(&i, &i), minus_one);
//! assert_eq!(alg.mul(&j, &j), minus_one);
//! assert_eq!(alg.mul(&k, &k), minus_one);
//! assert_eq!(alg.mul(&alg.mul(&i, &j), &k), minus_one); // ijk = -1
//! ```
//!
//! In characteristic two the squares `q` and the polar form `b` are
//! independent data. Here `e₀² = *2`, `e₁² = *3` and `e₀e₁ + e₁e₀ = *1`, so the
//! generators do not commute, and `(e₀ + e₁)² = q₀ + q₁ + b₀₁ = *0`.
//!
//! ```
//! use ogdoad::clifford::{CliffordAlgebra, Metric};
//! use ogdoad::scalar::Nimber;
//!
//! let metric = Metric::new(vec![Nimber(2), Nimber(3)], [((0, 1), Nimber(1))]);
//! let alg = CliffordAlgebra::new(2, metric);
//! let (e0, e1) = (alg.e(0), alg.e(1));
//! assert_eq!(alg.mul(&e0, &e0), alg.scalar(Nimber(2)));
//! assert_eq!(alg.anticommutator(&e0, &e1), alg.scalar(Nimber(1)));
//! assert_ne!(alg.mul(&e0, &e1), alg.mul(&e1, &e0));
//! let v = alg.add(&e0, &e1);
//! assert!(alg.mul(&v, &v).is_zero());
//! ```

pub mod blade;
pub mod cga;
pub mod divided_power;
pub mod engine;
pub mod frobenius;
pub mod hopf;
pub mod outermorphism;
pub mod spinor;
pub mod spinor_norm;
pub mod versor;

pub use blade::*;
pub use cga::*;
pub use divided_power::*;
pub use engine::*;
pub use frobenius::*;
pub use hopf::*;
pub use outermorphism::*;
pub use spinor::*;
pub use spinor_norm::*;
// `versor` adds only inherent methods to `CliffordAlgebra` (reachable through
// the type itself), so there is nothing to glob-re-export from it.
