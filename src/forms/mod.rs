//! Quadratic forms and their invariants.
//!
//! The primary organization follows the characteristic of the scalar field:
//!
//! * [`char0`] classifies real, complex, and rational forms on each backend's
//!   documented exact domain.
//! * [`oddchar`] classifies forms over supported finite fields of odd
//!   characteristic by dimension and discriminant.
//! * [`char2`] provides Arf, Brown, Dickson, and extraspecial-group invariants.
//!
//! [`classify`] dispatches to these implementations from the scalar type.
//! [`witt`] contains Clifford centers and Witt/Brauer--Wall classes, [`springer`]
//! contains valued-field residue decompositions, [`local_global`] contains
//! reciprocity and isotropy criteria, and [`integral`] contains lattices and
//! finite quadratic modules. [`symplectic`] and [`hermitian`] cover alternating
//! and Hermitian forms; [`trace_form`] constructs trace and transfer forms from
//! field extensions.
//!
//! Public items from each child module are re-exported here.
//!
//! # Examples
//!
//! One call, [`ClassifyForm::classify`], dispatches on the scalar field and
//! returns that characteristic's invariant: the signature (with Hasse data)
//! over `Q`, dimension and discriminant class over `F_7`, and the Arf invariant
//! of the full `(q, b)` metric over nimbers.
//!
//! ```
//! use ogdoad::clifford::Metric;
//! use ogdoad::forms::ClassifyForm;
//! use ogdoad::scalar::{Fp, Nimber, Rational, Scalar};
//!
//! // x^2 + y^2 - z^2 over Q has real signature (2, 1).
//! let q = Metric::diagonal([1, 1, -1].map(Rational::from_int).to_vec());
//! assert_eq!(Rational::classify(&q).unwrap().signature, (2, 1));
//!
//! // x^2 + 3y^2 over F_7: 3 is a nonsquare mod 7, so the discriminant class is nontrivial.
//! let f7 = Metric::diagonal([1, 3].map(Fp::<7>::from_int).to_vec());
//! let odd = Fp::<7>::classify(&f7).unwrap();
//! assert_eq!((odd.dim, odd.disc_is_square), (2, false));
//!
//! // x^2 + xy + y^2 over F_2 is the anisotropic plane: Arf invariant 1.
//! let plane = Metric::new(vec![Nimber(1), Nimber(1)], [((0, 1), Nimber(1))]);
//! let arf = Nimber::classify(&plane).unwrap();
//! assert_eq!((arf.arf, arf.rank, arf.radical_dim), (1, 2, 0));
//! ```

pub mod char0;
pub mod char2;
pub mod classify;
pub mod diagonalize;
pub mod equivalence;
pub mod field_invariants;
pub mod hermitian;
pub mod integral;
pub mod local_global;
pub mod oddchar;
pub mod quadric_fit;
pub mod springer;
pub mod symplectic;
pub mod trace_form;
pub mod witt;

pub use char0::*;
pub use char2::*;
pub use classify::*;
pub use diagonalize::*;
pub use equivalence::*;
pub use field_invariants::*;
pub use hermitian::*;
pub use integral::*;
pub use local_global::*;
pub use oddchar::*;
pub use quadric_fit::*;
pub use springer::*;
pub use symplectic::*;
pub use trace_form::*;
pub use witt::*;
