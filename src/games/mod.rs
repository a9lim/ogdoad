//! Combinatorial games and checked bridges to arithmetic and integral forms.
//!
//! [`grundy`](mod@grundy), [`kernel`], [`coin_turning`], and [`misere`] cover
//! finite impartial play. [`partizan`], [`number_game`], and [`nimber_game`]
//! provide short-game and represented transfinite value models; [`loopy`]
//! handles finite cyclic graphs separately. [`thermography`], [`heating`], and
//! [`tropical_thermography`] provide temperature-theoretic operations.
//! [`hackenbush`], [`lexicode`](mod@lexicode), and [`game_exterior`] are explicit
//! cross-pillar constructions.
//!
//! A [`Game`] is an acyclic short-game tree and supports only its additive
//! group operations. Cyclic play belongs in [`loopy`], and no API treats an
//! arbitrary partizan game as a Clifford scalar.

pub mod atomic_weight;
pub mod coin_turning;
pub mod game_exterior;
pub mod grundy;
pub mod hackenbush;
pub mod heating;
pub mod kernel;
pub mod lexicode;
pub mod loopy;
pub mod misere;
pub mod nimber_game;
pub mod number_game;
pub mod partizan;
pub mod piecewise;
pub mod thermography;
pub mod tropical_thermography;

pub use atomic_weight::*;
pub use coin_turning::*;
pub use game_exterior::*;
pub use grundy::*;
pub use hackenbush::*;
pub use heating::*;
pub use kernel::*;
pub use lexicode::*;
pub use loopy::*;
pub use misere::*;
pub use nimber_game::*;
pub use number_game::*;
pub use partizan::*;
pub use piecewise::*;
pub use thermography::*;
pub use tropical_thermography::*;
