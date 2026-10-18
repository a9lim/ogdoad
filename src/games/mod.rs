//! Combinatorial games and checked bridges to arithmetic and integral forms.
//!
//! [`grundy`](mod@grundy), [`kernel`], [`coin_turning`], [`octal`], and
//! [`misere`] cover finite impartial play. [`partizan`], [`number_game`], and [`nimber_game`]
//! provide short-game and represented transfinite value models; [`loopy`]
//! handles finite cyclic graphs separately. [`thermography`], [`heating`], and
//! [`tropical_thermography`] provide temperature-theoretic operations.
//! [`hackenbush`], [`lexicode`](mod@lexicode), [`witt_fifo`],
//! [`brown_selector`], and [`game_exterior`] are explicit cross-pillar
//! constructions.
//!
//! A [`Game`] is an acyclic short-game tree and supports only its additive
//! group operations. Cyclic play belongs in [`loopy`], and no API treats an
//! arbitrary partizan game as a Clifford scalar.
//!
//! # Examples
//!
//! Canonical forms and Sprague--Grundy values describe the same sums: `{0|0}`
//! is the star `*`, which cancels itself under disjunctive sum, and a Nim
//! position has the XOR of its heap sizes as its Grundy value.
//!
//! ```
//! use ogdoad::games::{grundy, nim_moves, Game, PartizanOutcome};
//! use std::collections::HashMap;
//!
//! // * = {0|0} is fuzzy with 0, and * + * = 0 in the game group.
//! let star = Game::star();
//! assert_eq!(star.to_string(), "{0|0}");
//! assert_eq!(star.outcome_class(), PartizanOutcome::N);
//! assert_eq!(star.add(&star).canonical().to_string(), "0");
//!
//! // up = {0|*} is a positive infinitesimal: up + * is fuzzy, up + up + * is positive.
//! let up = Game::up();
//! assert_eq!(up.add(&star).outcome_class(), PartizanOutcome::N);
//! assert_eq!(up.add(&up).add(&star).outcome_class(), PartizanOutcome::L);
//!
//! // Sprague--Grundy: Nim heaps 1, 2, 3 have value 1 ^ 2 ^ 3 = 0, heaps 3, 5 have 3 ^ 5 = 6.
//! let mut memo = HashMap::new();
//! assert_eq!(grundy(&vec![1, 2, 3], &nim_moves, &mut memo), 0);
//! assert_eq!(grundy(&vec![3, 5], &nim_moves, &mut memo), 6);
//! ```

pub mod arena;
pub mod atomic_weight;
pub mod brown_selector;
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
pub mod octal;
pub mod partizan;
pub mod piecewise;
pub mod thermography;
pub mod tropical_thermography;
pub mod witt_fifo;

pub use arena::{ArenaError, GameArena, GameId};
pub use atomic_weight::*;
pub use brown_selector::*;
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
pub use octal::{GuySmithCertificate, GuySmithError, GuySmithWitness, OctalCode, OctalCodeError};
pub use partizan::*;
pub use piecewise::*;
pub use thermography::*;
pub use tropical_thermography::*;
pub use witt_fifo::*;
