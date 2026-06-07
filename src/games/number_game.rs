//! Transfinite number-valued games carried by their surreal value.

use crate::games::Game;
use crate::scalar::{Ordinal, Scalar, Surreal};
use std::cmp::Ordering;

/// A transfinite **number-valued** game, carried by its surreal value rather than
/// a (necessarily infinite) option tree. Numbers are the one transfinite class
/// needing no materialized options: value, birthday, and the group/order
/// operations all come from [`Surreal`]. The finite [`Game`] engine is untouched
/// — `NumberGame` is a parallel *view*, not a `Game`, the numbers-only honoring
/// of "games of transfinite birthday" (`ω = {0,1,2,...|}` is a number).
#[derive(Clone, Debug, PartialEq)]
pub struct NumberGame {
    value: Surreal,
}

impl NumberGame {
    /// The number-game of a surreal value (always succeeds — no options built).
    pub fn from_surreal(s: &Surreal) -> NumberGame {
        NumberGame { value: s.clone() }
    }

    /// The exact surreal value.
    pub fn value(&self) -> &Surreal {
        &self.value
    }

    /// The birthday as an [`Ordinal`], via [`Surreal::birthday_ordinal`]. `None`
    /// when the value is outside the representable sign-expansion subclass (e.g.
    /// `sqrt(omega)`).
    pub fn birthday(&self) -> Option<Ordinal> {
        self.value.birthday_ordinal()
    }

    /// Negation (additive inverse) — surreal negation.
    pub fn neg(&self) -> NumberGame {
        NumberGame {
            value: self.value.neg(),
        }
    }

    /// Disjunctive sum: for numbers this is exactly surreal addition (no options
    /// materialized).
    pub fn add(&self, other: &NumberGame) -> NumberGame {
        NumberGame {
            value: self.value.add(&other.value),
        }
    }

    /// The game order = the surreal order on values.
    pub fn cmp(&self, other: &NumberGame) -> Ordering {
        self.value.cmp(&other.value)
    }

    /// Bridge to the finite engine: `Some(short Game)` iff the value is dyadic;
    /// `None` for genuinely transfinite numbers (`omega`, `epsilon`, ...), which
    /// have no finite option tree. On dyadics this agrees with
    /// [`Game::from_surreal`]/[`Game::number_value`].
    pub fn to_finite_game(&self) -> Option<Game> {
        Game::from_surreal(&self.value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{Rational, Surreal};

    #[test]
    fn transfinite_bridge() {
        let w = Surreal::omega();
        let ng = NumberGame::from_surreal(&w);
        assert_eq!(ng.value(), &w);
        assert_eq!(ng.birthday(), Some(Ordinal::omega()));
        assert!(ng.to_finite_game().is_none());

        let one = NumberGame::from_surreal(&Surreal::from_int(1));
        assert_eq!(ng.add(&one).value(), &w.add(&Surreal::from_int(1)));
        assert_eq!(
            ng.cmp(&NumberGame::from_surreal(&Surreal::from_int(1_000_000))),
            Ordering::Greater
        );
        assert_eq!(ng.neg().value(), &w.neg());

        let d = Surreal::from_rational(Rational::new(3, 4));
        let ngd = NumberGame::from_surreal(&d);
        let fin = Game::from_surreal(&d).unwrap();
        assert_eq!(ngd.birthday().unwrap().as_finite(), Some(fin.birthday()));
        assert!(ngd.to_finite_game().is_some());
    }
}
