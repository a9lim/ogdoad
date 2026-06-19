//! Heating, Berlekamp overheating, and Norton multiplication for short games.
//!
//! These are game-valued operators, complementary to
//! [`thermography`](crate::games::thermography), which computes stops and
//! thermographs.  They are standard CGT infrastructure: heating is the recursive
//! inverse of cooling by a number, Norton multiplication extends multiplication
//! by a positive "unit" game through incentives, and Berlekamp overheating
//! `int_s^t G` uses Norton multiplication on integer leaves and shifts hot
//! options by `t`.
//!
//! Boundary: this module deliberately does **not** assert that overheating gives
//! the temperature filtration an associated-graded product. That remains the
//! `under` open problem.

use crate::games::Game;
use crate::scalar::{Rational, Surreal};

/// True iff `g > 0` in the short-game order.
pub fn is_positive_game(g: &Game) -> bool {
    let zero = Game::zero();
    zero.le(g) && !g.le(&zero)
}

/// The exact integer value of a short game, if it is an integer-valued number.
pub fn integer_game_value(g: &Game) -> Option<i128> {
    let q = g.number_value()?.as_rational()?;
    q.is_integer().then_some(q.numer())
}

/// Heat a game by a dyadic rational temperature.
///
/// Numbers are fixed; non-number options are recursively shifted as
/// `{ heat(G^L,t) + t | heat(G^R,t) - t }`.  Returns `None` when `t` is not
/// dyadic, because arbitrary rationals are not short games.
pub fn heat(g: &Game, t: &Rational) -> Option<Game> {
    let shift = Game::from_surreal(&Surreal::from_rational(t.clone()))?;
    Some(heat_by_game(g, &shift))
}

/// Norton multiplication `G.U` by a positive unit game `U`.
///
/// Returns `None` when `unit` is not strictly positive. Integer leaves use the
/// literal repeated-sum definition; non-integers recurse through the incentives
/// of `unit`.
pub fn norton_multiply(g: &Game, unit: &Game) -> Option<Game> {
    if !is_positive_game(unit) {
        return None;
    }
    Some(norton_multiply_unchecked(g, unit))
}

/// Berlekamp overheating `int_s^t G`.
///
/// The lower unit `s` must be positive. Integer leaves become `G.s` via Norton
/// multiplication; non-integers recurse as `{ overheat(G^L)+t | overheat(G^R)-t }`.
pub fn overheat(g: &Game, s: &Game, t: &Game) -> Option<Game> {
    if !is_positive_game(s) {
        return None;
    }
    Some(overheat_unchecked(g, s, t))
}

fn heat_by_game(g: &Game, shift: &Game) -> Game {
    let g = g.canonical();
    if g.is_number() {
        return g;
    }
    let neg_shift = shift.neg();
    let left = g
        .left()
        .iter()
        .map(|gl| heat_by_game(gl, shift).add(shift))
        .collect();
    let right = g
        .right()
        .iter()
        .map(|gr| heat_by_game(gr, shift).add(&neg_shift))
        .collect();
    Game::new(left, right).canonical()
}

fn norton_multiply_unchecked(g: &Game, unit: &Game) -> Game {
    let g = g.canonical();
    if let Some(n) = integer_game_value(&g) {
        return if n >= 0 {
            unit.times_int(n)
        } else {
            unit.neg().times_int(-n)
        }
        .canonical();
    }

    let increments = norton_increments(unit);
    let mut left = Vec::new();
    for gl in g.left() {
        let gl_u = norton_multiply_unchecked(gl, unit);
        for inc in &increments {
            left.push(gl_u.add(inc));
        }
    }

    let mut right = Vec::new();
    for gr in g.right() {
        let gr_u = norton_multiply_unchecked(gr, unit);
        for inc in &increments {
            right.push(gr_u.add(&inc.neg()));
        }
    }

    Game::new(left, right).canonical()
}

fn norton_increments(unit: &Game) -> Vec<Game> {
    let unit = unit.canonical();
    let mut out = Vec::new();
    for u in unit.left() {
        out.push(u.clone()); // U + (u - U)
    }
    for u in unit.right() {
        out.push(unit.add(&unit.add(&u.neg())).canonical()); // U + (U - u)
    }
    out
}

fn overheat_unchecked(g: &Game, s: &Game, t: &Game) -> Game {
    let g = g.canonical();
    if integer_game_value(&g).is_some() {
        return norton_multiply_unchecked(&g, s);
    }
    let neg_t = t.neg();
    let left = g
        .left()
        .iter()
        .map(|gl| overheat_unchecked(gl, s, t).add(t))
        .collect();
    let right = g
        .right()
        .iter()
        .map(|gr| overheat_unchecked(gr, s, t).add(&neg_t))
        .collect();
    Game::new(left, right).canonical()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::games::atomic_weight_int;
    use crate::games::piecewise::req;
    use crate::games::thermography::{mean_value, temperature};

    fn int(n: i128) -> Rational {
        Rational::from(n)
    }

    fn assert_value_eq(a: &Game, b: &Game) {
        assert!(a.eq(b), "{} != {}", a.display(), b.display());
        assert!(a.canonical().structural_eq(&b.canonical()));
    }

    #[test]
    fn heating_fixes_numbers_and_increases_switch_temperature() {
        let two = int(2);
        assert_value_eq(&heat(&Game::integer(5), &two).unwrap(), &Game::integer(5));

        let heated = heat(&Game::switch(1, -1), &two).unwrap();
        assert_value_eq(&heated, &Game::switch(3, -3));
        assert!(req(&mean_value(&heated).unwrap(), &int(0)));
        assert!(req(&temperature(&heated).unwrap(), &int(3)));
    }

    #[test]
    fn heating_rejects_non_dyadic_temperatures() {
        assert!(heat(&Game::switch(1, -1), &Rational::new(1, 3)).is_none());
    }

    #[test]
    fn norton_unit_one_is_identity_and_rejects_nonpositive_units() {
        let g = Game::switch(3, -1);
        assert_value_eq(&norton_multiply(&g, &Game::integer(1)).unwrap(), &g);
        assert!(norton_multiply(&g, &Game::zero()).is_none());
        assert!(norton_multiply(&g, &Game::integer(-1)).is_none());
    }

    #[test]
    fn norton_multiplication_has_product_mean_for_integer_unit() {
        let g = Game::switch(3, -1); // mean 1
        let product = norton_multiply(&g, &Game::integer(2)).unwrap();
        assert_value_eq(&product, &Game::switch(7, -3));
        assert!(req(&mean_value(&product).unwrap(), &int(2)));
    }

    #[test]
    fn berlekamp_overheating_uses_lower_unit_on_integer_leaves() {
        let g = Game::switch(1, -1);
        let hot = overheat(&g, &Game::integer(1), &Game::integer(2)).unwrap();
        assert_value_eq(&hot, &Game::switch(3, -3));
        assert!(req(&temperature(&hot).unwrap(), &int(3)));
    }

    #[test]
    fn positive_unit_can_be_hot() {
        let unit = Game::up();
        assert!(is_positive_game(&unit));
        let doubled = norton_multiply(&Game::integer(2), &unit).unwrap();
        assert_value_eq(&doubled, &unit.add(&unit));
        assert_eq!(
            integer_game_value(&Game::new(vec![Game::integer(0)], vec![Game::integer(1)])),
            None
        );
    }

    #[test]
    fn hot_units_do_not_descend_mod_cold_numbers() {
        // In the tau=0 associated-graded candidate, G and G+1 differ by a cold
        // number. Multiplication by the positive infinitesimal unit ↑ sees that
        // hidden integer leaf, so the output difference remains leading-temp 0.
        let g = Game::star();
        let h = g.add(&Game::integer(1));
        assert!(req(&temperature(&g.add(&h.neg())).unwrap(), &int(-1)));

        let unit = Game::up();
        let p = norton_multiply(&g, &unit).unwrap();
        let q = norton_multiply(&h, &unit).unwrap();
        let delta = p.add(&q.neg());
        assert!(req(&temperature(&p).unwrap(), &int(0)));
        assert!(req(&temperature(&q).unwrap(), &int(0)));
        assert!(req(&temperature(&delta).unwrap(), &int(0)));
        assert_eq!(atomic_weight_int(&delta), Some(-1));

        let p = overheat(&g, &unit, &Game::zero()).unwrap();
        let q = overheat(&h, &unit, &Game::zero()).unwrap();
        let delta = p.add(&q.neg());
        assert!(req(&temperature(&p).unwrap(), &int(0)));
        assert!(req(&temperature(&q).unwrap(), &int(0)));
        assert!(req(&temperature(&delta).unwrap(), &int(0)));
        assert_eq!(atomic_weight_int(&delta), Some(-2));
    }
}
