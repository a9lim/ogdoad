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
//! [`numeric_norton_regrade`] and [`numeric_norton_mean_temperature`] compute the
//! exact affine thermographic regrading for a positive numeric unit without
//! materializing the Norton product. Nonnumeric units do not satisfy this rule.
//!
//! They do **not** form a multiplicative scalar action.  The exact obstruction is
//! [`numeric_norton_composition_defect`]: composing the `u` and `v` transports
//! differs in degree from the `uv` transport by a nonnegative dyadic defect.

use crate::games::partizan::integer_value;
use crate::games::Game;
use crate::scalar::{Rational, Scalar, Surreal};
use std::cmp::Ordering;
use std::collections::HashMap;

/// True iff `g > 0` in the short-game order.
pub fn is_positive_game(g: &Game) -> bool {
    let zero = Game::zero();
    zero.le(g) && !g.le(&zero)
}

/// The exact integer value of a short game, if it is an integer-valued number.
pub fn integer_game_value(g: &Game) -> Option<i128> {
    integer_value(g)
}

/// The affine temperature regrading `(scale, shift)` for a positive numeric
/// Norton unit.
///
/// Every short-game number is dyadic.  Write the positive unit as
/// `u = m / 2^k` in lowest terms, put `delta = 2^-k` (and `delta = 1` when
/// `k = 0`), and set `a = u - delta`.  Then every non-number `G` in the
/// thermographic domain satisfies
///
/// ```text
/// mean(G.u) = u * mean(G)
/// temp(G.u) = u * temp(G) + a.
/// ```
///
/// Thus Norton multiplication by `u` sends the temperature layer `tau` to
/// `u*tau + a` for `tau >= 0`.  The cold-number branch is strictly lower than `a`; see
/// [`numeric_norton_mean_temperature`] for its exact formula.  Returns `None`
/// for nonnumeric or nonpositive units.
pub fn numeric_norton_regrade(unit: &Game) -> Option<(Rational, Rational)> {
    if !is_positive_game(unit) {
        return None;
    }
    let scale = unit.number_value()?.as_rational()?;
    let mesh = Rational::new(1, scale.denom());
    let shift = scale.sub(&mesh);
    Some((scale, shift))
}

/// The exact degree defect in composing two positive numeric Norton transports.
///
/// Apply `first_unit = u` and then `second_unit = v`.  If
/// `delta_x = 1 / denominator(x)` (with `delta_x = 1` for an integer), the
/// individual degree maps on nonnumeric temperature layers are
///
/// ```text
/// r_x(tau) = x*tau + x - delta_x.
/// ```
///
/// Their composite and the transport by the ordinary dyadic product differ by
///
/// ```text
/// r_v(r_u(tau)) - r_(uv)(tau)
///     = v*(1 - delta_u) - delta_v + delta_(uv) >= 0.
/// ```
///
/// The defect is independent of `tau`.  It can be positive: for `u = 1/2` and
/// `v = 2` it is `1`, so `A_2 A_(1/2)(*)` has temperature `1` while
/// `A_1(*) = *` has temperature `0`.  Consequently the numeric Norton transports
/// cannot be the scalar action of an associative graded algebra whose dyadic
/// coefficients multiply ordinarily.  Returns `None` when either unit is not a
/// positive short-game number.
pub fn numeric_norton_composition_defect(
    first_unit: &Game,
    second_unit: &Game,
) -> Option<Rational> {
    let (first_scale, first_shift) = numeric_norton_regrade(first_unit)?;
    let (second_scale, second_shift) = numeric_norton_regrade(second_unit)?;
    let product = first_scale.mul(&second_scale);
    let product_shift = product.sub(&Rational::new(1, product.denom()));
    Some(
        second_scale
            .mul(&first_shift)
            .add(&second_shift)
            .sub(&product_shift),
    )
}

/// Compute `(mean, temperature)` of `G.u` for a positive numeric unit `u`
/// without constructing the Norton product.
///
/// For non-numbers this applies the affine regrading returned by
/// [`numeric_norton_regrade`].  If `G` is a number with canonical dyadic mesh
/// `epsilon = 1 / denominator(G)`, its Norton image is either still a number or
/// a lower hot residue:
///
/// ```text
/// temp(G.u) = -1                         if a - u*epsilon < 0,
///             a - u*epsilon             otherwise,
/// ```
///
/// where `a` is the regrading shift.  In particular every cold number maps
/// strictly below `a`, which is the missing fact needed for numeric Norton
/// multiplication to descend to the temperature associated graded.  Returns
/// `None` when `unit` is not a positive number or `G` lies outside ordinary
/// thermography's domain.
pub fn numeric_norton_mean_temperature(g: &Game, unit: &Game) -> Option<(Rational, Rational)> {
    let (scale, shift) = numeric_norton_regrade(unit)?;
    let input = crate::games::thermography::thermograph(g)?;
    let output_mean = scale.mul(&input.mast);

    let output_temperature = if let Some(value) = g.number_value() {
        let value = value.as_rational()?;
        let epsilon = Rational::new(1, value.denom());
        let candidate = shift.sub(&scale.mul(&epsilon));
        if candidate.sign() == Ordering::Less {
            Rational::from_int(-1)
        } else {
            candidate
        }
    } else {
        scale.mul(&input.temperature).add(&shift)
    };
    Some((output_mean, output_temperature))
}

/// Heat a game by a dyadic rational temperature.
///
/// Numbers are fixed; non-number options are recursively shifted as
/// `{ heat(G^L,t) + t | heat(G^R,t) - t }`.  Returns `None` when `t` is not
/// dyadic, because arbitrary rationals are not short games.
pub fn heat(g: &Game, t: &Rational) -> Option<Game> {
    let shift = Game::from_surreal(&Surreal::from_rational(t.clone()))?;
    let neg_shift = shift.neg();
    let g = g.canonical();
    Some(heat_canonical(&g, &shift, &neg_shift, &mut HashMap::new()))
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
    let g = g.canonical();
    let unit = unit.canonical();
    let neg_unit = unit.neg();
    let increments = norton_increments_canonical(&unit);
    let neg_increments = increments.iter().map(Game::neg).collect::<Vec<_>>();
    Some(norton_multiply_canonical(
        &g,
        &unit,
        &neg_unit,
        &increments,
        &neg_increments,
        &mut HashMap::new(),
    ))
}

/// Berlekamp overheating `int_s^t G`.
///
/// The lower unit `s` must be positive. Integer leaves become `G.s` via Norton
/// multiplication; non-integers recurse as `{ overheat(G^L)+t | overheat(G^R)-t }`.
pub fn overheat(g: &Game, s: &Game, t: &Game) -> Option<Game> {
    if !is_positive_game(s) {
        return None;
    }
    let g = g.canonical();
    let s = s.canonical();
    let neg_s = s.neg();
    let increments = norton_increments_canonical(&s);
    let neg_increments = increments.iter().map(Game::neg).collect::<Vec<_>>();
    let t = t.canonical();
    let neg_t = t.neg();
    Some(overheat_canonical(
        &g,
        &s,
        &neg_s,
        &increments,
        &neg_increments,
        &t,
        &neg_t,
        &mut HashMap::new(),
        &mut HashMap::new(),
    ))
}

fn heat_canonical(
    g: &Game,
    shift: &Game,
    neg_shift: &Game,
    memo: &mut HashMap<usize, Game>,
) -> Game {
    let key = g.ptr_id();
    if let Some(heated) = memo.get(&key) {
        return heated.clone();
    }
    if g.is_number() {
        memo.insert(key, g.clone());
        return g.clone();
    }
    let left = g
        .left()
        .iter()
        .map(|gl| heat_canonical(gl, shift, neg_shift, memo).add(shift))
        .collect();
    let right = g
        .right()
        .iter()
        .map(|gr| heat_canonical(gr, shift, neg_shift, memo).add(neg_shift))
        .collect();
    let heated = Game::new(left, right).canonical();
    memo.insert(key, heated.clone());
    heated
}

fn norton_multiply_canonical(
    g: &Game,
    unit: &Game,
    neg_unit: &Game,
    increments: &[Game],
    neg_increments: &[Game],
    memo: &mut HashMap<usize, Game>,
) -> Game {
    let key = g.ptr_id();
    if let Some(product) = memo.get(&key) {
        return product.clone();
    }
    if let Some(n) = integer_game_value(g) {
        let product = if n >= 0 {
            unit.times_int(n)
        } else {
            neg_unit.times_int(-n)
        }
        .canonical();
        memo.insert(key, product.clone());
        return product;
    }

    let mut left = Vec::new();
    for gl in g.left() {
        let gl_u = norton_multiply_canonical(gl, unit, neg_unit, increments, neg_increments, memo);
        for inc in increments {
            left.push(gl_u.add(inc));
        }
    }

    let mut right = Vec::new();
    for gr in g.right() {
        let gr_u = norton_multiply_canonical(gr, unit, neg_unit, increments, neg_increments, memo);
        for inc in neg_increments {
            right.push(gr_u.add(inc));
        }
    }

    let product = Game::new(left, right).canonical();
    memo.insert(key, product.clone());
    product
}

fn norton_increments_canonical(unit: &Game) -> Vec<Game> {
    let mut out = Vec::new();
    for u in unit.left() {
        out.push(u.clone()); // U + (u - U)
    }
    for u in unit.right() {
        out.push(unit.add(&unit.add(&u.neg())).canonical()); // U + (U - u)
    }
    out
}

#[allow(clippy::too_many_arguments)]
fn overheat_canonical(
    g: &Game,
    s: &Game,
    neg_s: &Game,
    increments: &[Game],
    neg_increments: &[Game],
    t: &Game,
    neg_t: &Game,
    overheat_memo: &mut HashMap<usize, Game>,
    norton_memo: &mut HashMap<usize, Game>,
) -> Game {
    let key = g.ptr_id();
    if let Some(overheated) = overheat_memo.get(&key) {
        return overheated.clone();
    }
    if integer_game_value(g).is_some() {
        let overheated =
            norton_multiply_canonical(g, s, neg_s, increments, neg_increments, norton_memo);
        overheat_memo.insert(key, overheated.clone());
        return overheated;
    }
    let left = g
        .left()
        .iter()
        .map(|gl| {
            overheat_canonical(
                gl,
                s,
                neg_s,
                increments,
                neg_increments,
                t,
                neg_t,
                overheat_memo,
                norton_memo,
            )
            .add(t)
        })
        .collect();
    let right = g
        .right()
        .iter()
        .map(|gr| {
            overheat_canonical(
                gr,
                s,
                neg_s,
                increments,
                neg_increments,
                t,
                neg_t,
                overheat_memo,
                norton_memo,
            )
            .add(neg_t)
        })
        .collect();
    let overheated = Game::new(left, right).canonical();
    overheat_memo.insert(key, overheated.clone());
    overheated
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::games::atomic_weight_int;
    use crate::games::piecewise::req;
    use crate::games::thermography::{mean_value, temperature};
    use std::collections::BTreeMap;

    fn int(n: i128) -> Rational {
        Rational::from(n)
    }

    fn dyadic(n: i128, d: i128) -> Game {
        Game::from_surreal(&Surreal::from_rational(Rational::new(n, d))).unwrap()
    }

    fn assert_value_eq(a: &Game, b: &Game) {
        assert!(a.eq(b), "{} != {}", a.display(), b.display());
        assert!(a.canonical().structural_eq(&b.canonical()));
    }

    fn day_two_values() -> Vec<Game> {
        let day_one = [
            Game::zero(),
            Game::integer(1),
            Game::integer(-1),
            Game::star(),
        ];
        let mut values = BTreeMap::new();
        for left_mask in 0u128..(1 << day_one.len()) {
            for right_mask in 0u128..(1 << day_one.len()) {
                let left = day_one
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| left_mask & (1 << i) != 0)
                    .map(|(_, g)| g.clone())
                    .collect();
                let right = day_one
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| right_mask & (1 << i) != 0)
                    .map(|(_, g)| g.clone())
                    .collect();
                let game = Game::new(left, right).canonical();
                values.entry(game.display()).or_insert(game);
            }
        }
        let values: Vec<Game> = values.into_values().collect();
        assert_eq!(values.len(), 22);
        values
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
    fn heating_transforms_each_shared_source_node_once() {
        let heap = Game::nim_heap(6).canonical();
        let shift = Game::integer(1);
        let neg_shift = shift.neg();
        let mut memo = HashMap::new();
        let heated = heat_canonical(&heap, &shift, &neg_shift, &mut memo);
        assert_eq!(memo.len(), 7, "one entry for each shared heap size");
        assert_value_eq(&heated, &heat(&heap, &Rational::one()).unwrap());
    }

    #[test]
    fn norton_unit_one_is_identity_and_rejects_nonpositive_units() {
        let g = Game::switch(3, -1);
        assert_value_eq(&norton_multiply(&g, &Game::integer(1)).unwrap(), &g);
        assert!(norton_multiply(&g, &Game::zero()).is_none());
        assert!(norton_multiply(&g, &Game::integer(-1)).is_none());
    }

    /// A second, independently written transcription of Norton multiplication's
    /// recursive definition (Winning Ways / Siegel's CGT, "Norton's product") —
    /// deliberately NOT calling `norton_multiply`/`norton_multiply_canonical`/
    /// `norton_increments_canonical` — used below as the oracle for the non-integer-`G` /
    /// non-integer-`U` recursive branch. No citable page-pinned Winning Ways
    /// worked example for this exact case was found on hand, so per AGENTS.md this
    /// pins a cross-check computed two ways instead. The one deliberate structural
    /// difference from the production code: the right-option increment is grouped
    /// as `(U+U)+(-u)` here versus production's `U+(U+(-u))` — equal by
    /// associativity of game addition, but a different raw game tree before
    /// canonicalization, so a transcription bug (wrong sign, wrong shift, wrong
    /// slot) in either implementation is likely to surface as a disagreement.
    /// Residual risk this does NOT cover: both implementations sharing the same
    /// *misunderstanding* of the definition.
    fn norton_oracle(g: &Game, unit: &Game) -> Game {
        let g = g.canonical();
        if let Some(n) = integer_value(&g) {
            return if n >= 0 {
                unit.times_int(n)
            } else {
                unit.neg().times_int(-n)
            };
        }
        let u = unit.canonical();
        let mut incs = Vec::new();
        for ul in u.left() {
            incs.push(ul.clone());
        }
        for ur in u.right() {
            incs.push(u.add(&u).add(&ur.neg())); // (U+U) + (-u), cf. production's U+(U-u)
        }
        let mut left = Vec::new();
        for gl in g.left() {
            let base = norton_oracle(gl, unit);
            for inc in &incs {
                left.push(base.add(inc));
            }
        }
        let mut right = Vec::new();
        for gr in g.right() {
            let base = norton_oracle(gr, unit);
            for inc in &incs {
                right.push(base.add(&inc.neg()));
            }
        }
        Game::new(left, right)
    }

    #[test]
    fn norton_multiply_matches_an_independently_written_oracle_for_a_nontrivial_unit() {
        // Every *existing* Norton test has G integer (hits the trivial
        // `unit.times_int` leaf, skipping `norton_increments` entirely) or U integer
        // (whose canonical form `{k-1|}` has no Right options, so the "U+(U-u)" half
        // of `norton_increments` never runs). This is the first case with both G and
        // U genuinely non-integer, so `norton_increments` runs on both its Left and
        // Right branches.
        for (g, unit) in [
            (Game::switch(1, -1), Game::up()),
            (Game::star(), Game::up()),
        ] {
            let expected = norton_oracle(&g, &unit);
            let actual = norton_multiply(&g, &unit).unwrap();
            assert!(
                actual.eq(&expected),
                "norton_multiply({}, {}) = {} but the independent oracle gives {}",
                g.display(),
                unit.display(),
                actual.display(),
                expected.display()
            );
        }
    }

    #[test]
    fn norton_multiplication_has_product_mean_for_integer_unit() {
        let g = Game::switch(3, -1); // mean 1
        let product = norton_multiply(&g, &Game::integer(2)).unwrap();
        assert_value_eq(&product, &Game::switch(7, -3));
        assert!(req(&mean_value(&product).unwrap(), &int(2)));
    }

    #[test]
    fn positive_numeric_units_have_the_exact_affine_thermic_regrade() {
        let star2 = Game::nim_heap(2);
        let nested = Game::new(vec![Game::integer(3)], vec![Game::switch(1, -1)]);
        let mut games = day_two_values();
        games.extend([
            Game::integer(-2),
            dyadic(-3, 4),
            dyadic(1, 4),
            dyadic(1, 2),
            dyadic(3, 4),
            Game::star(),
            star2,
            Game::up(),
            Game::up().neg(),
            Game::switch(1, -1),
            Game::switch(3, -1),
            nested,
        ]);
        let units = [
            dyadic(1, 4),
            dyadic(1, 2),
            dyadic(3, 4),
            Game::integer(1),
            dyadic(5, 4),
            dyadic(3, 2),
            Game::integer(2),
            Game::integer(3),
        ];

        for unit in units {
            let (scale, shift) = numeric_norton_regrade(&unit).unwrap();
            assert!(scale.sign() == Ordering::Greater);
            assert!(shift.sign() != Ordering::Less);
            for g in &games {
                let product = norton_multiply(g, &unit).unwrap();
                let (predicted_mean, predicted_temperature) =
                    numeric_norton_mean_temperature(g, &unit).unwrap();
                assert!(
                    req(&mean_value(&product).unwrap(), &predicted_mean),
                    "mean regrade failed for G={} and u={}",
                    g.display(),
                    scale
                );
                assert!(
                    req(&temperature(&product).unwrap(), &predicted_temperature),
                    "temperature regrade failed for G={} and u={} (shift {})",
                    g.display(),
                    scale,
                    shift
                );
            }
        }

        assert!(numeric_norton_regrade(&Game::up()).is_none());
        assert!(numeric_norton_regrade(&Game::zero()).is_none());
        assert!(numeric_norton_regrade(&Game::integer(-1)).is_none());
    }

    #[test]
    fn numeric_images_of_numbers_pin_the_lower_temperature_lemma() {
        let numbers = [
            dyadic(1, 8),
            dyadic(1, 4),
            dyadic(1, 2),
            dyadic(3, 4),
            dyadic(5, 8),
            Game::integer(2),
        ];
        let units = [
            dyadic(1, 4),
            dyadic(1, 2),
            Game::integer(1),
            dyadic(5, 4),
            dyadic(3, 2),
            Game::integer(2),
            Game::integer(3),
        ];
        for unit in units {
            let (_, shift) = numeric_norton_regrade(&unit).unwrap();
            for number in &numbers {
                let product = norton_multiply(number, &unit).unwrap();
                let (_, predicted_temperature) =
                    numeric_norton_mean_temperature(number, &unit).unwrap();
                assert!(req(&temperature(&product).unwrap(), &predicted_temperature));
                assert!(
                    predicted_temperature.cmp(&shift) == Ordering::Less,
                    "numeric image did not stay below shift for x={}, u={}",
                    number.display(),
                    unit.display()
                );
            }
        }

        // The load-bearing subtlety: numeric images need not remain numbers.
        let half_times_two = norton_multiply(&dyadic(1, 2), &Game::integer(2)).unwrap();
        assert!(!half_times_two.is_number());
        assert_value_eq(&half_times_two, &Game::integer(1).add(&Game::star()));
        assert!(req(&temperature(&half_times_two).unwrap(), &int(0)));
    }

    #[test]
    fn numeric_norton_is_the_matching_berlekamp_overheating() {
        let games = [
            dyadic(1, 4),
            Game::star(),
            Game::up(),
            Game::switch(1, -1),
            Game::new(vec![Game::integer(3)], vec![Game::switch(1, -1)]),
        ];
        let units = [dyadic(1, 2), dyadic(3, 4), dyadic(3, 2), Game::integer(2)];
        for unit in units {
            let (_, shift) = numeric_norton_regrade(&unit).unwrap();
            let shift = dyadic(shift.numer(), shift.denom());
            for game in &games {
                assert_value_eq(
                    &norton_multiply(game, &unit).unwrap(),
                    &overheat(game, &unit, &shift).unwrap(),
                );
            }
        }
    }

    #[test]
    fn numeric_norton_has_the_exact_composition_defect() {
        // The theorem is degree-level, so test it on several nonnumeric layers.
        let games = [Game::star(), Game::up(), Game::switch(1, -1)];
        let cases = [
            (dyadic(1, 2), Game::integer(2), int(1)),
            (Game::integer(2), dyadic(1, 2), Rational::new(1, 2)),
            (Game::integer(3), dyadic(1, 2), int(0)),
            (dyadic(1, 2), dyadic(1, 4), int(0)),
            (dyadic(3, 2), dyadic(3, 2), Rational::new(1, 2)),
        ];

        for (first, second, expected_defect) in cases {
            let defect = numeric_norton_composition_defect(&first, &second).unwrap();
            assert!(req(&defect, &expected_defect));
            assert!(defect.sign() != Ordering::Less);

            let first_value = first.number_value().unwrap().as_rational().unwrap();
            let second_value = second.number_value().unwrap().as_rational().unwrap();
            let product_value = first_value.mul(&second_value);
            let product_unit = dyadic(product_value.numer(), product_value.denom());
            for game in &games {
                let composite =
                    norton_multiply(&norton_multiply(game, &first).unwrap(), &second).unwrap();
                let direct = norton_multiply(game, &product_unit).unwrap();
                let actual_defect = temperature(&composite)
                    .unwrap()
                    .sub(&temperature(&direct).unwrap());
                assert!(
                    req(&actual_defect, &defect),
                    "composition defect failed for G={}, u={}, v={}",
                    game.display(),
                    first_value,
                    second_value
                );
                assert!(req(
                    &mean_value(&composite).unwrap(),
                    &mean_value(&direct).unwrap()
                ));
            }
        }

        assert!(numeric_norton_composition_defect(&Game::up(), &Game::integer(2)).is_none());
        assert!(numeric_norton_composition_defect(&Game::integer(1), &Game::zero()).is_none());
    }

    #[test]
    fn bounded_day_three_singleton_options_obey_numeric_regrade() {
        let day_two = day_two_values();
        let mut candidates = BTreeMap::new();
        for left in std::iter::once(None).chain(day_two.iter().map(Some)) {
            for right in std::iter::once(None).chain(day_two.iter().map(Some)) {
                let game = Game::new(
                    left.into_iter().cloned().collect(),
                    right.into_iter().cloned().collect(),
                )
                .canonical();
                candidates.entry(game.display()).or_insert(game);
            }
        }
        let units = [dyadic(3, 4), dyadic(3, 2), Game::integer(2)];
        let mut checked = 0usize;
        for game in candidates.into_values() {
            if mean_value(&game).is_none() {
                continue;
            }
            for unit in &units {
                let product = norton_multiply(&game, unit).unwrap();
                let Some(actual_mean) = mean_value(&product) else {
                    continue;
                };
                let actual_temperature = temperature(&product).unwrap();
                let (predicted_mean, predicted_temperature) =
                    numeric_norton_mean_temperature(&game, unit).unwrap();
                assert!(req(&actual_mean, &predicted_mean));
                assert!(req(&actual_temperature, &predicted_temperature));
                checked += 1;
            }
        }
        assert!(
            checked > 300,
            "bounded census was unexpectedly small: {checked}"
        );
    }

    #[test]
    fn numeric_norton_units_descend_to_temperature_layers() {
        // Each pair differs by the cold number 1/2, including the tau=0
        // all-small layer and two genuinely hot layers.  The cold image need
        // not remain a number, but the exact formula keeps it strictly below
        // the affine output layer.
        let half = dyadic(1, 2);
        let representatives = [
            (Game::star(), Game::star().add(&half), int(0)),
            (Game::switch(1, -1), Game::switch(1, -1).add(&half), int(1)),
            (Game::switch(3, -1), Game::switch(3, -1).add(&half), int(2)),
        ];
        let units = [dyadic(1, 2), dyadic(3, 4), dyadic(3, 2), Game::integer(2)];

        for unit in units {
            let (scale, shift) = numeric_norton_regrade(&unit).unwrap();
            for (g, h, tau) in &representatives {
                let input_delta = g.add(&h.neg());
                assert!(temperature(&input_delta).unwrap().cmp(tau) == Ordering::Less);

                let output_layer = scale.mul(tau).add(&shift);
                let output_delta = norton_multiply(g, &unit)
                    .unwrap()
                    .add(&norton_multiply(h, &unit).unwrap().neg());
                assert!(
                    temperature(&output_delta).unwrap().cmp(&output_layer) == Ordering::Less,
                    "numeric Norton descent failed for tau={}, u={}",
                    tau,
                    scale
                );
            }
        }
    }

    #[test]
    fn numeric_norton_is_additive_on_bounded_pairs() {
        // Norton linearity is standard CGT; keep a source-level sentinel because
        // it is the algebraic step that turns the thermic formula into quotient
        // descent rather than a representative-by-representative coincidence.
        let games = [Game::star(), Game::up(), Game::switch(1, -1)];
        let units = [dyadic(3, 4), Game::integer(2)];
        for unit in units {
            for g in &games {
                for h in &games {
                    let sum_product = norton_multiply(&g.add(h), &unit).unwrap();
                    let product_sum = norton_multiply(g, &unit)
                        .unwrap()
                        .add(&norton_multiply(h, &unit).unwrap());
                    assert_value_eq(&sum_product, &product_sum);
                }
            }
        }
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
