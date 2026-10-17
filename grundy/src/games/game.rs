//! `Game`: short game values held in sealed canonical form.
//!
//! Every value lives in a per-thread [`GameArena`], so equality and hashing are
//! id comparisons, and options are sorted by a deterministic structural order
//! independent of allocation and discovery order. Every operation is therefore
//! a function of the value.
//!
//! Arena work is paid from the statement's fuel through a [`Meter`], and
//! birthdays are bounded by a host guard because every game algorithm
//! recurses on depth.

use std::cell::RefCell;
use std::cmp::Ordering;

use ogdoad::games::{ArenaExhausted, Game, GameArena, GameId};
use ogdoad::scalar::{Rational, Surreal};

use super::super::error::{err, GrundyError, GrundyErrorKind, GrundyResult};

/// The latest day a `Game` may be born: game algorithms recurse on depth, so
/// depth is a host resource like the call stack.
pub const MAX_BIRTHDAY: u128 = 1 << 14;

/// A sealed canonical short game.
#[derive(Clone)]
pub struct GameV {
    id: GameId,
}

thread_local! {
    static ARENA: RefCell<GameArena> = RefCell::new(GameArena::new());
}

fn with<R>(f: impl FnOnce(&mut GameArena) -> R) -> R {
    ARENA.with(|arena| f(&mut arena.borrow_mut()))
}

/// Pays for canonical-game work.
pub trait Meter {
    /// The fuel left.
    fn remaining(&self) -> u128;
    /// Spend fuel, failing with `E_Fuel` past the budget.
    fn charge(&mut self, amount: u128) -> GrundyResult<()>;
}

/// Run arena work within the meter's remaining fuel, then charge what it used.
fn metered<R>(
    meter: &mut impl Meter,
    work: impl FnOnce(&mut GameArena) -> Result<R, ArenaExhausted>,
) -> GrundyResult<R> {
    let remaining = meter.remaining();
    let (result, left) = with(|arena| {
        arena.set_budget(Some(remaining));
        let result = work(arena);
        let left = arena.budget().unwrap_or(0);
        arena.set_budget(None);
        (result, left)
    });
    match result {
        Ok(value) => {
            meter.charge(remaining - left)?;
            Ok(value)
        }
        Err(ArenaExhausted) => Err(meter
            .charge(u128::MAX)
            .expect_err("an exhausted arena exceeds the remaining fuel")),
    }
}

fn too_deep(birthday: u128) -> GrundyError {
    err(
        GrundyErrorKind::StackDepth,
        format!(
            "the game would be born on day {birthday}, past the host guard of day {MAX_BIRTHDAY}"
        ),
    )
    .with_hint("game depth is a host resource, distinct from fuel")
}

/// Refuse a game born past [`MAX_BIRTHDAY`].
pub fn guard(birthday: u128) -> GrundyResult<()> {
    if birthday > MAX_BIRTHDAY {
        return Err(too_deep(birthday));
    }
    Ok(())
}

impl GameV {
    fn sealed(id: GameId) -> GrundyResult<GameV> {
        guard(with(|arena| arena.birthday(id)))?;
        Ok(GameV { id })
    }

    /// Seal an engine game: canonicalize and intern it.
    pub fn seal(game: &Game, meter: &mut impl Meter) -> GrundyResult<GameV> {
        GameV::sealed(metered(meter, |arena| arena.intern(game))?)
    }

    /// The underlying canonical engine game.
    pub fn game(&self) -> Game {
        with(|arena| arena.to_game(self.id))
    }

    /// `0`.
    pub fn zero() -> GameV {
        GameV {
            id: with(|arena| arena.zero()),
        }
    }

    /// The integer `n`.
    pub fn integer(n: i128, meter: &mut impl Meter) -> GrundyResult<GameV> {
        guard(n.unsigned_abs())?;
        GameV::sealed(metered(meter, |arena| arena.integer(n))?)
    }

    /// The nimber `*n`.
    pub fn nimber(n: u128, meter: &mut impl Meter) -> GrundyResult<GameV> {
        guard(n)?;
        GameV::sealed(metered(meter, |arena| arena.nimber(n))?)
    }

    /// The dyadic `num/den` in lowest terms.
    pub fn dyadic(num: i128, den: u128, meter: &mut impl Meter) -> GrundyResult<GameV> {
        if den == 0 {
            return Err(err(GrundyErrorKind::DivisionByZero, "zero denominator"));
        }
        let den_i = i128::try_from(den)
            .map_err(|_| err(GrundyErrorKind::Overflow, "denominator exceeds i128"))?;
        let value = Surreal::from_rational(Rational::new(num, den_i));
        GameV::of_surreal(&value, meter)?.ok_or_else(|| {
            err(
                GrundyErrorKind::Domain,
                format!("{num}/{den} is not a dyadic rational"),
            )
            .with_hint("only dyadics are short games; `1/3` is not born on any finite day")
        })
    }

    /// The game of a dyadic surreal; `None` for any other surreal.
    pub fn of_surreal(value: &Surreal, meter: &mut impl Meter) -> GrundyResult<Option<GameV>> {
        let Some((num, k)) = value.as_dyadic() else {
            return Ok(None);
        };
        // The canonical form of n + m/2^k is born on day |n| + k (+1 when k > 0).
        let whole = num.unsigned_abs() >> k.min(127);
        guard(whole.saturating_add(k))?;
        Ok(Some(GameV::sealed(metered(meter, |arena| {
            arena.dyadic(num, k)
        })?)?))
    }

    /// `up` (or `down`).
    pub fn up(down: bool) -> GameV {
        GameV {
            id: with(|arena| if down { arena.down() } else { arena.up() }),
        }
    }

    /// Build `{L | R}` from sealed options.
    pub fn form(left: &[GameV], right: &[GameV], meter: &mut impl Meter) -> GrundyResult<GameV> {
        let birthday = left
            .iter()
            .chain(right)
            .map(|g| g.birthday() + 1)
            .max()
            .unwrap_or(0);
        guard(birthday)?;
        let ids = |side: &[GameV]| side.iter().map(|g| g.id).collect::<Vec<_>>();
        let (left, right) = (ids(left), ids(right));
        GameV::sealed(metered(meter, |arena| arena.form(&left, &right))?)
    }

    /// The disjunctive sum.
    pub fn add(&self, other: &GameV, meter: &mut impl Meter) -> GrundyResult<GameV> {
        let both_numbers = self.is_number() && other.is_number();
        if !both_numbers {
            // Sum algorithms recurse to the sum of the birthdays.
            guard(self.birthday() + other.birthday())?;
        }
        GameV::sealed(metered(meter, |arena| arena.add(self.id, other.id))?)
    }

    /// The negative.
    pub fn neg(&self, meter: &mut impl Meter) -> GrundyResult<GameV> {
        GameV::sealed(metered(meter, |arena| arena.neg(self.id))?)
    }

    /// `self − other`.
    pub fn sub(&self, other: &GameV, meter: &mut impl Meter) -> GrundyResult<GameV> {
        let negated = other.neg(meter)?;
        self.add(&negated, meter)
    }

    /// `self ≤ other` in the game order.
    pub fn le(&self, other: &GameV, meter: &mut impl Meter) -> GrundyResult<bool> {
        metered(meter, |arena| arena.le(self.id, other.id))
    }

    /// The four-way comparison: `Some(ordering)` or `None` for fuzzy.
    pub fn compare(&self, other: &GameV, meter: &mut impl Meter) -> GrundyResult<Option<Ordering>> {
        metered(meter, |arena| arena.compare(self.id, other.id))
    }

    /// The deterministic structural order (also the `Key` order).
    pub fn structural_cmp(&self, other: &GameV) -> Ordering {
        with(|arena| arena.structural_cmp(self.id, other.id))
    }

    /// Value equality (an id comparison).
    pub fn same(&self, other: &GameV) -> bool {
        self.id == other.id
    }

    /// The interned id (a value key within one session).
    pub fn id(&self) -> usize {
        self.id.index()
    }

    /// Canonical Left options in structural order.
    pub fn lefts(&self) -> Vec<GameV> {
        with(|arena| {
            arena
                .left(self.id)
                .iter()
                .map(|id| GameV { id: *id })
                .collect()
        })
    }

    /// Canonical Right options in structural order.
    pub fn rights(&self) -> Vec<GameV> {
        with(|arena| {
            arena
                .right(self.id)
                .iter()
                .map(|id| GameV { id: *id })
                .collect()
        })
    }

    /// The value birthday.
    pub fn birthday(&self) -> u128 {
        with(|arena| arena.birthday(self.id))
    }

    /// Whether the game is a number.
    pub fn is_number(&self) -> bool {
        with(|arena| arena.number_value(self.id).is_some())
    }

    /// The number value, if the game is a number.
    pub fn number(&self) -> Option<Surreal> {
        with(|arena| arena.number_value(self.id).cloned())
    }

    /// `n` if the canonical form is the nimber `*n`.
    pub fn as_nimber(&self) -> Option<u128> {
        with(|arena| arena.nimber_value(self.id))
    }
}
