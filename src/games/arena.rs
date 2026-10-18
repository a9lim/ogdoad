//! A hash-consed store of canonical short games.
//!
//! [`Game::canonical`] reduces one tree per call and keeps no comparison
//! results between calls or between nodes. Values with large shared structure,
//! such as sums with big integer parts or high nimbers, therefore repeat the same
//! order comparisons many times. A [`GameArena`] interns each canonical form
//! once and memoizes the order, sums, and negations across operations:
//!
//! - numbers, nimbers, and `↑` are built directly in canonical form;
//! - a sum of numbers is added as numbers;
//! - a number plus a non-number uses number translation,
//!   `G + x = {G^L + x | G^R + x}`.
//!
//! # Budget
//!
//! An arena holds an optional count of remaining steps
//! ([`set_budget`](GameArena::set_budget)). The builders,
//! [`form`](GameArena::form), [`intern`](GameArena::intern),
//! [`le`](GameArena::le), [`compare`](GameArena::compare),
//! [`add`](GameArena::add), and [`neg`](GameArena::neg) charge each memo miss
//! one step plus the options and input entries it scans, before doing that
//! work. An operation that would exceed the budget fails with
//! [`ArenaError::BudgetExhausted`] and leaves the budget at zero; every memo
//! entry it recorded is complete and stays valid. Memo hits are free, so what
//! an operation costs depends on what the arena has already computed.
//!
//! Accessors, [`structural_cmp`](GameArena::structural_cmp), and
//! [`to_game`](GameArena::to_game) are unmetered: their work is bounded by the
//! interned structure, and both cache their results for the arena's lifetime.
//! [`positions`](GameArena::positions) is bounded by its `limit`.
//!
//! # Limits
//!
//! - Number values are dyadic rationals `num / 2^k` with an `i128` numerator
//!   and `k <= 126` ([`GameArena::MAX_DYADIC_EXPONENT`]), the range a
//!   [`Surreal`] coefficient holds. A builder, form, or sum whose number value
//!   falls outside that range fails with [`ArenaError::NumberOutOfRange`];
//!   number arithmetic is exact inside it.
//! - A [`GameId`] is meaningful only in the arena that issued it. Ids are not
//!   checked against their arena: a foreign id names an unrelated value or
//!   panics.
//! - Recursion depth is proportional to the birthdays involved, as it is for
//!   [`Game`], and for [`intern`](GameArena::intern) to the depth of the
//!   supplied tree. In the metered operations a finite budget also bounds it,
//!   since every level is charged before it descends; callers that run
//!   unbudgeted on arbitrary inputs bound birthdays themselves.
//! - An arena holds fewer than `2^32` canonical forms; interning past that
//!   panics.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::games::Game;
use crate::scalar::{Rational, Surreal};

/// A canonical game in a [`GameArena`]. Within one arena, equal ids are
/// exactly equal values.
///
/// Ids carry no order: the allocation order has no mathematical meaning. Use
/// [`GameArena::le`] for the game order and [`GameArena::structural_cmp`] for a
/// deterministic total order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GameId(u32);

impl GameId {
    /// The allocation index, for side tables indexed by id. It depends on
    /// construction order, not on the value.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Why an arena operation was refused.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArenaError {
    /// The step budget ran out. The budget is left at zero.
    BudgetExhausted,
    /// A number value falls outside the dyadics `num / 2^k` with an `i128`
    /// numerator and `k <= 126`.
    NumberOutOfRange,
}

impl fmt::Display for ArenaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArenaError::BudgetExhausted => write!(f, "the game arena's step budget is exhausted"),
            ArenaError::NumberOutOfRange => write!(
                f,
                "a number value falls outside the arena's dyadic range (i128 numerator, exponent at most 126)"
            ),
        }
    }
}

impl std::error::Error for ArenaError {}

type Step<T> = Result<T, ArenaError>;

/// A dyadic rational `num / 2^k` in lowest terms (`k == 0` or `num` odd), with
/// `k <= MAX_DYADIC_EXPONENT`. Its arithmetic is exact and refuses only values
/// outside that range.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Dyadic {
    num: i128,
    k: u32,
}

impl Dyadic {
    const ZERO: Dyadic = Dyadic { num: 0, k: 0 };

    /// `num / 2^k` in lowest terms, in constant time.
    fn new(num: i128, k: u128) -> Step<Dyadic> {
        if num == 0 {
            return Ok(Dyadic::ZERO);
        }
        let shift = k.min(u128::from(num.trailing_zeros()));
        let k = k - shift;
        if k > GameArena::MAX_DYADIC_EXPONENT {
            return Err(ArenaError::NumberOutOfRange);
        }
        Ok(Dyadic {
            num: num >> shift,
            k: k as u32,
        })
    }

    fn integer(n: i128) -> Dyadic {
        Dyadic { num: n, k: 0 }
    }

    fn floor(self) -> i128 {
        self.num >> self.k
    }

    fn neg(self) -> Step<Dyadic> {
        let num = self.num.checked_neg().ok_or(ArenaError::NumberOutOfRange)?;
        Ok(Dyadic { num, k: self.k })
    }

    fn add(self, other: Dyadic) -> Step<Dyadic> {
        let overflow = ArenaError::NumberOutOfRange;
        let (a, b) = if self.k <= other.k {
            (self, other)
        } else {
            (other, self)
        };
        if a.k == b.k {
            if a.k == 0 {
                return a
                    .num
                    .checked_add(b.num)
                    .map(Dyadic::integer)
                    .ok_or(overflow);
            }
            // Both numerators are odd: a + b = 2 (a' + b' + 1) with a' = a >> 1.
            let half = (a.num >> 1)
                .checked_add(b.num >> 1)
                .and_then(|sum| sum.checked_add(1))
                .ok_or(overflow)?;
            return Dyadic::new(half, u128::from(a.k) - 1);
        }
        // `b.num` is odd and the scaled `a.num` even, so the sum stays reduced.
        // The scaled term may leave i128 while the sum does not.
        let num = shl_add(a.num, b.k - a.k, b.num).ok_or(overflow)?;
        Ok(Dyadic { num, k: b.k })
    }

    /// The simplest number greater than `self`: `{self | }`.
    fn simplest_above(self) -> Step<Dyadic> {
        if self < Dyadic::ZERO {
            return Ok(Dyadic::ZERO);
        }
        let n = self
            .floor()
            .checked_add(1)
            .ok_or(ArenaError::NumberOutOfRange)?;
        Ok(Dyadic::integer(n))
    }

    /// The simplest number less than `self`: `{ | self}`.
    fn simplest_below(self) -> Step<Dyadic> {
        self.neg()?.simplest_above()?.neg()
    }

    /// The simplest number strictly between `l < r`.
    fn simplest_between(l: Dyadic, r: Dyadic) -> Step<Dyadic> {
        if l < Dyadic::ZERO && Dyadic::ZERO < r {
            return Ok(Dyadic::ZERO);
        }
        if r <= Dyadic::ZERO {
            return Dyadic::simplest_between(r.neg()?, l.neg()?)?.neg();
        }
        // 0 <= l < r: the least integer above `l`, if it lies below `r`.
        let next = l.simplest_above()?;
        if next < r {
            return Ok(next);
        }
        // Otherwise both lie in one unit interval, and the simplest number
        // between them is the one of least denominator.
        let overflow = ArenaError::NumberOutOfRange;
        for d in 1..=GameArena::MAX_DYADIC_EXPONENT {
            let lk = u128::from(l.k);
            let floor = if lk >= d {
                l.num >> (lk - d)
            } else {
                l.num.checked_mul(1 << (d - lk)).ok_or(overflow)?
            };
            let candidate = Dyadic::new(floor.checked_add(1).ok_or(overflow)?, d)?;
            if candidate < r {
                return Ok(candidate);
            }
        }
        Err(overflow)
    }

    fn to_surreal(self) -> Surreal {
        Surreal::from_rational(Rational::new(self.num, 1 << self.k))
    }
}

/// `a * 2^shift + b` exactly, for `0 < shift < 128`, or `None` when it leaves
/// `i128`. Works in 256-bit two's complement `(hi, lo)`, so an aligned term
/// outside `i128` that `b` cancels back into range is not refused.
fn shl_add(a: i128, shift: u32, b: i128) -> Option<i128> {
    let (a_lo, a_hi) = (a as u128, if a < 0 { -1i128 } else { 0 });
    let lo = a_lo << shift;
    let hi = a_hi.wrapping_shl(shift) | (a_lo >> (128 - shift)) as i128;
    let (b_lo, b_hi) = (b as u128, if b < 0 { -1i128 } else { 0 });
    let (lo, carry) = lo.overflowing_add(b_lo);
    let hi = hi.wrapping_add(b_hi).wrapping_add(i128::from(carry));
    let num = lo as i128;
    (hi == if num < 0 { -1 } else { 0 }).then_some(num)
}

impl Ord for Dyadic {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.k == other.k {
            return self.num.cmp(&other.num);
        }
        let (a, b, flipped) = if self.k < other.k {
            (self, other, false)
        } else {
            (other, self, true)
        };
        // Compare a * 2^(b.k - a.k) with b.num; on overflow the scaled side
        // exceeds every i128 in magnitude.
        let ordering = match a.num.checked_mul(1 << (b.k - a.k)) {
            Some(scaled) => scaled.cmp(&b.num),
            None if a.num > 0 => Ordering::Greater,
            None => Ordering::Less,
        };
        if flipped {
            ordering.reverse()
        } else {
            ordering
        }
    }
}

impl PartialOrd for Dyadic {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Sorted Left and Right option ids of a canonical node.
type Children = (Box<[GameId]>, Box<[GameId]>);

struct Node {
    left: Box<[GameId]>,
    right: Box<[GameId]>,
    birthday: u128,
    number: Option<Dyadic>,
    nimber: Option<u128>,
}

/// The options of a form that is being canonicalized and is not yet interned.
struct Pending<'a> {
    left: &'a [GameId],
    right: &'a [GameId],
}

/// Canonical short games, interned once, with persistent order, sum, and
/// negation memos.
///
/// See the [module documentation](self) for the budget and the limits.
///
/// # Examples
///
/// Sums and comparisons of standard values:
///
/// ```
/// use ogdoad::games::{ArenaError, GameArena};
///
/// # fn main() -> Result<(), ArenaError> {
/// let mut arena = GameArena::new();
/// let (star, up) = (arena.nimber(1)?, arena.up()?);
/// // * + * = 0, and *3 + *5 = *6 by nim-addition.
/// assert_eq!(arena.add(star, star)?, arena.zero());
/// let (s3, s5) = (arena.nimber(3)?, arena.nimber(5)?);
/// assert_eq!(arena.add(s3, s5)?, arena.nimber(6)?);
/// // ↑ + * is confused with 0, while ↑ + ↑ + * is positive.
/// let up_star = arena.add(up, star)?;
/// assert_eq!(arena.compare(up_star, arena.zero())?, None);
/// let up_up_star = arena.add(up_star, up)?;
/// assert_eq!(arena.compare(up_up_star, arena.zero())?, Some(std::cmp::Ordering::Greater));
/// // 1/2 + 1/2 = 1: equal values share one id.
/// let half = arena.dyadic(1, 1)?;
/// assert_eq!(arena.add(half, half)?, arena.integer(1)?);
/// # Ok(())
/// # }
/// ```
///
/// Budgets and the number range are refusals, not panics:
///
/// ```
/// use ogdoad::games::{ArenaError, GameArena};
///
/// let mut arena = GameArena::new();
/// arena.set_budget(Some(10));
/// assert_eq!(arena.nimber(40), Err(ArenaError::BudgetExhausted));
/// assert_eq!(arena.budget(), Some(0));
/// arena.set_budget(None);
/// assert!(arena.dyadic(1, 126).is_ok());
/// assert_eq!(arena.dyadic(1, 127), Err(ArenaError::NumberOutOfRange));
/// ```
pub struct GameArena {
    nodes: Vec<Node>,
    by_children: HashMap<Children, GameId>,
    dyadics: HashMap<Dyadic, GameId>,
    /// Every integer in `integers.0 ..= integers.1` is interned.
    integers: (i128, i128),
    nimbers: Vec<GameId>,
    le_memo: HashMap<(GameId, GameId), bool>,
    sums: HashMap<(GameId, GameId), GameId>,
    negs: HashMap<GameId, GameId>,
    order: HashMap<(GameId, GameId), Ordering>,
    games: Vec<Option<Game>>,
    budget: Option<u128>,
}

impl Default for GameArena {
    fn default() -> Self {
        GameArena::new()
    }
}

impl GameArena {
    /// The largest `k` of a number value `num / 2^k` the arena represents.
    pub const MAX_DYADIC_EXPONENT: u128 = 126;

    /// An arena holding only `0`, with no step budget.
    pub fn new() -> GameArena {
        let mut arena = GameArena {
            nodes: Vec::new(),
            by_children: HashMap::new(),
            dyadics: HashMap::new(),
            integers: (0, 0),
            nimbers: Vec::new(),
            le_memo: HashMap::new(),
            sums: HashMap::new(),
            negs: HashMap::new(),
            order: HashMap::new(),
            games: Vec::new(),
            budget: None,
        };
        let zero = arena
            .intern_node(Vec::new(), Vec::new())
            .expect("0 is a number in range");
        arena.dyadics.insert(Dyadic::ZERO, zero);
        arena.nimbers.push(zero);
        arena
    }

    /// Set the steps remaining before operations fail; `None` is unbounded.
    pub fn set_budget(&mut self, steps: Option<u128>) {
        self.budget = steps;
    }

    /// The steps remaining, or `None` when unbounded.
    pub fn budget(&self) -> Option<u128> {
        self.budget
    }

    fn charge(&mut self, steps: usize) -> Step<()> {
        if let Some(budget) = self.budget.as_mut() {
            let steps = steps as u128;
            if *budget < steps {
                *budget = 0;
                return Err(ArenaError::BudgetExhausted);
            }
            *budget -= steps;
        }
        Ok(())
    }

    /// The number of interned canonical forms.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Always false: the arena holds `0` from creation.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    fn node(&self, g: GameId) -> &Node {
        &self.nodes[g.index()]
    }

    /// `0`.
    pub fn zero(&self) -> GameId {
        GameId(0)
    }

    /// Canonical Left options, in structural order.
    pub fn left(&self, g: GameId) -> &[GameId] {
        &self.node(g).left
    }

    /// Canonical Right options, in structural order.
    pub fn right(&self, g: GameId) -> &[GameId] {
        &self.node(g).right
    }

    /// The birthday of the value.
    pub fn birthday(&self, g: GameId) -> u128 {
        self.node(g).birthday
    }

    /// The number the game equals, if it is a number.
    pub fn number_value(&self, g: GameId) -> Option<Surreal> {
        self.node(g).number.map(Dyadic::to_surreal)
    }

    /// `n` if the game is the nimber `*n`.
    pub fn nimber_value(&self, g: GameId) -> Option<u128> {
        self.node(g).nimber
    }

    /// A deterministic total order on canonical forms, independent of
    /// construction order: birthday, then option counts, then options in order.
    /// Unmetered and memoized.
    pub fn structural_cmp(&mut self, a: GameId, b: GameId) -> Ordering {
        if a == b {
            return Ordering::Equal;
        }
        if let Some(ordering) = self.order.get(&(a, b)) {
            return *ordering;
        }
        let (na, nb) = (self.node(a), self.node(b));
        let mut ordering = na
            .birthday
            .cmp(&nb.birthday)
            .then(na.left.len().cmp(&nb.left.len()))
            .then(na.right.len().cmp(&nb.right.len()));
        let (left, right) = (na.left.len(), na.right.len());
        for i in 0..left + right {
            if ordering != Ordering::Equal {
                break;
            }
            let (x, y) = if i < left {
                (self.node(a).left[i], self.node(b).left[i])
            } else {
                (self.node(a).right[i - left], self.node(b).right[i - left])
            };
            ordering = self.structural_cmp(x, y);
        }
        self.order.insert((a, b), ordering);
        self.order.insert((b, a), ordering.reverse());
        ordering
    }

    /// Intern `{left | right}`, whose options must be canonical and which must
    /// have no dominated or reversible option. Fails only when the form is a
    /// number outside the dyadic range.
    fn intern_node(&mut self, mut left: Vec<GameId>, mut right: Vec<GameId>) -> Step<GameId> {
        left.sort_by(|a, b| self.structural_cmp(*a, *b));
        left.dedup();
        right.sort_by(|a, b| self.structural_cmp(*a, *b));
        right.dedup();
        let key = (left.into_boxed_slice(), right.into_boxed_slice());
        if let Some(&id) = self.by_children.get(&key) {
            return Ok(id);
        }
        let number = self.number_of(&key.0, &key.1)?;
        let birthday = key
            .0
            .iter()
            .chain(key.1.iter())
            .map(|child| self.node(*child).birthday + 1)
            .max()
            .unwrap_or(0);
        let nimber = (key.0 == key.1
            && key
                .0
                .iter()
                .enumerate()
                .all(|(k, child)| self.node(*child).nimber == Some(k as u128)))
        .then_some(key.0.len() as u128);
        let id = GameId(u32::try_from(self.nodes.len()).expect("fewer than 2^32 game forms"));
        self.nodes.push(Node {
            left: key.0.clone(),
            right: key.1.clone(),
            birthday,
            number,
            nimber,
        });
        self.games.push(None);
        self.by_children.insert(key, id);
        Ok(id)
    }

    /// The simplicity theorem on options whose values are known.
    fn number_of(&self, left: &[GameId], right: &[GameId]) -> Step<Option<Dyadic>> {
        let values = |side: &[GameId]| -> Option<Vec<Dyadic>> {
            side.iter().map(|child| self.node(*child).number).collect()
        };
        let (Some(lvals), Some(rvals)) = (values(left), values(right)) else {
            return Ok(None);
        };
        match (lvals.into_iter().max(), rvals.into_iter().min()) {
            (None, None) => Ok(Some(Dyadic::ZERO)),
            (Some(l), None) => l.simplest_above().map(Some),
            (None, Some(r)) => r.simplest_below().map(Some),
            (Some(l), Some(r)) if l < r => Dyadic::simplest_between(l, r).map(Some),
            _ => Ok(None),
        }
    }

    // -------------------------------------------------------------- builders

    /// The integer `n`. Building it costs one step for each integer not yet
    /// interned between `0` and `n`.
    pub fn integer(&mut self, n: i128) -> Step<GameId> {
        self.number(Dyadic::integer(n))
    }

    /// The dyadic `num / 2^k`, refused when its lowest terms need `k > 126`.
    pub fn dyadic(&mut self, num: i128, k: u128) -> Step<GameId> {
        self.number(Dyadic::new(num, k)?)
    }

    fn number(&mut self, d: Dyadic) -> Step<GameId> {
        if let Some(&id) = self.dyadics.get(&d) {
            return Ok(id);
        }
        let id = if d.k == 0 {
            // Extend the integer chain outward from its built end.
            let (step, mut current): (i128, i128) = if d.num > 0 {
                (1, self.integers.1)
            } else {
                (-1, self.integers.0)
            };
            let mut id = self.dyadics[&Dyadic::integer(current)];
            while current != d.num {
                self.charge(1)?;
                current += step;
                id = if step > 0 {
                    self.intern_node(vec![id], Vec::new())?
                } else {
                    self.intern_node(Vec::new(), vec![id])?
                };
                self.dyadics.insert(Dyadic::integer(current), id);
                if step > 0 {
                    self.integers.1 = current;
                } else {
                    self.integers.0 = current;
                }
            }
            id
        } else {
            // num / 2^k = {(num - 1) / 2^k | (num + 1) / 2^k} for odd num.
            self.charge(1)?;
            let half = d.num >> 1;
            let k = u128::from(d.k) - 1;
            let left = self.number(Dyadic::new(half, k)?)?;
            let right = self.number(Dyadic::new(half + 1, k)?)?;
            self.intern_node(vec![left], vec![right])?
        };
        self.dyadics.insert(d, id);
        Ok(id)
    }

    /// The game of a dyadic surreal; `None` for any other surreal.
    pub fn from_surreal(&mut self, s: &Surreal) -> Step<Option<GameId>> {
        match s.as_dyadic() {
            Some((num, k)) => self.dyadic(num, k).map(Some),
            None => Ok(None),
        }
    }

    /// The nimber `*n`. Building it costs `m + 1` steps for each `*m` not yet
    /// interned with `m <= n`.
    pub fn nimber(&mut self, n: u128) -> Step<GameId> {
        while self.nimbers.len() as u128 <= n {
            self.charge(self.nimbers.len() + 1)?;
            let options = self.nimbers.clone();
            let id = self.intern_node(options.clone(), options)?;
            self.nimbers.push(id);
        }
        Ok(self.nimbers[n as usize])
    }

    /// `↑ = {0 | *}`.
    pub fn up(&mut self) -> Step<GameId> {
        self.charge(2)?;
        let zero = self.zero();
        let star = self.intern_node(vec![zero], vec![zero])?;
        self.intern_node(vec![zero], vec![star])
    }

    /// `↓ = {* | 0}`.
    pub fn down(&mut self) -> Step<GameId> {
        self.charge(2)?;
        let zero = self.zero();
        let star = self.intern_node(vec![zero], vec![zero])?;
        self.intern_node(vec![star], vec![zero])
    }

    /// The number of distinct positions reachable from `g`, `g` included,
    /// counting at most `limit + 1`.
    pub fn positions(&self, g: GameId, limit: usize) -> usize {
        let mut seen = HashSet::from([g]);
        if seen.len() > limit {
            return seen.len();
        }
        let mut stack = vec![g];
        while let Some(node) = stack.pop() {
            let node = self.node(node);
            for &child in node.left.iter().chain(node.right.iter()) {
                if seen.insert(child) {
                    if seen.len() > limit {
                        return seen.len();
                    }
                    stack.push(child);
                }
            }
        }
        seen.len()
    }

    /// The canonical form of `{left | right}` for canonical options: dominated
    /// options are removed and reversible ones bypassed until stable. The
    /// supplied entries are charged before they are scanned.
    pub fn form(&mut self, left: &[GameId], right: &[GameId]) -> Step<GameId> {
        self.charge(left.len() + right.len())?;
        self.reduce(left, right)
    }

    /// [`form`](Self::form) for option lists built by charged arena work.
    fn reduce(&mut self, left: &[GameId], right: &[GameId]) -> Step<GameId> {
        let mut left = dedup(left);
        let mut right = dedup(right);
        loop {
            self.charge(1 + left.len() + right.len())?;
            left = self.extremal(left, true)?;
            right = self.extremal(right, false)?;
            let pending = Pending {
                left: &left,
                right: &right,
            };
            let (mut into, mut from) = (HashMap::new(), HashMap::new());
            let mut changed = false;
            let mut new_left = Vec::new();
            for &x in pending.left {
                let mut bypass = None;
                for i in 0..self.node(x).right.len() {
                    let xr = self.node(x).right[i];
                    if self.le_pending(xr, &pending, &mut into)? {
                        bypass = Some(xr);
                        break;
                    }
                }
                match bypass {
                    Some(xr) => {
                        changed = true;
                        new_left.extend_from_slice(&self.node(xr).left);
                    }
                    None => new_left.push(x),
                }
            }
            let mut new_right = Vec::new();
            for &y in pending.right {
                let mut bypass = None;
                for i in 0..self.node(y).left.len() {
                    let yl = self.node(y).left[i];
                    if self.pending_le(&pending, yl, &mut from)? {
                        bypass = Some(yl);
                        break;
                    }
                }
                match bypass {
                    Some(yl) => {
                        changed = true;
                        new_right.extend_from_slice(&self.node(yl).right);
                    }
                    None => new_right.push(y),
                }
            }
            if !changed {
                break;
            }
            left = dedup(&new_left);
            right = dedup(&new_right);
        }
        self.charge(1)?;
        self.intern_node(left, right)
    }
    /// The order-maximal (Left) or order-minimal (Right) options.
    fn extremal(&mut self, options: Vec<GameId>, maximal: bool) -> Step<Vec<GameId>> {
        let mut kept: Vec<GameId> = Vec::new();
        'candidates: for candidate in options {
            // Comparisons against numbers take no memo step, but still work.
            self.charge(1 + kept.len())?;
            for &k in &kept {
                let dominated = if maximal {
                    self.le(candidate, k)?
                } else {
                    self.le(k, candidate)?
                };
                if dominated {
                    continue 'candidates;
                }
            }
            let mut survivors = Vec::with_capacity(kept.len() + 1);
            for &k in &kept {
                let dominated = if maximal {
                    self.le(k, candidate)?
                } else {
                    self.le(candidate, k)?
                };
                if !dominated {
                    survivors.push(k);
                }
            }
            survivors.push(candidate);
            kept = survivors;
        }
        Ok(kept)
    }

    /// `a ≤ P` for a pending form `P`.
    fn le_pending(
        &mut self,
        a: GameId,
        pending: &Pending<'_>,
        memo: &mut HashMap<GameId, bool>,
    ) -> Step<bool> {
        if let Some(&answer) = memo.get(&a) {
            return Ok(answer);
        }
        self.charge(1 + self.node(a).left.len() + pending.right.len())?;
        let mut answer = true;
        for &pr in pending.right {
            if self.le(pr, a)? {
                answer = false;
                break;
            }
        }
        if answer {
            let mut from = HashMap::new();
            for i in 0..self.node(a).left.len() {
                let al = self.node(a).left[i];
                if self.pending_le(pending, al, &mut from)? {
                    answer = false;
                    break;
                }
            }
        }
        memo.insert(a, answer);
        Ok(answer)
    }

    /// `P ≤ b` for a pending form `P`.
    fn pending_le(
        &mut self,
        pending: &Pending<'_>,
        b: GameId,
        memo: &mut HashMap<GameId, bool>,
    ) -> Step<bool> {
        if let Some(&answer) = memo.get(&b) {
            return Ok(answer);
        }
        self.charge(1 + pending.left.len() + self.node(b).right.len())?;
        let mut answer = true;
        for &pl in pending.left {
            if self.le(b, pl)? {
                answer = false;
                break;
            }
        }
        if answer {
            let mut into = HashMap::new();
            for i in 0..self.node(b).right.len() {
                let br = self.node(b).right[i];
                if self.le_pending(br, pending, &mut into)? {
                    answer = false;
                    break;
                }
            }
        }
        memo.insert(b, answer);
        Ok(answer)
    }

    // ------------------------------------------------------------ operations

    /// `a ≤ b` in the game order.
    pub fn le(&mut self, a: GameId, b: GameId) -> Step<bool> {
        if a == b {
            return Ok(true);
        }
        if let (Some(x), Some(y)) = (self.node(a).number, self.node(b).number) {
            return Ok(x <= y);
        }
        if let Some(&answer) = self.le_memo.get(&(a, b)) {
            return Ok(answer);
        }
        self.charge(1 + self.node(a).left.len() + self.node(b).right.len())?;
        let mut answer = true;
        for i in 0..self.node(a).left.len() {
            let al = self.node(a).left[i];
            if self.le(b, al)? {
                answer = false;
                break;
            }
        }
        if answer {
            for i in 0..self.node(b).right.len() {
                let br = self.node(b).right[i];
                if self.le(br, a)? {
                    answer = false;
                    break;
                }
            }
        }
        self.le_memo.insert((a, b), answer);
        Ok(answer)
    }

    /// The four-way comparison: `Some(ordering)`, or `None` when fuzzy.
    pub fn compare(&mut self, a: GameId, b: GameId) -> Step<Option<Ordering>> {
        if a == b {
            return Ok(Some(Ordering::Equal));
        }
        Ok(match (self.le(a, b)?, self.le(b, a)?) {
            (true, true) => Some(Ordering::Equal),
            (true, false) => Some(Ordering::Less),
            (false, true) => Some(Ordering::Greater),
            (false, false) => None,
        })
    }

    /// The disjunctive sum.
    pub fn add(&mut self, a: GameId, b: GameId) -> Step<GameId> {
        let zero = self.zero();
        if a == zero {
            return Ok(b);
        }
        if b == zero {
            return Ok(a);
        }
        let key = if a.0 <= b.0 { (a, b) } else { (b, a) };
        if let Some(&sum) = self.sums.get(&key) {
            return Ok(sum);
        }
        let sum = match (self.node(a).number, self.node(b).number) {
            (Some(x), Some(y)) => self.number(x.add(y)?)?,
            (Some(_), None) => self.translate(b, a)?,
            (None, Some(_)) => self.translate(a, b)?,
            (None, None) => {
                let (na, nb) = (self.node(a), self.node(b));
                self.charge(1 + na.left.len() + na.right.len() + nb.left.len() + nb.right.len())?;
                let mut left = Vec::new();
                let mut right = Vec::new();
                for i in 0..self.node(a).left.len() {
                    let al = self.node(a).left[i];
                    left.push(self.add(al, b)?);
                }
                for i in 0..self.node(b).left.len() {
                    let bl = self.node(b).left[i];
                    left.push(self.add(a, bl)?);
                }
                for i in 0..self.node(a).right.len() {
                    let ar = self.node(a).right[i];
                    right.push(self.add(ar, b)?);
                }
                for i in 0..self.node(b).right.len() {
                    let br = self.node(b).right[i];
                    right.push(self.add(a, br)?);
                }
                self.reduce(&left, &right)?
            }
        };
        self.sums.insert(key, sum);
        Ok(sum)
    }

    /// `g + x` for a non-number `g` and a number `x`, by number translation.
    fn translate(&mut self, g: GameId, x: GameId) -> Step<GameId> {
        self.charge(1 + self.node(g).left.len() + self.node(g).right.len())?;
        let mut left = Vec::new();
        let mut right = Vec::new();
        for i in 0..self.node(g).left.len() {
            let gl = self.node(g).left[i];
            left.push(self.add(gl, x)?);
        }
        for i in 0..self.node(g).right.len() {
            let gr = self.node(g).right[i];
            right.push(self.add(gr, x)?);
        }
        self.reduce(&left, &right)
    }

    /// The negative. Negation preserves canonical form.
    pub fn neg(&mut self, a: GameId) -> Step<GameId> {
        if let Some(&negated) = self.negs.get(&a) {
            return Ok(negated);
        }
        let negated = if let Some(x) = self.node(a).number {
            self.number(x.neg()?)?
        } else {
            self.charge(1 + self.node(a).left.len() + self.node(a).right.len())?;
            let mut left = Vec::new();
            let mut right = Vec::new();
            for i in 0..self.node(a).right.len() {
                let ar = self.node(a).right[i];
                left.push(self.neg(ar)?);
            }
            for i in 0..self.node(a).left.len() {
                let al = self.node(a).left[i];
                right.push(self.neg(al)?);
            }
            self.intern_node(left, right)?
        };
        self.negs.insert(a, negated);
        self.negs.insert(negated, a);
        Ok(negated)
    }

    /// Canonicalize and intern an engine game. Each distinct subtree is charged
    /// before it is visited, then reduced as by [`form`](Self::form).
    pub fn intern(&mut self, game: &Game) -> Step<GameId> {
        fn visit(
            arena: &mut GameArena,
            game: &Game,
            memo: &mut HashMap<usize, GameId>,
        ) -> Step<GameId> {
            if let Some(&id) = memo.get(&game.ptr_id()) {
                return Ok(id);
            }
            arena.charge(1 + game.left().len() + game.right().len())?;
            let left = game
                .left()
                .iter()
                .map(|option| visit(arena, option, memo))
                .collect::<Step<Vec<_>>>()?;
            let right = game
                .right()
                .iter()
                .map(|option| visit(arena, option, memo))
                .collect::<Step<Vec<_>>>()?;
            let id = arena.reduce(&left, &right)?;
            memo.insert(game.ptr_id(), id);
            Ok(id)
        }
        visit(self, game, &mut HashMap::new())
    }

    /// The canonical form as an engine game, sharing common subgames.
    /// Unmetered; each node is exported once per arena.
    pub fn to_game(&mut self, g: GameId) -> Game {
        if let Some(game) = &self.games[g.index()] {
            return game.clone();
        }
        let left = (0..self.node(g).left.len())
            .map(|i| {
                let child = self.node(g).left[i];
                self.to_game(child)
            })
            .collect();
        let right = (0..self.node(g).right.len())
            .map(|i| {
                let child = self.node(g).right[i];
                self.to_game(child)
            })
            .collect();
        let game = Game::new(left, right);
        self.games[g.index()] = Some(game.clone());
        game
    }
}

fn dedup(ids: &[GameId]) -> Vec<GameId> {
    let mut seen = HashSet::new();
    ids.iter().copied().filter(|id| seen.insert(*id)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::Rational;

    /// A deterministic xorshift for reproducible random games.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    /// Random non-canonical games: each new game picks up to three Left and
    /// three Right options from the games built so far.
    fn random_games(seed: u64, count: usize) -> Vec<Game> {
        let mut rng = Rng(seed);
        let mut pool = vec![Game::zero()];
        while pool.len() < count {
            let pick = |rng: &mut Rng| {
                (0..rng.below(4))
                    .map(|_| pool[rng.below(pool.len())].clone())
                    .collect::<Vec<_>>()
            };
            let left = pick(&mut rng);
            let right = pick(&mut rng);
            pool.push(Game::new(left, right));
        }
        pool
    }

    fn same(arena: &mut GameArena, id: GameId, game: &Game) -> bool {
        arena.to_game(id).structural_eq(&game.canonical())
    }

    #[test]
    fn builders_match_engine_canonical_forms() {
        let mut arena = GameArena::new();
        for n in [-7, -1, 0, 1, 5, 12] {
            let id = arena.integer(n).unwrap();
            assert!(same(&mut arena, id, &Game::integer(n)), "integer {n}");
            assert_eq!(arena.birthday(id), n.unsigned_abs());
        }
        for (num, den) in [(1, 2), (-3, 4), (5, 8), (7, 2), (-1, 16)] {
            let s = Surreal::from_rational(Rational::new(num, den));
            let id = arena.from_surreal(&s).unwrap().unwrap();
            assert!(same(&mut arena, id, &Game::from_surreal(&s).unwrap()));
            assert_eq!(arena.number_value(id), Some(s.clone()));
        }
        for n in 0..9 {
            let id = arena.nimber(n).unwrap();
            assert!(same(&mut arena, id, &Game::nim_heap(n)), "nimber {n}");
            assert_eq!(arena.nimber_value(id), Some(n));
        }
        let up = arena.up().unwrap();
        assert!(same(&mut arena, up, &Game::up()));
        let down = arena.down().unwrap();
        assert!(same(&mut arena, down, &Game::up().neg()));
        assert_eq!(arena.neg(up).unwrap(), down);
    }

    #[test]
    fn interning_matches_engine_canonical_form() {
        let games = random_games(0x9e37_79b9_7f4a_7c15, 120);
        let mut arena = GameArena::new();
        for game in &games {
            let id = arena.intern(game).unwrap();
            assert!(same(&mut arena, id, game), "{game}");
            assert_eq!(arena.number_value(id), game.canonical().number_value());
            assert_eq!(arena.birthday(id), game.canonical().birthday());
        }
    }

    #[test]
    fn order_sum_and_negation_match_the_engine() {
        let games = random_games(0x2545_f491_4f6c_dd1d, 60);
        let mut arena = GameArena::new();
        let ids: Vec<GameId> = games.iter().map(|g| arena.intern(g).unwrap()).collect();
        for (i, g) in games.iter().enumerate().step_by(3) {
            let negated = arena.neg(ids[i]).unwrap();
            assert!(same(&mut arena, negated, &g.neg()));
            for (j, h) in games.iter().enumerate().step_by(5) {
                assert_eq!(arena.le(ids[i], ids[j]).unwrap(), g.le(h), "{g} ≤ {h}");
                let sum = arena.add(ids[i], ids[j]).unwrap();
                assert!(same(&mut arena, sum, &g.add(h)), "{g} + {h}");
            }
        }
    }

    #[test]
    fn equal_values_share_one_id() {
        let mut arena = GameArena::new();
        let star = arena.nimber(1).unwrap();
        let two_stars = arena.add(star, star).unwrap();
        assert_eq!(two_stars, arena.zero());
        let one = arena.integer(1).unwrap();
        let half = arena.dyadic(1, 1).unwrap();
        assert_eq!(arena.add(half, half).unwrap(), one);
        let s28 = arena.nimber(28).unwrap();
        let s3 = arena.nimber(3).unwrap();
        assert_eq!(arena.add(s28, s3).unwrap(), arena.nimber(31).unwrap());
    }

    #[test]
    fn large_number_sums_stay_cheap() {
        let mut arena = GameArena::new();
        arena.set_budget(Some(100_000));
        let a = arena.integer(1000).unwrap();
        let star = arena.nimber(1).unwrap();
        let sum = arena.add(a, a).unwrap();
        assert_eq!(arena.number_value(sum), Some(Surreal::from(2000)));
        let a_star = arena.add(a, star).unwrap();
        let twice = arena.add(a_star, a).unwrap();
        let expected = arena.integer(2000).unwrap();
        assert_eq!(twice, arena.add(expected, star).unwrap());
        assert!(arena.budget().unwrap() > 0);
    }

    #[test]
    fn exhaustion_fails_and_leaves_the_arena_consistent() {
        let mut arena = GameArena::new();
        arena.set_budget(Some(10));
        assert_eq!(arena.nimber(40), Err(ArenaError::BudgetExhausted));
        assert_eq!(arena.budget(), Some(0));
        arena.set_budget(None);
        let games = random_games(7, 40);
        let ids: Vec<GameId> = games.iter().map(|g| arena.intern(g).unwrap()).collect();
        arena.set_budget(Some(25));
        let _ = arena.add(ids[39], ids[38]);
        arena.set_budget(None);
        for (i, g) in games.iter().enumerate().skip(30) {
            for (j, h) in games.iter().enumerate().skip(30) {
                assert_eq!(arena.le(ids[i], ids[j]).unwrap(), g.le(h));
                let sum = arena.add(ids[i], ids[j]).unwrap();
                assert!(same(&mut arena, sum, &g.add(h)));
            }
        }
    }

    /// Every reduced dyadic `num / 2^k` with `|num| < 2^(k + 2)` and `k <= 3`.
    fn small_dyadics() -> Vec<Dyadic> {
        let mut out = Vec::new();
        for k in 0..=3u128 {
            let bound = 1i128 << (k + 2);
            for num in -bound..=bound {
                let d = Dyadic::new(num, k).unwrap();
                if !out.contains(&d) {
                    out.push(d);
                }
            }
        }
        out
    }

    fn rational(d: Dyadic) -> Rational {
        Rational::new(d.num, 1 << d.k)
    }

    #[test]
    fn dyadic_arithmetic_matches_rational_and_surreal_oracles() {
        let values = small_dyadics();
        for &x in &values {
            assert_eq!(rational(x.neg().unwrap()), -rational(x));
            let above = x.to_surreal().simplest_above().unwrap();
            assert_eq!(x.simplest_above().unwrap().to_surreal(), above);
            let below = x.to_surreal().simplest_below().unwrap();
            assert_eq!(x.simplest_below().unwrap().to_surreal(), below);
            for &y in &values {
                assert_eq!(x.cmp(&y), rational(x).cmp(&rational(y)), "{x:?} vs {y:?}");
                assert_eq!(rational(x.add(y).unwrap()), rational(x) + rational(y));
                if x < y {
                    let expected = Surreal::simplest_between(&x.to_surreal(), &y.to_surreal());
                    assert_eq!(
                        Some(Dyadic::simplest_between(x, y).unwrap().to_surreal()),
                        expected,
                        "simplest between {x:?} and {y:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn dyadics_near_the_range_edge_are_exact_or_refused() {
        let mut arena = GameArena::new();
        let tiny = arena.dyadic(1, 126).unwrap();
        let two = arena.integer(2).unwrap();
        assert!(!arena.le(two, tiny).unwrap());
        assert!(arena.le(tiny, two).unwrap());
        // x = 1 + 2^-126 doubles to (2^126 + 1) / 2^125, whose unreduced
        // numerator overflows i128.
        let one = arena.integer(1).unwrap();
        let x = arena.add(one, tiny).unwrap();
        let doubled = arena.add(x, x).unwrap();
        assert_eq!(
            arena.number_value(doubled),
            Some(Surreal::from_rational(Rational::new(
                (1 << 126) + 1,
                1 << 125
            )))
        );
        assert_eq!(arena.dyadic(1, 127), Err(ArenaError::NumberOutOfRange));
        // 2 - 2^-126 = (2^127 - 1) / 2^126: the aligned 2 * 2^126 leaves i128,
        // the sum does not.
        let neg_tiny = arena.dyadic(-1, 126).unwrap();
        let sum = arena.add(two, neg_tiny).unwrap();
        assert_eq!(
            arena.number_value(sum),
            Some(Surreal::from_rational(Rational::new(i128::MAX, 1 << 126)))
        );
        assert_eq!(arena.dyadic(i128::MAX, 126).map(|_| ()), Ok(()));
        // {0 | 2^-126} is the number 2^-127, outside the range.
        let zero = arena.zero();
        assert_eq!(
            arena.form(&[zero], &[tiny]),
            Err(ArenaError::NumberOutOfRange)
        );
        // Large exponents of zero and even numerators reduce in constant time.
        arena.set_budget(Some(0));
        assert_eq!(arena.dyadic(0, u128::MAX), Ok(zero));
        assert_eq!(arena.dyadic(1 << 100, 100), Ok(one));
    }

    #[test]
    fn budgets_bound_work_before_it_is_done() {
        let mut arena = GameArena::new();
        // Each level of a dyadic is charged before it recurses.
        arena.set_budget(Some(20));
        assert_eq!(arena.dyadic(1, 120), Err(ArenaError::BudgetExhausted));
        // Supplied option lists are charged before they are scanned.
        arena.set_budget(Some(100));
        let zero = arena.zero();
        assert_eq!(
            arena.form(&vec![zero; 1000], &[]),
            Err(ArenaError::BudgetExhausted)
        );
        // Interning charges each subtree before descending into it.
        let mut chain = Game::zero();
        for _ in 0..2000 {
            chain = Game::new(vec![chain.clone()], vec![chain]);
        }
        arena.set_budget(Some(100));
        assert_eq!(arena.intern(&chain), Err(ArenaError::BudgetExhausted));
        assert_eq!(arena.budget(), Some(0));
    }

    #[test]
    fn positions_caps_its_count() {
        let mut arena = GameArena::new();
        let star10 = arena.nimber(10).unwrap();
        assert_eq!(arena.positions(star10, 0), 1);
        assert_eq!(arena.positions(star10, 1), 2);
        assert_eq!(arena.positions(star10, 5), 6);
        assert_eq!(arena.positions(star10, 100), 11);
    }

    #[test]
    fn shl_add_is_exact_at_the_i128_edge() {
        for a in [-5i128, -1, 0, 1, 3, 1 << 60, -(1 << 60)] {
            for shift in [1u32, 7, 60] {
                for b in [-7i128, -1, 0, 1, 9] {
                    let exact = a.checked_mul(1 << shift).and_then(|x| x.checked_add(b));
                    assert_eq!(shl_add(a, shift, b), exact, "{a} << {shift} + {b}");
                }
            }
        }
        assert_eq!(shl_add(2, 126, -1), Some(i128::MAX));
        assert_eq!(shl_add(-2, 126, 0), Some(i128::MIN));
        assert_eq!(shl_add(2, 126, 0), None);
        assert_eq!(shl_add(-2, 126, -1), None);
        // 3 * 2^126 leaves i128; subtracting 2^126 + 1 lands on i128::MAX.
        assert_eq!(shl_add(3, 126, -(1 << 126) - 1), Some(i128::MAX));
        assert_eq!(shl_add(i128::MAX, 127, 0), None);
        assert_eq!(shl_add(-1, 127, 0), Some(i128::MIN));
    }
}
