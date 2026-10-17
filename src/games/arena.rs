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
//! Every memo miss charges one step plus the options it scans against an
//! optional budget. An operation that would exceed the budget fails with
//! [`ArenaExhausted`], and every memo entry it recorded stays valid.
//!
//! Recursion depth is proportional to the birthdays involved, as it is for
//! [`Game`]. Callers that admit arbitrary inputs bound birthdays themselves.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;

use crate::games::Game;
use crate::scalar::{Scalar, Surreal};

/// A canonical game in a [`GameArena`]. Within one arena, equal ids are
/// exactly equal values.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GameId(u32);

impl GameId {
    /// The allocation index. It depends on construction order, not on the
    /// value; use [`GameArena::structural_cmp`] for a deterministic order.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// An arena operation exceeded its step budget.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ArenaExhausted;

impl fmt::Display for ArenaExhausted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "the game arena's step budget is exhausted")
    }
}

impl std::error::Error for ArenaExhausted {}

type Step<T> = Result<T, ArenaExhausted>;

/// Sorted Left and Right option ids of a canonical node.
type Children = (Box<[GameId]>, Box<[GameId]>);

struct Node {
    left: Box<[GameId]>,
    right: Box<[GameId]>,
    birthday: u128,
    number: Option<Surreal>,
    nimber: Option<u128>,
}

/// The options of a form that is being canonicalized and is not yet interned.
struct Pending<'a> {
    left: &'a [GameId],
    right: &'a [GameId],
}

/// Canonical short games, interned once, with persistent order, sum, and
/// negation memos.
pub struct GameArena {
    nodes: Vec<Node>,
    by_children: HashMap<Children, GameId>,
    dyadics: HashMap<(i128, u128), GameId>,
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
        let zero = arena.intern_node(Vec::new(), Vec::new());
        arena.dyadics.insert((0, 0), zero);
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
                return Err(ArenaExhausted);
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
    pub fn number_value(&self, g: GameId) -> Option<&Surreal> {
        self.node(g).number.as_ref()
    }

    /// `n` if the game is the nimber `*n`.
    pub fn nimber_value(&self, g: GameId) -> Option<u128> {
        self.node(g).nimber
    }

    /// A deterministic total order on canonical forms, independent of
    /// construction order: birthday, then option counts, then options in order.
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
    /// have no dominated or reversible option.
    fn intern_node(&mut self, mut left: Vec<GameId>, mut right: Vec<GameId>) -> GameId {
        left.sort_by(|a, b| self.structural_cmp(*a, *b));
        left.dedup();
        right.sort_by(|a, b| self.structural_cmp(*a, *b));
        right.dedup();
        let key = (left.into_boxed_slice(), right.into_boxed_slice());
        if let Some(&id) = self.by_children.get(&key) {
            return id;
        }
        let birthday = key
            .0
            .iter()
            .chain(key.1.iter())
            .map(|child| self.node(*child).birthday + 1)
            .max()
            .unwrap_or(0);
        let number = self.number_of(&key.0, &key.1);
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
        id
    }

    /// The simplicity theorem on options whose values are known.
    fn number_of(&self, left: &[GameId], right: &[GameId]) -> Option<Surreal> {
        let values = |side: &[GameId]| -> Option<Vec<Surreal>> {
            side.iter()
                .map(|child| self.node(*child).number.clone())
                .collect()
        };
        let (lvals, rvals) = (values(left)?, values(right)?);
        let lmax = lvals.into_iter().max();
        let rmin = rvals.into_iter().min();
        match (lmax, rmin) {
            (None, None) => Some(Surreal::zero()),
            (Some(l), None) => l.simplest_above(),
            (None, Some(r)) => r.simplest_below(),
            (Some(l), Some(r)) => Surreal::simplest_between(&l, &r),
        }
    }

    // -------------------------------------------------------------- builders

    /// The integer `n`.
    pub fn integer(&mut self, n: i128) -> Step<GameId> {
        self.dyadic(n, 0)
    }

    /// The dyadic `num / 2^k`.
    pub fn dyadic(&mut self, num: i128, k: u128) -> Step<GameId> {
        let (num, k) = reduce_dyadic(num, k);
        if let Some(&id) = self.dyadics.get(&(num, k)) {
            return Ok(id);
        }
        let id = if k == 0 {
            // Extend the integer chain outward from its built end.
            let (step, mut current): (i128, i128) = if num > 0 {
                (1, self.integers.1)
            } else {
                (-1, self.integers.0)
            };
            let mut id = self.dyadics[&(current, 0)];
            while current != num {
                self.charge(1)?;
                current += step;
                id = if step > 0 {
                    self.intern_node(vec![id], Vec::new())
                } else {
                    self.intern_node(Vec::new(), vec![id])
                };
                self.dyadics.insert((current, 0), id);
                if step > 0 {
                    self.integers.1 = current;
                } else {
                    self.integers.0 = current;
                }
            }
            id
        } else {
            let below = num
                .checked_sub(1)
                .expect("dyadic numerator overflowed i128");
            let above = num
                .checked_add(1)
                .expect("dyadic numerator overflowed i128");
            let (ln, lk) = reduce_dyadic(below, k);
            let (rn, rk) = reduce_dyadic(above, k);
            let left = self.dyadic(ln, lk)?;
            let right = self.dyadic(rn, rk)?;
            self.charge(1)?;
            self.intern_node(vec![left], vec![right])
        };
        self.dyadics.insert((num, k), id);
        Ok(id)
    }

    /// The game of a dyadic surreal; `None` for any other surreal.
    pub fn from_surreal(&mut self, s: &Surreal) -> Step<Option<GameId>> {
        match s.as_dyadic() {
            Some((num, k)) => self.dyadic(num, k).map(Some),
            None => Ok(None),
        }
    }

    /// The nimber `*n`.
    pub fn nimber(&mut self, n: u128) -> Step<GameId> {
        while self.nimbers.len() as u128 <= n {
            let options = self.nimbers.clone();
            self.charge(options.len() + 1)?;
            let id = self.intern_node(options.clone(), options);
            self.nimbers.push(id);
        }
        Ok(self.nimbers[n as usize])
    }

    /// `↑ = {0 | *}`.
    pub fn up(&mut self) -> Step<GameId> {
        self.charge(2)?;
        let zero = self.zero();
        let star = self.intern_node(vec![zero], vec![zero]);
        Ok(self.intern_node(vec![zero], vec![star]))
    }

    /// `↓ = {* | 0}`.
    pub fn down(&mut self) -> Step<GameId> {
        self.charge(2)?;
        let zero = self.zero();
        let star = self.intern_node(vec![zero], vec![zero]);
        Ok(self.intern_node(vec![star], vec![zero]))
    }

    /// The number of distinct positions reachable from `g`, counting at
    /// most `limit + 1`.
    pub fn positions(&self, g: GameId, limit: usize) -> usize {
        let mut seen = std::collections::HashSet::from([g]);
        let mut stack = vec![g];
        while let Some(node) = stack.pop() {
            if seen.len() > limit {
                break;
            }
            for &child in self
                .node(node)
                .left
                .iter()
                .chain(self.node(node).right.iter())
            {
                if seen.insert(child) {
                    stack.push(child);
                }
            }
        }
        seen.len()
    }

    /// The canonical form of `{left | right}` for canonical options: dominated
    /// options are removed and reversible ones bypassed until stable.
    pub fn form(&mut self, left: &[GameId], right: &[GameId]) -> Step<GameId> {
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
        Ok(self.intern_node(left, right))
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
        if let (Some(x), Some(y)) = (&self.node(a).number, &self.node(b).number) {
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
        let key = if a <= b { (a, b) } else { (b, a) };
        if let Some(&sum) = self.sums.get(&key) {
            return Ok(sum);
        }
        let numbers = (self.node(a).number.clone(), self.node(b).number.clone());
        let sum = match numbers {
            (Some(x), Some(y)) => {
                let (num, k) = Scalar::add(&x, &y)
                    .as_dyadic()
                    .expect("a sum of dyadics is dyadic");
                self.dyadic(num, k)?
            }
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
                self.form(&left, &right)?
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
        self.form(&left, &right)
    }

    /// The negative. Negation preserves canonical form.
    pub fn neg(&mut self, a: GameId) -> Step<GameId> {
        if let Some(&negated) = self.negs.get(&a) {
            return Ok(negated);
        }
        let negated = if let Some(x) = self.node(a).number.clone() {
            let (num, k) = x.neg().as_dyadic().expect("a negated dyadic is dyadic");
            self.dyadic(num, k)?
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
            self.intern_node(left, right)
        };
        self.negs.insert(a, negated);
        self.negs.insert(negated, a);
        Ok(negated)
    }

    /// Canonicalize and intern an engine game.
    pub fn intern(&mut self, game: &Game) -> Step<GameId> {
        fn visit(
            arena: &mut GameArena,
            game: &Game,
            memo: &mut HashMap<usize, GameId>,
        ) -> Step<GameId> {
            if let Some(&id) = memo.get(&game.ptr_id()) {
                return Ok(id);
            }
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
            let id = arena.form(&left, &right)?;
            memo.insert(game.ptr_id(), id);
            Ok(id)
        }
        visit(self, game, &mut HashMap::new())
    }

    /// The canonical form as an engine game, sharing common subgames.
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

fn reduce_dyadic(mut num: i128, mut k: u128) -> (i128, u128) {
    while k > 0 && num % 2 == 0 {
        num /= 2;
        k -= 1;
    }
    if num == 0 {
        k = 0;
    }
    (num, k)
}

fn dedup(ids: &[GameId]) -> Vec<GameId> {
    let mut seen = std::collections::HashSet::new();
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
            assert_eq!(arena.number_value(id), Some(&s));
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
            assert_eq!(
                arena.number_value(id).cloned(),
                game.canonical().number_value()
            );
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
        assert_eq!(arena.number_value(sum), Some(&Surreal::from(2000)));
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
        assert_eq!(arena.nimber(40), Err(ArenaExhausted));
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
}
