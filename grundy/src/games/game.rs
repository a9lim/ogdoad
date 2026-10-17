//! `Game`: short game values held in sealed canonical form.
//!
//! Every value is canonicalized and hash-consed in a per-thread interner, so
//! equality and hashing are id comparisons, and options are sorted by a
//! deterministic structural order independent of allocation and discovery
//! order. Every operation is therefore a function of the value.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

use ogdoad::games::Game;
use ogdoad::scalar::{Rational, Surreal};

use super::super::error::{err, GrundyErrorKind, GrundyResult};

/// A sealed canonical short game.
#[derive(Clone)]
pub struct GameV {
    id: u32,
}

struct Node {
    game: Game,
    left: Rc<[u32]>,
    right: Rc<[u32]>,
    birthday: u32,
}

/// Sorted Left and Right option ids of a canonical node.
type Children = (Rc<[u32]>, Rc<[u32]>);

#[derive(Default)]
struct Interner {
    nodes: Vec<Node>,
    by_children: HashMap<Children, u32>,
    order: HashMap<(u32, u32), Ordering>,
}

thread_local! {
    static INTERNER: RefCell<Interner> = RefCell::new(Interner::default());
}

impl Interner {
    fn cmp(&mut self, a: u32, b: u32) -> Ordering {
        if a == b {
            return Ordering::Equal;
        }
        if let Some(ordering) = self.order.get(&(a, b)) {
            return *ordering;
        }
        let (na, nb) = (&self.nodes[a as usize], &self.nodes[b as usize]);
        let mut ordering = na
            .birthday
            .cmp(&nb.birthday)
            .then(na.left.len().cmp(&nb.left.len()))
            .then(na.right.len().cmp(&nb.right.len()));
        if ordering == Ordering::Equal {
            let (la, lb) = (na.left.clone(), nb.left.clone());
            let (ra, rb) = (na.right.clone(), nb.right.clone());
            for (x, y) in la.iter().zip(lb.iter()).chain(ra.iter().zip(rb.iter())) {
                ordering = self.cmp(*x, *y);
                if ordering != Ordering::Equal {
                    break;
                }
            }
        }
        self.order.insert((a, b), ordering);
        self.order.insert((b, a), ordering.reverse());
        ordering
    }

    fn intern_canonical(&mut self, game: &Game, memo: &mut HashMap<usize, u32>) -> u32 {
        if let Some(&id) = memo.get(&game.ptr_id()) {
            return id;
        }
        let mut left: Vec<u32> = game
            .left()
            .iter()
            .map(|option| self.intern_canonical(option, memo))
            .collect();
        let mut right: Vec<u32> = game
            .right()
            .iter()
            .map(|option| self.intern_canonical(option, memo))
            .collect();
        left.sort_by(|a, b| self.cmp(*a, *b));
        right.sort_by(|a, b| self.cmp(*a, *b));
        left.dedup();
        right.dedup();
        let key: Children = (left.into(), right.into());
        let id = match self.by_children.get(&key) {
            Some(&id) => id,
            None => {
                let birthday = key
                    .0
                    .iter()
                    .chain(key.1.iter())
                    .map(|child| self.nodes[*child as usize].birthday + 1)
                    .max()
                    .unwrap_or(0);
                let rebuilt = Game::new(
                    key.0
                        .iter()
                        .map(|child| self.nodes[*child as usize].game.clone())
                        .collect(),
                    key.1
                        .iter()
                        .map(|child| self.nodes[*child as usize].game.clone())
                        .collect(),
                );
                let id = self.nodes.len() as u32;
                self.nodes.push(Node {
                    game: rebuilt,
                    left: key.0.clone(),
                    right: key.1.clone(),
                    birthday,
                });
                self.by_children.insert(key, id);
                id
            }
        };
        memo.insert(game.ptr_id(), id);
        id
    }
}

fn with<R>(f: impl FnOnce(&mut Interner) -> R) -> R {
    INTERNER.with(|interner| f(&mut interner.borrow_mut()))
}

impl GameV {
    /// Seal a game: canonicalize and intern it.
    pub fn seal(game: &Game) -> GameV {
        let canonical = game.canonical();
        let id = with(|interner| interner.intern_canonical(&canonical, &mut HashMap::new()));
        GameV { id }
    }

    /// The underlying canonical engine game.
    pub fn game(&self) -> Game {
        with(|interner| interner.nodes[self.id as usize].game.clone())
    }

    /// The integer `n`.
    pub fn integer(n: i128) -> GameV {
        GameV::seal(&Game::integer(n))
    }

    /// The nimber `*n`.
    pub fn nimber(n: u128) -> GameV {
        GameV::seal(&Game::nim_heap(n))
    }

    /// The dyadic `num/den` in lowest terms.
    pub fn dyadic(num: i128, den: u128) -> GrundyResult<GameV> {
        if den == 0 {
            return Err(err(GrundyErrorKind::DivisionByZero, "zero denominator"));
        }
        let den = i128::try_from(den)
            .map_err(|_| err(GrundyErrorKind::Overflow, "denominator exceeds i128"))?;
        let value = Surreal::from_rational(Rational::new(num, den));
        Game::from_surreal(&value)
            .map(|game| GameV::seal(&game))
            .ok_or_else(|| {
                err(
                    GrundyErrorKind::Domain,
                    format!("{num}/{den} is not a dyadic rational"),
                )
                .with_hint("only dyadics are short games; `1/3` is not born on any finite day")
            })
    }

    /// `up` (or `down`).
    pub fn up(down: bool) -> GameV {
        let up = GameV::seal(&Game::up());
        if down {
            up.neg()
        } else {
            up
        }
    }

    /// Build `{L | R}` from sealed options.
    pub fn form(left: &[GameV], right: &[GameV]) -> GameV {
        GameV::seal(&Game::new(
            left.iter().map(GameV::game).collect(),
            right.iter().map(GameV::game).collect(),
        ))
    }

    /// The disjunctive sum.
    pub fn add(&self, other: &GameV) -> GameV {
        GameV::seal(&self.game().add(&other.game()))
    }

    /// The negative.
    pub fn neg(&self) -> GameV {
        GameV::seal(&self.game().neg())
    }

    /// `self ≤ other` in the game order.
    pub fn le(&self, other: &GameV) -> bool {
        self.id == other.id || self.game().le(&other.game())
    }

    /// The four-way comparison: `Some(ordering)` or `None` for fuzzy.
    pub fn compare(&self, other: &GameV) -> Option<Ordering> {
        if self.id == other.id {
            return Some(Ordering::Equal);
        }
        match (self.le(other), other.le(self)) {
            (true, true) => Some(Ordering::Equal),
            (true, false) => Some(Ordering::Less),
            (false, true) => Some(Ordering::Greater),
            (false, false) => None,
        }
    }

    /// The deterministic structural order (also the `Key` order).
    pub fn structural_cmp(&self, other: &GameV) -> Ordering {
        with(|interner| interner.cmp(self.id, other.id))
    }

    /// Value equality (an id comparison).
    pub fn same(&self, other: &GameV) -> bool {
        self.id == other.id
    }

    /// The interned id (a value key within one session).
    pub fn id(&self) -> u32 {
        self.id
    }

    /// Canonical Left options in structural order.
    pub fn lefts(&self) -> Vec<GameV> {
        with(|interner| {
            interner.nodes[self.id as usize]
                .left
                .iter()
                .map(|id| GameV { id: *id })
                .collect()
        })
    }

    /// Canonical Right options in structural order.
    pub fn rights(&self) -> Vec<GameV> {
        with(|interner| {
            interner.nodes[self.id as usize]
                .right
                .iter()
                .map(|id| GameV { id: *id })
                .collect()
        })
    }

    /// The value birthday.
    pub fn birthday(&self) -> u32 {
        with(|interner| interner.nodes[self.id as usize].birthday)
    }

    /// The number value, if the game is a number.
    pub fn number(&self) -> Option<Surreal> {
        self.game().number_value()
    }

    /// `n` if the canonical form is the nimber `*n`.
    pub fn as_nimber(&self) -> Option<u128> {
        let left = self.lefts();
        let right = self.rights();
        if left.len() != right.len() || left.iter().zip(&right).any(|(a, b)| !a.same(b)) {
            return None;
        }
        // Options of *n are exactly *0 … *(n-1), each a nimber.
        let mut seen = vec![false; left.len()];
        for option in &left {
            let k = option.as_nimber()?;
            let k = usize::try_from(k).ok()?;
            if k >= seen.len() || seen[k] {
                return None;
            }
            seen[k] = true;
        }
        Some(left.len() as u128)
    }

    /// Canonical display: integers, dyadics, nimbers, `up`/`down`, and braces
    /// otherwise.
    pub fn display(&self) -> String {
        if let Some(surreal) = self.number() {
            if let Some((num, k)) = surreal.as_dyadic() {
                return if k == 0 {
                    num.to_string()
                } else {
                    format!("{num}/{}", 1u128 << k)
                };
            }
        }
        if let Some(n) = self.as_nimber() {
            return format!("*{n}");
        }
        if self.same(&GameV::up(false)) {
            return "up".to_string();
        }
        if self.same(&GameV::up(true)) {
            return "down".to_string();
        }
        let side = |options: Vec<GameV>| {
            options
                .iter()
                .map(GameV::display_option)
                .collect::<Vec<_>>()
                .join(", ")
        };
        let left = side(self.lefts());
        let right = side(self.rights());
        match (left.is_empty(), right.is_empty()) {
            (true, true) => "{|}".to_string(),
            (false, true) => format!("{{{left} |}}"),
            (true, false) => format!("{{| {right}}}"),
            (false, false) => format!("{{{left} | {right}}}"),
        }
    }

    fn display_option(&self) -> String {
        self.display()
    }
}
