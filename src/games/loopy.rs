//! Loopy combinatorial games — games whose move graph may contain cycles, so
//! play need not terminate. This is the third escape (beside the interactive
//! [`kernel`] route and the [`misere`](crate::games::misere)
//! route) from the XOR-linear P-sets of normal-play disjunctive sums: a cyclic
//! rule admits a **Draw** outcome — a position from which neither player can force
//! a win — and the Draw-set is a genuinely new degree of freedom to test against
//! the Gold quadric `{Q=0}` (see `OPEN.md`, the Tier-2 open question).
//!
//! Four layers, in weight order:
//!
//!   1. [`LoopyGraph`] — the graph-level engine. A thin, fully-computable wrapper
//!      over [`kernel::outcomes`](crate::games::outcomes), which already performs
//!      retrograde Win/Loss/**Draw** analysis on cyclic graphs. This is the
//!      load-bearing part.
//!   2. [`LoopyPartizanGraph`] — the two-sided Left/Right engine. This keeps the
//!      two starting-player questions separate, so values such as `tis`/`tisn` do
//!      not get flattened into the five classical partizan outcome classes.
//!   3. [`loopy_nim_values`] — the impartial loopy nim-values: Draw positions are
//!      `Side` (the loopy `∞`), the rest carry an ordinary nimber. Acyclic
//!      non-Draw regions use the usual DAG recursion; small cyclic non-Draw
//!      regions use a bounded sidling solver for the finite mex equations, and
//!      the certificate records the checked recovery condition used for additive
//!      claims.
//!   4. [`LoopyValue`] — a small catalogue of canonical named loopy values
//!      (`on`, `off`, `over`, `under`, `dud`, `±`, `tis`, `tisn`, `∗`) plus
//!      integer onside/offside `s&t` tags, with exact two-sided outcomes,
//!      negation, conservative partial order, and the partial sum-monoid. A finite
//!      tag carrying an infinite object — the same discipline as
//!      [`NumberGame`](crate::games::NumberGame).
//!
//! And the payoff for this project, [`loopy_decision_sets`] / [`loopy_quadric_probe`]:
//! take an arbitrary cyclic move rule on positions `F₂^k` and read off **both** its
//! Loss-set and its Draw-set, fitting each with
//! [`fit_f2_quadratic`]. A B-coupled cyclic rule
//! whose *Draw-set* is `{Q=0}` would be a Tier-2 witness even if its Loss-set is
//! not — structurally impossible for the acyclic `interactive_kernel` probe.
//!
//! Deliberately **out of scope** here: [`Game`](crate::games::Game) stays an acyclic
//! `Arc` tree (it cannot represent cycles, by construction), and
//! [`thermography`](crate::games::thermography) stays finite-game-only — loopy games
//! never freeze to a number, so classical temperature does not apply. The sidling
//! support below is still finite and certified: over-budget or non-canonical
//! fixed-point systems return `None` rather than pretending to be full loopy-game
//! equality.

use std::cmp::Ordering;
use std::collections::VecDeque;

use crate::forms::{fit_f2_quadratic, QuadricFit};
use crate::games::grundy::mex;
use crate::games::kernel::{self, Outcome};

const MAX_SIDLING_ASSIGNMENTS: usize = 200_000;

// ---------------------------------------------------------------------------
// 1. The canonical-stopper catalogue.
// ---------------------------------------------------------------------------

/// The winner of one of the two starter questions in a finite loopy partizan
/// graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LoopyWinner {
    /// Left can force a win from this starter state.
    Left,
    /// Right can force a win from this starter state.
    Right,
    /// Neither player can force a win; optimal play can be drawn forever.
    Draw,
}

/// The exact two-sided outcome of a partizan loopy position: one result when Left
/// is to move, and one result when Right is to move.
///
/// The classical five outcome classes embed as the cases where the pair is
/// `(Right, Left)` (`P`), `(Left, Right)` (`N`), `(Left, Left)` (`L`),
/// `(Right, Right)` (`R`), or `(Draw, Draw)` (`Draw`). Mixed cases such as
/// `tis = (Left, Draw)` are real loopy-partizan values and deliberately do not
/// collapse to a [`PartizanOutcome`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LoopyPartizanOutcome {
    pub left_to_move: LoopyWinner,
    pub right_to_move: LoopyWinner,
}

impl LoopyPartizanOutcome {
    pub fn new(left_to_move: LoopyWinner, right_to_move: LoopyWinner) -> Self {
        Self {
            left_to_move,
            right_to_move,
        }
    }

    /// The classical partizan outcome class, when this two-sided result lies in
    /// the classical five-class image.
    pub fn partizan_class(&self) -> Option<PartizanOutcome> {
        use LoopyWinner::*;
        match (self.left_to_move, self.right_to_move) {
            (Right, Left) => Some(PartizanOutcome::P),
            (Left, Right) => Some(PartizanOutcome::N),
            (Left, Left) => Some(PartizanOutcome::L),
            (Right, Right) => Some(PartizanOutcome::R),
            (Draw, Draw) => Some(PartizanOutcome::Draw),
            _ => None,
        }
    }

    pub fn has_draw(&self) -> bool {
        self.left_to_move == LoopyWinner::Draw || self.right_to_move == LoopyWinner::Draw
    }
}

/// The outcome class of a (partizan, possibly loopy) game value: who wins under
/// optimal play. Unlike the impartial [`Outcome`] (which is keyed on the player to
/// move), this names the partizan class directly, and adds [`Draw`](Self::Draw)
/// for loopy values like `dud`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PartizanOutcome {
    /// Previous player wins (the player who *just* moved) — i.e. the player to move
    /// loses. The class of `0`.
    P,
    /// Next player wins (the player to move). The class of `∗`.
    N,
    /// Left wins regardless of who moves first.
    L,
    /// Right wins regardless of who moves first.
    R,
    /// Neither player can force a win — a draw under best play. The class of `dud`.
    Draw,
}

/// A catalogue of named loopy values, plus integer onside/offside (`s&t`) tags.
/// This is not a complete equality theory for loopy games; arithmetic returns
/// `None` whenever a sum leaves the represented catalogue or would require a
/// non-local sidling/equality proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LoopyValue {
    /// `0 = {|}` — the second player (previous mover) wins.
    Zero,
    /// `∗ = {0|0}` — the first player (next mover) wins.
    Star,
    /// `on = {on|}` — Right has no move and loses; Left wins regardless. Larger
    /// than every stopper.
    On,
    /// `off = {|off} = −on` — Left has no move and loses; Right wins regardless.
    Off,
    /// `over = {0|over}` — a positive infinitesimal: `0 < over < x` for every
    /// positive number `x`. Left wins.
    Over,
    /// `under = {under|0} = −over` — a negative infinitesimal. Right wins.
    Under,
    /// `± = {on|off}` — the hot next-player loopy switch.
    PlusMinus,
    /// `tis` (`this is`), the left-swinging non-stopper. In this repo's finite
    /// tag convention it records the two-sided result `(Left, Draw)` and the
    /// sidled sides `1&0`.
    Tis,
    /// `tisn` (`this isn't`), the right-swinging dual of [`Tis`](Self::Tis).
    /// It records `(Draw, Right)` and sidled sides `0&-1`.
    Tisn,
    /// A finite onside/offside tag `s&t`. Addition and negation are carried on the
    /// pair itself; equality with arbitrary loopy games is not decided here.
    OnsideOffside { onside: i128, offside: i128 },
    /// `dud = {dud|dud}` — the "deathless universal draw": both players loop
    /// forever, neither wins. Absorbing under sum; confused with every value.
    Dud,
}

impl LoopyValue {
    /// Build an onside/offside value `s&t`, normalizing `0&0` to `0`.
    pub fn onside_offside(onside: i128, offside: i128) -> LoopyValue {
        if onside == 0 && offside == 0 {
            LoopyValue::Zero
        } else {
            LoopyValue::OnsideOffside { onside, offside }
        }
    }

    /// The `{Left | Right}` form, for display.
    pub fn form(&self) -> String {
        match self {
            LoopyValue::Zero => "{|}".to_string(),
            LoopyValue::Star => "{0|0}".to_string(),
            LoopyValue::On => "{on|}".to_string(),
            LoopyValue::Off => "{|off}".to_string(),
            LoopyValue::Over => "{0|over}".to_string(),
            LoopyValue::Under => "{under|0}".to_string(),
            LoopyValue::PlusMinus => "{on|off}".to_string(),
            LoopyValue::Tis => "{0|tisn}".to_string(),
            LoopyValue::Tisn => "{tis|0}".to_string(),
            LoopyValue::OnsideOffside { onside, offside } => {
                format!("{onside}&{offside}")
            }
            LoopyValue::Dud => "{dud|dud}".to_string(),
        }
    }

    /// The conventional name.
    pub fn name(&self) -> String {
        match self {
            LoopyValue::Zero => "0".to_string(),
            LoopyValue::Star => "*".to_string(),
            LoopyValue::On => "on".to_string(),
            LoopyValue::Off => "off".to_string(),
            LoopyValue::Over => "over".to_string(),
            LoopyValue::Under => "under".to_string(),
            LoopyValue::PlusMinus => "±".to_string(),
            LoopyValue::Tis => "tis".to_string(),
            LoopyValue::Tisn => "tisn".to_string(),
            LoopyValue::OnsideOffside { onside, offside } => {
                format!("{onside}&{offside}")
            }
            LoopyValue::Dud => "dud".to_string(),
        }
    }

    /// Who wins under optimal play for each starter. Use
    /// [`partizan_outcome`](Self::partizan_outcome) when you need the classical
    /// five-class projection.
    pub fn outcome(&self) -> LoopyPartizanOutcome {
        use LoopyWinner::*;
        match self {
            LoopyValue::Zero => LoopyPartizanOutcome::new(Right, Left),
            LoopyValue::Star | LoopyValue::PlusMinus => LoopyPartizanOutcome::new(Left, Right),
            LoopyValue::On | LoopyValue::Over => LoopyPartizanOutcome::new(Left, Left),
            LoopyValue::Off | LoopyValue::Under => LoopyPartizanOutcome::new(Right, Right),
            LoopyValue::Tis => LoopyPartizanOutcome::new(Left, Draw),
            LoopyValue::Tisn => LoopyPartizanOutcome::new(Draw, Right),
            LoopyValue::OnsideOffside { onside, offside } => {
                LoopyPartizanOutcome::new(winner_from_sign(*onside), winner_from_sign(*offside))
            }
            LoopyValue::Dud => LoopyPartizanOutcome::new(Draw, Draw),
        }
    }

    /// The classical partizan outcome class, when this value has one. Values such
    /// as `tis` and `tisn` have a mixed draw/win starter pair, so they return
    /// `None` rather than being flattened into a false five-class answer.
    pub fn partizan_outcome(&self) -> Option<PartizanOutcome> {
        self.outcome().partizan_class()
    }

    /// The sidled onside/offside pair when this finite tag carries one.
    pub fn sides(&self) -> Option<(i128, i128)> {
        match *self {
            LoopyValue::Tis => Some((1, 0)),
            LoopyValue::Tisn => Some((0, -1)),
            LoopyValue::OnsideOffside { onside, offside } => Some((onside, offside)),
            _ => None,
        }
    }

    /// Negation (swap the Left/Right roles): `−on = off`, `−over = under`, and the
    /// self-negating `0`, `∗`, `±`, `dud`.
    pub fn neg(&self) -> LoopyValue {
        match self {
            LoopyValue::Zero => LoopyValue::Zero,
            LoopyValue::Star => LoopyValue::Star,
            LoopyValue::On => LoopyValue::Off,
            LoopyValue::Off => LoopyValue::On,
            LoopyValue::Over => LoopyValue::Under,
            LoopyValue::Under => LoopyValue::Over,
            LoopyValue::PlusMinus => LoopyValue::PlusMinus,
            LoopyValue::Tis => LoopyValue::Tisn,
            LoopyValue::Tisn => LoopyValue::Tis,
            LoopyValue::OnsideOffside { onside, offside } => {
                LoopyValue::onside_offside(-*offside, -*onside)
            }
            LoopyValue::Dud => LoopyValue::Dud,
        }
    }

    /// Whether this value is a **stopper** (guaranteed to end when played in
    /// isolation). The named non-stoppers here are `dud`, `tis`, and `tisn`.
    pub fn is_stopper(&self) -> bool {
        !matches!(self, LoopyValue::Dud | LoopyValue::Tis | LoopyValue::Tisn)
    }

    /// The disjunctive sum, where it is defined on this catalogue. Returns `None`
    /// when the sum leaves the catalogue or when this small catalogue deliberately
    /// refuses a drawn value not represented by its named tags.
    ///
    /// The closed cases: `dud` absorbs everything (`dud + G = dud`); `on + off =
    /// dud`; `on`/`off` absorb every other represented stopper (`on` is `>` every
    /// stopper); `∗ + ∗ = 0`; `over + over = over`, `under + under = under`,
    /// `∗ + over = over`, `∗ + under = under`; `s&t + u&v = (s+u)&(t+v)`;
    /// and `0` is the identity.
    pub fn add(&self, other: &LoopyValue) -> Option<LoopyValue> {
        use LoopyValue::*;
        let r = match (*self, *other) {
            (Dud, _) | (_, Dud) => Dud,
            (Zero, x) | (x, Zero) => x,
            (On, On) => On,
            (Off, Off) => Off,
            (On, Off) | (Off, On) => Dud,
            (On, Star)
            | (Star, On)
            | (On, Over)
            | (Over, On)
            | (On, Under)
            | (Under, On)
            | (On, PlusMinus)
            | (PlusMinus, On) => On,
            (Off, Star)
            | (Star, Off)
            | (Off, Over)
            | (Over, Off)
            | (Off, Under)
            | (Under, Off)
            | (Off, PlusMinus)
            | (PlusMinus, Off) => Off,
            (Star, Star) => Zero,
            (Over, Over) | (Star, Over) | (Over, Star) => Over,
            (Under, Under) | (Star, Under) | (Under, Star) => Under,
            (
                OnsideOffside {
                    onside: a,
                    offside: b,
                },
                OnsideOffside {
                    onside: c,
                    offside: d,
                },
            ) => LoopyValue::onside_offside(a + c, b + d),
            (Over, Under) | (Under, Over) => return None,
            (PlusMinus, PlusMinus)
            | (PlusMinus, Star)
            | (Star, PlusMinus)
            | (PlusMinus, Over)
            | (Over, PlusMinus)
            | (PlusMinus, Under)
            | (Under, PlusMinus)
            | (Tis, _)
            | (_, Tis)
            | (Tisn, _)
            | (_, Tisn)
            | (OnsideOffside { .. }, _)
            | (_, OnsideOffside { .. }) => return None,
        };
        Some(r)
    }
}

fn winner_from_sign(x: i128) -> LoopyWinner {
    if x > 0 {
        LoopyWinner::Left
    } else if x < 0 {
        LoopyWinner::Right
    } else {
        LoopyWinner::Draw
    }
}

impl PartialOrd for LoopyValue {
    /// The conservative partial order on the catalogue. The comparable core is the
    /// chain `off < under < ∗ < over < on`, with `0` confused with `∗` and between
    /// `under` and `over`. `on` sits above and `off` below every other non-`dud`
    /// value. `dud` is confused with
    /// everything (comparable only to itself). Incomparable ⇒ `None`.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use LoopyValue::*;
        if self == other {
            return Some(Ordering::Equal);
        }
        match (*self, *other) {
            // dud is confused with every other value.
            (Dud, _) | (_, Dud) => None,
            // The extended tags need a genuine comparison proof; equality was
            // handled above, so keep the catalogue order conservative.
            (PlusMinus, _)
            | (_, PlusMinus)
            | (Tis, _)
            | (_, Tis)
            | (Tisn, _)
            | (_, Tisn)
            | (OnsideOffside { .. }, _)
            | (_, OnsideOffside { .. }) => None,
            // on is the top, off the bottom (over all non-dud values).
            (On, _) => Some(Ordering::Greater),
            (_, On) => Some(Ordering::Less),
            (Off, _) => Some(Ordering::Less),
            (_, Off) => Some(Ordering::Greater),
            // star is confused with 0, but sits between under and over.
            (Star, Zero) | (Zero, Star) => None,
            (Star, Over) | (Under, Star) => Some(Ordering::Less),
            (Over, Star) | (Star, Under) => Some(Ordering::Greater),
            // the remaining comparable chain under < 0 < over.
            (a, b) => {
                let rank = |v: LoopyValue| match v {
                    Under => -1i128,
                    Zero => 0,
                    Over => 1,
                    _ => unreachable!("on/off/star/dud handled above"),
                };
                Some(rank(a).cmp(&rank(b)))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// 2. The graph-level engine.
// ---------------------------------------------------------------------------

/// A loopy game as a finite move graph (`succ[v]` = the positions reachable from
/// `v` in one move). The move graph may be cyclic; outcomes are computed by the
/// retrograde [`kernel::outcomes`](crate::games::outcomes) (Win / Loss / Draw,
/// where **Loss = P-position** and **Draw = the loopy escape**).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopyGraph {
    succ: Vec<Vec<usize>>,
}

impl LoopyGraph {
    /// Build from explicit adjacency lists.
    pub fn new(succ: Vec<Vec<usize>>) -> LoopyGraph {
        LoopyGraph { succ }
    }

    /// Build from a move rule on positions `0..n` (the rule may produce cycles).
    pub fn from_rule<F: Fn(usize) -> Vec<usize>>(n: usize, moves: F) -> LoopyGraph {
        LoopyGraph {
            succ: (0..n).map(moves).collect(),
        }
    }

    /// The adjacency lists.
    pub fn succ(&self) -> &[Vec<usize>] {
        &self.succ
    }

    /// Win / Loss / Draw of every position (retrograde analysis).
    pub fn outcomes(&self) -> Vec<Outcome> {
        kernel::outcomes(&self.succ)
    }

    /// The Loss positions = **P-positions** (the player to move loses).
    pub fn loss_set(&self) -> Vec<usize> {
        self.indices_with(Outcome::Loss)
    }

    /// The Win positions = N-positions (the player to move wins).
    pub fn win_set(&self) -> Vec<usize> {
        self.indices_with(Outcome::Win)
    }

    /// The Draw positions — the loopy degree of freedom (neither player can force a
    /// win). Empty iff the game is effectively non-loopy.
    pub fn draw_set(&self) -> Vec<usize> {
        self.indices_with(Outcome::Draw)
    }

    fn indices_with(&self, want: Outcome) -> Vec<usize> {
        self.outcomes()
            .into_iter()
            .enumerate()
            .filter(|(_, o)| *o == want)
            .map(|(i, _)| i)
            .collect()
    }

    /// A coarse reading of a position as a catalogue [`LoopyValue`], via its
    /// impartial outcome only: a **Loss** is `0`, a **Draw** is `dud`. A **Win** is
    /// `None` — its value is a nonzero loopy nimber (use [`loopy_nim_values`]), not
    /// a named catalogue stopper. This is deliberately partial: an impartial move
    /// graph cannot express the Left/Right asymmetry of `on`/`off`/`over`/`under`.
    pub fn classify(&self, v: usize) -> Option<LoopyValue> {
        match self.outcomes().get(v)? {
            Outcome::Loss => Some(LoopyValue::Zero),
            Outcome::Draw => Some(LoopyValue::Dud),
            Outcome::Win => None,
        }
    }
}

// ---------------------------------------------------------------------------
// 3. The two-sided partizan graph engine.
// ---------------------------------------------------------------------------

/// A finite loopy partizan game graph. `left[v]` are Left's legal moves from
/// position `v`; `right[v]` are Right's legal moves. Cycles are allowed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopyPartizanGraph {
    left: Vec<Vec<usize>>,
    right: Vec<Vec<usize>>,
}

impl LoopyPartizanGraph {
    /// Build from explicit Left and Right adjacency lists.
    pub fn new(left: Vec<Vec<usize>>, right: Vec<Vec<usize>>) -> LoopyPartizanGraph {
        assert_eq!(
            left.len(),
            right.len(),
            "left/right move tables must have the same number of positions"
        );
        LoopyPartizanGraph { left, right }
    }

    /// Build from move rules on positions `0..n`.
    pub fn from_rules<L, R>(n: usize, left_moves: L, right_moves: R) -> LoopyPartizanGraph
    where
        L: Fn(usize) -> Vec<usize>,
        R: Fn(usize) -> Vec<usize>,
    {
        LoopyPartizanGraph {
            left: (0..n).map(left_moves).collect(),
            right: (0..n).map(right_moves).collect(),
        }
    }

    /// Left's adjacency lists.
    pub fn left(&self) -> &[Vec<usize>] {
        &self.left
    }

    /// Right's adjacency lists.
    pub fn right(&self) -> &[Vec<usize>] {
        &self.right
    }

    /// Exact two-sided loopy-partizan outcome of every position.
    pub fn outcomes(&self) -> Vec<LoopyPartizanOutcome> {
        solve_partizan_outcomes(&self.left, &self.right)
    }

    /// Classical partizan outcome classes where the exact two-sided outcome lies
    /// in the five-class image. Mixed loopy starter pairs (`tis`, `tisn`, …)
    /// return `None`.
    pub fn partizan_outcomes(&self) -> Vec<Option<PartizanOutcome>> {
        self.outcomes()
            .into_iter()
            .map(|o| o.partizan_class())
            .collect()
    }

    /// The classical class of position `v`, if it has one.
    pub fn classify(&self, v: usize) -> Option<PartizanOutcome> {
        self.outcomes().get(v).and_then(|o| o.partizan_class())
    }

    /// Positions whose exact starter pair contains a draw for at least one player
    /// to move.
    pub fn draw_set(&self) -> Vec<usize> {
        self.outcomes()
            .into_iter()
            .enumerate()
            .filter_map(|(i, o)| o.has_draw().then_some(i))
            .collect()
    }

    /// Positions whose exact outcome is outside the classical five classes.
    pub fn nonclassical_set(&self) -> Vec<usize> {
        self.outcomes()
            .into_iter()
            .enumerate()
            .filter_map(|(i, o)| o.partizan_class().is_none().then_some(i))
            .collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Turn {
    Left,
    Right,
}

fn state(v: usize, turn: Turn) -> usize {
    2 * v
        + match turn {
            Turn::Left => 0,
            Turn::Right => 1,
        }
}

fn state_parts(s: usize) -> (usize, Turn) {
    (s / 2, if s & 1 == 0 { Turn::Left } else { Turn::Right })
}

fn owner_winner(turn: Turn) -> LoopyWinner {
    match turn {
        Turn::Left => LoopyWinner::Left,
        Turn::Right => LoopyWinner::Right,
    }
}

fn opponent_winner(turn: Turn) -> LoopyWinner {
    match turn {
        Turn::Left => LoopyWinner::Right,
        Turn::Right => LoopyWinner::Left,
    }
}

fn solve_partizan_outcomes(left: &[Vec<usize>], right: &[Vec<usize>]) -> Vec<LoopyPartizanOutcome> {
    assert_eq!(
        left.len(),
        right.len(),
        "left/right move tables must have the same number of positions"
    );
    let n = left.len();
    let states = 2 * n;
    let mut succ = vec![Vec::new(); states];
    let mut pred = vec![Vec::new(); states];
    for v in 0..n {
        for &w in &left[v] {
            let s = state(v, Turn::Left);
            let t = state(w, Turn::Right);
            succ[s].push(t);
            pred[t].push(s);
        }
        for &w in &right[v] {
            let s = state(v, Turn::Right);
            let t = state(w, Turn::Left);
            succ[s].push(t);
            pred[t].push(s);
        }
    }

    let mut remaining: Vec<usize> = succ.iter().map(Vec::len).collect();
    let mut label: Vec<Option<LoopyWinner>> = vec![None; states];
    let mut queue = VecDeque::new();

    for s in 0..states {
        if succ[s].is_empty() {
            let (_, turn) = state_parts(s);
            label[s] = Some(opponent_winner(turn));
            queue.push_back(s);
        }
    }

    while let Some(s) = queue.pop_front() {
        let winner = label[s].unwrap();
        for &p in &pred[s] {
            if label[p].is_some() {
                continue;
            }
            let (_, turn) = state_parts(p);
            if winner == owner_winner(turn) {
                label[p] = Some(winner);
                queue.push_back(p);
            } else {
                remaining[p] -= 1;
                if remaining[p] == 0 {
                    label[p] = Some(winner);
                    queue.push_back(p);
                }
            }
        }
    }

    (0..n)
        .map(|v| {
            LoopyPartizanOutcome::new(
                label[state(v, Turn::Left)].unwrap_or(LoopyWinner::Draw),
                label[state(v, Turn::Right)].unwrap_or(LoopyWinner::Draw),
            )
        })
        .collect()
}

// ---------------------------------------------------------------------------
// 4. Impartial loopy nim-values (partial sidling).
// ---------------------------------------------------------------------------

/// A loopy nim-value: an ordinary nimber, or `Side` (the loopy `∞`) for a drawn
/// position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopyNimber {
    /// A genuine nimber (the position terminates under optimal impartial play).
    Value(u128),
    /// The "side" value `∞`: a Draw position, from which play can be sustained
    /// forever.
    Side,
}

/// Certificate for [`loopy_nim_values_certified`]: the outcome split, the positions
/// promoted to `Side`, whether the bounded sidling solver was needed, and the
/// checked recovery condition for additive finite-nimber claims.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopyNimCertificate {
    pub outcomes: Vec<Outcome>,
    pub side_positions: Vec<usize>,
    pub used_sidling_solver: bool,
    pub sidling_assignments_examined: usize,
    /// True when every finite-valued position has only finite-valued options.
    /// Under this checked condition the emitted finite nimbers are ordinary
    /// Sprague-Grundy labels on a closed subgame, so additivity claims are local
    /// checked facts instead of prose caveats.
    pub recovery_condition_holds: bool,
    /// Finite-valued positions with at least one `Side` option. These are exactly
    /// the blockers for the checked recovery condition above.
    pub recovery_blockers: Vec<usize>,
}

/// Loopy nim-values of an impartial game graph. Draw positions (per
/// [`kernel::outcomes`](crate::games::outcomes)) are `Side`; the rest carry an
/// ordinary nimber `mex`-computed over their non-`Side` options.
///
/// **Exact** when the non-Draw subgraph is acyclic — there `Value(0) ⟺ Loss` and
/// the values agree with [`grundy_graph`](crate::games::grundy_graph). If the
/// non-Draw subgraph is cyclic, a bounded sidling search is accepted only when the
/// finite mex equations have a **unique** solution; ambiguous or over-budget
/// cyclic systems return `None` rather than choosing an order-dependent value.
///
/// **Recovery check**: when a position has Draw (Side) options the emitted
/// `Value(k)` is the Grundy value of the Draw-deleted subgraph at that vertex.
/// The certificate records a checked finite recovery condition:
/// `recovery_condition_holds` iff all finite-valued positions have only
/// finite-valued successors. Only under that condition should additivity-over-sums
/// be cited for the finite nimbers. The `Side` values themselves have no additive
/// nimber arithmetic.
pub fn loopy_nim_values(succ: &[Vec<usize>]) -> Option<Vec<LoopyNimber>> {
    loopy_nim_values_certified(succ).map(|(values, _)| values)
}

/// [`loopy_nim_values`] plus a small certificate explaining the outcome split and
/// whether cyclic non-Draw sidling was solved uniquely by the bounded mex-equation
/// search.
pub fn loopy_nim_values_certified(
    succ: &[Vec<usize>],
) -> Option<(Vec<LoopyNimber>, LoopyNimCertificate)> {
    let n = succ.len();
    let out = kernel::outcomes(succ);
    let is_side: Vec<bool> = out.iter().map(|o| *o == Outcome::Draw).collect();
    let mut val = vec![0u128; n];
    let mut state = vec![0u128; n]; // 0 unvisited, 1 visiting, 2 done
    let mut needs_sidling = false;

    fn dfs(
        succ: &[Vec<usize>],
        is_side: &[bool],
        v: usize,
        state: &mut [u128],
        val: &mut [u128],
    ) -> Option<()> {
        match state[v] {
            2 => return Some(()),
            1 => return None, // back-edge among non-Side nodes ⇒ defer to full sidling
            _ => {}
        }
        state[v] = 1;
        let mut opts = Vec::new();
        for &w in &succ[v] {
            if is_side[w] {
                continue; // a Side option neither blocks a mex value nor forces a loss
            }
            dfs(succ, is_side, w, state, val)?;
            opts.push(val[w]);
        }
        val[v] = mex(opts);
        state[v] = 2;
        Some(())
    }

    for v in 0..n {
        if !is_side[v] && dfs(succ, &is_side, v, &mut state, &mut val).is_none() {
            needs_sidling = true;
            break;
        }
    }

    let mut assignments = 0usize;
    if needs_sidling {
        let (sidled, count) = solve_mex_sidling(succ, &is_side)?;
        val = sidled;
        assignments = count;
    }

    let values: Vec<LoopyNimber> = (0..n)
        .map(|v| {
            if is_side[v] {
                LoopyNimber::Side
            } else {
                LoopyNimber::Value(val[v])
            }
        })
        .collect();
    let recovery_blockers: Vec<usize> = (0..n)
        .filter(|&v| !is_side[v] && succ[v].iter().any(|&w| is_side[w]))
        .collect();
    let cert = LoopyNimCertificate {
        outcomes: out,
        side_positions: is_side
            .iter()
            .enumerate()
            .filter_map(|(i, &side)| side.then_some(i))
            .collect(),
        used_sidling_solver: needs_sidling,
        sidling_assignments_examined: assignments,
        recovery_condition_holds: recovery_blockers.is_empty(),
        recovery_blockers,
    };
    Some((values, cert))
}

fn solve_mex_sidling(succ: &[Vec<usize>], is_side: &[bool]) -> Option<(Vec<u128>, usize)> {
    let n = succ.len();
    let finite: Vec<usize> = (0..n).filter(|&v| !is_side[v]).collect();
    let mut order = finite.clone();
    order.sort_by_key(|&v| succ[v].iter().filter(|&&w| !is_side[w]).count());
    let mut assigned = vec![false; n];
    for (v, &side) in is_side.iter().enumerate() {
        if side {
            assigned[v] = true;
        }
    }
    let values = vec![0u128; n];
    let max_for: Vec<u128> = (0..n)
        .map(|v| succ[v].iter().filter(|&&w| !is_side[w]).count() as u128)
        .collect();
    let examined = 0usize;

    struct Solver<'a> {
        order: Vec<usize>,
        succ: &'a [Vec<usize>],
        is_side: &'a [bool],
        max_for: Vec<u128>,
        assigned: Vec<bool>,
        values: Vec<u128>,
        examined: usize,
    }

    impl Solver<'_> {
        fn rec(&mut self, idx: usize, solution: &mut Option<Vec<u128>>) -> Option<bool> {
            if self.examined > MAX_SIDLING_ASSIGNMENTS {
                return None;
            }
            if idx == self.order.len() {
                if all_mex_equations_hold(self.succ, self.is_side, &self.values) {
                    if solution.is_some() {
                        return Some(false); // multiple fixed points: not canonical
                    }
                    *solution = Some(self.values.clone());
                }
                return Some(true);
            }
            let v = self.order[idx];
            for candidate in 0..=self.max_for[v] {
                self.examined += 1;
                if self.examined > MAX_SIDLING_ASSIGNMENTS {
                    return None;
                }
                self.values[v] = candidate;
                self.assigned[v] = true;
                if partial_mex_equations_hold(self.succ, self.is_side, &self.assigned, &self.values)
                {
                    match self.rec(idx + 1, solution) {
                        Some(true) => {}
                        Some(false) => return Some(false),
                        None => return None,
                    }
                }
                self.assigned[v] = false;
            }
            Some(true)
        }
    }

    let mut solver = Solver {
        order,
        succ,
        is_side,
        max_for,
        assigned,
        values,
        examined,
    };
    let mut solution = None;
    match solver.rec(0, &mut solution) {
        Some(true) => solution.map(|values| (values, solver.examined)),
        Some(false) | None => None,
    }
}

fn partial_mex_equations_hold(
    succ: &[Vec<usize>],
    is_side: &[bool],
    assigned: &[bool],
    values: &[u128],
) -> bool {
    for v in 0..succ.len() {
        if is_side[v] || !assigned[v] {
            continue;
        }
        if succ[v].iter().any(|&w| !is_side[w] && !assigned[w]) {
            continue;
        }
        if values[v] != mex_value(succ, is_side, values, v) {
            return false;
        }
    }
    true
}

fn all_mex_equations_hold(succ: &[Vec<usize>], is_side: &[bool], values: &[u128]) -> bool {
    (0..succ.len())
        .filter(|&v| !is_side[v])
        .all(|v| values[v] == mex_value(succ, is_side, values, v))
}

fn mex_value(succ: &[Vec<usize>], is_side: &[bool], values: &[u128], v: usize) -> u128 {
    mex(succ[v]
        .iter()
        .filter_map(|&w| (!is_side[w]).then_some(values[w])))
}

// ---------------------------------------------------------------------------
// 5. The research instrument: Loss-set AND Draw-set of a cyclic rule.
// ---------------------------------------------------------------------------

/// Given a move rule on positions `0..n` (cycles allowed), return its
/// `(loss_set, draw_set)` — the P-positions and the loopy Draw positions. The
/// acyclic analogue (`examples/interactive_kernel.rs`) discards the Draw count;
/// here both sets are first-class, which is the point: a cyclic rule can carve a
/// non-XOR-linear Draw-set.
pub fn loopy_decision_sets<F: Fn(usize) -> Vec<usize>>(
    n: usize,
    moves: F,
) -> (Vec<usize>, Vec<usize>) {
    let g = LoopyGraph::from_rule(n, moves);
    (g.loss_set(), g.draw_set())
}

/// Probe a cyclic move rule on `F₂^k` (positions `0..2^k`) for a quadric P-set or
/// Draw-set: returns `(loss_fit, draw_fit)`, each the
/// [`fit_f2_quadratic`] of the corresponding set
/// (or `None` if that set is not the zero-set of any `F₂` quadratic form). A
/// genuinely-quadratic Draw-set ([`QuadricFit::is_genuinely_quadratic`]) is the
/// Tier-2 target.
pub fn loopy_quadric_probe<F: Fn(usize) -> Vec<usize>>(
    k: usize,
    moves: F,
) -> (Option<QuadricFit>, Option<QuadricFit>) {
    assert!(k <= 20, "loopy_quadric_probe is exponential in k");
    let n = 1usize << k;
    let (loss, draw) = loopy_decision_sets(n, moves);
    let loss_u: Vec<u128> = loss.iter().map(|&v| v as u128).collect();
    let draw_u: Vec<u128> = draw.iter().map(|&v| v as u128).collect();
    (fit_f2_quadratic(&loss_u, k), fit_f2_quadratic(&draw_u, k))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::games::grundy_graph;

    // --- the catalogue ---

    #[test]
    fn negation_is_an_involution_and_swaps_sides() {
        use LoopyValue::*;
        for v in [
            Zero,
            Star,
            On,
            Off,
            Over,
            Under,
            PlusMinus,
            Tis,
            Tisn,
            LoopyValue::onside_offside(3, -2),
            Dud,
        ] {
            assert_eq!(v.neg().neg(), v);
        }
        assert_eq!(On.neg(), Off);
        assert_eq!(Over.neg(), Under);
        assert_eq!(Tis.neg(), Tisn);
        assert_eq!(
            LoopyValue::onside_offside(3, -2).neg(),
            LoopyValue::onside_offside(2, -3)
        );
        assert_eq!(Dud.neg(), Dud);
    }

    #[test]
    fn outcomes_of_the_stoppers() {
        use LoopyValue::*;
        assert_eq!(Zero.partizan_outcome(), Some(PartizanOutcome::P));
        assert_eq!(Star.partizan_outcome(), Some(PartizanOutcome::N));
        assert_eq!(PlusMinus.partizan_outcome(), Some(PartizanOutcome::N));
        assert_eq!(On.partizan_outcome(), Some(PartizanOutcome::L));
        assert_eq!(Off.partizan_outcome(), Some(PartizanOutcome::R));
        assert_eq!(Over.partizan_outcome(), Some(PartizanOutcome::L));
        assert_eq!(Under.partizan_outcome(), Some(PartizanOutcome::R));
        assert_eq!(Dud.partizan_outcome(), Some(PartizanOutcome::Draw));
        assert_eq!(
            Tis.outcome(),
            LoopyPartizanOutcome::new(LoopyWinner::Left, LoopyWinner::Draw)
        );
        assert_eq!(
            Tisn.outcome(),
            LoopyPartizanOutcome::new(LoopyWinner::Draw, LoopyWinner::Right)
        );
        assert_eq!(Tis.partizan_outcome(), None);
        assert_eq!(Tis.sides(), Some((1, 0)));
        assert_eq!(Tisn.sides(), Some((0, -1)));
        assert!(!Dud.is_stopper());
        assert!(!Tis.is_stopper());
        assert!(On.is_stopper());
    }

    #[test]
    fn the_closed_sums() {
        use LoopyValue::*;
        // 0 is the identity.
        for v in [Zero, Star, On, Off, Over, Under, PlusMinus, Tis, Tisn, Dud] {
            assert_eq!(Zero.add(&v), Some(v));
        }
        // dud absorbs everything.
        for v in [Zero, Star, On, Off, Over, Under, PlusMinus, Tis, Tisn, Dud] {
            assert_eq!(Dud.add(&v), Some(Dud));
            assert_eq!(v.add(&Dud), Some(Dud));
        }
        assert_eq!(On.add(&Off), Some(Dud)); // on + off = dud
        assert_eq!(On.add(&On), Some(On));
        assert_eq!(Off.add(&Off), Some(Off));
        assert_eq!(On.add(&Star), Some(On)); // on absorbs stoppers
        assert_eq!(On.add(&Over), Some(On));
        assert_eq!(Star.add(&Star), Some(Zero));
        assert_eq!(Over.add(&Under), None);
        assert_eq!(Over.add(&Over), Some(Over));
        assert_eq!(Under.add(&Under), Some(Under));
        assert_eq!(Star.add(&Over), Some(Over));
        assert_eq!(Star.add(&Under), Some(Under));
        // over+under is a draw-class value outside these named tags.
        assert_eq!(Under.add(&Over), None);
        assert_eq!(
            LoopyValue::onside_offside(1, 0).add(&LoopyValue::onside_offside(0, -1)),
            Some(LoopyValue::onside_offside(1, -1))
        );
        assert_eq!(Tis.add(&Tisn), None);
    }

    #[test]
    fn the_partial_order() {
        use LoopyValue::*;
        // the comparable chain off < under < 0 < over < on.
        assert!(Off < Under && Under < Zero && Zero < Over && Over < On);
        assert!(Under < Star && Star < Over);
        assert!(Off < On);
        // on/off are the extremes (over every non-dud value).
        assert!(On > Star && Off < Star);
        // star is confused with 0; dud with everything.
        assert_eq!(Star.partial_cmp(&Zero), None);
        assert_eq!(Dud.partial_cmp(&Zero), None);
        assert_eq!(Dud.partial_cmp(&On), None);
        assert_eq!(Dud.partial_cmp(&Dud), Some(Ordering::Equal));
    }

    // --- the graph engine ---

    #[test]
    fn two_cycle_is_all_draws() {
        let g = LoopyGraph::new(vec![vec![1], vec![0]]);
        assert_eq!(g.outcomes(), vec![Outcome::Draw, Outcome::Draw]);
        assert_eq!(g.draw_set(), vec![0, 1]);
        assert_eq!(g.classify(0), Some(LoopyValue::Dud));
    }

    #[test]
    fn nim_heap_path_has_no_draws() {
        // The Nim heap of size n is the path n → {n-1, …, 0}: only 0 is a Loss.
        let n = 6usize;
        let succ: Vec<Vec<usize>> = (0..=n).map(|h| (0..h).collect()).collect();
        let g = LoopyGraph::new(succ);
        assert_eq!(g.loss_set(), vec![0]);
        assert!(g.draw_set().is_empty());
        assert_eq!(g.classify(0), Some(LoopyValue::Zero));
    }

    // --- the partizan graph engine ---

    #[test]
    fn partizan_graph_recovers_classical_short_outcomes() {
        // position 0 is terminal; 1 = *; 2 = {0|}; 3 = {|0}.
        let left = vec![vec![], vec![0], vec![0], vec![]];
        let right = vec![vec![], vec![0], vec![], vec![0]];
        let g = LoopyPartizanGraph::new(left, right);
        assert_eq!(
            g.partizan_outcomes(),
            vec![
                Some(PartizanOutcome::P),
                Some(PartizanOutcome::N),
                Some(PartizanOutcome::L),
                Some(PartizanOutcome::R),
            ]
        );
        assert!(g.draw_set().is_empty());
    }

    #[test]
    fn partizan_graph_keeps_tis_as_mixed_draw_class() {
        // Repo convention: tis = {0|tisn}, tisn = {tis|0}, with 0 terminal.
        let left = vec![vec![2], vec![0], vec![]];
        let right = vec![vec![1], vec![2], vec![]];
        let g = LoopyPartizanGraph::new(left, right);
        let out = g.outcomes();
        assert_eq!(out[0], LoopyValue::Tis.outcome());
        assert_eq!(out[1], LoopyValue::Tisn.outcome());
        assert_eq!(g.classify(0), None);
        assert_eq!(g.nonclassical_set(), vec![0, 1]);
        assert_eq!(g.draw_set(), vec![0, 1]);
    }

    #[test]
    fn impartial_partizan_graph_matches_kernel_outcomes() {
        let succ = vec![vec![1], vec![2, 0], vec![]];
        let g = LoopyPartizanGraph::new(succ.clone(), succ.clone());
        assert_eq!(
            g.partizan_outcomes(),
            kernel::outcomes(&succ)
                .into_iter()
                .map(|o| match o {
                    Outcome::Loss => Some(PartizanOutcome::P),
                    Outcome::Win => Some(PartizanOutcome::N),
                    Outcome::Draw => Some(PartizanOutcome::Draw),
                })
                .collect::<Vec<_>>()
        );
    }

    // --- loopy nim-values ---

    #[test]
    fn loopy_nim_values_match_grundy_on_acyclic_graphs() {
        // No draws ⇒ the non-Side subgraph is the whole (acyclic) graph.
        let succ = vec![vec![1, 2], vec![3], vec![3], vec![]];
        let lv = loopy_nim_values(&succ).unwrap();
        let g = grundy_graph(&succ).unwrap();
        for v in 0..succ.len() {
            assert_eq!(lv[v], LoopyNimber::Value(g[v]));
        }
    }

    #[test]
    fn draws_are_side_and_value_zero_is_loss() {
        // 0↔1 a drawn 2-cycle; 2→3, 3 terminal (Loss). 2 is a Win (→ Loss 3).
        let succ = vec![vec![1], vec![0], vec![3], vec![]];
        let lv = loopy_nim_values(&succ).unwrap();
        assert_eq!(lv[0], LoopyNimber::Side);
        assert_eq!(lv[1], LoopyNimber::Side);
        assert_eq!(lv[3], LoopyNimber::Value(0)); // terminal ⇒ Loss ⇒ 0
        assert_eq!(lv[2], LoopyNimber::Value(1)); // mex{0} = 1
    }

    #[test]
    fn cyclic_non_draw_subgraph_uses_bounded_sidling() {
        // cycle-with-exit: 0→1, 1→{2,0}, 2 terminal. kernel resolves 0,1 to
        // Loss/Win (non-Draw), and the bounded sidling solver finds the finite mex
        // fixed point g = [0, 1, 0].
        let succ = vec![vec![1], vec![2, 0], vec![]];
        let (values, cert) = loopy_nim_values_certified(&succ).unwrap();
        assert_eq!(
            values,
            vec![
                LoopyNimber::Value(0),
                LoopyNimber::Value(1),
                LoopyNimber::Value(0)
            ]
        );
        assert!(cert.used_sidling_solver);
        assert!(cert.sidling_assignments_examined > 0);
        assert!(cert.recovery_condition_holds);
        assert!(cert.recovery_blockers.is_empty());
        // but the outcome analysis is still exact.
        let g = LoopyGraph::new(succ);
        assert_eq!(
            g.outcomes(),
            vec![Outcome::Loss, Outcome::Win, Outcome::Loss]
        );
    }

    #[test]
    fn ambiguous_cyclic_sidling_returns_none() {
        // Symmetric cycle-with-exits:
        //   g0 = mex{g1,0}, g1 = mex{g0,0}
        // has two fixed points, (1,2) and (2,1). Positions 0 and 1 are graph-
        // symmetric, so choosing either finite assignment would be noncanonical.
        let succ = vec![vec![1, 2], vec![0, 3], vec![], vec![]];
        assert_eq!(loopy_nim_values(&succ), None);
        assert_eq!(loopy_nim_values_certified(&succ), None);
        let g = LoopyGraph::new(succ);
        assert_eq!(
            g.outcomes(),
            vec![Outcome::Win, Outcome::Win, Outcome::Loss, Outcome::Loss]
        );
    }

    #[test]
    fn recovery_certificate_flags_finite_positions_with_side_options() {
        // 0↔1 is Side; 2 also has a move to terminal 3, so 2 is finite-valued but
        // points at a Side option. Its local mex value is computed, while the
        // recovery/additivity condition is explicitly false.
        let succ = vec![vec![1], vec![0], vec![0, 3], vec![]];
        let (_values, cert) = loopy_nim_values_certified(&succ).unwrap();
        assert_eq!(cert.side_positions, vec![0, 1]);
        assert!(!cert.recovery_condition_holds);
        assert_eq!(cert.recovery_blockers, vec![2]);
    }

    // --- the research instrument ---

    #[test]
    fn decision_sets_recover_an_acyclic_loss_set_with_no_draws() {
        // A downward (terminating) rule: move v → any w < v. Then 0 is the only
        // Loss and there are no Draws — matching the acyclic interactive probe.
        let n = 8;
        let (loss, draw) = loopy_decision_sets(n, |v| (0..v).collect());
        assert_eq!(loss, vec![0]);
        assert!(draw.is_empty());
    }

    #[test]
    fn quadric_probe_reads_both_sets() {
        // A cyclic rule on F₂² that makes {0} a Loss and pairs the rest into a draw
        // cycle — exercising both fit slots. Here we just check the plumbing: the
        // loss-set fits (a point) and the call returns without panicking.
        let (loss_fit, _draw_fit) = loopy_quadric_probe(2, |v| {
            if v == 0 {
                vec![] // terminal ⇒ Loss
            } else {
                vec![0] // everyone moves to 0 ⇒ Win, no draws
            }
        });
        // {0} as a P-set over F₂² is the anisotropic quadric (Arf 1).
        let f = loss_fit.expect("{0} is a quadric");
        assert!(f.is_genuinely_quadratic());
        assert_eq!(f.arf.arf, 1);
    }
}
