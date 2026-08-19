//! The pass-free weighted-source Witt--FIFO arena.
//!
//! Given an `F_2` quadratic form
//!
//! ```text
//! Q(x) = sum_i q_i x_i + sum_{i<j} b_ij x_i x_j,
//! ```
//!
//! [`WittFifoArena::try_new`] deterministically puts the alternating polar form
//! `B = (b_ij)` into symplectic-pairs-plus-radical coordinates. It loads the
//! public matching and the refinement-weighted source pairs proved in the
//! Gold--Arf construction. The resulting finite impartial normal-play root is a
//! `P`-position exactly when `Q(x) = 0`.
//!
//! This module constructs only the proved matching-plus-isolates arena. It does
//! not assume or expose the stronger arbitrary-graph isolated-dummy FIFO
//! conjecture.

use crate::games::{mex, Game};
use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::sync::Arc;

/// A loaded coin in a weighted-source Witt--FIFO arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WittFifoCoinId(usize);

impl WittFifoCoinId {
    /// Stable zero-based index within its arena.
    pub fn index(self) -> usize {
        self.0
    }
}

/// The public origin of a loaded coin.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WittFifoCoinKind {
    /// An active coordinate in the deterministic adapted basis.
    Strategic {
        /// Index of the adapted basis vector.
        adapted_index: usize,
    },
    /// One endpoint of the source pair for an active original coordinate.
    Source {
        /// Index in the caller's original basis.
        original_index: usize,
        /// `false` and `true` distinguish the two endpoints.
        endpoint: bool,
    },
}

/// Public metadata for one loaded coin.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WittFifoCoin {
    kind: WittFifoCoinKind,
    potential_mate: Option<WittFifoCoinId>,
    edge_weight: bool,
    close_charge: bool,
}

impl WittFifoCoin {
    /// Whether this is a strategic or source coin, with its source coordinate.
    pub fn kind(&self) -> WittFifoCoinKind {
        self.kind
    }

    /// Mate in the public potential matching, including zero-weight source pairs.
    pub fn potential_mate(&self) -> Option<WittFifoCoinId> {
        self.potential_mate
    }

    /// Weight charged when this coin opens while its mate is open.
    pub fn edge_weight(&self) -> bool {
        self.edge_weight
    }

    /// Public label charged when this coin closes.
    pub fn close_charge(&self) -> bool {
        self.close_charge
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct CorePosition {
    untouched: [u128; 3],
    queue: VecDeque<WittFifoCoinId>,
    ko: bool,
    charge: bool,
}

impl CorePosition {
    fn with_untouched(coin_count: usize) -> Self {
        debug_assert!(coin_count <= 384);
        let mut untouched = [0u128; 3];
        for coin in 0..coin_count {
            untouched[coin / 128] |= 1u128 << (coin % 128);
        }
        CorePosition {
            untouched,
            queue: VecDeque::new(),
            ko: false,
            charge: false,
        }
    }

    fn is_untouched(&self, coin: usize) -> bool {
        self.untouched[coin / 128] & (1u128 << (coin % 128)) != 0
    }

    fn open(&mut self, coin: usize) {
        self.untouched[coin / 128] &= !(1u128 << (coin % 128));
    }

    fn untouched_count(&self) -> usize {
        self.untouched
            .iter()
            .map(|word| word.count_ones() as usize)
            .sum()
    }

    fn untouched_empty(&self) -> bool {
        self.untouched.iter().all(|&word| word == 0)
    }
}

/// A coherent position of the arena. Fields are opaque so positions cannot be
/// forged for a different arena.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WittFifoPosition {
    owner: Arc<()>,
    owner_id: usize,
    core: Option<CorePosition>,
}

impl WittFifoPosition {
    /// Number of loaded coins not yet opened.
    pub fn untouched_count(&self) -> usize {
        self.core.as_ref().map_or(0, CorePosition::untouched_count)
    }

    /// FIFO queue of coins that are open and not yet closed.
    pub fn queue(&self) -> impl Iterator<Item = WittFifoCoinId> + '_ {
        self.core.iter().flat_map(|core| core.queue.iter().copied())
    }

    /// Current one-step ko bit. The optionless sink reports `false`.
    pub fn ko(&self) -> bool {
        self.core.as_ref().is_some_and(|core| core.ko)
    }

    /// Accumulated binary charge. The optionless sink reports `false`.
    pub fn charge(&self) -> bool {
        self.core.as_ref().is_some_and(|core| core.charge)
    }

    /// Whether every coin has been opened and the FIFO queue has drained.
    pub fn is_drained(&self) -> bool {
        self.core
            .as_ref()
            .is_some_and(|core| core.queue.is_empty() && core.untouched_empty())
    }

    /// Whether this is the optionless sink reached by the charge-one tail.
    pub fn is_sink(&self) -> bool {
        self.core.is_none()
    }

    /// Exact number of core OPEN/CLOSE moves remaining. The optional tail is not
    /// included.
    pub fn core_clock(&self) -> usize {
        self.core
            .as_ref()
            .map_or(0, |core| 2 * core.untouched_count() + core.queue.len())
    }
}

/// One impartial arena move.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WittFifoMove {
    /// Open one untouched coin and append it to the FIFO.
    Open(WittFifoCoinId),
    /// Close the FIFO front.
    Close,
    /// Take the unique charge-one tail move to the optionless sink.
    Tail,
}

/// Checked-construction or finite-unfolding failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WittFifoError {
    /// The bitmask representation supports at most 128 original coordinates.
    DimensionTooLarge {
        /// Supplied original dimension.
        dimension: usize,
    },
    /// Diagonal and polar rows must have the same length.
    ShapeMismatch {
        /// Number of supplied diagonal entries.
        diagonal: usize,
        /// Number of supplied polar rows.
        polar: usize,
    },
    /// A polar row contains a bit outside the declared dimension.
    PolarRowOutOfRange {
        /// Offending row index.
        row: usize,
    },
    /// An alternating polar form must have zero diagonal.
    PolarDiagonalNonzero {
        /// Offending diagonal index.
        index: usize,
    },
    /// The supplied polar matrix is not symmetric.
    PolarNotSymmetric {
        /// First mismatched coordinate.
        i: usize,
        /// Second mismatched coordinate.
        j: usize,
    },
    /// The input vector contains a coordinate outside the declared dimension.
    InputOutOfRange,
    /// A move is not legal from the supplied position.
    IllegalMove,
    /// The position was created by a different arena instance.
    PositionArenaMismatch,
    /// Unfolding reached the caller's explicit state budget.
    StateBudgetExceeded {
        /// Maximum number of memoized states allowed.
        budget: usize,
    },
}

impl fmt::Display for WittFifoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DimensionTooLarge { dimension } => write!(
                f,
                "Witt--FIFO uses u128 coordinates, so dimension {dimension} exceeds 128"
            ),
            Self::ShapeMismatch { diagonal, polar } => write!(
                f,
                "Witt--FIFO needs one polar row per diagonal entry, got {diagonal} and {polar}"
            ),
            Self::PolarRowOutOfRange { row } => {
                write!(
                    f,
                    "polar row {row} has a bit outside the declared dimension"
                )
            }
            Self::PolarDiagonalNonzero { index } => {
                write!(f, "alternating polar entry b[{index},{index}] must be zero")
            }
            Self::PolarNotSymmetric { i, j } => {
                write!(f, "polar entries b[{i},{j}] and b[{j},{i}] disagree")
            }
            Self::InputOutOfRange => f.write_str("input vector is outside the declared F_2 space"),
            Self::IllegalMove => f.write_str("illegal Witt--FIFO move"),
            Self::PositionArenaMismatch => {
                f.write_str("Witt--FIFO position belongs to a different arena")
            }
            Self::StateBudgetExceeded { budget } => {
                write!(f, "Witt--FIFO unfolding exceeded state budget {budget}")
            }
        }
    }
}

impl std::error::Error for WittFifoError {}

/// Compact rules and loaded data for one weighted-source Witt--FIFO arena.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WittFifoArena {
    owner: Arc<()>,
    dimension: usize,
    input: u128,
    adapted_basis: Vec<u128>,
    adapted_coordinates: u128,
    frame_mates: Vec<Option<usize>>,
    coins: Vec<WittFifoCoin>,
    quadratic_value: bool,
}

impl WittFifoArena {
    /// Construct the proved matching-plus-isolates realization of `Q(x)`.
    pub fn try_new(diagonal: &[bool], polar: &[u128], input: u128) -> Result<Self, WittFifoError> {
        validate_quadratic_data(diagonal, polar, input)?;
        let dimension = diagonal.len();
        let (adapted_basis, frame_mates) = adapted_frame(dimension, polar);
        let adapted_coordinates = coordinates_in_basis(input, &adapted_basis);

        let mut coins = Vec::new();
        let mut strategic = vec![None; dimension];
        for adapted_index in 0..dimension {
            if adapted_coordinates & (1u128 << adapted_index) == 0 {
                continue;
            }
            let id = WittFifoCoinId(coins.len());
            strategic[adapted_index] = Some(id);
            coins.push(WittFifoCoin {
                kind: WittFifoCoinKind::Strategic { adapted_index },
                potential_mate: None,
                edge_weight: false,
                close_charge: public_quadratic(adapted_basis[adapted_index], polar),
            });
        }

        for i in 0..dimension {
            let Some(j) = frame_mates[i] else {
                continue;
            };
            let (Some(ci), Some(cj)) = (strategic[i], strategic[j]) else {
                continue;
            };
            coins[ci.0].potential_mate = Some(cj);
            coins[ci.0].edge_weight = true;
        }

        for original_index in 0..dimension {
            if input & (1u128 << original_index) == 0 {
                continue;
            }
            let first = WittFifoCoinId(coins.len());
            let second = WittFifoCoinId(coins.len() + 1);
            let weight = diagonal[original_index];
            coins.push(WittFifoCoin {
                kind: WittFifoCoinKind::Source {
                    original_index,
                    endpoint: false,
                },
                potential_mate: Some(second),
                edge_weight: weight,
                close_charge: false,
            });
            coins.push(WittFifoCoin {
                kind: WittFifoCoinKind::Source {
                    original_index,
                    endpoint: true,
                },
                potential_mate: Some(first),
                edge_weight: weight,
                close_charge: false,
            });
        }

        Ok(Self {
            owner: Arc::new(()),
            dimension,
            input,
            adapted_basis,
            adapted_coordinates,
            frame_mates,
            coins,
            quadratic_value: evaluate_quadratic(input, diagonal, polar),
        })
    }

    /// Original `F_2` dimension.
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// Input vector in original-basis bitmask coordinates.
    pub fn input(&self) -> u128 {
        self.input
    }

    /// Deterministic adapted basis, as original-coordinate bitmasks.
    pub fn adapted_basis(&self) -> &[u128] {
        &self.adapted_basis
    }

    /// Coordinates of the input in the adapted basis.
    pub fn adapted_coordinates(&self) -> u128 {
        self.adapted_coordinates
    }

    /// Mate map on the full adapted frame; radical vectors have no mate.
    pub fn frame_mates(&self) -> &[Option<usize>] {
        &self.frame_mates
    }

    /// Loaded public coins in deterministic play order.
    pub fn coins(&self) -> &[WittFifoCoin] {
        &self.coins
    }

    /// Direct algebraic value `Q(x)`, retained as an independent oracle for
    /// callers and tests. Arena transitions do not consult it.
    pub fn quadratic_value(&self) -> bool {
        self.quadratic_value
    }

    /// Empty-queue, zero-charge root with every loaded coin untouched.
    pub fn initial(&self) -> WittFifoPosition {
        WittFifoPosition {
            owner: self.owner.clone(),
            owner_id: Arc::as_ptr(&self.owner) as usize,
            core: Some(CorePosition::with_untouched(self.coins.len())),
        }
    }

    fn validate_position(&self, position: &WittFifoPosition) -> Result<(), WittFifoError> {
        if !Arc::ptr_eq(&self.owner, &position.owner) {
            return Err(WittFifoError::PositionArenaMismatch);
        }
        if let Some(core) = &position.core {
            if core.queue.iter().any(|coin| coin.0 >= self.coins.len()) {
                return Err(WittFifoError::PositionArenaMismatch);
            }
        }
        Ok(())
    }

    /// Legal impartial moves from a coherent position, in deterministic order.
    pub fn legal_moves(
        &self,
        position: &WittFifoPosition,
    ) -> Result<Vec<WittFifoMove>, WittFifoError> {
        self.validate_position(position)?;
        let Some(core) = &position.core else {
            return Ok(Vec::new());
        };
        let untouched_empty = core.untouched_empty();
        if untouched_empty && core.queue.is_empty() {
            return Ok(if core.charge {
                vec![WittFifoMove::Tail]
            } else {
                Vec::new()
            });
        }

        let mut moves: Vec<WittFifoMove> = (0..self.coins.len())
            .filter(|&coin| core.is_untouched(coin))
            .map(|coin| WittFifoMove::Open(WittFifoCoinId(coin)))
            .collect();
        if !core.queue.is_empty() && (!core.ko || untouched_empty) {
            moves.push(WittFifoMove::Close);
        }
        Ok(moves)
    }

    /// Apply one checked arena move.
    pub fn play(
        &self,
        position: &WittFifoPosition,
        movement: WittFifoMove,
    ) -> Result<WittFifoPosition, WittFifoError> {
        self.validate_position(position)?;
        let Some(mut core) = position.core.clone() else {
            return Err(WittFifoError::IllegalMove);
        };
        match movement {
            WittFifoMove::Open(coin) => {
                if coin.0 >= self.coins.len() || !core.is_untouched(coin.0) {
                    return Err(WittFifoError::IllegalMove);
                }
                let was_empty = core.queue.is_empty();
                let data = self.coins[coin.0];
                if data
                    .potential_mate
                    .is_some_and(|mate| core.queue.contains(&mate))
                {
                    core.charge ^= data.edge_weight;
                }
                core.open(coin.0);
                core.queue.push_back(coin);
                core.ko = was_empty;
            }
            WittFifoMove::Close => {
                let untouched_empty = core.untouched_empty();
                if core.queue.is_empty() || (core.ko && !untouched_empty) {
                    return Err(WittFifoError::IllegalMove);
                }
                let front = core.queue.pop_front().expect("queue was checked nonempty");
                core.charge ^= self.coins[front.0].close_charge;
                core.ko = false;
            }
            WittFifoMove::Tail => {
                let drained = core.queue.is_empty() && core.untouched_empty();
                if !drained || !core.charge {
                    return Err(WittFifoError::IllegalMove);
                }
                return Ok(WittFifoPosition {
                    owner: position.owner.clone(),
                    owner_id: position.owner_id,
                    core: None,
                });
            }
        }
        Ok(WittFifoPosition {
            owner: position.owner.clone(),
            owner_id: position.owner_id,
            core: Some(core),
        })
    }

    /// The deterministic public matching move used whenever the designated seat
    /// controls the current position.
    pub fn matching_strategy_move(
        &self,
        position: &WittFifoPosition,
    ) -> Result<Option<WittFifoMove>, WittFifoError> {
        self.validate_position(position)?;
        let Some(core) = &position.core else {
            return Ok(None);
        };
        if !core.untouched_empty() {
            if let Some(&front) = core.queue.front() {
                if let Some(mate) = self.coins[front.0].potential_mate {
                    if core.is_untouched(mate.0) {
                        return Ok(Some(WittFifoMove::Open(mate)));
                    }
                }
            }
            let least = (0..self.coins.len())
                .find(|&coin| core.is_untouched(coin))
                .expect("an untouched coin exists");
            return Ok(Some(WittFifoMove::Open(WittFifoCoinId(least))));
        }
        if !core.queue.is_empty() {
            return Ok(Some(WittFifoMove::Close));
        }
        Ok(core.charge.then_some(WittFifoMove::Tail))
    }

    /// Grundy value of the loaded root, with an explicit memoized-state budget.
    pub fn grundy(&self, state_budget: usize) -> Result<u128, WittFifoError> {
        fn visit(
            arena: &WittFifoArena,
            position: &WittFifoPosition,
            state_budget: usize,
            memo: &mut HashMap<WittFifoPosition, u128>,
        ) -> Result<u128, WittFifoError> {
            if let Some(&value) = memo.get(position) {
                return Ok(value);
            }
            if memo.len() >= state_budget {
                return Err(WittFifoError::StateBudgetExceeded {
                    budget: state_budget,
                });
            }
            let mut option_values = Vec::new();
            for movement in arena.legal_moves(position)? {
                let next = arena.play(position, movement)?;
                option_values.push(visit(arena, &next, state_budget, memo)?);
            }
            let value = mex(option_values);
            memo.insert(position.clone(), value);
            Ok(value)
        }

        visit(self, &self.initial(), state_budget, &mut HashMap::new())
    }

    /// Materialize the loaded root as an ordinary finite impartial [`Game`].
    /// The arena remains the preferred compact representation.
    pub fn to_game(&self, state_budget: usize) -> Result<Game, WittFifoError> {
        fn visit(
            arena: &WittFifoArena,
            position: &WittFifoPosition,
            state_budget: usize,
            memo: &mut HashMap<WittFifoPosition, Game>,
        ) -> Result<Game, WittFifoError> {
            if let Some(game) = memo.get(position) {
                return Ok(game.clone());
            }
            if memo.len() >= state_budget {
                return Err(WittFifoError::StateBudgetExceeded {
                    budget: state_budget,
                });
            }
            let mut options = Vec::new();
            for movement in arena.legal_moves(position)? {
                let next = arena.play(position, movement)?;
                options.push(visit(arena, &next, state_budget, memo)?);
            }
            let game = Game::new(options.clone(), options);
            memo.insert(position.clone(), game.clone());
            Ok(game)
        }

        visit(self, &self.initial(), state_budget, &mut HashMap::new())
    }
}

fn coordinate_mask(dimension: usize) -> u128 {
    if dimension == 128 {
        u128::MAX
    } else if dimension == 0 {
        0
    } else {
        (1u128 << dimension) - 1
    }
}

fn validate_quadratic_data(
    diagonal: &[bool],
    polar: &[u128],
    input: u128,
) -> Result<(), WittFifoError> {
    let dimension = diagonal.len();
    if dimension > 128 {
        return Err(WittFifoError::DimensionTooLarge { dimension });
    }
    if polar.len() != dimension {
        return Err(WittFifoError::ShapeMismatch {
            diagonal: dimension,
            polar: polar.len(),
        });
    }
    let mask = coordinate_mask(dimension);
    if input & !mask != 0 {
        return Err(WittFifoError::InputOutOfRange);
    }
    for (i, &row) in polar.iter().enumerate() {
        if row & !mask != 0 {
            return Err(WittFifoError::PolarRowOutOfRange { row: i });
        }
        if row & (1u128 << i) != 0 {
            return Err(WittFifoError::PolarDiagonalNonzero { index: i });
        }
        for j in (i + 1)..dimension {
            if ((row >> j) & 1) != ((polar[j] >> i) & 1) {
                return Err(WittFifoError::PolarNotSymmetric { i, j });
            }
        }
    }
    Ok(())
}

fn polar_pair(mut left: u128, right: u128, polar: &[u128]) -> bool {
    let mut value = false;
    while left != 0 {
        let i = left.trailing_zeros() as usize;
        left &= left - 1;
        value ^= (polar[i] & right).count_ones() & 1 == 1;
    }
    value
}

fn public_quadratic(mut vector: u128, polar: &[u128]) -> bool {
    let mut value = false;
    while vector != 0 {
        let i = vector.trailing_zeros() as usize;
        vector &= vector - 1;
        let above = if i == 127 { 0 } else { (!0u128) << (i + 1) };
        value ^= (polar[i] & vector & above).count_ones() & 1 == 1;
    }
    value
}

fn evaluate_quadratic(vector: u128, diagonal: &[bool], polar: &[u128]) -> bool {
    let mut value = public_quadratic(vector, polar);
    let mut active = vector;
    while active != 0 {
        let i = active.trailing_zeros() as usize;
        active &= active - 1;
        value ^= diagonal[i];
    }
    value
}

fn adapted_frame(dimension: usize, polar: &[u128]) -> (Vec<u128>, Vec<Option<usize>>) {
    let mut remaining: Vec<u128> = (0..dimension).map(|i| 1u128 << i).collect();
    let mut basis = Vec::with_capacity(dimension);
    let mut mates = Vec::with_capacity(dimension);
    while !remaining.is_empty() {
        let left = remaining.remove(0);
        if let Some(position) = remaining
            .iter()
            .position(|&right| polar_pair(left, right, polar))
        {
            let right = remaining.remove(position);
            for vector in &mut remaining {
                if polar_pair(*vector, right, polar) {
                    *vector ^= left;
                }
                if polar_pair(*vector, left, polar) {
                    *vector ^= right;
                }
            }
            let left_index = basis.len();
            let right_index = left_index + 1;
            basis.push(left);
            mates.push(Some(right_index));
            basis.push(right);
            mates.push(Some(left_index));
        } else {
            basis.push(left);
            mates.push(None);
        }
    }
    (basis, mates)
}

fn coordinates_in_basis(mut vector: u128, basis: &[u128]) -> u128 {
    let mut pivots: [Option<(u128, u128)>; 128] = [None; 128];
    for (i, &basis_vector) in basis.iter().enumerate() {
        let mut row = basis_vector;
        let mut coordinates = 1u128 << i;
        while row != 0 {
            let column = row.trailing_zeros() as usize;
            if let Some((pivot, pivot_coordinates)) = pivots[column] {
                row ^= pivot;
                coordinates ^= pivot_coordinates;
            } else {
                pivots[column] = Some((row, coordinates));
                break;
            }
        }
    }

    let mut coordinates = 0u128;
    while vector != 0 {
        let column = vector.trailing_zeros() as usize;
        let (pivot, pivot_coordinates) =
            pivots[column].expect("the adapted frame is a basis of the full space");
        vector ^= pivot;
        coordinates ^= pivot_coordinates;
    }
    coordinates
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_malformed_quadratic_data() {
        assert!(matches!(
            WittFifoArena::try_new(&[false], &[], 0),
            Err(WittFifoError::ShapeMismatch { .. })
        ));
        assert!(matches!(
            WittFifoArena::try_new(&[false], &[1], 0),
            Err(WittFifoError::PolarDiagonalNonzero { .. })
        ));
        assert!(matches!(
            WittFifoArena::try_new(&[false, false], &[2, 0], 0),
            Err(WittFifoError::PolarNotSymmetric { .. })
        ));
        assert!(matches!(
            WittFifoArena::try_new(&[false], &[0], 2),
            Err(WittFifoError::InputOutOfRange)
        ));
    }

    #[test]
    fn positions_are_owned_by_their_constructing_arena() {
        let first = WittFifoArena::try_new(&[false], &[0], 1).unwrap();
        let second = WittFifoArena::try_new(&[false], &[0], 1).unwrap();
        assert_eq!(first, second);
        assert_eq!(
            second.legal_moves(&first.initial()),
            Err(WittFifoError::PositionArenaMismatch)
        );
    }

    #[test]
    fn potential_source_pair_survives_zero_weight() {
        let arena = WittFifoArena::try_new(&[false], &[0], 1).unwrap();
        assert_eq!(arena.coins().len(), 3);
        let sources: Vec<_> = arena
            .coins()
            .iter()
            .filter(|coin| matches!(coin.kind(), WittFifoCoinKind::Source { .. }))
            .collect();
        assert_eq!(sources.len(), 2);
        assert!(sources.iter().all(|coin| coin.potential_mate().is_some()));
        assert!(sources.iter().all(|coin| !coin.edge_weight()));
    }

    #[test]
    fn every_core_move_drops_the_exact_clock() {
        let arena = WittFifoArena::try_new(&[true], &[0], 1).unwrap();
        let root = arena.initial();
        for movement in arena.legal_moves(&root).unwrap() {
            let next = arena.play(&root, movement).unwrap();
            assert_eq!(root.core_clock(), next.core_clock() + 1);
        }
    }

    #[test]
    fn small_roots_realize_the_quadratic_zero_set() {
        let cases = [
            (vec![], vec![], 0),
            (vec![false], vec![0], 0),
            (vec![false], vec![0], 1),
            (vec![true], vec![0], 1),
            (vec![false, false], vec![0b10, 0b01], 0b01),
            (vec![false, false], vec![0b10, 0b01], 0b11),
            (vec![true, false], vec![0b10, 0b01], 0b11),
        ];
        for (diagonal, polar, input) in cases {
            let arena = WittFifoArena::try_new(&diagonal, &polar, input).unwrap();
            let grundy = arena.grundy(1_000_000).unwrap();
            assert_eq!(grundy == 0, !arena.quadratic_value());
            let game = arena.to_game(1_000_000).unwrap();
            assert_eq!(
                game.outcome_class(),
                if grundy == 0 {
                    crate::games::PartizanOutcome::P
                } else {
                    crate::games::PartizanOutcome::N
                }
            );
        }
    }

    #[test]
    fn static_loaded_charge_identity_is_exhaustive_through_dimension_four() {
        for dimension in 0..=4usize {
            let edges = dimension * dimension.saturating_sub(1) / 2;
            for edge_mask in 0..(1usize << edges) {
                let mut polar = vec![0u128; dimension];
                let mut edge = 0usize;
                for i in 0..dimension {
                    for j in (i + 1)..dimension {
                        if edge_mask & (1usize << edge) != 0 {
                            polar[i] |= 1u128 << j;
                            polar[j] |= 1u128 << i;
                        }
                        edge += 1;
                    }
                }
                for diagonal_mask in 0..(1u128 << dimension) {
                    let diagonal: Vec<bool> = (0..dimension)
                        .map(|i| diagonal_mask & (1u128 << i) != 0)
                        .collect();
                    for input in 0..(1u128 << dimension) {
                        let arena = WittFifoArena::try_new(&diagonal, &polar, input).unwrap();
                        let mut loaded_charge = false;
                        for (i, coin) in arena.coins().iter().enumerate() {
                            loaded_charge ^= coin.close_charge();
                            if coin.potential_mate().is_some_and(|mate| i < mate.index()) {
                                loaded_charge ^= coin.edge_weight();
                            }
                        }
                        assert_eq!(loaded_charge, arena.quadratic_value());
                    }
                }
            }
        }
    }

    #[test]
    fn public_matching_strategy_forces_the_charge_for_either_seat() {
        fn forces(
            arena: &WittFifoArena,
            position: &WittFifoPosition,
            designated_seat: bool,
            to_move: bool,
            target: bool,
            memo: &mut HashMap<(WittFifoPosition, bool), bool>,
        ) -> bool {
            if position.is_drained() {
                return position.charge() == target;
            }
            if let Some(&answer) = memo.get(&(position.clone(), to_move)) {
                return answer;
            }
            let answer = if to_move == designated_seat {
                let movement = arena
                    .matching_strategy_move(position)
                    .unwrap()
                    .expect("a non-drained core has a strategy move");
                let next = arena.play(position, movement).unwrap();
                forces(arena, &next, designated_seat, !to_move, target, memo)
            } else {
                arena
                    .legal_moves(position)
                    .unwrap()
                    .into_iter()
                    .all(|movement| {
                        let next = arena.play(position, movement).unwrap();
                        forces(arena, &next, designated_seat, !to_move, target, memo)
                    })
            };
            memo.insert((position.clone(), to_move), answer);
            answer
        }

        let arena = WittFifoArena::try_new(&[true, false], &[0b10, 0b01], 0b11).unwrap();
        for designated_seat in [false, true] {
            assert!(forces(
                &arena,
                &arena.initial(),
                designated_seat,
                false,
                arena.quadratic_value(),
                &mut HashMap::new(),
            ));
        }
    }

    #[test]
    fn charge_one_drained_position_has_exactly_the_tail() {
        let arena = WittFifoArena::try_new(&[true], &[0], 1).unwrap();
        let mut position = arena.initial();
        while !position.is_drained() {
            let movement = arena.matching_strategy_move(&position).unwrap().unwrap();
            position = arena.play(&position, movement).unwrap();
        }
        assert!(position.charge());
        assert_eq!(
            arena.legal_moves(&position).unwrap(),
            vec![WittFifoMove::Tail]
        );
        let sink = arena.play(&position, WittFifoMove::Tail).unwrap();
        assert!(sink.is_sink());
        assert!(arena.legal_moves(&sink).unwrap().is_empty());
    }

    #[test]
    fn packed_position_covers_the_full_384_coin_bound() {
        let diagonal = vec![false; 128];
        let polar = vec![0u128; 128];
        let arena = WittFifoArena::try_new(&diagonal, &polar, u128::MAX).unwrap();
        assert_eq!(arena.coins().len(), 384);

        let mut position = arena.initial();
        assert_eq!(position.untouched_count(), 384);
        for coin in 0..384 {
            position = arena
                .play(&position, WittFifoMove::Open(WittFifoCoinId(coin)))
                .unwrap();
        }
        assert_eq!(position.untouched_count(), 0);
        assert_eq!(position.queue().count(), 384);
        for _ in 0..384 {
            position = arena.play(&position, WittFifoMove::Close).unwrap();
        }
        assert!(position.is_drained());
    }
}
