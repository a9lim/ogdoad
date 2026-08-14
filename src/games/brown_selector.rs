//! The intrinsic four-outcome Brown selector.
//!
//! A checked `Z/4`-quadratic form splits canonically as
//! `q = lift(ell) + 2Q`. [`BrownSelector::try_new`] constructs the single
//! partizan root `{ A_(Q+ell)(x) | A_Q(x) }`, where both followers are the full
//! weighted-source Witt--FIFO arenas. Its outcomes decode as
//! `N, R, P, L -> 0, 1, 2, 3`.

use crate::games::{Game, PartizanOutcome, WittFifoArena, WittFifoError};
use std::fmt;

/// Checked-construction or finite-unfolding failure for a Brown selector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BrownSelectorError {
    /// Basis values and off-diagonal polar rows must have equal length.
    ShapeMismatch {
        /// Number of basis values.
        values: usize,
        /// Number of polar rows.
        polar: usize,
    },
    /// A basis value is not a canonical residue in `0..4`.
    NoncanonicalValue {
        /// Offending basis index.
        index: usize,
        /// Supplied noncanonical value.
        value: u128,
    },
    /// An off-diagonal polar row contains a bit outside the dimension.
    PolarRowOutOfRange {
        /// Offending row index.
        row: usize,
    },
    /// Brown polar input carries only off-diagonal entries.
    PolarDiagonalNonzero {
        /// Offending diagonal index.
        index: usize,
    },
    /// The off-diagonal Brown polar is not symmetric.
    PolarNotSymmetric {
        /// First mismatched coordinate.
        i: usize,
        /// Second mismatched coordinate.
        j: usize,
    },
    /// The input vector contains a coordinate outside the dimension.
    InputOutOfRange,
    /// Construction or unfolding of an ordinary quadratic follower failed.
    WittFifo(WittFifoError),
}

impl fmt::Display for BrownSelectorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ShapeMismatch { values, polar } => write!(
                f,
                "Brown selector needs one polar row per basis value, got {values} and {polar}"
            ),
            Self::NoncanonicalValue { index, value } => {
                write!(f, "Brown value q4[{index}]={value} is not in 0..4")
            }
            Self::PolarRowOutOfRange { row } => {
                write!(f, "Brown polar row {row} exceeds the declared dimension")
            }
            Self::PolarDiagonalNonzero { index } => write!(
                f,
                "Brown polar input is off-diagonal, so b[{index},{index}] must be zero"
            ),
            Self::PolarNotSymmetric { i, j } => {
                write!(f, "Brown polar entries b[{i},{j}] and b[{j},{i}] disagree")
            }
            Self::InputOutOfRange => {
                f.write_str("Brown-selector input is outside the declared F_2 space")
            }
            Self::WittFifo(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for BrownSelectorError {}

impl From<WittFifoError> for BrownSelectorError {
    fn from(value: WittFifoError) -> Self {
        Self::WittFifo(value)
    }
}

/// One intrinsic Brown-selector root and its two ordinary quadratic followers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BrownSelector {
    linear_diagonal: Vec<bool>,
    classical_diagonal: Vec<bool>,
    classical_polar: Vec<u128>,
    input: u128,
    residue: u128,
    left: WittFifoArena,
    right: WittFifoArena,
}

impl BrownSelector {
    /// Construct `{ A_(Q+ell)(x) | A_Q(x) }` from basis values `q4` and the
    /// off-diagonal symmetric Brown polar.
    pub fn try_new(
        q4: &[u128],
        brown_polar: &[u128],
        input: u128,
    ) -> Result<Self, BrownSelectorError> {
        validate_brown_data(q4, brown_polar, input)?;
        let dimension = q4.len();
        let linear_diagonal: Vec<bool> = q4.iter().map(|value| value & 1 == 1).collect();
        let classical_diagonal: Vec<bool> = q4.iter().map(|value| (value >> 1) & 1 == 1).collect();
        let mut classical_polar = brown_polar.to_vec();
        for i in 0..dimension {
            if !linear_diagonal[i] {
                continue;
            }
            for j in (i + 1)..dimension {
                if linear_diagonal[j] {
                    classical_polar[i] ^= 1u128 << j;
                    classical_polar[j] ^= 1u128 << i;
                }
            }
        }
        let left_diagonal: Vec<bool> = classical_diagonal
            .iter()
            .zip(&linear_diagonal)
            .map(|(&quadratic, &linear)| quadratic ^ linear)
            .collect();
        let left = WittFifoArena::try_new(&left_diagonal, &classical_polar, input)?;
        let right = WittFifoArena::try_new(&classical_diagonal, &classical_polar, input)?;

        Ok(Self {
            linear_diagonal,
            classical_diagonal,
            classical_polar,
            input,
            residue: evaluate_brown(input, q4, brown_polar),
            left,
            right,
        })
    }

    /// Basis values of the canonical linear part `ell`.
    pub fn linear_diagonal(&self) -> &[bool] {
        &self.linear_diagonal
    }

    /// Basis values of the canonical ordinary quadratic part `Q`.
    pub fn classical_diagonal(&self) -> &[bool] {
        &self.classical_diagonal
    }

    /// Corrected alternating polar `B_Q = b + ell tensor ell`.
    pub fn classical_polar(&self) -> &[u128] {
        &self.classical_polar
    }

    /// Input vector in original-basis bitmask coordinates.
    pub fn input(&self) -> u128 {
        self.input
    }

    /// Directly evaluated Brown residue `q(x)` in `0..4`.
    pub fn residue(&self) -> u128 {
        self.residue
    }

    /// Unique Left follower `A_(Q+ell)(x)`.
    pub fn left_follower(&self) -> &WittFifoArena {
        &self.left
    }

    /// Unique Right follower `A_Q(x)`.
    pub fn right_follower(&self) -> &WittFifoArena {
        &self.right
    }

    /// Materialize the one-root selector as a finite short [`Game`]. The budget
    /// applies independently to each ordinary follower.
    pub fn to_game(&self, state_budget_per_follower: usize) -> Result<Game, BrownSelectorError> {
        Ok(Game::new(
            vec![self.left.to_game(state_budget_per_follower)?],
            vec![self.right.to_game(state_budget_per_follower)?],
        ))
    }

    /// Compute the selector's intrinsic normal-play outcome from the actual game.
    pub fn outcome_class(
        &self,
        state_budget_per_follower: usize,
    ) -> Result<PartizanOutcome, BrownSelectorError> {
        Ok(self.to_game(state_budget_per_follower)?.outcome_class())
    }

    /// Decode `N, R, P, L` as `0, 1, 2, 3`. Draws are outside the finite
    /// selector's image.
    pub fn decode_outcome(outcome: PartizanOutcome) -> Option<u128> {
        match outcome {
            PartizanOutcome::N => Some(0),
            PartizanOutcome::R => Some(1),
            PartizanOutcome::P => Some(2),
            PartizanOutcome::L => Some(3),
            PartizanOutcome::Draw => None,
        }
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

fn validate_brown_data(q4: &[u128], polar: &[u128], input: u128) -> Result<(), BrownSelectorError> {
    if q4.len() != polar.len() {
        return Err(BrownSelectorError::ShapeMismatch {
            values: q4.len(),
            polar: polar.len(),
        });
    }
    if q4.len() > 128 {
        return Err(BrownSelectorError::WittFifo(
            WittFifoError::DimensionTooLarge {
                dimension: q4.len(),
            },
        ));
    }
    for (index, &value) in q4.iter().enumerate() {
        if value >= 4 {
            return Err(BrownSelectorError::NoncanonicalValue { index, value });
        }
    }
    let mask = coordinate_mask(q4.len());
    if input & !mask != 0 {
        return Err(BrownSelectorError::InputOutOfRange);
    }
    for (i, &row) in polar.iter().enumerate() {
        if row & !mask != 0 {
            return Err(BrownSelectorError::PolarRowOutOfRange { row: i });
        }
        if row & (1u128 << i) != 0 {
            return Err(BrownSelectorError::PolarDiagonalNonzero { index: i });
        }
        for j in (i + 1)..q4.len() {
            if ((row >> j) & 1) != ((polar[j] >> i) & 1) {
                return Err(BrownSelectorError::PolarNotSymmetric { i, j });
            }
        }
    }
    Ok(())
}

fn evaluate_brown(mut vector: u128, q4: &[u128], polar: &[u128]) -> u128 {
    let original = vector;
    let mut value = 0u128;
    let mut cross = false;
    while vector != 0 {
        let i = vector.trailing_zeros() as usize;
        vector &= vector - 1;
        value += q4[i];
        let above = if i == 127 { 0 } else { (!0u128) << (i + 1) };
        cross ^= (polar[i] & original & above).count_ones() & 1 == 1;
    }
    (value + if cross { 2 } else { 0 }) % 4
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_noncanonical_or_incoherent_input() {
        assert!(matches!(
            BrownSelector::try_new(&[4], &[0], 0),
            Err(BrownSelectorError::NoncanonicalValue { .. })
        ));
        assert!(matches!(
            BrownSelector::try_new(&[0, 0], &[2, 0], 0),
            Err(BrownSelectorError::PolarNotSymmetric { .. })
        ));
    }

    #[test]
    fn canonical_split_has_corrected_polar() {
        let selector = BrownSelector::try_new(&[1, 1], &[0, 0], 0b11).unwrap();
        assert_eq!(selector.linear_diagonal(), &[true, true]);
        assert_eq!(selector.classical_diagonal(), &[false, false]);
        assert_eq!(selector.classical_polar(), &[0b10, 0b01]);
        assert_eq!(selector.residue(), 2);
    }

    #[test]
    fn actual_selector_game_realizes_all_four_outcomes() {
        let expected = [
            PartizanOutcome::N,
            PartizanOutcome::R,
            PartizanOutcome::P,
            PartizanOutcome::L,
        ];
        for residue in 0..4u128 {
            let selector = BrownSelector::try_new(&[residue], &[0], 1).unwrap();
            let outcome = selector.outcome_class(100_000).unwrap();
            assert_eq!(outcome, expected[residue as usize]);
            assert_eq!(BrownSelector::decode_outcome(outcome), Some(residue));
            assert_eq!(selector.residue(), residue);
            let game = selector.to_game(100_000).unwrap();
            assert_eq!(game.left().len(), 1);
            assert_eq!(game.right().len(), 1);
        }
    }

    #[test]
    fn canonical_split_recomposes_every_brown_form_through_dimension_three() {
        for dimension in 0..=3usize {
            let edges = dimension * dimension.saturating_sub(1) / 2;
            for edge_mask in 0..(1usize << edges) {
                let mut brown_polar = vec![0u128; dimension];
                let mut edge = 0usize;
                for i in 0..dimension {
                    for j in (i + 1)..dimension {
                        if edge_mask & (1usize << edge) != 0 {
                            brown_polar[i] |= 1u128 << j;
                            brown_polar[j] |= 1u128 << i;
                        }
                        edge += 1;
                    }
                }
                for value_code in 0..4usize.pow(dimension as u32) {
                    let mut code = value_code;
                    let mut q4 = vec![0u128; dimension];
                    for value in &mut q4 {
                        *value = (code % 4) as u128;
                        code /= 4;
                    }
                    for input in 0..(1u128 << dimension) {
                        let selector = BrownSelector::try_new(&q4, &brown_polar, input).unwrap();
                        let mut linear = false;
                        let mut active = input;
                        while active != 0 {
                            let i = active.trailing_zeros() as usize;
                            active &= active - 1;
                            linear ^= selector.linear_diagonal()[i];
                        }
                        let quadratic = selector.right_follower().quadratic_value();
                        assert_eq!(
                            selector.residue(),
                            (linear as u128 + 2 * quadratic as u128) % 4
                        );
                        assert_eq!(
                            selector.left_follower().quadratic_value(),
                            quadratic ^ linear
                        );
                    }
                }
            }
        }
    }
}
