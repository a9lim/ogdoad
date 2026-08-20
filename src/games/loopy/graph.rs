//! The graph-level engine: [`LoopyGraph`], a thin wrapper over
//! [`kernel::outcomes`](crate::games::kernel).

use crate::games::kernel::{self, Outcome};
use std::sync::OnceLock;

use super::catalogue::LoopyValue;

/// A loopy game as a finite move graph (`succ[v]` = the positions reachable from
/// `v` in one move). The move graph may be cyclic; outcomes are computed by the
/// retrograde [`kernel::outcomes`](crate::games::outcomes) (Win / Loss / Draw,
/// where **Loss = P-position** and **Draw = the loopy escape**).
#[derive(Debug)]
pub struct LoopyGraph {
    succ: Vec<Vec<usize>>,
    outcomes: OnceLock<Vec<Outcome>>,
}

impl Clone for LoopyGraph {
    fn clone(&self) -> Self {
        let outcomes = OnceLock::new();
        if let Some(cached) = self.outcomes.get() {
            outcomes
                .set(cached.clone())
                .expect("fresh outcome cache accepts one value");
        }
        LoopyGraph {
            succ: self.succ.clone(),
            outcomes,
        }
    }
}

impl PartialEq for LoopyGraph {
    fn eq(&self, other: &Self) -> bool {
        self.succ == other.succ
    }
}

impl Eq for LoopyGraph {}

impl LoopyGraph {
    /// Build from explicit adjacency lists.
    pub fn new(succ: Vec<Vec<usize>>) -> LoopyGraph {
        LoopyGraph {
            succ,
            outcomes: OnceLock::new(),
        }
    }

    /// Build from a move rule on positions `0..n` (the rule may produce cycles).
    pub fn from_rule<F: Fn(usize) -> Vec<usize>>(n: usize, moves: F) -> LoopyGraph {
        LoopyGraph {
            succ: (0..n).map(moves).collect(),
            outcomes: OnceLock::new(),
        }
    }

    /// The adjacency lists.
    pub fn succ(&self) -> &[Vec<usize>] {
        &self.succ
    }

    /// Win / Loss / Draw of every position (retrograde analysis).
    pub fn outcomes(&self) -> &[Outcome] {
        self.outcomes
            .get_or_init(|| kernel::outcomes(&self.succ))
            .as_slice()
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
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, o)| *o == want)
            .map(|(i, _)| i)
            .collect()
    }

    /// A coarse reading of a position as a catalogue [`LoopyValue`], via its
    /// impartial outcome only: a **Loss** is `0`, a **Draw** is `dud`. A **Win** is
    /// `None` — its value is a nonzero loopy nimber (use [`loopy_nim_values`](crate::games::loopy_nim_values)), not
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn outcome_analysis_is_cached() {
        let graph = LoopyGraph::new(vec![vec![1], vec![]]);
        let first = graph.outcomes().as_ptr();
        let second = graph.outcomes().as_ptr();
        assert_eq!(first, second);
    }
}
