//! Certifying retrograde analysis for finite partizan game graphs.
//!
//! [`LoopyPartizanGraph::certify_outcomes`] labels every turn-state
//! `(node, mover)` Win, Loss, or Draw for the player to move, with ranks and
//! chosen moves. [`LoopyPartizanGraph::verify_outcome_certificate`] checks a
//! certificate by local conditions alone, in `O(V + E)`, independent of the
//! solver that produced it:
//!
//! * **Win** of rank `r > 0`: the chosen move reaches an opponent **Loss** of
//!   rank `< r`. Rank 0 is a terminal state, a win only in misère play.
//! * **Loss** of rank `r`: every move reaches an opponent **Win** of rank
//!   `< r`. A terminal state is a rank-0 loss in normal play.
//! * **Draw**: not terminal, no move reaches an opponent **Loss**, and the
//!   chosen move reaches a **Draw**.
//!
//! Win and Loss labels are sound by induction on rank. A player at a Draw
//! state who keeps choosing Draw successors never reaches a Loss state, and no
//! move from a Draw state reaches one, so neither player can force a win.
//! Conversely the retrograde stages supply such ranks, so the labeling is
//! exactly the optimal-play partition. Ranks need not be optimal distances.

use std::collections::VecDeque;
use std::fmt;

use super::{LoopyMover, LoopyPartizanGraph, LoopyPartizanOutcome, LoopyWinner};

/// Which terminal positions are wins.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PlayConvention {
    /// A player with no move loses.
    Normal,
    /// A player with no move wins.
    Misere,
}

/// The verdict of a turn-state for the player to move.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum StateVerdict {
    /// The mover can force a finite win.
    Win,
    /// The opponent can force a finite win.
    Loss,
    /// Neither player can force a win.
    Draw,
}

/// One turn-state's label.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct StateLabel {
    /// The verdict for the player to move.
    pub verdict: StateVerdict,
    /// The rank for Win and Loss labels; zero for Draw.
    pub rank: u128,
    /// The chosen successor turn-state, for Win (rank > 0) and Draw.
    pub chosen: Option<usize>,
}

/// A full labeling of a graph's turn-states. State `2v` is node `v` with Left
/// to move; state `2v + 1` is node `v` with Right to move.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutcomeCertificate {
    /// The play convention.
    pub convention: PlayConvention,
    /// One label per turn-state.
    pub labels: Vec<StateLabel>,
}

/// Why a certificate fails its check.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CertificateError {
    /// The label count is not twice the node count.
    LabelCount {
        /// Twice the node count.
        expected: usize,
        /// Labels supplied.
        found: usize,
    },
    /// A label's condition fails at a turn-state.
    Condition {
        /// The turn-state.
        state: usize,
        /// Which condition failed.
        reason: &'static str,
    },
}

impl fmt::Display for CertificateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CertificateError::LabelCount { expected, found } => {
                write!(f, "expected {expected} turn-state labels, found {found}")
            }
            CertificateError::Condition { state, reason } => {
                let (node, mover) = state_parts(*state);
                let mover = match mover {
                    LoopyMover::Left => 'L',
                    LoopyMover::Right => 'R',
                };
                write!(f, "turn-state {node}:{mover}: {reason}")
            }
        }
    }
}

impl std::error::Error for CertificateError {}

fn state(node: usize, mover: LoopyMover) -> usize {
    2 * node
        + match mover {
            LoopyMover::Left => 0,
            LoopyMover::Right => 1,
        }
}

fn state_parts(s: usize) -> (usize, LoopyMover) {
    (
        s / 2,
        if s.is_multiple_of(2) {
            LoopyMover::Left
        } else {
            LoopyMover::Right
        },
    )
}

fn successors(graph: &LoopyPartizanGraph, s: usize) -> Vec<usize> {
    let (node, mover) = state_parts(s);
    match mover {
        LoopyMover::Left => graph.left()[node]
            .iter()
            .map(|&w| state(w, LoopyMover::Right))
            .collect(),
        LoopyMover::Right => graph.right()[node]
            .iter()
            .map(|&w| state(w, LoopyMover::Left))
            .collect(),
    }
}

impl LoopyPartizanGraph {
    /// Solve every turn-state under a convention, producing a certificate.
    pub fn certify_outcomes(&self, convention: PlayConvention) -> OutcomeCertificate {
        let n = self.node_count();
        let states = 2 * n;
        let succ: Vec<Vec<usize>> = (0..states).map(|s| successors(self, s)).collect();
        let mut pred = vec![Vec::new(); states];
        for (s, targets) in succ.iter().enumerate() {
            for &t in targets {
                pred[t].push(s);
            }
        }
        let mut remaining: Vec<usize> = succ.iter().map(Vec::len).collect();
        let mut labels: Vec<Option<StateLabel>> = vec![None; states];
        let mut queue = VecDeque::new();
        for s in 0..states {
            if succ[s].is_empty() {
                labels[s] = Some(StateLabel {
                    verdict: match convention {
                        PlayConvention::Normal => StateVerdict::Loss,
                        PlayConvention::Misere => StateVerdict::Win,
                    },
                    rank: 0,
                    chosen: None,
                });
                queue.push_back(s);
            }
        }
        // FIFO order keeps ranks nondecreasing along the queue, so a Loss
        // labeled by its last Win successor exceeds every successor's rank.
        while let Some(t) = queue.pop_front() {
            let label = labels[t].expect("queued states are labeled");
            for &p in &pred[t] {
                if labels[p].is_some() {
                    continue;
                }
                match label.verdict {
                    StateVerdict::Loss => {
                        labels[p] = Some(StateLabel {
                            verdict: StateVerdict::Win,
                            rank: label.rank + 1,
                            chosen: Some(t),
                        });
                        queue.push_back(p);
                    }
                    StateVerdict::Win => {
                        remaining[p] -= 1;
                        if remaining[p] == 0 {
                            labels[p] = Some(StateLabel {
                                verdict: StateVerdict::Loss,
                                rank: label.rank + 1,
                                chosen: None,
                            });
                            queue.push_back(p);
                        }
                    }
                    StateVerdict::Draw => unreachable!("draws are assigned after the queue"),
                }
            }
        }
        let undecided: Vec<bool> = labels.iter().map(Option::is_none).collect();
        let labels = (0..states)
            .map(|s| {
                labels[s].unwrap_or_else(|| StateLabel {
                    verdict: StateVerdict::Draw,
                    rank: 0,
                    chosen: succ[s].iter().copied().find(|&t| undecided[t]),
                })
            })
            .collect();
        OutcomeCertificate { convention, labels }
    }

    /// Check a certificate by its local conditions, returning the outcome
    /// pair of every node.
    pub fn verify_outcome_certificate(
        &self,
        certificate: &OutcomeCertificate,
    ) -> Result<Vec<LoopyPartizanOutcome>, CertificateError> {
        let n = self.node_count();
        let labels = &certificate.labels;
        if labels.len() != 2 * n {
            return Err(CertificateError::LabelCount {
                expected: 2 * n,
                found: labels.len(),
            });
        }
        let fail = |state, reason| Err(CertificateError::Condition { state, reason });
        for (s, label) in labels.iter().enumerate() {
            let succ = successors(self, s);
            match label.verdict {
                StateVerdict::Win => {
                    if succ.is_empty() {
                        if certificate.convention != PlayConvention::Misere {
                            return fail(s, "a terminal state is a loss in normal play");
                        }
                        if label.rank != 0 || label.chosen.is_some() {
                            return fail(s, "a terminal win has rank 0 and no chosen move");
                        }
                        continue;
                    }
                    let Some(t) = label.chosen else {
                        return fail(s, "a win needs a chosen move");
                    };
                    if !succ.contains(&t) {
                        return fail(s, "the chosen move is not legal");
                    }
                    let target = labels[t];
                    if target.verdict != StateVerdict::Loss || target.rank >= label.rank {
                        return fail(
                            s,
                            "a win's chosen move must reach a lower-rank opponent loss",
                        );
                    }
                }
                StateVerdict::Loss => {
                    if succ.is_empty() {
                        if certificate.convention != PlayConvention::Normal {
                            return fail(s, "a terminal state is a win in misère play");
                        }
                        if label.rank != 0 {
                            return fail(s, "a terminal loss has rank 0");
                        }
                        continue;
                    }
                    if label.chosen.is_some() {
                        return fail(s, "a loss chooses no move");
                    }
                    for &t in &succ {
                        let target = labels[t];
                        if target.verdict != StateVerdict::Win || target.rank >= label.rank {
                            return fail(
                                s,
                                "every move from a loss must reach a lower-rank opponent win",
                            );
                        }
                    }
                }
                StateVerdict::Draw => {
                    if label.rank != 0 {
                        return fail(s, "a draw has rank 0");
                    }
                    if succ
                        .iter()
                        .any(|&t| labels[t].verdict == StateVerdict::Loss)
                    {
                        return fail(s, "a draw has no move to an opponent loss");
                    }
                    match label.chosen {
                        Some(t) if succ.contains(&t) && labels[t].verdict == StateVerdict::Draw => {
                        }
                        _ => return fail(s, "a draw's chosen move must reach a draw"),
                    }
                }
            }
        }
        Ok((0..n)
            .map(|v| {
                let side =
                    |s: usize, mover: LoopyWinner, opponent: LoopyWinner| match labels[s].verdict {
                        StateVerdict::Win => mover,
                        StateVerdict::Loss => opponent,
                        StateVerdict::Draw => LoopyWinner::Draw,
                    };
                LoopyPartizanOutcome::new(
                    side(
                        state(v, LoopyMover::Left),
                        LoopyWinner::Left,
                        LoopyWinner::Right,
                    ),
                    side(
                        state(v, LoopyMover::Right),
                        LoopyWinner::Right,
                        LoopyWinner::Left,
                    ),
                )
            })
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn graph(left: Vec<Vec<usize>>, right: Vec<Vec<usize>>) -> LoopyPartizanGraph {
        LoopyPartizanGraph::new(left, right).unwrap()
    }

    fn seeded_graphs() -> Vec<LoopyPartizanGraph> {
        let mut seed = 0x9e37_79b9_7f4a_7c15_u64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        (0..400)
            .map(|_| {
                let n = 1 + (next() % 7) as usize;
                let mut side = || {
                    (0..n)
                        .map(|_| {
                            (0..(next() % 3) as usize)
                                .map(|_| (next() % n as u64) as usize)
                                .collect()
                        })
                        .collect::<Vec<Vec<usize>>>()
                };
                let left = side();
                let right = side();
                graph(left, right)
            })
            .collect()
    }

    #[test]
    fn normal_certificates_verify_and_agree_with_the_solver() {
        for g in seeded_graphs() {
            let certificate = g.certify_outcomes(PlayConvention::Normal);
            let verified = g.verify_outcome_certificate(&certificate).unwrap();
            assert_eq!(verified, g.outcomes());
        }
    }

    #[test]
    fn misere_certificates_verify_and_swap_terminal_verdicts() {
        for g in seeded_graphs() {
            let certificate = g.certify_outcomes(PlayConvention::Misere);
            g.verify_outcome_certificate(&certificate).unwrap();
        }
        // A lone terminal node: normal play, the mover loses; misère, wins.
        let zero = graph(vec![vec![]], vec![vec![]]);
        let normal = zero
            .verify_outcome_certificate(&zero.certify_outcomes(PlayConvention::Normal))
            .unwrap();
        let misere = zero
            .verify_outcome_certificate(&zero.certify_outcomes(PlayConvention::Misere))
            .unwrap();
        assert_eq!(
            normal[0],
            LoopyPartizanOutcome::new(LoopyWinner::Right, LoopyWinner::Left)
        );
        assert_eq!(
            misere[0],
            LoopyPartizanOutcome::new(LoopyWinner::Left, LoopyWinner::Right)
        );
    }

    #[test]
    fn forged_certificates_are_rejected() {
        for g in seeded_graphs() {
            let honest = g.certify_outcomes(PlayConvention::Normal);
            for s in 0..honest.labels.len() {
                for verdict in [StateVerdict::Win, StateVerdict::Loss, StateVerdict::Draw] {
                    if verdict == honest.labels[s].verdict {
                        continue;
                    }
                    let mut forged = honest.clone();
                    forged.labels[s].verdict = verdict;
                    // A forged label either fails its check or the whole
                    // forgery is a different valid labeling, which the
                    // uniqueness of the retrograde partition forbids.
                    if let Ok(outcomes) = g.verify_outcome_certificate(&forged) {
                        assert_eq!(outcomes, g.outcomes());
                        panic!("a changed verdict at state {s} verified");
                    }
                }
            }
        }
    }

    #[test]
    fn rank_and_move_forgeries_are_rejected() {
        let on = graph(vec![vec![0]], vec![vec![]]);
        let honest = on.certify_outcomes(PlayConvention::Normal);
        on.verify_outcome_certificate(&honest).unwrap();
        let mut forged = honest.clone();
        forged.labels[1].rank = 5;
        assert!(on.verify_outcome_certificate(&forged).is_err());
        let mut short = honest.clone();
        short.labels.pop();
        assert!(matches!(
            on.verify_outcome_certificate(&short),
            Err(CertificateError::LabelCount { .. })
        ));
    }
}
