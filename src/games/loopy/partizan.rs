//! The two-sided partizan loopy graph engine: [`LoopyPartizanGraph`], graph
//! algebra, stopper detection, and the exact-outcome solver.

use std::collections::{HashMap, VecDeque};
use std::fmt;

use crate::games::Game;

use super::catalogue::{LoopyPartizanOutcome, LoopyWinner, PartizanOutcome};

/// The side whose move is next in a turn-expanded loopy graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LoopyMover {
    Left,
    Right,
}

impl LoopyMover {
    fn other(self) -> Self {
        match self {
            Self::Left => Self::Right,
            Self::Right => Self::Left,
        }
    }
}

/// One vertex of the turn-expanded graph used by stopper detection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LoopyTurnState {
    pub node: usize,
    pub mover: LoopyMover,
}

/// A reachable alternating cycle proving that a presented graph is not a stopper.
///
/// `cycle` is closed: its first state is repeated as its last state. Consecutive
/// states follow a legal move and alternate the mover.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopyStopperWitness {
    pub cycle: Vec<LoopyTurnState>,
}

/// The result of testing a presented loopy graph for the stopper property.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoopyStopperStatus {
    Stopper,
    NonStopper { witness: LoopyStopperWitness },
}

/// A structural or resource error while constructing or combining partizan
/// loopy graphs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoopyPartizanGraphError {
    MismatchedNodeCounts {
        left: usize,
        right: usize,
    },
    InvalidEdge {
        mover: LoopyMover,
        source: usize,
        target: usize,
        node_count: usize,
    },
    InvalidRoot {
        root: usize,
        node_count: usize,
    },
    /// A reachable product graph would contain more than the allowed number of
    /// nodes. This is an operational resource signal, not a game-theory result.
    NodeBudgetExceeded {
        budget: u128,
    },
}

impl fmt::Display for LoopyPartizanGraphError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MismatchedNodeCounts { left, right } => write!(
                f,
                "left/right move tables must have the same number of positions: left has {left}, right has {right}"
            ),
            Self::InvalidEdge {
                mover,
                source,
                target,
                node_count,
            } => write!(
                f,
                "{mover:?} adjacency list out of range: node {source} contains target {target}, but the graph has {node_count} nodes"
            ),
            Self::InvalidRoot { root, node_count } => write!(
                f,
                "graph root {root} is out of range for a graph with {node_count} nodes"
            ),
            Self::NodeBudgetExceeded { budget } => write!(
                f,
                "reachable graph exceeds its {budget}-node budget"
            ),
        }
    }
}

impl std::error::Error for LoopyPartizanGraphError {}

/// A finite loopy partizan game graph. `left[v]` are Left's legal moves from
/// position `v`; `right[v]` are Right's legal moves. Cycles are allowed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopyPartizanGraph {
    left: Vec<Vec<usize>>,
    right: Vec<Vec<usize>>,
}

impl LoopyPartizanGraph {
    /// Build from explicit Left and Right adjacency lists.
    ///
    /// Both tables must have the same length and every edge target must name a
    /// node in that shared range.
    pub fn new(
        left: Vec<Vec<usize>>,
        right: Vec<Vec<usize>>,
    ) -> Result<LoopyPartizanGraph, LoopyPartizanGraphError> {
        if left.len() != right.len() {
            return Err(LoopyPartizanGraphError::MismatchedNodeCounts {
                left: left.len(),
                right: right.len(),
            });
        }
        let node_count = left.len();
        validate_edges(&left, LoopyMover::Left, node_count)?;
        validate_edges(&right, LoopyMover::Right, node_count)?;
        Ok(LoopyPartizanGraph { left, right })
    }

    /// Build from move rules on positions `0..n`.
    pub fn from_rules<L, R>(
        n: usize,
        left_moves: L,
        right_moves: R,
    ) -> Result<LoopyPartizanGraph, LoopyPartizanGraphError>
    where
        L: Fn(usize) -> Vec<usize>,
        R: Fn(usize) -> Vec<usize>,
    {
        Self::new(
            (0..n).map(left_moves).collect(),
            (0..n).map(right_moves).collect(),
        )
    }

    /// Embed a finite short [`Game`] as an acyclic graph whose root is node `0`.
    ///
    /// The embedding preserves every option occurrence. Shared `Arc` subtrees may
    /// therefore appear more than once in the graph, which does not change play.
    /// The root is the first budgeted node, and each option occurrence is counted
    /// when it is discovered. Exactly `node_budget` nodes are allowed; failure
    /// exposes no partial graph.
    pub fn from_game(
        game: &Game,
        node_budget: u128,
    ) -> Result<LoopyPartizanGraph, LoopyPartizanGraphError> {
        if node_budget == 0 {
            return Err(LoopyPartizanGraphError::NodeBudgetExceeded {
                budget: node_budget,
            });
        }
        let mut left = vec![Vec::new()];
        let mut right = vec![Vec::new()];
        let mut queue = VecDeque::from([(0, game.clone())]);

        while let Some((node, position)) = queue.pop_front() {
            for option in position.left() {
                if left.len() as u128 >= node_budget {
                    return Err(LoopyPartizanGraphError::NodeBudgetExceeded {
                        budget: node_budget,
                    });
                }
                let target = left.len();
                left.push(Vec::new());
                right.push(Vec::new());
                left[node].push(target);
                queue.push_back((target, option.clone()));
            }
            for option in position.right() {
                if left.len() as u128 >= node_budget {
                    return Err(LoopyPartizanGraphError::NodeBudgetExceeded {
                        budget: node_budget,
                    });
                }
                let target = left.len();
                left.push(Vec::new());
                right.push(Vec::new());
                right[node].push(target);
                queue.push_back((target, option.clone()));
            }
        }

        Ok(LoopyPartizanGraph { left, right })
    }

    /// Number of graph nodes.
    pub fn node_count(&self) -> usize {
        self.left.len()
    }

    /// Left's adjacency lists.
    pub fn left(&self) -> &[Vec<usize>] {
        &self.left
    }

    /// Right's adjacency lists.
    pub fn right(&self) -> &[Vec<usize>] {
        &self.right
    }

    /// Negation `-G`: retain the node set and swap Left's and Right's moves.
    pub fn neg(&self) -> LoopyPartizanGraph {
        LoopyPartizanGraph {
            left: self.right.clone(),
            right: self.left.clone(),
        }
    }

    /// Build the reachable disjunctive product rooted at `(self_root, other_root)`.
    ///
    /// The returned root is node `0`. A move changes exactly one component along
    /// an edge belonging to the mover. The root counts as the first budgeted node;
    /// every other distinct reachable pair is counted when first discovered.
    /// Exactly `node_budget` nodes are allowed, and the first further discovery
    /// returns [`NodeBudgetExceeded`](LoopyPartizanGraphError::NodeBudgetExceeded)
    /// without exposing a partial graph.
    pub fn sum(
        &self,
        self_root: usize,
        other: &LoopyPartizanGraph,
        other_root: usize,
        node_budget: u128,
    ) -> Result<LoopyPartizanGraph, LoopyPartizanGraphError> {
        self.validate_root(self_root)?;
        other.validate_root(other_root)?;

        let mut pairs = Vec::new();
        let mut indices = HashMap::new();
        let mut left = Vec::new();
        let mut right = Vec::new();
        discover_product_node(
            (self_root, other_root),
            node_budget,
            &mut pairs,
            &mut indices,
            &mut left,
            &mut right,
        )?;

        let mut cursor = 0;
        while cursor < pairs.len() {
            let (first, second) = pairs[cursor];

            for &target in &self.left[first] {
                let product_target = discover_product_node(
                    (target, second),
                    node_budget,
                    &mut pairs,
                    &mut indices,
                    &mut left,
                    &mut right,
                )?;
                left[cursor].push(product_target);
            }
            for &target in &other.left[second] {
                let product_target = discover_product_node(
                    (first, target),
                    node_budget,
                    &mut pairs,
                    &mut indices,
                    &mut left,
                    &mut right,
                )?;
                left[cursor].push(product_target);
            }
            for &target in &self.right[first] {
                let product_target = discover_product_node(
                    (target, second),
                    node_budget,
                    &mut pairs,
                    &mut indices,
                    &mut left,
                    &mut right,
                )?;
                right[cursor].push(product_target);
            }
            for &target in &other.right[second] {
                let product_target = discover_product_node(
                    (first, target),
                    node_budget,
                    &mut pairs,
                    &mut indices,
                    &mut left,
                    &mut right,
                )?;
                right[cursor].push(product_target);
            }
            cursor += 1;
        }

        Ok(LoopyPartizanGraph { left, right })
    }

    /// Exact two-sided loopy-partizan outcome of every position.
    pub fn outcomes(&self) -> Vec<LoopyPartizanOutcome> {
        solve_partizan_outcomes(&self.left, &self.right)
    }

    /// The exact result from `root`, first with Left starting and then with Right.
    ///
    /// A player wins when they can force a finite win. If the starter cannot
    /// force a win but can prevent a loss, optimal play is a draw; infinite play
    /// is a draw, so each player chooses win over draw over loss. This is the
    /// nine-cell readout used by grundy's outcome doubles.
    ///
    /// The survival interpretation that the stopper-order projection uses is
    /// pinned to Aaron N. Siegel, *Combinatorial Game Theory*, GSM 146,
    /// Def. VI.1.8, p. 284 (survival), and Thm. VI.2.1, p. 290 (stopper order).
    pub fn outcome_pair(
        &self,
        root: usize,
    ) -> Result<LoopyPartizanOutcome, LoopyPartizanGraphError> {
        self.validate_root(root)?;
        Ok(self.outcomes()[root])
    }

    /// Test the presented graph rooted at `root` for the stopper property.
    ///
    /// Both possible initial movers are considered. A graph is a stopper exactly
    /// when neither root state can reach a directed cycle in the turn-expanded
    /// graph `(node, mover)`. A non-stopper includes a closed alternating cycle
    /// witness.
    pub fn stopper_status(
        &self,
        root: usize,
    ) -> Result<LoopyStopperStatus, LoopyPartizanGraphError> {
        self.validate_root(root)?;
        if let Some(witness) = self.alternating_cycle(root) {
            Ok(LoopyStopperStatus::NonStopper { witness })
        } else {
            Ok(LoopyStopperStatus::Stopper)
        }
    }

    /// Whether the presented graph rooted at `root` is a stopper.
    pub fn is_stopper(&self, root: usize) -> Result<bool, LoopyPartizanGraphError> {
        Ok(matches!(
            self.stopper_status(root)?,
            LoopyStopperStatus::Stopper
        ))
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

    fn validate_root(&self, root: usize) -> Result<(), LoopyPartizanGraphError> {
        if root < self.node_count() {
            Ok(())
        } else {
            Err(LoopyPartizanGraphError::InvalidRoot {
                root,
                node_count: self.node_count(),
            })
        }
    }

    fn alternating_cycle(&self, root: usize) -> Option<LoopyStopperWitness> {
        let state_count = 2 * self.node_count();
        let mut colors = vec![0_u8; state_count];
        let mut parent = vec![None; state_count];

        for mover in [LoopyMover::Left, LoopyMover::Right] {
            let start = state(root, mover);
            if colors[start] != 0 {
                continue;
            }
            colors[start] = 1;
            let mut stack = vec![(start, 0_usize)];

            while let Some((current, next_edge)) = stack.last_mut() {
                let (node, turn) = state_parts(*current);
                let moves = match turn {
                    LoopyMover::Left => &self.left[node],
                    LoopyMover::Right => &self.right[node],
                };
                if *next_edge == moves.len() {
                    colors[*current] = 2;
                    stack.pop();
                    continue;
                }

                let target_node = moves[*next_edge];
                *next_edge += 1;
                let target = state(target_node, turn.other());
                match colors[target] {
                    0 => {
                        colors[target] = 1;
                        parent[target] = Some(*current);
                        stack.push((target, 0));
                    }
                    1 => {
                        let mut cycle = vec![*current];
                        while *cycle.last().unwrap() != target {
                            cycle
                                .push(parent[*cycle.last().unwrap()].expect(
                                    "a gray DFS ancestor on the active stack has a parent",
                                ));
                        }
                        cycle.reverse();
                        cycle.push(target);
                        return Some(LoopyStopperWitness {
                            cycle: cycle
                                .into_iter()
                                .map(|expanded| {
                                    let (node, mover) = state_parts(expanded);
                                    LoopyTurnState { node, mover }
                                })
                                .collect(),
                        });
                    }
                    _ => {}
                }
            }
        }
        None
    }
}

fn validate_edges(
    adjacency: &[Vec<usize>],
    mover: LoopyMover,
    node_count: usize,
) -> Result<(), LoopyPartizanGraphError> {
    for (source, targets) in adjacency.iter().enumerate() {
        for &target in targets {
            if target >= node_count {
                return Err(LoopyPartizanGraphError::InvalidEdge {
                    mover,
                    source,
                    target,
                    node_count,
                });
            }
        }
    }
    Ok(())
}

fn discover_product_node(
    pair: (usize, usize),
    node_budget: u128,
    pairs: &mut Vec<(usize, usize)>,
    indices: &mut HashMap<(usize, usize), usize>,
    left: &mut Vec<Vec<usize>>,
    right: &mut Vec<Vec<usize>>,
) -> Result<usize, LoopyPartizanGraphError> {
    if let Some(&index) = indices.get(&pair) {
        return Ok(index);
    }
    if (pairs.len() as u128) >= node_budget {
        return Err(LoopyPartizanGraphError::NodeBudgetExceeded {
            budget: node_budget,
        });
    }
    let index = pairs.len();
    pairs.push(pair);
    indices.insert(pair, index);
    left.push(Vec::new());
    right.push(Vec::new());
    Ok(index)
}

fn state(v: usize, turn: LoopyMover) -> usize {
    2 * v
        + match turn {
            LoopyMover::Left => 0,
            LoopyMover::Right => 1,
        }
}

fn state_parts(s: usize) -> (usize, LoopyMover) {
    (
        s / 2,
        if s & 1 == 0 {
            LoopyMover::Left
        } else {
            LoopyMover::Right
        },
    )
}

fn owner_winner(turn: LoopyMover) -> LoopyWinner {
    match turn {
        LoopyMover::Left => LoopyWinner::Left,
        LoopyMover::Right => LoopyWinner::Right,
    }
}

fn opponent_winner(turn: LoopyMover) -> LoopyWinner {
    match turn {
        LoopyMover::Left => LoopyWinner::Right,
        LoopyMover::Right => LoopyWinner::Left,
    }
}

fn solve_partizan_outcomes(left: &[Vec<usize>], right: &[Vec<usize>]) -> Vec<LoopyPartizanOutcome> {
    let n = left.len();
    let states = 2 * n;
    let mut succ = vec![Vec::new(); states];
    let mut pred = vec![Vec::new(); states];
    for v in 0..n {
        for &w in &left[v] {
            let s = state(v, LoopyMover::Left);
            let t = state(w, LoopyMover::Right);
            succ[s].push(t);
            pred[t].push(s);
        }
        for &w in &right[v] {
            let s = state(v, LoopyMover::Right);
            let t = state(w, LoopyMover::Left);
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
                label[state(v, LoopyMover::Left)].unwrap_or(LoopyWinner::Draw),
                label[state(v, LoopyMover::Right)].unwrap_or(LoopyWinner::Draw),
            )
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::games::LoopyValue;

    fn graph(left: Vec<Vec<usize>>, right: Vec<Vec<usize>>) -> LoopyPartizanGraph {
        LoopyPartizanGraph::new(left, right).unwrap()
    }

    fn on() -> LoopyPartizanGraph {
        graph(vec![vec![0]], vec![vec![]])
    }

    fn off() -> LoopyPartizanGraph {
        graph(vec![vec![]], vec![vec![0]])
    }

    fn over() -> LoopyPartizanGraph {
        graph(vec![vec![1], vec![]], vec![vec![0], vec![]])
    }

    fn under() -> LoopyPartizanGraph {
        graph(vec![vec![0], vec![]], vec![vec![1], vec![]])
    }

    fn dud() -> LoopyPartizanGraph {
        graph(vec![vec![0]], vec![vec![0]])
    }

    fn ones() -> LoopyPartizanGraph {
        // root 0 = {1 | root}; node 1 = {0 |}; node 2 = 0.
        graph(
            vec![vec![1], vec![2], vec![]],
            vec![vec![0], vec![], vec![]],
        )
    }

    #[test]
    fn constructor_rejects_malformed_adjacency() {
        assert_eq!(
            LoopyPartizanGraph::new(vec![vec![]], vec![]),
            Err(LoopyPartizanGraphError::MismatchedNodeCounts { left: 1, right: 0 })
        );
        assert_eq!(
            LoopyPartizanGraph::new(vec![vec![1]], vec![vec![]]),
            Err(LoopyPartizanGraphError::InvalidEdge {
                mover: LoopyMover::Left,
                source: 0,
                target: 1,
                node_count: 1,
            })
        );
        assert_eq!(
            LoopyPartizanGraph::new(vec![vec![]], vec![vec![2]]),
            Err(LoopyPartizanGraphError::InvalidEdge {
                mover: LoopyMover::Right,
                source: 0,
                target: 2,
                node_count: 1,
            })
        );
    }

    #[test]
    fn catalogue_graphs_have_the_pinned_outcome_pairs() {
        for (presented, expected) in [
            (on(), LoopyValue::On.outcome()),
            (off(), LoopyValue::Off.outcome()),
            (over(), LoopyValue::Over.outcome()),
            (under(), LoopyValue::Under.outcome()),
            (dud(), LoopyValue::Dud.outcome()),
            (ones(), LoopyValue::On.outcome()),
        ] {
            assert_eq!(presented.outcome_pair(0).unwrap(), expected);
        }
    }

    #[test]
    fn graph_negation_swaps_over_and_under() {
        assert_eq!(over().neg(), under());
        assert_eq!(over().neg().neg(), over());
    }

    #[test]
    fn reachable_product_sums_are_outcome_commutative() {
        let catalogue = [on(), off(), over(), under(), dud(), ones()];
        for first in &catalogue {
            for second in &catalogue {
                let forward = first.sum(0, second, 0, 64).unwrap();
                let reverse = second.sum(0, first, 0, 64).unwrap();
                assert_eq!(
                    forward.outcome_pair(0).unwrap(),
                    reverse.outcome_pair(0).unwrap()
                );
            }
        }

        assert_eq!(
            on().sum(0, &off(), 0, 4).unwrap().outcome_pair(0),
            Ok(LoopyValue::Dud.outcome())
        );
        assert_eq!(
            over().sum(0, &under(), 0, 16).unwrap().outcome_pair(0),
            Ok(LoopyValue::Dud.outcome())
        );
    }

    #[test]
    fn product_budget_counts_distinct_pairs_at_discovery() {
        let zero = LoopyPartizanGraph::from_game(&Game::zero(), 1).expect("one-node zero");
        assert_eq!(
            over().sum(0, &zero, 0, 0),
            Err(LoopyPartizanGraphError::NodeBudgetExceeded { budget: 0 })
        );
        assert_eq!(
            over().sum(0, &zero, 0, 1),
            Err(LoopyPartizanGraphError::NodeBudgetExceeded { budget: 1 })
        );
        assert_eq!(over().sum(0, &zero, 0, 2).unwrap().node_count(), 2);
    }

    #[test]
    fn finite_embedding_supports_mixed_sums() {
        let finite_star =
            LoopyPartizanGraph::from_game(&Game::star(), 3).expect("three-node star unfolding");
        assert_eq!(
            finite_star.outcome_pair(0).unwrap(),
            LoopyValue::Star.outcome()
        );
        let mixed = over().sum(0, &finite_star, 0, 16).unwrap();
        assert_eq!(mixed.outcome_pair(0).unwrap(), LoopyValue::Over.outcome());
    }

    #[test]
    fn finite_embedding_stops_during_shared_dag_unfolding() {
        let mut dag = Game::star();
        for _ in 0..26 {
            dag = Game::new(vec![dag.clone()], vec![dag.clone()]);
        }
        assert_eq!(
            LoopyPartizanGraph::from_game(&dag, 8),
            Err(LoopyPartizanGraphError::NodeBudgetExceeded { budget: 8 })
        );
    }

    #[test]
    fn stopper_detection_uses_alternating_turn_states() {
        assert!(over().is_stopper(0).unwrap());
        assert!(under().is_stopper(0).unwrap());
        assert!(ones().is_stopper(0).unwrap());
        assert!(!dud().is_stopper(0).unwrap());

        let sum = over().sum(0, &under(), 0, 16).unwrap();
        assert!(!sum.is_stopper(0).unwrap());
        let LoopyStopperStatus::NonStopper { witness } = sum.stopper_status(0).unwrap() else {
            panic!("over + under must carry a non-stopper witness");
        };
        assert_eq!(witness.cycle.first(), witness.cycle.last());
        assert!(witness.cycle.len() >= 3);
        for edge in witness.cycle.windows(2) {
            let (source, target) = (edge[0], edge[1]);
            assert_eq!(target.mover, source.mover.other());
            let moves = match source.mover {
                LoopyMover::Left => &sum.left[source.node],
                LoopyMover::Right => &sum.right[source.node],
            };
            assert!(moves.contains(&target.node));
        }
    }

    // This test-side oracle deliberately does not call the production retrograde
    // solver. It enumerates both players' memoryless strategies, plays each pair
    // to a terminal state or repeated turn-state, and applies the force-win
    // quantifiers directly (the Rust port of the loopy_audit2.py lineage).
    #[test]
    fn retrograde_matches_independent_strategy_oracle_on_seeded_small_graphs() {
        const GRAPH_COUNT: usize = 256;
        const MAX_NODES: usize = 4;
        const MAX_OUT_DEGREE: usize = 2;
        const SEED: u64 = 0x4f47_4841_4d03_500d;

        let mut rng = Lcg(SEED);
        for case in 0..GRAPH_COUNT {
            let node_count = 1 + rng.below(MAX_NODES);
            let left = random_adjacency(node_count, MAX_OUT_DEGREE, &mut rng);
            let right = random_adjacency(node_count, MAX_OUT_DEGREE, &mut rng);
            let presented = graph(left, right);
            let actual = presented.outcomes();
            for (root, outcome) in actual.into_iter().enumerate() {
                assert_eq!(
                    outcome,
                    brute_force_outcome(&presented, root),
                    "oracle mismatch in seeded graph {case}, root {root}: {presented:?}"
                );
            }
        }
    }

    type Strategy = Vec<Option<usize>>;

    fn brute_force_outcome(graph: &LoopyPartizanGraph, root: usize) -> LoopyPartizanOutcome {
        let left_strategies = enumerate_strategies(graph.left());
        let right_strategies = enumerate_strategies(graph.right());
        LoopyPartizanOutcome::new(
            brute_force_starter(
                graph,
                root,
                LoopyMover::Left,
                &left_strategies,
                &right_strategies,
            ),
            brute_force_starter(
                graph,
                root,
                LoopyMover::Right,
                &left_strategies,
                &right_strategies,
            ),
        )
    }

    fn brute_force_starter(
        graph: &LoopyPartizanGraph,
        root: usize,
        starter: LoopyMover,
        left_strategies: &[Strategy],
        right_strategies: &[Strategy],
    ) -> LoopyWinner {
        let left_forces = left_strategies.iter().any(|left| {
            right_strategies.iter().all(|right| {
                play_strategies(graph, root, starter, left, right) == LoopyWinner::Left
            })
        });
        let right_forces = right_strategies.iter().any(|right| {
            left_strategies.iter().all(|left| {
                play_strategies(graph, root, starter, left, right) == LoopyWinner::Right
            })
        });
        assert!(!(left_forces && right_forces));
        match (left_forces, right_forces) {
            (true, false) => LoopyWinner::Left,
            (false, true) => LoopyWinner::Right,
            (false, false) => LoopyWinner::Draw,
            (true, true) => unreachable!(),
        }
    }

    fn enumerate_strategies(adjacency: &[Vec<usize>]) -> Vec<Strategy> {
        let mut strategies = vec![vec![None; adjacency.len()]];
        for (node, moves) in adjacency.iter().enumerate() {
            if moves.is_empty() {
                continue;
            }
            let mut expanded = Vec::with_capacity(strategies.len() * moves.len());
            for strategy in strategies {
                for &target in moves {
                    let mut choice = strategy.clone();
                    choice[node] = Some(target);
                    expanded.push(choice);
                }
            }
            strategies = expanded;
        }
        strategies
    }

    fn play_strategies(
        graph: &LoopyPartizanGraph,
        root: usize,
        starter: LoopyMover,
        left_strategy: &Strategy,
        right_strategy: &Strategy,
    ) -> LoopyWinner {
        let mut seen = vec![false; 2 * graph.node_count()];
        let mut node = root;
        let mut mover = starter;
        loop {
            let expanded = state(node, mover);
            if seen[expanded] {
                return LoopyWinner::Draw;
            }
            seen[expanded] = true;

            let (moves, strategy) = match mover {
                LoopyMover::Left => (&graph.left[node], left_strategy),
                LoopyMover::Right => (&graph.right[node], right_strategy),
            };
            if moves.is_empty() {
                return opponent_winner(mover);
            }
            node = strategy[node].expect("every non-terminal strategy chooses a move");
            mover = mover.other();
        }
    }

    struct Lcg(u64);

    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            self.0
        }

        fn below(&mut self, limit: usize) -> usize {
            (self.next() % limit as u64) as usize
        }
    }

    fn random_adjacency(
        node_count: usize,
        max_out_degree: usize,
        rng: &mut Lcg,
    ) -> Vec<Vec<usize>> {
        let max_degree = max_out_degree.min(node_count);
        (0..node_count)
            .map(|_| {
                let degree = rng.below(max_degree + 1);
                let mut targets: Vec<usize> = (0..node_count).collect();
                for i in (1..targets.len()).rev() {
                    let j = rng.below(i + 1);
                    targets.swap(i, j);
                }
                targets.truncate(degree);
                targets
            })
            .collect()
    }
}
