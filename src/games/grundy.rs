//! Sprague–Grundy theory: the normal-play impartial center.
//!
//! Every finite acyclic impartial game under normal play has a **Grundy value**,
//! the nimber given by the *mex* (minimal excludant) of its options' values:
//!
//!   g(G) = mex { g(G') : G' a move from G }.
//!
//! A position is a P-position (the player to move loses) iff `g(G) = 0`, so this
//! refines [`kernel::outcomes`](crate::games::outcomes): `outcomes` returns a
//! Win/Loss/Draw label, while the Grundy value records the full finite nimber.
//!
//! The **Sprague–Grundy theorem** is then `g(G + H) = g(G) ⊕ g(H)`: under
//! disjunctive sum every impartial game behaves as a single Nim heap of size
//! `g(G)`. This module computes Grundy values over an explicit finite game graph
//! ([`grundy_graph`]) or a move-generating closure ([`grundy`], analogous to
//! [`try_misere_is_n`](crate::games::try_misere_is_n)). Tests compare the two
//! routes and verify the disjunctive-sum XOR law for Nim.

use std::collections::{HashMap, HashSet};
use std::convert::Infallible;
use std::hash::Hash;

/// The minimal excludant of a set of nimbers: the least non-negative integer not
/// present.
///
/// # Examples
///
/// ```
/// use ogdoad::games::mex;
///
/// assert_eq!(mex([]), 0);
/// assert_eq!(mex([0, 1, 3]), 2);
/// assert_eq!(mex([1, 2, 3]), 0);
/// assert_eq!(mex([0, 0, 1, u128::MAX]), 2); // duplicates and huge values are harmless
/// ```
pub fn mex<I: IntoIterator<Item = u128>>(values: I) -> u128 {
    let values: Vec<u128> = values.into_iter().collect();
    // For n supplied values, mex is at most n. Values outside that interval
    // cannot affect the result, so a dense marker avoids hashing arbitrary
    // u128s on every game-node visit.
    let mut seen = vec![false; values.len() + 1];
    for value in values {
        if let Ok(index) = usize::try_from(value) {
            if index < seen.len() {
                seen[index] = true;
            }
        }
    }
    seen.iter()
        .position(|present| !present)
        .expect("n values cannot cover n+1 candidate mex values") as u128
}

fn grundy_dfs(succ: &[Vec<usize>], v: usize, state: &mut [u8], g: &mut [u128]) -> Option<()> {
    match state[v] {
        2 => return Some(()),
        1 => return None, // back-edge ⇒ a cycle ⇒ Grundy value undefined
        _ => {}
    }
    state[v] = 1;
    for &w in &succ[v] {
        grundy_dfs(succ, w, state, g)?;
    }
    g[v] = mex(succ[v].iter().map(|&w| g[w]));
    state[v] = 2;
    Some(())
}

/// Grundy values of a finite **acyclic** impartial game graph, given as
/// adjacency lists (`succ[v]` = the positions reachable from `v` in one move).
/// Returns `None` if the graph has a cycle — Grundy values are only defined on
/// terminating (loopy-free) games; use [`outcomes`](crate::games::outcomes) for
/// the Win/Loss/Draw analysis of loopy games.
///
/// Position `v` is a P-position (Loss) iff `result[v] == 0`.
///
/// # Examples
///
/// ```
/// use ogdoad::games::grundy_graph;
///
/// // 0 -> {1, 2}, 1 -> {2}, 2 terminal: g(2) = 0, g(1) = mex{0} = 1, g(0) = mex{1, 0} = 2.
/// let succ = vec![vec![1, 2], vec![2], vec![]];
/// assert_eq!(grundy_graph(&succ), Some(vec![2, 1, 0]));
/// // A cycle has no Grundy value: the checked API returns None.
/// assert_eq!(grundy_graph(&[vec![1], vec![0]]), None);
/// ```
pub fn grundy_graph(succ: &[Vec<usize>]) -> Option<Vec<u128>> {
    let n = succ.len();
    let mut state = vec![0u8; n];
    let mut g = vec![0u128; n];
    for v in 0..n {
        grundy_dfs(succ, v, &mut state, &mut g)?;
    }
    Some(g)
}

/// The Grundy value of a position given a move generator, memoised, or `None`
/// if the move graph reachable from `pos` has a directed cycle (Grundy values are
/// then undefined), exactly as for [`grundy_graph`] and
/// [`try_misere_is_n`](crate::games::try_misere_is_n). `moves(pos)` returns the
/// positions reachable in one move. This is the way to compute Grundy values of
/// games defined by a rule (Nim, octal games, …) without materialising the whole
/// graph.
///
/// Evaluation is iterative, so long chains of positions need no native stack.
/// Memo entries are recorded only for completed positions, so a refused call
/// leaves the memo valid.
///
/// # Examples
///
/// Positions can be any hashable type with a move generator. In the subtraction
/// game with moves `{1, 2}` a heap `n` moves to `n - 1` or `n - 2`, and the
/// Grundy value is `n mod 3`:
///
/// ```
/// use ogdoad::games::grundy;
/// use std::collections::HashMap;
///
/// let moves = |n: &u32| (1..=2).filter(|&k| k <= *n).map(|k| n - k).collect::<Vec<u32>>();
/// let mut memo = HashMap::new();
/// for n in 0..12 {
///     assert_eq!(grundy(&n, &moves, &mut memo), Some(u128::from(n % 3)));
/// }
/// // A cyclic rule has no Grundy value.
/// assert_eq!(grundy(&0u8, &|n: &u8| vec![(n + 1) % 3], &mut HashMap::new()), None);
/// ```
pub fn grundy<P, F>(pos: &P, moves: &F, memo: &mut HashMap<P, u128>) -> Option<u128>
where
    P: Eq + Hash + Clone,
    F: Fn(&P) -> Vec<P>,
{
    match grundy_with(pos, |p| Ok::<_, Infallible>(moves(p)), memo) {
        Ok(value) => value,
        Err(never) => match never {},
    }
}

/// [`grundy`] with a fallible move generator, whose first error is returned.
/// The depth-first search keeps its own stack of positions with their pending
/// options.
pub(crate) fn grundy_with<P, E>(
    pos: &P,
    mut moves: impl FnMut(&P) -> Result<Vec<P>, E>,
    memo: &mut HashMap<P, u128>,
) -> Result<Option<u128>, E>
where
    P: Eq + Hash + Clone,
{
    if let Some(&value) = memo.get(pos) {
        return Ok(Some(value));
    }
    let mut visiting = HashSet::from([pos.clone()]);
    let mut stack = vec![(pos.clone(), moves(pos)?, 0usize)];
    while let Some((_, options, next)) = stack.last_mut() {
        if let Some(option) = options.get(*next).cloned() {
            *next += 1;
            if memo.contains_key(&option) {
                continue;
            }
            if !visiting.insert(option.clone()) {
                return Ok(None);
            }
            let option_moves = moves(&option)?;
            stack.push((option, option_moves, 0));
        } else {
            let (position, options, _) = stack.pop().expect("the stack is nonempty");
            let value = mex(options.iter().map(|option| memo[option]));
            visiting.remove(&position);
            memo.insert(position, value);
        }
    }
    Ok(memo.get(pos).copied())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::games::{outcomes, Outcome};

    #[test]
    fn mex_basics() {
        assert_eq!(mex([]), 0);
        assert_eq!(mex([0, 1, 2]), 3);
        assert_eq!(mex([1, 2, 3]), 0);
        assert_eq!(mex([0, 2, 3]), 1);
        assert_eq!(mex([0, 0, 1, 1]), 2); // duplicates ignored
        assert_eq!(mex([0, 1, u128::MAX]), 2); // out-of-range values are irrelevant
    }

    #[test]
    fn single_nim_heap_grundy_is_its_size() {
        // The heap of size h is the path h → {h-1, …, 0}; g(h) = mex{0..h} = h.
        let n = 8;
        let succ: Vec<Vec<usize>> = (0..=n).map(|h| (0..h).collect()).collect();
        let g = grundy_graph(&succ).unwrap();
        assert_eq!(g, (0..=n as u128).collect::<Vec<_>>());
    }

    #[test]
    fn grundy_zero_iff_loss() {
        // Cross-check against kernel::outcomes on an acyclic graph: Grundy 0 ⟺ Loss.
        let succ = vec![vec![1, 2], vec![3], vec![3], vec![]];
        let g = grundy_graph(&succ).unwrap();
        let o = outcomes(&succ);
        for v in 0..succ.len() {
            assert_eq!(g[v] == 0, o[v] == Outcome::Loss);
        }
    }

    #[test]
    fn cyclic_graph_has_no_grundy_value() {
        assert_eq!(grundy_graph(&[vec![1], vec![0]]), None);
    }

    #[test]
    fn sprague_grundy_theorem_is_boutons_xor() {
        // Nim: a position is a multiset of heap sizes; a move shrinks one heap.
        // The Sprague–Grundy theorem says g(position) = XOR of the heap sizes.
        // `&Vec` matches the `Fn(&P)` move-generator bound (`P = Vec<u128>`).
        #[allow(clippy::ptr_arg)]
        fn nim_moves(heaps: &Vec<u128>) -> Vec<Vec<u128>> {
            let mut out = Vec::new();
            for (i, &h) in heaps.iter().enumerate() {
                for new in 0..h {
                    let mut next = heaps.clone();
                    next[i] = new;
                    next.retain(|&x| x != 0);
                    next.sort_unstable();
                    out.push(next);
                }
            }
            out
        }
        let mut memo = HashMap::new();
        for a in 0..=4u128 {
            for b in 0..=4u128 {
                for c in 0..=4u128 {
                    let mut heaps: Vec<u128> = vec![a, b, c];
                    heaps.retain(|&x| x != 0);
                    heaps.sort_unstable();
                    let g = grundy(&heaps, &nim_moves, &mut memo);
                    assert_eq!(g, Some(a ^ b ^ c), "heaps {a},{b},{c}");
                }
            }
        }
    }

    #[test]
    fn grundy_is_iterative_and_refuses_cycles() {
        // A chain of a million positions needs no native stack.
        let chain = |n: &u32| if *n == 0 { vec![] } else { vec![n - 1] };
        let mut memo = HashMap::new();
        assert_eq!(grundy(&1_000_000u32, &chain, &mut memo), Some(0));
        assert_eq!(grundy(&999_999u32, &chain, &mut memo), Some(1));
        // A cycle below an acyclic prefix is refused, and the memo keeps only
        // completed positions.
        let cyclic = |n: &u32| match n {
            0 => vec![1],
            1 => vec![2],
            2 => vec![1],
            _ => vec![n - 1],
        };
        let mut memo = HashMap::new();
        assert_eq!(grundy(&5u32, &cyclic, &mut memo), None);
        assert!(memo.is_empty());
        assert_eq!(grundy(&7u32, &|_: &u32| vec![7], &mut HashMap::new()), None);
    }

    #[test]
    fn grundy_with_returns_the_first_move_error() {
        let moves = |n: &u32| {
            if *n == 3 {
                Err("bad position")
            } else {
                Ok(vec![n + 1])
            }
        };
        assert_eq!(
            grundy_with(&0, moves, &mut HashMap::new()),
            Err("bad position")
        );
    }
}
