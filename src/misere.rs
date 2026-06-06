//! Misère play: where disjunctive sums stop being linear.
//!
//! NOTES.md's open question needs a game whose P-positions are the *quadric*
//! `{Q=0}` of a Gold form. Normal-play disjunctive sums can't supply one: their
//! outcomes are XOR-linear (P ⟺ ⊕ of Grundy values = 0), so the P-set is always
//! a *subspace*. The two escape routes are interactive games and **misère** play
//! (last player to move loses), where sums are genuinely non-linear — Grundy
//! values no longer determine the outcome of a sum.
//!
//! This module is the instrument for the misère route: a memoised misère-outcome
//! evaluator for any finite impartial game (given a `moves` function), plus the
//! canonical witness that misère is non-linear — misère Nim, whose P-set is
//! provably *not* `{⊕ = 0}` and not even a coset. That clears the bar normal play
//! fails. Whether a misère game's P-set is an actual Gold quadric is the part
//! that stays open; this gives the tooling to test candidates.

use std::collections::HashMap;
use std::hash::Hash;

/// Misère outcome of a finite impartial game: `true` = **N-position** (the player
/// to move wins under misère, last-to-move-loses), `false` = **P-position** (the
/// previous player wins). `moves(p)` lists the positions reachable in one move; a
/// position with no moves is terminal, and under misère the player who *cannot*
/// move **wins**, so a terminal position is an N-position. Memoised on positions.
pub fn misere_is_n<P, F>(pos: &P, moves: &F, memo: &mut HashMap<P, bool>) -> bool
where
    P: Clone + Eq + Hash,
    F: Fn(&P) -> Vec<P>,
{
    if let Some(&v) = memo.get(pos) {
        return v;
    }
    let nexts = moves(pos);
    // terminal ⇒ N (can't-move wins); otherwise N ⟺ some move reaches a P.
    let result = nexts.is_empty() || nexts.iter().any(|q| !misere_is_n(q, moves, memo));
    memo.insert(pos.clone(), result);
    result
}

/// Convenience: `true` iff `pos` is a misère P-position (second player wins).
pub fn misere_is_p<P, F>(pos: &P, moves: &F, memo: &mut HashMap<P, bool>) -> bool
where
    P: Clone + Eq + Hash,
    F: Fn(&P) -> Vec<P>,
{
    !misere_is_n(pos, moves, memo)
}

/// A Nim position: heap sizes, kept sorted ascending with empty heaps dropped so
/// equal positions share a memo key.
pub fn nim_canonical(mut heaps: Vec<u32>) -> Vec<u32> {
    heaps.retain(|&h| h != 0);
    heaps.sort_unstable();
    heaps
}

/// The moves of Nim: reduce any one heap to any strictly smaller size.
pub fn nim_moves(pos: &Vec<u32>) -> Vec<Vec<u32>> {
    let mut out = Vec::new();
    for i in 0..pos.len() {
        for v in 0..pos[i] {
            let mut q = pos.clone();
            q[i] = v;
            out.push(nim_canonical(q));
        }
    }
    out
}

/// The misère-Nim theorem (Bouton): a position is a misère P-position iff either
/// every heap is ≤ 1 and there is an *odd* number of heaps, or some heap is ≥ 2
/// and the nim-sum (XOR) of the heaps is 0. (The empty position is N.)
pub fn misere_nim_p_predicted(heaps: &[u32]) -> bool {
    let xor = heaps.iter().fold(0u32, |a, &h| a ^ h);
    let max = heaps.iter().copied().max().unwrap_or(0);
    if max <= 1 {
        heaps.len() % 2 == 1
    } else {
        xor == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn misere_nim_matches_boutons_theorem() {
        // Verify the tree evaluator against the closed-form theorem over all Nim
        // positions with up to 4 heaps of size ≤ 4.
        let mut memo: HashMap<Vec<u32>, bool> = HashMap::new();
        fn rec(prefix: &mut Vec<u32>, depth: usize, memo: &mut HashMap<Vec<u32>, bool>) {
            if depth == 0 {
                let pos = nim_canonical(prefix.clone());
                let is_p = misere_is_p(&pos, &nim_moves, memo);
                assert_eq!(
                    is_p,
                    misere_nim_p_predicted(&pos),
                    "misère Nim mismatch at {pos:?}"
                );
                return;
            }
            for h in 0..=4u32 {
                prefix.push(h);
                rec(prefix, depth - 1, memo);
                prefix.pop();
            }
        }
        rec(&mut Vec::new(), 4, &mut memo);
    }

    #[test]
    fn misere_is_genuinely_nonlinear() {
        // The normal-play P-set is exactly {XOR = 0} — a subspace. The misère
        // P-set is NOT: it contains a XOR≠0 point and excludes a XOR=0 point, so
        // it is neither {XOR=0} nor a coset of any subspace. This is precisely the
        // non-linearity normal-play sums lack (and that a quadratic P-set needs).
        let mut memo: HashMap<Vec<u32>, bool> = HashMap::new();
        let one = nim_canonical(vec![1]); // XOR = 1, but misère-P (you must take the last coin)
        let oneone = nim_canonical(vec![1, 1]); // XOR = 0, but misère-N
        assert!(misere_is_p(&one, &nim_moves, &mut memo));
        assert!(!misere_is_p(&oneone, &nim_moves, &mut memo));
        // 0 ∈ P-set?  empty position is terminal ⇒ N, so 0 ∉ misère-P. A subspace
        // (or its outcome set) would contain 0; a coset structure is impossible
        // because [1] (xor 1) is P while [1,1]+[1,1]-style xor-0 combos are N.
        let empty = nim_canonical(vec![]);
        assert!(!misere_is_p(&empty, &nim_moves, &mut memo));

        // Concrete subspace-failure witness: u=[1], v=[1] are both in the P-set
        // under the all-ones regime, but their nim-sum (xor) leaves the regime.
        // (Here the point is structural: outcome is not an XOR-linear function.)
        let three_ones = nim_canonical(vec![1, 1, 1]); // XOR = 1, misère-P (odd count)
        assert!(misere_is_p(&three_ones, &nim_moves, &mut memo));
    }
}
