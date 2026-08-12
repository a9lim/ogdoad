//! Quadric-fitting instruments for finite loopy decision sets.
//!
//! An arbitrary cyclic rule on `F₂^k` has both a Loss-set and a Draw-set. These
//! functions extract both sets and fit each with [`fit_f2_quadratic`]. They are
//! bounded diagnostic tools, not a universal game-realization theorem.

use crate::forms::{fit_f2_quadratic, QuadricFit};

use super::graph::LoopyGraph;

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
/// genuinely quadratic fit is reported by
/// [`QuadricFit::is_genuinely_quadratic`].
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
