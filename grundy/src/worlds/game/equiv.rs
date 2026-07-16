//! Multiform equality, matching, and regular-game fingerprints.

use super::*;

pub(crate) fn game_structural_eq_multiset(lhs: &Game, rhs: &Game) -> bool {
    game_structural_eq_multiset_inner(lhs, rhs, &mut HashMap::new())
}

pub(crate) fn game_structural_eq_multiset_inner(
    lhs: &Game,
    rhs: &Game,
    memo: &mut HashMap<(usize, usize), bool>,
) -> bool {
    if lhs.ptr_eq(rhs) {
        return true;
    }
    let key = (lhs.ptr_id(), rhs.ptr_id());
    if let Some(&equal) = memo.get(&key) {
        return equal;
    }
    let equal = lhs.left().len() == rhs.left().len()
        && lhs.right().len() == rhs.right().len()
        && perfect_matching(lhs.left().len(), |left, right| {
            game_structural_eq_multiset_inner(&lhs.left()[left], &rhs.left()[right], memo)
        })
        && perfect_matching(lhs.right().len(), |left, right| {
            game_structural_eq_multiset_inner(&lhs.right()[left], &rhs.right()[right], memo)
        });
    memo.insert(key, equal);
    memo.insert((key.1, key.0), equal);
    equal
}

pub(crate) fn perfect_matching(
    size: usize,
    mut compatible: impl FnMut(usize, usize) -> bool,
) -> bool {
    // Sides are multisets: equality is an existential bijection, not a sorted
    // presentation walk. The compatibility matrix preserves multiplicity, and
    // the augmenting-path matcher finds a bijection without canonicalizing.
    let edges = (0..size)
        .map(|left| {
            (0..size)
                .map(|right| compatible(left, right))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut matched_right = vec![None; size];
    (0..size).all(|left| augment_matching(left, &edges, &mut vec![false; size], &mut matched_right))
}

pub(crate) fn augment_matching(
    left: usize,
    edges: &[Vec<bool>],
    seen_right: &mut [bool],
    matched_right: &mut [Option<usize>],
) -> bool {
    for right in 0..edges.len() {
        if !edges[left][right] || seen_right[right] {
            continue;
        }
        seen_right[right] = true;
        if matched_right[right]
            .is_none_or(|previous| augment_matching(previous, edges, seen_right, matched_right))
        {
            matched_right[right] = Some(left);
            return true;
        }
    }
    false
}

pub(crate) fn game_element_has_draw(element: &GameElement) -> bool {
    match element {
        GameElement::Finite(_) => false,
        GameElement::Graph(reference) => reference.graph.has_draw[reference.node],
    }
}

#[derive(Clone, Default)]
pub(crate) struct RegularEqState {
    // Graph pairs are coinductive assumptions. A repeated pair closes one
    // synchronized descent path; the finite product of node sets bounds all
    // paths. Mixed graph/tree paths instead reject a repeated graph node,
    // because a genuinely cyclic unfolding cannot equal a finite tree.
    visited_pairs: HashSet<GraphPair>,
    mixed_path: HashSet<GraphKey>,
}

pub(crate) fn game_element_regular_eq(lhs: &GameElement, rhs: &GameElement) -> bool {
    regular_eq_inner(lhs, rhs, &mut RegularEqState::default())
}

pub(crate) fn regular_eq_inner(
    lhs: &GameElement,
    rhs: &GameElement,
    state: &mut RegularEqState,
) -> bool {
    match (lhs, rhs) {
        (GameElement::Finite(lhs), GameElement::Finite(rhs)) => {
            game_structural_eq_multiset(lhs, rhs)
        }
        (GameElement::Graph(lhs), GameElement::Graph(rhs)) => {
            if !state.visited_pairs.insert((graph_key(lhs), graph_key(rhs))) {
                return true;
            }
            regular_options_eq(lhs, rhs, true, state) && regular_options_eq(lhs, rhs, false, state)
        }
        (GameElement::Graph(graph), GameElement::Finite(finite))
        | (GameElement::Finite(finite), GameElement::Graph(graph)) => {
            if !state.mixed_path.insert(graph_key(graph)) {
                return false;
            }
            let graph_value = GameElement::Graph(graph.clone());
            let finite_value = GameElement::Finite(finite.clone());
            let result = [true, false].into_iter().all(|left| {
                let graph_options = game_options(&graph_value, left);
                let finite_options = game_options(&finite_value, left);
                graph_options.len() == finite_options.len()
                    && regular_element_options_eq(&graph_options, &finite_options, state)
            });
            state.mixed_path.remove(&graph_key(graph));
            result
        }
    }
}

pub(crate) fn regular_options_eq(
    lhs: &GraphRef,
    rhs: &GraphRef,
    left: bool,
    state: &RegularEqState,
) -> bool {
    let lhs = game_options(&GameElement::Graph(lhs.clone()), left);
    let rhs = game_options(&GameElement::Graph(rhs.clone()), left);
    lhs.len() == rhs.len() && regular_element_options_eq(&lhs, &rhs, state)
}

pub(crate) fn regular_element_options_eq(
    lhs: &[GameElement],
    rhs: &[GameElement],
    state: &RegularEqState,
) -> bool {
    // Every matrix edge gets branch-local assumptions. A failed candidate
    // cannot leak an optimistic cycle into another candidate's matching proof.
    perfect_matching(lhs.len(), |left, right| {
        let mut branch = state.clone();
        regular_eq_inner(&lhs[left], &rhs[right], &mut branch)
    })
}

pub(crate) fn graph_key(reference: &GraphRef) -> GraphKey {
    (Arc::as_ptr(&reference.graph) as usize, reference.node)
}

pub(crate) fn game_mu_call_key(name: &str, body: &Expr, args: &[Value<GameElement>]) -> String {
    let args = args
        .iter()
        .map(|arg| match arg {
            Value::Element(GameElement::Finite(game)) => format!("e:{}", game_form_key(game)),
            Value::Element(GameElement::Graph(reference)) => {
                let (graph, node) = graph_key(reference);
                format!("g:{graph}:{node}")
            }
            Value::Index(value) => format!("i:{value}"),
            Value::Bool(value) => format!("b:{value}"),
            Value::Function(_) => "f".to_string(),
        })
        .collect::<Vec<_>>()
        .join("|");
    format!("{name}:{}@{args}", crate::unparse::unparse_expr(body))
}

pub(crate) fn game_form_key(game: &Game) -> String {
    let recognized = display_game(game);
    if recognized.starts_with('{') {
        game.structural_string()
    } else {
        recognized
    }
}
