use ogdoad::games::{Game, LoopyPartizanGraph};
use ogdoad::ogham::{ast::OutcomeCell, OghamSession};

const SEED: u64 = 0x0360_5eed_cafe_f00d;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProjectedRelation {
    Eq,
    Lt,
    Gt,
    Fuzzy,
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

    fn index(&mut self, upper: usize) -> usize {
        (self.next() as usize) % upper
    }

    fn bit(&mut self) -> bool {
        self.next() & 1 == 1
    }
}

#[derive(Clone)]
struct StopperCase {
    expression: String,
    graph: LoopyPartizanGraph,
}

#[test]
fn seeded_stopper_pairs_match_independent_second_player_survival_oracle() {
    let mut session = OghamSession::new("game").expect("game world");
    let mut rng = Lcg(SEED);
    let mut cases = Vec::new();

    for index in 0..16 {
        let cycle_len = 1 + rng.index(3);
        let cycle_is_left = rng.bit();
        let left_zero = (0..cycle_len).map(|_| rng.bit()).collect::<Vec<_>>();
        let right_zero = (0..cycle_len).map(|_| rng.bit()).collect::<Vec<_>>();
        let name = format!("stop{index}");
        let definition =
            stopper_definition(&name, cycle_len, cycle_is_left, &left_zero, &right_zero);
        session
            .eval_line(&definition)
            .unwrap_or_else(|err| panic!("seed {SEED:#x}, definition `{definition}`: {err}"));
        let graph = stopper_graph(cycle_len, cycle_is_left, &left_zero, &right_zero);
        assert!(
            graph.is_stopper(0).expect("generated graph root"),
            "seed {SEED:#x}, generated case {index}"
        );
        cases.push(StopperCase {
            expression: name,
            graph,
        });
    }

    for (expression, game) in [
        ("0", Game::zero()),
        ("1", Game::integer(1)),
        ("*1", Game::star()),
        ("{1 | -1}", Game::switch(1, -1)),
    ] {
        cases.push(StopperCase {
            expression: expression.to_string(),
            graph: LoopyPartizanGraph::from_game(&game, 128).expect("small finite game graph"),
        });
    }

    for pair_index in 0..64 {
        let lhs_index = rng.index(cases.len());
        let mut rhs_index = rng.index(cases.len());
        if rhs_index == lhs_index {
            rhs_index = (rhs_index + 1) % cases.len();
        }
        let lhs = &cases[lhs_index];
        let rhs = &cases[rhs_index];
        let difference = independent_difference(&lhs.graph, &rhs.graph);
        let expected = independent_projection_by_survival(&difference, 0);
        let actual = language_projected_relation(&mut session, &lhs.expression, &rhs.expression);
        assert_eq!(
            actual, expected,
            "seed {SEED:#x}, pair {pair_index}, {} versus {}",
            lhs.expression, rhs.expression
        );
    }
}

#[test]
fn seeded_fresh_pairs_obey_negation_rotation_and_operand_swap() {
    let mut session = OghamSession::new("game").expect("game world");
    let mut rng = Lcg(SEED ^ 0xa11c_e5a5_51de_0002);
    let mut names = Vec::new();

    for index in 0..20 {
        let cycle_len = 1 + rng.index(3);
        let cycle_is_left = rng.bit();
        let left_zero = (0..cycle_len).map(|_| rng.bit()).collect::<Vec<_>>();
        let right_zero = (0..cycle_len).map(|_| rng.bit()).collect::<Vec<_>>();
        let name = format!("law{index}");
        let definition =
            stopper_definition(&name, cycle_len, cycle_is_left, &left_zero, &right_zero);
        session
            .eval_line(&definition)
            .unwrap_or_else(|err| panic!("seeded definition `{definition}`: {err}"));
        let graph = stopper_graph(cycle_len, cycle_is_left, &left_zero, &right_zero);
        assert_ne!(graph, graph.neg(), "case {index} must be non-self-dual");
        names.push(name);
    }

    for pair_index in 0..48 {
        let lhs_index = rng.index(names.len());
        let mut rhs_index = rng.index(names.len());
        if rhs_index == lhs_index {
            rhs_index = (rhs_index + 1) % names.len();
        }
        let lhs = &names[lhs_index];
        let rhs = &names[rhs_index];
        let cell = language_outcome_cell(&mut session, lhs, rhs);
        assert_eq!(
            language_outcome_cell(&mut session, &format!("-({lhs})"), &format!("-({rhs})")),
            cell.rotate(),
            "negation rotation, seed {SEED:#x}, pair {pair_index}: {lhs}, {rhs}"
        );
        assert_eq!(
            language_outcome_cell(&mut session, rhs, lhs),
            cell.rotate(),
            "operand swap, seed {SEED:#x}, pair {pair_index}: {lhs}, {rhs}"
        );
    }
}

fn stopper_definition(
    name: &str,
    cycle_len: usize,
    cycle_is_left: bool,
    left_zero: &[bool],
    right_zero: &[bool],
) -> String {
    let mut next = name.to_string();
    for node in (0..cycle_len).rev() {
        let mut left = if left_zero[node] {
            vec!["0".to_string()]
        } else {
            Vec::new()
        };
        let mut right = if right_zero[node] {
            vec!["0".to_string()]
        } else {
            Vec::new()
        };
        if cycle_is_left {
            left.push(next);
        } else {
            right.push(next);
        }
        next = format!("{{{} | {}}}", left.join(", "), right.join(", "));
    }
    format!("{name} =: {next}")
}

fn stopper_graph(
    cycle_len: usize,
    cycle_is_left: bool,
    left_zero: &[bool],
    right_zero: &[bool],
) -> LoopyPartizanGraph {
    let zero = cycle_len;
    let mut left = vec![Vec::new(); cycle_len + 1];
    let mut right = vec![Vec::new(); cycle_len + 1];
    for node in 0..cycle_len {
        if left_zero[node] {
            left[node].push(zero);
        }
        if right_zero[node] {
            right[node].push(zero);
        }
        let target = (node + 1) % cycle_len;
        if cycle_is_left {
            left[node].push(target);
        } else {
            right[node].push(target);
        }
    }
    LoopyPartizanGraph::new(left, right).expect("generated adjacency tables")
}

fn independent_projection_by_survival(
    difference: &LoopyPartizanGraph,
    root: usize,
) -> ProjectedRelation {
    // This deliberately does not call the engine outcome solver or its projection
    // table. It computes each player's finite-win attractor directly on the
    // turn-expanded graph. The opponent survives moving second exactly when that
    // initial state is outside the mover's least force-win fixed point.
    let left_wins = force_win_attractor(difference, true);
    let right_wins = force_win_attractor(difference, false);
    let left_survives_moving_second = !right_wins[state(root, false)];
    let right_survives_moving_second = !left_wins[state(root, true)];
    match (left_survives_moving_second, right_survives_moving_second) {
        (true, false) => ProjectedRelation::Gt,
        (false, true) => ProjectedRelation::Lt,
        (false, false) => ProjectedRelation::Fuzzy,
        (true, true) => ProjectedRelation::Eq,
    }
}

fn independent_difference(
    lhs: &LoopyPartizanGraph,
    rhs: &LoopyPartizanGraph,
) -> LoopyPartizanGraph {
    // Independent cartesian construction of G + (-H). This intentionally avoids
    // `LoopyPartizanGraph::sum` as well as `neg`, so the oracle covers the
    // language's difference construction in addition to its projection table.
    let rhs_size = rhs.node_count();
    let node_count = lhs.node_count() * rhs_size;
    let pair = |left: usize, right: usize| left * rhs_size + right;
    let mut left_moves = vec![Vec::new(); node_count];
    let mut right_moves = vec![Vec::new(); node_count];
    for left in 0..lhs.node_count() {
        for right in 0..rhs.node_count() {
            let source = pair(left, right);
            left_moves[source].extend(lhs.left()[left].iter().map(|&target| pair(target, right)));
            left_moves[source].extend(rhs.right()[right].iter().map(|&target| pair(left, target)));
            right_moves[source].extend(lhs.right()[left].iter().map(|&target| pair(target, right)));
            right_moves[source].extend(rhs.left()[right].iter().map(|&target| pair(left, target)));
        }
    }
    LoopyPartizanGraph::new(left_moves, right_moves).expect("cartesian difference graph")
}

fn force_win_attractor(graph: &LoopyPartizanGraph, winner_is_left: bool) -> Vec<bool> {
    let mut wins = vec![false; 2 * graph.node_count()];
    loop {
        let mut changed = false;
        for node in 0..graph.node_count() {
            for left_to_move in [true, false] {
                let moves = if left_to_move {
                    &graph.left()[node]
                } else {
                    &graph.right()[node]
                };
                let winner_to_move = left_to_move == winner_is_left;
                let forced = if winner_to_move {
                    moves
                        .iter()
                        .any(|&target| wins[state(target, !left_to_move)])
                } else {
                    moves.is_empty()
                        || moves
                            .iter()
                            .all(|&target| wins[state(target, !left_to_move)])
                };
                let position = state(node, left_to_move);
                if forced && !wins[position] {
                    wins[position] = true;
                    changed = true;
                }
            }
        }
        if !changed {
            return wins;
        }
    }
}

fn state(node: usize, left_to_move: bool) -> usize {
    2 * node + usize::from(!left_to_move)
}

fn language_projected_relation(
    session: &mut OghamSession,
    lhs: &str,
    rhs: &str,
) -> ProjectedRelation {
    let true_relations = [
        ("=", ProjectedRelation::Eq),
        ("<", ProjectedRelation::Lt),
        (">", ProjectedRelation::Gt),
        ("∥", ProjectedRelation::Fuzzy),
    ]
    .into_iter()
    .filter_map(|(glyph, relation)| {
        eval_bool(session, &format!("({lhs}) {glyph} ({rhs})")).then_some(relation)
    })
    .collect::<Vec<_>>();
    assert_eq!(
        true_relations.len(),
        1,
        "one projected relation for `{lhs}` and `{rhs}`: {true_relations:?}"
    );
    true_relations[0]
}

fn language_outcome_cell(session: &mut OghamSession, lhs: &str, rhs: &str) -> OutcomeCell {
    let true_cells = OutcomeCell::ALL
        .into_iter()
        .filter(|cell| eval_bool(session, &format!("({lhs}) {} ({rhs})", cell.glyph())))
        .collect::<Vec<_>>();
    assert_eq!(
        true_cells.len(),
        1,
        "one outcome cell for `{lhs}` and `{rhs}`: {true_cells:?}"
    );
    true_cells[0]
}

fn eval_bool(session: &mut OghamSession, expression: &str) -> bool {
    let value = session
        .eval_line(expression)
        .unwrap_or_else(|err| panic!("`{expression}` failed: {err}"))
        .value
        .unwrap_or_else(|| panic!("`{expression}` returned no value"));
    match value.as_str() {
        "true" => true,
        "false" => false,
        _ => panic!("`{expression}` returned `{value}`"),
    }
}
