use ogdoad::games::{Game, LoopyPartizanGraph};
use ogdoad::grundy::{ast::OutcomeCell, GrundySession};

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
    let mut session = GrundySession::new("game").expect("game world");
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
    let mut session = GrundySession::new("game").expect("game world");
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

#[test]
fn seeded_loopy_displays_rebuild_equivalent_values_in_fresh_sessions() {
    let named = vec![
        DisplayCase::new(
            "multi-SCC sum",
            ["on =: {on |}", "l =: [1, 2] ⧺ l"],
            "l + on",
        ),
        DisplayCase::new(
            "shared subgraph",
            ["a =: {a |}", "b =: {a | b}"],
            "{b, b | a}",
        ),
        DisplayCase::new(
            "duplicate mutual edges",
            ["a =: {b, b | a}; b =: {| a, a}"],
            "a",
        ),
        DisplayCase::new(
            "ambient generated-name collisions",
            ["g1 := 0", "g2 := 1", "g3 := -1", "on =: {on |}"],
            "-on",
        ),
        DisplayCase::new(
            "rebinding history",
            ["a =: {a |}", "old := a", "a =: {| a}"],
            "{old | a}",
        ),
        DisplayCase::new(
            "named root with external cycle",
            ["a =: {0 | a}", "g =: {a | g}"],
            "g",
        ),
        DisplayCase::new(
            "named root with anonymous negated cycle",
            ["on =: {on |}", "x := -on", "g =: {x | g}"],
            "g",
        ),
        DisplayCase::new(
            "user anchor and generated-name collision",
            ["on =: {on |}", "g1 =: {1 | g1}", "a := -on"],
            "{a | g1}",
        ),
        DisplayCase::new(
            "nested negated sums",
            ["on =: {on |}", "off =: {| off}"],
            "-((on + -off) + -(off + on))",
        ),
        DisplayCase::new(
            "sum-product graph of mutual systems",
            ["a =: {b |}; b =: {| a}", "c =: {1, d |}; d =: {| c, -1}"],
            "a + c",
        ),
    ];
    for case in &named {
        assert_display_roundtrip(case);
    }

    let mut rng = Lcg(SEED ^ 0xd15c_1a7e_5cc0_0004);
    for case_index in 0..32 {
        let case = randomized_display_case(&mut rng, case_index);
        assert_display_roundtrip(&case);
    }
}

struct DisplayCase {
    label: String,
    setup: Vec<String>,
    expression: String,
}

impl DisplayCase {
    fn new<const N: usize>(label: &str, setup: [&str; N], expression: &str) -> Self {
        Self {
            label: label.to_string(),
            setup: setup.into_iter().map(str::to_string).collect(),
            expression: expression.to_string(),
        }
    }
}

fn randomized_display_case(rng: &mut Lcg, case_index: usize) -> DisplayCase {
    let count = 2 + rng.index(3);
    let names = (0..count)
        .map(|node| format!("r{case_index}_{node}"))
        .collect::<Vec<_>>();
    let equations = (0..count)
        .map(|node| {
            let next = (node + 1) % count;
            let mut left = Vec::new();
            let mut right = Vec::new();
            if rng.bit() {
                left.push(names[next].clone());
            } else {
                right.push(names[next].clone());
            }
            if rng.bit() {
                left.push(names[next].clone());
            }
            if rng.bit() {
                left.push((rng.index(4) as i128 - 1).to_string());
            }
            if rng.bit() {
                right.push((rng.index(4) as i128 - 1).to_string());
            }
            format!(
                "{} =: {{{} | {}}}",
                names[node],
                left.join(", "),
                right.join(", ")
            )
        })
        .collect::<Vec<_>>()
        .join("; ");
    let mut setup = (1..=rng.index(4))
        .map(|index| format!("g{index} := {index}"))
        .collect::<Vec<_>>();
    setup.push(equations);
    let expression = match rng.index(4) {
        0 => names[0].clone(),
        1 => format!("{{9 | {}}}", names[0]),
        2 => format!("-{}", names[0]),
        _ => format!("{{{0}, {0} | {1}}}", names[0], names[count - 1]),
    };
    DisplayCase {
        label: format!("seeded random system {case_index}"),
        setup,
        expression,
    }
}

fn assert_display_roundtrip(case: &DisplayCase) {
    let mut source = GrundySession::new("game").expect("source game world");
    for statement in &case.setup {
        source.eval_line(statement).unwrap_or_else(|err| {
            panic!("{} source setup `{statement}` failed: {err}", case.label)
        });
    }
    let display = source
        .eval_line(&case.expression)
        .unwrap_or_else(|err| panic!("{} source expression failed: {err}", case.label))
        .value
        .unwrap_or_else(|| panic!("{} source expression returned no value", case.label));
    let executable = executable_display(&display);

    let mut fresh = GrundySession::new("game").expect("fresh game world");
    fresh
        .eval_line(&format!("rebuilt := {executable}"))
        .unwrap_or_else(|err| {
            panic!(
                "{} display did not evaluate in a fresh session: `{display}`: {err}",
                case.label
            )
        });
    for statement in &case.setup {
        fresh.eval_line(statement).unwrap_or_else(|err| {
            panic!(
                "{} comparison setup `{statement}` failed: {err}",
                case.label
            )
        });
    }
    assert!(
        eval_bool(&mut fresh, &format!("rebuilt ≡ ({})", case.expression)),
        "{} rebuilt a structurally different value from `{display}`",
        case.label
    );
}

fn executable_display(display: &str) -> String {
    if display.starts_with('(') {
        return display.to_string();
    }
    let root = display
        .split_once(" =:")
        .map(|(name, _)| name)
        .expect("loopy display equation root");
    format!("({display}; {root})")
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
    session: &mut GrundySession,
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

fn language_outcome_cell(session: &mut GrundySession, lhs: &str, rhs: &str) -> OutcomeCell {
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

fn eval_bool(session: &mut GrundySession, expression: &str) -> bool {
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
