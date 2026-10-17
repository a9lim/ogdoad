//! Law tests: properties no finite vector list exhausts, against independent
//! oracles where one exists. Seeds are fixed so failures replay.

use grundy::GrundySession;
use ogdoad::games::{Game, LoopyPartizanGraph};

const SEED: u64 = 0x0400_5eed_cafe_f00d;

struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 11
    }

    fn index(&mut self, upper: usize) -> usize {
        (self.next() as usize) % upper
    }

    fn bit(&mut self) -> bool {
        self.next() & 1 == 1
    }
}

fn eval(session: &mut GrundySession, src: &str) -> String {
    session
        .eval_line(src)
        .unwrap_or_else(|err| panic!("`{src}` failed: {err}"))
        .value
        .unwrap_or_default()
}

fn eval_bool(session: &mut GrundySession, src: &str) -> bool {
    match eval(session, src).as_str() {
        "true" => true,
        "false" => false,
        other => panic!("`{src}` returned `{other}`"),
    }
}

// ------------------------------------------------------------ stoppers

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Projected {
    Eq,
    Lt,
    Gt,
    Fuzzy,
}

struct StopperCase {
    expression: String,
    graph: LoopyPartizanGraph,
}

fn stopper_definition(
    name: &str,
    len: usize,
    left_cycle: bool,
    lz: &[bool],
    rz: &[bool],
) -> String {
    let mut next = name.to_string();
    for node in (0..len).rev() {
        let mut left: Vec<String> = if lz[node] {
            vec!["0".into()]
        } else {
            Vec::new()
        };
        let mut right: Vec<String> = if rz[node] {
            vec!["0".into()]
        } else {
            Vec::new()
        };
        if left_cycle {
            left.push(next);
        } else {
            right.push(next);
        }
        next = format!("{{{} | {}}}", left.join(", "), right.join(", "));
    }
    format!("{name} =: {next}")
}

fn stopper_graph(len: usize, left_cycle: bool, lz: &[bool], rz: &[bool]) -> LoopyPartizanGraph {
    let zero = len;
    let mut left = vec![Vec::new(); len + 1];
    let mut right = vec![Vec::new(); len + 1];
    for node in 0..len {
        if lz[node] {
            left[node].push(zero);
        }
        if rz[node] {
            right[node].push(zero);
        }
        let target = (node + 1) % len;
        if left_cycle {
            left[node].push(target);
        } else {
            right[node].push(target);
        }
    }
    LoopyPartizanGraph::new(left, right).expect("generated tables")
}

fn random_stopper(rng: &mut Lcg, name: &str) -> (String, LoopyPartizanGraph) {
    let len = 1 + rng.index(3);
    let left_cycle = rng.bit();
    let lz: Vec<bool> = (0..len).map(|_| rng.bit()).collect();
    let rz: Vec<bool> = (0..len).map(|_| rng.bit()).collect();
    (
        stopper_definition(name, len, left_cycle, &lz, &rz),
        stopper_graph(len, left_cycle, &lz, &rz),
    )
}

/// The independent oracle: each player's finite-win attractor, computed
/// directly, never through the engine's solver or projection table.
fn force_win(graph: &LoopyPartizanGraph, winner_is_left: bool) -> Vec<bool> {
    let state = |node: usize, left_to_move: bool| 2 * node + usize::from(!left_to_move);
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
                let winner_moves = left_to_move == winner_is_left;
                let forced = if winner_moves {
                    moves.iter().any(|&t| wins[state(t, !left_to_move)])
                } else {
                    moves.iter().all(|&t| wins[state(t, !left_to_move)])
                };
                let s = state(node, left_to_move);
                if forced && !wins[s] {
                    wins[s] = true;
                    changed = true;
                }
            }
        }
        if !changed {
            return wins;
        }
    }
}

/// Independent cartesian construction of `G + (-H)`.
fn difference(lhs: &LoopyPartizanGraph, rhs: &LoopyPartizanGraph) -> LoopyPartizanGraph {
    let size = rhs.node_count();
    let n = lhs.node_count() * size;
    let pair = |a: usize, b: usize| a * size + b;
    let mut left = vec![Vec::new(); n];
    let mut right = vec![Vec::new(); n];
    for a in 0..lhs.node_count() {
        for b in 0..size {
            let s = pair(a, b);
            left[s].extend(lhs.left()[a].iter().map(|&t| pair(t, b)));
            left[s].extend(rhs.right()[b].iter().map(|&t| pair(a, t)));
            right[s].extend(lhs.right()[a].iter().map(|&t| pair(t, b)));
            right[s].extend(rhs.left()[b].iter().map(|&t| pair(a, t)));
        }
    }
    LoopyPartizanGraph::new(left, right).expect("difference graph")
}

fn survival_projection(graph: &LoopyPartizanGraph) -> Projected {
    let left_wins = force_win(graph, true);
    let right_wins = force_win(graph, false);
    let left_survives_second = !right_wins[1];
    let right_survives_second = !left_wins[0];
    match (left_survives_second, right_survives_second) {
        (true, false) => Projected::Gt,
        (false, true) => Projected::Lt,
        (false, false) => Projected::Fuzzy,
        (true, true) => Projected::Eq,
    }
}

fn language_projection(session: &mut GrundySession, lhs: &str, rhs: &str) -> Projected {
    let found: Vec<Projected> = [
        ("=", Projected::Eq),
        ("<", Projected::Lt),
        (">", Projected::Gt),
        ("∥", Projected::Fuzzy),
    ]
    .into_iter()
    .filter(|(glyph, _)| eval_bool(session, &format!("({lhs} : Form) {glyph} ({rhs} : Form)")))
    .map(|(_, relation)| relation)
    .collect();
    assert_eq!(
        found.len(),
        1,
        "one relation for `{lhs}` vs `{rhs}`: {found:?}"
    );
    found[0]
}

#[test]
fn stopper_comparisons_match_an_independent_survival_oracle() {
    let mut session = GrundySession::new();
    let mut rng = Lcg(SEED);
    let mut cases = Vec::new();
    for index in 0..16 {
        let name = format!("stop{index}");
        let (definition, graph) = random_stopper(&mut rng, &name);
        eval(&mut session, &definition);
        assert!(graph.is_stopper(0).expect("root"));
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
            graph: LoopyPartizanGraph::from_game(&game, 128).expect("small game"),
        });
    }
    for pair in 0..64 {
        let a = rng.index(cases.len());
        let b = (rng.index(cases.len() - 1) + a + 1) % cases.len();
        let expected = survival_projection(&difference(&cases[a].graph, &cases[b].graph));
        let actual = language_projection(&mut session, &cases[a].expression, &cases[b].expression);
        assert_eq!(
            actual, expected,
            "pair {pair}: {} vs {}",
            cases[a].expression, cases[b].expression
        );
    }
}

// ------------------------------------------------------------ outcome cells

const CELLS: [&str; 9] = [">>", ">‿", "><", "‿>", "‿‿", "‿<", "<>", "<‿", "<<"];

fn rotate(cell: &str) -> String {
    cell.chars()
        .rev()
        .map(|c| match c {
            '>' => '<',
            '<' => '>',
            other => other,
        })
        .collect()
}

fn language_cell(session: &mut GrundySession, lhs: &str, rhs: &str) -> String {
    let found: Vec<&str> = CELLS
        .into_iter()
        .filter(|cell| eval_bool(session, &format!("({lhs} : Form) {cell} ({rhs} : Form)")))
        .collect();
    assert_eq!(found.len(), 1, "one cell for `{lhs}` vs `{rhs}`: {found:?}");
    found[0].to_string()
}

#[test]
fn outcome_cells_rotate_under_negation_and_operand_swap() {
    let mut session = GrundySession::new();
    let mut rng = Lcg(SEED ^ 0xa11c_e5a5_51de_0002);
    let mut names = Vec::new();
    for index in 0..20 {
        let name = format!("law{index}");
        let (definition, _) = random_stopper(&mut rng, &name);
        eval(&mut session, &definition);
        names.push(name);
    }
    names.push("dud".to_string());
    eval(&mut session, "dud =: {dud | dud}");
    for pair in 0..48 {
        let a = &names[rng.index(names.len())];
        let b = &names[rng.index(names.len())];
        let cell = language_cell(&mut session, a, b);
        assert_eq!(
            language_cell(&mut session, &format!("-{a}"), &format!("-{b}")),
            rotate(&cell),
            "negation rotation, pair {pair}: {a}, {b}"
        );
        assert_eq!(
            language_cell(&mut session, b, a),
            rotate(&cell),
            "operand swap, pair {pair}"
        );
    }
}

// ------------------------------------------------------------ display law

/// Display, rebuild in a fresh session, and compare structurally (`≡`).
fn assert_rebuilds(label: &str, setup: &[String], expression: &str) {
    let mut source = GrundySession::new();
    for statement in setup {
        eval(&mut source, statement);
    }
    let display = eval(&mut source, expression);
    let executable = match display.split_once(" =: ") {
        Some((root, _)) if !display.starts_with('(') => format!("({display}; {root})"),
        _ => display.clone(),
    };
    let mut fresh = GrundySession::new();
    fresh
        .eval_line(&format!("rebuilt := {executable}"))
        .unwrap_or_else(|err| panic!("{label}: `{display}` did not rebuild: {err}"));
    for statement in setup {
        eval(&mut fresh, statement);
    }
    assert!(
        eval_bool(&mut fresh, &format!("rebuilt ≡ ({expression})")),
        "{label}: `{display}` rebuilt a different value"
    );
}

#[test]
fn loopy_displays_rebuild_equivalent_values() {
    let named: &[(&str, &[&str], &str)] = &[
        (
            "multi-SCC sum",
            &["on =: {on |}", "l =: {1 | {2 | l}}"],
            "l + on",
        ),
        (
            "shared subgraph",
            &["a =: {a |}", "b =: {a | b}"],
            "{b, b | a}",
        ),
        (
            "duplicate mutual edges",
            &["a =: {b, b | a}; b =: {| a, a}"],
            "a",
        ),
        (
            "ambient generated-name collisions",
            &["g1 := 0", "g2 := 1", "g3 := -1", "on =: {on |}"],
            "-on",
        ),
        (
            "rebinding history",
            &["a =: {a |}", "old := a", "a =: {| a}"],
            "{old | a}",
        ),
        (
            "named root with external cycle",
            &["a =: {0 | a}", "g =: {a | g}"],
            "g",
        ),
        (
            "user anchor and generated-name collision",
            &["on =: {on |}", "g1 =: {1 | g1}", "a := -on"],
            "{a | g1}",
        ),
        (
            "nested negated sums",
            &["on =: {on |}", "off =: {| off}"],
            "-((on + -off) + -(off + on))",
        ),
        (
            "sum of mutual systems",
            &["a =: {b |}; b =: {| a}", "c =: {1, d |}; d =: {| c, -1}"],
            "a + c",
        ),
    ];
    for (label, setup, expression) in named {
        let setup: Vec<String> = setup.iter().map(|s| s.to_string()).collect();
        assert_rebuilds(label, &setup, expression);
    }
    let mut rng = Lcg(SEED ^ 0xd15c_1a7e_5cc0_0004);
    for case in 0..32 {
        let count = 2 + rng.index(3);
        let names: Vec<String> = (0..count).map(|n| format!("r{case}_{n}")).collect();
        let equations = (0..count)
            .map(|node| {
                let next = &names[(node + 1) % count];
                let (mut left, mut right) = (Vec::new(), Vec::new());
                if rng.bit() {
                    left.push(next.clone());
                } else {
                    right.push(next.clone());
                }
                if rng.bit() {
                    left.push(next.clone());
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
        let mut setup: Vec<String> = (1..=rng.index(4)).map(|i| format!("g{i} := {i}")).collect();
        setup.push(equations);
        let expression = match rng.index(4) {
            0 => names[0].clone(),
            1 => format!("{{9 | {}}}", names[0]),
            2 => format!("-{}", names[0]),
            _ => format!("{{{0}, {0} | {1}}}", names[0], names[count - 1]),
        };
        assert_rebuilds(&format!("random system {case}"), &setup, &expression);
    }
}

#[test]
fn every_value_display_is_a_fixed_point() {
    let programs: &[(&[&str], &str)] = &[
        (&[], "[(1, true), (2, false)]"),
        (&[], "{0 | 1} + *1"),
        (&[], "(t↑3 - t : F7[t])"),
        (&[], "(1/t + 1 : F3(t))"),
        (&[], "(x + 1 : F27)"),
        (&[], "*3 ⋅ *5"),
        (&[], "(*ω : Ordinal) + (*3 : Ordinal)"),
        (&[], "3⋅ω↑2 - ω + 1/2"),
        (&["k := 3"], "x ↦ x + k"),
        (
            &["fact =: n ↦ if n = 0 then 1 else n ⋅ fact(n - 1)"],
            "fact",
        ),
        (
            &["data Tree = Leaf | Node(Tree, Tree)"],
            "Node(Leaf, Node(Leaf, Leaf))",
        ),
        (
            &["alg := clifford([1, 2])", "[e0, e1] := basis(alg)"],
            "3⋅e0∧e1 + e1",
        ),
        (
            &["gr := grassmann(2) : Algebra(F5)", "[e0, e1] := basis(gr)"],
            "e0∧e1",
        ),
        (&[], "impartial(n ↦ [[k] for k in 0..n])"),
        (&["over =: {0 | over}"], "certify(over)"),
        (
            &["n := impartial(n ↦ [[k] for k in 0..n])"],
            "misere_quotient(n, [1, 2], 2, 2)",
        ),
        (
            &["g := impartial(n ↦ [[a, n - a] for a in 1..n if 2⋅a < n])"],
            "certify_sg(g, 8)",
        ),
        (&[], "periodic(octal([7, 7]), 71, 12)"),
    ];
    for (setup, expression) in programs {
        let mut session = GrundySession::new();
        for statement in *setup {
            eval(&mut session, statement);
        }
        let shown = eval(&mut session, expression);
        let mut fresh = GrundySession::new();
        if expression.contains("Node") {
            eval(&mut fresh, setup[0]);
        }
        let again = eval(&mut fresh, &shown);
        assert_eq!(again, shown, "`{expression}` display is not a fixed point");
    }
}

// ------------------------------------------------------------ rulesets

/// A random terminating impartial ruleset on heaps: every option strictly
/// lowers the total, and may split.
fn random_ruleset(rng: &mut Lcg) -> String {
    let removals: Vec<u64> = (0..1 + rng.index(3)).map(|_| 1 + rng.next() % 3).collect();
    let split = rng.bit();
    let list = removals
        .iter()
        .map(u64::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    if split {
        format!("impartial(n ↦ [[a, n - k - a] for k in [{list}] if k ≤ n for a in 0..=n - k])")
    } else {
        format!("impartial(n ↦ [[n - k] for k in [{list}] if k ≤ n])")
    }
}

#[test]
fn values_of_impartial_rulesets_are_their_grundy_nimbers() {
    let mut rng = Lcg(SEED ^ 0x5a6e_7a1e_0000_0005);
    for case in 0..12 {
        let mut session = GrundySession::new();
        let rules = random_ruleset(&mut rng);
        eval(&mut session, &format!("r := {rules}"));
        for n in 0..12 {
            let sg = eval(&mut session, &format!("sg(r, {n})"));
            assert!(
                eval_bool(
                    &mut session,
                    &format!("value(r, {n}) = game(*{sg} : Nimber)")
                ),
                "case {case} `{rules}` heap {n}: value is not *{sg}"
            );
        }
    }
}

#[test]
fn winning_moves_are_exactly_the_moves_to_second_player_wins() {
    let mut rng = Lcg(SEED ^ 0x0b5e_55ed_0000_0006);
    for case in 0..10 {
        let mut session = GrundySession::new();
        let rules = random_ruleset(&mut rng);
        eval(&mut session, &format!("r := {rules}"));
        let heaps: Vec<String> = (0..2 + rng.index(2))
            .map(|_| (1 + rng.index(6)).to_string())
            .collect();
        let sum = format!("[{}]", heaps.join(", "));
        // Independent check through the presented sum-state graph: a move wins
        // exactly when its successor is a second-player win.
        let check = format!(
            "all(m ↦ contains(winning(r, {sum}, Left), m) = (outcome(graph_of(m)) = (Right, Left)), moves(r, {sum}, Left))"
        );
        eval(
            &mut session,
            "graph_of := m ↦ fold((acc, c) ↦ acc + graph(r, c), 0 : Form, m)",
        );
        assert!(
            eval_bool(&mut session, &check),
            "case {case} `{rules}` at {sum}"
        );
    }
}

#[test]
fn certified_outcomes_agree_with_direct_outcomes() {
    let mut session = GrundySession::new();
    let mut rng = Lcg(SEED ^ 0xce27_1f1e_0000_0007);
    eval(&mut session, "claim_cell := c ↦ c");
    for index in 0..24 {
        let name = format!("s{index}");
        let (definition, _) = random_stopper(&mut rng, &name);
        eval(&mut session, &definition);
        let claim = eval(&mut session, &format!("certify({name} + -{name})"));
        let (want_l, want_r) = {
            let out = eval(&mut session, &format!("outcome({name} + -{name})"));
            let trimmed = out.trim_matches(|c| c == '(' || c == ')').to_string();
            let mut parts = trimmed.split(", ");
            (
                parts.next().unwrap().to_string(),
                parts.next().unwrap().to_string(),
            )
        };
        assert!(
            claim.ends_with(&format!("/* claim: outcome ({want_l}, {want_r}) */")),
            "claim `{claim}` disagrees with ({want_l}, {want_r})"
        );
    }
}

// ------------------------------------------------------------ literals

#[test]
fn fraction_literals_agree_with_division_wherever_both_exist() {
    // Agreement includes failure: in characteristic 3, `1/3` and `(1)/(3)`
    // are both a division by zero.
    let mut session = GrundySession::new();
    let outcome = |session: &mut GrundySession, src: &str| match session.eval_line(src) {
        Ok(out) => out.value.unwrap_or_default(),
        Err(err) => err.kind.code().to_string(),
    };
    for ty in ["Surreal", "F5", "F7", "F5(t)", "F9", "F2[t]"] {
        for (num, den) in [(1, 2), (3, 4), (-2, 3), (6, 1), (1, 3), (2, 5)] {
            let literal = outcome(&mut session, &format!("({num}/{den} : {ty})"));
            let division = outcome(&mut session, &format!("(({num}) / ({den}) : {ty})"));
            assert_eq!(literal, division, "{num}/{den} at {ty}");
        }
    }
}
