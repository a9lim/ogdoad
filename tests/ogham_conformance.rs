use ogdoad::ogham::{
    ast::OutcomeCell, parse_statement, unparse_statement, EvalLine, OghamError, OghamErrorKind,
    OghamSession,
};

#[derive(Debug)]
enum Outcome {
    Ok(EvalLine),
    Err(OghamError),
}

#[test]
fn ogham_conformance_corpus() {
    let corpus = include_str!("../docs/ogham/conformance.txt");
    run_corpus(corpus);
}

#[test]
fn stage_b_atoms_and_containers_round_trip_through_canonical_syntax() {
    for input in [
        "#2",
        "#(1 + 2)",
        "up",
        "down",
        "dim",
        "[up, down, #3]",
        "true ? #1 : false ? #2 : #3",
        "t↑#(1 + 1)",
        "ω↑#2",
        "ω↑#(1 + 1)",
        "coef([1, 2], #1)",
        "/(*2)",
        "1/(/2)",
    ] {
        let parsed = parse_statement(input)
            .unwrap_or_else(|err| panic!("syntax failed for `{input}`: {err}"));
        let canonical = unparse_statement(&parsed);
        let reparsed = parse_statement(&canonical)
            .unwrap_or_else(|err| panic!("canonical syntax `{canonical}` failed: {err}"));
        assert_eq!(parsed, reparsed, "parse/unparse identity for `{input}`");
    }
}

#[test]
fn stage_e_outcome_syntax_round_trips_and_underscore_stays_contextual() {
    for (input, canonical) in [
        ("1 >> 0", "1 >> 0"),
        ("1 >_ 0", "1 >‿ 0"),
        ("1 >< 0", "1 >< 0"),
        ("1 _> 0", "1 ‿> 0"),
        ("1 __ 0", "1 ‿‿ 0"),
        ("1 _< 0", "1 ‿< 0"),
        ("1 <> 0", "1 <> 0"),
        ("1 <_ 0", "1 <‿ 0"),
        ("1 << 0", "1 << 0"),
        ("foo_bar := 1", "foo_bar := 1"),
        ("foo__bar := 2", "foo__bar := 2"),
    ] {
        let parsed = parse_statement(input)
            .unwrap_or_else(|err| panic!("syntax failed for `{input}`: {err}"));
        assert_eq!(unparse_statement(&parsed), canonical);
        let reparsed = parse_statement(canonical)
            .unwrap_or_else(|err| panic!("canonical syntax `{canonical}` failed: {err}"));
        assert_eq!(parsed, reparsed, "parse/unparse identity for `{input}`");
    }

    for atom in ["_", "‿"] {
        let lone = parse_statement(&format!("1 {atom} 2"))
            .expect_err("a lone mover atom must be rejected");
        assert_eq!(lone.kind, OghamErrorKind::Parse);
        assert_eq!(
            lone.hint.as_deref(),
            Some("mover-result atoms come in pairs")
        );
    }
}

#[test]
fn stage_e_nine_cells_are_exact_and_obey_rotation_swap_and_hasdraw_union() {
    let mut session = OghamSession::new("game").expect("game world");
    for definition in [
        "on =: {on |}",
        "off =: {| off}",
        "dud =: {dud | dud}",
        "ll := on",
        "ld := {0 | dud}",
        "lr := *1",
        "dl := {dud |}",
        "dd := dud",
        "dr := {dud | 0}",
        "rl := 0",
        "rd := {| dud}",
        "rr := off",
    ] {
        session
            .eval_line(definition)
            .unwrap_or_else(|err| panic!("definition `{definition}` failed: {err}"));
    }

    let witnesses = [
        ("ll", OutcomeCell::LeftLeft),
        ("ld", OutcomeCell::LeftDraw),
        ("lr", OutcomeCell::LeftRight),
        ("dl", OutcomeCell::DrawLeft),
        ("dd", OutcomeCell::DrawDraw),
        ("dr", OutcomeCell::DrawRight),
        ("rl", OutcomeCell::RightLeft),
        ("rd", OutcomeCell::RightDraw),
        ("rr", OutcomeCell::RightRight),
    ];

    for (value, expected) in witnesses {
        assert_eq!(language_outcome_cell(&mut session, value, "0"), expected);
        assert_eq!(
            language_outcome_cell(&mut session, &format!("-({value})"), "0"),
            expected.rotate(),
            "negation rotation for {value}"
        );
        assert_eq!(
            language_outcome_cell(&mut session, "0", value),
            expected.rotate(),
            "operand swap rotation for {value}"
        );

        let hasdraw = eval_language_bool(&mut session, &format!("hasdraw({value})"));
        let union = eval_language_bool(
            &mut session,
            &format!(
                "{value} >‿ 0 or {value} ‿> 0 or {value} ‿‿ 0 or {value} ‿< 0 or {value} <‿ 0"
            ),
        );
        assert_eq!(hasdraw, union, "hasdraw union for {value}");
    }

    for (lhs, rhs) in [("1", "0"), ("*1", "0"), ("on", "dud"), ("ld", "rd")] {
        let _ = language_outcome_cell(&mut session, lhs, rhs);
    }

    for lhs in ["-1", "0", "1", "*1", "*2"] {
        for rhs in ["-1", "0", "1", "*1", "*2"] {
            assert!(matches!(
                language_outcome_cell(&mut session, lhs, rhs),
                OutcomeCell::LeftLeft
                    | OutcomeCell::LeftRight
                    | OutcomeCell::RightLeft
                    | OutcomeCell::RightRight
            ));
        }
    }
}

#[test]
fn stage_e_budget_witness_and_wrong_world_errors_are_distinct() {
    let mut materialization = OghamSession::new("game").expect("game world");
    materialization.set_graph_budget(0);
    let definition_budget = materialization
        .eval_line("on =: {on |}")
        .expect_err("a recursive graph root consumes one node");
    assert_eq!(definition_budget.kind, OghamErrorKind::GraphBudget);

    let mut game = OghamSession::new("game").expect("game world");
    game.eval_line("dud =: {dud | dud}")
        .expect("dud definition");
    let loopy = game
        .eval_line("dud = 0")
        .expect_err("non-stopper single must be refused");
    assert_eq!(loopy.kind, OghamErrorKind::Loopy);
    assert!(loopy.message.contains("alternating cycle 0:L→0:R→0:L"));
    let right_loopy = game
        .eval_line("0 = dud")
        .expect_err("the right presented operand must also pass the stopper gate");
    assert_eq!(right_loopy.kind, OghamErrorKind::Loopy);
    assert!(right_loopy
        .message
        .contains("right operand has alternating cycle"));

    game.eval_line("over =: {0 | over}")
        .expect("over definition");
    game.eval_line("under =: {under | 0}")
        .expect("under definition");
    game.set_graph_budget(2);
    let budget = game
        .eval_line("over + under")
        .expect_err("product must exceed the tiny graph budget");
    assert_eq!(budget.kind, OghamErrorKind::GraphBudget);
    assert_ne!(budget.kind, loopy.kind);
    game.set_world("game").expect("world reset");
    assert_eq!(game.graph_budget(), 1 << 16);

    let mut integer = OghamSession::new("integer 0").expect("integer world");
    let double = integer
        .eval_line("1 >> 0")
        .expect_err("outcome doubles are game-only");
    assert_eq!(double.kind, OghamErrorKind::WrongWorld);
    let stopper = integer
        .eval_line("stopper(0)")
        .expect_err("stopper is game-only");
    assert_eq!(stopper.kind, OghamErrorKind::WrongWorld);

    let outcome = integer
        .eval_line("outcome(0)")
        .expect_err("outcome is taught as relations");
    assert_eq!(outcome.kind, OghamErrorKind::Unbound);
    assert!(outcome
        .hint
        .as_deref()
        .is_some_and(|hint| hint.contains("relations against 0")));
}

fn language_outcome_cell(session: &mut OghamSession, lhs: &str, rhs: &str) -> OutcomeCell {
    let true_cells = OutcomeCell::ALL
        .into_iter()
        .filter(|cell| eval_language_bool(session, &format!("({lhs}) {} ({rhs})", cell.glyph())))
        .collect::<Vec<_>>();
    assert_eq!(
        true_cells.len(),
        1,
        "exactly one outcome cell for `{lhs}` and `{rhs}`: {true_cells:?}"
    );
    true_cells[0]
}

fn eval_language_bool(session: &mut OghamSession, input: &str) -> bool {
    let value = session
        .eval_line(input)
        .unwrap_or_else(|err| panic!("Bool expression `{input}` failed: {err}"))
        .value
        .unwrap_or_else(|| panic!("Bool expression `{input}` returned no value"));
    match value.as_str() {
        "true" => true,
        "false" => false,
        _ => panic!("Bool expression `{input}` returned `{value}`"),
    }
}

#[test]
fn stage_b_parse_guidance_is_carried_by_hints() {
    let mut poly = OghamSession::new("poly5").expect("poly5 world");
    let product = poly
        .eval_line("t * t")
        .expect_err("ASCII star is not product");
    assert_eq!(product.kind, OghamErrorKind::Parse);
    assert_eq!(
        product.hint.as_deref(),
        Some("`*` is the nimber prefix; the product is `⋅` (sugar `.`)")
    );

    let mut game = OghamSession::new("game").expect("game world");
    let not_equal = game
        .eval_line("*1 != *2")
        .expect_err("not-equal has a teaching error");
    assert_eq!(not_equal.kind, OghamErrorKind::Parse);
    assert_eq!(
        not_equal.hint.as_deref(),
        Some("not-equal is `not (a = b)`; `!` is fuzzy `∥`")
    );

    let pipe = game
        .eval_line("*1 | *2")
        .expect_err("a relation-tier bar has a teaching error");
    assert_eq!(pipe.kind, OghamErrorKind::Parse);
    assert_eq!(
        pipe.hint.as_deref(),
        Some("the braceform bar is structural; fuzzy is `∥` (sugar `!`)")
    );

    let braces = game
        .eval_line("{1, 2}")
        .expect_err("barless braces are not containers");
    assert_eq!(braces.kind, OghamErrorKind::Parse);
    assert_eq!(
        braces.hint.as_deref(),
        Some("`[a, b]` is the list; braces are game forms `{L | R}`")
    );

    for name in ["up", "down"] {
        let literal = game
            .eval_line(&format!("{name}()"))
            .expect_err("call spelling was removed for literal atoms");
        assert_eq!(literal.kind, OghamErrorKind::UnknownFn);
        let expected = format!("`{name}` is a literal now");
        assert_eq!(literal.hint.as_deref(), Some(expected.as_str()));
    }

    let mut integer = OghamSession::new("integer 0").expect("integer world");
    let dim = integer
        .eval_line("dim()")
        .expect_err("dim call spelling was removed");
    assert_eq!(dim.kind, OghamErrorKind::UnknownFn);
    assert_eq!(dim.hint.as_deref(), Some("`dim` is a literal now"));

    let function = integer
        .eval_line("id(x) := x")
        .expect_err("function-definition call syntax was removed");
    assert_eq!(function.kind, OghamErrorKind::Parse);
    assert_eq!(
        function.hint.as_deref(),
        Some("functions are lambdas: `name := x ↦ …`")
    );
}

fn run_corpus(corpus: &str) {
    let mut session: Option<OghamSession> = None;
    let mut pending: Option<(usize, String, Outcome)> = None;
    let lines = corpus.lines().collect::<Vec<_>>();
    let mut idx = 0usize;
    while idx < lines.len() {
        let raw = lines[idx];
        let line_no = idx + 1;
        let line = raw.trim();
        idx += 1;
        if line.is_empty() || line.starts_with("//") {
            continue;
        }
        if let Some(decl) = line.strip_prefix("@world ") {
            finish_pending(&mut pending);
            session = Some(
                OghamSession::new(decl)
                    .unwrap_or_else(|err| panic!("line {line_no}: world failed: {err}")),
            );
            continue;
        }
        if let Some(raw_budget) = line.strip_prefix("@fuel ") {
            finish_pending(&mut pending);
            let budget = raw_budget
                .trim()
                .parse::<u128>()
                .unwrap_or_else(|_| panic!("line {line_no}: fuel budget must be a u128"));
            session
                .as_mut()
                .unwrap_or_else(|| panic!("line {line_no}: @fuel before @world"))
                .set_fuel_budget(budget);
            continue;
        }
        if let Some(raw_budget) = line.strip_prefix("@graph ") {
            finish_pending(&mut pending);
            let budget = raw_budget
                .trim()
                .parse::<u128>()
                .unwrap_or_else(|_| panic!("line {line_no}: graph budget must be a u128"));
            session
                .as_mut()
                .unwrap_or_else(|| panic!("line {line_no}: @graph before @world"))
                .set_graph_budget(budget);
            continue;
        }
        if let Some(input) = line.strip_prefix("> ") {
            finish_pending(&mut pending);
            let mut input = input.to_string();
            while idx < lines.len() {
                let cont = lines[idx].trim();
                if let Some(rest) = cont.strip_prefix(">> ") {
                    input.push('\n');
                    input.push_str(rest);
                    idx += 1;
                } else {
                    break;
                }
            }
            let sess = session
                .as_mut()
                .unwrap_or_else(|| panic!("line {line_no}: statement before @world"));
            let outcome = match sess.eval_line(&input) {
                Ok(line) => Outcome::Ok(line),
                Err(err) => Outcome::Err(err),
            };
            pending = Some((line_no, input, outcome));
            continue;
        }
        if line.starts_with(">> ") {
            panic!("line {line_no}: continuation without input");
        }
        if let Some(expected) = line.strip_prefix("~ ") {
            let Some((input_line, input, outcome)) = pending.as_ref() else {
                panic!("line {line_no}: canonical expectation without input");
            };
            match outcome {
                Outcome::Ok(out) => assert_eq!(
                    out.canonical, expected,
                    "line {input_line}: canonical echo for `{input}`"
                ),
                Outcome::Err(err) => {
                    panic!("line {input_line}: expected canonical echo but got {err}")
                }
            }
            continue;
        }
        if let Some(expected) = line.strip_prefix("= ") {
            let Some((input_line, input, outcome)) = pending.take() else {
                panic!("line {line_no}: value expectation without input");
            };
            match outcome {
                Outcome::Ok(out) => assert_eq!(
                    out.value.as_deref(),
                    Some(expected),
                    "line {input_line}: value for `{input}`"
                ),
                Outcome::Err(err) => panic!("line {input_line}: expected value but got {err}"),
            }
            continue;
        }
        if let Some(expected) = line.strip_prefix("! ") {
            let Some((input_line, input, outcome)) = pending.take() else {
                panic!("line {line_no}: error expectation without input");
            };
            let (kind, needle) = expected
                .split_once(':')
                .map_or((expected, ""), |(kind, needle)| {
                    (kind.trim(), needle.trim())
                });
            match outcome {
                Outcome::Err(err) => {
                    assert_eq!(
                        err.kind.code(),
                        kind,
                        "line {input_line}: error kind for `{input}`"
                    );
                    let haystack = format!("{err}");
                    assert!(
                        needle.is_empty() || haystack.contains(needle),
                        "line {input_line}: expected error substring `{needle}` in `{haystack}`"
                    );
                }
                Outcome::Ok(out) => panic!("line {input_line}: expected error but got {out:?}"),
            }
            continue;
        }
        panic!("line {line_no}: unknown corpus directive `{line}`");
    }
    finish_pending(&mut pending);
}

fn finish_pending(pending: &mut Option<(usize, String, Outcome)>) {
    let Some((line_no, input, outcome)) = pending.take() else {
        return;
    };
    match outcome {
        Outcome::Ok(out) => {
            assert!(
                out.value.is_none(),
                "line {line_no}: `{input}` produced unexpected value {:?}",
                out.value
            );
        }
        Outcome::Err(err) => panic!("line {line_no}: `{input}` failed unexpectedly: {err}"),
    }
}

#[test]
fn error_kind_codes_are_stable() {
    assert_eq!(OghamErrorKind::BareInt.code(), "E_BareInt");
    assert_eq!(OghamErrorKind::KummerEscape.code(), "E_KummerEscape");
    assert_eq!(OghamErrorKind::Fuel.code(), "E_Fuel");
    assert_eq!(OghamErrorKind::Improper.code(), "E_Improper");
    assert_eq!(OghamErrorKind::Unfounded.code(), "E_Unfounded");
    assert_eq!(OghamErrorKind::Loopy.code(), "E_Loopy");
    assert_eq!(OghamErrorKind::GraphBudget.code(), "E_GraphBudget");
}

#[test]
fn captured_recursive_function_survives_rebinding() {
    let mut session = OghamSession::new("integer 0").expect("integer world");
    session
        .eval_line("fact =: n ↦ n = 0 ? 1 : n⋅fact@(n - 1)")
        .expect("recursive definition");
    session
        .eval_line("captured := n ↦ fact@n")
        .expect("capture recursive value");
    session
        .eval_line("fact := n ↦ 0")
        .expect("rebind original name");
    let result = session.eval_line("captured@5").expect("call capture");
    assert_eq!(result.value.as_deref(), Some("120"));
}

#[test]
fn recursion_depth_guard_preempts_the_host_stack() {
    let mut session = OghamSession::new("integer 0").expect("integer world");
    session
        .eval_line("f =: n ↦ n = 0 ? 0 : f@(n - 1)")
        .expect("recursive definition");
    let err = session
        .eval_line("f@60000")
        .expect_err("deep descent must stop before overflowing the host stack");
    assert_eq!(err.kind, OghamErrorKind::Fuel);
    assert!(err.message.contains("recursion depth safety guard"));
    assert!(err.message.contains("1024 frames"));
    assert!(err.message.contains("step(s) remaining"));
}

#[test]
fn recursive_list_folds_have_realistic_worker_stack_headroom() {
    let mut session = OghamSession::new("game").expect("game world");
    session
        .eval_line("len =: m ↦ nleft(m) = 0 ? 0 : 1 + len@(right(m, 0))")
        .expect("recursive list length");

    for length in [80_u128, 1000] {
        let items = (0..length)
            .map(|value| value.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let result = session
            .eval_line(&format!("len@[{items}]"))
            .unwrap_or_else(|err| panic!("length-{length} list fold failed: {err}"));
        let expected = format!("#{length}");
        assert_eq!(result.value.as_deref(), Some(expected.as_str()));
    }
}

#[test]
fn flat_container_syntax_does_not_create_recursive_ast_depth() {
    let mut session = OghamSession::new("game").expect("game world");
    let items = (0_u128..2000)
        .map(|value| value.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    session
        .eval_line(&format!("[{items}]"))
        .expect("the flat container AST is bounded independently of its length");
}

#[test]
fn delimiter_depth_errors_before_the_recursive_parser() {
    let mut session = OghamSession::new("integer 0").expect("integer world");
    let input = format!("{}0{}", "(".repeat(2000), ")".repeat(2000));
    let err = session
        .eval_line(&input)
        .expect_err("deep delimiters must stop before the recursive parser");
    assert_eq!(err.kind, OghamErrorKind::Parse);
    assert!(err.message.contains("source nesting"));
    assert!(err.message.contains("1536 delimiters"));
}

#[test]
fn world_metric_depth_is_guarded_on_the_persistent_worker() {
    let mut session = OghamSession::new("integer 0").expect("integer world");
    let decl = format!(
        ":world integer 1 q=[{}1{}]",
        "(".repeat(1600),
        ")".repeat(1600)
    );
    let err = session
        .set_world(&decl)
        .expect_err("deep metric syntax must be rejected without aborting the host");
    assert_eq!(err.kind, OghamErrorKind::Parse);
    assert!(err.message.contains("source nesting"));
    assert!(err.message.contains("1536 delimiters"));

    let result = session
        .eval_line("7")
        .expect("the persistent worker and prior world remain usable");
    assert_eq!(result.value.as_deref(), Some("7"));
}

#[test]
fn centralized_guidance_uses_the_hint_field() {
    let mut poly = OghamSession::new("polyint").expect("polyint world");
    let modulus = poly
        .eval_line("(t↑2 - 1) % (2⋅t + 2)")
        .expect_err("non-monic divisor");
    assert_eq!(modulus.kind, OghamErrorKind::Modulus);
    assert!(!modulus.message.contains("monic"));
    assert!(modulus
        .hint
        .as_deref()
        .is_some_and(|hint| hint.contains("must be monic")));

    let mut integer = OghamSession::new("integer 0").expect("integer world");
    let equiv = integer
        .eval_line("1 ≡ 1")
        .expect_err("form equality is game-only");
    assert_eq!(equiv.kind, OghamErrorKind::WrongWorld);
    assert_eq!(
        equiv.hint.as_deref(),
        Some("`=` is already structural here")
    );
}

#[test]
fn step_fuel_message_remains_distinct_from_depth_guard() {
    let mut session = OghamSession::new("integer 0").expect("integer world");
    session
        .eval_line("fib =: n ↦ n < 2 ? n : fib@(n - 1) + fib@(n - 2)")
        .expect("recursive definition");
    session.set_fuel_budget(5000);
    let err = session
        .eval_line("fib@25")
        .expect_err("step fuel must catch broad recursion");
    assert_eq!(err.kind, OghamErrorKind::Fuel);
    assert!(err.message.contains("exhausted its fuel budget of 5000"));
    assert!(!err.message.contains("recursion depth safety guard"));
}

#[test]
fn recursive_function_restores_definition_time_world_validation() {
    let mut session = OghamSession::new("fp5 0").expect("fp5 world");
    let err = session
        .eval_line("bad =: x ↦ x < 1 ? bad@x : x")
        .expect_err("ordered comparison must fail while defining the recursive function");
    assert_eq!(err.kind, OghamErrorKind::WrongWorld);
}

#[test]
fn ogham_game_form_equality_is_multiset_structural() {
    let mut session = OghamSession::new("game").expect("game world");
    let reordered = session
        .eval_line("{0, 1 |} ≡ {1, 0 |}")
        .expect("multiset structural comparison");
    assert_eq!(reordered.value.as_deref(), Some("true"));

    let multiplicity = session
        .eval_line("{0, 0 |} ≡ {0 |}")
        .expect("multiplicity-sensitive structural comparison");
    assert_eq!(multiplicity.value.as_deref(), Some("false"));

    let factorial = session
        .eval_line("!5")
        .expect_err("factorial prefix was removed in 0.3.5");
    assert_eq!(factorial.kind, OghamErrorKind::Parse);

    session
        .eval_line("loop =: {loop |}")
        .expect("guarded loopy Element fixpoint");
    let loop_value = session.eval_line("loop").expect("display loopy value");
    assert_eq!(loop_value.value.as_deref(), Some("loop =: {loop |}"));
}

#[test]
fn cyclic_form_equality_uses_unordered_bisimulation() {
    let mut session = OghamSession::new("game").expect("game world");
    session
        .eval_line("a =: {0, a | *1}")
        .expect("first regular tree");
    session
        .eval_line("b =: {b, 0 | *1}")
        .expect("alpha-renamed reordered regular tree");
    let reordered = session
        .eval_line("a ≡ b")
        .expect("unordered cyclic bisimilarity");
    assert_eq!(reordered.value.as_deref(), Some("true"));

    session
        .eval_line("c =: {c, c |}")
        .expect("multiplicity-two cycle");
    session
        .eval_line("d =: {d |}")
        .expect("multiplicity-one cycle");
    let multiplicity = session
        .eval_line("c ≡ d")
        .expect("cyclic multiplicity check");
    assert_eq!(multiplicity.value.as_deref(), Some("false"));

    session
        .eval_line("aa =: {0 | aa}")
        .expect("zero-headed cycle");
    session
        .eval_line("bb =: {*1 | bb}")
        .expect("star-headed cycle");
    let unequal = session
        .eval_line("aa ≡ bb")
        .expect("different cyclic unfoldings");
    assert_eq!(unequal.value.as_deref(), Some("false"));

    session
        .eval_line("p1 =: {0 | p1}")
        .expect("period-one presentation");
    session
        .eval_line("p2 =: {0 | {0 | p2}}")
        .expect("period-two presentation of the same unfolding");
    let periods = session
        .eval_line("p1 ≡ p2")
        .expect("finite presentations of one regular tree");
    assert_eq!(periods.value.as_deref(), Some("true"));
}

#[test]
fn drawn_rename_guidance_uses_the_hint_field() {
    let mut session = OghamSession::new("game").expect("game world");
    let err = session
        .eval_line("drawn(0)")
        .expect_err("the old draw predicate name was removed");
    assert_eq!(err.kind, OghamErrorKind::UnknownFn);
    assert_eq!(
        err.hint.as_deref(),
        Some("`drawn` was renamed to `hasdraw`")
    );
    assert!(!err.message.contains("hasdraw"));
}

#[test]
fn ogham_coinductive_append_walk_outcomes_and_fixpoint_reduction() {
    let mut session = OghamSession::new("game").expect("game world");
    session
        .eval_line("ones =: {1 | ones}")
        .expect("constant stream");

    let graft = session
        .eval_line("[1, 2] ⧺ [3]")
        .expect("finite spine reaches nil");
    assert_eq!(graft.value.as_deref(), Some("[1, 2, 3]"));

    let cycle = session
        .eval_line("ones ⧺ canon(ones)")
        .expect("cyclic spine is the append result");
    assert_eq!(cycle.value.as_deref(), Some("ones =: {1 | ones}"));

    let prefixed_cycle = session
        .eval_line("([9] ⧺ ones) ⧺ {5 | 0}")
        .expect("finite prefix into a cycle is unchanged");
    assert_eq!(
        prefixed_cycle.value.as_deref(),
        Some("(ones =: {1 | ones}; {9 | ones})")
    );

    let improper = session
        .eval_line("{0 |} ⧺ canon(ones)")
        .expect_err("non-cons non-nil right-spine node stays improper");
    assert_eq!(improper.kind, OghamErrorKind::Improper);
    assert!(improper.message.contains("neither cons nor nil"));

    let invalid_definition = session
        .eval_line("bad := u ↦ [u] ⧺ coef(u, 0)")
        .expect_err("lazy operands still receive definition-time world validation");
    assert_eq!(invalid_definition.kind, OghamErrorKind::WrongWorld);

    session
        .eval_line("l =: ones ⧺ {5 | l}")
        .expect("cyclic-left reduction discards the recursive right operand");
    let degenerates = session
        .eval_line("l ≡ ones")
        .expect("discarded self-reference degenerates to ordinary binding");
    assert_eq!(degenerates.value.as_deref(), Some("true"));
}
