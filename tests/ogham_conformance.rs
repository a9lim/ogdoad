use ogdoad::ogham::{
    parse_statement, unparse_statement, EvalLine, OghamError, OghamErrorKind, OghamSession,
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
fn ogham_v0_3_archive_syntax_and_echoes() {
    let lines = include_str!("../docs/ogham/conformance_v0.3.txt")
        .lines()
        .collect::<Vec<_>>();
    let mut idx = 0usize;
    while idx < lines.len() {
        let line_no = idx + 1;
        let line = lines[idx].trim();
        idx += 1;
        let Some(input) = line.strip_prefix("> ") else {
            continue;
        };
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
        let parsed = parse_statement(&input)
            .unwrap_or_else(|err| panic!("line {line_no}: syntax failed for `{input}`: {err}"));
        let canonical = unparse_statement(&parsed);
        let expected = lines[idx..]
            .iter()
            .map(|line| line.trim())
            .find(|line| !line.is_empty() && !line.starts_with('#'));
        if let Some(expected) = expected.and_then(|line| line.strip_prefix("~ ")) {
            assert_eq!(
                canonical, expected,
                "line {line_no}: canonical echo for `{input}`"
            );
        }
    }
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
        if line.is_empty() || line.starts_with('#') {
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
            .eval_line(&format!("len@{{{items}}}"))
            .unwrap_or_else(|err| panic!("length-{length} list fold failed: {err}"));
        let expected = length.to_string();
        assert_eq!(result.value.as_deref(), Some(expected.as_str()));
    }
}

#[test]
fn flat_list_sugar_depth_errors_before_recursive_ast_consumers() {
    let mut session = OghamSession::new("game").expect("game world");
    let items = (0_u128..2000)
        .map(|value| value.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let err = session
        .eval_line(&format!("{{{items}}}"))
        .expect_err("deep list sugar must stop before recursive AST consumers");
    assert_eq!(err.kind, OghamErrorKind::Parse);
    assert!(err.message.contains("syntax tree"));
    assert!(err.message.contains("1536 nodes"));
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
fn ogham_game_stage_d_boundaries() {
    let mut session = OghamSession::new("game").expect("game world");
    let ordered = session
        .eval_line("{0, 1 |} ≡ {1, 0 |}")
        .expect("ordered structural comparison");
    assert_eq!(ordered.value.as_deref(), Some("false"));

    let factorial = session.eval_line("!5").expect("integer-game factorial");
    assert_eq!(factorial.value.as_deref(), Some("120"));

    session
        .eval_line("loop =: {loop |}")
        .expect("guarded loopy Element fixpoint");
    let loop_value = session.eval_line("loop").expect("display loopy value");
    assert_eq!(loop_value.value.as_deref(), Some("loop =: {loop |}"));
}

#[test]
fn ogham_coinductive_append_walk_outcomes_and_fixpoint_reduction() {
    let mut session = OghamSession::new("game").expect("game world");
    session
        .eval_line("ones =: {1 | ones}")
        .expect("constant stream");

    let graft = session
        .eval_line("{1, 2} ⧺ {3}")
        .expect("finite spine reaches nil");
    assert_eq!(graft.value.as_deref(), Some("{1 | {2 | {3 | 0}}}"));

    let cycle = session
        .eval_line("ones ⧺ {5 | 0}")
        .expect("cyclic spine is the append result");
    assert_eq!(cycle.value.as_deref(), Some("ones =: {1 | ones}"));

    let prefixed_cycle = session
        .eval_line("({9} ⧺ ones) ⧺ {5 | 0}")
        .expect("finite prefix into a cycle is unchanged");
    assert_eq!(
        prefixed_cycle.value.as_deref(),
        Some("(ones =: {1 | ones}; {9 | ones})")
    );

    let improper = session
        .eval_line("{0 |} ⧺ {5 | 0}")
        .expect_err("non-cons non-nil right-spine node stays improper");
    assert_eq!(improper.kind, OghamErrorKind::Improper);
    assert!(improper.message.contains("neither cons nor nil"));

    session
        .eval_line("l =: ones ⧺ {5 | l}")
        .expect("cyclic-left reduction discards the recursive right operand");
    let degenerates = session
        .eval_line("l ≡ ones")
        .expect("discarded self-reference degenerates to ordinary binding");
    assert_eq!(degenerates.value.as_deref(), Some("true"));
}
