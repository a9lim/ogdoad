use super::*;

/// Run a program on a large stack and collect each statement's display (or
/// error code and message).
fn run(lines: &[&str]) -> Vec<String> {
    let lines: Vec<String> = lines.iter().map(|s| s.to_string()).collect();
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || {
            let mut session = Session::new();
            lines
                .iter()
                .map(|line| match session.eval(line) {
                    Ok(out) => out.value.unwrap_or_default(),
                    Err(e) => format!("{}: {}", e.kind.code(), e.message),
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("join")
}

fn last(lines: &[&str]) -> String {
    run(lines).pop().unwrap_or_default()
}

#[test]
fn arithmetic_and_defaulting() {
    assert_eq!(last(&["3 + 4"]), "7");
    assert_eq!(last(&["*3 ⋅ *5"]), "*15 : Nimber");
    assert_eq!(last(&["*3 + *5"]), "*6");
    assert_eq!(last(&["3 + *1"]), "{3 | 3}");
    assert_eq!(last(&["1/2 + 1/2"]), "1 : Game");
    assert_eq!(last(&["3 - 1 : Game"]), "2 : Game");
    assert_eq!(last(&["{0 | 1}"]), "1/2");
    assert_eq!(last(&["up + up"]), "{0 | {0, *1 | 0}}");
    assert_eq!(last(&["2↑10"]), "1024");
    assert_eq!(last(&["[k⋅k for k in 0..5]"]), "[0, 1, 4, 9, 16]");
    assert_eq!(last(&["ω + 1"]), "ω + 1");
}

#[test]
fn functions_and_recursion() {
    assert_eq!(
        last(&[
            "fact =: n ↦ if n = 0 then 1 else n ⋅ fact(n - 1)",
            "fact(20)"
        ]),
        "2432902008176640000"
    );
    assert_eq!(
        last(&["succ := x ↦ x + 1", "(succ(3), succ({0 |}))"]),
        "(4, 2) : (Int, Game)"
    );
    assert_eq!(
        last(&[
            "ev =: n ↦ if n = 0 then true else od(n - 1); od =: n ↦ if n = 0 then false else ev(n - 1)",
            "(ev(10), od(7))"
        ]),
        "(true, true)"
    );
    assert_eq!(
        last(&["loop =: n ↦ loop(n + 1)", "loop(0)"])
            .split(':')
            .next(),
        Some("E_StackDepth")
    );
    assert_eq!(
        last(&["spin =: n ↦ if n = 0 then 0 else spin(n)", "spin(1)"])
            .split(':')
            .next(),
        Some("E_StackDepth")
    );
}

#[test]
fn grundys_game() {
    let out = run(&[
        "grundy_game := impartial(n ↦ [[a, n - a] for a in 1..n if 2⋅a < n])",
        "[sg(grundy_game, n) for n in 0..20]",
        "value(grundy_game, 7)",
        "winning(grundy_game, [7, 5, 4], Left)",
    ]);
    // Grundy's game: 0 0 0 1 0 2 1 0 2 1 0 2 1 3 2 1 3 2 4 3 (OEIS A002188).
    assert_eq!(
        out[1],
        "[0, 0, 0, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 3, 2, 4, 3]"
    );
    assert_eq!(out[2], "0 : Game");
    assert!(out[3].starts_with('['), "{}", out[3]);
}

#[test]
fn partizan_and_loopy() {
    let out = run(&[
        "on =: {on |}",
        "on",
        "over =: {0 | over}",
        "over = over",
        "over ‿‿ over",
        "outcome(over)",
        "data Cell = Empty | Black",
        "hop := partizan(n ↦ if n > 0 then [[n - 1]] else [], n ↦ [[n + 1]])",
        "graph(hop, 0)",
    ]);
    assert_eq!(out[1], "on =: {on |}");
    assert_eq!(out[3], "true");
    assert_eq!(out[4], "true");
    assert_eq!(out[5], "(Left, Left)");
    assert!(out[8].starts_with("E_GraphBudget"), "{}", out[8]);
}

#[test]
fn cycles_are_reported() {
    let out = run(&[
        "bounce := impartial(n ↦ [[1 - n]])",
        "sg(bounce, 0)",
        "graph(bounce, 0)",
    ]);
    assert!(
        out[1].starts_with("E_Loopy: the component positions cycle: 0 → 1 → 0"),
        "{}",
        out[1]
    );
    assert!(out[2].contains("=:"), "{}", out[2]);
}
