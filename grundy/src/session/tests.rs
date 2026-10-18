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

#[test]
fn evidence_pipeline() {
    let out = run(&[
        "over =: {0 | over}",
        "c := certify(over)",
        "check := (c : Claim)",
        "grundy_game := impartial(n ↦ [[a, n - a] for a in 1..n if 2⋅a < n])",
        "s := certify_sg(grundy_game, 9)",
        "kayles := octal([7, 7])",
        "[sg(kayles, n) for n in 0..12]",
        "p := periodic(kayles, 71, 12)",
        "periodic(kayles, 70, 12)",
        "good := verify(sg_witness(grundy_game, 3, [(3, 1, 1), (2, 0, 0), (1, 0, 0)]))",
        "bad := verify(sg_witness(grundy_game, 3, [(3, 0, 1), (2, 0, 0), (1, 0, 0)]))",
    ]);
    for (index, line) in out.iter().enumerate() {
        assert!(
            !line.starts_with("E_Domain: internal"),
            "line {index}: {line}"
        );
    }
    assert_eq!(out[6], "[0, 1, 2, 3, 1, 4, 3, 2, 1, 4, 2, 6]");
    assert!(out[8].starts_with("E_Refuted"), "{}", out[8]);
    assert_eq!(out[9], "");
    assert!(out[10].starts_with("E_Refuted"), "{}", out[10]);
}

#[test]
fn misere_instruments() {
    let out = run(&[
        "nim := impartial(n ↦ [[k] for k in 0..n])",
        "misere(nim, [1])",
        "misere(nim, [1, 1])",
        "q := sampled(misere_quotient(nim, [1], 3, 3))",
        "len(classes(q))",
        "p_classes(q)",
        "if misere_equal(nim, [], [1, 1], sums([1], 3)) then 1 else 0",
        "sampled(misere_equal(nim, [], [1, 1], sums([1], 3)))",
        "match separate(nim, [1], [], sums([1], 2)) { None ↦ false, Some(_) ↦ true }",
        "samples(misere_equal(nim, [], [1, 1], sums([1], 3)))",
    ]);
    assert_eq!(out[1], "(Right, Left)");
    assert_eq!(out[2], "(Left, Right)");
    assert_eq!(out[4], "2");
    assert_eq!(out[5], "[1]");
    assert!(out[6].starts_with("E_Type"), "{}", out[6]);
    assert_eq!(out[7], "true");
    assert_eq!(out[8], "true");
    assert_eq!(out[9], "4");
}

#[test]
fn algebra_worlds() {
    let out = run(&[
        "p := (t↑2 + 1 : F5[t])",
        "p",
        "p(2)",
        "deg(p)",
        "gcd(p, (t↑4 - 1 : F5[t]))",
        "(1/t : F2(t))",
        "integral(1/t : F2(t))",
        "(x↑2 : F9)",
        "frob(x : F9)",
        "alg := clifford([*1, *1])",
        "[e0, e1] := basis(alg)",
        "e0 ⋅ e0",
        "e0 ∧ e1",
        "(e0 + e1) ⋅ (e0 + e1)",
        "vector(alg, [*1, *2]) ∧ vector(alg, [*1, *3])",
        "other := clifford([*1])",
        "[f0] := basis(other)",
        "e0 + f0",
        "rev(e0 ∧ e1)",
        "tr(x : F4)",
        "nimtr(*7, 4)",
        "ω↑(1/2)",
        "(*ω : Ordinal) ⋅ (*ω : Ordinal)",
    ]);
    assert_eq!(out[1], "t↑2 + 1 : F5[t]");
    assert_eq!(out[2], "0 : F5");
    assert_eq!(out[3], "2");
    assert!(out[4].ends_with(": F5[t]"), "{}", out[4]);
    assert_eq!(out[6], "false");
    assert_eq!(
        out[11],
        "(alg := clifford([*1, *1]); [e0, e1] := basis(alg); *1 + (e0 - e0))"
    );
    assert_eq!(
        out[12],
        "(alg := clifford([*1, *1]); [e0, e1] := basis(alg); e0∧e1)"
    );
    assert!(out[17].starts_with("E_AlgebraMismatch"), "{}", out[17]);
    for (index, line) in out.iter().enumerate() {
        assert!(!line.contains("internal"), "line {index}: {line}");
    }
}

/// The display law: re-evaluating a value's display in a fresh session
/// reproduces the display.
fn display_round_trip(setup: &[&str], expr: &str) {
    let mut lines: Vec<&str> = setup.to_vec();
    lines.push(expr);
    let shown = run(&lines).pop().unwrap();
    assert!(!shown.starts_with("E_"), "`{expr}` failed: {shown}");
    let again = last(&[shown.as_str()]);
    let bare_root = shown
        .split_once(" =: ")
        .map(|(root, _)| root.to_string())
        .filter(|root| root.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'));
    let reshown = if let Some(root) = bare_root {
        // A bare equation statement displays nothing; show its root.
        run(&[shown.as_str(), root.as_str()]).pop().unwrap()
    } else {
        again
    };
    assert_eq!(reshown, shown, "display of `{expr}` is not a fixed point");
}

#[test]
fn display_law_round_trips() {
    display_round_trip(&[], "3 + 4");
    display_round_trip(&[], "*3 ⋅ *5");
    display_round_trip(&[], "{0 | 1} + *1");
    display_round_trip(&[], "[(1, true), (2, false)]");
    display_round_trip(&[], "(t↑3 - t : F7[t])");
    display_round_trip(&[], "(x + 1 : F27)");
    display_round_trip(&["k := 3"], "x ↦ x + k");
    display_round_trip(
        &["fact =: n ↦ if n = 0 then 1 else n ⋅ fact(n - 1)"],
        "fact",
    );
    display_round_trip(&["on =: {on |}"], "on");
    display_round_trip(&["a =: {b |}; b =: {| a}"], "a");
    display_round_trip(&["on =: {on |}"], "[on, on]");
    display_round_trip(
        &["alg := clifford([1, 2])", "[e0, e1] := basis(alg)"],
        "3⋅e0∧e1 + e1",
    );
    display_round_trip(&[], "impartial(n ↦ [[k] for k in 0..n])");
    display_round_trip(&["over =: {0 | over}"], "certify(over)");
    display_round_trip(
        &["nim := impartial(n ↦ [[k] for k in 0..n])"],
        "misere_quotient(nim, [1], 2, 2)",
    );
    display_round_trip(
        &["g := impartial(n ↦ [[a, n - a] for a in 1..n if 2⋅a < n])"],
        "certify_sg(g, 6)",
    );
    display_round_trip(&[], "periodic(octal([7, 7]), 71, 12)");
}
