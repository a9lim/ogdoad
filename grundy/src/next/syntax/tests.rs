use super::super::error::GrundyErrorKind;
use super::ast::{Stmt, Unspan};
use super::lex::needs_continuation;
use super::parse::parse_statement;
use super::unparse::unparse_stmt;

fn canonical(src: &str) -> String {
    let stmt = parse_statement(src).unwrap_or_else(|err| panic!("`{src}` failed: {err}"));
    unparse_stmt(&stmt)
}

fn unspanned(src: &str) -> Stmt {
    let mut stmt = parse_statement(src).unwrap_or_else(|err| panic!("`{src}` failed: {err}"));
    stmt.unspan();
    stmt
}

/// `parse ∘ unparse = id` on parser-produced trees, and the rendering is a
/// fixed point.
fn round_trip(src: &str) {
    let first = canonical(src);
    let second = canonical(&first);
    assert_eq!(
        first, second,
        "canonical rendering of `{src}` is not a fixed point"
    );
    assert_eq!(
        unspanned(src),
        unspanned(&first),
        "`{src}` and its rendering `{first}` parse differently"
    );
}

#[test]
fn canonical_spellings() {
    for (input, expected) in [
        ("1 + 2", "1 + 2"),
        ("*2 . *3", "*2⋅*3"),
        ("x ^ 2", "x↑2"),
        ("2 ^ -1", "2↑-1"),
        ("a & b", "a∧b"),
        ("a ! b", "a ∥ b"),
        ("a == b", "a = b"),
        ("a === b", "a ≡ b"),
        ("a <= b", "a ≤ b"),
        ("a >= b", "a ≥ b"),
        ("g >_ h", "g >‿ h"),
        ("g __ h", "g ‿‿ h"),
        ("xs ++ ys", "xs ⧺ ys"),
        ("x ~ x + 1", "x ↦ x + 1"),
        ("w", "ω"),
        ("*", "*1"),
        ("{0|}", "{0 |}"),
        ("{|0}", "{| 0}"),
        ("{|}", "{|}"),
        ("{1, 2 | 0}", "{1, 2 | 0}"),
        ("[k for k in 0 .. n]", "[k for k in 0..n]"),
        (
            "[a for a in 1..=n if 2 . a < n]",
            "[a for a in 1..=n if 2⋅a < n]",
        ),
        ("(a, b) ↦ a", "(a, b) ↦ a"),
        ("((a, b)) ↦ a", "((a, b)) ↦ a"),
        ("(n : Int) ↦ n", "(n : Int) ↦ n"),
        ("f := x ↦ x", "f := x ↦ x"),
        (
            "f =: n ↦ if n = 0 then 1 else n . f(n - 1)",
            "f =: n ↦ if n = 0 then 1 else n⋅f(n - 1)",
        ),
        ("(a := 1; b := 2; a + b)", "(a := 1; b := 2; a + b)"),
        ("a := 1; b := 2; a + b", "a := 1; b := 2; a + b"),
        (
            "data Cell = Empty | Toad | Frog",
            "data Cell = Empty | Toad | Frog",
        ),
        ("data T = Leaf | Node(T, T)", "data T = Leaf | Node(T, T)"),
        (
            "match c { Empty ↦ 0, Toad ↦ 1, _ ↦ 2 }",
            "match c { Empty ↦ 0, Toad ↦ 1, _ ↦ 2 }",
        ),
        ("[x, ..rest] := xs", "[x, ..rest] := xs"),
        ("{..ls, 0 | ..rs}", "{..ls, 0 | ..rs}"),
        ("p := t^2 + 1 : F5[t]", "p := t↑2 + 1 : F5[t]"),
        ("q := 1/t : F2(t)", "q := 1/t : F2(t)"),
        ("f : (Int, Int) -> Int", "f : (Int, Int) → Int"),
        (
            "g : (Int -> Int) -> List(Int)",
            "g : (Int → Int) → List(Int)",
        ),
        ("*(w + 1)", "*(ω + 1)"),
        ("*(w^2.3 + w + 4)", "*(ω↑2⋅3 + ω + 4)"),
        ("xs[0]", "xs[0]"),
        ("f(x)(y)", "f(x)(y)"),
        ("not a = b", "not a = b"),
        (
            "if a then b else if c then d else e",
            "if a then b else if c then d else e",
        ),
    ] {
        assert_eq!(canonical(input), expected, "canonical form of `{input}`");
        round_trip(input);
    }
}

#[test]
fn minimal_parentheses_round_trip() {
    for input in [
        "(a + b)⋅c",
        "a + b⋅c",
        "a - (b - c)",
        "(a - b) - c",
        "-(a↑2)",
        "(-a)↑2",
        "a↑b↑c",
        "(a↑b)↑c",
        "-(1/2)",
        "x⋅(1/2)",
        "1/2⋅x",
        "x - -1/2",
        "1/(2)",
        "(1)/2",
        "/(*2)",
        "x/(*2)",
        "x/(/y)",
        "/(/x)",
        "- -x",
        "(if a then b else c) + 1",
        "(if a then b else c) : Int",
        "(x ↦ x)(3)",
        "f((x ↦ x))",
        "(a = b) = c",
        "(a ⧺ b) ⧺ c",
        "a ⧺ b ⧺ c",
        "(0..3) ⧺ [4]",
        "[(if a then b else c) for x in xs]",
        "[(x ↦ x) for x in xs]",
        "match (a, b) { (0, _) ↦ 1, (_, y) ↦ y }",
        "{(x : Game) | 0}",
        "not (a and b)",
        "(not a) and b",
        "a or b and c",
        "(a or b) and c",
        "[[a, n - a] for a in 1..n if 2⋅a < n]",
        "-1/2",
        "*3⋅e0∧e1",
        "(a∧b)∧c",
        "a∧(b∧c)",
        "() ↦ 3",
        "(Toad) ↦ 1",
        "x := (y := 2; y)",
    ] {
        round_trip(input);
    }
}

#[test]
fn literal_shaped_fractions_only_without_parentheses() {
    use super::ast::ExprKind;
    let expr_kind = |src: &str| match unspanned(src) {
        Stmt::Seq(_, Some(expr)) => expr.kind,
        other => panic!("not an expression: {other:?}"),
    };
    assert_eq!(expr_kind("1/2"), ExprKind::Frac(1, 2));
    assert_eq!(expr_kind("-3/4"), ExprKind::Frac(-3, 4));
    assert_eq!(expr_kind("3/-4"), ExprKind::Frac(-3, 4));
    assert!(matches!(expr_kind("(1)/2"), ExprKind::Binary(..)));
    assert!(matches!(expr_kind("1/(2)"), ExprKind::Binary(..)));
    assert!(matches!(expr_kind("-(1)/2"), ExprKind::Binary(..)));
    assert!(matches!(expr_kind("1/2↑2"), ExprKind::Binary(..)));
}

#[test]
fn teaching_errors_carry_hints() {
    for (input, needle) in [
        ("a != b", "not (a = b)"),
        ("{a, b}", "`[a, b]` is the list"),
        ("a | b", "brace bar is structural"),
        ("a < b < c", "parenthesize the Bool"),
        ("2 * 3", "the product is `⋅`"),
        ("_", "come in pairs"),
        ("‿", "come in pairs"),
        ("1 + if a then b else c", "parenthesize it"),
        ("1; 2", "dead code"),
        ("if a then b", "`else` is mandatory"),
        ("up()", "without parentheses"),
        ("x : F5[s]", "named `t`"),
    ] {
        let err = parse_statement(input).expect_err(input);
        assert_eq!(err.kind, GrundyErrorKind::Parse, "`{input}`: {err}");
        let hint = err.hint.unwrap_or_default();
        assert!(
            hint.contains(needle),
            "`{input}` hint `{hint}` lacks `{needle}`"
        );
    }
}

/// Deep inputs need the evaluation worker's stack, not a test thread's.
fn on_big_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("join");
}

#[test]
fn structural_errors() {
    on_big_stack(structural_errors_body);
}

fn structural_errors_body() {
    assert_eq!(
        parse_statement("*(1 + w)").unwrap_err().kind,
        GrundyErrorKind::CnfOrder
    );
    assert_eq!(
        parse_statement("a ^^ b").unwrap_err().kind,
        GrundyErrorKind::Reserved
    );
    assert_eq!(
        parse_statement("O(3)").unwrap_err().kind,
        GrundyErrorKind::Reserved
    );
    let deep = format!("{}0{}", "(".repeat(2000), ")".repeat(2000));
    let err = parse_statement(&deep).unwrap_err();
    assert!(err.message.contains("1536"), "{err}");
    let long_chain = format!("{}x", "-".repeat(5000));
    assert_eq!(
        parse_statement(&long_chain).unwrap_err().kind,
        GrundyErrorKind::Parse
    );
    assert!(parse_statement("(a, b) =: x").is_err());
}

#[test]
fn continuation_follows_delimiters_and_trailing_operators() {
    for (src, expected) in [
        ("f := x ↦", true),
        ("(a", true),
        ("[1, 2,", true),
        ("x + ", true),
        ("if a then", true),
        ("/* open", true),
        ("x + 1", false),
        ("f(x)", false),
        ("a := 1;", true),
        ("data T = A |", true),
    ] {
        assert_eq!(needs_continuation(src).unwrap(), expected, "`{src}`");
    }
}

#[test]
fn comments_are_whitespace() {
    assert_eq!(canonical("1 + /* nested /* deep */ */ 2 // tail"), "1 + 2");
    assert!(parse_statement("1 /* open").is_err());
}
