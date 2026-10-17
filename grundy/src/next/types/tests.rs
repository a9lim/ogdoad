use super::infer::{Checker, Globals};
use super::*;
use crate::next::syntax::ast::Stmt;
use crate::next::syntax::parse::parse_statement;

struct Session {
    ts: TypeState,
    data: DataRegistry,
    globals: Globals,
}

impl Session {
    fn new() -> Self {
        Session {
            ts: TypeState::default(),
            data: DataRegistry::default(),
            globals: Globals::default(),
        }
    }

    /// Check a statement; return the final expression's type or the last
    /// binding's scheme.
    fn check(&mut self, src: &str) -> Result<String, String> {
        let Stmt::Seq(bindings, expr) = parse_statement(src).map_err(|e| e.to_string())? else {
            panic!("data declarations are handled by the session");
        };
        let mut checker = Checker::new(&mut self.ts, &self.data, &self.globals);
        let checked = checker
            .check_seq(&bindings, expr.as_ref())
            .map_err(|e| e.to_string())?;
        let mut last = None;
        for (name, scheme) in checked.defined {
            last = Some(show_scheme(&scheme, &self.data));
            self.globals.values.insert(name, scheme);
        }
        Ok(match checked.ty {
            Some(ty) => show_ty(&ty, &self.data, &mut VarNames::default()),
            None => last.unwrap_or_default(),
        })
    }
}

fn ty(src: &str) -> String {
    Session::new()
        .check(src)
        .unwrap_or_else(|e| panic!("`{src}`: {e}"))
}

fn ty_err(src: &str) -> String {
    match Session::new().check(src) {
        Ok(ty) => panic!("`{src}` checked as {ty}"),
        Err(e) => e,
    }
}

#[test]
fn literal_defaulting() {
    assert_eq!(ty("3 + 4"), "Int");
    assert_eq!(ty("*3 ⋅ *5"), "Nimber");
    assert_eq!(ty("*3 + *5"), "Game");
    assert_eq!(ty("3 + *1"), "Game");
    assert_eq!(ty("1/2"), "Game");
    assert_eq!(ty("1/2 : Surreal"), "Surreal");
    assert_eq!(ty("ω + 1"), "Surreal");
    assert_eq!(ty("ω↑(1/2)"), "Surreal");
    assert_eq!(ty("2↑10"), "Int");
    assert_eq!(ty("{0 | 1}"), "Game");
    assert_eq!(ty("up + *1"), "Game");
    assert_eq!(ty("/(*2)"), "Nimber");
    assert_eq!(ty("[1, 2]"), "List(Int)");
    assert_eq!(ty("[]"), "List(a)");
    assert_eq!(ty("(1, true)"), "(Int, Bool)");
    assert!(ty_err("3 : Nimber").contains("no integer literals"));
    assert!(ty_err("{0 | 1} ⋅ 2").contains("additive group"));
}

#[test]
fn generalization_follows_bindings() {
    let mut s = Session::new();
    assert_eq!(
        s.check("succ := x ↦ x + 1").unwrap(),
        "Add a, IntLit a ⇒ a → a"
    );
    assert_eq!(s.check("succ(3)").unwrap(), "Int");
    assert_eq!(s.check("succ({0 |})").unwrap(), "Game");
    assert_eq!(s.check("three := 3").unwrap(), "Int");
    assert!(s
        .check("three + *1")
        .unwrap_err()
        .contains("no star literals"));
    assert_eq!(s.check("xs := []").unwrap(), "List(a)");
    assert_eq!(s.check("xs ⧺ [1]").unwrap(), "List(Int)");
    assert_eq!(s.check("xs ⧺ [true]").unwrap(), "List(Bool)");
    assert_eq!(s.check("id := x ↦ x").unwrap(), "a → a");
    assert_eq!(s.check("(id(1), id(true))").unwrap(), "(Int, Bool)");
}

#[test]
fn recursion_by_inferred_type() {
    let mut s = Session::new();
    assert_eq!(
        s.check("fact =: n ↦ if n = 0 then 1 else n ⋅ fact(n - 1)")
            .unwrap(),
        "Add a, Eq a, IntLit a, Mul a ⇒ a → a"
    );
    assert_eq!(s.check("on =: {on |}").unwrap(), "Form");
    assert_eq!(s.check("a =: {b |}; b =: {| a}").unwrap(), "Form");
    assert_eq!(
        s.check("ev =: n ↦ if n = 0 then true else od(n - 1); od =: n ↦ if n = 0 then false else ev(n - 1)")
            .unwrap(),
        "Add a, Eq a, IntLit a ⇒ a → Bool"
    );
    assert!(s.check("b =: not b").unwrap_err().contains("E_Fixpoint"));
    assert_eq!(
        s.check("neg2 =: x ↦ if x = 0 then 0 else -neg2(x - 1)")
            .unwrap(),
        "Add a, Add b, Eq a, IntLit a, IntLit b ⇒ a → b"
    );
    // The result's literal is not tied to the argument: it defaults alone.
    assert_eq!(s.check("neg2({0 |})").unwrap(), "Int");
    assert_eq!(s.check("neg2({0 |}) : Game").unwrap(), "Game");
}

#[test]
fn rulesets_type() {
    let mut s = Session::new();
    assert_eq!(
        s.check("grundy_game := impartial(n ↦ [[a, n - a] for a in 1..n if 2 ⋅ a < n])")
            .unwrap(),
        "Rules(Int)"
    );
    assert_eq!(s.check("sg(grundy_game, 7)").unwrap(), "Int");
    assert_eq!(s.check("value(grundy_game, 7)").unwrap(), "Game");
    assert_eq!(
        s.check("[sg(grundy_game, n) for n in 0..20]").unwrap(),
        "List(Int)"
    );
    assert!(s.check("sg(grundy_game, true)").is_err());
}

#[test]
fn annotations_bind_generators() {
    assert_eq!(ty("t↑2 + 1 : F5[t]"), "F5[t]");
    assert_eq!(ty("(p := (t↑2 + 1 : F5[t]); p(2))"), "F5");
    assert_eq!(ty("x + 1 : F9"), "F9");
    assert_eq!(ty("1/t : F2(t)"), "F2(t)");
    assert!(ty_err("t + 1").contains("E_Unbound"));
}

#[test]
fn relations_and_errors() {
    assert_eq!(ty("{0 | 1} >‿ 0"), "Bool");
    assert_eq!(ty("3 < 4"), "Bool");
    assert!(ty_err("(3 : F5) < 4").contains("no order"));
    assert!(ty_err("1 + true").contains("E_Type"));
    assert!(ty_err("(x ↦ x)(1, 2)").contains("E_Arity"));
    assert_eq!(ty("3 ≡ 3"), "Bool");
    assert!(ty_err("(3 : Int) ≡ 3").contains("E_Type"));
}
