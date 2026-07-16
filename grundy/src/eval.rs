use super::ast::{
    BinaryOp, Binding, DataSort, Expr, LambdaBinder, OutcomeCell, RelOp, StarLiteral, Statement,
    UnaryOp,
};
use super::error::*;
use super::lex::{needs_continuation, strip_comments};
use super::parse::parse_statement;
use super::unparse::unparse_statement;
use ogdoad::clifford::{CliffordAlgebra, Metric, Multivector};
use ogdoad::games::{
    Game, LoopyMover, LoopyPartizanGraph, LoopyPartizanGraphError, LoopyPartizanOutcome,
    LoopyStopperStatus, LoopyWinner,
};
use ogdoad::scalar::{
    nim_trace, ExactFieldScalar, FiniteField, Fp, Fpn, HasRingOfIntegers, Integer,
    IntegerDivExactError, Nimber, Omnific, Ordinal, Poly, Rational, RationalFunction, Scalar,
    Surreal,
};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::Display;
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::sync::{mpsc, Arc};
use std::thread::JoinHandle;

const DEFAULT_FUEL: u128 = 1 << 16;
const DEFAULT_GRAPH_BUDGET: u128 = 1 << 16;
const RECURSION_DEPTH_GUARD: u128 = 1 << 10;
const AST_DEPTH_GUARD: u128 = 3 << 9;
const EVAL_STACK_BYTES: usize = 64 * 1024 * 1024;

#[path = "runtime/mod.rs"]
mod runtime;
#[path = "session.rs"]
mod session;
#[path = "worlds/mod.rs"]
mod worlds;

pub(crate) use runtime::*;
pub(crate) use session::*;
pub use session::{eval_to_string, EvalLine, GrundySession};
pub(crate) use worlds::*;

/// The language release implemented by this evaluator.
pub const GRUNDY_VERSION: &str = "0.3.6";

/// Compact grouping of every fixed-dispatch grundy world.
pub const WORLD_MENU: &str = concat!(
    "worlds:\n",
    "  scalar   nimber ordinal surreal omnific integer\n",
    "  finite   fp2 fp3 fp5 fp7 f4 f8 f16 f9 f27 f25\n",
    "  poly     integer[t] fp2[t] fp3[t] fp5[t] fp7[t]\n",
    "  fraction fp2(t) fp3(t) fp5(t) fp7(t)\n",
    "  game     game",
);

const WORLD_NAMES: [&str; 34] = [
    "nimber",
    "ordinal",
    "surreal",
    "omnific",
    "integer",
    "fp2",
    "fp3",
    "fp5",
    "fp7",
    "f4",
    "f8",
    "f16",
    "f9",
    "f27",
    "f25",
    "integer[t]",
    "fp2[t]",
    "fp3[t]",
    "fp5[t]",
    "fp7[t]",
    "fp2(t)",
    "fp3(t)",
    "fp5(t)",
    "fp7(t)",
    "polyint",
    "poly2",
    "poly3",
    "poly5",
    "poly7",
    "ratfunc2",
    "ratfunc3",
    "ratfunc5",
    "ratfunc7",
    "game",
];

enum World {
    Game(GameRuntime),
    Nimber(CliffordRuntime<Nimber>),
    Ordinal(CliffordRuntime<Ordinal>),
    Surreal(CliffordRuntime<Surreal>),
    Omnific(CliffordRuntime<Omnific>),
    Integer(CliffordRuntime<Integer>),
    Fp2(CliffordRuntime<Fp<2>>),
    Fp3(CliffordRuntime<Fp<3>>),
    Fp5(CliffordRuntime<Fp<5>>),
    Fp7(CliffordRuntime<Fp<7>>),
    F4(CliffordRuntime<Fpn<2, 2>>),
    F8(CliffordRuntime<Fpn<2, 3>>),
    F16(CliffordRuntime<Fpn<2, 4>>),
    F9(CliffordRuntime<Fpn<3, 2>>),
    F27(CliffordRuntime<Fpn<3, 3>>),
    F25(CliffordRuntime<Fpn<5, 2>>),
    PolyInt(PolyRuntime<Integer>),
    Poly2(PolyRuntime<Fp<2>>),
    Poly3(PolyRuntime<Fp<3>>),
    Poly5(PolyRuntime<Fp<5>>),
    Poly7(PolyRuntime<Fp<7>>),
    RatFunc2(RatFuncRuntime<Fp<2>>),
    RatFunc3(RatFuncRuntime<Fp<3>>),
    RatFunc5(RatFuncRuntime<Fp<5>>),
    RatFunc7(RatFuncRuntime<Fp<7>>),
}

macro_rules! with_world_runtime {
    ($world:expr, |$runtime:ident| $body:expr) => {
        match $world {
            World::Game($runtime) => $body,
            World::Nimber($runtime) => $body,
            World::Ordinal($runtime) => $body,
            World::Surreal($runtime) => $body,
            World::Omnific($runtime) => $body,
            World::Integer($runtime) => $body,
            World::Fp2($runtime) => $body,
            World::Fp3($runtime) => $body,
            World::Fp5($runtime) => $body,
            World::Fp7($runtime) => $body,
            World::F4($runtime) => $body,
            World::F8($runtime) => $body,
            World::F16($runtime) => $body,
            World::F9($runtime) => $body,
            World::F27($runtime) => $body,
            World::F25($runtime) => $body,
            World::PolyInt($runtime) => $body,
            World::Poly2($runtime) => $body,
            World::Poly3($runtime) => $body,
            World::Poly5($runtime) => $body,
            World::Poly7($runtime) => $body,
            World::RatFunc2($runtime) => $body,
            World::RatFunc3($runtime) => $body,
            World::RatFunc5($runtime) => $body,
            World::RatFunc7($runtime) => $body,
        }
    };
}

impl World {
    fn from_decl(decl: &str) -> GrundyResult<Self> {
        ensure_source_nesting_depth(decl)?;
        let decl = strip_comments(decl)?;
        let decl = decl.trim().strip_prefix(":world ").unwrap_or(decl.trim());
        let mut parts = decl.split_whitespace();
        let name = parts
            .next()
            .ok_or_else(|| parse_error("missing world name"))?;
        let tail: Vec<&str> = parts.collect();
        if !WORLD_NAMES.contains(&name) {
            return Err(unknown_world_error(name));
        }
        macro_rules! build_poly {
            ($variant:ident, $ty:ty, $label:expr) => {{
                ensure_function_world_decl($label, &tail)?;
                return Ok(World::$variant(PolyRuntime::<$ty>::new($label)));
            }};
        }
        macro_rules! build_ratfunc {
            ($variant:ident, $ty:ty, $label:expr) => {{
                ensure_function_world_decl($label, &tail)?;
                return Ok(World::$variant(RatFuncRuntime::<$ty>::new($label)));
            }};
        }
        match name {
            "game" => {
                ensure_function_world_decl(name, &tail)?;
                return Ok(World::Game(GameRuntime::new()));
            }
            "integer[t]" | "polyint" => build_poly!(PolyInt, Integer, "integer[t]"),
            "fp2[t]" | "poly2" => build_poly!(Poly2, Fp<2>, "fp2[t]"),
            "fp3[t]" | "poly3" => build_poly!(Poly3, Fp<3>, "fp3[t]"),
            "fp5[t]" | "poly5" => build_poly!(Poly5, Fp<5>, "fp5[t]"),
            "fp7[t]" | "poly7" => build_poly!(Poly7, Fp<7>, "fp7[t]"),
            "fp2(t)" | "ratfunc2" => build_ratfunc!(RatFunc2, Fp<2>, "fp2(t)"),
            "fp3(t)" | "ratfunc3" => build_ratfunc!(RatFunc3, Fp<3>, "fp3(t)"),
            "fp5(t)" | "ratfunc5" => build_ratfunc!(RatFunc5, Fp<5>, "fp5(t)"),
            "fp7(t)" | "ratfunc7" => build_ratfunc!(RatFunc7, Fp<7>, "fp7(t)"),
            _ => {}
        }
        if name == "nimber" && tail.first().is_some_and(|part| part.starts_with("gold(")) {
            let second = tail[0];
            let metric = parse_gold_metric(second)?;
            return Ok(World::Nimber(CliffordRuntime::from_metric(
                "nimber", metric,
            )));
        }
        let (dim, rest) = if let Some(second) = tail.first().copied() {
            let dim = second
                .parse::<usize>()
                .map_err(|_| parse_error("world dimension must be a usize"))?;
            (
                dim,
                decl.split_once(second).map_or("", |(_, tail)| tail).trim(),
            )
        } else {
            (0, "")
        };
        macro_rules! build {
            ($variant:ident, $ty:ty, $label:expr) => {
                Ok(World::$variant(build_runtime::<$ty>($label, dim, rest)?))
            };
        }
        match name {
            "nimber" => build!(Nimber, Nimber, "nimber"),
            "ordinal" => build!(Ordinal, Ordinal, "ordinal"),
            "surreal" => build!(Surreal, Surreal, "surreal"),
            "omnific" => build!(Omnific, Omnific, "omnific"),
            "integer" => build!(Integer, Integer, "integer"),
            "fp2" => build!(Fp2, Fp<2>, "fp2"),
            "fp3" => build!(Fp3, Fp<3>, "fp3"),
            "fp5" => build!(Fp5, Fp<5>, "fp5"),
            "fp7" => build!(Fp7, Fp<7>, "fp7"),
            "f4" => build!(F4, Fpn<2, 2>, "f4"),
            "f8" => build!(F8, Fpn<2, 3>, "f8"),
            "f16" => build!(F16, Fpn<2, 4>, "f16"),
            "f9" => build!(F9, Fpn<3, 2>, "f9"),
            "f27" => build!(F27, Fpn<3, 3>, "f27"),
            "f25" => build!(F25, Fpn<5, 2>, "f25"),
            _ => unreachable!("world name was checked against the fixed menu"),
        }
    }

    fn eval_statement(&mut self, stmt: &Statement) -> GrundyResult<Option<String>> {
        with_world_runtime!(self, |runtime| runtime.eval_statement(stmt))
    }

    fn reset_fuel(&mut self) {
        with_world_runtime!(self, |runtime| runtime.reset_fuel())
    }

    fn set_fuel_budget(&mut self, budget: u128) {
        with_world_runtime!(self, |runtime| runtime.set_fuel_budget(budget))
    }

    fn fuel_budget(&self) -> u128 {
        with_world_runtime!(self, |runtime| runtime.fuel_budget())
    }

    fn set_graph_budget(&mut self, budget: u128) {
        with_world_runtime!(self, |runtime| runtime.set_graph_budget(budget))
    }

    fn graph_budget(&self) -> u128 {
        with_world_runtime!(self, |runtime| runtime.graph_budget())
    }

    fn summary(&self) -> String {
        with_world_runtime!(self, |runtime| runtime.summary())
    }

    fn env_summary(&self) -> Vec<String> {
        with_world_runtime!(self, |runtime| runtime.env_summary())
    }
}

fn unknown_world_error(name: &str) -> GrundyError {
    let nearest = WORLD_NAMES
        .iter()
        .map(|candidate| (*candidate, edit_distance(name, candidate)))
        .min_by_key(|(_, distance)| *distance)
        .filter(|(_, distance)| *distance <= 2)
        .map(|(candidate, _)| canonical_world_name(candidate));
    let hint = match nearest {
        Some(candidate) => format!("{WORLD_MENU}\ndid you mean `{candidate}`?"),
        None => WORLD_MENU.to_string(),
    };
    GrundyError::new(
        GrundyErrorKind::WrongWorld,
        Span::point(0),
        format!("unknown world `{name}`"),
    )
    .with_hint(hint)
}

fn canonical_world_name(name: &str) -> &'static str {
    match name {
        "polyint" | "integer[t]" => "integer[t]",
        "poly2" | "fp2[t]" => "fp2[t]",
        "poly3" | "fp3[t]" => "fp3[t]",
        "poly5" | "fp5[t]" => "fp5[t]",
        "poly7" | "fp7[t]" => "fp7[t]",
        "ratfunc2" | "fp2(t)" => "fp2(t)",
        "ratfunc3" | "fp3(t)" => "fp3(t)",
        "ratfunc5" | "fp5(t)" => "fp5(t)",
        "ratfunc7" | "fp7(t)" => "fp7(t)",
        "nimber" => "nimber",
        "ordinal" => "ordinal",
        "surreal" => "surreal",
        "omnific" => "omnific",
        "integer" => "integer",
        "fp2" => "fp2",
        "fp3" => "fp3",
        "fp5" => "fp5",
        "fp7" => "fp7",
        "f4" => "f4",
        "f8" => "f8",
        "f16" => "f16",
        "f9" => "f9",
        "f27" => "f27",
        "f25" => "f25",
        "game" => "game",
        _ => unreachable!("canonicalized name comes from WORLD_NAMES"),
    }
}

fn edit_distance(lhs: &str, rhs: &str) -> usize {
    let mut previous: Vec<usize> = (0..=rhs.chars().count()).collect();
    let mut current = vec![0; previous.len()];
    for (lhs_index, lhs_char) in lhs.chars().enumerate() {
        current[0] = lhs_index + 1;
        for (rhs_index, rhs_char) in rhs.chars().enumerate() {
            let deletion = previous[rhs_index + 1] + 1;
            let insertion = current[rhs_index] + 1;
            let substitution = previous[rhs_index] + usize::from(lhs_char != rhs_char);
            current[rhs_index + 1] = deletion.min(insertion).min(substitution);
        }
        std::mem::swap(&mut previous, &mut current);
    }
    previous[rhs.chars().count()]
}

fn ensure_function_world_decl(name: &str, tail: &[&str]) -> GrundyResult<()> {
    if tail.is_empty() || tail == ["0"] {
        Ok(())
    } else {
        Err(parse_error(format!(
            "`{name}` is a function-shaped scalar world; it takes no metric declaration"
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multiset_walk_matches_the_engine_structural_fingerprint() {
        let zero = Game::integer(0);
        let one = Game::integer(1);
        let star = Game::nim_heap(1);
        let up = Game::up();
        let reordered_a = Game::new(
            vec![zero.clone(), one.clone()],
            vec![star.clone(), zero.clone()],
        );
        let reordered_b = Game::new(
            vec![one.clone(), zero.clone()],
            vec![zero.clone(), star.clone()],
        );
        let duplicate = Game::new(vec![zero.clone(), zero.clone()], Vec::new());
        let singleton = Game::new(vec![zero.clone()], Vec::new());
        let games = [
            zero,
            one,
            star,
            up.clone(),
            up.neg(),
            reordered_a,
            reordered_b,
            duplicate,
            singleton,
        ];

        for lhs in &games {
            for rhs in &games {
                assert_eq!(
                    game_structural_eq_multiset(lhs, rhs),
                    lhs.structural_eq(rhs),
                    "language walk diverged from engine fingerprint on {lhs} and {rhs}"
                );
            }
        }
    }

    #[test]
    fn stopper_projection_table_covers_all_nine_cells() {
        use LoopyWinner::{Draw, Left, Right};

        for (outcome, expected) in [
            (LoopyPartizanOutcome::new(Left, Left), RelOp::Gt),
            (LoopyPartizanOutcome::new(Left, Draw), RelOp::Gt),
            (LoopyPartizanOutcome::new(Left, Right), RelOp::Fuzzy),
            (LoopyPartizanOutcome::new(Draw, Left), RelOp::Eq),
            (LoopyPartizanOutcome::new(Draw, Draw), RelOp::Eq),
            (LoopyPartizanOutcome::new(Draw, Right), RelOp::Lt),
            (LoopyPartizanOutcome::new(Right, Left), RelOp::Eq),
            (LoopyPartizanOutcome::new(Right, Draw), RelOp::Eq),
            (LoopyPartizanOutcome::new(Right, Right), RelOp::Lt),
        ] {
            assert_eq!(project_stopper_outcome(outcome), expected);
        }
    }
}
