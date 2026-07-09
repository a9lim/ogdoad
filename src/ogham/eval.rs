use super::ast::{BinaryOp, Binding, Expr, RelOp, Sort, StarLiteral, Statement, UnaryOp};
use super::error::{OghamError, OghamErrorKind, OghamResult, Span};
use super::lex::needs_continuation;
use super::parse::parse_statement;
use super::unparse::unparse_statement;
use crate::clifford::{CliffordAlgebra, Metric, Multivector};
use crate::games::{Game, LoopyPartizanGraph};
use crate::scalar::{
    checked_factorial_i128, factorial_in_scalar, nim_trace, ExactFieldScalar, FiniteField, Fp, Fpn,
    Integer, IntegerDivExactError, Nimber, Omnific, Ordinal, Poly, Rational, RationalFunction,
    Scalar, Surreal,
};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Display;
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::sync::Arc;

const DEFAULT_FUEL: u128 = 1 << 16;
const RECURSION_DEPTH_GUARD: u128 = 1 << 10;
const AST_DEPTH_GUARD: u128 = 3 << 9;
const EVAL_STACK_BYTES: usize = 64 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalLine {
    pub canonical: String,
    pub value: Option<String>,
}

#[derive(Clone, Debug, PartialEq)]
enum Value<E> {
    Element(E),
    Index(i128),
    Bool(bool),
    Function(FunctionValue),
}

#[derive(Clone, Debug, PartialEq)]
struct FunctionValue {
    binders: Vec<Binder>,
    body: Expr,
    ret: Sort,
    mu_name: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Binder {
    name: String,
    sort: Sort,
}

impl FunctionValue {
    fn binder_names(&self) -> Vec<String> {
        self.binders
            .iter()
            .map(|binder| binder.name.clone())
            .collect()
    }

    fn lambda_expr(&self) -> Expr {
        Expr::Lambda {
            binders: self.binder_names(),
            body: Box::new(self.body.clone()),
        }
    }

    fn to_expr(&self) -> Expr {
        self.mu_name.as_ref().map_or_else(
            || self.lambda_expr(),
            |name| Expr::Block {
                bindings: vec![Binding {
                    name: name.clone(),
                    expr: self.lambda_expr(),
                    recursive: true,
                }],
                body: Box::new(Expr::Ident(name.clone())),
            },
        )
    }
}

fn validation_stub(function: &FunctionValue, body: Expr) -> FunctionValue {
    FunctionValue {
        binders: function.binders.clone(),
        body,
        ret: function.ret,
        mu_name: None,
    }
}

fn display_value<E: Display>(value: &Value<E>) -> String {
    match value {
        Value::Element(value) => value.to_string(),
        Value::Index(value) => value.to_string(),
        Value::Bool(value) => value.to_string(),
        Value::Function(function) => {
            let lambda = super::unparse::unparse_expr(&function.lambda_expr());
            function
                .mu_name
                .as_ref()
                .map_or(lambda.clone(), |name| format!("{name} =: {lambda}"))
        }
    }
}

pub fn eval_to_string(world: &str, src: &str) -> OghamResult<String> {
    let mut session = OghamSession::new(world)?;
    let mut out = Vec::new();
    let mut pending = String::new();
    for line in src.lines() {
        let trimmed = line.trim();
        if pending.is_empty() && (trimmed.is_empty() || trimmed.starts_with('#')) {
            continue;
        }
        if pending.is_empty() {
            if let Some(rest) = trimmed.strip_prefix(":world ") {
                session.set_world(rest)?;
                continue;
            }
            if let Some(rest) = trimmed.strip_prefix(":fuel ") {
                let budget = rest
                    .trim()
                    .parse::<u128>()
                    .map_err(|_| parse_error("fuel budget must be a u128"))?;
                session.set_fuel_budget(budget);
                continue;
            }
        }
        if !pending.is_empty() {
            pending.push('\n');
        }
        pending.push_str(trimmed);
        if needs_continuation(&pending)? {
            continue;
        }
        if let Some(value) = session.eval_line(&pending)?.value {
            out.push(value);
        }
        pending.clear();
    }
    if !pending.is_empty() {
        if let Some(value) = session.eval_line(&pending)?.value {
            out.push(value);
        }
    }
    Ok(out.join("\n"))
}

pub struct OghamSession {
    world: World,
}

impl OghamSession {
    pub fn new(world_decl: &str) -> OghamResult<Self> {
        Ok(OghamSession {
            world: World::from_decl(world_decl)?,
        })
    }

    pub fn set_world(&mut self, world_decl: &str) -> OghamResult<()> {
        self.world = World::from_decl(world_decl)?;
        Ok(())
    }

    pub fn eval_line(&mut self, src: &str) -> OghamResult<EvalLine> {
        std::thread::scope(|scope| {
            let worker = std::thread::Builder::new()
                .name("ogham-eval".to_string())
                .stack_size(EVAL_STACK_BYTES)
                .spawn_scoped(scope, || self.eval_line_on_worker(src))
                .map_err(|err| {
                    OghamError::new(
                        OghamErrorKind::Overflow,
                        Span::point(0),
                        format!(
                            "unable to allocate the {EVAL_STACK_BYTES}-byte evaluation stack: {err}"
                        ),
                    )
                })?;
            match worker.join() {
                Ok(result) => result,
                Err(payload) => resume_unwind(payload),
            }
        })
    }

    fn eval_line_on_worker(&mut self, src: &str) -> OghamResult<EvalLine> {
        ensure_source_nesting_depth(src)?;
        let stmt = parse_statement(src)?;
        ensure_statement_depth(&stmt)?;
        let canonical = unparse_statement(&stmt);
        self.world.reset_fuel();
        let value = self.world.eval_statement(&stmt)?;
        Ok(EvalLine { canonical, value })
    }

    pub fn set_fuel_budget(&mut self, budget: u128) {
        self.world.set_fuel_budget(budget);
    }

    pub fn fuel_budget(&self) -> u128 {
        self.world.fuel_budget()
    }

    pub fn world_summary(&self) -> String {
        self.world.summary()
    }

    pub fn env_summary(&self) -> Vec<String> {
        self.world.env_summary()
    }
}

enum World {
    Game(GameRuntime),
    Nimber(Runtime<Nimber>),
    Ordinal(Runtime<Ordinal>),
    Surreal(Runtime<Surreal>),
    Omnific(Runtime<Omnific>),
    Integer(Runtime<Integer>),
    Fp2(Runtime<Fp<2>>),
    Fp3(Runtime<Fp<3>>),
    Fp5(Runtime<Fp<5>>),
    Fp7(Runtime<Fp<7>>),
    F4(Runtime<Fpn<2, 2>>),
    F8(Runtime<Fpn<2, 3>>),
    F16(Runtime<Fpn<2, 4>>),
    F9(Runtime<Fpn<3, 2>>),
    F27(Runtime<Fpn<3, 3>>),
    F25(Runtime<Fpn<5, 2>>),
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

impl World {
    fn from_decl(decl: &str) -> OghamResult<Self> {
        let decl = decl.trim().strip_prefix(":world ").unwrap_or(decl.trim());
        let mut parts = decl.split_whitespace();
        let name = parts
            .next()
            .ok_or_else(|| parse_error("missing world name"))?;
        let tail: Vec<&str> = parts.collect();
        macro_rules! build_poly {
            ($variant:ident, $ty:ty, $label:expr) => {{
                ensure_function_world_decl(name, &tail)?;
                return Ok(World::$variant(PolyRuntime::<$ty>::new($label)));
            }};
        }
        macro_rules! build_ratfunc {
            ($variant:ident, $ty:ty, $label:expr) => {{
                ensure_function_world_decl(name, &tail)?;
                return Ok(World::$variant(RatFuncRuntime::<$ty>::new($label)));
            }};
        }
        match name {
            "game" => {
                ensure_function_world_decl(name, &tail)?;
                return Ok(World::Game(GameRuntime::new()));
            }
            "polyint" => build_poly!(PolyInt, Integer, "polyint"),
            "poly2" => build_poly!(Poly2, Fp<2>, "poly2"),
            "poly3" => build_poly!(Poly3, Fp<3>, "poly3"),
            "poly5" => build_poly!(Poly5, Fp<5>, "poly5"),
            "poly7" => build_poly!(Poly7, Fp<7>, "poly7"),
            "ratfunc2" => build_ratfunc!(RatFunc2, Fp<2>, "ratfunc2"),
            "ratfunc3" => build_ratfunc!(RatFunc3, Fp<3>, "ratfunc3"),
            "ratfunc5" => build_ratfunc!(RatFunc5, Fp<5>, "ratfunc5"),
            "ratfunc7" => build_ratfunc!(RatFunc7, Fp<7>, "ratfunc7"),
            _ => {}
        }
        let second = tail
            .first()
            .copied()
            .ok_or_else(|| parse_error("missing world dimension or constructor"))?;
        if name == "nimber" && second.starts_with("gold(") {
            let metric = parse_gold_metric(second)?;
            return Ok(World::Nimber(Runtime::from_metric("nimber", metric)));
        }
        let dim = second
            .parse::<usize>()
            .map_err(|_| parse_error("world dimension must be a usize"))?;
        let rest = decl.split_once(second).map_or("", |(_, tail)| tail).trim();
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
            _ => Err(OghamError::new(
                OghamErrorKind::WrongWorld,
                Span::point(0),
                format!("unknown world `{name}`"),
            )),
        }
    }

    fn eval_statement(&mut self, stmt: &Statement) -> OghamResult<Option<String>> {
        macro_rules! dispatch {
            ($rt:expr) => {
                $rt.eval_statement(stmt)
            };
        }
        match self {
            World::Game(rt) => dispatch!(rt),
            World::Nimber(rt) => dispatch!(rt),
            World::Ordinal(rt) => dispatch!(rt),
            World::Surreal(rt) => dispatch!(rt),
            World::Omnific(rt) => dispatch!(rt),
            World::Integer(rt) => dispatch!(rt),
            World::Fp2(rt) => dispatch!(rt),
            World::Fp3(rt) => dispatch!(rt),
            World::Fp5(rt) => dispatch!(rt),
            World::Fp7(rt) => dispatch!(rt),
            World::F4(rt) => dispatch!(rt),
            World::F8(rt) => dispatch!(rt),
            World::F16(rt) => dispatch!(rt),
            World::F9(rt) => dispatch!(rt),
            World::F27(rt) => dispatch!(rt),
            World::F25(rt) => dispatch!(rt),
            World::PolyInt(rt) => dispatch!(rt),
            World::Poly2(rt) => dispatch!(rt),
            World::Poly3(rt) => dispatch!(rt),
            World::Poly5(rt) => dispatch!(rt),
            World::Poly7(rt) => dispatch!(rt),
            World::RatFunc2(rt) => dispatch!(rt),
            World::RatFunc3(rt) => dispatch!(rt),
            World::RatFunc5(rt) => dispatch!(rt),
            World::RatFunc7(rt) => dispatch!(rt),
        }
    }

    fn reset_fuel(&mut self) {
        macro_rules! dispatch {
            ($rt:expr) => {
                $rt.reset_fuel()
            };
        }
        match self {
            World::Game(rt) => dispatch!(rt),
            World::Nimber(rt) => dispatch!(rt),
            World::Ordinal(rt) => dispatch!(rt),
            World::Surreal(rt) => dispatch!(rt),
            World::Omnific(rt) => dispatch!(rt),
            World::Integer(rt) => dispatch!(rt),
            World::Fp2(rt) => dispatch!(rt),
            World::Fp3(rt) => dispatch!(rt),
            World::Fp5(rt) => dispatch!(rt),
            World::Fp7(rt) => dispatch!(rt),
            World::F4(rt) => dispatch!(rt),
            World::F8(rt) => dispatch!(rt),
            World::F16(rt) => dispatch!(rt),
            World::F9(rt) => dispatch!(rt),
            World::F27(rt) => dispatch!(rt),
            World::F25(rt) => dispatch!(rt),
            World::PolyInt(rt) => dispatch!(rt),
            World::Poly2(rt) => dispatch!(rt),
            World::Poly3(rt) => dispatch!(rt),
            World::Poly5(rt) => dispatch!(rt),
            World::Poly7(rt) => dispatch!(rt),
            World::RatFunc2(rt) => dispatch!(rt),
            World::RatFunc3(rt) => dispatch!(rt),
            World::RatFunc5(rt) => dispatch!(rt),
            World::RatFunc7(rt) => dispatch!(rt),
        }
    }

    fn set_fuel_budget(&mut self, budget: u128) {
        macro_rules! dispatch {
            ($rt:expr) => {
                $rt.set_fuel_budget(budget)
            };
        }
        match self {
            World::Game(rt) => dispatch!(rt),
            World::Nimber(rt) => dispatch!(rt),
            World::Ordinal(rt) => dispatch!(rt),
            World::Surreal(rt) => dispatch!(rt),
            World::Omnific(rt) => dispatch!(rt),
            World::Integer(rt) => dispatch!(rt),
            World::Fp2(rt) => dispatch!(rt),
            World::Fp3(rt) => dispatch!(rt),
            World::Fp5(rt) => dispatch!(rt),
            World::Fp7(rt) => dispatch!(rt),
            World::F4(rt) => dispatch!(rt),
            World::F8(rt) => dispatch!(rt),
            World::F16(rt) => dispatch!(rt),
            World::F9(rt) => dispatch!(rt),
            World::F27(rt) => dispatch!(rt),
            World::F25(rt) => dispatch!(rt),
            World::PolyInt(rt) => dispatch!(rt),
            World::Poly2(rt) => dispatch!(rt),
            World::Poly3(rt) => dispatch!(rt),
            World::Poly5(rt) => dispatch!(rt),
            World::Poly7(rt) => dispatch!(rt),
            World::RatFunc2(rt) => dispatch!(rt),
            World::RatFunc3(rt) => dispatch!(rt),
            World::RatFunc5(rt) => dispatch!(rt),
            World::RatFunc7(rt) => dispatch!(rt),
        }
    }

    fn fuel_budget(&self) -> u128 {
        macro_rules! dispatch {
            ($rt:expr) => {
                $rt.fuel_budget
            };
        }
        match self {
            World::Game(rt) => dispatch!(rt),
            World::Nimber(rt) => dispatch!(rt),
            World::Ordinal(rt) => dispatch!(rt),
            World::Surreal(rt) => dispatch!(rt),
            World::Omnific(rt) => dispatch!(rt),
            World::Integer(rt) => dispatch!(rt),
            World::Fp2(rt) => dispatch!(rt),
            World::Fp3(rt) => dispatch!(rt),
            World::Fp5(rt) => dispatch!(rt),
            World::Fp7(rt) => dispatch!(rt),
            World::F4(rt) => dispatch!(rt),
            World::F8(rt) => dispatch!(rt),
            World::F16(rt) => dispatch!(rt),
            World::F9(rt) => dispatch!(rt),
            World::F27(rt) => dispatch!(rt),
            World::F25(rt) => dispatch!(rt),
            World::PolyInt(rt) => dispatch!(rt),
            World::Poly2(rt) => dispatch!(rt),
            World::Poly3(rt) => dispatch!(rt),
            World::Poly5(rt) => dispatch!(rt),
            World::Poly7(rt) => dispatch!(rt),
            World::RatFunc2(rt) => dispatch!(rt),
            World::RatFunc3(rt) => dispatch!(rt),
            World::RatFunc5(rt) => dispatch!(rt),
            World::RatFunc7(rt) => dispatch!(rt),
        }
    }

    fn summary(&self) -> String {
        macro_rules! dispatch {
            ($rt:expr) => {
                $rt.summary()
            };
        }
        match self {
            World::Game(rt) => dispatch!(rt),
            World::Nimber(rt) => dispatch!(rt),
            World::Ordinal(rt) => dispatch!(rt),
            World::Surreal(rt) => dispatch!(rt),
            World::Omnific(rt) => dispatch!(rt),
            World::Integer(rt) => dispatch!(rt),
            World::Fp2(rt) => dispatch!(rt),
            World::Fp3(rt) => dispatch!(rt),
            World::Fp5(rt) => dispatch!(rt),
            World::Fp7(rt) => dispatch!(rt),
            World::F4(rt) => dispatch!(rt),
            World::F8(rt) => dispatch!(rt),
            World::F16(rt) => dispatch!(rt),
            World::F9(rt) => dispatch!(rt),
            World::F27(rt) => dispatch!(rt),
            World::F25(rt) => dispatch!(rt),
            World::PolyInt(rt) => dispatch!(rt),
            World::Poly2(rt) => dispatch!(rt),
            World::Poly3(rt) => dispatch!(rt),
            World::Poly5(rt) => dispatch!(rt),
            World::Poly7(rt) => dispatch!(rt),
            World::RatFunc2(rt) => dispatch!(rt),
            World::RatFunc3(rt) => dispatch!(rt),
            World::RatFunc5(rt) => dispatch!(rt),
            World::RatFunc7(rt) => dispatch!(rt),
        }
    }

    fn env_summary(&self) -> Vec<String> {
        macro_rules! dispatch {
            ($rt:expr) => {
                $rt.env_summary()
            };
        }
        match self {
            World::Game(rt) => dispatch!(rt),
            World::Nimber(rt) => dispatch!(rt),
            World::Ordinal(rt) => dispatch!(rt),
            World::Surreal(rt) => dispatch!(rt),
            World::Omnific(rt) => dispatch!(rt),
            World::Integer(rt) => dispatch!(rt),
            World::Fp2(rt) => dispatch!(rt),
            World::Fp3(rt) => dispatch!(rt),
            World::Fp5(rt) => dispatch!(rt),
            World::Fp7(rt) => dispatch!(rt),
            World::F4(rt) => dispatch!(rt),
            World::F8(rt) => dispatch!(rt),
            World::F16(rt) => dispatch!(rt),
            World::F9(rt) => dispatch!(rt),
            World::F27(rt) => dispatch!(rt),
            World::F25(rt) => dispatch!(rt),
            World::PolyInt(rt) => dispatch!(rt),
            World::Poly2(rt) => dispatch!(rt),
            World::Poly3(rt) => dispatch!(rt),
            World::Poly5(rt) => dispatch!(rt),
            World::Poly7(rt) => dispatch!(rt),
            World::RatFunc2(rt) => dispatch!(rt),
            World::RatFunc3(rt) => dispatch!(rt),
            World::RatFunc5(rt) => dispatch!(rt),
            World::RatFunc7(rt) => dispatch!(rt),
        }
    }
}

fn ensure_function_world_decl(name: &str, tail: &[&str]) -> OghamResult<()> {
    if tail.is_empty() || tail == ["0"] {
        Ok(())
    } else {
        Err(parse_error(format!(
            "`{name}` is a function-shaped scalar world; it takes no metric declaration"
        )))
    }
}

#[derive(Clone)]
enum GameElement {
    Finite(Game),
    Graph(GraphRef),
}

#[derive(Clone)]
struct GraphRef {
    graph: Arc<RegularGameGraph>,
    node: usize,
}

struct RegularGameGraph {
    name: String,
    nodes: Vec<RegularGameNode>,
    drawn: Vec<bool>,
}

type GraphKey = (usize, usize);
type GraphPair = (GraphKey, GraphKey);

#[derive(Clone)]
struct RegularGameNode {
    left: Vec<RegularGameEdge>,
    right: Vec<RegularGameEdge>,
}

#[derive(Clone)]
enum RegularGameEdge {
    Finite(Game),
    Local(usize),
    External(GraphRef),
}

#[derive(Clone)]
enum SymbolicGame {
    Value(GameElement),
    Form {
        left: Vec<SymbolicGame>,
        right: Vec<SymbolicGame>,
    },
    SelfRef,
}

impl std::fmt::Display for GameElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", display_game_element(self))
    }
}

struct GameRuntime {
    env: BTreeMap<String, Value<GameElement>>,
    fuel_budget: u128,
    fuel_remaining: u128,
    active_mu_calls: HashSet<String>,
    recursion_depth: u128,
    validation_stub_names: BTreeSet<String>,
}

impl GameRuntime {
    fn new() -> Self {
        GameRuntime {
            env: BTreeMap::new(),
            fuel_budget: DEFAULT_FUEL,
            fuel_remaining: DEFAULT_FUEL,
            active_mu_calls: HashSet::new(),
            recursion_depth: 0,
            validation_stub_names: BTreeSet::new(),
        }
    }

    fn reset_fuel(&mut self) {
        self.fuel_remaining = self.fuel_budget;
        self.active_mu_calls.clear();
        self.recursion_depth = 0;
    }

    fn set_fuel_budget(&mut self, budget: u128) {
        self.fuel_budget = budget;
        self.reset_fuel();
    }

    fn eval_statement(&mut self, stmt: &Statement) -> OghamResult<Option<String>> {
        match stmt {
            Statement::Binding {
                name,
                expr,
                recursive,
            } => {
                self.bind_name(name, expr, *recursive)?;
                Ok(None)
            }
            Statement::Expr(expr) => Ok(Some(display_game_value(&self.eval_value(expr)?))),
            Statement::Seq { bindings, tail } => {
                for binding in bindings {
                    self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
                }
                self.eval_statement(tail)
            }
        }
    }

    fn bind_name(&mut self, name: &str, expr: &Expr, recursive: bool) -> OghamResult<()> {
        if reserved_function_binder(name) {
            return Err(OghamError::new(
                OghamErrorKind::Reserved,
                Span::point(0),
                format!("`{name}` is reserved in the `game` world"),
            ));
        }
        if recursive && contains_free_name(expr, name) {
            if let Expr::Lambda { binders, body } = expr {
                let function = self.close_function(
                    binders.clone(),
                    body.as_ref().clone(),
                    Some(name.to_string()),
                )?;
                self.env.insert(name.to_string(), Value::Function(function));
                return Ok(());
            }
            let reduced = self.reduce_element_fixpoint(name, expr, false)?;
            let value = materialize_regular_game(name, reduced)?;
            self.env.insert(name.to_string(), Value::Element(value));
            return Ok(());
        }
        let value = self.eval_value(expr)?;
        self.env.insert(name.to_string(), value);
        Ok(())
    }

    fn eval_block(&mut self, bindings: &[Binding], body: &Expr) -> OghamResult<Value<GameElement>> {
        let saved = self.env.clone();
        let result = (|| {
            for binding in bindings {
                self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
            }
            self.eval_value(body)
        })();
        self.env = saved;
        result
    }

    fn summary(&self) -> String {
        "game".to_string()
    }

    fn env_summary(&self) -> Vec<String> {
        self.env
            .iter()
            .map(|(name, value)| format!("{name} := {}", display_game_value(value)))
            .collect()
    }

    fn eval_value(&mut self, expr: &Expr) -> OghamResult<Value<GameElement>> {
        match expr {
            Expr::Bool(value) => Ok(Value::Bool(*value)),
            Expr::Tuple(_) => Err(fn_sort_error()),
            Expr::Block { bindings, body } => self.eval_block(bindings, body),
            Expr::Lambda { binders, body } => self
                .close_function(binders.clone(), body.as_ref().clone(), None)
                .map(Value::Function),
            Expr::Ident(name) => self
                .env
                .get(name)
                .cloned()
                .ok_or_else(|| unbound_error(name)),
            Expr::Call { name, args } if name == "drawn" => {
                expect_arity(name, args, 1)?;
                Ok(Value::Bool(game_element_drawn(
                    &self.eval_element(&args[0])?,
                )))
            }
            Expr::Relation { op, lhs, rhs } => Ok(Value::Bool(self.eval_relation(*op, lhs, rhs)?)),
            Expr::Unary {
                op: UnaryOp::Not,
                expr,
            } => Ok(Value::Bool(!self.eval_bool(expr)?)),
            Expr::Binary {
                op: BinaryOp::And,
                lhs,
                rhs,
            } => {
                let lhs = self.eval_bool(lhs)?;
                if self.static_sort(rhs)? != Sort::Bool {
                    return Err(bool_sort_error());
                }
                if !lhs {
                    return Ok(Value::Bool(false));
                }
                Ok(Value::Bool(self.eval_bool(rhs)?))
            }
            Expr::Binary {
                op: BinaryOp::Or,
                lhs,
                rhs,
            } => {
                let lhs = self.eval_bool(lhs)?;
                if self.static_sort(rhs)? != Sort::Bool {
                    return Err(bool_sort_error());
                }
                if lhs {
                    return Ok(Value::Bool(true));
                }
                Ok(Value::Bool(self.eval_bool(rhs)?))
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                let then_sort = self.static_sort(then_expr)?;
                let else_sort = self.static_sort(else_expr)?;
                if then_sort != else_sort {
                    return Err(sort_mismatch(then_sort, else_sort));
                }
                if self.eval_bool(cond)? {
                    self.eval_value(then_expr)
                } else {
                    self.eval_value(else_expr)
                }
            }
            Expr::Binary {
                op: BinaryOp::At,
                lhs,
                rhs,
            } => self.eval_at(lhs, rhs),
            _ if expression_is_index(expr) => Ok(Value::Index(self.eval_index(expr)?)),
            _ => match self.eval_element(expr) {
                Ok(value) => Ok(Value::Element(value)),
                Err(err) if err.kind == OghamErrorKind::IndexSort => {
                    Ok(Value::Index(self.eval_index(expr)?))
                }
                Err(err) => Err(err),
            },
        }
    }

    fn eval_bool(&mut self, expr: &Expr) -> OghamResult<bool> {
        match self.eval_value(expr)? {
            Value::Bool(value) => Ok(value),
            Value::Element(_) | Value::Index(_) => Err(bool_sort_error()),
            Value::Function(_) => Err(fn_sort_error()),
        }
    }

    fn eval_at(&mut self, lhs: &Expr, rhs: &Expr) -> OghamResult<Value<GameElement>> {
        let lhs_v = self.eval_value(lhs)?;
        let Value::Function(function) = lhs_v else {
            return Err(game_wrong_world(
                "Element application with `@` is not defined for games",
            ));
        };
        if let Expr::Tuple(items) = rhs {
            return self.apply_function_exprs(&function, items);
        }
        match self.eval_value(rhs)? {
            Value::Function(rhs_fn) => self
                .compose_functions(&function, &rhs_fn)
                .map(Value::Function),
            _ => self.apply_function_exprs(&function, std::slice::from_ref(rhs)),
        }
    }

    fn apply_function(
        &mut self,
        function: &FunctionValue,
        args: Vec<Value<GameElement>>,
    ) -> OghamResult<Value<GameElement>> {
        if args.len() != function.binders.len() {
            return Err(OghamError::new(
                OghamErrorKind::Arity,
                Span::point(0),
                format!(
                    "function expects {} argument(s), got {}",
                    function.binders.len(),
                    args.len()
                ),
            ));
        }
        consume_fuel(function, &mut self.fuel_remaining, self.fuel_budget)?;
        for (binder, arg) in function.binders.iter().zip(&args) {
            ensure_value_sort(arg, binder.sort)?;
        }
        let call_key = function
            .mu_name
            .as_ref()
            .map(|name| game_mu_call_key(name, &function.body, &args));
        if call_key
            .as_ref()
            .is_some_and(|key| self.active_mu_calls.contains(key))
        {
            self.fuel_remaining = 0;
            return Err(OghamError::new(
                OghamErrorKind::Fuel,
                Span::point(0),
                format!(
                    "recursive definition `{}` exhausted its fuel budget of {}",
                    function.mu_name.as_deref().unwrap_or("μ"),
                    self.fuel_budget
                ),
            ));
        }
        let recursive_frame = enter_recursion_frame(
            function,
            &mut self.recursion_depth,
            self.fuel_remaining,
            self.fuel_budget,
        )?;
        if let Some(key) = &call_key {
            self.active_mu_calls.insert(key.clone());
        }
        let mut previous_args = Vec::new();
        for (binder, arg) in function.binders.iter().zip(args.iter()) {
            previous_args.push((
                binder.name.clone(),
                self.env.insert(binder.name.clone(), arg.clone()),
            ));
        }
        let previous = function.mu_name.as_ref().map(|name| {
            self.env
                .insert(name.clone(), Value::Function(function.clone()))
        });
        let result = match function.ret {
            Sort::Element => self.eval_element(&function.body).map(Value::Element),
            Sort::Index => self.eval_index(&function.body).map(Value::Index),
            Sort::Bool => self.eval_bool(&function.body).map(Value::Bool),
        };
        if let Some(name) = &function.mu_name {
            if let Some(previous) = previous.flatten() {
                self.env.insert(name.clone(), previous);
            } else {
                self.env.remove(name);
            }
        }
        for (name, previous) in previous_args.into_iter().rev() {
            if let Some(previous) = previous {
                self.env.insert(name, previous);
            } else {
                self.env.remove(&name);
            }
        }
        if let Some(key) = call_key {
            self.active_mu_calls.remove(&key);
        }
        leave_recursion_frame(recursive_frame, &mut self.recursion_depth);
        result
    }

    fn apply_function_exprs(
        &mut self,
        function: &FunctionValue,
        args: &[Expr],
    ) -> OghamResult<Value<GameElement>> {
        if args.len() != function.binders.len() {
            return Err(OghamError::new(
                OghamErrorKind::Arity,
                Span::point(0),
                format!(
                    "function expects {} argument(s), got {}",
                    function.binders.len(),
                    args.len()
                ),
            ));
        }
        let values = function
            .binders
            .iter()
            .zip(args)
            .map(|(binder, arg)| self.eval_arg_for_sort(arg, binder.sort))
            .collect::<OghamResult<Vec<_>>>()?;
        self.apply_function(function, values)
    }

    fn eval_arg_for_sort(&mut self, expr: &Expr, sort: Sort) -> OghamResult<Value<GameElement>> {
        match sort {
            Sort::Element => self.eval_element(expr).map(Value::Element),
            Sort::Index => self.eval_index(expr).map(Value::Index),
            Sort::Bool => self.eval_bool(expr).map(Value::Bool),
        }
    }

    fn compose_functions(
        &mut self,
        lhs: &FunctionValue,
        rhs: &FunctionValue,
    ) -> OghamResult<FunctionValue> {
        if lhs.binders.len() != 1 {
            return Err(OghamError::new(
                OghamErrorKind::Arity,
                Span::point(0),
                "function composition needs a unary head",
            ));
        }
        if lhs.binders[0].sort != rhs.ret {
            return Err(sort_mismatch(lhs.binders[0].sort, rhs.ret));
        }
        let mut replacements = BTreeMap::new();
        replacements.insert(lhs.binders[0].name.clone(), rhs.body.clone());
        let body = beta_normalize(substitute_names(&lhs.body, &replacements))?;
        let function = FunctionValue {
            binders: rhs.binders.clone(),
            body,
            ret: lhs.ret,
            mu_name: None,
        };
        self.validate_function_body(&function)?;
        Ok(function)
    }

    fn close_function(
        &mut self,
        binders: Vec<String>,
        body: Expr,
        mu_name: Option<String>,
    ) -> OghamResult<FunctionValue> {
        check_binders(&binders, reserved_function_binder)?;
        let mut bound: BTreeSet<String> = binders.iter().cloned().collect();
        bound.extend(mu_name.iter().cloned());
        bound.extend(self.validation_stub_names.iter().cloned());
        let substituted = substitute_env(&body, &bound, &self.env)?;
        let body = beta_normalize(substituted)?;
        let (mut binder_sorts, mut ret) = infer_function_signature(&body, &binders)?;
        refine_game_binder_sorts(&body, &binders, &mut binder_sorts, &self.env);
        if let Some(hint) = game_return_sort_hint(&body, &self.env, mu_name.as_deref()) {
            ret = hint;
        }
        if let Some(name) = mu_name.as_deref() {
            if is_game_index_counter(name, &body) {
                for (binder, sort) in binders.iter().zip(&mut binder_sorts) {
                    if contains_game_binder_unit_step(binder, &body) {
                        *sort = Sort::Index;
                    }
                }
            }
        }
        let function = FunctionValue {
            binders: binders
                .into_iter()
                .zip(binder_sorts)
                .map(|(name, sort)| Binder { name, sort })
                .collect(),
            body,
            ret,
            mu_name,
        };
        if let Some(name) = &function.mu_name {
            let stub = validation_stub(&function, self.sample_expr(function.ret)?);
            let previous = self.env.insert(name.clone(), Value::Function(stub));
            self.validation_stub_names.insert(name.clone());
            let validation = self.validate_function_body(&function);
            self.validation_stub_names.remove(name);
            if let Some(previous) = previous {
                self.env.insert(name.clone(), previous);
            } else {
                self.env.remove(name);
            }
            validation?;
        } else {
            self.validate_function_body(&function)?;
        }
        Ok(function)
    }

    fn validate_function_body(&mut self, function: &FunctionValue) -> OghamResult<()> {
        let mut replacements = BTreeMap::new();
        for binder in &function.binders {
            replacements.insert(binder.name.clone(), self.sample_expr(binder.sort)?);
        }
        let sampled = substitute_names(&function.body, &replacements);
        self.validate_all(&sampled)
    }

    fn validate_all(&mut self, expr: &Expr) -> OghamResult<()> {
        match expr {
            Expr::Lambda { .. } => return Err(fn_sort_error()),
            Expr::Block { bindings, body } => {
                let saved = self.env.clone();
                let saved_validation_stubs = self.validation_stub_names.clone();
                let result = (|| {
                    for binding in bindings {
                        if !matches!(binding.expr, Expr::Lambda { .. }) {
                            self.validate_all(&binding.expr)?;
                        }
                        self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
                        if let Some(Value::Function(function)) =
                            self.env.get(&binding.name).cloned()
                        {
                            let stub = validation_stub(&function, self.sample_expr(function.ret)?);
                            self.env.insert(binding.name.clone(), Value::Function(stub));
                            self.validation_stub_names.insert(binding.name.clone());
                        }
                    }
                    self.validate_all(body)
                })();
                self.env = saved;
                self.validation_stub_names = saved_validation_stubs;
                result?;
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.validate_all(cond)?;
                self.validate_all(then_expr)?;
                self.validate_all(else_expr)?;
                return Ok(());
            }
            Expr::Binary {
                op: BinaryOp::And | BinaryOp::Or,
                lhs,
                rhs,
            } => {
                self.validate_all(lhs)?;
                self.validate_all(rhs)?;
            }
            _ => {}
        }
        ignore_static_partiality(self.eval_value(expr))
    }

    fn sample_expr(&self, sort: Sort) -> OghamResult<Expr> {
        match sort {
            Sort::Element => Ok(Expr::Int(0)),
            Sort::Index => Ok(Expr::Int(1)),
            Sort::Bool => Ok(Expr::Bool(true)),
        }
    }

    fn static_sort(&self, expr: &Expr) -> OghamResult<Sort> {
        static_sort(expr, &self.env, false)
    }

    fn eval_relation(&mut self, op: RelOp, lhs: &Expr, rhs: &Expr) -> OghamResult<bool> {
        if !bool_shaped(lhs)
            && !bool_shaped(rhs)
            && (expression_is_index(lhs)
                || expression_is_index(rhs)
                || game_known_sort(lhs, &self.env) == Some(Sort::Index)
                || game_known_sort(rhs, &self.env) == Some(Sort::Index)
                || self.static_sort(lhs) == Ok(Sort::Index)
                || self.static_sort(rhs) == Ok(Sort::Index))
        {
            let lhs = self.eval_index(lhs)?;
            let rhs = self.eval_index(rhs)?;
            return ordered_relation(op, lhs.cmp(&rhs));
        }
        let lhs_v = self.eval_value(lhs)?;
        let rhs_v = self.eval_value(rhs)?;
        match (lhs_v, rhs_v) {
            (Value::Function(_), _) | (_, Value::Function(_)) => Err(fn_sort_error()),
            (Value::Bool(lhs), Value::Bool(rhs)) => {
                if op == RelOp::Eq {
                    Ok(lhs == rhs)
                } else {
                    Err(bool_sort_error())
                }
            }
            (Value::Bool(_), _) | (_, Value::Bool(_)) => Err(bool_sort_error()),
            (Value::Index(lhs), Value::Index(rhs)) => ordered_relation(op, lhs.cmp(&rhs)),
            (Value::Index(_), _) | (_, Value::Index(_)) => Err(index_sort_error()),
            (Value::Element(lhs), Value::Element(rhs)) => {
                if op == RelOp::Equiv {
                    return Ok(game_element_regular_eq(&lhs, &rhs));
                }
                let (GameElement::Finite(lhs), GameElement::Finite(rhs)) = (lhs, rhs) else {
                    return Err(loopy_error(
                        "value relations are not defined on loopy games in the 3.0 envelope",
                    ));
                };
                match op {
                    RelOp::Eq => Ok(lhs.eq(&rhs)),
                    RelOp::Lt => Ok(lhs.le(&rhs) && !rhs.le(&lhs)),
                    RelOp::Gt => Ok(rhs.le(&lhs) && !lhs.le(&rhs)),
                    RelOp::Fuzzy => Ok(lhs.fuzzy(&rhs)),
                    RelOp::Equiv => unreachable!("handled above"),
                }
            }
        }
    }

    fn eval_element(&mut self, expr: &Expr) -> OghamResult<GameElement> {
        match expr {
            Expr::Bool(_) => Err(bool_sort_error()),
            Expr::Int(n) => {
                let n = i128::try_from(*n).map_err(|_| overflow("game integer exceeds i128"))?;
                Ok(GameElement::Finite(Game::integer(n)))
            }
            Expr::Star(StarLiteral::Finite(n)) => Ok(GameElement::Finite(Game::nim_heap(*n))),
            Expr::Star(StarLiteral::Cnf(_)) => Err(game_wrong_world(
                "transfinite nimber games are outside the finite `game` world",
            )),
            Expr::Omega => Err(game_wrong_world(
                "`ω` is not a finite short game; use finite game forms",
            )),
            Expr::Blade(_) => Err(game_wrong_world("the game world has no Clifford blades")),
            Expr::Vector(_) => Err(game_wrong_world(
                "the game world has no fixed arrays; lists are braces here: `{1, 2, 3}`",
            )),
            Expr::Tuple(_) | Expr::Lambda { .. } => Err(fn_sort_error()),
            Expr::GameForm { left, right } => build_game_form(
                left.iter()
                    .map(|item| self.eval_element(item))
                    .collect::<OghamResult<Vec<_>>>()?,
                right
                    .iter()
                    .map(|item| self.eval_element(item))
                    .collect::<OghamResult<Vec<_>>>()?,
            ),
            Expr::Block { bindings, body } => match self.eval_block(bindings, body)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Ident(name) => match self.env.get(name) {
                Some(Value::Element(value)) => Ok(value.clone()),
                Some(Value::Index(_)) => Err(index_sort_error()),
                Some(Value::Bool(_)) => Err(bool_sort_error()),
                Some(Value::Function(_)) => Err(fn_sort_error()),
                None => Err(unbound_error(name)),
            },
            Expr::Call { name, args } => self.eval_element_call(name, args),
            Expr::Factorial(expr) => {
                let n = self.eval_index(expr)?;
                let value = checked_factorial_i128(n)
                    .ok_or_else(|| overflow("factorial exceeds the i128 game-integer range"))?;
                Ok(GameElement::Finite(Game::integer(value)))
            }
            Expr::Unary { op, expr } => match op {
                UnaryOp::Neg => match self.eval_element(expr)? {
                    GameElement::Finite(game) => Ok(GameElement::Finite(game.neg())),
                    GameElement::Graph(_) => Err(loopy_error(
                        "unary `-` is not defined on loopy games in the 3.0 envelope",
                    )),
                },
                UnaryOp::Inv => Err(game_wrong_world(
                    "games form an additive group, not a field; `/` is undefined",
                )),
                UnaryOp::Not => Err(bool_sort_error()),
            },
            Expr::Binary {
                op: BinaryOp::At, ..
            } => match self.eval_value(expr)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Binary { op, lhs, rhs } => self.eval_binary(*op, lhs, rhs),
            Expr::Ternary { .. } => match self.eval_value(expr)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Relation { .. } => Err(bool_sort_error()),
        }
    }

    fn eval_binary(&mut self, op: BinaryOp, lhs: &Expr, rhs: &Expr) -> OghamResult<GameElement> {
        match op {
            BinaryOp::Add | BinaryOp::Sub => {
                let lhs = self.eval_element(lhs)?;
                let rhs = self.eval_element(rhs)?;
                let (GameElement::Finite(lhs), GameElement::Finite(rhs)) = (lhs, rhs) else {
                    return Err(loopy_error(
                        "additive operations are not defined on loopy games in the 3.0 envelope",
                    ));
                };
                Ok(GameElement::Finite(if op == BinaryOp::Add {
                    lhs.add(&rhs)
                } else {
                    lhs.add(&rhs.neg())
                }))
            }
            BinaryOp::Append => {
                let lhs = self.eval_element(lhs)?;
                let rhs = self.eval_element(rhs)?;
                append_game_element(&lhs, &rhs)
            }
            BinaryOp::Mul => Err(game_wrong_world(
                "games are an additive group, not a ring; `⋅` is undefined",
            )),
            BinaryOp::Wedge => Err(game_wrong_world(
                "the game world has no wedge product; list append is `⧺`",
            )),
            BinaryOp::Div => Err(game_wrong_world(
                "games are an additive group, not a field; `/` is undefined",
            )),
            BinaryOp::Rem => Err(game_wrong_world("remainder `%` is undefined for games")),
            BinaryOp::Pow => Err(game_wrong_world("power `↑` is undefined for games")),
            BinaryOp::At => Err(game_wrong_world(
                "Element application with `@` is not defined for games",
            )),
            BinaryOp::And | BinaryOp::Or => Err(bool_sort_error()),
        }
    }

    fn eval_element_call(&mut self, name: &str, args: &[Expr]) -> OghamResult<GameElement> {
        match name {
            "canon" => {
                expect_arity(name, args, 1)?;
                match self.eval_element(&args[0])? {
                    GameElement::Finite(game) => Ok(GameElement::Finite(game.canonical())),
                    GameElement::Graph(_) => Err(loopy_error(
                        "`canon` is not defined on loopy games in the 3.0 envelope",
                    )),
                }
            }
            "left" | "right" => {
                expect_arity(name, args, 2)?;
                let game = self.eval_element(&args[0])?;
                let index = game_option_index(name, self.eval_index(&args[1])?)?;
                let options = game_options(&game, name == "left");
                options.get(index).cloned().ok_or_else(|| {
                    domain(format!(
                        "{name} option index {index} is outside option count {}",
                        options.len()
                    ))
                })
            }
            "up" => {
                expect_arity(name, args, 0)?;
                Ok(GameElement::Finite(Game::up()))
            }
            "down" => {
                expect_arity(name, args, 0)?;
                Ok(GameElement::Finite(Game::up().neg()))
            }
            "nleft" | "nright" => {
                Err(index_sort_error().with_hint(format!("`{name}` returns an Index")))
            }
            "coef" | "dim" => Err(array_world_error(name)),
            "rev" | "grade" | "even" | "dual" | "frob" | "tr" => Err(game_wrong_world(&format!(
                "`{name}` is a Clifford-world operation, not a game operation"
            ))),
            "deg" | "gcd" => Err(game_wrong_world(&format!(
                "`{name}` is a function-world operation, not a game operation"
            ))),
            "drawn" => Err(bool_sort_error()),
            _ => Err(OghamError::new(
                OghamErrorKind::UnknownFn,
                Span::point(0),
                format!("unknown function `{name}`"),
            )),
        }
    }

    fn reduce_element_fixpoint(
        &mut self,
        name: &str,
        expr: &Expr,
        _inside_form: bool,
    ) -> OghamResult<SymbolicGame> {
        match expr {
            Expr::Ident(found) if found == name => Ok(SymbolicGame::SelfRef),
            Expr::GameForm { left, right } => Ok(SymbolicGame::Form {
                left: left
                    .iter()
                    .map(|item| self.reduce_element_fixpoint(name, item, true))
                    .collect::<OghamResult<_>>()?,
                right: right
                    .iter()
                    .map(|item| self.reduce_element_fixpoint(name, item, true))
                    .collect::<OghamResult<_>>()?,
            }),
            Expr::Binary {
                op: BinaryOp::Append,
                lhs,
                rhs,
            } => {
                if contains_free_name(lhs, name) {
                    return Err(unfounded_error(name));
                }
                let left = self.eval_element(lhs)?;
                let right = self.reduce_element_fixpoint(name, rhs, false)?;
                append_symbolic_spine(&left, right)
            }
            _ if contains_free_name(expr, name) => Err(unfounded_error(name)),
            _ => self.eval_element(expr).map(SymbolicGame::Value),
        }
    }

    fn eval_index(&mut self, expr: &Expr) -> OghamResult<i128> {
        match expr {
            Expr::Int(n) => u128_to_i128(*n),
            Expr::Bool(_) => Err(bool_sort_error()),
            Expr::Tuple(_) | Expr::Lambda { .. } => Err(fn_sort_error()),
            Expr::Block { bindings, body } => match self.eval_block(bindings, body)? {
                Value::Index(value) => Ok(value),
                Value::Element(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Ident(name) => match self.env.get(name) {
                Some(Value::Index(value)) => Ok(*value),
                Some(Value::Element(_)) => Err(index_sort_error()),
                Some(Value::Bool(_)) => Err(bool_sort_error()),
                Some(Value::Function(_)) => Err(fn_sort_error()),
                None => Err(unbound_error(name)),
            },
            Expr::Call { name, args } if matches!(name.as_str(), "nleft" | "nright") => {
                expect_arity(name, args, 1)?;
                let game = self.eval_element(&args[0])?;
                let len = game_options(&game, name == "nleft").len();
                i128::try_from(len).map_err(|_| overflow("game option count exceeds i128"))
            }
            Expr::Call { name, .. } if name == "dim" => Err(array_world_error(name)),
            Expr::Unary {
                op: UnaryOp::Neg,
                expr,
            } => self
                .eval_index(expr)?
                .checked_neg()
                .ok_or_else(|| overflow("index negation overflowed i128")),
            Expr::Unary {
                op: UnaryOp::Inv, ..
            } => Err(index_sort_error()),
            Expr::Unary {
                op: UnaryOp::Not, ..
            } => Err(bool_sort_error()),
            Expr::Binary {
                op: BinaryOp::At, ..
            } => match self.eval_value(expr)? {
                Value::Index(value) => Ok(value),
                Value::Element(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Binary { op, lhs, rhs } => {
                let lhs = self.eval_index(lhs)?;
                let rhs = self.eval_index(rhs)?;
                eval_index_binary(*op, lhs, rhs)
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                if self.eval_bool(cond)? {
                    self.eval_index(then_expr)
                } else {
                    self.eval_index(else_expr)
                }
            }
            Expr::Relation { .. } => Err(bool_sort_error()),
            Expr::Star(_)
            | Expr::Omega
            | Expr::Blade(_)
            | Expr::Vector(_)
            | Expr::GameForm { .. }
            | Expr::Call { .. }
            | Expr::Factorial(_) => Err(index_sort_error()),
        }
    }
}

fn display_game_value(value: &Value<GameElement>) -> String {
    match value {
        Value::Element(game) => display_game_element(game),
        Value::Index(value) => value.to_string(),
        Value::Bool(value) => value.to_string(),
        Value::Function(function) => {
            let lambda = super::unparse::unparse_expr(&function.lambda_expr());
            function
                .mu_name
                .as_ref()
                .map_or(lambda.clone(), |name| format!("{name} =: {lambda}"))
        }
    }
}

fn display_game_element(element: &GameElement) -> String {
    match element {
        GameElement::Finite(game) => display_game(game),
        GameElement::Graph(reference) if !reference.graph.name.is_empty() => {
            let mut anchors = HashMap::new();
            anchors.insert(graph_key(reference), reference.graph.name.clone());
            format!(
                "{} =: {}",
                reference.graph.name,
                display_graph_node(reference, &anchors, true, &mut HashSet::new())
            )
        }
        GameElement::Graph(reference) => display_composite_graph(reference),
    }
}

fn display_composite_graph(reference: &GraphRef) -> String {
    let mut external = Vec::new();
    collect_external_cycles(reference, &mut HashSet::new(), &mut external);
    if external.is_empty() {
        return display_graph_node(reference, &HashMap::new(), true, &mut HashSet::new());
    }
    let mut anchors = HashMap::new();
    for cycle in &external {
        anchors
            .entry(graph_key(cycle))
            .or_insert_with(|| cycle.graph.name.clone());
    }
    let mut parts = external
        .iter()
        .map(|cycle| {
            format!(
                "{} =: {}",
                cycle.graph.name,
                display_graph_node(cycle, &anchors, true, &mut HashSet::new())
            )
        })
        .collect::<Vec<_>>();
    parts.push(display_graph_node(
        reference,
        &anchors,
        true,
        &mut HashSet::new(),
    ));
    format!("({})", parts.join("; "))
}

fn collect_external_cycles(
    reference: &GraphRef,
    visited: &mut HashSet<(usize, usize)>,
    out: &mut Vec<GraphRef>,
) {
    if !visited.insert(graph_key(reference)) {
        return;
    }
    let node = &reference.graph.nodes[reference.node];
    for edge in node.left.iter().chain(&node.right) {
        match edge {
            RegularGameEdge::Local(node) => collect_external_cycles(
                &GraphRef {
                    graph: reference.graph.clone(),
                    node: *node,
                },
                visited,
                out,
            ),
            RegularGameEdge::External(external) => {
                if external.graph.name.is_empty() {
                    collect_external_cycles(external, visited, out);
                } else if !out
                    .iter()
                    .any(|found| graph_key(found) == graph_key(external))
                {
                    out.push(external.clone());
                }
            }
            RegularGameEdge::Finite(_) => {}
        }
    }
}

fn display_graph_node(
    reference: &GraphRef,
    anchors: &HashMap<GraphKey, String>,
    expand_root: bool,
    active: &mut HashSet<GraphKey>,
) -> String {
    let key = graph_key(reference);
    if !expand_root {
        if let Some(name) = anchors.get(&key) {
            return name.clone();
        }
    }
    if !active.insert(key) {
        return anchors
            .get(&key)
            .cloned()
            .unwrap_or_else(|| reference.graph.name.clone());
    }
    let node = &reference.graph.nodes[reference.node];
    let left = node
        .left
        .iter()
        .map(|edge| display_regular_edge(reference, edge, anchors, active))
        .collect::<Vec<_>>()
        .join(", ");
    let right = node
        .right
        .iter()
        .map(|edge| display_regular_edge(reference, edge, anchors, active))
        .collect::<Vec<_>>()
        .join(", ");
    active.remove(&key);
    display_raw_game_form(&left, &right)
}

fn display_regular_edge(
    owner: &GraphRef,
    edge: &RegularGameEdge,
    anchors: &HashMap<GraphKey, String>,
    active: &mut HashSet<GraphKey>,
) -> String {
    match edge {
        RegularGameEdge::Finite(game) => display_game(game),
        RegularGameEdge::Local(node) => display_graph_node(
            &GraphRef {
                graph: owner.graph.clone(),
                node: *node,
            },
            anchors,
            false,
            active,
        ),
        RegularGameEdge::External(reference) => {
            display_graph_node(reference, anchors, false, active)
        }
    }
}

fn display_raw_game_form(left: &str, right: &str) -> String {
    match (left.is_empty(), right.is_empty()) {
        (true, true) => "{|}".to_string(),
        (false, true) => format!("{{{left} |}}"),
        (true, false) => format!("{{| {right}}}"),
        (false, false) => format!("{{{left} | {right}}}"),
    }
}

fn display_game(game: &Game) -> String {
    if let Some(integer) = structural_game_integer(game) {
        return integer.to_string();
    }
    if let Some(nimber) = structural_game_nimber(game) {
        return format!("*{nimber}");
    }
    let left = game
        .left()
        .iter()
        .map(display_game)
        .collect::<Vec<_>>()
        .join(", ");
    let right = game
        .right()
        .iter()
        .map(display_game)
        .collect::<Vec<_>>()
        .join(", ");
    match (left.is_empty(), right.is_empty()) {
        (true, true) => "0".to_string(),
        (false, true) => format!("{{{left} |}}"),
        (true, false) => format!("{{| {right}}}"),
        (false, false) => format!("{{{left} | {right}}}"),
    }
}

fn structural_game_integer(game: &Game) -> Option<i128> {
    if game.left().is_empty() && game.right().is_empty() {
        return Some(0);
    }
    if game.left().len() == 1 && game.right().is_empty() {
        let value = structural_game_integer(&game.left()[0])?;
        return (value >= 0).then(|| value.checked_add(1)).flatten();
    }
    if game.left().is_empty() && game.right().len() == 1 {
        let value = structural_game_integer(&game.right()[0])?;
        return (value <= 0).then(|| value.checked_sub(1)).flatten();
    }
    None
}

fn structural_game_nimber(game: &Game) -> Option<u128> {
    if game.left().is_empty() && game.right().is_empty() {
        return Some(0);
    }
    if game.left().len() != game.right().len() {
        return None;
    }
    for (index, (left, right)) in game.left().iter().zip(game.right()).enumerate() {
        let expected = u128::try_from(index).ok()?;
        if structural_game_nimber(left)? != expected
            || structural_game_nimber(right)? != expected
            || !game_structural_eq_ordered(left, right)
        {
            return None;
        }
    }
    u128::try_from(game.left().len()).ok()
}

fn game_structural_eq_ordered(lhs: &Game, rhs: &Game) -> bool {
    lhs.left().len() == rhs.left().len()
        && lhs.right().len() == rhs.right().len()
        && lhs
            .left()
            .iter()
            .zip(rhs.left())
            .all(|(lhs, rhs)| game_structural_eq_ordered(lhs, rhs))
        && lhs
            .right()
            .iter()
            .zip(rhs.right())
            .all(|(lhs, rhs)| game_structural_eq_ordered(lhs, rhs))
}

fn append_game_spine(spine: &Game, tail: &Game) -> OghamResult<Game> {
    if spine.left().is_empty() && spine.right().is_empty() {
        return Ok(tail.clone());
    }
    if spine.left().len() == 1 && spine.right().len() == 1 {
        return Ok(Game::new(
            vec![spine.left()[0].clone()],
            vec![append_game_spine(&spine.right()[0], tail)?],
        ));
    }
    Err(OghamError::new(
        OghamErrorKind::Improper,
        Span::point(0),
        "left operand of `⧺` must be a finite proper spine",
    ))
}

fn build_game_form(left: Vec<GameElement>, right: Vec<GameElement>) -> OghamResult<GameElement> {
    if left
        .iter()
        .chain(&right)
        .all(|value| matches!(value, GameElement::Finite(_)))
    {
        let finite = |values: Vec<GameElement>| {
            values
                .into_iter()
                .map(|value| match value {
                    GameElement::Finite(game) => game,
                    GameElement::Graph(_) => unreachable!("checked above"),
                })
                .collect()
        };
        return Ok(GameElement::Finite(Game::new(finite(left), finite(right))));
    }
    materialize_regular_game(
        "",
        SymbolicGame::Form {
            left: left.into_iter().map(SymbolicGame::Value).collect(),
            right: right.into_iter().map(SymbolicGame::Value).collect(),
        },
    )
}

fn append_game_element(spine: &GameElement, tail: &GameElement) -> OghamResult<GameElement> {
    let GameElement::Finite(spine) = spine else {
        return Err(OghamError::new(
            OghamErrorKind::Improper,
            Span::point(0),
            "left operand of `⧺` is cyclic; the coinductive candidate is the left operand itself",
        ));
    };
    if let GameElement::Finite(tail) = tail {
        return append_game_spine(spine, tail).map(GameElement::Finite);
    }
    append_symbolic_spine(&spine_as_element(spine), SymbolicGame::Value(tail.clone()))
        .and_then(|value| materialize_regular_game("", value))
}

fn spine_as_element(game: &Game) -> GameElement {
    GameElement::Finite(game.clone())
}

fn append_symbolic_spine(spine: &GameElement, tail: SymbolicGame) -> OghamResult<SymbolicGame> {
    let GameElement::Finite(spine) = spine else {
        return Err(OghamError::new(
            OghamErrorKind::Improper,
            Span::point(0),
            "left operand of `⧺` must be a finite proper spine",
        ));
    };
    if spine.left().is_empty() && spine.right().is_empty() {
        return Ok(tail);
    }
    if spine.left().len() == 1 && spine.right().len() == 1 {
        return Ok(SymbolicGame::Form {
            left: vec![SymbolicGame::Value(GameElement::Finite(
                spine.left()[0].clone(),
            ))],
            right: vec![append_symbolic_spine(
                &GameElement::Finite(spine.right()[0].clone()),
                tail,
            )?],
        });
    }
    Err(OghamError::new(
        OghamErrorKind::Improper,
        Span::point(0),
        "left operand of `⧺` must be a finite proper spine",
    ))
}

fn materialize_regular_game(name: &str, root: SymbolicGame) -> OghamResult<GameElement> {
    if matches!(root, SymbolicGame::SelfRef) {
        return Err(unfounded_error(name));
    }
    if let SymbolicGame::Value(value) = root {
        return Ok(value);
    }
    let mut nodes = Vec::new();
    materialize_symbolic_node(&root, &mut nodes)?;
    let drawn = classify_regular_nodes(&nodes);
    Ok(GameElement::Graph(GraphRef {
        graph: Arc::new(RegularGameGraph {
            name: name.to_string(),
            nodes,
            drawn,
        }),
        node: 0,
    }))
}

fn materialize_symbolic_node(
    value: &SymbolicGame,
    nodes: &mut Vec<RegularGameNode>,
) -> OghamResult<usize> {
    let SymbolicGame::Form { left, right } = value else {
        return Err(OghamError::new(
            OghamErrorKind::Unfounded,
            Span::point(0),
            "an Element fixpoint must reduce to a brace constructor",
        ));
    };
    let index = nodes.len();
    nodes.push(RegularGameNode {
        left: Vec::new(),
        right: Vec::new(),
    });
    let left = left
        .iter()
        .map(|item| materialize_symbolic_edge(item, nodes))
        .collect::<OghamResult<_>>()?;
    let right = right
        .iter()
        .map(|item| materialize_symbolic_edge(item, nodes))
        .collect::<OghamResult<_>>()?;
    nodes[index] = RegularGameNode { left, right };
    Ok(index)
}

fn materialize_symbolic_edge(
    value: &SymbolicGame,
    nodes: &mut Vec<RegularGameNode>,
) -> OghamResult<RegularGameEdge> {
    match value {
        SymbolicGame::SelfRef => Ok(RegularGameEdge::Local(0)),
        SymbolicGame::Value(GameElement::Finite(game)) => Ok(RegularGameEdge::Finite(game.clone())),
        SymbolicGame::Value(GameElement::Graph(reference)) => {
            Ok(RegularGameEdge::External(reference.clone()))
        }
        SymbolicGame::Form { .. } => {
            materialize_symbolic_node(value, nodes).map(RegularGameEdge::Local)
        }
    }
}

#[derive(Clone)]
enum ClassificationPosition {
    Current(usize),
    External(GraphRef),
    Finite(Game),
}

fn classify_regular_nodes(nodes: &[RegularGameNode]) -> Vec<bool> {
    let mut positions = (0..nodes.len())
        .map(ClassificationPosition::Current)
        .collect::<Vec<_>>();
    let mut external = HashMap::new();
    let mut left = vec![Vec::new(); positions.len()];
    let mut right = vec![Vec::new(); positions.len()];
    let mut cursor = 0;
    while cursor < positions.len() {
        let (left_edges, right_edges) = match positions[cursor].clone() {
            ClassificationPosition::Current(node) => {
                (nodes[node].left.clone(), nodes[node].right.clone())
            }
            ClassificationPosition::External(reference) => {
                let node = &reference.graph.nodes[reference.node];
                let adapt = |edge: &RegularGameEdge| match edge {
                    RegularGameEdge::Local(node) => RegularGameEdge::External(GraphRef {
                        graph: reference.graph.clone(),
                        node: *node,
                    }),
                    edge => edge.clone(),
                };
                (
                    node.left.iter().map(adapt).collect(),
                    node.right.iter().map(adapt).collect(),
                )
            }
            ClassificationPosition::Finite(game) => (
                game.left()
                    .iter()
                    .cloned()
                    .map(RegularGameEdge::Finite)
                    .collect(),
                game.right()
                    .iter()
                    .cloned()
                    .map(RegularGameEdge::Finite)
                    .collect(),
            ),
        };
        left[cursor] = classification_edges(
            left_edges,
            &mut positions,
            &mut left,
            &mut right,
            &mut external,
        );
        right[cursor] = classification_edges(
            right_edges,
            &mut positions,
            &mut left,
            &mut right,
            &mut external,
        );
        cursor += 1;
    }
    let draw_set = LoopyPartizanGraph::new(left, right)
        .draw_set()
        .into_iter()
        .collect::<HashSet<_>>();
    (0..nodes.len())
        .map(|node| draw_set.contains(&node))
        .collect()
}

fn classification_edges(
    edges: Vec<RegularGameEdge>,
    positions: &mut Vec<ClassificationPosition>,
    left: &mut Vec<Vec<usize>>,
    right: &mut Vec<Vec<usize>>,
    external: &mut HashMap<GraphKey, usize>,
) -> Vec<usize> {
    edges
        .into_iter()
        .map(|edge| match edge {
            RegularGameEdge::Local(node) => node,
            RegularGameEdge::Finite(game) => {
                let index = positions.len();
                positions.push(ClassificationPosition::Finite(game));
                left.push(Vec::new());
                right.push(Vec::new());
                index
            }
            RegularGameEdge::External(reference) => {
                let key = graph_key(&reference);
                *external.entry(key).or_insert_with(|| {
                    let index = positions.len();
                    positions.push(ClassificationPosition::External(reference));
                    left.push(Vec::new());
                    right.push(Vec::new());
                    index
                })
            }
        })
        .collect()
}

fn game_options(element: &GameElement, left: bool) -> Vec<GameElement> {
    match element {
        GameElement::Finite(game) => {
            let options = if left { game.left() } else { game.right() };
            options.iter().cloned().map(GameElement::Finite).collect()
        }
        GameElement::Graph(reference) => {
            let node = &reference.graph.nodes[reference.node];
            let edges = if left { &node.left } else { &node.right };
            edges
                .iter()
                .map(|edge| match edge {
                    RegularGameEdge::Finite(game) => GameElement::Finite(game.clone()),
                    RegularGameEdge::Local(node) => GameElement::Graph(GraphRef {
                        graph: reference.graph.clone(),
                        node: *node,
                    }),
                    RegularGameEdge::External(reference) => GameElement::Graph(reference.clone()),
                })
                .collect()
        }
    }
}

fn game_element_drawn(element: &GameElement) -> bool {
    match element {
        GameElement::Finite(_) => false,
        GameElement::Graph(reference) => reference.graph.drawn[reference.node],
    }
}

fn game_element_regular_eq(lhs: &GameElement, rhs: &GameElement) -> bool {
    regular_eq_inner(lhs, rhs, &mut HashSet::new(), &mut HashSet::new())
}

fn regular_eq_inner(
    lhs: &GameElement,
    rhs: &GameElement,
    visited: &mut HashSet<GraphPair>,
    mixed: &mut HashSet<GraphKey>,
) -> bool {
    match (lhs, rhs) {
        (GameElement::Finite(lhs), GameElement::Finite(rhs)) => {
            game_structural_eq_ordered(lhs, rhs)
        }
        (GameElement::Graph(lhs), GameElement::Graph(rhs)) => {
            if !visited.insert((graph_key(lhs), graph_key(rhs))) {
                return true;
            }
            regular_options_eq(lhs, rhs, true, visited, mixed)
                && regular_options_eq(lhs, rhs, false, visited, mixed)
        }
        (GameElement::Graph(graph), GameElement::Finite(finite))
        | (GameElement::Finite(finite), GameElement::Graph(graph)) => {
            if !mixed.insert(graph_key(graph)) {
                return false;
            }
            let graph_value = GameElement::Graph(graph.clone());
            let finite_value = GameElement::Finite(finite.clone());
            let result = [true, false].into_iter().all(|left| {
                let graph_options = game_options(&graph_value, left);
                let finite_options = game_options(&finite_value, left);
                graph_options.len() == finite_options.len()
                    && graph_options
                        .iter()
                        .zip(&finite_options)
                        .all(|(lhs, rhs)| regular_eq_inner(lhs, rhs, visited, mixed))
            });
            mixed.remove(&graph_key(graph));
            result
        }
    }
}

fn regular_options_eq(
    lhs: &GraphRef,
    rhs: &GraphRef,
    left: bool,
    visited: &mut HashSet<GraphPair>,
    mixed: &mut HashSet<GraphKey>,
) -> bool {
    let lhs = game_options(&GameElement::Graph(lhs.clone()), left);
    let rhs = game_options(&GameElement::Graph(rhs.clone()), left);
    lhs.len() == rhs.len()
        && lhs
            .iter()
            .zip(&rhs)
            .all(|(lhs, rhs)| regular_eq_inner(lhs, rhs, visited, mixed))
}

fn graph_key(reference: &GraphRef) -> GraphKey {
    (Arc::as_ptr(&reference.graph) as usize, reference.node)
}

fn game_mu_call_key(name: &str, body: &Expr, args: &[Value<GameElement>]) -> String {
    let args = args
        .iter()
        .map(|arg| match arg {
            Value::Element(GameElement::Finite(game)) => format!("e:{}", display_game(game)),
            Value::Element(GameElement::Graph(reference)) => {
                let (graph, node) = graph_key(reference);
                format!("g:{graph}:{node}")
            }
            Value::Index(value) => format!("i:{value}"),
            Value::Bool(value) => format!("b:{value}"),
            Value::Function(_) => "f".to_string(),
        })
        .collect::<Vec<_>>()
        .join("|");
    format!("{name}:{}@{args}", super::unparse::unparse_expr(body))
}

fn unfounded_error(name: &str) -> OghamError {
    OghamError::new(
        OghamErrorKind::Unfounded,
        Span::point(0),
        format!("Element fixpoint `{name}` is not guarded by a brace constructor"),
    )
}

fn loopy_error(message: &str) -> OghamError {
    OghamError::new(OghamErrorKind::Loopy, Span::point(0), message)
}

fn game_option_index(name: &str, index: i128) -> OghamResult<usize> {
    usize::try_from(index).map_err(|_| domain(format!("{name} option index must be non-negative")))
}

fn game_wrong_world(message: &str) -> OghamError {
    OghamError::new(OghamErrorKind::WrongWorld, Span::point(0), message)
}

fn refine_game_binder_sorts(
    expr: &Expr,
    binders: &[String],
    sorts: &mut [Sort],
    env: &BTreeMap<String, Value<GameElement>>,
) {
    match expr {
        Expr::Relation { lhs, rhs, .. } => {
            if game_known_sort(lhs, env) == Some(Sort::Index) {
                mark_game_expr_sort(rhs, Sort::Index, binders, sorts);
            }
            if game_known_sort(rhs, env) == Some(Sort::Index) {
                mark_game_expr_sort(lhs, Sort::Index, binders, sorts);
            }
            refine_game_binder_sorts(lhs, binders, sorts, env);
            refine_game_binder_sorts(rhs, binders, sorts, env);
        }
        Expr::Binary {
            op: BinaryOp::At,
            lhs,
            rhs,
        } => {
            if let Expr::Ident(name) = &**lhs {
                if let Some(Value::Function(function)) = env.get(name) {
                    let args: Vec<&Expr> = match &**rhs {
                        Expr::Tuple(items) => items.iter().collect(),
                        item => vec![item],
                    };
                    for (arg, binder) in args.into_iter().zip(&function.binders) {
                        mark_game_expr_sort(arg, binder.sort, binders, sorts);
                    }
                }
            }
            refine_game_binder_sorts(lhs, binders, sorts, env);
            refine_game_binder_sorts(rhs, binders, sorts, env);
        }
        Expr::Block { bindings, body } => {
            for binding in bindings {
                refine_game_binder_sorts(&binding.expr, binders, sorts, env);
            }
            refine_game_binder_sorts(body, binders, sorts, env);
        }
        Expr::Vector(items) | Expr::Tuple(items) => {
            for item in items {
                refine_game_binder_sorts(item, binders, sorts, env);
            }
        }
        Expr::GameForm { left, right } => {
            for item in left.iter().chain(right) {
                refine_game_binder_sorts(item, binders, sorts, env);
            }
        }
        Expr::Lambda { body, .. } | Expr::Factorial(body) | Expr::Unary { expr: body, .. } => {
            refine_game_binder_sorts(body, binders, sorts, env);
        }
        Expr::Call { args, .. } => {
            for arg in args {
                refine_game_binder_sorts(arg, binders, sorts, env);
            }
        }
        Expr::Binary { lhs, rhs, .. } => {
            refine_game_binder_sorts(lhs, binders, sorts, env);
            refine_game_binder_sorts(rhs, binders, sorts, env);
        }
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            refine_game_binder_sorts(cond, binders, sorts, env);
            refine_game_binder_sorts(then_expr, binders, sorts, env);
            refine_game_binder_sorts(else_expr, binders, sorts, env);
        }
        Expr::Int(_)
        | Expr::Bool(_)
        | Expr::Star(_)
        | Expr::Omega
        | Expr::Blade(_)
        | Expr::Ident(_) => {}
    }
}

fn mark_game_expr_sort(expr: &Expr, sort: Sort, binders: &[String], sorts: &mut [Sort]) {
    match expr {
        Expr::Ident(name) => {
            if let Some(index) = binders.iter().position(|binder| binder == name) {
                sorts[index] = sort;
            }
        }
        Expr::Unary { expr, .. } => mark_game_expr_sort(expr, sort, binders, sorts),
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Pow,
            lhs,
            rhs,
        } => {
            mark_game_expr_sort(lhs, sort, binders, sorts);
            mark_game_expr_sort(rhs, sort, binders, sorts);
        }
        _ => {}
    }
}

fn game_known_sort(expr: &Expr, env: &BTreeMap<String, Value<GameElement>>) -> Option<Sort> {
    match expr {
        Expr::Call { name, .. } if matches!(name.as_str(), "nleft" | "nright" | "dim" | "deg") => {
            Some(Sort::Index)
        }
        Expr::Call { name, .. } if name == "drawn" => Some(Sort::Bool),
        Expr::Binary {
            op: BinaryOp::At,
            lhs,
            ..
        } => game_function_expr_return_sort(lhs, env),
        Expr::Bool(_)
        | Expr::Relation { .. }
        | Expr::Unary {
            op: UnaryOp::Not, ..
        }
        | Expr::Binary {
            op: BinaryOp::And | BinaryOp::Or,
            ..
        } => Some(Sort::Bool),
        _ => None,
    }
}

fn game_function_expr_return_sort(
    expr: &Expr,
    env: &BTreeMap<String, Value<GameElement>>,
) -> Option<Sort> {
    match expr {
        Expr::Ident(name) => match env.get(name) {
            Some(Value::Function(function)) => Some(function.ret),
            _ => None,
        },
        Expr::Block { bindings, body } => {
            let Expr::Ident(name) = &**body else {
                return None;
            };
            let binding = bindings
                .iter()
                .rev()
                .find(|binding| &binding.name == name)?;
            let Expr::Lambda { body, .. } = &binding.expr else {
                return None;
            };
            game_return_sort_hint(
                body,
                env,
                binding.recursive.then_some(binding.name.as_str()),
            )
        }
        _ => None,
    }
}

fn game_return_sort_hint(
    body: &Expr,
    env: &BTreeMap<String, Value<GameElement>>,
    mu_name: Option<&str>,
) -> Option<Sort> {
    if bool_shaped(body) {
        return Some(Sort::Bool);
    }
    if let Some(name) = mu_name {
        if is_game_index_counter(name, body) {
            return Some(Sort::Index);
        }
    }
    match body {
        Expr::Binary {
            op: BinaryOp::At,
            lhs,
            ..
        } => game_function_expr_return_sort(lhs, env),
        Expr::Call { name, .. } if matches!(name.as_str(), "nleft" | "nright" | "dim" | "deg") => {
            Some(Sort::Index)
        }
        Expr::Block { bindings, body } => {
            let mut local_returns = BTreeMap::new();
            for binding in bindings {
                if let Expr::Lambda { body, .. } = &binding.expr {
                    let hint = if bool_shaped(body) {
                        Some(Sort::Bool)
                    } else if binding.recursive && is_game_index_counter(&binding.name, body) {
                        Some(Sort::Index)
                    } else {
                        game_return_sort_hint(body, env, None)
                    };
                    if let Some(sort) = hint {
                        local_returns.insert(binding.name.as_str(), sort);
                    }
                }
            }
            if let Expr::Binary {
                op: BinaryOp::At,
                lhs,
                ..
            } = &**body
            {
                if let Expr::Ident(name) = &**lhs {
                    return local_returns.get(name.as_str()).copied();
                }
            }
            game_return_sort_hint(body, env, None)
        }
        Expr::Ternary {
            then_expr,
            else_expr,
            ..
        } => {
            let lhs = game_return_sort_hint(then_expr, env, mu_name);
            let rhs = game_return_sort_hint(else_expr, env, mu_name);
            (lhs == rhs).then_some(lhs).flatten()
        }
        _ => game_known_sort(body, env),
    }
}

fn is_game_index_counter(name: &str, expr: &Expr) -> bool {
    contains_game_self_call(name, expr) && contains_game_unit_step(expr)
}

fn contains_game_self_call(name: &str, expr: &Expr) -> bool {
    match expr {
        Expr::Binary {
            op: BinaryOp::At,
            lhs,
            rhs,
        } => {
            matches!(&**lhs, Expr::Ident(callee) if callee == name)
                || contains_game_self_call(name, lhs)
                || contains_game_self_call(name, rhs)
        }
        Expr::Block { bindings, body } => {
            bindings
                .iter()
                .any(|binding| contains_game_self_call(name, &binding.expr))
                || contains_game_self_call(name, body)
        }
        Expr::Vector(items) | Expr::Tuple(items) => {
            items.iter().any(|item| contains_game_self_call(name, item))
        }
        Expr::GameForm { left, right } => left
            .iter()
            .chain(right)
            .any(|item| contains_game_self_call(name, item)),
        Expr::Lambda { body, .. } | Expr::Factorial(body) | Expr::Unary { expr: body, .. } => {
            contains_game_self_call(name, body)
        }
        Expr::Call { args, .. } => args.iter().any(|arg| contains_game_self_call(name, arg)),
        Expr::Binary { lhs, rhs, .. } | Expr::Relation { lhs, rhs, .. } => {
            contains_game_self_call(name, lhs) || contains_game_self_call(name, rhs)
        }
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            contains_game_self_call(name, cond)
                || contains_game_self_call(name, then_expr)
                || contains_game_self_call(name, else_expr)
        }
        Expr::Int(_)
        | Expr::Bool(_)
        | Expr::Star(_)
        | Expr::Omega
        | Expr::Blade(_)
        | Expr::Ident(_) => false,
    }
}

fn contains_game_unit_step(expr: &Expr) -> bool {
    match expr {
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub,
            lhs,
            rhs,
        } if (matches!(&**lhs, Expr::Ident(_)) && matches!(&**rhs, Expr::Int(1)))
            || matches!(&**lhs, Expr::Int(1)) =>
        {
            true
        }
        Expr::Block { bindings, body } => {
            bindings
                .iter()
                .any(|binding| contains_game_unit_step(&binding.expr))
                || contains_game_unit_step(body)
        }
        Expr::Vector(items) | Expr::Tuple(items) => items.iter().any(contains_game_unit_step),
        Expr::GameForm { left, right } => left.iter().chain(right).any(contains_game_unit_step),
        Expr::Lambda { body, .. } | Expr::Factorial(body) | Expr::Unary { expr: body, .. } => {
            contains_game_unit_step(body)
        }
        Expr::Call { args, .. } => args.iter().any(contains_game_unit_step),
        Expr::Binary { lhs, rhs, .. } | Expr::Relation { lhs, rhs, .. } => {
            contains_game_unit_step(lhs) || contains_game_unit_step(rhs)
        }
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            contains_game_unit_step(cond)
                || contains_game_unit_step(then_expr)
                || contains_game_unit_step(else_expr)
        }
        Expr::Int(_)
        | Expr::Bool(_)
        | Expr::Star(_)
        | Expr::Omega
        | Expr::Blade(_)
        | Expr::Ident(_) => false,
    }
}

fn contains_game_binder_unit_step(binder: &str, expr: &Expr) -> bool {
    match expr {
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub,
            lhs,
            rhs,
        } if matches!(&**lhs, Expr::Ident(name) if name == binder)
            && matches!(&**rhs, Expr::Int(1)) =>
        {
            true
        }
        Expr::Block { bindings, body } => {
            bindings
                .iter()
                .any(|binding| contains_game_binder_unit_step(binder, &binding.expr))
                || contains_game_binder_unit_step(binder, body)
        }
        Expr::Vector(items) | Expr::Tuple(items) => items
            .iter()
            .any(|item| contains_game_binder_unit_step(binder, item)),
        Expr::GameForm { left, right } => left
            .iter()
            .chain(right)
            .any(|item| contains_game_binder_unit_step(binder, item)),
        Expr::Lambda { body, .. } | Expr::Factorial(body) | Expr::Unary { expr: body, .. } => {
            contains_game_binder_unit_step(binder, body)
        }
        Expr::Call { args, .. } => args
            .iter()
            .any(|arg| contains_game_binder_unit_step(binder, arg)),
        Expr::Binary { lhs, rhs, .. } | Expr::Relation { lhs, rhs, .. } => {
            contains_game_binder_unit_step(binder, lhs)
                || contains_game_binder_unit_step(binder, rhs)
        }
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            contains_game_binder_unit_step(binder, cond)
                || contains_game_binder_unit_step(binder, then_expr)
                || contains_game_binder_unit_step(binder, else_expr)
        }
        Expr::Int(_)
        | Expr::Bool(_)
        | Expr::Star(_)
        | Expr::Omega
        | Expr::Blade(_)
        | Expr::Ident(_) => false,
    }
}

struct PolyRuntime<S: PolyWorldCoeff> {
    name: &'static str,
    env: BTreeMap<String, Value<Poly<S>>>,
    fuel_budget: u128,
    fuel_remaining: u128,
    recursion_depth: u128,
    validation_stub_names: BTreeSet<String>,
}

impl<S: PolyWorldCoeff> PolyRuntime<S> {
    fn new(name: &'static str) -> Self {
        PolyRuntime {
            name,
            env: BTreeMap::new(),
            fuel_budget: DEFAULT_FUEL,
            fuel_remaining: DEFAULT_FUEL,
            recursion_depth: 0,
            validation_stub_names: BTreeSet::new(),
        }
    }

    fn reset_fuel(&mut self) {
        self.fuel_remaining = self.fuel_budget;
        self.recursion_depth = 0;
    }

    fn set_fuel_budget(&mut self, budget: u128) {
        self.fuel_budget = budget;
        self.reset_fuel();
    }

    fn eval_statement(&mut self, stmt: &Statement) -> OghamResult<Option<String>> {
        match stmt {
            Statement::Binding {
                name,
                expr,
                recursive,
            } => {
                self.bind_name(name, expr, *recursive)?;
                Ok(None)
            }
            Statement::Expr(expr) => Ok(Some(display_value(&self.eval_value(expr)?))),
            Statement::Seq { bindings, tail } => {
                for binding in bindings {
                    self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
                }
                self.eval_statement(tail)
            }
        }
    }

    fn bind_name(&mut self, name: &str, expr: &Expr, recursive: bool) -> OghamResult<()> {
        if name == "t" || reserved_function_binder(name) {
            return Err(OghamError::new(
                OghamErrorKind::Reserved,
                Span::point(0),
                format!("`{name}` is reserved in the `{}` world", self.name),
            ));
        }
        if recursive && contains_free_name(expr, name) {
            let Expr::Lambda { binders, body } = expr else {
                return Err(element_fixpoint_error(name));
            };
            let function = self.close_function(
                binders.clone(),
                body.as_ref().clone(),
                Some(name.to_string()),
            )?;
            self.env.insert(name.to_string(), Value::Function(function));
            return Ok(());
        }
        let value = self.eval_value(expr)?;
        self.env.insert(name.to_string(), value);
        Ok(())
    }

    fn eval_block(&mut self, bindings: &[Binding], body: &Expr) -> OghamResult<Value<Poly<S>>> {
        let saved = self.env.clone();
        let result = (|| {
            for binding in bindings {
                self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
            }
            self.eval_value(body)
        })();
        self.env = saved;
        result
    }

    fn summary(&self) -> String {
        self.name.to_string()
    }

    fn env_summary(&self) -> Vec<String> {
        self.env
            .iter()
            .map(|(name, value)| format!("{name} := {}", display_value(value)))
            .collect()
    }

    fn eval_value(&mut self, expr: &Expr) -> OghamResult<Value<Poly<S>>> {
        match expr {
            Expr::Bool(value) => Ok(Value::Bool(*value)),
            Expr::Tuple(_) => Err(fn_sort_error()),
            Expr::Block { bindings, body } => self.eval_block(bindings, body),
            Expr::Lambda { binders, body } => self
                .close_function(binders.clone(), body.as_ref().clone(), None)
                .map(Value::Function),
            Expr::Ident(name) => {
                if name == "t" {
                    Ok(Value::Element(Poly::t()))
                } else if let Some(value) = self.env.get(name) {
                    Ok(value.clone())
                } else {
                    Err(unbound_error(name))
                }
            }
            Expr::Relation { op, lhs, rhs } => Ok(Value::Bool(self.eval_relation(*op, lhs, rhs)?)),
            Expr::Unary {
                op: UnaryOp::Not,
                expr,
            } => Ok(Value::Bool(!self.eval_bool(expr)?)),
            Expr::Binary {
                op: BinaryOp::And,
                lhs,
                rhs,
            } => {
                let lhs = self.eval_bool(lhs)?;
                if self.static_sort(rhs)? != Sort::Bool {
                    return Err(bool_sort_error());
                }
                if !lhs {
                    return Ok(Value::Bool(false));
                }
                Ok(Value::Bool(self.eval_bool(rhs)?))
            }
            Expr::Binary {
                op: BinaryOp::Or,
                lhs,
                rhs,
            } => {
                let lhs = self.eval_bool(lhs)?;
                if self.static_sort(rhs)? != Sort::Bool {
                    return Err(bool_sort_error());
                }
                if lhs {
                    return Ok(Value::Bool(true));
                }
                Ok(Value::Bool(self.eval_bool(rhs)?))
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                let then_sort = self.static_sort(then_expr)?;
                let else_sort = self.static_sort(else_expr)?;
                if then_sort != else_sort {
                    return Err(sort_mismatch(then_sort, else_sort));
                }
                if self.eval_bool(cond)? {
                    self.eval_value(then_expr)
                } else {
                    self.eval_value(else_expr)
                }
            }
            Expr::Binary {
                op: BinaryOp::At,
                lhs,
                rhs,
            } => self.eval_at(lhs, rhs),
            _ if expression_is_index(expr) => Ok(Value::Index(self.eval_index(expr)?)),
            _ => match self.eval_element(expr) {
                Ok(value) => Ok(Value::Element(value)),
                Err(err) if err.kind == OghamErrorKind::IndexSort => {
                    Ok(Value::Index(self.eval_index(expr)?))
                }
                Err(err) => Err(err),
            },
        }
    }

    fn eval_bool(&mut self, expr: &Expr) -> OghamResult<bool> {
        match self.eval_value(expr)? {
            Value::Bool(value) => Ok(value),
            Value::Element(_) | Value::Index(_) => Err(bool_sort_error()),
            Value::Function(_) => Err(fn_sort_error()),
        }
    }

    fn eval_at(&mut self, lhs: &Expr, rhs: &Expr) -> OghamResult<Value<Poly<S>>> {
        let lhs_v = self.eval_value(lhs)?;
        match lhs_v {
            Value::Function(function) => {
                if let Expr::Tuple(items) = rhs {
                    return self.apply_function_exprs(&function, items);
                }
                match self.eval_value(rhs)? {
                    Value::Function(rhs_fn) => self
                        .compose_functions(&function, &rhs_fn)
                        .map(Value::Function),
                    _ => self.apply_function_exprs(&function, std::slice::from_ref(rhs)),
                }
            }
            Value::Element(lhs_e) => match self.eval_value(rhs)? {
                Value::Element(rhs_e) => Ok(Value::Element(lhs_e.compose(&rhs_e))),
                Value::Function(rhs_fn) => self
                    .compose_element_with_function(lhs, &rhs_fn)
                    .map(Value::Function),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
            },
            Value::Index(_) => Err(index_sort_error()),
            Value::Bool(_) => Err(bool_sort_error()),
        }
    }

    fn compose_element_with_function(
        &mut self,
        lhs: &Expr,
        rhs: &FunctionValue,
    ) -> OghamResult<FunctionValue> {
        let mut replacements = BTreeMap::new();
        replacements.insert("t".to_string(), rhs.body.clone());
        let body = beta_normalize(substitute_names(lhs, &replacements))?;
        let function = FunctionValue {
            binders: rhs.binders.clone(),
            body,
            ret: Sort::Element,
            mu_name: None,
        };
        self.validate_function_body(&function)?;
        Ok(function)
    }

    fn apply_function(
        &mut self,
        function: &FunctionValue,
        args: Vec<Value<Poly<S>>>,
    ) -> OghamResult<Value<Poly<S>>> {
        if args.len() != function.binders.len() {
            return Err(OghamError::new(
                OghamErrorKind::Arity,
                Span::point(0),
                format!(
                    "function expects {} argument(s), got {}",
                    function.binders.len(),
                    args.len()
                ),
            ));
        }
        consume_fuel(function, &mut self.fuel_remaining, self.fuel_budget)?;
        let mut replacements = BTreeMap::new();
        for (binder, arg) in function.binders.iter().zip(args.iter()) {
            ensure_value_sort(arg, binder.sort)?;
            replacements.insert(binder.name.clone(), value_to_expr(arg)?);
        }
        let body = substitute_names(&function.body, &replacements);
        let recursive_frame = enter_recursion_frame(
            function,
            &mut self.recursion_depth,
            self.fuel_remaining,
            self.fuel_budget,
        )?;
        let previous = function.mu_name.as_ref().map(|name| {
            self.env
                .insert(name.clone(), Value::Function(function.clone()))
        });
        let result = self.eval_value(&body);
        if let Some(name) = &function.mu_name {
            if let Some(previous) = previous.flatten() {
                self.env.insert(name.clone(), previous);
            } else {
                self.env.remove(name);
            }
        }
        leave_recursion_frame(recursive_frame, &mut self.recursion_depth);
        result
    }

    fn apply_function_exprs(
        &mut self,
        function: &FunctionValue,
        args: &[Expr],
    ) -> OghamResult<Value<Poly<S>>> {
        if args.len() != function.binders.len() {
            return Err(OghamError::new(
                OghamErrorKind::Arity,
                Span::point(0),
                format!(
                    "function expects {} argument(s), got {}",
                    function.binders.len(),
                    args.len()
                ),
            ));
        }
        let values = function
            .binders
            .iter()
            .zip(args)
            .map(|(binder, arg)| self.eval_arg_for_sort(arg, binder.sort))
            .collect::<OghamResult<Vec<_>>>()?;
        self.apply_function(function, values)
    }

    fn eval_arg_for_sort(&mut self, expr: &Expr, sort: Sort) -> OghamResult<Value<Poly<S>>> {
        match sort {
            Sort::Element => self.eval_element(expr).map(Value::Element),
            Sort::Index => self.eval_index(expr).map(Value::Index),
            Sort::Bool => self.eval_bool(expr).map(Value::Bool),
        }
    }

    fn compose_functions(
        &mut self,
        lhs: &FunctionValue,
        rhs: &FunctionValue,
    ) -> OghamResult<FunctionValue> {
        if lhs.binders.len() != 1 {
            return Err(OghamError::new(
                OghamErrorKind::Arity,
                Span::point(0),
                "function composition needs a unary head",
            ));
        }
        if lhs.binders[0].sort != rhs.ret {
            return Err(sort_mismatch(lhs.binders[0].sort, rhs.ret));
        }
        let mut replacements = BTreeMap::new();
        replacements.insert(lhs.binders[0].name.clone(), rhs.body.clone());
        let body = beta_normalize(substitute_names(&lhs.body, &replacements))?;
        let function = FunctionValue {
            binders: rhs.binders.clone(),
            body,
            ret: lhs.ret,
            mu_name: None,
        };
        self.validate_function_body(&function)?;
        Ok(function)
    }

    fn close_function(
        &mut self,
        binders: Vec<String>,
        body: Expr,
        mu_name: Option<String>,
    ) -> OghamResult<FunctionValue> {
        check_binders(&binders, |name| {
            name == "t" || reserved_function_binder(name)
        })
        .map_err(|err| {
            if err.kind == OghamErrorKind::Shadow && err.message.contains("`t`") {
                err.with_hint("`t` is the indeterminate here; `5⋅t + 1` is already a function")
            } else {
                err
            }
        })?;
        let mut bound: BTreeSet<String> = binders.iter().cloned().collect();
        bound.extend(mu_name.iter().cloned());
        bound.extend(self.validation_stub_names.iter().cloned());
        let substituted = substitute_env(&body, &bound, &self.env)?;
        let body = beta_normalize(substituted)?;
        let (binder_sorts, ret) = infer_function_signature(&body, &binders)?;
        let function = FunctionValue {
            binders: binders
                .into_iter()
                .zip(binder_sorts)
                .map(|(name, sort)| Binder { name, sort })
                .collect(),
            body,
            ret,
            mu_name,
        };
        if let Some(name) = &function.mu_name {
            let stub = validation_stub(&function, self.sample_expr(function.ret)?);
            let previous = self.env.insert(name.clone(), Value::Function(stub));
            self.validation_stub_names.insert(name.clone());
            let validation = self.validate_function_body(&function);
            self.validation_stub_names.remove(name);
            if let Some(previous) = previous {
                self.env.insert(name.clone(), previous);
            } else {
                self.env.remove(name);
            }
            validation?;
        } else {
            self.validate_function_body(&function)?;
        }
        Ok(function)
    }

    fn validate_function_body(&mut self, function: &FunctionValue) -> OghamResult<()> {
        let mut replacements = BTreeMap::new();
        for binder in &function.binders {
            replacements.insert(binder.name.clone(), self.sample_expr(binder.sort)?);
        }
        let sampled = substitute_names(&function.body, &replacements);
        self.validate_all(&sampled)
    }

    fn validate_all(&mut self, expr: &Expr) -> OghamResult<()> {
        match expr {
            Expr::Lambda { .. } => return Err(fn_sort_error()),
            Expr::Block { bindings, body } => {
                let saved = self.env.clone();
                let saved_validation_stubs = self.validation_stub_names.clone();
                let result = (|| {
                    for binding in bindings {
                        if !matches!(binding.expr, Expr::Lambda { .. }) {
                            self.validate_all(&binding.expr)?;
                        }
                        self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
                        if let Some(Value::Function(function)) =
                            self.env.get(&binding.name).cloned()
                        {
                            let stub = validation_stub(&function, self.sample_expr(function.ret)?);
                            self.env.insert(binding.name.clone(), Value::Function(stub));
                            self.validation_stub_names.insert(binding.name.clone());
                        }
                    }
                    self.validate_all(body)
                })();
                self.env = saved;
                self.validation_stub_names = saved_validation_stubs;
                result?;
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.validate_all(cond)?;
                self.validate_all(then_expr)?;
                self.validate_all(else_expr)?;
            }
            Expr::Binary {
                op: BinaryOp::And | BinaryOp::Or,
                lhs,
                rhs,
            } => {
                self.validate_all(lhs)?;
                self.validate_all(rhs)?;
            }
            _ => {}
        }
        ignore_static_partiality(self.eval_value(expr))
    }

    fn sample_expr(&self, sort: Sort) -> OghamResult<Expr> {
        match sort {
            Sort::Element => parse_display_expr(&Poly::<S>::one().to_string()),
            Sort::Index => Ok(Expr::Int(1)),
            Sort::Bool => Ok(Expr::Bool(true)),
        }
    }
    fn static_sort(&self, expr: &Expr) -> OghamResult<Sort> {
        static_sort(expr, &self.env, true)
    }

    fn eval_relation(&mut self, op: RelOp, lhs: &Expr, rhs: &Expr) -> OghamResult<bool> {
        if op == RelOp::Equiv {
            return Err(game_only_error("`≡`"));
        }
        if !bool_shaped(lhs)
            && !bool_shaped(rhs)
            && (expression_is_index(lhs) || expression_is_index(rhs))
        {
            let lhs = self.eval_index(lhs)?;
            let rhs = self.eval_index(rhs)?;
            return ordered_relation(op, lhs.cmp(&rhs));
        }
        let lhs_v = self.eval_value(lhs)?;
        let rhs_v = self.eval_value(rhs)?;
        match (lhs_v, rhs_v) {
            (Value::Function(_), _) | (_, Value::Function(_)) => Err(fn_sort_error()),
            (Value::Bool(lhs), Value::Bool(rhs)) => {
                if op == RelOp::Eq {
                    Ok(lhs == rhs)
                } else {
                    Err(bool_sort_error())
                }
            }
            (Value::Bool(_), _) | (_, Value::Bool(_)) => Err(bool_sort_error()),
            (Value::Index(lhs), Value::Index(rhs)) => ordered_relation(op, lhs.cmp(&rhs)),
            (Value::Index(_), _) | (_, Value::Index(_)) => Err(index_sort_error()),
            (Value::Element(lhs), Value::Element(rhs)) => {
                if op == RelOp::Eq {
                    Ok(lhs == rhs)
                } else {
                    Err(no_order_error())
                }
            }
        }
    }

    fn eval_element(&mut self, expr: &Expr) -> OghamResult<Poly<S>> {
        match expr {
            Expr::Bool(_) => Err(bool_sort_error()),
            Expr::GameForm { .. } => Err(game_only_error("game forms")),
            Expr::Int(n) => Ok(Poly::constant(S::bare_int(*n, Span::point(0))?)),
            Expr::Star(star) => Ok(Poly::constant(S::star(star, Span::point(0))?)),
            Expr::Omega => Ok(Poly::constant(S::omega(Span::point(0))?)),
            Expr::Blade(_) | Expr::Vector(_) => Err(OghamError::new(
                OghamErrorKind::WrongWorld,
                Span::point(0),
                "function-shaped worlds do not have Clifford blades or vectors",
            )),
            Expr::Ident(name) => {
                if name == "t" {
                    Ok(Poly::t())
                } else if let Some(value) = self.env.get(name) {
                    match value {
                        Value::Element(value) => Ok(value.clone()),
                        Value::Index(_) => Err(index_sort_error()),
                        Value::Bool(_) => Err(bool_sort_error()),
                        Value::Function(_) => Err(fn_sort_error()),
                    }
                } else {
                    Err(unbound_error(name))
                }
            }
            Expr::Tuple(_) | Expr::Lambda { .. } => Err(fn_sort_error()),
            Expr::Block { bindings, body } => match self.eval_block(bindings, body)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Call { name, args } => self.eval_call(name, args),
            Expr::Factorial(expr) => {
                let n = self.eval_index(expr)?;
                Ok(Poly::constant(S::factorial(n, Span::point(0))?))
            }
            Expr::Unary { op, expr } => {
                let value = self.eval_element(expr)?;
                match op {
                    UnaryOp::Neg => Ok(value.neg()),
                    UnaryOp::Inv => self.inverse_element(&value),
                    UnaryOp::Not => Err(bool_sort_error()),
                }
            }
            Expr::Binary {
                op: BinaryOp::At, ..
            } => match self.eval_value(expr)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Binary { op, lhs, rhs } => self.eval_binary(*op, lhs, rhs),
            Expr::Ternary { .. } => match self.eval_value(expr)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Relation { .. } => Err(OghamError::new(
                OghamErrorKind::BoolSort,
                Span::point(0),
                "relation result is Bool, not Element",
            )),
        }
    }

    fn eval_binary(&mut self, op: BinaryOp, lhs: &Expr, rhs: &Expr) -> OghamResult<Poly<S>> {
        if op == BinaryOp::Append {
            return Err(game_only_error("`⧺`"));
        }
        if op == BinaryOp::Pow {
            return self.eval_power(lhs, rhs);
        }
        if matches!(op, BinaryOp::And | BinaryOp::Or) {
            return Err(bool_sort_error());
        }
        let lhs_v = self.eval_element(lhs)?;
        let rhs_v = self.eval_element(rhs)?;
        match op {
            BinaryOp::Add => Ok(lhs_v.add(&rhs_v)),
            BinaryOp::Sub => Ok(lhs_v.sub(&rhs_v)),
            BinaryOp::Mul => Ok(lhs_v.mul(&rhs_v)),
            BinaryOp::Div => poly_exact_div::<S>(&lhs_v, &rhs_v, Span::point(0)),
            BinaryOp::Rem => poly_rem::<S>(&lhs_v, &rhs_v, Span::point(0)),
            BinaryOp::At => Ok(lhs_v.compose(&rhs_v)),
            BinaryOp::Wedge => Err(OghamError::new(
                OghamErrorKind::WrongWorld,
                Span::point(0),
                "wedge product belongs to Clifford worlds",
            )),
            BinaryOp::Pow | BinaryOp::And | BinaryOp::Or | BinaryOp::Append => unreachable!(),
        }
    }

    fn eval_power(&mut self, lhs: &Expr, rhs: &Expr) -> OghamResult<Poly<S>> {
        let base = self.eval_element(lhs)?;
        let exp = self.eval_index(rhs).map_err(|err| {
            if err.kind == OghamErrorKind::IndexSort {
                exp_sort_error()
            } else {
                err
            }
        })?;
        if exp < 0 {
            let inv = self.inverse_element(&base)?;
            let k = exp
                .checked_neg()
                .and_then(|v| u128::try_from(v).ok())
                .ok_or_else(|| overflow("negative exponent magnitude exceeds u128"))?;
            Ok(pow_poly(&inv, k))
        } else {
            let k = u128::try_from(exp).map_err(|_| overflow("exponent exceeds u128"))?;
            Ok(pow_poly(&base, k))
        }
    }

    fn eval_call(&mut self, name: &str, args: &[Expr]) -> OghamResult<Poly<S>> {
        match name {
            "coef" | "dim" => Err(array_world_error(name)),
            "deg" => Err(index_sort_error().with_hint("`deg` returns an Index")),
            "gcd" => {
                expect_arity(name, args, 2)?;
                let lhs = self.eval_element(&args[0])?;
                let rhs = self.eval_element(&args[1])?;
                S::gcd_poly(&lhs, &rhs, Span::point(0))
            }
            _ => Err(OghamError::new(
                OghamErrorKind::UnknownFn,
                Span::point(0),
                format!("unknown function `{name}`"),
            )),
        }
    }

    fn eval_index(&mut self, expr: &Expr) -> OghamResult<i128> {
        match expr {
            Expr::Int(n) => u128_to_i128(*n),
            Expr::Bool(_) => Err(bool_sort_error()),
            Expr::Tuple(_) | Expr::Lambda { .. } => Err(fn_sort_error()),
            Expr::Block { bindings, body } => match self.eval_block(bindings, body)? {
                Value::Index(value) => Ok(value),
                Value::Element(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Ident(name) => match self.env.get(name) {
                Some(Value::Index(value)) => Ok(*value),
                Some(Value::Element(_)) => Err(index_sort_error()),
                Some(Value::Bool(_)) => Err(bool_sort_error()),
                Some(Value::Function(_)) => Err(fn_sort_error()),
                None => Err(unbound_error(name)),
            },
            Expr::Call { name, .. } if name == "dim" => Err(array_world_error(name)),
            Expr::Call { name, args } if name == "deg" => {
                expect_arity(name, args, 1)?;
                let value = self.eval_element(&args[0])?;
                let degree = value.degree().ok_or_else(|| {
                    OghamError::new(
                        OghamErrorKind::Domain,
                        Span::point(0),
                        "degree of the zero polynomial is undefined",
                    )
                })?;
                i128::try_from(degree).map_err(|_| overflow("polynomial degree exceeds i128"))
            }
            Expr::Unary {
                op: UnaryOp::Neg,
                expr,
            } => self
                .eval_index(expr)?
                .checked_neg()
                .ok_or_else(|| overflow("index negation overflowed i128")),
            Expr::Unary {
                op: UnaryOp::Inv, ..
            } => Err(index_sort_error()),
            Expr::Unary {
                op: UnaryOp::Not, ..
            } => Err(bool_sort_error()),
            Expr::Binary { op, lhs, rhs } => {
                let lhs = self.eval_index(lhs)?;
                let rhs = self.eval_index(rhs)?;
                eval_index_binary(*op, lhs, rhs)
            }
            Expr::Ternary { .. } => match self.eval_value(expr)? {
                Value::Index(value) => Ok(value),
                Value::Element(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Relation { .. } => Err(bool_sort_error()),
            Expr::Star(_)
            | Expr::Omega
            | Expr::Blade(_)
            | Expr::Vector(_)
            | Expr::Call { .. }
            | Expr::Factorial(_) => Err(index_sort_error()),
            Expr::GameForm { .. } => Err(game_only_error("game forms")),
        }
    }

    fn inverse_element(&self, value: &Poly<S>) -> OghamResult<Poly<S>> {
        if value.is_zero() {
            return Err(OghamError::new(
                OghamErrorKind::DivisionByZero,
                Span::point(0),
                "division by zero",
            ));
        }
        value.inv().ok_or_else(|| {
            OghamError::new(
                OghamErrorKind::NotInvertible,
                Span::point(0),
                "polynomial is not a unit",
            )
        })
    }
}

struct RatFuncRuntime<S: OghamScalar + ExactFieldScalar> {
    name: &'static str,
    env: BTreeMap<String, Value<RationalFunction<S>>>,
    fuel_budget: u128,
    fuel_remaining: u128,
    recursion_depth: u128,
    validation_stub_names: BTreeSet<String>,
}

impl<S: OghamScalar + ExactFieldScalar> RatFuncRuntime<S> {
    fn new(name: &'static str) -> Self {
        RatFuncRuntime {
            name,
            env: BTreeMap::new(),
            fuel_budget: DEFAULT_FUEL,
            fuel_remaining: DEFAULT_FUEL,
            recursion_depth: 0,
            validation_stub_names: BTreeSet::new(),
        }
    }

    fn reset_fuel(&mut self) {
        self.fuel_remaining = self.fuel_budget;
        self.recursion_depth = 0;
    }

    fn set_fuel_budget(&mut self, budget: u128) {
        self.fuel_budget = budget;
        self.reset_fuel();
    }

    fn eval_statement(&mut self, stmt: &Statement) -> OghamResult<Option<String>> {
        match stmt {
            Statement::Binding {
                name,
                expr,
                recursive,
            } => {
                self.bind_name(name, expr, *recursive)?;
                Ok(None)
            }
            Statement::Expr(expr) => Ok(Some(display_value(&self.eval_value(expr)?))),
            Statement::Seq { bindings, tail } => {
                for binding in bindings {
                    self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
                }
                self.eval_statement(tail)
            }
        }
    }

    fn bind_name(&mut self, name: &str, expr: &Expr, recursive: bool) -> OghamResult<()> {
        if name == "t" || reserved_function_binder(name) {
            return Err(OghamError::new(
                OghamErrorKind::Reserved,
                Span::point(0),
                format!("`{name}` is reserved in the `{}` world", self.name),
            ));
        }
        if recursive && contains_free_name(expr, name) {
            let Expr::Lambda { binders, body } = expr else {
                return Err(element_fixpoint_error(name));
            };
            let function = self.close_function(
                binders.clone(),
                body.as_ref().clone(),
                Some(name.to_string()),
            )?;
            self.env.insert(name.to_string(), Value::Function(function));
            return Ok(());
        }
        let value = self.eval_value(expr)?;
        self.env.insert(name.to_string(), value);
        Ok(())
    }

    fn eval_block(
        &mut self,
        bindings: &[Binding],
        body: &Expr,
    ) -> OghamResult<Value<RationalFunction<S>>> {
        let saved = self.env.clone();
        let result = (|| {
            for binding in bindings {
                self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
            }
            self.eval_value(body)
        })();
        self.env = saved;
        result
    }

    fn summary(&self) -> String {
        self.name.to_string()
    }

    fn env_summary(&self) -> Vec<String> {
        self.env
            .iter()
            .map(|(name, value)| format!("{name} := {}", display_value(value)))
            .collect()
    }

    fn eval_value(&mut self, expr: &Expr) -> OghamResult<Value<RationalFunction<S>>> {
        match expr {
            Expr::Bool(value) => Ok(Value::Bool(*value)),
            Expr::Tuple(_) => Err(fn_sort_error()),
            Expr::Block { bindings, body } => self.eval_block(bindings, body),
            Expr::Lambda { binders, body } => self
                .close_function(binders.clone(), body.as_ref().clone(), None)
                .map(Value::Function),
            Expr::Ident(name) => {
                if name == "t" {
                    Ok(Value::Element(RationalFunction::t()))
                } else if let Some(value) = self.env.get(name) {
                    Ok(value.clone())
                } else {
                    Err(unbound_error(name))
                }
            }
            Expr::Relation { op, lhs, rhs } => Ok(Value::Bool(self.eval_relation(*op, lhs, rhs)?)),
            Expr::Unary {
                op: UnaryOp::Not,
                expr,
            } => Ok(Value::Bool(!self.eval_bool(expr)?)),
            Expr::Binary {
                op: BinaryOp::And,
                lhs,
                rhs,
            } => {
                let lhs = self.eval_bool(lhs)?;
                if self.static_sort(rhs)? != Sort::Bool {
                    return Err(bool_sort_error());
                }
                if !lhs {
                    return Ok(Value::Bool(false));
                }
                Ok(Value::Bool(self.eval_bool(rhs)?))
            }
            Expr::Binary {
                op: BinaryOp::Or,
                lhs,
                rhs,
            } => {
                let lhs = self.eval_bool(lhs)?;
                if self.static_sort(rhs)? != Sort::Bool {
                    return Err(bool_sort_error());
                }
                if lhs {
                    return Ok(Value::Bool(true));
                }
                Ok(Value::Bool(self.eval_bool(rhs)?))
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                let then_sort = self.static_sort(then_expr)?;
                let else_sort = self.static_sort(else_expr)?;
                if then_sort != else_sort {
                    return Err(sort_mismatch(then_sort, else_sort));
                }
                if self.eval_bool(cond)? {
                    self.eval_value(then_expr)
                } else {
                    self.eval_value(else_expr)
                }
            }
            Expr::Binary {
                op: BinaryOp::At,
                lhs,
                rhs,
            } => self.eval_at(lhs, rhs),
            _ => match self.eval_element(expr) {
                Ok(value) => Ok(Value::Element(value)),
                Err(err) if err.kind == OghamErrorKind::IndexSort => {
                    Ok(Value::Index(self.eval_index(expr)?))
                }
                Err(err) => Err(err),
            },
        }
    }

    fn eval_bool(&mut self, expr: &Expr) -> OghamResult<bool> {
        match self.eval_value(expr)? {
            Value::Bool(value) => Ok(value),
            Value::Element(_) | Value::Index(_) => Err(bool_sort_error()),
            Value::Function(_) => Err(fn_sort_error()),
        }
    }

    fn eval_at(&mut self, lhs: &Expr, rhs: &Expr) -> OghamResult<Value<RationalFunction<S>>> {
        let lhs_v = self.eval_value(lhs)?;
        match lhs_v {
            Value::Function(function) => {
                if let Expr::Tuple(items) = rhs {
                    return self.apply_function_exprs(&function, items);
                }
                match self.eval_value(rhs)? {
                    Value::Function(rhs_fn) => self
                        .compose_functions(&function, &rhs_fn)
                        .map(Value::Function),
                    _ => self.apply_function_exprs(&function, std::slice::from_ref(rhs)),
                }
            }
            Value::Element(lhs_e) => match self.eval_value(rhs)? {
                Value::Element(rhs_e) => {
                    substitute_rational_function(&lhs_e, &rhs_e, Span::point(0)).map(Value::Element)
                }
                Value::Function(rhs_fn) => self
                    .compose_element_with_function(lhs, &rhs_fn)
                    .map(Value::Function),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
            },
            Value::Index(_) => Err(index_sort_error()),
            Value::Bool(_) => Err(bool_sort_error()),
        }
    }

    fn compose_element_with_function(
        &mut self,
        lhs: &Expr,
        rhs: &FunctionValue,
    ) -> OghamResult<FunctionValue> {
        let mut replacements = BTreeMap::new();
        replacements.insert("t".to_string(), rhs.body.clone());
        let body = beta_normalize(substitute_names(lhs, &replacements))?;
        let function = FunctionValue {
            binders: rhs.binders.clone(),
            body,
            ret: Sort::Element,
            mu_name: None,
        };
        self.validate_function_body(&function)?;
        Ok(function)
    }

    fn apply_function(
        &mut self,
        function: &FunctionValue,
        args: Vec<Value<RationalFunction<S>>>,
    ) -> OghamResult<Value<RationalFunction<S>>> {
        if args.len() != function.binders.len() {
            return Err(OghamError::new(
                OghamErrorKind::Arity,
                Span::point(0),
                format!(
                    "function expects {} argument(s), got {}",
                    function.binders.len(),
                    args.len()
                ),
            ));
        }
        consume_fuel(function, &mut self.fuel_remaining, self.fuel_budget)?;
        let mut replacements = BTreeMap::new();
        for (binder, arg) in function.binders.iter().zip(args.iter()) {
            ensure_value_sort(arg, binder.sort)?;
            replacements.insert(binder.name.clone(), value_to_expr(arg)?);
        }
        let body = substitute_names(&function.body, &replacements);
        let recursive_frame = enter_recursion_frame(
            function,
            &mut self.recursion_depth,
            self.fuel_remaining,
            self.fuel_budget,
        )?;
        let previous = function.mu_name.as_ref().map(|name| {
            self.env
                .insert(name.clone(), Value::Function(function.clone()))
        });
        let result = self.eval_value(&body);
        if let Some(name) = &function.mu_name {
            if let Some(previous) = previous.flatten() {
                self.env.insert(name.clone(), previous);
            } else {
                self.env.remove(name);
            }
        }
        leave_recursion_frame(recursive_frame, &mut self.recursion_depth);
        result
    }

    fn apply_function_exprs(
        &mut self,
        function: &FunctionValue,
        args: &[Expr],
    ) -> OghamResult<Value<RationalFunction<S>>> {
        if args.len() != function.binders.len() {
            return Err(OghamError::new(
                OghamErrorKind::Arity,
                Span::point(0),
                format!(
                    "function expects {} argument(s), got {}",
                    function.binders.len(),
                    args.len()
                ),
            ));
        }
        let values = function
            .binders
            .iter()
            .zip(args)
            .map(|(binder, arg)| self.eval_arg_for_sort(arg, binder.sort))
            .collect::<OghamResult<Vec<_>>>()?;
        self.apply_function(function, values)
    }

    fn eval_arg_for_sort(
        &mut self,
        expr: &Expr,
        sort: Sort,
    ) -> OghamResult<Value<RationalFunction<S>>> {
        match sort {
            Sort::Element => self.eval_element(expr).map(Value::Element),
            Sort::Index => self.eval_index(expr).map(Value::Index),
            Sort::Bool => self.eval_bool(expr).map(Value::Bool),
        }
    }

    fn compose_functions(
        &mut self,
        lhs: &FunctionValue,
        rhs: &FunctionValue,
    ) -> OghamResult<FunctionValue> {
        if lhs.binders.len() != 1 {
            return Err(OghamError::new(
                OghamErrorKind::Arity,
                Span::point(0),
                "function composition needs a unary head",
            ));
        }
        if lhs.binders[0].sort != rhs.ret {
            return Err(sort_mismatch(lhs.binders[0].sort, rhs.ret));
        }
        let mut replacements = BTreeMap::new();
        replacements.insert(lhs.binders[0].name.clone(), rhs.body.clone());
        let body = beta_normalize(substitute_names(&lhs.body, &replacements))?;
        let function = FunctionValue {
            binders: rhs.binders.clone(),
            body,
            ret: lhs.ret,
            mu_name: None,
        };
        self.validate_function_body(&function)?;
        Ok(function)
    }

    fn close_function(
        &mut self,
        binders: Vec<String>,
        body: Expr,
        mu_name: Option<String>,
    ) -> OghamResult<FunctionValue> {
        check_binders(&binders, |name| {
            name == "t" || reserved_function_binder(name)
        })
        .map_err(|err| {
            if err.kind == OghamErrorKind::Shadow && err.message.contains("`t`") {
                err.with_hint("`t` is the indeterminate here; `5⋅t + 1` is already a function")
            } else {
                err
            }
        })?;
        let mut bound: BTreeSet<String> = binders.iter().cloned().collect();
        bound.extend(mu_name.iter().cloned());
        bound.extend(self.validation_stub_names.iter().cloned());
        let substituted = substitute_env(&body, &bound, &self.env)?;
        let body = beta_normalize(substituted)?;
        let (binder_sorts, ret) = infer_function_signature(&body, &binders)?;
        let function = FunctionValue {
            binders: binders
                .into_iter()
                .zip(binder_sorts)
                .map(|(name, sort)| Binder { name, sort })
                .collect(),
            body,
            ret,
            mu_name,
        };
        if let Some(name) = &function.mu_name {
            let stub = validation_stub(&function, self.sample_expr(function.ret)?);
            let previous = self.env.insert(name.clone(), Value::Function(stub));
            self.validation_stub_names.insert(name.clone());
            let validation = self.validate_function_body(&function);
            self.validation_stub_names.remove(name);
            if let Some(previous) = previous {
                self.env.insert(name.clone(), previous);
            } else {
                self.env.remove(name);
            }
            validation?;
        } else {
            self.validate_function_body(&function)?;
        }
        Ok(function)
    }

    fn validate_function_body(&mut self, function: &FunctionValue) -> OghamResult<()> {
        let mut replacements = BTreeMap::new();
        for binder in &function.binders {
            replacements.insert(binder.name.clone(), self.sample_expr(binder.sort)?);
        }
        let sampled = substitute_names(&function.body, &replacements);
        self.validate_all(&sampled)
    }

    fn validate_all(&mut self, expr: &Expr) -> OghamResult<()> {
        match expr {
            Expr::Lambda { .. } => return Err(fn_sort_error()),
            Expr::Block { bindings, body } => {
                let saved = self.env.clone();
                let saved_validation_stubs = self.validation_stub_names.clone();
                let result = (|| {
                    for binding in bindings {
                        if !matches!(binding.expr, Expr::Lambda { .. }) {
                            self.validate_all(&binding.expr)?;
                        }
                        self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
                        if let Some(Value::Function(function)) =
                            self.env.get(&binding.name).cloned()
                        {
                            let stub = validation_stub(&function, self.sample_expr(function.ret)?);
                            self.env.insert(binding.name.clone(), Value::Function(stub));
                            self.validation_stub_names.insert(binding.name.clone());
                        }
                    }
                    self.validate_all(body)
                })();
                self.env = saved;
                self.validation_stub_names = saved_validation_stubs;
                result?;
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.validate_all(cond)?;
                self.validate_all(then_expr)?;
                self.validate_all(else_expr)?;
            }
            Expr::Binary {
                op: BinaryOp::And | BinaryOp::Or,
                lhs,
                rhs,
            } => {
                self.validate_all(lhs)?;
                self.validate_all(rhs)?;
            }
            _ => {}
        }
        ignore_static_partiality(self.eval_value(expr))
    }

    fn sample_expr(&self, sort: Sort) -> OghamResult<Expr> {
        match sort {
            Sort::Element => parse_display_expr(&RationalFunction::<S>::one().to_string()),
            Sort::Index => Ok(Expr::Int(1)),
            Sort::Bool => Ok(Expr::Bool(true)),
        }
    }

    fn static_sort(&self, expr: &Expr) -> OghamResult<Sort> {
        static_sort(expr, &self.env, false)
    }

    fn eval_relation(&mut self, op: RelOp, lhs: &Expr, rhs: &Expr) -> OghamResult<bool> {
        if op == RelOp::Equiv {
            return Err(game_only_error("`≡`"));
        }
        if !bool_shaped(lhs)
            && !bool_shaped(rhs)
            && (expression_is_index(lhs) || expression_is_index(rhs))
        {
            let lhs = self.eval_index(lhs)?;
            let rhs = self.eval_index(rhs)?;
            return ordered_relation(op, lhs.cmp(&rhs));
        }
        let lhs_v = self.eval_value(lhs)?;
        let rhs_v = self.eval_value(rhs)?;
        match (lhs_v, rhs_v) {
            (Value::Function(_), _) | (_, Value::Function(_)) => Err(fn_sort_error()),
            (Value::Bool(lhs), Value::Bool(rhs)) => {
                if op == RelOp::Eq {
                    Ok(lhs == rhs)
                } else {
                    Err(bool_sort_error())
                }
            }
            (Value::Bool(_), _) | (_, Value::Bool(_)) => Err(bool_sort_error()),
            (Value::Index(lhs), Value::Index(rhs)) => ordered_relation(op, lhs.cmp(&rhs)),
            (Value::Index(_), _) | (_, Value::Index(_)) => Err(index_sort_error()),
            (Value::Element(lhs), Value::Element(rhs)) => {
                if op == RelOp::Eq {
                    Ok(lhs == rhs)
                } else {
                    Err(no_order_error())
                }
            }
        }
    }

    fn eval_element(&mut self, expr: &Expr) -> OghamResult<RationalFunction<S>> {
        match expr {
            Expr::Bool(_) => Err(bool_sort_error()),
            Expr::GameForm { .. } => Err(game_only_error("game forms")),
            Expr::Int(n) => Ok(RationalFunction::from_base(S::bare_int(
                *n,
                Span::point(0),
            )?)),
            Expr::Star(star) => Ok(RationalFunction::from_base(S::star(star, Span::point(0))?)),
            Expr::Omega => Ok(RationalFunction::from_base(S::omega(Span::point(0))?)),
            Expr::Blade(_) | Expr::Vector(_) => Err(OghamError::new(
                OghamErrorKind::WrongWorld,
                Span::point(0),
                "function-shaped worlds do not have Clifford blades or vectors",
            )),
            Expr::Ident(name) => {
                if name == "t" {
                    Ok(RationalFunction::t())
                } else if let Some(value) = self.env.get(name) {
                    match value {
                        Value::Element(value) => Ok(value.clone()),
                        Value::Index(_) => Err(index_sort_error()),
                        Value::Bool(_) => Err(bool_sort_error()),
                        Value::Function(_) => Err(fn_sort_error()),
                    }
                } else {
                    Err(unbound_error(name))
                }
            }
            Expr::Tuple(_) | Expr::Lambda { .. } => Err(fn_sort_error()),
            Expr::Block { bindings, body } => match self.eval_block(bindings, body)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Call { name, args } => self.eval_call(name, args),
            Expr::Factorial(expr) => {
                let n = self.eval_index(expr)?;
                Ok(RationalFunction::from_base(S::factorial(
                    n,
                    Span::point(0),
                )?))
            }
            Expr::Unary { op, expr } => {
                let value = self.eval_element(expr)?;
                match op {
                    UnaryOp::Neg => Ok(value.neg()),
                    UnaryOp::Inv => self.inverse_element(&value),
                    UnaryOp::Not => Err(bool_sort_error()),
                }
            }
            Expr::Binary {
                op: BinaryOp::At, ..
            } => match self.eval_value(expr)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Binary { op, lhs, rhs } => self.eval_binary(*op, lhs, rhs),
            Expr::Ternary { .. } => match self.eval_value(expr)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Relation { .. } => Err(OghamError::new(
                OghamErrorKind::BoolSort,
                Span::point(0),
                "relation result is Bool, not Element",
            )),
        }
    }

    fn eval_binary(
        &mut self,
        op: BinaryOp,
        lhs: &Expr,
        rhs: &Expr,
    ) -> OghamResult<RationalFunction<S>> {
        if op == BinaryOp::Append {
            return Err(game_only_error("`⧺`"));
        }
        if op == BinaryOp::Pow {
            return self.eval_power(lhs, rhs);
        }
        if matches!(op, BinaryOp::And | BinaryOp::Or) {
            return Err(bool_sort_error());
        }
        let lhs_v = self.eval_element(lhs)?;
        let rhs_v = self.eval_element(rhs)?;
        match op {
            BinaryOp::Add => Ok(lhs_v.add(&rhs_v)),
            BinaryOp::Sub => Ok(lhs_v.sub(&rhs_v)),
            BinaryOp::Mul => Ok(lhs_v.mul(&rhs_v)),
            BinaryOp::Div => {
                if rhs_v.is_zero() {
                    Err(OghamError::new(
                        OghamErrorKind::DivisionByZero,
                        Span::point(0),
                        "division by zero",
                    ))
                } else {
                    Ok(lhs_v.mul(&rhs_v.inv().expect("checked nonzero rational function")))
                }
            }
            BinaryOp::Rem => Err(OghamError::new(
                OghamErrorKind::WrongWorld,
                Span::point(0),
                "function-field worlds are fields; `%` is only active in polynomial worlds",
            )),
            BinaryOp::At => substitute_rational_function(&lhs_v, &rhs_v, Span::point(0)),
            BinaryOp::Wedge => Err(OghamError::new(
                OghamErrorKind::WrongWorld,
                Span::point(0),
                "wedge product belongs to Clifford worlds",
            )),
            BinaryOp::Pow | BinaryOp::And | BinaryOp::Or | BinaryOp::Append => unreachable!(),
        }
    }

    fn eval_power(&mut self, lhs: &Expr, rhs: &Expr) -> OghamResult<RationalFunction<S>> {
        let base = self.eval_element(lhs)?;
        let exp = self.eval_index(rhs).map_err(|err| {
            if err.kind == OghamErrorKind::IndexSort {
                exp_sort_error()
            } else {
                err
            }
        })?;
        if exp < 0 {
            let inv = self.inverse_element(&base)?;
            let k = exp
                .checked_neg()
                .and_then(|v| u128::try_from(v).ok())
                .ok_or_else(|| overflow("negative exponent magnitude exceeds u128"))?;
            Ok(pow_rational_function(&inv, k))
        } else {
            let k = u128::try_from(exp).map_err(|_| overflow("exponent exceeds u128"))?;
            Ok(pow_rational_function(&base, k))
        }
    }

    fn eval_call(&mut self, name: &str, _args: &[Expr]) -> OghamResult<RationalFunction<S>> {
        match name {
            "coef" | "dim" => Err(array_world_error(name)),
            "deg" | "gcd" => Err(OghamError::new(
                OghamErrorKind::WrongWorld,
                Span::point(0),
                format!("`{name}` is a polynomial-world function, not a ratfunc function"),
            )),
            _ => Err(OghamError::new(
                OghamErrorKind::UnknownFn,
                Span::point(0),
                format!("unknown function `{name}`"),
            )),
        }
    }

    fn eval_index(&mut self, expr: &Expr) -> OghamResult<i128> {
        match expr {
            Expr::Int(n) => u128_to_i128(*n),
            Expr::Bool(_) => Err(bool_sort_error()),
            Expr::Tuple(_) | Expr::Lambda { .. } => Err(fn_sort_error()),
            Expr::Block { bindings, body } => match self.eval_block(bindings, body)? {
                Value::Index(value) => Ok(value),
                Value::Element(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Ident(name) => match self.env.get(name) {
                Some(Value::Index(value)) => Ok(*value),
                Some(Value::Element(_)) => Err(index_sort_error()),
                Some(Value::Bool(_)) => Err(bool_sort_error()),
                Some(Value::Function(_)) => Err(fn_sort_error()),
                None => Err(unbound_error(name)),
            },
            Expr::Call { name, .. } if name == "deg" => Err(OghamError::new(
                OghamErrorKind::WrongWorld,
                Span::point(0),
                "`deg` is a polynomial-world function, not a ratfunc function",
            )),
            Expr::Call { name, .. } if name == "dim" => Err(array_world_error(name)),
            Expr::Unary {
                op: UnaryOp::Neg,
                expr,
            } => self
                .eval_index(expr)?
                .checked_neg()
                .ok_or_else(|| overflow("index negation overflowed i128")),
            Expr::Unary {
                op: UnaryOp::Inv, ..
            } => Err(index_sort_error()),
            Expr::Unary {
                op: UnaryOp::Not, ..
            } => Err(bool_sort_error()),
            Expr::Binary { op, lhs, rhs } => {
                let lhs = self.eval_index(lhs)?;
                let rhs = self.eval_index(rhs)?;
                eval_index_binary(*op, lhs, rhs)
            }
            Expr::Ternary { .. } => match self.eval_value(expr)? {
                Value::Index(value) => Ok(value),
                Value::Element(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Relation { .. } => Err(bool_sort_error()),
            Expr::Star(_)
            | Expr::Omega
            | Expr::Blade(_)
            | Expr::Vector(_)
            | Expr::Call { .. }
            | Expr::Factorial(_) => Err(index_sort_error()),
            Expr::GameForm { .. } => Err(game_only_error("game forms")),
        }
    }

    fn inverse_element(&self, value: &RationalFunction<S>) -> OghamResult<RationalFunction<S>> {
        if value.is_zero() {
            return Err(OghamError::new(
                OghamErrorKind::DivisionByZero,
                Span::point(0),
                "division by zero",
            ));
        }
        Ok(value.inv().expect("checked nonzero rational function"))
    }
}

struct Runtime<S: OghamScalar> {
    name: &'static str,
    alg: CliffordAlgebra<S>,
    env: BTreeMap<String, Value<Multivector<S>>>,
    fuel_budget: u128,
    fuel_remaining: u128,
    recursion_depth: u128,
    validation_stub_names: BTreeSet<String>,
}

impl<S: OghamScalar> Runtime<S> {
    fn from_metric(name: &'static str, metric: Metric<S>) -> Self {
        Runtime {
            name,
            alg: CliffordAlgebra::new(metric.dim(), metric),
            env: BTreeMap::new(),
            fuel_budget: DEFAULT_FUEL,
            fuel_remaining: DEFAULT_FUEL,
            recursion_depth: 0,
            validation_stub_names: BTreeSet::new(),
        }
    }

    fn reset_fuel(&mut self) {
        self.fuel_remaining = self.fuel_budget;
        self.recursion_depth = 0;
    }

    fn set_fuel_budget(&mut self, budget: u128) {
        self.fuel_budget = budget;
        self.reset_fuel();
    }

    fn eval_statement(&mut self, stmt: &Statement) -> OghamResult<Option<String>> {
        match stmt {
            Statement::Binding {
                name,
                expr,
                recursive,
            } => {
                self.bind_name(name, expr, *recursive)?;
                Ok(None)
            }
            Statement::Expr(expr) => Ok(Some(display_value(&self.eval_value(expr)?))),
            Statement::Seq { bindings, tail } => {
                for binding in bindings {
                    self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
                }
                self.eval_statement(tail)
            }
        }
    }

    fn bind_name(&mut self, name: &str, expr: &Expr, recursive: bool) -> OghamResult<()> {
        if S::reserved_ident(name) || reserved_function_binder(name) {
            return Err(OghamError::new(
                OghamErrorKind::Reserved,
                Span::point(0),
                format!("`{name}` is reserved in the `{}` world", self.name),
            ));
        }
        if recursive && contains_free_name(expr, name) {
            let Expr::Lambda { binders, body } = expr else {
                return Err(element_fixpoint_error(name));
            };
            let function = self.close_function(
                binders.clone(),
                body.as_ref().clone(),
                Some(name.to_string()),
            )?;
            self.env.insert(name.to_string(), Value::Function(function));
            return Ok(());
        }
        let value = self.eval_value(expr)?;
        self.env.insert(name.to_string(), value);
        Ok(())
    }

    fn eval_block(
        &mut self,
        bindings: &[Binding],
        body: &Expr,
    ) -> OghamResult<Value<Multivector<S>>> {
        let saved = self.env.clone();
        let result = (|| {
            for binding in bindings {
                self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
            }
            self.eval_value(body)
        })();
        self.env = saved;
        result
    }

    fn summary(&self) -> String {
        format!("{} dim {}", self.name, self.alg.dim())
    }

    fn env_summary(&self) -> Vec<String> {
        self.env
            .iter()
            .map(|(name, value)| format!("{name} := {}", display_value(value)))
            .collect()
    }

    fn eval_value(&mut self, expr: &Expr) -> OghamResult<Value<Multivector<S>>> {
        match expr {
            Expr::Bool(value) => Ok(Value::Bool(*value)),
            Expr::Tuple(_) => Err(fn_sort_error()),
            Expr::Block { bindings, body } => self.eval_block(bindings, body),
            Expr::Lambda { binders, body } => self
                .close_function(binders.clone(), body.as_ref().clone(), None)
                .map(Value::Function),
            Expr::Ident(name) => {
                if let Some(value) = self.env.get(name) {
                    Ok(value.clone())
                } else if let Some(x) = S::named_element(name, Span::point(0))? {
                    Ok(Value::Element(self.alg.scalar(x)))
                } else {
                    Err(unbound_error(name))
                }
            }
            Expr::Relation { op, lhs, rhs } => Ok(Value::Bool(self.eval_relation(*op, lhs, rhs)?)),
            Expr::Unary {
                op: UnaryOp::Not,
                expr,
            } => Ok(Value::Bool(!self.eval_bool(expr)?)),
            Expr::Binary {
                op: BinaryOp::And,
                lhs,
                rhs,
            } => {
                let lhs = self.eval_bool(lhs)?;
                if self.static_sort(rhs)? != Sort::Bool {
                    return Err(bool_sort_error());
                }
                if !lhs {
                    return Ok(Value::Bool(false));
                }
                Ok(Value::Bool(self.eval_bool(rhs)?))
            }
            Expr::Binary {
                op: BinaryOp::Or,
                lhs,
                rhs,
            } => {
                let lhs = self.eval_bool(lhs)?;
                if self.static_sort(rhs)? != Sort::Bool {
                    return Err(bool_sort_error());
                }
                if lhs {
                    return Ok(Value::Bool(true));
                }
                Ok(Value::Bool(self.eval_bool(rhs)?))
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                let then_sort = self.static_sort(then_expr)?;
                let else_sort = self.static_sort(else_expr)?;
                if then_sort != else_sort {
                    return Err(match (then_sort, else_sort) {
                        (Sort::Bool, _) | (_, Sort::Bool) => bool_sort_error(),
                        _ => index_sort_error(),
                    });
                }
                if self.eval_bool(cond)? {
                    self.eval_value(then_expr)
                } else {
                    self.eval_value(else_expr)
                }
            }
            Expr::Binary {
                op: BinaryOp::At,
                lhs,
                rhs,
            } => self.eval_at(lhs, rhs),
            _ => match self.eval_expr(expr) {
                Ok(value) => Ok(Value::Element(value)),
                Err(err) if err.kind == OghamErrorKind::IndexSort => {
                    Ok(Value::Index(self.eval_index(expr)?))
                }
                Err(err) => Err(err),
            },
        }
    }

    fn eval_bool(&mut self, expr: &Expr) -> OghamResult<bool> {
        match self.eval_value(expr)? {
            Value::Bool(value) => Ok(value),
            Value::Element(_) | Value::Index(_) => Err(bool_sort_error()),
            Value::Function(_) => Err(fn_sort_error()),
        }
    }

    fn eval_at(&mut self, lhs: &Expr, rhs: &Expr) -> OghamResult<Value<Multivector<S>>> {
        let lhs_v = self.eval_value(lhs)?;
        let Value::Function(function) = lhs_v else {
            return Err(OghamError::new(
                OghamErrorKind::WrongWorld,
                Span::point(0),
                "only Function values apply with `@` in this world; element evaluation lives in function-shaped worlds",
            ));
        };
        if let Expr::Tuple(items) = rhs {
            return self.apply_function_exprs(&function, items);
        }
        match self.eval_value(rhs)? {
            Value::Function(rhs_fn) => self
                .compose_functions(&function, &rhs_fn)
                .map(Value::Function),
            _ => self.apply_function_exprs(&function, std::slice::from_ref(rhs)),
        }
    }

    fn apply_function(
        &mut self,
        function: &FunctionValue,
        args: Vec<Value<Multivector<S>>>,
    ) -> OghamResult<Value<Multivector<S>>> {
        if args.len() != function.binders.len() {
            return Err(OghamError::new(
                OghamErrorKind::Arity,
                Span::point(0),
                format!(
                    "function expects {} argument(s), got {}",
                    function.binders.len(),
                    args.len()
                ),
            ));
        }
        consume_fuel(function, &mut self.fuel_remaining, self.fuel_budget)?;
        let mut replacements = BTreeMap::new();
        for (binder, arg) in function.binders.iter().zip(args.iter()) {
            ensure_value_sort(arg, binder.sort)?;
            replacements.insert(binder.name.clone(), value_to_expr(arg)?);
        }
        let body = substitute_names(&function.body, &replacements);
        let recursive_frame = enter_recursion_frame(
            function,
            &mut self.recursion_depth,
            self.fuel_remaining,
            self.fuel_budget,
        )?;
        let previous = function.mu_name.as_ref().map(|name| {
            self.env
                .insert(name.clone(), Value::Function(function.clone()))
        });
        let result = self.eval_value(&body);
        if let Some(name) = &function.mu_name {
            if let Some(previous) = previous.flatten() {
                self.env.insert(name.clone(), previous);
            } else {
                self.env.remove(name);
            }
        }
        leave_recursion_frame(recursive_frame, &mut self.recursion_depth);
        result
    }

    fn apply_function_exprs(
        &mut self,
        function: &FunctionValue,
        args: &[Expr],
    ) -> OghamResult<Value<Multivector<S>>> {
        if args.len() != function.binders.len() {
            return Err(OghamError::new(
                OghamErrorKind::Arity,
                Span::point(0),
                format!(
                    "function expects {} argument(s), got {}",
                    function.binders.len(),
                    args.len()
                ),
            ));
        }
        let values = function
            .binders
            .iter()
            .zip(args)
            .map(|(binder, arg)| self.eval_arg_for_sort(arg, binder.sort))
            .collect::<OghamResult<Vec<_>>>()?;
        self.apply_function(function, values)
    }

    fn eval_arg_for_sort(&mut self, expr: &Expr, sort: Sort) -> OghamResult<Value<Multivector<S>>> {
        match sort {
            Sort::Element => self.eval_expr(expr).map(Value::Element),
            Sort::Index => self.eval_index(expr).map(Value::Index),
            Sort::Bool => self.eval_bool(expr).map(Value::Bool),
        }
    }

    fn compose_functions(
        &mut self,
        lhs: &FunctionValue,
        rhs: &FunctionValue,
    ) -> OghamResult<FunctionValue> {
        if lhs.binders.len() != 1 {
            return Err(OghamError::new(
                OghamErrorKind::Arity,
                Span::point(0),
                "function composition needs a unary head",
            ));
        }
        if lhs.binders[0].sort != rhs.ret {
            return Err(sort_mismatch(lhs.binders[0].sort, rhs.ret));
        }
        let mut replacements = BTreeMap::new();
        replacements.insert(lhs.binders[0].name.clone(), rhs.body.clone());
        let body = beta_normalize(substitute_names(&lhs.body, &replacements))?;
        let function = FunctionValue {
            binders: rhs.binders.clone(),
            body,
            ret: lhs.ret,
            mu_name: None,
        };
        self.validate_function_body(&function)?;
        Ok(function)
    }

    fn close_function(
        &mut self,
        binders: Vec<String>,
        body: Expr,
        mu_name: Option<String>,
    ) -> OghamResult<FunctionValue> {
        check_binders(&binders, |name| {
            S::reserved_ident(name) || reserved_function_binder(name)
        })?;
        let mut bound: BTreeSet<String> = binders.iter().cloned().collect();
        bound.extend(mu_name.iter().cloned());
        bound.extend(self.validation_stub_names.iter().cloned());
        let substituted = substitute_env(&body, &bound, &self.env)?;
        let body = beta_normalize(substituted)?;
        let (binder_sorts, ret) = infer_function_signature(&body, &binders)?;
        let function = FunctionValue {
            binders: binders
                .into_iter()
                .zip(binder_sorts)
                .map(|(name, sort)| Binder { name, sort })
                .collect(),
            body,
            ret,
            mu_name,
        };
        if let Some(name) = &function.mu_name {
            let stub = validation_stub(&function, self.sample_expr(function.ret)?);
            let previous = self.env.insert(name.clone(), Value::Function(stub));
            self.validation_stub_names.insert(name.clone());
            let validation = self.validate_function_body(&function);
            self.validation_stub_names.remove(name);
            if let Some(previous) = previous {
                self.env.insert(name.clone(), previous);
            } else {
                self.env.remove(name);
            }
            validation?;
        } else {
            self.validate_function_body(&function)?;
        }
        Ok(function)
    }

    fn validate_function_body(&mut self, function: &FunctionValue) -> OghamResult<()> {
        let mut replacements = BTreeMap::new();
        for binder in &function.binders {
            replacements.insert(binder.name.clone(), self.sample_expr(binder.sort)?);
        }
        let sampled = substitute_names(&function.body, &replacements);
        self.validate_all(&sampled)
    }

    fn validate_all(&mut self, expr: &Expr) -> OghamResult<()> {
        match expr {
            Expr::Lambda { .. } => return Err(fn_sort_error()),
            Expr::Block { bindings, body } => {
                let saved = self.env.clone();
                let saved_validation_stubs = self.validation_stub_names.clone();
                let result = (|| {
                    for binding in bindings {
                        if !matches!(binding.expr, Expr::Lambda { .. }) {
                            self.validate_all(&binding.expr)?;
                        }
                        self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
                        if let Some(Value::Function(function)) =
                            self.env.get(&binding.name).cloned()
                        {
                            let stub = validation_stub(&function, self.sample_expr(function.ret)?);
                            self.env.insert(binding.name.clone(), Value::Function(stub));
                            self.validation_stub_names.insert(binding.name.clone());
                        }
                    }
                    self.validate_all(body)
                })();
                self.env = saved;
                self.validation_stub_names = saved_validation_stubs;
                result?;
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.validate_all(cond)?;
                self.validate_all(then_expr)?;
                self.validate_all(else_expr)?;
            }
            Expr::Binary {
                op: BinaryOp::And | BinaryOp::Or,
                lhs,
                rhs,
            } => {
                self.validate_all(lhs)?;
                self.validate_all(rhs)?;
            }
            _ => {}
        }
        ignore_static_partiality(self.eval_value(expr))
    }

    fn sample_expr(&self, sort: Sort) -> OghamResult<Expr> {
        match sort {
            Sort::Element => parse_display_expr(&self.alg.scalar(S::one()).to_string()),
            Sort::Index => Ok(Expr::Int(1)),
            Sort::Bool => Ok(Expr::Bool(true)),
        }
    }

    fn static_sort(&self, expr: &Expr) -> OghamResult<Sort> {
        static_sort(expr, &self.env, false)
    }

    fn eval_relation(&mut self, op: RelOp, lhs: &Expr, rhs: &Expr) -> OghamResult<bool> {
        if op == RelOp::Equiv {
            return Err(game_only_error("`≡`"));
        }
        if !bool_shaped(lhs)
            && !bool_shaped(rhs)
            && (expression_is_index(lhs) || expression_is_index(rhs))
        {
            let lhs = self.eval_index(lhs)?;
            let rhs = self.eval_index(rhs)?;
            return ordered_relation(op, lhs.cmp(&rhs));
        }
        let lhs_v = self.eval_value(lhs)?;
        let rhs_v = self.eval_value(rhs)?;
        match (lhs_v, rhs_v) {
            (Value::Function(_), _) | (_, Value::Function(_)) => Err(fn_sort_error()),
            (Value::Bool(lhs), Value::Bool(rhs)) => {
                if op == RelOp::Eq {
                    Ok(lhs == rhs)
                } else {
                    Err(bool_sort_error())
                }
            }
            (Value::Bool(_), _) | (_, Value::Bool(_)) => Err(bool_sort_error()),
            (Value::Index(lhs), Value::Index(rhs)) => ordered_relation(op, lhs.cmp(&rhs)),
            (Value::Index(_), _) | (_, Value::Index(_)) => Err(index_sort_error()),
            (Value::Element(lhs), Value::Element(rhs)) => {
                if op == RelOp::Eq {
                    return Ok(lhs == rhs);
                }
                let Some(lhs) = scalar_part(&lhs) else {
                    return Err(grade0_error(Span::point(0)));
                };
                let Some(rhs) = scalar_part(&rhs) else {
                    return Err(grade0_error(Span::point(0)));
                };
                S::relation(op, &lhs, &rhs, Span::point(0))
            }
        }
    }

    fn eval_expr(&mut self, expr: &Expr) -> OghamResult<Multivector<S>> {
        match expr {
            Expr::Bool(_) => Err(bool_sort_error()),
            Expr::GameForm { .. } => Err(game_only_error("game forms")),
            Expr::Int(n) => Ok(self.alg.scalar(S::bare_int(*n, Span::point(0))?)),
            Expr::Star(star) => Ok(self.alg.scalar(S::star(star, Span::point(0))?)),
            Expr::Omega => Ok(self.alg.scalar(S::omega(Span::point(0))?)),
            Expr::Blade(i) => {
                if *i >= self.alg.dim() {
                    Err(OghamError::new(
                        OghamErrorKind::BladeIndex,
                        Span::point(0),
                        format!("blade e{i} is outside dimension {}", self.alg.dim()),
                    ))
                } else {
                    Ok(self.alg.e(*i))
                }
            }
            Expr::Vector(items) => self.eval_vector(items),
            Expr::Tuple(_) | Expr::Lambda { .. } => Err(fn_sort_error()),
            Expr::Block { bindings, body } => match self.eval_block(bindings, body)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Ident(name) => {
                if let Some(value) = self.env.get(name) {
                    match value {
                        Value::Element(value) => Ok(value.clone()),
                        Value::Index(_) => Err(index_sort_error()),
                        Value::Bool(_) => Err(bool_sort_error()),
                        Value::Function(_) => Err(fn_sort_error()),
                    }
                } else if let Some(x) = S::named_element(name, Span::point(0))? {
                    Ok(self.alg.scalar(x))
                } else {
                    Err(unbound_error(name))
                }
            }
            Expr::Call { name, args } => self.eval_call(name, args),
            Expr::Factorial(expr) => {
                let n = self.eval_index(expr)?;
                Ok(self.alg.scalar(S::factorial(n, Span::point(0))?))
            }
            Expr::Unary { op, expr } => {
                let value = self.eval_expr(expr)?;
                match op {
                    UnaryOp::Neg => Ok(-value),
                    UnaryOp::Inv => self.inverse_mv(&value),
                    UnaryOp::Not => Err(bool_sort_error()),
                }
            }
            Expr::Binary {
                op: BinaryOp::At, ..
            } => match self.eval_value(expr)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Binary { op, lhs, rhs } => self.eval_binary(*op, lhs, rhs),
            Expr::Ternary { .. } => match self.eval_value(expr)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Relation { .. } => Err(OghamError::new(
                OghamErrorKind::BoolSort,
                Span::point(0),
                "relation result is Bool, not Element",
            )),
        }
    }

    fn eval_binary(&mut self, op: BinaryOp, lhs: &Expr, rhs: &Expr) -> OghamResult<Multivector<S>> {
        if op == BinaryOp::Append {
            return Err(game_only_error("`⧺`"));
        }
        if op == BinaryOp::Pow {
            return self.eval_power(lhs, rhs);
        }
        if op == BinaryOp::At {
            return Err(OghamError::new(
                OghamErrorKind::WrongWorld,
                Span::point(0),
                "element composition lives in the function-shaped worlds — poly/ratfunc",
            ));
        }
        if matches!(op, BinaryOp::And | BinaryOp::Or) {
            return Err(bool_sort_error());
        }
        let lhs_v = self.eval_expr(lhs)?;
        let rhs_v = self.eval_expr(rhs)?;
        match op {
            BinaryOp::Add => Ok(lhs_v + rhs_v),
            BinaryOp::Sub => Ok(lhs_v - rhs_v),
            BinaryOp::Mul => self.mul_mv(&lhs_v, &rhs_v),
            BinaryOp::Div => self.div_mv(&lhs_v, &rhs_v),
            BinaryOp::Rem => {
                let Some(lhs_s) = scalar_part(&lhs_v) else {
                    return Err(grade0_error(Span::point(0)));
                };
                let Some(rhs_s) = scalar_part(&rhs_v) else {
                    return Err(grade0_error(Span::point(0)));
                };
                Ok(self.alg.scalar(S::rem(&lhs_s, &rhs_s, Span::point(0))?))
            }
            BinaryOp::Wedge => Ok(self.alg.wedge(&lhs_v, &rhs_v)),
            BinaryOp::Pow | BinaryOp::At | BinaryOp::And | BinaryOp::Or | BinaryOp::Append => {
                unreachable!()
            }
        }
    }

    fn eval_power(&mut self, lhs: &Expr, rhs: &Expr) -> OghamResult<Multivector<S>> {
        if lhs.is_omega_atom() {
            if let Err(index_err) = self.eval_index(rhs) {
                if index_err.kind == OghamErrorKind::IndexSort {
                    let exp = self.eval_expr(rhs)?;
                    let Some(exp) = scalar_part(&exp) else {
                        return Err(exp_sort_error());
                    };
                    return Ok(self.alg.scalar(S::omega_pow(exp, Span::point(0))?));
                }
                return Err(index_err);
            }
        }
        let base = self.eval_expr(lhs)?;
        let exp = self.eval_index(rhs).map_err(|err| {
            if err.kind == OghamErrorKind::IndexSort {
                exp_sort_error()
            } else {
                err
            }
        })?;
        if exp < 0 {
            let inv = self.inverse_mv(&base)?;
            let k = exp
                .checked_neg()
                .and_then(|v| u128::try_from(v).ok())
                .ok_or_else(|| overflow("negative exponent magnitude exceeds u128"))?;
            self.pow_mv(&inv, k)
        } else {
            let k = u128::try_from(exp).map_err(|_| overflow("exponent exceeds u128"))?;
            self.pow_mv(&base, k)
        }
    }

    fn eval_vector(&mut self, items: &[Expr]) -> OghamResult<Multivector<S>> {
        if self.alg.dim() == 0 || items.len() != self.alg.dim() {
            return Err(OghamError::new(
                OghamErrorKind::DimMismatch,
                Span::point(0),
                format!(
                    "vector length {} does not match world dimension {}",
                    items.len(),
                    self.alg.dim()
                ),
            ));
        }
        let mut out = self.alg.zero();
        for (i, expr) in items.iter().enumerate() {
            let value = self.eval_expr(expr)?;
            let Some(coeff) = scalar_part(&value) else {
                return Err(grade0_error(Span::point(0)));
            };
            out = self
                .alg
                .add(&out, &self.alg.scalar_mul(&coeff, &self.alg.e(i)));
        }
        Ok(out)
    }

    fn eval_call(&mut self, name: &str, args: &[Expr]) -> OghamResult<Multivector<S>> {
        match name {
            "coef" => {
                expect_arity(name, args, 2)?;
                let value = self.eval_expr(&args[0])?;
                let index = self.eval_index(&args[1])?;
                let index = usize::try_from(index).map_err(|_| {
                    OghamError::new(
                        OghamErrorKind::BladeIndex,
                        Span::point(0),
                        format!(
                            "coefficient index {index} is outside dimension {}",
                            self.alg.dim()
                        ),
                    )
                })?;
                if index >= self.alg.dim() {
                    return Err(OghamError::new(
                        OghamErrorKind::BladeIndex,
                        Span::point(0),
                        format!(
                            "coefficient index {index} is outside dimension {}",
                            self.alg.dim()
                        ),
                    ));
                }
                let mask = 1u128.checked_shl(index as u32).ok_or_else(|| {
                    OghamError::new(
                        OghamErrorKind::BladeIndex,
                        Span::point(0),
                        format!("coefficient index {index} exceeds the u128 blade mask"),
                    )
                })?;
                let coefficient = value.terms().get(&mask).cloned().unwrap_or_else(S::zero);
                Ok(self.alg.scalar(coefficient))
            }
            "dim" => Err(index_sort_error().with_hint("`dim()` returns an Index")),
            "rev" => {
                expect_arity(name, args, 1)?;
                if self.alg.metric().has_upper() {
                    return Err(OghamError::new(
                        OghamErrorKind::GeneralMetric,
                        Span::point(0),
                        "reverse is undefined for the Chevalley construction",
                    ));
                }
                let x = self.eval_expr(&args[0])?;
                Ok(self.alg.reverse(&x))
            }
            "grade" => {
                expect_arity(name, args, 2)?;
                let x = self.eval_expr(&args[0])?;
                let k = self.eval_index(&args[1])?;
                if k < 0 {
                    return Err(OghamError::new(
                        OghamErrorKind::Domain,
                        Span::point(0),
                        "grade index must be non-negative",
                    ));
                }
                Ok(self.alg.grade_part(&x, k as usize))
            }
            "even" => {
                expect_arity(name, args, 1)?;
                let x = self.eval_expr(&args[0])?;
                Ok(self.alg.even_part(&x))
            }
            "dual" => {
                expect_arity(name, args, 1)?;
                if self.alg.metric().has_upper() {
                    return Err(OghamError::new(
                        OghamErrorKind::GeneralMetric,
                        Span::point(0),
                        "dual is undefined for general-bilinear metrics",
                    ));
                }
                let x = self.eval_expr(&args[0])?;
                self.alg.dual(&x).ok_or_else(|| {
                    OghamError::new(
                        OghamErrorKind::NotInvertible,
                        Span::point(0),
                        "pseudoscalar is not invertible",
                    )
                })
            }
            "frob" => {
                expect_arity(name, args, 1)?;
                let x = self.eval_grade0(&args[0])?;
                Ok(self.alg.scalar(S::frob(&x, Span::point(0))?))
            }
            "tr" => {
                if args.is_empty() || args.len() > 2 {
                    return Err(OghamError::new(
                        OghamErrorKind::Arity,
                        Span::point(0),
                        "`tr` expects one or two arguments",
                    ));
                }
                let x = self.eval_grade0(&args[0])?;
                let m = if args.len() == 2 {
                    Some(self.eval_index(&args[1])?)
                } else {
                    None
                };
                Ok(self.alg.scalar(S::trace(&x, m, Span::point(0))?))
            }
            _ => Err(OghamError::new(
                OghamErrorKind::UnknownFn,
                Span::point(0),
                format!("unknown function `{name}`"),
            )),
        }
    }

    fn eval_grade0(&mut self, expr: &Expr) -> OghamResult<S> {
        let value = self.eval_expr(expr)?;
        scalar_part(&value).ok_or_else(|| grade0_error(Span::point(0)))
    }

    fn eval_index(&mut self, expr: &Expr) -> OghamResult<i128> {
        match expr {
            Expr::Int(n) => u128_to_i128(*n),
            Expr::Bool(_) => Err(bool_sort_error()),
            Expr::Tuple(_) | Expr::Lambda { .. } => Err(fn_sort_error()),
            Expr::Block { bindings, body } => match self.eval_block(bindings, body)? {
                Value::Index(value) => Ok(value),
                Value::Element(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Ident(name) => match self.env.get(name) {
                Some(Value::Index(value)) => Ok(*value),
                Some(Value::Element(_)) => Err(index_sort_error()),
                Some(Value::Bool(_)) => Err(bool_sort_error()),
                Some(Value::Function(_)) => Err(fn_sort_error()),
                None => Err(unbound_error(name)),
            },
            Expr::Call { name, args } if name == "dim" => {
                expect_arity(name, args, 0)?;
                i128::try_from(self.alg.dim()).map_err(|_| overflow("world dimension exceeds i128"))
            }
            Expr::Unary {
                op: UnaryOp::Neg,
                expr,
            } => self
                .eval_index(expr)?
                .checked_neg()
                .ok_or_else(|| overflow("index negation overflowed i128")),
            Expr::Unary {
                op: UnaryOp::Inv, ..
            } => Err(index_sort_error()),
            Expr::Unary {
                op: UnaryOp::Not, ..
            } => Err(bool_sort_error()),
            Expr::Binary { op, lhs, rhs } => {
                let lhs = self.eval_index(lhs)?;
                let rhs = self.eval_index(rhs)?;
                match op {
                    BinaryOp::Add => lhs
                        .checked_add(rhs)
                        .ok_or_else(|| overflow("index addition overflowed i128")),
                    BinaryOp::Sub => lhs
                        .checked_sub(rhs)
                        .ok_or_else(|| overflow("index subtraction overflowed i128")),
                    BinaryOp::Mul => lhs
                        .checked_mul(rhs)
                        .ok_or_else(|| overflow("index multiplication overflowed i128")),
                    BinaryOp::Pow => {
                        if rhs < 0 {
                            return Err(OghamError::new(
                                OghamErrorKind::Domain,
                                Span::point(0),
                                "index exponent must be non-negative",
                            ));
                        }
                        checked_i128_pow(lhs, rhs as u128)
                    }
                    BinaryOp::Div
                    | BinaryOp::Rem
                    | BinaryOp::Wedge
                    | BinaryOp::At
                    | BinaryOp::And
                    | BinaryOp::Or
                    | BinaryOp::Append => Err(index_sort_error()),
                }
            }
            Expr::Ternary { .. } => match self.eval_value(expr)? {
                Value::Index(value) => Ok(value),
                Value::Element(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Relation { .. } => Err(bool_sort_error()),
            Expr::Star(_)
            | Expr::Omega
            | Expr::Blade(_)
            | Expr::Vector(_)
            | Expr::Call { .. }
            | Expr::Factorial(_) => Err(index_sort_error()),
            Expr::GameForm { .. } => Err(game_only_error("game forms")),
        }
    }

    fn inverse_mv(&self, value: &Multivector<S>) -> OghamResult<Multivector<S>> {
        if let Some(s) = scalar_part(value) {
            if s.is_zero() {
                return Err(OghamError::new(
                    OghamErrorKind::DivisionByZero,
                    Span::point(0),
                    "division by zero",
                ));
            }
            return Ok(self.alg.scalar(S::inv_scalar(&s, Span::point(0))?));
        }
        self.alg.multivector_inverse(value).ok_or_else(|| {
            OghamError::new(
                OghamErrorKind::NotInvertible,
                Span::point(0),
                "multivector is not invertible",
            )
        })
    }

    fn div_mv(&self, lhs: &Multivector<S>, rhs: &Multivector<S>) -> OghamResult<Multivector<S>> {
        if rhs.is_zero() {
            return Err(OghamError::new(
                OghamErrorKind::DivisionByZero,
                Span::point(0),
                "division by zero",
            ));
        }
        if let (Some(a), Some(b)) = (scalar_part(lhs), scalar_part(rhs)) {
            if let Some(out) = S::exact_div(&a, &b, Span::point(0)) {
                return Ok(self.alg.scalar(out?));
            }
        }
        let inv = self.inverse_mv(rhs)?;
        self.mul_mv(lhs, &inv)
    }

    fn mul_mv(&self, lhs: &Multivector<S>, rhs: &Multivector<S>) -> OghamResult<Multivector<S>> {
        if let (Some(a), Some(b)) = (scalar_part(lhs), scalar_part(rhs)) {
            return Ok(self.alg.scalar(S::mul_checked(&a, &b, Span::point(0))?));
        }
        S::mv_mul(&self.alg, lhs, rhs, Span::point(0))
    }

    fn pow_mv(&self, value: &Multivector<S>, k: u128) -> OghamResult<Multivector<S>> {
        if let Some(s) = scalar_part(value) {
            return Ok(self.alg.scalar(S::pow_checked(&s, k, Span::point(0))?));
        }
        S::mv_pow(&self.alg, value, k, Span::point(0))
    }
}

trait PolyWorldCoeff: OghamScalar {
    fn divrem_poly(
        lhs: &Poly<Self>,
        divisor: &Poly<Self>,
        span: Span,
    ) -> OghamResult<(Poly<Self>, Poly<Self>)>;
    fn gcd_poly(lhs: &Poly<Self>, rhs: &Poly<Self>, span: Span) -> OghamResult<Poly<Self>>;
}

impl<const P: u128> PolyWorldCoeff for Fp<P>
where
    Fp<P>: OghamScalar,
{
    fn divrem_poly(
        lhs: &Poly<Self>,
        divisor: &Poly<Self>,
        span: Span,
    ) -> OghamResult<(Poly<Self>, Poly<Self>)> {
        if divisor.is_zero() {
            return Err(OghamError::new(
                OghamErrorKind::DivisionByZero,
                span,
                "polynomial division by zero",
            ));
        }
        Ok(lhs.divrem(divisor))
    }

    fn gcd_poly(lhs: &Poly<Self>, rhs: &Poly<Self>, _span: Span) -> OghamResult<Poly<Self>> {
        Ok(lhs.gcd(rhs))
    }
}

impl PolyWorldCoeff for Integer {
    fn divrem_poly(
        lhs: &Poly<Self>,
        divisor: &Poly<Self>,
        span: Span,
    ) -> OghamResult<(Poly<Self>, Poly<Self>)> {
        if divisor.is_zero() {
            return Err(OghamError::new(
                OghamErrorKind::DivisionByZero,
                span,
                "polynomial division by zero",
            ));
        }
        if !matches!(divisor.leading(), Some(c) if *c == Integer::one()) {
            return Err(OghamError::new(
                OghamErrorKind::Modulus,
                span,
                "polyint divisors must be monic",
            ));
        }
        Ok(lhs.divrem(divisor))
    }

    fn gcd_poly(lhs: &Poly<Self>, rhs: &Poly<Self>, span: Span) -> OghamResult<Poly<Self>> {
        integer_poly_gcd(lhs, rhs, span)
    }
}

fn poly_rem<S: PolyWorldCoeff>(lhs: &Poly<S>, rhs: &Poly<S>, span: Span) -> OghamResult<Poly<S>> {
    let (_, r) = S::divrem_poly(lhs, rhs, span)?;
    Ok(r)
}

fn poly_exact_div<S: PolyWorldCoeff>(
    lhs: &Poly<S>,
    rhs: &Poly<S>,
    span: Span,
) -> OghamResult<Poly<S>> {
    let (q, r) = S::divrem_poly(lhs, rhs, span)?;
    if r.is_zero() {
        Ok(q)
    } else {
        Err(OghamError::new(
            OghamErrorKind::NotInvertible,
            span,
            format!("polynomial exact division failed with remainder {r}"),
        ))
    }
}

fn pow_poly<S: Scalar>(base: &Poly<S>, mut k: u128) -> Poly<S> {
    if k == 0 {
        return Poly::one();
    }
    let mut acc = Poly::one();
    let mut x = base.clone();
    loop {
        if k & 1 == 1 {
            acc = acc.mul(&x);
        }
        k >>= 1;
        if k == 0 {
            break;
        }
        x = x.mul(&x);
    }
    acc
}

fn pow_rational_function<S: ExactFieldScalar>(
    base: &RationalFunction<S>,
    mut k: u128,
) -> RationalFunction<S> {
    if k == 0 {
        return RationalFunction::one();
    }
    let mut acc = RationalFunction::one();
    let mut x = base.clone();
    loop {
        if k & 1 == 1 {
            acc = acc.mul(&x);
        }
        k >>= 1;
        if k == 0 {
            break;
        }
        x = x.mul(&x);
    }
    acc
}

fn substitute_rational_function<S: OghamScalar + ExactFieldScalar>(
    f: &RationalFunction<S>,
    arg: &RationalFunction<S>,
    span: Span,
) -> OghamResult<RationalFunction<S>> {
    let num = eval_poly_at_rational_function(f.num(), arg);
    let den = eval_poly_at_rational_function(f.den(), arg);
    if den.is_zero() {
        return Err(OghamError::new(
            OghamErrorKind::DivisionByZero,
            span,
            "rational-function evaluation hit a pole",
        ));
    }
    Ok(num.mul(&den.inv().expect("checked nonzero rational function")))
}

fn eval_poly_at_rational_function<S: ExactFieldScalar>(
    poly: &Poly<S>,
    x: &RationalFunction<S>,
) -> RationalFunction<S> {
    let mut acc = RationalFunction::zero();
    for c in poly.coeffs().iter().rev() {
        acc = acc.mul(x).add(&RationalFunction::from_base(c.clone()));
    }
    acc
}

#[derive(Clone, Copy)]
enum ExpectedSort {
    Any,
    Known(Sort),
}

fn value_to_expr<E: Display>(value: &Value<E>) -> OghamResult<Expr> {
    match value {
        Value::Element(value) => parse_display_expr(&value.to_string()),
        Value::Index(value) => Ok(index_literal_expr(*value)?),
        Value::Bool(value) => Ok(Expr::Bool(*value)),
        Value::Function(function) => Ok(function.to_expr()),
    }
}

fn contains_free_name(expr: &Expr, target: &str) -> bool {
    fn visit(expr: &Expr, target: &str, bound: &BTreeSet<String>) -> bool {
        match expr {
            Expr::Ident(name) => name == target && !bound.contains(name),
            Expr::Lambda { binders, body } => {
                let mut nested = bound.clone();
                nested.extend(binders.iter().cloned());
                visit(body, target, &nested)
            }
            Expr::Block { bindings, body } => {
                let mut nested = bound.clone();
                for binding in bindings {
                    if binding.recursive {
                        nested.insert(binding.name.clone());
                    }
                    if visit(&binding.expr, target, &nested) {
                        return true;
                    }
                    nested.insert(binding.name.clone());
                }
                visit(body, target, &nested)
            }
            Expr::Vector(items) | Expr::Tuple(items) => {
                items.iter().any(|item| visit(item, target, bound))
            }
            Expr::GameForm { left, right } => left
                .iter()
                .chain(right)
                .any(|item| visit(item, target, bound)),
            Expr::Call { args, .. } => args.iter().any(|arg| visit(arg, target, bound)),
            Expr::Factorial(inner) => visit(inner, target, bound),
            Expr::Unary { expr, .. } => visit(expr, target, bound),
            Expr::Binary { lhs, rhs, .. } | Expr::Relation { lhs, rhs, .. } => {
                visit(lhs, target, bound) || visit(rhs, target, bound)
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                visit(cond, target, bound)
                    || visit(then_expr, target, bound)
                    || visit(else_expr, target, bound)
            }
            Expr::Int(_) | Expr::Bool(_) | Expr::Star(_) | Expr::Omega | Expr::Blade(_) => false,
        }
    }

    visit(expr, target, &BTreeSet::new())
}

fn ensure_source_nesting_depth(src: &str) -> OghamResult<()> {
    let mut depth = 0_u128;
    for line in src.lines() {
        for ch in line.chars().take_while(|ch| *ch != '#') {
            match ch {
                '(' | '[' | '{' => {
                    depth += 1;
                    if depth > AST_DEPTH_GUARD {
                        return Err(OghamError::new(
                            OghamErrorKind::Parse,
                            Span::point(0),
                            format!(
                                "source nesting exceeds the depth safety guard of {AST_DEPTH_GUARD} delimiters; the parser stack is bounded"
                            ),
                        ));
                    }
                }
                ')' | ']' | '}' => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    Ok(())
}

fn ensure_statement_depth(statement: &Statement) -> OghamResult<()> {
    enum SyntaxNode<'a> {
        Statement(&'a Statement),
        Expr(&'a Expr),
    }

    let mut pending = vec![(SyntaxNode::Statement(statement), 1_u128)];
    while let Some((node, depth)) = pending.pop() {
        if depth > AST_DEPTH_GUARD {
            return Err(OghamError::new(
                OghamErrorKind::Parse,
                Span::point(0),
                format!(
                    "statement syntax tree exceeds the depth safety guard of {AST_DEPTH_GUARD} nodes; recursive AST consumers require bounded input depth"
                ),
            ));
        }
        let child_depth = depth + 1;
        match node {
            SyntaxNode::Statement(Statement::Binding { expr, .. })
            | SyntaxNode::Statement(Statement::Expr(expr)) => {
                pending.push((SyntaxNode::Expr(expr), child_depth));
            }
            SyntaxNode::Statement(Statement::Seq { bindings, tail }) => {
                pending.push((SyntaxNode::Statement(tail), child_depth));
                pending.extend(
                    bindings
                        .iter()
                        .map(|binding| (SyntaxNode::Expr(&binding.expr), child_depth)),
                );
            }
            SyntaxNode::Expr(
                Expr::Int(_)
                | Expr::Bool(_)
                | Expr::Star(_)
                | Expr::Omega
                | Expr::Blade(_)
                | Expr::Ident(_),
            ) => {}
            SyntaxNode::Expr(Expr::Vector(items) | Expr::Tuple(items)) => {
                pending.extend(
                    items
                        .iter()
                        .map(|item| (SyntaxNode::Expr(item), child_depth)),
                );
            }
            SyntaxNode::Expr(Expr::Lambda { body, .. } | Expr::Factorial(body)) => {
                pending.push((SyntaxNode::Expr(body), child_depth));
            }
            SyntaxNode::Expr(Expr::Block { bindings, body }) => {
                pending.push((SyntaxNode::Expr(body), child_depth));
                pending.extend(
                    bindings
                        .iter()
                        .map(|binding| (SyntaxNode::Expr(&binding.expr), child_depth)),
                );
            }
            SyntaxNode::Expr(Expr::GameForm { left, right }) => {
                pending.extend(
                    left.iter()
                        .chain(right)
                        .map(|item| (SyntaxNode::Expr(item), child_depth)),
                );
            }
            SyntaxNode::Expr(Expr::Call { args, .. }) => {
                pending.extend(args.iter().map(|arg| (SyntaxNode::Expr(arg), child_depth)));
            }
            SyntaxNode::Expr(Expr::Unary { expr, .. }) => {
                pending.push((SyntaxNode::Expr(expr), child_depth));
            }
            SyntaxNode::Expr(Expr::Binary { lhs, rhs, .. })
            | SyntaxNode::Expr(Expr::Relation { lhs, rhs, .. }) => {
                pending.push((SyntaxNode::Expr(lhs), child_depth));
                pending.push((SyntaxNode::Expr(rhs), child_depth));
            }
            SyntaxNode::Expr(Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            }) => {
                pending.push((SyntaxNode::Expr(cond), child_depth));
                pending.push((SyntaxNode::Expr(then_expr), child_depth));
                pending.push((SyntaxNode::Expr(else_expr), child_depth));
            }
        }
    }
    Ok(())
}

fn consume_fuel(function: &FunctionValue, remaining: &mut u128, budget: u128) -> OghamResult<()> {
    let Some(name) = &function.mu_name else {
        return Ok(());
    };
    if *remaining == 0 {
        return Err(OghamError::new(
            OghamErrorKind::Fuel,
            Span::point(0),
            format!("recursive definition `{name}` exhausted its fuel budget of {budget}"),
        ));
    }
    *remaining -= 1;
    Ok(())
}

fn enter_recursion_frame(
    function: &FunctionValue,
    depth: &mut u128,
    remaining: u128,
    budget: u128,
) -> OghamResult<bool> {
    let Some(name) = &function.mu_name else {
        return Ok(false);
    };
    if *depth >= RECURSION_DEPTH_GUARD {
        return Err(OghamError::new(
            OghamErrorKind::Fuel,
            Span::point(0),
            format!(
                "recursive definition `{name}` reached the recursion depth safety guard ({RECURSION_DEPTH_GUARD} frames); fuel budget {budget} has {remaining} step(s) remaining, but the host stack is not unbounded"
            ),
        ));
    }
    *depth += 1;
    Ok(true)
}

fn leave_recursion_frame(entered: bool, depth: &mut u128) {
    if entered {
        *depth -= 1;
    }
}

fn parse_display_expr(src: &str) -> OghamResult<Expr> {
    match parse_statement(src)? {
        Statement::Expr(expr) => Ok(expr),
        Statement::Binding { .. } | Statement::Seq { .. } => {
            Err(parse_error("display did not round-trip as expression"))
        }
    }
}

fn index_literal_expr(value: i128) -> OghamResult<Expr> {
    if value >= 0 {
        Ok(Expr::Int(value as u128))
    } else {
        Ok(Expr::Unary {
            op: UnaryOp::Neg,
            expr: Box::new(Expr::Int(value.unsigned_abs())),
        })
    }
}

fn value_sort<E>(value: &Value<E>) -> Sort {
    match value {
        Value::Element(_) => Sort::Element,
        Value::Index(_) => Sort::Index,
        Value::Bool(_) => Sort::Bool,
        Value::Function(_) => unreachable!("Function values are not first-order binder sorts"),
    }
}

fn env_sort<E>(value: &Value<E>) -> OghamResult<Sort> {
    match value {
        Value::Element(_) => Ok(Sort::Element),
        Value::Index(_) => Ok(Sort::Index),
        Value::Bool(_) => Ok(Sort::Bool),
        Value::Function(_) => Err(fn_sort_error()),
    }
}

fn ensure_value_sort<E>(value: &Value<E>, expected: Sort) -> OghamResult<()> {
    match value {
        Value::Function(_) => Err(fn_sort_error()),
        _ if value_sort(value) == expected => Ok(()),
        Value::Bool(_) => Err(bool_sort_error()),
        _ if expected == Sort::Bool => Err(bool_sort_error()),
        _ => Err(index_sort_error()),
    }
}

fn substitute_env<E: Display>(
    expr: &Expr,
    bound: &BTreeSet<String>,
    env: &BTreeMap<String, Value<E>>,
) -> OghamResult<Expr> {
    match expr {
        Expr::Ident(name) if !bound.contains(name) => {
            if let Some(value) = env.get(name) {
                value_to_expr(value)
            } else {
                Ok(expr.clone())
            }
        }
        Expr::Lambda { binders, body } => {
            let mut nested_bound = bound.clone();
            nested_bound.extend(binders.iter().cloned());
            Ok(Expr::Lambda {
                binders: binders.clone(),
                body: Box::new(substitute_env(body, &nested_bound, env)?),
            })
        }
        Expr::Block { bindings, body } => {
            let mut nested_bound = bound.clone();
            let mut out = Vec::with_capacity(bindings.len());
            for binding in bindings {
                if binding.recursive {
                    nested_bound.insert(binding.name.clone());
                }
                out.push(Binding {
                    name: binding.name.clone(),
                    expr: substitute_env(&binding.expr, &nested_bound, env)?,
                    recursive: binding.recursive,
                });
                nested_bound.insert(binding.name.clone());
            }
            Ok(Expr::Block {
                bindings: out,
                body: Box::new(substitute_env(body, &nested_bound, env)?),
            })
        }
        Expr::Vector(items) => Ok(Expr::Vector(
            items
                .iter()
                .map(|item| substitute_env(item, bound, env))
                .collect::<OghamResult<Vec<_>>>()?,
        )),
        Expr::Tuple(items) => Ok(Expr::Tuple(
            items
                .iter()
                .map(|item| substitute_env(item, bound, env))
                .collect::<OghamResult<Vec<_>>>()?,
        )),
        Expr::GameForm { left, right } => Ok(Expr::GameForm {
            left: left
                .iter()
                .map(|item| substitute_env(item, bound, env))
                .collect::<OghamResult<Vec<_>>>()?,
            right: right
                .iter()
                .map(|item| substitute_env(item, bound, env))
                .collect::<OghamResult<Vec<_>>>()?,
        }),
        Expr::Call { name, args } => Ok(Expr::Call {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| substitute_env(arg, bound, env))
                .collect::<OghamResult<Vec<_>>>()?,
        }),
        Expr::Factorial(inner) => Ok(Expr::Factorial(Box::new(substitute_env(
            inner, bound, env,
        )?))),
        Expr::Unary { op, expr } => Ok(Expr::Unary {
            op: *op,
            expr: Box::new(substitute_env(expr, bound, env)?),
        }),
        Expr::Binary { op, lhs, rhs } => Ok(Expr::Binary {
            op: *op,
            lhs: Box::new(substitute_env(lhs, bound, env)?),
            rhs: Box::new(substitute_env(rhs, bound, env)?),
        }),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => Ok(Expr::Ternary {
            cond: Box::new(substitute_env(cond, bound, env)?),
            then_expr: Box::new(substitute_env(then_expr, bound, env)?),
            else_expr: Box::new(substitute_env(else_expr, bound, env)?),
        }),
        Expr::Relation { op, lhs, rhs } => Ok(Expr::Relation {
            op: *op,
            lhs: Box::new(substitute_env(lhs, bound, env)?),
            rhs: Box::new(substitute_env(rhs, bound, env)?),
        }),
        _ => Ok(expr.clone()),
    }
}

fn substitute_names(expr: &Expr, replacements: &BTreeMap<String, Expr>) -> Expr {
    match expr {
        Expr::Ident(name) => replacements
            .get(name)
            .cloned()
            .unwrap_or_else(|| expr.clone()),
        Expr::Lambda { binders, body } => {
            let mut nested = replacements.clone();
            for binder in binders {
                nested.remove(binder);
            }
            Expr::Lambda {
                binders: binders.clone(),
                body: Box::new(substitute_names(body, &nested)),
            }
        }
        Expr::Block { bindings, body } => {
            let mut nested = replacements.clone();
            let mut out = Vec::with_capacity(bindings.len());
            for binding in bindings {
                if binding.recursive {
                    nested.remove(&binding.name);
                }
                out.push(Binding {
                    name: binding.name.clone(),
                    expr: substitute_names(&binding.expr, &nested),
                    recursive: binding.recursive,
                });
                nested.remove(&binding.name);
            }
            Expr::Block {
                bindings: out,
                body: Box::new(substitute_names(body, &nested)),
            }
        }
        Expr::Vector(items) => Expr::Vector(
            items
                .iter()
                .map(|item| substitute_names(item, replacements))
                .collect(),
        ),
        Expr::Tuple(items) => Expr::Tuple(
            items
                .iter()
                .map(|item| substitute_names(item, replacements))
                .collect(),
        ),
        Expr::GameForm { left, right } => Expr::GameForm {
            left: left
                .iter()
                .map(|item| substitute_names(item, replacements))
                .collect(),
            right: right
                .iter()
                .map(|item| substitute_names(item, replacements))
                .collect(),
        },
        Expr::Call { name, args } => Expr::Call {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| substitute_names(arg, replacements))
                .collect(),
        },
        Expr::Factorial(inner) => Expr::Factorial(Box::new(substitute_names(inner, replacements))),
        Expr::Unary { op, expr } => Expr::Unary {
            op: *op,
            expr: Box::new(substitute_names(expr, replacements)),
        },
        Expr::Binary { op, lhs, rhs } => Expr::Binary {
            op: *op,
            lhs: Box::new(substitute_names(lhs, replacements)),
            rhs: Box::new(substitute_names(rhs, replacements)),
        },
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => Expr::Ternary {
            cond: Box::new(substitute_names(cond, replacements)),
            then_expr: Box::new(substitute_names(then_expr, replacements)),
            else_expr: Box::new(substitute_names(else_expr, replacements)),
        },
        Expr::Relation { op, lhs, rhs } => Expr::Relation {
            op: *op,
            lhs: Box::new(substitute_names(lhs, replacements)),
            rhs: Box::new(substitute_names(rhs, replacements)),
        },
        _ => expr.clone(),
    }
}

fn beta_normalize(expr: Expr) -> OghamResult<Expr> {
    match expr {
        Expr::Vector(items) => Ok(Expr::Vector(
            items
                .into_iter()
                .map(beta_normalize)
                .collect::<OghamResult<Vec<_>>>()?,
        )),
        Expr::Tuple(items) => Ok(Expr::Tuple(
            items
                .into_iter()
                .map(beta_normalize)
                .collect::<OghamResult<Vec<_>>>()?,
        )),
        Expr::GameForm { left, right } => Ok(Expr::GameForm {
            left: left
                .into_iter()
                .map(beta_normalize)
                .collect::<OghamResult<Vec<_>>>()?,
            right: right
                .into_iter()
                .map(beta_normalize)
                .collect::<OghamResult<Vec<_>>>()?,
        }),
        Expr::Lambda { binders, body } => Ok(Expr::Lambda {
            binders,
            body: Box::new(beta_normalize(*body)?),
        }),
        Expr::Block { bindings, body } => Ok(Expr::Block {
            bindings: bindings
                .into_iter()
                .map(|binding| {
                    beta_normalize(binding.expr).map(|expr| Binding {
                        name: binding.name,
                        expr,
                        recursive: binding.recursive,
                    })
                })
                .collect::<OghamResult<Vec<_>>>()?,
            body: Box::new(beta_normalize(*body)?),
        }),
        Expr::Call { name, args } => Ok(Expr::Call {
            name,
            args: args
                .into_iter()
                .map(beta_normalize)
                .collect::<OghamResult<Vec<_>>>()?,
        }),
        Expr::Factorial(inner) => Ok(Expr::Factorial(Box::new(beta_normalize(*inner)?))),
        Expr::Unary { op, expr } => Ok(Expr::Unary {
            op,
            expr: Box::new(beta_normalize(*expr)?),
        }),
        Expr::Binary {
            op: BinaryOp::At,
            lhs,
            rhs,
        } => {
            let lhs = beta_normalize(*lhs)?;
            let rhs = beta_normalize(*rhs)?;
            if let Expr::Lambda {
                binders,
                body: lhs_body,
            } = lhs
            {
                if let Expr::Lambda {
                    binders: rhs_binders,
                    body: rhs_body,
                } = rhs
                {
                    if binders.len() != 1 {
                        return Err(OghamError::new(
                            OghamErrorKind::Arity,
                            Span::point(0),
                            "function composition needs a unary head",
                        ));
                    }
                    let mut replacements = BTreeMap::new();
                    replacements.insert(binders[0].clone(), *rhs_body);
                    return Ok(Expr::Lambda {
                        binders: rhs_binders,
                        body: Box::new(beta_normalize(substitute_names(&lhs_body, &replacements))?),
                    });
                }
                let args = match rhs {
                    Expr::Tuple(items) => items,
                    value => vec![value],
                };
                if args.len() != binders.len() {
                    return Err(OghamError::new(
                        OghamErrorKind::Arity,
                        Span::point(0),
                        format!(
                            "function expects {} argument(s), got {}",
                            binders.len(),
                            args.len()
                        ),
                    ));
                }
                let replacements = binders.into_iter().zip(args).collect();
                return beta_normalize(substitute_names(&lhs_body, &replacements));
            }
            Ok(Expr::Binary {
                op: BinaryOp::At,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            })
        }
        Expr::Binary { op, lhs, rhs } => Ok(Expr::Binary {
            op,
            lhs: Box::new(beta_normalize(*lhs)?),
            rhs: Box::new(beta_normalize(*rhs)?),
        }),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => Ok(Expr::Ternary {
            cond: Box::new(beta_normalize(*cond)?),
            then_expr: Box::new(beta_normalize(*then_expr)?),
            else_expr: Box::new(beta_normalize(*else_expr)?),
        }),
        Expr::Relation { op, lhs, rhs } => Ok(Expr::Relation {
            op,
            lhs: Box::new(beta_normalize(*lhs)?),
            rhs: Box::new(beta_normalize(*rhs)?),
        }),
        _ => Ok(expr),
    }
}

fn check_binders(binders: &[String], is_world_shadow: impl Fn(&str) -> bool) -> OghamResult<()> {
    let mut seen = BTreeSet::new();
    for binder in binders {
        if !seen.insert(binder.clone()) {
            return Err(OghamError::new(
                OghamErrorKind::Shadow,
                Span::point(0),
                format!("duplicate binder `{binder}`"),
            ));
        }
        if is_world_shadow(binder) {
            return Err(OghamError::new(
                OghamErrorKind::Shadow,
                Span::point(0),
                format!("binder `{binder}` shadows a reserved name"),
            ));
        }
    }
    Ok(())
}

fn infer_function_signature(body: &Expr, binders: &[String]) -> OghamResult<(Vec<Sort>, Sort)> {
    let mut slots = binders
        .iter()
        .map(|name| (name.clone(), None))
        .collect::<BTreeMap<String, Option<Sort>>>();
    let ret = infer_expr_sort(body, ExpectedSort::Any, &mut slots)?;
    let sorts = binders
        .iter()
        .map(|name| {
            slots
                .get(name)
                .and_then(|sort| *sort)
                .unwrap_or(Sort::Element)
        })
        .collect();
    Ok((sorts, ret))
}

fn infer_expr_sort(
    expr: &Expr,
    expected: ExpectedSort,
    binders: &mut BTreeMap<String, Option<Sort>>,
) -> OghamResult<Sort> {
    match expr {
        Expr::Bool(_) => expect_sort(Sort::Bool, expected),
        Expr::Int(_) | Expr::Star(_) | Expr::Omega | Expr::Blade(_) => {
            expect_sort(default_sort(expected), expected)
        }
        Expr::Vector(items) => {
            for item in items {
                infer_expr_sort(item, ExpectedSort::Known(Sort::Element), binders)?;
            }
            expect_sort(Sort::Element, expected)
        }
        Expr::GameForm { left, right } => {
            for item in left.iter().chain(right) {
                infer_expr_sort(item, ExpectedSort::Known(Sort::Element), binders)?;
            }
            expect_sort(Sort::Element, expected)
        }
        Expr::Block { bindings, body } => {
            for binding in bindings {
                infer_block_binding_rhs(&binding.expr, binders)?;
            }
            infer_expr_sort(body, expected, binders)
        }
        Expr::Tuple(_) | Expr::Lambda { .. } => Err(fn_sort_error()),
        Expr::Ident(name) => {
            if binders.contains_key(name) {
                let sort = default_sort(expected);
                mark_binder_sort(binders, name, sort)?;
                Ok(sort)
            } else {
                expect_sort(default_sort(expected), expected)
            }
        }
        Expr::Call { name, args } => match name.as_str() {
            "nleft" | "nright" => {
                expect_arity(name, args, 1)?;
                infer_expr_sort(&args[0], ExpectedSort::Known(Sort::Element), binders)?;
                expect_sort(Sort::Index, expected)
            }
            "left" | "right" => {
                expect_arity(name, args, 2)?;
                infer_expr_sort(&args[0], ExpectedSort::Known(Sort::Element), binders)?;
                infer_expr_sort(&args[1], ExpectedSort::Known(Sort::Index), binders)?;
                expect_sort(Sort::Element, expected)
            }
            "canon" => {
                expect_arity(name, args, 1)?;
                infer_expr_sort(&args[0], ExpectedSort::Known(Sort::Element), binders)?;
                expect_sort(Sort::Element, expected)
            }
            "up" | "down" => {
                expect_arity(name, args, 0)?;
                expect_sort(Sort::Element, expected)
            }
            "drawn" => {
                expect_arity(name, args, 1)?;
                infer_expr_sort(&args[0], ExpectedSort::Known(Sort::Element), binders)?;
                expect_sort(Sort::Bool, expected)
            }
            "dim" => {
                expect_arity(name, args, 0)?;
                expect_sort(Sort::Index, expected)
            }
            "coef" => {
                expect_arity(name, args, 2)?;
                infer_expr_sort(&args[0], ExpectedSort::Known(Sort::Element), binders)?;
                infer_expr_sort(&args[1], ExpectedSort::Known(Sort::Index), binders)?;
                expect_sort(Sort::Element, expected)
            }
            "deg" => {
                expect_arity(name, args, 1)?;
                infer_expr_sort(&args[0], ExpectedSort::Known(Sort::Element), binders)?;
                expect_sort(Sort::Index, expected)
            }
            "grade" => {
                expect_arity(name, args, 2)?;
                infer_expr_sort(&args[0], ExpectedSort::Known(Sort::Element), binders)?;
                infer_expr_sort(&args[1], ExpectedSort::Known(Sort::Index), binders)?;
                expect_sort(Sort::Element, expected)
            }
            "rev" | "even" | "dual" | "frob" => {
                expect_arity(name, args, 1)?;
                infer_expr_sort(&args[0], ExpectedSort::Known(Sort::Element), binders)?;
                expect_sort(Sort::Element, expected)
            }
            "tr" => {
                if args.is_empty() || args.len() > 2 {
                    return Err(OghamError::new(
                        OghamErrorKind::Arity,
                        Span::point(0),
                        "`tr` expects one or two arguments",
                    ));
                }
                infer_expr_sort(&args[0], ExpectedSort::Known(Sort::Element), binders)?;
                if args.len() == 2 {
                    infer_expr_sort(&args[1], ExpectedSort::Known(Sort::Index), binders)?;
                }
                expect_sort(Sort::Element, expected)
            }
            "gcd" => {
                expect_arity(name, args, 2)?;
                infer_expr_sort(&args[0], ExpectedSort::Known(Sort::Element), binders)?;
                infer_expr_sort(&args[1], ExpectedSort::Known(Sort::Element), binders)?;
                expect_sort(Sort::Element, expected)
            }
            _ => Err(OghamError::new(
                OghamErrorKind::UnknownFn,
                Span::point(0),
                format!("unknown function `{name}`"),
            )),
        },
        Expr::Factorial(inner) => {
            infer_expr_sort(inner, ExpectedSort::Known(Sort::Index), binders)?;
            expect_sort(Sort::Element, expected)
        }
        Expr::Unary { op, expr } => match op {
            UnaryOp::Not => {
                infer_expr_sort(expr, ExpectedSort::Known(Sort::Bool), binders)?;
                expect_sort(Sort::Bool, expected)
            }
            UnaryOp::Neg => {
                let sort = default_sort(expected);
                infer_expr_sort(expr, ExpectedSort::Known(sort), binders)?;
                expect_sort(sort, expected)
            }
            UnaryOp::Inv => {
                infer_expr_sort(expr, ExpectedSort::Known(Sort::Element), binders)?;
                expect_sort(Sort::Element, expected)
            }
        },
        Expr::Binary { op, lhs, rhs } => match op {
            BinaryOp::And | BinaryOp::Or => {
                infer_expr_sort(lhs, ExpectedSort::Known(Sort::Bool), binders)?;
                infer_expr_sort(rhs, ExpectedSort::Known(Sort::Bool), binders)?;
                expect_sort(Sort::Bool, expected)
            }
            BinaryOp::Pow => {
                let sort = match expected {
                    ExpectedSort::Known(Sort::Index) => Sort::Index,
                    _ => Sort::Element,
                };
                infer_expr_sort(lhs, ExpectedSort::Known(sort), binders)?;
                infer_expr_sort(rhs, ExpectedSort::Known(Sort::Index), binders)?;
                expect_sort(sort, expected)
            }
            BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul => {
                let sort = default_sort(expected);
                infer_expr_sort(lhs, ExpectedSort::Known(sort), binders)?;
                infer_expr_sort(rhs, ExpectedSort::Known(sort), binders)?;
                expect_sort(sort, expected)
            }
            BinaryOp::Div | BinaryOp::Rem | BinaryOp::Wedge | BinaryOp::Append => {
                infer_expr_sort(lhs, ExpectedSort::Known(Sort::Element), binders)?;
                infer_expr_sort(rhs, ExpectedSort::Known(Sort::Element), binders)?;
                expect_sort(Sort::Element, expected)
            }
            BinaryOp::At => expect_sort(default_sort(expected), expected),
        },
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            infer_expr_sort(cond, ExpectedSort::Known(Sort::Bool), binders)?;
            let branch_expected = expected;
            let then_sort = infer_expr_sort(then_expr, branch_expected, binders)?;
            let else_sort = infer_expr_sort(else_expr, ExpectedSort::Known(then_sort), binders)?;
            if then_sort != else_sort {
                return Err(sort_mismatch(then_sort, else_sort));
            }
            expect_sort(then_sort, expected)
        }
        Expr::Relation { op, lhs, rhs } => {
            let sort = relation_operand_sort(*op, lhs, rhs);
            infer_expr_sort(lhs, ExpectedSort::Known(sort), binders)?;
            infer_expr_sort(rhs, ExpectedSort::Known(sort), binders)?;
            expect_sort(Sort::Bool, expected)
        }
    }
}

fn infer_block_binding_rhs(
    rhs: &Expr,
    binders: &mut BTreeMap<String, Option<Sort>>,
) -> OghamResult<()> {
    match rhs {
        Expr::Lambda {
            binders: local_binders,
            body,
        } => infer_nested_lambda_body(local_binders, body, binders),
        _ => infer_expr_sort(rhs, ExpectedSort::Any, binders).map(|_| ()),
    }
}

fn infer_nested_lambda_body(
    local_binders: &[String],
    body: &Expr,
    binders: &mut BTreeMap<String, Option<Sort>>,
) -> OghamResult<()> {
    let local = local_binders.iter().cloned().collect::<BTreeSet<_>>();
    let mut nested = binders.clone();
    for name in local_binders {
        nested.insert(name.clone(), None);
    }
    infer_expr_sort(body, ExpectedSort::Any, &mut nested)?;
    for name in binders.keys().cloned().collect::<Vec<_>>() {
        if local.contains(&name) {
            continue;
        }
        if let Some(sort) = nested.get(&name).and_then(|sort| *sort) {
            mark_binder_sort(binders, &name, sort)?;
        }
    }
    Ok(())
}

fn relation_operand_sort(op: RelOp, lhs: &Expr, rhs: &Expr) -> Sort {
    if op == RelOp::Fuzzy {
        Sort::Element
    } else if op == RelOp::Eq && (bool_shaped(lhs) || bool_shaped(rhs)) {
        Sort::Bool
    } else if index_shaped(lhs) || index_shaped(rhs) {
        Sort::Index
    } else {
        Sort::Element
    }
}

fn default_sort(expected: ExpectedSort) -> Sort {
    match expected {
        ExpectedSort::Known(sort) => sort,
        ExpectedSort::Any => Sort::Element,
    }
}

fn expect_sort(actual: Sort, expected: ExpectedSort) -> OghamResult<Sort> {
    match expected {
        ExpectedSort::Any => Ok(actual),
        ExpectedSort::Known(expected) if expected == actual => Ok(actual),
        ExpectedSort::Known(expected) => Err(sort_mismatch(expected, actual)),
    }
}

fn mark_binder_sort(
    binders: &mut BTreeMap<String, Option<Sort>>,
    name: &str,
    sort: Sort,
) -> OghamResult<()> {
    let slot = binders
        .get_mut(name)
        .expect("binder existence checked before mark");
    match slot {
        Some(existing) if *existing != sort => Err(sort_mismatch(*existing, sort)),
        Some(_) => Ok(()),
        None => {
            *slot = Some(sort);
            Ok(())
        }
    }
}

fn index_shaped(expr: &Expr) -> bool {
    match expr {
        Expr::Call { name, .. } if matches!(name.as_str(), "deg" | "dim" | "nleft" | "nright") => {
            true
        }
        Expr::Block { body, .. } => index_shaped(body),
        Expr::Unary {
            op: UnaryOp::Neg,
            expr,
        } => index_shaped(expr),
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Pow,
            lhs,
            rhs,
        } => index_shaped(lhs) || index_shaped(rhs),
        _ => false,
    }
}

fn bool_shaped(expr: &Expr) -> bool {
    match expr {
        Expr::Bool(_)
        | Expr::Relation { .. }
        | Expr::Unary {
            op: UnaryOp::Not, ..
        }
        | Expr::Binary {
            op: BinaryOp::And | BinaryOp::Or,
            ..
        } => true,
        Expr::Call { name, .. } if name == "drawn" => true,
        Expr::Block { body, .. } => bool_shaped(body),
        _ => false,
    }
}

fn static_sort<E>(
    expr: &Expr,
    env: &BTreeMap<String, Value<E>>,
    deg_is_index: bool,
) -> OghamResult<Sort> {
    match expr {
        Expr::Bool(_) | Expr::Relation { .. } => Ok(Sort::Bool),
        Expr::Lambda { .. } | Expr::Tuple(_) => Err(fn_sort_error()),
        Expr::Block { bindings, body } => {
            let mut local_sorts = env
                .iter()
                .map(|(name, value)| env_sort(value).map(|sort| (name.clone(), sort)))
                .collect::<OghamResult<BTreeMap<_, _>>>()?;
            for binding in bindings {
                let sort = static_sort_with_sorts(&binding.expr, &local_sorts, deg_is_index)?;
                local_sorts.insert(binding.name.clone(), sort);
            }
            static_sort_with_sorts(body, &local_sorts, deg_is_index)
        }
        Expr::Ident(name) => match env.get(name) {
            Some(Value::Element(_)) => Ok(Sort::Element),
            Some(Value::Index(_)) => Ok(Sort::Index),
            Some(Value::Bool(_)) => Ok(Sort::Bool),
            Some(Value::Function(_)) => Err(fn_sort_error()),
            None => Ok(Sort::Element),
        },
        Expr::Call { name, .. }
            if matches!(name.as_str(), "dim" | "nleft" | "nright")
                || (deg_is_index && name == "deg") =>
        {
            Ok(Sort::Index)
        }
        Expr::Call { name, .. } if name == "drawn" => Ok(Sort::Bool),
        Expr::Unary {
            op: UnaryOp::Not, ..
        } => Ok(Sort::Bool),
        Expr::Unary { expr, .. } => static_sort(expr, env, deg_is_index),
        Expr::Binary {
            op: BinaryOp::At,
            lhs,
            ..
        } => match &**lhs {
            Expr::Ident(name) => match env.get(name) {
                Some(Value::Function(function)) => Ok(function.ret),
                _ => Ok(Sort::Element),
            },
            _ => Ok(Sort::Element),
        },
        Expr::Binary {
            op: BinaryOp::And | BinaryOp::Or,
            ..
        } => Ok(Sort::Bool),
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Pow,
            lhs,
            rhs,
        } => {
            let lhs = static_sort(lhs, env, deg_is_index).unwrap_or(Sort::Element);
            let rhs = static_sort(rhs, env, deg_is_index).unwrap_or(Sort::Element);
            if lhs == Sort::Bool || rhs == Sort::Bool {
                Ok(Sort::Bool)
            } else if lhs == Sort::Index || rhs == Sort::Index {
                Ok(Sort::Index)
            } else {
                Ok(Sort::Element)
            }
        }
        Expr::Ternary {
            then_expr,
            else_expr,
            ..
        } => {
            let then_sort = static_sort(then_expr, env, deg_is_index)?;
            let else_sort = static_sort(else_expr, env, deg_is_index)?;
            if then_sort == else_sort {
                Ok(then_sort)
            } else {
                Err(sort_mismatch(then_sort, else_sort))
            }
        }
        _ => Ok(Sort::Element),
    }
}

fn static_sort_with_sorts(
    expr: &Expr,
    env: &BTreeMap<String, Sort>,
    deg_is_index: bool,
) -> OghamResult<Sort> {
    match expr {
        Expr::Bool(_) | Expr::Relation { .. } => Ok(Sort::Bool),
        Expr::Lambda { .. } | Expr::Tuple(_) => Err(fn_sort_error()),
        Expr::Block { bindings, body } => {
            let mut local = env.clone();
            for binding in bindings {
                let sort = static_sort_with_sorts(&binding.expr, &local, deg_is_index)?;
                local.insert(binding.name.clone(), sort);
            }
            static_sort_with_sorts(body, &local, deg_is_index)
        }
        Expr::Ident(name) => Ok(env.get(name).copied().unwrap_or(Sort::Element)),
        Expr::Call { name, .. }
            if matches!(name.as_str(), "dim" | "nleft" | "nright")
                || (deg_is_index && name == "deg") =>
        {
            Ok(Sort::Index)
        }
        Expr::Call { name, .. } if name == "drawn" => Ok(Sort::Bool),
        Expr::Unary {
            op: UnaryOp::Not, ..
        } => Ok(Sort::Bool),
        Expr::Unary { expr, .. } => static_sort_with_sorts(expr, env, deg_is_index),
        Expr::Binary {
            op: BinaryOp::And | BinaryOp::Or,
            ..
        } => Ok(Sort::Bool),
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Pow,
            lhs,
            rhs,
        } => {
            let lhs = static_sort_with_sorts(lhs, env, deg_is_index).unwrap_or(Sort::Element);
            let rhs = static_sort_with_sorts(rhs, env, deg_is_index).unwrap_or(Sort::Element);
            if lhs == Sort::Bool || rhs == Sort::Bool {
                Ok(Sort::Bool)
            } else if lhs == Sort::Index || rhs == Sort::Index {
                Ok(Sort::Index)
            } else {
                Ok(Sort::Element)
            }
        }
        Expr::Ternary {
            then_expr,
            else_expr,
            ..
        } => {
            let then_sort = static_sort_with_sorts(then_expr, env, deg_is_index)?;
            let else_sort = static_sort_with_sorts(else_expr, env, deg_is_index)?;
            if then_sort == else_sort {
                Ok(then_sort)
            } else {
                Err(sort_mismatch(then_sort, else_sort))
            }
        }
        _ => Ok(Sort::Element),
    }
}

fn reserved_function_binder(name: &str) -> bool {
    matches!(
        name,
        "rev"
            | "grade"
            | "even"
            | "dual"
            | "frob"
            | "tr"
            | "deg"
            | "gcd"
            | "coef"
            | "dim"
            | "canon"
            | "nleft"
            | "nright"
            | "left"
            | "right"
            | "up"
            | "down"
            | "drawn"
    )
}

fn sort_mismatch(expected: Sort, actual: Sort) -> OghamError {
    if expected == Sort::Bool || actual == Sort::Bool {
        bool_sort_error()
    } else {
        index_sort_error()
    }
}

fn ignore_static_partiality<E>(result: OghamResult<Value<E>>) -> OghamResult<()> {
    match result {
        Ok(_) => Ok(()),
        Err(err) if is_runtime_partiality(err.kind) => Ok(()),
        Err(err) => Err(err),
    }
}

fn is_runtime_partiality(kind: OghamErrorKind) -> bool {
    matches!(
        kind,
        OghamErrorKind::DivisionByZero
            | OghamErrorKind::NotInvertible
            | OghamErrorKind::Domain
            | OghamErrorKind::Overflow
            | OghamErrorKind::KummerEscape
            | OghamErrorKind::Modulus
    )
}

fn expression_is_index(expr: &Expr) -> bool {
    match expr {
        Expr::Call { name, .. } if matches!(name.as_str(), "deg" | "dim" | "nleft" | "nright") => {
            true
        }
        Expr::Unary { expr, .. } => expression_is_index(expr),
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul,
            lhs,
            rhs,
        } => expression_is_index(lhs) || expression_is_index(rhs),
        Expr::Binary {
            op: BinaryOp::Pow,
            lhs,
            rhs,
        } => expression_is_index(lhs) || (plain_index_expr(lhs) && expression_is_index(rhs)),
        _ => false,
    }
}

fn plain_index_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Int(_) => true,
        Expr::Call { name, .. } if matches!(name.as_str(), "deg" | "dim" | "nleft" | "nright") => {
            true
        }
        Expr::Unary {
            op: UnaryOp::Neg,
            expr,
        } => plain_index_expr(expr),
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Pow,
            lhs,
            rhs,
        } => plain_index_expr(lhs) && plain_index_expr(rhs),
        _ => false,
    }
}

fn eval_index_binary(op: BinaryOp, lhs: i128, rhs: i128) -> OghamResult<i128> {
    match op {
        BinaryOp::Add => lhs
            .checked_add(rhs)
            .ok_or_else(|| overflow("index addition overflowed i128")),
        BinaryOp::Sub => lhs
            .checked_sub(rhs)
            .ok_or_else(|| overflow("index subtraction overflowed i128")),
        BinaryOp::Mul => lhs
            .checked_mul(rhs)
            .ok_or_else(|| overflow("index multiplication overflowed i128")),
        BinaryOp::Pow => {
            if rhs < 0 {
                return Err(OghamError::new(
                    OghamErrorKind::Domain,
                    Span::point(0),
                    "index exponent must be non-negative",
                ));
            }
            checked_i128_pow(lhs, rhs as u128)
        }
        _ => Err(index_sort_error()),
    }
}

fn no_order_error() -> OghamError {
    OghamError::new(
        OghamErrorKind::WrongWorld,
        Span::point(0),
        "this world has no canonical order",
    )
}

fn integer_poly_gcd(
    lhs: &Poly<Integer>,
    rhs: &Poly<Integer>,
    span: Span,
) -> OghamResult<Poly<Integer>> {
    let lhs = integer_poly_to_rational(lhs);
    let rhs = integer_poly_to_rational(rhs);
    primitive_integer_poly_from_rational(&lhs.gcd(&rhs), span)
}

fn integer_poly_to_rational(p: &Poly<Integer>) -> Poly<Rational> {
    Poly::new(p.coeffs().iter().map(|c| Rational::from_int(c.0)).collect())
}

fn primitive_integer_poly_from_rational(
    p: &Poly<Rational>,
    span: Span,
) -> OghamResult<Poly<Integer>> {
    if p.is_zero() {
        return Ok(Poly::zero());
    }
    let mut scale = 1i128;
    for c in p.coeffs() {
        scale = lcm_positive_i128(scale, c.denom(), span)?;
    }
    let mut coeffs = Vec::with_capacity(p.coeffs().len());
    for c in p.coeffs() {
        let factor = scale / c.denom();
        coeffs.push(
            c.numer()
                .checked_mul(factor)
                .ok_or_else(|| overflow("integer polynomial gcd coefficient overflowed i128"))?,
        );
    }
    let content = gcd_i128_slice(&coeffs, span)?;
    if content > 1 {
        for c in &mut coeffs {
            *c /= content;
        }
    }
    if coeffs.last().is_some_and(|c| *c < 0) {
        for c in &mut coeffs {
            *c = c.checked_neg().ok_or_else(|| {
                overflow("integer polynomial gcd sign normalization overflowed i128")
            })?;
        }
    }
    Ok(Poly::new(coeffs.into_iter().map(Integer).collect()))
}

fn gcd_i128_slice(values: &[i128], span: Span) -> OghamResult<i128> {
    let mut g = 0u128;
    for value in values {
        g = gcd_u128_local(g, value.unsigned_abs());
    }
    i128::try_from(g).map_err(|_| {
        OghamError::new(
            OghamErrorKind::Overflow,
            span,
            "integer polynomial gcd content exceeds i128",
        )
    })
}

fn lcm_positive_i128(lhs: i128, rhs: i128, span: Span) -> OghamResult<i128> {
    debug_assert!(lhs > 0 && rhs > 0);
    let gcd = gcd_u128_local(lhs as u128, rhs as u128);
    let gcd = i128::try_from(gcd).map_err(|_| {
        OghamError::new(
            OghamErrorKind::Overflow,
            span,
            "integer polynomial denominator gcd exceeds i128",
        )
    })?;
    lhs.checked_div(gcd)
        .and_then(|x| x.checked_mul(rhs))
        .ok_or_else(|| overflow("integer polynomial denominator lcm overflowed i128"))
}

fn gcd_u128_local(mut lhs: u128, mut rhs: u128) -> u128 {
    while rhs != 0 {
        let next = lhs % rhs;
        lhs = rhs;
        rhs = next;
    }
    lhs
}

trait OghamScalar: Scalar + Sized + Display + 'static {
    fn bare_int(n: u128, span: Span) -> OghamResult<Self>;
    fn star(lit: &StarLiteral, span: Span) -> OghamResult<Self>;
    fn omega(span: Span) -> OghamResult<Self>;
    fn omega_pow(_exp: Self, span: Span) -> OghamResult<Self> {
        Err(OghamError::new(
            OghamErrorKind::ExpSort,
            span,
            "`ω↑s` is only an element-level monomial constructor in surreal-family worlds",
        ))
    }
    fn named_element(_name: &str, _span: Span) -> OghamResult<Option<Self>> {
        Ok(None)
    }
    fn reserved_ident(_name: &str) -> bool {
        false
    }
    fn factorial(n: i128, span: Span) -> OghamResult<Self>;
    fn inv_scalar(value: &Self, span: Span) -> OghamResult<Self> {
        value
            .inv()
            .ok_or_else(|| OghamError::new(OghamErrorKind::NotInvertible, span, "not invertible"))
    }
    fn exact_div(_lhs: &Self, _rhs: &Self, _span: Span) -> Option<OghamResult<Self>> {
        None
    }
    fn rem(_lhs: &Self, _rhs: &Self, span: Span) -> OghamResult<Self> {
        Err(OghamError::new(
            OghamErrorKind::WrongWorld,
            span,
            "field worlds have no informative remainder operator",
        ))
    }
    fn relation(_op: RelOp, _lhs: &Self, _rhs: &Self, span: Span) -> OghamResult<bool> {
        Err(OghamError::new(
            OghamErrorKind::WrongWorld,
            span,
            "this world has no canonical order",
        ))
    }
    fn frob(_value: &Self, span: Span) -> OghamResult<Self> {
        Err(OghamError::new(
            OghamErrorKind::WrongWorld,
            span,
            "`frob` is only available in finite-field worlds",
        ))
    }
    fn trace(_value: &Self, _m: Option<i128>, span: Span) -> OghamResult<Self> {
        Err(OghamError::new(
            OghamErrorKind::WrongWorld,
            span,
            "`tr` is only available in finite-field worlds",
        ))
    }
    fn mul_checked(lhs: &Self, rhs: &Self, _span: Span) -> OghamResult<Self> {
        Ok(lhs.mul(rhs))
    }
    fn pow_checked(base: &Self, mut k: u128, span: Span) -> OghamResult<Self> {
        if k == 0 {
            return Ok(Self::one());
        }
        let mut acc = Self::one();
        let mut x = base.clone();
        loop {
            if k & 1 == 1 {
                acc = Self::mul_checked(&acc, &x, span)?;
            }
            k >>= 1;
            if k == 0 {
                break;
            }
            x = Self::mul_checked(&x, &x, span)?;
        }
        Ok(acc)
    }
    fn mv_mul(
        alg: &CliffordAlgebra<Self>,
        lhs: &Multivector<Self>,
        rhs: &Multivector<Self>,
        _span: Span,
    ) -> OghamResult<Multivector<Self>> {
        Ok(alg.mul(lhs, rhs))
    }
    fn mv_pow(
        alg: &CliffordAlgebra<Self>,
        value: &Multivector<Self>,
        k: u128,
        _span: Span,
    ) -> OghamResult<Multivector<Self>> {
        Ok(alg.pow(value, k))
    }
}

impl OghamScalar for Nimber {
    fn bare_int(n: u128, span: Span) -> OghamResult<Self> {
        if n == 0 {
            return Ok(Nimber::zero());
        }
        Err(OghamError::new(
            OghamErrorKind::BareInt,
            span,
            format!("bare integer `{n}` is not a nimber literal"),
        )
        .with_hint(format!("did you mean `*{n}`?")))
    }

    fn star(lit: &StarLiteral, span: Span) -> OghamResult<Self> {
        match lit {
            StarLiteral::Finite(n) => Ok(Nimber(*n)),
            StarLiteral::Cnf(_) => Err(OghamError::new(
                OghamErrorKind::WrongWorld,
                span,
                "transfinite star-literals belong to the `ordinal` world",
            )),
        }
    }

    fn omega(span: Span) -> OghamResult<Self> {
        Err(OghamError::new(
            OghamErrorKind::WrongWorld,
            span,
            "`ω` is not a finite nimber literal",
        ))
    }

    fn factorial(n: i128, span: Span) -> OghamResult<Self> {
        Err(OghamError::new(
            OghamErrorKind::BareInt,
            span,
            format!("`!{n}` would land through a bare integer in a nim-world"),
        ))
    }

    fn relation(op: RelOp, lhs: &Self, rhs: &Self, _span: Span) -> OghamResult<bool> {
        Ok(match op {
            RelOp::Lt | RelOp::Gt => false,
            RelOp::Fuzzy => lhs.fuzzy(rhs),
            RelOp::Eq => lhs == rhs,
            RelOp::Equiv => return Err(game_only_error("`≡`")),
        })
    }

    fn frob(value: &Self, _span: Span) -> OghamResult<Self> {
        Ok(value.frobenius())
    }

    fn trace(value: &Self, m: Option<i128>, span: Span) -> OghamResult<Self> {
        let Some(m) = m else {
            return Err(OghamError::new(
                OghamErrorKind::Arity,
                span,
                "`tr` in the nimber world expects `tr(x, m)`",
            ));
        };
        if m <= 0 {
            return Err(OghamError::new(
                OghamErrorKind::Domain,
                span,
                "nimber trace degree must be positive",
            ));
        }
        Ok(Nimber(nim_trace(value.0, m as u128)))
    }
}

impl OghamScalar for Ordinal {
    fn bare_int(n: u128, span: Span) -> OghamResult<Self> {
        if n == 0 {
            return Ok(Ordinal::from_u128(0));
        }
        Err(OghamError::new(
            OghamErrorKind::BareInt,
            span,
            format!("bare integer `{n}` is not an ordinal-nimber value"),
        )
        .with_hint(format!("did you mean `*{n}`?")))
    }

    fn star(lit: &StarLiteral, _span: Span) -> OghamResult<Self> {
        Ok(match lit {
            StarLiteral::Finite(n) => Ordinal::from_u128(*n),
            StarLiteral::Cnf(cnf) => cnf.clone(),
        })
    }

    fn omega(span: Span) -> OghamResult<Self> {
        Err(OghamError::new(
            OghamErrorKind::BareOrdinal,
            span,
            "bare `ω` is an ordinal address, not a value",
        )
        .with_hint("values are starred here: `*ω`"))
    }

    fn factorial(n: i128, span: Span) -> OghamResult<Self> {
        Err(OghamError::new(
            OghamErrorKind::BareInt,
            span,
            format!("`!{n}` would land through a bare integer in a nim-world"),
        ))
    }

    fn inv_scalar(value: &Self, span: Span) -> OghamResult<Self> {
        if value.is_zero() {
            return Err(OghamError::new(
                OghamErrorKind::DivisionByZero,
                span,
                "division by zero",
            ));
        }
        value.checked_inv().ok_or_else(|| kummer_escape(span))
    }

    fn relation(op: RelOp, lhs: &Self, rhs: &Self, _span: Span) -> OghamResult<bool> {
        Ok(match op {
            RelOp::Lt | RelOp::Gt => false,
            RelOp::Fuzzy => lhs.fuzzy(rhs),
            RelOp::Eq => lhs == rhs,
            RelOp::Equiv => return Err(game_only_error("`≡`")),
        })
    }

    fn mul_checked(lhs: &Self, rhs: &Self, span: Span) -> OghamResult<Self> {
        lhs.nim_mul(rhs).ok_or_else(|| kummer_escape(span))
    }

    fn pow_checked(base: &Self, k: u128, span: Span) -> OghamResult<Self> {
        base.nim_pow(k).ok_or_else(|| kummer_escape(span))
    }

    fn mv_mul(
        alg: &CliffordAlgebra<Self>,
        lhs: &Multivector<Self>,
        rhs: &Multivector<Self>,
        span: Span,
    ) -> OghamResult<Multivector<Self>> {
        catch_unwind(AssertUnwindSafe(|| alg.mul(lhs, rhs))).map_err(|_| kummer_escape(span))
    }

    fn mv_pow(
        alg: &CliffordAlgebra<Self>,
        value: &Multivector<Self>,
        k: u128,
        span: Span,
    ) -> OghamResult<Multivector<Self>> {
        catch_unwind(AssertUnwindSafe(|| alg.pow(value, k))).map_err(|_| kummer_escape(span))
    }
}

impl OghamScalar for Surreal {
    fn bare_int(n: u128, _span: Span) -> OghamResult<Self> {
        Ok(Surreal::from_int(u128_to_i128(n)?))
    }

    fn star(_lit: &StarLiteral, span: Span) -> OghamResult<Self> {
        Err(OghamError::new(
            OghamErrorKind::WrongWorld,
            span,
            "`*3` is a nimber; this is the `surreal` world",
        ))
    }

    fn omega(_span: Span) -> OghamResult<Self> {
        Ok(Surreal::omega())
    }

    fn omega_pow(exp: Self, _span: Span) -> OghamResult<Self> {
        Ok(Surreal::omega_pow(exp))
    }

    fn factorial(n: i128, _span: Span) -> OghamResult<Self> {
        if n < 0 {
            return Err(domain("factorial is only defined for n >= 0"));
        }
        let n = checked_factorial_i128(n).ok_or_else(|| overflow("factorial exceeds i128"))?;
        Ok(Surreal::from_int(n))
    }

    fn inv_scalar(value: &Self, span: Span) -> OghamResult<Self> {
        if value.is_zero() {
            return Err(OghamError::new(
                OghamErrorKind::DivisionByZero,
                span,
                "division by zero",
            ));
        }
        value.inv().ok_or_else(|| {
            OghamError::new(
                OghamErrorKind::NotInvertible,
                span,
                "only CNF monomials invert exactly; 1/(ω+1) is an infinite Hahn series",
            )
        })
    }

    fn rem(lhs: &Self, rhs: &Self, span: Span) -> OghamResult<Self> {
        if rhs.is_zero() {
            return Err(OghamError::new(
                OghamErrorKind::DivisionByZero,
                span,
                "division by zero",
            ));
        }
        lhs.rem(rhs).ok_or_else(|| modulus_error(span))
    }

    fn relation(op: RelOp, lhs: &Self, rhs: &Self, _span: Span) -> OghamResult<bool> {
        ordered_relation(op, lhs.cmp(rhs))
    }
}

impl OghamScalar for Omnific {
    fn bare_int(n: u128, _span: Span) -> OghamResult<Self> {
        Ok(Omnific::from_int(u128_to_i128(n)?))
    }

    fn star(_lit: &StarLiteral, span: Span) -> OghamResult<Self> {
        Err(OghamError::new(
            OghamErrorKind::WrongWorld,
            span,
            "`*3` is a nimber; this is the `omnific` world",
        ))
    }

    fn omega(_span: Span) -> OghamResult<Self> {
        Ok(Omnific::omega())
    }

    fn omega_pow(exp: Self, span: Span) -> OghamResult<Self> {
        Omnific::from_surreal(Surreal::omega_pow(exp.inner().clone())).ok_or_else(|| {
            OghamError::new(
                OghamErrorKind::Domain,
                span,
                "omega-power exponent does not produce an omnific integer",
            )
        })
    }

    fn factorial(n: i128, _span: Span) -> OghamResult<Self> {
        if n < 0 {
            return Err(domain("factorial is only defined for n >= 0"));
        }
        let n = checked_factorial_i128(n).ok_or_else(|| overflow("factorial exceeds i128"))?;
        Ok(Omnific::from_int(n))
    }

    fn rem(lhs: &Self, rhs: &Self, span: Span) -> OghamResult<Self> {
        if rhs.is_zero() {
            return Err(OghamError::new(
                OghamErrorKind::DivisionByZero,
                span,
                "division by zero",
            ));
        }
        lhs.rem(rhs).ok_or_else(|| modulus_error(span))
    }

    fn relation(op: RelOp, lhs: &Self, rhs: &Self, _span: Span) -> OghamResult<bool> {
        ordered_relation(op, lhs.cmp(rhs))
    }
}

impl OghamScalar for Integer {
    fn bare_int(n: u128, _span: Span) -> OghamResult<Self> {
        Ok(Integer(u128_to_i128(n)?))
    }

    fn star(_lit: &StarLiteral, span: Span) -> OghamResult<Self> {
        Err(OghamError::new(
            OghamErrorKind::WrongWorld,
            span,
            "`*3` is a nimber; this is the `integer` world",
        ))
    }

    fn omega(span: Span) -> OghamResult<Self> {
        Err(OghamError::new(
            OghamErrorKind::WrongWorld,
            span,
            "`ω` belongs to the surreal-family worlds",
        ))
    }

    fn factorial(n: i128, _span: Span) -> OghamResult<Self> {
        if n < 0 {
            return Err(domain("factorial is only defined for n >= 0"));
        }
        let n = checked_factorial_i128(n).ok_or_else(|| overflow("factorial exceeds i128"))?;
        Ok(Integer(n))
    }

    fn exact_div(lhs: &Self, rhs: &Self, span: Span) -> Option<OghamResult<Self>> {
        Some(match lhs.div_exact(rhs) {
            Ok(q) => Ok(q),
            Err(IntegerDivExactError::DivisionByZero) => Err(OghamError::new(
                OghamErrorKind::DivisionByZero,
                span,
                "division by zero",
            )),
            Err(IntegerDivExactError::Remainder(r)) => Err(OghamError::new(
                OghamErrorKind::NotInvertible,
                span,
                format!("integer exact division failed with remainder {r}"),
            )),
        })
    }

    fn rem(lhs: &Self, rhs: &Self, span: Span) -> OghamResult<Self> {
        lhs.rem(rhs).ok_or_else(|| {
            OghamError::new(OghamErrorKind::DivisionByZero, span, "division by zero")
        })
    }

    fn relation(op: RelOp, lhs: &Self, rhs: &Self, _span: Span) -> OghamResult<bool> {
        ordered_relation(op, lhs.cmp(rhs))
    }
}

macro_rules! impl_fp_ogham {
    ($($p:literal),* $(,)?) => {
        $(
            impl OghamScalar for Fp<$p> {
                fn bare_int(n: u128, _span: Span) -> OghamResult<Self> {
                    Ok(Fp::<$p>::from_u128(n))
                }
                fn star(_lit: &StarLiteral, span: Span) -> OghamResult<Self> {
                    Err(OghamError::new(
                        OghamErrorKind::WrongWorld,
                        span,
                        "`*3` is a nimber; this is a prime-field world",
                    ))
                }
                fn omega(span: Span) -> OghamResult<Self> {
                    Err(OghamError::new(
                        OghamErrorKind::WrongWorld,
                        span,
                        "`ω` belongs to the surreal-family worlds",
                    ))
                }
                fn factorial(n: i128, _span: Span) -> OghamResult<Self> {
                    factorial_in_scalar::<Self>(n).ok_or_else(|| domain("factorial is only defined for n >= 0"))
                }
                fn rem(_lhs: &Self, _rhs: &Self, span: Span) -> OghamResult<Self> {
                    Err(OghamError::new(
                        OghamErrorKind::WrongWorld,
                        span,
                        "field worlds have no informative remainder operator",
                    ))
                }
                fn frob(value: &Self, _span: Span) -> OghamResult<Self> {
                    Ok(*value)
                }
                fn trace(value: &Self, m: Option<i128>, span: Span) -> OghamResult<Self> {
                    if m.is_some() {
                        return Err(OghamError::new(
                            OghamErrorKind::Arity,
                            span,
                            "`tr` in prime fields expects one argument",
                        ));
                    }
                    Ok(*value)
                }
            }
        )*
    };
}

macro_rules! impl_fpn_ogham {
    ($(($p:literal, $n:literal)),* $(,)?) => {
        $(
            impl OghamScalar for Fpn<$p, $n> {
                fn bare_int(n: u128, _span: Span) -> OghamResult<Self> {
                    Ok(Fpn::<$p, $n>::constant(n))
                }
                fn star(_lit: &StarLiteral, span: Span) -> OghamResult<Self> {
                    Err(OghamError::new(
                        OghamErrorKind::WrongWorld,
                        span,
                        "`*3` is a nimber; this is an extension-field world",
                    ))
                }
                fn omega(span: Span) -> OghamResult<Self> {
                    Err(OghamError::new(
                        OghamErrorKind::WrongWorld,
                        span,
                        "`ω` belongs to the surreal-family worlds",
                    ))
                }
                fn named_element(name: &str, _span: Span) -> OghamResult<Option<Self>> {
                    Ok((name == "x").then(Fpn::<$p, $n>::generator))
                }
                fn reserved_ident(name: &str) -> bool {
                    name == "x"
                }
                fn factorial(n: i128, _span: Span) -> OghamResult<Self> {
                    factorial_in_scalar::<Self>(n).ok_or_else(|| domain("factorial is only defined for n >= 0"))
                }
                fn rem(_lhs: &Self, _rhs: &Self, span: Span) -> OghamResult<Self> {
                    Err(OghamError::new(
                        OghamErrorKind::WrongWorld,
                        span,
                        "field worlds have no informative remainder operator",
                    ))
                }
                fn frob(value: &Self, _span: Span) -> OghamResult<Self> {
                    Ok(value.frobenius())
                }
                fn trace(value: &Self, m: Option<i128>, span: Span) -> OghamResult<Self> {
                    if m.is_some() {
                        return Err(OghamError::new(
                            OghamErrorKind::Arity,
                            span,
                            "`tr` in extension fields expects one argument",
                        ));
                    }
                    Ok(value.relative_trace(1))
                }
            }
        )*
    };
}

impl_fp_ogham!(2, 3, 5, 7);
impl_fpn_ogham!((2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (5, 2));

fn build_runtime<S: OghamScalar>(
    name: &'static str,
    dim: usize,
    rest: &str,
) -> OghamResult<Runtime<S>> {
    let metric = if rest.trim().is_empty() {
        if dim == 0 {
            Metric::diagonal(Vec::new())
        } else {
            return Err(parse_error(
                "positive-dimensional worlds need `q=[...]` or `grassmann`",
            ));
        }
    } else if rest.contains("grassmann") {
        Metric::grassmann(dim)
    } else {
        let q_src = extract_bracket(rest, "q")?;
        let q = parse_scalar_list::<S>(&q_src)?;
        if q.len() != dim {
            return Err(OghamError::new(
                OghamErrorKind::DimMismatch,
                Span::point(0),
                format!("q length {} does not match dimension {dim}", q.len()),
            ));
        }
        let b = if let Some(b_src) = extract_bracket_opt(rest, "b")? {
            parse_sparse_pairs::<S>(&b_src)?
        } else {
            BTreeMap::new()
        };
        let a = if let Some(a_src) = extract_bracket_opt(rest, "a")? {
            parse_sparse_pairs::<S>(&a_src)?
        } else {
            BTreeMap::new()
        };
        Metric::general(q, b, a)
    };
    Ok(Runtime::from_metric(name, metric))
}

fn parse_gold_metric(src: &str) -> OghamResult<Metric<Nimber>> {
    let inner = src
        .strip_prefix("gold(")
        .and_then(|s| s.strip_suffix(')'))
        .ok_or_else(|| parse_error("expected `gold(m,a)`"))?;
    let mut parts = inner.split(',');
    let m = parts
        .next()
        .ok_or_else(|| parse_error("missing gold m"))?
        .trim()
        .parse::<usize>()
        .map_err(|_| parse_error("gold m must be a usize"))?;
    let a = parts
        .next()
        .ok_or_else(|| parse_error("missing gold a"))?
        .trim()
        .parse::<usize>()
        .map_err(|_| parse_error("gold a must be a usize"))?;
    if parts.next().is_some() {
        return Err(parse_error("gold expects exactly two arguments"));
    }
    Ok(crate::forms::gold_form(m, a))
}

fn parse_scalar_list<S: OghamScalar>(src: &str) -> OghamResult<Vec<S>> {
    if src.trim().is_empty() {
        return Ok(Vec::new());
    }
    split_top_level(src, ',')
        .into_iter()
        .map(|part| parse_metric_scalar::<S>(&part))
        .collect()
}

fn parse_sparse_pairs<S: OghamScalar>(src: &str) -> OghamResult<BTreeMap<(usize, usize), S>> {
    let mut out = BTreeMap::new();
    if src.trim().is_empty() {
        return Ok(out);
    }
    for entry in split_top_level(src, ',') {
        let (ij, value) = entry
            .split_once(':')
            .ok_or_else(|| parse_error("sparse metric entries need `(i,j):value`"))?;
        let ij = ij.trim();
        let ij = ij
            .strip_prefix('(')
            .and_then(|s| s.strip_suffix(')'))
            .ok_or_else(|| parse_error("sparse metric key needs `(i,j)`"))?;
        let (i, j) = ij
            .split_once(',')
            .ok_or_else(|| parse_error("sparse metric key needs two indices"))?;
        let i = i
            .trim()
            .parse::<usize>()
            .map_err(|_| parse_error("metric index must be a usize"))?;
        let j = j
            .trim()
            .parse::<usize>()
            .map_err(|_| parse_error("metric index must be a usize"))?;
        out.insert((i, j), parse_metric_scalar::<S>(value)?);
    }
    Ok(out)
}

fn parse_metric_scalar<S: OghamScalar>(src: &str) -> OghamResult<S> {
    let mut rt = Runtime::<S>::from_metric("metric", Metric::diagonal(Vec::new()));
    let stmt = parse_statement(src)?;
    let Statement::Expr(expr) = stmt else {
        return Err(parse_error("metric scalar must be an expression"));
    };
    let value = rt.eval_expr(&expr)?;
    scalar_part(&value).ok_or_else(|| grade0_error(Span::point(0)))
}

fn extract_bracket(rest: &str, key: &str) -> OghamResult<String> {
    extract_bracket_opt(rest, key)?.ok_or_else(|| parse_error(format!("missing `{key}=[...]`")))
}

fn extract_bracket_opt(rest: &str, key: &str) -> OghamResult<Option<String>> {
    let needle = format!("{key}=");
    let Some(start) = rest.find(&needle) else {
        return Ok(None);
    };
    let after = &rest[start + needle.len()..];
    let Some(open) = after.find('[') else {
        return Err(parse_error(format!("`{key}` needs `[...]`")));
    };
    let mut depth = 0i32;
    let mut begin = None;
    for (idx, ch) in after[open..].char_indices() {
        match ch {
            '[' => {
                if depth == 0 {
                    begin = Some(open + idx + ch.len_utf8());
                }
                depth += 1;
            }
            ']' => {
                depth -= 1;
                if depth == 0 {
                    let begin = begin.expect("set at opening bracket");
                    return Ok(Some(after[begin..open + idx].to_string()));
                }
            }
            _ => {}
        }
    }
    Err(parse_error(format!("unterminated `{key}` bracket list")))
}

fn split_top_level(src: &str, delim: char) -> Vec<String> {
    let mut out = Vec::new();
    let mut start = 0usize;
    let mut parens = 0i32;
    let mut brackets = 0i32;
    for (idx, ch) in src.char_indices() {
        match ch {
            '(' => parens += 1,
            ')' => parens -= 1,
            '[' => brackets += 1,
            ']' => brackets -= 1,
            c if c == delim && parens == 0 && brackets == 0 => {
                out.push(src[start..idx].trim().to_string());
                start = idx + ch.len_utf8();
            }
            _ => {}
        }
    }
    out.push(src[start..].trim().to_string());
    out
}

fn scalar_part<S: Scalar>(value: &Multivector<S>) -> Option<S> {
    match value.terms() {
        terms if terms.is_empty() => Some(S::zero()),
        terms if terms.len() == 1 => terms.get(&0).cloned(),
        _ => None,
    }
}

fn expect_arity(name: &str, args: &[Expr], expected: usize) -> OghamResult<()> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(OghamError::new(
            OghamErrorKind::Arity,
            Span::point(0),
            format!("`{name}` expects {expected} argument(s)"),
        ))
    }
}

fn ordered_relation(op: RelOp, cmp: Ordering) -> OghamResult<bool> {
    Ok(match op {
        RelOp::Eq => cmp == Ordering::Equal,
        RelOp::Lt => cmp == Ordering::Less,
        RelOp::Gt => cmp == Ordering::Greater,
        RelOp::Fuzzy => false,
        RelOp::Equiv => return Err(game_only_error("`≡`")),
    })
}

fn checked_i128_pow(base: i128, mut exp: u128) -> OghamResult<i128> {
    if exp == 0 {
        return Ok(1);
    }
    let mut acc = 1i128;
    let mut x = base;
    loop {
        if exp & 1 == 1 {
            acc = acc
                .checked_mul(x)
                .ok_or_else(|| overflow("index power overflowed i128"))?;
        }
        exp >>= 1;
        if exp == 0 {
            break;
        }
        x = x
            .checked_mul(x)
            .ok_or_else(|| overflow("index power overflowed i128"))?;
    }
    Ok(acc)
}

fn u128_to_i128(n: u128) -> OghamResult<i128> {
    i128::try_from(n).map_err(|_| overflow("integer literal exceeds i128 in this world"))
}

fn parse_error(message: impl Into<String>) -> OghamError {
    OghamError::new(OghamErrorKind::Parse, Span::point(0), message)
}

fn index_sort_error() -> OghamError {
    OghamError::new(
        OghamErrorKind::IndexSort,
        Span::point(0),
        "expected an Index expression",
    )
}

fn bool_sort_error() -> OghamError {
    OghamError::new(
        OghamErrorKind::BoolSort,
        Span::point(0),
        "expected a Bool expression",
    )
}

fn fn_sort_error() -> OghamError {
    OghamError::new(
        OghamErrorKind::FnSort,
        Span::point(0),
        "Function values are first-order and cannot appear here",
    )
}

fn exp_sort_error() -> OghamError {
    OghamError::new(
        OghamErrorKind::ExpSort,
        Span::point(0),
        "exponent must be an Index",
    )
    .with_hint("`↑`/`^` is power; the wedge product is `∧`/`&`")
}

fn unbound_error(name: &str) -> OghamError {
    let err = OghamError::new(
        OghamErrorKind::Unbound,
        Span::point(0),
        format!("unbound identifier `{name}`"),
    );
    if name == "t" {
        err.with_hint("`t` is the indeterminate in poly/ratfunc worlds")
    } else {
        err.with_hint(format!(
            "did you mean `{name} := ...`? recursive definition? `{name} =: ...`"
        ))
    }
}

fn element_fixpoint_error(name: &str) -> OghamError {
    OghamError::new(
        OghamErrorKind::WrongWorld,
        Span::point(0),
        format!("element fixpoint `{name} =: ...` has no fixpoint theory outside the `game` world"),
    )
}

fn grade0_error(span: Span) -> OghamError {
    OghamError::new(
        OghamErrorKind::Grade0,
        span,
        "operation requires a grade-0 element",
    )
}

fn modulus_error(span: Span) -> OghamError {
    OghamError::new(
        OghamErrorKind::Modulus,
        span,
        "moduli here are monic omega-powers: `% ω↑2` truncates the CNF below it",
    )
}

fn kummer_escape(span: Span) -> OghamError {
    OghamError::new(
        OghamErrorKind::KummerEscape,
        span,
        "ordinal nim-product escaped beyond the source-verified tower below ω^(ω^ω)",
    )
    .with_hint("below ω^(ω^ω), primes <= 709 — see docs/OPEN.md")
}

fn overflow(message: impl Into<String>) -> OghamError {
    OghamError::new(OghamErrorKind::Overflow, Span::point(0), message)
}

fn domain(message: impl Into<String>) -> OghamError {
    OghamError::new(OghamErrorKind::Domain, Span::point(0), message)
}

fn game_only_error(feature: &str) -> OghamError {
    OghamError::new(
        OghamErrorKind::WrongWorld,
        Span::point(0),
        format!("{feature} is only defined in the `game` world"),
    )
}

fn array_world_error(feature: &str) -> OghamError {
    OghamError::new(
        OghamErrorKind::WrongWorld,
        Span::point(0),
        format!("`{feature}` is only defined in fixed-dimension Clifford worlds"),
    )
    .with_hint("arrays are world-fixed length; the free-shape container lives in the game world")
}
