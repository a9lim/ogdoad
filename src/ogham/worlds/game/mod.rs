//! Game-world runtime and operator wiring.

use super::super::*;

mod display;
mod equiv;
mod fixpoint;

pub(crate) use display::*;
pub(crate) use equiv::*;
pub(crate) use fixpoint::*;

#[derive(Clone)]
pub(crate) enum GameElement {
    Finite(Game),
    Graph(GraphRef),
}

#[derive(Clone)]
pub(crate) struct GraphRef {
    graph: Arc<RegularGameGraph>,
    node: usize,
}

pub(crate) struct RegularGameGraph {
    name: String,
    nodes: Vec<RegularGameNode>,
    has_draw: Vec<bool>,
}

pub(crate) type GraphKey = (usize, usize);
pub(crate) type GraphPair = (GraphKey, GraphKey);

#[derive(Clone)]
pub(crate) struct RegularGameNode {
    left: Vec<RegularGameEdge>,
    right: Vec<RegularGameEdge>,
}

#[derive(Clone)]
pub(crate) enum RegularGameEdge {
    Finite(Game),
    Local(usize),
    External(GraphRef),
}

#[derive(Clone)]
pub(crate) enum SymbolicGame {
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

pub(crate) struct GameRuntime {
    pub(crate) env: BTreeMap<String, Value<GameElement>>,
    pub(crate) fuel_budget: u128,
    pub(crate) fuel_remaining: u128,
    pub(crate) graph_budget: u128,
    pub(crate) active_mu_calls: HashSet<String>,
    pub(crate) recursion_depth: u128,
    pub(crate) validation_sample_function_names: BTreeSet<String>,
}

impl WorldOps for GameRuntime {
    type Element = GameElement;

    fn env(&self) -> &BTreeMap<String, Value<Self::Element>> {
        &self.env
    }

    fn env_mut(&mut self) -> &mut BTreeMap<String, Value<Self::Element>> {
        &mut self.env
    }

    fn fuel_budget(&self) -> u128 {
        self.fuel_budget
    }

    fn fuel_budget_mut(&mut self) -> &mut u128 {
        &mut self.fuel_budget
    }

    fn graph_budget(&self) -> u128 {
        self.graph_budget
    }

    fn graph_budget_mut(&mut self) -> &mut u128 {
        &mut self.graph_budget
    }

    fn fuel_remaining_mut(&mut self) -> &mut u128 {
        &mut self.fuel_remaining
    }

    fn recursion_depth_mut(&mut self) -> &mut u128 {
        &mut self.recursion_depth
    }

    fn validation_sample_function_names(&self) -> &BTreeSet<String> {
        &self.validation_sample_function_names
    }

    fn validation_sample_function_names_mut(&mut self) -> &mut BTreeSet<String> {
        &mut self.validation_sample_function_names
    }

    fn world_name(&self) -> &'static str {
        "game"
    }

    fn world_summary(&self) -> String {
        "game".to_string()
    }

    fn world_display_value(&self, value: &Value<Self::Element>) -> String {
        display_game_value(value)
    }

    fn world_eval_element(&mut self, expr: &Expr) -> OghamResult<Self::Element> {
        GameRuntime::eval_element(self, expr)
    }

    fn world_eval_index(&mut self, expr: &Expr) -> OghamResult<i128> {
        GameRuntime::eval_index(self, expr)
    }

    fn world_eval_relation(&mut self, op: RelOp, lhs: &Expr, rhs: &Expr) -> OghamResult<bool> {
        GameRuntime::eval_relation(self, op, lhs, rhs)
    }

    fn sample_element_expr(&self) -> OghamResult<Expr> {
        Ok(Expr::Int(0))
    }

    fn special_value_call(
        &mut self,
        name: &str,
        args: &[Expr],
    ) -> Option<OghamResult<Value<Self::Element>>> {
        matches!(name, "hasdraw" | "stopper").then(|| {
            expect_arity(name, args, 1)?;
            let element = self.eval_element(&args[0])?;
            let result = if name == "hasdraw" {
                game_element_has_draw(&element)
            } else {
                game_element_is_stopper(&element, self.graph_budget)?
            };
            Ok(Value::Bool(result))
        })
    }

    fn bind_recursive_element(&mut self, name: &str, expr: &Expr) -> OghamResult<()> {
        let reduced = self.reduce_element_fixpoint(name, expr, false)?;
        let value = materialize_regular_game(name, reduced, self.graph_budget)?;
        self.env.insert(name.to_string(), Value::Element(value));
        Ok(())
    }

    fn refine_function_signature(
        &self,
        body: &Expr,
        binders: &[String],
        binder_sorts: &mut [Sort],
        ret: &mut Sort,
        mu_name: Option<&str>,
    ) {
        refine_game_binder_sorts(body, binders, binder_sorts, &self.env);
        if let Some(hint) = game_return_sort_hint(body, &self.env, mu_name) {
            *ret = hint;
        }
        if let Some(name) = mu_name {
            if is_game_index_counter(name, body) {
                for (binder, sort) in binders.iter().zip(binder_sorts) {
                    if contains_game_binder_unit_step(binder, body) {
                        *sort = Sort::Index;
                    }
                }
            }
        }
    }

    fn prefer_index_expression(&self) -> bool {
        true
    }

    fn skip_ternary_eval_after_validation(&self) -> bool {
        true
    }

    fn reset_world_call_state(&mut self) {
        self.active_mu_calls.clear();
    }

    fn element_at(
        &mut self,
        _lhs_expr: &Expr,
        _lhs: Self::Element,
        _rhs: &Expr,
    ) -> OghamResult<Value<Self::Element>> {
        Err(game_wrong_world(
            "Element application with `@` is not defined for games",
        ))
    }

    fn non_function_at_error(&self) -> Option<OghamError> {
        Some(game_wrong_world(
            "Element application with `@` is not defined for games",
        ))
    }

    fn function_call_key(
        &self,
        function: &FunctionValue,
        args: &[Value<Self::Element>],
    ) -> Option<String> {
        function
            .mu_name
            .as_ref()
            .map(|name| game_mu_call_key(name, &function.body, args))
    }

    fn call_key_is_active(&self, key: &str) -> bool {
        self.active_mu_calls.contains(key)
    }

    fn activate_call_key(&mut self, key: String) {
        self.active_mu_calls.insert(key);
    }

    fn deactivate_call_key(&mut self, key: &str) {
        self.active_mu_calls.remove(key);
    }

    fn install_call_arguments(
        &mut self,
        function: &FunctionValue,
        args: &[Value<Self::Element>],
    ) -> Vec<(String, Option<Value<Self::Element>>)> {
        function
            .binders
            .iter()
            .zip(args)
            .map(|(binder, arg)| {
                (
                    binder.name.clone(),
                    self.env.insert(binder.name.clone(), arg.clone()),
                )
            })
            .collect()
    }

    fn eval_function_body(
        &mut self,
        function: &FunctionValue,
        _args: &[Value<Self::Element>],
    ) -> OghamResult<Value<Self::Element>> {
        match function.ret {
            Sort::Element => self.eval_element(&function.body).map(Value::Element),
            Sort::Index => self.eval_index(&function.body).map(Value::Index),
            Sort::Bool => self.eval_bool(&function.body).map(Value::Bool),
        }
    }
}

impl GameRuntime {
    pub(crate) fn new() -> Self {
        GameRuntime {
            env: BTreeMap::new(),
            fuel_budget: DEFAULT_FUEL,
            fuel_remaining: DEFAULT_FUEL,
            graph_budget: DEFAULT_GRAPH_BUDGET,
            active_mu_calls: HashSet::new(),
            recursion_depth: 0,
            validation_sample_function_names: BTreeSet::new(),
        }
    }

    fn eval_relation(&mut self, op: RelOp, lhs: &Expr, rhs: &Expr) -> OghamResult<bool> {
        if let RelOp::Outcome(cell) = op {
            let lhs = self.eval_element(lhs)?;
            let rhs = self.eval_element(rhs)?;
            return Ok(
                outcome_cell(game_difference_outcome(&lhs, &rhs, self.graph_budget)?) == cell,
            );
        }
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
                if let (GameElement::Finite(lhs), GameElement::Finite(rhs)) = (&lhs, &rhs) {
                    LoopyPartizanGraph::from_game(lhs, self.graph_budget)
                        .map_err(partizan_graph_error)?;
                    LoopyPartizanGraph::from_game(rhs, self.graph_budget)
                        .map_err(partizan_graph_error)?;
                    return match op {
                        RelOp::Eq => Ok(lhs.eq(rhs)),
                        RelOp::Lt => Ok(lhs.le(rhs) && !rhs.le(lhs)),
                        RelOp::Gt => Ok(rhs.le(lhs) && !lhs.le(rhs)),
                        RelOp::Fuzzy => Ok(lhs.fuzzy(rhs)),
                        RelOp::Equiv | RelOp::Outcome(_) => unreachable!("handled above"),
                    };
                }
                ensure_game_stopper("left", &lhs, self.graph_budget)?;
                ensure_game_stopper("right", &rhs, self.graph_budget)?;
                let projected = project_stopper_outcome(game_difference_outcome(
                    &lhs,
                    &rhs,
                    self.graph_budget,
                )?);
                Ok(op == projected)
            }
        }
    }

    fn eval_element(&mut self, expr: &Expr) -> OghamResult<GameElement> {
        match expr {
            Expr::Bool(_) => Err(bool_sort_error()),
            Expr::Index(_) => Err(index_sort_error()),
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
            Expr::Container(items) => {
                let mut tail = GameElement::Finite(Game::integer(0));
                for item in items.iter().rev() {
                    tail = build_game_form(
                        vec![self.eval_element(item)?],
                        vec![tail],
                        self.graph_budget,
                    )?;
                }
                Ok(tail)
            }
            Expr::Up => Ok(GameElement::Finite(Game::up())),
            Expr::Down => Ok(GameElement::Finite(Game::up().neg())),
            Expr::Dim => Err(game_wrong_world(
                "`dim` is a fixed-shape Clifford literal; the game container is free-shape",
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
                self.graph_budget,
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
            Expr::Unary { op, expr } => match op {
                UnaryOp::Neg => negate_game_element(self.eval_element(expr)?, self.graph_budget),
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
                add_game_elements(lhs, rhs, op == BinaryOp::Sub, self.graph_budget)
            }
            BinaryOp::Append => {
                let lhs = self.eval_element(lhs)?;
                match walk_game_spine(&lhs)? {
                    SpineWalk::Cycles => Ok(lhs),
                    SpineWalk::ReachesNil(heads) => {
                        let rhs = self.eval_element(rhs)?;
                        graft_game_spine(heads, rhs, self.graph_budget)
                    }
                }
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
                        "`canon` is not defined on loopy games in the 0.3.0 envelope",
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
            "up" | "down" | "dim" => Err(literal_call_error(name)),
            "nleft" | "nright" => {
                Err(index_sort_error().with_hint(format!("`{name}` returns an Index")))
            }
            "coef" => Err(array_world_error(name)),
            "rev" | "grade" | "even" | "dual" | "frob" | "tr" => Err(game_wrong_world(&format!(
                "`{name}` is a Clifford-world operation, not a game operation"
            ))),
            "deg" | "gcd" => Err(game_wrong_world(&format!(
                "`{name}` is a function-world operation, not a game operation"
            ))),
            "hasdraw" | "stopper" => Err(bool_sort_error()),
            "drawn" => Err(renamed_function_error("drawn", "hasdraw")),
            "outcome" | "winner" | "who" => Err(outcome_name_error(name)),
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
            Expr::Index(_) => Err(index_sort_error()),
            Expr::Ident(found) if found == name => Ok(SymbolicGame::SelfRef),
            Expr::Container(items) => {
                let mut tail = SymbolicGame::Value(GameElement::Finite(Game::integer(0)));
                for item in items.iter().rev() {
                    tail = SymbolicGame::Form {
                        left: vec![self.reduce_element_fixpoint(name, item, true)?],
                        right: vec![tail],
                    };
                }
                Ok(tail)
            }
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
                match walk_game_spine(&left)? {
                    SpineWalk::Cycles => Ok(SymbolicGame::Value(left)),
                    SpineWalk::ReachesNil(heads) => {
                        let right = self.reduce_element_fixpoint(name, rhs, false)?;
                        Ok(symbolic_spine(heads, right))
                    }
                }
            }
            _ if contains_free_name(expr, name) => Err(unfounded_error(name)),
            _ => self.eval_element(expr).map(SymbolicGame::Value),
        }
    }

    fn eval_index(&mut self, expr: &Expr) -> OghamResult<i128> {
        match expr {
            Expr::Index(expr) => self.eval_index(expr),
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
            Expr::Call { name, .. } if name == "dim" => Err(literal_call_error(name)),
            Expr::Dim => Err(game_wrong_world(
                "`dim` is a fixed-shape Clifford literal; the game container is free-shape",
            )),
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
            | Expr::Container(_)
            | Expr::Up
            | Expr::Down
            | Expr::GameForm { .. }
            | Expr::Call { .. } => Err(index_sort_error()),
        }
    }
}
