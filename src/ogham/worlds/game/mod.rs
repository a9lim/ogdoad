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
    equation_names: BTreeMap<usize, String>,
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
    SystemRef(usize),
}

impl std::fmt::Display for GameElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", display_game_element(self))
    }
}

pub(crate) struct GameRuntime {
    pub(crate) state: RuntimeState<GameElement>,
}

impl WorldOps for GameRuntime {
    type Element = GameElement;

    fn state(&self) -> &RuntimeState<Self::Element> {
        &self.state
    }

    fn state_mut(&mut self) -> &mut RuntimeState<Self::Element> {
        &mut self.state
    }

    fn world_name(&self) -> &'static str {
        "game"
    }

    fn world_summary(&self) -> String {
        "game".to_string()
    }

    fn world_display_value(&self, value: &Value<Self::Element>) -> String {
        display_game_value(value, &self.state.env)
    }

    fn world_eval_element(&mut self, expr: &Expr) -> OghamResult<Self::Element> {
        GameRuntime::eval_element(self, expr)
    }

    fn index_primitive(&mut self, expr: &Expr) -> IndexPrimitive {
        match expr {
            Expr::Call { name, args } if matches!(name.as_str(), "nleft" | "nright") => {
                IndexPrimitive::from_result((|| {
                    expect_arity(name, args, 1)?;
                    let game = self.eval_element(&args[0])?;
                    let len = game_options(&game, name == "nleft").len();
                    i128::try_from(len).map_err(|_| overflow("game option count exceeds i128"))
                })())
            }
            Expr::Call { name, args } if name == "birthday" => {
                IndexPrimitive::from_result((|| {
                    expect_arity(name, args, 1)?;
                    match self.eval_element(&args[0])? {
                        GameElement::Finite(game) => i128::try_from(game.birthday())
                            .map_err(|_| overflow("game birthday exceeds i128")),
                        GameElement::Graph(_) => {
                            Err(loopy_error("loopy games have no finite formation day"))
                        }
                    }
                })())
            }
            Expr::Call { name, .. } if name == "dim" => {
                IndexPrimitive::Error(literal_call_error(name))
            }
            Expr::Dim => IndexPrimitive::Error(game_wrong_world_hint(
                "`dim` is a fixed-shape Clifford literal",
                "the game container is free-shape",
            )),
            _ => IndexPrimitive::NotHandled,
        }
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
        matches!(name, "hasdraw" | "stopper" | "integral").then(|| {
            expect_arity(name, args, 1)?;
            if name == "integral" {
                return Err(game_wrong_world(
                    "the game world has no ring-of-integers pairing",
                ));
            }
            let element = self.eval_element(&args[0])?;
            let result = if name == "hasdraw" {
                game_element_has_draw(&element)
            } else {
                game_element_is_stopper(&element, self.state.graph_budget)?
            };
            Ok(Value::Bool(result))
        })
    }

    fn bind_recursive_element(&mut self, name: &str, expr: &Expr) -> OghamResult<()> {
        let reduced = self.reduce_element_fixpoint(name, expr, false)?;
        let value = materialize_regular_game(name, reduced, self.state.graph_budget)?;
        self.state
            .env
            .insert(name.to_string(), Value::Element(value));
        Ok(())
    }

    fn bind_recursive_system(&mut self, bindings: &[Binding]) -> OghamResult<usize> {
        let mut count = 0;
        while let Some(binding) = bindings.get(count) {
            if !binding.recursive
                || matches!(binding.expr, Expr::Lambda { .. })
                || matches!(
                    game_known_sort(&binding.expr, &self.state.env),
                    Some(DataSort::Index | DataSort::Bool)
                )
            {
                break;
            }
            count += 1;
        }
        if count == 0 {
            return Ok(0);
        }
        let names = bindings[..count]
            .iter()
            .map(|binding| binding.name.clone())
            .collect::<Vec<_>>();
        let has_system_reference = bindings[..count].iter().any(|binding| {
            names
                .iter()
                .any(|name| contains_free_name(&binding.expr, name))
        });
        if count == 1 || !has_system_reference {
            return Ok(0);
        }
        let roots = bindings[..count]
            .iter()
            .map(|binding| self.reduce_element_system(&binding.name, &names, &binding.expr, false))
            .collect::<OghamResult<Vec<_>>>()?;
        let values = materialize_regular_system(&names, roots, self.state.graph_budget)?;
        for (name, value) in names.into_iter().zip(values) {
            self.state.env.insert(name, Value::Element(value));
        }
        Ok(count)
    }

    fn refine_function_signature(
        &self,
        body: &Expr,
        binders: &[String],
        binder_sorts: &mut [DataSort],
        ret: &mut DataSort,
        mu_name: Option<&str>,
    ) {
        refine_game_binder_sorts(body, binders, binder_sorts, &self.state.env);
        if let Some(hint) = game_return_sort_hint(body, &self.state.env, mu_name) {
            *ret = hint;
        }
        if let Some(name) = mu_name {
            if is_game_index_counter(name, body) {
                for (binder, sort) in binders.iter().zip(binder_sorts) {
                    if contains_game_binder_unit_step(binder, body) {
                        *sort = DataSort::Index;
                    }
                }
            }
        }
    }

    fn prefer_index_expression(&self) -> bool {
        true
    }

    fn skip_if_eval_after_validation(&self) -> bool {
        true
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
                    self.state.env.insert(binder.name.clone(), arg.clone()),
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
            DataSort::Element => self.eval_element(&function.body).map(Value::Element),
            DataSort::Index => self.eval_index(&function.body).map(Value::Index),
            DataSort::Bool => self.eval_bool(&function.body).map(Value::Bool),
        }
    }
}

impl GameRuntime {
    pub(crate) fn new() -> Self {
        GameRuntime {
            state: RuntimeState::new(),
        }
    }

    fn eval_relation(&mut self, op: RelOp, lhs: &Expr, rhs: &Expr) -> OghamResult<bool> {
        if let RelOp::Outcome(cell) = op {
            let lhs = self.eval_element(lhs)?;
            let rhs = self.eval_element(rhs)?;
            return Ok(outcome_cell(game_difference_outcome(
                &lhs,
                &rhs,
                self.state.graph_budget,
            )?) == cell);
        }
        if !bool_shaped(lhs)
            && !bool_shaped(rhs)
            && (expression_is_index(lhs)
                || expression_is_index(rhs)
                || game_known_sort(lhs, &self.state.env) == Some(DataSort::Index)
                || game_known_sort(rhs, &self.state.env) == Some(DataSort::Index)
                || self.static_sort(lhs) == Ok(DataSort::Index)
                || self.static_sort(rhs) == Ok(DataSort::Index))
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
                    LoopyPartizanGraph::from_game(lhs, self.state.graph_budget)
                        .map_err(partizan_graph_error)?;
                    LoopyPartizanGraph::from_game(rhs, self.state.graph_budget)
                        .map_err(partizan_graph_error)?;
                    return match op {
                        RelOp::Eq => Ok(lhs.eq(rhs)),
                        RelOp::Lt => Ok(lhs.le(rhs) && !rhs.le(lhs)),
                        RelOp::Gt => Ok(rhs.le(lhs) && !lhs.le(rhs)),
                        RelOp::Fuzzy => Ok(lhs.fuzzy(rhs)),
                        RelOp::Equiv | RelOp::Outcome(_) => unreachable!("handled above"),
                    };
                }
                ensure_game_stopper("left", &lhs, self.state.graph_budget)?;
                ensure_game_stopper("right", &rhs, self.state.graph_budget)?;
                let projected = project_stopper_outcome(game_difference_outcome(
                    &lhs,
                    &rhs,
                    self.state.graph_budget,
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
            Expr::Omega => Err(game_wrong_world_hint(
                "`ω` is not a finite short game",
                "use finite game forms",
            )),
            Expr::Blade(_) => Err(game_wrong_world("the game world has no Clifford blades")),
            Expr::Container(items) => {
                let mut tail = GameElement::Finite(Game::integer(0));
                for item in items.iter().rev() {
                    tail = build_game_form(
                        vec![self.eval_element(item)?],
                        vec![tail],
                        self.state.graph_budget,
                    )?;
                }
                Ok(tail)
            }
            Expr::Up => Ok(GameElement::Finite(Game::up())),
            Expr::Down => Ok(GameElement::Finite(Game::up().neg())),
            Expr::Dim => Err(game_wrong_world_hint(
                "`dim` is a fixed-shape Clifford literal",
                "the game container is free-shape",
            )),
            Expr::Lambda { .. } => Err(fn_sort_error()),
            Expr::GameForm { left, right } => build_game_form(
                left.iter()
                    .map(|item| self.eval_element(item))
                    .collect::<OghamResult<Vec<_>>>()?,
                right
                    .iter()
                    .map(|item| self.eval_element(item))
                    .collect::<OghamResult<Vec<_>>>()?,
                self.state.graph_budget,
            ),
            Expr::Block { bindings, body } => match self.eval_block(bindings, body)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Ident(name) => match self.state.env.get(name) {
                Some(Value::Element(value)) => Ok(value.clone()),
                Some(Value::Index(_)) => Err(index_sort_error()),
                Some(Value::Bool(_)) => Err(bool_sort_error()),
                Some(Value::Function(_)) => Err(fn_sort_error()),
                None => Err(unbound_error(name)),
            },
            Expr::Call { name, args } => self.eval_element_call(name, args),
            Expr::Unary { op, expr } => match op {
                UnaryOp::Neg => {
                    negate_game_element(self.eval_element(expr)?, self.state.graph_budget)
                }
                UnaryOp::Inv => Err(game_wrong_world_hint(
                    "games form an additive group, not a field",
                    "`/` is undefined for games",
                )),
                UnaryOp::Not => Err(bool_sort_error()),
            },
            Expr::Apply { .. } => match self.eval_value(expr)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Binary { op, lhs, rhs } => self.eval_binary(*op, lhs, rhs),
            Expr::If { .. } => match self.eval_value(expr)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Relation { .. } => Err(bool_sort_error()),
        }
    }

    fn eval_binary(&mut self, op: BinaryOp, lhs: &Expr, rhs: &Expr) -> OghamResult<GameElement> {
        if op == BinaryOp::Div {
            if let Some(literal) = eval_game_fraction_literal(lhs, rhs) {
                return literal;
            }
        }
        match op {
            BinaryOp::Add | BinaryOp::Sub => {
                let lhs = self.eval_element(lhs)?;
                let rhs = self.eval_element(rhs)?;
                add_game_elements(lhs, rhs, op == BinaryOp::Sub, self.state.graph_budget)
            }
            BinaryOp::Append => {
                match self.static_sort(rhs)? {
                    DataSort::Element => {}
                    DataSort::Index => return Err(index_sort_error()),
                    DataSort::Bool => return Err(bool_sort_error()),
                }
                let lhs = self.eval_element(lhs)?;
                match walk_game_spine(&lhs)? {
                    SpineWalk::Cycles => Ok(lhs),
                    SpineWalk::ReachesNil(heads) => {
                        let rhs = self.eval_element(rhs)?;
                        graft_game_spine(heads, rhs, self.state.graph_budget)
                    }
                }
            }
            BinaryOp::Mul => Err(game_wrong_world_hint(
                "games are an additive group, not a ring",
                "`⋅` is undefined for games",
            )),
            BinaryOp::Wedge => Err(game_wrong_world_hint(
                "the game world has no wedge product",
                "list append is `⧺`",
            )),
            BinaryOp::Div => Err(game_wrong_world_hint(
                "games are an additive group, not a field",
                "`/` is undefined for games",
            )),
            BinaryOp::Rem => Err(game_wrong_world("remainder `%` is undefined for games")),
            BinaryOp::Pow => Err(game_wrong_world("power `↑` is undefined for games")),
            BinaryOp::And | BinaryOp::Or => Err(bool_sort_error()),
        }
    }

    fn eval_element_call(&mut self, name: &str, args: &[Expr]) -> OghamResult<GameElement> {
        match name {
            "canon" => {
                expect_arity(name, args, 1)?;
                match self.eval_element(&args[0])? {
                    GameElement::Finite(game) => Ok(GameElement::Finite(game.canonical())),
                    GameElement::Graph(_) => {
                        Err(loopy_error("`canon` is not defined on loopy games")
                            .with_hint("graph fusion is not yet in the envelope"))
                    }
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
            "nleft" | "nright" | "birthday" => {
                Err(index_sort_error().with_hint(format!("`{name}` returns an Index")))
            }
            "coef" => Err(array_world_error(name)),
            "rev" | "grade" | "even" | "dual" | "frob" | "tr" => Err(game_wrong_world(&format!(
                "`{name}` is a Clifford-world operation, not a game operation"
            ))),
            "deg" | "gcd" => Err(game_wrong_world(&format!(
                "`{name}` is a function-world operation, not a game operation"
            ))),
            "hasdraw" | "stopper" | "integral" => Err(bool_sort_error()),
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
        inside_form: bool,
    ) -> OghamResult<SymbolicGame> {
        self.reduce_element_system(name, &[name.to_string()], expr, inside_form)
    }

    fn reduce_element_system(
        &mut self,
        equation: &str,
        names: &[String],
        expr: &Expr,
        _inside_form: bool,
    ) -> OghamResult<SymbolicGame> {
        match expr {
            Expr::Index(_) => Err(index_sort_error()),
            Expr::Ident(found) => names
                .iter()
                .position(|name| name == found)
                .map(SymbolicGame::SystemRef)
                .map_or_else(|| self.eval_element(expr).map(SymbolicGame::Value), Ok),
            Expr::Container(items) => {
                let mut tail = SymbolicGame::Value(GameElement::Finite(Game::integer(0)));
                for item in items.iter().rev() {
                    tail = SymbolicGame::Form {
                        left: vec![self.reduce_element_system(equation, names, item, true)?],
                        right: vec![tail],
                    };
                }
                Ok(tail)
            }
            Expr::GameForm { left, right } => Ok(SymbolicGame::Form {
                left: left
                    .iter()
                    .map(|item| self.reduce_element_system(equation, names, item, true))
                    .collect::<OghamResult<_>>()?,
                right: right
                    .iter()
                    .map(|item| self.reduce_element_system(equation, names, item, true))
                    .collect::<OghamResult<_>>()?,
            }),
            Expr::Binary {
                op: BinaryOp::Append,
                lhs,
                rhs,
            } => self.reduce_element_append(equation, names, lhs, rhs),
            Expr::If {
                cond,
                then_expr,
                else_expr,
            } => {
                if self.reduce_fixpoint_bool(equation, names, cond)? {
                    self.reduce_element_system(equation, names, then_expr, _inside_form)
                } else {
                    self.reduce_element_system(equation, names, else_expr, _inside_form)
                }
            }
            _ => {
                if let Some(name) = names.iter().find(|name| contains_free_name(expr, name)) {
                    return Err(unfounded_system_error(equation, name));
                }
                self.eval_element(expr).map(SymbolicGame::Value)
            }
        }
    }

    fn reduce_element_append(
        &mut self,
        equation: &str,
        names: &[String],
        lhs: &Expr,
        rhs: &Expr,
    ) -> OghamResult<SymbolicGame> {
        let left = self.reduce_element_system(equation, names, lhs, false)?;
        let mut heads = Vec::new();
        let mut current = left;
        loop {
            match current {
                SymbolicGame::SystemRef(index) => {
                    return Err(unfounded_system_error(equation, &names[index]));
                }
                SymbolicGame::Form { left, right } => match (left.len(), right.len()) {
                    (0, 0) => {
                        let tail = self.reduce_element_system(equation, names, rhs, false)?;
                        return Ok(symbolic_spine_parts(heads, tail));
                    }
                    (1, 1) => {
                        heads.push(left.into_iter().next().expect("singleton symbolic head"));
                        current = right.into_iter().next().expect("singleton symbolic tail");
                    }
                    _ => return Err(improper_spine_error()),
                },
                SymbolicGame::Value(value) => match walk_game_spine(&value)? {
                    SpineWalk::Cycles => {
                        return Ok(symbolic_spine_parts(heads, SymbolicGame::Value(value)));
                    }
                    SpineWalk::ReachesNil(value_heads) => {
                        heads.extend(value_heads.into_iter().map(SymbolicGame::Value));
                        let tail = self.reduce_element_system(equation, names, rhs, false)?;
                        return Ok(symbolic_spine_parts(heads, tail));
                    }
                },
            }
        }
    }

    fn reduce_fixpoint_bool(
        &mut self,
        equation: &str,
        names: &[String],
        expr: &Expr,
    ) -> OghamResult<bool> {
        match expr {
            Expr::Bool(value) => Ok(*value),
            Expr::Unary {
                op: UnaryOp::Not,
                expr,
            } => self
                .reduce_fixpoint_bool(equation, names, expr)
                .map(|value| !value),
            Expr::Binary {
                op: BinaryOp::And,
                lhs,
                rhs,
            } => {
                if !self.reduce_fixpoint_bool(equation, names, lhs)? {
                    Ok(false)
                } else {
                    self.reduce_fixpoint_bool(equation, names, rhs)
                }
            }
            Expr::Binary {
                op: BinaryOp::Or,
                lhs,
                rhs,
            } => {
                if self.reduce_fixpoint_bool(equation, names, lhs)? {
                    Ok(true)
                } else {
                    self.reduce_fixpoint_bool(equation, names, rhs)
                }
            }
            Expr::If {
                cond,
                then_expr,
                else_expr,
            } => {
                if self.reduce_fixpoint_bool(equation, names, cond)? {
                    self.reduce_fixpoint_bool(equation, names, then_expr)
                } else {
                    self.reduce_fixpoint_bool(equation, names, else_expr)
                }
            }
            _ => {
                if let Some(name) = names.iter().find(|name| contains_free_name(expr, name)) {
                    return Err(unfounded_system_error(equation, name));
                }
                self.eval_bool(expr)
            }
        }
    }
}

fn eval_game_fraction_literal(lhs: &Expr, rhs: &Expr) -> Option<OghamResult<GameElement>> {
    let numerator = signed_integer_literal(lhs)?;
    let denominator = signed_integer_literal(rhs)?;
    Some((|| {
        let numerator = numerator?;
        let denominator = denominator?;
        if denominator == 0 {
            return Err(OghamError::new(
                OghamErrorKind::DivisionByZero,
                Span::point(0),
                "division by zero",
            ));
        }
        let rational = Rational::try_new(numerator, denominator)
            .ok_or_else(|| overflow("fraction literal exceeds i128"))?;
        if !(rational.denom() as u128).is_power_of_two() {
            return Err(OghamError::new(
                OghamErrorKind::Domain,
                Span::point(0),
                "fraction literal is not dyadic",
            )
            .with_hint("only dyadics are short games; `1/3` is not born on any finite day"));
        }
        let surreal = Surreal::from_rational(rational);
        let game = Game::from_surreal(&surreal)
            .expect("a rational with power-of-two denominator is dyadic");
        Ok(GameElement::Finite(game))
    })())
}

fn signed_integer_literal(expr: &Expr) -> Option<OghamResult<i128>> {
    match expr {
        Expr::Int(value) => {
            Some(i128::try_from(*value).map_err(|_| overflow("fraction literal exceeds i128")))
        }
        Expr::Unary {
            op: UnaryOp::Neg,
            expr,
        } => match expr.as_ref() {
            Expr::Int(value) if *value == i128::MIN.unsigned_abs() => Some(Ok(i128::MIN)),
            Expr::Int(value) => Some(
                i128::try_from(*value)
                    .map_err(|_| overflow("fraction literal exceeds i128"))
                    .and_then(|value| {
                        value
                            .checked_neg()
                            .ok_or_else(|| overflow("fraction literal exceeds i128"))
                    }),
            ),
            _ => None,
        },
        _ => None,
    }
}
