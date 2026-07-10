//! Shared world-independent evaluator and its narrow world contract.

use super::*;

mod function;
mod index;
mod state;
mod transform;
mod validate;
mod value;

pub(crate) use function::*;
pub(crate) use index::*;
pub(crate) use state::*;
pub(crate) use transform::*;
pub(crate) use validate::*;
pub(crate) use value::*;

/// The narrow per-world surface under the shared binding/function runtime.
///
/// Literal interpretation, element operators, relations, stdlib calls, and
/// display stay world-specific. Closure, application, sequencing, validation,
/// recursion bookkeeping, and fuel live once in [`SharedRuntime`].
pub(crate) trait WorldOps: Sized {
    type Element: Clone + Display;

    fn state(&self) -> &RuntimeState<Self::Element>;
    fn state_mut(&mut self) -> &mut RuntimeState<Self::Element>;
    fn world_name(&self) -> &'static str;
    fn world_summary(&self) -> String;
    fn world_eval_element(&mut self, expr: &Expr) -> OghamResult<Self::Element>;
    fn world_eval_relation(&mut self, op: RelOp, lhs: &Expr, rhs: &Expr) -> OghamResult<bool>;
    fn sample_element_expr(&self) -> OghamResult<Expr>;

    fn index_primitive(&mut self, _expr: &Expr) -> IndexPrimitive {
        IndexPrimitive::NotHandled
    }

    fn world_display_value(&self, value: &Value<Self::Element>) -> String {
        display_value(value)
    }

    fn reserved_ident(&self, _name: &str) -> bool {
        false
    }

    fn adjust_binder_error(&self, err: OghamError) -> OghamError {
        err
    }

    fn named_element(&self, _name: &str) -> OghamResult<Option<Self::Element>> {
        Ok(None)
    }

    fn special_value_call(
        &mut self,
        _name: &str,
        _args: &[Expr],
    ) -> Option<OghamResult<Value<Self::Element>>> {
        None
    }

    fn bind_recursive_element(&mut self, name: &str, _expr: &Expr) -> OghamResult<()> {
        Err(element_fixpoint_error(name))
    }

    fn bind_recursive_system(&mut self, _bindings: &[Binding]) -> OghamResult<usize> {
        Ok(0)
    }

    fn refine_function_signature(
        &self,
        _body: &Expr,
        _binders: &[String],
        _binder_sorts: &mut [DataSort],
        _ret: &mut DataSort,
        _mu_name: Option<&str>,
    ) {
    }

    fn deg_is_index(&self) -> bool {
        false
    }

    fn prefer_index_expression(&self) -> bool {
        false
    }

    fn skip_ternary_eval_after_validation(&self) -> bool {
        false
    }

    fn reset_world_call_state(&mut self) {
        self.state_mut().active_call_keys.clear();
    }

    fn element_at(
        &mut self,
        _lhs_expr: &Expr,
        _lhs: Self::Element,
        _rhs: &Expr,
    ) -> OghamResult<Value<Self::Element>> {
        Err(OghamError::new(
            OghamErrorKind::WrongWorld,
            Span::point(0),
            "only Function values apply with `@` in this world; element evaluation lives in function-shaped worlds",
        ))
    }

    fn non_function_at_error(&self) -> Option<OghamError> {
        None
    }

    fn function_call_key(
        &self,
        _function: &FunctionValue,
        _args: &[Value<Self::Element>],
    ) -> Option<String> {
        None
    }

    fn call_key_is_active(&self, key: &str) -> bool {
        self.state().active_call_keys.contains(key)
    }

    fn activate_call_key(&mut self, key: String) {
        self.state_mut().active_call_keys.insert(key);
    }

    fn deactivate_call_key(&mut self, key: &str) {
        self.state_mut().active_call_keys.remove(key);
    }

    fn install_call_arguments(
        &mut self,
        _function: &FunctionValue,
        _args: &[Value<Self::Element>],
    ) -> Vec<(String, Option<Value<Self::Element>>)> {
        Vec::new()
    }

    fn eval_function_body(
        &mut self,
        function: &FunctionValue,
        args: &[Value<Self::Element>],
    ) -> OghamResult<Value<Self::Element>> {
        let mut replacements = BTreeMap::new();
        for (binder, arg) in function.binders.iter().zip(args) {
            replacements.insert(binder.name.clone(), value_to_expr(arg)?);
        }
        let body = substitute_names(&function.body, &replacements);
        match function.ret {
            DataSort::Element => self.world_eval_element(&body).map(Value::Element),
            DataSort::Index => SharedRuntime::eval_index(self, &body).map(Value::Index),
            DataSort::Bool => SharedRuntime::eval_bool(self, &body).map(Value::Bool),
        }
    }
}

pub(crate) trait SharedRuntime: WorldOps {
    fn env(&self) -> &BTreeMap<String, Value<Self::Element>> {
        &self.state().env
    }

    fn env_mut(&mut self) -> &mut BTreeMap<String, Value<Self::Element>> {
        &mut self.state_mut().env
    }

    fn fuel_budget(&self) -> u128 {
        self.state().fuel_budget
    }

    fn fuel_budget_mut(&mut self) -> &mut u128 {
        &mut self.state_mut().fuel_budget
    }

    fn graph_budget(&self) -> u128 {
        self.state().graph_budget
    }

    fn graph_budget_mut(&mut self) -> &mut u128 {
        &mut self.state_mut().graph_budget
    }

    fn fuel_remaining_mut(&mut self) -> &mut u128 {
        &mut self.state_mut().fuel_remaining
    }

    fn recursion_depth_mut(&mut self) -> &mut u128 {
        &mut self.state_mut().recursion_depth
    }

    fn validation_sample_function_names(&self) -> &BTreeSet<String> {
        &self.state().validation_sample_function_names
    }

    fn validation_sample_function_names_mut(&mut self) -> &mut BTreeSet<String> {
        &mut self.state_mut().validation_sample_function_names
    }

    fn eval_index(&mut self, expr: &Expr) -> OghamResult<i128> {
        index::eval_index(self, expr)
    }

    fn reset_fuel(&mut self) {
        let budget = self.fuel_budget();
        *self.fuel_remaining_mut() = budget;
        *self.recursion_depth_mut() = 0;
        self.reset_world_call_state();
    }

    fn set_fuel_budget(&mut self, budget: u128) {
        *self.fuel_budget_mut() = budget;
        self.reset_fuel();
    }

    fn set_graph_budget(&mut self, budget: u128) {
        *self.graph_budget_mut() = budget;
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
            Statement::Expr(expr) => {
                let value = self.eval_value(expr)?;
                Ok(Some(self.world_display_value(&value)))
            }
            Statement::Seq { bindings, tail } => {
                if let Statement::Binding {
                    name,
                    expr,
                    recursive,
                } = tail.as_ref()
                {
                    let mut system = bindings.clone();
                    system.push(Binding {
                        name: name.clone(),
                        expr: expr.clone(),
                        recursive: *recursive,
                    });
                    self.bind_bindings(&system)?;
                    return Ok(None);
                }
                self.bind_bindings(bindings)?;
                self.eval_statement(tail)
            }
        }
    }

    fn bind_bindings(&mut self, bindings: &[Binding]) -> OghamResult<()> {
        let mut index = 0;
        while index < bindings.len() {
            let consumed = if bindings[index].recursive {
                self.bind_recursive_system(&bindings[index..])?
            } else {
                0
            };
            if consumed == 0 {
                let binding = &bindings[index];
                self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
                index += 1;
            } else {
                index += consumed;
            }
        }
        Ok(())
    }

    fn bind_name(&mut self, name: &str, expr: &Expr, recursive: bool) -> OghamResult<()> {
        if self.reserved_ident(name) || reserved_function_binder(name) {
            return Err(OghamError::new(
                OghamErrorKind::Reserved,
                Span::point(0),
                format!("`{name}` is reserved in the `{}` world", self.world_name()),
            ));
        }
        if recursive && contains_free_name(expr, name) {
            if let Expr::Lambda { binders, body } = expr {
                let function = self.close_function(
                    binders.clone(),
                    body.as_ref().clone(),
                    Some(name.to_string()),
                )?;
                self.env_mut()
                    .insert(name.to_string(), Value::Function(function));
                return Ok(());
            }
            return self.bind_recursive_element(name, expr);
        }
        let value = self.eval_value(expr)?;
        self.env_mut().insert(name.to_string(), value);
        Ok(())
    }

    fn eval_block(
        &mut self,
        bindings: &[Binding],
        body: &Expr,
    ) -> OghamResult<Value<Self::Element>> {
        let saved = self.env().clone();
        let result = (|| {
            self.bind_bindings(bindings)?;
            self.eval_value(body)
        })();
        *self.env_mut() = saved;
        result
    }

    fn summary(&self) -> String {
        self.world_summary()
    }

    fn env_summary(&self) -> Vec<String> {
        self.env()
            .iter()
            .map(|(name, value)| format!("{name} := {}", self.world_display_value(value)))
            .collect()
    }

    fn eval_value(&mut self, expr: &Expr) -> OghamResult<Value<Self::Element>> {
        match expr {
            Expr::Bool(value) => Ok(Value::Bool(*value)),
            Expr::Block { bindings, body } => self.eval_block(bindings, body),
            Expr::Lambda { binders, body } => self
                .close_function(binders.clone(), body.as_ref().clone(), None)
                .map(Value::Function),
            Expr::Ident(name) => {
                if let Some(value) = self.env().get(name) {
                    Ok(value.clone())
                } else if let Some(value) = self.named_element(name)? {
                    Ok(Value::Element(value))
                } else {
                    Err(unbound_error(name))
                }
            }
            Expr::Call { name, args } => {
                if name == "drawn" {
                    return Err(renamed_function_error("drawn", "hasdraw"));
                }
                if matches!(name.as_str(), "outcome" | "winner" | "who") {
                    return Err(outcome_name_error(name));
                }
                if name == "stopper" && self.world_name() != "game" {
                    return Err(game_only_error("`stopper`"));
                }
                if let Some(result) = self.special_value_call(name, args) {
                    result
                } else {
                    self.eval_element_or_index(expr)
                }
            }
            Expr::Relation { op, lhs, rhs } => {
                if matches!(op, RelOp::Outcome(_)) && self.world_name() != "game" {
                    return Err(game_only_error("outcome doubles"));
                }
                Ok(Value::Bool(self.world_eval_relation(*op, lhs, rhs)?))
            }
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
                if self.static_sort(rhs)? != DataSort::Bool {
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
                if self.static_sort(rhs)? != DataSort::Bool {
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
            Expr::Apply { callee, args } => self.eval_apply(callee, args),
            _ => self.eval_element_or_index(expr),
        }
    }

    fn eval_element_or_index(&mut self, expr: &Expr) -> OghamResult<Value<Self::Element>> {
        if self.prefer_index_expression() && expression_is_index(expr) {
            return self.eval_index(expr).map(Value::Index);
        }
        match self.world_eval_element(expr) {
            Ok(value) => Ok(Value::Element(value)),
            Err(err) if err.kind == OghamErrorKind::IndexSort => {
                self.eval_index(expr).map(Value::Index)
            }
            Err(err) => Err(err),
        }
    }

    fn eval_bool(&mut self, expr: &Expr) -> OghamResult<bool> {
        match self.eval_value(expr)? {
            Value::Bool(value) => Ok(value),
            Value::Element(_) | Value::Index(_) => Err(bool_sort_error()),
            Value::Function(_) => Err(fn_sort_error()),
        }
    }

    fn eval_apply(&mut self, callee: &Expr, args: &[Expr]) -> OghamResult<Value<Self::Element>> {
        match self.eval_value(callee)? {
            Value::Function(function) => {
                if args.len() != 1 {
                    return self.apply_function_exprs(&function, args);
                }
                match self.eval_value(&args[0])? {
                    Value::Function(rhs_function) => self
                        .compose_functions(&function, &rhs_function)
                        .map(Value::Function),
                    _ => self.apply_function_exprs(&function, args),
                }
            }
            Value::Element(lhs_value) if args.len() == 1 => {
                self.element_at(callee, lhs_value, &args[0])
            }
            Value::Element(_) => Err(fn_sort_error()),
            Value::Index(_) => Err(self
                .non_function_at_error()
                .unwrap_or_else(index_sort_error)),
            Value::Bool(_) => Err(self.non_function_at_error().unwrap_or_else(bool_sort_error)),
        }
    }

    fn apply_function(
        &mut self,
        function: &FunctionValue,
        args: Vec<Value<Self::Element>>,
    ) -> OghamResult<Value<Self::Element>> {
        if args.len() != function.binders.len() {
            return Err(function_arity_error(function.binders.len(), args.len()));
        }
        let budget = self.fuel_budget();
        consume_fuel(function, self.fuel_remaining_mut(), budget)?;
        for (binder, arg) in function.binders.iter().zip(&args) {
            ensure_value_sort(arg, binder.sort)?;
        }
        let call_key = self.function_call_key(function, &args);
        if let Some(key) = call_key.as_deref() {
            if self.call_key_is_active(key) {
                *self.fuel_remaining_mut() = 0;
                return Err(OghamError::new(
                    OghamErrorKind::Fuel,
                    Span::point(0),
                    format!(
                        "recursive definition `{}` exhausted its fuel budget of {}",
                        function.mu_name.as_deref().unwrap_or("μ"),
                        budget
                    ),
                ));
            }
        }
        let remaining = *self.fuel_remaining_mut();
        let recursive_frame =
            enter_recursion_frame(function, self.recursion_depth_mut(), remaining, budget)?;
        if let Some(key) = call_key.clone() {
            self.activate_call_key(key);
        }
        let previous_args = self.install_call_arguments(function, &args);
        let previous = function.mu_name.as_ref().map(|name| {
            self.env_mut()
                .insert(name.clone(), Value::Function(function.clone()))
        });
        let result = self.eval_function_body(function, &args);
        if let Some(name) = &function.mu_name {
            if let Some(previous) = previous.flatten() {
                self.env_mut().insert(name.clone(), previous);
            } else {
                self.env_mut().remove(name);
            }
        }
        for (name, previous) in previous_args.into_iter().rev() {
            if let Some(previous) = previous {
                self.env_mut().insert(name, previous);
            } else {
                self.env_mut().remove(&name);
            }
        }
        if let Some(key) = call_key {
            self.deactivate_call_key(&key);
        }
        leave_recursion_frame(recursive_frame, self.recursion_depth_mut());
        result
    }

    fn apply_function_exprs(
        &mut self,
        function: &FunctionValue,
        args: &[Expr],
    ) -> OghamResult<Value<Self::Element>> {
        if args.len() != function.binders.len() {
            return Err(function_arity_error(function.binders.len(), args.len()));
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
        sort: DataSort,
    ) -> OghamResult<Value<Self::Element>> {
        match sort {
            DataSort::Element => self.world_eval_element(expr).map(Value::Element),
            DataSort::Index => self.eval_index(expr).map(Value::Index),
            DataSort::Bool => self.eval_bool(expr).map(Value::Bool),
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
            ret: DataSort::Element,
            mu_name: None,
        };
        self.validate_function_body(&function)?;
        Ok(function)
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
            self.reserved_ident(name) || reserved_function_binder(name)
        })
        .map_err(|err| self.adjust_binder_error(err))?;
        let mut bound: BTreeSet<String> = binders.iter().cloned().collect();
        bound.extend(mu_name.iter().cloned());
        bound.extend(self.validation_sample_function_names().iter().cloned());
        let substituted = substitute_env(&body, &bound, self.env())?;
        let body = beta_normalize(substituted)?;
        let (mut binder_sorts, mut ret) = infer_function_signature(&body, &binders)?;
        self.refine_function_signature(
            &body,
            &binders,
            &mut binder_sorts,
            &mut ret,
            mu_name.as_deref(),
        );
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
            let sample = validation_sample_function(&function, self.sample_expr(function.ret)?);
            let previous = self.env_mut().insert(name.clone(), Value::Function(sample));
            self.validation_sample_function_names_mut()
                .insert(name.clone());
            let validation = self.validate_function_body(&function);
            self.validation_sample_function_names_mut().remove(name);
            if let Some(previous) = previous {
                self.env_mut().insert(name.clone(), previous);
            } else {
                self.env_mut().remove(name);
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
                let saved = self.env().clone();
                let saved_samples = self.validation_sample_function_names().clone();
                let result = (|| {
                    let mut index = 0;
                    while index < bindings.len() {
                        let consumed = if bindings[index].recursive {
                            self.bind_recursive_system(&bindings[index..])?
                        } else {
                            0
                        };
                        if consumed > 0 {
                            for binding in &bindings[index..index + consumed] {
                                self.validate_all(&binding.expr)?;
                            }
                            index += consumed;
                            continue;
                        }
                        let binding = &bindings[index];
                        if !matches!(binding.expr, Expr::Lambda { .. }) {
                            self.validate_all(&binding.expr)?;
                        }
                        self.bind_name(&binding.name, &binding.expr, binding.recursive)?;
                        if let Some(Value::Function(function)) =
                            self.env().get(&binding.name).cloned()
                        {
                            let sample = validation_sample_function(
                                &function,
                                self.sample_expr(function.ret)?,
                            );
                            self.env_mut()
                                .insert(binding.name.clone(), Value::Function(sample));
                            self.validation_sample_function_names_mut()
                                .insert(binding.name.clone());
                        }
                        index += 1;
                    }
                    self.validate_all(body)
                })();
                *self.env_mut() = saved;
                *self.validation_sample_function_names_mut() = saved_samples;
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
                if self.skip_ternary_eval_after_validation() {
                    return Ok(());
                }
            }
            Expr::Binary {
                op: BinaryOp::And | BinaryOp::Or | BinaryOp::Append,
                lhs,
                rhs,
            } => {
                // These are exactly the non-strict binary positions. Validate
                // both sides now; runtime evaluation may skip the right side.
                self.validate_all(lhs)?;
                self.validate_all(rhs)?;
            }
            _ => {}
        }
        ignore_static_partiality(self.eval_value(expr))
    }

    fn sample_expr(&self, sort: DataSort) -> OghamResult<Expr> {
        match sort {
            DataSort::Element => self.sample_element_expr(),
            DataSort::Index => Ok(Expr::Int(1)),
            DataSort::Bool => Ok(Expr::Bool(true)),
        }
    }

    fn static_sort(&self, expr: &Expr) -> OghamResult<DataSort> {
        static_sort(expr, self.env(), self.deg_is_index())
    }
}

impl<T: WorldOps> SharedRuntime for T {}
