//! Rational-function-world runtime and substitution helpers.

use super::super::*;

pub(crate) struct RatFuncRuntime<S: GrundyScalar + ExactFieldScalar> {
    pub(crate) name: &'static str,
    pub(crate) state: RuntimeState<RationalFunction<S>>,
}

impl<S: GrundyScalar + ExactFieldScalar> WorldOps for RatFuncRuntime<S> {
    type Element = RationalFunction<S>;

    fn state(&self) -> &RuntimeState<Self::Element> {
        &self.state
    }

    fn state_mut(&mut self) -> &mut RuntimeState<Self::Element> {
        &mut self.state
    }

    fn world_name(&self) -> &'static str {
        self.name
    }

    fn world_summary(&self) -> String {
        self.name.to_string()
    }

    fn world_eval_element(&mut self, expr: &Expr) -> GrundyResult<Self::Element> {
        RatFuncRuntime::eval_element(self, expr)
    }

    fn index_primitive(&mut self, expr: &Expr) -> IndexPrimitive {
        match expr {
            Expr::Call { name, .. } if name == "deg" => IndexPrimitive::Error(GrundyError::new(
                GrundyErrorKind::WrongWorld,
                Span::point(0),
                "`deg` is a polynomial-world function, not a rational-function operation",
            )),
            Expr::Call { name, .. } if name == "dim" => {
                IndexPrimitive::Error(literal_call_error(name))
            }
            Expr::Dim => IndexPrimitive::Error(array_world_error("dim")),
            Expr::GameForm { .. } => IndexPrimitive::Error(game_only_error("game forms")),
            _ => IndexPrimitive::NotHandled,
        }
    }

    fn world_eval_relation(&mut self, op: RelOp, lhs: &Expr, rhs: &Expr) -> GrundyResult<bool> {
        RatFuncRuntime::eval_relation(self, op, lhs, rhs)
    }

    fn sample_element_expr(&self) -> GrundyResult<Expr> {
        parse_display_expr(&RationalFunction::<S>::one().to_string())
    }

    fn reserved_ident(&self, name: &str) -> bool {
        name == "t"
    }

    fn adjust_binder_error(&self, err: GrundyError) -> GrundyError {
        if err.kind == GrundyErrorKind::Shadow && err.message.contains("`t`") {
            err.with_hint("`t` is the indeterminate here; `5⋅t + 1` is already a function")
        } else {
            err
        }
    }

    fn named_element(&self, name: &str) -> GrundyResult<Option<Self::Element>> {
        Ok((name == "t").then(RationalFunction::t))
    }

    fn special_value_call(
        &mut self,
        name: &str,
        args: &[Expr],
    ) -> Option<GrundyResult<Value<Self::Element>>> {
        (name == "integral").then(|| {
            expect_arity(name, args, 1)?;
            let value = self.eval_element(&args[0])?;
            Ok(Value::Bool(value.is_integral()))
        })
    }

    fn element_at(
        &mut self,
        lhs_expr: &Expr,
        lhs: Self::Element,
        rhs: &Expr,
    ) -> GrundyResult<Value<Self::Element>> {
        match self.eval_value(rhs)? {
            Value::Element(rhs) => {
                substitute_rational_function(&lhs, &rhs, Span::point(0)).map(Value::Element)
            }
            Value::Function(rhs) => self
                .compose_element_with_function(lhs_expr, &rhs)
                .map(Value::Function),
            Value::Index(_) => Err(index_sort_error()),
            Value::Bool(_) => Err(bool_sort_error()),
        }
    }
}

impl<S: GrundyScalar + ExactFieldScalar> RatFuncRuntime<S> {
    pub(crate) fn new(name: &'static str) -> Self {
        RatFuncRuntime {
            name,
            state: RuntimeState::new(),
        }
    }

    fn eval_relation(&mut self, op: RelOp, lhs: &Expr, rhs: &Expr) -> GrundyResult<bool> {
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

    fn eval_element(&mut self, expr: &Expr) -> GrundyResult<RationalFunction<S>> {
        match expr {
            Expr::Bool(_) => Err(bool_sort_error()),
            Expr::Index(_) => Err(index_sort_error()),
            Expr::GameForm { .. } => Err(game_only_error("game forms")),
            Expr::Int(n) => Ok(RationalFunction::from_base(S::bare_int(
                *n,
                Span::point(0),
            )?)),
            Expr::Star(star) => Ok(RationalFunction::from_base(S::star(star, Span::point(0))?)),
            Expr::Omega => Ok(RationalFunction::from_base(S::omega(Span::point(0))?)),
            Expr::Blade(_) => Err(GrundyError::new(
                GrundyErrorKind::WrongWorld,
                Span::point(0),
                "function-shaped worlds do not have Clifford blades",
            )),
            Expr::Container(items) => self.eval_container(items),
            Expr::Up => Err(game_only_error("`up`")),
            Expr::Down => Err(game_only_error("`down`")),
            Expr::Dim => Err(array_world_error("dim")),
            Expr::Ident(name) => {
                if name == "t" {
                    Ok(RationalFunction::t())
                } else if let Some(value) = self.state.env.get(name) {
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
            Expr::Lambda { .. } => Err(fn_sort_error()),
            Expr::Block { bindings, body } => match self.eval_block(bindings, body)? {
                Value::Element(value) => Ok(value),
                Value::Index(_) => Err(index_sort_error()),
                Value::Bool(_) => Err(bool_sort_error()),
                Value::Function(_) => Err(fn_sort_error()),
            },
            Expr::Call { name, args } => self.eval_call(name, args),
            Expr::Unary { op, expr } => {
                let value = self.eval_element(expr)?;
                match op {
                    UnaryOp::Neg => Ok(value.neg()),
                    UnaryOp::Inv => self.inverse_element(&value),
                    UnaryOp::Not => Err(bool_sort_error()),
                }
            }
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
            Expr::Relation { .. } => Err(GrundyError::new(
                GrundyErrorKind::BoolSort,
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
    ) -> GrundyResult<RationalFunction<S>> {
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
                    Err(GrundyError::new(
                        GrundyErrorKind::DivisionByZero,
                        Span::point(0),
                        "division by zero",
                    ))
                } else {
                    Ok(lhs_v.mul(&rhs_v.inv().expect("checked nonzero rational function")))
                }
            }
            BinaryOp::Rem => Err(GrundyError::new(
                GrundyErrorKind::WrongWorld,
                Span::point(0),
                "function-field worlds are fields",
            )
            .with_hint("`%` is only active in polynomial worlds")),
            BinaryOp::Wedge => Err(GrundyError::new(
                GrundyErrorKind::WrongWorld,
                Span::point(0),
                "wedge product belongs to Clifford worlds",
            )),
            BinaryOp::Pow | BinaryOp::And | BinaryOp::Or | BinaryOp::Append => unreachable!(),
        }
    }

    fn eval_power(&mut self, lhs: &Expr, rhs: &Expr) -> GrundyResult<RationalFunction<S>> {
        let base = self.eval_element(lhs)?;
        let exp = self.eval_index(rhs).map_err(|err| {
            if err.kind == GrundyErrorKind::IndexSort {
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

    fn eval_call(&mut self, name: &str, _args: &[Expr]) -> GrundyResult<RationalFunction<S>> {
        match name {
            "up" | "down" | "dim" => Err(literal_call_error(name)),
            "coef" => Err(GrundyError::new(
                GrundyErrorKind::WrongWorld,
                Span::point(0),
                "`coef` is unavailable on rational functions",
            )),
            "deg" | "gcd" => Err(GrundyError::new(
                GrundyErrorKind::WrongWorld,
                Span::point(0),
                format!(
                    "`{name}` is a polynomial-world function, not a rational-function operation"
                ),
            )),
            "integral" => Err(bool_sort_error()),
            _ => Err(GrundyError::new(
                GrundyErrorKind::UnknownFn,
                Span::point(0),
                format!("unknown function `{name}`"),
            )),
        }
    }

    fn inverse_element(&self, value: &RationalFunction<S>) -> GrundyResult<RationalFunction<S>> {
        if value.is_zero() {
            return Err(GrundyError::new(
                GrundyErrorKind::DivisionByZero,
                Span::point(0),
                "division by zero",
            ));
        }
        Ok(value.inv().expect("checked nonzero rational function"))
    }

    fn eval_container(&mut self, items: &[Expr]) -> GrundyResult<RationalFunction<S>> {
        let mut coefficients = Vec::with_capacity(items.len());
        for item in items {
            let value = self.eval_element(item)?;
            if value.den() != &Poly::one() || value.num().degree().is_some_and(|degree| degree > 0)
            {
                return Err(GrundyError::new(
                    GrundyErrorKind::Domain,
                    Span::point(0),
                    "rational-function container entry is not constant",
                )
                .with_hint("container entries are coefficients; `t` is not a coefficient"));
            }
            coefficients.push(value.num().coeff(0));
        }
        Ok(RationalFunction::from_poly(Poly::new(coefficients)))
    }
}

pub(crate) fn pow_rational_function<S: ExactFieldScalar>(
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

pub(crate) fn substitute_rational_function<S: GrundyScalar + ExactFieldScalar>(
    f: &RationalFunction<S>,
    arg: &RationalFunction<S>,
    span: Span,
) -> GrundyResult<RationalFunction<S>> {
    let num = eval_poly_at_rational_function(f.num(), arg);
    let den = eval_poly_at_rational_function(f.den(), arg);
    if den.is_zero() {
        return Err(GrundyError::new(
            GrundyErrorKind::DivisionByZero,
            span,
            "rational-function evaluation hit a pole",
        ));
    }
    Ok(num.mul(&den.inv().expect("checked nonzero rational function")))
}

pub(crate) fn eval_poly_at_rational_function<S: ExactFieldScalar>(
    poly: &Poly<S>,
    x: &RationalFunction<S>,
) -> RationalFunction<S> {
    let mut acc = RationalFunction::zero();
    for c in poly.coeffs().iter().rev() {
        acc = acc.mul(x).add(&RationalFunction::from_base(c.clone()));
    }
    acc
}
