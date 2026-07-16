//! Polynomial-world runtime, coefficient contract, and polynomial helpers.

use super::super::*;

pub(crate) struct PolyRuntime<S: PolyWorldCoeff> {
    pub(crate) name: &'static str,
    pub(crate) state: RuntimeState<Poly<S>>,
}

impl<S: PolyWorldCoeff> WorldOps for PolyRuntime<S> {
    type Element = Poly<S>;

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
        PolyRuntime::eval_element(self, expr)
    }

    fn index_primitive(&mut self, expr: &Expr) -> IndexPrimitive {
        match expr {
            Expr::Call { name, .. } if name == "dim" => {
                IndexPrimitive::Error(literal_call_error(name))
            }
            Expr::Dim => IndexPrimitive::Error(array_world_error("dim")),
            Expr::Call { name, args } if name == "deg" => IndexPrimitive::from_result((|| {
                expect_arity(name, args, 1)?;
                let value = self.eval_element(&args[0])?;
                let degree = value.degree().ok_or_else(|| {
                    GrundyError::new(
                        GrundyErrorKind::Domain,
                        Span::point(0),
                        "degree of the zero polynomial is undefined",
                    )
                })?;
                i128::try_from(degree).map_err(|_| overflow("polynomial degree exceeds i128"))
            })(
            )),
            Expr::GameForm { .. } => IndexPrimitive::Error(game_only_error("game forms")),
            _ => IndexPrimitive::NotHandled,
        }
    }

    fn world_eval_relation(&mut self, op: RelOp, lhs: &Expr, rhs: &Expr) -> GrundyResult<bool> {
        PolyRuntime::eval_relation(self, op, lhs, rhs)
    }

    fn sample_element_expr(&self) -> GrundyResult<Expr> {
        parse_display_expr(&Poly::<S>::one().to_string())
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
        Ok((name == "t").then(Poly::t))
    }

    fn special_value_call(
        &mut self,
        name: &str,
        args: &[Expr],
    ) -> Option<GrundyResult<Value<Self::Element>>> {
        (name == "integral").then(|| {
            expect_arity(name, args, 1)?;
            self.eval_element(&args[0])?;
            Ok(Value::Bool(true))
        })
    }

    fn deg_is_index(&self) -> bool {
        true
    }

    fn prefer_index_expression(&self) -> bool {
        true
    }

    fn element_at(
        &mut self,
        lhs_expr: &Expr,
        lhs: Self::Element,
        rhs: &Expr,
    ) -> GrundyResult<Value<Self::Element>> {
        match self.eval_value(rhs)? {
            Value::Element(rhs) => Ok(Value::Element(lhs.compose(&rhs))),
            Value::Function(rhs) => self
                .compose_element_with_function(lhs_expr, &rhs)
                .map(Value::Function),
            Value::Index(_) => Err(index_sort_error()),
            Value::Bool(_) => Err(bool_sort_error()),
        }
    }
}

impl<S: PolyWorldCoeff> PolyRuntime<S> {
    pub(crate) fn new(name: &'static str) -> Self {
        PolyRuntime {
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

    fn eval_element(&mut self, expr: &Expr) -> GrundyResult<Poly<S>> {
        match expr {
            Expr::Bool(_) => Err(bool_sort_error()),
            Expr::Index(_) => Err(index_sort_error()),
            Expr::GameForm { .. } => Err(game_only_error("game forms")),
            Expr::Int(n) => Ok(Poly::constant(S::bare_int(*n, Span::point(0))?)),
            Expr::Star(star) => Ok(Poly::constant(S::star(star, Span::point(0))?)),
            Expr::Omega => Ok(Poly::constant(S::omega(Span::point(0))?)),
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
                    Ok(Poly::t())
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

    fn eval_binary(&mut self, op: BinaryOp, lhs: &Expr, rhs: &Expr) -> GrundyResult<Poly<S>> {
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
            BinaryOp::Wedge => Err(GrundyError::new(
                GrundyErrorKind::WrongWorld,
                Span::point(0),
                "wedge product belongs to Clifford worlds",
            )),
            BinaryOp::Pow | BinaryOp::And | BinaryOp::Or | BinaryOp::Append => unreachable!(),
        }
    }

    fn eval_power(&mut self, lhs: &Expr, rhs: &Expr) -> GrundyResult<Poly<S>> {
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
            Ok(pow_poly(&inv, k))
        } else {
            let k = u128::try_from(exp).map_err(|_| overflow("exponent exceeds u128"))?;
            Ok(pow_poly(&base, k))
        }
    }

    fn eval_call(&mut self, name: &str, args: &[Expr]) -> GrundyResult<Poly<S>> {
        match name {
            "up" | "down" | "dim" => Err(literal_call_error(name)),
            "coef" => {
                expect_arity(name, args, 2)?;
                let value = self.eval_element(&args[0])?;
                let index = self.eval_index(&args[1])?;
                let index = usize::try_from(index)
                    .map_err(|_| domain("coefficient index must be non-negative"))?;
                Ok(Poly::constant(value.coeff(index)))
            }
            "deg" => Err(index_sort_error().with_hint("`deg` returns an Index")),
            "integral" => Err(bool_sort_error()),
            "gcd" => {
                expect_arity(name, args, 2)?;
                let lhs = self.eval_element(&args[0])?;
                let rhs = self.eval_element(&args[1])?;
                S::gcd_poly(&lhs, &rhs, Span::point(0))
            }
            _ => Err(GrundyError::new(
                GrundyErrorKind::UnknownFn,
                Span::point(0),
                format!("unknown function `{name}`"),
            )),
        }
    }

    fn inverse_element(&self, value: &Poly<S>) -> GrundyResult<Poly<S>> {
        if value.is_zero() {
            return Err(GrundyError::new(
                GrundyErrorKind::DivisionByZero,
                Span::point(0),
                "division by zero",
            ));
        }
        value.inv().ok_or_else(|| {
            GrundyError::new(
                GrundyErrorKind::NotInvertible,
                Span::point(0),
                "polynomial is not a unit",
            )
        })
    }

    fn eval_container(&mut self, items: &[Expr]) -> GrundyResult<Poly<S>> {
        let mut coefficients = Vec::with_capacity(items.len());
        for item in items {
            let value = self.eval_element(item)?;
            if value.degree().is_some_and(|degree| degree > 0) {
                return Err(GrundyError::new(
                    GrundyErrorKind::Domain,
                    Span::point(0),
                    "polynomial container entry is not constant",
                )
                .with_hint("container entries are coefficients; `t` is not a coefficient"));
            }
            coefficients.push(value.coeff(0));
        }
        Ok(Poly::new(coefficients))
    }
}

pub(crate) trait PolyWorldCoeff: GrundyScalar {
    fn divrem_poly(
        lhs: &Poly<Self>,
        divisor: &Poly<Self>,
        span: Span,
    ) -> GrundyResult<(Poly<Self>, Poly<Self>)>;
    fn gcd_poly(lhs: &Poly<Self>, rhs: &Poly<Self>, span: Span) -> GrundyResult<Poly<Self>>;
}

impl<const P: u128> PolyWorldCoeff for Fp<P>
where
    Fp<P>: GrundyScalar,
{
    fn divrem_poly(
        lhs: &Poly<Self>,
        divisor: &Poly<Self>,
        span: Span,
    ) -> GrundyResult<(Poly<Self>, Poly<Self>)> {
        if divisor.is_zero() {
            return Err(GrundyError::new(
                GrundyErrorKind::DivisionByZero,
                span,
                "polynomial division by zero",
            ));
        }
        Ok(lhs.divrem(divisor))
    }

    fn gcd_poly(lhs: &Poly<Self>, rhs: &Poly<Self>, _span: Span) -> GrundyResult<Poly<Self>> {
        Ok(lhs.gcd(rhs))
    }
}

impl PolyWorldCoeff for Integer {
    fn divrem_poly(
        lhs: &Poly<Self>,
        divisor: &Poly<Self>,
        span: Span,
    ) -> GrundyResult<(Poly<Self>, Poly<Self>)> {
        if divisor.is_zero() {
            return Err(GrundyError::new(
                GrundyErrorKind::DivisionByZero,
                span,
                "polynomial division by zero",
            ));
        }
        if !matches!(divisor.leading(), Some(c) if *c == Integer::one()) {
            return Err(polyint_modulus_error(span));
        }
        Ok(lhs.divrem(divisor))
    }

    fn gcd_poly(lhs: &Poly<Self>, rhs: &Poly<Self>, span: Span) -> GrundyResult<Poly<Self>> {
        integer_poly_gcd(lhs, rhs, span)
    }
}

pub(crate) fn poly_rem<S: PolyWorldCoeff>(
    lhs: &Poly<S>,
    rhs: &Poly<S>,
    span: Span,
) -> GrundyResult<Poly<S>> {
    let (_, r) = S::divrem_poly(lhs, rhs, span)?;
    Ok(r)
}

pub(crate) fn poly_exact_div<S: PolyWorldCoeff>(
    lhs: &Poly<S>,
    rhs: &Poly<S>,
    span: Span,
) -> GrundyResult<Poly<S>> {
    let (q, r) = S::divrem_poly(lhs, rhs, span)?;
    if r.is_zero() {
        Ok(q)
    } else {
        Err(GrundyError::new(
            GrundyErrorKind::NotInvertible,
            span,
            format!("polynomial exact division failed with remainder {r}"),
        ))
    }
}

pub(crate) fn pow_poly<S: Scalar>(base: &Poly<S>, mut k: u128) -> Poly<S> {
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

pub(crate) fn integer_poly_gcd(
    lhs: &Poly<Integer>,
    rhs: &Poly<Integer>,
    span: Span,
) -> GrundyResult<Poly<Integer>> {
    let lhs = integer_poly_to_rational(lhs);
    let rhs = integer_poly_to_rational(rhs);
    primitive_integer_poly_from_rational(&lhs.gcd(&rhs), span)
}

pub(crate) fn integer_poly_to_rational(p: &Poly<Integer>) -> Poly<Rational> {
    Poly::new(p.coeffs().iter().map(|c| Rational::from_int(c.0)).collect())
}

pub(crate) fn primitive_integer_poly_from_rational(
    p: &Poly<Rational>,
    span: Span,
) -> GrundyResult<Poly<Integer>> {
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

pub(crate) fn gcd_i128_slice(values: &[i128], span: Span) -> GrundyResult<i128> {
    let mut g = 0u128;
    for value in values {
        g = gcd_u128_local(g, value.unsigned_abs());
    }
    i128::try_from(g).map_err(|_| {
        GrundyError::new(
            GrundyErrorKind::Overflow,
            span,
            "integer polynomial gcd content exceeds i128",
        )
    })
}

pub(crate) fn lcm_positive_i128(lhs: i128, rhs: i128, span: Span) -> GrundyResult<i128> {
    debug_assert!(lhs > 0 && rhs > 0);
    let gcd = gcd_u128_local(lhs as u128, rhs as u128);
    let gcd = i128::try_from(gcd).map_err(|_| {
        GrundyError::new(
            GrundyErrorKind::Overflow,
            span,
            "integer polynomial denominator gcd exceeds i128",
        )
    })?;
    lhs.checked_div(gcd)
        .and_then(|x| x.checked_mul(rhs))
        .ok_or_else(|| overflow("integer polynomial denominator lcm overflowed i128"))
}

pub(crate) fn gcd_u128_local(mut lhs: u128, mut rhs: u128) -> u128 {
    while rhs != 0 {
        let next = lhs % rhs;
        lhs = rhs;
        rhs = next;
    }
    lhs
}
