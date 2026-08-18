//! Clifford-world runtime, scalar contract, and metric/scalar parsing.

use super::super::*;

pub(crate) struct CliffordRuntime<S: GrundyScalar> {
    pub(crate) name: &'static str,
    pub(crate) alg: CliffordAlgebra<S>,
    pub(crate) state: RuntimeState<Multivector<S>>,
}

impl<S: GrundyScalar> WorldOps for CliffordRuntime<S> {
    type Element = Multivector<S>;

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
        format!("{} dim {}", self.name, self.alg.dim())
    }

    fn world_eval_element(&mut self, expr: &Expr) -> GrundyResult<Self::Element> {
        CliffordRuntime::eval_expr(self, expr)
    }

    fn index_primitive(&mut self, expr: &Expr) -> IndexPrimitive {
        match expr {
            Expr::Call { name, .. } if name == "dim" => {
                IndexPrimitive::Error(literal_call_error(name))
            }
            Expr::Dim => IndexPrimitive::from_result(
                i128::try_from(self.alg.dim())
                    .map_err(|_| overflow("world dimension exceeds i128")),
            ),
            Expr::GameForm { .. } => IndexPrimitive::Error(game_only_error("game forms")),
            _ => IndexPrimitive::NotHandled,
        }
    }

    fn world_eval_relation(&mut self, op: RelOp, lhs: &Expr, rhs: &Expr) -> GrundyResult<bool> {
        CliffordRuntime::eval_relation(self, op, lhs, rhs)
    }

    fn sample_element_expr(&self) -> GrundyResult<Expr> {
        parse_display_expr(&self.alg.scalar(S::one()).to_string())
    }

    fn reserved_ident(&self, name: &str) -> bool {
        S::reserved_ident(name)
    }

    fn named_element(&self, name: &str) -> GrundyResult<Option<Self::Element>> {
        Ok(S::named_element(name, Span::point(0))?.map(|value| self.alg.scalar(value)))
    }

    fn special_value_call(
        &mut self,
        name: &str,
        args: &[Expr],
    ) -> Option<GrundyResult<Value<Self::Element>>> {
        (name == "integral").then(|| {
            expect_arity(name, args, 1)?;
            let value = self.eval_grade0(&args[0])?;
            S::integral(&value, Span::point(0)).map(Value::Bool)
        })
    }

    fn non_function_at_error(&self) -> Option<GrundyError> {
        Some(
            GrundyError::new(
                GrundyErrorKind::WrongWorld,
                Span::point(0),
                "only Function values apply with `@` in this world",
            )
            .with_hint("element evaluation lives in function-shaped worlds"),
        )
    }
}

impl<S: GrundyScalar> CliffordRuntime<S> {
    pub(crate) fn from_metric(name: &'static str, metric: Metric<S>) -> Self {
        CliffordRuntime {
            name,
            alg: CliffordAlgebra::new(metric.dim(), metric),
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

    fn eval_expr(&mut self, expr: &Expr) -> GrundyResult<Multivector<S>> {
        match expr {
            Expr::Bool(_) => Err(bool_sort_error()),
            Expr::Index(_) | Expr::Dim => Err(index_sort_error()),
            Expr::GameForm { .. } => Err(game_only_error("game forms")),
            Expr::Int(n) => Ok(self.alg.scalar(S::bare_int(*n, Span::point(0))?)),
            Expr::Star(star) => Ok(self.alg.scalar(S::star(star, Span::point(0))?)),
            Expr::Omega => Ok(self.alg.scalar(S::omega(Span::point(0))?)),
            Expr::Blade(i) => {
                if *i >= self.alg.dim() {
                    Err(GrundyError::new(
                        GrundyErrorKind::BladeIndex,
                        Span::point(0),
                        format!("blade e{i} is outside dimension {}", self.alg.dim()),
                    ))
                } else {
                    Ok(self.alg.e(*i))
                }
            }
            Expr::Container(items) => self.eval_container(items),
            Expr::Up => Err(game_only_error("`up`")),
            Expr::Down => Err(game_only_error("`down`")),
            Expr::Lambda { .. } => Err(fn_sort_error()),
            Expr::Block { bindings, body } => into_element(self.eval_block(bindings, body)?),
            Expr::Ident(name) => {
                if let Some(value) = self.state.env.get(name) {
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
            Expr::Unary { op, expr } => {
                let value = self.eval_expr(expr)?;
                match op {
                    UnaryOp::Neg => Ok(-value),
                    UnaryOp::Inv => self.inverse_mv(&value),
                    UnaryOp::Not => Err(bool_sort_error()),
                }
            }
            Expr::Apply { .. } | Expr::If { .. } => into_element(self.eval_value(expr)?),
            Expr::Binary { op, lhs, rhs } => self.eval_binary(*op, lhs, rhs),
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
    ) -> GrundyResult<Multivector<S>> {
        if op == BinaryOp::Append {
            return Err(game_only_error("`⧺`"));
        }
        if op == BinaryOp::Pow {
            return self.eval_power(lhs, rhs);
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
            BinaryOp::Pow | BinaryOp::And | BinaryOp::Or | BinaryOp::Append => {
                unreachable!()
            }
        }
    }

    fn eval_power(&mut self, lhs: &Expr, rhs: &Expr) -> GrundyResult<Multivector<S>> {
        if lhs.is_omega_atom() {
            if let Err(index_err) = self.eval_index(rhs) {
                if index_err.kind == GrundyErrorKind::IndexSort {
                    if matches!(rhs, Expr::Index(_)) {
                        return Err(index_err);
                    }
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
            if err.kind == GrundyErrorKind::IndexSort {
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

    fn eval_container(&mut self, items: &[Expr]) -> GrundyResult<Multivector<S>> {
        if items.len() != self.alg.dim() {
            return Err(GrundyError::new(
                GrundyErrorKind::DimMismatch,
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

    fn eval_call(&mut self, name: &str, args: &[Expr]) -> GrundyResult<Multivector<S>> {
        match name {
            "coef" => {
                expect_arity(name, args, 2)?;
                let value = self.eval_expr(&args[0])?;
                let index = self.eval_index(&args[1])?;
                let index = usize::try_from(index).map_err(|_| {
                    GrundyError::new(
                        GrundyErrorKind::BladeIndex,
                        Span::point(0),
                        format!(
                            "coefficient index {index} is outside dimension {}",
                            self.alg.dim()
                        ),
                    )
                })?;
                if index >= self.alg.dim() {
                    return Err(GrundyError::new(
                        GrundyErrorKind::BladeIndex,
                        Span::point(0),
                        format!(
                            "coefficient index {index} is outside dimension {}",
                            self.alg.dim()
                        ),
                    ));
                }
                let mask = 1u128.checked_shl(index as u32).ok_or_else(|| {
                    GrundyError::new(
                        GrundyErrorKind::BladeIndex,
                        Span::point(0),
                        format!("coefficient index {index} exceeds the u128 blade mask"),
                    )
                })?;
                let coefficient = value.terms().get(&mask).cloned().unwrap_or_else(S::zero);
                Ok(self.alg.scalar(coefficient))
            }
            "up" | "down" | "dim" => Err(literal_call_error(name)),
            "rev" => {
                expect_arity(name, args, 1)?;
                if self.alg.metric().has_upper() {
                    return Err(GrundyError::new(
                        GrundyErrorKind::GeneralMetric,
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
                    return Err(GrundyError::new(
                        GrundyErrorKind::Domain,
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
                    return Err(GrundyError::new(
                        GrundyErrorKind::GeneralMetric,
                        Span::point(0),
                        "dual is undefined for general-bilinear metrics",
                    ));
                }
                let x = self.eval_expr(&args[0])?;
                self.alg.dual(&x).ok_or_else(|| {
                    GrundyError::new(
                        GrundyErrorKind::NotInvertible,
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
                    return Err(GrundyError::new(
                        GrundyErrorKind::Arity,
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
            "integral" => Err(bool_sort_error()),
            _ => Err(GrundyError::new(
                GrundyErrorKind::UnknownFn,
                Span::point(0),
                format!("unknown function `{name}`"),
            )),
        }
    }

    fn eval_grade0(&mut self, expr: &Expr) -> GrundyResult<S> {
        let value = self.eval_expr(expr)?;
        scalar_part(&value).ok_or_else(|| grade0_error(Span::point(0)))
    }

    fn inverse_mv(&self, value: &Multivector<S>) -> GrundyResult<Multivector<S>> {
        if let Some(s) = scalar_part(value) {
            if s.is_zero() {
                return Err(GrundyError::new(
                    GrundyErrorKind::DivisionByZero,
                    Span::point(0),
                    "division by zero",
                ));
            }
            return Ok(self.alg.scalar(S::inv_scalar(&s, Span::point(0))?));
        }
        self.alg.multivector_inverse(value).ok_or_else(|| {
            GrundyError::new(
                GrundyErrorKind::NotInvertible,
                Span::point(0),
                "multivector is not invertible",
            )
        })
    }

    fn div_mv(&self, lhs: &Multivector<S>, rhs: &Multivector<S>) -> GrundyResult<Multivector<S>> {
        if rhs.is_zero() {
            return Err(GrundyError::new(
                GrundyErrorKind::DivisionByZero,
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

    fn mul_mv(&self, lhs: &Multivector<S>, rhs: &Multivector<S>) -> GrundyResult<Multivector<S>> {
        if let (Some(a), Some(b)) = (scalar_part(lhs), scalar_part(rhs)) {
            return Ok(self.alg.scalar(S::mul_checked(&a, &b, Span::point(0))?));
        }
        S::mv_mul(&self.alg, lhs, rhs, Span::point(0))
    }

    fn pow_mv(&self, value: &Multivector<S>, k: u128) -> GrundyResult<Multivector<S>> {
        if let Some(s) = scalar_part(value) {
            return Ok(self.alg.scalar(S::pow_checked(&s, k, Span::point(0))?));
        }
        S::mv_pow(&self.alg, value, k, Span::point(0))
    }
}

pub(crate) trait GrundyScalar: Scalar + Sized + Display + 'static {
    fn bare_int(n: u128, span: Span) -> GrundyResult<Self>;
    fn star(lit: &StarLiteral, span: Span) -> GrundyResult<Self>;
    fn omega(span: Span) -> GrundyResult<Self>;
    fn omega_pow(_exp: Self, span: Span) -> GrundyResult<Self> {
        Err(GrundyError::new(
            GrundyErrorKind::ExpSort,
            span,
            "`ω↑s` is only an element-level monomial constructor in surreal-family worlds",
        ))
    }
    fn named_element(_name: &str, _span: Span) -> GrundyResult<Option<Self>> {
        Ok(None)
    }
    fn reserved_ident(_name: &str) -> bool {
        false
    }
    fn inv_scalar(value: &Self, span: Span) -> GrundyResult<Self> {
        value
            .inv()
            .ok_or_else(|| GrundyError::new(GrundyErrorKind::NotInvertible, span, "not invertible"))
    }
    fn exact_div(_lhs: &Self, _rhs: &Self, _span: Span) -> Option<GrundyResult<Self>> {
        None
    }
    fn rem(_lhs: &Self, _rhs: &Self, span: Span) -> GrundyResult<Self> {
        Err(GrundyError::new(
            GrundyErrorKind::WrongWorld,
            span,
            "field worlds have no informative remainder operator",
        ))
    }
    fn relation(_op: RelOp, _lhs: &Self, _rhs: &Self, span: Span) -> GrundyResult<bool> {
        Err(GrundyError::new(
            GrundyErrorKind::WrongWorld,
            span,
            "this world has no canonical order",
        ))
    }
    fn frob(_value: &Self, span: Span) -> GrundyResult<Self> {
        Err(GrundyError::new(
            GrundyErrorKind::WrongWorld,
            span,
            "`frob` is only available in finite-field worlds",
        ))
    }
    fn trace(_value: &Self, _m: Option<i128>, span: Span) -> GrundyResult<Self> {
        Err(GrundyError::new(
            GrundyErrorKind::WrongWorld,
            span,
            "`tr` is only available in finite-field worlds",
        ))
    }
    fn integral(_value: &Self, span: Span) -> GrundyResult<bool> {
        Err(GrundyError::new(
            GrundyErrorKind::WrongWorld,
            span,
            "this scalar world has no supported ring-of-integers pairing",
        ))
    }
    fn mul_checked(lhs: &Self, rhs: &Self, _span: Span) -> GrundyResult<Self> {
        Ok(lhs.mul(rhs))
    }
    fn pow_checked(base: &Self, mut k: u128, span: Span) -> GrundyResult<Self> {
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
    ) -> GrundyResult<Multivector<Self>> {
        Ok(alg.mul(lhs, rhs))
    }
    fn mv_pow(
        alg: &CliffordAlgebra<Self>,
        value: &Multivector<Self>,
        k: u128,
        _span: Span,
    ) -> GrundyResult<Multivector<Self>> {
        Ok(alg.pow(value, k))
    }
}

impl GrundyScalar for Nimber {
    fn bare_int(n: u128, span: Span) -> GrundyResult<Self> {
        if n == 0 {
            return Ok(Nimber::zero());
        }
        Err(GrundyError::new(
            GrundyErrorKind::BareInt,
            span,
            format!("bare integer `{n}` is not a nimber literal"),
        )
        .with_hint(format!("did you mean `*{n}`?")))
    }

    fn star(lit: &StarLiteral, span: Span) -> GrundyResult<Self> {
        match lit {
            StarLiteral::Finite(n) => Ok(Nimber(*n)),
            StarLiteral::Cnf(_) => Err(GrundyError::new(
                GrundyErrorKind::WrongWorld,
                span,
                "transfinite star-literals belong to the `ordinal` world",
            )),
        }
    }

    fn omega(span: Span) -> GrundyResult<Self> {
        Err(GrundyError::new(
            GrundyErrorKind::WrongWorld,
            span,
            "`ω` is not a finite nimber literal",
        ))
    }

    fn relation(op: RelOp, lhs: &Self, rhs: &Self, _span: Span) -> GrundyResult<bool> {
        Ok(match op {
            RelOp::Lt | RelOp::Gt => false,
            RelOp::Fuzzy => lhs.fuzzy(rhs),
            RelOp::Eq => lhs == rhs,
            RelOp::Equiv => return Err(game_only_error("`≡`")),
            RelOp::Outcome(_) => return Err(game_only_error("outcome doubles")),
        })
    }

    fn frob(value: &Self, _span: Span) -> GrundyResult<Self> {
        Ok(value.frobenius())
    }

    fn trace(value: &Self, m: Option<i128>, span: Span) -> GrundyResult<Self> {
        let Some(m) = m else {
            return Err(GrundyError::new(
                GrundyErrorKind::Arity,
                span,
                "`tr` in the nimber world expects `tr(x, m)`",
            ));
        };
        if m <= 0 {
            return Err(GrundyError::new(
                GrundyErrorKind::Domain,
                span,
                "nimber trace degree must be positive",
            ));
        }
        Ok(Nimber(nim_trace(value.0, m as u128)))
    }
}

impl GrundyScalar for Ordinal {
    fn bare_int(n: u128, span: Span) -> GrundyResult<Self> {
        if n == 0 {
            return Ok(Ordinal::from_u128(0));
        }
        Err(GrundyError::new(
            GrundyErrorKind::BareInt,
            span,
            format!("bare integer `{n}` is not an ordinal-nimber value"),
        )
        .with_hint(format!("did you mean `*{n}`?")))
    }

    fn star(lit: &StarLiteral, _span: Span) -> GrundyResult<Self> {
        Ok(match lit {
            StarLiteral::Finite(n) => Ordinal::from_u128(*n),
            StarLiteral::Cnf(cnf) => cnf.clone(),
        })
    }

    fn omega(span: Span) -> GrundyResult<Self> {
        Err(GrundyError::new(
            GrundyErrorKind::BareOrdinal,
            span,
            "bare `ω` is an ordinal address, not a value",
        )
        .with_hint("values are starred here: `*ω`"))
    }

    fn inv_scalar(value: &Self, span: Span) -> GrundyResult<Self> {
        if value.is_zero() {
            return Err(GrundyError::new(
                GrundyErrorKind::DivisionByZero,
                span,
                "division by zero",
            ));
        }
        value.checked_inv().ok_or_else(|| kummer_escape(span))
    }

    fn relation(op: RelOp, lhs: &Self, rhs: &Self, _span: Span) -> GrundyResult<bool> {
        Ok(match op {
            RelOp::Lt | RelOp::Gt => false,
            RelOp::Fuzzy => lhs.fuzzy(rhs),
            RelOp::Eq => lhs == rhs,
            RelOp::Equiv => return Err(game_only_error("`≡`")),
            RelOp::Outcome(_) => return Err(game_only_error("outcome doubles")),
        })
    }

    fn mul_checked(lhs: &Self, rhs: &Self, span: Span) -> GrundyResult<Self> {
        lhs.nim_mul(rhs).ok_or_else(|| kummer_escape(span))
    }

    fn pow_checked(base: &Self, k: u128, span: Span) -> GrundyResult<Self> {
        base.nim_pow(k).ok_or_else(|| kummer_escape(span))
    }

    fn mv_mul(
        alg: &CliffordAlgebra<Self>,
        lhs: &Multivector<Self>,
        rhs: &Multivector<Self>,
        span: Span,
    ) -> GrundyResult<Multivector<Self>> {
        catch_unwind(AssertUnwindSafe(|| alg.mul(lhs, rhs))).map_err(|_| kummer_escape(span))
    }

    fn mv_pow(
        alg: &CliffordAlgebra<Self>,
        value: &Multivector<Self>,
        k: u128,
        span: Span,
    ) -> GrundyResult<Multivector<Self>> {
        catch_unwind(AssertUnwindSafe(|| alg.pow(value, k))).map_err(|_| kummer_escape(span))
    }
}

impl GrundyScalar for Surreal {
    fn bare_int(n: u128, _span: Span) -> GrundyResult<Self> {
        Ok(Surreal::from_int(u128_to_i128(n)?))
    }

    fn star(_lit: &StarLiteral, span: Span) -> GrundyResult<Self> {
        Err(GrundyError::new(
            GrundyErrorKind::WrongWorld,
            span,
            "star-literals are not Elements in the `surreal` world",
        )
        .with_hint("`*3` is a nimber literal"))
    }

    fn omega(_span: Span) -> GrundyResult<Self> {
        Ok(Surreal::omega())
    }

    fn omega_pow(exp: Self, _span: Span) -> GrundyResult<Self> {
        Ok(Surreal::omega_pow(exp))
    }

    fn inv_scalar(value: &Self, span: Span) -> GrundyResult<Self> {
        if value.is_zero() {
            return Err(GrundyError::new(
                GrundyErrorKind::DivisionByZero,
                span,
                "division by zero",
            ));
        }
        value.inv().ok_or_else(|| {
            GrundyError::new(
                GrundyErrorKind::NotInvertible,
                span,
                "only CNF monomials invert exactly; 1/(ω+1) is an infinite Hahn series",
            )
        })
    }

    fn rem(lhs: &Self, rhs: &Self, span: Span) -> GrundyResult<Self> {
        if rhs.is_zero() {
            return Err(GrundyError::new(
                GrundyErrorKind::DivisionByZero,
                span,
                "division by zero",
            ));
        }
        lhs.rem(rhs).ok_or_else(|| modulus_error(span))
    }

    fn relation(op: RelOp, lhs: &Self, rhs: &Self, _span: Span) -> GrundyResult<bool> {
        ordered_relation(op, lhs.cmp(rhs))
    }

    fn integral(value: &Self, _span: Span) -> GrundyResult<bool> {
        Ok(HasRingOfIntegers::is_integral(value))
    }
}

impl GrundyScalar for Omnific {
    fn bare_int(n: u128, _span: Span) -> GrundyResult<Self> {
        Ok(Omnific::from_int(u128_to_i128(n)?))
    }

    fn star(_lit: &StarLiteral, span: Span) -> GrundyResult<Self> {
        Err(GrundyError::new(
            GrundyErrorKind::WrongWorld,
            span,
            "star-literals are not Elements in the `omnific` world",
        )
        .with_hint("`*3` is a nimber literal"))
    }

    fn omega(_span: Span) -> GrundyResult<Self> {
        Ok(Omnific::omega())
    }

    fn omega_pow(exp: Self, span: Span) -> GrundyResult<Self> {
        Omnific::from_surreal(Surreal::omega_pow(exp.inner().clone())).ok_or_else(|| {
            GrundyError::new(
                GrundyErrorKind::Domain,
                span,
                "omega-power exponent does not produce an omnific integer",
            )
        })
    }

    fn rem(lhs: &Self, rhs: &Self, span: Span) -> GrundyResult<Self> {
        if rhs.is_zero() {
            return Err(GrundyError::new(
                GrundyErrorKind::DivisionByZero,
                span,
                "division by zero",
            ));
        }
        lhs.rem(rhs).ok_or_else(|| modulus_error(span))
    }

    fn relation(op: RelOp, lhs: &Self, rhs: &Self, _span: Span) -> GrundyResult<bool> {
        ordered_relation(op, lhs.cmp(rhs))
    }

    fn integral(_value: &Self, _span: Span) -> GrundyResult<bool> {
        Ok(true)
    }
}

impl GrundyScalar for Integer {
    fn bare_int(n: u128, _span: Span) -> GrundyResult<Self> {
        Ok(Integer(u128_to_i128(n)?))
    }

    fn star(_lit: &StarLiteral, span: Span) -> GrundyResult<Self> {
        Err(GrundyError::new(
            GrundyErrorKind::WrongWorld,
            span,
            "star-literals are not Elements in the `integer` world",
        )
        .with_hint("`*3` is a nimber literal"))
    }

    fn omega(span: Span) -> GrundyResult<Self> {
        Err(GrundyError::new(
            GrundyErrorKind::WrongWorld,
            span,
            "`ω` belongs to the surreal-family worlds",
        ))
    }

    fn exact_div(lhs: &Self, rhs: &Self, span: Span) -> Option<GrundyResult<Self>> {
        Some(match lhs.div_exact(rhs) {
            Ok(q) => Ok(q),
            Err(IntegerDivExactError::DivisionByZero) => Err(GrundyError::new(
                GrundyErrorKind::DivisionByZero,
                span,
                "division by zero",
            )),
            Err(IntegerDivExactError::Remainder(r)) => Err(GrundyError::new(
                GrundyErrorKind::NotInvertible,
                span,
                format!("integer exact division failed with remainder {r}"),
            )),
        })
    }

    fn rem(lhs: &Self, rhs: &Self, span: Span) -> GrundyResult<Self> {
        lhs.rem(rhs).ok_or_else(|| {
            GrundyError::new(GrundyErrorKind::DivisionByZero, span, "division by zero")
        })
    }

    fn relation(op: RelOp, lhs: &Self, rhs: &Self, _span: Span) -> GrundyResult<bool> {
        ordered_relation(op, lhs.cmp(rhs))
    }

    fn integral(_value: &Self, _span: Span) -> GrundyResult<bool> {
        Ok(true)
    }
}

macro_rules! impl_fp_grundy {
    ($($p:literal),* $(,)?) => {
        $(
            impl GrundyScalar for Fp<$p> {
                fn bare_int(n: u128, _span: Span) -> GrundyResult<Self> {
                    Ok(Fp::<$p>::from_u128(n))
                }
                fn star(_lit: &StarLiteral, span: Span) -> GrundyResult<Self> {
                    Err(GrundyError::new(
                        GrundyErrorKind::WrongWorld,
                        span,
                        "star-literals are not Elements in prime-field worlds",
                    )
                    .with_hint("`*3` is a nimber literal"))
                }
                fn omega(span: Span) -> GrundyResult<Self> {
                    Err(GrundyError::new(
                        GrundyErrorKind::WrongWorld,
                        span,
                        "`ω` belongs to the surreal-family worlds",
                    ))
                }
                fn rem(_lhs: &Self, _rhs: &Self, span: Span) -> GrundyResult<Self> {
                    Err(GrundyError::new(
                        GrundyErrorKind::WrongWorld,
                        span,
                        "field worlds have no informative remainder operator",
                    ))
                }
                fn frob(value: &Self, _span: Span) -> GrundyResult<Self> {
                    Ok(*value)
                }
                fn trace(value: &Self, m: Option<i128>, span: Span) -> GrundyResult<Self> {
                    if m.is_some() {
                        return Err(GrundyError::new(
                            GrundyErrorKind::Arity,
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

macro_rules! impl_fpn_grundy {
    ($(($p:literal, $n:literal)),* $(,)?) => {
        $(
            impl GrundyScalar for Fpn<$p, $n> {
                fn bare_int(n: u128, _span: Span) -> GrundyResult<Self> {
                    Ok(Fpn::<$p, $n>::constant(n))
                }
                fn star(_lit: &StarLiteral, span: Span) -> GrundyResult<Self> {
                    Err(GrundyError::new(
                        GrundyErrorKind::WrongWorld,
                        span,
                        "star-literals are not Elements in extension-field worlds",
                    )
                    .with_hint("`*3` is a nimber literal"))
                }
                fn omega(span: Span) -> GrundyResult<Self> {
                    Err(GrundyError::new(
                        GrundyErrorKind::WrongWorld,
                        span,
                        "`ω` belongs to the surreal-family worlds",
                    ))
                }
                fn named_element(name: &str, _span: Span) -> GrundyResult<Option<Self>> {
                    Ok((name == "x").then(Fpn::<$p, $n>::generator))
                }
                fn reserved_ident(name: &str) -> bool {
                    name == "x"
                }
                fn rem(_lhs: &Self, _rhs: &Self, span: Span) -> GrundyResult<Self> {
                    Err(GrundyError::new(
                        GrundyErrorKind::WrongWorld,
                        span,
                        "field worlds have no informative remainder operator",
                    ))
                }
                fn frob(value: &Self, _span: Span) -> GrundyResult<Self> {
                    Ok(value.frobenius())
                }
                fn trace(value: &Self, m: Option<i128>, span: Span) -> GrundyResult<Self> {
                    if m.is_some() {
                        return Err(GrundyError::new(
                            GrundyErrorKind::Arity,
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

impl_fp_grundy!(2, 3, 5, 7);
impl_fpn_grundy!((2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (5, 2));

pub(crate) fn build_runtime<S: GrundyScalar>(
    name: &'static str,
    dim: usize,
    rest: &str,
) -> GrundyResult<CliffordRuntime<S>> {
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
            return Err(GrundyError::new(
                GrundyErrorKind::DimMismatch,
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
    Ok(CliffordRuntime::from_metric(name, metric))
}

pub(crate) fn parse_gold_metric(src: &str) -> GrundyResult<Metric<Nimber>> {
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
    Ok(ogdoad::forms::gold_form(m, a))
}

pub(crate) fn parse_scalar_list<S: GrundyScalar>(src: &str) -> GrundyResult<Vec<S>> {
    if src.trim().is_empty() {
        return Ok(Vec::new());
    }
    split_top_level(src, ',')
        .into_iter()
        .map(|part| parse_metric_scalar::<S>(&part))
        .collect()
}

pub(crate) fn parse_sparse_pairs<S: GrundyScalar>(
    src: &str,
) -> GrundyResult<BTreeMap<(usize, usize), S>> {
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

pub(crate) fn parse_metric_scalar<S: GrundyScalar>(src: &str) -> GrundyResult<S> {
    let mut rt = CliffordRuntime::<S>::from_metric("metric", Metric::diagonal(Vec::new()));
    ensure_source_nesting_depth(src)?;
    let stmt = parse_statement(src)?;
    ensure_statement_depth(&stmt)?;
    let Statement::Expr(expr) = stmt else {
        return Err(parse_error("metric scalar must be an expression"));
    };
    let value = rt.eval_expr(&expr)?;
    scalar_part(&value).ok_or_else(|| grade0_error(Span::point(0)))
}

pub(crate) fn extract_bracket(rest: &str, key: &str) -> GrundyResult<String> {
    extract_bracket_opt(rest, key)?.ok_or_else(|| parse_error(format!("missing `{key}=[...]`")))
}

pub(crate) fn extract_bracket_opt(rest: &str, key: &str) -> GrundyResult<Option<String>> {
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

pub(crate) fn split_top_level(src: &str, delim: char) -> Vec<String> {
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

pub(crate) fn scalar_part<S: Scalar>(value: &Multivector<S>) -> Option<S> {
    match value.terms() {
        terms if terms.is_empty() => Some(S::zero()),
        terms if terms.len() == 1 => terms.get(&0).cloned(),
        _ => None,
    }
}
