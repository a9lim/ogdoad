//! Shared Index evaluation and numeric helpers.

use super::*;

pub(crate) enum IndexPrimitive {
    NotHandled,
    Value(i128),
    Error(OghamError),
}

impl IndexPrimitive {
    pub(crate) fn from_result(result: OghamResult<i128>) -> Self {
        match result {
            Ok(value) => Self::Value(value),
            Err(err) => Self::Error(err),
        }
    }
}

pub(crate) fn eval_index<R: SharedRuntime>(runtime: &mut R, expr: &Expr) -> OghamResult<i128> {
    match runtime.index_primitive(expr) {
        IndexPrimitive::Value(value) => return Ok(value),
        IndexPrimitive::Error(err) => return Err(err),
        IndexPrimitive::NotHandled => {}
    }
    match expr {
        Expr::Index(expr) => eval_index(runtime, expr),
        Expr::Int(n) => u128_to_i128(*n),
        Expr::Bool(_) => Err(bool_sort_error()),
        Expr::Lambda { .. } => Err(fn_sort_error()),
        Expr::Block { bindings, body } => match runtime.eval_block(bindings, body)? {
            Value::Index(value) => Ok(value),
            Value::Element(_) => Err(index_sort_error()),
            Value::Bool(_) => Err(bool_sort_error()),
            Value::Function(_) => Err(fn_sort_error()),
        },
        Expr::Ident(name) => match runtime.env().get(name) {
            Some(Value::Index(value)) => Ok(*value),
            Some(Value::Element(_)) => Err(index_sort_error()),
            Some(Value::Bool(_)) => Err(bool_sort_error()),
            Some(Value::Function(_)) => Err(fn_sort_error()),
            None => Err(unbound_error(name)),
        },
        Expr::Unary {
            op: UnaryOp::Neg,
            expr,
        } => eval_index(runtime, expr)?
            .checked_neg()
            .ok_or_else(|| overflow("index negation overflowed i128")),
        Expr::Unary {
            op: UnaryOp::Inv, ..
        } => Err(index_sort_error()),
        Expr::Unary {
            op: UnaryOp::Not, ..
        } => Err(bool_sort_error()),
        Expr::Apply { .. } => match runtime.eval_value(expr)? {
            Value::Index(value) => Ok(value),
            Value::Element(_) => Err(index_sort_error()),
            Value::Bool(_) => Err(bool_sort_error()),
            Value::Function(_) => Err(fn_sort_error()),
        },
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            if runtime.eval_bool(cond)? {
                eval_index(runtime, then_expr)
            } else {
                eval_index(runtime, else_expr)
            }
        }
        Expr::Binary { op, lhs, rhs } => {
            let lhs = eval_index(runtime, lhs)?;
            let rhs = eval_index(runtime, rhs)?;
            eval_index_binary(*op, lhs, rhs)
        }
        Expr::Relation { .. } => Err(bool_sort_error()),
        Expr::Star(_)
        | Expr::Omega
        | Expr::Blade(_)
        | Expr::Container(_)
        | Expr::Up
        | Expr::Down
        | Expr::Dim
        | Expr::GameForm { .. }
        | Expr::Call { .. } => Err(index_sort_error()),
    }
}

pub(crate) fn parse_display_expr(src: &str) -> OghamResult<Expr> {
    match parse_statement(src)? {
        Statement::Expr(expr) => Ok(expr),
        Statement::Binding { .. } | Statement::Seq { .. } => {
            Err(parse_error("display did not round-trip as expression"))
        }
    }
}

pub(crate) fn index_literal_expr(value: i128) -> OghamResult<Expr> {
    let inner = if value >= 0 {
        Expr::Int(value as u128)
    } else {
        Expr::Unary {
            op: UnaryOp::Neg,
            expr: Box::new(Expr::Int(value.unsigned_abs())),
        }
    };
    Ok(Expr::Index(Box::new(inner)))
}

pub(crate) fn wrap_index_expr(inner: Expr) -> Expr {
    if matches!(inner, Expr::Index(_)) {
        inner
    } else {
        Expr::Index(Box::new(inner))
    }
}

pub(crate) fn display_index(value: i128) -> String {
    if value >= 0 {
        format!("#{value}")
    } else {
        format!("#({value})")
    }
}

pub(crate) fn value_sort<E>(value: &Value<E>) -> DataSort {
    match value {
        Value::Element(_) => DataSort::Element,
        Value::Index(_) => DataSort::Index,
        Value::Bool(_) => DataSort::Bool,
        Value::Function(_) => unreachable!("Function values are not first-order binder sorts"),
    }
}

pub(crate) fn env_sort<E>(value: &Value<E>) -> OghamResult<DataSort> {
    match value {
        Value::Element(_) => Ok(DataSort::Element),
        Value::Index(_) => Ok(DataSort::Index),
        Value::Bool(_) => Ok(DataSort::Bool),
        Value::Function(_) => Err(fn_sort_error()),
    }
}

pub(crate) fn ensure_value_sort<E>(value: &Value<E>, expected: DataSort) -> OghamResult<()> {
    match value {
        Value::Function(_) => Err(fn_sort_error()),
        _ if value_sort(value) == expected => Ok(()),
        Value::Bool(_) => Err(bool_sort_error()),
        _ if expected == DataSort::Bool => Err(bool_sort_error()),
        _ => Err(index_sort_error()),
    }
}

pub(crate) fn eval_index_binary(op: BinaryOp, lhs: i128, rhs: i128) -> OghamResult<i128> {
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

pub(crate) fn expect_arity(name: &str, args: &[Expr], expected: usize) -> OghamResult<()> {
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

pub(crate) fn ordered_relation(op: RelOp, cmp: Ordering) -> OghamResult<bool> {
    Ok(match op {
        RelOp::Eq => cmp == Ordering::Equal,
        RelOp::Lt => cmp == Ordering::Less,
        RelOp::Gt => cmp == Ordering::Greater,
        RelOp::Fuzzy => false,
        RelOp::Equiv => return Err(game_only_error("`≡`")),
        RelOp::Outcome(_) => return Err(game_only_error("outcome doubles")),
    })
}

pub(crate) fn checked_i128_pow(base: i128, mut exp: u128) -> OghamResult<i128> {
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

pub(crate) fn u128_to_i128(n: u128) -> OghamResult<i128> {
    i128::try_from(n).map_err(|_| overflow("integer literal exceeds i128 in this world"))
}
