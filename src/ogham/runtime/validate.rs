//! Definition-time sort, binder, and partiality validation.

use super::*;

#[derive(Clone, Copy)]
pub(crate) enum ExpectedSort {
    Any,
    Known(Sort),
}

pub(crate) fn check_binders(
    binders: &[String],
    is_world_shadow: impl Fn(&str) -> bool,
) -> OghamResult<()> {
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

pub(crate) fn infer_function_signature(
    body: &Expr,
    binders: &[String],
) -> OghamResult<(Vec<Sort>, Sort)> {
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

pub(crate) fn infer_expr_sort(
    expr: &Expr,
    expected: ExpectedSort,
    binders: &mut BTreeMap<String, Option<Sort>>,
) -> OghamResult<Sort> {
    match expr {
        Expr::Bool(_) => expect_sort(Sort::Bool, expected),
        Expr::Int(_) | Expr::Star(_) | Expr::Omega | Expr::Blade(_) | Expr::Up | Expr::Down => {
            expect_sort(default_sort(expected), expected)
        }
        Expr::Dim => expect_sort(Sort::Index, expected),
        Expr::Container(items) => {
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
            "up" | "down" | "dim" => Err(literal_call_error(name)),
            "hasdraw" | "stopper" => {
                expect_arity(name, args, 1)?;
                infer_expr_sort(&args[0], ExpectedSort::Known(Sort::Element), binders)?;
                expect_sort(Sort::Bool, expected)
            }
            "drawn" => Err(renamed_function_error("drawn", "hasdraw")),
            "outcome" | "winner" | "who" => Err(outcome_name_error(name)),
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
        Expr::Index(inner) => {
            infer_expr_sort(inner, ExpectedSort::Known(Sort::Index), binders)?;
            expect_sort(Sort::Index, expected)
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

pub(crate) fn infer_block_binding_rhs(
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

pub(crate) fn infer_nested_lambda_body(
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

pub(crate) fn relation_operand_sort(op: RelOp, lhs: &Expr, rhs: &Expr) -> Sort {
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

pub(crate) fn default_sort(expected: ExpectedSort) -> Sort {
    match expected {
        ExpectedSort::Known(sort) => sort,
        ExpectedSort::Any => Sort::Element,
    }
}

pub(crate) fn expect_sort(actual: Sort, expected: ExpectedSort) -> OghamResult<Sort> {
    match expected {
        ExpectedSort::Any => Ok(actual),
        ExpectedSort::Known(expected) if expected == actual => Ok(actual),
        ExpectedSort::Known(expected) => Err(sort_mismatch(expected, actual)),
    }
}

pub(crate) fn mark_binder_sort(
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

pub(crate) fn index_shaped(expr: &Expr) -> bool {
    match expr {
        Expr::Index(_) | Expr::Dim => true,
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

pub(crate) fn bool_shaped(expr: &Expr) -> bool {
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
        Expr::Call { name, .. } if matches!(name.as_str(), "hasdraw" | "stopper") => true,
        Expr::Block { body, .. } => bool_shaped(body),
        _ => false,
    }
}

pub(crate) fn static_sort<E>(
    expr: &Expr,
    env: &BTreeMap<String, Value<E>>,
    deg_is_index: bool,
) -> OghamResult<Sort> {
    match expr {
        Expr::Bool(_) | Expr::Relation { .. } => Ok(Sort::Bool),
        Expr::Index(_) | Expr::Dim => Ok(Sort::Index),
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
        Expr::Call { name, .. } if matches!(name.as_str(), "hasdraw" | "stopper") => Ok(Sort::Bool),
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

pub(crate) fn static_sort_with_sorts(
    expr: &Expr,
    env: &BTreeMap<String, Sort>,
    deg_is_index: bool,
) -> OghamResult<Sort> {
    match expr {
        Expr::Bool(_) | Expr::Relation { .. } => Ok(Sort::Bool),
        Expr::Index(_) | Expr::Dim => Ok(Sort::Index),
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
        Expr::Call { name, .. } if matches!(name.as_str(), "hasdraw" | "stopper") => Ok(Sort::Bool),
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

pub(crate) fn reserved_function_binder(name: &str) -> bool {
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
            | "hasdraw"
            | "stopper"
    )
}

pub(crate) fn ignore_static_partiality<E>(result: OghamResult<Value<E>>) -> OghamResult<()> {
    match result {
        Ok(_) => Ok(()),
        Err(err) if is_runtime_partiality(err.kind) => Ok(()),
        Err(err) => Err(err),
    }
}

pub(crate) fn is_runtime_partiality(kind: OghamErrorKind) -> bool {
    matches!(
        kind,
        OghamErrorKind::DivisionByZero
            | OghamErrorKind::NotInvertible
            | OghamErrorKind::Domain
            | OghamErrorKind::Overflow
            | OghamErrorKind::KummerEscape
            | OghamErrorKind::Modulus
            | OghamErrorKind::GraphBudget
    )
}

pub(crate) fn expression_is_index(expr: &Expr) -> bool {
    match expr {
        Expr::Index(_) | Expr::Dim => true,
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

pub(crate) fn plain_index_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Int(_) | Expr::Index(_) | Expr::Dim => true,
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
