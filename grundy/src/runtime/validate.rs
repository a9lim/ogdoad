//! Definition-time sort, binder, and partiality validation.

use super::*;

#[derive(Clone, Copy)]
pub(crate) enum ExpectedSort {
    Any,
    Known(DataSort),
}

#[derive(Clone, Copy)]
enum StaticBindingSort {
    Data(DataSort),
    Function(DataSort),
}

pub(crate) fn check_binders(
    binders: &[String],
    is_world_shadow: impl Fn(&str) -> bool,
) -> GrundyResult<()> {
    let mut seen = BTreeSet::new();
    for binder in binders {
        if !seen.insert(binder.clone()) {
            return Err(GrundyError::new(
                GrundyErrorKind::Shadow,
                Span::point(0),
                format!("duplicate binder `{binder}`"),
            ));
        }
        if is_world_shadow(binder) {
            return Err(GrundyError::new(
                GrundyErrorKind::Shadow,
                Span::point(0),
                format!("binder `{binder}` shadows a reserved name"),
            ));
        }
    }
    Ok(())
}

/// Return sorts of the Functions visible to inference: environment Functions,
/// earlier lambdas of an enclosing sequence, and assumed μ-names.
pub(crate) type FnSorts = BTreeMap<String, DataSort>;

/// The order in which a μ-Function's own return sort is solved: Element
/// first, because an unforced sort is Element by rule (§6.1).
const RETURN_SORT_CANDIDATES: [DataSort; 3] = [DataSort::Element, DataSort::Index, DataSort::Bool];

pub(crate) fn infer_function_signature(
    body: &Expr,
    binders: &[LambdaBinder],
    fns: &FnSorts,
) -> GrundyResult<(Vec<DataSort>, DataSort)> {
    let mut slots = binders
        .iter()
        .map(|binder| (binder.name.clone(), binder.declared_sort))
        .collect::<BTreeMap<String, Option<DataSort>>>();
    let ret = infer_expr_sort(body, ExpectedSort::Any, &mut slots, fns)?;
    let sorts = binders
        .iter()
        .map(|binder| {
            slots
                .get(&binder.name)
                .and_then(|sort| *sort)
                .unwrap_or(DataSort::Element)
        })
        .collect();
    Ok((sorts, ret))
}

/// A μ-Function's return sort solves `ret = sort(body)` with the μ-name in
/// scope at the assumed sort. The first self-consistent candidate wins.
pub(crate) fn infer_recursive_signature(
    body: &Expr,
    binders: &[LambdaBinder],
    mu_name: &str,
    fns: &FnSorts,
) -> GrundyResult<(Vec<DataSort>, DataSort)> {
    let mut first_error = None;
    for assumed in RETURN_SORT_CANDIDATES {
        let mut assumed_fns = fns.clone();
        assumed_fns.insert(mu_name.to_string(), assumed);
        match infer_function_signature(body, binders, &assumed_fns) {
            Ok((sorts, ret)) if ret == assumed => return Ok((sorts, ret)),
            Ok((_, ret)) => {
                first_error.get_or_insert_with(|| sort_mismatch(assumed, ret));
            }
            Err(err) => {
                first_error.get_or_insert(err);
            }
        }
    }
    Err(first_error.expect("at least one return sort candidate"))
}

pub(crate) fn infer_expr_sort(
    expr: &Expr,
    expected: ExpectedSort,
    binders: &mut BTreeMap<String, Option<DataSort>>,
    fns: &FnSorts,
) -> GrundyResult<DataSort> {
    match expr {
        Expr::Bool(_) => expect_sort(DataSort::Bool, expected),
        Expr::Int(_) | Expr::Star(_) | Expr::Omega | Expr::Blade(_) | Expr::Up | Expr::Down => {
            expect_sort(default_sort(expected), expected)
        }
        Expr::Dim => expect_sort(DataSort::Index, expected),
        Expr::Container(items) => {
            for item in items {
                infer_expr_sort(item, ExpectedSort::Known(DataSort::Element), binders, fns)?;
            }
            expect_sort(DataSort::Element, expected)
        }
        Expr::GameForm { left, right } => {
            for item in left.iter().chain(right) {
                infer_expr_sort(item, ExpectedSort::Known(DataSort::Element), binders, fns)?;
            }
            expect_sort(DataSort::Element, expected)
        }
        Expr::Block { bindings, body } => {
            let mut local_fns = fns.clone();
            for binding in bindings {
                let mu_name = binding.recursive.then_some(binding.name.as_str());
                match infer_block_binding_rhs(&binding.expr, binders, &local_fns, mu_name)? {
                    Some(ret) => local_fns.insert(binding.name.clone(), ret),
                    None => local_fns.remove(&binding.name),
                };
            }
            infer_expr_sort(body, expected, binders, &local_fns)
        }
        Expr::Lambda { .. } => Err(fn_sort_error()),
        Expr::Ident(name) => {
            if let Some(slot) = binders.get(name) {
                // A sort-neutral occurrence reads the binder's declared or
                // already-inferred sort; only an unresolved binder takes the
                // position's default.
                let sort = match (*slot, expected) {
                    (Some(sort), ExpectedSort::Any) => sort,
                    _ => default_sort(expected),
                };
                mark_binder_sort(binders, name, sort)?;
                Ok(sort)
            } else {
                expect_sort(default_sort(expected), expected)
            }
        }
        Expr::Call { name, args } => match name.as_str() {
            "nleft" | "nright" | "birthday" | "deg" => {
                expect_arity(name, args, 1)?;
                infer_expr_sort(
                    &args[0],
                    ExpectedSort::Known(DataSort::Element),
                    binders,
                    fns,
                )?;
                expect_sort(DataSort::Index, expected)
            }
            "left" | "right" | "coef" | "grade" => {
                expect_arity(name, args, 2)?;
                infer_expr_sort(
                    &args[0],
                    ExpectedSort::Known(DataSort::Element),
                    binders,
                    fns,
                )?;
                infer_expr_sort(&args[1], ExpectedSort::Known(DataSort::Index), binders, fns)?;
                expect_sort(DataSort::Element, expected)
            }
            "up" | "down" | "dim" => Err(literal_call_error(name)),
            "hasdraw" | "stopper" | "integral" => {
                expect_arity(name, args, 1)?;
                infer_expr_sort(
                    &args[0],
                    ExpectedSort::Known(DataSort::Element),
                    binders,
                    fns,
                )?;
                expect_sort(DataSort::Bool, expected)
            }
            "drawn" => Err(function_replacement_error("drawn", "hasdraw")),
            "outcome" | "winner" | "who" => Err(outcome_name_error(name)),
            "canon" | "rev" | "even" | "dual" | "frob" => {
                expect_arity(name, args, 1)?;
                infer_expr_sort(
                    &args[0],
                    ExpectedSort::Known(DataSort::Element),
                    binders,
                    fns,
                )?;
                expect_sort(DataSort::Element, expected)
            }
            "tr" => {
                if args.is_empty() || args.len() > 2 {
                    return Err(GrundyError::new(
                        GrundyErrorKind::Arity,
                        Span::point(0),
                        "`tr` expects one or two arguments",
                    ));
                }
                infer_expr_sort(
                    &args[0],
                    ExpectedSort::Known(DataSort::Element),
                    binders,
                    fns,
                )?;
                if args.len() == 2 {
                    infer_expr_sort(&args[1], ExpectedSort::Known(DataSort::Index), binders, fns)?;
                }
                expect_sort(DataSort::Element, expected)
            }
            "gcd" => {
                expect_arity(name, args, 2)?;
                infer_expr_sort(
                    &args[0],
                    ExpectedSort::Known(DataSort::Element),
                    binders,
                    fns,
                )?;
                infer_expr_sort(
                    &args[1],
                    ExpectedSort::Known(DataSort::Element),
                    binders,
                    fns,
                )?;
                expect_sort(DataSort::Element, expected)
            }
            _ => Err(GrundyError::new(
                GrundyErrorKind::UnknownFn,
                Span::point(0),
                format!("unknown function `{name}`"),
            )),
        },
        Expr::Apply { callee, .. } => match &**callee {
            Expr::Ident(name) if !binders.contains_key(name) => match fns.get(name) {
                Some(ret) => expect_sort(*ret, expected),
                None => expect_sort(default_sort(expected), expected),
            },
            _ => expect_sort(default_sort(expected), expected),
        },
        Expr::Index(inner) => {
            infer_expr_sort(inner, ExpectedSort::Known(DataSort::Index), binders, fns)?;
            expect_sort(DataSort::Index, expected)
        }
        Expr::Unary { op, expr } => match op {
            UnaryOp::Not => {
                infer_expr_sort(expr, ExpectedSort::Known(DataSort::Bool), binders, fns)?;
                expect_sort(DataSort::Bool, expected)
            }
            UnaryOp::Neg => {
                let sort = default_sort(expected);
                infer_expr_sort(expr, ExpectedSort::Known(sort), binders, fns)?;
                expect_sort(sort, expected)
            }
            UnaryOp::Inv => {
                infer_expr_sort(expr, ExpectedSort::Known(DataSort::Element), binders, fns)?;
                expect_sort(DataSort::Element, expected)
            }
        },
        Expr::Binary { op, lhs, rhs } => match op {
            BinaryOp::And | BinaryOp::Or => {
                infer_expr_sort(lhs, ExpectedSort::Known(DataSort::Bool), binders, fns)?;
                infer_expr_sort(rhs, ExpectedSort::Known(DataSort::Bool), binders, fns)?;
                expect_sort(DataSort::Bool, expected)
            }
            BinaryOp::Pow => {
                let sort = match expected {
                    ExpectedSort::Known(DataSort::Index) => DataSort::Index,
                    _ => DataSort::Element,
                };
                infer_expr_sort(lhs, ExpectedSort::Known(sort), binders, fns)?;
                infer_expr_sort(rhs, ExpectedSort::Known(DataSort::Index), binders, fns)?;
                expect_sort(sort, expected)
            }
            BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul => {
                let sort = default_sort(expected);
                infer_expr_sort(lhs, ExpectedSort::Known(sort), binders, fns)?;
                infer_expr_sort(rhs, ExpectedSort::Known(sort), binders, fns)?;
                expect_sort(sort, expected)
            }
            BinaryOp::Div | BinaryOp::Rem | BinaryOp::Wedge | BinaryOp::Append => {
                infer_expr_sort(lhs, ExpectedSort::Known(DataSort::Element), binders, fns)?;
                infer_expr_sort(rhs, ExpectedSort::Known(DataSort::Element), binders, fns)?;
                expect_sort(DataSort::Element, expected)
            }
        },
        Expr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            infer_expr_sort(cond, ExpectedSort::Known(DataSort::Bool), binders, fns)?;
            let branch_expected = expected;
            let then_sort = infer_expr_sort(then_expr, branch_expected, binders, fns)?;
            let else_sort =
                infer_expr_sort(else_expr, ExpectedSort::Known(then_sort), binders, fns)?;
            if then_sort != else_sort {
                return Err(sort_mismatch(then_sort, else_sort));
            }
            expect_sort(then_sort, expected)
        }
        Expr::Relation { op, lhs, rhs } => {
            let declared = |expr: &Expr| match expr {
                Expr::Ident(name) => binders.get(name).and_then(|sort| *sort),
                _ => None,
            };
            let lhs_declared = declared(lhs);
            let rhs_declared = declared(rhs);
            let sort = if *op == RelOp::Eq
                && matches!(
                    (lhs_declared, rhs_declared),
                    (Some(DataSort::Bool), _) | (_, Some(DataSort::Bool))
                ) {
                DataSort::Bool
            } else if *op != RelOp::Fuzzy
                && matches!(
                    (lhs_declared, rhs_declared),
                    (Some(DataSort::Index), _) | (_, Some(DataSort::Index))
                )
            {
                DataSort::Index
            } else {
                relation_operand_sort(*op, lhs, rhs)
            };
            infer_expr_sort(lhs, ExpectedSort::Known(sort), binders, fns)?;
            infer_expr_sort(rhs, ExpectedSort::Known(sort), binders, fns)?;
            expect_sort(DataSort::Bool, expected)
        }
    }
}

/// Infers a sequence binding's right-hand side. A lambda yields its return
/// sort, so later occurrences of its name apply at that sort.
pub(crate) fn infer_block_binding_rhs(
    rhs: &Expr,
    binders: &mut BTreeMap<String, Option<DataSort>>,
    fns: &FnSorts,
    mu_name: Option<&str>,
) -> GrundyResult<Option<DataSort>> {
    match rhs {
        Expr::Lambda {
            binders: local_binders,
            body,
        } => infer_nested_lambda_body(local_binders, body, binders, fns, mu_name).map(Some),
        _ => infer_expr_sort(rhs, ExpectedSort::Any, binders, fns).map(|_| None),
    }
}

pub(crate) fn infer_nested_lambda_body(
    local_binders: &[LambdaBinder],
    body: &Expr,
    binders: &mut BTreeMap<String, Option<DataSort>>,
    fns: &FnSorts,
    mu_name: Option<&str>,
) -> GrundyResult<DataSort> {
    let local = local_binders
        .iter()
        .map(|binder| binder.name.clone())
        .collect::<BTreeSet<_>>();
    let (nested, ret) = match mu_name {
        None => infer_nested_attempt(local_binders, body, binders, fns),
        Some(name) => {
            let mut first_error = None;
            let mut solved = None;
            for assumed in RETURN_SORT_CANDIDATES {
                let mut assumed_fns = fns.clone();
                assumed_fns.insert(name.to_string(), assumed);
                match infer_nested_attempt(local_binders, body, binders, &assumed_fns) {
                    Ok((nested, ret)) if ret == assumed => {
                        solved = Some((nested, ret));
                        break;
                    }
                    Ok((_, ret)) => {
                        first_error.get_or_insert_with(|| sort_mismatch(assumed, ret));
                    }
                    Err(err) => {
                        first_error.get_or_insert(err);
                    }
                }
            }
            solved.ok_or_else(|| first_error.expect("at least one return sort candidate"))
        }
    }?;
    for name in binders.keys().cloned().collect::<Vec<_>>() {
        if local.contains(&name) {
            continue;
        }
        if let Some(sort) = nested.get(&name).and_then(|sort| *sort) {
            mark_binder_sort(binders, &name, sort)?;
        }
    }
    Ok(ret)
}

type BinderSlots = BTreeMap<String, Option<DataSort>>;

fn infer_nested_attempt(
    local_binders: &[LambdaBinder],
    body: &Expr,
    binders: &BinderSlots,
    fns: &FnSorts,
) -> GrundyResult<(BinderSlots, DataSort)> {
    let mut nested = binders.clone();
    for binder in local_binders {
        nested.insert(binder.name.clone(), binder.declared_sort);
    }
    let ret = infer_expr_sort(body, ExpectedSort::Any, &mut nested, fns)?;
    Ok((nested, ret))
}

pub(crate) fn relation_operand_sort(op: RelOp, lhs: &Expr, rhs: &Expr) -> DataSort {
    if op == RelOp::Fuzzy {
        DataSort::Element
    } else if op == RelOp::Eq && (bool_shaped(lhs) || bool_shaped(rhs)) {
        DataSort::Bool
    } else if index_shaped(lhs) || index_shaped(rhs) {
        DataSort::Index
    } else {
        DataSort::Element
    }
}

pub(crate) fn default_sort(expected: ExpectedSort) -> DataSort {
    match expected {
        ExpectedSort::Known(sort) => sort,
        ExpectedSort::Any => DataSort::Element,
    }
}

pub(crate) fn expect_sort(actual: DataSort, expected: ExpectedSort) -> GrundyResult<DataSort> {
    match expected {
        ExpectedSort::Any => Ok(actual),
        ExpectedSort::Known(expected) if expected == actual => Ok(actual),
        ExpectedSort::Known(expected) => Err(sort_mismatch(expected, actual)),
    }
}

pub(crate) fn mark_binder_sort(
    binders: &mut BTreeMap<String, Option<DataSort>>,
    name: &str,
    sort: DataSort,
) -> GrundyResult<()> {
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
        Expr::Call { name, .. }
            if matches!(
                name.as_str(),
                "deg" | "dim" | "nleft" | "nright" | "birthday"
            ) =>
        {
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
        Expr::Call { name, .. } if matches!(name.as_str(), "hasdraw" | "stopper" | "integral") => {
            true
        }
        Expr::Block { body, .. } => bool_shaped(body),
        _ => false,
    }
}

pub(crate) fn static_sort<E>(
    expr: &Expr,
    env: &BTreeMap<String, Value<E>>,
    deg_is_index: bool,
) -> GrundyResult<DataSort> {
    let bindings = env
        .iter()
        .map(|(name, value)| {
            let sort = match value {
                Value::Element(_) => StaticBindingSort::Data(DataSort::Element),
                Value::Index(_) => StaticBindingSort::Data(DataSort::Index),
                Value::Bool(_) => StaticBindingSort::Data(DataSort::Bool),
                Value::Function(function) => StaticBindingSort::Function(function.ret),
            };
            (name.clone(), sort)
        })
        .collect();
    static_sort_with_bindings(expr, &bindings, deg_is_index)
}

fn static_sort_with_bindings(
    expr: &Expr,
    env: &BTreeMap<String, StaticBindingSort>,
    deg_is_index: bool,
) -> GrundyResult<DataSort> {
    match expr {
        Expr::Bool(_)
        | Expr::Relation { .. }
        | Expr::Unary {
            op: UnaryOp::Not, ..
        }
        | Expr::Binary {
            op: BinaryOp::And | BinaryOp::Or,
            ..
        } => Ok(DataSort::Bool),
        Expr::Index(_) | Expr::Dim => Ok(DataSort::Index),
        Expr::Lambda { .. } => Err(fn_sort_error()),
        Expr::Block { bindings, body } => {
            let mut local = env.clone();
            for binding in bindings {
                let sort = static_sort_with_bindings(&binding.expr, &local, deg_is_index)?;
                local.insert(binding.name.clone(), StaticBindingSort::Data(sort));
            }
            static_sort_with_bindings(body, &local, deg_is_index)
        }
        Expr::Ident(name) => match env.get(name) {
            Some(StaticBindingSort::Data(sort)) => Ok(*sort),
            Some(StaticBindingSort::Function(_)) => Err(fn_sort_error()),
            None => Ok(DataSort::Element),
        },
        Expr::Call { name, .. }
            if matches!(name.as_str(), "dim" | "nleft" | "nright" | "birthday")
                || (deg_is_index && name == "deg") =>
        {
            Ok(DataSort::Index)
        }
        Expr::Call { name, .. } if matches!(name.as_str(), "hasdraw" | "stopper" | "integral") => {
            Ok(DataSort::Bool)
        }
        Expr::Unary { expr, .. } => static_sort_with_bindings(expr, env, deg_is_index),
        Expr::Apply { callee, .. } => match &**callee {
            Expr::Ident(name) => match env.get(name) {
                Some(StaticBindingSort::Function(ret)) => Ok(*ret),
                _ => Ok(DataSort::Element),
            },
            _ => Ok(DataSort::Element),
        },
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Pow,
            lhs,
            rhs,
        } => {
            let lhs =
                static_sort_with_bindings(lhs, env, deg_is_index).unwrap_or(DataSort::Element);
            let rhs =
                static_sort_with_bindings(rhs, env, deg_is_index).unwrap_or(DataSort::Element);
            if lhs == DataSort::Bool || rhs == DataSort::Bool {
                Ok(DataSort::Bool)
            } else if lhs == DataSort::Index || rhs == DataSort::Index {
                Ok(DataSort::Index)
            } else {
                Ok(DataSort::Element)
            }
        }
        Expr::If {
            then_expr,
            else_expr,
            ..
        } => {
            let then_sort = static_sort_with_bindings(then_expr, env, deg_is_index)?;
            let else_sort = static_sort_with_bindings(else_expr, env, deg_is_index)?;
            if then_sort == else_sort {
                Ok(then_sort)
            } else {
                Err(sort_mismatch(then_sort, else_sort))
            }
        }
        _ => Ok(DataSort::Element),
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
            | "birthday"
            | "integral"
    )
}

pub(crate) fn ignore_static_partiality<E>(result: GrundyResult<Value<E>>) -> GrundyResult<()> {
    match result {
        Ok(_) => Ok(()),
        Err(err) if is_runtime_partiality(err.kind) => Ok(()),
        Err(err) => Err(err),
    }
}

pub(crate) fn is_runtime_partiality(kind: GrundyErrorKind) -> bool {
    matches!(
        kind,
        GrundyErrorKind::DivisionByZero
            | GrundyErrorKind::NotInvertible
            | GrundyErrorKind::Domain
            | GrundyErrorKind::Overflow
            | GrundyErrorKind::KummerEscape
            | GrundyErrorKind::Modulus
            | GrundyErrorKind::GraphBudget
    )
}

pub(crate) fn expression_is_index(expr: &Expr) -> bool {
    match expr {
        Expr::Index(_) | Expr::Dim => true,
        Expr::Call { name, .. }
            if matches!(
                name.as_str(),
                "deg" | "dim" | "nleft" | "nright" | "birthday"
            ) =>
        {
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
        Expr::Call { name, .. }
            if matches!(
                name.as_str(),
                "deg" | "dim" | "nleft" | "nright" | "birthday"
            ) =>
        {
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
