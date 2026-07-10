//! AST substitution, beta normalization, and free-name analysis.

use super::*;

pub(crate) fn value_to_expr<E: Display>(value: &Value<E>) -> OghamResult<Expr> {
    match value {
        Value::Element(value) => parse_display_expr(&value.to_string()),
        Value::Index(value) => Ok(index_literal_expr(*value)?),
        Value::Bool(value) => Ok(Expr::Bool(*value)),
        Value::Function(function) => Ok(function.to_expr()),
    }
}

pub(crate) fn contains_free_name(expr: &Expr, target: &str) -> bool {
    fn visit(expr: &Expr, target: &str, bound: &BTreeSet<String>) -> bool {
        match expr {
            Expr::Ident(name) => name == target && !bound.contains(name),
            Expr::Lambda { binders, body } => {
                let mut nested = bound.clone();
                nested.extend(binders.iter().map(|binder| binder.name.clone()));
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
            Expr::Container(items) => items.iter().any(|item| visit(item, target, bound)),
            Expr::Apply { callee, args } => {
                visit(callee, target, bound) || args.iter().any(|arg| visit(arg, target, bound))
            }
            Expr::GameForm { left, right } => left
                .iter()
                .chain(right)
                .any(|item| visit(item, target, bound)),
            Expr::Call { args, .. } => args.iter().any(|arg| visit(arg, target, bound)),
            Expr::Index(inner) => visit(inner, target, bound),
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
            Expr::Int(_)
            | Expr::Bool(_)
            | Expr::Star(_)
            | Expr::Omega
            | Expr::Blade(_)
            | Expr::Up
            | Expr::Down
            | Expr::Dim => false,
        }
    }

    visit(expr, target, &BTreeSet::new())
}

pub(crate) fn substitute_env<E: Display>(
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
            nested_bound.extend(binders.iter().map(|binder| binder.name.clone()));
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
        Expr::Container(items) => Ok(Expr::Container(
            items
                .iter()
                .map(|item| substitute_env(item, bound, env))
                .collect::<OghamResult<Vec<_>>>()?,
        )),
        Expr::Apply { callee, args } => Ok(Expr::Apply {
            callee: Box::new(substitute_env(callee, bound, env)?),
            args: args
                .iter()
                .map(|arg| substitute_env(arg, bound, env))
                .collect::<OghamResult<Vec<_>>>()?,
        }),
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
        Expr::Index(inner) => Ok(wrap_index_expr(substitute_env(inner, bound, env)?)),
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

pub(crate) fn substitute_names(expr: &Expr, replacements: &BTreeMap<String, Expr>) -> Expr {
    match expr {
        Expr::Ident(name) => replacements
            .get(name)
            .cloned()
            .unwrap_or_else(|| expr.clone()),
        Expr::Lambda { binders, body } => {
            let mut nested = replacements.clone();
            for binder in binders {
                nested.remove(&binder.name);
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
        Expr::Container(items) => Expr::Container(
            items
                .iter()
                .map(|item| substitute_names(item, replacements))
                .collect(),
        ),
        Expr::Apply { callee, args } => Expr::Apply {
            callee: Box::new(substitute_names(callee, replacements)),
            args: args
                .iter()
                .map(|arg| substitute_names(arg, replacements))
                .collect(),
        },
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
        Expr::Index(inner) => wrap_index_expr(substitute_names(inner, replacements)),
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

pub(crate) fn beta_normalize(expr: Expr) -> OghamResult<Expr> {
    match expr {
        Expr::Container(items) => Ok(Expr::Container(
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
        Expr::Index(inner) => Ok(wrap_index_expr(beta_normalize(*inner)?)),
        Expr::Unary { op, expr } => Ok(Expr::Unary {
            op,
            expr: Box::new(beta_normalize(*expr)?),
        }),
        Expr::Apply { callee, args } => {
            let callee = beta_normalize(*callee)?;
            let args = args
                .into_iter()
                .map(beta_normalize)
                .collect::<OghamResult<Vec<_>>>()?;
            if let Expr::Lambda {
                binders,
                body: lhs_body,
            } = callee
            {
                if let [Expr::Lambda {
                    binders: rhs_binders,
                    body: rhs_body,
                }] = args.as_slice()
                {
                    if binders.len() != 1 {
                        return Err(OghamError::new(
                            OghamErrorKind::Arity,
                            Span::point(0),
                            "function composition needs a unary head",
                        ));
                    }
                    let mut replacements = BTreeMap::new();
                    replacements.insert(binders[0].name.clone(), *rhs_body.clone());
                    return Ok(Expr::Lambda {
                        binders: rhs_binders.clone(),
                        body: Box::new(beta_normalize(substitute_names(&lhs_body, &replacements))?),
                    });
                }
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
                let replacements = binders
                    .into_iter()
                    .map(|binder| binder.name)
                    .zip(args)
                    .collect();
                return beta_normalize(substitute_names(&lhs_body, &replacements));
            }
            Ok(Expr::Apply {
                callee: Box::new(callee),
                args,
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
