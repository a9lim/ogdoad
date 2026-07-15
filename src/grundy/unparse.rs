use super::ast::{
    BinaryOp, Binding, DataSort, Expr, LambdaBinder, RelOp, StarLiteral, Statement, UnaryOp,
};

pub fn unparse_statement(stmt: &Statement) -> String {
    match stmt {
        Statement::Binding {
            name,
            expr,
            recursive,
        } => format!(
            "{name} {} {}",
            binding_sigil(*recursive),
            unparse_expr(expr)
        ),
        Statement::Expr(expr) => unparse_expr(expr),
        Statement::Seq { bindings, tail } => {
            let mut parts = bindings.iter().map(unparse_binding).collect::<Vec<_>>();
            parts.push(unparse_statement(tail));
            parts.join("; ")
        }
    }
}

pub fn unparse_expr(expr: &Expr) -> String {
    unparse_prec(expr, 0, false)
}

fn unparse_prec(expr: &Expr, parent: u8, rhs: bool) -> String {
    let prec = precedence(expr);
    let mut out = match expr {
        Expr::Int(n) => n.to_string(),
        Expr::Index(expr) => match &**expr {
            Expr::Int(n) => format!("#{n}"),
            _ => format!("#({})", unparse_expr(expr)),
        },
        Expr::Bool(value) => value.to_string(),
        Expr::Star(StarLiteral::Finite(n)) => format!("*{n}"),
        Expr::Star(StarLiteral::Cnf(cnf)) => cnf.to_string(),
        Expr::Omega => "ω".to_string(),
        Expr::Blade(i) => format!("e{i}"),
        Expr::Up => "up".to_string(),
        Expr::Down => "down".to_string(),
        Expr::Dim => "dim".to_string(),
        Expr::Container(items) => format!(
            "[{}]",
            items
                .iter()
                .map(unparse_expr)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Expr::GameForm { left, right } => {
            let left = left.iter().map(unparse_expr).collect::<Vec<_>>().join(", ");
            let right = right
                .iter()
                .map(unparse_expr)
                .collect::<Vec<_>>()
                .join(", ");
            match (left.is_empty(), right.is_empty()) {
                (true, true) => "{|}".to_string(),
                (false, true) => format!("{{{left} |}}"),
                (true, false) => format!("{{| {right}}}"),
                (false, false) => format!("{{{left} | {right}}}"),
            }
        }
        Expr::Ident(name) => name.clone(),
        Expr::Lambda { binders, body } => {
            let binders = if binders.len() == 1 {
                unparse_lambda_binder(&binders[0])
            } else {
                format!(
                    "({})",
                    binders
                        .iter()
                        .map(unparse_lambda_binder)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            format!("{binders} ↦ {}", unparse_prec(body, prec, false))
        }
        Expr::Block { bindings, body } => {
            let mut parts = bindings.iter().map(unparse_binding).collect::<Vec<_>>();
            parts.push(unparse_expr(body));
            format!("({})", parts.join("; "))
        }
        Expr::Call { name, args } => format!(
            "{name}({})",
            args.iter()
                .enumerate()
                .map(|(index, expr)| unparse_call_arg(name, index, expr))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Expr::Apply { callee, args } => {
            let args = if args.len() == 1 {
                unparse_prec(&args[0], prec, true)
            } else {
                format!(
                    "({})",
                    args.iter().map(unparse_expr).collect::<Vec<_>>().join(", ")
                )
            };
            format!("{}@{args}", unparse_prec(callee, prec, false))
        }
        Expr::Unary { op, expr } => {
            let sigil = match op {
                UnaryOp::Neg => "-",
                UnaryOp::Inv => "/",
                UnaryOp::Not => "not ",
            };
            let parent = if matches!(op, UnaryOp::Not) { prec } else { 10 };
            let inner = unparse_prec(expr, parent, false);
            if matches!(op, UnaryOp::Inv) && (inner.starts_with('/') || inner.starts_with('*')) {
                format!("/({})", unparse_expr(expr))
            } else {
                format!("{sigil}{inner}")
            }
        }
        Expr::Binary { op, lhs, rhs } => match op {
            BinaryOp::Add => format!(
                "{} + {}",
                unparse_prec(lhs, prec, false),
                unparse_prec(rhs, prec, true)
            ),
            BinaryOp::Sub => format!(
                "{} - {}",
                unparse_prec(lhs, prec, false),
                unparse_prec(rhs, prec + 1, true)
            ),
            BinaryOp::Mul => format!(
                "{}⋅{}",
                unparse_prec(lhs, prec, false),
                unparse_prec(rhs, prec, true)
            ),
            BinaryOp::Div => format!(
                "{}/{}",
                unparse_prec(lhs, prec, false),
                unparse_divisor(rhs, prec + 1)
            ),
            BinaryOp::Rem => format!(
                "{}%{}",
                unparse_prec(lhs, prec, false),
                unparse_prec(rhs, prec + 1, true)
            ),
            BinaryOp::Wedge => format!(
                "{}{}{}",
                unparse_prec(lhs, prec, false),
                if is_blade_chain(lhs) && is_blade_chain(rhs) {
                    "∧"
                } else {
                    " ∧ "
                },
                unparse_prec(rhs, prec, true)
            ),
            BinaryOp::Pow => {
                let omega_base = lhs.is_omega_atom();
                let lhs = unparse_prec(lhs, prec, false);
                let rhs = match &**rhs {
                    // Base `ω` also accepts Scalar exponents, so an explicit
                    // Index mark is informative here rather than redundant.
                    Expr::Index(_) if omega_base => unparse_prec(rhs, prec, true),
                    Expr::Index(expr) => unparse_exponent(expr, prec),
                    expr => unparse_exponent(expr, prec),
                };
                format!("{lhs}↑{rhs}")
            }
            BinaryOp::And => format!(
                "{} and {}",
                unparse_prec(lhs, prec, false),
                unparse_prec(rhs, prec, true)
            ),
            BinaryOp::Or => format!(
                "{} or {}",
                unparse_prec(lhs, prec, false),
                unparse_prec(rhs, prec, true)
            ),
            BinaryOp::Append => format!(
                "{} ⧺ {}",
                unparse_prec(lhs, prec + 1, false),
                unparse_prec(rhs, prec, false)
            ),
        },
        Expr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            format!(
                "if {} then {} else {}",
                unparse_prec(cond, 0, false),
                unparse_prec(then_expr, 0, false),
                unparse_prec(else_expr, 0, false)
            )
        }
        Expr::Relation { op, lhs, rhs } => {
            let sigil = match op {
                RelOp::Eq => "=",
                RelOp::Lt => "<",
                RelOp::Gt => ">",
                RelOp::Fuzzy => "∥",
                RelOp::Equiv => "≡",
                RelOp::Outcome(cell) => cell.glyph(),
            };
            format!(
                "{} {sigil} {}",
                unparse_prec(lhs, prec, false),
                unparse_prec(rhs, prec, true)
            )
        }
    };
    if prec < parent
        || (rhs && prec == parent && matches!(expr, Expr::Binary { .. } | Expr::If { .. }))
    {
        out = format!("({out})");
    }
    out
}

fn unparse_lambda_binder(binder: &LambdaBinder) -> String {
    let mark = match binder.declared_sort {
        Some(DataSort::Index) => "#",
        Some(DataSort::Bool) => "?",
        Some(DataSort::Element) | None => "",
    };
    format!("{mark}{}", binder.name)
}

fn unparse_exponent(expr: &Expr, precedence: u8) -> String {
    match expr {
        Expr::Int(_) | Expr::Ident(_) => unparse_prec(expr, precedence, true),
        Expr::Unary {
            op: UnaryOp::Neg,
            expr,
        } if matches!(**expr, Expr::Int(_)) => {
            format!("-{}", unparse_prec(expr, 10, true))
        }
        _ => format!("({})", unparse_expr(expr)),
    }
}

fn unparse_divisor(expr: &Expr, precedence: u8) -> String {
    let rendered = unparse_prec(expr, precedence, true);
    if rendered.starts_with('/') || rendered.starts_with('*') {
        format!("({})", unparse_expr(expr))
    } else {
        rendered
    }
}

fn unparse_call_arg(name: &str, index: usize, expr: &Expr) -> String {
    if matches!(
        (name, index),
        ("grade" | "coef" | "left" | "right", 1) | ("tr", 1)
    ) {
        if let Expr::Index(inner) = expr {
            return unparse_expr(inner);
        }
    }
    unparse_expr(expr)
}

fn is_blade_chain(expr: &Expr) -> bool {
    match expr {
        Expr::Blade(_) => true,
        Expr::Binary {
            op: BinaryOp::Wedge,
            lhs,
            rhs,
        } => is_blade_chain(lhs) && is_blade_chain(rhs),
        _ => false,
    }
}

fn binding_sigil(recursive: bool) -> &'static str {
    if recursive {
        "=:"
    } else {
        ":="
    }
}

fn unparse_binding(binding: &Binding) -> String {
    format!(
        "{} {} {}",
        binding.name,
        binding_sigil(binding.recursive),
        unparse_expr(&binding.expr)
    )
}

fn precedence(expr: &Expr) -> u8 {
    match expr {
        Expr::Lambda { .. } => 0,
        Expr::Block { .. } => 13,
        Expr::If { .. } => 1,
        Expr::Binary {
            op: BinaryOp::Or, ..
        } => 2,
        Expr::Binary {
            op: BinaryOp::And, ..
        } => 3,
        Expr::Unary {
            op: UnaryOp::Not, ..
        } => 4,
        Expr::Relation { .. } => 5,
        Expr::Binary {
            op: BinaryOp::Append,
            ..
        } => 6,
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub,
            ..
        } => 7,
        Expr::Binary {
            op: BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem,
            ..
        } => 8,
        Expr::Binary {
            op: BinaryOp::Wedge,
            ..
        } => 9,
        Expr::Unary { .. } => 10,
        Expr::Binary {
            op: BinaryOp::Pow, ..
        } => 11,
        Expr::Apply { .. } => 12,
        _ => 13,
    }
}
