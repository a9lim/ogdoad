use super::ast::{BinaryOp, Expr, RelOp, StarLiteral, Statement, UnaryOp};

pub fn unparse_statement(stmt: &Statement) -> String {
    match stmt {
        Statement::Binding { name, expr } => format!("{name} := {}", unparse_expr(expr)),
        Statement::Expr(expr) => unparse_expr(expr),
    }
}

pub fn unparse_expr(expr: &Expr) -> String {
    unparse_prec(expr, 0, false)
}

fn unparse_prec(expr: &Expr, parent: u8, rhs: bool) -> String {
    let prec = precedence(expr);
    let mut out = match expr {
        Expr::Int(n) => n.to_string(),
        Expr::Star(StarLiteral::Finite(n)) => format!("*{n}"),
        Expr::Star(StarLiteral::Cnf(cnf)) => cnf.to_string(),
        Expr::Omega => "ω".to_string(),
        Expr::Blade(i) => format!("e{i}"),
        Expr::Vector(items) => format!(
            "[{}]",
            items
                .iter()
                .map(unparse_expr)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Expr::Ident(name) => name.clone(),
        Expr::Call { name, args } => format!(
            "{name}({})",
            args.iter().map(unparse_expr).collect::<Vec<_>>().join(", ")
        ),
        Expr::Factorial(expr) => {
            if matches!(**expr, Expr::Int(_)) {
                format!("!{}", unparse_prec(expr, 8, false))
            } else {
                format!("!({})", unparse_expr(expr))
            }
        }
        Expr::Unary { op, expr } => {
            let sigil = match op {
                UnaryOp::Neg => "-",
                UnaryOp::Inv => "/",
            };
            format!("{sigil}{}", unparse_prec(expr, 6, false))
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
                unparse_prec(rhs, prec + 1, true)
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
                let lhs = unparse_prec(lhs, prec, false);
                let rhs = match &**rhs {
                    Expr::Int(_) => unparse_prec(rhs, prec, true),
                    Expr::Unary {
                        op: UnaryOp::Neg,
                        expr,
                    } if matches!(**expr, Expr::Int(_)) => {
                        format!("-{}", unparse_prec(expr, 8, true))
                    }
                    _ => format!("({})", unparse_expr(rhs)),
                };
                format!("{lhs}↑{rhs}")
            }
            BinaryOp::At => format!(
                "{}@{}",
                unparse_prec(lhs, prec, false),
                unparse_prec(rhs, prec, true)
            ),
        },
        Expr::Relation { op, lhs, rhs } => {
            let sigil = match op {
                RelOp::Eq => "=",
                RelOp::Lt => "<",
                RelOp::Gt => ">",
                RelOp::Fuzzy => "|",
            };
            format!(
                "{} {sigil} {}",
                unparse_prec(lhs, 1, false),
                unparse_prec(rhs, 1, true)
            )
        }
    };
    if prec < parent || (rhs && prec == parent && matches!(expr, Expr::Binary { .. })) {
        out = format!("({out})");
    }
    out
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

fn precedence(expr: &Expr) -> u8 {
    match expr {
        Expr::Relation { .. } => 1,
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub,
            ..
        } => 2,
        Expr::Binary {
            op: BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem,
            ..
        } => 3,
        Expr::Binary {
            op: BinaryOp::Wedge,
            ..
        } => 4,
        Expr::Unary { .. } => 5,
        Expr::Binary {
            op: BinaryOp::Pow, ..
        } => 6,
        Expr::Binary {
            op: BinaryOp::At, ..
        } => 7,
        _ => 8,
    }
}
