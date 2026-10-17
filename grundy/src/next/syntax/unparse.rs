//! Canonical source rendering with minimal parentheses.
//!
//! The law is `parse ∘ unparse = id` on parser-produced trees (modulo spans).

use super::ast::*;

/// Precedence levels, loosest first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Level {
    Expr,
    Cond,
    Or,
    And,
    Not,
    Rel,
    Concat,
    Range,
    Add,
    Mul,
    Wedge,
    Unary,
    Pow,
    Postfix,
    Atom,
}

/// Render a statement canonically.
pub fn unparse_stmt(stmt: &Stmt) -> String {
    match stmt {
        Stmt::Data(decl) => unparse_data(decl),
        Stmt::Seq(bindings, expr) => {
            let mut parts: Vec<String> = bindings.iter().map(unparse_binding).collect();
            if let Some(expr) = expr {
                parts.push(unparse_expr(expr));
            }
            parts.join("; ")
        }
    }
}

/// Render a data declaration.
pub fn unparse_data(decl: &DataDecl) -> String {
    let ctors = decl
        .ctors
        .iter()
        .map(|ctor| {
            if ctor.fields.is_empty() {
                ctor.name.clone()
            } else {
                format!(
                    "{}({})",
                    ctor.name,
                    ctor.fields
                        .iter()
                        .map(unparse_type)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        })
        .collect::<Vec<_>>()
        .join(" | ");
    format!("data {} = {ctors}", decl.name)
}

/// Render one binding.
pub fn unparse_binding(binding: &Binding) -> String {
    let op = match binding.kind {
        BindKind::Let => ":=",
        BindKind::Rec => "=:",
    };
    format!(
        "{} {op} {}",
        unparse_pat(&binding.pat),
        unparse_expr(&binding.expr)
    )
}

/// Render an expression canonically.
pub fn unparse_expr(expr: &Expr) -> String {
    render(expr, Level::Expr)
}

fn level_of(expr: &Expr) -> Level {
    match &expr.kind {
        ExprKind::Lambda(..) | ExprKind::Annot(..) => Level::Expr,
        ExprKind::If(..) | ExprKind::Match(..) => Level::Cond,
        ExprKind::Binary(BinaryOp::Or, ..) => Level::Or,
        ExprKind::Binary(BinaryOp::And, ..) => Level::And,
        ExprKind::Unary(UnaryOp::Not, _) => Level::Not,
        ExprKind::Relation(..) => Level::Rel,
        ExprKind::Binary(BinaryOp::Concat, ..) => Level::Concat,
        ExprKind::Range { .. } => Level::Range,
        ExprKind::Binary(BinaryOp::Add | BinaryOp::Sub, ..) => Level::Add,
        ExprKind::Binary(BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem, ..)
        | ExprKind::Frac(..) => Level::Mul,
        ExprKind::Binary(BinaryOp::Wedge, ..) => Level::Wedge,
        ExprKind::Unary(..) => Level::Unary,
        ExprKind::Binary(BinaryOp::Pow, ..) => Level::Pow,
        ExprKind::Call(..) | ExprKind::Index(..) => Level::Postfix,
        _ => Level::Atom,
    }
}

fn render(expr: &Expr, min: Level) -> String {
    let text = render_bare(expr);
    if level_of(expr) < min {
        format!("({text})")
    } else {
        text
    }
}

fn render_bare(expr: &Expr) -> String {
    match &expr.kind {
        ExprKind::Int(n) => n.to_string(),
        ExprKind::Frac(num, den) => format!("{num}/{den}"),
        ExprKind::Star(index) => unparse_star(index),
        ExprKind::Omega => "ω".to_string(),
        ExprKind::Bool(b) => b.to_string(),
        ExprKind::Up => "up".to_string(),
        ExprKind::Down => "down".to_string(),
        ExprKind::Var(name) | ExprKind::Con(name) => name.clone(),
        ExprKind::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(unparse_expr)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ExprKind::List(items) => format!("[{}]", render_items(items)),
        ExprKind::Comprehension(head, clauses) => {
            let mut text = format!("[{}", render(head, Level::Or));
            for clause in clauses {
                match clause {
                    Clause::For(pat, source) => {
                        text.push_str(&format!(
                            " for {} in {}",
                            unparse_pat(pat),
                            render(source, Level::Or)
                        ));
                    }
                    Clause::If(guard) => {
                        text.push_str(&format!(" if {}", render(guard, Level::Or)));
                    }
                }
            }
            text.push(']');
            text
        }
        ExprKind::Range { lo, hi, inclusive } => format!(
            "{}{}{}",
            render(lo, Level::Add),
            if *inclusive { "..=" } else { ".." },
            render(hi, Level::Add)
        ),
        ExprKind::Form { left, right } => {
            let left = render_items(left);
            let right = render_items(right);
            match (left.is_empty(), right.is_empty()) {
                (true, true) => "{|}".to_string(),
                (false, true) => format!("{{{left} |}}"),
                (true, false) => format!("{{| {right}}}"),
                (false, false) => format!("{{{left} | {right}}}"),
            }
        }
        ExprKind::Call(callee, args) => format!(
            "{}({})",
            render(callee, Level::Postfix),
            args.iter().map(unparse_expr).collect::<Vec<_>>().join(", ")
        ),
        ExprKind::Index(base, index) => {
            format!("{}[{}]", render(base, Level::Postfix), unparse_expr(index))
        }
        ExprKind::Lambda(params, body) => {
            let params = match params.as_slice() {
                [Param { pat, ty: None }]
                    if matches!(pat.kind, PatKind::Var(_) | PatKind::Wild) =>
                {
                    unparse_pat(pat)
                }
                _ => format!(
                    "({})",
                    params
                        .iter()
                        .map(|param| match &param.ty {
                            Some(ty) =>
                                format!("{} : {}", unparse_pat(&param.pat), unparse_type(ty)),
                            None => unparse_pat(&param.pat),
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            };
            format!("{params} ↦ {}", render(body, Level::Expr))
        }
        ExprKind::Annot(inner, ty) => {
            format!("{} : {}", render(inner, Level::Or), unparse_type(ty))
        }
        ExprKind::Unary(op, inner) => match op {
            UnaryOp::Not => format!("not {}", render(inner, Level::Not)),
            UnaryOp::Neg => format!("-{}", render(inner, Level::Unary)),
            UnaryOp::Recip => {
                let rendered = render(inner, Level::Unary);
                if rendered.starts_with('*') || rendered.starts_with('/') {
                    format!("/({rendered})")
                } else {
                    format!("/{rendered}")
                }
            }
        },
        ExprKind::Binary(op, lhs, rhs) => render_binary(*op, lhs, rhs),
        ExprKind::Relation(op, lhs, rhs) => format!(
            "{} {} {}",
            render(lhs, Level::Concat),
            relop_text(*op),
            render(rhs, Level::Concat)
        ),
        ExprKind::If(cond, then_branch, else_branch) => format!(
            "if {} then {} else {}",
            render(cond, Level::Expr),
            render(then_branch, Level::Expr),
            render(else_branch, Level::Expr)
        ),
        ExprKind::Match(scrutinee, arms) => format!(
            "match {} {{ {} }}",
            render(scrutinee, Level::Or),
            arms.iter()
                .map(|(pat, body)| format!("{} ↦ {}", unparse_pat(pat), render(body, Level::Expr)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ExprKind::Block(bindings, body) => {
            let mut parts: Vec<String> = bindings.iter().map(unparse_binding).collect();
            parts.push(unparse_expr(body));
            format!("({})", parts.join("; "))
        }
    }
}

fn render_items(items: &[Item]) -> String {
    items
        .iter()
        .map(|item| match item {
            Item::One(expr) => unparse_expr(expr),
            Item::Splice(expr) => format!("..{}", render(expr, Level::Or)),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// Whether an operand is literal-shaped (`7` or `-7`), so that `/` between two
/// such operands would re-parse as a fraction literal.
fn is_literal_int(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Int(_) => true,
        ExprKind::Unary(UnaryOp::Neg, inner) => matches!(inner.kind, ExprKind::Int(_)),
        _ => false,
    }
}

fn render_binary(op: BinaryOp, lhs: &Expr, rhs: &Expr) -> String {
    match op {
        BinaryOp::Or | BinaryOp::And => {
            let level = if op == BinaryOp::Or {
                Level::Or
            } else {
                Level::And
            };
            let word = if op == BinaryOp::Or { "or" } else { "and" };
            format!("{} {word} {}", render(lhs, level), render(rhs, next(level)))
        }
        BinaryOp::Concat => format!(
            "{} ⧺ {}",
            render(lhs, Level::Range),
            render(rhs, Level::Concat)
        ),
        BinaryOp::Add | BinaryOp::Sub => format!(
            "{} {} {}",
            render(lhs, Level::Add),
            if op == BinaryOp::Add { "+" } else { "-" },
            render(rhs, Level::Mul)
        ),
        BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem => {
            let lhs_text = render(lhs, Level::Mul);
            let mut rhs_text = render(rhs, Level::Wedge);
            let glyph = match op {
                BinaryOp::Mul => "⋅",
                BinaryOp::Div => "/",
                _ => "%",
            };
            if op == BinaryOp::Div
                && ((is_literal_int(lhs) && is_literal_int(rhs))
                    || rhs_text.starts_with('*')
                    || rhs_text.starts_with('/'))
                && !rhs_text.starts_with('(')
            {
                rhs_text = format!("({rhs_text})");
            }
            format!("{lhs_text}{glyph}{rhs_text}")
        }
        BinaryOp::Wedge => format!(
            "{}∧{}",
            render(lhs, Level::Wedge),
            render(rhs, Level::Unary)
        ),
        BinaryOp::Pow => format!(
            "{}↑{}",
            render(lhs, Level::Postfix),
            render(rhs, Level::Unary)
        ),
    }
}

fn next(level: Level) -> Level {
    match level {
        Level::Or => Level::And,
        Level::And => Level::Not,
        other => other,
    }
}

fn relop_text(op: RelOp) -> String {
    match op {
        RelOp::Eq => "=".to_string(),
        RelOp::Lt => "<".to_string(),
        RelOp::Gt => ">".to_string(),
        RelOp::Le => "≤".to_string(),
        RelOp::Ge => "≥".to_string(),
        RelOp::Fuzzy => "∥".to_string(),
        RelOp::Equiv => "≡".to_string(),
        RelOp::Outcome(cell) => cell.glyphs(),
    }
}

/// Render a star literal.
pub fn unparse_star(index: &StarIndex) -> String {
    match index {
        StarIndex::Finite(n) => format!("*{n}"),
        StarIndex::Omega => "*ω".to_string(),
        StarIndex::Cnf(terms) => format!("*({})", unparse_cnf(terms)),
    }
}

/// Render a structural CNF.
pub fn unparse_cnf(terms: &[CnfTerm]) -> String {
    terms
        .iter()
        .map(|term| match &term.exponent {
            None => term.coefficient.to_string(),
            Some(exponent) => {
                let base = match exponent {
                    CnfExponent::Finite(1) => "ω".to_string(),
                    CnfExponent::Finite(n) => format!("ω↑{n}"),
                    CnfExponent::Omega => "ω↑ω".to_string(),
                    CnfExponent::Cnf(inner) => format!("ω↑({})", unparse_cnf(inner)),
                };
                if term.coefficient == 1 {
                    base
                } else {
                    format!("{base}⋅{}", term.coefficient)
                }
            }
        })
        .collect::<Vec<_>>()
        .join(" + ")
}

/// Render a pattern.
pub fn unparse_pat(pat: &Pat) -> String {
    match &pat.kind {
        PatKind::Wild => "_".to_string(),
        PatKind::Var(name) => name.clone(),
        PatKind::Int(n) => n.to_string(),
        PatKind::Bool(b) => b.to_string(),
        PatKind::Tuple(items) => format!(
            "({})",
            items.iter().map(unparse_pat).collect::<Vec<_>>().join(", ")
        ),
        PatKind::Con(name, args) if args.is_empty() => name.clone(),
        PatKind::Con(name, args) => format!(
            "{name}({})",
            args.iter().map(unparse_pat).collect::<Vec<_>>().join(", ")
        ),
        PatKind::List(items, rest) => {
            let mut parts: Vec<String> = items.iter().map(unparse_pat).collect();
            if let Some(rest) = rest {
                parts.push(format!("..{}", unparse_pat(rest)));
            }
            format!("[{}]", parts.join(", "))
        }
        PatKind::Annot(inner, ty) => format!("({} : {})", unparse_pat(inner), unparse_type(ty)),
    }
}

/// Render a type expression.
pub fn unparse_type(ty: &TypeExpr) -> String {
    match &ty.kind {
        TypeKind::Named(name, args) if args.is_empty() => name.clone(),
        TypeKind::Named(name, args) => format!(
            "{name}({})",
            args.iter().map(unparse_type).collect::<Vec<_>>().join(", ")
        ),
        TypeKind::PolyRing(name) => format!("{name}[t]"),
        TypeKind::RatField(name) => format!("{name}(t)"),
        TypeKind::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(unparse_type)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        TypeKind::Fun(args, ret) => {
            let args_text = match args.as_slice() {
                [single] if !matches!(single.kind, TypeKind::Fun(..) | TypeKind::Tuple(_)) => {
                    unparse_type(single)
                }
                _ => format!(
                    "({})",
                    args.iter().map(unparse_type).collect::<Vec<_>>().join(", ")
                ),
            };
            format!("{args_text} → {}", unparse_type(ret))
        }
        TypeKind::Var(name) => name.clone(),
    }
}
