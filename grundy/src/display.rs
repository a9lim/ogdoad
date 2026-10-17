//! Canonical display: every value renders as a program that rebuilds it.
//!
//! Closures render as a sequence binding their captured free variables, then
//! the lambda; recursive groups render as their `=:` system. Claims render as
//! `verify(<witness>)`, so re-evaluating the text re-checks the evidence.

use std::collections::BTreeSet;

use ogdoad::games::{PlayConvention, StateVerdict};

use super::algebra::AlgebraV;
use super::core::CtorRef;
use super::eval::value::{Closure, GenericV, PolyBody, Value};
use super::games::claims::{BoundedV, QuotientV, Statement, WitnessV};
use super::games::form::{display_game_element_in_env, FormNames};
use super::games::rules::{RulesKind, RulesV};
use super::syntax::ast::*;
use super::syntax::unparse::unparse_expr;
use super::types::DataRegistry;

/// Display context: data declarations and the names in scope.
pub struct Show<'a> {
    /// Data declarations, for constructor names.
    pub data: &'a DataRegistry,
    /// Global names, so Form displays never capture a different binding.
    pub names: FormNames,
    /// Atoms the display may still write.
    pub budget: std::cell::Cell<u128>,
    /// Whether the display ran out of budget.
    pub exhausted: std::cell::Cell<bool>,
}

impl<'a> Show<'a> {
    /// A display context writing at most `budget` atoms.
    pub fn new(data: &'a DataRegistry, names: FormNames, budget: u128) -> Show<'a> {
        Show {
            data,
            names,
            budget: std::cell::Cell::new(budget),
            exhausted: std::cell::Cell::new(false),
        }
    }
}

impl Show<'_> {
    /// Render a value at statement level: a single game equation stays a
    /// bare `g =: …` statement.
    pub fn top(&self, value: &Value) -> String {
        match value {
            Value::Form(f) => display_game_element_in_env(&f.0, &self.names),
            other => self.value(other),
        }
    }
}

/// Display a value with no names in scope.
pub fn show_plain(value: &Value, data: &DataRegistry) -> String {
    Show::new(data, FormNames::new(), u128::MAX).value(value)
}

fn join<T>(items: impl IntoIterator<Item = T>, f: impl FnMut(T) -> String) -> String {
    items.into_iter().map(f).collect::<Vec<_>>().join(", ")
}

impl Show<'_> {
    /// Render a value.
    pub fn value(&self, value: &Value) -> String {
        if self.exhausted.get() {
            return String::new();
        }
        match self.budget.get().checked_sub(1) {
            Some(left) => self.budget.set(left),
            None => {
                self.exhausted.set(true);
                return String::new();
            }
        }
        match value {
            Value::Int(n) => n.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Tuple(items) => format!("({})", join(items.iter(), |v| self.value(v))),
            Value::List(items) => format!("[{}]", join(items.iter(), |v| self.value(v))),
            Value::Data(value) => {
                let name = ctor_name(&value.ctor, self.data);
                if value.fields.is_empty() {
                    name
                } else {
                    format!("{name}({})", join(&value.fields, |v| self.value(v)))
                }
            }
            Value::Winner(w) => ["Left", "Right", "Draw"][*w as usize].to_string(),
            Value::Option(None) => "None".to_string(),
            Value::Option(Some(inner)) => format!("Some({})", self.value(inner)),
            Value::Game(g) => {
                let mut budget = self.budget.get();
                let shown = g.display(&mut budget);
                self.budget.set(budget);
                shown.unwrap_or_else(|| {
                    self.exhausted.set(true);
                    String::new()
                })
            }
            Value::Form(f) => {
                let text = display_game_element_in_env(&f.0, &self.names);
                // A bare single equation is a statement; nested, it names its root.
                match text.split_once(" =: ") {
                    Some((root, _)) if !text.starts_with('(') => format!("({text}; {root})"),
                    _ => text,
                }
            }
            Value::Scalar(s) => s.to_string(),
            Value::Poly(p) => p.to_string(),
            Value::RatFunc(f) => f.to_string(),
            Value::Algebra(a) => self.algebra(a),
            Value::Mv(v) => match v.algebra() {
                Some(alg) if v.has_blades() => {
                    let basis = join(0..alg.dim(), |i| format!("e{i}"));
                    format!(
                        "(alg := {}; [{basis}] := basis(alg); {v})",
                        self.algebra(&alg)
                    )
                }
                _ => v.to_string(),
            },
            Value::Closure(closure) => self.closure(closure),
            Value::Generic(generic) => self.generic(generic),
            Value::Builtin(builtin, _) => builtin.name().to_string(),
            Value::CtorFn(ctor) => ctor_name(ctor, self.data),
            Value::Rules(rules) => self.rules(rules),
            Value::Witness(w) => self.witness(w),
            Value::Claim(c) => format!(
                "verify({}) /* claim: {} */",
                self.witness(&c.witness),
                self.statement(&c.statement)
            ),
            Value::Bounded(b) => self.bounded(b),
            Value::Quotient(q) => self.quotient(q),
        }
    }

    fn algebra(&self, alg: &AlgebraV) -> String {
        let (q, b, a) = alg.metric_values();
        let q = format!("[{}]", join(&q, |v| self.value(v)));
        if b.is_empty() && a.is_empty() {
            return format!("clifford({q})");
        }
        let pairs = |pairs: &[((usize, usize), Value)]| {
            format!(
                "[{}]",
                join(pairs, |((i, j), v)| format!(
                    "(({i}, {j}), {})",
                    self.value(v)
                ))
            )
        };
        format!("clifford_metric({q}, {}, {})", pairs(&b), pairs(&a))
    }

    fn rules(&self, rules: &RulesV) -> String {
        match &rules.kind {
            RulesKind::Impartial(f) => format!("impartial({})", self.value(f)),
            RulesKind::Partizan(l, r) => format!("partizan({}, {})", self.value(l), self.value(r)),
            RulesKind::Octal(code) => {
                format!("octal([{}])", join(code.digits(), |d| d.to_string()))
            }
        }
    }

    fn witness(&self, witness: &WitnessV) -> String {
        match witness {
            WitnessV::Outcome {
                left,
                right,
                convention,
                labels,
            } => {
                let adjacency = |rows: &[Vec<usize>]| {
                    format!(
                        "[{}]",
                        join(rows, |row| format!("[{}]", join(row, |n| n.to_string())))
                    )
                };
                let labels = join(labels, |label| {
                    let verdict = match label.verdict {
                        StateVerdict::Loss => 0,
                        StateVerdict::Win => 1,
                        StateVerdict::Draw => 2,
                    };
                    let chosen = label.chosen.map_or("-1".to_string(), |c| c.to_string());
                    format!("({verdict}, {}, {chosen})", label.rank)
                });
                format!(
                    "outcome_witness({}, {}, {}, [{labels}])",
                    adjacency(left),
                    adjacency(right),
                    *convention == PlayConvention::Misere
                )
            }
            WitnessV::Grundy { rules, root, table } => format!(
                "sg_witness({}, {}, [{}])",
                self.value(rules),
                self.value(root),
                join(table, |(p, g, r)| format!("({}, {g}, {r})", self.value(p)))
            ),
            WitnessV::Periodic {
                rules,
                preperiod,
                period,
            } => format!(
                "periodic_witness({}, {preperiod}, {period})",
                self.value(rules)
            ),
            WitnessV::Separation {
                rules,
                p,
                q,
                context,
            } => format!(
                "separation_witness({}, [{}], [{}], [{}])",
                self.value(rules),
                join(p, |v| self.value(v)),
                join(q, |v| self.value(v)),
                join(context, |v| self.value(v))
            ),
        }
    }

    fn statement(&self, statement: &Statement) -> String {
        match statement {
            Statement::Outcome(cell) => {
                let name = |m: Mover| match m {
                    Mover::Left => "Left",
                    Mover::Right => "Right",
                    Mover::Draw => "Draw",
                };
                format!(
                    "outcome ({}, {})",
                    name(cell.left_first),
                    name(cell.right_first)
                )
            }
            Statement::Grundy(g) => format!("sg = {g}"),
            Statement::Periodic { preperiod, period } => {
                format!("every heap from {preperiod} on repeats with period {period}")
            }
            Statement::Separated => "misère-distinguishable".to_string(),
        }
    }

    fn bounded(&self, bounded: &BoundedV) -> String {
        format!(
            "bounded({}, {})",
            self.value(&bounded.value),
            bounded.samples
        )
    }

    fn quotient(&self, q: &QuotientV) -> String {
        let classes = format!(
            "[{}]",
            join(&q.classes, |class| format!(
                "[{}]",
                join(class, |member| format!(
                    "[{}]",
                    join(member, |v| self.value(v))
                ))
            ))
        );
        let p = format!("[{}]", join(&q.p, |c| c.to_string()));
        let table = match &q.table {
            None => "None".to_string(),
            Some(rows) => format!(
                "Some([{}])",
                join(rows, |row| format!("[{}]", join(row, |c| c.to_string())))
            ),
        };
        format!("quotient({classes}, {p}, {table})")
    }

    fn closure(&self, closure: &Closure) -> String {
        match &closure.rec {
            None => {
                let lambda = &closure.lam.source;
                self.captured_block(
                    &[lambda],
                    &[],
                    &closure.env,
                    &closure.globals,
                    unparse_expr(lambda),
                )
            }
            Some((group, index)) => {
                let sources: Vec<&Expr> = group.lams.iter().map(|lam| &lam.source).collect();
                let equations = group
                    .names
                    .iter()
                    .zip(&sources)
                    .map(|(name, source)| format!("{name} =: {}", unparse_expr(source)))
                    .collect::<Vec<_>>()
                    .join("; ");
                let body = format!("{equations}; {}", group.names[*index]);
                self.captured_block(&sources, &group.names, &group.env, &group.globals, body)
            }
        }
    }

    fn generic(&self, generic: &GenericV) -> String {
        match &generic.body {
            PolyBody::Expr(super::core::Core::Lambda(lam)) => self.captured_block(
                &[&lam.source],
                &[],
                &generic.env,
                &generic.globals,
                unparse_expr(&lam.source),
            ),
            PolyBody::Expr(_) => "<generic>".to_string(),
            PolyBody::Group { names, lams, index } => {
                let sources: Vec<&Expr> = lams.iter().map(|lam| &lam.source).collect();
                let equations = names
                    .iter()
                    .zip(&sources)
                    .map(|(name, source)| format!("{name} =: {}", unparse_expr(source)))
                    .collect::<Vec<_>>()
                    .join("; ");
                self.captured_block(
                    &sources,
                    names,
                    &generic.env,
                    &generic.globals,
                    format!("{equations}; {}", names[*index]),
                )
            }
        }
    }

    fn captured_block(
        &self,
        sources: &[&Expr],
        bound: &[String],
        env: &super::eval::value::Env,
        globals: &super::eval::value::Globals,
        body: String,
    ) -> String {
        let mut free = BTreeSet::new();
        for source in sources {
            free_vars(source, &mut Vec::new(), &mut free);
        }
        for name in bound {
            free.remove(name);
        }
        let mut lets = Vec::new();
        for name in &free {
            if let Some(value) = env.get(name).or_else(|| globals.get(name)) {
                lets.push(format!("{name} := {}", self.value(value)));
            }
        }
        if lets.is_empty() && bound.is_empty() {
            return body;
        }
        lets.push(body);
        format!("({})", lets.join("; "))
    }
}

/// The surface name of a constructor.
pub fn ctor_name(ctor: &CtorRef, data: &DataRegistry) -> String {
    match ctor {
        CtorRef::Data(id, index) => data.get(*id).ctors[*index as usize].0.clone(),
        CtorRef::Winner(w) => ["Left", "Right", "Draw"][*w as usize].to_string(),
        CtorRef::Some => "Some".to_string(),
        CtorRef::None => "None".to_string(),
    }
}

/// Collect the free variables of an expression.
pub fn free_vars(expr: &Expr, bound: &mut Vec<String>, out: &mut BTreeSet<String>) {
    let with =
        |names: Vec<String>, bound: &mut Vec<String>, f: &mut dyn FnMut(&mut Vec<String>)| {
            let depth = bound.len();
            bound.extend(names);
            f(bound);
            bound.truncate(depth);
        };
    match &expr.kind {
        ExprKind::Var(name) => {
            if !bound.contains(name) {
                out.insert(name.clone());
            }
        }
        ExprKind::Int(_)
        | ExprKind::Frac(..)
        | ExprKind::Star(_)
        | ExprKind::Omega
        | ExprKind::Bool(_)
        | ExprKind::Up
        | ExprKind::Down
        | ExprKind::Con(_) => {}
        ExprKind::Tuple(items) => items.iter().for_each(|e| free_vars(e, bound, out)),
        ExprKind::List(items) => items.iter().for_each(|item| free_item(item, bound, out)),
        ExprKind::Form { left, right } => left
            .iter()
            .chain(right)
            .for_each(|item| free_item(item, bound, out)),
        ExprKind::Comprehension(head, clauses) => {
            let depth = bound.len();
            for clause in clauses {
                match clause {
                    Clause::For(pat, source) => {
                        free_vars(source, bound, out);
                        bound.extend(pat.binders().into_iter().map(String::from));
                    }
                    Clause::If(guard) => free_vars(guard, bound, out),
                }
            }
            free_vars(head, bound, out);
            bound.truncate(depth);
        }
        ExprKind::Range { lo, hi, .. } => {
            free_vars(lo, bound, out);
            free_vars(hi, bound, out);
        }
        ExprKind::Call(callee, args) => {
            free_vars(callee, bound, out);
            args.iter().for_each(|a| free_vars(a, bound, out));
        }
        ExprKind::Index(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Relation(_, a, b) => {
            free_vars(a, bound, out);
            free_vars(b, bound, out);
        }
        ExprKind::Lambda(params, body) => {
            let names = params
                .iter()
                .flat_map(|p| p.pat.binders().into_iter().map(String::from))
                .collect();
            with(names, bound, &mut |bound| free_vars(body, bound, out));
        }
        ExprKind::Unary(_, a) => free_vars(a, bound, out),
        ExprKind::If(c, a, b) => {
            free_vars(c, bound, out);
            free_vars(a, bound, out);
            free_vars(b, bound, out);
        }
        ExprKind::Match(scrutinee, arms) => {
            free_vars(scrutinee, bound, out);
            for (pat, body) in arms {
                let names = pat.binders().into_iter().map(String::from).collect();
                with(names, bound, &mut |bound| free_vars(body, bound, out));
            }
        }
        ExprKind::Block(bindings, body) => {
            let depth = bound.len();
            let mut index = 0;
            while index < bindings.len() {
                if bindings[index].kind == BindKind::Rec {
                    let mut end = index;
                    while end < bindings.len() && bindings[end].kind == BindKind::Rec {
                        bound.extend(bindings[end].pat.binders().into_iter().map(String::from));
                        end += 1;
                    }
                    for binding in &bindings[index..end] {
                        free_vars(&binding.expr, bound, out);
                    }
                    index = end;
                } else {
                    free_vars(&bindings[index].expr, bound, out);
                    bound.extend(bindings[index].pat.binders().into_iter().map(String::from));
                    index += 1;
                }
            }
            free_vars(body, bound, out);
            bound.truncate(depth);
        }
        ExprKind::Annot(inner, ty) => {
            let generator = match &ty.kind {
                TypeKind::PolyRing(_) | TypeKind::RatField(_) => Some("t"),
                TypeKind::Named(name, args)
                    if args.is_empty()
                        && matches!(name.as_str(), "F4" | "F8" | "F16" | "F9" | "F27" | "F25") =>
                {
                    Some("x")
                }
                _ => None,
            };
            match generator {
                Some(name) => with(vec![name.to_string()], bound, &mut |bound| {
                    free_vars(inner, bound, out)
                }),
                None => free_vars(inner, bound, out),
            }
        }
    }
}

fn free_item(item: &Item, bound: &mut Vec<String>, out: &mut BTreeSet<String>) {
    match item {
        Item::One(expr) | Item::Splice(expr) => free_vars(expr, bound, out),
    }
}
