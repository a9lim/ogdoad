//! The tree-walking evaluator over [`Core`].

use std::collections::BTreeSet;
use std::rc::Rc;

use ogdoad::games::Game;
use ogdoad::scalar::{Omnific, Rational, Surreal};

use super::super::algebra::scalar::{AddOp, DivOp, MulOp, RemOp, ScalarV, SubOp};
use super::super::core::{mentioned, visit_vars, CBind, CClause, CItem, CPat, Core, CtorRef, Lam};
use super::super::error::{err, GrundyError, GrundyErrorKind, GrundyResult, Span};
use super::super::games::form::{
    add_game_elements, build_game_form, form_outcome_cell, form_value_relation,
    game_element_regular_eq, materialize_regular_system, negate_game_element, FormV, SymbolicGame,
};
use super::super::games::game::{guard, GameV};
use super::super::syntax::ast::{BinaryOp, Mover, OutcomeCell, RelOp, StarIndex, UnaryOp};
use super::super::types::{DataRegistry, Ty, TyCon};
use super::builtins::call_builtin;
use super::value::*;

/// Default work budget: closure calls plus produced list elements.
pub const DEFAULT_FUEL: u128 = 1 << 22;
/// Default node budget for every graph materialization and exploration.
pub const DEFAULT_GRAPH_BUDGET: u128 = 1 << 16;
/// The host call-depth guard.
pub const DEPTH_LIMIT: usize = 4096;

/// The evaluator.
pub struct Interp<'a> {
    /// Data declarations.
    pub data: &'a DataRegistry,
    /// Remaining fuel for the current statement.
    pub fuel: u128,
    /// The statement's fuel budget (for messages).
    pub fuel_budget: u128,
    /// The node budget.
    pub graph_budget: u128,
    depth: usize,
}

impl super::super::games::game::Meter for Interp<'_> {
    fn remaining(&self) -> u128 {
        self.fuel
    }

    fn charge(&mut self, amount: u128) -> GrundyResult<()> {
        self.spend(amount)
    }
}

/// A place where evaluation is happening.
#[derive(Clone)]
pub struct Scope {
    /// Local bindings.
    pub env: Env,
    /// Captured globals.
    pub globals: Globals,
    /// The type instantiation.
    pub tenv: TEnv,
}

impl Scope {
    fn bind(&self, name: &str, value: Value) -> Scope {
        Scope {
            env: self.env.bind(name, value),
            globals: self.globals.clone(),
            tenv: self.tenv.clone(),
        }
    }

    fn lookup(&self, name: &str) -> Option<&Value> {
        self.env.get(name).or_else(|| self.globals.get(name))
    }
}

impl<'a> Interp<'a> {
    /// A fresh evaluator.
    pub fn new(data: &'a DataRegistry, fuel: u128, graph_budget: u128) -> Self {
        Interp {
            data,
            fuel,
            fuel_budget: fuel,
            graph_budget,
            depth: 0,
        }
    }

    /// Spend fuel.
    pub fn spend(&mut self, amount: u128) -> GrundyResult<()> {
        if self.fuel < amount {
            self.fuel = 0;
            return Err(err(
                GrundyErrorKind::Fuel,
                format!(
                    "the statement exhausted its work budget of {}",
                    self.fuel_budget
                ),
            )
            .with_hint("raise it with `:fuel n`; budgets are never a value"));
        }
        self.fuel -= amount;
        Ok(())
    }

    /// Resolve a type through the runtime instantiation.
    pub fn resolve(&self, ty: &Ty, tenv: &TEnv) -> Ty {
        match ty {
            Ty::Var(v) => match tenv.get(v) {
                Some(bound) => self.resolve(bound, tenv),
                None => Ty::Var(*v),
            },
            Ty::Con(con, args) => Ty::Con(
                *con,
                args.iter().map(|arg| self.resolve(arg, tenv)).collect(),
            ),
            Ty::Fun(args, ret) => Ty::Fun(
                args.iter().map(|arg| self.resolve(arg, tenv)).collect(),
                Box::new(self.resolve(ret, tenv)),
            ),
        }
    }

    // ------------------------------------------------------------- statements

    /// Execute one binding, returning the names it binds.
    pub fn exec_bind(&mut self, bind: &CBind, scope: &Scope) -> GrundyResult<Vec<(String, Value)>> {
        match bind {
            CBind::Let {
                pat,
                expr,
                tparams,
                span,
            } => {
                if !tparams.is_empty() {
                    let CPat::Var(name) = pat else {
                        unreachable!("only variables generalize")
                    };
                    return Ok(vec![(name.clone(), {
                        let (env, depth) = capture(scope, &mentioned(expr))?;
                        Value::Generic(Rc::new(GenericV {
                            tparams: tparams.clone(),
                            body: PolyBody::Expr(expr.clone()),
                            env,
                            globals: scope.globals.clone(),
                            tenv: scope.tenv.clone(),
                            depth,
                        }))
                    })]);
                }
                let value = self.eval(expr, scope)?;
                let mut out = Vec::new();
                if !self.match_pat(pat, &value, &mut out) {
                    return Err(GrundyError::new(
                        GrundyErrorKind::Pattern,
                        *span,
                        "the binding pattern does not match the value",
                    ));
                }
                Ok(out)
            }
            CBind::RecFns {
                names,
                lams,
                tparams,
            } => {
                let (env, depth) = capture(scope, &group_mentions(names, lams))?;
                if !tparams.is_empty() {
                    return Ok(names
                        .iter()
                        .enumerate()
                        .map(|(index, name)| {
                            (
                                name.clone(),
                                Value::Generic(Rc::new(GenericV {
                                    tparams: tparams.clone(),
                                    body: PolyBody::Group {
                                        names: names.clone(),
                                        lams: lams.clone(),
                                        index,
                                    },
                                    env: env.clone(),
                                    globals: scope.globals.clone(),
                                    tenv: scope.tenv.clone(),
                                    depth,
                                })),
                            )
                        })
                        .collect());
                }
                let group = Rc::new(RecGroup {
                    names: names.clone(),
                    lams: lams.clone(),
                    env,
                    globals: scope.globals.clone(),
                    tenv: scope.tenv.clone(),
                    depth,
                });
                Ok(group_members(&group))
            }
            CBind::RecForms {
                names,
                exprs,
                spans,
            } => self.exec_forms(names, exprs, spans, scope),
        }
    }

    fn exec_forms(
        &mut self,
        names: &[String],
        exprs: &[Core],
        spans: &[Span],
        scope: &Scope,
    ) -> GrundyResult<Vec<(String, Value)>> {
        let system: BTreeSet<&str> = names.iter().map(String::as_str).collect();
        let mut roots = Vec::new();
        for (expr, span) in exprs.iter().zip(spans) {
            let root = self
                .reduce_form(expr, names, &system, scope)
                .map_err(|e| e.at(*span))?;
            if let SymbolicGame::SystemRef(target) = root {
                return Err(unfounded(&names[roots.len()], &names[target]).at(*span));
            }
            roots.push(root);
        }
        let values = materialize_regular_system(names, roots, self.graph_budget)?;
        Ok(names
            .iter()
            .cloned()
            .zip(values.into_iter().map(|v| Value::Form(FormV(v))))
            .collect())
    }

    /// Reduce a game equation's right-hand side with the system's names
    /// symbolic. System names are guarded only when they sit directly as
    /// brace options (possibly inside nested braces).
    fn reduce_form(
        &mut self,
        expr: &Core,
        names: &[String],
        system: &BTreeSet<&str>,
        scope: &Scope,
    ) -> GrundyResult<SymbolicGame> {
        match expr {
            Core::Var(name, _) if system.contains(name.as_str()) => {
                // A bare root reference is rejected by the caller; inside a
                // brace it is a guarded edge.
                let index = names.iter().position(|n| n == name).expect("system name");
                Ok(SymbolicGame::SystemRef(index))
            }
            Core::Form(left, right, _, _) => {
                let mut side = |items: &[CItem]| -> GrundyResult<Vec<SymbolicGame>> {
                    let mut out = Vec::new();
                    for item in items {
                        match item {
                            CItem::One(core) => {
                                out.push(self.reduce_form(core, names, system, scope)?)
                            }
                            CItem::Splice(core) => {
                                if mentions(core, system) {
                                    return Err(err(
                                        GrundyErrorKind::Unfounded,
                                        "a system name inside a splice is unguarded",
                                    )
                                    .with_hint("system names sit directly as brace options"));
                                }
                                for value in self.eval(core, scope)?.as_list().iter() {
                                    out.push(SymbolicGame::Value(as_form(value).0.clone()));
                                }
                            }
                        }
                    }
                    Ok(out)
                };
                let left = side(left)?;
                let right = side(right)?;
                Ok(SymbolicGame::Form { left, right })
            }
            other => {
                if mentions(other, system) {
                    return Err(err(
                        GrundyErrorKind::Unfounded,
                        "a system name is used outside a brace constructor",
                    )
                    .with_hint("guard it: `g =: {g |}`; other operators need the finished value"));
                }
                let value = self.eval(other, scope)?;
                Ok(SymbolicGame::Value(as_form(&value).0.clone()))
            }
        }
    }

    // ------------------------------------------------------------ expressions

    /// Evaluate an expression.
    pub fn eval(&mut self, core: &Core, scope: &Scope) -> GrundyResult<Value> {
        match core {
            Core::Int(n, ty) => {
                let ty = self.resolve(ty, &scope.tenv);
                self.int_literal(*n, &ty)
            }
            Core::Frac(num, den, ty) => {
                let ty = self.resolve(ty, &scope.tenv);
                self.frac_literal(*num, *den, &ty)
            }
            Core::Star(index, ty) => {
                let ty = self.resolve(ty, &scope.tenv);
                self.star_literal(index, &ty)
            }
            Core::Omega(ty) => match self.resolve(ty, &scope.tenv) {
                ty @ Ty::Con(TyCon::Mv, _) => super::super::algebra::omega_literal(&ty),
                Ty::Con(con, _) => Ok(Value::Scalar(ScalarV::omega(con)?)),
                other => Err(unresolved(&other)),
            },
            Core::Up(down, ty) => match self.resolve(ty, &scope.tenv) {
                Ty::Con(TyCon::Game, _) => Ok(Value::Game(GameV::up(*down, self)?)),
                Ty::Con(TyCon::Form, _) => {
                    let up = Game::up();
                    Ok(Value::Form(FormV::finite(if *down {
                        up.neg()
                    } else {
                        up
                    })))
                }
                other => Err(unresolved(&other)),
            },
            Core::Bool(b) => Ok(Value::Bool(*b)),
            Core::Var(name, span) => scope
                .lookup(name)
                .cloned()
                .ok_or_else(|| internal(format!("unbound `{name}` at runtime")).at(*span)),
            Core::Inst(name, tys, span) => {
                let value = scope
                    .lookup(name)
                    .cloned()
                    .ok_or_else(|| internal(format!("unbound `{name}` at runtime")).at(*span))?;
                match value {
                    Value::Generic(generic) => {
                        let tys: Vec<Ty> =
                            tys.iter().map(|ty| self.resolve(ty, &scope.tenv)).collect();
                        self.instantiate(&generic, &tys)
                    }
                    other => Ok(other),
                }
            }
            Core::Builtin(builtin, tys) => Ok(Value::Builtin(
                *builtin,
                tys.iter()
                    .map(|ty| self.resolve(ty, &scope.tenv))
                    .collect::<Vec<_>>()
                    .into(),
            )),
            Core::Ctor(ctor, arity) => Ok(if *arity == 0 {
                construct(ctor, Vec::new())?
            } else {
                Value::CtorFn(ctor.clone())
            }),
            Core::Tuple(items) => Ok(Value::tuple(
                items
                    .iter()
                    .map(|item| self.eval(item, scope))
                    .collect::<GrundyResult<_>>()?,
            )),
            Core::List(items) => Ok(Value::list(self.items(items, scope)?)),
            Core::Comp(head, clauses) => {
                let mut out = Vec::new();
                self.comprehension(head, clauses, scope, &mut out)?;
                Ok(Value::list(out))
            }
            Core::Range(lo, hi, inclusive, span) => {
                let lo = self.eval(lo, scope)?.as_int();
                let hi = self.eval(hi, scope)?.as_int();
                let end = if *inclusive {
                    hi.checked_add(1)
                } else {
                    Some(hi)
                }
                .ok_or_else(|| err(GrundyErrorKind::Overflow, "range bound overflows").at(*span))?;
                let len = end.saturating_sub(lo).max(0);
                self.spend(len as u128).map_err(|e| e.at(*span))?;
                Ok(Value::list((lo..end).map(Value::Int).collect()))
            }
            Core::Form(left, right, ty, span) => {
                let left = self.items(left, scope)?;
                let right = self.items(right, scope)?;
                match self.resolve(ty, &scope.tenv) {
                    Ty::Con(TyCon::Game, _) => {
                        let games =
                            |values: &[Value]| values.iter().map(as_game).collect::<Vec<_>>();
                        Ok(Value::Game(GameV::form(
                            &games(&left),
                            &games(&right),
                            self,
                        )?))
                    }
                    Ty::Con(TyCon::Form, _) => {
                        let forms = |values: Vec<Value>| {
                            values
                                .iter()
                                .map(|value| as_form(value).0.clone())
                                .collect()
                        };
                        Ok(Value::Form(FormV(
                            build_game_form(forms(left), forms(right), self.graph_budget)
                                .map_err(|e| e.at(*span))?,
                        )))
                    }
                    other => Err(unresolved(&other)),
                }
            }
            Core::Call(callee, args, span) => {
                let callee = self.eval(callee, scope)?;
                let args = args
                    .iter()
                    .map(|arg| self.eval(arg, scope))
                    .collect::<GrundyResult<Vec<_>>>()?;
                self.apply(&callee, args).map_err(|e| e.at(*span))
            }
            Core::Subst(callee, arg, span) => {
                let callee = self.eval(callee, scope)?;
                let arg = self.eval(arg, scope)?;
                // Horner's rule: one product per coefficient, and composition
                // grows the accumulator to the product of the sizes.
                let p = size_of(&callee).unwrap_or(1);
                let q = size_of(&arg).unwrap_or(1);
                self.spend(p.saturating_mul(p).saturating_mul(q).saturating_mul(q))?;
                super::super::algebra::substitute(&callee, &arg).map_err(|e| e.at(*span))
            }
            Core::Index(base, index, span) => {
                let base = self.eval(base, scope)?;
                let index = self.eval(index, scope)?.as_int();
                let items = base.as_list();
                usize::try_from(index)
                    .ok()
                    .and_then(|i| items.get(i))
                    .cloned()
                    .ok_or_else(|| {
                        GrundyError::new(
                            GrundyErrorKind::Domain,
                            *span,
                            format!("index {index} is outside a list of length {}", items.len()),
                        )
                    })
            }
            Core::Lambda(lam) => {
                let (env, depth) = capture(scope, &lam.mentions)?;
                Ok(Value::Closure(Rc::new(Closure {
                    lam: lam.clone(),
                    env,
                    globals: scope.globals.clone(),
                    tenv: scope.tenv.clone(),
                    rec: None,
                    depth,
                })))
            }
            Core::Unary(UnaryOp::Neg, inner, span) if matches!(**inner, Core::Int(n, _) if n == 1 << 127) =>
            {
                // `-2¹²⁷` is representable though `2¹²⁷` is not: read it as
                // `-(2¹²⁷ - 1) - 1`, so the least Int displays and re-reads.
                let Core::Int(n, ty) = &**inner else {
                    unreachable!("matched a literal")
                };
                let ty = self.resolve(ty, &scope.tenv);
                let magnitude = self.int_literal(n - 1, &ty)?;
                let negated = self.unary(UnaryOp::Neg, magnitude)?;
                let one = self.int_literal(1, &ty)?;
                self.binary(BinaryOp::Sub, negated, one)
                    .map_err(|e| e.at(*span))
            }
            Core::Unary(op, inner, span) => {
                let value = self.eval(inner, scope)?;
                self.unary(*op, value).map_err(|e| e.at(*span))
            }
            Core::Binary(op, lhs, rhs, span) => {
                let lhs = self.eval(lhs, scope)?;
                let rhs = self.eval(rhs, scope)?;
                self.binary(*op, lhs, rhs).map_err(|e| e.at(*span))
            }
            Core::Rel(op, lhs, rhs, span) => {
                let lhs = self.eval(lhs, scope)?;
                let rhs = self.eval(rhs, scope)?;
                self.relation(*op, &lhs, &rhs)
                    .map(Value::Bool)
                    .map_err(|e| e.at(*span))
            }
            Core::And(lhs, rhs) => {
                if self.eval(lhs, scope)?.as_bool() {
                    self.eval(rhs, scope)
                } else {
                    Ok(Value::Bool(false))
                }
            }
            Core::Or(lhs, rhs) => {
                if self.eval(lhs, scope)?.as_bool() {
                    Ok(Value::Bool(true))
                } else {
                    self.eval(rhs, scope)
                }
            }
            Core::If(cond, then_branch, else_branch) => {
                if self.eval(cond, scope)?.as_bool() {
                    self.eval(then_branch, scope)
                } else {
                    self.eval(else_branch, scope)
                }
            }
            Core::Match(scrutinee, arms, span) => {
                let value = self.eval(scrutinee, scope)?;
                for (pat, body) in arms {
                    let mut bound = Vec::new();
                    if self.match_pat(pat, &value, &mut bound) {
                        let mut inner = scope.clone();
                        for (name, value) in bound {
                            inner = inner.bind(&name, value);
                        }
                        return self.eval(body, &inner);
                    }
                }
                Err(GrundyError::new(
                    GrundyErrorKind::Pattern,
                    *span,
                    "no match arm matches the value",
                )
                .with_hint("add a final `_ ↦ …` arm"))
            }
            Core::Let(binds, body) => {
                let mut inner = scope.clone();
                for bind in binds {
                    for (name, value) in self.exec_bind(bind, &inner)? {
                        inner = inner.bind(&name, value);
                    }
                }
                self.eval(body, &inner)
            }
            Core::Gen(name, ty, body) => {
                let ty = self.resolve(ty, &scope.tenv);
                let generator = super::super::algebra::generator(&ty)?;
                self.eval(body, &scope.bind(name, generator))
            }
        }
    }

    fn items(&mut self, items: &[CItem], scope: &Scope) -> GrundyResult<Vec<Value>> {
        let mut out = Vec::new();
        for item in items {
            match item {
                CItem::One(core) => out.push(self.eval(core, scope)?),
                CItem::Splice(core) => {
                    let list = self.eval(core, scope)?;
                    out.extend(list.as_list().iter().cloned());
                }
            }
        }
        Ok(out)
    }

    fn comprehension(
        &mut self,
        head: &Core,
        clauses: &[CClause],
        scope: &Scope,
        out: &mut Vec<Value>,
    ) -> GrundyResult<()> {
        match clauses.split_first() {
            None => {
                self.spend(1)?;
                out.push(self.eval(head, scope)?);
                Ok(())
            }
            Some((CClause::If(guard), rest)) => {
                if self.eval(guard, scope)?.as_bool() {
                    self.comprehension(head, rest, scope, out)?;
                }
                Ok(())
            }
            Some((CClause::For(pat, source), rest)) => {
                let list = self.eval(source, scope)?;
                for item in list.as_list().iter() {
                    let mut bound = Vec::new();
                    if self.match_pat(pat, item, &mut bound) {
                        let mut inner = scope.clone();
                        for (name, value) in bound {
                            inner = inner.bind(&name, value);
                        }
                        self.comprehension(head, rest, &inner, out)?;
                    }
                }
                Ok(())
            }
        }
    }

    // ------------------------------------------------------------- functions

    /// Instantiate a generalized binding.
    pub fn instantiate(&mut self, generic: &GenericV, tys: &[Ty]) -> GrundyResult<Value> {
        let mut tenv = (*generic.tenv).clone();
        for (var, ty) in generic.tparams.iter().zip(tys) {
            tenv.insert(*var, ty.clone());
        }
        let tenv: TEnv = Rc::new(tenv);
        match &generic.body {
            PolyBody::Expr(core) => self.eval(
                core,
                &Scope {
                    env: generic.env.clone(),
                    globals: generic.globals.clone(),
                    tenv,
                },
            ),
            PolyBody::Group { names, lams, index } => {
                let group = Rc::new(RecGroup {
                    names: names.clone(),
                    lams: lams.clone(),
                    env: generic.env.clone(),
                    globals: generic.globals.clone(),
                    tenv,
                    depth: generic.depth,
                });
                Ok(group_members(&group).swap_remove(*index).1)
            }
        }
    }

    /// Apply a function value.
    pub fn apply(&mut self, callee: &Value, args: Vec<Value>) -> GrundyResult<Value> {
        match callee {
            Value::Closure(closure) => {
                self.spend(1)?;
                if self.depth >= DEPTH_LIMIT {
                    return Err(err(
                        GrundyErrorKind::StackDepth,
                        format!(
                            "call depth exceeds the host guard of {DEPTH_LIMIT} frames ({} fuel left)",
                            self.fuel
                        ),
                    )
                    .with_hint("depth is a host resource, not fuel"));
                }
                let mut env = closure.env.clone();
                if let Some((group, _)) = &closure.rec {
                    for (name, value) in group_members(group) {
                        env = env.bind(name, value);
                    }
                }
                let lam = &closure.lam;
                for (pat, arg) in lam.params.iter().zip(args) {
                    let mut bound = Vec::new();
                    if !self.match_pat(pat, &arg, &mut bound) {
                        return Err(err(
                            GrundyErrorKind::Pattern,
                            "the argument does not match the parameter pattern",
                        ));
                    }
                    for (name, value) in bound {
                        env = env.bind(name, value);
                    }
                }
                let scope = Scope {
                    env,
                    globals: closure.globals.clone(),
                    tenv: closure.tenv.clone(),
                };
                self.depth += 1;
                let result = self.eval(&lam.body, &scope);
                self.depth -= 1;
                result
            }
            Value::Builtin(builtin, tys) => call_builtin(self, *builtin, tys, args),
            Value::CtorFn(ctor) => construct(ctor, args),
            other => Err(internal(format!("applied a {}", other.kind_name()))),
        }
    }

    // ---------------------------------------------------------------- patterns

    /// Match a pattern, appending bindings. Returns whether it matched.
    pub fn match_pat(&self, pat: &CPat, value: &Value, out: &mut Vec<(String, Value)>) -> bool {
        match (pat, value) {
            (CPat::Wild, _) => true,
            (CPat::Var(name), _) => {
                out.push((name.clone(), value.clone()));
                true
            }
            (CPat::Int(n), Value::Int(m)) => n == m,
            (CPat::Bool(b), Value::Bool(c)) => b == c,
            (CPat::Tuple(items), Value::Tuple(values)) => {
                items.len() == values.len()
                    && items
                        .iter()
                        .zip(values.iter())
                        .all(|(item, value)| self.match_pat(item, value, out))
            }
            (CPat::List(items, rest), Value::List(values)) => {
                if values.len() < items.len() || (rest.is_none() && values.len() != items.len()) {
                    return false;
                }
                if !items
                    .iter()
                    .zip(values.iter())
                    .all(|(item, value)| self.match_pat(item, value, out))
                {
                    return false;
                }
                match rest {
                    Some(rest) => {
                        let tail = Value::list(values[items.len()..].to_vec());
                        self.match_pat(rest, &tail, out)
                    }
                    None => true,
                }
            }
            (CPat::Ctor(ctor, args), value) => match (ctor, value) {
                (CtorRef::Winner(w), Value::Winner(v)) => w == v,
                (CtorRef::None, Value::Option(None)) => true,
                (CtorRef::Some, Value::Option(Some(inner))) => self.match_pat(&args[0], inner, out),
                (CtorRef::Data(..), Value::Data(data)) => {
                    data.ctor == *ctor
                        && args
                            .iter()
                            .zip(&data.fields)
                            .all(|(arg, field)| self.match_pat(arg, field, out))
                }
                _ => false,
            },
            _ => false,
        }
    }

    // ---------------------------------------------------------------- literals

    fn int_literal(&mut self, n: u128, ty: &Ty) -> GrundyResult<Value> {
        if let Ty::Con(TyCon::Form, _) = ty {
            // The integer form n has n positions.
            guard(n)?;
            self.spend(n)?;
        }
        match ty {
            Ty::Con(TyCon::Int, _) => {
                Ok(Value::Int(i128::try_from(n).map_err(|_| {
                    err(GrundyErrorKind::Overflow, "literal exceeds i128")
                })?))
            }
            Ty::Con(TyCon::Game, _) => Ok(Value::Game(GameV::integer(to_i128(n)?, self)?)),
            Ty::Con(TyCon::Form, _) => Ok(Value::Form(FormV::finite(Game::integer(to_i128(n)?)))),
            Ty::Con(con, _) if ScalarV::zero(*con).is_some() => {
                Ok(Value::Scalar(ScalarV::int_literal(*con, n)?))
            }
            Ty::Con(..) => super::super::algebra::int_literal(ty, n),
            other => Err(unresolved(other)),
        }
    }

    fn frac_literal(&mut self, num: i128, den: u128, ty: &Ty) -> GrundyResult<Value> {
        if den == 0 {
            return Err(err(GrundyErrorKind::DivisionByZero, "zero denominator"));
        }
        match ty {
            Ty::Con(TyCon::Game, _) => Ok(Value::Game(GameV::dyadic(num, den, self)?)),
            Ty::Con(TyCon::Form, _) => {
                // Validate and size the dyadic as a Game, then present it.
                let birthday = GameV::dyadic(num, den, self)?.birthday();
                self.spend(birthday)?;
                let surreal = Surreal::from_rational(Rational::new(num, to_i128(den)?));
                Ok(Value::Form(FormV::finite(
                    Game::from_surreal(&surreal).expect("dyadic checked"),
                )))
            }
            Ty::Con(TyCon::Surreal, _) => Ok(Value::Scalar(ScalarV::Surreal(
                Surreal::from_rational(Rational::new(num, to_i128(den)?)),
            ))),
            Ty::Con(con, _) if ScalarV::zero(*con).is_some() => {
                let magnitude = ScalarV::int_literal(*con, num.unsigned_abs())?;
                let magnitude = if num < 0 { magnitude.neg() } else { magnitude };
                let denominator = ScalarV::int_literal(*con, den)?;
                Ok(Value::Scalar(magnitude.zip(&denominator, DivOp)?))
            }
            Ty::Con(..) => super::super::algebra::frac_literal(ty, num, den),
            other => Err(unresolved(other)),
        }
    }

    fn star_literal(&mut self, index: &StarIndex, ty: &Ty) -> GrundyResult<Value> {
        if let (Ty::Con(TyCon::Form, _), StarIndex::Finite(n)) = (ty, index) {
            // The nimber form *n has n(n+1)/2 option edges.
            guard(*n)?;
            self.spend(n.saturating_mul(n.saturating_add(1)) / 2)?;
        }
        let finite = || match index {
            StarIndex::Finite(n) => Ok(*n),
            _ => Err(err(
                GrundyErrorKind::Domain,
                "transfinite nimber games are outside the short games",
            )
            .with_hint("transfinite nimbers are Ordinal: `(*ω : Ordinal)`")),
        };
        match ty {
            Ty::Con(TyCon::Game, _) => Ok(Value::Game(GameV::nimber(finite()?, self)?)),
            Ty::Con(TyCon::Form, _) => Ok(Value::Form(FormV::finite(Game::nim_heap(finite()?)))),
            Ty::Con(con, _) if ScalarV::zero(*con).is_some() => {
                Ok(Value::Scalar(ScalarV::star_literal(*con, index)?))
            }
            Ty::Con(..) => super::super::algebra::star_literal(ty, index),
            other => Err(unresolved(other)),
        }
    }

    // --------------------------------------------------------------- operators

    fn unary(&mut self, op: UnaryOp, value: Value) -> GrundyResult<Value> {
        match (op, value) {
            (UnaryOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
            (UnaryOp::Neg, Value::Int(n)) => n
                .checked_neg()
                .map(Value::Int)
                .ok_or_else(|| err(GrundyErrorKind::Overflow, "negation overflows i128")),
            (UnaryOp::Neg, Value::Game(g)) => Ok(Value::Game(g.neg(self)?)),
            (UnaryOp::Neg, Value::Form(f)) => Ok(Value::Form(FormV(negate_game_element(
                f.0,
                self.graph_budget,
            )?))),
            (UnaryOp::Neg, Value::Scalar(s)) => Ok(Value::Scalar(s.neg())),
            (UnaryOp::Recip, Value::Scalar(s)) => Ok(Value::Scalar(s.inverse()?)),
            (op, value) => super::super::algebra::unary(op, &value),
        }
    }

    /// Apply an arithmetic or list operator.
    pub fn binary(&mut self, op: BinaryOp, lhs: Value, rhs: Value) -> GrundyResult<Value> {
        // Products of values that grow cost the product of their sizes, paid
        // before the work; their powers go through square-and-multiply so
        // every step pays.
        if let (Some(a), Some(b)) = (size_of(&lhs), size_of(&rhs)) {
            if matches!(
                op,
                BinaryOp::Mul | BinaryOp::Div | BinaryOp::Wedge | BinaryOp::Rem
            ) {
                self.spend(a.saturating_mul(b))?;
            }
        }
        if let (BinaryOp::Pow, Some(_), Value::Int(k)) = (op, size_of(&lhs), &rhs) {
            return self.power(lhs, *k);
        }
        let overflow = || {
            err(
                GrundyErrorKind::Overflow,
                "integer arithmetic overflows i128",
            )
        };
        match (op, &lhs, &rhs) {
            (BinaryOp::Concat, Value::List(a), Value::List(b)) => {
                self.spend((a.len() + b.len()) as u128)?;
                Ok(Value::list(a.iter().chain(b.iter()).cloned().collect()))
            }
            (BinaryOp::Add, Value::Int(a), Value::Int(b)) => {
                a.checked_add(*b).map(Value::Int).ok_or_else(overflow)
            }
            (BinaryOp::Sub, Value::Int(a), Value::Int(b)) => {
                a.checked_sub(*b).map(Value::Int).ok_or_else(overflow)
            }
            (BinaryOp::Mul, Value::Int(a), Value::Int(b)) => {
                a.checked_mul(*b).map(Value::Int).ok_or_else(overflow)
            }
            (BinaryOp::Rem, Value::Int(a), Value::Int(b)) => {
                if *b == 0 {
                    return Err(err(GrundyErrorKind::DivisionByZero, "remainder by zero"));
                }
                a.checked_rem_euclid(*b)
                    .map(Value::Int)
                    .ok_or_else(overflow)
            }
            (BinaryOp::Pow, Value::Int(a), Value::Int(k)) => {
                if *k < 0 {
                    return Err(err(
                        GrundyErrorKind::Domain,
                        "Int powers take a natural exponent",
                    )
                    .with_hint("negative powers leave the integers; use a field such as Surreal"));
                }
                match a {
                    0 => Ok(Value::Int(i128::from(*k == 0))),
                    1 => Ok(Value::Int(1)),
                    -1 => Ok(Value::Int(if k % 2 == 0 { 1 } else { -1 })),
                    // |a| ≥ 2 overflows i128 past the 127th power.
                    _ => u32::try_from(*k)
                        .ok()
                        .and_then(|k| a.checked_pow(k))
                        .map(Value::Int)
                        .ok_or_else(overflow),
                }
            }
            (BinaryOp::Add, Value::Game(a), Value::Game(b)) => Ok(Value::Game(a.add(b, self)?)),
            (BinaryOp::Sub, Value::Game(a), Value::Game(b)) => Ok(Value::Game(a.sub(b, self)?)),
            (BinaryOp::Add | BinaryOp::Sub, Value::Form(a), Value::Form(b)) => {
                Ok(Value::Form(FormV(add_game_elements(
                    a.0.clone(),
                    b.0.clone(),
                    op == BinaryOp::Sub,
                    self.graph_budget,
                )?)))
            }
            (BinaryOp::Add, Value::Scalar(a), Value::Scalar(b)) => {
                Ok(Value::Scalar(a.zip(b, AddOp)?))
            }
            (BinaryOp::Sub, Value::Scalar(a), Value::Scalar(b)) => {
                Ok(Value::Scalar(a.zip(b, SubOp)?))
            }
            (BinaryOp::Mul, Value::Scalar(a), Value::Scalar(b)) => {
                Ok(Value::Scalar(a.zip(b, MulOp)?))
            }
            (
                BinaryOp::Div,
                Value::Scalar(ScalarV::Omnific(a)),
                Value::Scalar(ScalarV::Omnific(b)),
            ) => self.omnific_divide(a, b),
            (BinaryOp::Div, Value::Scalar(a), Value::Scalar(b)) => {
                Ok(Value::Scalar(a.zip(b, DivOp)?))
            }
            (BinaryOp::Rem, Value::Scalar(a), Value::Scalar(b)) => {
                Ok(Value::Scalar(a.zip(b, RemOp)?))
            }
            (BinaryOp::Pow, Value::Scalar(a), Value::Int(k)) => Ok(Value::Scalar(a.power(*k)?)),
            (BinaryOp::Pow, Value::Scalar(a), Value::Scalar(e)) => {
                Ok(Value::Scalar(a.omega_pow(e)?))
            }
            _ => super::super::algebra::binary(op, &lhs, &rhs),
        }
    }

    /// Evaluate a relation.
    pub fn relation(&mut self, op: RelOp, lhs: &Value, rhs: &Value) -> GrundyResult<bool> {
        match (lhs, rhs) {
            (Value::Game(a), Value::Game(b)) => Ok(match op {
                RelOp::Eq => a.same(b),
                RelOp::Outcome(cell) => game_cell(a, b, self)? == cell,
                RelOp::Equiv => unreachable!("checker restricts `≡` to Form"),
                _ => order_relation(op, a.compare(b, self)?),
            }),
            (Value::Form(a), Value::Form(b)) => match op {
                RelOp::Equiv => Ok(game_element_regular_eq(&a.0, &b.0)),
                RelOp::Outcome(cell) => {
                    Ok(form_outcome_cell(&a.0, &b.0, self.graph_budget)? == cell)
                }
                _ => form_value_relation(op, &a.0, &b.0, self.graph_budget),
            },
            (Value::Int(a), Value::Int(b)) => Ok(order_relation(op, Some(a.cmp(b)))),
            (Value::Scalar(a), Value::Scalar(b)) => Ok(a.relation(op, b)),
            (Value::Poly(_) | Value::RatFunc(_) | Value::Mv(_), _) => {
                super::super::algebra::relation(op, lhs, rhs)
            }
            _ if op == RelOp::Eq => self.equal(lhs, rhs),
            _ => super::super::algebra::relation(op, lhs, rhs),
        }
    }

    /// `=` on containers is element-wise with each element's own `=`: Forms
    /// compare by value where the stopper theory licenses it, and
    /// multivectors only within one algebra.
    pub fn equal(&mut self, a: &Value, b: &Value) -> GrundyResult<bool> {
        let pairwise = |interp: &mut Self, xs: &[Value], ys: &[Value]| -> GrundyResult<bool> {
            if xs.len() != ys.len() {
                return Ok(false);
            }
            for (x, y) in xs.iter().zip(ys) {
                if !interp.equal(x, y)? {
                    return Ok(false);
                }
            }
            Ok(true)
        };
        match (a, b) {
            (Value::Tuple(x), Value::Tuple(y)) | (Value::List(x), Value::List(y)) => {
                pairwise(self, x, y)
            }
            (Value::Data(x), Value::Data(y)) => {
                Ok(x.ctor == y.ctor && pairwise(self, &x.fields, &y.fields)?)
            }
            (Value::Option(x), Value::Option(y)) => match (x, y) {
                (Some(x), Some(y)) => self.equal(x, y),
                (None, None) => Ok(true),
                _ => Ok(false),
            },
            (
                Value::Game(_)
                | Value::Form(_)
                | Value::Int(_)
                | Value::Scalar(_)
                | Value::Poly(_)
                | Value::RatFunc(_)
                | Value::Mv(_),
                _,
            ) => self.relation(RelOp::Eq, a, b),
            _ => Ok(values_equal(a, b)),
        }
    }
}

impl Interp<'_> {
    /// Exact omnific division, by long division on leading terms. An omnific
    /// quotient has no negative exponent and an integer constant term, so a
    /// step that needs a negative exponent, or a non-integral result, shows
    /// that no omnific quotient exists.
    fn omnific_divide(&mut self, a: &Omnific, b: &Omnific) -> GrundyResult<Value> {
        use ogdoad::scalar::Scalar as _;
        if b.is_zero() {
            return Err(err(GrundyErrorKind::DivisionByZero, "division by zero"));
        }
        let not_exact = || {
            err(
                GrundyErrorKind::NotInvertible,
                "the quotient is not an omnific integer",
            )
            .with_hint("omnific division is exact; its units are ±1")
        };
        let divisor = b.inner();
        let (lead_exp, lead_coef) = divisor.terms()[0].clone();
        let lead_inv = lead_coef.inv().expect("a leading coefficient is nonzero");
        let mut rem = a.inner().clone();
        let mut quot = Surreal::zero();
        while !rem.is_zero() {
            self.spend(divisor.terms().len() as u128)?;
            let (exp, coef) = rem.terms()[0].clone();
            let q_exp = exp.add(&lead_exp.neg());
            if q_exp.sign() == std::cmp::Ordering::Less {
                return Err(not_exact());
            }
            let term = Surreal::monomial(q_exp, coef.mul(&lead_inv));
            quot = quot.add(&term);
            rem = rem.add(&term.mul(divisor).neg());
        }
        Omnific::from_surreal(quot)
            .map(|q| Value::Scalar(ScalarV::Omnific(q)))
            .ok_or_else(not_exact)
    }

    /// `x ↑ k` by square-and-multiply; negative `k` inverts first.
    fn power(&mut self, base: Value, k: i128) -> GrundyResult<Value> {
        // A monomial's power is its coefficient's power, placed: the work is
        // the size of the result.
        let magnitude = k.unsigned_abs();
        match &base {
            Value::Poly(p) if k >= 0 => {
                if let Some(result) = p.monomial_power(magnitude, &mut |n| self.spend(n)) {
                    return Ok(Value::Poly(result?));
                }
            }
            Value::RatFunc(f) => {
                let inverted;
                let f = if k < 0 {
                    inverted = f.inverse()?;
                    &inverted
                } else {
                    f
                };
                if let Some(result) = f.monomial_power(magnitude, &mut |n| self.spend(n)) {
                    return Ok(Value::RatFunc(result?));
                }
            }
            _ => {}
        }
        let unit = one_like(&base)?;
        let mut base = if k < 0 {
            if let Value::Poly(_) = base {
                return Err(err(
                    GrundyErrorKind::NotInvertible,
                    "a negative power of a polynomial leaves the ring",
                )
                .with_hint("rational functions are `S(t)`"));
            }
            self.unary(UnaryOp::Recip, base)?
        } else {
            base
        };
        let mut k = k.unsigned_abs();
        let mut acc = unit;
        while k > 0 {
            if k & 1 == 1 {
                acc = self.binary(BinaryOp::Mul, acc, base.clone())?;
            }
            k >>= 1;
            if k > 0 {
                base = self.binary(BinaryOp::Mul, base.clone(), base)?;
            }
        }
        Ok(acc)
    }
}

/// The size of a value whose arithmetic cost grows with it.
fn size_of(value: &Value) -> Option<u128> {
    match value {
        Value::Scalar(s @ (ScalarV::Surreal(_) | ScalarV::Omnific(_))) => Some(s.size()),
        Value::Poly(p) => Some(p.size()),
        Value::RatFunc(f) => Some(f.size()),
        Value::Mv(v) => Some(v.size()),
        _ => None,
    }
}

/// The unit of a sized value's ring.
fn one_like(value: &Value) -> GrundyResult<Value> {
    Ok(match value {
        Value::Scalar(s) => Value::Scalar(s.power(0)?),
        Value::Poly(p) => Value::Poly(p.one_like()),
        Value::RatFunc(f) => Value::RatFunc(f.one_like()),
        Value::Mv(v) => Value::Mv(v.one_like()),
        other => return Err(internal(format!("no unit for a {}", other.kind_name()))),
    })
}

/// The outcome cell of `a - b` for short games: no draws.
pub fn game_cell(
    a: &GameV,
    b: &GameV,
    meter: &mut impl super::super::games::game::Meter,
) -> GrundyResult<OutcomeCell> {
    let (left_first, right_first) = match a.compare(b, meter)? {
        Some(std::cmp::Ordering::Greater) => (Mover::Left, Mover::Left),
        Some(std::cmp::Ordering::Less) => (Mover::Right, Mover::Right),
        Some(std::cmp::Ordering::Equal) => (Mover::Right, Mover::Left),
        None => (Mover::Left, Mover::Right),
    };
    Ok(OutcomeCell {
        left_first,
        right_first,
    })
}

fn order_relation(op: RelOp, ordering: Option<std::cmp::Ordering>) -> bool {
    use std::cmp::Ordering::*;
    match op {
        RelOp::Eq => ordering == Some(Equal),
        RelOp::Lt => ordering == Some(Less),
        RelOp::Gt => ordering == Some(Greater),
        RelOp::Le => matches!(ordering, Some(Less | Equal)),
        RelOp::Ge => matches!(ordering, Some(Greater | Equal)),
        RelOp::Fuzzy => ordering.is_none(),
        RelOp::Equiv | RelOp::Outcome(_) => false,
    }
}

/// The members of a recursive group, each a closure that rebuilds the group
/// on call (no reference cycles).
pub fn group_members(group: &Rc<RecGroup>) -> Vec<(String, Value)> {
    group
        .names
        .iter()
        .enumerate()
        .map(|(index, name)| {
            (
                name.clone(),
                Value::Closure(Rc::new(Closure {
                    lam: group.lams[index].clone(),
                    env: group.env.clone(),
                    globals: group.globals.clone(),
                    tenv: group.tenv.clone(),
                    rec: Some((group.clone(), index)),
                    depth: group.depth.saturating_add(1),
                })),
            )
        })
        .collect()
}

/// Build a constructor value.
pub fn construct(ctor: &CtorRef, mut args: Vec<Value>) -> GrundyResult<Value> {
    Ok(match ctor {
        CtorRef::Winner(w) => Value::Winner(*w),
        CtorRef::None => Value::Option(None),
        CtorRef::Some => Value::Option(Some(Rc::new(args.pop().expect("one field")))),
        CtorRef::Data(..) => {
            let depth = guard_depth(args.iter().map(Value::depth).max().unwrap_or(0))?;
            Value::Data(Rc::new(DataV {
                ctor: ctor.clone(),
                fields: args,
                depth,
            }))
        }
    })
}

/// One level above `depth`, refused past the host guard.
fn guard_depth(depth: u32) -> GrundyResult<u32> {
    let depth = depth.saturating_add(1);
    if depth > MAX_VALUE_DEPTH {
        return Err(err(
            GrundyErrorKind::StackDepth,
            format!("the value would nest {depth} levels deep, past the host guard of {MAX_VALUE_DEPTH}"),
        )
        .with_hint("value depth is a host resource, distinct from fuel"));
    }
    Ok(depth)
}

/// The bindings of `env` a function body mentions, and the depth of a
/// function capturing them. Capturing only these keeps closures from holding
/// unrelated values and makes the captured environment what display shows.
fn capture(scope: &Scope, names: &[String]) -> GrundyResult<(Env, u32)> {
    let mut captured = Env::new();
    let mut depth = 0;
    for name in names {
        if let Some(value) = scope.env.get(name) {
            depth = depth.max(value.depth());
            captured = captured.bind(name.clone(), value.clone());
        } else if let Some(value) = scope.globals.get(name) {
            // Globals are shared by snapshot, but a closure over one still
            // nests through it.
            depth = depth.max(value.depth());
        }
    }
    Ok((captured, guard_depth(depth)?))
}

/// What a recursive group's members mention, less the members themselves.
fn group_mentions(names: &[String], lams: &[Rc<Lam>]) -> Vec<String> {
    let mut all: BTreeSet<&str> = lams
        .iter()
        .flat_map(|lam| lam.mentions.iter().map(String::as_str))
        .collect();
    for name in names {
        all.remove(name.as_str());
    }
    all.into_iter().map(String::from).collect()
}

/// Read a Game value.
pub fn as_game(value: &Value) -> GameV {
    match value {
        Value::Game(g) => g.clone(),
        other => panic!("expected a Game, found {}", other.kind_name()),
    }
}

/// Read a Form value.
pub fn as_form(value: &Value) -> &FormV {
    match value {
        Value::Form(f) => f,
        other => panic!("expected a Form, found {}", other.kind_name()),
    }
}

/// Whether an expression mentions any of the names (conservatively,
/// ignoring shadowing).
pub fn mentions(core: &Core, names: &BTreeSet<&str>) -> bool {
    let mut found = false;
    visit_vars(core, &mut |name| found |= names.contains(name));
    found
}

fn unfounded(equation: &str, name: &str) -> GrundyError {
    err(
        GrundyErrorKind::Unfounded,
        format!("game equation `{equation}` is `{name}` itself, unguarded by a brace constructor"),
    )
    .with_hint("guard it: `g =: {g |}`")
}

fn unresolved(ty: &Ty) -> GrundyError {
    internal(format!("a literal's type is unresolved at runtime: {ty:?}"))
}

/// An invariant violation: a well-typed program reached an impossible state.
pub fn internal(message: impl Into<String>) -> GrundyError {
    err(
        GrundyErrorKind::Domain,
        format!("internal: {}", message.into()),
    )
}

fn to_i128(n: u128) -> GrundyResult<i128> {
    i128::try_from(n).map_err(|_| err(GrundyErrorKind::Overflow, "literal exceeds i128"))
}
