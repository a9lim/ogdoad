//! The tree-walking evaluator over [`Core`].

use std::collections::BTreeSet;
use std::rc::Rc;

use ogdoad::games::Game;
use ogdoad::scalar::{Rational, Surreal};

use super::super::algebra::scalar::{AddOp, DivOp, MulOp, RemOp, ScalarV, SubOp};
use super::super::core::{CBind, CClause, CItem, CPat, Core, CtorRef};
use super::super::error::{err, GrundyError, GrundyErrorKind, GrundyResult, Span};
use super::super::games::form::{
    add_game_elements, build_game_form, form_outcome_cell, form_value_relation,
    game_element_regular_eq, materialize_regular_system, negate_game_element, FormV, SymbolicGame,
};
use super::super::games::game::GameV;
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
                    return Ok(vec![(
                        name.clone(),
                        Value::Generic(Rc::new(GenericV {
                            tparams: tparams.clone(),
                            body: PolyBody::Expr(expr.clone()),
                            env: scope.env.clone(),
                            globals: scope.globals.clone(),
                            tenv: scope.tenv.clone(),
                        })),
                    )]);
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
                                    env: scope.env.clone(),
                                    globals: scope.globals.clone(),
                                    tenv: scope.tenv.clone(),
                                })),
                            )
                        })
                        .collect());
                }
                let group = Rc::new(RecGroup {
                    names: names.clone(),
                    lams: lams.clone(),
                    env: scope.env.clone(),
                    globals: scope.globals.clone(),
                    tenv: scope.tenv.clone(),
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
            Core::Int(n, ty) => self.int_literal(*n, &self.resolve(ty, &scope.tenv)),
            Core::Frac(num, den, ty) => {
                self.frac_literal(*num, *den, &self.resolve(ty, &scope.tenv))
            }
            Core::Star(index, ty) => self.star_literal(index, &self.resolve(ty, &scope.tenv)),
            Core::Omega(ty) => match self.resolve(ty, &scope.tenv) {
                Ty::Con(con, _) => Ok(Value::Scalar(ScalarV::omega(con)?)),
                other => Err(unresolved(&other)),
            },
            Core::Up(down, ty) => match self.resolve(ty, &scope.tenv) {
                Ty::Con(TyCon::Game, _) => Ok(Value::Game(GameV::up(*down))),
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
                construct(ctor, Vec::new())
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
                        Ok(Value::Game(GameV::form(&games(&left), &games(&right))))
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
            Core::Lambda(lam) => Ok(Value::Closure(Rc::new(Closure {
                lam: lam.clone(),
                env: scope.env.clone(),
                globals: scope.globals.clone(),
                tenv: scope.tenv.clone(),
                rec: None,
            }))),
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
            Value::CtorFn(ctor) => Ok(construct(ctor, args)),
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

    fn int_literal(&self, n: u128, ty: &Ty) -> GrundyResult<Value> {
        match ty {
            Ty::Con(TyCon::Int, _) => {
                Ok(Value::Int(i128::try_from(n).map_err(|_| {
                    err(GrundyErrorKind::Overflow, "literal exceeds i128")
                })?))
            }
            Ty::Con(TyCon::Game, _) => Ok(Value::Game(GameV::integer(to_i128(n)?))),
            Ty::Con(TyCon::Form, _) => Ok(Value::Form(FormV::finite(Game::integer(to_i128(n)?)))),
            Ty::Con(con, _) if ScalarV::zero(*con).is_some() => {
                Ok(Value::Scalar(ScalarV::int_literal(*con, n)?))
            }
            Ty::Con(..) => super::super::algebra::int_literal(ty, n),
            other => Err(unresolved(other)),
        }
    }

    fn frac_literal(&self, num: i128, den: u128, ty: &Ty) -> GrundyResult<Value> {
        if den == 0 {
            return Err(err(GrundyErrorKind::DivisionByZero, "zero denominator"));
        }
        match ty {
            Ty::Con(TyCon::Game, _) => Ok(Value::Game(GameV::dyadic(num, den)?)),
            Ty::Con(TyCon::Form, _) => {
                let game = GameV::dyadic(num, den)?;
                let den = to_i128(den)?;
                let surreal = Surreal::from_rational(Rational::new(num, den));
                let _ = game;
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

    fn star_literal(&self, index: &StarIndex, ty: &Ty) -> GrundyResult<Value> {
        let finite = || match index {
            StarIndex::Finite(n) => Ok(*n),
            _ => Err(err(
                GrundyErrorKind::Domain,
                "transfinite nimber games are outside the short games",
            )
            .with_hint("transfinite nimbers are Ordinal: `(*ω : Ordinal)`")),
        };
        match ty {
            Ty::Con(TyCon::Game, _) => Ok(Value::Game(GameV::nimber(finite()?))),
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
            (UnaryOp::Neg, Value::Game(g)) => Ok(Value::Game(g.neg())),
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
                let k = u32::try_from(*k).map_err(|_| {
                    err(
                        GrundyErrorKind::Domain,
                        "Int powers take a natural exponent below 2³²",
                    )
                })?;
                a.checked_pow(k).map(Value::Int).ok_or_else(overflow)
            }
            (BinaryOp::Add, Value::Game(a), Value::Game(b)) => Ok(Value::Game(a.add(b))),
            (BinaryOp::Sub, Value::Game(a), Value::Game(b)) => Ok(Value::Game(a.add(&b.neg()))),
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
                RelOp::Outcome(cell) => game_cell(a, b) == cell,
                RelOp::Equiv => unreachable!("checker restricts `≡` to Form"),
                _ => order_relation(op, a.compare(b)),
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
            _ if op == RelOp::Eq => Ok(values_equal(lhs, rhs)),
            _ => super::super::algebra::relation(op, lhs, rhs),
        }
    }
}

/// The outcome cell of `a - b` for short games: no draws.
pub fn game_cell(a: &GameV, b: &GameV) -> OutcomeCell {
    let (left_first, right_first) = match a.compare(b) {
        Some(std::cmp::Ordering::Greater) => (Mover::Left, Mover::Left),
        Some(std::cmp::Ordering::Less) => (Mover::Right, Mover::Right),
        Some(std::cmp::Ordering::Equal) => (Mover::Right, Mover::Left),
        None => (Mover::Left, Mover::Right),
    };
    OutcomeCell {
        left_first,
        right_first,
    }
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
                })),
            )
        })
        .collect()
}

/// Build a constructor value.
pub fn construct(ctor: &CtorRef, mut args: Vec<Value>) -> Value {
    match ctor {
        CtorRef::Winner(w) => Value::Winner(*w),
        CtorRef::None => Value::Option(None),
        CtorRef::Some => Value::Option(Some(Rc::new(args.pop().expect("one field")))),
        CtorRef::Data(..) => Value::Data(Rc::new(DataV {
            ctor: ctor.clone(),
            fields: args,
        })),
    }
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

/// Visit every variable reference in an expression.
pub fn visit_vars(core: &Core, f: &mut dyn FnMut(&str)) {
    let item = |item: &CItem, f: &mut dyn FnMut(&str)| match item {
        CItem::One(core) | CItem::Splice(core) => visit_vars(core, f),
    };
    match core {
        Core::Var(name, _) | Core::Inst(name, _, _) => f(name),
        Core::Int(..)
        | Core::Frac(..)
        | Core::Star(..)
        | Core::Omega(_)
        | Core::Up(..)
        | Core::Bool(_)
        | Core::Builtin(..)
        | Core::Ctor(..) => {}
        Core::Tuple(items) => items.iter().for_each(|i| visit_vars(i, f)),
        Core::List(items) => items.iter().for_each(|i| item(i, f)),
        Core::Comp(head, clauses) => {
            visit_vars(head, f);
            for clause in clauses {
                match clause {
                    CClause::For(_, source) => visit_vars(source, f),
                    CClause::If(guard) => visit_vars(guard, f),
                }
            }
        }
        Core::Range(a, b, ..)
        | Core::Subst(a, b, _)
        | Core::Index(a, b, _)
        | Core::Binary(_, a, b, _)
        | Core::Rel(_, a, b, _)
        | Core::And(a, b)
        | Core::Or(a, b) => {
            visit_vars(a, f);
            visit_vars(b, f);
        }
        Core::Form(left, right, ..) => {
            left.iter().chain(right).for_each(|i| item(i, f));
        }
        Core::Call(callee, args, _) => {
            visit_vars(callee, f);
            args.iter().for_each(|a| visit_vars(a, f));
        }
        Core::Lambda(lam) => visit_vars(&lam.body, f),
        Core::Unary(_, a, _) => visit_vars(a, f),
        Core::If(c, a, b) => {
            visit_vars(c, f);
            visit_vars(a, f);
            visit_vars(b, f);
        }
        Core::Match(scrutinee, arms, _) => {
            visit_vars(scrutinee, f);
            arms.iter().for_each(|(_, body)| visit_vars(body, f));
        }
        Core::Let(binds, body) => {
            for bind in binds {
                match bind {
                    CBind::Let { expr, .. } => visit_vars(expr, f),
                    CBind::RecFns { lams, .. } => {
                        lams.iter().for_each(|lam| visit_vars(&lam.body, f))
                    }
                    CBind::RecForms { exprs, .. } => exprs.iter().for_each(|e| visit_vars(e, f)),
                }
            }
            visit_vars(body, f);
        }
        Core::Gen(_, _, body) => visit_vars(body, f),
    }
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
