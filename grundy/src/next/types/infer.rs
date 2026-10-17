//! Type inference and elaboration from surface syntax to [`Core`].

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use super::super::builtins;
use super::super::core::{CBind, CClause, CItem, CPat, Core, CtorRef, Lam};
use super::super::error::{err, GrundyError, GrundyErrorKind, GrundyResult, Span};
use super::super::syntax::ast::*;
use super::super::syntax::parse::is_prime_field_name;
use super::*;

/// Where a constructor name resolves.
#[derive(Clone, Debug)]
pub struct CtorInfo {
    /// The constructor reference.
    pub ctor: CtorRef,
    /// Its type scheme (a function type when it has fields).
    pub scheme: Scheme,
    /// Its field count.
    pub arity: usize,
}

/// Elaborated bindings and, for globals, their new schemes.
type Elaborated = (Vec<CBind>, Vec<(String, Scheme)>);

/// Session-level names visible to the checker.
#[derive(Clone, Debug, Default)]
pub struct Globals {
    /// Global value bindings.
    pub values: BTreeMap<String, Scheme>,
    /// Data type names.
    pub types: BTreeMap<String, DataId>,
    /// Constructor names.
    pub ctors: BTreeMap<String, CtorInfo>,
}

/// The result of checking one statement.
pub struct Checked {
    /// The elaborated bindings.
    pub binds: Vec<CBind>,
    /// The elaborated final expression, if any.
    pub expr: Option<Core>,
    /// New global schemes, in binding order.
    pub defined: Vec<(String, Scheme)>,
    /// The final expression's type.
    pub ty: Option<Ty>,
}

#[derive(Clone, Debug)]
struct Local {
    scheme: Scheme,
}

/// The checker for one statement.
pub struct Checker<'a> {
    /// Unifier state, persistent across the session for unique variables.
    pub ts: &'a mut TypeState,
    /// Data registry.
    pub data: &'a DataRegistry,
    /// Session names.
    pub globals: &'a Globals,
    scopes: Vec<Vec<(String, Local)>>,
}

impl<'a> Checker<'a> {
    /// A checker over session state.
    pub fn new(ts: &'a mut TypeState, data: &'a DataRegistry, globals: &'a Globals) -> Self {
        Checker {
            ts,
            data,
            globals,
            scopes: Vec::new(),
        }
    }

    // ------------------------------------------------------------- statements

    /// Check a top-level sequence. Bindings become globals; the final
    /// expression's type is defaulted.
    pub fn check_seq(
        &mut self,
        bindings: &[Binding],
        expr: Option<&Expr>,
    ) -> GrundyResult<Checked> {
        self.ts.level = 0;
        self.ts.preds.clear();
        self.scopes.push(Vec::new());
        let result = (|| {
            let (binds, defined) = self.bindings(bindings, true)?;
            let (expr, ty) = match expr {
                Some(expr) => {
                    let (core, ty) = self.infer(expr)?;
                    (Some(core), Some(ty))
                }
                None => (None, None),
            };
            self.ts.default_all(self.data)?;
            Ok((binds, defined, expr, ty))
        })();
        self.scopes.pop();
        let (mut binds, defined, mut expr, ty) = result?;
        for bind in &mut binds {
            zonk_bind(self.ts, bind);
        }
        if let Some(expr) = &mut expr {
            zonk_core(self.ts, expr);
        }
        let defined = defined
            .into_iter()
            .map(|(name, scheme)| (name, zonk_scheme(self.ts, &scheme)))
            .collect();
        Ok(Checked {
            binds,
            expr,
            defined,
            ty: ty.map(|ty| self.ts.zonk(&ty)),
        })
    }

    /// Check a sequence of bindings in the current scope, returning the
    /// elaborated bindings and (for globals) the new schemes.
    fn bindings(&mut self, bindings: &[Binding], global: bool) -> GrundyResult<Elaborated> {
        let mut out = Vec::new();
        let mut defined = Vec::new();
        let mut index = 0;
        while index < bindings.len() {
            if bindings[index].kind == BindKind::Rec {
                let mut end = index;
                while end < bindings.len() && bindings[end].kind == BindKind::Rec {
                    end += 1;
                }
                let (bind, names) = self.rec_run(&bindings[index..end])?;
                out.push(bind);
                if global {
                    defined.extend(names);
                }
                index = end;
                continue;
            }
            let binding = &bindings[index];
            let (bind, names) = self.let_binding(binding)?;
            out.push(bind);
            if global {
                defined.extend(names);
            }
            index += 1;
        }
        Ok((out, defined))
    }

    fn let_binding(&mut self, binding: &Binding) -> GrundyResult<(CBind, Vec<(String, Scheme)>)> {
        let span = binding.span;
        if let PatKind::Var(name) = &binding.pat.kind {
            self.ts.level += 1;
            let inferred = self.infer(&binding.expr);
            self.ts.level -= 1;
            let (core, ty) = inferred?;
            let is_lambda = is_lambda(&binding.expr);
            let scheme = self
                .ts
                .generalize(&ty, is_lambda, self.data)
                .map_err(|e| e.at(binding.expr.span))?;
            let tparams = if is_lambda {
                scheme.vars.clone()
            } else {
                Vec::new()
            };
            self.bind_local(name, scheme.clone());
            return Ok((
                CBind::Let {
                    pat: CPat::Var(name.clone()),
                    expr: core,
                    tparams,
                    span,
                },
                vec![(name.clone(), scheme)],
            ));
        }
        let (core, ty) = self.infer(&binding.expr)?;
        let mut bound = Vec::new();
        let pat = self.pattern(&binding.pat, &ty, &mut bound)?;
        let mut defined = Vec::new();
        for (name, ty) in bound {
            let scheme = Scheme::mono(ty);
            self.bind_local(&name, scheme.clone());
            defined.push((name, scheme));
        }
        Ok((
            CBind::Let {
                pat,
                expr: core,
                tparams: Vec::new(),
                span,
            },
            defined,
        ))
    }

    fn rec_run(&mut self, run: &[Binding]) -> GrundyResult<(CBind, Vec<(String, Scheme)>)> {
        let mut seen = BTreeSet::new();
        let mut names = Vec::new();
        for binding in run {
            let PatKind::Var(name) = &binding.pat.kind else {
                unreachable!("the parser admits only variables for `=:`");
            };
            if !seen.insert(name.clone()) {
                return Err(GrundyError::new(
                    GrundyErrorKind::Shadow,
                    binding.pat.span,
                    format!("`{name}` is defined twice in one recursive system"),
                ));
            }
            names.push(name.clone());
        }
        self.ts.level += 1;
        let vars: Vec<Ty> = names.iter().map(|_| self.ts.fresh()).collect();
        self.scopes.push(
            names
                .iter()
                .zip(&vars)
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        Local {
                            scheme: Scheme::mono(ty.clone()),
                        },
                    )
                })
                .collect(),
        );
        let inferred = (|| {
            let mut cores = Vec::new();
            for (binding, var) in run.iter().zip(&vars) {
                let (core, ty) = self.infer(&binding.expr)?;
                self.ts
                    .unify(var, &ty, self.data)
                    .map_err(|e| e.at(binding.expr.span))?;
                cores.push(core);
            }
            Ok(cores)
        })();
        self.scopes.pop();
        self.ts.level -= 1;
        let cores = inferred?;
        // Functions or game equations, decided by the inferred types.
        let mut functions = Vec::new();
        for (binding, var) in run.iter().zip(&vars) {
            let ty = self.ts.shallow(var);
            match ty {
                Ty::Fun(..) => {
                    if !is_lambda(&binding.expr) {
                        return Err(GrundyError::new(
                            GrundyErrorKind::Fixpoint,
                            binding.expr.span,
                            "a recursive function is written as a lambda",
                        )
                        .with_hint("`f =: x ↦ …`"));
                    }
                    functions.push(true);
                }
                Ty::Con(TyCon::Form, _) => functions.push(false),
                Ty::Var(_) => {
                    // A brace-only right-hand side is GameLike; recursion
                    // makes it a cyclic Form.
                    self.ts
                        .unify(var, &Ty::form(), self.data)
                        .map_err(|e| e.at(binding.expr.span))?;
                    functions.push(false);
                }
                other => {
                    let shown = self.ts.show(&other, self.data);
                    return Err(GrundyError::new(
                        GrundyErrorKind::Fixpoint,
                        binding.pat.span,
                        format!(
                            "`{}` =: has no recursion theory at type {shown}",
                            names_of(binding)
                        ),
                    )
                    .with_hint(
                        "recursion is for functions (unfolding) and Forms (guarded game equations)",
                    ));
                }
            }
        }
        if functions.iter().any(|f| *f) != functions.iter().all(|f| *f) {
            return Err(GrundyError::new(
                GrundyErrorKind::Fixpoint,
                run[0].span.join(run[run.len() - 1].span),
                "a recursive system is all functions or all game equations",
            )
            .with_hint("separate the runs with a `:=` binding or a new statement"));
        }
        if functions[0] {
            let group_ty = Ty::tuple(vars.clone());
            let scheme = self
                .ts
                .generalize(&group_ty, true, self.data)
                .map_err(|e| e.at(run[0].span))?;
            let Ty::Con(_, member_tys) = &scheme.ty else {
                unreachable!("group type is a tuple")
            };
            let mut defined = Vec::new();
            for (name, ty) in names.iter().zip(member_tys) {
                let member = Scheme {
                    vars: scheme.vars.clone(),
                    preds: scheme.preds.clone(),
                    ty: ty.clone(),
                };
                self.bind_local(name, member.clone());
                defined.push((name.clone(), member));
            }
            let lams = run
                .iter()
                .zip(cores)
                .map(|(binding, core)| match core {
                    Core::Lambda(lam) => lam,
                    _ => Rc::new(Lam {
                        params: Vec::new(),
                        body: core,
                        source: binding.expr.clone(),
                    }),
                })
                .collect();
            Ok((
                CBind::RecFns {
                    names,
                    lams,
                    tparams: scheme.vars,
                },
                defined,
            ))
        } else {
            let mut defined = Vec::new();
            for name in &names {
                let scheme = Scheme::mono(Ty::form());
                self.bind_local(name, scheme.clone());
                defined.push((name.clone(), scheme));
            }
            Ok((
                CBind::RecForms {
                    names,
                    exprs: cores,
                    spans: run.iter().map(|binding| binding.span).collect(),
                },
                defined,
            ))
        }
    }

    fn bind_local(&mut self, name: &str, scheme: Scheme) {
        self.scopes
            .last_mut()
            .expect("a scope")
            .push((name.to_string(), Local { scheme }));
    }

    fn lookup_local(&self, name: &str) -> Option<&Local> {
        self.scopes
            .iter()
            .rev()
            .flat_map(|scope| scope.iter().rev())
            .find(|(bound, _)| bound == name)
            .map(|(_, local)| local)
    }

    // ------------------------------------------------------------ expressions

    /// Infer an expression's type, elaborating it.
    pub fn infer(&mut self, expr: &Expr) -> GrundyResult<(Core, Ty)> {
        self.infer_inner(expr).map_err(|e| e.at(expr.span))
    }

    fn require(&mut self, class: Class, ty: &Ty, span: Span) -> GrundyResult<()> {
        self.ts
            .require(Pred::Is(class, ty.clone()), self.data)
            .map_err(|e| e.at(span))
    }

    fn unify_at(&mut self, a: &Ty, b: &Ty, span: Span) -> GrundyResult<()> {
        self.ts.unify(a, b, self.data).map_err(|e| e.at(span))
    }

    fn literal(&mut self, class: Class, span: Span) -> GrundyResult<Ty> {
        let ty = self.ts.fresh();
        self.require(class, &ty, span)?;
        Ok(ty)
    }

    fn infer_inner(&mut self, expr: &Expr) -> GrundyResult<(Core, Ty)> {
        let span = expr.span;
        match &expr.kind {
            ExprKind::Int(n) => {
                let ty = self.literal(Class::IntLit, span)?;
                Ok((Core::Int(*n, ty.clone()), ty))
            }
            ExprKind::Frac(num, den) => {
                let ty = self.literal(Class::FracLit, span)?;
                Ok((Core::Frac(*num, *den, ty.clone()), ty))
            }
            ExprKind::Star(index) => {
                let ty = self.literal(Class::StarLit, span)?;
                Ok((Core::Star(index.clone(), ty.clone()), ty))
            }
            ExprKind::Omega => {
                let ty = self.literal(Class::OmegaLit, span)?;
                Ok((Core::Omega(ty.clone()), ty))
            }
            ExprKind::Up | ExprKind::Down => {
                let ty = self.literal(Class::GameLike, span)?;
                Ok((
                    Core::Up(matches!(expr.kind, ExprKind::Down), ty.clone()),
                    ty,
                ))
            }
            ExprKind::Bool(b) => Ok((Core::Bool(*b), Ty::bool())),
            ExprKind::Var(name) => self.variable(name, span),
            ExprKind::Con(name) => self.constructor(name, span),
            ExprKind::Tuple(items) => {
                let mut cores = Vec::new();
                let mut tys = Vec::new();
                for item in items {
                    let (core, ty) = self.infer(item)?;
                    cores.push(core);
                    tys.push(ty);
                }
                Ok((Core::Tuple(cores), Ty::tuple(tys)))
            }
            ExprKind::List(items) => {
                let elem = self.ts.fresh();
                let items = self.items(items, &elem)?;
                Ok((Core::List(items), Ty::list(elem)))
            }
            ExprKind::Comprehension(head, clauses) => {
                self.scopes.push(Vec::new());
                let result = (|| {
                    let mut out = Vec::new();
                    for clause in clauses {
                        match clause {
                            Clause::For(pat, source) => {
                                let (core, ty) = self.infer(source)?;
                                let elem = self.ts.fresh();
                                self.unify_at(&ty, &Ty::list(elem.clone()), source.span)?;
                                let mut bound = Vec::new();
                                let cpat = self.pattern(pat, &elem, &mut bound)?;
                                for (name, ty) in bound {
                                    self.bind_local(&name, Scheme::mono(ty));
                                }
                                out.push(CClause::For(cpat, core));
                            }
                            Clause::If(guard) => {
                                let (core, ty) = self.infer(guard)?;
                                self.unify_at(&ty, &Ty::bool(), guard.span)?;
                                out.push(CClause::If(core));
                            }
                        }
                    }
                    let (head, ty) = self.infer(head)?;
                    Ok((Core::Comp(Box::new(head), out), Ty::list(ty)))
                })();
                self.scopes.pop();
                result
            }
            ExprKind::Range { lo, hi, inclusive } => {
                let (lo_core, lo_ty) = self.infer(lo)?;
                self.unify_at(&lo_ty, &Ty::int(), lo.span)?;
                let (hi_core, hi_ty) = self.infer(hi)?;
                self.unify_at(&hi_ty, &Ty::int(), hi.span)?;
                Ok((
                    Core::Range(Box::new(lo_core), Box::new(hi_core), *inclusive, span),
                    Ty::list(Ty::int()),
                ))
            }
            ExprKind::Form { left, right } => {
                let ty = self.literal(Class::GameLike, span)?;
                let left = self.items(left, &ty)?;
                let right = self.items(right, &ty)?;
                Ok((Core::Form(left, right, ty.clone(), span), ty))
            }
            ExprKind::Call(callee, args) => self.call(callee, args, span),
            ExprKind::Index(base, index) => {
                let (base_core, base_ty) = self.infer(base)?;
                let elem = self.ts.fresh();
                self.unify_at(&base_ty, &Ty::list(elem.clone()), base.span)?;
                let (index_core, index_ty) = self.infer(index)?;
                self.unify_at(&index_ty, &Ty::int(), index.span)?;
                Ok((
                    Core::Index(Box::new(base_core), Box::new(index_core), span),
                    elem,
                ))
            }
            ExprKind::Lambda(params, body) => {
                self.scopes.push(Vec::new());
                let result = (|| {
                    let mut annotation_vars = BTreeMap::new();
                    let mut cpats = Vec::new();
                    let mut param_tys = Vec::new();
                    let mut names = BTreeSet::new();
                    for param in params {
                        let ty = match &param.ty {
                            Some(ty) => self.annotation(ty, &mut annotation_vars)?,
                            None => self.ts.fresh(),
                        };
                        let mut bound = Vec::new();
                        let cpat = self.pattern(&param.pat, &ty, &mut bound)?;
                        for (name, ty) in bound {
                            if !names.insert(name.clone()) {
                                return Err(GrundyError::new(
                                    GrundyErrorKind::Shadow,
                                    param.pat.span,
                                    format!("duplicate binder `{name}`"),
                                ));
                            }
                            self.bind_local(&name, Scheme::mono(ty));
                        }
                        cpats.push(cpat);
                        param_tys.push(ty);
                    }
                    let (body_core, body_ty) = self.infer(body)?;
                    Ok((
                        Core::Lambda(Rc::new(Lam {
                            params: cpats,
                            body: body_core,
                            source: expr.clone(),
                        })),
                        Ty::Fun(param_tys, Box::new(body_ty)),
                    ))
                })();
                self.scopes.pop();
                result
            }
            ExprKind::Unary(op, inner) => {
                let (core, ty) = self.infer(inner)?;
                match op {
                    UnaryOp::Not => self.unify_at(&ty, &Ty::bool(), inner.span)?,
                    UnaryOp::Neg => self.require(Class::Add, &ty, span)?,
                    UnaryOp::Recip => self.require(Class::Div, &ty, span)?,
                }
                Ok((Core::Unary(*op, Box::new(core), span), ty))
            }
            ExprKind::Binary(op, lhs, rhs) => self.binary(*op, lhs, rhs, span),
            ExprKind::Relation(op, lhs, rhs) => {
                let (lhs_core, lhs_ty) = self.infer(lhs)?;
                let (rhs_core, rhs_ty) = self.infer(rhs)?;
                self.unify_at(&lhs_ty, &rhs_ty, span)?;
                match op {
                    RelOp::Eq => self.require(Class::Eq, &lhs_ty, span)?,
                    RelOp::Lt | RelOp::Gt | RelOp::Le | RelOp::Ge | RelOp::Fuzzy => {
                        self.require(Class::Ord, &lhs_ty, span)?
                    }
                    RelOp::Equiv => self.unify_at(&lhs_ty, &Ty::form(), span).map_err(|e| {
                        e.with_hint(
                            "`≡` compares presented Forms; on values `=` is already structural",
                        )
                    })?,
                    RelOp::Outcome(_) => self.require(Class::GameLike, &lhs_ty, span)?,
                }
                Ok((
                    Core::Rel(*op, Box::new(lhs_core), Box::new(rhs_core), span),
                    Ty::bool(),
                ))
            }
            ExprKind::If(cond, then_branch, else_branch) => {
                let (cond_core, cond_ty) = self.infer(cond)?;
                self.unify_at(&cond_ty, &Ty::bool(), cond.span)?;
                let (then_core, then_ty) = self.infer(then_branch)?;
                let (else_core, else_ty) = self.infer(else_branch)?;
                self.unify_at(&then_ty, &else_ty, else_branch.span)?;
                Ok((
                    Core::If(
                        Box::new(cond_core),
                        Box::new(then_core),
                        Box::new(else_core),
                    ),
                    then_ty,
                ))
            }
            ExprKind::Match(scrutinee, arms) => {
                let (scrutinee_core, scrutinee_ty) = self.infer(scrutinee)?;
                let result_ty = self.ts.fresh();
                let mut out = Vec::new();
                for (pat, body) in arms {
                    self.scopes.push(Vec::new());
                    let arm = (|| {
                        let mut bound = Vec::new();
                        let cpat = self.pattern(pat, &scrutinee_ty, &mut bound)?;
                        for (name, ty) in bound {
                            self.bind_local(&name, Scheme::mono(ty));
                        }
                        let (body_core, body_ty) = self.infer(body)?;
                        self.unify_at(&body_ty, &result_ty, body.span)?;
                        Ok((cpat, body_core))
                    })();
                    self.scopes.pop();
                    out.push(arm?);
                }
                Ok((Core::Match(Box::new(scrutinee_core), out, span), result_ty))
            }
            ExprKind::Block(bindings, body) => {
                self.scopes.push(Vec::new());
                let result = (|| {
                    let (binds, _) = self.bindings(bindings, false)?;
                    let (body_core, body_ty) = self.infer(body)?;
                    Ok((Core::Let(binds, Box::new(body_core)), body_ty))
                })();
                self.scopes.pop();
                result
            }
            ExprKind::Annot(inner, ty_expr) => {
                let mut vars = BTreeMap::new();
                let ty = self.annotation(ty_expr, &mut vars)?;
                let generator = generator_name(&ty);
                if let Some(name) = generator {
                    self.scopes.push(vec![(
                        name.to_string(),
                        Local {
                            scheme: Scheme::mono(ty.clone()),
                        },
                    )]);
                }
                let result = self.infer(inner);
                if generator.is_some() {
                    self.scopes.pop();
                }
                let (core, inner_ty) = result?;
                self.unify_at(&inner_ty, &ty, span)?;
                let core = match generator {
                    Some(name) => Core::Gen(name.to_string(), ty.clone(), Box::new(core)),
                    None => core,
                };
                Ok((core, ty))
            }
        }
    }

    fn items(&mut self, items: &[Item], elem: &Ty) -> GrundyResult<Vec<CItem>> {
        let mut out = Vec::new();
        for item in items {
            match item {
                Item::One(expr) => {
                    let (core, ty) = self.infer(expr)?;
                    self.unify_at(&ty, elem, expr.span)?;
                    out.push(CItem::One(core));
                }
                Item::Splice(expr) => {
                    let (core, ty) = self.infer(expr)?;
                    self.unify_at(&ty, &Ty::list(elem.clone()), expr.span)?;
                    out.push(CItem::Splice(core));
                }
            }
        }
        Ok(out)
    }

    fn variable(&mut self, name: &str, span: Span) -> GrundyResult<(Core, Ty)> {
        if let Some(local) = self.lookup_local(name).cloned() {
            return self.instantiate_var(name, &local.scheme, span);
        }
        if let Some(scheme) = self.globals.values.get(name).cloned() {
            return self.instantiate_var(name, &scheme, span);
        }
        if let Some(builtin) = builtins::lookup(name) {
            let (ty, inst) = self.ts.instantiate(builtins::scheme(builtin), self.data)?;
            return Ok((Core::Builtin(builtin, inst), ty));
        }
        Err(unbound(name, span))
    }

    fn instantiate_var(
        &mut self,
        name: &str,
        scheme: &Scheme,
        span: Span,
    ) -> GrundyResult<(Core, Ty)> {
        if scheme.vars.is_empty() {
            return Ok((Core::Var(name.to_string(), span), scheme.ty.clone()));
        }
        let (ty, inst) = self
            .ts
            .instantiate(scheme, self.data)
            .map_err(|e| e.at(span))?;
        Ok((Core::Inst(name.to_string(), inst, span), ty))
    }

    fn constructor(&mut self, name: &str, span: Span) -> GrundyResult<(Core, Ty)> {
        let info = match builtin_ctor(name) {
            Some(info) => info,
            None => self.globals.ctors.get(name).cloned().ok_or_else(|| {
                GrundyError::new(
                    GrundyErrorKind::Unbound,
                    span,
                    format!("unknown constructor `{name}`"),
                )
                .with_hint("declare it with `data T = …`")
            })?,
        };
        let (ty, _) = self.ts.instantiate(&info.scheme, self.data)?;
        Ok((Core::Ctor(info.ctor, info.arity), ty))
    }

    fn call(&mut self, callee: &Expr, args: &[Expr], span: Span) -> GrundyResult<(Core, Ty)> {
        let (callee_core, callee_ty) = self.infer(callee)?;
        let mut arg_cores = Vec::new();
        let mut arg_tys = Vec::new();
        for arg in args {
            let (core, ty) = self.infer(arg)?;
            arg_cores.push(core);
            arg_tys.push(ty);
        }
        // Polynomials and rational functions are callable: evaluation at a
        // scalar, or composition with another polynomial.
        if let Ty::Con(con @ (TyCon::Poly | TyCon::RatFunc), scalar) = self.ts.shallow(&callee_ty) {
            if arg_cores.len() != 1 {
                return Err(GrundyError::new(
                    GrundyErrorKind::Arity,
                    span,
                    "substitution takes one argument",
                ));
            }
            let arg_ty = self.ts.shallow(&arg_tys[0]);
            let callee_ty = Ty::Con(con, scalar.clone());
            let result = match &arg_ty {
                // Composition stays in one ring or field.
                Ty::Con(TyCon::Poly | TyCon::RatFunc, _) => {
                    self.unify_at(&arg_ty, &callee_ty, args[0].span)?;
                    callee_ty
                }
                _ => {
                    self.unify_at(&arg_ty, &scalar[0], args[0].span)?;
                    scalar[0].clone()
                }
            };
            return Ok((
                Core::Subst(
                    Box::new(callee_core),
                    Box::new(arg_cores.pop().expect("one argument")),
                    span,
                ),
                result,
            ));
        }
        let ret = self.ts.fresh();
        let expected = Ty::Fun(arg_tys, Box::new(ret.clone()));
        self.ts
            .unify(&callee_ty, &expected, self.data)
            .map_err(|e| {
                if e.kind == GrundyErrorKind::Arity {
                    GrundyError::new(
                        GrundyErrorKind::Arity,
                        span,
                        format!(
                            "`{}` called with {} argument{}",
                            unparse_callee(callee),
                            args.len(),
                            if args.len() == 1 { "" } else { "s" }
                        ),
                    )
                    .with_hint(format!(
                        "its type is {}",
                        self.ts.show(&callee_ty, self.data)
                    ))
                } else {
                    e.at(span)
                }
            })?;
        Ok((Core::Call(Box::new(callee_core), arg_cores, span), ret))
    }

    fn binary(
        &mut self,
        op: BinaryOp,
        lhs: &Expr,
        rhs: &Expr,
        span: Span,
    ) -> GrundyResult<(Core, Ty)> {
        let (lhs_core, lhs_ty) = self.infer(lhs)?;
        let (rhs_core, rhs_ty) = self.infer(rhs)?;
        let ty = match op {
            BinaryOp::And | BinaryOp::Or => {
                self.unify_at(&lhs_ty, &Ty::bool(), lhs.span)?;
                self.unify_at(&rhs_ty, &Ty::bool(), rhs.span)?;
                let lhs_core = Box::new(lhs_core);
                let rhs_core = Box::new(rhs_core);
                return Ok((
                    if op == BinaryOp::And {
                        Core::And(lhs_core, rhs_core)
                    } else {
                        Core::Or(lhs_core, rhs_core)
                    },
                    Ty::bool(),
                ));
            }
            BinaryOp::Pow => {
                self.ts
                    .require(Pred::Pow(lhs_ty.clone(), rhs_ty), self.data)
                    .map_err(|e| e.at(span))?;
                lhs_ty
            }
            BinaryOp::Concat => {
                let elem = self.ts.fresh();
                self.unify_at(&lhs_ty, &Ty::list(elem.clone()), lhs.span)?;
                self.unify_at(&rhs_ty, &lhs_ty, rhs.span)?;
                lhs_ty
            }
            _ => {
                self.unify_at(&lhs_ty, &rhs_ty, span)?;
                let class = match op {
                    BinaryOp::Add | BinaryOp::Sub => Class::Add,
                    BinaryOp::Mul => Class::Mul,
                    BinaryOp::Div => Class::Div,
                    BinaryOp::Rem => Class::Rem,
                    BinaryOp::Wedge => Class::Wedge,
                    _ => unreachable!(),
                };
                self.require(class, &lhs_ty, span)?;
                lhs_ty
            }
        };
        Ok((
            Core::Binary(op, Box::new(lhs_core), Box::new(rhs_core), span),
            ty,
        ))
    }

    // --------------------------------------------------------------- patterns

    fn pattern(&mut self, pat: &Pat, ty: &Ty, bound: &mut Vec<(String, Ty)>) -> GrundyResult<CPat> {
        let span = pat.span;
        match &pat.kind {
            PatKind::Wild => Ok(CPat::Wild),
            PatKind::Var(name) => {
                if bound.iter().any(|(existing, _)| existing == name) {
                    return Err(GrundyError::new(
                        GrundyErrorKind::Shadow,
                        span,
                        format!("duplicate binder `{name}`"),
                    ));
                }
                bound.push((name.clone(), ty.clone()));
                Ok(CPat::Var(name.clone()))
            }
            PatKind::Int(n) => {
                self.unify_at(ty, &Ty::int(), span)?;
                Ok(CPat::Int(*n))
            }
            PatKind::Bool(b) => {
                self.unify_at(ty, &Ty::bool(), span)?;
                Ok(CPat::Bool(*b))
            }
            PatKind::Tuple(items) => {
                let tys: Vec<Ty> = items.iter().map(|_| self.ts.fresh()).collect();
                self.unify_at(ty, &Ty::tuple(tys.clone()), span)?;
                let mut out = Vec::new();
                for (item, item_ty) in items.iter().zip(&tys) {
                    out.push(self.pattern(item, item_ty, bound)?);
                }
                Ok(CPat::Tuple(out))
            }
            PatKind::List(items, rest) => {
                let elem = self.ts.fresh();
                self.unify_at(ty, &Ty::list(elem.clone()), span)?;
                let mut out = Vec::new();
                for item in items {
                    out.push(self.pattern(item, &elem, bound)?);
                }
                let rest = match rest {
                    Some(rest) => Some(Box::new(self.pattern(rest, ty, bound)?)),
                    None => None,
                };
                Ok(CPat::List(out, rest))
            }
            PatKind::Con(name, args) => {
                let info = match builtin_ctor(name) {
                    Some(info) => info,
                    None => self.globals.ctors.get(name).cloned().ok_or_else(|| {
                        GrundyError::new(
                            GrundyErrorKind::Unbound,
                            span,
                            format!("unknown constructor `{name}`"),
                        )
                    })?,
                };
                if args.len() != info.arity {
                    return Err(GrundyError::new(
                        GrundyErrorKind::Arity,
                        span,
                        format!(
                            "constructor `{name}` has {} field{}, the pattern gives {}",
                            info.arity,
                            if info.arity == 1 { "" } else { "s" },
                            args.len()
                        ),
                    ));
                }
                let (ctor_ty, _) = self.ts.instantiate(&info.scheme, self.data)?;
                let (field_tys, result_ty) = match ctor_ty {
                    Ty::Fun(fields, ret) => (fields, *ret),
                    other => (Vec::new(), other),
                };
                self.unify_at(ty, &result_ty, span)?;
                let mut out = Vec::new();
                for (arg, field_ty) in args.iter().zip(&field_tys) {
                    out.push(self.pattern(arg, field_ty, bound)?);
                }
                Ok(CPat::Ctor(info.ctor, out))
            }
            PatKind::Annot(inner, ty_expr) => {
                let annotated = self.annotation(ty_expr, &mut BTreeMap::new())?;
                self.unify_at(ty, &annotated, span)?;
                self.pattern(inner, ty, bound)
            }
        }
    }

    // ------------------------------------------------------------------ types

    fn annotation(&mut self, ty: &TypeExpr, vars: &mut BTreeMap<String, Ty>) -> GrundyResult<Ty> {
        let globals = self.globals;
        let ts = &mut *self.ts;
        type_from_expr(ty, &globals.types, vars, &mut || ts.fresh())
    }
}

fn names_of(binding: &Binding) -> String {
    binding.pat.binders().join(", ")
}

fn unparse_callee(callee: &Expr) -> String {
    super::super::syntax::unparse::unparse_expr(callee)
}

fn unbound(name: &str, span: Span) -> GrundyError {
    let mut error = GrundyError::new(
        GrundyErrorKind::Unbound,
        span,
        format!("unbound identifier `{name}`"),
    );
    let hint = match name {
        "omega" => Some("ω is `ω` (sugar `w`)".to_string()),
        "t" => Some("the indeterminate is bound by its ring: `(t↑2 + 1 : F5[t])`".to_string()),
        "x" => Some("the field generator is bound by its field: `(x + 1 : F9)`".to_string()),
        "outcome_of" | "winner" | "who" => Some(
            "outcomes are `outcome(g)`, or relations against 0: `g > 0`, `g < 0`, `g = 0`, `g ∥ 0`"
                .to_string(),
        ),
        _ => Some(format!(
            "define it first: `{name} := …`; recursive definitions use `=:`"
        )),
    };
    if let Some(hint) = hint {
        error = error.with_hint(hint);
    }
    error
}

fn is_lambda(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Lambda(..) => true,
        ExprKind::Annot(inner, _) => is_lambda(inner),
        _ => false,
    }
}

/// The generator a type binds in its annotation: `t` for polynomial rings
/// and rational-function fields, `x` for the extension fields.
pub fn generator_name(ty: &Ty) -> Option<&'static str> {
    match ty {
        Ty::Con(TyCon::Poly | TyCon::RatFunc, _) => Some("t"),
        Ty::Con(TyCon::Fpn(..), _) => Some("x"),
        _ => None,
    }
}

fn builtin_ctor(name: &str) -> Option<CtorInfo> {
    let winner = Ty::con(TyCon::Winner);
    let option_of = |a: Ty| Ty::Con(TyCon::Option, vec![a]);
    Some(match name {
        "Left" | "Right" | "Draw" => CtorInfo {
            ctor: CtorRef::Winner(match name {
                "Left" => 0,
                "Right" => 1,
                _ => 2,
            }),
            scheme: Scheme::mono(winner),
            arity: 0,
        },
        "Some" => CtorInfo {
            ctor: CtorRef::Some,
            scheme: Scheme {
                vars: vec![0],
                preds: Vec::new(),
                ty: Ty::Fun(vec![Ty::Var(0)], Box::new(option_of(Ty::Var(0)))),
            },
            arity: 1,
        },
        "None" => CtorInfo {
            ctor: CtorRef::None,
            scheme: Scheme {
                vars: vec![0],
                preds: Vec::new(),
                ty: option_of(Ty::Var(0)),
            },
            arity: 0,
        },
        _ => return None,
    })
}

/// Whether a name is a builtin constructor.
pub fn is_builtin_ctor(name: &str) -> bool {
    builtin_ctor(name).is_some()
}

/// Convert a type expression, allocating variables with `fresh`.
pub fn type_from_expr(
    ty: &TypeExpr,
    data: &BTreeMap<String, DataId>,
    vars: &mut BTreeMap<String, Ty>,
    fresh: &mut dyn FnMut() -> Ty,
) -> GrundyResult<Ty> {
    let span = ty.span;
    let unknown = |name: &str| {
        GrundyError::new(
            GrundyErrorKind::Unbound,
            span,
            format!("unknown type `{name}`"),
        )
    };
    match &ty.kind {
        TypeKind::Var(name) => Ok(vars.entry(name.clone()).or_insert_with(fresh).clone()),
        TypeKind::Tuple(items) => {
            let mut out = Vec::new();
            for item in items {
                out.push(type_from_expr(item, data, vars, fresh)?);
            }
            Ok(Ty::tuple(out))
        }
        TypeKind::Fun(args, ret) => {
            let mut out = Vec::new();
            for arg in args {
                out.push(type_from_expr(arg, data, vars, fresh)?);
            }
            Ok(Ty::Fun(
                out,
                Box::new(type_from_expr(ret, data, vars, fresh)?),
            ))
        }
        TypeKind::PolyRing(name) => {
            let scalar = scalar_con(name).ok_or_else(|| unknown(name))?;
            if !matches!(scalar, TyCon::Fp(_) | TyCon::Int) {
                return Err(GrundyError::new(
                    GrundyErrorKind::Type,
                    span,
                    format!("polynomial rings are over F2, F3, F5, F7, or Int, not {name}"),
                ));
            }
            Ok(Ty::Con(TyCon::Poly, vec![Ty::con(scalar)]))
        }
        TypeKind::RatField(name) => {
            debug_assert!(is_prime_field_name(name));
            let scalar = scalar_con(name).ok_or_else(|| unknown(name))?;
            Ok(Ty::Con(TyCon::RatFunc, vec![Ty::con(scalar)]))
        }
        TypeKind::Named(name, args) => {
            let mut converted = Vec::new();
            for arg in args {
                converted.push(type_from_expr(arg, data, vars, fresh)?);
            }
            let arity_error = |want: usize| {
                GrundyError::new(
                    GrundyErrorKind::Arity,
                    span,
                    format!(
                        "type `{name}` takes {want} argument{}",
                        if want == 1 { "" } else { "s" }
                    ),
                )
            };
            let unary = |con: TyCon, converted: Vec<Ty>| {
                if converted.len() == 1 {
                    Ok(Ty::Con(con, converted))
                } else {
                    Err(arity_error(1))
                }
            };
            match name.as_str() {
                "List" => unary(TyCon::List, converted),
                "Option" => unary(TyCon::Option, converted),
                "Rules" => unary(TyCon::Rules, converted),
                "Bounded" => unary(TyCon::Bounded, converted),
                "Quotient" => unary(TyCon::Quotient, converted),
                "Algebra" => unary(TyCon::Algebra, converted),
                "Mv" => unary(TyCon::Mv, converted),
                _ => {
                    if !converted.is_empty() {
                        return Err(arity_error(0));
                    }
                    let con = match name.as_str() {
                        "Bool" => TyCon::Bool,
                        "Game" => TyCon::Game,
                        "Form" => TyCon::Form,
                        "Winner" => TyCon::Winner,
                        "Witness" => TyCon::Witness,
                        "Claim" => TyCon::Claim,
                        other => match scalar_con(other) {
                            Some(con) => con,
                            None => match data.get(other) {
                                Some(id) => TyCon::Data(*id),
                                None => return Err(unknown(other)),
                            },
                        },
                    };
                    Ok(Ty::con(con))
                }
            }
        }
    }
}

/// Convert a closed signature, numbering its variables from zero.
pub fn type_from_expr_closed(
    ty: &TypeExpr,
    data: &DataRegistry,
) -> GrundyResult<(Ty, BTreeMap<String, Ty>)> {
    let _ = data;
    let mut vars = BTreeMap::new();
    let mut next = 0;
    let mut fresh = || {
        let v = Ty::Var(next);
        next += 1;
        v
    };
    let ty = type_from_expr(ty, &BTreeMap::new(), &mut vars, &mut fresh)?;
    Ok((ty, vars))
}

/// Scalar and numeric type names.
pub fn scalar_con(name: &str) -> Option<TyCon> {
    Some(match name {
        "Int" => TyCon::Int,
        "Nimber" => TyCon::Nimber,
        "Ordinal" => TyCon::Ordinal,
        "Surreal" => TyCon::Surreal,
        "Omnific" => TyCon::Omnific,
        "F2" => TyCon::Fp(2),
        "F3" => TyCon::Fp(3),
        "F5" => TyCon::Fp(5),
        "F7" => TyCon::Fp(7),
        "F4" => TyCon::Fpn(2, 2),
        "F8" => TyCon::Fpn(2, 3),
        "F16" => TyCon::Fpn(2, 4),
        "F9" => TyCon::Fpn(3, 2),
        "F27" => TyCon::Fpn(3, 3),
        "F25" => TyCon::Fpn(5, 2),
        _ => return None,
    })
}

/// Convert data declaration field types.
pub fn data_field_types(
    decl: &DataDecl,
    data: &BTreeMap<String, DataId>,
) -> GrundyResult<Vec<(String, Vec<Ty>)>> {
    let mut out = Vec::new();
    for ctor in &decl.ctors {
        let mut fields = Vec::new();
        for field in &ctor.fields {
            let mut vars = BTreeMap::new();
            let ty = type_from_expr(field, data, &mut vars, &mut || Ty::Var(u32::MAX))?;
            if !vars.is_empty() {
                return Err(GrundyError::new(
                    GrundyErrorKind::Type,
                    field.span,
                    "data fields have concrete types",
                ));
            }
            fields.push(ty);
        }
        out.push((ctor.name.clone(), fields));
    }
    Ok(out)
}

fn zonk_scheme(ts: &TypeState, scheme: &Scheme) -> Scheme {
    Scheme {
        vars: scheme.vars.clone(),
        preds: scheme
            .preds
            .iter()
            .map(|pred| match pred {
                Pred::Is(class, ty) => Pred::Is(*class, ts.zonk(ty)),
                Pred::Pow(a, e) => Pred::Pow(ts.zonk(a), ts.zonk(e)),
            })
            .collect(),
        ty: ts.zonk(&scheme.ty),
    }
}

/// Apply the final substitution to every type in a binding.
pub fn zonk_bind(ts: &TypeState, bind: &mut CBind) {
    match bind {
        CBind::Let { expr, .. } => zonk_core(ts, expr),
        CBind::RecFns { lams, .. } => {
            for lam in lams {
                let lam = Rc::get_mut(lam).expect("fresh lambda");
                zonk_core(ts, &mut lam.body);
            }
        }
        CBind::RecForms { exprs, .. } => exprs.iter_mut().for_each(|expr| zonk_core(ts, expr)),
    }
}

/// Apply the final substitution to every type in an expression.
pub fn zonk_core(ts: &TypeState, core: &mut Core) {
    let z = |ty: &mut Ty| *ty = ts.zonk(ty);
    match core {
        Core::Int(_, ty)
        | Core::Frac(_, _, ty)
        | Core::Star(_, ty)
        | Core::Omega(ty)
        | Core::Up(_, ty) => z(ty),
        Core::Bool(_) | Core::Var(..) | Core::Ctor(..) => {}
        Core::Inst(_, tys, _) | Core::Builtin(_, tys) => tys.iter_mut().for_each(z),
        Core::Tuple(items) => items.iter_mut().for_each(|item| zonk_core(ts, item)),
        Core::List(items) => items.iter_mut().for_each(|item| zonk_item(ts, item)),
        Core::Comp(head, clauses) => {
            zonk_core(ts, head);
            for clause in clauses {
                match clause {
                    CClause::For(_, source) => zonk_core(ts, source),
                    CClause::If(guard) => zonk_core(ts, guard),
                }
            }
        }
        Core::Range(a, b, ..) | Core::Subst(a, b, _) | Core::Index(a, b, _) => {
            zonk_core(ts, a);
            zonk_core(ts, b);
        }
        Core::Binary(_, a, b, _) | Core::Rel(_, a, b, _) | Core::And(a, b) | Core::Or(a, b) => {
            zonk_core(ts, a);
            zonk_core(ts, b);
        }
        Core::Form(left, right, ty, _) => {
            left.iter_mut().for_each(|item| zonk_item(ts, item));
            right.iter_mut().for_each(|item| zonk_item(ts, item));
            z(ty);
        }
        Core::Call(callee, args, _) => {
            zonk_core(ts, callee);
            args.iter_mut().for_each(|arg| zonk_core(ts, arg));
        }
        Core::Lambda(lam) => {
            let lam = Rc::get_mut(lam).expect("fresh lambda");
            zonk_core(ts, &mut lam.body);
        }
        Core::Unary(_, a, _) => zonk_core(ts, a),
        Core::If(c, a, b) => {
            zonk_core(ts, c);
            zonk_core(ts, a);
            zonk_core(ts, b);
        }
        Core::Match(scrutinee, arms, _) => {
            zonk_core(ts, scrutinee);
            arms.iter_mut().for_each(|(_, body)| zonk_core(ts, body));
        }
        Core::Let(binds, body) => {
            binds.iter_mut().for_each(|bind| zonk_bind(ts, bind));
            zonk_core(ts, body);
        }
        Core::Gen(_, ty, body) => {
            z(ty);
            zonk_core(ts, body);
        }
    }
}

fn zonk_item(ts: &TypeState, item: &mut CItem) {
    match item {
        CItem::One(core) | CItem::Splice(core) => zonk_core(ts, core),
    }
}

/// An error for a type annotation that names no type.
pub fn unknown_type(name: &str) -> GrundyError {
    err(GrundyErrorKind::Unbound, format!("unknown type `{name}`"))
}
