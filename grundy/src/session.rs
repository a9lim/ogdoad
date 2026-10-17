//! A session: persistent types, data declarations, and global values.
//!
//! [`Session`] is single-threaded (values are `Rc`). The public handle runs
//! it on a persistent large-stack worker.

use std::cell::Cell;
use std::collections::BTreeMap;
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::rc::Rc;
use std::sync::Once;

use super::core::CtorRef;
use super::display::Show;
use super::error::{GrundyError, GrundyErrorKind, GrundyResult, Span};
use super::eval::interp::{Interp, Scope, DEFAULT_FUEL, DEFAULT_GRAPH_BUDGET};
use super::eval::value::{Env, Globals, Value};
use super::games::form::{FormV, GameElement};
use super::syntax::ast::{DataDecl, Stmt};
use super::syntax::parse::{parse_expr, parse_statement};
use super::syntax::unparse::unparse_stmt;
use super::types::infer::{data_field_types, Checker, CtorInfo, Globals as TypeGlobals};
use super::types::{
    show_scheme, show_ty, DataId, DataInfo, DataRegistry, Scheme, Ty, TyCon, TypeState, VarNames,
};

/// The printed result of one statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Output {
    /// The canonical rendering of the input.
    pub echo: String,
    /// The final value's display, with a type annotation when needed.
    pub value: Option<String>,
}

/// Session state.
pub struct Session {
    ts: TypeState,
    data: DataRegistry,
    types: TypeGlobals,
    values: Globals,
    /// The per-statement work budget.
    pub fuel: u128,
    /// The node budget.
    pub graph_budget: u128,
}

impl Default for Session {
    fn default() -> Self {
        Session::new()
    }
}

impl Session {
    /// An empty session.
    pub fn new() -> Session {
        Session {
            ts: TypeState::default(),
            data: DataRegistry::default(),
            types: TypeGlobals::default(),
            values: Rc::new(BTreeMap::new()),
            fuel: DEFAULT_FUEL,
            graph_budget: DEFAULT_GRAPH_BUDGET,
        }
    }

    /// Evaluate one statement.
    pub fn eval(&mut self, src: &str) -> GrundyResult<Output> {
        // A failed statement leaves no trace, including unifications it made.
        let saved = self.ts.clone();
        let result = contain_overflow(Span::new(0, src.len()), || self.eval_statement(src));
        if result.is_err() {
            self.ts = saved;
        }
        result
    }

    fn eval_statement(&mut self, src: &str) -> GrundyResult<Output> {
        let stmt = parse_statement(src)?;
        let echo = unparse_stmt(&stmt);
        match stmt {
            Stmt::Data(decl) => {
                self.declare(&decl)?;
                Ok(Output { echo, value: None })
            }
            Stmt::Seq(bindings, expr) => {
                let checked = {
                    let mut checker = Checker::new(&mut self.ts, &self.data, &self.types);
                    checker.check_seq(&bindings, expr.as_ref())?
                };
                let mut interp = Interp::new(&self.data, self.fuel, self.graph_budget);
                let mut values = (*self.values).clone();
                for bind in &checked.binds {
                    let scope = Scope {
                        env: Env::new(),
                        globals: Rc::new(values.clone()),
                        tenv: Rc::new(BTreeMap::new()),
                    };
                    for (name, value) in interp.exec_bind(bind, &scope)? {
                        values.insert(name, value);
                    }
                }
                let shown = match (&checked.expr, &checked.ty) {
                    (Some(expr), Some(ty)) => {
                        let scope = Scope {
                            env: Env::new(),
                            globals: Rc::new(values.clone()),
                            tenv: Rc::new(BTreeMap::new()),
                        };
                        let value = interp.eval(expr, &scope)?;
                        Some(self.show_typed(&value, ty, interp.fuel)?)
                    }
                    _ => None,
                };
                // Commit only after the whole statement succeeded.
                self.values = Rc::new(values);
                for (name, scheme) in checked.defined {
                    self.types.values.insert(name, scheme);
                }
                Ok(Output { echo, value: shown })
            }
        }
    }

    fn declare(&mut self, decl: &DataDecl) -> GrundyResult<()> {
        let id = self.data.decls.len() as DataId;
        let mut names = self.types.types.clone();
        names.insert(decl.name.clone(), id);
        let fields = data_field_types(decl, &names).map_err(|e| e.at(decl.span))?;
        let mut seen = std::collections::BTreeSet::new();
        for (ctor, _) in &fields {
            if !seen.insert(ctor.clone()) || super::types::infer::is_builtin_ctor(ctor) {
                return Err(GrundyError::new(
                    GrundyErrorKind::Shadow,
                    decl.span,
                    format!("constructor `{ctor}` is already defined"),
                ));
            }
        }
        let plain = fields
            .iter()
            .flat_map(|(_, tys)| tys)
            .all(|ty| self.plain(ty, id));
        self.data.decls.push(DataInfo {
            name: decl.name.clone(),
            ctors: fields.clone(),
            plain,
        });
        self.types.types.insert(decl.name.clone(), id);
        let result = Ty::con(TyCon::Data(id));
        for (index, (ctor, tys)) in fields.into_iter().enumerate() {
            let arity = tys.len();
            let ty = if tys.is_empty() {
                result.clone()
            } else {
                Ty::Fun(tys, Box::new(result.clone()))
            };
            self.types.ctors.insert(
                ctor,
                CtorInfo {
                    ctor: CtorRef::Data(id, index as u32),
                    scheme: Scheme::mono(ty),
                    arity,
                },
            );
        }
        Ok(())
    }

    /// Whether a field type supports `=` and `Key`, assuming the declaration
    /// being defined does.
    fn plain(&self, ty: &Ty, own: DataId) -> bool {
        use super::types::{instance, Class, Pred};
        match ty {
            Ty::Con(TyCon::Data(id), _) => *id == own || self.data.get(*id).plain,
            Ty::Con(..) => [Class::Eq, Class::Key].iter().all(|class| {
                instance(*class, ty, &self.data).is_some_and(|subgoals| {
                    subgoals.iter().all(|pred| match pred {
                        Pred::Is(_, inner) => self.plain(inner, own),
                        Pred::Pow(..) => false,
                    })
                })
            }),
            _ => false,
        }
    }

    /// Display a value; annotate with its type exactly when re-reading the
    /// text alone would not recover that type.
    pub fn show_typed(&self, value: &Value, ty: &Ty, budget: u128) -> GrundyResult<String> {
        let names = self
            .values
            .iter()
            .map(|(name, value)| {
                let graph = match value {
                    Value::Form(FormV(GameElement::Graph(graph))) => Some(graph.clone()),
                    _ => None,
                };
                (name.clone(), graph)
            })
            .collect();
        let reads = |text: &str, ty: &Ty| self.reads_as(text, ty);
        let show = Show::new(&self.data, names, budget, Some(&reads));
        let text = show.top(value);
        if show.exhausted.get() {
            return Err(GrundyError::new(
                GrundyErrorKind::Fuel,
                Span::default(),
                format!("the display exceeds the {budget} atoms of work left"),
            )
            .with_hint("raise it with `:fuel n`; budgets are never a value"));
        }
        Ok(if self.reads_as(&text, ty) {
            text
        } else {
            let ty = show_ty(ty, &self.data, &mut VarNames::default());
            if super::display::starts_open(&text) {
                format!("({text}) : {ty}")
            } else {
                format!("{text} : {ty}")
            }
        })
    }

    fn reads_as(&self, text: &str, ty: &Ty) -> bool {
        // A display is an expression, or an equation system whose last
        // equation names the value (`on =: {on |}`).
        let (bindings, expr) = match parse_expr(text) {
            Ok(expr) => (Vec::new(), expr),
            Err(_) => match parse_statement(text) {
                Ok(Stmt::Seq(bindings, None)) if !bindings.is_empty() => {
                    let last = bindings.last().expect("non-empty");
                    let names = last.pat.binders();
                    let [name] = names.as_slice() else {
                        return false;
                    };
                    let expr = super::syntax::ast::Expr::new(
                        super::syntax::ast::ExprKind::Var(name.to_string()),
                        last.span,
                    );
                    (bindings, expr)
                }
                _ => return false,
            },
        };
        // Displays are closed, so a fresh unifier suffices.
        let mut ts = TypeState::default();
        let empty = TypeGlobals {
            values: BTreeMap::new(),
            types: self.types.types.clone(),
            ctors: self.types.ctors.clone(),
        };
        let mut checker = Checker::new(&mut ts, &self.data, &empty);
        let Ok(checked) = checker.check_seq(&bindings, Some(&expr)) else {
            return false;
        };
        let Some(read) = checked.ty else {
            return false;
        };
        alpha_equal(&read, ty)
    }

    /// The type of an expression, generalized as a binding would be, for
    /// `:type`.
    pub fn type_of(&mut self, src: &str) -> GrundyResult<String> {
        let expr = parse_expr(src)?;
        let binding = super::syntax::ast::Binding {
            pat: super::syntax::ast::Pat::new(
                super::syntax::ast::PatKind::Var("it".to_string()),
                expr.span,
            ),
            kind: super::syntax::ast::BindKind::Let,
            span: expr.span,
            expr,
        };
        let mut checker = Checker::new(&mut self.ts, &self.data, &self.types);
        let checked = checker.check_seq(&[binding], None)?;
        let (_, scheme) = checked.defined.into_iter().next().expect("one binding");
        Ok(show_scheme(&scheme, &self.data))
    }

    /// Every global with its scheme, for `:env`.
    pub fn env(&self) -> Vec<(String, String)> {
        self.types
            .values
            .iter()
            .map(|(name, scheme)| (name.clone(), show_scheme(scheme, &self.data)))
            .collect()
    }
}

/// Type equality up to renaming of variables.
pub fn alpha_equal(a: &Ty, b: &Ty) -> bool {
    fn go(a: &Ty, b: &Ty, map: &mut BTreeMap<u32, u32>, back: &mut BTreeMap<u32, u32>) -> bool {
        match (a, b) {
            (Ty::Var(x), Ty::Var(y)) => {
                let fwd = *map.entry(*x).or_insert(*y);
                let bwd = *back.entry(*y).or_insert(*x);
                fwd == *y && bwd == *x
            }
            (Ty::Con(c, xs), Ty::Con(d, ys)) => {
                c == d
                    && xs.len() == ys.len()
                    && xs.iter().zip(ys).all(|(x, y)| go(x, y, map, back))
            }
            (Ty::Fun(xs, r), Ty::Fun(ys, s)) => {
                xs.len() == ys.len()
                    && xs.iter().zip(ys).all(|(x, y)| go(x, y, map, back))
                    && go(r, s, map, back)
            }
            _ => false,
        }
    }
    go(a, b, &mut BTreeMap::new(), &mut BTreeMap::new())
}

#[cfg(test)]
mod tests;

thread_local! {
    static CONTAINING: Cell<bool> = const { Cell::new(false) };
}

/// Whether a panic message is an exact backend's documented coefficient
/// overflow, as opposed to a defect.
fn engine_overflow(message: &str) -> bool {
    message.contains("overflowed i128") || message.contains("overflows u128")
}

/// Run a statement, turning the exact backends' fixed-width coefficient
/// overflow into `E_Overflow`. The statement commits nothing; any other
/// panic propagates unchanged.
fn contain_overflow<T>(span: Span, f: impl FnOnce() -> GrundyResult<T>) -> GrundyResult<T> {
    static QUIET_HOOK: Once = Once::new();
    QUIET_HOOK.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            let contained =
                CONTAINING.with(Cell::get) && info.payload_as_str().is_some_and(engine_overflow);
            if !contained {
                previous(info);
            }
        }));
    });
    let outer = CONTAINING.with(|c| c.replace(true));
    let outcome = catch_unwind(AssertUnwindSafe(f));
    CONTAINING.with(|c| c.set(outer));
    match outcome {
        Ok(result) => result,
        Err(payload) => {
            let message = payload
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| payload.downcast_ref::<&str>().copied());
            match message {
                Some(message) if engine_overflow(message) => Err(GrundyError::new(
                    GrundyErrorKind::Overflow,
                    span,
                    format!("exact arithmetic exceeds its fixed-width coefficients ({message})"),
                )
                .with_hint(
                    "Surreal, Omnific, and Int[t] coefficients are i128 rationals and integers",
                )),
                _ => resume_unwind(payload),
            }
        }
    }
}
