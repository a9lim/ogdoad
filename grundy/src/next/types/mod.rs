//! Types, built-in classes, unification, and defaulting.
//!
//! Inference is Damas–Milner with level-based generalization and a fixed set
//! of built-in classes (no user instances). Literal classes default through
//! the order [`DEFAULT_ORDER`]; defaulting is static and never retried after
//! a value-level failure.

pub mod infer;

#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use super::error::{err, GrundyError, GrundyErrorKind, GrundyResult};

/// A unification variable, unique within a session.
pub type TyVar = u32;

/// Index of a user data declaration in the session registry.
pub type DataId = u32;

/// Type constructors.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TyCon {
    /// ℤ as checked `i128`.
    Int,
    /// Verdicts.
    Bool,
    /// Short game values in sealed canonical form.
    Game,
    /// Presented games: finite trees or finite cyclic graphs.
    Form,
    /// `Left | Right | Draw`.
    Winner,
    /// Evidence data awaiting verification.
    Witness,
    /// A verified statement.
    Claim,
    /// A sampled misère quotient.
    Quotient,
    /// Finite nimbers `F_{2^128}`.
    Nimber,
    /// Ordinal nimbers `On₂`.
    Ordinal,
    /// Surreal numbers (finite Hahn support).
    Surreal,
    /// Omnific integers.
    Omnific,
    /// `F_p` for `p ∈ {2, 3, 5, 7}`.
    Fp(u8),
    /// `F_{p^n}`: F4, F8, F16, F9, F27, F25.
    Fpn(u8, u8),
    /// `List(a)`.
    List,
    /// An n-tuple.
    Tuple(u8),
    /// `Option(a)`.
    Option,
    /// `Rules(s)`.
    Rules,
    /// `Bounded(a)`.
    Bounded,
    /// `S[t]`.
    Poly,
    /// `S(t)`.
    RatFunc,
    /// `Algebra(S)`.
    Algebra,
    /// `Mv(S)`.
    Mv,
    /// A user data type.
    Data(DataId),
}

/// Types.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Ty {
    /// A unification variable.
    Var(TyVar),
    /// A constructor applied to arguments.
    Con(TyCon, Vec<Ty>),
    /// A function of fixed arity.
    Fun(Vec<Ty>, Box<Ty>),
}

impl Ty {
    /// A nullary constructor.
    pub fn con(con: TyCon) -> Ty {
        Ty::Con(con, Vec::new())
    }

    /// `List(a)`.
    pub fn list(elem: Ty) -> Ty {
        Ty::Con(TyCon::List, vec![elem])
    }

    /// An n-tuple.
    pub fn tuple(items: Vec<Ty>) -> Ty {
        Ty::Con(TyCon::Tuple(items.len() as u8), items)
    }

    /// `Int`.
    pub fn int() -> Ty {
        Ty::con(TyCon::Int)
    }

    /// `Bool`.
    pub fn bool() -> Ty {
        Ty::con(TyCon::Bool)
    }

    /// `Game`.
    pub fn game() -> Ty {
        Ty::con(TyCon::Game)
    }

    /// `Form`.
    pub fn form() -> Ty {
        Ty::con(TyCon::Form)
    }

    fn free_vars(&self, out: &mut BTreeSet<TyVar>) {
        match self {
            Ty::Var(v) => {
                out.insert(*v);
            }
            Ty::Con(_, args) => args.iter().for_each(|arg| arg.free_vars(out)),
            Ty::Fun(args, ret) => {
                args.iter().for_each(|arg| arg.free_vars(out));
                ret.free_vars(out);
            }
        }
    }

    /// Free variables in order of first occurrence.
    pub fn vars(&self) -> BTreeSet<TyVar> {
        let mut out = BTreeSet::new();
        self.free_vars(&mut out);
        out
    }

    /// Substitute variables.
    pub fn subst(&self, map: &BTreeMap<TyVar, Ty>) -> Ty {
        match self {
            Ty::Var(v) => map.get(v).cloned().unwrap_or(Ty::Var(*v)),
            Ty::Con(con, args) => Ty::Con(*con, args.iter().map(|arg| arg.subst(map)).collect()),
            Ty::Fun(args, ret) => Ty::Fun(
                args.iter().map(|arg| arg.subst(map)).collect(),
                Box::new(ret.subst(map)),
            ),
        }
    }
}

/// Built-in classes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Class {
    /// `=`
    Eq,
    /// `< > ≤ ≥ ∥` (partial orders).
    Ord,
    /// `+ -` and unary `-`.
    Add,
    /// `⋅` and `↑` by `Int`.
    Mul,
    /// `/` and unary `/`.
    Div,
    /// `%`.
    Rem,
    /// `∧`.
    Wedge,
    /// Usable as a ruleset position: structural equality, hashing, and order.
    Key,
    /// Numerals.
    IntLit,
    /// `*n`.
    StarLit,
    /// Literal-shaped `a/b`.
    FracLit,
    /// `ω`.
    OmegaLit,
    /// Game literals, brace forms, and outcome doubles: `Game` or `Form`.
    GameLike,
    /// Embeddable into `Game` by `game(x)`: Int, Nimber, Surreal, Game.
    IntoGame,
}

impl Class {
    /// The class name as displayed.
    pub fn name(self) -> &'static str {
        match self {
            Class::Eq => "Eq",
            Class::Ord => "Ord",
            Class::Add => "Add",
            Class::Mul => "Mul",
            Class::Div => "Div",
            Class::Rem => "Rem",
            Class::Wedge => "Wedge",
            Class::Key => "Key",
            Class::IntLit => "IntLit",
            Class::StarLit => "StarLit",
            Class::FracLit => "FracLit",
            Class::OmegaLit => "OmegaLit",
            Class::GameLike => "GameLike",
            Class::IntoGame => "IntoGame",
        }
    }
}

/// A class predicate.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Pred {
    /// `C a`.
    Is(Class, Ty),
    /// `a ↑ e` is defined: `e = Int` with `Mul a`, or `a = e = Surreal`.
    Pow(Ty, Ty),
}

impl Pred {
    fn vars(&self) -> BTreeSet<TyVar> {
        match self {
            Pred::Is(_, ty) => ty.vars(),
            Pred::Pow(a, e) => {
                let mut out = a.vars();
                out.extend(e.vars());
                out
            }
        }
    }

    fn subst(&self, map: &BTreeMap<TyVar, Ty>) -> Pred {
        match self {
            Pred::Is(class, ty) => Pred::Is(*class, ty.subst(map)),
            Pred::Pow(a, e) => Pred::Pow(a.subst(map), e.subst(map)),
        }
    }
}

/// A type scheme `∀ vars. preds ⇒ ty`.
#[derive(Clone, Debug, PartialEq)]
pub struct Scheme {
    /// Quantified variables.
    pub vars: Vec<TyVar>,
    /// Constraints on them.
    pub preds: Vec<Pred>,
    /// The body.
    pub ty: Ty,
}

impl Scheme {
    /// A monomorphic scheme.
    pub fn mono(ty: Ty) -> Scheme {
        Scheme {
            vars: Vec::new(),
            preds: Vec::new(),
            ty,
        }
    }
}

/// The candidates an ambiguous literal variable defaults through, in order.
pub const DEFAULT_ORDER: [TyCon; 5] = [
    TyCon::Int,
    TyCon::Game,
    TyCon::Nimber,
    TyCon::Surreal,
    TyCon::Form,
];

/// A user data declaration as the checker sees it.
#[derive(Clone, Debug)]
pub struct DataInfo {
    /// The type name.
    pub name: String,
    /// Constructors: name and field types.
    pub ctors: Vec<(String, Vec<Ty>)>,
    /// Whether values support `=` and `Key` (no function fields).
    pub plain: bool,
}

/// Session-wide registry of data declarations.
#[derive(Clone, Debug, Default)]
pub struct DataRegistry {
    /// Declarations by id.
    pub decls: Vec<DataInfo>,
}

impl DataRegistry {
    /// The declaration for an id.
    pub fn get(&self, id: DataId) -> &DataInfo {
        &self.decls[id as usize]
    }
}

/// Unifier state: variable bindings with levels, and pending predicates.
#[derive(Clone, Debug, Default)]
pub struct TypeState {
    bindings: Vec<Option<Ty>>,
    levels: Vec<u32>,
    /// The current let-nesting level.
    pub level: u32,
    /// Predicates not yet discharged.
    pub preds: Vec<Pred>,
}

impl TypeState {
    /// A fresh variable at the current level.
    pub fn fresh(&mut self) -> Ty {
        let id = self.bindings.len() as TyVar;
        self.bindings.push(None);
        self.levels.push(self.level);
        Ty::Var(id)
    }

    /// Resolve the head of a type through bindings.
    pub fn shallow(&self, ty: &Ty) -> Ty {
        let mut ty = ty.clone();
        while let Ty::Var(v) = ty {
            match &self.bindings[v as usize] {
                Some(bound) => ty = bound.clone(),
                None => return Ty::Var(v),
            }
        }
        ty
    }

    /// Fully apply the current substitution.
    pub fn zonk(&self, ty: &Ty) -> Ty {
        match self.shallow(ty) {
            Ty::Var(v) => Ty::Var(v),
            Ty::Con(con, args) => Ty::Con(con, args.iter().map(|arg| self.zonk(arg)).collect()),
            Ty::Fun(args, ret) => Ty::Fun(
                args.iter().map(|arg| self.zonk(arg)).collect(),
                Box::new(self.zonk(&ret)),
            ),
        }
    }

    fn zonk_pred(&self, pred: &Pred) -> Pred {
        match pred {
            Pred::Is(class, ty) => Pred::Is(*class, self.zonk(ty)),
            Pred::Pow(a, e) => Pred::Pow(self.zonk(a), self.zonk(e)),
        }
    }

    fn occurs_and_adjust(&mut self, var: TyVar, ty: &Ty, level: u32) -> bool {
        match self.shallow(ty) {
            Ty::Var(v) => {
                if v == var {
                    return true;
                }
                let slot = &mut self.levels[v as usize];
                *slot = (*slot).min(level);
                false
            }
            Ty::Con(_, args) => args
                .iter()
                .any(|arg| self.occurs_and_adjust(var, arg, level)),
            Ty::Fun(args, ret) => {
                args.iter()
                    .any(|arg| self.occurs_and_adjust(var, arg, level))
                    || self.occurs_and_adjust(var, &ret, level)
            }
        }
    }

    /// Unify two types.
    pub fn unify(&mut self, a: &Ty, b: &Ty, data: &DataRegistry) -> GrundyResult<()> {
        let a = self.shallow(a);
        let b = self.shallow(b);
        match (&a, &b) {
            (Ty::Var(x), Ty::Var(y)) if x == y => Ok(()),
            (Ty::Var(x), other) | (other, Ty::Var(x)) => {
                let level = self.levels[*x as usize];
                if self.occurs_and_adjust(*x, other, level) {
                    return Err(err(
                        GrundyErrorKind::Type,
                        format!(
                            "infinite type: {} occurs in {}",
                            self.show(&Ty::Var(*x), data),
                            self.show(other, data)
                        ),
                    ));
                }
                self.bindings[*x as usize] = Some(other.clone());
                Ok(())
            }
            (Ty::Con(c1, a1), Ty::Con(c2, a2)) if c1 == c2 && a1.len() == a2.len() => {
                for (x, y) in a1.iter().zip(a2) {
                    self.unify(x, y, data)
                        .map_err(|_| self.mismatch(&a, &b, data))?;
                }
                Ok(())
            }
            (Ty::Fun(p1, r1), Ty::Fun(p2, r2)) if p1.len() == p2.len() => {
                for (x, y) in p1.iter().zip(p2) {
                    self.unify(x, y, data)
                        .map_err(|_| self.mismatch(&a, &b, data))?;
                }
                self.unify(r1, r2, data)
                    .map_err(|_| self.mismatch(&a, &b, data))
            }
            (Ty::Fun(p1, _), Ty::Fun(p2, _)) => Err(err(
                GrundyErrorKind::Arity,
                format!(
                    "a function of {} argument{} where one of {} is expected",
                    p1.len(),
                    if p1.len() == 1 { "" } else { "s" },
                    p2.len()
                ),
            )),
            _ => Err(self.mismatch(&a, &b, data)),
        }
    }

    fn mismatch(&self, a: &Ty, b: &Ty, data: &DataRegistry) -> GrundyError {
        let a = self.zonk(a);
        let b = self.zonk(b);
        let mut names = VarNames::default();
        let mut error = err(
            GrundyErrorKind::Type,
            format!(
                "type mismatch: {} vs {}",
                show_ty(&a, data, &mut names),
                show_ty(&b, data, &mut names)
            ),
        );
        if let Some(hint) = mismatch_hint(&a, &b) {
            error = error.with_hint(hint);
        }
        error
    }

    /// Show a type with fresh variable names.
    pub fn show(&self, ty: &Ty, data: &DataRegistry) -> String {
        show_ty(&self.zonk(ty), data, &mut VarNames::default())
    }

    /// Record a predicate, reducing it as far as its head allows.
    pub fn require(&mut self, pred: Pred, data: &DataRegistry) -> GrundyResult<()> {
        let mut work = vec![pred];
        while let Some(pred) = work.pop() {
            match self.reduce(&pred, data)? {
                Reduced::Done(subgoals) => work.extend(subgoals),
                Reduced::Stuck => self.preds.push(self.zonk_pred(&pred)),
            }
        }
        Ok(())
    }

    fn reduce(&mut self, pred: &Pred, data: &DataRegistry) -> GrundyResult<Reduced> {
        match pred {
            Pred::Is(class, ty) => {
                let head = self.shallow(ty);
                match &head {
                    Ty::Var(_) => Ok(Reduced::Stuck),
                    _ => match instance(*class, &head, data) {
                        Some(subgoals) => Ok(Reduced::Done(subgoals)),
                        None => Err(no_instance(*class, &self.zonk(&head), data)),
                    },
                }
            }
            Pred::Pow(base, exponent) => {
                let base_head = self.shallow(base);
                let exponent_head = self.shallow(exponent);
                match (&base_head, &exponent_head) {
                    (_, Ty::Con(TyCon::Int, _)) => {
                        Ok(Reduced::Done(vec![Pred::Is(Class::Mul, base_head)]))
                    }
                    (_, Ty::Con(TyCon::Surreal, _)) => {
                        self.unify(&base_head, &Ty::con(TyCon::Surreal), data)
                            .map_err(|_| {
                                err(
                                    GrundyErrorKind::Type,
                                    "a Surreal exponent needs the base `ω`",
                                )
                                .with_hint("exponents are Int, except `ω↑s` in Surreal")
                            })?;
                        Ok(Reduced::Done(Vec::new()))
                    }
                    (Ty::Con(TyCon::Surreal, _), Ty::Var(_)) => Ok(Reduced::Stuck),
                    (Ty::Con(..) | Ty::Fun(..), Ty::Var(_)) => {
                        // Only Surreal admits non-Int exponents, so the
                        // exponent of any other base is Int.
                        self.unify(&exponent_head, &Ty::int(), data)?;
                        Ok(Reduced::Done(vec![Pred::Is(Class::Mul, base_head)]))
                    }
                    (Ty::Var(_), Ty::Var(_)) => Ok(Reduced::Stuck),
                    (_, other) => Err(err(
                        GrundyErrorKind::Type,
                        format!("exponents are Int, not {}", self.show(other, data)),
                    )
                    .with_hint("`↑`/`^` is power; the wedge product is `∧`/`&`")),
                }
            }
        }
    }

    /// Re-reduce pending predicates after new bindings.
    pub fn simplify(&mut self, data: &DataRegistry) -> GrundyResult<()> {
        let pending = std::mem::take(&mut self.preds);
        for pred in pending {
            self.require(pred, data)?;
        }
        self.dedup_preds();
        Ok(())
    }

    fn dedup_preds(&mut self) {
        let mut seen = BTreeSet::new();
        let preds = std::mem::take(&mut self.preds);
        for pred in preds {
            let pred = self.zonk_pred(&pred);
            if seen.insert(pred.clone()) {
                self.preds.push(pred);
            }
        }
    }

    /// Generalize `ty` over variables above the current level, taking the
    /// predicates on them. When `constrained` is false (a value binding),
    /// constrained variables stay monomorphic and their predicates pending.
    pub fn generalize(
        &mut self,
        ty: &Ty,
        constrained: bool,
        data: &DataRegistry,
    ) -> GrundyResult<Scheme> {
        self.simplify(data)?;
        let level = self.level;
        let type_vars = self.zonk(ty).vars();
        // A local variable that appears only in predicates can never be
        // determined from outside: default it now.
        let ambiguous: BTreeSet<TyVar> = self
            .preds
            .iter()
            .flat_map(Pred::vars)
            .filter(|v| self.levels[*v as usize] > level && !type_vars.contains(v))
            .collect();
        if !ambiguous.is_empty() {
            self.default_vars(&ambiguous, data)?;
            self.simplify(data)?;
        }
        let ty = self.zonk(ty);
        let mut quantified: BTreeSet<TyVar> = ty
            .vars()
            .into_iter()
            .filter(|v| self.levels[*v as usize] > level)
            .collect();
        if !constrained {
            for pred in &self.preds {
                for v in pred.vars() {
                    quantified.remove(&v);
                }
            }
        }
        let mut attached = Vec::new();
        let mut kept = Vec::new();
        for pred in std::mem::take(&mut self.preds) {
            if pred.vars().iter().any(|v| quantified.contains(v)) {
                attached.push(pred);
            } else {
                kept.push(pred);
            }
        }
        self.preds = kept;
        // Unquantified local variables now belong to the enclosing scope.
        for (v, slot) in self.levels.iter_mut().enumerate() {
            if *slot > level && !quantified.contains(&(v as TyVar)) {
                *slot = level;
            }
        }
        Ok(Scheme {
            vars: quantified.into_iter().collect(),
            preds: attached,
            ty,
        })
    }

    /// Instantiate a scheme with fresh variables, adding its predicates.
    pub fn instantiate(
        &mut self,
        scheme: &Scheme,
        data: &DataRegistry,
    ) -> GrundyResult<(Ty, Vec<Ty>)> {
        let mut map = BTreeMap::new();
        let mut args = Vec::new();
        for v in &scheme.vars {
            let fresh = self.fresh();
            args.push(fresh.clone());
            map.insert(*v, fresh);
        }
        for pred in &scheme.preds {
            self.require(pred.subst(&map), data)?;
        }
        Ok((scheme.ty.subst(&map), args))
    }

    /// Default every variable that carries a predicate: at the end of a
    /// top-level statement.
    pub fn default_all(&mut self, data: &DataRegistry) -> GrundyResult<()> {
        loop {
            self.simplify(data)?;
            let vars: BTreeSet<TyVar> = self.preds.iter().flat_map(Pred::vars).collect();
            if vars.is_empty() {
                return Ok(());
            }
            self.default_vars(&vars, data)?;
            self.simplify(data)?;
            let remaining: BTreeSet<TyVar> = self.preds.iter().flat_map(Pred::vars).collect();
            if remaining == vars {
                return Err(self.ambiguity(&remaining, data));
            }
        }
    }

    fn default_vars(&mut self, vars: &BTreeSet<TyVar>, data: &DataRegistry) -> GrundyResult<()> {
        for &v in vars {
            if !matches!(self.shallow(&Ty::Var(v)), Ty::Var(_)) {
                continue;
            }
            let on_v: Vec<Pred> = self
                .preds
                .iter()
                .filter(|pred| pred.vars().contains(&v))
                .cloned()
                .collect();
            if on_v.is_empty() {
                continue;
            }
            let mut chosen = None;
            for candidate in DEFAULT_ORDER {
                let mut trial = self.clone();
                let ok = trial.unify(&Ty::Var(v), &Ty::con(candidate), data).is_ok()
                    && trial.simplify(data).is_ok()
                    && on_v.iter().all(|pred| trial.satisfiable(pred, data));
                if ok {
                    chosen = Some(candidate);
                    break;
                }
            }
            match chosen {
                Some(candidate) => {
                    self.unify(&Ty::Var(v), &Ty::con(candidate), data)?;
                }
                None => {
                    let only: BTreeSet<TyVar> = [v].into_iter().collect();
                    return Err(self.ambiguity(&only, data));
                }
            }
        }
        Ok(())
    }

    fn satisfiable(&self, pred: &Pred, data: &DataRegistry) -> bool {
        let mut trial = self.clone();
        trial.preds.clear();
        if trial.require(self.zonk_pred(pred), data).is_err() {
            return false;
        }
        // Remaining predicates must each be satisfiable by some candidate.
        trial.preds.iter().all(|pending| match pending {
            Pred::Pow(_, _) => true,
            Pred::Is(class, Ty::Var(_)) => DEFAULT_ORDER
                .iter()
                .any(|candidate| instance(*class, &Ty::con(*candidate), data).is_some()),
            Pred::Is(..) => true,
        })
    }

    fn ambiguity(&self, vars: &BTreeSet<TyVar>, data: &DataRegistry) -> GrundyError {
        let preds: Vec<String> = self
            .preds
            .iter()
            .filter(|pred| pred.vars().iter().any(|v| vars.contains(v)))
            .map(|pred| show_pred(pred, data, &mut VarNames::default()))
            .collect();
        let game_ring = self.preds.iter().any(|pred| {
            matches!(pred, Pred::Is(Class::GameLike, Ty::Var(v)) if vars.contains(v))
        }) && self.preds.iter().any(|pred| {
            matches!(pred, Pred::Is(Class::Mul | Class::Div, Ty::Var(v)) if vars.contains(v))
        });
        err(
            GrundyErrorKind::Ambiguous,
            format!(
                "no type satisfies {} among the defaults Int, Game, Nimber, Surreal, Form",
                preds.join(", ")
            ),
        )
        .with_hint(if game_ring {
            "games are an additive group, not a ring"
        } else {
            "annotate the intended type: `(e : Surreal)`"
        })
    }

    /// Whether a variable is still unbound.
    pub fn is_unbound(&self, v: TyVar) -> bool {
        matches!(self.shallow(&Ty::Var(v)), Ty::Var(_))
    }

    /// The level of a variable.
    pub fn var_level(&self, v: TyVar) -> u32 {
        self.levels[v as usize]
    }

    /// Discard predicates (after a failed statement).
    pub fn reset_pending(&mut self) {
        self.preds.clear();
        self.level = 0;
    }
}

enum Reduced {
    Done(Vec<Pred>),
    Stuck,
}

fn no_instance(class: Class, ty: &Ty, data: &DataRegistry) -> GrundyError {
    let shown = show_ty(ty, data, &mut VarNames::default());
    let message = match class {
        Class::IntLit => format!("{shown} has no integer literals"),
        Class::StarLit => format!("{shown} has no star literals"),
        Class::FracLit => format!("{shown} has no fraction literals"),
        Class::OmegaLit => format!("{shown} has no `ω`"),
        Class::GameLike => format!("{shown} is not a game type"),
        Class::Add => format!("{shown} has no `+`"),
        Class::Mul => format!("{shown} has no `⋅`"),
        Class::Div => format!("{shown} has no `/`"),
        Class::Rem => format!("{shown} has no `%`"),
        Class::Wedge => format!("{shown} has no `∧`"),
        Class::Ord => format!("{shown} has no order"),
        Class::Eq => format!("{shown} has no `=`"),
        Class::Key => format!("{shown} cannot be a ruleset position"),
        Class::IntoGame => format!("{shown} does not embed into Game"),
    };
    let mut error = err(GrundyErrorKind::Type, message);
    let hint = match (class, ty) {
        (Class::IntLit, Ty::Con(TyCon::Nimber | TyCon::Ordinal, _)) => {
            Some("nimbers are written `*3`; `from_int` would collapse 3 to 1 in characteristic two")
        }
        (Class::Mul | Class::Div, Ty::Con(TyCon::Game | TyCon::Form, _)) => {
            Some("games are an additive group, not a ring")
        }
        (Class::Wedge, Ty::Con(TyCon::Game | TyCon::Form, _)) => {
            Some("the exterior product needs a Clifford algebra; lists concatenate with `⧺`")
        }
        (Class::FracLit, Ty::Con(TyCon::Int, _)) => {
            Some("Int has no fractions; integer quotients are `div(a, b)`")
        }
        (Class::Div, Ty::Con(TyCon::Int, _)) => Some("integer quotients are `div(a, b)`"),
        (Class::Ord, Ty::Con(TyCon::Fp(_) | TyCon::Fpn(..), _)) => {
            Some("finite fields have no order")
        }
        _ => None,
    };
    if let Some(hint) = hint {
        error = error.with_hint(hint);
    }
    error
}

/// The instance table: `Some(subgoals)` if `class` holds for the head of `ty`.
pub fn instance(class: Class, ty: &Ty, data: &DataRegistry) -> Option<Vec<Pred>> {
    use Class::*;
    use TyCon as T;
    let Ty::Con(con, args) = ty else {
        return None;
    };
    let yes = || Some(Vec::new());
    let each = |class: Class| {
        Some(
            args.iter()
                .map(|arg| Pred::Is(class, arg.clone()))
                .collect(),
        )
    };
    match (con, class) {
        (T::Int | T::Nimber | T::Surreal | T::Game, IntoGame) => yes(),
        (T::Int, Eq | Ord | Add | Mul | Rem | Key | IntLit) => yes(),
        (T::Bool, Eq | Key) => yes(),
        (T::Winner, Eq | Key) => yes(),
        (T::Game, Eq | Ord | Add | Key | IntLit | StarLit | FracLit | GameLike) => yes(),
        (T::Form, Eq | Ord | Add | IntLit | StarLit | FracLit | GameLike) => yes(),
        (T::Nimber | T::Ordinal, Eq | Ord | Add | Mul | Div | Key | StarLit) => yes(),
        (T::Surreal, Eq | Ord | Add | Mul | Div | Rem | Key | IntLit | FracLit | OmegaLit) => yes(),
        (T::Omnific, Eq | Ord | Add | Mul | Div | Rem | Key | IntLit | OmegaLit) => yes(),
        (T::Fp(_) | T::Fpn(..), Eq | Add | Mul | Div | Key | IntLit | FracLit) => yes(),
        (T::Poly, Eq | Add | Mul | Div | Rem | Key) => yes(),
        (T::Poly, IntLit | FracLit) => each(class),
        (T::RatFunc, Eq | Add | Mul | Div | Key | IntLit | FracLit) => yes(),
        (T::Mv, Eq | Add | Mul | Div | Wedge) => yes(),
        (T::Mv, IntLit | StarLit | FracLit | OmegaLit) => each(class),
        (T::List | T::Tuple(_) | T::Option, Eq | Key) => each(class),
        (T::Data(id), Eq | Key) => data.get(*id).plain.then(Vec::new),
        _ => None,
    }
}

fn mismatch_hint(a: &Ty, b: &Ty) -> Option<&'static str> {
    use TyCon as T;
    let pair = |x: TyCon, y: TyCon| matches!((a, b), (Ty::Con(p, _), Ty::Con(q, _)) if (*p == x && *q == y) || (*p == y && *q == x));
    if pair(T::Int, T::Game) {
        Some("integers and games are different types; `game(n)` embeds an Int")
    } else if pair(T::Nimber, T::Game) {
        Some("`game(*n)` embeds a Nimber; `nimber(g)` reads a nimber-valued game")
    } else if pair(T::Game, T::Form) {
        Some("`form(g)` presents a value; `canon(f)` reads a finite form's value")
    } else if pair(T::Bool, T::Int) {
        Some("Bool is a verdict, not a number")
    } else {
        None
    }
}

/// Assigns `a, b, c, …` to type variables in order of appearance.
#[derive(Default)]
pub struct VarNames {
    names: BTreeMap<TyVar, String>,
}

impl VarNames {
    fn name(&mut self, v: TyVar) -> String {
        let next = self.names.len();
        self.names
            .entry(v)
            .or_insert_with(|| {
                let letter = (b'a' + (next % 26) as u8) as char;
                if next < 26 {
                    letter.to_string()
                } else {
                    format!("{letter}{}", next / 26)
                }
            })
            .clone()
    }
}

/// Render a type.
pub fn show_ty(ty: &Ty, data: &DataRegistry, names: &mut VarNames) -> String {
    match ty {
        Ty::Var(v) => names.name(*v),
        Ty::Fun(args, ret) => {
            let args_text = match args.as_slice() {
                [single] if !matches!(single, Ty::Fun(..)) && !is_tuple(single) => {
                    show_ty(single, data, names)
                }
                _ => format!(
                    "({})",
                    args.iter()
                        .map(|arg| show_ty(arg, data, names))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            };
            format!("{args_text} → {}", show_ty(ret, data, names))
        }
        Ty::Con(con, args) => {
            let arg = |i: usize, names: &mut VarNames| show_ty(&args[i], data, names);
            match con {
                TyCon::Int => "Int".into(),
                TyCon::Bool => "Bool".into(),
                TyCon::Game => "Game".into(),
                TyCon::Form => "Form".into(),
                TyCon::Winner => "Winner".into(),
                TyCon::Witness => "Witness".into(),
                TyCon::Claim => "Claim".into(),
                TyCon::Quotient => format!("Quotient({})", arg(0, names)),
                TyCon::Nimber => "Nimber".into(),
                TyCon::Ordinal => "Ordinal".into(),
                TyCon::Surreal => "Surreal".into(),
                TyCon::Omnific => "Omnific".into(),
                TyCon::Fp(p) => format!("F{p}"),
                TyCon::Fpn(p, n) => format!("F{}", (*p as u32).pow(*n as u32)),
                TyCon::List => format!("List({})", arg(0, names)),
                TyCon::Option => format!("Option({})", arg(0, names)),
                TyCon::Rules => format!("Rules({})", arg(0, names)),
                TyCon::Bounded => format!("Bounded({})", arg(0, names)),
                TyCon::Algebra => format!("Algebra({})", arg(0, names)),
                TyCon::Mv => format!("Mv({})", arg(0, names)),
                TyCon::Poly => format!("{}[t]", arg(0, names)),
                TyCon::RatFunc => format!("{}(t)", arg(0, names)),
                TyCon::Tuple(_) => format!(
                    "({})",
                    args.iter()
                        .map(|arg| show_ty(arg, data, names))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                TyCon::Data(id) => data.get(*id).name.clone(),
            }
        }
    }
}

fn is_tuple(ty: &Ty) -> bool {
    matches!(ty, Ty::Con(TyCon::Tuple(_), _))
}

/// Render a predicate.
pub fn show_pred(pred: &Pred, data: &DataRegistry, names: &mut VarNames) -> String {
    match pred {
        Pred::Is(class, ty) => format!("{} {}", class.name(), show_ty(ty, data, names)),
        Pred::Pow(a, e) => format!(
            "Pow {} {}",
            show_ty(a, data, names),
            show_ty(e, data, names)
        ),
    }
}

/// Render a scheme: `Add a, IntLit a ⇒ a → a`.
pub fn show_scheme(scheme: &Scheme, data: &DataRegistry) -> String {
    let mut names = VarNames::default();
    let ty = show_ty(&scheme.ty, data, &mut names);
    if scheme.preds.is_empty() {
        return ty;
    }
    let mut preds: Vec<String> = scheme
        .preds
        .iter()
        .map(|pred| show_pred(pred, data, &mut names))
        .collect();
    preds.sort();
    preds.dedup();
    format!("{} ⇒ {ty}", preds.join(", "))
}

impl fmt::Display for Class {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}
