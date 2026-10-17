//! Syntax trees. Every node carries the source span it was parsed from;
//! [`Unspan`] erases spans so trees compare modulo source positions.

use super::super::error::Span;

/// An identifier or constructor name.
pub type Name = String;

/// One of the nine outcome cells: the result when Left starts, then the
/// result when Right starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OutcomeCell {
    /// Result when Left moves first.
    pub left_first: Mover,
    /// Result when Right moves first.
    pub right_first: Mover,
}

/// A mover-result atom inside an outcome double.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Mover {
    /// `>`: Left wins.
    Left,
    /// `<`: Right wins.
    Right,
    /// `‿`: the game is drawn.
    Draw,
}

impl Mover {
    /// The canonical glyph.
    pub fn glyph(self) -> char {
        match self {
            Mover::Left => '>',
            Mover::Right => '<',
            Mover::Draw => '‿',
        }
    }

    /// The atom for a glyph, accepting the `_` sugar for `‿`.
    pub fn from_glyph(ch: char) -> Option<Mover> {
        match ch {
            '>' => Some(Mover::Left),
            '<' => Some(Mover::Right),
            '‿' | '_' => Some(Mover::Draw),
            _ => None,
        }
    }
}

impl OutcomeCell {
    /// The canonical two-glyph spelling.
    pub fn glyphs(self) -> String {
        format!("{}{}", self.left_first.glyph(), self.right_first.glyph())
    }
}

/// A star literal's index: a finite integer or a Cantor normal form ordinal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StarIndex {
    /// `*n` (bare `*` is `*1`).
    Finite(u128),
    /// `*ω`.
    Omega,
    /// `*(cnf)`: strictly descending `ω↑e⋅c` terms.
    Cnf(Vec<CnfTerm>),
}

/// One `ω↑exponent⋅coefficient` term of a structural CNF index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CnfTerm {
    /// The exponent; `None` for a finite term.
    pub exponent: Option<CnfExponent>,
    /// The coefficient (at least one).
    pub coefficient: u128,
}

/// A CNF exponent: a finite integer, `ω`, or a nested CNF.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CnfExponent {
    /// A finite exponent.
    Finite(u128),
    /// `ω`.
    Omega,
    /// A parenthesized nested CNF.
    Cnf(Vec<CnfTerm>),
}

/// Unary operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    /// `-a`, filling `0 - a`.
    Neg,
    /// `/a`, filling `1/a`.
    Recip,
    /// `not a`.
    Not,
}

/// Binary operators other than relations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `⋅`
    Mul,
    /// `/`
    Div,
    /// `%`
    Rem,
    /// `∧`
    Wedge,
    /// `↑`
    Pow,
    /// `⧺` list concatenation.
    Concat,
    /// `and` (short-circuit).
    And,
    /// `or` (short-circuit).
    Or,
}

/// Relation operators: non-chaining, Bool-valued.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelOp {
    /// `=`
    Eq,
    /// `<`
    Lt,
    /// `>`
    Gt,
    /// `≤`
    Le,
    /// `≥`
    Ge,
    /// `∥`
    Fuzzy,
    /// `≡` structural form equality.
    Equiv,
    /// One of the nine outcome doubles.
    Outcome(OutcomeCell),
}

/// An element of a list literal or brace side: an expression or a splice.
#[derive(Clone, Debug, PartialEq)]
pub enum Item {
    /// A single element.
    One(Expr),
    /// `..xs`: every element of a list.
    Splice(Expr),
}

/// A comprehension clause.
#[derive(Clone, Debug, PartialEq)]
pub enum Clause {
    /// `for pat in expr`.
    For(Pat, Expr),
    /// `if expr`.
    If(Expr),
}

/// A lambda parameter: a pattern with an optional type annotation.
#[derive(Clone, Debug, PartialEq)]
pub struct Param {
    /// The bound pattern.
    pub pat: Pat,
    /// An optional annotation.
    pub ty: Option<TypeExpr>,
}

/// An expression node.
#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    /// The node.
    pub kind: ExprKind,
    /// Its source span.
    pub span: Span,
}

/// Expression forms.
#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    /// A natural-number literal.
    Int(u128),
    /// A literal-shaped fraction `n/d` (sign carried by the numerator).
    Frac(i128, u128),
    /// `*n`, `*ω`, `*(cnf)`.
    Star(StarIndex),
    /// `ω`.
    Omega,
    /// `true` / `false`.
    Bool(bool),
    /// `up`.
    Up,
    /// `down`.
    Down,
    /// A lowercase variable.
    Var(Name),
    /// An uppercase constructor.
    Con(Name),
    /// `(a, b, …)` with at least two elements.
    Tuple(Vec<Expr>),
    /// `[a, ..xs, b]`.
    List(Vec<Item>),
    /// `[head for … if …]`.
    Comprehension(Box<Expr>, Vec<Clause>),
    /// `a .. b` or `a ..= b`.
    Range {
        /// Lower bound (inclusive).
        lo: Box<Expr>,
        /// Upper bound.
        hi: Box<Expr>,
        /// Whether the upper bound is included.
        inclusive: bool,
    },
    /// `{L | R}`.
    Form {
        /// Left options.
        left: Vec<Item>,
        /// Right options.
        right: Vec<Item>,
    },
    /// `f(a, b)`.
    Call(Box<Expr>, Vec<Expr>),
    /// `xs[i]`.
    Index(Box<Expr>, Box<Expr>),
    /// `params ↦ body`.
    Lambda(Vec<Param>, Box<Expr>),
    /// A unary operator.
    Unary(UnaryOp, Box<Expr>),
    /// A binary operator.
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    /// A relation.
    Relation(RelOp, Box<Expr>, Box<Expr>),
    /// `if c then a else b`.
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `match e { pat ↦ e, … }`.
    Match(Box<Expr>, Vec<(Pat, Expr)>),
    /// `(b1; b2; e)`: bindings scoped over a final expression.
    Block(Vec<Binding>, Box<Expr>),
    /// `e : T`.
    Annot(Box<Expr>, TypeExpr),
}

impl Expr {
    /// Construct a node.
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Expr { kind, span }
    }
}

/// Patterns.
#[derive(Clone, Debug, PartialEq)]
pub struct Pat {
    /// The node.
    pub kind: PatKind,
    /// Its source span.
    pub span: Span,
}

/// Pattern forms.
#[derive(Clone, Debug, PartialEq)]
pub enum PatKind {
    /// `_`.
    Wild,
    /// A variable.
    Var(Name),
    /// An integer literal, possibly negative.
    Int(i128),
    /// `true` / `false`.
    Bool(bool),
    /// `(p, q, …)`.
    Tuple(Vec<Pat>),
    /// `C` or `C(p, …)`.
    Con(Name, Vec<Pat>),
    /// `[p, q]` or `[p, ..rest]`.
    List(Vec<Pat>, Option<Box<Pat>>),
    /// `p : T`.
    Annot(Box<Pat>, TypeExpr),
}

impl Pat {
    /// Construct a node.
    pub fn new(kind: PatKind, span: Span) -> Self {
        Pat { kind, span }
    }

    /// The variables bound by the pattern, in order.
    pub fn binders(&self) -> Vec<&str> {
        let mut out = Vec::new();
        self.collect_binders(&mut out);
        out
    }

    fn collect_binders<'a>(&'a self, out: &mut Vec<&'a str>) {
        match &self.kind {
            PatKind::Var(name) => out.push(name),
            PatKind::Wild | PatKind::Int(_) | PatKind::Bool(_) => {}
            PatKind::Tuple(items) | PatKind::Con(_, items) => {
                for item in items {
                    item.collect_binders(out);
                }
            }
            PatKind::List(items, rest) => {
                for item in items {
                    item.collect_binders(out);
                }
                if let Some(rest) = rest {
                    rest.collect_binders(out);
                }
            }
            PatKind::Annot(inner, _) => inner.collect_binders(out),
        }
    }
}

/// Binding forms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindKind {
    /// `:=`
    Let,
    /// `=:`
    Rec,
}

/// One binding `pat := e` or `name =: e`.
#[derive(Clone, Debug, PartialEq)]
pub struct Binding {
    /// The bound pattern (a variable for `=:`).
    pub pat: Pat,
    /// `:=` or `=:`.
    pub kind: BindKind,
    /// The right-hand side.
    pub expr: Expr,
    /// The binding's span.
    pub span: Span,
}

/// A type expression in an annotation or data declaration.
#[derive(Clone, Debug, PartialEq)]
pub struct TypeExpr {
    /// The node.
    pub kind: TypeKind,
    /// Its source span.
    pub span: Span,
}

/// Type expression forms.
#[derive(Clone, Debug, PartialEq)]
pub enum TypeKind {
    /// `Name` or `Name(T, …)`.
    Named(Name, Vec<TypeExpr>),
    /// A polynomial ring `S[t]`.
    PolyRing(Name),
    /// A rational-function field `S(t)`.
    RatField(Name),
    /// `(A, B)` with at least two components.
    Tuple(Vec<TypeExpr>),
    /// `A → B` or `(A, B) → C`.
    Fun(Vec<TypeExpr>, Box<TypeExpr>),
    /// A lowercase type variable.
    Var(Name),
}

impl TypeExpr {
    /// Construct a node.
    pub fn new(kind: TypeKind, span: Span) -> Self {
        TypeExpr { kind, span }
    }
}

/// One constructor of a data declaration.
#[derive(Clone, Debug, PartialEq)]
pub struct CtorDecl {
    /// Constructor name.
    pub name: Name,
    /// Field types.
    pub fields: Vec<TypeExpr>,
    /// Source span.
    pub span: Span,
}

/// `data Name = C1 | C2(T, …)`.
#[derive(Clone, Debug, PartialEq)]
pub struct DataDecl {
    /// Type name.
    pub name: Name,
    /// Constructors in declaration order.
    pub ctors: Vec<CtorDecl>,
    /// Source span.
    pub span: Span,
}

/// A top-level statement.
#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    /// A data declaration.
    Data(DataDecl),
    /// Bindings, optionally followed by a final expression: `b1; b2; e`.
    Seq(Vec<Binding>, Option<Expr>),
}

/// Erase every span in a tree, for comparisons modulo source positions.
pub trait Unspan {
    /// Replace every span by the default.
    fn unspan(&mut self);
}

impl Unspan for Expr {
    fn unspan(&mut self) {
        self.span = Span::default();
        match &mut self.kind {
            ExprKind::Int(_)
            | ExprKind::Frac(..)
            | ExprKind::Star(_)
            | ExprKind::Omega
            | ExprKind::Bool(_)
            | ExprKind::Up
            | ExprKind::Down
            | ExprKind::Var(_)
            | ExprKind::Con(_) => {}
            ExprKind::Tuple(items) => items.iter_mut().for_each(Unspan::unspan),
            ExprKind::List(items) => items.iter_mut().for_each(Unspan::unspan),
            ExprKind::Comprehension(head, clauses) => {
                head.unspan();
                for clause in clauses {
                    match clause {
                        Clause::For(pat, expr) => {
                            pat.unspan();
                            expr.unspan();
                        }
                        Clause::If(expr) => expr.unspan(),
                    }
                }
            }
            ExprKind::Range { lo, hi, .. } => {
                lo.unspan();
                hi.unspan();
            }
            ExprKind::Form { left, right } => {
                left.iter_mut().for_each(Unspan::unspan);
                right.iter_mut().for_each(Unspan::unspan);
            }
            ExprKind::Call(callee, args) => {
                callee.unspan();
                args.iter_mut().for_each(Unspan::unspan);
            }
            ExprKind::Index(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Relation(_, a, b) => {
                a.unspan();
                b.unspan();
            }
            ExprKind::Lambda(params, body) => {
                for param in params {
                    param.pat.unspan();
                    if let Some(ty) = &mut param.ty {
                        ty.unspan();
                    }
                }
                body.unspan();
            }
            ExprKind::Unary(_, a) => a.unspan(),
            ExprKind::If(c, a, b) => {
                c.unspan();
                a.unspan();
                b.unspan();
            }
            ExprKind::Match(scrutinee, arms) => {
                scrutinee.unspan();
                for (pat, expr) in arms {
                    pat.unspan();
                    expr.unspan();
                }
            }
            ExprKind::Block(bindings, body) => {
                bindings.iter_mut().for_each(Unspan::unspan);
                body.unspan();
            }
            ExprKind::Annot(expr, ty) => {
                expr.unspan();
                ty.unspan();
            }
        }
    }
}

impl Unspan for Item {
    fn unspan(&mut self) {
        match self {
            Item::One(expr) | Item::Splice(expr) => expr.unspan(),
        }
    }
}

impl Unspan for Pat {
    fn unspan(&mut self) {
        self.span = Span::default();
        match &mut self.kind {
            PatKind::Wild | PatKind::Var(_) | PatKind::Int(_) | PatKind::Bool(_) => {}
            PatKind::Tuple(items) | PatKind::Con(_, items) => {
                items.iter_mut().for_each(Unspan::unspan)
            }
            PatKind::List(items, rest) => {
                items.iter_mut().for_each(Unspan::unspan);
                if let Some(rest) = rest {
                    rest.unspan();
                }
            }
            PatKind::Annot(inner, ty) => {
                inner.unspan();
                ty.unspan();
            }
        }
    }
}

impl Unspan for TypeExpr {
    fn unspan(&mut self) {
        self.span = Span::default();
        match &mut self.kind {
            TypeKind::Named(_, args) | TypeKind::Tuple(args) => {
                args.iter_mut().for_each(Unspan::unspan)
            }
            TypeKind::Fun(args, ret) => {
                args.iter_mut().for_each(Unspan::unspan);
                ret.unspan();
            }
            TypeKind::PolyRing(_) | TypeKind::RatField(_) | TypeKind::Var(_) => {}
        }
    }
}

impl Unspan for Binding {
    fn unspan(&mut self) {
        self.span = Span::default();
        self.pat.unspan();
        self.expr.unspan();
    }
}

impl Unspan for Stmt {
    fn unspan(&mut self) {
        match self {
            Stmt::Data(decl) => {
                decl.span = Span::default();
                for ctor in &mut decl.ctors {
                    ctor.span = Span::default();
                    ctor.fields.iter_mut().for_each(Unspan::unspan);
                }
            }
            Stmt::Seq(bindings, expr) => {
                bindings.iter_mut().for_each(Unspan::unspan);
                if let Some(expr) = expr {
                    expr.unspan();
                }
            }
        }
    }
}
