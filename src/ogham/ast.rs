use crate::scalar::Ordinal;

#[derive(Clone, Debug, PartialEq)]
pub enum Statement {
    Binding {
        name: String,
        expr: Expr,
        recursive: bool,
    },
    Expr(Expr),
    Seq {
        bindings: Vec<Binding>,
        tail: Box<Statement>,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub struct Binding {
    pub name: String,
    pub expr: Expr,
    pub recursive: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Int(u128),
    Bool(bool),
    Star(StarLiteral),
    Omega,
    Blade(usize),
    Vector(Vec<Expr>),
    Tuple(Vec<Expr>),
    Ident(String),
    Lambda {
        binders: Vec<String>,
        body: Box<Expr>,
    },
    Block {
        bindings: Vec<Binding>,
        body: Box<Expr>,
    },
    GameForm {
        left: Vec<Expr>,
        right: Vec<Expr>,
    },
    Call {
        name: String,
        args: Vec<Expr>,
    },
    Factorial(Box<Expr>),
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Ternary {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    Relation {
        op: RelOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
}

impl Expr {
    pub fn is_omega_atom(&self) -> bool {
        matches!(self, Expr::Omega)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum StarLiteral {
    Finite(u128),
    Cnf(Ordinal),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Inv,
    Not,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Wedge,
    Pow,
    At,
    And,
    Or,
    Append,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelOp {
    Eq,
    Lt,
    Gt,
    Fuzzy,
    Equiv,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sort {
    Element,
    Index,
    Bool,
}
