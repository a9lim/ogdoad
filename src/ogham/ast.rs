use crate::scalar::Ordinal;

#[derive(Clone, Debug, PartialEq)]
pub enum Statement {
    Binding { name: String, expr: Expr },
    Expr(Expr),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Int(u128),
    Star(StarLiteral),
    Omega,
    Blade(usize),
    Vector(Vec<Expr>),
    Ident(String),
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
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelOp {
    Eq,
    Lt,
    Gt,
    Fuzzy,
}
