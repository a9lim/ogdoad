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
    Index(Box<Expr>),
    Bool(bool),
    Star(StarLiteral),
    Omega,
    Blade(usize),
    Container(Vec<Expr>),
    Up,
    Down,
    Dim,
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
    Outcome(OutcomeCell),
}

/// One cell of the loopy-game outcome grid. The first coordinate is the result
/// with Left starting; the second is the result with Right starting.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OutcomeCell {
    LeftLeft,
    LeftDraw,
    LeftRight,
    DrawLeft,
    DrawDraw,
    DrawRight,
    RightLeft,
    RightDraw,
    RightRight,
}

impl OutcomeCell {
    pub const ALL: [Self; 9] = [
        Self::LeftLeft,
        Self::LeftDraw,
        Self::LeftRight,
        Self::DrawLeft,
        Self::DrawDraw,
        Self::DrawRight,
        Self::RightLeft,
        Self::RightDraw,
        Self::RightRight,
    ];

    pub fn glyph(self) -> &'static str {
        match self {
            Self::LeftLeft => ">>",
            Self::LeftDraw => ">‿",
            Self::LeftRight => "><",
            Self::DrawLeft => "‿>",
            Self::DrawDraw => "‿‿",
            Self::DrawRight => "‿<",
            Self::RightLeft => "<>",
            Self::RightDraw => "<‿",
            Self::RightRight => "<<",
        }
    }

    pub fn rotate(self) -> Self {
        match self {
            Self::LeftLeft => Self::RightRight,
            Self::LeftDraw => Self::DrawRight,
            Self::LeftRight => Self::LeftRight,
            Self::DrawLeft => Self::RightDraw,
            Self::DrawDraw => Self::DrawDraw,
            Self::DrawRight => Self::LeftDraw,
            Self::RightLeft => Self::RightLeft,
            Self::RightDraw => Self::DrawLeft,
            Self::RightRight => Self::LeftLeft,
        }
    }

    pub(crate) fn from_atoms(first: char, second: char) -> Self {
        match (first, second) {
            ('>', '>') => Self::LeftLeft,
            ('>', '‿') => Self::LeftDraw,
            ('>', '<') => Self::LeftRight,
            ('‿', '>') => Self::DrawLeft,
            ('‿', '‿') => Self::DrawDraw,
            ('‿', '<') => Self::DrawRight,
            ('<', '>') => Self::RightLeft,
            ('<', '‿') => Self::RightDraw,
            ('<', '<') => Self::RightRight,
            _ => unreachable!("lexer normalizes mover-result atoms"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sort {
    Element,
    Index,
    Bool,
}
