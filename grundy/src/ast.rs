//! Syntax tree types for the grundy language.

use ogdoad::scalar::Ordinal;

/// A top-level statement or semicolon-separated statement sequence.
#[derive(Clone, Debug, PartialEq)]
pub enum Statement {
    /// A non-recursive (`:=`) or recursive (`=:`) binding.
    Binding {
        /// Bound identifier.
        name: String,
        /// Right-hand-side expression.
        expr: Expr,
        /// Whether the source used `=:`.
        recursive: bool,
    },
    /// A value-producing expression statement.
    Expr(Expr),
    /// Bindings followed by a final statement.
    Seq {
        /// Ordered prefix bindings.
        bindings: Vec<Binding>,
        /// Final statement.
        tail: Box<Statement>,
    },
}

/// One binding within a sequence or expression block.
#[derive(Clone, Debug, PartialEq)]
pub struct Binding {
    /// Bound identifier.
    pub name: String,
    /// Right-hand-side expression.
    pub expr: Expr,
    /// Whether the binding uses `=:`.
    pub recursive: bool,
}

/// A lambda binder and any explicitly declared data sort.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LambdaBinder {
    /// Binder name.
    pub name: String,
    /// Sort selected by `#` or `?`; `None` means an unmarked binder.
    pub declared_sort: Option<DataSort>,
}

/// A grundy expression before evaluation.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    /// Unsigned integer token; its data sort depends on context and world.
    Int(u128),
    /// Explicit Index expression `#(...)`.
    Index(Box<Expr>),
    /// Boolean literal.
    Bool(bool),
    /// Star-prefixed nimber or ordinal literal.
    Star(StarLiteral),
    /// The omega literal.
    Omega,
    /// Basis blade `e_i`.
    Blade(usize),
    /// World-shaped bracket container.
    Container(Vec<Expr>),
    /// The game `up`.
    Up,
    /// The game `down`.
    Down,
    /// The current Clifford dimension.
    Dim,
    /// Identifier reference.
    Ident(String),
    /// First-order lambda expression.
    Lambda {
        /// Ordered binders.
        binders: Vec<LambdaBinder>,
        /// Lambda body.
        body: Box<Expr>,
    },
    /// Parenthesized bindings followed by a value expression.
    Block {
        /// Local bindings.
        bindings: Vec<Binding>,
        /// Result expression.
        body: Box<Expr>,
    },
    /// Partizan game form `{ left | right }`.
    GameForm {
        /// Left options.
        left: Vec<Expr>,
        /// Right options.
        right: Vec<Expr>,
    },
    /// Named built-in call.
    Call {
        /// Built-in name.
        name: String,
        /// Call arguments.
        args: Vec<Expr>,
    },
    /// Function application with `@`.
    Apply {
        /// Function expression.
        callee: Box<Expr>,
        /// Argument frame.
        args: Vec<Expr>,
    },
    /// Unary operation.
    Unary {
        /// Operator.
        op: UnaryOp,
        /// Operand.
        expr: Box<Expr>,
    },
    /// Binary operation.
    Binary {
        /// Operator.
        op: BinaryOp,
        /// Left operand.
        lhs: Box<Expr>,
        /// Right operand.
        rhs: Box<Expr>,
    },
    /// Conditional expression.
    If {
        /// Boolean condition.
        cond: Box<Expr>,
        /// Selected when the condition is true.
        then_expr: Box<Expr>,
        /// Selected when the condition is false.
        else_expr: Box<Expr>,
    },
    /// Boolean relation.
    Relation {
        /// Relation operator.
        op: RelOp,
        /// Left operand.
        lhs: Box<Expr>,
        /// Right operand.
        rhs: Box<Expr>,
    },
}

impl Expr {
    /// Whether this expression is exactly the omega atom.
    pub fn is_omega_atom(&self) -> bool {
        matches!(self, Expr::Omega)
    }
}

/// Payload of a star-prefixed literal.
#[derive(Clone, Debug, PartialEq)]
pub enum StarLiteral {
    /// Finite nimber address.
    Finite(u128),
    /// Ordinal address in Cantor normal form.
    Cnf(Ordinal),
}

/// Unary expression operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    /// Additive negation.
    Neg,
    /// Multiplicative inverse.
    Inv,
    /// Boolean negation.
    Not,
}

/// Binary expression operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Algebra product.
    Mul,
    /// Division.
    Div,
    /// Remainder.
    Rem,
    /// Exterior product.
    Wedge,
    /// Exponentiation.
    Pow,
    /// Lazy Boolean conjunction.
    And,
    /// Lazy Boolean disjunction.
    Or,
    /// Game-spine append.
    Append,
}

/// Relation operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelOp {
    /// Value equality.
    Eq,
    /// Strictly less than.
    Lt,
    /// Strictly greater than.
    Gt,
    /// Incomparability.
    Fuzzy,
    /// Game multiform equality.
    Equiv,
    /// One loopy-game outcome cell.
    Outcome(OutcomeCell),
}

/// One cell of the loopy-game outcome grid. The first coordinate is the result
/// with Left starting; the second is the result with Right starting.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OutcomeCell {
    /// Left wins for both starters (`>>`).
    LeftLeft,
    /// Left wins moving first; Right-start is drawn (`>‿`).
    LeftDraw,
    /// The first player wins (`><`).
    LeftRight,
    /// Left-start is drawn; Left wins moving second (`‿>`).
    DrawLeft,
    /// Both starters draw (`‿‿`).
    DrawDraw,
    /// Left-start is drawn; Right wins moving second (`‿<`).
    DrawRight,
    /// The second player wins (`<>`).
    RightLeft,
    /// Right wins moving first; Right-start is drawn (`<‿`).
    RightDraw,
    /// Right wins for both starters (`<<`).
    RightRight,
}

impl OutcomeCell {
    /// All nine cells in row-major starter-result order.
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

    /// The canonical two-glyph spelling.
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

    /// Rotate the outcome grid by 180 degrees.
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

/// The three first-order data sorts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DataSort {
    /// A value in the active mathematical world.
    Element,
    /// A host-sized mathematical index.
    Index,
    /// A Boolean verdict.
    Bool,
}
