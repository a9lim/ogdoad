//! Structured errors produced by parsing, type checking, and evaluation.

use std::fmt;

/// Half-open byte range in the submitted source.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    /// First byte in the range.
    pub start: usize,
    /// First byte after the range.
    pub end: usize,
}

impl Span {
    /// Construct a half-open byte range.
    pub fn new(start: usize, end: usize) -> Self {
        Span { start, end }
    }

    /// Construct an empty range at one byte position.
    pub fn point(pos: usize) -> Self {
        Span {
            start: pos,
            end: pos,
        }
    }

    /// The smallest range covering both spans.
    pub fn join(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

/// Stable machine-readable error categories.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GrundyErrorKind {
    /// Invalid token or grammar.
    Parse,
    /// Syntax reserved by the grammar but unsupported.
    Reserved,
    /// Two types that must agree do not unify.
    Type,
    /// A type the program does not determine and no default resolves.
    Ambiguous,
    /// Unbound identifier, constructor, or type name.
    Unbound,
    /// A binder or binding that shadows a reserved name, or duplicates one.
    Shadow,
    /// Call with the wrong number of arguments.
    Arity,
    /// A refutable pattern did not match, or a `match` had no matching arm.
    Pattern,
    /// A recursive binding whose type has no recursion theory here.
    Fixpoint,
    /// Unguarded recursive game equation.
    Unfounded,
    /// Operand outside an operation's mathematical domain.
    Domain,
    /// Missing multiplicative inverse or exact quotient.
    NotInvertible,
    /// Division or remainder by zero.
    DivisionByZero,
    /// Fixed-width arithmetic overflow.
    Overflow,
    /// Ordinal nim operation outside the supported Kummer tower.
    KummerEscape,
    /// Unsupported modulus.
    Modulus,
    /// Noncanonical order in a Cantor-normal-form literal.
    CnfOrder,
    /// Operation unavailable for a general bilinear metric.
    GeneralMetric,
    /// Multivectors from different Clifford algebras.
    AlgebraMismatch,
    /// Coordinate list length does not match the Clifford dimension.
    DimMismatch,
    /// Blade or coefficient index outside the dimension.
    BladeIndex,
    /// Operation outside the supported loopy-game envelope.
    Loopy,
    /// Evidence that fails its independent check.
    Refuted,
    /// The work budget was exhausted.
    Fuel,
    /// Evaluator recursion exceeded its host frame guard.
    StackDepth,
    /// A graph or exploration exceeded its node budget.
    GraphBudget,
}

impl GrundyErrorKind {
    /// Stable `E_*` code used by diagnostics and conformance vectors.
    pub fn code(self) -> &'static str {
        match self {
            GrundyErrorKind::Parse => "E_Parse",
            GrundyErrorKind::Reserved => "E_Reserved",
            GrundyErrorKind::Type => "E_Type",
            GrundyErrorKind::Ambiguous => "E_Ambiguous",
            GrundyErrorKind::Unbound => "E_Unbound",
            GrundyErrorKind::Shadow => "E_Shadow",
            GrundyErrorKind::Arity => "E_Arity",
            GrundyErrorKind::Pattern => "E_Pattern",
            GrundyErrorKind::Fixpoint => "E_Fixpoint",
            GrundyErrorKind::Unfounded => "E_Unfounded",
            GrundyErrorKind::Domain => "E_Domain",
            GrundyErrorKind::NotInvertible => "E_NotInvertible",
            GrundyErrorKind::DivisionByZero => "E_DivisionByZero",
            GrundyErrorKind::Overflow => "E_Overflow",
            GrundyErrorKind::KummerEscape => "E_KummerEscape",
            GrundyErrorKind::Modulus => "E_Modulus",
            GrundyErrorKind::CnfOrder => "E_CnfOrder",
            GrundyErrorKind::GeneralMetric => "E_GeneralMetric",
            GrundyErrorKind::AlgebraMismatch => "E_AlgebraMismatch",
            GrundyErrorKind::DimMismatch => "E_DimMismatch",
            GrundyErrorKind::BladeIndex => "E_BladeIndex",
            GrundyErrorKind::Loopy => "E_Loopy",
            GrundyErrorKind::Refuted => "E_Refuted",
            GrundyErrorKind::Fuel => "E_Fuel",
            GrundyErrorKind::StackDepth => "E_StackDepth",
            GrundyErrorKind::GraphBudget => "E_GraphBudget",
        }
    }

    /// Every kind, in declaration order.
    pub const ALL: [GrundyErrorKind; 26] = [
        GrundyErrorKind::Parse,
        GrundyErrorKind::Reserved,
        GrundyErrorKind::Type,
        GrundyErrorKind::Ambiguous,
        GrundyErrorKind::Unbound,
        GrundyErrorKind::Shadow,
        GrundyErrorKind::Arity,
        GrundyErrorKind::Pattern,
        GrundyErrorKind::Fixpoint,
        GrundyErrorKind::Unfounded,
        GrundyErrorKind::Domain,
        GrundyErrorKind::NotInvertible,
        GrundyErrorKind::DivisionByZero,
        GrundyErrorKind::Overflow,
        GrundyErrorKind::KummerEscape,
        GrundyErrorKind::Modulus,
        GrundyErrorKind::CnfOrder,
        GrundyErrorKind::GeneralMetric,
        GrundyErrorKind::AlgebraMismatch,
        GrundyErrorKind::DimMismatch,
        GrundyErrorKind::BladeIndex,
        GrundyErrorKind::Loopy,
        GrundyErrorKind::Refuted,
        GrundyErrorKind::Fuel,
        GrundyErrorKind::StackDepth,
        GrundyErrorKind::GraphBudget,
    ];
}

/// One structured grundy diagnostic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrundyError {
    /// Machine-readable category.
    pub kind: GrundyErrorKind,
    /// Source span associated with the failure.
    pub span: Span,
    /// Direct description of the failure.
    pub message: String,
    /// Optional corrective guidance.
    pub hint: Option<String>,
}

impl GrundyError {
    /// Construct an error without a hint.
    pub fn new(kind: GrundyErrorKind, span: Span, message: impl Into<String>) -> Self {
        GrundyError {
            kind,
            span,
            message: message.into(),
            hint: None,
        }
    }

    /// Attach corrective guidance.
    pub fn with_hint(mut self, hint: impl Into<String>) -> Self {
        self.hint = Some(hint.into());
        self
    }

    /// Attach a span if the error does not carry a meaningful one yet.
    pub fn at(mut self, span: Span) -> Self {
        if self.span == Span::default() {
            self.span = span;
        }
        self
    }
}

impl fmt::Display for GrundyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.kind.code(), self.message)?;
        if let Some(hint) = &self.hint {
            write!(f, " ({hint})")?;
        }
        Ok(())
    }
}

impl std::error::Error for GrundyError {}

/// Result type for grundy parsing, checking, and evaluation.
pub type GrundyResult<T> = Result<T, GrundyError>;

/// Shorthand for an error without a span; callers attach one with [`GrundyError::at`].
pub(crate) fn err(kind: GrundyErrorKind, message: impl Into<String>) -> GrundyError {
    GrundyError::new(kind, Span::default(), message)
}
