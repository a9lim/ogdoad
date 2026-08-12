use std::fmt;

use super::ast::DataSort;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span { start, end }
    }

    pub fn point(pos: usize) -> Self {
        Span {
            start: pos,
            end: pos,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GrundyErrorKind {
    Parse,
    Reserved,
    ExpSort,
    IndexSort,
    BoolSort,
    FnSort,
    FixpointSort,
    Shadow,
    SeqValue,
    BareInt,
    BareOrdinal,
    WrongWorld,
    CnfOrder,
    KummerEscape,
    NotInvertible,
    DivisionByZero,
    BladeIndex,
    DimMismatch,
    GeneralMetric,
    Unbound,
    Arity,
    UnknownFn,
    Grade0,
    Modulus,
    Overflow,
    Domain,
    Fuel,
    StackDepth,
    Improper,
    Unfounded,
    Loopy,
    GraphBudget,
}

impl GrundyErrorKind {
    pub fn code(self) -> &'static str {
        match self {
            GrundyErrorKind::Parse => "E_Parse",
            GrundyErrorKind::Reserved => "E_Reserved",
            GrundyErrorKind::ExpSort => "E_ExpSort",
            GrundyErrorKind::IndexSort => "E_IndexSort",
            GrundyErrorKind::BoolSort => "E_BoolSort",
            GrundyErrorKind::FnSort => "E_FnSort",
            GrundyErrorKind::FixpointSort => "E_FixpointSort",
            GrundyErrorKind::Shadow => "E_Shadow",
            GrundyErrorKind::SeqValue => "E_SeqValue",
            GrundyErrorKind::BareInt => "E_BareInt",
            GrundyErrorKind::BareOrdinal => "E_BareOrdinal",
            GrundyErrorKind::WrongWorld => "E_WrongWorld",
            GrundyErrorKind::CnfOrder => "E_CnfOrder",
            GrundyErrorKind::KummerEscape => "E_KummerEscape",
            GrundyErrorKind::NotInvertible => "E_NotInvertible",
            GrundyErrorKind::DivisionByZero => "E_DivisionByZero",
            GrundyErrorKind::BladeIndex => "E_BladeIndex",
            GrundyErrorKind::DimMismatch => "E_DimMismatch",
            GrundyErrorKind::GeneralMetric => "E_GeneralMetric",
            GrundyErrorKind::Unbound => "E_Unbound",
            GrundyErrorKind::Arity => "E_Arity",
            GrundyErrorKind::UnknownFn => "E_UnknownFn",
            GrundyErrorKind::Grade0 => "E_Grade0",
            GrundyErrorKind::Modulus => "E_Modulus",
            GrundyErrorKind::Overflow => "E_Overflow",
            GrundyErrorKind::Domain => "E_Domain",
            GrundyErrorKind::Fuel => "E_Fuel",
            GrundyErrorKind::StackDepth => "E_StackDepth",
            GrundyErrorKind::Improper => "E_Improper",
            GrundyErrorKind::Unfounded => "E_Unfounded",
            GrundyErrorKind::Loopy => "E_Loopy",
            GrundyErrorKind::GraphBudget => "E_GraphBudget",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrundyError {
    pub kind: GrundyErrorKind,
    pub span: Span,
    pub message: String,
    pub hint: Option<String>,
}

impl GrundyError {
    pub fn new(kind: GrundyErrorKind, span: Span, message: impl Into<String>) -> Self {
        GrundyError {
            kind,
            span,
            message: message.into(),
            hint: None,
        }
    }

    pub fn with_hint(mut self, hint: impl Into<String>) -> Self {
        self.hint = Some(hint.into());
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

pub type GrundyResult<T> = Result<T, GrundyError>;

pub(crate) fn parse_error(message: impl Into<String>) -> GrundyError {
    GrundyError::new(GrundyErrorKind::Parse, Span::point(0), message)
}

pub(crate) fn index_sort_error() -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::IndexSort,
        Span::point(0),
        "expected an Index expression",
    )
}

pub(crate) fn bool_sort_error() -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::BoolSort,
        Span::point(0),
        "expected a Bool expression",
    )
}

pub(crate) fn fn_sort_error() -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::FnSort,
        Span::point(0),
        "Function values are first-order and cannot appear here",
    )
}

pub(crate) fn fixpoint_sort_error() -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::FixpointSort,
        Span::point(0),
        "Bool and Index values do not have recursive fixpoint semantics",
    )
    .with_hint("recursion is for Functions (unfolding) and game Elements (graphs)")
}

pub(crate) fn exp_sort_error() -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::ExpSort,
        Span::point(0),
        "exponent must be an Index",
    )
    .with_hint("`↑`/`^` is power; the wedge product is `∧`/`&`")
}

pub(crate) fn sort_mismatch(expected: DataSort, actual: DataSort) -> GrundyError {
    if expected == DataSort::Bool || actual == DataSort::Bool {
        bool_sort_error()
    } else {
        index_sort_error()
    }
}

pub(crate) fn unbound_error(name: &str) -> GrundyError {
    let err = GrundyError::new(
        GrundyErrorKind::Unbound,
        Span::point(0),
        format!("unbound identifier `{name}`"),
    );
    if name == "omega" {
        err.with_hint("`ω` (sugar `w`) is the omega literal")
    } else if name == "t" {
        err.with_hint("`t` is the indeterminate in polynomial and rational-function worlds")
    } else {
        err.with_hint(format!(
            "did you mean `{name} := ...`? recursive definition? `{name} =: ...`"
        ))
    }
}

pub(crate) fn outcome_name_error(name: &str) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::Unbound,
        Span::point(0),
        format!("unbound outcome name `{name}`"),
    )
    .with_hint(
        "outcomes are relations against 0: `g > 0` Left wins, `g < 0` Right wins, \
         `g = 0` second player wins, `g ∥ 0` first player wins; draws use the `‿` doubles",
    )
}

pub(crate) fn literal_call_error(name: &str) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::UnknownFn,
        Span::point(0),
        format!("unknown function `{name}`"),
    )
    .with_hint(format!("write the literal `{name}` without parentheses"))
}

pub(crate) fn renamed_function_error(old: &str, new: &str) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::UnknownFn,
        Span::point(0),
        format!("unknown function `{old}`"),
    )
    .with_hint(format!("`{old}` was renamed to `{new}`"))
}

pub(crate) fn element_fixpoint_error(name: &str) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::WrongWorld,
        Span::point(0),
        format!("element fixpoint `{name} =: ...` has no fixpoint theory outside the `game` world"),
    )
}

pub(crate) fn grade0_error(span: Span) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::Grade0,
        span,
        "operation requires a grade-0 element",
    )
}

pub(crate) fn modulus_error(span: Span) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::Modulus,
        span,
        "remainder modulus is outside this world's supported scope",
    )
    .with_hint("moduli here are monic omega-powers: `% ω↑2` truncates the CNF below it")
}

pub(crate) fn polyint_modulus_error(span: Span) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::Modulus,
        span,
        "`integer[t]` divisor is outside the exact-division domain",
    )
    .with_hint("`integer[t]` divisors must be monic")
}

pub(crate) fn kummer_escape(span: Span) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::KummerEscape,
        span,
        "ordinal nim-product escaped beyond the source-verified tower below ω^(ω^ω)",
    )
    .with_hint("below ω^(ω^ω), primes <= 727 — see docs/OPEN.md")
}

pub(crate) fn overflow(message: impl Into<String>) -> GrundyError {
    GrundyError::new(GrundyErrorKind::Overflow, Span::point(0), message)
}

pub(crate) fn domain(message: impl Into<String>) -> GrundyError {
    GrundyError::new(GrundyErrorKind::Domain, Span::point(0), message)
}

pub(crate) fn graph_budget_error(budget: u128) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::GraphBudget,
        Span::point(0),
        format!("materialized graph exceeded its node budget of {budget}"),
    )
}

pub(crate) fn game_only_error(feature: &str) -> GrundyError {
    let err = GrundyError::new(
        GrundyErrorKind::WrongWorld,
        Span::point(0),
        format!("{feature} is only defined in the `game` world"),
    );
    if feature == "`≡`" {
        err.with_hint("`=` is already structural here")
    } else {
        err
    }
}

pub(crate) fn array_world_error(feature: &str) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::WrongWorld,
        Span::point(0),
        format!("`{feature}` is only defined in fixed-dimension Clifford worlds"),
    )
    .with_hint("`[…]` is fixed-shape in Clifford worlds and a free spine in the game world")
}

pub(crate) fn no_order_error() -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::WrongWorld,
        Span::point(0),
        "this world has no canonical order",
    )
}
