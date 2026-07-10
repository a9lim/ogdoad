use std::fmt;

use super::ast::Sort;

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
pub enum OghamErrorKind {
    Parse,
    Reserved,
    ExpSort,
    IndexSort,
    BoolSort,
    FnSort,
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
    Improper,
    Unfounded,
    Loopy,
    GraphBudget,
}

impl OghamErrorKind {
    pub fn code(self) -> &'static str {
        match self {
            OghamErrorKind::Parse => "E_Parse",
            OghamErrorKind::Reserved => "E_Reserved",
            OghamErrorKind::ExpSort => "E_ExpSort",
            OghamErrorKind::IndexSort => "E_IndexSort",
            OghamErrorKind::BoolSort => "E_BoolSort",
            OghamErrorKind::FnSort => "E_FnSort",
            OghamErrorKind::Shadow => "E_Shadow",
            OghamErrorKind::SeqValue => "E_SeqValue",
            OghamErrorKind::BareInt => "E_BareInt",
            OghamErrorKind::BareOrdinal => "E_BareOrdinal",
            OghamErrorKind::WrongWorld => "E_WrongWorld",
            OghamErrorKind::CnfOrder => "E_CnfOrder",
            OghamErrorKind::KummerEscape => "E_KummerEscape",
            OghamErrorKind::NotInvertible => "E_NotInvertible",
            OghamErrorKind::DivisionByZero => "E_DivisionByZero",
            OghamErrorKind::BladeIndex => "E_BladeIndex",
            OghamErrorKind::DimMismatch => "E_DimMismatch",
            OghamErrorKind::GeneralMetric => "E_GeneralMetric",
            OghamErrorKind::Unbound => "E_Unbound",
            OghamErrorKind::Arity => "E_Arity",
            OghamErrorKind::UnknownFn => "E_UnknownFn",
            OghamErrorKind::Grade0 => "E_Grade0",
            OghamErrorKind::Modulus => "E_Modulus",
            OghamErrorKind::Overflow => "E_Overflow",
            OghamErrorKind::Domain => "E_Domain",
            OghamErrorKind::Fuel => "E_Fuel",
            OghamErrorKind::Improper => "E_Improper",
            OghamErrorKind::Unfounded => "E_Unfounded",
            OghamErrorKind::Loopy => "E_Loopy",
            OghamErrorKind::GraphBudget => "E_GraphBudget",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OghamError {
    pub kind: OghamErrorKind,
    pub span: Span,
    pub message: String,
    pub hint: Option<String>,
}

impl OghamError {
    pub fn new(kind: OghamErrorKind, span: Span, message: impl Into<String>) -> Self {
        OghamError {
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

impl fmt::Display for OghamError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.kind.code(), self.message)?;
        if let Some(hint) = &self.hint {
            write!(f, " ({hint})")?;
        }
        Ok(())
    }
}

impl std::error::Error for OghamError {}

pub type OghamResult<T> = Result<T, OghamError>;

pub(crate) fn parse_error(message: impl Into<String>) -> OghamError {
    OghamError::new(OghamErrorKind::Parse, Span::point(0), message)
}

pub(crate) fn index_sort_error() -> OghamError {
    OghamError::new(
        OghamErrorKind::IndexSort,
        Span::point(0),
        "expected an Index expression",
    )
}

pub(crate) fn bool_sort_error() -> OghamError {
    OghamError::new(
        OghamErrorKind::BoolSort,
        Span::point(0),
        "expected a Bool expression",
    )
}

pub(crate) fn fn_sort_error() -> OghamError {
    OghamError::new(
        OghamErrorKind::FnSort,
        Span::point(0),
        "Function values are first-order and cannot appear here",
    )
}

pub(crate) fn exp_sort_error() -> OghamError {
    OghamError::new(
        OghamErrorKind::ExpSort,
        Span::point(0),
        "exponent must be an Index",
    )
    .with_hint("`↑`/`^` is power; the wedge product is `∧`/`&`")
}

pub(crate) fn sort_mismatch(expected: Sort, actual: Sort) -> OghamError {
    if expected == Sort::Bool || actual == Sort::Bool {
        bool_sort_error()
    } else {
        index_sort_error()
    }
}

pub(crate) fn unbound_error(name: &str) -> OghamError {
    let err = OghamError::new(
        OghamErrorKind::Unbound,
        Span::point(0),
        format!("unbound identifier `{name}`"),
    );
    if name == "omega" {
        err.with_hint("`ω` (sugar `w`) is the omega literal")
    } else if name == "t" {
        err.with_hint("`t` is the indeterminate in poly/ratfunc worlds")
    } else {
        err.with_hint(format!(
            "did you mean `{name} := ...`? recursive definition? `{name} =: ...`"
        ))
    }
}

pub(crate) fn outcome_name_error(name: &str) -> OghamError {
    OghamError::new(
        OghamErrorKind::Unbound,
        Span::point(0),
        format!("unbound outcome name `{name}`"),
    )
    .with_hint(
        "outcomes are relations against 0: `g > 0` Left wins, `g < 0` Right wins, \
         `g = 0` second player wins, `g ∥ 0` first player wins; draws use the `‿` doubles",
    )
}

pub(crate) fn literal_call_error(name: &str) -> OghamError {
    OghamError::new(
        OghamErrorKind::UnknownFn,
        Span::point(0),
        format!("unknown function `{name}`"),
    )
    .with_hint(format!("`{name}` is a literal now"))
}

pub(crate) fn renamed_function_error(old: &str, new: &str) -> OghamError {
    OghamError::new(
        OghamErrorKind::UnknownFn,
        Span::point(0),
        format!("unknown function `{old}`"),
    )
    .with_hint(format!("`{old}` was renamed to `{new}`"))
}

pub(crate) fn element_fixpoint_error(name: &str) -> OghamError {
    OghamError::new(
        OghamErrorKind::WrongWorld,
        Span::point(0),
        format!("element fixpoint `{name} =: ...` has no fixpoint theory outside the `game` world"),
    )
}

pub(crate) fn grade0_error(span: Span) -> OghamError {
    OghamError::new(
        OghamErrorKind::Grade0,
        span,
        "operation requires a grade-0 element",
    )
}

pub(crate) fn modulus_error(span: Span) -> OghamError {
    OghamError::new(
        OghamErrorKind::Modulus,
        span,
        "remainder modulus is outside this world's supported scope",
    )
    .with_hint("moduli here are monic omega-powers: `% ω↑2` truncates the CNF below it")
}

pub(crate) fn polyint_modulus_error(span: Span) -> OghamError {
    OghamError::new(
        OghamErrorKind::Modulus,
        span,
        "polyint divisor is outside the exact-division domain",
    )
    .with_hint("polyint divisors must be monic")
}

pub(crate) fn kummer_escape(span: Span) -> OghamError {
    OghamError::new(
        OghamErrorKind::KummerEscape,
        span,
        "ordinal nim-product escaped beyond the source-verified tower below ω^(ω^ω)",
    )
    .with_hint("below ω^(ω^ω), primes <= 709 — see docs/OPEN.md")
}

pub(crate) fn overflow(message: impl Into<String>) -> OghamError {
    OghamError::new(OghamErrorKind::Overflow, Span::point(0), message)
}

pub(crate) fn domain(message: impl Into<String>) -> OghamError {
    OghamError::new(OghamErrorKind::Domain, Span::point(0), message)
}

pub(crate) fn graph_budget_error(budget: u128) -> OghamError {
    OghamError::new(
        OghamErrorKind::GraphBudget,
        Span::point(0),
        format!("materialized graph exceeded its node budget of {budget}"),
    )
}

pub(crate) fn game_only_error(feature: &str) -> OghamError {
    let err = OghamError::new(
        OghamErrorKind::WrongWorld,
        Span::point(0),
        format!("{feature} is only defined in the `game` world"),
    );
    if feature == "`≡`" {
        err.with_hint("`=` is already structural here")
    } else {
        err
    }
}

pub(crate) fn array_world_error(feature: &str) -> OghamError {
    OghamError::new(
        OghamErrorKind::WrongWorld,
        Span::point(0),
        format!("`{feature}` is only defined in fixed-dimension Clifford worlds"),
    )
    .with_hint("`[…]` is fixed-shape in Clifford worlds and a free spine in the game world")
}

pub(crate) fn no_order_error() -> OghamError {
    OghamError::new(
        OghamErrorKind::WrongWorld,
        Span::point(0),
        "this world has no canonical order",
    )
}
