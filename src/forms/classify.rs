//! The classifier façade: one entry point that dispatches on the scalar field.
//!
//! The three characteristic legs ([`char0`](crate::forms::char0),
//! [`oddchar`](crate::forms::oddchar), [`char2`](crate::forms::char2)) each ship
//! their own classifier with a leg-specific signature — `classify_surreal`,
//! `classify_finite_odd`, `arf_invariant`, … Choosing the right one is a fact
//! about the field, not the form, so it can be resolved *at compile time* from
//! the scalar type. [`ClassifyForm`] does exactly that: write
//! `metric.classify()` (or `S::classify(metric)`) and the correct leg is
//! selected by the monomorphised `S` — no manual `match` on characteristic.
//!
//! [`ClassifyWitt`] is the same idea for the unified [`WittClassG`], over the
//! three legs where a single Witt class exists (real char 0, odd char, char 2).
//! `Rational`'s Witt invariant is the full Hasse–Minkowski datum and surcomplex's
//! is `W(ℂ) = ℤ/2`; neither is a `WittClassG`, so those two backends implement
//! [`ClassifyForm`] but not [`ClassifyWitt`] — honest, not a gap.

use crate::clifford::{CliffordAlgebra, Metric};
use crate::forms::{
    arf_fpn_char2, arf_invariant, arf_ordinal_finite, bw_class_complex, bw_class_finite_odd,
    bw_class_nimber, bw_class_real, classify_finite_odd, classify_rational, classify_surcomplex,
    classify_surreal, finite_odd_witt, isometric_finite_odd, isometric_fpn_char2, isometric_nimber,
    isometric_ordinal_finite, isometric_rational, isometric_real, isometric_surcomplex,
    ordinal_metric_finite_subfield_degree, witt_decompose_finite_odd, witt_decompose_real,
    ArfInvariants, BrauerWallClass, CliffordInvariants, OddCharInvariants, OddWittDecomp,
    RationalCliffordInvariants, RealWittDecomp, WittClassG,
};
use crate::scalar::{Fp, Fpn, Nimber, Ordinal, Rational, Scalar, Surcomplex, Surreal};

/// Classification invariants for the `Fpn<P,N>` finite-field tower. Odd-characteristic
/// extension fields land in the usual finite-odd invariant; characteristic-2
/// extension fields land in the Arf invariant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FiniteFieldInvariants {
    /// Finite field of odd characteristic.
    Odd(OddCharInvariants),
    /// Finite field of characteristic 2.
    Char2(ArfInvariants),
}

/// Witt-decomposition data for the finite-field tower `Fpn<P,N>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FiniteFieldWittDecomp {
    /// Odd-characteristic finite field.
    Odd(OddWittDecomp),
    /// Characteristic-2 finite field.
    Char2(Char2WittDecomp),
}

/// Witt-decomposition data for a characteristic-2 finite-field form.
///
/// **Basis-dependence caveat for defective forms.** When `radical_anisotropic`
/// is `true` (the polar radical carries a nonzero `Q`-value), the fields
/// `witt_index`, `core_anisotropic_dim`, and `arf` describe the **chosen**
/// symplectic complement of the radical, not an isometry invariant of the
/// whole form.  Different choices of symplectic complement can yield different
/// Arf bits and hence different `witt_index`/`core_anisotropic_dim` values.
/// This matches the semantics of [`crate::forms::ArfInvariants::o_type`], which
/// carries the same caveat.  Callers that need isometry-invariant data for
/// defective forms should use [`crate::forms::ArfInvariants`] directly and
/// check the `radical_anisotropic` flag before relying on the Arf bit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Char2WittDecomp {
    /// Extension degree `m` for `F_{2^m}`.
    pub field_degree: u128,
    /// Number of hyperbolic planes split from the nonsingular core.
    ///
    /// **Not an isometry invariant when `radical_anisotropic` is true** — see
    /// the struct-level caveat.
    pub witt_index: usize,
    /// Dimension of the anisotropic nonsingular core: `0` for hyperbolic, `2`
    /// for the anisotropic plane.
    ///
    /// **Not an isometry invariant when `radical_anisotropic` is true** — see
    /// the struct-level caveat.
    pub core_anisotropic_dim: usize,
    /// Dimension of the polar radical.
    pub radical_dim: usize,
    /// Whether the quadratic form is nonzero on the radical (defective form).
    pub radical_anisotropic: bool,
    /// Arf bit of the **chosen** symplectic complement's nonsingular core.
    ///
    /// **Not an isometry invariant when `radical_anisotropic` is true** — see
    /// the struct-level caveat.
    pub arf: u128,
}

impl Char2WittDecomp {
    fn from_arf(field_degree: u128, arf: &ArfInvariants) -> Self {
        let core_anisotropic_dim = if arf.arf == 0 { 0 } else { 2 };
        let witt_index = arf.rank.saturating_sub(core_anisotropic_dim) / 2;
        Char2WittDecomp {
            field_degree,
            witt_index,
            core_anisotropic_dim,
            radical_dim: arf.radical_dim,
            radical_anisotropic: arf.radical_anisotropic,
            arf: arf.arf,
        }
    }
}

impl FiniteFieldInvariants {
    /// `display()` alias kept for Python callers.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for FiniteFieldInvariants {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FiniteFieldInvariants::Odd(c) => write!(f, "{c}"),
            FiniteFieldInvariants::Char2(c) => {
                write!(
                    f,
                    "char 2: Arf {} rank {} radical {}{} ({})",
                    c.arf,
                    c.rank,
                    c.radical_dim,
                    if c.radical_anisotropic {
                        " defective"
                    } else {
                        ""
                    },
                    c.o_type()
                )
            }
        }
    }
}

/// Reason a façade classifier or Witt/Brauer-Wall method returned `Err`.
///
/// Only the façade entry points return `Result` — the underlying leg functions
/// whose `None` is single-valued and mathematically honest stay `Option`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ClassifyError {
    /// The metric has a non-trivial general-bilinear `a` component; the
    /// characteristic-2 and Arf classifiers require a pure (q, b) metric.
    GeneralBilinearMetric,
    /// The metric could not be diagonalized over this scalar backend
    /// (e.g. exact square root not representable in the `Surreal` model).
    DiagonalizerFailure,
    /// The field or ordinal window is outside the supported classifier domain
    /// (e.g. `Ordinal` entries beyond the detected finite windows).
    UnsupportedFieldOrWindow,
    /// The form has a non-trivial polar radical (`radical_dim > 0`); the
    /// Witt group and Brauer-Wall class require a nonsingular form.
    SingularForm {
        /// Dimension of the radical.
        radical_dim: usize,
        /// Whether the quadratic form is nonzero on the radical.
        radical_anisotropic: bool,
    },
}

impl std::fmt::Display for ClassifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ClassifyError::GeneralBilinearMetric => {
                f.write_str("classifier requires a pure (q, b) metric, not general bilinear")
            }
            ClassifyError::DiagonalizerFailure => {
                f.write_str("metric could not be diagonalized over this scalar backend")
            }
            ClassifyError::UnsupportedFieldOrWindow => {
                f.write_str("field or ordinal window is outside the supported classifier domain")
            }
            ClassifyError::SingularForm {
                radical_dim,
                radical_anisotropic,
            } => write!(
                f,
                "singular form: radical_dim={radical_dim}, radical_anisotropic={radical_anisotropic}"
            ),
        }
    }
}

/// Classify the quadratic form data attached to a [`Metric`] over `Self`,
/// dispatched on the scalar field. For real/complex-style legs this is also the
/// implemented Clifford-algebra closure type; for `Rational` it is the complete
/// Hasse-Minkowski quadratic-form invariant, not a full rational Brauer-Wall
/// class. The [`Class`](ClassifyForm::Class) associated type is the leg-specific
/// datum:
///
/// | scalar | `Class` | leg |
/// |---|---|---|
/// | [`Surreal`] | [`CliffordInvariants`] | exact-square char 0 subdomain (8-fold) |
/// | [`Surcomplex<Surreal>`](Surcomplex) | [`CliffordInvariants`] | exact-square char 0 subdomain (2-fold) |
/// | [`Rational`] | [`RationalCliffordInvariants`] | char 0, full Hasse-Minkowski form invariant |
/// | [`Fp<P>`](Fp) | [`OddCharInvariants`] | odd characteristic |
/// | [`Fpn<P,N>`](Fpn) | [`FiniteFieldInvariants`] | finite extension fields, odd or char 2 |
/// | [`Nimber`] | [`ArfInvariants`] | characteristic 2 (Arf) |
/// | [`Ordinal`] | [`ArfInvariants`] | detected finite ordinal-nimber windows only |
///
/// `Err` means the metric is outside the classifier's domain (e.g. a non-diagonal
/// char-2 form, or a metric the diagonalizer can't reduce); see [`ClassifyError`].
impl From<crate::forms::WittClassError> for ClassifyError {
    fn from(e: crate::forms::WittClassError) -> Self {
        match e {
            crate::forms::WittClassError::GeneralBilinearMetric => {
                ClassifyError::GeneralBilinearMetric
            }
            crate::forms::WittClassError::Singular {
                radical_dim,
                radical_anisotropic,
            } => ClassifyError::SingularForm {
                radical_dim,
                radical_anisotropic,
            },
        }
    }
}

/// Failure diagnosis for the char-0 / odd legs: general-bilinear data first,
/// then a diagonalizer probe, then the honest out-of-domain default.
fn char0_failure<S: crate::scalar::Scalar>(metric: &Metric<S>) -> ClassifyError {
    if metric.a().values().any(|v| !v.is_zero()) {
        return ClassifyError::GeneralBilinearMetric;
    }
    if crate::forms::as_diagonal(metric).is_none() {
        return ClassifyError::DiagonalizerFailure;
    }
    ClassifyError::UnsupportedFieldOrWindow
}

/// Failure diagnosis for the char-2 legs over `Nimber`: general-bilinear data,
/// then a polar-radical (singular form) probe, then the out-of-domain default.
fn char2_nimber_failure(metric: &Metric<Nimber>) -> ClassifyError {
    if metric.a().values().any(|v| !v.is_zero()) {
        return ClassifyError::GeneralBilinearMetric;
    }
    if let Some(arf) = arf_invariant(metric) {
        if arf.radical_dim != 0 {
            return ClassifyError::SingularForm {
                radical_dim: arf.radical_dim,
                radical_anisotropic: arf.radical_anisotropic,
            };
        }
    }
    ClassifyError::UnsupportedFieldOrWindow
}

/// Generic metric-shape diagnosis where no leg-specific probe applies.
fn generic_failure<S: crate::scalar::Scalar>(metric: &Metric<S>) -> ClassifyError {
    if metric.a().values().any(|v| !v.is_zero()) {
        return ClassifyError::GeneralBilinearMetric;
    }
    ClassifyError::UnsupportedFieldOrWindow
}

/// Diagnose a two-metric failure: blame `m1` if it is out of domain, else `m2`.
fn two_metric_failure<S: crate::scalar::Scalar>(
    m1: &Metric<S>,
    m2: &Metric<S>,
    diagnose: impl Fn(&Metric<S>) -> ClassifyError,
) -> ClassifyError {
    match diagnose(m1) {
        ClassifyError::UnsupportedFieldOrWindow => diagnose(m2),
        e => e,
    }
}

pub trait ClassifyForm: Scalar {
    /// The classification datum produced for this field's characteristic leg.
    type Class;

    /// Classify the form carried by `metric`.
    fn classify(metric: &Metric<Self>) -> Result<Self::Class, ClassifyError>;
}

/// The unified Witt class [`WittClassG`] of a form, for the three legs where a
/// single Witt class exists. (`Rational` and `Surcomplex` deliberately do not
/// implement this — see the module docs.)
pub trait ClassifyWitt: Scalar {
    /// The Witt class of the form carried by `metric`.
    fn witt_class(metric: &Metric<Self>) -> Result<WittClassG, ClassifyError>;
}

/// Isometry comparison for scalar worlds with a complete invariant available.
pub trait ClassifyIsometry: Scalar {
    /// Whether two forms over the same scalar world are isometric.
    fn isometric(m1: &Metric<Self>, m2: &Metric<Self>) -> Result<bool, ClassifyError>;
}

/// Constructive Witt decomposition where the crate has a concrete decomposition
/// datum for that scalar world.
pub trait DecomposeWitt: Scalar {
    /// The decomposition datum for this scalar world.
    type Decomp;

    /// Split a form into hyperbolic planes plus anisotropic kernel data.
    fn witt_decompose(metric: &Metric<Self>) -> Result<Self::Decomp, ClassifyError>;
}

/// Brauer-Wall class of the Clifford algebra attached to a form.
pub trait ClassifyBrauerWall: Scalar {
    /// The Brauer-Wall class of `Cl(metric)`.
    fn bw_class(metric: &Metric<Self>) -> Result<BrauerWallClass, ClassifyError>;
}

impl ClassifyForm for Surreal {
    type Class = CliffordInvariants;
    fn classify(metric: &Metric<Self>) -> Result<CliffordInvariants, ClassifyError> {
        classify_surreal(metric).ok_or_else(|| char0_failure(metric))
    }
}

impl ClassifyForm for Surcomplex<Surreal> {
    type Class = CliffordInvariants;
    fn classify(metric: &Metric<Self>) -> Result<CliffordInvariants, ClassifyError> {
        classify_surcomplex(metric).ok_or_else(|| char0_failure(metric))
    }
}

impl ClassifyForm for Rational {
    type Class = RationalCliffordInvariants;
    fn classify(metric: &Metric<Self>) -> Result<RationalCliffordInvariants, ClassifyError> {
        classify_rational(metric).ok_or_else(|| char0_failure(metric))
    }
}

impl<const P: u128> ClassifyForm for Fp<P> {
    type Class = OddCharInvariants;
    fn classify(metric: &Metric<Self>) -> Result<OddCharInvariants, ClassifyError> {
        classify_finite_odd(metric).ok_or_else(|| char0_failure(metric))
    }
}

impl<const P: u128, const N: usize> ClassifyForm for Fpn<P, N> {
    type Class = FiniteFieldInvariants;
    fn classify(metric: &Metric<Self>) -> Result<FiniteFieldInvariants, ClassifyError> {
        if P == 2 {
            arf_fpn_char2(metric)
                .map(FiniteFieldInvariants::Char2)
                .ok_or_else(|| generic_failure(metric))
        } else {
            classify_finite_odd(metric)
                .map(FiniteFieldInvariants::Odd)
                .ok_or_else(|| char0_failure(metric))
        }
    }
}

impl ClassifyForm for Nimber {
    type Class = ArfInvariants;
    fn classify(metric: &Metric<Self>) -> Result<ArfInvariants, ClassifyError> {
        arf_invariant(metric).ok_or_else(|| generic_failure(metric))
    }
}

impl ClassifyForm for Ordinal {
    type Class = ArfInvariants;
    fn classify(metric: &Metric<Self>) -> Result<ArfInvariants, ClassifyError> {
        arf_ordinal_finite(metric).ok_or_else(|| generic_failure(metric))
    }
}

impl ClassifyWitt for Surreal {
    fn witt_class(metric: &Metric<Self>) -> Result<WittClassG, ClassifyError> {
        let (p, q, _r) =
            crate::forms::char0::surreal_signature(metric).ok_or_else(|| char0_failure(metric))?;
        Ok(WittClassG::char0(p, q))
    }
}

impl<const P: u128> ClassifyWitt for Fp<P> {
    fn witt_class(metric: &Metric<Self>) -> Result<WittClassG, ClassifyError> {
        finite_odd_witt(metric).ok_or_else(|| char0_failure(metric))
    }
}

impl<const P: u128, const N: usize> ClassifyWitt for Fpn<P, N> {
    fn witt_class(metric: &Metric<Self>) -> Result<WittClassG, ClassifyError> {
        if P == 2 {
            let arf = arf_fpn_char2(metric).ok_or_else(|| generic_failure(metric))?;
            if arf.radical_dim != 0 {
                return Err(ClassifyError::SingularForm {
                    radical_dim: arf.radical_dim,
                    radical_anisotropic: arf.radical_anisotropic,
                });
            }
            Ok(WittClassG::Char2 {
                field_degree: N as u128,
                arf: arf.arf,
            })
        } else {
            finite_odd_witt(metric).ok_or_else(|| char0_failure(metric))
        }
    }
}

impl ClassifyWitt for Nimber {
    fn witt_class(metric: &Metric<Self>) -> Result<WittClassG, ClassifyError> {
        WittClassG::try_char2_from_metric(metric).map_err(ClassifyError::from)
    }
}

impl ClassifyWitt for Ordinal {
    fn witt_class(metric: &Metric<Self>) -> Result<WittClassG, ClassifyError> {
        let arf = arf_ordinal_finite(metric).ok_or_else(|| generic_failure(metric))?;
        if arf.radical_dim != 0 {
            return Err(ClassifyError::SingularForm {
                radical_dim: arf.radical_dim,
                radical_anisotropic: arf.radical_anisotropic,
            });
        }
        Ok(WittClassG::Char2 {
            field_degree: ordinal_char2_field_degree(metric)
                .ok_or(ClassifyError::UnsupportedFieldOrWindow)?,
            arf: arf.arf,
        })
    }
}

impl ClassifyIsometry for Surreal {
    fn isometric(m1: &Metric<Self>, m2: &Metric<Self>) -> Result<bool, ClassifyError> {
        isometric_real(m1, m2).ok_or_else(|| two_metric_failure(m1, m2, char0_failure))
    }
}

impl ClassifyIsometry for Surcomplex<Surreal> {
    fn isometric(m1: &Metric<Self>, m2: &Metric<Self>) -> Result<bool, ClassifyError> {
        isometric_surcomplex(m1, m2).ok_or_else(|| two_metric_failure(m1, m2, char0_failure))
    }
}

impl ClassifyIsometry for Rational {
    fn isometric(m1: &Metric<Self>, m2: &Metric<Self>) -> Result<bool, ClassifyError> {
        isometric_rational(m1, m2).ok_or_else(|| two_metric_failure(m1, m2, char0_failure))
    }
}

impl<const P: u128> ClassifyIsometry for Fp<P> {
    fn isometric(m1: &Metric<Self>, m2: &Metric<Self>) -> Result<bool, ClassifyError> {
        isometric_finite_odd(m1, m2).ok_or_else(|| two_metric_failure(m1, m2, char0_failure))
    }
}

impl<const P: u128, const N: usize> ClassifyIsometry for Fpn<P, N> {
    fn isometric(m1: &Metric<Self>, m2: &Metric<Self>) -> Result<bool, ClassifyError> {
        if P == 2 {
            isometric_fpn_char2(m1, m2).ok_or_else(|| two_metric_failure(m1, m2, generic_failure))
        } else {
            isometric_finite_odd(m1, m2).ok_or_else(|| two_metric_failure(m1, m2, char0_failure))
        }
    }
}

impl ClassifyIsometry for Nimber {
    fn isometric(m1: &Metric<Self>, m2: &Metric<Self>) -> Result<bool, ClassifyError> {
        isometric_nimber(m1, m2).ok_or_else(|| two_metric_failure(m1, m2, generic_failure))
    }
}

impl ClassifyIsometry for Ordinal {
    fn isometric(m1: &Metric<Self>, m2: &Metric<Self>) -> Result<bool, ClassifyError> {
        isometric_ordinal_finite(m1, m2).ok_or_else(|| two_metric_failure(m1, m2, generic_failure))
    }
}

impl DecomposeWitt for Surreal {
    type Decomp = RealWittDecomp;
    fn witt_decompose(metric: &Metric<Self>) -> Result<Self::Decomp, ClassifyError> {
        witt_decompose_real(metric).ok_or_else(|| char0_failure(metric))
    }
}

impl<const P: u128> DecomposeWitt for Fp<P> {
    type Decomp = OddWittDecomp;
    fn witt_decompose(metric: &Metric<Self>) -> Result<Self::Decomp, ClassifyError> {
        witt_decompose_finite_odd(metric).ok_or_else(|| char0_failure(metric))
    }
}

impl<const P: u128, const N: usize> DecomposeWitt for Fpn<P, N> {
    type Decomp = FiniteFieldWittDecomp;
    fn witt_decompose(metric: &Metric<Self>) -> Result<Self::Decomp, ClassifyError> {
        if P == 2 {
            let arf = arf_fpn_char2(metric).ok_or_else(|| generic_failure(metric))?;
            Ok(FiniteFieldWittDecomp::Char2(Char2WittDecomp::from_arf(
                N as u128, &arf,
            )))
        } else {
            witt_decompose_finite_odd(metric)
                .map(FiniteFieldWittDecomp::Odd)
                .ok_or_else(|| char0_failure(metric))
        }
    }
}

impl ClassifyBrauerWall for Surreal {
    fn bw_class(metric: &Metric<Self>) -> Result<BrauerWallClass, ClassifyError> {
        bw_class_real(metric).ok_or_else(|| char0_failure(metric))
    }
}

impl ClassifyBrauerWall for Surcomplex<Surreal> {
    fn bw_class(metric: &Metric<Self>) -> Result<BrauerWallClass, ClassifyError> {
        bw_class_complex(metric).ok_or_else(|| char0_failure(metric))
    }
}

impl<const P: u128> ClassifyBrauerWall for Fp<P> {
    fn bw_class(metric: &Metric<Self>) -> Result<BrauerWallClass, ClassifyError> {
        bw_class_finite_odd(metric).ok_or_else(|| char0_failure(metric))
    }
}

impl<const P: u128, const N: usize> ClassifyBrauerWall for Fpn<P, N> {
    fn bw_class(metric: &Metric<Self>) -> Result<BrauerWallClass, ClassifyError> {
        if P == 2 {
            let arf = arf_fpn_char2(metric).ok_or_else(|| generic_failure(metric))?;
            if arf.radical_dim != 0 {
                return Err(ClassifyError::SingularForm {
                    radical_dim: arf.radical_dim,
                    radical_anisotropic: arf.radical_anisotropic,
                });
            }
            Ok(BrauerWallClass::Char2 {
                field_degree: N as u128,
                arf: arf.arf,
            })
        } else {
            bw_class_finite_odd(metric).ok_or_else(|| char0_failure(metric))
        }
    }
}

impl ClassifyBrauerWall for Nimber {
    fn bw_class(metric: &Metric<Self>) -> Result<BrauerWallClass, ClassifyError> {
        bw_class_nimber(metric).ok_or_else(|| char2_nimber_failure(metric))
    }
}

impl ClassifyBrauerWall for Ordinal {
    fn bw_class(metric: &Metric<Self>) -> Result<BrauerWallClass, ClassifyError> {
        let arf = arf_ordinal_finite(metric).ok_or_else(|| generic_failure(metric))?;
        if arf.radical_dim != 0 {
            return Err(ClassifyError::SingularForm {
                radical_dim: arf.radical_dim,
                radical_anisotropic: arf.radical_anisotropic,
            });
        }
        Ok(BrauerWallClass::Char2 {
            field_degree: ordinal_char2_field_degree(metric)
                .ok_or(ClassifyError::UnsupportedFieldOrWindow)?,
            arf: arf.arf,
        })
    }
}

fn ordinal_char2_field_degree(metric: &Metric<Ordinal>) -> Option<u128> {
    ordinal_metric_finite_subfield_degree(metric)
}

/// Ergonomic methods so callers can write `metric.classify()` /
/// `algebra.classify()` instead of `S::classify(&metric)`.
///
/// These methods return `Result<_, ClassifyError>` so callers can distinguish
/// *why* a classification failed (unsupported field, diagonalizer failure, …)
/// without reading the AGENTS docs. The underlying trait methods stay `Option`
/// for the single-valued partial-math cases.
impl<S: ClassifyForm> Metric<S> {
    /// Classify the form (see [`ClassifyForm`]).
    pub fn classify(&self) -> Result<S::Class, ClassifyError> {
        S::classify(self)
    }
}

impl<S: ClassifyWitt> Metric<S> {
    /// The unified Witt class (see [`ClassifyWitt`]).
    pub fn witt_class(&self) -> Result<WittClassG, ClassifyError> {
        S::witt_class(self)
    }
}

impl<S: ClassifyIsometry> Metric<S> {
    /// Test isometry against another form over the same scalar world.
    pub fn isometric_to(&self, other: &Self) -> Result<bool, ClassifyError> {
        S::isometric(self, other)
    }
}

impl<S: DecomposeWitt> Metric<S> {
    /// Split the form into hyperbolic planes plus anisotropic kernel data.
    pub fn witt_decompose(&self) -> Result<S::Decomp, ClassifyError> {
        S::witt_decompose(self)
    }
}

impl<S: ClassifyBrauerWall> Metric<S> {
    /// The Brauer-Wall class of the attached Clifford algebra.
    pub fn bw_class(&self) -> Result<BrauerWallClass, ClassifyError> {
        S::bw_class(self)
    }
}

impl<S: ClassifyForm> CliffordAlgebra<S> {
    /// Classify the algebra's underlying form (see [`ClassifyForm`]).
    pub fn classify(&self) -> Result<S::Class, ClassifyError> {
        S::classify(&self.metric)
    }
}

impl<S: ClassifyWitt> CliffordAlgebra<S> {
    /// The unified Witt class of the algebra's form (see [`ClassifyWitt`]).
    pub fn witt_class(&self) -> Result<WittClassG, ClassifyError> {
        S::witt_class(&self.metric)
    }
}

impl<S: ClassifyIsometry> CliffordAlgebra<S> {
    /// Test isometry of the underlying forms.
    pub fn isometric_to(&self, other: &Self) -> Result<bool, ClassifyError> {
        S::isometric(&self.metric, &other.metric)
    }
}

impl<S: DecomposeWitt> CliffordAlgebra<S> {
    /// Witt decomposition of the algebra's underlying form.
    pub fn witt_decompose(&self) -> Result<S::Decomp, ClassifyError> {
        S::witt_decompose(&self.metric)
    }
}

impl<S: ClassifyBrauerWall> CliffordAlgebra<S> {
    /// Brauer-Wall class of the algebra.
    pub fn bw_class(&self) -> Result<BrauerWallClass, ClassifyError> {
        S::bw_class(&self.metric)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clifford::Metric;

    #[test]
    fn classify_dispatches_on_scalar_type() {
        // char 0, real-closed: Cl(2,0) over the surreals matches classify_surreal.
        let m = Metric::diagonal(vec![Surreal::one(), Surreal::one()]);
        assert_eq!(m.classify().ok(), classify_surreal(&m));
        assert!(m.classify().is_ok());

        // char 2: Arf via the trait matches arf_invariant, and witt_class agrees.
        let n = Metric::diagonal(vec![Nimber::one(), Nimber::one()]);
        assert_eq!(n.classify().ok(), arf_invariant(&n));
        assert_eq!(
            n.witt_class().ok(),
            WittClassG::try_char2_from_metric(&n).ok()
        );
        assert_eq!(n.bw_class().ok(), bw_class_nimber(&n));

        // odd char: F_5 dispatch produces the odd-char datum.
        let f = Metric::diagonal(vec![Fp::<5>::from_int(1), Fp::<5>::from_int(2)]);
        assert_eq!(f.classify().ok(), classify_finite_odd(&f));
        assert_eq!(f.witt_class().ok(), finite_odd_witt(&f));

        // finite extension field: the same façade reaches the generic odd-field leg.
        let f9 = Metric::diagonal(vec![Fpn::<3, 2>::constant(1), Fpn::<3, 2>::generator()]);
        assert_eq!(
            f9.classify().ok(),
            classify_finite_odd(&f9).map(FiniteFieldInvariants::Odd)
        );
        assert_eq!(f9.witt_class().ok(), finite_odd_witt(&f9));

        // finite extension field, characteristic 2: the same façade now reaches
        // the generic Arf leg rather than falling through the odd-char classifier.
        let mut b = std::collections::BTreeMap::new();
        b.insert((0usize, 1usize), Fpn::<2, 3>::one());
        let f8 = Metric::new(vec![Fpn::<2, 3>::generator(), Fpn::<2, 3>::generator()], b);
        assert_eq!(
            f8.classify().ok(),
            arf_fpn_char2(&f8).map(FiniteFieldInvariants::Char2)
        );
        assert!(matches!(f8.classify(), Ok(FiniteFieldInvariants::Char2(_))));

        // ordinal-nimber coefficients classify inside detected finite windows;
        // the first transfinite one here is F_4(ω) = F_64.
        let mut b = std::collections::BTreeMap::new();
        b.insert((0usize, 1usize), Ordinal::one());
        let omega = Ordinal::omega();
        let ord = Metric::new(vec![omega.clone(), omega], b);
        let arf = arf_ordinal_finite(&ord).unwrap();
        assert_eq!(ord.classify().ok(), Some(arf.clone()));
        assert_eq!(
            ord.witt_class().ok(),
            Some(WittClassG::Char2 {
                field_degree: 6,
                arf: arf.arf
            })
        );
        assert_eq!(
            ord.bw_class().ok(),
            Some(BrauerWallClass::Char2 {
                field_degree: 6,
                arf: arf.arf
            })
        );

        let outside_window = Metric::diagonal(vec![Ordinal::omega_pow(Ordinal::omega())]);
        assert!(outside_window.classify().is_ok());
        assert_eq!(ordinal_char2_field_degree(&outside_window), Some(20));

        let outside_segment = Metric::diagonal(vec![Ordinal::omega_pow(Ordinal::omega_pow(
            Ordinal::omega(),
        ))]);
        assert!(outside_segment.classify().is_err());
        assert!(outside_segment.bw_class().is_err());
    }

    #[test]
    fn algebra_classify_matches_metric_classify() {
        let alg = CliffordAlgebra::new(
            2,
            Metric::diagonal(vec![Surreal::one(), Surreal::one().neg()]),
        );
        assert_eq!(alg.classify(), alg.metric.classify());
        assert_eq!(alg.witt_class(), alg.metric.witt_class());
        assert_eq!(alg.witt_decompose(), alg.metric.witt_decompose());
        assert_eq!(alg.bw_class(), alg.metric.bw_class());
    }

    #[test]
    fn structural_facades_dispatch() {
        let f = Metric::diagonal(vec![Fp::<5>::from_int(1), Fp::<5>::from_int(1)]);
        let g = Metric::diagonal(vec![Fp::<5>::from_int(2), Fp::<5>::from_int(3)]);
        assert_eq!(f.isometric_to(&g).ok(), isometric_finite_odd(&f, &g));
        assert_eq!(f.witt_decompose().ok(), witt_decompose_finite_odd(&f));
        assert_eq!(f.bw_class().ok(), bw_class_finite_odd(&f));

        let f9 = Metric::diagonal(vec![Fpn::<3, 2>::constant(1), Fpn::<3, 2>::constant(1)]);
        let g9 = Metric::diagonal(vec![Fpn::<3, 2>::constant(2), Fpn::<3, 2>::constant(2)]);
        assert_eq!(f9.isometric_to(&g9).ok(), isometric_finite_odd(&f9, &g9));
        assert_eq!(
            f9.witt_decompose().ok(),
            witt_decompose_finite_odd(&f9).map(FiniteFieldWittDecomp::Odd)
        );
        assert_eq!(f9.bw_class().ok(), bw_class_finite_odd(&f9));

        let mut b = std::collections::BTreeMap::new();
        b.insert((0usize, 1usize), Fpn::<2, 3>::one());
        let f8 = Metric::new(vec![Fpn::<2, 3>::zero(), Fpn::<2, 3>::zero()], b);
        assert_eq!(
            f8.witt_decompose().ok(),
            Some(FiniteFieldWittDecomp::Char2(Char2WittDecomp {
                field_degree: 3,
                witt_index: 1,
                core_anisotropic_dim: 0,
                radical_dim: 0,
                radical_anisotropic: false,
                arf: 0,
            }))
        );
        assert_eq!(
            f8.bw_class().ok(),
            Some(BrauerWallClass::Char2 {
                field_degree: 3,
                arf: 0
            })
        );

        let mut b = std::collections::BTreeMap::new();
        b.insert((0usize, 1usize), Nimber::one());
        let n = Metric::new(vec![Nimber::zero(), Nimber::zero()], b);
        assert_eq!(n.bw_class().ok(), bw_class_nimber(&n));

        let mut b = std::collections::BTreeMap::new();
        b.insert((0usize, 1usize), Ordinal::one());
        let ord = Metric::new(vec![Ordinal::omega(), Ordinal::omega()], b);
        assert_eq!(ord.isometric_to(&ord).ok(), Some(true));
    }

    #[test]
    fn classify_error_distinguishes_general_bilinear_from_window() {
        let mut a = std::collections::BTreeMap::new();
        a.insert((0usize, 1usize), Nimber(1));
        let metric = Metric::general(
            vec![Nimber(1), Nimber(1)],
            std::collections::BTreeMap::<(usize, usize), Nimber>::new(),
            a,
        );
        assert!(matches!(
            metric.witt_class(),
            Err(ClassifyError::GeneralBilinearMetric)
        ));
        assert!(matches!(
            metric.classify(),
            Err(ClassifyError::GeneralBilinearMetric)
        ));
    }

    #[test]
    fn classify_error_reports_singular_form_with_radical_data() {
        // Empty polar form in char 2: the whole space is the polar radical, and
        // q is nonzero on it, so the Witt/BW classes must refuse with the
        // radical data rather than a catch-all.
        let metric = Metric::diagonal(vec![Nimber(1), Nimber(0)]);
        match metric.witt_class() {
            Err(ClassifyError::SingularForm {
                radical_dim,
                radical_anisotropic,
            }) => {
                assert_eq!(radical_dim, 2);
                assert!(radical_anisotropic);
            }
            other => panic!("expected SingularForm, got {other:?}"),
        }
    }
}
