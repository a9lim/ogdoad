//! Mod-two Milnor symbols and Milnor residue maps assembled as global Witt
//! invariants.
//!
//! The symbol layer exposes the part of Milnor K-theory already computed by the
//! crate's form and Brauer surfaces:
//!
//! ```text
//! K^M_0(F)/2 = Z/2,
//! K^M_1(F)/2 = F*/F*^2,
//! K^M_2(F)/2 = H^2(F, Z/2) = Br(F)[2]       (char(F) != 2).
//! ```
//!
//! [`Mod2MilnorField`] constructs the pure symbols `{a}` and `{a,b}`. The
//! degree-one carriers are square classes; the degree-two carriers reuse the
//! exact quaternion/Brauer classes already maintained by the rational and
//! odd-characteristic function-field layers. [`ClassifyMilnor`] exposes the
//! strict graded maps `e_0`, `e_1`, and `e_2` on metrics: unlike a reporting
//! tuple, `e_n` returns [`MilnorInvariantError::OutsideFundamentalIdeal`] unless
//! the form actually lies in `I^n`.
//!
//! This module deliberately stops at degree two and characteristic not two.
//! Characteristic-two quadratic Witt theory uses the Kato/Artin--Schreier
//! filtration rather than this Milnor filtration, and wild local norm-residue
//! symbols remain outside the implemented surface.
//!
//! The Springer layer computes per-place residue buckets; this module assembles
//! the Witt-group-level maps supplied by Milnor's exact sequence
//! (Milnor–Husemoller, *Symmetric Bilinear Forms*, Ch. IV; Lam, GSM 67, Ch. IX):
//!
//! ```text
//! 0 → W(ℤ) → W(ℚ) →∂ ⊕_p W(F_p) → 0        (exact)
//! ```
//!
//! The kernel `W(ℤ) ≅ ℤ` is detected by the **signature**; for odd `p`, the boundary
//! `∂_p` is the **second Springer residue** lifted from `LocalResidueForm` buckets to
//! Witt classes. For `p = 2`, Milnor's hand-defined boundary lands in
//! `W(F₂) ≅ ℤ/2`: a diagonal line contributes exactly when its `2`-adic valuation is
//! odd (the residue unit is then the unique nonzero element of `F₂`). So
//! `(signature, (∂_p)_p)` is a *complete* invariant of `W(ℚ)`: two rational diagonal
//! forms are Witt-equivalent over `ℚ` iff they share a signature and all residues —
//! the sequence ties three pillar surfaces together (the Springer residues, the
//! global field layer, and the integral pillar's signature).
//!
//! The equal-characteristic odd leg uses the split form of the same idea:
//!
//! ```text
//! W(F_q(t)) ≅ W(F_q) ⊕ ⊕_π W(F_q[t]/π).
//! ```
//!
//! [`global_residues_ff`] returns the `W(F_q)` summand from the even-valuation layer
//! at the degree place `∞`, plus the nonzero second residues at finite monic
//! irreducible places. This is exact on the `RationalFunction`/`Poly`
//! backend and uses the same `FunctionFieldPlace` arithmetic as the function-field Hilbert and
//! Hasse–Minkowski layers.
//!
//! The residue is computed directly from the `i128` entries (`v_p`, the Legendre
//! symbol, and the signed-discriminant square class), matching the
//! [`finite_odd_witt`](crate::forms::finite_odd_witt) convention, so it is **exact**;
//! `springer_decompose_qp` on the capped `Q_p` model supplies a computational
//! cross-check.
//!
//! **The `∂₂` boundary (load-bearing).** `∂₂` (residue characteristic 2) is **not**
//! Springer's second residue — Milnor defines it by hand in Ch. IV. This module uses
//! the crate's existing char-2 [`WittClassG`] carrier as the `W(F₂) ≅ ℤ/2` target:
//! `Char2 { field_degree: 1, arf }`, with `arf` the parity of odd dyadic valuation
//! lines. The char-2 constant fields of `F_q(t)` are a separate matter (the
//! Aravire–Jacob layer in `springer/char2.rs`), and tame/wild norm-residue symbols
//! are outside this Witt-residue map.

use crate::forms::{
    as_diagonal, bw_class_function_field, bw_class_rational, finite_odd_witt, is_global_square_ff,
    legendre, relevant_primes, try_chi_kappa, try_hilbert_symbol_qp, try_kappa_order,
    try_relevant_places_ff, try_residue_unit_at, try_square_free, try_tame_symbol_exponent_ff,
    try_valuation_at_ff, unit_part, val_p, Brauer2Class, FiniteOddField, FunctionFieldBrauer2Class,
    FunctionFieldPlace, WittClassG,
};
use crate::scalar::{
    is_prime_u128, ExactFieldScalar, Fp, Fpn, Poly, Rational, RationalFunction, Scalar,
};
use std::collections::BTreeMap;

// ---------------------------------------------------------------------------
// Degree <= 2 mod-two Milnor classes and pure symbols.
// ---------------------------------------------------------------------------

/// A class in `K^M_0(F)/2 = Z/2`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MilnorK0Class(u128);

impl MilnorK0Class {
    /// Construct the parity class of an integer.
    pub fn from_parity(value: u128) -> Self {
        MilnorK0Class(value & 1)
    }

    /// Construct the degree-zero class of a vector-space dimension.
    pub fn from_dimension(dim: usize) -> Self {
        MilnorK0Class((dim & 1) as u128)
    }

    /// The representative bit, `0` or `1`.
    pub fn value(self) -> u128 {
        self.0
    }

    /// Addition in `Z/2`.
    pub fn sum(self, other: Self) -> Self {
        MilnorK0Class(self.0 ^ other.0)
    }

    /// Multiplication in `Z/2`.
    pub fn product(self, other: Self) -> Self {
        MilnorK0Class(self.0 & other.0)
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for MilnorK0Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MilnorK0Mod2({})", self.0)
    }
}

/// A class in `K^M_1(Q)/2 = Q*/Q*^2`, stored as a nonzero square-free `i128`
/// representative. A rational `n/d` has the same square class as `n*d`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RationalMilnorK1Class {
    representative: i128,
}

impl RationalMilnorK1Class {
    /// Construct `{a}` for a nonzero rational `a`. `None` on zero or bounded
    /// `i128` overflow while reducing the square class.
    pub fn from_rational(a: &Rational) -> Option<Self> {
        if a.is_zero() {
            return None;
        }
        let representative = try_square_free(a.numer().checked_mul(a.denom())?)?;
        Some(RationalMilnorK1Class { representative })
    }

    fn from_representative(representative: i128) -> Option<Self> {
        let representative = try_square_free(representative)?;
        (representative != 0).then_some(RationalMilnorK1Class { representative })
    }

    /// The canonical square-free representative.
    pub fn representative(self) -> i128 {
        self.representative
    }

    /// Whether this is the trivial square class.
    pub fn is_trivial(self) -> bool {
        self.representative == 1
    }

    /// Addition in `K^M_1/2`, induced by multiplication in `Q*`.
    /// `None` if the bounded representative product overflows.
    pub fn try_add(self, other: Self) -> Option<Self> {
        RationalMilnorK1Class::from_representative(
            self.representative.checked_mul(other.representative)?,
        )
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for RationalMilnorK1Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MilnorK1Mod2(Q; {})", self.representative)
    }
}

/// A class in `K^M_1(F_q)/2 = F_q*/F_q*^2` for an odd finite field, including
/// residue extensions whose concrete scalar type is selected dynamically by a
/// place. The class bit is `0` for a square and `1` for a nonsquare.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FiniteFieldMilnorK1Class {
    characteristic: u128,
    field_order: u128,
    nonsquare: u128,
}

impl FiniteFieldMilnorK1Class {
    fn new(characteristic: u128, field_order: u128, nonsquare: u128) -> Option<Self> {
        (characteristic != 2 && nonsquare <= 1).then_some(FiniteFieldMilnorK1Class {
            characteristic,
            field_order,
            nonsquare,
        })
    }

    /// Characteristic prime of the finite field.
    pub fn characteristic(self) -> u128 {
        self.characteristic
    }

    /// Order of the finite field.
    pub fn field_order(self) -> u128 {
        self.field_order
    }

    /// The square-class bit: `0` for square, `1` for nonsquare.
    pub fn nonsquare(self) -> u128 {
        self.nonsquare
    }

    /// Whether this is the trivial square class.
    pub fn is_trivial(self) -> bool {
        self.nonsquare == 0
    }

    /// Addition in `K^M_1/2`. `None` when the operands name different fields.
    pub fn try_add(self, other: Self) -> Option<Self> {
        if self.characteristic != other.characteristic || self.field_order != other.field_order {
            return None;
        }
        FiniteFieldMilnorK1Class::new(
            self.characteristic,
            self.field_order,
            self.nonsquare ^ other.nonsquare,
        )
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for FiniteFieldMilnorK1Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "MilnorK1Mod2(F_{}; {})",
            self.field_order, self.nonsquare
        )
    }
}

/// The unique class in `K^M_2(F_q)/2 = 0` for a finite field of odd
/// characteristic. Field metadata prevents accidental cross-field addition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FiniteFieldMilnorK2Class {
    characteristic: u128,
    field_order: u128,
}

impl FiniteFieldMilnorK2Class {
    fn new(characteristic: u128, field_order: u128) -> Option<Self> {
        (characteristic != 2).then_some(FiniteFieldMilnorK2Class {
            characteristic,
            field_order,
        })
    }

    /// Characteristic prime of the finite field.
    pub fn characteristic(self) -> u128 {
        self.characteristic
    }

    /// Order of the finite field.
    pub fn field_order(self) -> u128 {
        self.field_order
    }

    /// Every degree-two mod-two Milnor class over a finite field is trivial.
    pub fn is_trivial(self) -> bool {
        true
    }

    /// Addition in the trivial group. `None` when the operands name different
    /// fields.
    pub fn try_add(self, other: Self) -> Option<Self> {
        (self == other).then_some(self)
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for FiniteFieldMilnorK2Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MilnorK2Mod2(F_{}; 0)", self.field_order)
    }
}

/// A class in `K^M_1(F_q(t))/2`, stored by a nonzero representative. Equality
/// is equality modulo global squares, not literal rational-function equality.
#[derive(Debug, Clone)]
pub struct FunctionFieldMilnorK1Class<S: FiniteOddField> {
    representative: RationalFunction<S>,
}

impl<S: FiniteOddField> FunctionFieldMilnorK1Class<S> {
    fn new(representative: RationalFunction<S>) -> Option<Self> {
        (!representative.is_zero()).then_some(FunctionFieldMilnorK1Class { representative })
    }

    /// A representative of the global square class.
    pub fn representative(&self) -> &RationalFunction<S> {
        &self.representative
    }

    /// Whether the representative is a global square.
    pub fn is_trivial(&self) -> bool {
        is_global_square_ff(&self.representative)
    }

    /// Addition in `K^M_1/2`, induced by multiplication in `F_q(t)*`.
    pub fn add(&self, other: &Self) -> Self {
        FunctionFieldMilnorK1Class {
            representative: self.representative.mul(&other.representative),
        }
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl<S: FiniteOddField> PartialEq for FunctionFieldMilnorK1Class<S> {
    fn eq(&self, other: &Self) -> bool {
        let Some(other_inv) = other.representative.inv() else {
            return false;
        };
        is_global_square_ff(&self.representative.mul(&other_inv))
    }
}

impl<S: FiniteOddField> Eq for FunctionFieldMilnorK1Class<S> {}

impl<S: FiniteOddField> std::fmt::Display for FunctionFieldMilnorK1Class<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "MilnorK1Mod2(F_{}(t); {})",
            S::field_order(),
            self.representative
        )
    }
}

/// `K^M_2(Q)/2`, realized by the norm-residue map as the rational two-torsion
/// Brauer group.
pub type RationalMilnorK2Class = Brauer2Class;

/// `K^M_2(F_q(t))/2`, realized by the norm-residue map as the function-field
/// two-torsion Brauer group.
pub type FunctionFieldMilnorK2Class<S> = FunctionFieldBrauer2Class<S>;

/// Exact characteristic-not-two fields for which Ogdoad exposes degree-one and
/// degree-two mod-two Milnor symbols.
pub trait Mod2MilnorField: ExactFieldScalar {
    /// Carrier of `K^M_1(Self)/2`.
    type K1Class;
    /// Carrier of `K^M_2(Self)/2`.
    type K2Class;

    /// Whether this monomorphization is inside the implemented
    /// characteristic-not-two field domain.
    fn supports_mod2_milnor() -> bool;

    /// The degree-one pure symbol `{a}`. `None` for `a = 0` or when bounded
    /// square-class arithmetic leaves the represented domain.
    fn milnor_symbol_1(a: &Self) -> Option<Self::K1Class>;

    /// The degree-two pure symbol `{a,b}`. `None` if either argument is zero or
    /// when the exact Brauer calculation leaves the represented domain.
    fn milnor_symbol_2(a: &Self, b: &Self) -> Option<Self::K2Class>;
}

fn finite_milnor_symbol_1<F: FiniteOddField>(a: &F) -> Option<FiniteFieldMilnorK1Class> {
    F::ensure_supported()?;
    if a.is_zero() {
        return None;
    }
    FiniteFieldMilnorK1Class::new(
        F::characteristic_prime(),
        F::field_order(),
        u128::from(!F::is_square_value(*a)),
    )
}

fn finite_milnor_symbol_2<F: FiniteOddField>(a: &F, b: &F) -> Option<FiniteFieldMilnorK2Class> {
    F::ensure_supported()?;
    if a.is_zero() || b.is_zero() {
        return None;
    }
    FiniteFieldMilnorK2Class::new(F::characteristic_prime(), F::field_order())
}

impl Mod2MilnorField for Rational {
    type K1Class = RationalMilnorK1Class;
    type K2Class = RationalMilnorK2Class;

    fn supports_mod2_milnor() -> bool {
        true
    }

    fn milnor_symbol_1(a: &Self) -> Option<Self::K1Class> {
        RationalMilnorK1Class::from_rational(a)
    }

    fn milnor_symbol_2(a: &Self, b: &Self) -> Option<Self::K2Class> {
        let a = RationalMilnorK1Class::from_rational(a)?.representative();
        let b = RationalMilnorK1Class::from_rational(b)?.representative();
        Brauer2Class::quaternion(a, b)
    }
}

impl<const P: u128> Mod2MilnorField for Fp<P> {
    type K1Class = FiniteFieldMilnorK1Class;
    type K2Class = FiniteFieldMilnorK2Class;

    fn supports_mod2_milnor() -> bool {
        <Self as FiniteOddField>::is_supported_odd_field()
    }

    fn milnor_symbol_1(a: &Self) -> Option<Self::K1Class> {
        finite_milnor_symbol_1(a)
    }

    fn milnor_symbol_2(a: &Self, b: &Self) -> Option<Self::K2Class> {
        finite_milnor_symbol_2(a, b)
    }
}

impl<const P: u128, const N: usize> Mod2MilnorField for Fpn<P, N> {
    type K1Class = FiniteFieldMilnorK1Class;
    type K2Class = FiniteFieldMilnorK2Class;

    fn supports_mod2_milnor() -> bool {
        <Self as FiniteOddField>::is_supported_odd_field()
    }

    fn milnor_symbol_1(a: &Self) -> Option<Self::K1Class> {
        finite_milnor_symbol_1(a)
    }

    fn milnor_symbol_2(a: &Self, b: &Self) -> Option<Self::K2Class> {
        finite_milnor_symbol_2(a, b)
    }
}

impl<S: FiniteOddField> Mod2MilnorField for RationalFunction<S> {
    type K1Class = FunctionFieldMilnorK1Class<S>;
    type K2Class = FunctionFieldMilnorK2Class<S>;

    fn supports_mod2_milnor() -> bool {
        S::is_supported_odd_field()
    }

    fn milnor_symbol_1(a: &Self) -> Option<Self::K1Class> {
        S::ensure_supported()?;
        FunctionFieldMilnorK1Class::new(a.clone())
    }

    fn milnor_symbol_2(a: &Self, b: &Self) -> Option<Self::K2Class> {
        S::ensure_supported()?;
        FunctionFieldBrauer2Class::quaternion(a, b)
    }
}

/// Construct the degree-one pure symbol `{a}` generically.
pub fn milnor_symbol_1<F: Mod2MilnorField>(a: &F) -> Option<F::K1Class> {
    F::milnor_symbol_1(a)
}

/// Construct the degree-two pure symbol `{a,b}` generically.
pub fn milnor_symbol_2<F: Mod2MilnorField>(a: &F, b: &F) -> Option<F::K2Class> {
    F::milnor_symbol_2(a, b)
}

// ---------------------------------------------------------------------------
// Strict e_n maps on the fundamental-ideal filtration.
// ---------------------------------------------------------------------------

/// Why a strict mod-two Milnor invariant of a metric is undefined.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MilnorInvariantError {
    /// The metric could not be diagonalized in the implemented
    /// characteristic-not-two field domain.
    DiagonalizerFailure,
    /// The diagonalized form has a nonzero radical, so it does not represent a
    /// class in the nonsingular Witt ring.
    SingularForm {
        /// Dimension of the radical.
        radical_dim: usize,
    },
    /// `e_n` was requested for a form outside `I^n`.
    OutsideFundamentalIdeal {
        /// Requested power `n`.
        power: usize,
    },
    /// The field parameters or bounded exact arithmetic are outside the
    /// implemented symbol surface.
    UnsupportedFieldOrArithmetic,
}

impl std::fmt::Display for MilnorInvariantError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MilnorInvariantError::DiagonalizerFailure => {
                f.write_str("metric could not be diagonalized for mod-two Milnor invariants")
            }
            MilnorInvariantError::SingularForm { radical_dim } => {
                write!(
                    f,
                    "Milnor invariants require a nonsingular form (radical_dim={radical_dim})"
                )
            }
            MilnorInvariantError::OutsideFundamentalIdeal { power } => {
                write!(f, "form is outside the fundamental-ideal power I^{power}")
            }
            MilnorInvariantError::UnsupportedFieldOrArithmetic => {
                f.write_str("field or bounded arithmetic is outside the mod-two Milnor surface")
            }
        }
    }
}

fn strict_diagonal<S: Scalar>(
    metric: &crate::clifford::Metric<S>,
) -> Result<crate::clifford::Metric<S>, MilnorInvariantError> {
    let diagonal = as_diagonal(metric).ok_or(MilnorInvariantError::DiagonalizerFailure)?;
    let radical_dim = diagonal.q().iter().filter(|x| x.is_zero()).count();
    if radical_dim != 0 {
        return Err(MilnorInvariantError::SingularForm { radical_dim });
    }
    Ok(diagonal)
}

pub(crate) fn strict_milnor_e0<F: Mod2MilnorField>(
    metric: &crate::clifford::Metric<F>,
) -> Result<MilnorK0Class, MilnorInvariantError> {
    if !F::supports_mod2_milnor() {
        return Err(MilnorInvariantError::UnsupportedFieldOrArithmetic);
    }
    let diagonal = strict_diagonal(metric)?;
    Ok(MilnorK0Class::from_dimension(diagonal.dim()))
}

pub(crate) fn finite_milnor_e1<F: FiniteOddField>(
    metric: &crate::clifford::Metric<F>,
) -> Result<FiniteFieldMilnorK1Class, MilnorInvariantError> {
    F::ensure_supported().ok_or(MilnorInvariantError::UnsupportedFieldOrArithmetic)?;
    let diagonal = strict_diagonal(metric)?;
    let WittClassG::OddChar {
        e0,
        sclass,
        field_order,
        ..
    } = finite_odd_witt(&diagonal).ok_or(MilnorInvariantError::UnsupportedFieldOrArithmetic)?
    else {
        unreachable!("finite_odd_witt returns the odd-characteristic variant")
    };
    if e0 != 0 {
        return Err(MilnorInvariantError::OutsideFundamentalIdeal { power: 1 });
    }
    FiniteFieldMilnorK1Class::new(F::characteristic_prime(), field_order, sclass)
        .ok_or(MilnorInvariantError::UnsupportedFieldOrArithmetic)
}

pub(crate) fn finite_milnor_e2<F: FiniteOddField>(
    metric: &crate::clifford::Metric<F>,
) -> Result<FiniteFieldMilnorK2Class, MilnorInvariantError> {
    let e1 = finite_milnor_e1(metric)?;
    if !e1.is_trivial() {
        return Err(MilnorInvariantError::OutsideFundamentalIdeal { power: 2 });
    }
    FiniteFieldMilnorK2Class::new(e1.characteristic(), e1.field_order())
        .ok_or(MilnorInvariantError::UnsupportedFieldOrArithmetic)
}

pub(crate) fn rational_milnor_e1(
    metric: &crate::clifford::Metric<Rational>,
) -> Result<RationalMilnorK1Class, MilnorInvariantError> {
    let diagonal = strict_diagonal(metric)?;
    let bw =
        bw_class_rational(&diagonal).ok_or(MilnorInvariantError::UnsupportedFieldOrArithmetic)?;
    if bw.dimension_parity() != 0 {
        return Err(MilnorInvariantError::OutsideFundamentalIdeal { power: 1 });
    }
    RationalMilnorK1Class::from_representative(bw.signed_discriminant())
        .ok_or(MilnorInvariantError::UnsupportedFieldOrArithmetic)
}

pub(crate) fn rational_milnor_e2(
    metric: &crate::clifford::Metric<Rational>,
) -> Result<RationalMilnorK2Class, MilnorInvariantError> {
    let diagonal = strict_diagonal(metric)?;
    let bw =
        bw_class_rational(&diagonal).ok_or(MilnorInvariantError::UnsupportedFieldOrArithmetic)?;
    if bw.dimension_parity() != 0 || bw.signed_discriminant() != 1 {
        return Err(MilnorInvariantError::OutsideFundamentalIdeal { power: 2 });
    }
    Ok(bw.clifford_brauer_class().clone())
}

pub(crate) fn function_field_milnor_e1<S: FiniteOddField>(
    metric: &crate::clifford::Metric<RationalFunction<S>>,
) -> Result<FunctionFieldMilnorK1Class<S>, MilnorInvariantError> {
    let diagonal = strict_diagonal(metric)?;
    let bw = bw_class_function_field(&diagonal)
        .ok_or(MilnorInvariantError::UnsupportedFieldOrArithmetic)?;
    if bw.dimension_parity() != 0 {
        return Err(MilnorInvariantError::OutsideFundamentalIdeal { power: 1 });
    }
    FunctionFieldMilnorK1Class::new(bw.signed_discriminant().clone())
        .ok_or(MilnorInvariantError::UnsupportedFieldOrArithmetic)
}

pub(crate) fn function_field_milnor_e2<S: FiniteOddField>(
    metric: &crate::clifford::Metric<RationalFunction<S>>,
) -> Result<FunctionFieldMilnorK2Class<S>, MilnorInvariantError> {
    let diagonal = strict_diagonal(metric)?;
    let bw = bw_class_function_field(&diagonal)
        .ok_or(MilnorInvariantError::UnsupportedFieldOrArithmetic)?;
    if bw.dimension_parity() != 0 || !is_global_square_ff(bw.signed_discriminant()) {
        return Err(MilnorInvariantError::OutsideFundamentalIdeal { power: 2 });
    }
    Ok(bw.clifford_brauer_class().clone())
}

// ---------------------------------------------------------------------------
// Tame residue maps on pure symbols.
// ---------------------------------------------------------------------------

/// The discrete-valuation boundary `partial_p {a} = v_p(a) mod 2` from
/// `K^M_1(Q)/2` to `K^M_0(F_p)/2`.
pub fn milnor_residue_symbol_1_q(a: &Rational, p: u128) -> Option<MilnorK0Class> {
    if a.is_zero() || !is_prime_u128(p) {
        return None;
    }
    let pi = i128::try_from(p).ok()?;
    let valuation = val_p(a.numer(), pi) as i128 - val_p(a.denom(), pi) as i128;
    Some(MilnorK0Class::from_parity(valuation.rem_euclid(2) as u128))
}

/// The tame boundary of `{a,b}` at an odd rational prime, returned as a square
/// class in `K^M_1(F_p)/2`. The dyadic wild symbol is deliberately not supplied.
pub fn milnor_residue_symbol_2_q(
    a: &Rational,
    b: &Rational,
    p: u128,
) -> Option<FiniteFieldMilnorK1Class> {
    if p == 2 || !is_prime_u128(p) {
        return None;
    }
    let a = RationalMilnorK1Class::from_rational(a)?.representative();
    let b = RationalMilnorK1Class::from_rational(b)?.representative();
    let nonsquare = u128::from(try_hilbert_symbol_qp(a, b, p)? == -1);
    FiniteFieldMilnorK1Class::new(p, p, nonsquare)
}

/// The discrete-valuation boundary `partial_v {a} = v(a) mod 2` from
/// `K^M_1(F_q(t))/2` to `K^M_0(kappa(v))/2`.
pub fn milnor_residue_symbol_1_ff<S: FiniteOddField>(
    a: &RationalFunction<S>,
    place: &FunctionFieldPlace<S>,
) -> Option<MilnorK0Class> {
    if a.is_zero() {
        return None;
    }
    Some(MilnorK0Class::from_parity(
        try_valuation_at_ff(a, place)?.rem_euclid(2) as u128,
    ))
}

/// The tame boundary of `{a,b}` at a place of `F_q(t)`, returned as the
/// residue-field square class. It is the quadratic (`n = 2`) slice of the
/// existing tame Kummer symbol.
pub fn milnor_residue_symbol_2_ff<S: FiniteOddField>(
    a: &RationalFunction<S>,
    b: &RationalFunction<S>,
    place: &FunctionFieldPlace<S>,
) -> Option<FiniteFieldMilnorK1Class> {
    let nonsquare = try_tame_symbol_exponent_ff(2, a, b, place)?;
    FiniteFieldMilnorK1Class::new(
        S::characteristic_prime(),
        try_kappa_order(place)?,
        nonsquare,
    )
}

/// The split Milnor invariant of a diagonal form over odd `F_q(t)`.
///
/// The first component is the constant-field class selected at `∞`; the vector is
/// the finite-place support of nonzero second residues.
pub type FunctionFieldMilnorResidues<S> = (WittClassG, Vec<(FunctionFieldPlace<S>, WittClassG)>);

/// The second residue `∂_p⟨a_1,…,a_n⟩` at an **odd** prime `p`, as a Witt class over
/// `F_p`. It collects the residue units of the entries of **odd** `p`-valuation and
/// returns the Witt class of `⟂ ⟨ū_i⟩` over `F_p`, using the multiplicativity of the
/// Legendre symbol (so no product overflows): `∏ (u_i | p)` times the
/// `(−1)^{m(m−1)/2}` signed-discriminant correction gives the square class.
fn second_residue_at(entries: &[i128], p: u128) -> WittClassG {
    let pi = p as i128;
    let mut leg_prod: i128 = 1; // ∏ (u_i | p) over odd-valuation entries
    let mut m: i128 = 0; // dimension of the residue form
    for &a in entries {
        if val_p(a, pi) % 2 == 1 {
            leg_prod *= legendre(unit_part(a, pi), pi);
            m += 1;
        }
    }
    let leg_neg1 = legendre(-1, pi); // (−1 | p): +1 iff p ≡ 1 (mod 4)
    let signed_leg = if ((m * (m - 1) / 2) & 1) == 1 {
        leg_prod * leg_neg1
    } else {
        leg_prod
    };
    WittClassG::OddChar {
        field_order: p,
        kappa: if leg_neg1 == 1 { 0 } else { 1 },
        e0: (m & 1) as u128,
        sclass: if signed_leg == 1 { 0 } else { 1 },
    }
}

/// Milnor's hand-defined dyadic residue `∂₂ : W(ℚ) → W(F₂) ≅ ℤ/2`.
/// Since every odd unit reduces to `1 ∈ F₂`, only the parity of entries with odd
/// `2`-adic valuation survives.
fn dyadic_residue_at(entries: &[i128]) -> WittClassG {
    let arf = entries.iter().filter(|&&a| val_p(a, 2) % 2 == 1).count() as u128 & 1;
    WittClassG::Char2 {
        field_degree: 1,
        arf,
    }
}

/// Whether a Witt class over `F_p` is the zero class (even dimension and square signed
/// discriminant ⇒ hyperbolic).
fn is_zero_residue(w: &WittClassG) -> bool {
    matches!(
        w,
        WittClassG::OddChar {
            e0: 0,
            sclass: 0,
            ..
        } | WittClassG::Char2 { arf: 0, .. }
    )
}

/// The image of the rational diagonal form `⟨a_1,…,a_n⟩` (nonzero `i128` entries)
/// under the Milnor map `W(ℚ) → ℤ ⊕ ⊕_p W(F_p)`: the **signature** `(#positive −
/// #negative)` and the nonzero residues `∂_p`, keyed by prime. Zero residues are
/// omitted, so the map of an everywhere-good integral form is empty.
///
/// `None` if any entry is zero (a radical — the form is degenerate). Two forms with
/// equal `global_residues` are Witt-equivalent over `ℚ`; a difference at any prime,
/// or in the signature, witnesses inequivalence.
pub fn global_residues(entries: &[i128]) -> Option<(i128, BTreeMap<u128, WittClassG>)> {
    if entries.contains(&0) {
        return None;
    }
    let signature: i128 = entries.iter().map(|&a| a.signum()).sum();
    let mut residues = BTreeMap::new();
    for p in relevant_primes(entries) {
        let w = if p == 2 {
            dyadic_residue_at(entries)
        } else {
            second_residue_at(entries, p)
        };
        if !is_zero_residue(&w) {
            residues.insert(p, w);
        }
    }
    Some((signature, residues))
}

fn oddchar_witt_from_residue_units<S: FiniteOddField>(
    units: &[Poly<S>],
    place: &FunctionFieldPlace<S>,
) -> Option<WittClassG> {
    let mut chi_prod: i128 = 1;
    for unit in units {
        chi_prod *= try_chi_kappa(unit, place)?;
    }
    let m = i128::try_from(units.len()).ok()?;
    let field_order = try_kappa_order(place)?;
    let chi_neg1 = if field_order % 4 == 1 { 1 } else { -1 };
    let signed_chi = if ((m * (m - 1) / 2) & 1) == 1 {
        chi_prod * chi_neg1
    } else {
        chi_prod
    };
    Some(WittClassG::OddChar {
        field_order,
        kappa: if chi_neg1 == 1 { 0 } else { 1 },
        e0: (m & 1) as u128,
        sclass: if signed_chi == 1 { 0 } else { 1 },
    })
}

fn second_residue_at_ff<S: FiniteOddField>(
    entries: &[RationalFunction<S>],
    place: &FunctionFieldPlace<S>,
) -> Option<WittClassG> {
    let mut units = Vec::new();
    for entry in entries {
        if try_valuation_at_ff(entry, place)?.rem_euclid(2) != 0 {
            units.push(try_residue_unit_at(entry, place)?);
        }
    }
    oddchar_witt_from_residue_units(&units, place)
}

fn constant_class_at_infinity_ff<S: FiniteOddField>(
    entries: &[RationalFunction<S>],
) -> Option<WittClassG> {
    let place = FunctionFieldPlace::Infinite;
    let mut units = Vec::new();
    for entry in entries {
        if try_valuation_at_ff(entry, &place)?.rem_euclid(2) == 0 {
            units.push(try_residue_unit_at(entry, &place)?);
        }
    }
    oddchar_witt_from_residue_units(&units, &place)
}

/// The split Milnor map for a diagonal form over `F_q(t)` with odd `q`:
/// `W(F_q(t)) ≅ W(F_q) ⊕ ⊕_π W(F_q[t]/π)`.
///
/// The first component is the `W(F_q)` class obtained by the even-valuation
/// layer at the degree place `∞`; the vector contains the nonzero second
/// residues at finite monic irreducible places. Zero residues are omitted.
///
/// `None` if any entry is zero. Characteristic-2 function fields use the
/// separate Artin-Schreier/Aravire-Jacob layer, not this tame odd-residue
/// sequence.
pub fn global_residues_ff<S: FiniteOddField>(
    entries: &[RationalFunction<S>],
) -> Option<FunctionFieldMilnorResidues<S>> {
    if entries.iter().any(|entry| entry.is_zero()) {
        return None;
    }
    let constant = constant_class_at_infinity_ff(entries)?;
    let mut residues = Vec::new();
    for place in try_relevant_places_ff(entries)? {
        if matches!(place, FunctionFieldPlace::Infinite) {
            continue;
        }
        let w = second_residue_at_ff(entries, &place)?;
        if !is_zero_residue(&w) {
            residues.push((place, w));
        }
    }
    Some((constant, residues))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clifford::Metric;
    use crate::forms::{springer_decompose_qp, try_is_isotropic_q};
    use crate::scalar::{Fp, Fpn, Qp, Rational, RationalFunction};

    fn q(n: i128) -> Rational {
        Rational::from_int(n)
    }

    #[test]
    fn degree_zero_is_zmod_two() {
        let zero = MilnorK0Class::from_dimension(4);
        let one = MilnorK0Class::from_dimension(5);
        assert_eq!(zero.value(), 0);
        assert_eq!(one.value(), 1);
        assert_eq!(one.sum(one), zero);
        assert_eq!(one.product(one), one);
        assert_eq!(one.product(zero), zero);
        assert_eq!(one.to_string(), "MilnorK0Mod2(1)");
    }

    #[test]
    fn rational_k1_is_the_canonical_square_class() {
        let two = milnor_symbol_1(&q(2)).unwrap();
        let eight = milnor_symbol_1(&q(8)).unwrap();
        let three = milnor_symbol_1(&q(3)).unwrap();
        let six = milnor_symbol_1(&q(6)).unwrap();
        assert_eq!(two, eight, "square factors do not change {{a}}");
        assert_eq!(two.try_add(three), Some(six));
        assert_eq!(
            milnor_symbol_1(&Rational::new(2, 3)),
            milnor_symbol_1(&q(6))
        );
        assert!(milnor_symbol_1(&Rational::zero()).is_none());
        assert_eq!(two.to_string(), "MilnorK1Mod2(Q; 2)");
    }

    #[test]
    fn rational_k2_obeys_symbol_relations() {
        let (a, b, c) = (q(2), q(3), q(5));
        let ab = a.mul(&b);
        let lhs = milnor_symbol_2(&ab, &c).unwrap();
        let rhs = milnor_symbol_2(&a, &c)
            .unwrap()
            .add(&milnor_symbol_2(&b, &c).unwrap());
        assert_eq!(lhs, rhs, "{{ab,c}} = {{a,c}} + {{b,c}}");
        assert_eq!(
            milnor_symbol_2(&a, &b),
            milnor_symbol_2(&b, &a),
            "degree-two mod-two symbols are symmetric"
        );
        for n in -8..=8 {
            if n == 0 || n == 1 {
                continue;
            }
            let x = q(n);
            let one_minus_x = q(1).add(&x.neg());
            assert!(
                milnor_symbol_2(&x, &one_minus_x).unwrap().is_split(),
                "Steinberg: {{a,1-a}}=0 at a={n}"
            );
        }
        assert!(
            milnor_symbol_2(&a, &a.neg()).unwrap().is_split(),
            "{{a,-a}}=0"
        );
        assert!(milnor_symbol_2(&Rational::zero(), &b).is_none());
    }

    #[test]
    fn finite_field_symbols_are_square_class_and_trivial_k2() {
        let two = Fp::<5>::from_int(2);
        let four = Fp::<5>::from_int(4);
        let k1_two = milnor_symbol_1(&two).unwrap();
        let k1_four = milnor_symbol_1(&four).unwrap();
        assert_eq!(k1_two.nonsquare(), 1);
        assert!(k1_four.is_trivial());
        assert!(milnor_symbol_2(&two, &four).unwrap().is_trivial());
        assert_eq!(k1_two.to_string(), "MilnorK1Mod2(F_5; 1)");

        type F9 = Fpn<3, 2>;
        for i in 1..F9::field_order() {
            let x = <F9 as FiniteOddField>::from_index(i);
            let square = x.mul(&x);
            assert!(milnor_symbol_1(&square).unwrap().is_trivial());
            assert!(milnor_symbol_2(&x, &square).unwrap().is_trivial());
        }

        assert!(milnor_symbol_1(&Fp::<2>::one()).is_none());
        assert!(milnor_symbol_2(&Fp::<2>::one(), &Fp::<2>::one()).is_none());
    }

    #[test]
    fn strict_en_maps_have_their_actual_ideal_domains() {
        let two = q(2);
        let three = q(3);
        let p1 = crate::forms::pfister1(&two);
        assert_eq!(p1.milnor_e0().unwrap().value(), 0);
        assert_eq!(p1.milnor_e1().unwrap(), milnor_symbol_1(&two).unwrap());
        assert_eq!(
            p1.milnor_e2(),
            Err(MilnorInvariantError::OutsideFundamentalIdeal { power: 2 })
        );

        let p2 = crate::forms::pfister(&[two.clone(), three.clone()]);
        assert!(p2.milnor_e1().unwrap().is_trivial());
        assert_eq!(
            p2.milnor_e2().unwrap(),
            milnor_symbol_2(&two, &three).unwrap(),
            "e2(<<a,b>>) = {{a,b}}"
        );
        let algebra = crate::clifford::CliffordAlgebra::new(p2.dim(), p2.clone());
        assert_eq!(algebra.milnor_e2(), p2.milnor_e2());

        let odd = Metric::diagonal(vec![q(1), q(2), q(3)]);
        assert_eq!(
            odd.milnor_e1(),
            Err(MilnorInvariantError::OutsideFundamentalIdeal { power: 1 })
        );
        let singular = Metric::diagonal(vec![q(1), q(0)]);
        assert_eq!(
            singular.milnor_e0(),
            Err(MilnorInvariantError::SingularForm { radical_dim: 1 })
        );
    }

    #[test]
    fn strict_en_maps_cover_finite_and_function_fields() {
        let a = Fp::<5>::from_int(2);
        let b = Fp::<5>::from_int(3);
        let p2 = crate::forms::pfister(&[a, b]);
        assert!(p2.milnor_e1().unwrap().is_trivial());
        assert!(p2.milnor_e2().unwrap().is_trivial());

        let t = rf(&[0, 1], &[1]);
        let two = rf(&[2], &[1]);
        let ff_p1 = crate::forms::pfister1(&t);
        assert_eq!(ff_p1.milnor_e1().unwrap(), milnor_symbol_1(&t).unwrap());
        let ff_p2 = crate::forms::pfister(&[t.clone(), two.clone()]);
        assert!(ff_p2.milnor_e1().unwrap().is_trivial());
        assert_eq!(
            ff_p2.milnor_e2().unwrap(),
            milnor_symbol_2(&t, &two).unwrap()
        );
    }

    #[test]
    fn function_field_k1_equality_is_modulo_global_squares() {
        let t = rf(&[0, 1], &[1]);
        let t1 = rf(&[1, 1], &[1]);
        let square = t1.mul(&t1);
        assert_eq!(
            milnor_symbol_1(&t),
            milnor_symbol_1(&t.mul(&square)),
            "multiplication by (t+1)^2 preserves the square class"
        );
        assert!(milnor_symbol_1(&t)
            .unwrap()
            .add(&milnor_symbol_1(&t).unwrap())
            .is_trivial());
        assert_eq!(milnor_symbol_2(&t, &t1), milnor_symbol_2(&t1, &t));
        let one_minus_t = F5::one().add(&t.neg());
        assert!(milnor_symbol_2(&t, &one_minus_t).unwrap().is_split());
    }

    #[test]
    fn pure_symbol_residues_reuse_the_existing_local_symbols() {
        let eighteen_fifths = Rational::new(18, 5);
        assert_eq!(
            milnor_residue_symbol_1_q(&eighteen_fifths, 3)
                .unwrap()
                .value(),
            0
        );
        assert_eq!(
            milnor_residue_symbol_1_q(&eighteen_fifths, 5)
                .unwrap()
                .value(),
            1
        );
        for p in [3, 5, 7, 11] {
            let residue = milnor_residue_symbol_2_q(&q(2), &q(3), p).unwrap();
            assert_eq!(
                residue.nonsquare(),
                u128::from(try_hilbert_symbol_qp(2, 3, p).unwrap() == -1)
            );
        }
        assert!(milnor_residue_symbol_2_q(&q(-1), &q(-1), 2).is_none());

        let t = rf(&[0, 1], &[1]);
        let two = rf(&[2], &[1]);
        let at_t = FunctionFieldPlace::Finite(poly(&[0, 1]));
        assert_eq!(milnor_residue_symbol_1_ff(&t, &at_t).unwrap().value(), 1);
        let residue = milnor_residue_symbol_2_ff(&t, &two, &at_t).unwrap();
        assert_eq!(
            residue.nonsquare(),
            try_tame_symbol_exponent_ff(2, &t, &two, &at_t).unwrap()
        );
        assert_eq!(residue.field_order(), 5);
        assert_eq!(
            milnor_symbol_2(&t, &two)
                .unwrap()
                .ramified_places()
                .contains(&at_t),
            !residue.is_trivial()
        );
    }

    /// `∂₅` via the capped `Q₅` Springer engine: the Witt class of the odd-valuation
    /// (parity-1) residue layer, built independently of the `i128` route.
    fn springer_residue_q5(entries: &[i128]) -> WittClassG {
        type Q5 = Qp<5, 6>;
        let metric = Metric::diagonal(entries.iter().map(|&a| Q5::from_int(a)).collect());
        let decomp = springer_decompose_qp(&metric).unwrap();
        let mut dim = 0usize;
        let mut disc_sq = true; // running square class of the residue discriminant
        for form in decomp.parity_layer(1) {
            dim += form.dim;
            disc_sq = disc_sq == form.disc_is_square; // XNOR of square classes
        }
        let m = dim as i128;
        let leg_neg1 = legendre(-1, 5); // +1 (5 ≡ 1 mod 4)
        let signed_sq = if ((m * (m - 1) / 2) & 1) == 1 && leg_neg1 != 1 {
            !disc_sq
        } else {
            disc_sq
        };
        WittClassG::OddChar {
            field_order: 5,
            kappa: if leg_neg1 == 1 { 0 } else { 1 },
            e0: (dim & 1) as u128,
            sclass: if signed_sq { 0 } else { 1 },
        }
    }

    /// `∂₃` via the capped `Q₃` Springer engine — the `p ≡ 3 (mod 4)` companion to
    /// `springer_residue_q5` (`p ≡ 1 (mod 4)`, `kappa = 0`). At `p = 5` the
    /// `leg_neg1` factor in `second_residue_at`'s signed-discriminant twist is `+1`,
    /// so multiplying by it is a no-op — a mis-encoded twist would go undetected.
    /// `p = 3` has `leg_neg1 = -1` (`kappa = 1`), so this is the first Springer
    /// cross-check that actually exercises the twist.
    fn springer_residue_q3(entries: &[i128]) -> WittClassG {
        type Q3 = Qp<3, 6>;
        let metric = Metric::diagonal(entries.iter().map(|&a| Q3::from_int(a)).collect());
        let decomp = springer_decompose_qp(&metric).unwrap();
        let mut dim = 0usize;
        let mut disc_sq = true; // running square class of the residue discriminant
        for form in decomp.parity_layer(1) {
            dim += form.dim;
            disc_sq = disc_sq == form.disc_is_square; // XNOR of square classes
        }
        let m = dim as i128;
        let leg_neg1 = legendre(-1, 3); // -1 (3 ≡ 3 mod 4)
        let signed_sq = if ((m * (m - 1) / 2) & 1) == 1 && leg_neg1 != 1 {
            !disc_sq
        } else {
            disc_sq
        };
        WittClassG::OddChar {
            field_order: 3,
            kappa: if leg_neg1 == 1 { 0 } else { 1 },
            e0: (dim & 1) as u128,
            sclass: if signed_sq { 0 } else { 1 },
        }
    }

    fn f2_class(arf: u128) -> WittClassG {
        WittClassG::Char2 {
            field_degree: 1,
            arf,
        }
    }

    type F5 = RationalFunction<Fp<5>>;
    type Poly5 = Poly<Fp<5>>;

    fn rf(num: &[i128], den: &[i128]) -> F5 {
        RationalFunction::new(
            num.iter().map(|&n| Fp::<5>::from_int(n)).collect(),
            den.iter().map(|&n| Fp::<5>::from_int(n)).collect(),
        )
    }

    fn poly(c: &[i128]) -> Poly5 {
        Poly::new(c.iter().map(|&n| Fp::<5>::from_int(n)).collect())
    }

    fn odd_class(field_order: u128, e0: u128, sclass: u128) -> WittClassG {
        WittClassG::OddChar {
            field_order,
            kappa: if field_order % 4 == 1 { 0 } else { 1 },
            e0,
            sclass,
        }
    }

    fn residue_at<'a>(
        residues: &'a [(FunctionFieldPlace<Fp<5>>, WittClassG)],
        place: &FunctionFieldPlace<Fp<5>>,
    ) -> Option<&'a WittClassG> {
        residues.iter().find(|(pl, _)| pl == place).map(|(_, w)| w)
    }

    #[test]
    fn second_residue_matches_springer_over_q5() {
        // The exact i128 residue and the capped-Q₅ Springer residue agree on forms
        // exercising even/odd valuations and square/nonsquare units at 5.
        for entries in [
            vec![1, 5],
            vec![2, 10],
            vec![3, 15, 5],
            vec![1, 1],
            vec![7, 5, 25, 2],
        ] {
            assert_eq!(
                second_residue_at(&entries, 5),
                springer_residue_q5(&entries),
                "∂₅ mismatch on {entries:?}"
            );
        }
    }

    #[test]
    fn second_residue_matches_springer_over_q3() {
        // The p=3 companion to second_residue_matches_springer_over_q5: p ≡ 3 (mod 4)
        // gives kappa=1, so entries with an even number (2 or 3 mod 4) of odd-valuation
        // lines genuinely exercise the sign-twist branch that p=5 (kappa=0) cannot.
        for entries in [
            vec![1, 3],       // m=1: no twist regardless of kappa
            vec![3, 6],       // m=2: twist flips the sign
            vec![1, 1, 3, 3], // m=2, different residue units
            vec![3, 6, 12],   // m=3: twist triggers again
            vec![2, 4],       // m=0: both entries even valuation, zero residue
        ] {
            assert_eq!(
                second_residue_at(&entries, 3),
                springer_residue_q3(&entries),
                "∂₃ mismatch on {entries:?}"
            );
        }
    }

    #[test]
    fn dyadic_residue_is_milnors_hand_boundary() {
        // Over F_2 every odd unit reduces to 1, so ∂_2 only sees the parity of
        // odd 2-adic valuation lines.
        assert_eq!(dyadic_residue_at(&[1]), f2_class(0));
        assert_eq!(dyadic_residue_at(&[2]), f2_class(1));
        assert_eq!(dyadic_residue_at(&[-2]), f2_class(1));
        assert_eq!(dyadic_residue_at(&[1, 2]), f2_class(1));
        assert_eq!(dyadic_residue_at(&[2, -2]), f2_class(0));
    }

    #[test]
    fn global_residues_include_the_dyadic_cell() {
        for (entries, signature) in [(&[2i128][..], 1), (&[1, 2], 2), (&[-2], -1)] {
            let (sig, res) = global_residues(entries).unwrap();
            assert_eq!(sig, signature);
            assert_eq!(res.get(&2), Some(&f2_class(1)), "entries={entries:?}");
        }

        let (sig, res) = global_residues(&[2, -2]).unwrap();
        assert_eq!(sig, 0);
        assert!(
            res.is_empty(),
            "the hyperbolic pair <2,-2> has zero residues"
        );

        let (_, mixed) = global_residues(&[6]).unwrap();
        assert_eq!(
            mixed.keys().copied().collect::<Vec<_>>(),
            vec![2, 3],
            "<6> has both dyadic and odd-prime residues"
        );
    }

    #[test]
    fn residues_have_finite_support_at_dividing_primes() {
        // ∂_p = 0 for p ∤ ∏ a_i: ⟨1,1,1⟩ has no odd residues.
        let (sig, res) = global_residues(&[1, 1, 1]).unwrap();
        assert_eq!(sig, 3);
        assert!(res.is_empty());
        // ⟨3, 5⟩: residues exactly at 3 and 5 (each an odd-valuation unit line).
        let (sig, res) = global_residues(&[3, 5]).unwrap();
        assert_eq!(sig, 2);
        assert_eq!(res.keys().copied().collect::<Vec<_>>(), vec![3, 5]);
    }

    #[test]
    fn radical_entry_is_rejected() {
        assert_eq!(global_residues(&[1, 0, 2]), None);
    }

    #[test]
    fn function_field_residues_split_at_infinity() {
        let (constant, residues) = global_residues_ff(&[rf(&[1], &[1])]).unwrap();
        assert_eq!(constant, odd_class(5, 1, 0));
        assert!(
            residues.is_empty(),
            "constant forms have no finite residues"
        );

        let (constant, residues) = global_residues_ff(&[rf(&[0, 1], &[1])]).unwrap();
        assert_eq!(constant, odd_class(5, 0, 0));
        assert_eq!(
            residue_at(&residues, &FunctionFieldPlace::Finite(poly(&[0, 1]))),
            Some(&odd_class(5, 1, 0))
        );

        let (constant, residues) = global_residues_ff(&[rf(&[1], &[0, 1])]).unwrap();
        assert_eq!(constant, odd_class(5, 0, 0));
        assert_eq!(
            residue_at(&residues, &FunctionFieldPlace::Finite(poly(&[0, 1]))),
            Some(&odd_class(5, 1, 0))
        );

        let (constant, residues) = global_residues_ff(&[rf(&[2], &[1])]).unwrap();
        assert_eq!(constant, odd_class(5, 1, 1), "2 is nonsquare in F_5");
        assert!(residues.is_empty());
    }

    #[test]
    fn function_field_residues_see_degree_two_places() {
        let place = FunctionFieldPlace::Finite(poly(&[2, 0, 1])); // t^2 + 2 irreducible over F_5
        let (constant, residues) = global_residues_ff(&[rf(&[2, 0, 1], &[1])]).unwrap();
        assert_eq!(constant, odd_class(5, 1, 0));
        assert_eq!(residue_at(&residues, &place), Some(&odd_class(25, 1, 0)));
    }

    #[test]
    fn function_field_residues_are_square_and_hyperbolic_stable() {
        let base = global_residues_ff(&[rf(&[0, 1], &[1])]).unwrap();
        let square = rf(&[1, 1], &[1]).mul(&rf(&[1, 1], &[1]));
        let square_multiple = global_residues_ff(&[rf(&[0, 1], &[1]).mul(&square)]).unwrap();
        assert_eq!(square_multiple, base);

        let hyperbolic = global_residues_ff(&[rf(&[0, 1], &[1]), rf(&[0, 4], &[1])]).unwrap();
        assert_eq!(hyperbolic.0, odd_class(5, 0, 0));
        assert!(hyperbolic.1.is_empty());
    }

    #[test]
    fn function_field_residues_reject_radical_entries() {
        assert_eq!(global_residues_ff(&[rf(&[1], &[1]), rf(&[0], &[1])]), None);
    }

    #[test]
    fn witt_invariants_are_square_and_hyperbolic_stable() {
        // ⟨3⟩ ≅ ⟨12⟩ (12 = 3·4, a square multiple) and adding a hyperbolic plane
        // ⟨1,−1⟩ changes nothing — all three share signature and residues.
        let base = global_residues(&[3]).unwrap();
        assert_eq!(global_residues(&[12]).unwrap(), base);
        assert_eq!(global_residues(&[3, 1, -1]).unwrap(), base);
        // Same at the dyadic prime: ⟨2⟩ ≅ ⟨8⟩, and ⟨1,-1⟩ is still hyperbolic.
        let dyadic = global_residues(&[2]).unwrap();
        assert_eq!(global_residues(&[8]).unwrap(), dyadic);
        assert_eq!(global_residues(&[2, 1, -1]).unwrap(), dyadic);
    }

    #[test]
    fn residues_distinguish_inequivalent_forms() {
        // ⟨1⟩ and ⟨3⟩ have equal signature but differ at p = 3 ⇒ not Witt-equivalent.
        let one = global_residues(&[1]).unwrap();
        let three = global_residues(&[3]).unwrap();
        assert_eq!(one.0, three.0, "same signature");
        assert_ne!(one.1, three.1, "different residue at 3");
        // Cross-check with Hasse–Minkowski: ⟨1,−3⟩ is anisotropic over ℚ (3 is not a
        // square), so ⟨1⟩ ⊥ ⟨−3⟩ is not hyperbolic — they are genuinely inequivalent.
        assert_eq!(try_is_isotropic_q(&[1, -3]), Some(false));

        // Same signature, dyadic residue differs: ⟨1⟩ and ⟨2⟩ are not equivalent.
        let two = global_residues(&[2]).unwrap();
        assert_eq!(one.0, two.0, "same signature");
        assert_ne!(one.1, two.1, "different dyadic residue");
        assert_eq!(try_is_isotropic_q(&[1, -2]), Some(false));
    }

    #[test]
    fn reconstruction_agrees_with_hasse_minkowski() {
        // Equal residues + equal signature ⇒ Witt-equivalent ⇒ a ⊥ (−b) hyperbolic,
        // hence isotropic. ⟨3⟩ vs ⟨12⟩: ⟨3,−12⟩ is isotropic (x = 2y).
        assert_eq!(
            global_residues(&[3]).unwrap(),
            global_residues(&[12]).unwrap()
        );
        assert_eq!(try_is_isotropic_q(&[3, -12]), Some(true));

        // ⟨3,5⟩ vs ⟨12,45⟩ (entrywise square multiples): same residues at 3 and 5,
        // and ⟨3,5,−12,−45⟩ is isotropic ((x,z) = (2,1): 3·4 − 12 = 0).
        assert_eq!(
            global_residues(&[3, 5]).unwrap(),
            global_residues(&[12, 45]).unwrap()
        );
        assert_eq!(try_is_isotropic_q(&[3, 5, -12, -45]), Some(true));

        // Dyadic reconstruction: ⟨2⟩ vs ⟨8⟩ differ by a square multiple, so the
        // difference form is isotropic; ⟨2⟩ vs ⟨1⟩ has a dyadic-residue mismatch.
        assert_eq!(
            global_residues(&[2]).unwrap(),
            global_residues(&[8]).unwrap()
        );
        assert_eq!(try_is_isotropic_q(&[2, -8]), Some(true));
        assert_ne!(
            global_residues(&[2]).unwrap(),
            global_residues(&[1]).unwrap()
        );
        assert_eq!(try_is_isotropic_q(&[2, -1]), Some(false));
    }
}
