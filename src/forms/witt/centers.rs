//! Centers of Clifford algebras and their even subalgebras.
//!
//! For a nonsingular quadratic space of positive dimension, one of
//! `Z(Cl(q))` and `Z(Cl^0(q))` is the ground field and the other is the
//! discriminant quadratic etale algebra.  In characteristic not two its
//! generator is the volume element `omega` with
//!
//! ```text
//! omega^2 = (-1)^(n(n-1)/2) det(q).
//! ```
//!
//! The quadratic center is the full center when `n` is odd and the even center
//! when `n` is even.  In characteristic two a nonsingular quadratic space has
//! even dimension.  For a symplectic basis `(a_i,b_i)`, the element
//! `z = sum_i a_i b_i` is central in `Cl^0(q)` and satisfies
//!
//! ```text
//! z^2 + z = sum_i q(a_i) q(b_i).
//! ```
//!
//! The Kummer or Artin--Schreier class of that relation is compared here with
//! the independently computed discriminant/Arf coordinate of the existing
//! Brauer--Wall classifier.  These are the standard center descriptions from
//! the Clifford-algebra chapters of Knus--Merkurjev--Rost--Tignol, *The Book of
//! Involutions*; this module's contribution is their exact realization and the
//! cross-surface check on Ogdoad's represented scalar domains.

use crate::clifford::{CliffordAlgebra, Metric, Multivector};
use crate::forms::{
    arf_f2, arf_fpn_char2, arf_ordinal_finite, as_diagonal, bw_class_complex, bw_class_finite_odd,
    bw_class_function_field, bw_class_nimber, bw_class_rational, bw_class_real,
    ordinal_metric_finite_subfield_degree, BrauerWallClass, FiniteFieldMilnorK1Class,
    FiniteOddField, FunctionFieldBrauerWallClass, FunctionFieldMilnorK1Class, Mod2MilnorField,
    RationalBrauerWallClass, RationalMilnorK1Class,
};
use crate::scalar::{
    nim_degree, nim_trace, FieldExtension, Fp, Fpn, Nimber, Ordinal, Rational, RationalFunction,
    Scalar, Surcomplex, Surreal,
};
use std::cmp::Ordering;
use std::collections::BTreeMap;

/// The defining relation of a quadratic etale center.
#[derive(Debug, Clone, PartialEq)]
pub enum QuadraticEtaleRelation<S: Scalar> {
    /// `F[omega]/(omega^2 - d)` in characteristic not two.
    Kummer {
        /// The represented signed discriminant `d = omega^2`.
        generator_square: S,
    },
    /// `F[z]/(z^2 + z + c)` in characteristic two.
    ArtinSchreier {
        /// The represented Artin--Schreier discriminant `c = z^2 + z`.
        representative: S,
    },
}

impl<S: Scalar> QuadraticEtaleRelation<S> {
    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl<S: Scalar> std::fmt::Display for QuadraticEtaleRelation<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuadraticEtaleRelation::Kummer { generator_square } => {
                write!(f, "omega^2={generator_square}")
            }
            QuadraticEtaleRelation::ArtinSchreier { representative } => {
                write!(f, "z^2+z={representative}")
            }
        }
    }
}

/// A full or even Clifford center, materialized by its central generator when
/// it is quadratic over the ground field.
#[derive(Debug, Clone, PartialEq)]
pub enum DiscriminantEtaleAlgebra<S: Scalar, D> {
    /// The center is exactly the coefficient field.
    GroundField,
    /// The discriminant quadratic etale algebra.
    QuadraticEtale {
        /// A concrete central generator in the represented Clifford algebra.
        generator: Multivector<S>,
        /// Its Kummer or Artin--Schreier defining relation.
        relation: QuadraticEtaleRelation<S>,
        /// The corresponding square or Artin--Schreier class.
        discriminant_class: D,
        /// Whether the quadratic etale algebra is split as `F x F`.
        split: bool,
    },
}

impl<S: Scalar, D> DiscriminantEtaleAlgebra<S, D> {
    /// Degree of the center over the coefficient field.
    pub fn degree(&self) -> usize {
        match self {
            DiscriminantEtaleAlgebra::GroundField => 1,
            DiscriminantEtaleAlgebra::QuadraticEtale { .. } => 2,
        }
    }

    /// Whether this is the coefficient field rather than a quadratic center.
    pub fn is_ground_field(&self) -> bool {
        matches!(self, DiscriminantEtaleAlgebra::GroundField)
    }

    /// The concrete quadratic generator, when the center has degree two.
    pub fn generator(&self) -> Option<&Multivector<S>> {
        match self {
            DiscriminantEtaleAlgebra::GroundField => None,
            DiscriminantEtaleAlgebra::QuadraticEtale { generator, .. } => Some(generator),
        }
    }

    /// The defining relation, when the center has degree two.
    pub fn relation(&self) -> Option<&QuadraticEtaleRelation<S>> {
        match self {
            DiscriminantEtaleAlgebra::GroundField => None,
            DiscriminantEtaleAlgebra::QuadraticEtale { relation, .. } => Some(relation),
        }
    }

    /// The discriminant class, when the center has degree two.
    pub fn discriminant_class(&self) -> Option<&D> {
        match self {
            DiscriminantEtaleAlgebra::GroundField => None,
            DiscriminantEtaleAlgebra::QuadraticEtale {
                discriminant_class, ..
            } => Some(discriminant_class),
        }
    }

    /// `Some(true)` for a split quadratic center, `Some(false)` for a quadratic
    /// field center, and `None` for the degree-one ground-field center.
    pub fn quadratic_is_split(&self) -> Option<bool> {
        match self {
            DiscriminantEtaleAlgebra::GroundField => None,
            DiscriminantEtaleAlgebra::QuadraticEtale { split, .. } => Some(*split),
        }
    }
}

impl<S: Scalar, D: std::fmt::Display> std::fmt::Display for DiscriminantEtaleAlgebra<S, D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DiscriminantEtaleAlgebra::GroundField => f.write_str("GroundField"),
            DiscriminantEtaleAlgebra::QuadraticEtale {
                relation,
                discriminant_class,
                split,
                ..
            } => match relation {
                QuadraticEtaleRelation::Kummer { generator_square } => write!(
                    f,
                    "QuadraticEtale(omega^2={generator_square}, class={discriminant_class}, split={split})"
                ),
                QuadraticEtaleRelation::ArtinSchreier { representative } => write!(
                    f,
                    "QuadraticEtale(z^2+z={representative}, class={discriminant_class}, split={split})"
                ),
            },
        }
    }
}

impl<S: Scalar, D: std::fmt::Display> DiscriminantEtaleAlgebra<S, D> {
    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

/// Full-center/even-center data joined to the existing Brauer--Wall class.
#[derive(Debug, Clone, PartialEq)]
pub struct CliffordCenterInvariants<S: Scalar, D, B> {
    dimension: usize,
    center: DiscriminantEtaleAlgebra<S, D>,
    even_center: DiscriminantEtaleAlgebra<S, D>,
    brauer_wall_class: B,
    brauer_wall_agrees: bool,
}

impl<S: Scalar, D, B> CliffordCenterInvariants<S, D, B> {
    /// Dimension of the nonsingular quadratic space.
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// `Z(Cl(q))`.
    pub fn center(&self) -> &DiscriminantEtaleAlgebra<S, D> {
        &self.center
    }

    /// `Z(Cl^0(q))`.
    pub fn even_center(&self) -> &DiscriminantEtaleAlgebra<S, D> {
        &self.even_center
    }

    /// The independently computed Brauer--Wall class used for the comparison.
    pub fn brauer_wall_class(&self) -> &B {
        &self.brauer_wall_class
    }

    /// Whether parity and discriminant/Arf class agree with the corresponding
    /// Brauer--Wall coordinates.
    pub fn brauer_wall_agrees(&self) -> bool {
        self.brauer_wall_agrees
    }

    /// The unique quadratic center, except in dimension zero where both centers
    /// are the ground field.
    pub fn quadratic_center(&self) -> Option<&DiscriminantEtaleAlgebra<S, D>> {
        if self.center.degree() == 2 {
            Some(&self.center)
        } else if self.even_center.degree() == 2 {
            Some(&self.even_center)
        } else {
            None
        }
    }
}

impl<S: Scalar, D: std::fmt::Display, B: std::fmt::Display> std::fmt::Display
    for CliffordCenterInvariants<S, D, B>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "CliffordCenters(dim={}, center={}, even_center={}, brauer_wall={}, agrees={})",
            self.dimension,
            self.center,
            self.even_center,
            self.brauer_wall_class,
            self.brauer_wall_agrees
        )
    }
}

impl<S: Scalar, D: std::fmt::Display, B: std::fmt::Display> CliffordCenterInvariants<S, D, B> {
    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

/// Why a Clifford center could not be constructed on the represented domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum CliffordCenterError {
    /// Characteristic-not-two diagonalization failed.
    DiagonalizerFailure,
    /// The form is singular; degenerate Clifford centers have a larger
    /// nilpotent structure and are not discriminant etale algebras.
    SingularForm {
        /// Dimension of the polar radical.
        radical_dim: usize,
    },
    /// The metric has a nonzero general-bilinear contraction in characteristic
    /// two, outside the quadratic Clifford surface.
    GeneralBilinearMetric,
    /// A constructed volume/Artin--Schreier generator failed its scalar
    /// quadratic relation.
    GeneratorRelationFailure,
    /// Field parameters, exact roots, finite windows, or bounded arithmetic are
    /// outside the implemented classifier domain.
    UnsupportedFieldOrArithmetic,
}

impl std::fmt::Display for CliffordCenterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CliffordCenterError::DiagonalizerFailure => {
                f.write_str("metric could not be diagonalized for its Clifford center")
            }
            CliffordCenterError::SingularForm { radical_dim } => write!(
                f,
                "Clifford discriminant centers require a nonsingular form (radical_dim={radical_dim})"
            ),
            CliffordCenterError::GeneralBilinearMetric => f.write_str(
                "characteristic-two Clifford centers require a pure quadratic (q,b) metric",
            ),
            CliffordCenterError::GeneratorRelationFailure => {
                f.write_str("constructed center generator failed its quadratic relation")
            }
            CliffordCenterError::UnsupportedFieldOrArithmetic => {
                f.write_str("field or exact arithmetic is outside the Clifford-center surface")
            }
        }
    }
}

impl std::error::Error for CliffordCenterError {}

/// Real square class of the signed discriminant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RealCenterDiscriminant {
    negative: bool,
}

impl RealCenterDiscriminant {
    /// Whether the signed discriminant is negative.
    pub fn is_negative(self) -> bool {
        self.negative
    }

    /// The real quadratic etale algebra is split exactly for positive signed
    /// discriminant.
    pub fn is_split(self) -> bool {
        !self.negative
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for RealCenterDiscriminant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(if self.negative {
            "negative"
        } else {
            "positive"
        })
    }
}

/// The unique square class over the represented algebraically closed complex
/// domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ComplexCenterDiscriminant;

impl ComplexCenterDiscriminant {
    /// Every nonzero complex square class is trivial on this classifier domain.
    pub fn is_split(self) -> bool {
        true
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for ComplexCenterDiscriminant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("trivial")
    }
}

/// An Artin--Schreier discriminant class over a represented finite
/// characteristic-two field.
#[derive(Debug, Clone)]
pub struct ArtinSchreierCenterDiscriminant<S: Scalar> {
    representative: S,
    field_degree: u128,
    class: u128,
}

impl<S: Scalar> ArtinSchreierCenterDiscriminant<S> {
    fn new(representative: S, field_degree: u128, class: u128) -> Option<Self> {
        (field_degree > 0 && class <= 1).then_some(ArtinSchreierCenterDiscriminant {
            representative,
            field_degree,
            class,
        })
    }

    /// A coefficient `c` in the equation `z^2 + z = c`.
    pub fn representative(&self) -> &S {
        &self.representative
    }

    /// Degree `m` of the represented field over `F_2`.
    pub fn field_degree(&self) -> u128 {
        self.field_degree
    }

    /// The quotient class in `F/AS(F)`, represented by its absolute trace bit.
    pub fn class(&self) -> u128 {
        self.class
    }

    /// The quadratic etale algebra is split exactly when `c` is in the image of
    /// `x -> x^2 + x`.
    pub fn is_split(&self) -> bool {
        self.class == 0
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl<S: Scalar> PartialEq for ArtinSchreierCenterDiscriminant<S> {
    fn eq(&self, other: &Self) -> bool {
        self.field_degree == other.field_degree && self.class == other.class
    }
}

impl<S: Scalar> Eq for ArtinSchreierCenterDiscriminant<S> {}

impl<S: Scalar> std::fmt::Display for ArtinSchreierCenterDiscriminant<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "AS(F_2^{}, representative={}, class={})",
            self.field_degree, self.representative, self.class
        )
    }
}

/// Discriminant class for a const-generic finite field, whose characteristic is
/// selected only after monomorphization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FiniteFieldCenterDiscriminant<S: Scalar> {
    /// Odd-characteristic Kummer square class.
    Kummer(FiniteFieldMilnorK1Class),
    /// Characteristic-two Artin--Schreier class.
    ArtinSchreier(ArtinSchreierCenterDiscriminant<S>),
}

/// Clifford-center report over an odd rational function field.
pub type FunctionFieldCliffordCenterInvariants<S> = CliffordCenterInvariants<
    RationalFunction<S>,
    FunctionFieldMilnorK1Class<S>,
    FunctionFieldBrauerWallClass<S>,
>;

impl<S: Scalar> FiniteFieldCenterDiscriminant<S> {
    /// Whether the associated quadratic etale algebra is split.
    pub fn is_split(&self) -> bool {
        match self {
            FiniteFieldCenterDiscriminant::Kummer(class) => class.is_trivial(),
            FiniteFieldCenterDiscriminant::ArtinSchreier(class) => class.is_split(),
        }
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl<S: Scalar> std::fmt::Display for FiniteFieldCenterDiscriminant<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FiniteFieldCenterDiscriminant::Kummer(class) => write!(f, "{class}"),
            FiniteFieldCenterDiscriminant::ArtinSchreier(class) => write!(f, "{class}"),
        }
    }
}

fn place_quadratic_center<S: Scalar, D, B>(
    dim: usize,
    generator: Multivector<S>,
    relation: QuadraticEtaleRelation<S>,
    discriminant_class: D,
    split: bool,
    brauer_wall_class: B,
    brauer_wall_agrees: bool,
) -> CliffordCenterInvariants<S, D, B> {
    if dim == 0 {
        return CliffordCenterInvariants {
            dimension: 0,
            center: DiscriminantEtaleAlgebra::GroundField,
            even_center: DiscriminantEtaleAlgebra::GroundField,
            brauer_wall_class,
            brauer_wall_agrees,
        };
    }
    let quadratic = DiscriminantEtaleAlgebra::QuadraticEtale {
        generator,
        relation,
        discriminant_class,
        split,
    };
    let (center, even_center) = if dim.is_multiple_of(2) {
        (DiscriminantEtaleAlgebra::GroundField, quadratic)
    } else {
        (quadratic, DiscriminantEtaleAlgebra::GroundField)
    };
    CliffordCenterInvariants {
        dimension: dim,
        center,
        even_center,
        brauer_wall_class,
        brauer_wall_agrees,
    }
}

fn kummer_volume<S: Scalar>(
    metric: &Metric<S>,
) -> Result<(Multivector<S>, S), CliffordCenterError> {
    let diagonal = as_diagonal(metric).ok_or(CliffordCenterError::DiagonalizerFailure)?;
    let radical_dim = diagonal.q().iter().filter(|x| x.is_zero()).count();
    if radical_dim != 0 {
        return Err(CliffordCenterError::SingularForm { radical_dim });
    }

    let algebra = CliffordAlgebra::new(metric.dim(), metric.clone());
    let volume = if metric.b().is_empty() && metric.a().is_empty() {
        algebra.pseudoscalar()
    } else {
        let two = S::one().add(&S::one());
        let half = two
            .inv()
            .ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
        let symmetric_contraction: BTreeMap<(usize, usize), S> = metric
            .b()
            .iter()
            .map(|(&indices, value)| (indices, value.mul(&half)))
            .collect();
        let exterior_gauge = CliffordAlgebra::new(
            metric.dim(),
            Metric::general(
                metric.q().to_vec(),
                metric.b().clone(),
                symmetric_contraction,
            ),
        );
        exterior_gauge
            .transport_gauge_to(&algebra, &exterior_gauge.pseudoscalar())
            .ok_or(CliffordCenterError::GeneratorRelationFailure)?
    };
    let square_mv = algebra.mul(&volume, &volume);
    let square = algebra.scalar_part(&square_mv);
    if square_mv != algebra.scalar(square.clone()) || square.is_zero() {
        return Err(CliffordCenterError::GeneratorRelationFailure);
    }
    Ok((volume, square))
}

fn vector_from_coordinates<S: Scalar>(
    algebra: &CliffordAlgebra<S>,
    coordinates: &[S],
) -> Multivector<S> {
    coordinates
        .iter()
        .enumerate()
        .fold(algebra.zero(), |acc, (i, coefficient)| {
            algebra.add(&acc, &algebra.scalar_mul(coefficient, &algebra.e(i)))
        })
}

fn quadratic_value_char2<S: Scalar>(vector: &[S], q: &[S], polar: &[Vec<S>]) -> S {
    let mut value = S::zero();
    for i in 0..vector.len() {
        value = value.add(&vector[i].mul(&vector[i]).mul(&q[i]));
        for j in (i + 1)..vector.len() {
            value = value.add(&vector[i].mul(&vector[j]).mul(&polar[i][j]));
        }
    }
    value
}

fn polar_value<S: Scalar>(left: &[S], right: &[S], polar: &[Vec<S>]) -> S {
    let mut value = S::zero();
    for i in 0..left.len() {
        for j in (i + 1)..left.len() {
            let cross = left[i].mul(&right[j]).add(&left[j].mul(&right[i]));
            value = value.add(&cross.mul(&polar[i][j]));
        }
    }
    value
}

fn vector_scale<S: Scalar>(coefficient: &S, vector: &[S]) -> Vec<S> {
    vector.iter().map(|x| coefficient.mul(x)).collect()
}

fn vector_add<S: Scalar>(left: &[S], right: &[S]) -> Vec<S> {
    left.iter().zip(right).map(|(x, y)| x.add(y)).collect()
}

struct Char2CenterReduction<S: Scalar> {
    generator: Multivector<S>,
    representative: S,
    arf: u128,
    radical_dim: usize,
}

fn char2_center_reduction<S: Scalar>(
    metric: &Metric<S>,
    trace_to_f2: impl Fn(&S) -> Option<u128>,
) -> Result<Char2CenterReduction<S>, CliffordCenterError> {
    if !metric.a().is_empty() {
        return Err(CliffordCenterError::GeneralBilinearMetric);
    }
    let n = metric.dim();
    let mut polar = vec![vec![S::zero(); n]; n];
    for (&(i, j), value) in metric.b() {
        polar[i][j] = value.clone();
        polar[j][i] = value.clone();
    }
    let mut vectors: Vec<Vec<S>> = (0..n)
        .map(|i| {
            let mut vector = vec![S::zero(); n];
            vector[i] = S::one();
            vector
        })
        .collect();
    let mut pairs = Vec::new();
    let mut representative = S::zero();
    let mut radical_dim = 0usize;

    while let Some(a) = vectors.pop() {
        if let Some(position) = vectors
            .iter()
            .position(|candidate| !polar_value(&a, candidate, &polar).is_zero())
        {
            let b_raw = vectors.swap_remove(position);
            let pairing = polar_value(&a, &b_raw, &polar);
            let pairing_inv = pairing
                .inv()
                .ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
            let b = vector_scale(&pairing_inv, &b_raw);
            for vector in &mut vectors {
                let wb = polar_value(vector, &b, &polar);
                let wa = polar_value(vector, &a, &polar);
                let mut orthogonalized = vector.clone();
                if !wb.is_zero() {
                    orthogonalized = vector_add(&orthogonalized, &vector_scale(&wb, &a));
                }
                if !wa.is_zero() {
                    orthogonalized = vector_add(&orthogonalized, &vector_scale(&wa, &b));
                }
                *vector = orthogonalized;
            }
            let qa = quadratic_value_char2(&a, metric.q(), &polar);
            let qb = quadratic_value_char2(&b, metric.q(), &polar);
            representative = representative.add(&qa.mul(&qb));
            pairs.push((a, b));
        } else {
            radical_dim += 1;
        }
    }

    if radical_dim != 0 {
        return Err(CliffordCenterError::SingularForm { radical_dim });
    }
    let arf = trace_to_f2(&representative)
        .filter(|class| *class <= 1)
        .ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let algebra = CliffordAlgebra::new(n, metric.clone());
    let generator = pairs.iter().fold(algebra.zero(), |acc, (a, b)| {
        let a = vector_from_coordinates(&algebra, a);
        let b = vector_from_coordinates(&algebra, b);
        algebra.add(&acc, &algebra.mul(&a, &b))
    });
    let relation_value = algebra.add(&algebra.mul(&generator, &generator), &generator);
    if relation_value != algebra.scalar(representative.clone()) {
        return Err(CliffordCenterError::GeneratorRelationFailure);
    }
    Ok(Char2CenterReduction {
        generator,
        representative,
        arf,
        radical_dim,
    })
}

fn char2_centers<S: Scalar, B>(
    metric: &Metric<S>,
    reduction: Char2CenterReduction<S>,
    field_degree: u128,
    brauer_wall_class: B,
    brauer_wall_agrees: bool,
) -> Result<CliffordCenterInvariants<S, ArtinSchreierCenterDiscriminant<S>, B>, CliffordCenterError>
{
    debug_assert_eq!(reduction.radical_dim, 0);
    let discriminant = ArtinSchreierCenterDiscriminant::new(
        reduction.representative.clone(),
        field_degree,
        reduction.arf,
    )
    .ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    Ok(place_quadratic_center(
        metric.dim(),
        reduction.generator,
        QuadraticEtaleRelation::ArtinSchreier {
            representative: reduction.representative,
        },
        discriminant.clone(),
        discriminant.is_split(),
        brauer_wall_class,
        brauer_wall_agrees,
    ))
}

pub(crate) fn centers_real(
    metric: &Metric<Surreal>,
) -> Result<
    CliffordCenterInvariants<Surreal, RealCenterDiscriminant, BrauerWallClass>,
    CliffordCenterError,
> {
    let brauer_wall =
        bw_class_real(metric).ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let (generator, square) = kummer_volume(metric)?;
    let discriminant = RealCenterDiscriminant {
        negative: square.sign() == Ordering::Less,
    };
    let agrees = match brauer_wall {
        BrauerWallClass::Real(index) => {
            index % 2 == (metric.dim() % 2) as u128
                && matches!(index, 1 | 2 | 5 | 6) == discriminant.negative
        }
        _ => false,
    };
    Ok(place_quadratic_center(
        metric.dim(),
        generator,
        QuadraticEtaleRelation::Kummer {
            generator_square: square,
        },
        discriminant,
        discriminant.is_split(),
        brauer_wall,
        agrees,
    ))
}

pub(crate) fn centers_complex(
    metric: &Metric<Surcomplex<Surreal>>,
) -> Result<
    CliffordCenterInvariants<Surcomplex<Surreal>, ComplexCenterDiscriminant, BrauerWallClass>,
    CliffordCenterError,
> {
    let brauer_wall =
        bw_class_complex(metric).ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let (generator, square) = kummer_volume(metric)?;
    let agrees = matches!(
        brauer_wall,
        BrauerWallClass::Complex(parity) if parity == (metric.dim() % 2) as u128
    );
    Ok(place_quadratic_center(
        metric.dim(),
        generator,
        QuadraticEtaleRelation::Kummer {
            generator_square: square,
        },
        ComplexCenterDiscriminant,
        true,
        brauer_wall,
        agrees,
    ))
}

pub(crate) fn centers_rational(
    metric: &Metric<Rational>,
) -> Result<
    CliffordCenterInvariants<Rational, RationalMilnorK1Class, RationalBrauerWallClass>,
    CliffordCenterError,
> {
    let brauer_wall =
        bw_class_rational(metric).ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let (generator, square) = kummer_volume(metric)?;
    let discriminant = RationalMilnorK1Class::from_rational(&square)
        .ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let agrees = brauer_wall.dimension_parity() == (metric.dim() % 2) as u128
        && brauer_wall.signed_discriminant() == discriminant.representative();
    Ok(place_quadratic_center(
        metric.dim(),
        generator,
        QuadraticEtaleRelation::Kummer {
            generator_square: square,
        },
        discriminant,
        discriminant.is_trivial(),
        brauer_wall,
        agrees,
    ))
}

fn centers_finite_odd<F>(
    metric: &Metric<F>,
) -> Result<
    CliffordCenterInvariants<F, FiniteFieldCenterDiscriminant<F>, BrauerWallClass>,
    CliffordCenterError,
>
where
    F: FiniteOddField + Mod2MilnorField<K1Class = FiniteFieldMilnorK1Class>,
{
    F::ensure_supported().ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let brauer_wall =
        bw_class_finite_odd(metric).ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let (generator, square) = kummer_volume(metric)?;
    let class = crate::forms::milnor_symbol_1(&square)
        .ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let agrees = matches!(
        brauer_wall,
        BrauerWallClass::OddChar { e0, sclass, .. }
            if e0 == (metric.dim() % 2) as u128 && sclass == class.nonsquare()
    );
    let discriminant = FiniteFieldCenterDiscriminant::Kummer(class);
    Ok(place_quadratic_center(
        metric.dim(),
        generator,
        QuadraticEtaleRelation::Kummer {
            generator_square: square,
        },
        discriminant.clone(),
        discriminant.is_split(),
        brauer_wall,
        agrees,
    ))
}

pub(crate) fn centers_fp<const P: u128>(
    metric: &Metric<Fp<P>>,
) -> Result<
    CliffordCenterInvariants<Fp<P>, FiniteFieldCenterDiscriminant<Fp<P>>, BrauerWallClass>,
    CliffordCenterError,
> {
    if P != 2 {
        return centers_finite_odd(metric);
    }
    if !Fp::<P>::modulus_is_prime() {
        return Err(CliffordCenterError::UnsupportedFieldOrArithmetic);
    }
    let reduction = char2_center_reduction(metric, |x| Some(x.value() & 1))?;
    let qd = metric
        .q()
        .iter()
        .map(|x| x.value() == 1)
        .collect::<Vec<_>>();
    let mut polar = vec![0u128; metric.dim()];
    for (&(i, j), value) in metric.b() {
        if value.value() == 1 {
            polar[i] |= 1u128 << j;
            polar[j] |= 1u128 << i;
        }
    }
    let existing = arf_f2(metric.dim(), &qd, &polar);
    let arf = existing.arf;
    let brauer_wall = BrauerWallClass::Char2 {
        field_degree: 1,
        arf,
    };
    let discriminant = ArtinSchreierCenterDiscriminant::new(reduction.representative, 1, arf)
        .ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let discriminant = FiniteFieldCenterDiscriminant::ArtinSchreier(discriminant);
    Ok(place_quadratic_center(
        metric.dim(),
        reduction.generator,
        QuadraticEtaleRelation::ArtinSchreier {
            representative: reduction.representative,
        },
        discriminant.clone(),
        discriminant.is_split(),
        brauer_wall,
        existing.radical_dim == 0 && existing.arf == reduction.arf,
    ))
}

pub(crate) fn centers_fpn<const P: u128, const N: usize>(
    metric: &Metric<Fpn<P, N>>,
) -> Result<
    CliffordCenterInvariants<Fpn<P, N>, FiniteFieldCenterDiscriminant<Fpn<P, N>>, BrauerWallClass>,
    CliffordCenterError,
> {
    if P != 2 {
        return centers_finite_odd(metric);
    }
    if !Fpn::<P, N>::is_supported_field() {
        return Err(CliffordCenterError::UnsupportedFieldOrArithmetic);
    }
    let reduction = char2_center_reduction(metric, |x| Some(x.trace().value()))?;
    let existing =
        arf_fpn_char2(metric).ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let field_degree = N as u128;
    let brauer_wall = BrauerWallClass::Char2 {
        field_degree,
        arf: existing.arf,
    };
    let agrees = existing.radical_dim == 0 && existing.arf == reduction.arf;
    let discriminant =
        ArtinSchreierCenterDiscriminant::new(reduction.representative, field_degree, reduction.arf)
            .ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let discriminant = FiniteFieldCenterDiscriminant::ArtinSchreier(discriminant);
    Ok(place_quadratic_center(
        metric.dim(),
        reduction.generator,
        QuadraticEtaleRelation::ArtinSchreier {
            representative: reduction.representative,
        },
        discriminant.clone(),
        discriminant.is_split(),
        brauer_wall,
        agrees,
    ))
}

pub(crate) fn centers_function_field<S: FiniteOddField>(
    metric: &Metric<RationalFunction<S>>,
) -> Result<FunctionFieldCliffordCenterInvariants<S>, CliffordCenterError> {
    let brauer_wall =
        bw_class_function_field(metric).ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let (generator, square) = kummer_volume(metric)?;
    let discriminant = crate::forms::milnor_symbol_1(&square)
        .ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let bw_discriminant = crate::forms::milnor_symbol_1(brauer_wall.signed_discriminant())
        .ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let agrees = brauer_wall.dimension_parity() == (metric.dim() % 2) as u128
        && discriminant == bw_discriminant;
    let split = discriminant.is_trivial();
    Ok(place_quadratic_center(
        metric.dim(),
        generator,
        QuadraticEtaleRelation::Kummer {
            generator_square: square,
        },
        discriminant,
        split,
        brauer_wall,
        agrees,
    ))
}

fn nimber_metric_field_degree(metric: &Metric<Nimber>) -> u128 {
    metric
        .q()
        .iter()
        .map(|x| nim_degree(x.0))
        .chain(metric.b().values().map(|x| nim_degree(x.0)))
        .max()
        .unwrap_or(1)
}

pub(crate) fn centers_nimber(
    metric: &Metric<Nimber>,
) -> Result<
    CliffordCenterInvariants<Nimber, ArtinSchreierCenterDiscriminant<Nimber>, BrauerWallClass>,
    CliffordCenterError,
> {
    let field_degree = nimber_metric_field_degree(metric);
    let reduction = char2_center_reduction(metric, |x| Some(nim_trace(x.0, field_degree)))?;
    let brauer_wall =
        bw_class_nimber(metric).ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let agrees = matches!(
        brauer_wall,
        BrauerWallClass::Char2 {
            field_degree: degree,
            arf,
        } if degree == field_degree && arf == reduction.arf
    );
    char2_centers(metric, reduction, field_degree, brauer_wall, agrees)
}

fn ordinal_trace_to_f2(x: &Ordinal, degree: u128) -> Option<u128> {
    let mut trace = Ordinal::zero();
    let mut conjugate = x.clone();
    for i in 0..degree {
        trace = trace.add(&conjugate);
        if i + 1 != degree {
            conjugate = conjugate.nim_mul(&conjugate)?;
        }
    }
    match trace.as_finite()? {
        0 => Some(0),
        1 => Some(1),
        _ => None,
    }
}

pub(crate) fn centers_ordinal(
    metric: &Metric<Ordinal>,
) -> Result<
    CliffordCenterInvariants<Ordinal, ArtinSchreierCenterDiscriminant<Ordinal>, BrauerWallClass>,
    CliffordCenterError,
> {
    let field_degree = ordinal_metric_finite_subfield_degree(metric)
        .ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let reduction = char2_center_reduction(metric, |x| ordinal_trace_to_f2(x, field_degree))?;
    let existing =
        arf_ordinal_finite(metric).ok_or(CliffordCenterError::UnsupportedFieldOrArithmetic)?;
    let brauer_wall = BrauerWallClass::Char2 {
        field_degree,
        arf: existing.arf,
    };
    let agrees = existing.radical_dim == 0 && existing.arf == reduction.arf;
    char2_centers(metric, reduction, field_degree, brauer_wall, agrees)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{Fp, Fpn};
    use std::collections::BTreeMap;

    fn q(n: i128) -> Rational {
        Rational::from_int(n)
    }

    fn assert_kummer_relation<S: Scalar, D, B>(
        metric: &Metric<S>,
        centers: &CliffordCenterInvariants<S, D, B>,
    ) {
        let algebra = CliffordAlgebra::new(metric.dim(), metric.clone());
        let quadratic = centers.quadratic_center().expect("positive dimension");
        let generator = quadratic.generator().unwrap();
        let QuadraticEtaleRelation::Kummer { generator_square } = quadratic.relation().unwrap()
        else {
            panic!("expected Kummer relation")
        };
        assert_eq!(
            algebra.mul(generator, generator),
            algebra.scalar(generator_square.clone())
        );
    }

    fn assert_artin_schreier_relation<S: Scalar, D, B>(
        metric: &Metric<S>,
        centers: &CliffordCenterInvariants<S, D, B>,
    ) {
        let algebra = CliffordAlgebra::new(metric.dim(), metric.clone());
        let quadratic = centers.quadratic_center().expect("positive dimension");
        let generator = quadratic.generator().unwrap();
        let QuadraticEtaleRelation::ArtinSchreier { representative } =
            quadratic.relation().unwrap()
        else {
            panic!("expected Artin-Schreier relation")
        };
        assert_eq!(
            algebra.add(&algebra.mul(generator, generator), generator),
            algebra.scalar(representative.clone())
        );
    }

    fn assert_full_central<S: Scalar>(metric: &Metric<S>, generator: &Multivector<S>) {
        let algebra = CliffordAlgebra::new(metric.dim(), metric.clone());
        for i in 0..metric.dim() {
            assert!(algebra.commutator(generator, &algebra.e(i)).is_zero());
        }
    }

    fn assert_even_central<S: Scalar>(metric: &Metric<S>, generator: &Multivector<S>) {
        let algebra = CliffordAlgebra::new(metric.dim(), metric.clone());
        for i in 0..metric.dim() {
            for j in (i + 1)..metric.dim() {
                let even = algebra.mul(&algebra.e(i), &algebra.e(j));
                assert!(algebra.commutator(generator, &even).is_zero());
            }
        }
    }

    #[test]
    fn rational_centers_switch_with_parity_and_materialize_volume_relation() {
        let odd = Metric::diagonal(vec![q(2)]);
        let odd_centers = centers_rational(&odd).unwrap();
        assert_eq!(odd_centers.center().degree(), 2);
        assert!(odd_centers.even_center().is_ground_field());
        assert_eq!(odd_centers.center().quadratic_is_split(), Some(false));
        assert_eq!(
            odd_centers.center().display(),
            "QuadraticEtale(omega^2=2, class=MilnorK1Mod2(Q; 2), split=false)"
        );
        assert!(odd_centers.brauer_wall_agrees());
        assert_kummer_relation(&odd, &odd_centers);
        assert_full_central(&odd, odd_centers.center().generator().unwrap());
        assert_eq!(odd.clifford_centers(), Ok(odd_centers.clone()));
        let odd_algebra = CliffordAlgebra::new(odd.dim(), odd.clone());
        assert_eq!(odd_algebra.centers(), Ok(odd_centers));

        let even = Metric::diagonal(vec![q(1), q(1)]);
        let even_centers = centers_rational(&even).unwrap();
        assert!(even_centers.center().is_ground_field());
        assert_eq!(even_centers.even_center().degree(), 2);
        assert_eq!(
            even_centers
                .even_center()
                .discriminant_class()
                .unwrap()
                .representative(),
            -1
        );
        assert!(even_centers.brauer_wall_agrees());
        assert_kummer_relation(&even, &even_centers);
        assert_even_central(&even, even_centers.even_center().generator().unwrap());

        let split = Metric::diagonal(vec![q(1), q(-1)]);
        assert_eq!(
            centers_rational(&split)
                .unwrap()
                .even_center()
                .quadratic_is_split(),
            Some(true)
        );
    }

    #[test]
    fn nondiagonal_and_general_gauge_centers_use_actual_central_generators() {
        let mut polar = BTreeMap::new();
        polar.insert((0, 1), q(2));
        let hyperbolic = Metric::new(vec![q(0), q(0)], polar);
        let centers = centers_rational(&hyperbolic).unwrap();
        assert_eq!(centers.even_center().quadratic_is_split(), Some(true));
        assert_kummer_relation(&hyperbolic, &centers);
        assert_even_central(&hyperbolic, centers.even_center().generator().unwrap());

        let nondiagonal_odd = hyperbolic.direct_sum(&Metric::diagonal(vec![q(1)]));
        let centers = centers_rational(&nondiagonal_odd).unwrap();
        assert_kummer_relation(&nondiagonal_odd, &centers);
        assert_full_central(&nondiagonal_odd, centers.center().generator().unwrap());

        let mut upper = BTreeMap::new();
        upper.insert((0, 1), q(1));
        let general = Metric::general(vec![q(1), q(1)], BTreeMap::new(), upper);
        let centers = centers_rational(&general).unwrap();
        assert_kummer_relation(&general, &centers);
        assert_even_central(&general, centers.even_center().generator().unwrap());
    }

    #[test]
    fn finite_odd_and_function_field_centers_match_brauer_wall_coordinates() {
        let finite = Metric::diagonal(vec![Fp::<5>::from_int(1), Fp::<5>::from_int(2)]);
        let finite_centers = centers_fp(&finite).unwrap();
        assert!(finite_centers.brauer_wall_agrees());
        assert_eq!(
            finite_centers.even_center().quadratic_is_split(),
            Some(false)
        );
        assert_kummer_relation(&finite, &finite_centers);

        type F5t = RationalFunction<Fp<5>>;
        let t = F5t::new(vec![Fp::<5>::zero(), Fp::<5>::one()], vec![Fp::<5>::one()]);
        let function = Metric::diagonal(vec![t.clone()]);
        let function_centers = centers_function_field(&function).unwrap();
        assert!(function_centers.brauer_wall_agrees());
        assert_eq!(function_centers.center().quadratic_is_split(), Some(false));
        assert_kummer_relation(&function, &function_centers);
    }

    #[test]
    fn real_and_complex_center_classes_match_the_classification_tables() {
        for positive in 0..=4 {
            for negative in 0..=4 {
                let coefficients = std::iter::repeat_n(Surreal::one(), positive)
                    .chain(std::iter::repeat_n(Surreal::one().neg(), negative))
                    .collect();
                let real = Metric::diagonal(coefficients);
                let real_centers = centers_real(&real).unwrap();
                assert!(real_centers.brauer_wall_agrees());
                if positive + negative > 0 {
                    assert_kummer_relation(&real, &real_centers);
                }
            }
        }

        let real = Metric::diagonal(vec![Surreal::one(), Surreal::one()]);
        assert_eq!(
            centers_real(&real)
                .unwrap()
                .even_center()
                .quadratic_is_split(),
            Some(false)
        );

        let complex = Metric::diagonal(vec![
            Surcomplex::<Surreal>::one(),
            Surcomplex::<Surreal>::one(),
        ]);
        let complex_centers = centers_complex(&complex).unwrap();
        assert!(complex_centers.brauer_wall_agrees());
        assert_eq!(
            complex_centers.even_center().quadratic_is_split(),
            Some(true)
        );
        assert_kummer_relation(&complex, &complex_centers);
    }

    fn f2_plane(q0: i128, q1: i128) -> Metric<Fpn<2, 1>> {
        let mut polar = BTreeMap::new();
        polar.insert((0, 1), Fpn::<2, 1>::one());
        Metric::new(
            vec![Fpn::<2, 1>::from_int(q0), Fpn::<2, 1>::from_int(q1)],
            polar,
        )
    }

    #[test]
    fn characteristic_two_even_center_is_the_artin_schreier_discriminant_algebra() {
        let split = f2_plane(0, 0);
        let split_centers = centers_fpn(&split).unwrap();
        assert!(split_centers.center().is_ground_field());
        assert_eq!(split_centers.even_center().quadratic_is_split(), Some(true));
        assert!(split_centers.brauer_wall_agrees());
        assert_artin_schreier_relation(&split, &split_centers);
        assert_even_central(&split, split_centers.even_center().generator().unwrap());

        let nonsplit = f2_plane(1, 1);
        let nonsplit_centers = centers_fpn(&nonsplit).unwrap();
        assert_eq!(
            nonsplit_centers.even_center().quadratic_is_split(),
            Some(false)
        );
        assert!(nonsplit_centers.brauer_wall_agrees());
        assert_artin_schreier_relation(&nonsplit, &nonsplit_centers);
        assert_even_central(
            &nonsplit,
            nonsplit_centers.even_center().generator().unwrap(),
        );

        let rank_four = split.direct_sum(&nonsplit);
        let rank_four_centers = centers_fpn(&rank_four).unwrap();
        assert_eq!(
            rank_four_centers.even_center().quadratic_is_split(),
            Some(false)
        );
        assert!(rank_four_centers.brauer_wall_agrees());
        assert_artin_schreier_relation(&rank_four, &rank_four_centers);
        assert_even_central(
            &rank_four,
            rank_four_centers.even_center().generator().unwrap(),
        );
    }

    #[test]
    fn nimber_and_ordinal_centers_reuse_their_finite_field_windows() {
        let mut nim_polar = BTreeMap::new();
        nim_polar.insert((0, 1), Nimber(1));
        let nim = Metric::new(vec![Nimber(1), Nimber(1)], nim_polar);
        let nim_centers = centers_nimber(&nim).unwrap();
        assert!(nim_centers.brauer_wall_agrees());
        assert_eq!(nim_centers.even_center().quadratic_is_split(), Some(false));
        assert_artin_schreier_relation(&nim, &nim_centers);

        let mut ord_polar = BTreeMap::new();
        ord_polar.insert((0, 1), Ordinal::from_int(1));
        let ord = Metric::new(vec![Ordinal::from_int(1), Ordinal::from_int(1)], ord_polar);
        let ord_centers = centers_ordinal(&ord).unwrap();
        assert!(ord_centers.brauer_wall_agrees());
        assert_eq!(ord_centers.even_center().quadratic_is_split(), Some(false));
        assert_artin_schreier_relation(&ord, &ord_centers);
    }

    #[test]
    fn dimension_zero_and_singular_forms_keep_their_exact_boundaries() {
        let empty = Metric::<Rational>::diagonal(Vec::new());
        let centers = centers_rational(&empty).unwrap();
        assert!(centers.center().is_ground_field());
        assert!(centers.even_center().is_ground_field());
        assert!(centers.quadratic_center().is_none());

        let singular = Metric::diagonal(vec![q(1), q(0)]);
        assert_eq!(
            centers_rational(&singular),
            Err(CliffordCenterError::SingularForm { radical_dim: 1 })
        );
    }
}
