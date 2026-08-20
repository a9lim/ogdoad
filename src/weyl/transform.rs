use super::algebra::{ExpansionTracker, WeylAlgebra, WeylError, WeylExpansionBudget};
use super::element::{add_term, WeylElement};
use crate::scalar::Scalar;
use std::collections::{BTreeMap, BTreeSet};

/// A checked affine-linear homomorphism between Weyl algebras over the same
/// scalar ring.
///
/// `linear[target][source]` is the coefficient of the target generator in the
/// image of a source generator:
///
/// ```text
/// z_source_i |-> translation[i] + sum_j linear[j][i] z_target_j.
/// ```
///
/// Construction checks every defining commutator. Applying the map substitutes
/// generator images in PBW order under one shared expansion budget.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylHomomorphism<S: Scalar> {
    source: WeylAlgebra<S>,
    target: WeylAlgebra<S>,
    linear: Vec<Vec<S>>,
    translation: Vec<S>,
    images: Vec<WeylElement<S>>,
}

impl<S: Scalar> WeylHomomorphism<S> {
    /// Construct an affine-linear map and verify all source commutators in the
    /// target algebra.
    pub fn try_new(
        source: WeylAlgebra<S>,
        target: WeylAlgebra<S>,
        linear: Vec<Vec<S>>,
        translation: Vec<S>,
    ) -> Result<Self, WeylError> {
        validate_shape(&source, &target, &linear, &translation)?;
        for left in 0..source.dim() {
            for right in 0..source.dim() {
                if linear_commutator(&target, &linear, left, right)
                    != source.commutator[left][right]
                {
                    return Err(WeylError::CommutatorNotPreserved { left, right });
                }
            }
        }
        let images = affine_images(&target, &linear, &translation);
        Ok(Self {
            source,
            target,
            linear,
            translation,
            images,
        })
    }

    /// Identity automorphism viewed as a homomorphism.
    pub fn identity(algebra: &WeylAlgebra<S>) -> Self {
        Self::try_new(
            algebra.clone(),
            algebra.clone(),
            identity_matrix::<S>(algebra.dim()),
            vec![S::zero(); algebra.dim()],
        )
        .expect("identity preserves every Weyl commutator")
    }

    /// Source Weyl algebra.
    pub fn source(&self) -> &WeylAlgebra<S> {
        &self.source
    }

    /// Target Weyl algebra.
    pub fn target(&self) -> &WeylAlgebra<S> {
        &self.target
    }

    /// Target-by-source linear coefficient matrix.
    pub fn linear(&self) -> &[Vec<S>] {
        &self.linear
    }

    /// Constant image of each source generator.
    pub fn translation(&self) -> &[S] {
        &self.translation
    }

    /// Checked affine image of one source generator.
    pub fn generator_image(&self, index: usize) -> Result<&WeylElement<S>, WeylError> {
        self.images
            .get(index)
            .ok_or(WeylError::GeneratorOutOfRange {
                index,
                dim: self.source.dim(),
            })
    }

    /// Apply the homomorphism without a finite expansion budget.
    pub fn apply(&self, element: &WeylElement<S>) -> Result<WeylElement<S>, WeylError> {
        self.apply_with_budget(element, WeylExpansionBudget::unbounded())
    }

    /// Apply the homomorphism under one term/work expansion budget.
    pub fn apply_with_budget(
        &self,
        element: &WeylElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<WeylElement<S>, WeylError> {
        apply_affine_images(
            &self.source,
            &self.target,
            &self.images,
            element,
            false,
            budget,
        )
    }

    /// Compose `self` after `before`, returning `self o before`.
    pub fn compose(&self, before: &Self) -> Result<Self, WeylError> {
        if before.target != self.source {
            return Err(WeylError::MapContextMismatch);
        }
        let linear = matrix_mul(&self.linear, &before.linear);
        let mut translation = before.translation.clone();
        for (source, translated) in translation.iter_mut().enumerate() {
            for middle in 0..self.source.dim() {
                *translated =
                    translated.add(&before.linear[middle][source].mul(&self.translation[middle]));
            }
        }
        Self::try_new(
            before.source.clone(),
            self.target.clone(),
            linear,
            translation,
        )
    }

    /// Invert a square affine map whose represented linear part is invertible.
    pub fn inverse(&self) -> Result<Self, WeylError> {
        if self.source.dim() != self.target.dim() {
            return Err(WeylError::NonInvertibleLinearPart);
        }
        let inverse_linear = crate::linalg::field::inverse_matrix(self.linear.clone())
            .ok_or(WeylError::NonInvertibleLinearPart)?;
        let mut inverse_translation = vec![S::zero(); self.target.dim()];
        for (source, translated) in inverse_translation.iter_mut().enumerate() {
            for target in 0..self.source.dim() {
                *translated =
                    translated.sub(&inverse_linear[target][source].mul(&self.translation[target]));
            }
        }
        Self::try_new(
            self.target.clone(),
            self.source.clone(),
            inverse_linear,
            inverse_translation,
        )
    }

    /// Block-direct-sum two homomorphisms.
    pub fn direct_sum(&self, other: &Self) -> Result<Self, WeylError> {
        let source = self.source.try_direct_sum(&other.source)?;
        let target = self.target.try_direct_sum(&other.target)?;
        let mut linear = vec![vec![S::zero(); source.dim()]; target.dim()];
        for row in 0..self.target.dim() {
            for column in 0..self.source.dim() {
                linear[row][column] = self.linear[row][column].clone();
            }
        }
        for row in 0..other.target.dim() {
            for column in 0..other.source.dim() {
                linear[self.target.dim() + row][self.source.dim() + column] =
                    other.linear[row][column].clone();
            }
        }
        let translation = self
            .translation
            .iter()
            .cloned()
            .chain(other.translation.iter().cloned())
            .collect();
        Self::try_new(source, target, linear, translation)
    }

    /// Embed source generators into selected target coordinates.
    ///
    /// The index list must have one distinct target index per source generator;
    /// commutator preservation is checked after constructing the coordinate
    /// injection.
    pub fn coordinate_embedding(
        source: &WeylAlgebra<S>,
        target: &WeylAlgebra<S>,
        target_indices: &[usize],
    ) -> Result<Self, WeylError> {
        if target_indices.len() != source.dim() {
            return Err(WeylError::EmbeddingDimensionMismatch {
                expected: source.dim(),
                actual: target_indices.len(),
            });
        }
        let mut seen = BTreeSet::new();
        let mut linear = vec![vec![S::zero(); source.dim()]; target.dim()];
        for (source_index, &target_index) in target_indices.iter().enumerate() {
            if target_index >= target.dim() {
                return Err(WeylError::EmbeddingIndexOutOfRange {
                    index: target_index,
                    dim: target.dim(),
                });
            }
            if !seen.insert(target_index) {
                return Err(WeylError::DuplicateEmbeddingIndex {
                    index: target_index,
                });
            }
            linear[target_index][source_index] = S::one();
        }
        Self::try_new(
            source.clone(),
            target.clone(),
            linear,
            vec![S::zero(); source.dim()],
        )
    }

    /// Canonical inclusion of the left factor into an orthogonal direct sum.
    pub fn left_direct_sum_embedding(
        left: &WeylAlgebra<S>,
        right: &WeylAlgebra<S>,
    ) -> Result<Self, WeylError> {
        let target = left.try_direct_sum(right)?;
        let indices: Vec<usize> = (0..left.dim()).collect();
        Self::coordinate_embedding(left, &target, &indices)
    }

    /// Canonical inclusion of the right factor into an orthogonal direct sum.
    pub fn right_direct_sum_embedding(
        left: &WeylAlgebra<S>,
        right: &WeylAlgebra<S>,
    ) -> Result<Self, WeylError> {
        let target = left.try_direct_sum(right)?;
        let indices: Vec<usize> = (0..right.dim()).map(|index| left.dim() + index).collect();
        Self::coordinate_embedding(right, &target, &indices)
    }
}

/// An invertible affine-linear Weyl endomorphism.
///
/// The wrapper stores a checked inverse, making automorphisms a distinct public
/// type from general homomorphisms.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylAutomorphism<S: Scalar> {
    forward: WeylHomomorphism<S>,
    inverse: WeylHomomorphism<S>,
}

impl<S: Scalar> WeylAutomorphism<S> {
    /// Promote an invertible affine endomorphism.
    pub fn try_from_homomorphism(forward: WeylHomomorphism<S>) -> Result<Self, WeylError> {
        if forward.source != forward.target {
            return Err(WeylError::NotEndomorphism);
        }
        let inverse = forward.inverse()?;
        Ok(Self { forward, inverse })
    }

    /// Underlying checked homomorphism.
    pub fn homomorphism(&self) -> &WeylHomomorphism<S> {
        &self.forward
    }

    /// Underlying Weyl algebra.
    pub fn algebra(&self) -> &WeylAlgebra<S> {
        self.forward.source()
    }

    /// Checked inverse homomorphism.
    pub fn inverse_homomorphism(&self) -> &WeylHomomorphism<S> {
        &self.inverse
    }

    /// Apply the automorphism.
    pub fn apply(&self, element: &WeylElement<S>) -> Result<WeylElement<S>, WeylError> {
        self.forward.apply(element)
    }

    /// Apply the automorphism under an expansion budget.
    pub fn apply_with_budget(
        &self,
        element: &WeylElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<WeylElement<S>, WeylError> {
        self.forward.apply_with_budget(element, budget)
    }

    /// Apply the checked inverse automorphism.
    pub fn apply_inverse(&self, element: &WeylElement<S>) -> Result<WeylElement<S>, WeylError> {
        self.inverse.apply(element)
    }

    /// Return the inverse automorphism.
    pub fn inverse(&self) -> Self {
        Self {
            forward: self.inverse.clone(),
            inverse: self.forward.clone(),
        }
    }

    /// Compose `self` after `before`.
    pub fn compose(&self, before: &Self) -> Result<Self, WeylError> {
        Self::try_from_homomorphism(self.forward.compose(&before.forward)?)
    }
}

/// An invertible affine-linear anti-endomorphism.
///
/// It reverses products: `a(uv) = a(v)a(u)`. Construction checks the reversed
/// commutator relation separately from [`WeylAutomorphism`].
#[derive(Clone, Debug, PartialEq)]
pub struct WeylAntiAutomorphism<S: Scalar> {
    algebra: WeylAlgebra<S>,
    linear: Vec<Vec<S>>,
    translation: Vec<S>,
    images: Vec<WeylElement<S>>,
    inverse_linear: Vec<Vec<S>>,
    inverse_translation: Vec<S>,
}

impl<S: Scalar> WeylAntiAutomorphism<S> {
    /// Construct an affine anti-automorphism of `algebra`.
    pub fn try_new(
        algebra: WeylAlgebra<S>,
        linear: Vec<Vec<S>>,
        translation: Vec<S>,
    ) -> Result<Self, WeylError> {
        validate_shape(&algebra, &algebra, &linear, &translation)?;
        for left in 0..algebra.dim() {
            for right in 0..algebra.dim() {
                if linear_commutator(&algebra, &linear, left, right)
                    != algebra.commutator[left][right].neg()
                {
                    return Err(WeylError::CommutatorNotReversed { left, right });
                }
            }
        }
        let inverse_linear = crate::linalg::field::inverse_matrix(linear.clone())
            .ok_or(WeylError::NonInvertibleLinearPart)?;
        let mut inverse_translation = vec![S::zero(); algebra.dim()];
        for (source, translated) in inverse_translation.iter_mut().enumerate() {
            for target in 0..algebra.dim() {
                *translated =
                    translated.sub(&inverse_linear[target][source].mul(&translation[target]));
            }
        }
        let images = affine_images(&algebra, &linear, &translation);
        Ok(Self {
            algebra,
            linear,
            translation,
            images,
            inverse_linear,
            inverse_translation,
        })
    }

    /// Underlying Weyl algebra.
    pub fn algebra(&self) -> &WeylAlgebra<S> {
        &self.algebra
    }

    /// Target-by-source linear coefficient matrix.
    pub fn linear(&self) -> &[Vec<S>] {
        &self.linear
    }

    /// Constant image of each generator.
    pub fn translation(&self) -> &[S] {
        &self.translation
    }

    /// Apply the anti-automorphism, reversing PBW substitution order.
    pub fn apply(&self, element: &WeylElement<S>) -> Result<WeylElement<S>, WeylError> {
        self.apply_with_budget(element, WeylExpansionBudget::unbounded())
    }

    /// Apply the anti-automorphism under an expansion budget.
    pub fn apply_with_budget(
        &self,
        element: &WeylElement<S>,
        budget: WeylExpansionBudget,
    ) -> Result<WeylElement<S>, WeylError> {
        apply_affine_images(
            &self.algebra,
            &self.algebra,
            &self.images,
            element,
            true,
            budget,
        )
    }

    /// Return the inverse anti-automorphism.
    pub fn inverse(&self) -> Self {
        Self::try_new(
            self.algebra.clone(),
            self.inverse_linear.clone(),
            self.inverse_translation.clone(),
        )
        .expect("the affine inverse of an anti-automorphism is anti-multiplicative")
    }

    /// Compose `self` after another anti-automorphism. Reversing twice produces
    /// an ordinary automorphism.
    pub fn compose_anti(&self, before: &Self) -> Result<WeylAutomorphism<S>, WeylError> {
        if self.algebra != before.algebra {
            return Err(WeylError::MapContextMismatch);
        }
        let linear = matrix_mul(&self.linear, &before.linear);
        let mut translation = before.translation.clone();
        for (source, translated) in translation.iter_mut().enumerate() {
            for middle in 0..self.algebra.dim() {
                *translated =
                    translated.add(&before.linear[middle][source].mul(&self.translation[middle]));
            }
        }
        WeylAutomorphism::try_from_homomorphism(WeylHomomorphism::try_new(
            self.algebra.clone(),
            self.algebra.clone(),
            linear,
            translation,
        )?)
    }
}

impl<S: Scalar> WeylAlgebra<S> {
    /// Standard Fourier automorphism `x_i -> d_i`, `d_i -> -x_i`.
    pub fn fourier_automorphism(&self) -> Result<WeylAutomorphism<S>, WeylError> {
        let pairs = self.standard_pairs.ok_or(WeylError::RequiresStandard)?;
        let mut linear = vec![vec![S::zero(); self.dim()]; self.dim()];
        for pair in 0..pairs {
            linear[pairs + pair][pair] = S::one();
            linear[pair][pairs + pair] = S::one().neg();
        }
        self.automorphism_from_data(linear, vec![S::zero(); self.dim()])
    }

    /// Standard diagonal symplectic scaling
    /// `x_i -> lambda_i x_i`, `d_i -> lambda_i^-1 d_i`.
    pub fn scaling_automorphism(&self, scales: &[S]) -> Result<WeylAutomorphism<S>, WeylError> {
        let pairs = self.standard_pairs.ok_or(WeylError::RequiresStandard)?;
        if scales.len() != pairs {
            return Err(WeylError::ScaleDimensionMismatch {
                expected: pairs,
                actual: scales.len(),
            });
        }
        let mut linear = vec![vec![S::zero(); self.dim()]; self.dim()];
        for (pair, scale) in scales.iter().enumerate() {
            let inverse = scale.inv().ok_or(WeylError::NonUnitScale { index: pair })?;
            linear[pair][pair] = scale.clone();
            linear[pairs + pair][pairs + pair] = inverse;
        }
        self.automorphism_from_data(linear, vec![S::zero(); self.dim()])
    }

    /// Standard momentum shear `x -> x`, `d -> d + A x` for symmetric `A`.
    pub fn shear_automorphism(&self, shear: &[Vec<S>]) -> Result<WeylAutomorphism<S>, WeylError> {
        let pairs = self.standard_pairs.ok_or(WeylError::RequiresStandard)?;
        if shear.len() != pairs {
            return Err(WeylError::ShearRowCountMismatch {
                expected: pairs,
                actual: shear.len(),
            });
        }
        for (row, entries) in shear.iter().enumerate() {
            if entries.len() != pairs {
                return Err(WeylError::ShearDimensionMismatch {
                    row,
                    expected: pairs,
                    actual: entries.len(),
                });
            }
            for column in 0..row {
                if entries[column] != shear[column][row] {
                    return Err(WeylError::ShearNotSymmetric {
                        left: row,
                        right: column,
                    });
                }
            }
        }
        let mut linear = identity_matrix::<S>(self.dim());
        for differential in 0..pairs {
            for position in 0..pairs {
                linear[position][pairs + differential] = shear[differential][position].clone();
            }
        }
        self.automorphism_from_data(linear, vec![S::zero(); self.dim()])
    }

    /// Translate every standard generator by a scalar constant.
    pub fn translation_automorphism(
        &self,
        translation: &[S],
    ) -> Result<WeylAutomorphism<S>, WeylError> {
        self.standard_pairs.ok_or(WeylError::RequiresStandard)?;
        if translation.len() != self.dim() {
            return Err(WeylError::TranslationDimensionMismatch {
                expected: self.dim(),
                actual: translation.len(),
            });
        }
        self.automorphism_from_data(identity_matrix::<S>(self.dim()), translation.to_vec())
    }

    /// Parity automorphism `z_i -> -z_i`.
    pub fn parity_automorphism(&self) -> Result<WeylAutomorphism<S>, WeylError> {
        self.standard_pairs.ok_or(WeylError::RequiresStandard)?;
        let mut linear = vec![vec![S::zero(); self.dim()]; self.dim()];
        for (index, row) in linear.iter_mut().enumerate() {
            row[index] = S::one().neg();
        }
        self.automorphism_from_data(linear, vec![S::zero(); self.dim()])
    }

    /// Formal adjoint anti-automorphism `x_i^* = x_i`, `d_i^* = -d_i`.
    pub fn formal_adjoint(&self) -> Result<WeylAntiAutomorphism<S>, WeylError> {
        let pairs = self.standard_pairs.ok_or(WeylError::RequiresStandard)?;
        let mut linear = identity_matrix::<S>(self.dim());
        for pair in 0..pairs {
            linear[pairs + pair][pairs + pair] = S::one().neg();
        }
        WeylAntiAutomorphism::try_new(self.clone(), linear, vec![S::zero(); self.dim()])
    }

    fn automorphism_from_data(
        &self,
        linear: Vec<Vec<S>>,
        translation: Vec<S>,
    ) -> Result<WeylAutomorphism<S>, WeylError> {
        WeylAutomorphism::try_from_homomorphism(WeylHomomorphism::try_new(
            self.clone(),
            self.clone(),
            linear,
            translation,
        )?)
    }
}

fn validate_shape<S: Scalar>(
    source: &WeylAlgebra<S>,
    target: &WeylAlgebra<S>,
    linear: &[Vec<S>],
    translation: &[S],
) -> Result<(), WeylError> {
    if linear.len() != target.dim() {
        return Err(WeylError::LinearMapRowMismatch {
            expected: target.dim(),
            actual: linear.len(),
        });
    }
    for (row, entries) in linear.iter().enumerate() {
        if entries.len() != source.dim() {
            return Err(WeylError::LinearMapColumnMismatch {
                row,
                expected: source.dim(),
                actual: entries.len(),
            });
        }
    }
    if translation.len() != source.dim() {
        return Err(WeylError::TranslationDimensionMismatch {
            expected: source.dim(),
            actual: translation.len(),
        });
    }
    Ok(())
}

fn linear_commutator<S: Scalar>(
    target: &WeylAlgebra<S>,
    linear: &[Vec<S>],
    left: usize,
    right: usize,
) -> S {
    let mut commutator = S::zero();
    for target_left in 0..target.dim() {
        if linear[target_left][left].is_zero() {
            continue;
        }
        for target_right in 0..target.dim() {
            let omega = &target.commutator[target_left][target_right];
            if linear[target_right][right].is_zero() || omega.is_zero() {
                continue;
            }
            commutator = commutator.add(
                &linear[target_left][left]
                    .mul(&linear[target_right][right])
                    .mul(omega),
            );
        }
    }
    commutator
}

fn affine_images<S: Scalar>(
    target: &WeylAlgebra<S>,
    linear: &[Vec<S>],
    translation: &[S],
) -> Vec<WeylElement<S>> {
    (0..translation.len())
        .map(|source| {
            let mut image = target.scalar(translation[source].clone());
            for target_index in 0..target.dim() {
                if linear[target_index][source].is_zero() {
                    continue;
                }
                image = image
                    + target
                        .scalar_mul(
                            &linear[target_index][source],
                            &target.generator(target_index),
                        )
                        .expect("target generator has the target dimension");
            }
            image
        })
        .collect()
}

fn apply_affine_images<S: Scalar>(
    source: &WeylAlgebra<S>,
    target: &WeylAlgebra<S>,
    images: &[WeylElement<S>],
    element: &WeylElement<S>,
    reverse: bool,
    budget: WeylExpansionBudget,
) -> Result<WeylElement<S>, WeylError> {
    source.validate_element(element)?;
    let mut tracker = ExpansionTracker::new(budget);
    let mut output = BTreeMap::new();
    for (monomial, coefficient) in &element.terms {
        tracker.charge(1)?;
        let mut image = target.scalar(coefficient.clone());
        if reverse {
            for generator in (0..source.dim()).rev() {
                multiply_image_power(
                    target,
                    &mut image,
                    &images[generator],
                    monomial.exponents()[generator],
                    &mut tracker,
                )?;
            }
        } else {
            for generator in 0..source.dim() {
                multiply_image_power(
                    target,
                    &mut image,
                    &images[generator],
                    monomial.exponents()[generator],
                    &mut tracker,
                )?;
            }
        }
        for (image_monomial, image_coefficient) in image.terms {
            tracker.charge(1)?;
            add_term(&mut output, image_monomial, image_coefficient);
            tracker.ensure_terms(output.len())?;
        }
    }
    Ok(WeylElement {
        dim: target.dim(),
        terms: output,
    })
}

fn multiply_image_power<S: Scalar>(
    target: &WeylAlgebra<S>,
    accumulator: &mut WeylElement<S>,
    image: &WeylElement<S>,
    mut exponent: u128,
    tracker: &mut ExpansionTracker,
) -> Result<(), WeylError> {
    if exponent == 0 {
        return Ok(());
    }
    let power = target.pow_with_tracker(image, &mut exponent, tracker)?;
    *accumulator = super::product::multiply(target, accumulator, &power, tracker)?;
    Ok(())
}

fn identity_matrix<S: Scalar>(dim: usize) -> Vec<Vec<S>> {
    (0..dim)
        .map(|row| {
            (0..dim)
                .map(|column| if row == column { S::one() } else { S::zero() })
                .collect()
        })
        .collect()
}

fn matrix_mul<S: Scalar>(left: &[Vec<S>], right: &[Vec<S>]) -> Vec<Vec<S>> {
    let rows = left.len();
    let inner = right.len();
    let columns = right.first().map_or(0, Vec::len);
    let mut product = vec![vec![S::zero(); columns]; rows];
    for row in 0..rows {
        for column in 0..columns {
            product[row][column] = (0..inner).fold(S::zero(), |sum, index| {
                sum.add(&left[row][index].mul(&right[index][column]))
            });
        }
    }
    product
}
