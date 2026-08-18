//! Dickson invariants and certified vector-symmetry factorizations in
//! characteristic two.

use super::field::FiniteChar2Field;
use crate::clifford::{CliffordAlgebra, Metric, Multivector};
use crate::linalg::{f2, field};
use crate::scalar::{nim_add, ExactFieldScalar, Nimber, Scalar};
use std::error::Error;
use std::fmt;

/// Failure modes for characteristic-two vector-symmetry factorization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Char2FactorizationError {
    /// The scalar field does not have characteristic two.
    WrongCharacteristic,
    /// The automatic factorizer needs a supported enumerable finite field.
    UnsupportedField,
    /// General ordered-contraction metrics are outside quadratic-form scope.
    GeneralMetric,
    /// The transformation is not a square matrix of the metric dimension.
    DimensionMismatch,
    /// The polar form is singular, so the quadratic space is not regular.
    SingularPolarForm,
    /// The supplied matrix does not preserve the quadratic form.
    NotIsometry,
    /// A supplied factor has zero quadratic value and cannot define a symmetry.
    IsotropicFactor,
    /// Wall-form elimination could not construct a vector-symmetry basis.
    /// This includes the non-generated coset in the exceptional split
    /// four-space over `F_2`.
    FactorizationFailed,
    /// The factors did not recompose to the supplied matrix.
    ProductMismatch,
    /// Factor parity disagreed with the matrix Dickson invariant.
    DicksonMismatch,
}

impl fmt::Display for Char2FactorizationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            Self::WrongCharacteristic => "the scalar field must have characteristic two",
            Self::UnsupportedField => {
                "automatic factorization needs a supported enumerable characteristic-two field"
            }
            Self::GeneralMetric => "ordered-contraction metrics are not quadratic forms",
            Self::DimensionMismatch => {
                "the transformation must be a square matrix of the metric dimension"
            }
            Self::SingularPolarForm => "the quadratic form must have nonsingular polar form",
            Self::NotIsometry => "the matrix does not preserve the quadratic form",
            Self::IsotropicFactor => "every vector-symmetry factor must be anisotropic",
            Self::FactorizationFailed => "Wall-form elimination did not produce a factorization",
            Self::ProductMismatch => "the vector symmetries do not recompose to the matrix",
            Self::DicksonMismatch => "factor parity does not equal the Dickson invariant",
        };
        f.write_str(message)
    }
}

impl Error for Char2FactorizationError {}

/// An exact certificate that a regular characteristic-two isometry is a
/// product of vector symmetries.
///
/// The fields are private: instances can only be constructed after exact
/// isometry, recomposition, and Dickson-parity checks. Matrices act on column
/// vectors, and the listed factors multiply from left to right.
#[derive(Clone, Debug, PartialEq)]
pub struct Char2SymmetryFactorization<S: ExactFieldScalar + Copy> {
    metric: Metric<S>,
    matrix: Vec<Vec<S>>,
    factors: Vec<Vec<S>>,
}

impl<S: ExactFieldScalar + Copy> Char2SymmetryFactorization<S> {
    /// The quadratic metric certified by this factorization.
    pub fn metric(&self) -> &Metric<S> {
        &self.metric
    }

    /// The certified isometry, as a row-major matrix acting on columns.
    pub fn matrix(&self) -> &[Vec<S>] {
        &self.matrix
    }

    /// Anisotropic roots of the vector symmetries, in multiplication order.
    pub fn factors(&self) -> &[Vec<S>] {
        &self.factors
    }

    /// Number of vector-symmetry factors.
    pub fn factor_count(&self) -> usize {
        self.factors.len()
    }

    /// Dickson invariant, equal to both `rank(I + g) mod 2` and factor parity.
    pub fn dickson(&self) -> u128 {
        (self.factors.len() % 2) as u128
    }

    /// The product of the factor vectors in the corresponding Clifford algebra.
    pub fn versor(&self) -> Multivector<S> {
        let alg = CliffordAlgebra::new(self.metric.dim(), self.metric.clone());
        self.factors.iter().fold(alg.scalar(S::one()), |acc, root| {
            alg.mul(&acc, &vector_multivector(&alg, root))
        })
    }

    /// Whether the certificate's Clifford versor has the certified grade parity
    /// and its twisted adjoint agrees with the matrix on every basis vector.
    pub fn verifies_clifford_action(&self) -> bool {
        let alg = CliffordAlgebra::new(self.metric.dim(), self.metric.clone());
        let versor = self.versor();
        if crate::clifford::versor_grade_parity(&versor) != Some(self.dickson()) {
            return false;
        }
        (0..self.metric.dim()).all(|j| {
            alg.twisted_sandwich(&versor, &alg.e(j))
                == Some(vector_multivector(
                    &alg,
                    &(0..self.metric.dim())
                        .map(|i| self.matrix[i][j])
                        .collect::<Vec<_>>(),
                ))
        })
    }

    /// Returns the canonical compact display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl<S: ExactFieldScalar + Copy> fmt::Display for Char2SymmetryFactorization<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Char2SymmetryFactorization(dim={}, factor_count={}, dickson={})",
            self.metric.dim(),
            self.factor_count(),
            self.dickson()
        )
    }
}

fn identity<S: Scalar + Copy>(n: usize) -> Vec<Vec<S>> {
    (0..n)
        .map(|i| {
            (0..n)
                .map(|j| if i == j { S::one() } else { S::zero() })
                .collect()
        })
        .collect()
}

fn matrix_shape<S>(matrix: &[Vec<S>], n: usize) -> bool {
    matrix.len() == n && matrix.iter().all(|row| row.len() == n)
}

fn matrix_mul<S: Scalar + Copy>(left: &[Vec<S>], right: &[Vec<S>]) -> Vec<Vec<S>> {
    let n = left.len();
    (0..n)
        .map(|i| {
            (0..n)
                .map(|j| (0..n).fold(S::zero(), |acc, k| acc.add(&left[i][k].mul(&right[k][j]))))
                .collect()
        })
        .collect()
}

fn add_vectors<S: Scalar + Copy>(left: &[S], right: &[S]) -> Vec<S> {
    left.iter().zip(right).map(|(a, b)| a.add(b)).collect()
}

fn scale_add_vectors<S: Scalar + Copy>(left: &[S], scalar: &S, right: &[S]) -> Vec<S> {
    left.iter()
        .zip(right)
        .map(|(a, b)| a.add(&scalar.mul(b)))
        .collect()
}

fn polar_matrix<S: Scalar + Copy>(metric: &Metric<S>) -> Vec<Vec<S>> {
    let n = metric.dim();
    let mut polar = vec![vec![S::zero(); n]; n];
    for (&(i, j), value) in metric.b() {
        polar[i][j] = *value;
        polar[j][i] = *value;
    }
    polar
}

fn bilinear<S: Scalar + Copy>(polar: &[Vec<S>], left: &[S], right: &[S]) -> S {
    left.iter().enumerate().fold(S::zero(), |outer, (i, a)| {
        let row = right
            .iter()
            .enumerate()
            .fold(S::zero(), |inner, (j, b)| inner.add(&polar[i][j].mul(b)));
        outer.add(&a.mul(&row))
    })
}

fn quadratic<S: Scalar + Copy>(metric: &Metric<S>, vector: &[S]) -> S {
    let diagonal = metric
        .q()
        .iter()
        .zip(vector)
        .fold(S::zero(), |acc, (q, x)| acc.add(&q.mul(&x.mul(x))));
    metric.b().iter().fold(diagonal, |acc, (&(i, j), b)| {
        acc.add(&b.mul(&vector[i].mul(&vector[j])))
    })
}

fn vector_symmetry_unchecked<S: Scalar + Copy>(
    metric: &Metric<S>,
    polar: &[Vec<S>],
    root: &[S],
) -> Option<Vec<Vec<S>>> {
    let n = metric.dim();
    let qinv = quadratic(metric, root).inv()?;
    let mut symmetry = identity::<S>(n);
    for j in 0..n {
        let mut ej = vec![S::zero(); n];
        ej[j] = S::one();
        let coefficient = bilinear(polar, &ej, root).mul(&qinv);
        for i in 0..n {
            symmetry[i][j] = symmetry[i][j].add(&root[i].mul(&coefficient));
        }
    }
    Some(symmetry)
}

/// Matrix of the vector symmetry `x ↦ x + B(x,v)Q(v)⁻¹v`.
pub fn char2_vector_symmetry<S: ExactFieldScalar + Copy>(
    metric: &Metric<S>,
    root: &[S],
) -> Result<Vec<Vec<S>>, Char2FactorizationError> {
    if S::characteristic() != 2 {
        return Err(Char2FactorizationError::WrongCharacteristic);
    }
    if metric.has_upper() {
        return Err(Char2FactorizationError::GeneralMetric);
    }
    if root.len() != metric.dim() {
        return Err(Char2FactorizationError::DimensionMismatch);
    }
    vector_symmetry_unchecked(metric, &polar_matrix(metric), root)
        .ok_or(Char2FactorizationError::IsotropicFactor)
}

fn is_isometry<S: Scalar + Copy>(metric: &Metric<S>, polar: &[Vec<S>], matrix: &[Vec<S>]) -> bool {
    let n = metric.dim();
    let columns: Vec<Vec<S>> = (0..n)
        .map(|j| (0..n).map(|i| matrix[i][j]).collect())
        .collect();
    if (0..n).any(|j| quadratic(metric, &columns[j]) != metric.q()[j]) {
        return false;
    }
    (0..n).all(|i| (0..n).all(|j| bilinear(polar, &columns[i], &columns[j]) == polar[i][j]))
}

fn residual_matrix<S: Scalar + Copy>(matrix: &[Vec<S>]) -> Vec<Vec<S>> {
    let mut residual = matrix.to_vec();
    for (i, row) in residual.iter_mut().enumerate() {
        row[i] = row[i].add(&S::one());
    }
    residual
}

fn columns_as_rows<S: Scalar + Copy>(columns: &[Vec<S>], nrows: usize) -> Vec<Vec<S>> {
    (0..nrows)
        .map(|i| columns.iter().map(|column| column[i]).collect())
        .collect()
}

fn residual_basis<S: Scalar + Copy>(residual: &[Vec<S>]) -> Option<(Vec<Vec<S>>, Vec<usize>)> {
    let n = residual.len();
    let mut columns: Vec<Vec<S>> = Vec::new();
    let mut preimages = Vec::new();
    let mut rank = 0;
    for j in 0..n {
        let column: Vec<S> = (0..n).map(|i| residual[i][j]).collect();
        let mut candidate = columns.clone();
        candidate.push(column.clone());
        let candidate_rank = field::unit_pivot_rank(columns_as_rows(&candidate, n))?;
        if candidate_rank > rank {
            columns.push(column);
            preimages.push(j);
            rank = candidate_rank;
        }
    }
    Some((columns, preimages))
}

fn coordinate_bilinear<S: Scalar + Copy>(gram: &[Vec<S>], left: &[S], right: &[S]) -> S {
    left.iter().enumerate().fold(S::zero(), |outer, (i, a)| {
        let row = right
            .iter()
            .enumerate()
            .fold(S::zero(), |inner, (j, b)| inner.add(&gram[i][j].mul(b)));
        outer.add(&a.mul(&row))
    })
}

#[derive(Clone)]
struct WallVector<S: Scalar + Copy> {
    ambient: Vec<S>,
    coordinates: Vec<S>,
}

fn continue_semi_orthogonal_basis<S: FiniteChar2Field>(
    gram: &[Vec<S>],
    basis: &[WallVector<S>],
    pivot_index: usize,
    pivot: WallVector<S>,
    clear_first_argument: bool,
) -> Option<Vec<WallVector<S>>> {
    let mut candidate = basis.to_vec();
    candidate[pivot_index] = pivot;
    candidate.swap(0, pivot_index);
    let diagonal = coordinate_bilinear(gram, &candidate[0].coordinates, &candidate[0].coordinates);
    let diagonal_inv = diagonal.inv()?;
    for j in 1..candidate.len() {
        let coefficient = if clear_first_argument {
            coordinate_bilinear(gram, &candidate[0].coordinates, &candidate[j].coordinates)
        } else {
            coordinate_bilinear(gram, &candidate[j].coordinates, &candidate[0].coordinates)
        }
        .mul(&diagonal_inv);
        candidate[j].ambient =
            scale_add_vectors(&candidate[j].ambient, &coefficient, &candidate[0].ambient);
        candidate[j].coordinates = scale_add_vectors(
            &candidate[j].coordinates,
            &coefficient,
            &candidate[0].coordinates,
        );
    }
    let mut rest = semi_orthogonal_basis(gram, &candidate[1..], clear_first_argument)?;
    let mut result = vec![candidate[0].clone()];
    result.append(&mut rest);
    Some(result)
}

fn semi_orthogonal_basis<S: FiniteChar2Field>(
    gram: &[Vec<S>],
    basis: &[WallVector<S>],
    clear_first_argument: bool,
) -> Option<Vec<WallVector<S>>> {
    if basis.is_empty() {
        return Some(Vec::new());
    }
    for i in 0..basis.len() {
        if !coordinate_bilinear(gram, &basis[i].coordinates, &basis[i].coordinates).is_zero() {
            if let Some(result) = continue_semi_orthogonal_basis(
                gram,
                basis,
                i,
                basis[i].clone(),
                clear_first_argument,
            ) {
                return Some(result);
            }
        }
    }
    for i in 0..basis.len() {
        for j in (i + 1)..basis.len() {
            for scalar_index in 1..S::field_order() {
                let scalar = S::from_index(scalar_index);
                let pivot = WallVector {
                    ambient: scale_add_vectors(&basis[i].ambient, &scalar, &basis[j].ambient),
                    coordinates: scale_add_vectors(
                        &basis[i].coordinates,
                        &scalar,
                        &basis[j].coordinates,
                    ),
                };
                if coordinate_bilinear(gram, &pivot.coordinates, &pivot.coordinates).is_zero() {
                    continue;
                }
                if let Some(result) =
                    continue_semi_orthogonal_basis(gram, basis, i, pivot, clear_first_argument)
                {
                    return Some(result);
                }
            }
        }
    }
    // Taylor's F2 repair mixes an anisotropic line with a hyperbolic pair.
    if S::field_order() == 2 {
        for i in 0..basis.len() {
            for j in (i + 1)..basis.len() {
                for k in (j + 1)..basis.len() {
                    let pivot = WallVector {
                        ambient: add_vectors(
                            &add_vectors(&basis[i].ambient, &basis[j].ambient),
                            &basis[k].ambient,
                        ),
                        coordinates: add_vectors(
                            &add_vectors(&basis[i].coordinates, &basis[j].coordinates),
                            &basis[k].coordinates,
                        ),
                    };
                    if coordinate_bilinear(gram, &pivot.coordinates, &pivot.coordinates).is_zero() {
                        continue;
                    }
                    if let Some(result) =
                        continue_semi_orthogonal_basis(gram, basis, i, pivot, clear_first_argument)
                    {
                        return Some(result);
                    }
                }
            }
        }
    }
    None
}

fn factor_nonalternating_wall<S: FiniteChar2Field>(
    polar: &[Vec<S>],
    matrix: &[Vec<S>],
) -> Option<Vec<Vec<S>>> {
    let residual = residual_matrix(matrix);
    let (basis, preimages) = residual_basis(&residual)?;
    let rank = basis.len();
    if rank == 0 {
        return Some(Vec::new());
    }
    let mut gram = vec![vec![S::zero(); rank]; rank];
    for i in 0..rank {
        let mut preimage = vec![S::zero(); polar.len()];
        preimage[preimages[i]] = S::one();
        for j in 0..rank {
            gram[i][j] = bilinear(polar, &preimage, &basis[j]);
        }
    }
    let wall_basis: Vec<WallVector<S>> = basis
        .into_iter()
        .enumerate()
        .map(|(i, ambient)| WallVector {
            ambient,
            coordinates: (0..rank)
                .map(|j| if i == j { S::one() } else { S::zero() })
                .collect(),
        })
        .collect();
    semi_orthogonal_basis(&gram, &wall_basis, true)
        .or_else(|| semi_orthogonal_basis(&gram, &wall_basis, false))
        .map(|vectors| vectors.into_iter().map(|vector| vector.ambient).collect())
}

fn with_anisotropic_coordinate_vector<S: FiniteChar2Field, T>(
    metric: &Metric<S>,
    mut visit: impl FnMut(Vec<S>) -> Option<T>,
) -> Option<T> {
    let n = metric.dim();
    for i in 0..n {
        let mut vector = vec![S::zero(); n];
        vector[i] = S::one();
        if !quadratic(metric, &vector).is_zero() {
            if let Some(result) = visit(vector) {
                return Some(result);
            }
        }
    }
    for i in 0..n {
        for j in (i + 1)..n {
            for scalar_index in 1..S::field_order() {
                let mut vector = vec![S::zero(); n];
                vector[i] = S::one();
                vector[j] = S::from_index(scalar_index);
                if !quadratic(metric, &vector).is_zero() {
                    if let Some(result) = visit(vector) {
                        return Some(result);
                    }
                }
            }
        }
    }
    None
}

fn product_of_symmetries<S: ExactFieldScalar + Copy>(
    metric: &Metric<S>,
    factors: &[Vec<S>],
) -> Result<Vec<Vec<S>>, Char2FactorizationError> {
    let polar = polar_matrix(metric);
    factors
        .iter()
        .try_fold(identity(metric.dim()), |product, root| {
            if root.len() != metric.dim() {
                return Err(Char2FactorizationError::DimensionMismatch);
            }
            let symmetry = vector_symmetry_unchecked(metric, &polar, root)
                .ok_or(Char2FactorizationError::IsotropicFactor)?;
            Ok(matrix_mul(&product, &symmetry))
        })
}

/// Certify a proposed characteristic-two vector-symmetry factorization.
pub fn certify_char2_symmetry_factorization<S: ExactFieldScalar + Copy>(
    metric: &Metric<S>,
    matrix: &[Vec<S>],
    factors: Vec<Vec<S>>,
) -> Result<Char2SymmetryFactorization<S>, Char2FactorizationError> {
    if S::characteristic() != 2 {
        return Err(Char2FactorizationError::WrongCharacteristic);
    }
    if metric.has_upper() {
        return Err(Char2FactorizationError::GeneralMetric);
    }
    let n = metric.dim();
    if !matrix_shape(matrix, n) {
        return Err(Char2FactorizationError::DimensionMismatch);
    }
    let polar = polar_matrix(metric);
    if field::unit_pivot_rank(polar.clone()) != Some(n) {
        return Err(Char2FactorizationError::SingularPolarForm);
    }
    if !is_isometry(metric, &polar, matrix) {
        return Err(Char2FactorizationError::NotIsometry);
    }
    if product_of_symmetries(metric, &factors)? != matrix {
        return Err(Char2FactorizationError::ProductMismatch);
    }
    let dickson = dickson_matrix_char2(matrix).ok_or(Char2FactorizationError::DimensionMismatch)?;
    if (factors.len() % 2) as u128 != dickson {
        return Err(Char2FactorizationError::DicksonMismatch);
    }
    Ok(Char2SymmetryFactorization {
        metric: metric.clone(),
        matrix: matrix.to_vec(),
        factors,
    })
}

fn certify_with_wall_orders<S: ExactFieldScalar + Copy>(
    metric: &Metric<S>,
    matrix: &[Vec<S>],
    prefix: &[Vec<S>],
    wall_factors: Vec<Vec<S>>,
) -> Option<Char2SymmetryFactorization<S>> {
    for wall_order in [
        wall_factors.clone(),
        wall_factors.into_iter().rev().collect(),
    ] {
        let mut factors = prefix.to_vec();
        factors.extend(wall_order);
        if let Ok(certificate) = certify_char2_symmetry_factorization(metric, matrix, factors) {
            return Some(certificate);
        }
    }
    None
}

/// Factor an isometry of a regular characteristic-two quadratic space into
/// vector symmetries and return an exact certificate.
///
/// Automatic root selection uses [`FiniteChar2Field`]'s finite enumeration.
/// The invariant and certificate checker remain generic through
/// [`char2_spinor_norm`] and [`certify_char2_symmetry_factorization`].
///
/// The algorithm uses Wall's residual space and Wall form. A nonalternating
/// Wall form is semi-orthogonalized directly. In the alternating case, one or
/// two auxiliary anisotropic symmetries convert it to a decomposable
/// nonalternating case; those symmetries remain in the final exact product.
pub fn factor_char2_isometry<S: FiniteChar2Field>(
    metric: &Metric<S>,
    matrix: &[Vec<S>],
) -> Result<Char2SymmetryFactorization<S>, Char2FactorizationError> {
    if !S::is_supported_char2_field() {
        return Err(Char2FactorizationError::UnsupportedField);
    }
    if S::characteristic() != 2 {
        return Err(Char2FactorizationError::WrongCharacteristic);
    }
    if metric.has_upper() {
        return Err(Char2FactorizationError::GeneralMetric);
    }
    let n = metric.dim();
    if !matrix_shape(matrix, n) {
        return Err(Char2FactorizationError::DimensionMismatch);
    }
    let polar = polar_matrix(metric);
    if field::unit_pivot_rank(polar.clone()) != Some(n) {
        return Err(Char2FactorizationError::SingularPolarForm);
    }
    if !is_isometry(metric, &polar, matrix) {
        return Err(Char2FactorizationError::NotIsometry);
    }

    if let Some(factors) = factor_nonalternating_wall(&polar, matrix) {
        if let Some(certificate) = certify_with_wall_orders(metric, matrix, &[], factors) {
            return Ok(certificate);
        }
    }

    if let Some(certificate) = with_anisotropic_coordinate_vector(metric, |auxiliary| {
        let symmetry = vector_symmetry_unchecked(metric, &polar, &auxiliary)
            .expect("visitor receives only anisotropic vectors");
        let modified = matrix_mul(&symmetry, matrix);
        let factors = factor_nonalternating_wall(&polar, &modified)?;
        certify_with_wall_orders(metric, matrix, &[auxiliary], factors)
    }) {
        return Ok(certificate);
    }

    if let Some(certificate) = with_anisotropic_coordinate_vector(metric, |first| {
        let first_symmetry = vector_symmetry_unchecked(metric, &polar, &first)
            .expect("visitor receives only anisotropic vectors");
        with_anisotropic_coordinate_vector(metric, |second| {
            let second_symmetry = vector_symmetry_unchecked(metric, &polar, &second)
                .expect("visitor receives only anisotropic vectors");
            let modified = matrix_mul(&second_symmetry, &matrix_mul(&first_symmetry, matrix));
            let factors = factor_nonalternating_wall(&polar, &modified)?;
            certify_with_wall_orders(metric, matrix, &[first.clone(), second], factors)
        })
    }) {
        return Ok(certificate);
    }
    Err(Char2FactorizationError::FactorizationFailed)
}

/// The Dickson invariant `D(g) = rank(I + g) mod 2` of a square matrix over an
/// exact characteristic-two field.
pub fn dickson_matrix_char2<S: ExactFieldScalar + Copy>(g: &[Vec<S>]) -> Option<u128> {
    let n = g.len();
    if S::characteristic() != 2 || !matrix_shape(g, n) {
        return None;
    }
    field::unit_pivot_rank(residual_matrix(g)).map(|rank| (rank % 2) as u128)
}

/// The additive characteristic-two spinor norm of an isometry, equivalently
/// its Dickson invariant `rank(I + g) mod 2`.
///
/// Unlike [`dickson_matrix_char2`], this entry point verifies that the metric is
/// a regular quadratic form and that `g` is an isometry. The returned bit
/// agrees with the parity of every certified vector-symmetry factorization,
/// including when the factorization is not minimal. It remains defined on the
/// exceptional split four-space over `F_2`, where not every isometry is
/// generated by vector symmetries.
pub fn char2_spinor_norm<S: ExactFieldScalar + Copy>(
    metric: &Metric<S>,
    matrix: &[Vec<S>],
) -> Result<u128, Char2FactorizationError> {
    if S::characteristic() != 2 {
        return Err(Char2FactorizationError::WrongCharacteristic);
    }
    if metric.has_upper() {
        return Err(Char2FactorizationError::GeneralMetric);
    }
    let n = metric.dim();
    if !matrix_shape(matrix, n) {
        return Err(Char2FactorizationError::DimensionMismatch);
    }
    let polar = polar_matrix(metric);
    if field::unit_pivot_rank(polar.clone()) != Some(n) {
        return Err(Char2FactorizationError::SingularPolarForm);
    }
    if !is_isometry(metric, &polar, matrix) {
        return Err(Char2FactorizationError::NotIsometry);
    }
    dickson_matrix_char2(matrix).ok_or(Char2FactorizationError::DimensionMismatch)
}

/// The **Dickson invariant** `D(g) ∈ F₂` of an orthogonal transformation `g`,
/// given as an n×n matrix over a nim-field: `D(g) = dim Im(g − I) mod 2`
/// (`= rank(g + I) mod 2`, since `−1 = 1`).
///
/// In characteristic 2 the determinant of any `g ∈ O(Q)` is forced to `1`, so it
/// cannot separate rotations from reflections — the Dickson invariant is the
/// replacement, with `SO(Q) = ker D`. A single reflection has `D = 1`; a product
/// of `k` reflections has `D = k mod 2`. It is the companion to the Arf
/// invariant: **Arf classifies the form, Dickson classifies `O(Q)`.**
pub fn dickson_matrix(g: &[Vec<u128>]) -> u128 {
    let n = g.len();
    let mut m: Vec<Vec<u128>> = g.to_vec();
    for i in 0..n {
        m[i][i] = nim_add(m[i][i], 1);
    }
    (f2::nim_rank(m) % 2) as u128
}

/// The Dickson invariant of a Clifford **versor** (a product of vectors) acting
/// by the twisted adjoint: it is the ℤ₂-grade parity of the versor — an even
/// versor (rotor) lies in `SO` with `D = 0`, an odd versor (e.g. a single vector,
/// a reflection) has `D = 1`. Returns `None` if the multivector is not of
/// homogeneous grade parity (hence not a versor) or is zero.
pub fn dickson_of_versor(alg: &CliffordAlgebra<Nimber>, v: &Multivector<Nimber>) -> Option<u128> {
    let dickson = crate::clifford::versor_grade_parity(v)?;
    alg.versor_inverse(v)?;
    Some(dickson)
}

fn vector_multivector<S: Scalar + Copy>(
    alg: &CliffordAlgebra<S>,
    coordinates: &[S],
) -> Multivector<S> {
    coordinates
        .iter()
        .enumerate()
        .fold(alg.zero(), |acc, (i, coefficient)| {
            alg.add(&acc, &alg.scalar_mul(coefficient, &alg.e(i)))
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{nim_mul, Fp, Fpn};
    use std::collections::BTreeMap;

    type F2 = Fp<2>;
    type F4 = Fpn<2, 2>;
    type F8 = Fpn<2, 3>;

    fn hyperbolic<S: Scalar + Copy>(planes: usize) -> Metric<S> {
        let mut b = BTreeMap::new();
        for plane in 0..planes {
            b.insert((2 * plane, 2 * plane + 1), S::one());
        }
        Metric::new(vec![S::zero(); 2 * planes], b)
    }

    fn product<S: ExactFieldScalar + Copy>(metric: &Metric<S>, roots: &[Vec<S>]) -> Vec<Vec<S>> {
        product_of_symmetries(metric, roots).unwrap()
    }

    #[test]
    fn dickson_separates_rotations_from_reflections() {
        assert_eq!(dickson_matrix(&[vec![1, 0], vec![0, 1]]), 0);
        assert_eq!(dickson_matrix(&[vec![0, 1], vec![1, 0]]), 1);
        assert_eq!(dickson_matrix(&[vec![2, 0], vec![0, 3]]), 0);
        let swap = [[0u128, 1], [1, 0]];
        let mut comp = vec![vec![0u128; 2]; 2];
        for i in 0..2 {
            for j in 0..2 {
                let mut acc = 0u128;
                for k in 0..2 {
                    acc ^= nim_mul(swap[i][k], swap[k][j]);
                }
                comp[i][j] = acc;
            }
        }
        assert_eq!(dickson_matrix(&comp), 0);
    }

    #[test]
    fn dickson_of_versor_is_grade_parity() {
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![Nimber(1), Nimber(1)]));
        let scalar_one = alg.scalar(Nimber(1));
        let e0 = alg.e(0);
        let e0e1 = alg.mul(&alg.e(0), &alg.e(1));
        assert_eq!(dickson_of_versor(&alg, &scalar_one), Some(0));
        assert_eq!(dickson_of_versor(&alg, &e0), Some(1));
        assert_eq!(dickson_of_versor(&alg, &e0e1), Some(0));
        let mixed = alg.add(&e0, &e0e1);
        assert_eq!(dickson_of_versor(&alg, &mixed), None);

        let null_alg = CliffordAlgebra::new(1, Metric::grassmann(1));
        assert_eq!(dickson_of_versor(&null_alg, &null_alg.e(0)), None);
    }

    #[test]
    fn identity_and_single_symmetry_are_certified_over_f2() {
        let metric = hyperbolic::<F2>(1);
        let identity_certificate = factor_char2_isometry(&metric, &identity(2)).unwrap();
        assert!(identity_certificate.factors().is_empty());
        assert_eq!(identity_certificate.dickson(), 0);
        assert!(identity_certificate.verifies_clifford_action());

        let root = vec![F2::one(), F2::one()];
        let symmetry = char2_vector_symmetry(&metric, &root).unwrap();
        let certificate = factor_char2_isometry(&metric, &symmetry).unwrap();
        assert_eq!(certificate.factor_count(), 1);
        assert_eq!(certificate.dickson(), 1);
        assert!(certificate.verifies_clifford_action());
    }

    #[test]
    fn extension_field_products_recompose_and_match_clifford_parity() {
        let metric4 = hyperbolic::<F4>(1);
        let a = F4::generator();
        let roots4 = vec![vec![F4::one(), F4::one()], vec![a, F4::one()]];
        let target4 = product(&metric4, &roots4);
        let certificate4 = factor_char2_isometry(&metric4, &target4).unwrap();
        assert_eq!(certificate4.matrix(), target4);
        assert_eq!(certificate4.dickson(), 0);
        assert!(certificate4.verifies_clifford_action());

        let metric8 = hyperbolic::<F8>(2);
        let b = F8::generator();
        let roots8 = vec![
            vec![F8::one(), F8::one(), F8::zero(), F8::zero()],
            vec![b, F8::one(), F8::one(), F8::one()],
            vec![F8::one(), b, b, b],
        ];
        let target8 = product(&metric8, &roots8);
        let certificate8 = factor_char2_isometry(&metric8, &target8).unwrap();
        assert_eq!(certificate8.matrix(), target8);
        assert_eq!(certificate8.dickson(), 1);
        assert!(certificate8.verifies_clifford_action());
    }

    #[test]
    fn split_four_space_over_f2_exposes_the_reflection_generation_exception() {
        let metric = hyperbolic::<F2>(2);
        let polar = polar_matrix(&metric);
        let target = (0u128..(1 << 16))
            .map(|bits| {
                (0..4)
                    .map(|i| {
                        (0..4)
                            .map(|j| F2::from_u128((bits >> (4 * i + j)) & 1))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            })
            .find(|matrix| {
                let residual = residual_matrix(matrix);
                let Some((basis, _)) = residual_basis(&residual) else {
                    return false;
                };
                !basis.is_empty()
                    && basis
                        .iter()
                        .all(|vector| quadratic(&metric, vector).is_zero())
                    && is_isometry(&metric, &polar, matrix)
            })
            .expect("O+(4,2) contains a nontrivial alternating-Wall isometry");

        assert!(factor_nonalternating_wall(&polar, &target).is_none());
        assert_eq!(
            factor_char2_isometry(&metric, &target),
            Err(Char2FactorizationError::FactorizationFailed)
        );
        assert_eq!(char2_spinor_norm(&metric, &target), Ok(0));
    }

    #[test]
    fn totally_singular_f4_residual_gets_the_rank_plus_two_factorization() {
        let metric = hyperbolic::<F4>(2);
        let target = vec![
            vec![F4::zero(), F4::zero(), F4::zero(), F4::one()],
            vec![F4::zero(), F4::zero(), F4::one(), F4::zero()],
            vec![F4::zero(), F4::one(), F4::zero(), F4::zero()],
            vec![F4::one(), F4::zero(), F4::zero(), F4::zero()],
        ];
        let residual = residual_matrix(&target);
        let (basis, _) = residual_basis(&residual).unwrap();
        assert_eq!(basis.len(), 2);
        assert!(basis
            .iter()
            .all(|vector| quadratic(&metric, vector).is_zero()));

        let certificate = factor_char2_isometry(&metric, &target).unwrap();
        assert_eq!(certificate.factor_count(), 4);
        assert_eq!(certificate.matrix(), target);
        assert_eq!(certificate.dickson(), 0);
        assert!(certificate.verifies_clifford_action());
    }

    #[test]
    fn every_element_of_the_f2_split_four_symmetry_subgroup_is_certified() {
        use std::collections::BTreeSet;

        let metric = hyperbolic::<F2>(2);
        let roots: Vec<Vec<F2>> = (1u128..16)
            .map(|bits| {
                (0..4)
                    .map(|i| F2::from_u128((bits >> i) & 1))
                    .collect::<Vec<_>>()
            })
            .filter(|root| !quadratic(&metric, root).is_zero())
            .collect();
        let generators: Vec<Vec<Vec<F2>>> = roots
            .iter()
            .map(|root| char2_vector_symmetry(&metric, root).unwrap())
            .collect();
        let key = |matrix: &[Vec<F2>]| {
            matrix
                .iter()
                .flatten()
                .enumerate()
                .fold(0u128, |bits, (i, value)| {
                    bits | ((!value.is_zero()) as u128) << i
                })
        };
        let mut seen = BTreeSet::from([key(&identity::<F2>(4))]);
        let mut subgroup = vec![identity::<F2>(4)];
        let mut cursor = 0;
        while cursor < subgroup.len() {
            let current = subgroup[cursor].clone();
            for generator in &generators {
                let next = matrix_mul(&current, generator);
                if seen.insert(key(&next)) {
                    subgroup.push(next);
                }
            }
            cursor += 1;
        }
        assert_eq!(subgroup.len(), 36);
        for matrix in subgroup {
            let certificate = factor_char2_isometry(&metric, &matrix).unwrap();
            assert_eq!(certificate.matrix(), matrix);
            assert_eq!(
                char2_spinor_norm(&metric, &matrix),
                Ok(certificate.dickson())
            );
            assert!(certificate.verifies_clifford_action());
        }
    }

    #[test]
    fn nimber_factorization_certificates_remain_generic() {
        let metric = hyperbolic::<Nimber>(1);
        let roots = vec![vec![Nimber(1), Nimber(1)], vec![Nimber(2), Nimber(1)]];
        let target = product(&metric, &roots);
        let certificate = certify_char2_symmetry_factorization(&metric, &target, roots).unwrap();
        assert_eq!(certificate.matrix(), target);
        assert!(certificate.verifies_clifford_action());
    }

    #[test]
    fn invalid_inputs_are_rejected_explicitly() {
        let odd = hyperbolic::<Fp<3>>(1);
        assert_eq!(
            char2_spinor_norm(&odd, &identity(2)),
            Err(Char2FactorizationError::WrongCharacteristic)
        );
        let singular = Metric::diagonal(vec![F2::one(), F2::one()]);
        assert_eq!(
            factor_char2_isometry(&singular, &identity(2)),
            Err(Char2FactorizationError::SingularPolarForm)
        );
        let regular = hyperbolic::<F2>(1);
        assert_eq!(
            factor_char2_isometry(&regular, &[vec![F2::one()]]),
            Err(Char2FactorizationError::DimensionMismatch)
        );
        assert_eq!(
            factor_char2_isometry(
                &regular,
                &[vec![F2::one(), F2::one()], vec![F2::zero(), F2::one()]],
            ),
            Err(Char2FactorizationError::NotIsometry)
        );
        assert_eq!(
            char2_vector_symmetry(&regular, &[F2::one(), F2::zero()]),
            Err(Char2FactorizationError::IsotropicFactor)
        );
    }

    #[test]
    fn certificate_constructor_rejects_wrong_products() {
        let metric = hyperbolic::<F2>(1);
        assert_eq!(
            certify_char2_symmetry_factorization(
                &metric,
                &identity(2),
                vec![vec![F2::one(), F2::one()]],
            ),
            Err(Char2FactorizationError::ProductMismatch)
        );
    }
}
