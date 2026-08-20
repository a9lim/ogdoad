//! **Symplectic (alternating) forms** — the skew member of the "form + involution"
//! family, completing it beside the symmetric bilinear forms (the rest of this
//! pillar) and the [`HermitianForm`](crate::forms::HermitianForm).
//!
//! An alternating bilinear form `B(x, x) = 0` (equivalently `Bᵀ = −B` *and* zero
//! diagonal — the diagonal condition is the genuine constraint in characteristic
//! 2, where `−B = B`) has the simplest classification in all of form theory: over
//! **any** field it is congruent to an orthogonal sum of hyperbolic planes and a
//! zero radical,
//!
//! ```text
//! B  ≅  (rank/2) · H  ⟂  0^{radical}
//! ```
//!
//! so the complete invariant is just `(rank, radical_dim)` with `rank` always even
//! — there is no characteristic trichotomy to dispatch (unlike the symmetric and
//! Hermitian cases), so this is a single generic routine. The radical is the
//! kernel `{x : Bx = 0}` (left and right kernels coincide for an alternating form).
//! Classification returns `None` over ring backends when the shared unit-pivot
//! solver encounters a nonunit pivot.

use crate::scalar::{ExactFieldScalar, Scalar};
use std::fmt;

/// A symplectic (alternating) form, carried by its alternating Gram matrix.
#[derive(Debug, Clone, PartialEq)]
pub struct SymplecticForm<S: Scalar> {
    gram: Vec<Vec<S>>,
}

/// The complete invariant of an alternating form: its rank (always even, twice the
/// number of hyperbolic planes) and the dimension of its radical.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymplecticInvariants {
    /// `2 × (number of hyperbolic planes)` — always even.
    pub rank: usize,
    /// Dimension of the radical (the kernel of the form).
    pub radical_dim: usize,
}

/// A failure to construct or internally certify Darboux coordinates.
///
/// These failures should be unreachable for a valid [`ExactFieldScalar`]
/// backend. They remain explicit so an invalid runtime field parameter or a
/// future elimination regression cannot be mistaken for a mathematical
/// decomposition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DarbouxError {
    /// A nonzero alternating pairing did not have a represented inverse.
    NoninvertiblePairing,
    /// The produced change-of-basis matrix was unexpectedly singular.
    SingularChangeOfBasis,
    /// The returned basis did not reproduce the advertised canonical Gram
    /// matrix.
    CertificateMismatch,
}

impl fmt::Display for DarbouxError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoninvertiblePairing => {
                formatter.write_str("nonzero Darboux pairing is not invertible")
            }
            Self::SingularChangeOfBasis => {
                formatter.write_str("Darboux change-of-basis matrix is singular")
            }
            Self::CertificateMismatch => {
                formatter.write_str("Darboux basis does not reproduce its canonical form")
            }
        }
    }
}

impl std::error::Error for DarbouxError {}

/// A certified Darboux-plus-radical basis for an alternating form.
///
/// If `P = basis_matrix`, its columns are the new basis vectors in original
/// coordinates, ordered
///
/// ```text
/// p_0,...,p_(r-1), q_0,...,q_(r-1), c_0,...,c_(s-1),
/// ```
///
/// with `B(q_i,p_j) = delta_ij`; the `c_k` span the radical. Consequently
/// `P^T B P = canonical_gram`. `inverse_basis_matrix` is `P^-1`, so its rows
/// recover Darboux coordinates from an original-coordinate column vector.
#[derive(Debug, Clone, PartialEq)]
pub struct DarbouxDecomposition<S: Scalar> {
    planes: usize,
    basis_matrix: Vec<Vec<S>>,
    inverse_basis_matrix: Vec<Vec<S>>,
    radical_basis: Vec<Vec<S>>,
    canonical_gram: Vec<Vec<S>>,
}

impl<S: Scalar> DarbouxDecomposition<S> {
    /// Dimension of the underlying alternating space.
    pub fn dim(&self) -> usize {
        self.basis_matrix.len()
    }

    /// Number of nondegenerate Darboux pairs.
    pub fn planes(&self) -> usize {
        self.planes
    }

    /// Dimension of the radical.
    pub fn radical_dim(&self) -> usize {
        self.radical_basis.len()
    }

    /// Matrix whose columns are the certified Darboux-plus-radical basis in
    /// original coordinates.
    pub fn basis_matrix(&self) -> &[Vec<S>] {
        &self.basis_matrix
    }

    /// Inverse of [`Self::basis_matrix`].
    pub fn inverse_basis_matrix(&self) -> &[Vec<S>] {
        &self.inverse_basis_matrix
    }

    /// Radical basis vectors, each expressed in original coordinates.
    pub fn radical_basis(&self) -> &[Vec<S>] {
        &self.radical_basis
    }

    /// Canonical alternating Gram matrix in Darboux-plus-radical order.
    pub fn canonical_gram(&self) -> &[Vec<S>] {
        &self.canonical_gram
    }

    /// Convert an original-coordinate column vector into Darboux coordinates.
    pub fn to_darboux_coordinates(&self, vector: &[S]) -> Option<Vec<S>> {
        (vector.len() == self.dim()).then(|| matrix_vector_mul(&self.inverse_basis_matrix, vector))
    }

    /// Convert a Darboux-coordinate column vector into original coordinates.
    pub fn from_darboux_coordinates(&self, vector: &[S]) -> Option<Vec<S>> {
        (vector.len() == self.dim()).then(|| matrix_vector_mul(&self.basis_matrix, vector))
    }

    /// Independently check `P^T B P`, `P^-1 P`, and the radical witnesses.
    pub fn verifies(&self, form: &SymplecticForm<S>) -> bool {
        if form.dim() != self.dim()
            || matrix_mul(&self.inverse_basis_matrix, &self.basis_matrix)
                != identity_matrix::<S>(self.dim())
            || congruence(form.gram(), &self.basis_matrix) != self.canonical_gram
        {
            return false;
        }
        self.radical_basis.iter().all(|vector| {
            matrix_vector_mul(form.gram(), vector)
                .iter()
                .all(Scalar::is_zero)
        })
    }
}

impl SymplecticInvariants {
    /// The number of hyperbolic planes in the canonical decomposition.
    pub fn planes(&self) -> usize {
        self.rank / 2
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for SymplecticInvariants {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "SymplecticInvariants(rank={}, radical_dim={}, planes={})",
            self.rank,
            self.radical_dim,
            self.planes()
        )
    }
}

impl<S: Scalar> SymplecticForm<S> {
    /// Build from a Gram matrix, checking it is square and **alternating**: zero
    /// diagonal and `A[i][j] = −A[j][i]`. Returns `None` otherwise. (In char 2 the
    /// off-diagonal condition reads as symmetry, so the explicit zero-diagonal
    /// check is what distinguishes alternating from merely symmetric there.)
    pub fn from_gram(gram: Vec<Vec<S>>) -> Option<Self> {
        let n = gram.len();
        for row in &gram {
            if row.len() != n {
                return None;
            }
        }
        for i in 0..n {
            if !gram[i][i].is_zero() {
                return None;
            }
            for j in (i + 1)..n {
                if gram[i][j] != gram[j][i].neg() {
                    return None;
                }
            }
        }
        Some(SymplecticForm { gram })
    }

    /// The standard symplectic form `r · H` on `2r` generators: the block-diagonal
    /// sum of `r` hyperbolic planes `[[0, 1], [−1, 0]]`.
    pub fn hyperbolic(r: usize) -> Self {
        let n = 2 * r;
        let mut gram = vec![vec![S::zero(); n]; n];
        for k in 0..r {
            gram[2 * k][2 * k + 1] = S::one();
            gram[2 * k + 1][2 * k] = S::one().neg();
        }
        SymplecticForm { gram }
    }

    /// Dimension of the form.
    pub fn dim(&self) -> usize {
        self.gram.len()
    }

    /// Alternating Gram matrix.
    pub fn gram(&self) -> &[Vec<S>] {
        &self.gram
    }

    /// The orthogonal direct sum (block-diagonal Gram).
    pub fn direct_sum(&self, other: &SymplecticForm<S>) -> SymplecticForm<S> {
        let (n, m) = (self.dim(), other.dim());
        let mut gram = vec![vec![S::zero(); n + m]; n + m];
        for i in 0..n {
            for j in 0..n {
                gram[i][j] = self.gram[i][j].clone();
            }
        }
        for i in 0..m {
            for j in 0..m {
                gram[n + i][n + j] = other.gram[i][j].clone();
            }
        }
        SymplecticForm { gram }
    }

    /// Classify the form: `(rank, radical_dim)`, the complete invariant over
    /// fields. The radical is the nullspace of the Gram; the rank is
    /// `dim − radical_dim` and is always even. Returns `None` when unit-pivot
    /// elimination cannot decide the kernel over a non-field scalar ring.
    pub fn classify(&self) -> Option<SymplecticInvariants> {
        let n = self.dim();
        let radical_dim = crate::linalg::field::unit_pivot_nullspace(self.gram.clone(), n)?.len();
        Some(SymplecticInvariants {
            rank: n - radical_dim,
            radical_dim,
        })
    }
}

impl<S: ExactFieldScalar> SymplecticForm<S> {
    /// Construct and certify a Darboux basis, its inverse change of basis, and
    /// a basis of the radical.
    ///
    /// This is field-gated because the reduction normalizes every nonzero
    /// pairing. The generic [`Self::classify`] method remains available over
    /// rings when unit-pivot elimination happens to suffice, but it does not
    /// promise coordinate witnesses there.
    pub fn darboux_decomposition(&self) -> Result<DarbouxDecomposition<S>, DarbouxError> {
        let dim = self.dim();
        let mut active = identity_columns::<S>(dim);
        let mut positions = Vec::new();
        let mut momenta = Vec::new();

        loop {
            let pair = (0..active.len()).find_map(|left| {
                ((left + 1)..active.len())
                    .find(|&right| !pairing(&self.gram, &active[right], &active[left]).is_zero())
                    .map(|right| (left, right))
            });
            let Some((left, right)) = pair else {
                break;
            };

            // Remove the larger index first so `left` remains valid.
            let paired = active.remove(right);
            let position = active.remove(left);
            let normalization = pairing(&self.gram, &paired, &position)
                .inv()
                .ok_or(DarbouxError::NoninvertiblePairing)?;
            let momentum = vector_scale(&paired, &normalization);

            // For B(q,p)=1 and B(p,q)=-1,
            // v -> v + B(v,q)p - B(v,p)q kills both pairings.
            for vector in &mut active {
                let with_momentum = pairing(&self.gram, vector, &momentum);
                let with_position = pairing(&self.gram, vector, &position);
                *vector = vector_add_scaled(vector, &position, &with_momentum);
                *vector = vector_add_scaled(vector, &momentum, &with_position.neg());
            }
            positions.push(position);
            momenta.push(momentum);
        }

        let radical_basis = active;
        let planes = positions.len();
        let columns: Vec<Vec<S>> = positions
            .into_iter()
            .chain(momenta)
            .chain(radical_basis.iter().cloned())
            .collect();
        let basis_matrix = matrix_from_columns(&columns, dim);
        let inverse_basis_matrix = crate::linalg::field::inverse_matrix(basis_matrix.clone())
            .ok_or(DarbouxError::SingularChangeOfBasis)?;
        let canonical_gram = darboux_gram::<S>(planes, radical_basis.len());
        let decomposition = DarbouxDecomposition {
            planes,
            basis_matrix,
            inverse_basis_matrix,
            radical_basis,
            canonical_gram,
        };
        if !decomposition.verifies(self) {
            return Err(DarbouxError::CertificateMismatch);
        }
        Ok(decomposition)
    }
}

fn identity_columns<S: Scalar>(dim: usize) -> Vec<Vec<S>> {
    (0..dim)
        .map(|column| {
            (0..dim)
                .map(|row| if row == column { S::one() } else { S::zero() })
                .collect()
        })
        .collect()
}

fn identity_matrix<S: Scalar>(dim: usize) -> Vec<Vec<S>> {
    identity_columns::<S>(dim)
}

fn matrix_from_columns<S: Scalar>(columns: &[Vec<S>], dim: usize) -> Vec<Vec<S>> {
    (0..dim)
        .map(|row| columns.iter().map(|column| column[row].clone()).collect())
        .collect()
}

fn vector_scale<S: Scalar>(vector: &[S], scalar: &S) -> Vec<S> {
    vector.iter().map(|entry| entry.mul(scalar)).collect()
}

fn vector_add_scaled<S: Scalar>(vector: &[S], addend: &[S], scalar: &S) -> Vec<S> {
    vector
        .iter()
        .zip(addend)
        .map(|(entry, direction)| entry.add(&direction.mul(scalar)))
        .collect()
}

fn matrix_vector_mul<S: Scalar>(matrix: &[Vec<S>], vector: &[S]) -> Vec<S> {
    matrix
        .iter()
        .map(|row| {
            row.iter()
                .zip(vector)
                .fold(S::zero(), |sum, (entry, coordinate)| {
                    sum.add(&entry.mul(coordinate))
                })
        })
        .collect()
}

fn matrix_mul<S: Scalar>(left: &[Vec<S>], right: &[Vec<S>]) -> Vec<Vec<S>> {
    let rows = left.len();
    let inner = right.len();
    let cols = right.first().map_or(0, Vec::len);
    let mut product = vec![vec![S::zero(); cols]; rows];
    for row in 0..rows {
        for col in 0..cols {
            product[row][col] = (0..inner).fold(S::zero(), |sum, index| {
                sum.add(&left[row][index].mul(&right[index][col]))
            });
        }
    }
    product
}

fn congruence<S: Scalar>(gram: &[Vec<S>], basis: &[Vec<S>]) -> Vec<Vec<S>> {
    let gram_basis = matrix_mul(gram, basis);
    let transpose: Vec<Vec<S>> = (0..basis.len())
        .map(|row| basis.iter().map(|column| column[row].clone()).collect())
        .collect();
    matrix_mul(&transpose, &gram_basis)
}

fn pairing<S: Scalar>(gram: &[Vec<S>], left: &[S], right: &[S]) -> S {
    let gram_right = matrix_vector_mul(gram, right);
    left.iter()
        .zip(&gram_right)
        .fold(S::zero(), |sum, (entry, paired)| {
            sum.add(&entry.mul(paired))
        })
}

fn darboux_gram<S: Scalar>(planes: usize, radical_dim: usize) -> Vec<Vec<S>> {
    let dim = planes
        .checked_mul(2)
        .and_then(|paired| paired.checked_add(radical_dim))
        .expect("Darboux dimension was already represented by an input matrix");
    let mut gram = vec![vec![S::zero(); dim]; dim];
    for pair in 0..planes {
        gram[pair][planes + pair] = S::one().neg();
        gram[planes + pair][pair] = S::one();
    }
    gram
}

/// Classify an alternating Gram matrix directly, or `None` if it is not square and
/// alternating. Convenience over [`SymplecticForm::from_gram`] + `classify`.
pub fn classify_symplectic<S: Scalar>(gram: Vec<Vec<S>>) -> Option<SymplecticInvariants> {
    SymplecticForm::from_gram(gram)?.classify()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{Nimber, Rational};

    fn r(n: i128) -> Rational {
        Rational::from_int(n)
    }

    #[test]
    fn hyperbolic_plane_has_rank_two() {
        let h = SymplecticForm::<Rational>::hyperbolic(1);
        assert_eq!(
            h.classify().unwrap(),
            SymplecticInvariants {
                rank: 2,
                radical_dim: 0
            }
        );
        assert_eq!(h.classify().unwrap().planes(), 1);
    }

    #[test]
    fn rank_is_always_even_and_radical_splits_off() {
        // 2 planes ⟂ a 1-dim radical: rank 4, radical 1.
        let f = SymplecticForm::<Rational>::hyperbolic(2).direct_sum(
            &SymplecticForm::from_gram(vec![vec![r(0)]]).unwrap(), // the zero form on 1 gen
        );
        let c = f.classify().unwrap();
        assert_eq!((c.rank, c.radical_dim), (4, 1));
        assert_eq!(c.rank % 2, 0);
    }

    #[test]
    fn non_alternating_is_rejected() {
        // nonzero diagonal: not alternating.
        assert!(SymplecticForm::from_gram(vec![vec![r(1), r(0)], vec![r(0), r(0)]]).is_none());
        // symmetric off-diagonal over char 0: not alternating (A[0][1] ≠ −A[1][0]).
        assert!(SymplecticForm::from_gram(vec![vec![r(0), r(1)], vec![r(1), r(0)]]).is_none());
    }

    #[test]
    fn char_two_alternating_is_symmetric_with_zero_diagonal() {
        // Over a nim-field, −1 = 1, so an alternating form is a symmetric matrix
        // with zero diagonal. [[0,1],[1,0]] is a hyperbolic plane.
        let h =
            SymplecticForm::from_gram(vec![vec![Nimber(0), Nimber(1)], vec![Nimber(1), Nimber(0)]])
                .unwrap();
        assert_eq!(
            h.classify().unwrap(),
            SymplecticInvariants {
                rank: 2,
                radical_dim: 0
            }
        );
        // but a nonzero diagonal is still rejected (alternating ⊋ symmetric).
        assert!(SymplecticForm::from_gram(vec![
            vec![Nimber(1), Nimber(1)],
            vec![Nimber(1), Nimber(0)],
        ])
        .is_none());
    }

    #[test]
    fn degenerate_form_is_all_radical() {
        // the zero form on 3 generators: rank 0, radical 3.
        let z = SymplecticForm::<Rational>::from_gram(vec![vec![r(0); 3]; 3]).unwrap();
        assert_eq!(
            z.classify().unwrap(),
            SymplecticInvariants {
                rank: 0,
                radical_dim: 3
            }
        );
    }

    #[test]
    fn free_function_matches_method() {
        let g = SymplecticForm::<Rational>::hyperbolic(3);
        assert_eq!(classify_symplectic(g.gram().to_vec()), g.classify());
    }

    #[test]
    fn nonfield_nonunit_pivot_is_refused() {
        use crate::scalar::Integer;

        let gram = vec![vec![Integer(0), Integer(2)], vec![Integer(-2), Integer(0)]];
        let f = SymplecticForm::from_gram(gram).unwrap();
        assert_eq!(f.classify(), None);
    }

    #[test]
    fn darboux_decomposition_certifies_basis_inverse_and_radical() {
        let form = SymplecticForm::from_gram(vec![
            vec![r(0), r(2), r(3)],
            vec![r(-2), r(0), r(5)],
            vec![r(-3), r(-5), r(0)],
        ])
        .unwrap();
        let decomposition = form.darboux_decomposition().unwrap();
        assert_eq!(decomposition.planes(), 1);
        assert_eq!(decomposition.radical_dim(), 1);
        assert!(decomposition.verifies(&form));

        let vector = vec![r(7), r(-2), r(11)];
        let coordinates = decomposition.to_darboux_coordinates(&vector).unwrap();
        assert_eq!(
            decomposition
                .from_darboux_coordinates(&coordinates)
                .unwrap(),
            vector
        );
        let radical = &decomposition.radical_basis()[0];
        assert!(matrix_vector_mul(form.gram(), radical)
            .iter()
            .all(Scalar::is_zero));
    }

    #[test]
    fn darboux_decomposition_is_characteristic_two_faithful() {
        let form = SymplecticForm::from_gram(vec![
            vec![Nimber(0), Nimber(1), Nimber(1)],
            vec![Nimber(1), Nimber(0), Nimber(0)],
            vec![Nimber(1), Nimber(0), Nimber(0)],
        ])
        .unwrap();
        let decomposition = form.darboux_decomposition().unwrap();
        assert_eq!(
            (decomposition.planes(), decomposition.radical_dim()),
            (1, 1)
        );
        assert!(decomposition.verifies(&form));
        assert_eq!(
            decomposition.canonical_gram(),
            &[
                vec![Nimber(0), Nimber(1), Nimber(0)],
                vec![Nimber(1), Nimber(0), Nimber(0)],
                vec![Nimber(0), Nimber(0), Nimber(0)],
            ]
        );
    }
}
