//! **Hermitian forms** — the natural quadratic-form structure over a field
//! carrying an involution, which the rest of the forms pillar
//! (symmetric/bilinear) never used.
//!
//! [`Surcomplex`] carries the conjugation `i ↦ −i` ([`Surcomplex::conj`]); a
//! Hermitian form has a conjugate-symmetric Gram matrix `H* = H` (so the diagonal
//! is real). Over the ideal algebraically-closed complexification of a real-closed
//! base, a nondegenerate Hermitian form is classified completely by its
//! **signature** `(p, q)` — Sylvester's law of inertia, the unitary-group
//! `U(p,q)` analogue of the orthogonal signature. The implemented finite-support
//! backend should be read with the same exact-representability caveat as
//! `forms::char0`. We reduce by **unitary (conjugate) congruence**
//! `H ↦ M* H M`, which keeps the form Hermitian and drives it to a real diagonal,
//! then read the signs.
//!
//! Over a finite field `F_{p^{2k}}`, the matching involution is the middle
//! Frobenius `x ↦ x^{p^k}`. Nondegenerate Hermitian forms over
//! `F_{p^{2k}}/F_{p^k}` are all equivalent in a fixed rank because the norm map
//! onto the fixed field is surjective; degenerate forms split off their radical.
//! The finite classifier therefore records exactly `(rank, radical_dim)`, plus
//! finite-field metadata identifying the quadratic extension.
//!
//! [`HermitianForm::restrict_scalars`] and
//! [`FiniteHermitianForm::restrict_scalars`] expose the associated ordinary
//! quadratic form `q(v) = h(v,v)` over the involution-fixed scalar world.  Its
//! polar form is `Tr(h(v,w))`.  Keeping those two formulas distinct is essential
//! in characteristic two, where `Tr(h(v,v)) = 0` but the norm quadratic form is
//! generally nonsingular.

use crate::clifford::{Metric, MAX_BASIS_DIM};
use crate::scalar::{FiniteField, Ordered, QuadraticInvolution, Scalar, Surcomplex};
use std::cmp::Ordering;
use std::collections::BTreeMap;

/// A Hermitian form, carried by its conjugate-symmetric Gram matrix over
/// `Surcomplex<S>`.
#[derive(Debug, Clone, PartialEq)]
pub struct HermitianForm<S: Scalar> {
    gram: Vec<Vec<Surcomplex<S>>>,
}

/// The signature of a Hermitian form: `(#positive, #negative, #radical)` real
/// diagonal entries after unitary diagonalization. The complete invariant over
/// the surcomplex field.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HermitianSignature {
    /// Number of positive diagonal entries.
    pub pos: usize,
    /// Number of negative diagonal entries.
    pub neg: usize,
    /// Dimension of the radical.
    pub radical: usize,
}

/// Failure to restrict a Hermitian form to an ordinary quadratic metric over
/// the involution-fixed scalar world.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HermitianRestrictionError {
    /// Restriction doubles the represented dimension and would exceed the
    /// Clifford engine's fixed-width generator boundary.
    DimensionTooLarge {
        /// Dimension over the Hermitian coefficient world.
        hermitian_dim: usize,
        /// Largest Hermitian dimension whose restriction fits the engine.
        max_hermitian_dim: usize,
    },
    /// A coefficient mathematically fixed by the involution could not be
    /// represented in the selected fixed-field backend.
    FixedFieldProjection,
}

impl std::fmt::Display for HermitianRestrictionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HermitianRestrictionError::DimensionTooLarge {
                hermitian_dim,
                max_hermitian_dim,
            } => write!(
                f,
                "Hermitian dimension {hermitian_dim} restricts past the supported maximum {max_hermitian_dim}"
            ),
            HermitianRestrictionError::FixedFieldProjection => {
                f.write_str("Hermitian restriction coefficient left the represented fixed field")
            }
        }
    }
}

impl std::error::Error for HermitianRestrictionError {}

/// Restrict the Hermitian Gram matrix `H` over `E/F` to the ordinary quadratic
/// map `q(v) = h(v,v)` on the underlying `F`-space.
///
/// In the coordinate basis `beta_a e_i`, the quadratic and polar entries are
///
/// ```text
/// q_(i,a)                 = project(conj(beta_a) H_ii beta_a)
/// b_((i,a),(j,c))         = Tr(conj(beta_a) H_ij beta_c).
/// ```
///
/// The second line is formed as `z + involute(z)`.  The first deliberately is
/// **not** `Tr(h(v,v))`: that would be `2 h(v,v)` and would erase every
/// quadratic value in characteristic two.
fn restrict_hermitian_gram<E>(
    gram: &[Vec<E>],
) -> Result<Metric<E::Fixed>, HermitianRestrictionError>
where
    E: QuadraticInvolution,
{
    let n = gram.len();
    let Some(dim) = n.checked_mul(2) else {
        return Err(HermitianRestrictionError::DimensionTooLarge {
            hermitian_dim: n,
            max_hermitian_dim: MAX_BASIS_DIM / 2,
        });
    };
    if dim > MAX_BASIS_DIM {
        return Err(HermitianRestrictionError::DimensionTooLarge {
            hermitian_dim: n,
            max_hermitian_dim: MAX_BASIS_DIM / 2,
        });
    }

    let basis = E::fixed_basis();
    let mut q = Vec::with_capacity(dim);
    for (i, row) in gram.iter().enumerate() {
        for beta in &basis {
            let value = beta.involute().mul(&row[i]).mul(beta);
            q.push(
                E::project_fixed(&value).ok_or(HermitianRestrictionError::FixedFieldProjection)?,
            );
        }
    }

    let mut b = BTreeMap::new();
    for left in 0..dim {
        let (i, a) = (left / 2, left % 2);
        for right in (left + 1)..dim {
            let (j, c) = (right / 2, right % 2);
            let value = basis[a].involute().mul(&gram[i][j]).mul(&basis[c]);
            let polar = value.add(&value.involute());
            let fixed =
                E::project_fixed(&polar).ok_or(HermitianRestrictionError::FixedFieldProjection)?;
            if !fixed.is_zero() {
                b.insert((left, right), fixed);
            }
        }
    }

    Ok(Metric::new(q, b))
}

impl HermitianSignature {
    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for HermitianSignature {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "HermitianSignature(pos={}, neg={}, radical={})",
            self.pos, self.neg, self.radical
        )
    }
}

/// A finite-field Hermitian form over `F_{p^{2k}}/F_{p^k}`, represented inside a
/// finite cyclic field `F` whose extension degree over the prime field is even.
///
/// The involution is the middle Frobenius `x ↦ x^{p^k}`. The Gram matrix must be
/// conjugate-symmetric for that involution, and diagonal entries must lie in the
/// fixed field.
#[derive(Debug, Clone, PartialEq)]
pub struct FiniteHermitianForm<F: FiniteField> {
    gram: Vec<Vec<F>>,
}

/// The complete finite-field Hermitian invariant: rank plus radical dimension.
///
/// `extension_degree` is `[F_{p^{2k}} : F_p]`; `base_degree` is `k`, so the
/// fixed field is `F_{p^k}`. The order fields are `None` exactly when the order
/// does not fit the crate's fixed-width `u128` metadata model (for example
/// `|F_{2^128}| = 2^128`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FiniteHermitianInvariants {
    /// Rank of the Hermitian form.
    pub rank: usize,
    /// Dimension of its radical.
    pub radical_dim: usize,
    /// Characteristic of the finite field.
    pub characteristic: u128,
    /// Degree of the fixed field over the prime field.
    pub base_degree: usize,
    /// Degree of the coefficient field over the prime field.
    pub extension_degree: usize,
    /// Order of the fixed field, when it fits `u128`.
    pub base_field_order: Option<u128>,
    /// Order of the coefficient field, when it fits `u128`.
    pub extension_field_order: Option<u128>,
}

impl FiniteHermitianInvariants {
    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for FiniteHermitianInvariants {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ext = self.extension_field_order.map_or_else(
            || format!("{}^{}", self.characteristic, self.extension_degree),
            |q| q.to_string(),
        );
        let base = self.base_field_order.map_or_else(
            || format!("{}^{}", self.characteristic, self.base_degree),
            |q| q.to_string(),
        );
        write!(
            f,
            "FiniteHermitianInvariants(rank={}, radical_dim={}, field=F_{ext} over F_{base})",
            self.rank, self.radical_dim,
        )
    }
}

fn checked_pow_u128(base: u128, exp: usize) -> Option<u128> {
    let mut out = 1u128;
    for _ in 0..exp {
        out = out.checked_mul(base)?;
    }
    Some(out)
}

fn ensure_supported_finite_hermitian<F: FiniteField>() -> bool {
    F::ext_degree() > 0 && F::ext_degree().is_multiple_of(2)
}

fn finite_hermitian_conj<F: FiniteField>(x: F) -> F {
    x.frobenius_iter(F::ext_degree() / 2)
}

fn matrix_rank<F: Scalar>(rows: Vec<Vec<F>>) -> usize {
    let ncols = rows.first().map_or(0, |r| r.len());
    let nullspace = crate::linalg::field::unit_pivot_nullspace(rows, ncols)
        .expect("finite-field pivot is always invertible; unit_pivot_nullspace returned None");
    ncols - nullspace.len()
}

impl<F: FiniteField> FiniteHermitianForm<F> {
    /// Build from a Gram matrix over a finite cyclic field with even extension
    /// degree, checking `H[i,j] = conj(H[j,i])` for the middle Frobenius
    /// involution.
    pub fn from_gram(gram: Vec<Vec<F>>) -> Option<Self> {
        if !ensure_supported_finite_hermitian::<F>() {
            return None;
        }
        let n = gram.len();
        for row in &gram {
            if row.len() != n {
                return None;
            }
        }
        for i in 0..n {
            if finite_hermitian_conj(gram[i][i]) != gram[i][i] {
                return None;
            }
            for j in 0..n {
                if gram[i][j] != finite_hermitian_conj(gram[j][i]) {
                    return None;
                }
            }
        }
        Some(FiniteHermitianForm { gram })
    }

    /// A diagonal Hermitian form from entries fixed by the middle Frobenius.
    pub fn diagonal(entries: Vec<F>) -> Option<Self> {
        if entries.iter().any(|&x| finite_hermitian_conj(x) != x) {
            return None;
        }
        let n = entries.len();
        let mut gram = vec![vec![F::zero(); n]; n];
        for (i, x) in entries.into_iter().enumerate() {
            gram[i][i] = x;
        }
        Self::from_gram(gram)
    }

    /// Dimension of the form.
    pub fn dim(&self) -> usize {
        self.gram.len()
    }

    /// Hermitian Gram matrix.
    pub fn gram(&self) -> &[Vec<F>] {
        &self.gram
    }

    /// The orthogonal direct sum (block-diagonal Gram).
    pub fn direct_sum(&self, other: &FiniteHermitianForm<F>) -> FiniteHermitianForm<F> {
        let (n, m) = (self.dim(), other.dim());
        let mut gram = vec![vec![F::zero(); n + m]; n + m];
        for i in 0..n {
            for j in 0..n {
                gram[i][j] = self.gram[i][j];
            }
        }
        for i in 0..m {
            for j in 0..m {
                gram[n + i][n + j] = other.gram[i][j];
            }
        }
        FiniteHermitianForm { gram }
    }

    /// Rank over the extension field. For finite Hermitian forms, this is the
    /// rank of the nondegenerate Hermitian summand.
    pub fn rank(&self) -> usize {
        matrix_rank(self.gram.clone())
    }

    /// The complete finite-field Hermitian invariant.
    pub fn classify(&self) -> FiniteHermitianInvariants {
        let rank = self.rank();
        let extension_degree = F::ext_degree();
        let base_degree = extension_degree / 2;
        FiniteHermitianInvariants {
            rank,
            radical_dim: self.dim() - rank,
            characteristic: F::characteristic(),
            base_degree,
            extension_degree,
            base_field_order: checked_pow_u128(F::characteristic(), base_degree),
            extension_field_order: checked_pow_u128(F::characteristic(), extension_degree),
        }
    }

    /// Restrict this `F_{p^{2k}}/F_{p^k}`-Hermitian form to the ordinary
    /// quadratic form `q(v) = h(v,v)` over its represented fixed field.
    ///
    /// The method is available when the coefficient backend supplies an exact
    /// [`QuadraticInvolution`] bridge.  It currently covers every finite field
    /// exposed by Python: `F_4/F_2`, `F_16/F_4`, `F_9/F_3`, and `F_25/F_5`.
    pub fn restrict_scalars(
        &self,
    ) -> Result<Metric<<F as QuadraticInvolution>::Fixed>, HermitianRestrictionError>
    where
        F: QuadraticInvolution,
    {
        restrict_hermitian_gram(&self.gram)
    }
}

/// Congruence by the elementary unit `E = I + λ·E_{source,target}`: `H ↦ E* H E`,
/// i.e. `col_target += λ·col_source` then `row_target += conj(λ)·row_source`.
/// Preserves Hermitian-ness.
fn combine<S: Scalar>(
    h: &mut [Vec<Surcomplex<S>>],
    target: usize,
    source: usize,
    lambda: &Surcomplex<S>,
) {
    let n = h.len();
    for r in 0..n {
        let add = lambda.mul(&h[r][source]);
        h[r][target] = h[r][target].add(&add);
    }
    let cl = lambda.conj();
    for c in 0..n {
        let add = cl.mul(&h[source][c]);
        h[target][c] = h[target][c].add(&add);
    }
}

/// Congruence permutation: swap rows `k,i` and columns `k,i`.
fn swap_rows_cols<S: Scalar>(h: &mut [Vec<Surcomplex<S>>], k: usize, i: usize) {
    h.swap(k, i);
    for row in h.iter_mut() {
        row.swap(k, i);
    }
}

/// Make `h[k][k]` a nonzero (real) pivot by congruence, or report that the whole
/// trailing block `[k..]` is zero (radical).
fn ensure_pivot<S: Scalar>(h: &mut [Vec<Surcomplex<S>>], k: usize) -> bool {
    let n = h.len();
    if !h[k][k].is_zero() {
        return true;
    }
    // a nonzero diagonal entry further down → swap it up.
    for i in (k + 1)..n {
        if !h[i][i].is_zero() {
            swap_rows_cols(h, k, i);
            return true;
        }
    }
    // all trailing diagonals zero: combine in an off-diagonal partner. With
    // λ = conj(H[k][j]), the new H[k][k] = H[k][j]·conj(H[k][j]) +
    // conj(H[k][j])·H[k][j] = 2|H[k][j]|² ≠ 0 (real).
    for j in (k + 1)..n {
        if !h[k][j].is_zero() {
            let lambda = h[k][j].conj();
            combine(h, k, j, &lambda);
            return true;
        }
    }
    false // the trailing block is entirely zero
}

impl<S: Scalar> HermitianForm<S> {
    /// Build from a Gram matrix, checking it is square, conjugate-symmetric, and
    /// real on the diagonal. `None` otherwise.
    pub fn from_gram(gram: Vec<Vec<Surcomplex<S>>>) -> Option<Self> {
        let n = gram.len();
        for row in &gram {
            if row.len() != n {
                return None;
            }
        }
        for i in 0..n {
            if !gram[i][i].im.is_zero() {
                return None; // Hermitian diagonal must be real
            }
            for j in 0..n {
                if gram[i][j] != gram[j][i].conj() {
                    return None; // H* = H
                }
            }
        }
        Some(HermitianForm { gram })
    }

    /// Build from a **skew-Hermitian** Gram matrix (`H* = −H`, so the diagonal is
    /// purely imaginary), returning the *Hermitian* form `iH` that classifies it.
    ///
    /// Over a field carrying the conjugation `i ↦ −i`, multiplication by `i` is a
    /// bijection `{skew-Hermitian} → {Hermitian}` (`conj(i) = −i` makes `(iH)* =
    /// iH` exactly when `H* = −H`), so the entire signature machinery transports —
    /// the skew-Hermitian invariant is the signature of `iH`. `None` if the input
    /// is not square and skew-Hermitian.
    pub fn from_skew(gram: Vec<Vec<Surcomplex<S>>>) -> Option<Self> {
        let n = gram.len();
        for row in &gram {
            if row.len() != n {
                return None;
            }
        }
        for i in 0..n {
            if !gram[i][i].re.is_zero() {
                return None; // skew-Hermitian diagonal is purely imaginary
            }
            for j in 0..n {
                if gram[i][j] != gram[j][i].conj().neg() {
                    return None; // H* = −H
                }
            }
        }
        let i_unit = Surcomplex::i();
        let h: Vec<Vec<Surcomplex<S>>> = gram
            .iter()
            .map(|row| row.iter().map(|x| i_unit.mul(x)).collect())
            .collect();
        Self::from_gram(h)
    }

    /// A diagonal Hermitian form from real entries.
    pub fn diagonal(reals: Vec<S>) -> Self {
        let n = reals.len();
        let mut gram = vec![vec![Surcomplex::zero(); n]; n];
        for (i, r) in reals.into_iter().enumerate() {
            gram[i][i] = Surcomplex::new(r, S::zero());
        }
        HermitianForm { gram }
    }

    /// Dimension of the form.
    pub fn dim(&self) -> usize {
        self.gram.len()
    }

    /// Hermitian Gram matrix.
    pub fn gram(&self) -> &[Vec<Surcomplex<S>>] {
        &self.gram
    }

    /// Restrict this Hermitian form over `Surcomplex<S>/S` to its ordinary
    /// quadratic form over `S`.  A Hermitian dimension `n` becomes quadratic
    /// dimension `2n` in the coordinate order `(e_0, i e_0, e_1, i e_1, ...)`.
    pub fn restrict_scalars(&self) -> Result<Metric<S>, HermitianRestrictionError>
    where
        S: Ordered,
    {
        restrict_hermitian_gram(&self.gram)
    }

    /// The orthogonal direct sum (block-diagonal Gram).
    pub fn direct_sum(&self, other: &HermitianForm<S>) -> HermitianForm<S> {
        let (n, m) = (self.dim(), other.dim());
        let mut gram = vec![vec![Surcomplex::zero(); n + m]; n + m];
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
        HermitianForm { gram }
    }

    /// Unitary (conjugate) congruence to a **real diagonal** — the diagonal
    /// entries (`re`-parts; the `im` parts vanish) whose signs are the signature.
    pub fn diagonalize(&self) -> Vec<S> {
        let n = self.dim();
        let mut h = self.gram.clone();
        for k in 0..n {
            if !ensure_pivot(&mut h, k) {
                continue; // h[k][k] stays 0: a radical direction
            }
            let pinv = h[k][k]
                .inv()
                .expect("nonzero real pivot inverts in a field");
            for i in (k + 1)..n {
                if !h[i][k].is_zero() {
                    let mu = h[k][i].neg().mul(&pinv); // −H[k][i]/H[k][k]
                    combine(&mut h, i, k, &mu);
                }
            }
        }
        (0..n).map(|k| h[k][k].re.clone()).collect()
    }

    /// The Hermitian signature `(pos, neg, radical)`, reading the sign of each
    /// real diagonal entry through `sign` (e.g. `|x| x.sign()` over the surreals
    /// or rationals — the ordered base field). The complete isometry invariant.
    pub fn signature(&self, sign: impl Fn(&S) -> Ordering) -> HermitianSignature {
        let mut sig = HermitianSignature {
            pos: 0,
            neg: 0,
            radical: 0,
        };
        for d in self.diagonalize() {
            match sign(&d) {
                Ordering::Greater => sig.pos += 1,
                Ordering::Less => sig.neg += 1,
                Ordering::Equal => sig.radical += 1,
            }
        }
        sig
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{Fpn, Nimber, QuadraticInvolution, Rational, Surreal};

    type GC = Surcomplex<Rational>;

    fn gc(re: i128, im: i128) -> GC {
        Surcomplex::new(Rational::from_int(re), Rational::from_int(im))
    }
    fn rsign(x: &Rational) -> Ordering {
        x.sign()
    }

    fn evaluate_metric<S: Scalar>(metric: &Metric<S>, coordinates: &[S]) -> S {
        assert_eq!(metric.dim(), coordinates.len());
        let mut value = S::zero();
        for (i, x) in coordinates.iter().enumerate() {
            value = value.add(&metric.q()[i].mul(&x.mul(x)));
        }
        for (&(i, j), bij) in metric.b() {
            value = value.add(&bij.mul(&coordinates[i].mul(&coordinates[j])));
        }
        value
    }

    #[test]
    fn surcomplex_restriction_keeps_quadratic_and_trace_polar_data() {
        let h = HermitianForm::from_gram(vec![vec![gc(2, 0), gc(0, 1)], vec![gc(0, -1), gc(2, 0)]])
            .unwrap();
        let restricted = h.restrict_scalars().unwrap();

        assert_eq!(restricted.q(), vec![rsign_value(2); 4]);
        assert_eq!(restricted.b().len(), 2);
        assert_eq!(restricted.b().get(&(0, 3)), Some(&rsign_value(-2)));
        assert_eq!(restricted.b().get(&(1, 2)), Some(&rsign_value(2)));
        assert!(restricted.a().is_empty());

        let diagonal = HermitianForm::<Rational>::diagonal(h.diagonalize())
            .restrict_scalars()
            .unwrap();
        assert_eq!(
            crate::forms::classify_rational(&restricted),
            crate::forms::classify_rational(&diagonal),
            "unitary diagonalization must preserve the restricted quadratic class"
        );
    }

    fn rsign_value(n: i128) -> Rational {
        Rational::from_int(n)
    }

    #[test]
    fn surcomplex_restriction_doubles_signature_and_radical() {
        let h = HermitianForm::<Surreal>::diagonal(vec![
            Surreal::from_int(1),
            Surreal::from_int(-1),
            Surreal::zero(),
        ]);
        let restricted = h.restrict_scalars().unwrap();
        assert_eq!(restricted.dim(), 6);
        assert_eq!(
            crate::forms::surreal_signature(&restricted),
            Some((2, 2, 2))
        );
    }

    #[test]
    fn restriction_refuses_a_doubled_dimension_past_the_engine_boundary() {
        let h = HermitianForm::<Rational>::diagonal(vec![Rational::one(); 65]);
        assert_eq!(
            h.restrict_scalars(),
            Err(HermitianRestrictionError::DimensionTooLarge {
                hermitian_dim: 65,
                max_hermitian_dim: 64,
            })
        );
    }

    #[test]
    fn finite_hermitian_forms_over_f9_are_rank_classified() {
        type F9 = Fpn<3, 2>;
        let one = F9::one();
        let two = F9::from_int(2);
        let x = F9::from_coeffs(&[0, 1]);
        let xbar = x.frobenius_iter(1);

        let h = FiniteHermitianForm::<F9>::from_gram(vec![vec![one, x], vec![xbar, two]])
            .expect("H* = H for the middle Frobenius involution");
        let inv = h.classify();
        assert_eq!(inv.rank, 2);
        assert_eq!(inv.radical_dim, 0);
        assert_eq!(inv.characteristic, 3);
        assert_eq!(inv.base_degree, 1);
        assert_eq!(inv.extension_degree, 2);
        assert_eq!(inv.base_field_order, Some(3));
        assert_eq!(inv.extension_field_order, Some(9));

        let split = FiniteHermitianForm::<F9>::diagonal(vec![one, one]).unwrap();
        let hyperbolic = FiniteHermitianForm::<F9>::from_gram(vec![
            vec![F9::zero(), one],
            vec![one, F9::zero()],
        ])
        .unwrap();
        assert_eq!(split.classify(), hyperbolic.classify());

        assert!(
            FiniteHermitianForm::<F9>::from_gram(vec![vec![one, x], vec![x, two]]).is_none(),
            "lower off-diagonal entry must be conjugated"
        );
        assert!(
            FiniteHermitianForm::<F9>::diagonal(vec![x]).is_none(),
            "diagonal entries must be fixed by conjugation"
        );

        let norm_plane = FiniteHermitianForm::<F9>::diagonal(vec![one])
            .unwrap()
            .restrict_scalars()
            .unwrap();
        let ordinary = crate::forms::classify_finite_odd(&norm_plane).unwrap();
        assert_eq!(ordinary.dim, 2);
        assert_eq!(ordinary.radical_dim, 0);
        assert!(ordinary.disc_is_square);
    }

    #[test]
    fn finite_char2_restriction_keeps_the_norm_quadratic_form() {
        type F4 = Fpn<2, 2>;
        type F16 = Fpn<2, 4>;

        let over_f2 = FiniteHermitianForm::<F4>::diagonal(vec![F4::one()])
            .unwrap()
            .restrict_scalars()
            .unwrap();
        let arf_f2 = crate::forms::arf_char2(&over_f2).unwrap();
        assert_eq!((arf_f2.arf, arf_f2.rank, arf_f2.radical_dim), (1, 2, 0));
        assert!(!arf_f2.radical_anisotropic);

        let fixed_coefficient = F4::generator();
        let coefficient = <F16 as QuadraticInvolution>::embed_fixed(&fixed_coefficient);
        let h = FiniteHermitianForm::<F16>::diagonal(vec![coefficient]).unwrap();
        let over_f4 = h.restrict_scalars().unwrap();
        let arf_f4 = crate::forms::arf_char2(&over_f4).unwrap();
        assert_eq!((arf_f4.arf, arf_f4.rank, arf_f4.radical_dim), (1, 2, 0));
        assert!(!arf_f4.radical_anisotropic);

        let basis = <F16 as QuadraticInvolution>::fixed_basis();
        for left in 0..4u128 {
            for right in 0..4u128 {
                let coords = [
                    F4::from_coeffs(&[left & 1, (left >> 1) & 1]),
                    F4::from_coeffs(&[right & 1, (right >> 1) & 1]),
                ];
                let vector = <F16 as QuadraticInvolution>::embed_fixed(&coords[0])
                    .mul(&basis[0])
                    .add(&<F16 as QuadraticInvolution>::embed_fixed(&coords[1]).mul(&basis[1]));
                let hermitian_value = vector.involute().mul(&coefficient).mul(&vector);
                let projected = <F16 as QuadraticInvolution>::project_fixed(&hermitian_value)
                    .expect("h(v,v) lies in F_4");
                assert_eq!(evaluate_metric(&over_f4, &coords), projected);
            }
        }

        let doubled = h.direct_sum(&h).restrict_scalars().unwrap();
        let doubled_arf = crate::forms::arf_char2(&doubled).unwrap();
        assert_eq!((doubled_arf.arf, doubled_arf.rank), (0, 4));
        assert_eq!(doubled, over_f4.direct_sum(&over_f4));
    }

    #[test]
    fn finite_hermitian_forms_include_char2_even_degree_fields() {
        type F16 = Fpn<2, 4>;
        let one = F16::one();
        let x = F16::from_coeffs(&[0, 1, 0, 0]);
        let xbar = x.frobenius_iter(2);
        let h = FiniteHermitianForm::<F16>::from_gram(vec![
            vec![one, x, F16::zero()],
            vec![xbar, one, F16::zero()],
            vec![F16::zero(), F16::zero(), F16::zero()],
        ])
        .unwrap();
        let inv = h.classify();
        assert_eq!(inv.rank, 2);
        assert_eq!(inv.radical_dim, 1);
        assert_eq!(inv.characteristic, 2);
        assert_eq!(inv.base_degree, 2);
        assert_eq!(inv.base_field_order, Some(4));
        assert_eq!(inv.extension_field_order, Some(16));
    }

    #[test]
    fn finite_hermitian_forms_reject_odd_degree_fields() {
        type F27 = Fpn<3, 3>;
        assert!(FiniteHermitianForm::<F27>::from_gram(vec![vec![F27::one()]]).is_none());
    }

    #[test]
    fn nimber_quadratic_middle_frobenius_reports_width_boundary() {
        let h = FiniteHermitianForm::<Nimber>::diagonal(vec![Nimber(1), Nimber(0)]).unwrap();
        let inv = h.classify();
        assert_eq!(inv.rank, 1);
        assert_eq!(inv.radical_dim, 1);
        assert_eq!(inv.characteristic, 2);
        assert_eq!(inv.base_degree, 64);
        assert_eq!(inv.extension_degree, 128);
        assert_eq!(inv.base_field_order, Some(1u128 << 64));
        assert_eq!(inv.extension_field_order, None);
    }

    #[test]
    fn diagonal_real_form_has_sylvester_signature() {
        // ⟨1,1,−1⟩ → (2,1,0); a real-entry Hermitian form is just the symmetric one.
        let h = HermitianForm::<Rational>::diagonal(vec![
            Rational::from_int(1),
            Rational::from_int(1),
            Rational::from_int(-1),
        ]);
        assert_eq!(
            h.signature(rsign),
            HermitianSignature {
                pos: 2,
                neg: 1,
                radical: 0
            }
        );
    }

    #[test]
    fn off_diagonal_hermitian_diagonalizes() {
        // H = [[2, i], [−i, 2]] is Hermitian (H[1][0] = conj(i) = −i), positive
        // definite (det = 4 − 1 = 3 > 0, trace 4 > 0) ⇒ signature (2,0).
        let h = HermitianForm::from_gram(vec![vec![gc(2, 0), gc(0, 1)], vec![gc(0, -1), gc(2, 0)]])
            .unwrap();
        // diagonalizes to [2, 3/2]; both positive.
        assert_eq!(
            h.diagonalize(),
            vec![Rational::from_int(2), Rational::new(3, 2)]
        );
        assert_eq!(
            h.signature(rsign),
            HermitianSignature {
                pos: 2,
                neg: 0,
                radical: 0
            }
        );
        // a non-Hermitian matrix is rejected.
        assert!(HermitianForm::from_gram(vec![
            vec![gc(2, 0), gc(0, 1)],
            vec![gc(0, 1), gc(2, 0)], // should be −i to be Hermitian
        ])
        .is_none());
    }

    #[test]
    fn off_diagonal_pivot_uses_conjugate_partner() {
        let h = HermitianForm::from_gram(vec![vec![gc(0, 0), gc(1, 1)], vec![gc(1, -1), gc(0, 0)]])
            .unwrap();
        assert_eq!(
            h.diagonalize(),
            vec![Rational::from_int(4), Rational::new(-1, 2)]
        );
        assert_eq!(
            h.signature(rsign),
            HermitianSignature {
                pos: 1,
                neg: 1,
                radical: 0
            }
        );
    }

    #[test]
    fn indefinite_and_radical() {
        // [[1,0],[0,−1]] → (1,1,0); a zero diagonal entry is radical.
        let h = HermitianForm::from_gram(vec![vec![gc(1, 0), gc(0, 0)], vec![gc(0, 0), gc(-1, 0)]])
            .unwrap();
        assert_eq!(h.signature(rsign).pos, 1);
        assert_eq!(h.signature(rsign).neg, 1);
        let rad =
            HermitianForm::<Rational>::diagonal(vec![Rational::from_int(0), Rational::from_int(5)]);
        assert_eq!(h.direct_sum(&h).signature(rsign).pos, 2); // additive
        assert_eq!(rad.signature(rsign).radical, 1);
    }

    #[test]
    fn skew_hermitian_signature_via_multiplication_by_i() {
        // The real skew-symmetric form [[0,1],[−1,0]] is skew-Hermitian; iH =
        // [[0,i],[−i,0]] is the standard Hermitian form with eigenvalues ±1, so
        // the skew-Hermitian signature is (1,1).
        let h = HermitianForm::<Rational>::from_skew(vec![
            vec![gc(0, 0), gc(1, 0)],
            vec![gc(-1, 0), gc(0, 0)],
        ])
        .unwrap();
        // det(iH) = −1 < 0 ⇒ indefinite ⇒ signature (1,1) (the exact diagonal
        // values depend on the congruence path, only the signs are invariant).
        let sig = h.signature(rsign);
        assert_eq!((sig.pos, sig.neg), (1, 1));
        // a purely-imaginary diagonal is allowed (skew-Hermitian); a real one is not.
        assert!(HermitianForm::<Rational>::from_skew(vec![
            vec![gc(0, 2), gc(0, 0)],
            vec![gc(0, 0), gc(0, -3)],
        ])
        .is_some());
        assert!(HermitianForm::<Rational>::from_skew(vec![
            vec![gc(1, 0), gc(0, 0)],
            vec![gc(0, 0), gc(0, 0)],
        ])
        .is_none());
    }

    #[test]
    fn signature_over_surreal_base() {
        // Hermitian forms over the surreal-complex field, with exact infinite
        // entries: ⟨ω, −ε⟩ Hermitian signature (1,1).
        let h =
            HermitianForm::<Surreal>::diagonal(vec![Surreal::omega(), Surreal::epsilon().neg()]);
        let sig = h.signature(|x| x.sign());
        assert_eq!(sig.pos, 1);
        assert_eq!(sig.neg, 1);
    }
}
