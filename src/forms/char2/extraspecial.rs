//! Extraspecial 2-groups attached to nonsingular `F_2` quadratic forms.
//!
//! A quadratic form `Q : V -> F_2` with polar form `B` determines the central
//! extension `1 -> F_2 -> E -> V -> 1` with commutator `B` and squaring map
//! `Q`. This module uses the same bitmask representation as [`arf_f2`]: vectors
//! in `V = F_2^n` are `u128` masks, `q[i]` is the square of basis vector `e_i`,
//! and `bmat[i]` records the polar neighbours of `e_i`.
//!
//! The Heisenberg/Pauli representation below is the finite Stone-von Neumann
//! side of the same object: after choosing a symplectic basis of `B`, the center
//! acts by `-1`, quotient vectors act by signed Pauli permutations on a
//! `2^r`-dimensional space, and symplectic transvections get projective Clifford
//! intertwiners. The matrices reuse the crate's dependency-free [`Complex64`]
//! type from the discriminant-form Weil layer. This is representation-theory
//! infrastructure, not a game rule.

use crate::clifford::Metric;
use crate::forms::Complex64;
use crate::forms::{arf_f2, ArfInvariants, OrthogonalType};
use crate::scalar::Nimber;
use std::fmt;

/// Full dense Pauli/Clifford matrices are only materialized up to this quotient
/// half-rank. The action-on-basis API remains available beyond this cap.
pub const HEISENBERG_WEIL_MATRIX_RANK_CAP: usize = 8;

/// Error returned when a metric is outside the extraspecial 2-group boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExtraspecialError {
    /// The bitmask model supports at most 128 `F_2` basis vectors.
    DimensionTooLarge,
    /// The diagonal and polar rows do not describe a symmetric alternating
    /// `F_2` polar form of the requested dimension.
    InvalidF2Data,
    /// The input `Metric<Nimber>` had coefficients outside the prime field
    /// `F_2 = {0,1}`.
    NonF2Metric,
    /// General-bilinear metrics have an upper contraction `a`; the extraspecial
    /// construction uses only the quadratic data `(q,b)`.
    GeneralBilinearMetric,
    /// The polar form has a radical, so the central extension is not
    /// extraspecial.
    SingularPolarForm,
}

impl fmt::Display for ExtraspecialError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExtraspecialError::DimensionTooLarge => {
                f.write_str("extraspecial bitmask dimension exceeds 128")
            }
            ExtraspecialError::InvalidF2Data => {
                f.write_str("invalid F2 quadratic data for extraspecial group")
            }
            ExtraspecialError::NonF2Metric => {
                f.write_str("extraspecial group needs a Metric<Nimber> over F2 entries")
            }
            ExtraspecialError::GeneralBilinearMetric => {
                f.write_str("extraspecial group is undefined for general-bilinear metrics")
            }
            ExtraspecialError::SingularPolarForm => {
                f.write_str("extraspecial group needs a nonsingular polar form")
            }
        }
    }
}

impl std::error::Error for ExtraspecialError {}

/// The central-product type of an extraspecial 2-group.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExtraspecialType {
    /// Plus type: central product of copies of `D_8`; equivalently Arf `0`.
    Plus,
    /// Minus type: `Q_8` central-producted with copies of `D_8`;
    /// equivalently Arf `1`.
    Minus,
}

impl ExtraspecialType {
    /// The matching orthogonal type of the quadratic form.
    pub fn orthogonal_type(self) -> OrthogonalType {
        match self {
            ExtraspecialType::Plus => OrthogonalType::OPlus,
            ExtraspecialType::Minus => OrthogonalType::OMinus,
        }
    }
}

impl fmt::Display for ExtraspecialType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExtraspecialType::Plus => f.write_str("+"),
            ExtraspecialType::Minus => f.write_str("-"),
        }
    }
}

/// An element `(z, v)` of an [`Extraspecial2Group`], with `z` central and
/// `v ∈ F_2^n` stored as a bitmask.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExtraspecialElement {
    central: bool,
    vector: u128,
}

impl ExtraspecialElement {
    /// Construct an element from the central bit and vector mask. Membership in
    /// a particular group is checked by [`Extraspecial2Group::contains`].
    pub fn new(central: bool, vector: u128) -> Self {
        ExtraspecialElement { central, vector }
    }

    /// The central `F_2` coordinate.
    pub fn central(&self) -> bool {
        self.central
    }

    /// The image in the quotient vector space `E/Z(E)`.
    pub fn vector(&self) -> u128 {
        self.vector
    }
}

/// The extraspecial 2-group attached to a nonsingular quadratic form over `F_2`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Extraspecial2Group {
    dim: usize,
    qd: Vec<bool>,
    bmat: Vec<u128>,
    arf: ArfInvariants,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CoordinateRow {
    pivot: usize,
    vector: u128,
    coords: u128,
}

/// The finite Heisenberg/Pauli representation attached to an
/// [`Extraspecial2Group`].
///
/// The representation uses a computed symplectic basis
/// `(x_0,y_0,...,x_{r-1},y_{r-1})` of the quotient `V = E/Z(E)`.  The basis state
/// `ket` is a bitmask in `F_2^r`; `x_i` flips bit `i`, `y_i` multiplies by
/// `(-1)^ket_i`, and the quadratic values `Q(x_i), Q(y_i)` insert the necessary
/// fourth-root phases so that each lift squares to the central action.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeisenbergWeilRepresentation {
    group: Extraspecial2Group,
    symplectic_basis: Vec<u128>,
    coordinate_rows: Vec<CoordinateRow>,
}

impl Extraspecial2Group {
    /// Build the group from `F_2` quadratic data. `bmat[i]` has bit `j` set iff
    /// `B(e_i,e_j)=1`; rows must be symmetric and diagonal-free.
    pub fn from_f2(qd: Vec<bool>, bmat: Vec<u128>) -> Result<Self, ExtraspecialError> {
        let dim = qd.len();
        validate_f2_data(dim, &bmat)?;
        if dim == 0 {
            return Err(ExtraspecialError::SingularPolarForm);
        }
        let arf = arf_f2(dim, &qd, &bmat);
        if arf.radical_dim != 0 || arf.rank != dim {
            return Err(ExtraspecialError::SingularPolarForm);
        }
        Ok(Extraspecial2Group { dim, qd, bmat, arf })
    }

    /// Build the group from a `Metric<Nimber>` whose entries lie in the prime
    /// subfield `F_2`. General-bilinear metrics are rejected.
    pub fn from_nimber_metric(metric: &Metric<Nimber>) -> Result<Self, ExtraspecialError> {
        if !metric.a().is_empty() {
            return Err(ExtraspecialError::GeneralBilinearMetric);
        }
        let dim = metric.dim();
        if dim > 128 {
            return Err(ExtraspecialError::DimensionTooLarge);
        }
        let qd = metric
            .q()
            .iter()
            .map(|x| match x.0 {
                0 => Ok(false),
                1 => Ok(true),
                _ => Err(ExtraspecialError::NonF2Metric),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut bmat = vec![0u128; dim];
        for (&(i, j), v) in metric.b() {
            let bit = match v.0 {
                0 => false,
                1 => true,
                _ => return Err(ExtraspecialError::NonF2Metric),
            };
            if bit {
                bmat[i] |= 1u128 << j;
                bmat[j] |= 1u128 << i;
            }
        }
        Self::from_f2(qd, bmat)
    }

    /// Dimension of the quotient vector space `E/Z(E)`.
    pub fn dim(&self) -> usize {
        self.dim
    }

    /// The exponent `k` such that `|E| = 2^k`.
    pub fn order_exponent(&self) -> usize {
        self.dim + 1
    }

    /// The group order as a `u128`, when it fits.
    pub fn order_u128(&self) -> Option<u128> {
        (self.order_exponent() < 128).then_some(1u128 << self.order_exponent())
    }

    /// Arf data of the defining quadratic form.
    pub fn arf(&self) -> &ArfInvariants {
        &self.arf
    }

    /// The central-product type, classified by the Arf bit.
    pub fn extraspecial_type(&self) -> ExtraspecialType {
        if self.arf.arf == 0 {
            ExtraspecialType::Plus
        } else {
            ExtraspecialType::Minus
        }
    }

    /// The finite Heisenberg/Pauli representation with central character `-1`.
    ///
    /// This chooses a symplectic basis of the nonsingular polar form and returns
    /// the standard `2^r`-dimensional Schrödinger model. Dense matrices are
    /// bounded by [`HEISENBERG_WEIL_MATRIX_RANK_CAP`], but
    /// [`HeisenbergWeilRepresentation::apply_to_basis_state`] gives the signed
    /// permutation action without materializing a matrix.
    pub fn heisenberg_weil_representation(&self) -> Option<HeisenbergWeilRepresentation> {
        HeisenbergWeilRepresentation::from_group(self.clone())
    }

    /// Identity element.
    pub fn identity(&self) -> ExtraspecialElement {
        ExtraspecialElement::new(false, 0)
    }

    /// The central involution.
    pub fn central_generator(&self) -> ExtraspecialElement {
        ExtraspecialElement::new(true, 0)
    }

    /// Lift of the `i`th basis vector.
    pub fn generator(&self, i: usize) -> Option<ExtraspecialElement> {
        (i < self.dim).then_some(ExtraspecialElement::new(false, 1u128 << i))
    }

    /// Construct an element, rejecting vector bits outside the quotient space.
    pub fn element(&self, central: bool, vector: u128) -> Option<ExtraspecialElement> {
        (vector & !self.mask() == 0).then_some(ExtraspecialElement::new(central, vector))
    }

    /// Whether `x` belongs to this group's bitmask universe.
    pub fn contains(&self, x: &ExtraspecialElement) -> bool {
        x.vector & !self.mask() == 0
    }

    /// Quadratic value `Q(v)`.
    pub fn q_value(&self, vector: u128) -> Option<bool> {
        if vector & !self.mask() == 0 {
            Some(self.q_value_unchecked(vector))
        } else {
            None
        }
    }

    /// Polar value `B(u,v)`.
    pub fn polar_value(&self, u: u128, v: u128) -> Option<bool> {
        if (u | v) & !self.mask() == 0 {
            Some(self.polar_value_unchecked(u, v))
        } else {
            None
        }
    }

    /// The canonical 2-cocycle `f(u,v)` used by the multiplication:
    ///
    /// `f(u,v) = Σ q_i u_i v_i + Σ_{i<j} b_ij u_i v_j`.
    pub fn cocycle_value(&self, u: u128, v: u128) -> Option<bool> {
        if (u | v) & !self.mask() == 0 {
            Some(self.cocycle_value_unchecked(u, v))
        } else {
            None
        }
    }

    /// Group multiplication.
    pub fn multiply(
        &self,
        x: &ExtraspecialElement,
        y: &ExtraspecialElement,
    ) -> Option<ExtraspecialElement> {
        if !self.contains(x) || !self.contains(y) {
            return None;
        }
        Some(ExtraspecialElement::new(
            x.central ^ y.central ^ self.cocycle_value_unchecked(x.vector, y.vector),
            x.vector ^ y.vector,
        ))
    }

    /// Inverse of an element.
    pub fn inverse(&self, x: &ExtraspecialElement) -> Option<ExtraspecialElement> {
        if !self.contains(x) {
            return None;
        }
        Some(ExtraspecialElement::new(
            x.central ^ self.q_value_unchecked(x.vector),
            x.vector,
        ))
    }

    /// Square `x^2`, always central and equal to `Q(x mod Z)`.
    pub fn square(&self, x: &ExtraspecialElement) -> Option<ExtraspecialElement> {
        if !self.contains(x) {
            return None;
        }
        Some(ExtraspecialElement::new(
            self.q_value_unchecked(x.vector),
            0,
        ))
    }

    /// Commutator `[x,y]`, always central and equal to `B(x mod Z, y mod Z)`.
    pub fn commutator(
        &self,
        x: &ExtraspecialElement,
        y: &ExtraspecialElement,
    ) -> Option<ExtraspecialElement> {
        if !self.contains(x) || !self.contains(y) {
            return None;
        }
        Some(ExtraspecialElement::new(
            self.polar_value_unchecked(x.vector, y.vector),
            0,
        ))
    }

    fn mask(&self) -> u128 {
        mask_for_dim(self.dim)
    }

    fn q_value_unchecked(&self, vector: u128) -> bool {
        let mut acc = false;
        let mut vv = vector;
        while vv != 0 {
            let i = vv.trailing_zeros() as usize;
            vv &= vv - 1;
            acc ^= self.qd[i];
            acc ^= parity(self.bmat[i] & vector & above(i));
        }
        acc
    }

    fn polar_value_unchecked(&self, u: u128, v: u128) -> bool {
        let mut acc = false;
        let mut uu = u;
        while uu != 0 {
            let i = uu.trailing_zeros() as usize;
            uu &= uu - 1;
            acc ^= parity(self.bmat[i] & v);
        }
        acc
    }

    fn cocycle_value_unchecked(&self, u: u128, v: u128) -> bool {
        let mut acc = false;
        let mut uu = u;
        while uu != 0 {
            let i = uu.trailing_zeros() as usize;
            uu &= uu - 1;
            acc ^= self.qd[i] && ((v >> i) & 1 == 1);
            acc ^= parity(self.bmat[i] & v & above(i));
        }
        acc
    }

    fn symplectic_basis(&self) -> Option<Vec<u128>> {
        let mut remaining: Vec<u128> = (0..self.dim).map(|i| 1u128 << i).collect();
        let mut basis = Vec::with_capacity(self.dim);
        while !remaining.is_empty() {
            let u = remaining[0];
            let v = *remaining
                .iter()
                .find(|&&w| self.polar_value_unchecked(u, w))?;
            basis.push(u);
            basis.push(v);

            let mut next = Vec::new();
            for &w in &remaining {
                let mut projected = w;
                if self.polar_value_unchecked(w, v) {
                    projected ^= u;
                }
                if self.polar_value_unchecked(w, u) {
                    projected ^= v;
                }
                insert_independent(&mut next, projected);
            }
            remaining = next;
        }
        (basis.len() == self.dim).then_some(basis)
    }
}

impl HeisenbergWeilRepresentation {
    fn from_group(group: Extraspecial2Group) -> Option<Self> {
        let symplectic_basis = group.symplectic_basis()?;
        let coordinate_rows = coordinate_rows_for_basis(&symplectic_basis)?;
        Some(HeisenbergWeilRepresentation {
            group,
            symplectic_basis,
            coordinate_rows,
        })
    }

    /// The underlying extraspecial group.
    pub fn group(&self) -> &Extraspecial2Group {
        &self.group
    }

    /// Half the quotient dimension: the representation has dimension `2^r`.
    pub fn rank(&self) -> usize {
        self.group.dim / 2
    }

    /// Dimension of `E/Z(E)`.
    pub fn quotient_dim(&self) -> usize {
        self.group.dim
    }

    /// Dimension of the representation space, when it fits in `u128`.
    pub fn hilbert_dim_u128(&self) -> Option<u128> {
        (self.rank() < 128).then_some(1u128 << self.rank())
    }

    /// The chosen symplectic basis `(x_0,y_0,...,x_{r-1},y_{r-1})`, as original
    /// quotient-space bitmasks.
    pub fn symplectic_basis(&self) -> &[u128] {
        &self.symplectic_basis
    }

    /// Coordinates of a quotient vector in the chosen symplectic basis.
    pub fn basis_coordinates(&self, vector: u128) -> Option<u128> {
        if vector & !self.group.mask() != 0 {
            return None;
        }
        let mut v = vector;
        let mut coords = 0u128;
        for row in &self.coordinate_rows {
            if (v >> row.pivot) & 1 == 1 {
                v ^= row.vector;
                coords ^= row.coords;
            }
        }
        (v == 0).then_some(coords)
    }

    /// Apply the representation of `x` to a computational basis state `ket`.
    ///
    /// Returns `(phase, target_ket)`, meaning `rho(x)|ket> = phase·|target_ket>`.
    /// The `ket` bitmask must lie in `F_2^r`.
    pub fn apply_to_basis_state(
        &self,
        x: &ExtraspecialElement,
        ket: u128,
    ) -> Option<(Complex64, u128)> {
        if !self.group.contains(x) || ket & !mask_for_dim(self.rank()) != 0 {
            return None;
        }
        let coords = self.basis_coordinates(x.vector)?;
        let product = self.ordered_product(coords)?;
        let mut phase = Complex64::one();
        let mut target = ket;
        let mut cc = coords;
        let mut ops = Vec::new();
        while cc != 0 {
            let k = cc.trailing_zeros() as usize;
            cc &= cc - 1;
            ops.push(k);
        }
        for k in ops.into_iter().rev() {
            let (p, next) = self.apply_basis_operator(k, target);
            phase = phase.mul(&p);
            target = next;
        }
        if product.central ^ x.central {
            phase = phase.scale(-1.0);
        }
        Some((phase, target))
    }

    /// Dense matrix of `rho(x)`, or `None` past the explicit matrix budget.
    pub fn matrix(&self, x: &ExtraspecialElement) -> Option<Vec<Vec<Complex64>>> {
        let n = self.matrix_dim()?;
        let mut out = vec![vec![Complex64::zero(); n]; n];
        for col in 0..n {
            let (phase, row) = self.apply_to_basis_state(x, col as u128)?;
            out[row as usize][col] = phase;
        }
        Some(out)
    }

    /// A projective Clifford/Weil operator for the symplectic transvection
    /// `w -> w + B(w,a)a`, returned as a dense matrix under the same budget as
    /// [`matrix`](Self::matrix).
    pub fn transvection_intertwiner(&self, a: u128) -> Option<Vec<Vec<Complex64>>> {
        self.transvection_intertwiner_with_sign(a, false)
    }

    /// Verify projectively that the transvection operator conjugates Pauli
    /// operators by `w -> w + B(w,a)a` on the original quotient generators.
    pub fn verify_transvection_intertwines(&self, a: u128) -> bool {
        if a == 0 || a & !self.group.mask() != 0 {
            return false;
        }
        let Some(u) = self.transvection_intertwiner(a) else {
            return false;
        };
        let Some(u_inv) = self.transvection_intertwiner_with_sign(a, true) else {
            return false;
        };
        for i in 0..self.group.dim {
            let v = 1u128 << i;
            let target = if self.group.polar_value_unchecked(v, a) {
                v ^ a
            } else {
                v
            };
            let Some(lhs) = self
                .matrix(&ExtraspecialElement::new(false, v))
                .map(|m| mat_mul(&mat_mul(&u, &m), &u_inv))
            else {
                return false;
            };
            let Some(rhs) = self.matrix(&ExtraspecialElement::new(false, target)) else {
                return false;
            };
            if !mat_projectively_approx_eq(&lhs, &rhs, 1e-8) {
                return false;
            }
        }
        true
    }

    fn matrix_dim(&self) -> Option<usize> {
        if self.rank() > HEISENBERG_WEIL_MATRIX_RANK_CAP {
            return None;
        }
        Some(1usize << self.rank())
    }

    fn ordered_product(&self, coords: u128) -> Option<ExtraspecialElement> {
        let mut acc = self.group.identity();
        let mut cc = coords;
        while cc != 0 {
            let k = cc.trailing_zeros() as usize;
            cc &= cc - 1;
            let basis_element = ExtraspecialElement::new(false, self.symplectic_basis[k]);
            acc = self.group.multiply(&acc, &basis_element)?;
        }
        Some(acc)
    }

    fn apply_basis_operator(&self, k: usize, ket: u128) -> (Complex64, u128) {
        let q = self.group.q_value_unchecked(self.symplectic_basis[k]);
        let mut phase = if q {
            Complex64::eighth_root(2)
        } else {
            Complex64::one()
        };
        let i = k / 2;
        if k.is_multiple_of(2) {
            (phase, ket ^ (1u128 << i))
        } else {
            if (ket >> i) & 1 == 1 {
                phase = phase.scale(-1.0);
            }
            (phase, ket)
        }
    }

    fn transvection_intertwiner_with_sign(
        &self,
        a: u128,
        inverse: bool,
    ) -> Option<Vec<Vec<Complex64>>> {
        if a == 0 || a & !self.group.mask() != 0 {
            return None;
        }
        let p = self.matrix(&ExtraspecialElement::new(false, a))?;
        let lambda = if self.group.q_value_unchecked(a) {
            Complex64::one()
        } else {
            Complex64::eighth_root(2)
        };
        let signed_lambda = if inverse { lambda.scale(-1.0) } else { lambda };
        let qp = mat_scale(&p, signed_lambda);
        let id = mat_identity(qp.len());
        Some(mat_scale(
            &mat_add(&id, &qp),
            Complex64::one().scale(std::f64::consts::FRAC_1_SQRT_2),
        ))
    }
}

/// Build the extraspecial 2-group attached to `F_2` quadratic data.
pub fn extraspecial_group_f2(
    qd: Vec<bool>,
    bmat: Vec<u128>,
) -> Result<Extraspecial2Group, ExtraspecialError> {
    Extraspecial2Group::from_f2(qd, bmat)
}

/// Build the extraspecial 2-group attached to an `F_2`-valued nimber metric.
pub fn extraspecial_group_nimber(
    metric: &Metric<Nimber>,
) -> Result<Extraspecial2Group, ExtraspecialError> {
    Extraspecial2Group::from_nimber_metric(metric)
}

/// Build the finite Heisenberg/Pauli representation attached to `F_2`
/// quadratic data.
pub fn heisenberg_weil_representation_f2(
    qd: Vec<bool>,
    bmat: Vec<u128>,
) -> Result<HeisenbergWeilRepresentation, ExtraspecialError> {
    Extraspecial2Group::from_f2(qd, bmat).map(|g| {
        g.heisenberg_weil_representation()
            .expect("nonsingular alternating forms admit a symplectic basis")
    })
}

/// Build the finite Heisenberg/Pauli representation attached to an `F_2`-valued
/// nimber metric.
pub fn heisenberg_weil_representation_nimber(
    metric: &Metric<Nimber>,
) -> Result<HeisenbergWeilRepresentation, ExtraspecialError> {
    Extraspecial2Group::from_nimber_metric(metric).map(|g| {
        g.heisenberg_weil_representation()
            .expect("nonsingular alternating forms admit a symplectic basis")
    })
}

fn validate_f2_data(dim: usize, bmat: &[u128]) -> Result<(), ExtraspecialError> {
    if dim > 128 {
        return Err(ExtraspecialError::DimensionTooLarge);
    }
    if bmat.len() != dim {
        return Err(ExtraspecialError::InvalidF2Data);
    }
    let mask = mask_for_dim(dim);
    for i in 0..dim {
        if bmat[i] & !mask != 0 || ((bmat[i] >> i) & 1 == 1) {
            return Err(ExtraspecialError::InvalidF2Data);
        }
        for j in (i + 1)..dim {
            if ((bmat[i] >> j) & 1) != ((bmat[j] >> i) & 1) {
                return Err(ExtraspecialError::InvalidF2Data);
            }
        }
    }
    Ok(())
}

fn mask_for_dim(dim: usize) -> u128 {
    if dim == 128 {
        !0u128
    } else if dim == 0 {
        0
    } else {
        (1u128 << dim) - 1
    }
}

fn above(i: usize) -> u128 {
    if i >= 127 {
        0
    } else {
        (!0u128) << (i + 1)
    }
}

fn parity(mask: u128) -> bool {
    mask.count_ones() & 1 == 1
}

fn insert_independent(rows: &mut Vec<u128>, mut v: u128) -> bool {
    if v == 0 {
        return false;
    }
    for &row in rows.iter() {
        let p = row.trailing_zeros() as usize;
        if (v >> p) & 1 == 1 {
            v ^= row;
        }
    }
    if v == 0 {
        return false;
    }
    let pivot = v.trailing_zeros() as usize;
    for row in rows.iter_mut() {
        if (*row >> pivot) & 1 == 1 {
            *row ^= v;
        }
    }
    rows.push(v);
    rows.sort_by_key(|row| row.trailing_zeros());
    true
}

fn coordinate_rows_for_basis(basis: &[u128]) -> Option<Vec<CoordinateRow>> {
    let mut rows: Vec<CoordinateRow> = Vec::new();
    for (j, &b) in basis.iter().enumerate() {
        let mut vector = b;
        let mut coords = 1u128 << j;
        for row in &rows {
            if (vector >> row.pivot) & 1 == 1 {
                vector ^= row.vector;
                coords ^= row.coords;
            }
        }
        if vector == 0 {
            return None;
        }
        let pivot = vector.trailing_zeros() as usize;
        for row in rows.iter_mut() {
            if (row.vector >> pivot) & 1 == 1 {
                row.vector ^= vector;
                row.coords ^= coords;
            }
        }
        rows.push(CoordinateRow {
            pivot,
            vector,
            coords,
        });
        rows.sort_by_key(|row| row.pivot);
    }
    Some(rows)
}

fn mat_identity(n: usize) -> Vec<Vec<Complex64>> {
    let mut out = vec![vec![Complex64::zero(); n]; n];
    for (i, row) in out.iter_mut().enumerate() {
        row[i] = Complex64::one();
    }
    out
}

fn mat_add(a: &[Vec<Complex64>], b: &[Vec<Complex64>]) -> Vec<Vec<Complex64>> {
    a.iter()
        .zip(b)
        .map(|(ra, rb)| ra.iter().zip(rb).map(|(x, y)| x.add(y)).collect())
        .collect()
}

fn mat_mul(a: &[Vec<Complex64>], b: &[Vec<Complex64>]) -> Vec<Vec<Complex64>> {
    let n = a.len();
    let m = b.first().map_or(0, Vec::len);
    let inner = b.len();
    let mut out = vec![vec![Complex64::zero(); m]; n];
    for i in 0..n {
        for k in 0..inner {
            for j in 0..m {
                out[i][j] = out[i][j].add(&a[i][k].mul(&b[k][j]));
            }
        }
    }
    out
}

fn mat_scale(a: &[Vec<Complex64>], c: Complex64) -> Vec<Vec<Complex64>> {
    a.iter()
        .map(|row| row.iter().map(|x| x.mul(&c)).collect())
        .collect()
}

#[cfg(test)]
fn mat_approx_eq(a: &[Vec<Complex64>], b: &[Vec<Complex64>], tol: f64) -> bool {
    a.len() == b.len()
        && a.iter().zip(b).all(|(ra, rb)| {
            ra.len() == rb.len() && ra.iter().zip(rb).all(|(x, y)| x.approx_eq(y, tol))
        })
}

fn mat_projectively_approx_eq(a: &[Vec<Complex64>], b: &[Vec<Complex64>], tol: f64) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut scalar = None;
    for (ra, rb) in a.iter().zip(b) {
        if ra.len() != rb.len() {
            return false;
        }
        for (x, y) in ra.iter().zip(rb) {
            if y.abs() > tol {
                let denom = y.re * y.re + y.im * y.im;
                scalar = Some(Complex64 {
                    re: (x.re * y.re + x.im * y.im) / denom,
                    im: (x.im * y.re - x.re * y.im) / denom,
                });
                break;
            } else if x.abs() > tol {
                return false;
            }
        }
        if scalar.is_some() {
            break;
        }
    }
    let Some(scalar) = scalar else {
        return true;
    };
    a.iter().zip(b).all(|(ra, rb)| {
        ra.iter()
            .zip(rb)
            .all(|(x, y)| x.approx_eq(&scalar.mul(y), tol))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clifford::Metric;
    use crate::forms::arf_nimber;
    use crate::scalar::Nimber;
    use std::collections::BTreeMap;

    fn bmat(dim: usize, pairs: &[(usize, usize)]) -> Vec<u128> {
        let mut rows = vec![0u128; dim];
        for &(i, j) in pairs {
            rows[i] |= 1u128 << j;
            rows[j] |= 1u128 << i;
        }
        rows
    }

    fn all_elements(g: &Extraspecial2Group) -> Vec<ExtraspecialElement> {
        let mut out = Vec::new();
        for vector in 0..(1u128 << g.dim()) {
            out.push(g.element(false, vector).unwrap());
            out.push(g.element(true, vector).unwrap());
        }
        out
    }

    fn check_representation(g: &Extraspecial2Group) {
        let rep = g.heisenberg_weil_representation().unwrap();
        assert_eq!(rep.quotient_dim(), g.dim());
        assert_eq!(rep.hilbert_dim_u128(), Some(1u128 << rep.rank()));

        let elems = all_elements(g);
        for x in &elems {
            let mx = rep.matrix(x).unwrap();
            for y in &elems {
                let my = rep.matrix(y).unwrap();
                let xy = g.multiply(x, y).unwrap();
                let mxy = rep.matrix(&xy).unwrap();
                assert!(mat_approx_eq(&mat_mul(&mx, &my), &mxy, 1e-8));
            }
        }
    }

    fn check_group_laws(g: &Extraspecial2Group) {
        let elems = all_elements(g);
        let id = g.identity();
        for x in &elems {
            assert_eq!(g.multiply(&id, x), Some(*x));
            assert_eq!(g.multiply(x, &id), Some(*x));
            let inv = g.inverse(x).unwrap();
            assert_eq!(g.multiply(x, &inv), Some(id));
            assert_eq!(g.multiply(&inv, x), Some(id));
            assert_eq!(
                g.square(x),
                Some(ExtraspecialElement::new(g.q_value(x.vector()).unwrap(), 0))
            );
            for y in &elems {
                assert_eq!(
                    g.commutator(x, y),
                    Some(ExtraspecialElement::new(
                        g.polar_value(x.vector(), y.vector()).unwrap(),
                        0
                    ))
                );
                for z in &elems {
                    let xy_z = g.multiply(&g.multiply(x, y).unwrap(), z).unwrap();
                    let x_yz = g.multiply(x, &g.multiply(y, z).unwrap()).unwrap();
                    assert_eq!(xy_z, x_yz);
                }
            }
        }
    }

    #[test]
    fn hyperbolic_plane_is_plus_type_d8_cell() {
        let g = Extraspecial2Group::from_f2(vec![false, false], bmat(2, &[(0, 1)])).unwrap();
        assert_eq!(g.order_exponent(), 3);
        assert_eq!(g.order_u128(), Some(8));
        assert_eq!(g.arf().arf, 0);
        assert_eq!(g.extraspecial_type(), ExtraspecialType::Plus);
        assert_eq!(
            g.extraspecial_type().orthogonal_type(),
            OrthogonalType::OPlus
        );

        let x = g.generator(0).unwrap();
        let y = g.generator(1).unwrap();
        assert_eq!(g.square(&x), Some(g.identity()));
        assert_eq!(g.square(&y), Some(g.identity()));
        assert_eq!(g.commutator(&x, &y), Some(g.central_generator()));
        assert_eq!(
            g.square(&g.multiply(&x, &y).unwrap()),
            Some(g.central_generator())
        );
        check_group_laws(&g);
        check_representation(&g);

        let rep = g.heisenberg_weil_representation().unwrap();
        assert!(rep.verify_transvection_intertwines(x.vector()));
        assert!(rep.verify_transvection_intertwines(y.vector()));
    }

    #[test]
    fn anisotropic_plane_is_minus_type_q8_cell() {
        let g = Extraspecial2Group::from_f2(vec![true, true], bmat(2, &[(0, 1)])).unwrap();
        assert_eq!(g.arf().arf, 1);
        assert_eq!(g.extraspecial_type(), ExtraspecialType::Minus);
        assert_eq!(
            g.extraspecial_type().orthogonal_type(),
            OrthogonalType::OMinus
        );

        for v in 1..4 {
            let x = g.element(false, v).unwrap();
            assert_eq!(g.square(&x), Some(g.central_generator()));
        }
        check_group_laws(&g);
        check_representation(&g);
    }

    #[test]
    fn heisenberg_representation_handles_rank_two_symplectic_reduction() {
        let g =
            Extraspecial2Group::from_f2(vec![false, true, true, false], bmat(4, &[(0, 2), (1, 3)]))
                .unwrap();
        let rep = g.heisenberg_weil_representation().unwrap();
        assert_eq!(rep.rank(), 2);
        assert_eq!(rep.hilbert_dim_u128(), Some(4));
        for pair in rep.symplectic_basis().chunks(2) {
            assert_eq!(g.polar_value(pair[0], pair[1]), Some(true));
        }
        check_representation(&g);
        assert!(rep.verify_transvection_intertwines(0b0101));
    }

    #[test]
    fn nimber_metric_route_matches_arf_classifier() {
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), Nimber(1));
        b.insert((2usize, 3usize), Nimber(1));
        let metric = Metric::new(vec![Nimber(1), Nimber(1), Nimber(0), Nimber(0)], b);
        let g = Extraspecial2Group::from_nimber_metric(&metric).unwrap();
        let arf = arf_nimber(&metric).unwrap();
        assert_eq!(g.arf(), &arf);
        assert_eq!(g.extraspecial_type(), ExtraspecialType::Minus);
    }

    #[test]
    fn rejects_singular_non_f2_and_general_metrics() {
        assert_eq!(
            Extraspecial2Group::from_f2(vec![true, true], bmat(2, &[])),
            Err(ExtraspecialError::SingularPolarForm)
        );
        assert_eq!(
            Extraspecial2Group::from_f2(vec![false, false], vec![0b10, 0]),
            Err(ExtraspecialError::InvalidF2Data)
        );

        let metric = Metric::diagonal(vec![Nimber(2), Nimber(1)]);
        assert_eq!(
            Extraspecial2Group::from_nimber_metric(&metric),
            Err(ExtraspecialError::NonF2Metric)
        );

        let mut upper = BTreeMap::new();
        upper.insert((0usize, 1usize), Nimber(1));
        let metric = Metric::general(vec![Nimber(0), Nimber(0)], BTreeMap::new(), upper);
        assert_eq!(
            Extraspecial2Group::from_nimber_metric(&metric),
            Err(ExtraspecialError::GeneralBilinearMetric)
        );
    }
}
