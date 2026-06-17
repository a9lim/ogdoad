//! Extraspecial 2-groups attached to nonsingular `F_2` quadratic forms.
//!
//! A quadratic form `Q : V -> F_2` with polar form `B` determines the central
//! extension `1 -> F_2 -> E -> V -> 1` with commutator `B` and squaring map
//! `Q`. This module uses the same bitmask representation as [`arf_f2`]: vectors
//! in `V = F_2^n` are `u128` masks, `q[i]` is the square of basis vector `e_i`,
//! and `bmat[i]` records the polar neighbours of `e_i`.

use crate::clifford::Metric;
use crate::forms::{arf_f2, ArfInvariants, OrthogonalType};
use crate::scalar::Nimber;
use std::fmt;

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
