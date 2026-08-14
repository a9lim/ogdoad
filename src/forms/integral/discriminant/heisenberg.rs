//! The 2-elementary overlap between discriminant-form and Heisenberg Weil
//! representations.
//!
//! The discriminant representation of `A` acts on `C[A]`, whereas the
//! Schrödinger representation attached directly to a symplectic quotient `V`
//! has dimension `sqrt(|V|)`.  The matching Heisenberg phase space is therefore
//! `A (+) A*`, whose Schrödinger space has dimension `|A|`.  This module makes
//! that doubled-space identification explicit and compares the two `S`/`T`
//! operators projectively.

use super::complex::Complex64;
use super::form::min_generators;
use super::gauss_sum::{mat_approx_eq, mat_mul, mat_scale};
use super::DiscriminantForm;
use crate::forms::{extraspecial_group_f2, HeisenbergWeilRepresentation};
use crate::scalar::{Rational, Scalar};
use std::fmt;

const TOL: f64 = 1e-8;

/// Coherence report for the 2-elementary discriminant module `(A,q)` and the
/// Schrödinger representation of its doubled Heisenberg phase space `A (+) A*`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwoElementaryWeilHeisenbergInvariants {
    /// `dim_F2 A`.
    pub rank: usize,
    /// `|A|`, also the common matrix dimension.
    pub order: usize,
    /// The discriminant `S` matrix agrees with the Heisenberg Fourier operator,
    /// after the bilinear identification `A -> A*` and the Milgram scalar.
    pub s_matches: bool,
    /// The discriminant `T` matrix agrees with the quadratic phase operator.
    pub t_matches: bool,
    /// `S` projectively exchanges position and momentum Pauli operators.
    pub s_intertwines: bool,
    /// `T` projectively implements the shear determined by the polar form.
    pub t_intertwines: bool,
    /// The original discriminant `S,T` satisfy the metaplectic relations.
    pub metaplectic_relations: bool,
}

impl TwoElementaryWeilHeisenbergInvariants {
    /// Whether every comparison in the doubled phase-space diagram succeeded.
    pub fn verified(&self) -> bool {
        self.s_matches
            && self.t_matches
            && self.s_intertwines
            && self.t_intertwines
            && self.metaplectic_relations
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for TwoElementaryWeilHeisenbergInvariants {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "TwoElementaryWeilHeisenbergInvariants(rank={}, order={}, s_matches={}, t_matches={}, s_intertwines={}, t_intertwines={}, metaplectic_relations={}, verified={})",
            self.rank,
            self.order,
            self.s_matches,
            self.t_matches,
            self.s_intertwines,
            self.t_intertwines,
            self.metaplectic_relations,
            self.verified(),
        )
    }
}

fn conjugate_transpose(a: &[Vec<Complex64>]) -> Vec<Vec<Complex64>> {
    let n = a.len();
    let mut out = vec![vec![Complex64::zero(); n]; n];
    for (i, row) in a.iter().enumerate() {
        for (j, value) in row.iter().enumerate() {
            out[j][i] = Complex64 {
                re: value.re,
                im: -value.im,
            };
        }
    }
    out
}

fn projectively_approx_eq(a: &[Vec<Complex64>], b: &[Vec<Complex64>]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut scalar = None;
    for (ra, rb) in a.iter().zip(b) {
        if ra.len() != rb.len() {
            return false;
        }
        for (x, y) in ra.iter().zip(rb) {
            if y.abs() > TOL {
                let denom = y.re * y.re + y.im * y.im;
                scalar = Some(Complex64 {
                    re: (x.re * y.re + x.im * y.im) / denom,
                    im: (x.im * y.re - x.re * y.im) / denom,
                });
                break;
            }
            if x.abs() > TOL {
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
            .all(|(x, y)| x.approx_eq(&scalar.mul(y), TOL))
    })
}

fn conjugates_projectively(
    operator: &[Vec<Complex64>],
    source: &[Vec<Complex64>],
    target: &[Vec<Complex64>],
) -> bool {
    let inverse = conjugate_transpose(operator);
    let conjugated = mat_mul(&mat_mul(operator, source), &inverse);
    projectively_approx_eq(&conjugated, target)
}

fn position_mask(mask: usize, rank: usize) -> u128 {
    let mut out = 0u128;
    for i in 0..rank {
        if (mask >> i) & 1 == 1 {
            out |= 1u128 << (2 * i);
        }
    }
    out
}

fn momentum_mask(mask: usize, rank: usize) -> u128 {
    let mut out = 0u128;
    for i in 0..rank {
        if (mask >> i) & 1 == 1 {
            out |= 1u128 << (2 * i + 1);
        }
    }
    out
}

fn hyperbolic_phase_space(rank: usize) -> Option<HeisenbergWeilRepresentation> {
    let dim = rank.checked_mul(2)?;
    if dim > 128 || rank == 0 {
        return None;
    }
    let mut bmat = vec![0u128; dim];
    for i in 0..rank {
        let x = 2 * i;
        let y = x + 1;
        bmat[x] |= 1u128 << y;
        bmat[y] |= 1u128 << x;
    }
    extraspecial_group_f2(vec![false; dim], bmat)
        .ok()?
        .heisenberg_weil_representation()
}

fn two_times_mod_two(x: &Rational) -> Option<bool> {
    let doubled = x.add(x);
    doubled
        .is_integer()
        .then_some(doubled.numer().rem_euclid(2) == 1)
}

impl DiscriminantForm {
    /// Compare the discriminant `S,T` matrices with the Schrödinger/Heisenberg
    /// operators on `A (+) A*` when `A` is a nontrivial 2-elementary group.
    ///
    /// Returns `None` outside that exact overlap, for the trivial discriminant
    /// group, or past the existing dense-matrix/group-table cap.  Higher
    /// 2-power and odd-primary modules require generalized finite Heisenberg
    /// groups and are deliberately not coerced into this binary adapter.
    pub fn two_elementary_weil_heisenberg(&self) -> Option<TwoElementaryWeilHeisenbergInvariants> {
        if self.group().is_empty() || !self.group().iter().all(|&d| d == 2) {
            return None;
        }
        let tables = self.tables_bounded(256)?;
        if tables.order.iter().any(|&order| order != 1 && order != 2) {
            return None;
        }
        let generators = min_generators(&tables);
        let rank = generators.len();
        let order = 1usize.checked_shl(u32::try_from(rank).ok()?)?;
        if order != tables.order.len() {
            return None;
        }

        // Reindex the HNF representatives by F2 coordinates in the selected
        // group basis.  `indices[mask]` is the original representative index.
        let mut indices = vec![tables.zero; order];
        for mask in 0..order {
            let mut index = tables.zero;
            for (bit, &generator) in generators.iter().enumerate() {
                if (mask >> bit) & 1 == 1 {
                    index = tables.add[index][generator];
                }
            }
            indices[mask] = index;
        }
        let mut unique = indices.clone();
        unique.sort_unstable();
        unique.dedup();
        if unique.len() != order {
            return None;
        }

        // The perfect discriminant pairing identifies y in A with the
        // character x |-> (-1)^B(y,x).  `dual[y]` is that character in the
        // coordinate dual basis.
        let mut dual = vec![0usize; order];
        for y in 0..order {
            for i in 0..rank {
                let value = self.bilinear_value_mod1(
                    &self.reps()[indices[y]],
                    &self.reps()[indices[1usize << i]],
                );
                if two_times_mod_two(&value)? {
                    dual[y] |= 1usize << i;
                }
            }
        }
        let mut dual_inverse = vec![usize::MAX; order];
        for (x, &character) in dual.iter().enumerate() {
            if character >= order || dual_inverse[character] != usize::MAX {
                return None;
            }
            dual_inverse[character] = x;
        }
        if dual_inverse.contains(&usize::MAX) {
            return None;
        }

        let rep = hyperbolic_phase_space(rank)?;
        let standard_fourier = rep.fourier_intertwiner()?;
        if !rep.verify_fourier_intertwines() {
            return None;
        }
        let mut heisenberg_s = vec![vec![Complex64::zero(); order]; order];
        for row in 0..order {
            heisenberg_s[row].clone_from_slice(&standard_fourier[dual[row]]);
        }

        let raw_s = self.weil_s()?;
        let raw_t = self.weil_t();
        let mut disc_s = vec![vec![Complex64::zero(); order]; order];
        let mut disc_t = vec![vec![Complex64::zero(); order]; order];
        for row in 0..order {
            for col in 0..order {
                disc_s[row][col] = raw_s[indices[row]][indices[col]];
            }
            disc_t[row][row] = raw_t[indices[row]];
        }

        let milgram_scalar = Complex64::eighth_root(self.weil_s_prefactor_phase_mod8()?);
        let expected_s = mat_scale(&heisenberg_s, milgram_scalar);
        let s_matches = mat_approx_eq(&disc_s, &expected_s, TOL);

        let mut expected_t = vec![vec![Complex64::zero(); order]; order];
        for mask in 0..order {
            let q = self.quadratic_value_mod2(&self.reps()[indices[mask]]);
            let theta = std::f64::consts::PI * (q.numer() as f64) / (q.denom() as f64);
            expected_t[mask][mask] = Complex64::cis(theta);
        }
        let t_matches = mat_approx_eq(&disc_t, &expected_t, TOL);

        let mut s_intertwines = true;
        let mut t_intertwines = true;
        for i in 0..rank {
            let position = 1usize << i;
            let character = dual[position];
            let x = rep.group().element(false, position_mask(position, rank))?;
            let z = rep.group().element(false, momentum_mask(character, rank))?;
            let xz = rep.group().element(
                false,
                position_mask(position, rank) | momentum_mask(character, rank),
            )?;
            s_intertwines &= conjugates_projectively(&disc_s, &rep.matrix(&x)?, &rep.matrix(&z)?);
            t_intertwines &= conjugates_projectively(&disc_t, &rep.matrix(&x)?, &rep.matrix(&xz)?);

            let momentum = 1usize << i;
            let source_z = rep.group().element(false, momentum_mask(momentum, rank))?;
            let target_x = rep
                .group()
                .element(false, position_mask(dual_inverse[momentum], rank))?;
            s_intertwines &=
                conjugates_projectively(&disc_s, &rep.matrix(&source_z)?, &rep.matrix(&target_x)?);
            t_intertwines &=
                conjugates_projectively(&disc_t, &rep.matrix(&source_z)?, &rep.matrix(&source_z)?);
        }

        Some(TwoElementaryWeilHeisenbergInvariants {
            rank,
            order,
            s_matches,
            t_matches,
            s_intertwines,
            t_intertwines,
            metaplectic_relations: self.verify_weil_relations(),
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::forms::{a_n, d_n, e_7, e_8, DiscriminantForm};

    #[test]
    fn ade_two_elementary_discriminant_modules_match_doubled_heisenberg_models() {
        for lattice in [a_n(1).unwrap(), d_n(4).unwrap(), d_n(8).unwrap(), e_7()] {
            let disc = DiscriminantForm::from_lattice(&lattice).unwrap();
            let report = disc
                .two_elementary_weil_heisenberg()
                .expect("nontrivial 2-elementary discriminant module");
            assert!(report.verified(), "failed report: {report:?}");
            assert_eq!(report.order, disc.reps().len());
            assert_eq!(report.order, 1usize << report.rank);
        }
    }

    #[test]
    fn adapter_declines_outside_nontrivial_two_elementary_overlap() {
        assert_eq!(
            DiscriminantForm::from_lattice(&a_n(2).unwrap())
                .unwrap()
                .two_elementary_weil_heisenberg(),
            None,
        );
        assert_eq!(
            DiscriminantForm::from_lattice(&a_n(3).unwrap())
                .unwrap()
                .two_elementary_weil_heisenberg(),
            None,
        );
        assert_eq!(
            DiscriminantForm::from_lattice(&e_8())
                .unwrap()
                .two_elementary_weil_heisenberg(),
            None,
        );
    }

    #[test]
    fn report_display_pins_the_projective_comparison() {
        let report = DiscriminantForm::from_lattice(&a_n(1).unwrap())
            .unwrap()
            .two_elementary_weil_heisenberg()
            .unwrap();
        assert_eq!(
            report.to_string(),
            "TwoElementaryWeilHeisenbergInvariants(rank=1, order=2, s_matches=true, t_matches=true, s_intertwines=true, t_intertwines=true, metaplectic_relations=true, verified=true)",
        );
        assert_eq!(report.display(), report.to_string());
    }
}
