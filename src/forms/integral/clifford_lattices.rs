//! Barnes-Wall lattices from the real Clifford-module side.
//!
//! The code-lattice side already builds `BW16` as Construction D from
//! `RM(0,4) <= RM(2,4)`. This module gives the reverse bridge promised by the
//! Clifford story: start with the real spinor module with weight basis indexed
//! by `F_2^4`, add the quadratic-phase rows coming from the degree-`<= 2`
//! functions on that basis, and recover the same integral lattice.

use super::codes::{barnes_wall_16, divided_lattice_from_rows, reed_muller_code};
use super::lattice::IntegralForm;

/// The spinor dimension in the shipped Barnes-Wall/Clifford certificate.
pub const BW16_CLIFFORD_SPINOR_DIMENSION: usize = 16;

/// The row-divisor in the integer numerator model for the Clifford-side `BW16`.
pub const BW16_CLIFFORD_ROW_DIVISOR: i128 = 4;

/// `|Aut(BW16)| = 2^21 * 3^5 * 5^2 * 7`.
///
/// This is the index-2 real Clifford/Bolt-Room-Wall subgroup stabilizing the
/// usual Barnes-Wall lattice in dimension 16.
pub const BW16_AUTOMORPHISM_GROUP_ORDER: u128 = 89_181_388_800;

/// The full real Clifford group `C_4` has structure
/// `2_+^(1+8).O^+(8,2)` and contains `Aut(BW16)` with index `2`.
pub const BW16_REAL_CLIFFORD_GROUP_ORDER: u128 = 178_362_777_600;

/// The index of `Aut(BW16)` in the full real Clifford group `C_4`.
pub const BW16_AUTOMORPHISM_INDEX_IN_CLIFFORD_GROUP: u128 = 2;

/// Verification record for the Clifford-side construction of `BW16`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CliffordBarnesWall16Report {
    pub lattice: IntegralForm,
    pub construction_d_lattice: IntegralForm,
    pub spinor_dimension: usize,
    pub row_divisor: i128,
    pub quadratic_phase_row_count: usize,
    pub coordinate_weight_row_count: usize,
    pub matches_construction_d: bool,
    pub automorphism_group_order: u128,
    pub full_clifford_group_order: u128,
    pub automorphism_index_in_clifford_group: u128,
}

impl CliffordBarnesWall16Report {
    /// The determinant of the Clifford-side lattice.
    pub fn determinant(&self) -> i128 {
        self.lattice.determinant()
    }

    /// The minimum norm, when the positive-definite geometry search applies.
    pub fn minimum(&self) -> Option<i128> {
        self.lattice.minimum()
    }

    /// The kissing number, when the positive-definite geometry search applies.
    pub fn kissing_number(&self) -> Option<usize> {
        self.lattice.kissing_number()
    }

    /// Whether the source-pinned group-order constants have the expected
    /// index-2 relation.
    pub fn recorded_group_orders_are_consistent(&self) -> bool {
        self.automorphism_group_order
            .checked_mul(self.automorphism_index_in_clifford_group)
            == Some(self.full_clifford_group_order)
    }
}

/// Integer numerator rows for the Clifford-side `BW16` certificate.
///
/// The actual lattice vectors are these rows divided by
/// `sqrt(BW16_CLIFFORD_ROW_DIVISOR) = 2`. The first row is the zero quadratic
/// phase, the next rows are signs `1 - 2q` for a row basis of `RM(2,4)`, and
/// the final sixteen rows are the `4e_x` coordinate weight rows of the spinor
/// module. Their `Z`-span is the same numerator lattice as
/// `RM(0,4) <= RM(2,4)` Construction D.
pub fn clifford_barnes_wall_16_numerator_rows() -> Vec<Vec<i128>> {
    let rm2 = reed_muller_code(2, 4).expect("RM(2,4) exists");
    let mut rows = Vec::with_capacity(1 + rm2.dim() + BW16_CLIFFORD_SPINOR_DIMENSION);

    rows.push(vec![1i128; BW16_CLIFFORD_SPINOR_DIMENSION]);
    for row in rm2.generators() {
        rows.push(
            row.iter()
                .map(|&bit| 1i128 - 2i128 * i128::from(bit))
                .collect(),
        );
    }
    for i in 0..BW16_CLIFFORD_SPINOR_DIMENSION {
        let mut row = vec![0i128; BW16_CLIFFORD_SPINOR_DIMENSION];
        row[i] = BW16_CLIFFORD_ROW_DIVISOR;
        rows.push(row);
    }

    rows
}

/// The Barnes-Wall lattice `BW16`, built from the Clifford/spinor-module rows.
pub fn clifford_barnes_wall_16() -> IntegralForm {
    divided_lattice_from_rows(
        clifford_barnes_wall_16_numerator_rows(),
        BW16_CLIFFORD_SPINOR_DIMENSION,
        BW16_CLIFFORD_ROW_DIVISOR,
    )
    .expect("Clifford BW16 rows give an integral full-rank lattice")
}

/// Build the Clifford-side `BW16` and compare it with the Reed-Muller
/// Construction-D route.
pub fn clifford_barnes_wall_16_report() -> CliffordBarnesWall16Report {
    let lattice = clifford_barnes_wall_16();
    let construction_d_lattice = barnes_wall_16();
    let rows = clifford_barnes_wall_16_numerator_rows();
    let coordinate_weight_row_count = BW16_CLIFFORD_SPINOR_DIMENSION;
    let quadratic_phase_row_count = rows.len() - coordinate_weight_row_count;
    let matches_construction_d = lattice.gram() == construction_d_lattice.gram();

    CliffordBarnesWall16Report {
        lattice,
        construction_d_lattice,
        spinor_dimension: BW16_CLIFFORD_SPINOR_DIMENSION,
        row_divisor: BW16_CLIFFORD_ROW_DIVISOR,
        quadratic_phase_row_count,
        coordinate_weight_row_count,
        matches_construction_d,
        automorphism_group_order: BW16_AUTOMORPHISM_GROUP_ORDER,
        full_clifford_group_order: BW16_REAL_CLIFFORD_GROUP_ORDER,
        automorphism_index_in_clifford_group: BW16_AUTOMORPHISM_INDEX_IN_CLIFFORD_GROUP,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clifford_rows_recover_construction_d_barnes_wall_16() {
        let rows = clifford_barnes_wall_16_numerator_rows();
        assert_eq!(rows.len(), 28);
        assert_eq!(rows[0], vec![1; BW16_CLIFFORD_SPINOR_DIMENSION]);

        let bw = clifford_barnes_wall_16();
        assert_eq!(bw.gram(), barnes_wall_16().gram());
        assert_eq!(bw.dim(), 16);
        assert!(bw.is_even());
        assert_eq!(bw.determinant(), 256);
        assert_eq!(bw.minimum(), Some(4));
        assert_eq!(bw.kissing_number(), Some(4320));
    }

    #[test]
    fn clifford_barnes_wall_report_pins_the_group_order_boundary() {
        let report = clifford_barnes_wall_16_report();
        assert!(report.matches_construction_d);
        assert_eq!(report.quadratic_phase_row_count, 12);
        assert_eq!(report.coordinate_weight_row_count, 16);
        assert_eq!(report.determinant(), 256);
        assert_eq!(report.minimum(), Some(4));
        assert_eq!(report.kissing_number(), Some(4320));
        assert!(report.recorded_group_orders_are_consistent());
        assert_eq!(
            report.automorphism_group_order * report.automorphism_index_in_clifford_group,
            report.full_clifford_group_order
        );
    }
}
