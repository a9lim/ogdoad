use crate::scalar::Scalar;

/// Blade masks are `u128`, so the basis has at most 128 named generators.
pub const MAX_BASIS_DIM: usize = 128;

/// Ascending list of set-bit indices of a blade mask.
pub fn bits(mask: u128) -> Vec<usize> {
    let mut v = Vec::new();
    let mut m = mask;
    while m != 0 {
        let i = m.trailing_zeros() as usize;
        v.push(i);
        m &= m - 1;
    }
    v
}

/// The grade (number of generators) of a blade mask.
pub fn grade(mask: u128) -> usize {
    mask.count_ones() as usize
}

/// Sign (+1/-1 as a Scalar) of reordering two disjoint ascending blades when
/// concatenated — i.e. the number of (i in a, j in b) with i > j, mod 2.
pub(super) fn wedge_sign<S: Scalar>(a: u128, b: u128) -> S {
    let mut swaps = 0usize;
    let mut aa = a;
    while aa != 0 {
        let i = aa.trailing_zeros() as usize;
        aa &= aa - 1;
        let below = b & ((1u128 << i) - 1);
        swaps += below.count_ones() as usize;
    }
    if swaps & 1 == 0 {
        S::one()
    } else {
        S::one().neg()
    }
}
