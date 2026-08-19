//! Blade-mask primitives shared by the whole engine and by the
//! structured-algebra layer above it: `bits`/`grade` decode a `u128` blade
//! mask, `MAX_BASIS_DIM` caps the basis at 128 generators, `grade_k_masks` is
//! the one grade-`k` blade-mask enumerator (Gosper's hack, ascending order)
//! shared by `blade.rs` and `outermorphism.rs`, and `wedge_sign` reads off the
//! antisymmetric reordering sign of two disjoint ascending blades through the
//! scalar's own `neg()` — never a literal `-1`, so char-2 sign-vanishing falls
//! out for free.

use crate::scalar::Scalar;

/// Blade masks are `u128`, so the basis has at most 128 named generators.
pub const MAX_BASIS_DIM: usize = 128;

/// All `u128` bitmasks with exactly `k` bits set among the first `n` bits,
/// enumerated by Gosper's hack in ascending numerical order (`C(n,k)` masks).
pub(crate) fn grade_k_masks(n: usize, k: usize) -> Vec<u128> {
    if k == 0 {
        return vec![0];
    }
    if k > n {
        return vec![];
    }
    assert!(n <= u128::BITS as usize, "basis masks fit in u128");
    if k == u128::BITS as usize {
        return vec![u128::MAX];
    }
    let mut out = Vec::new();
    let mut c: u128 = (1u128 << k) - 1;
    let limit = (n < u128::BITS as usize).then(|| 1u128 << n);
    loop {
        out.push(c);
        let u = c & c.wrapping_neg();
        let v = c.checked_add(u);
        match v {
            Some(v) if v != 0 => {
                let next = v + (((v ^ c) / u) >> 2);
                if limit.is_some_and(|lim| next >= lim) {
                    break;
                }
                c = next;
            }
            _ => break,
        }
    }
    out
}

/// Iterate over set-bit indices of a blade mask in ascending order without
/// allocating.
pub(crate) fn bit_indices(mut mask: u128) -> impl Iterator<Item = usize> {
    std::iter::from_fn(move || {
        if mask == 0 {
            return None;
        }
        let index = mask.trailing_zeros() as usize;
        mask &= mask - 1;
        Some(index)
    })
}

/// Ascending list of set-bit indices of a blade mask.
pub fn bits(mask: u128) -> Vec<usize> {
    bit_indices(mask).collect()
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
