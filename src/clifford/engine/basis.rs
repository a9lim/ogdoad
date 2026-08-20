//! Blade-mask primitives shared by the whole engine and by the
//! structured-algebra layer above it: `bits`/`grade` decode a `u128` blade
//! mask, `MAX_BASIS_DIM` caps the basis at 128 generators, `grade_k_masks` is
//! the one grade-`k` blade-mask enumerator (Gosper's hack, ascending order)
//! shared by `blade.rs` and `outermorphism.rs`, and `wedge_is_negative` reads
//! off the antisymmetric reordering parity of two disjoint ascending blades.

/// Blade masks are `u128`, so the basis has at most 128 named generators.
pub const MAX_BASIS_DIM: usize = 128;

/// Iterate over all `u128` bitmasks with exactly `k` bits set among the first
/// `n` bits. Gosper's hack yields ascending numerical order without allocating
/// the `C(n,k)`-element mask set.
pub(crate) fn grade_k_masks(n: usize, k: usize) -> impl Iterator<Item = u128> {
    let mut current = if k == 0 {
        Some(0)
    } else if k > n {
        None
    } else {
        assert!(n <= u128::BITS as usize, "basis masks fit in u128");
        Some(if k == u128::BITS as usize {
            u128::MAX
        } else {
            (1u128 << k) - 1
        })
    };
    let limit = (n < u128::BITS as usize).then(|| 1u128 << n);
    std::iter::from_fn(move || {
        let c = current?;
        if c == 0 {
            current = None;
            return Some(c);
        }
        let u = c & c.wrapping_neg();
        let v = c.checked_add(u);
        current = match v {
            Some(v) if v != 0 => {
                let next = v + (((v ^ c) / u) >> 2);
                if limit.is_some_and(|lim| next >= lim) {
                    None
                } else {
                    Some(next)
                }
            }
            _ => None,
        };
        Some(c)
    })
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

/// Whether reordering two disjoint ascending blades when concatenated has odd
/// parity — i.e. the number of `(i in a, j in b)` with `i > j`, mod 2.
pub(super) fn wedge_is_negative(a: u128, b: u128) -> bool {
    // Parallel prefix XOR turns bit i into the parity of b's bits 0..=i.
    // Shifting once therefore gives, at each bit of a, the parity of the b
    // indices strictly below it. Their dot product over F_2 is the swap parity.
    let mut prefix_parity = b;
    prefix_parity ^= prefix_parity << 1;
    prefix_parity ^= prefix_parity << 2;
    prefix_parity ^= prefix_parity << 4;
    prefix_parity ^= prefix_parity << 8;
    prefix_parity ^= prefix_parity << 16;
    prefix_parity ^= prefix_parity << 32;
    prefix_parity ^= prefix_parity << 64;
    (a & (prefix_parity << 1)).count_ones() & 1 == 1
}
