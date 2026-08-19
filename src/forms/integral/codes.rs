//! Finite linear codes and Construction A lattices.
//!
//! This is the finite-code side of the integral lattice story. A binary code
//! `C <= F_2^n` has three compatible readings here:
//!
//! * as a checked F2 row space, with duals and exact weight enumerators;
//! * as a source of integral lattices through Constructions A, B, and D;
//! * as an exact theta-series oracle through the Hamming weight enumerator.
//!
//! The `1/sqrt(2)` scale is part of the construction. Since [`IntegralForm`]
//! stores an integer Gram matrix, [`BinaryCode::construction_a`] returns `None`
//! unless the resulting Gram is integral; self-orthogonal codes satisfy that
//! boundary. Type I self-dual codes give odd unimodular lattices, while Type II
//! self-dual codes give even unimodular lattices. The same explicit integer-Gram
//! boundary is used for Construction B and the scaled nested-code Construction D.
//! The generated Reed-Muller family supplies the classical nested towers; in
//! the scaled Construction-D convention used here, `RM(0,4) <= RM(2,4)` gives
//! the determinant-256 Barnes-Wall lattice `BW16`.
//!
//! Odd-prime codes use [`PrimeCode`]. Their Construction A is the direct
//! `p`-ary analogue `(1/sqrt(p)){x in Z^n : x mod p in C}`; it is an
//! integer lattice exactly on the Euclidean self-orthogonal boundary. The
//! ternary Golay code gives the odd unimodular rank-12 `Z`-lattice attached to
//! this construction. This module does not implement the Eisenstein-integer
//! Construction A needed for the Coxeter--Todd `K12` lattice.

use super::lattice::IntegralForm;
use crate::linalg::integer::normalize_relation_rows;
use crate::scalar::{Fp, Scalar};
use std::collections::BTreeMap;

/// `|Aut(D16+)| = 2^15 * 16!`.
pub const D16_PLUS_AUT_ORDER: u128 = 685_597_979_049_984_000;

/// Codeword enumeration is exponential in the code dimension `k` (`2^k` binary
/// words, `P^k` over [`PrimeCode`]). Enumeration is capped at this many codewords
/// rather than silently overflowing a `usize` mask or running unbounded — the
/// same budget-`None` shape as the lattice wing's `AUTO_NODE_BUDGET`.
pub const CODEWORD_ENUMERATION_BUDGET: usize = 2_000_000;

/// A binary linear code, stored as a row-reduced F2 generator matrix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryCode {
    n: usize,
    generators: Vec<PackedBinaryRow>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PackedBinaryRow {
    words: Box<[u64]>,
}

impl PackedBinaryRow {
    fn from_bytes(row: &[u8]) -> Self {
        let mut words = vec![0u64; row.len().div_ceil(64)];
        for (column, &bit) in row.iter().enumerate() {
            words[column / 64] |= u64::from(bit) << (column % 64);
        }
        PackedBinaryRow {
            words: words.into_boxed_slice(),
        }
    }

    fn bit(&self, column: usize) -> u8 {
        ((self.words[column / 64] >> (column % 64)) & 1) as u8
    }

    fn first_one(&self) -> Option<usize> {
        self.words
            .iter()
            .enumerate()
            .find_map(|(word_index, &word)| {
                (word != 0).then(|| word_index * 64 + word.trailing_zeros() as usize)
            })
    }

    fn weight(&self) -> usize {
        self.words
            .iter()
            .map(|word| word.count_ones() as usize)
            .sum()
    }

    fn dot(&self, other: &PackedBinaryRow) -> u8 {
        (self
            .words
            .iter()
            .zip(&other.words)
            .fold(0u32, |parity, (&a, &b)| parity ^ (a & b).count_ones())
            & 1) as u8
    }

    fn to_bytes(&self, n: usize) -> Vec<u8> {
        (0..n).map(|column| self.bit(column)).collect()
    }
}

fn pow2_i128(exp: usize) -> Option<i128> {
    if exp >= 127 {
        None
    } else {
        Some(1i128 << exp)
    }
}

fn pow_i128_checked(mut base: i128, mut exp: usize) -> Option<i128> {
    let mut acc = 1i128;
    while exp > 0 {
        if exp & 1 == 1 {
            acc = acc.checked_mul(base)?;
        }
        exp >>= 1;
        if exp > 0 {
            base = base.checked_mul(base)?;
        }
    }
    Some(acc)
}

fn fp_add<const P: u128>(a: u128, b: u128) -> u128 {
    Fp::<P>::from_u128(a).add(&Fp::<P>::from_u128(b)).value()
}

fn fp_mul<const P: u128>(a: u128, b: u128) -> u128 {
    Fp::<P>::from_u128(a).mul(&Fp::<P>::from_u128(b)).value()
}

fn fp_neg<const P: u128>(a: u128) -> u128 {
    Fp::<P>::from_u128(a).neg().value()
}

fn fp_inv<const P: u128>(a: u128) -> u128 {
    Fp::<P>::from_u128(a)
        .inv()
        .expect("nonzero prime-field element is invertible")
        .value()
}

fn normalize_generators(mut rows: Vec<Vec<u8>>, n: usize) -> Option<Vec<Vec<u8>>> {
    if rows
        .iter()
        .any(|row| row.len() != n || row.iter().any(|&x| x > 1))
    {
        return None;
    }
    rows.retain(|row| row.iter().any(|&x| x != 0));
    let mut rank = 0usize;
    for col in 0..n {
        let Some(pivot) = (rank..rows.len()).find(|&r| rows[r][col] != 0) else {
            continue;
        };
        rows.swap(rank, pivot);
        let pivot_row = rows[rank].clone();
        for r in 0..rows.len() {
            if r == rank || rows[r][col] == 0 {
                continue;
            }
            for c in col..n {
                rows[r][c] ^= pivot_row[c];
            }
        }
        rank += 1;
        if rank == rows.len() {
            break;
        }
    }
    rows.truncate(rank);
    Some(rows)
}

fn normalize_generators_mod_p<const P: u128>(
    mut rows: Vec<Vec<u128>>,
    n: usize,
) -> Option<Vec<Vec<u128>>> {
    if P == 2 || !Fp::<P>::modulus_is_prime() {
        return None;
    }
    if rows
        .iter()
        .any(|row| row.len() != n || row.iter().any(|&x| x >= P))
    {
        return None;
    }
    rows.retain(|row| row.iter().any(|&x| x != 0));
    let mut rank = 0usize;
    for col in 0..n {
        let Some(pivot) = (rank..rows.len()).find(|&r| rows[r][col] != 0) else {
            continue;
        };
        rows.swap(rank, pivot);
        let inv = fp_inv::<P>(rows[rank][col]);
        for c in col..n {
            rows[rank][c] = fp_mul::<P>(rows[rank][c], inv);
        }
        let pivot_row = rows[rank].clone();
        for r in 0..rows.len() {
            if r == rank || rows[r][col] == 0 {
                continue;
            }
            let factor = fp_neg::<P>(rows[r][col]);
            for c in col..n {
                rows[r][c] = fp_add::<P>(rows[r][c], fp_mul::<P>(factor, pivot_row[c]));
            }
        }
        rank += 1;
        if rank == rows.len() {
            break;
        }
    }
    rows.truncate(rank);
    Some(rows)
}

fn rows_from_strings(rows: &[&str]) -> Vec<Vec<u8>> {
    rows.iter()
        .map(|row| {
            row.bytes()
                .map(|b| match b {
                    b'0' => 0,
                    b'1' => 1,
                    _ => panic!("binary generator rows must contain only 0/1"),
                })
                .collect()
        })
        .collect()
}

/// `binomial(n, k)`, `None` on `i128` overflow. The crate's one binomial-coefficient
/// recurrence; [`binomial`] and [`binomial_usize_checked`] are thin wrappers over it.
fn binomial_checked(n: usize, k: usize) -> Option<i128> {
    if k > n {
        return Some(0);
    }
    let k = k.min(n - k);
    let mut out = 1i128;
    for i in 1..=k {
        out = out.checked_mul((n - k + i) as i128)? / i as i128;
    }
    Some(out)
}

fn binomial(n: usize, k: usize) -> i128 {
    binomial_checked(n, k).expect("binomial coefficient exceeds i128")
}

fn binomial_usize_checked(n: usize, k: usize) -> Option<usize> {
    usize::try_from(binomial_checked(n, k)?).ok()
}

fn convolve_i128(a: &[i128], b: &[i128], terms: usize) -> Vec<i128> {
    let mut out = vec![0i128; terms];
    for (i, &ai) in a.iter().enumerate().take(terms) {
        if ai == 0 {
            continue;
        }
        for (j, &bj) in b.iter().enumerate().take(terms - i) {
            if bj == 0 {
                continue;
            }
            out[i + j] = out[i + j]
                .checked_add(ai.checked_mul(bj).expect("series coefficient exceeds i128"))
                .expect("series coefficient exceeds i128");
        }
    }
    out
}

fn series_pow_i128(base: &[i128], exp: usize, terms: usize) -> Vec<i128> {
    let mut out = vec![0i128; terms];
    if terms == 0 {
        return out;
    }
    out[0] = 1;
    for _ in 0..exp {
        out = convolve_i128(&out, base, terms);
    }
    out
}

fn even_residue_theta(terms: usize) -> Vec<i128> {
    let mut out = vec![0i128; terms];
    if terms == 0 {
        return out;
    }
    out[0] = 1;
    let mut m = 1usize;
    while m * m < terms {
        out[m * m] += 2;
        m += 1;
    }
    out
}

fn odd_residue_theta_without_quarter(terms: usize) -> Vec<i128> {
    let mut out = vec![0i128; terms];
    let mut m = 0usize;
    while m * (m + 1) < terms {
        out[m * (m + 1)] += 2; // m and -m-1.
        m += 1;
    }
    out
}

pub(super) fn divided_lattice_from_rows(
    rows: Vec<Vec<i128>>,
    n: usize,
    divisor: i128,
) -> Option<IntegralForm> {
    debug_assert!(divisor > 0);
    let basis = normalize_relation_rows(rows);
    if basis.len() != n {
        return None;
    }
    let mut gram = vec![vec![0i128; n]; n];
    for i in 0..n {
        for j in 0..n {
            let mut dot = 0i128;
            for k in 0..n {
                dot = dot
                    .checked_add(
                        basis[i][k]
                            .checked_mul(basis[j][k])
                            .expect("code-lattice Gram entry exceeds i128"),
                    )
                    .expect("code-lattice Gram entry exceeds i128");
            }
            if dot % divisor != 0 {
                return None;
            }
            gram[i][j] = dot / divisor;
        }
    }
    IntegralForm::new(gram)
}

impl BinaryCode {
    /// Build a binary code from generator rows. The stored basis is row-reduced
    /// over F2, so equivalent generator matrices compare equal.
    pub fn new(n: usize, generators: Vec<Vec<u8>>) -> Option<Self> {
        let generators = normalize_generators(generators, n)?
            .iter()
            .map(|row| PackedBinaryRow::from_bytes(row))
            .collect();
        Some(BinaryCode { n, generators })
    }

    /// The block length `n`.
    pub fn len(&self) -> usize {
        self.n
    }

    /// Whether the code has block length zero.
    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    /// The dimension `k`.
    pub fn dim(&self) -> usize {
        self.generators.len()
    }

    /// Row-reduced generator rows, unpacked to binary bytes.
    pub fn generators(&self) -> Vec<Vec<u8>> {
        self.generators
            .iter()
            .map(|row| row.to_bytes(self.n))
            .collect()
    }

    /// The number of codewords, `2^k`, when it fits the crate's `u128` payload.
    pub fn size(&self) -> Option<u128> {
        if self.dim() >= 128 {
            None
        } else {
            Some(1u128 << self.dim())
        }
    }

    /// Visits every codeword in Gray-code order while reusing one word buffer.
    /// Returns `None` past [`CODEWORD_ENUMERATION_BUDGET`].
    fn for_each_codeword(&self, mut visit: impl FnMut(&[u64])) -> Option<()> {
        let size = 1usize
            .checked_shl(self.dim() as u32)
            .filter(|&s| s <= CODEWORD_ENUMERATION_BUDGET)?;
        let mut word = vec![0u64; self.n.div_ceil(64)];
        visit(&word);
        for step in 1..size {
            let changed_row = step.trailing_zeros() as usize;
            for (x, &g) in word.iter_mut().zip(&self.generators[changed_row].words) {
                *x ^= g;
            }
            visit(&word);
        }
        Some(())
    }

    /// The dual code `C^perp = {x : x dot c = 0 for all c in C}`.
    pub fn dual(&self) -> BinaryCode {
        let mut pivot_for_row = Vec::new();
        let mut is_pivot = vec![false; self.n];
        for row in &self.generators {
            if let Some(p) = row.first_one() {
                pivot_for_row.push(p);
                is_pivot[p] = true;
            }
        }

        let mut dual_rows = Vec::new();
        for free in 0..self.n {
            if is_pivot[free] {
                continue;
            }
            let mut v = vec![0u8; self.n];
            v[free] = 1;
            for (r, &pivot) in pivot_for_row.iter().enumerate() {
                v[pivot] = self.generators[r].bit(free);
            }
            dual_rows.push(v);
        }
        BinaryCode::new(self.n, dual_rows).expect("dual rows have the same length")
    }

    /// The block direct sum `C ⊕ D`.
    pub fn direct_sum(&self, other: &BinaryCode) -> BinaryCode {
        let mut rows = Vec::with_capacity(self.dim() + other.dim());
        for row in &self.generators {
            let mut out = vec![0u8; self.n + other.n];
            out[..self.n].copy_from_slice(&row.to_bytes(self.n));
            rows.push(out);
        }
        for row in &other.generators {
            let mut out = vec![0u8; self.n + other.n];
            out[self.n..].copy_from_slice(&row.to_bytes(other.n));
            rows.push(out);
        }
        BinaryCode::new(self.n + other.n, rows).expect("direct-sum rows are binary")
    }

    fn contains_word(&self, word: &[u8]) -> bool {
        if word.len() != self.n || word.iter().any(|&x| x > 1) {
            return false;
        }
        let mut remainder = PackedBinaryRow::from_bytes(word).words.into_vec();
        for row in &self.generators {
            let pivot = row.first_one().expect("stored generator row is nonzero");
            if (remainder[pivot / 64] >> (pivot % 64)) & 1 == 0 {
                continue;
            }
            for (target, &word) in remainder.iter_mut().zip(&row.words) {
                *target ^= word;
            }
        }
        remainder.iter().all(|&word| word == 0)
    }

    /// Whether `other <= self` as a binary row space.
    pub fn contains(&self, other: &BinaryCode) -> bool {
        self.n == other.n
            && other
                .generators
                .iter()
                .all(|row| self.contains_word(&row.to_bytes(other.n)))
    }

    /// `C = C^perp`.
    pub fn is_self_dual(&self) -> bool {
        self.dim() * 2 == self.n && self.generators == self.dual().generators
    }

    /// `C <= C^perp`.
    pub fn is_self_orthogonal(&self) -> bool {
        (0..self.dim())
            .all(|i| (i..self.dim()).all(|j| self.generators[i].dot(&self.generators[j]) == 0))
    }

    /// Every codeword has Hamming weight divisible by 4.
    pub fn is_doubly_even(&self) -> bool {
        if self
            .generators
            .iter()
            .any(|row| !row.weight().is_multiple_of(4))
        {
            return false;
        }
        (0..self.dim())
            .all(|i| (i + 1..self.dim()).all(|j| self.generators[i].dot(&self.generators[j]) == 0))
    }

    /// The minimum nonzero Hamming weight, or `None` for the zero code (or past
    /// [`CODEWORD_ENUMERATION_BUDGET`]).
    pub fn minimum_distance(&self) -> Option<usize> {
        let mut minimum = None;
        self.for_each_codeword(|word| {
            let weight: usize = word.iter().map(|word| word.count_ones() as usize).sum();
            if weight > 0 {
                minimum = Some(minimum.map_or(weight, |old: usize| old.min(weight)));
            }
        })?;
        minimum
    }

    /// The Hamming weight enumerator coefficients:
    /// `out[w] = #{c in C : wt(c) = w}`.
    ///
    /// A code dimension past [`CODEWORD_ENUMERATION_BUDGET`] panics
    /// rather than silently truncating the enumerator.
    pub fn weight_enumerator(&self) -> Vec<i128> {
        let mut out = vec![0i128; self.n + 1];
        self.for_each_codeword(|word| {
            let weight: usize = word.iter().map(|word| word.count_ones() as usize).sum();
            out[weight] += 1;
        })
        .expect("code dimension exceeds CODEWORD_ENUMERATION_BUDGET");
        out
    }

    /// The exact MacWilliams transform of the Hamming weight enumerator. The
    /// result is the weight enumerator of `C^perp`.
    pub fn macwilliams_transform(&self) -> Vec<i128> {
        let a = self.weight_enumerator();
        let size = i128::try_from(self.size().expect("code size exceeds u128"))
            .expect("code size exceeds i128");
        let mut out = vec![0i128; self.n + 1];
        for (j, out_j) in out.iter_mut().enumerate() {
            let mut acc = 0i128;
            for (i, &ai) in a.iter().enumerate() {
                if ai == 0 {
                    continue;
                }
                let mut kraw = 0i128;
                for s in 0..=j {
                    let sign = if s % 2 == 0 { 1 } else { -1 };
                    kraw = kraw
                        .checked_add(
                            sign * binomial(i, s)
                                .checked_mul(binomial(self.n - i, j - s))
                                .expect("Krawtchouk coefficient exceeds i128"),
                        )
                        .expect("Krawtchouk coefficient exceeds i128");
                }
                acc = acc
                    .checked_add(ai.checked_mul(kraw).expect("MacWilliams sum exceeds i128"))
                    .expect("MacWilliams sum exceeds i128");
            }
            debug_assert_eq!(acc % size, 0);
            *out_j = acc / size;
        }
        out
    }

    /// Construction A with the standard `1/sqrt(2)` scaling. Returns `None`
    /// exactly when the scaled Gram matrix is not integral.
    pub fn construction_a(&self) -> Option<IntegralForm> {
        let mut rows: Vec<Vec<i128>> = self
            .generators
            .iter()
            .map(|row| row.to_bytes(self.n).into_iter().map(i128::from).collect())
            .collect();
        for i in 0..self.n {
            let mut row = vec![0i128; self.n];
            row[i] = 2;
            rows.push(row);
        }
        divided_lattice_from_rows(rows, self.n, 2)
    }

    /// Construction B:
    ///
    /// `B(C) = (1/sqrt(2)){x in Z^n : x mod 2 in C, sum_i x_i = 0 mod 4}`.
    ///
    /// The input code must be doubly even; the result is still returned through
    /// the same `Option` boundary as [`BinaryCode::construction_a`], so a
    /// non-integral scaled Gram is reported as `None`.
    pub fn construction_b(&self) -> Option<IntegralForm> {
        if !self.is_doubly_even() {
            return None;
        }
        let mut rows: Vec<Vec<i128>> = self
            .generators
            .iter()
            .map(|row| row.to_bytes(self.n).into_iter().map(i128::from).collect())
            .collect();
        match self.n {
            0 => {}
            1 => rows.push(vec![4]),
            n => {
                for i in 0..(n - 1) {
                    let mut row = vec![0i128; n];
                    row[i] = 2;
                    row[i + 1] = -2;
                    rows.push(row);
                }
                let mut row = vec![0i128; n];
                row[n - 2] = 2;
                row[n - 1] = 2;
                rows.push(row);
            }
        }
        divided_lattice_from_rows(rows, self.n, 2)
    }

    /// Compute the Construction A theta series from the Hamming weight
    /// enumerator and the one-dimensional even/odd residue theta series.
    ///
    /// This returns `None` outside the doubly-even boundary, where the
    /// quarter-powers from odd residue classes do not assemble into integer
    /// exponents.
    pub fn theta_series_via_weight_enumerator(&self, terms: usize) -> Option<Vec<i128>> {
        if !self.is_doubly_even() {
            return None;
        }
        if terms == 0 {
            return Some(Vec::new());
        }
        let weights = self.weight_enumerator();
        let even = even_residue_theta(terms);
        let odd = odd_residue_theta_without_quarter(terms);
        let mut out = vec![0i128; terms];
        for (w, &count) in weights.iter().enumerate() {
            if count == 0 {
                continue;
            }
            debug_assert_eq!(w % 4, 0);
            let shift = w / 4;
            if shift >= terms {
                continue;
            }
            let even_part = series_pow_i128(&even, self.n - w, terms - shift);
            let odd_part = series_pow_i128(&odd, w, terms - shift);
            let product = convolve_i128(&even_part, &odd_part, terms - shift);
            for (i, &coeff) in product.iter().enumerate() {
                out[i + shift] = out[i + shift]
                    .checked_add(
                        count
                            .checked_mul(coeff)
                            .expect("Construction A theta coefficient exceeds i128"),
                    )
                    .expect("Construction A theta coefficient exceeds i128");
            }
        }
        Some(out)
    }
}

/// A linear code over the odd prime field `F_P`, stored as a row-reduced
/// generator matrix with entries in `[0, P)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimeCode<const P: u128> {
    n: usize,
    generators: Vec<Vec<u128>>,
}

/// The ternary specialization, used by the Golay witness.
pub type TernaryCode = PrimeCode<3>;

fn dot_mod_p<const P: u128>(a: &[u128], b: &[u128]) -> u128 {
    a.iter()
        .zip(b)
        .fold(0u128, |acc, (&x, &y)| fp_add::<P>(acc, fp_mul::<P>(x, y)))
}

fn row_weight_p(row: &[u128]) -> usize {
    row.iter().filter(|&&x| x != 0).count()
}

fn qary_krawtchouk(q: i128, n: usize, i: usize, j: usize) -> Option<i128> {
    let mut out = 0i128;
    for s in 0..=j.min(i) {
        if j - s > n - i {
            continue;
        }
        let sign = if s % 2 == 0 { 1 } else { -1 };
        let term = binomial_checked(i, s)?
            .checked_mul(binomial_checked(n - i, j - s)?)?
            .checked_mul(pow_i128_checked(q - 1, j - s)?)?;
        out = out.checked_add(sign * term)?;
    }
    Some(out)
}

impl<const P: u128> PrimeCode<P> {
    /// Build an odd-prime-field code from generator rows. The stored basis is
    /// row-reduced over `F_P`, so equivalent generator matrices compare equal.
    pub fn new(n: usize, generators: Vec<Vec<u128>>) -> Option<Self> {
        Some(PrimeCode {
            n,
            generators: normalize_generators_mod_p::<P>(generators, n)?,
        })
    }

    /// The block length `n`.
    pub fn len(&self) -> usize {
        self.n
    }

    /// Whether the code has block length zero.
    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    /// The dimension `k`.
    pub fn dim(&self) -> usize {
        self.generators.len()
    }

    /// Row-reduced generator rows.
    pub fn generators(&self) -> &[Vec<u128>] {
        &self.generators
    }

    /// The number of codewords, `P^k`, when it fits the crate's `u128` payload.
    pub fn size(&self) -> Option<u128> {
        let mut out = 1u128;
        for _ in 0..self.dim() {
            out = out.checked_mul(P)?;
        }
        Some(out)
    }

    /// Visits every codeword in mixed-radix order while reusing one word
    /// buffer. Returns `None` past [`CODEWORD_ENUMERATION_BUDGET`].
    fn for_each_codeword(&self, mut visit: impl FnMut(&[u128])) -> Option<()> {
        let total = self
            .size()
            .and_then(|s| usize::try_from(s).ok())
            .filter(|&s| s <= CODEWORD_ENUMERATION_BUDGET)?;
        let mut coeffs = vec![0u128; self.dim()];
        let mut word = vec![0u128; self.n];
        for ordinal in 0..total {
            visit(&word);
            if ordinal + 1 == total {
                break;
            }
            let mut changed_row = 0usize;
            loop {
                coeffs[changed_row] = fp_add::<P>(coeffs[changed_row], 1);
                for (x, &g) in word.iter_mut().zip(&self.generators[changed_row]) {
                    *x = fp_add::<P>(*x, g);
                }
                if coeffs[changed_row] != 0 {
                    break;
                }
                changed_row += 1;
            }
        }
        Some(())
    }

    fn contains_word(&self, word: &[u128]) -> bool {
        if word.len() != self.n || word.iter().any(|&x| x >= P) {
            return false;
        }
        let mut rows = self.generators.clone();
        rows.push(word.to_vec());
        normalize_generators_mod_p::<P>(rows, self.n).is_some_and(|basis| basis.len() == self.dim())
    }

    /// Whether `other <= self` as an `F_P` row space.
    pub fn contains(&self, other: &PrimeCode<P>) -> bool {
        self.n == other.n && other.generators.iter().all(|row| self.contains_word(row))
    }

    /// The dual code `C^perp = {x : x dot c = 0 for all c in C}`.
    pub fn dual(&self) -> PrimeCode<P> {
        let mut pivot_for_row = Vec::new();
        let mut is_pivot = vec![false; self.n];
        for row in &self.generators {
            if let Some(p) = row.iter().position(|&x| x != 0) {
                pivot_for_row.push(p);
                is_pivot[p] = true;
            }
        }

        let mut dual_rows = Vec::new();
        for free in 0..self.n {
            if is_pivot[free] {
                continue;
            }
            let mut v = vec![0u128; self.n];
            v[free] = 1;
            for (r, &pivot) in pivot_for_row.iter().enumerate() {
                v[pivot] = fp_neg::<P>(self.generators[r][free]);
            }
            dual_rows.push(v);
        }
        PrimeCode::new(self.n, dual_rows).expect("dual rows have the same length")
    }

    /// The block direct sum `C ⊕ D`.
    pub fn direct_sum(&self, other: &PrimeCode<P>) -> PrimeCode<P> {
        let mut rows = Vec::with_capacity(self.dim() + other.dim());
        for row in &self.generators {
            let mut out = vec![0u128; self.n + other.n];
            out[..self.n].copy_from_slice(row);
            rows.push(out);
        }
        for row in &other.generators {
            let mut out = vec![0u128; self.n + other.n];
            out[self.n..].copy_from_slice(row);
            rows.push(out);
        }
        PrimeCode::new(self.n + other.n, rows).expect("direct-sum rows are p-ary")
    }

    /// `C = C^perp`.
    pub fn is_self_dual(&self) -> bool {
        self.dim() * 2 == self.n && self.generators == self.dual().generators
    }

    /// `C <= C^perp` under the Euclidean dot product over `F_P`.
    pub fn is_self_orthogonal(&self) -> bool {
        (0..self.dim()).all(|i| {
            (i..self.dim()).all(|j| dot_mod_p::<P>(&self.generators[i], &self.generators[j]) == 0)
        })
    }

    /// The minimum nonzero Hamming weight, or `None` for the zero code (or past
    /// [`CODEWORD_ENUMERATION_BUDGET`]).
    pub fn minimum_distance(&self) -> Option<usize> {
        let mut minimum = None;
        self.for_each_codeword(|word| {
            let weight = row_weight_p(word);
            if weight > 0 {
                minimum = Some(minimum.map_or(weight, |old: usize| old.min(weight)));
            }
        })?;
        minimum
    }

    /// The Hamming weight enumerator coefficients:
    /// `out[w] = #{c in C : wt(c) = w}`.
    ///
    /// A code dimension past [`CODEWORD_ENUMERATION_BUDGET`] panics
    /// rather than silently truncating the enumerator.
    pub fn weight_enumerator(&self) -> Vec<i128> {
        let mut out = vec![0i128; self.n + 1];
        self.for_each_codeword(|word| out[row_weight_p(word)] += 1)
            .expect("code dimension exceeds CODEWORD_ENUMERATION_BUDGET");
        out
    }

    /// The complete weight enumerator as composition counts.
    ///
    /// A key `[m_0, ..., m_{P-1}]` records how often each field symbol occurs in
    /// a codeword. This is the raw integer-count object; the complete MacWilliams
    /// transform itself lives over cyclotomic coefficients, so the integer
    /// transform exposed here is the Hamming/Krawtchouk specialization.
    pub fn complete_weight_enumerator(&self) -> Option<BTreeMap<Vec<usize>, i128>> {
        let p = usize::try_from(P).ok()?;
        let mut out = BTreeMap::new();
        self.for_each_codeword(|word| {
            let mut counts = vec![0usize; p];
            for x in word {
                counts[*x as usize] += 1;
            }
            *out.entry(counts).or_insert(0) += 1;
        })?;
        Some(out)
    }

    /// The q-ary MacWilliams transform of the Hamming weight enumerator. The
    /// result is the weight enumerator of `C^perp`.
    pub fn macwilliams_transform(&self) -> Option<Vec<i128>> {
        let q = i128::try_from(P).ok()?;
        let a = self.weight_enumerator();
        let size = i128::try_from(self.size()?).ok()?;
        let mut out = vec![0i128; self.n + 1];
        for (j, out_j) in out.iter_mut().enumerate() {
            let mut acc = 0i128;
            for (i, &ai) in a.iter().enumerate() {
                if ai == 0 {
                    continue;
                }
                acc = acc.checked_add(ai.checked_mul(qary_krawtchouk(q, self.n, i, j)?)?)?;
            }
            if acc % size != 0 {
                return None;
            }
            *out_j = acc / size;
        }
        Some(out)
    }

    /// Construction A with the standard `1/sqrt(P)` scaling:
    ///
    /// `A_P(C) = (1/sqrt(P)){x in Z^n : x mod P in C}`.
    ///
    /// Returns `None` exactly when the scaled Gram matrix is not integral.
    pub fn construction_a(&self) -> Option<IntegralForm> {
        let divisor = i128::try_from(P).ok()?;
        let mut rows: Vec<Vec<i128>> = self
            .generators
            .iter()
            .map(|row| {
                row.iter()
                    .map(|&x| i128::try_from(x).expect("field symbol exceeds i128"))
                    .collect()
            })
            .collect();
        for i in 0..self.n {
            let mut row = vec![0i128; self.n];
            row[i] = divisor;
            rows.push(row);
        }
        divided_lattice_from_rows(rows, self.n, divisor)
    }
}

/// The scaled Construction D lattice for an increasing binary-code tower
/// `C0 <= C1 <= ... <= C_{a-1}`:
///
/// `(1/sqrt(2^a)) (C0 + 2 C1 + ... + 2^(a-1) C_{a-1} + 2^a Z^n)`.
///
/// The one-level tower is exactly [`BinaryCode::construction_a`]. The function
/// returns `None` for an empty, unequal-length, non-nested, too-deep, or
/// non-integral tower.
pub fn construction_d(codes: &[BinaryCode]) -> Option<IntegralForm> {
    let first = codes.first()?;
    let n = first.n;
    if codes.iter().any(|code| code.n != n) {
        return None;
    }
    if codes.windows(2).any(|pair| !pair[1].contains(&pair[0])) {
        return None;
    }
    let divisor = pow2_i128(codes.len())?;
    let mut rows = Vec::new();
    for (level, code) in codes.iter().enumerate() {
        let scale = pow2_i128(level)?;
        for row in &code.generators {
            rows.push(
                row.to_bytes(n)
                    .into_iter()
                    .map(|x| scale * i128::from(x))
                    .collect(),
            );
        }
    }
    for i in 0..n {
        let mut row = vec![0i128; n];
        row[i] = divisor;
        rows.push(row);
    }
    divided_lattice_from_rows(rows, n, divisor)
}

/// The binary Reed-Muller code `RM(order, variables)`.
///
/// Generator rows are evaluations of all squarefree monomials of degree at
/// most `order` on `F_2^variables`. Returns `None` when `order > variables` or
/// the explicit generator matrix cannot be allocated.
pub fn reed_muller_code(order: usize, variables: usize) -> Option<BinaryCode> {
    if order > variables {
        return None;
    }
    let shift = u32::try_from(variables).ok()?;
    let n = 1usize.checked_shl(shift)?;
    let mut rows = Vec::new();
    rows.try_reserve_exact(
        (0..=order)
            .map(|degree| binomial_usize_checked(variables, degree))
            .try_fold(0usize, |acc, x| acc.checked_add(x?))?,
    )
    .ok()?;
    for degree in 0..=order {
        for monomial in 0..n {
            if monomial.count_ones() as usize != degree {
                continue;
            }
            let mut row = Vec::new();
            row.try_reserve_exact(n).ok()?;
            for point in 0..n {
                row.push(u8::from(point & monomial == monomial));
            }
            rows.push(row);
        }
    }
    BinaryCode::new(n, rows)
}

/// The Barnes-Wall lattice `BW16`, built as Construction D from
/// `RM(0,4) <= RM(2,4)`.
///
/// With this crate's scaled Construction-D convention the adjacent tower
/// `RM(1,4) <= RM(2,4)` gives the even unimodular rank-16 normalization
/// instead.
pub fn barnes_wall_16() -> IntegralForm {
    let rm0 = reed_muller_code(0, 4).expect("RM(0,4) exists");
    let rm2 = reed_muller_code(2, 4).expect("RM(2,4) exists");
    construction_d(&[rm0, rm2]).expect("RM(0,4) <= RM(2,4) gives an integral lattice")
}

/// The binary Hamming `[7,4,3]` code.
pub fn hamming_code() -> BinaryCode {
    BinaryCode::new(
        7,
        rows_from_strings(&["1000011", "0100101", "0010110", "0001111"]),
    )
    .expect("Hamming generator is binary")
}

/// The binary repetition `[n,1,n]` code, for `n > 0`.
pub fn repetition_code(n: usize) -> Option<BinaryCode> {
    if n == 0 {
        return None;
    }
    BinaryCode::new(n, vec![vec![1u8; n]])
}

/// The Type I self-dual `[2,1,2]` code; Construction A gives an odd unimodular
/// rank-2 lattice isometric to `Z^2`.
pub fn type_i_z2_code() -> BinaryCode {
    repetition_code(2).expect("length-2 repetition code exists")
}

/// A Type I self-dual code whose Construction A lattice is `Z^2 ⊕ E8`.
pub fn type_i_z2_plus_e8_code() -> BinaryCode {
    type_i_z2_code().direct_sum(&extended_hamming_code())
}

/// The extended Hamming `[8,4,4]` Type II code; Construction A gives `E8`.
pub fn extended_hamming_code() -> BinaryCode {
    BinaryCode::new(
        8,
        rows_from_strings(&["11110000", "11001100", "10101010", "11111111"]),
    )
    .expect("extended Hamming generator is binary")
}

/// The direct sum of two extended Hamming codes; Construction A gives
/// `E8 + E8`.
pub fn type_ii_e8_sum_code() -> BinaryCode {
    let mut rows = Vec::new();
    for row in extended_hamming_code().generators() {
        let mut r = vec![0u8; 16];
        r[..8].copy_from_slice(&row);
        rows.push(r);
    }
    for row in extended_hamming_code().generators() {
        let mut r = vec![0u8; 16];
        r[8..].copy_from_slice(&row);
        rows.push(r);
    }
    BinaryCode::new(16, rows).expect("direct sum generator is binary")
}

/// The indecomposable Type II `[16,8,4]` code whose Construction A lattice is
/// `D16+`.
pub fn type_ii_len16_code() -> BinaryCode {
    // One of the two length-16 Type II generators in the Harada-Munemasa
    // self-dual-code tables; the other is `E8` plus `E8`.
    BinaryCode::new(
        16,
        rows_from_strings(&[
            "1000000000001101",
            "0100001110011110",
            "0010001110011011",
            "0001000010000101",
            "0000100100000101",
            "0000011000000101",
            "0000000001010101",
            "0000000000100111",
        ]),
    )
    .expect("length-16 Type II generator is binary")
}

/// The `D16+` lattice, built by Construction A from the indecomposable Type II
/// length-16 code.
pub fn d16_plus() -> IntegralForm {
    type_ii_len16_code()
        .construction_a()
        .expect("Type II Construction A is integral")
}

/// The extended ternary Golay `[12,6,6]` code.
pub fn ternary_golay_code() -> TernaryCode {
    TernaryCode::new(
        12,
        vec![
            vec![1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1],
            vec![0, 1, 0, 0, 0, 0, 1, 0, 1, 2, 2, 1],
            vec![0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 2, 2],
            vec![0, 0, 0, 1, 0, 0, 1, 2, 1, 0, 1, 2],
            vec![0, 0, 0, 0, 1, 0, 1, 2, 2, 1, 0, 1],
            vec![0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 1, 0],
        ],
    )
    .expect("ternary Golay generator has entries in F_3")
}

/// The extended binary Golay `[24,12,8]` code.
pub fn golay_code() -> BinaryCode {
    BinaryCode::new(24, extended_golay_generator_rows()).expect("Golay generator is binary")
}

pub(crate) fn extended_golay_generator_rows() -> Vec<Vec<u8>> {
    let a: [[u8; 12]; 12] = [
        [1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1],
        [0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1],
        [0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1],
        [0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1],
        [0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1],
        [0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1],
        [1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0],
        [1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0],
        [1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0],
        [1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0],
        [1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0],
        [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1],
    ];
    (0..12)
        .map(|i| {
            let mut row = vec![0u8; 24];
            row[i] = 1;
            row[12..24].copy_from_slice(&a[i]);
            row
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::forms::e_8;

    #[test]
    fn packed_binary_generators_round_trip_across_word_boundaries() {
        let mut first = vec![0u8; 130];
        first[0] = 1;
        first[64] = 1;
        first[129] = 1;
        let mut second = vec![0u8; 130];
        second[65] = 1;
        second[128] = 1;
        let code = BinaryCode::new(130, vec![first.clone(), second.clone()]).unwrap();
        assert_eq!(code.generators(), vec![first, second]);
        let enumerator = code.weight_enumerator();
        assert_eq!(enumerator[2], 1);
        assert_eq!(enumerator[3], 1);
        assert_eq!(enumerator[5], 1);
    }

    #[test]
    fn hamming_macwilliams_matches_dual() {
        let h = hamming_code();
        assert_eq!(h.len(), 7);
        assert_eq!(h.dim(), 4);
        assert_eq!(h.minimum_distance(), Some(3));
        assert_eq!(h.macwilliams_transform(), h.dual().weight_enumerator());
        assert!(h.construction_a().is_none());
    }

    #[test]
    fn direct_sum_and_repetition_codes_build_type_i_examples() {
        assert!(repetition_code(0).is_none());
        let r2 = type_i_z2_code();
        assert_eq!(r2.len(), 2);
        assert_eq!(r2.dim(), 1);
        assert!(r2.is_self_dual());
        assert!(r2.is_self_orthogonal());
        assert!(!r2.is_doubly_even());
        assert_eq!(r2.weight_enumerator(), vec![1, 0, 1]);

        let z2 = r2.construction_a().unwrap();
        assert_eq!(z2.determinant(), 1);
        assert!(!z2.is_even());
        assert_eq!(z2.minimum(), Some(1));

        let z2_e8 = type_i_z2_plus_e8_code();
        assert_eq!(z2_e8.len(), 10);
        assert_eq!(z2_e8.dim(), 5);
        assert!(z2_e8.is_self_dual());
        assert!(!z2_e8.is_doubly_even());
        let lattice = z2_e8.construction_a().unwrap();
        assert_eq!(lattice.dim(), 10);
        assert!(lattice.is_unimodular());
        assert!(!lattice.is_even());
    }

    #[test]
    fn golay_macwilliams_and_construction_a_boundary() {
        let g = golay_code();
        assert_eq!(g.len(), 24);
        assert_eq!(g.dim(), 12);
        assert_eq!(g.minimum_distance(), Some(8));
        assert!(g.is_self_dual());
        assert!(g.is_doubly_even());
        assert_eq!(g.macwilliams_transform(), g.weight_enumerator());

        let l = g.construction_a().expect("Golay is Type II");
        assert_eq!(l.dim(), 24);
        assert!(l.is_even());
        assert!(l.is_unimodular());
        assert_eq!(g.theta_series_via_weight_enumerator(2), Some(vec![1, 48]));
    }

    #[test]
    fn type_ii_codes_build_the_rank_8_and_rank_16_lattices() {
        let e8_code = extended_hamming_code();
        assert!(e8_code.is_self_dual());
        assert!(e8_code.is_doubly_even());
        let e8_from_code = e8_code.construction_a().unwrap();
        assert_eq!(e8_from_code.dim(), 8);
        assert!(e8_from_code.is_even());
        assert!(e8_from_code.is_unimodular());
        assert_eq!(e8_from_code.determinant(), e_8().determinant());
        assert_eq!(
            e8_code.theta_series_via_weight_enumerator(2),
            Some(vec![1, 240])
        );

        let split = type_ii_e8_sum_code().construction_a().unwrap();
        assert_eq!(split.dim(), 16);
        assert!(split.is_even());
        assert!(split.is_unimodular());
        assert_eq!(split.determinant(), e_8().direct_sum(&e_8()).determinant());

        let d16 = d16_plus();
        assert_eq!(d16.dim(), 16);
        assert!(d16.is_even());
        assert!(d16.is_unimodular());
        assert_eq!(
            type_ii_len16_code().theta_series_via_weight_enumerator(2),
            Some(vec![1, 480])
        );
        // Formula-transcription check only: this re-evaluates the defining formula
        // `2^15 * 16!` and so cannot catch a wrong constant, only a copy/arithmetic
        // slip in `D16_PLUS_AUT_ORDER` itself. The real oracle for this number is
        // `theta::siegel_weil_rank16_mass_identity_is_exact`, which cross-checks
        // `|Aut(D16+)|` against the Minkowski-Siegel mass formula via the exact
        // rank-16 Siegel-Weil identity.
        assert_eq!(
            D16_PLUS_AUT_ORDER,
            (1u128 << 15) * (1..=16u128).product::<u128>()
        );
    }

    #[test]
    fn construction_b_cuts_out_the_golay_half_leech_lattice() {
        assert!(hamming_code().construction_b().is_none());
        let g = golay_code();
        let b = g.construction_b().expect("Golay is doubly even");
        assert_eq!(b.dim(), 24);
        assert!(b.is_even());
        assert_eq!(b.determinant(), 4);
        assert!(b.short_vectors(2).unwrap().is_empty());
        assert!((0..b.dim()).any(|i| b.gram()[i][i] == 4));
    }

    #[test]
    fn construction_d_recovers_a_and_builds_nested_towers() {
        let e8_code = extended_hamming_code();
        assert_eq!(
            construction_d(std::slice::from_ref(&e8_code))
                .unwrap()
                .gram(),
            e8_code.construction_a().unwrap().gram()
        );

        let zero = BinaryCode::new(8, Vec::new()).unwrap();
        assert!(construction_d(&[e8_code.clone(), zero.clone()]).is_none());

        let tower = construction_d(&[zero, e8_code]).expect("0 <= H_8 is nested");
        assert_eq!(tower.dim(), 8);
        assert!(tower.is_even());
        assert_eq!(tower.determinant(), 256);
        assert!(tower.short_vectors(2).unwrap().is_empty());
        assert!((0..tower.dim()).any(|i| tower.gram()[i][i] == 4));
    }

    #[test]
    fn reed_muller_codes_have_classical_parameters_and_nesting() {
        let expected = [
            (0, 1, Some(16)),
            (1, 5, Some(8)),
            (2, 11, Some(4)),
            (3, 15, Some(2)),
            (4, 16, Some(1)),
        ];
        let mut previous = None;
        for (order, dim, distance) in expected {
            let code = reed_muller_code(order, 4).expect("RM(order,4) exists");
            assert_eq!(code.len(), 16);
            assert_eq!(code.dim(), dim);
            assert_eq!(code.minimum_distance(), distance);
            if let Some(prev) = &previous {
                assert!(code.contains(prev));
            }
            previous = Some(code);
        }
        assert!(reed_muller_code(5, 4).is_none());
    }

    #[test]
    fn reed_muller_construction_d_gives_barnes_wall_16() {
        let rm0 = reed_muller_code(0, 4).unwrap();
        let rm2 = reed_muller_code(2, 4).unwrap();
        let bw = barnes_wall_16();
        assert_eq!(construction_d(&[rm0, rm2]).unwrap().gram(), bw.gram());
        assert_eq!(bw.dim(), 16);
        assert!(bw.is_even());
        assert_eq!(bw.determinant(), 256);
        assert_eq!(bw.minimum(), Some(4));
        assert_eq!(bw.kissing_number(), Some(4320));

        let rm1 = reed_muller_code(1, 4).unwrap();
        let unimodular = construction_d(&[rm1, reed_muller_code(2, 4).unwrap()]).unwrap();
        assert_eq!(unimodular.determinant(), 1);
        assert_eq!(unimodular.minimum(), Some(2));
        assert_eq!(unimodular.kissing_number(), Some(480));
    }

    #[test]
    fn prime_code_dual_and_macwilliams_are_exact() {
        let code = PrimeCode::<5>::new(3, vec![vec![1, 2, 0], vec![0, 1, 1]]).unwrap();
        assert_eq!(code.len(), 3);
        assert_eq!(code.dim(), 2);
        assert_eq!(code.size(), Some(25));
        assert!(code.contains(&code));
        assert_eq!(
            code.macwilliams_transform(),
            Some(code.dual().weight_enumerator())
        );

        let complete = code.complete_weight_enumerator().unwrap();
        assert_eq!(complete.values().sum::<i128>(), 25);
        assert!(PrimeCode::<2>::new(1, vec![vec![1]]).is_none());
        assert!(PrimeCode::<9>::new(1, vec![vec![1]]).is_none());
    }

    #[test]
    fn non_self_orthogonal_prime_code_has_no_integral_construction_a() {
        let code = PrimeCode::<3>::new(2, vec![vec![1, 0]]).unwrap();
        assert!(!code.is_self_orthogonal());
        assert!(code.construction_a().is_none());
    }

    #[test]
    fn ternary_golay_gives_the_honest_odd_construction_a_lattice() {
        let code = ternary_golay_code();
        assert_eq!(code.len(), 12);
        assert_eq!(code.dim(), 6);
        assert_eq!(code.size(), Some(729));
        assert_eq!(code.minimum_distance(), Some(6));
        assert!(code.is_self_dual());
        assert!(code.is_self_orthogonal());
        assert_eq!(code.macwilliams_transform(), Some(code.weight_enumerator()));
        assert_eq!(
            code.weight_enumerator(),
            vec![1, 0, 0, 0, 0, 0, 264, 0, 0, 440, 0, 0, 24]
        );

        let complete = code.complete_weight_enumerator().unwrap();
        assert_eq!(complete.values().sum::<i128>(), 729);

        let lattice = code.construction_a().unwrap();
        assert_eq!(lattice.dim(), 12);
        assert_eq!(lattice.determinant(), 1);
        assert!(
            !lattice.is_even(),
            "plain Z Construction A is odd; Coxeter-Todd needs the Eisenstein lift"
        );
        assert_eq!(lattice.minimum(), Some(2));
        assert_eq!(lattice.kissing_number(), Some(264));
    }

    #[test]
    fn weight_enumerator_theta_matches_construction_a_theta() {
        let e8_code = extended_hamming_code();
        let e8_lattice = e8_code.construction_a().unwrap();
        assert_eq!(
            e8_code.theta_series_via_weight_enumerator(3),
            e8_lattice.theta_series(3)
        );

        assert_eq!(
            type_ii_e8_sum_code().theta_series_via_weight_enumerator(3),
            Some(vec![1, 480, 61920])
        );
        assert_eq!(
            type_ii_len16_code().theta_series_via_weight_enumerator(3),
            Some(vec![1, 480, 61920])
        );
        assert_eq!(
            golay_code().theta_series_via_weight_enumerator(2),
            Some(vec![1, 48])
        );
    }
}
