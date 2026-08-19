//! The discriminant-form core: the even-lattice finite quadratic module
//! [`DiscriminantForm`], the odd-lattice [`OddDiscriminantForm`], Gauss sums,
//! Milgram/van der Blij checks, and the even Weil representation (`S`, `T`
//! matrices).

use super::complex::Complex64;
use super::gauss_sum::{mat_approx_eq, mat_identity, mat_mul, mat_pow, mat_scale, GaussSum};
use crate::forms::integral::diagonal::{
    rat_val, rational_congruence_diagonal, rational_mod_int, unit_mod8, DegenerateBehavior,
};
use crate::forms::integral::{is_prime_power, Genus, IntegralForm};
use crate::linalg::field::inverse_matrix;
use crate::linalg::integer::{gcd, normalize_relation_rows, prime_factors, reduce_integer_vector};
use crate::scalar::{Rational, Scalar};
use std::collections::BTreeSet;
use std::fmt;
use std::ops::{Index, IndexMut};

// ── rational / integer helpers ──

fn rational_to_f64(x: &Rational) -> f64 {
    (x.numer() as f64) / (x.denom() as f64)
}

fn dot_inv(v: &[i128], inv: &[Vec<Rational>], w: &[i128]) -> Rational {
    let n = v.len();
    let mut acc = Rational::zero();
    for i in 0..n {
        if v[i] == 0 {
            continue;
        }
        for (j, &wj) in w.iter().enumerate() {
            if wj == 0 {
                continue;
            }
            acc = acc.add(
                &Rational::from_int(v[i])
                    .mul(&inv[i][j])
                    .mul(&Rational::from_int(wj)),
            );
        }
    }
    acc
}

fn enumerate_hnf_reps(rows: &[Vec<i128>]) -> Option<Vec<Vec<i128>>> {
    let n = rows.len();
    if n == 0 {
        return Some(vec![Vec::new()]);
    }
    if rows.iter().any(|r| r.len() != n) {
        return None;
    }
    let mut pivots = Vec::with_capacity(n);
    for (i, row) in rows.iter().enumerate() {
        let lead = row.iter().position(|&x| x != 0)?;
        if lead != i || row[i] <= 0 {
            return None;
        }
        pivots.push(row[i]);
    }

    let mut reps = BTreeSet::new();
    let mut cur = vec![0i128; n];
    fn rec(
        idx: usize,
        pivots: &[i128],
        cur: &mut [i128],
        rows: &[Vec<i128>],
        reps: &mut BTreeSet<Vec<i128>>,
    ) {
        if idx == pivots.len() {
            let mut v = cur.to_vec();
            reduce_integer_vector(&mut v, rows.to_vec());
            reps.insert(v);
            return;
        }
        for x in 0..pivots[idx] {
            cur[idx] = x;
            rec(idx + 1, pivots, cur, rows, reps);
        }
        cur[idx] = 0;
    }
    rec(0, &pivots, &mut cur, rows, &mut reps);
    Some(reps.into_iter().collect())
}

// ── genus-signature helpers (used by genus_signature_mod8 / verify_milgram) ──

fn pow_mod8(mut base: i128, mut exp: u128) -> i128 {
    base = base.rem_euclid(8);
    let mut acc = 1i128;
    while exp > 0 {
        if exp & 1 == 1 {
            acc = (acc * base).rem_euclid(8);
        }
        base = (base * base).rem_euclid(8);
        exp >>= 1;
    }
    acc
}

fn is_antisquare_2(u: i128) -> bool {
    matches!(u.rem_euclid(8), 3 | 5)
}

fn diagonal_entries(lattice: &IntegralForm) -> Option<Vec<Rational>> {
    if lattice.determinant() == 0 {
        return None;
    }
    Some(rational_congruence_diagonal(
        lattice.gram(),
        DegenerateBehavior::RequireNonsingular,
    ))
}

fn two_adic_oddity(diag: &[Rational]) -> i128 {
    diag.iter()
        .map(|d| {
            let u = unit_mod8(d);
            let antisquare = rat_val(d, 2).rem_euclid(2) != 0 && is_antisquare_2(u);
            (u + if antisquare { 4 } else { 0 }).rem_euclid(8)
        })
        .sum::<i128>()
        .rem_euclid(8)
}

fn genus_oddity_and_p_excess_mod8(lattice: &IntegralForm) -> Option<(i128, i128)> {
    let genus = Genus::from_lattice(lattice)?;
    let oddity = genus
        .symbol_at(2)
        .iter()
        .map(|s| s.oddity)
        .sum::<i128>()
        .rem_euclid(8);
    let p_excess = genus
        .primes()
        .into_iter()
        .filter(|&p| p != 2)
        .flat_map(|p| {
            genus
                .symbol_at(p)
                .iter()
                .map(move |s| symbol_p_excess_mod8(p, s.scale, s.dim, s.sign))
        })
        .sum::<i128>()
        .rem_euclid(8);
    Some((oddity, p_excess))
}

fn symbol_p_excess_mod8(p: u128, scale: u128, dim: usize, sign: i128) -> i128 {
    let q = pow_mod8(p as i128, scale);
    let antisquare = if scale % 2 == 1 && sign < 0 { 4 } else { 0 };
    ((dim as i128) * (q - 1) + antisquare).rem_euclid(8)
}

/// Largest discriminant group [`DiscriminantForm::is_isomorphic`] will tabulate; past
/// it the Cayley-table build is refused with `None` (an honest budget, like
/// [`crate::forms::AUTO_NODE_BUDGET`]), never a wrong answer.
const ISO_GROUP_CAP: usize = 256;

/// Default node budget for the isomorphism search (candidate generator-images tried).
const ISO_NODE_BUDGET: u128 = 50_000_000;

/// The finite-abelian-group data of a discriminant form needed to compare two of
/// them: the identity index, each element's `q_L` value and additive order, and the
/// full Cayley addition table (indices into `reps`).
pub(crate) struct IsoTables {
    pub(crate) zero: usize,
    pub(crate) q: Vec<Rational>,
    pub(crate) order: Vec<usize>,
    pub(crate) add: SquareTable<usize>,
}

/// Dense row-major storage for the bounded square tables used by exact
/// finite-module algorithms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SquareTable<T> {
    side: usize,
    data: Box<[T]>,
}

impl<T: Clone> SquareTable<T> {
    pub(crate) fn filled(side: usize, value: T) -> Self {
        let len = side.checked_mul(side).expect("square table size overflow");
        SquareTable {
            side,
            data: vec![value; len].into_boxed_slice(),
        }
    }
}

impl<T> Index<usize> for SquareTable<T> {
    type Output = [T];

    fn index(&self, row: usize) -> &Self::Output {
        let start = row
            .checked_mul(self.side)
            .expect("square table row overflow");
        &self.data[start..start + self.side]
    }
}

impl<T> IndexMut<usize> for SquareTable<T> {
    fn index_mut(&mut self, row: usize) -> &mut Self::Output {
        let start = row
            .checked_mul(self.side)
            .expect("square table row overflow");
        &mut self.data[start..start + self.side]
    }
}

fn checked_i128_add(a: i128, b: i128) -> Option<i128> {
    a.checked_add(b)
}

fn checked_i128_sub(a: i128, b: i128) -> Option<i128> {
    a.checked_sub(b)
}

fn checked_i128_mul(a: i128, b: i128) -> Option<i128> {
    a.checked_mul(b)
}

fn lcm_usize(a: usize, b: usize) -> Option<usize> {
    let g = usize::try_from(gcd(i128::try_from(a).ok()?, i128::try_from(b).ok()?)).ok()?;
    a.checked_div(g)?.checked_mul(b)
}

fn divisors(n: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut d = 1usize;
    while d <= n / d {
        if n.is_multiple_of(d) {
            out.push(d);
            if d != n / d {
                out.push(n / d);
            }
        }
        d += 1;
    }
    out.sort_unstable();
    out
}

fn poly_trim(mut p: Vec<i128>) -> Vec<i128> {
    while p.len() > 1 && p.last() == Some(&0) {
        p.pop();
    }
    p
}

fn poly_mul(a: &[i128], b: &[i128]) -> Option<Vec<i128>> {
    if a.is_empty() || b.is_empty() {
        return Some(vec![0]);
    }
    let mut out = vec![0i128; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        if x == 0 {
            continue;
        }
        for (j, &y) in b.iter().enumerate() {
            if y == 0 {
                continue;
            }
            let term = checked_i128_mul(x, y)?;
            out[i + j] = checked_i128_add(out[i + j], term)?;
        }
    }
    Some(poly_trim(out))
}

fn poly_div_exact(num: &[i128], den: &[i128]) -> Option<Vec<i128>> {
    if den.is_empty() || den.last() != Some(&1) {
        return None;
    }
    if num.len() < den.len() {
        return if num.iter().all(|&x| x == 0) {
            Some(vec![0])
        } else {
            None
        };
    }
    let den_deg = den.len() - 1;
    let q_len = num.len() - den_deg;
    let mut rem = num.to_vec();
    let mut q = vec![0i128; q_len];
    for k in (0..q_len).rev() {
        let coeff = rem[k + den_deg];
        q[k] = coeff;
        if coeff == 0 {
            continue;
        }
        for j in 0..=den_deg {
            let term = checked_i128_mul(coeff, den[j])?;
            rem[k + j] = checked_i128_sub(rem[k + j], term)?;
        }
    }
    if rem[..den_deg].iter().any(|&x| x != 0) || rem[den_deg..].iter().any(|&x| x != 0) {
        return None;
    }
    Some(poly_trim(q))
}

fn cyclotomic_polynomial(
    n: usize,
    cache: &mut std::collections::BTreeMap<usize, Vec<i128>>,
) -> Option<Vec<i128>> {
    if let Some(p) = cache.get(&n) {
        return Some(p.clone());
    }
    let phi = if n == 1 {
        vec![-1, 1]
    } else {
        let mut numerator = vec![0i128; n + 1];
        numerator[0] = -1;
        numerator[n] = 1;
        let mut product = vec![1i128];
        for d in divisors(n).into_iter().filter(|&d| d < n) {
            let pd = cyclotomic_polynomial(d, cache)?;
            product = poly_mul(&product, &pd)?;
        }
        poly_div_exact(&numerator, &product)?
    };
    cache.insert(n, phi.clone());
    Some(phi)
}

fn reduce_cyclotomic(mut p: Vec<i128>, phi: &[i128]) -> Option<Vec<i128>> {
    let degree = phi.len().checked_sub(1)?;
    if degree == 0 {
        return None;
    }
    while p.len() > degree {
        let high_idx = p.len() - 1;
        let coeff = p.pop().expect("length checked");
        if coeff == 0 {
            continue;
        }
        let offset = high_idx - degree;
        for (j, &c) in phi[..degree].iter().enumerate() {
            let term = checked_i128_mul(coeff, c)?;
            p[offset + j] = checked_i128_sub(p[offset + j], term)?;
        }
    }
    p.resize(degree, 0);
    Some(p)
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Cyclo {
    coeffs: Vec<i128>,
}

struct CycloContext {
    order: usize,
    phi: Vec<i128>,
    powers: Vec<Vec<i128>>,
}

impl CycloContext {
    fn new(order: usize) -> Option<Self> {
        if order == 0 || order > FQM_CYCLOTOMIC_ORDER_CAP {
            return None;
        }
        let mut cache = std::collections::BTreeMap::new();
        let phi = cyclotomic_polynomial(order, &mut cache)?;
        let mut powers = Vec::with_capacity(order);
        for k in 0..order {
            let mut p = vec![0i128; k + 1];
            p[k] = 1;
            powers.push(reduce_cyclotomic(p, &phi)?);
        }
        Some(CycloContext { order, phi, powers })
    }

    fn zero(&self) -> Cyclo {
        Cyclo {
            coeffs: vec![0; self.phi.len() - 1],
        }
    }

    fn constant(&self, c: i128) -> Cyclo {
        let mut out = self.zero();
        out.coeffs[0] = c;
        out
    }

    fn root_power(&self, exp: isize) -> Cyclo {
        let order = self.order as isize;
        let idx = exp.rem_euclid(order) as usize;
        Cyclo {
            coeffs: self.powers[idx].clone(),
        }
    }
}

impl Cyclo {
    fn add_assign(&mut self, rhs: &Cyclo) -> Option<()> {
        for (a, &b) in self.coeffs.iter_mut().zip(&rhs.coeffs) {
            *a = checked_i128_add(*a, b)?;
        }
        Some(())
    }

    fn mul(&self, rhs: &Cyclo, ctx: &CycloContext) -> Option<Cyclo> {
        let mut raw = vec![0i128; self.coeffs.len() + rhs.coeffs.len() - 1];
        for (i, &x) in self.coeffs.iter().enumerate() {
            if x == 0 {
                continue;
            }
            for (j, &y) in rhs.coeffs.iter().enumerate() {
                if y == 0 {
                    continue;
                }
                let term = checked_i128_mul(x, y)?;
                raw[i + j] = checked_i128_add(raw[i + j], term)?;
            }
        }
        Some(Cyclo {
            coeffs: reduce_cyclotomic(raw, &ctx.phi)?,
        })
    }

    fn mul_root(&self, exp: isize, ctx: &CycloContext) -> Option<Cyclo> {
        self.mul(&ctx.root_power(exp), ctx)
    }

    fn conjugate(&self, ctx: &CycloContext) -> Option<Cyclo> {
        let mut out = ctx.zero();
        for (i, &c) in self.coeffs.iter().enumerate() {
            if c == 0 {
                continue;
            }
            let mut term = ctx.root_power(-(i as isize));
            for x in &mut term.coeffs {
                *x = checked_i128_mul(*x, c)?;
            }
            out.add_assign(&term)?;
        }
        Some(out)
    }

    fn principal_real_f64(&self, ctx: &CycloContext) -> f64 {
        let step = std::f64::consts::TAU / (ctx.order as f64);
        self.coeffs
            .iter()
            .enumerate()
            .map(|(k, &c)| (c as f64) * ((k as f64) * step).cos())
            .sum()
    }
}

/// Largest discriminant group for the p-primary Gauss/Brown phase projection. The
/// path enumerates the finite module exactly, so it declines rather than silently
/// truncating.
const FQM_GAUSS_GROUP_CAP: usize = 4096;

/// Largest cyclotomic order used by the exact algebraic Gauss-sum shape check.
const FQM_CYCLOTOMIC_ORDER_CAP: usize = 4096;

pub(crate) fn phase_mod8_from_q_values<'a>(
    q_values: impl IntoIterator<Item = &'a Rational>,
    group_order: usize,
) -> Option<i128> {
    let q_values: Vec<Rational> = q_values.into_iter().cloned().collect();
    if q_values.len() != group_order {
        return None;
    }
    let mut root_order = 8usize;
    for q in &q_values {
        let den = usize::try_from(q.denom()).ok()?;
        root_order = lcm_usize(root_order, den.checked_mul(2)?)?;
    }
    let ctx = CycloContext::new(root_order)?;
    let mut sum = ctx.zero();
    for q in &q_values {
        let den = usize::try_from(q.denom()).ok()?;
        let period = den.checked_mul(2)?;
        let numer = q.numer().rem_euclid(i128::try_from(period).ok()?);
        let scale = root_order.checked_div(period)?;
        let exp = usize::try_from(numer).ok()?.checked_mul(scale)? % root_order;
        sum.add_assign(&ctx.root_power(exp as isize))?;
    }

    let order_const = ctx.constant(i128::try_from(group_order).ok()?);
    let eighth_shift = root_order.checked_div(8)?;
    let mut candidates = Vec::new();
    for beta in 0..8i128 {
        let shift = -isize::try_from(beta.checked_mul(i128::try_from(eighth_shift).ok()?)?).ok()?;
        let t = sum.mul_root(shift, &ctx)?;
        if t.conjugate(&ctx)? != t {
            continue;
        }
        if t.mul(&t, &ctx)? == order_const {
            candidates.push((beta, t));
        }
    }

    match candidates.as_slice() {
        [(beta, _)] => Some(*beta),
        [] => None,
        _ => {
            // Exact algebra has narrowed the ambiguity to the two square roots.
            // The principal embedding chooses +sqrt(|A|) rather than its negative.
            candidates
                .into_iter()
                .find(|(_, t)| t.principal_real_f64(&ctx) > 0.0)
                .map(|(beta, _)| beta)
        }
    }
}

/// The subgroup generated by `gens`, as the set of element indices.
fn subgroup_closure(t: &IsoTables, gens: &[usize]) -> Vec<bool> {
    let mut set = vec![false; t.order.len()];
    set[t.zero] = true;
    let mut frontier = vec![t.zero];
    while let Some(x) = frontier.pop() {
        for &g in gens {
            let nx = t.add[x][g];
            if !set[nx] {
                set[nx] = true;
                frontier.push(nx);
            }
        }
    }
    set
}

/// A minimal generating set, chosen greedily by maximal order (which realizes the
/// invariant-factor count for a finite abelian group).
pub(super) fn min_generators(t: &IsoTables) -> Vec<usize> {
    let n = t.order.len();
    let mut gens: Vec<usize> = Vec::new();
    let mut covered = subgroup_closure(t, &gens);
    while covered.iter().filter(|&&present| present).count() < n {
        let g = (0..n)
            .filter(|&i| !covered[i])
            .max_by_key(|&i| t.order[i])
            .expect("a non-covered element exists while |covered| < |A|");
        gens.push(g);
        covered = subgroup_closure(t, &gens);
    }
    gens
}

/// Given images for the generators of `lt`, extend by the homomorphism property
/// (BFS over `lt`'s generator steps) and check the result is a `q`-preserving
/// bijection `lt → mt`. Returns `false` on any inconsistency.
fn verify_iso(lt: &IsoTables, mt: &IsoTables, gens: &[usize], img: &[usize]) -> bool {
    let n = lt.order.len();
    let mut phi = vec![usize::MAX; n];
    phi[lt.zero] = mt.zero;
    let mut frontier = vec![lt.zero];
    while let Some(x) = frontier.pop() {
        for (t, &g) in gens.iter().enumerate() {
            let nx = lt.add[x][g];
            let nimg = mt.add[phi[x]][img[t]];
            if phi[nx] == usize::MAX {
                phi[nx] = nimg;
                frontier.push(nx);
            } else if phi[nx] != nimg {
                return false; // not a well-defined homomorphism
            }
        }
    }
    if phi.contains(&usize::MAX) {
        return false; // gens did not generate (should not happen)
    }
    // Injective ⇒ bijective (equal finite cardinality).
    let mut seen = vec![false; n];
    for &p in &phi {
        if seen[p] {
            return false;
        }
        seen[p] = true;
    }
    // q preserved on *every* element (the complete quadratic-form check; homomorphism
    // + matching q on generators alone does not force it).
    (0..n).all(|i| mt.q[phi[i]] == lt.q[i])
}

/// DFS over generator-image assignments (pruned by equal order and equal `q`),
/// returning `Some(true)` on the first valid isomorphism, `Some(false)` if exhausted,
/// `None` if the node budget runs out first.
fn search_iso(
    lt: &IsoTables,
    mt: &IsoTables,
    gens: &[usize],
    img: &mut Vec<usize>,
    budget: &mut u128,
) -> Option<bool> {
    let depth = img.len();
    if depth == gens.len() {
        return Some(verify_iso(lt, mt, gens, img));
    }
    let g = gens[depth];
    for cand in 0..mt.order.len() {
        if mt.order[cand] != lt.order[g] || mt.q[cand] != lt.q[g] {
            continue;
        }
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        img.push(cand);
        match search_iso(lt, mt, gens, img, budget) {
            Some(true) => return Some(true),
            Some(false) => {}
            None => return None,
        }
        img.pop();
    }
    Some(false)
}

/// The shared private core behind [`DiscriminantForm`] and [`OddDiscriminantForm`]:
/// the finite abelian group `A_L = L#/L`, presented as canonical coset
/// representatives for `Z^n / GZ^n` plus the exact inverse Gram matrix, and the
/// bilinear pairing `b_L(y,z) = y^T G^{-1} z mod Z` both siblings share verbatim.
/// The two public types differ only in their *quadratic* value convention
/// (`mod 2Z` vs `mod Z`) and in which parity of lattice their constructor accepts.
#[derive(Clone, Debug, PartialEq)]
struct DiscriminantCore {
    /// Nontrivial invariant factors of `A_L`.
    group: Vec<i128>,
    /// Canonical representatives `y` for `Z^n / GZ^n`.
    reps: Vec<Vec<i128>>,
    /// The exact inverse Gram matrix.
    gram_inv: Vec<Vec<Rational>>,
}

impl DiscriminantCore {
    /// Build `A_L = L#/L` for a nonsingular integral lattice. Even/odd is the
    /// caller's concern: each public wrapper checks its own parity boundary before
    /// calling this.
    fn from_lattice(lattice: &IntegralForm) -> Option<Self> {
        if lattice.determinant() == 0 {
            return None;
        }
        let mat: Vec<Vec<Rational>> = lattice
            .gram()
            .iter()
            .map(|row| row.iter().map(|&x| Rational::from_int(x)).collect())
            .collect();
        let gram_inv = inverse_matrix(mat)?;
        let hnf = normalize_relation_rows(lattice.gram().to_vec());
        let reps = enumerate_hnf_reps(&hnf)?;
        let det = lattice.determinant().unsigned_abs() as usize;
        if reps.len() != det {
            return None;
        }
        let group = lattice
            .invariant_factors()
            .into_iter()
            .filter(|&d| d > 1)
            .collect();
        Some(DiscriminantCore {
            group,
            reps,
            gram_inv,
        })
    }

    /// `b_L(y,z) = y^T G^{-1} z mod Z`, represented in `[0, 1)`.
    fn bilinear_value_mod1(&self, y: &[i128], z: &[i128]) -> Rational {
        rational_mod_int(dot_inv(y, &self.gram_inv, z), 1)
    }
}

/// The finite discriminant quadratic module of an even lattice.
#[derive(Clone, Debug, PartialEq)]
pub struct DiscriminantForm {
    core: DiscriminantCore,
}

/// The finite discriminant quadratic object attached to an odd integral lattice.
///
/// For odd lattices the even-lattice value `x^2 mod 2Z` is not well-defined on
/// `L#/L`. The canonical odd replacement used here is `x^2 mod Z`, represented by
/// `q_L(y) = y^T G^{-1} y mod Z` on `Z^n / GZ^n`.
#[derive(Clone, Debug, PartialEq)]
pub struct OddDiscriminantForm {
    core: DiscriminantCore,
}

/// The odd-lattice Milgram/van der Blij congruence data.
///
/// The corrected signature is `oddity - p_excess (mod 8)`, using the
/// Conway-Sloane genus symbol. For even lattices the uncorrected discriminant
/// Gauss sum is handled by [`verify_milgram`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OddMilgramInvariants {
    /// Real signature modulo eight.
    pub signature_mod8: i128,
    /// Two-adic oddity modulo eight.
    pub oddity_mod8: i128,
    /// Sum of odd-prime excesses modulo eight.
    pub p_excess_mod8: i128,
    /// `oddity - p_excess` modulo eight.
    pub corrected_signature_mod8: i128,
    /// Signature obtained from the complete genus computation.
    pub genus_signature_mod8: i128,
}

impl OddMilgramInvariants {
    /// Whether the oddity-corrected genus formula recovers the real signature.
    pub fn verified(&self) -> bool {
        self.corrected_signature_mod8 == self.signature_mod8
            && self.genus_signature_mod8 == self.signature_mod8
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for OddMilgramInvariants {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "OddMilgramInvariants(signature_mod8={}, oddity_mod8={}, p_excess_mod8={}, corrected_signature_mod8={}, genus_signature_mod8={}, verified={})",
            self.signature_mod8,
            self.oddity_mod8,
            self.p_excess_mod8,
            self.corrected_signature_mod8,
            self.genus_signature_mod8,
            self.verified(),
        )
    }
}

impl DiscriminantForm {
    /// Build `q_L` for a nonsingular even lattice. Odd lattices return `None`
    /// because `x^T G x mod 2Z` is not well-defined on `L#/L`.
    pub fn from_lattice(lattice: &IntegralForm) -> Option<Self> {
        if !lattice.is_even() {
            return None;
        }
        Some(DiscriminantForm {
            core: DiscriminantCore::from_lattice(lattice)?,
        })
    }

    /// Nontrivial invariant factors of `A_L`.
    pub fn group(&self) -> &[i128] {
        &self.core.group
    }

    /// Canonical representatives `y` for `Z^n / GZ^n`.
    pub fn reps(&self) -> &[Vec<i128>] {
        &self.core.reps
    }

    /// The exact inverse Gram matrix.
    pub fn gram_inv(&self) -> &[Vec<Rational>] {
        &self.core.gram_inv
    }

    /// `q_L(y) = y^T G^{-1} y mod 2Z`, represented in `[0, 2)`.
    pub fn quadratic_value_mod2(&self, y: &[i128]) -> Rational {
        rational_mod_int(dot_inv(y, &self.core.gram_inv, y), 2)
    }

    /// `b_L(y,z) = y^T G^{-1} z mod Z`, represented in `[0, 1)`.
    pub fn bilinear_value_mod1(&self, y: &[i128], z: &[i128]) -> Rational {
        self.core.bilinear_value_mod1(y, z)
    }

    /// The normalized Gauss sum
    /// `|A_L|^{-1/2} * sum_x exp(pi*i*q_L(x))`.
    pub fn gauss_sum(&self) -> GaussSum {
        let mut re = 0.0f64;
        let mut im = 0.0f64;
        for y in &self.core.reps {
            let theta = std::f64::consts::PI * rational_to_f64(&self.quadratic_value_mod2(y));
            re += theta.cos();
            im += theta.sin();
        }
        let scale = 1.0 / (self.core.reps.len() as f64).sqrt();
        GaussSum {
            re: re * scale,
            im: im * scale,
        }
    }

    /// The Milgram phase as `signature mod 8`, extracted from the Gauss sum.
    pub fn milgram_signature_mod8(&self) -> Option<i128> {
        self.gauss_sum().phase_mod8(1e-8)
    }

    /// The **Brown invariant** `β ∈ ℤ/8` of the discriminant form, on the
    /// **2-elementary** slice. For `A_L ≅ (ℤ/2)^k`, `q_L` takes values
    /// in `½ℤ/2ℤ`, and `t ↦ 2t` identifies `(A_L, 2q_L)` with a `ℤ/4`-quadratic
    /// form whose Brown sum *is* the Milgram Gauss sum — so
    ///
    /// ```text
    /// β(2·q_L) ≡ sign(L)   (mod 8)
    /// ```
    ///
    /// (Milgram / van der Blij), computed from the **integer value-counts**
    /// `(n₀ − n₂) + i(n₁ − n₃)` — a fifth route to `σ mod 8`, and the first with no
    /// floating point (the [`GaussSum`] route is `f64`). `None` unless `A_L` is
    /// 2-elementary (read off the invariant factors); the discriminant bilinear
    /// form is nondegenerate on `A_L`, so this slice has no radical.
    pub fn brown_invariant(&self) -> Option<crate::forms::BrownInvariants> {
        use crate::forms::char2::beta_from_gauss;
        // 2-elementary ⇔ every nontrivial invariant factor is 2 (the unimodular
        // A_L = 0 case is vacuously 2-elementary, β = 0).
        if !self.core.group.iter().all(|&d| d == 2) {
            return None;
        }
        // q4(γ) = 2·q_L(γ) ∈ {0,1,2,3}; enumerate the whole (nondegenerate) group.
        let mut counts = [0i128; 4];
        for gamma in &self.core.reps {
            let two_q = self.quadratic_value_mod2(gamma);
            let two_q = two_q.add(&two_q);
            if !two_q.is_integer() {
                return None; // not actually 2-elementary at this element (defensive)
            }
            counts[two_q.numer().rem_euclid(4) as usize] += 1;
        }
        let re = counts[0] - counts[2];
        let im = counts[1] - counts[3];
        Some(crate::forms::BrownInvariants {
            beta: beta_from_gauss(re, im)?,
            rank: self.core.group.len(),
            radical_dim: 0,
            radical_anisotropic: false,
        })
    }

    /// The `reps` index of the coset containing the raw integer vector `v`.
    fn element_index(&self, v: &[i128]) -> Option<usize> {
        self.core
            .reps
            .iter()
            .position(|r| self.equivalent_mod_lattice(r, v))
    }

    /// Tabulate the finite abelian group `(A_L, +)` with each element's `q_L` value
    /// and order, plus the full addition table. `None` past `group_cap`.
    pub(crate) fn tables_bounded(&self, group_cap: usize) -> Option<IsoTables> {
        let n = self.core.reps.len();
        if n > group_cap {
            return None;
        }
        let zero = self
            .core
            .reps
            .iter()
            .position(|r| r.iter().all(|&x| x == 0))?;
        let q: Vec<Rational> = self
            .core
            .reps
            .iter()
            .map(|r| self.quadratic_value_mod2(r))
            .collect();
        let mut add = SquareTable::filled(n, 0usize);
        for i in 0..n {
            for j in 0..n {
                let s: Vec<i128> = self.core.reps[i]
                    .iter()
                    .zip(&self.core.reps[j])
                    .map(|(&a, &b)| a + b)
                    .collect();
                add[i][j] = self.element_index(&s)?;
            }
        }
        let mut order = vec![1usize; n];
        for i in 0..n {
            let mut cur = i;
            let mut k = 1usize;
            while cur != zero {
                cur = add[cur][i];
                k += 1;
            }
            order[i] = k;
        }
        Some(IsoTables {
            zero,
            q,
            order,
            add,
        })
    }

    /// The p-primary Milgram/Brown Gauss-sum phase projection of this finite
    /// quadratic module.
    ///
    /// This is the `Z/8` phase seen by Milgram's formula, decomposed over the
    /// primary subgroups of `A_L`. It is **not** the full Wall/Nikulin/
    /// Kawauchi-Kojima normal form of the FQM Witt group: distinct Witt classes can
    /// have the same phase. [`gauss_sum`](Self::gauss_sum) supplies a numerical
    /// comparison; this method first checks the relevant cyclotomic
    /// equalities exactly and only then chooses the positive square-root branch in
    /// the principal embedding.
    pub fn fqm_gauss_phase(&self) -> Option<super::phases::FqmGaussPhase> {
        use super::phases::FqmPrimaryPhase;
        let tables = self.tables_bounded(FQM_GAUSS_GROUP_CAP)?;
        let order = self.core.reps.len();
        let total = phase_mod8_from_q_values(tables.q.iter(), order)?;
        let mut primes = BTreeSet::new();
        for &d in &self.core.group {
            for p in prime_factors(d.unsigned_abs()) {
                primes.insert(p);
            }
        }

        let mut primary = Vec::new();
        for p in primes {
            let indices: Vec<usize> = tables
                .order
                .iter()
                .enumerate()
                .filter_map(|(i, &ord)| is_prime_power(ord as u128, p).then_some(i))
                .collect();
            let exponent = indices
                .iter()
                .map(|&i| tables.order[i] as u128)
                .max()
                .unwrap_or(1);
            let qs: Vec<&Rational> = indices.iter().map(|&i| &tables.q[i]).collect();
            let phase_mod8 = phase_mod8_from_q_values(qs, indices.len())?;
            primary.push(FqmPrimaryPhase {
                prime: p,
                order: indices.len(),
                exponent,
                phase_mod8,
            });
        }
        let sum = primary
            .iter()
            .map(|c| c.phase_mod8)
            .sum::<i128>()
            .rem_euclid(8);
        if sum != total {
            return None;
        }
        Some(super::phases::FqmGaussPhase {
            order,
            phase_mod8: total,
            primary,
        })
    }

    /// Milgram phase as `signature mod 8`, via the p-primary
    /// [`fqm_gauss_phase`](Self::fqm_gauss_phase) projection.
    pub fn milgram_signature_mod8_fqm(&self) -> Option<i128> {
        Some(self.fqm_gauss_phase()?.phase_mod8)
    }

    fn iso_tables(&self) -> Option<IsoTables> {
        self.tables_bounded(ISO_GROUP_CAP)
    }

    /// Whether two discriminant quadratic forms `(A_L, q_L)` and `(A_M, q_M)` are
    /// **isomorphic** — equal invariant factors plus a `q`-preserving group
    /// isomorphism. This is the finite-quadratic-module half of **Nikulin's
    /// criterion** (Nikulin, *Integral symmetric bilinear forms…*, Izv. Akad. Nauk
    /// SSSR **43** (1979), Cor. 1.9.4): two **even** lattices share a genus iff their
    /// signature pairs agree and their discriminant forms are isomorphic. Both inputs
    /// are even-lattice discriminant forms (the [`from_lattice`](Self::from_lattice)
    /// boundary); the signature half is checked separately by the caller.
    ///
    /// `Some(true)`/`Some(false)` is a decided answer; `None` only past the budget
    /// (group larger than `ISO_GROUP_CAP`, or the search exceeding the node budget)
    /// and does not silently guess. This is an FQM isomorphism search, not a
    /// p-adic-symbol reimplementation.
    pub fn is_isomorphic(&self, other: &Self) -> Option<bool> {
        self.is_isomorphic_bounded(other, ISO_NODE_BUDGET)
    }

    /// [`is_isomorphic`](Self::is_isomorphic) with an explicit node budget.
    pub fn is_isomorphic_bounded(&self, other: &Self, node_budget: u128) -> Option<bool> {
        if self.core.reps.len() != other.core.reps.len() {
            return Some(false);
        }
        let mut g1 = self.core.group.clone();
        let mut g2 = other.core.group.clone();
        g1.sort_unstable();
        g2.sort_unstable();
        if g1 != g2 {
            return Some(false);
        }
        let lt = self.iso_tables()?;
        let mt = other.iso_tables()?;
        // Necessary: the q-value multisets must agree (canonical reps ⇒ exact keys).
        let mut ql: Vec<(i128, i128)> = lt.q.iter().map(|x| (x.numer(), x.denom())).collect();
        let mut qm: Vec<(i128, i128)> = mt.q.iter().map(|x| (x.numer(), x.denom())).collect();
        ql.sort_unstable();
        qm.sort_unstable();
        if ql != qm {
            return Some(false);
        }
        let gens = min_generators(&lt);
        let mut budget = node_budget;
        let mut img: Vec<usize> = Vec::with_capacity(gens.len());
        search_iso(&lt, &mt, &gens, &mut img, &mut budget)
    }

    fn equivalent_mod_lattice(&self, a: &[i128], b: &[i128]) -> bool {
        let n = self.core.gram_inv.len();
        if a.len() != n || b.len() != n {
            return false;
        }
        let diff: Vec<i128> = a.iter().zip(b).map(|(&x, &y)| x - y).collect();
        for row in &self.core.gram_inv {
            let mut coord = Rational::zero();
            for (r, &d) in row.iter().zip(&diff) {
                if d != 0 {
                    coord = coord.add(&r.mul(&Rational::from_int(d)));
                }
            }
            if !coord.is_integer() {
                return false;
            }
        }
        true
    }

    fn negation_matrix(&self) -> Option<Vec<Vec<Complex64>>> {
        let n = self.core.reps.len();
        let mut out = vec![vec![Complex64::zero(); n]; n];
        for (col, gamma) in self.core.reps.iter().enumerate() {
            let neg_gamma: Vec<i128> = gamma.iter().map(|&x| -x).collect();
            let row = self
                .core
                .reps
                .iter()
                .position(|delta| self.equivalent_mod_lattice(delta, &neg_gamma))?;
            out[row][col] = Complex64::one();
        }
        Some(out)
    }

    fn weil_t_matrix(&self) -> Vec<Vec<Complex64>> {
        let t = self.weil_t();
        let mut out = vec![vec![Complex64::zero(); t.len()]; t.len()];
        for (i, z) in t.into_iter().enumerate() {
            out[i][i] = z;
        }
        out
    }

    /// The diagonal Weil `T` multipliers `exp(pi*i*q_L(gamma))`.
    pub fn weil_t(&self) -> Vec<Complex64> {
        self.core
            .reps
            .iter()
            .map(|gamma| {
                let theta =
                    std::f64::consts::PI * rational_to_f64(&self.quadratic_value_mod2(gamma));
                Complex64::cis(theta)
            })
            .collect()
    }

    /// The phase index of the `S` prefactor in the standard Weil convention:
    /// `exp(-2*pi*i*sign/8)`. The existing Milgram Gauss sum stores the conjugate
    /// phase `exp(+2*pi*i*sign/8)`, so this returns `-sign mod 8`.
    pub fn weil_s_prefactor_phase_mod8(&self) -> Option<i128> {
        Some((-self.milgram_signature_mod8()?).rem_euclid(8))
    }

    /// Recover the positive Milgram signature phase from the Weil `S` prefactor.
    pub fn weil_s_recovers_milgram_phase_mod8(&self) -> Option<i128> {
        Some((-self.weil_s_prefactor_phase_mod8()?).rem_euclid(8))
    }

    /// The Weil `S` matrix in the basis of discriminant representatives:
    /// `(sigma/sqrt(|A|)) * exp(-2*pi*i*b_L(gamma,delta))`.
    pub fn weil_s(&self) -> Option<Vec<Vec<Complex64>>> {
        let n = self.core.reps.len();
        if n == 0 {
            return None;
        }
        let sigma = Complex64::eighth_root(self.weil_s_prefactor_phase_mod8()?);
        let scale = 1.0 / (n as f64).sqrt();
        let mut out = vec![vec![Complex64::zero(); n]; n];
        for (col, gamma) in self.core.reps.iter().enumerate() {
            for (row, delta) in self.core.reps.iter().enumerate() {
                let theta = -2.0
                    * std::f64::consts::PI
                    * rational_to_f64(&self.bilinear_value_mod1(gamma, delta));
                out[row][col] = sigma.mul(&Complex64::cis(theta)).scale(scale);
            }
        }
        Some(out)
    }

    /// Verify the finite Weil representation bookkeeping for this discriminant
    /// form. With the standard `S` prefactor, the honest metaplectic relations are
    /// `S^2 = sigma^2 * (gamma -> -gamma)`, `S^4 = sigma^4 * I`, and
    /// `(ST)^3 = S^2`; for unimodular signature `0 mod 8` these collapse to the
    /// familiar scalar relations.
    pub fn verify_weil_relations(&self) -> bool {
        let Some(s_phase) = self.weil_s_prefactor_phase_mod8() else {
            return false;
        };
        if self.weil_s_recovers_milgram_phase_mod8() != self.milgram_signature_mod8() {
            return false;
        }
        let Some(s) = self.weil_s() else {
            return false;
        };
        let t = self.weil_t_matrix();
        let Some(neg) = self.negation_matrix() else {
            return false;
        };
        let tol = 1e-8;
        if self.weil_t().iter().any(|z| (z.abs() - 1.0).abs() > tol) {
            return false;
        }
        let s2 = mat_pow(&s, 2);
        let s4 = mat_pow(&s, 4);
        let st3 = mat_pow(&mat_mul(&s, &t), 3);
        let s2_target = mat_scale(&neg, Complex64::eighth_root(2 * s_phase));
        let s4_target = mat_scale(
            &mat_identity(self.core.reps.len()),
            Complex64::eighth_root(4 * s_phase),
        );
        mat_approx_eq(&s2, &s2_target, tol)
            && mat_approx_eq(&s4, &s4_target, tol)
            && mat_approx_eq(&st3, &s2, tol)
    }
}

impl OddDiscriminantForm {
    /// Build the odd-lattice discriminant object for a nonsingular odd lattice.
    ///
    /// Even lattices stay on [`DiscriminantForm`], whose `Q/2Z` values carry the
    /// nondegenerate Weil/Milgram finite quadratic module.
    pub fn from_lattice(lattice: &IntegralForm) -> Option<Self> {
        if lattice.is_even() {
            return None;
        }
        Some(OddDiscriminantForm {
            core: DiscriminantCore::from_lattice(lattice)?,
        })
    }

    /// Nontrivial invariant factors of `A_L`.
    pub fn group(&self) -> &[i128] {
        &self.core.group
    }

    /// Canonical representatives `y` for `Z^n / GZ^n`.
    pub fn reps(&self) -> &[Vec<i128>] {
        &self.core.reps
    }

    /// The exact inverse Gram matrix.
    pub fn gram_inv(&self) -> &[Vec<Rational>] {
        &self.core.gram_inv
    }

    /// `q_L(y) = y^T G^{-1} y mod Z`, represented in `[0, 1)`.
    pub fn quadratic_value_mod1(&self, y: &[i128]) -> Rational {
        rational_mod_int(dot_inv(y, &self.core.gram_inv, y), 1)
    }

    /// The discriminant bilinear pairing `b_L(y,z) = y^T G^{-1} z mod Z`.
    pub fn bilinear_value_mod1(&self, y: &[i128], z: &[i128]) -> Rational {
        self.core.bilinear_value_mod1(y, z)
    }

    /// The normalized Gauss sum of the `Q/Z` odd-lattice discriminant values.
    ///
    /// This sum is useful diagnostic data, but unlike the even `Q/2Z` form it is
    /// not the whole Milgram statement; use [`odd_milgram_report`] for the
    /// oddity-corrected signature congruence.
    pub fn gauss_sum(&self) -> GaussSum {
        let mut re = 0.0f64;
        let mut im = 0.0f64;
        for y in &self.core.reps {
            let theta = std::f64::consts::TAU * rational_to_f64(&self.quadratic_value_mod1(y));
            re += theta.cos();
            im += theta.sin();
        }
        let scale = 1.0 / (self.core.reps.len() as f64).sqrt();
        GaussSum {
            re: re * scale,
            im: im * scale,
        }
    }

    /// Phase of [`gauss_sum`](Self::gauss_sum), when it is an eighth root.
    pub fn gauss_phase_mod8(&self) -> Option<i128> {
        self.gauss_sum().phase_mod8(1e-8)
    }
}

/// Signature mod 8 from the Conway-Sloane oddity formula, using exact rational
/// diagonalization as an independent check on Milgram's Gauss sum.
pub fn genus_signature_mod8(lattice: &IntegralForm) -> Option<i128> {
    let diag = diagonal_entries(lattice)?;
    let oddity = two_adic_oddity(&diag);
    let (_, p_excess) = genus_oddity_and_p_excess_mod8(lattice)?;
    Some((oddity - p_excess).rem_euclid(8))
}

/// Verify Milgram/van der Blij for an even lattice, comparing the discriminant
/// FQM phase against exact real signature, the numerical Gauss sum, and the
/// genus oddity computation.
pub fn verify_milgram(lattice: &IntegralForm) -> Option<bool> {
    let disc = DiscriminantForm::from_lattice(lattice)?;
    let phase = disc.milgram_signature_mod8_fqm()?;
    let float_phase = disc.milgram_signature_mod8()?;
    let (pos, neg) = lattice.signature();
    let sig = (pos as i128 - neg as i128).rem_euclid(8);
    let genus_sig = genus_signature_mod8(lattice)?;
    Some(phase == sig && float_phase == sig && genus_sig == sig)
}

/// Report the odd-lattice Milgram/van der Blij signature congruence.
pub fn odd_milgram_report(lattice: &IntegralForm) -> Option<OddMilgramInvariants> {
    let _disc = OddDiscriminantForm::from_lattice(lattice)?;
    let (pos, neg) = lattice.signature();
    let signature_mod8 = (pos as i128 - neg as i128).rem_euclid(8);
    let (oddity_mod8, p_excess_mod8) = genus_oddity_and_p_excess_mod8(lattice)?;
    let corrected_signature_mod8 = (oddity_mod8 - p_excess_mod8).rem_euclid(8);
    Some(OddMilgramInvariants {
        signature_mod8,
        oddity_mod8,
        p_excess_mod8,
        corrected_signature_mod8,
        genus_signature_mod8: genus_signature_mod8(lattice)?,
    })
}

/// Verify the odd-lattice Milgram/van der Blij congruence.
pub fn verify_odd_milgram(lattice: &IntegralForm) -> Option<bool> {
    Some(odd_milgram_report(lattice)?.verified())
}
