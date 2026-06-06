//! The multivector engine, generic over any `Scalar` backend.
//!
//! ## Metric data — characteristic-faithful by design
//!
//! A blade is a `u32` bitmask over basis generators e_0..e_31. The algebra is
//! defined by two independent pieces of data, *not* a single bilinear form:
//!
//!   * `q[i]`      = e_i²                      (the quadratic form / squares)
//!   * `b[(i,j)]`  = e_i e_j + e_j e_i  (i<j)  (the polar / anticommutator form)
//!
//! In characteristic ≠ 2 these are linked (`b = 2·offdiag`, `q = diag`), so an
//! orthogonal basis just sets `b = 0`. In characteristic 2 they are genuinely
//! independent: the polar form is *alternating* (`b(i,i)=0`) yet `q[i]` can be
//! nonzero, and a nonzero off-diagonal `b[(i,j)]` is exactly what makes the
//! nim-Clifford algebra *non-commutative*. Carrying both is the faithful thing.
//!
//! "With nilpotents": set `q[i] = 0` and you get a null generator, e_i² = 0.
//! All `q = 0`, all `b = 0` ⇒ the exterior/Grassmann algebra.
//!
//! ## Product
//!
//! Two canonical blades multiply by concatenating their (ascending) generator
//! lists into a word and reducing to canonical form with the rules
//!   e_i e_i  → q[i]                            (equal adjacent: contract)
//!   e_i e_j  → b[(j,i)] − e_j e_i   (i>j)      (out of order: swap, emit polar)
//! The `−` goes through the scalar's own `neg()`, so in characteristic 2 it is
//! `+` automatically and signs vanish — no special-casing. Termination: each
//! step lowers (word length, inversion count) lexicographically.

use crate::scalar::Scalar;
use std::collections::BTreeMap;

/// Ascending list of set-bit indices of a blade mask.
fn bits(mask: u32) -> Vec<usize> {
    let mut v = Vec::new();
    let mut m = mask;
    while m != 0 {
        let i = m.trailing_zeros() as usize;
        v.push(i);
        m &= m - 1;
    }
    v
}

fn grade(mask: u32) -> u32 {
    mask.count_ones()
}

/// Sign (+1/-1 as a Scalar) of reordering two disjoint ascending blades when
/// concatenated — i.e. the number of (i in a, j in b) with i > j, mod 2.
fn wedge_sign<S: Scalar>(a: u32, b: u32) -> S {
    let mut swaps = 0u32;
    let mut aa = a;
    while aa != 0 {
        let i = aa.trailing_zeros();
        aa &= aa - 1;
        // count bits of b strictly below i
        let below = b & ((1u32 << i) - 1);
        swaps += below.count_ones();
    }
    if swaps & 1 == 0 {
        S::one()
    } else {
        S::one().neg()
    }
}

/// The metric: squares `q` and anticommutators `b` (keyed (i,j) with i<j).
#[derive(Clone, Debug)]
pub struct Metric<S: Scalar> {
    pub q: Vec<S>,
    pub b: BTreeMap<(usize, usize), S>,
}

impl<S: Scalar> Metric<S> {
    /// Orthogonal metric from a list of squares (b = 0). `Cl(p,q,r)` style.
    pub fn diagonal(q: Vec<S>) -> Self {
        Metric { q, b: BTreeMap::new() }
    }

    /// The fully-null metric: exterior/Grassmann algebra on `n` generators.
    pub fn grassmann(n: usize) -> Self {
        Metric { q: vec![S::zero(); n], b: BTreeMap::new() }
    }

    fn q_val(&self, i: usize) -> S {
        self.q.get(i).cloned().unwrap_or_else(S::zero)
    }

    fn b_val(&self, i: usize, j: usize) -> S {
        let key = if i < j { (i, j) } else { (j, i) };
        self.b.get(&key).cloned().unwrap_or_else(S::zero)
    }

    /// Reduce a generator word to canonical multivector terms.
    fn reduce_word(&self, word: &[usize]) -> BTreeMap<u32, S> {
        for p in 0..word.len().saturating_sub(1) {
            let (a, c) = (word[p], word[p + 1]);
            if a == c {
                // e_a e_a = q[a]
                let q = self.q_val(a);
                let mut rest = Vec::with_capacity(word.len() - 2);
                rest.extend_from_slice(&word[..p]);
                rest.extend_from_slice(&word[p + 2..]);
                return scale(self.reduce_word(&rest), &q);
            } else if a > c {
                // e_a e_c = b[(c,a)] - e_c e_a
                let bv = self.b_val(a, c);
                let mut removed = Vec::with_capacity(word.len() - 2);
                removed.extend_from_slice(&word[..p]);
                removed.extend_from_slice(&word[p + 2..]);
                let mut out = scale(self.reduce_word(&removed), &bv);

                let mut swapped = word.to_vec();
                swapped.swap(p, p + 1);
                let neg = S::one().neg();
                merge(&mut out, scale(self.reduce_word(&swapped), &neg));
                return out;
            }
        }
        // strictly increasing & distinct → a single canonical blade
        let mut mask = 0u32;
        for &g in word {
            mask |= 1 << g;
        }
        let mut m = BTreeMap::new();
        m.insert(mask, S::one());
        m
    }
}

fn scale<S: Scalar>(mut terms: BTreeMap<u32, S>, s: &S) -> BTreeMap<u32, S> {
    if s.is_zero() {
        return BTreeMap::new();
    }
    for v in terms.values_mut() {
        *v = v.mul(s);
    }
    terms.retain(|_, v| !v.is_zero());
    terms
}

fn merge<S: Scalar>(into: &mut BTreeMap<u32, S>, other: BTreeMap<u32, S>) {
    for (blade, coeff) in other {
        let e = into.entry(blade).or_insert_with(S::zero);
        *e = e.add(&coeff);
        if e.is_zero() {
            into.remove(&blade);
        }
    }
}

/// A multivector: blade-mask → coefficient (zeros never stored).
#[derive(Clone, Debug, PartialEq)]
pub struct Multivector<S: Scalar> {
    pub terms: BTreeMap<u32, S>,
}

/// A Clifford algebra: dimension + metric. Produces and combines multivectors.
#[derive(Clone, Debug)]
pub struct CliffordAlgebra<S: Scalar> {
    pub dim: usize,
    pub metric: Metric<S>,
}

impl<S: Scalar> CliffordAlgebra<S> {
    pub fn new(dim: usize, metric: Metric<S>) -> Self {
        CliffordAlgebra { dim, metric }
    }

    pub fn zero(&self) -> Multivector<S> {
        Multivector { terms: BTreeMap::new() }
    }

    pub fn scalar(&self, s: S) -> Multivector<S> {
        let mut terms = BTreeMap::new();
        if !s.is_zero() {
            terms.insert(0u32, s);
        }
        Multivector { terms }
    }

    /// The basis vector e_i.
    pub fn gen(&self, i: usize) -> Multivector<S> {
        let mut terms = BTreeMap::new();
        terms.insert(1u32 << i, S::one());
        Multivector { terms }
    }

    /// A single basis blade from a set of generators, coefficient 1.
    pub fn blade(&self, gens: &[usize]) -> Multivector<S> {
        let mut mask = 0u32;
        for &g in gens {
            mask |= 1 << g;
        }
        let mut terms = BTreeMap::new();
        terms.insert(mask, S::one());
        Multivector { terms }
    }

    pub fn add(&self, a: &Multivector<S>, b: &Multivector<S>) -> Multivector<S> {
        let mut terms = a.terms.clone();
        merge(&mut terms, b.terms.clone());
        Multivector { terms }
    }

    pub fn scalar_mul(&self, s: &S, a: &Multivector<S>) -> Multivector<S> {
        Multivector { terms: scale(a.terms.clone(), s) }
    }

    /// Geometric (Clifford) product.
    pub fn mul(&self, a: &Multivector<S>, b: &Multivector<S>) -> Multivector<S> {
        let mut out: BTreeMap<u32, S> = BTreeMap::new();
        for (&ba, ca) in &a.terms {
            for (&bb, cb) in &b.terms {
                let mut word = bits(ba);
                word.extend(bits(bb));
                let reduced = self.metric.reduce_word(&word);
                let coeff = ca.mul(cb);
                merge(&mut out, scale(reduced, &coeff));
            }
        }
        Multivector { terms: out }
    }

    /// Exterior (wedge) product — metric-independent.
    pub fn wedge(&self, a: &Multivector<S>, b: &Multivector<S>) -> Multivector<S> {
        let mut out: BTreeMap<u32, S> = BTreeMap::new();
        for (&ba, ca) in &a.terms {
            for (&bb, cb) in &b.terms {
                if ba & bb != 0 {
                    continue; // shared generator ⇒ wedge is 0
                }
                let sign = wedge_sign::<S>(ba, bb);
                let coeff = ca.mul(cb).mul(&sign);
                if coeff.is_zero() {
                    continue;
                }
                let e = out.entry(ba | bb).or_insert_with(S::zero);
                *e = e.add(&coeff);
                if e.is_zero() {
                    out.remove(&(ba | bb));
                }
            }
        }
        Multivector { terms: out }
    }

    /// Reversion: reverse the order of generators in every blade.
    /// On a grade-k blade this is (-1)^{k(k-1)/2}.
    pub fn reverse(&self, a: &Multivector<S>) -> Multivector<S> {
        let mut terms = BTreeMap::new();
        for (&blade, coeff) in &a.terms {
            let k = grade(blade);
            let c = if (k * (k.wrapping_sub(1)) / 2) & 1 == 1 {
                coeff.neg()
            } else {
                coeff.clone()
            };
            if !c.is_zero() {
                terms.insert(blade, c);
            }
        }
        Multivector { terms }
    }

    /// Grade-k projection.
    pub fn grade_part(&self, a: &Multivector<S>, k: u32) -> Multivector<S> {
        let terms = a
            .terms
            .iter()
            .filter(|(&blade, _)| grade(blade) == k)
            .map(|(&blade, c)| (blade, c.clone()))
            .collect();
        Multivector { terms }
    }
}

impl<S: Scalar> Multivector<S> {
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// Human-readable form, e.g. `3 + 2*e0 + 1*e0e1`.
    pub fn display(&self) -> String {
        if self.terms.is_empty() {
            return "0".to_string();
        }
        let one = S::one();
        let neg_one = S::one().neg();
        let mut parts = Vec::new();
        for (&blade, coeff) in &self.terms {
            if blade == 0 {
                parts.push(format!("{:?}", coeff));
                continue;
            }
            let label: String = bits(blade).iter().map(|i| format!("e{}", i)).collect();
            if *coeff == one {
                parts.push(label);
            } else if *coeff == neg_one {
                parts.push(format!("-{}", label));
            } else {
                parts.push(format!("{:?}*{}", coeff, label));
            }
        }
        parts.join(" + ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nimber::Nimber;
    use crate::scalar::Rational;

    fn r(n: i128) -> Rational {
        Rational::int(n)
    }

    #[test]
    fn complex_numbers_cl01() {
        // Cl(0,1): one generator with e0^2 = -1, the complex numbers.
        let alg = CliffordAlgebra::new(1, Metric::diagonal(vec![r(-1)]));
        let e0 = alg.gen(0);
        let sq = alg.mul(&e0, &e0);
        assert_eq!(sq, alg.scalar(r(-1)));
    }

    #[test]
    fn cl20_bivector_squares_to_minus_one() {
        // Cl(2,0): e0^2 = e1^2 = 1; e0e1 anticommutes and (e0e1)^2 = -1.
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![r(1), r(1)]));
        let e0 = alg.gen(0);
        let e1 = alg.gen(1);
        // anticommute: e0e1 = -(e1e0)
        let e0e1 = alg.mul(&e0, &e1);
        let e1e0 = alg.mul(&e1, &e0);
        assert_eq!(e0e1, alg.scalar_mul(&r(-1), &e1e0));
        // (e0e1)^2 = -1
        let sq = alg.mul(&e0e1, &e0e1);
        assert_eq!(sq, alg.scalar(r(-1)));
    }

    #[test]
    fn grassmann_generators_are_nilpotent() {
        // q = 0 ⇒ e_i^2 = 0, and the wedge matches the product off-diagonal.
        let alg = CliffordAlgebra::new(3, Metric::grassmann(3));
        for i in 0..3 {
            let ei = alg.gen(i);
            assert!(alg.mul(&ei, &ei).is_zero(), "e{i}^2 should be 0");
        }
        let (e0, e1) = (alg.gen(0), alg.gen(1));
        assert_eq!(alg.mul(&e0, &e1), alg.wedge(&e0, &e1));
        // antisymmetry
        assert_eq!(alg.mul(&e0, &e1), alg.scalar_mul(&r(-1), &alg.mul(&e1, &e0)));
    }

    #[test]
    fn nimber_orthogonal_is_commutative() {
        // char 2, b = 0 ⇒ e_i e_j = e_j e_i (the genuine char-2-orthogonal fact).
        let alg = CliffordAlgebra::new(2, Metric::diagonal(vec![Nimber(2), Nimber(3)]));
        let e0 = alg.gen(0);
        let e1 = alg.gen(1);
        assert_eq!(alg.mul(&e0, &e1), alg.mul(&e1, &e0)); // commute
        // e0^2 = q0 = 2 (a nimber!), not ±1
        assert_eq!(alg.mul(&e0, &e0), alg.scalar(Nimber(2)));
    }

    #[test]
    fn nimber_offdiagonal_is_noncommutative() {
        // char 2 with b[(0,1)] = t ⇒ e0 e1 + e1 e0 = t ≠ 0 ⇒ non-commutative.
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), Nimber(1));
        let alg = CliffordAlgebra::new(2, Metric { q: vec![Nimber(0), Nimber(0)], b });
        let e0 = alg.gen(0);
        let e1 = alg.gen(1);
        let anti = alg.add(&alg.mul(&e0, &e1), &alg.mul(&e1, &e0));
        assert_eq!(anti, alg.scalar(Nimber(1))); // {e0,e1} = 1
        assert_ne!(alg.mul(&e0, &e1), alg.mul(&e1, &e0)); // not commutative
    }

    // The real stress test of reduce_word: associativity on a nontrivial,
    // non-orthogonal metric, in both characteristics.
    fn assert_associative<S: Scalar>(alg: &CliffordAlgebra<S>, gens: &[Multivector<S>]) {
        for a in gens {
            for b in gens {
                for c in gens {
                    let l = alg.mul(&alg.mul(a, b), c);
                    let r = alg.mul(a, &alg.mul(b, c));
                    assert_eq!(l, r, "associativity failed");
                }
            }
        }
    }

    #[test]
    fn associativity_rational_nonorthogonal() {
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), r(1)); // non-orthogonal
        b.insert((1usize, 2usize), r(-1));
        let alg = CliffordAlgebra::new(3, Metric { q: vec![r(1), r(-1), r(2)], b });
        let gens = [
            alg.gen(0),
            alg.gen(1),
            alg.gen(2),
            alg.mul(&alg.gen(0), &alg.gen(1)),
            alg.add(&alg.gen(0), &alg.scalar(r(3))),
        ];
        assert_associative(&alg, &gens);
    }

    #[test]
    fn associativity_nimber_nonorthogonal() {
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), Nimber(1));
        b.insert((0usize, 2usize), Nimber(3));
        let alg = CliffordAlgebra::new(3, Metric { q: vec![Nimber(2), Nimber(1), Nimber(0)], b });
        let gens = [
            alg.gen(0),
            alg.gen(1),
            alg.gen(2),
            alg.mul(&alg.gen(0), &alg.gen(1)),
            alg.add(&alg.gen(2), &alg.scalar(Nimber(5))),
        ];
        assert_associative(&alg, &gens);
    }
}
