//! Char-2 **nim arithmetic** on ordinals: the transfinite additive group
//! (nim-addition = XOR of like-`ω`-power coefficients) and the field product
//! across `φ_{ω+1}` (ordinals `< ω³`) via the DiMuro/Conway tower. The CNF
//! canonicalizer lives here because its like-term merge *is* the nim addition
//! (XOR); the ordinary-ordinal merge in [`cantor`](super::cantor) builds its
//! terms directly instead. See the [module overview](super) for the field tower.

use super::Ordinal;
use crate::scalar::nim_mul;
use std::collections::BTreeMap;

/// A **tower element**: a sparse map from a *generator-power key* to a finite-nimber
/// coefficient. The key is the base-3 digit vector `(d₀, d₁, …)` of an exponent,
/// where digit `dₖ` is the power of the generator `gₖ = ω^(3ᵏ)` (each `dₖ < 3` in
/// canonical form). So the ordinal `ω^e · c` (finite `e = Σ dₖ·3ᵏ`) is the single
/// entry `key ↦ c`, and a general ordinal `< ω^ω` is the XOR of its terms' entries.
/// This is the recursive view that generalizes the flat `[c₀,c₁,c₂]`-mod-`(ω³−2)`
/// representation (which is the one-generator, `key.len() ≤ 1` special case).
type TowerElem = BTreeMap<Vec<u8>, u128>;

/// The base-3 digit vector of a finite exponent `e` (least-significant first, no
/// trailing zeros). `e = 0` ⇒ the empty key (the scalar position `ω^0`).
fn base3_digits(mut e: u128) -> Vec<u8> {
    let mut v = Vec::new();
    while e > 0 {
        v.push((e % 3) as u8);
        e /= 3;
    }
    v
}

/// Reduce a raw generator-power vector (digits may be `≥ 3`) to canonical digits
/// `< 3` plus an accumulated finite-nimber scalar, via the cube-root relations
/// `gₖ³ = g_{k-1}` (three at place `k` ⇒ one at place `k−1`) and `g₀³ = 2` (three at
/// place 0 ⇒ the scalar `2`). Processing high → low lets a single pass suffice
/// (each place carries at most once for a digit `≤ 4`).
fn reduce_key(raw: &[u32]) -> (Vec<u8>, u128) {
    let mut d: Vec<u32> = raw.to_vec();
    let mut s = 1u128;
    for k in (0..d.len()).rev() {
        while d[k] >= 3 {
            d[k] -= 3;
            if k == 0 {
                s = nim_mul(s, 2);
            } else {
                d[k - 1] += 1;
            }
        }
    }
    let mut key: Vec<u8> = d.iter().map(|&x| x as u8).collect();
    while key.last() == Some(&0) {
        key.pop();
    }
    (key, s)
}

/// Nim-multiply two tower elements. For each pair of monomials, the generator-power
/// vectors **add** (ordinary integer addition — `gₖ^i ⊗ gₖ^j = gₖ^{i+j}`), the
/// coefficients nim-multiply, the result is reduced to canonical digits, and like
/// terms XOR-accumulate (char 2).
fn tower_mul(a: &TowerElem, b: &TowerElem) -> TowerElem {
    let mut out: TowerElem = BTreeMap::new();
    for (ka, &va) in a {
        if va == 0 {
            continue;
        }
        for (kb, &vb) in b {
            if vb == 0 {
                continue;
            }
            let len = ka.len().max(kb.len());
            let raw: Vec<u32> = (0..len)
                .map(|i| {
                    ka.get(i).copied().unwrap_or(0) as u32 + kb.get(i).copied().unwrap_or(0) as u32
                })
                .collect();
            let (rk, s1) = reduce_key(&raw);
            let coeff = nim_mul(nim_mul(va, vb), s1);
            *out.entry(rk).or_insert(0) ^= coeff;
        }
    }
    out
}

/// Sort a raw term list into descending CNF and merge like `ω`-powers by **XOR**
/// (nim-addition of coefficients), dropping zeros. Exponents order by the ordinal
/// *lexicographic* order (coefficients are positive naturals, so structure and
/// value agree — unlike the surreals). The descending-merge recipe is shared with
/// the surreal backend via [`cnf::merge_descending`](super::super::cnf::merge_descending);
/// the XOR merge is exactly what makes the coefficient ring char 2.
fn canonicalize(raw: Vec<(Ordinal, u128)>) -> Vec<(Ordinal, u128)> {
    super::super::cnf::merge_descending(raw, |a, b| a.cmp(b), |x, y| x ^ y, |c| *c == 0)
}

impl Ordinal {
    /// Nim-addition: XOR the coefficients of like `ω`-powers. Complete and exact.
    pub fn nim_add(&self, other: &Ordinal) -> Ordinal {
        let mut raw = self.terms.clone();
        raw.extend(other.terms.iter().cloned());
        Ordinal {
            terms: canonicalize(raw),
        }
    }

    /// View this ordinal as an element of the field `φ_{ω+1}` (ordinals `< ω³`
    /// Cantor) — i.e. `ω²·c₂ + ω·c₁ + c₀` with each `cᵢ` finite. Returns the
    /// coefficient vector `[c₀, c₁, c₂]`, or `None` if any CNF exponent is `≥ 3`
    /// (the ordinal lives in a higher, still-staged field).
    pub fn as_below_omega3(&self) -> Option<[u128; 3]> {
        let mut coeffs = [0u128; 3];
        for (exp, c) in &self.terms {
            let e = exp.as_finite()?;
            if e >= 3 {
                return None;
            }
            coeffs[e as usize] = *c;
        }
        Some(coeffs)
    }

    /// Build the ordinal `ω²·c₂ + ω·c₁ + c₀` from its `φ_{ω+1}` coefficients.
    pub fn from_omega3_coeffs(c: [u128; 3]) -> Self {
        let mut raw = Vec::new();
        for (i, &v) in c.iter().enumerate() {
            if v != 0 {
                raw.push((Ordinal::from_u128(i as u128), v));
            }
        }
        Ordinal {
            terms: canonicalize(raw),
        }
    }

    /// View this ordinal as a [`TowerElem`] of the degree-3ⁿ cube-root tower —
    /// every ordinal `< ω^ω` (all CNF exponents finite). Returns `None` if any
    /// exponent is infinite (`≥ ω`), i.e. the ordinal is `≥ ω^ω` and lives above
    /// the implemented tower.
    fn as_below_omega_omega(&self) -> Option<TowerElem> {
        let mut t: TowerElem = BTreeMap::new();
        for (exp, c) in &self.terms {
            let e = exp.as_finite()?; // infinite exponent ⇒ ≥ ω^ω, staged
            *t.entry(base3_digits(e)).or_insert(0) ^= *c;
        }
        Some(t)
    }

    /// Rebuild an ordinal from a [`TowerElem`] (inverse of [`as_below_omega_omega`]):
    /// each key `(d₀,d₁,…)` becomes the exponent `e = Σ dₖ·3ᵏ`, emitting `ω^e · c`.
    fn from_tower_elem(t: &TowerElem) -> Self {
        let mut raw = Vec::new();
        for (key, &c) in t {
            if c == 0 {
                continue;
            }
            let mut e: u128 = 0;
            let mut pow: u128 = 1;
            for &d in key {
                e += d as u128 * pow;
                pow *= 3;
            }
            raw.push((Ordinal::from_u128(e), c));
        }
        Ordinal {
            terms: canonicalize(raw),
        }
    }

    /// Nim-multiplication. Exact across the **degree-3ⁿ cube-root tower** — every
    /// pair of ordinals `< ω^ω` — via the generators `gₙ = ω^(3ⁿ)` with `g₀³ = 2`
    /// and `gₙ³ = g_{n-1}` (Conway / DiMuro; see the module docs). An ordinal
    /// `< ω^ω` is a multivariate monomial in the `gₙ` (base-3 digits of its
    /// exponents, each `≤ 2`), so the product is digit-vector addition with
    /// cube-root carries ([`tower_mul`]). This strictly subsumes the old
    /// `< ω³`, `(ω³−2)`-reduction path (the one-generator case).
    ///
    /// Returns `None` only when an operand has an **infinite** CNF exponent
    /// (`≥ ω^ω`) — the higher tower (other primes, the `ω^ω …` levels) is staged.
    pub fn nim_mul(&self, other: &Ordinal) -> Option<Ordinal> {
        // Zero is absorbing in any field.
        if self.is_zero() || other.is_zero() {
            return Some(Ordinal::zero());
        }
        // Fast path: finite × finite is the proven `nimber::nim_mul`.
        if let (Some(a), Some(b)) = (self.as_finite(), other.as_finite()) {
            return Some(Ordinal::from_u128(nim_mul(a, b)));
        }
        // Tower path: both ordinals are < ω^ω (all CNF exponents finite).
        if let (Some(a), Some(b)) = (self.as_below_omega_omega(), other.as_below_omega_omega()) {
            return Some(Ordinal::from_tower_elem(&tower_mul(&a, &b)));
        }
        // ω^ω and above — the higher Lenstra tower is staged (Stage B).
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fin(n: u128) -> Ordinal {
        Ordinal::from_u128(n)
    }

    #[test]
    fn nim_add_is_xor_below_omega() {
        for a in 0..16u128 {
            for b in 0..16u128 {
                assert_eq!(fin(a).nim_add(&fin(b)), fin(a ^ b));
            }
        }
    }

    #[test]
    fn self_inverse_and_cancellation() {
        let omega = Ordinal::omega();
        // ω ⊕ ω = 0
        assert!(omega.nim_add(&omega).is_zero());
        // (ω·3) ⊕ (ω·3) = 0
        let w3 = Ordinal::monomial(fin(1), 3);
        assert!(w3.nim_add(&w3).is_zero());
        // (ω + 1) ⊕ 1 = ω
        let w_plus_1 = omega.nim_add(&fin(1));
        assert_eq!(w_plus_1.nim_add(&fin(1)), omega);
        // ω·2 ⊕ ω = ω·3  (coefficients XOR: 2 ⊕ 1 = 3)
        let w2 = Ordinal::monomial(fin(1), 2);
        assert_eq!(w2.nim_add(&omega), Ordinal::monomial(fin(1), 3));
    }

    #[test]
    fn additive_group_axioms_with_infinite_terms() {
        let a = Ordinal::omega().nim_add(&fin(2)); // ω + 2
        let b = Ordinal::omega_pow(fin(2)).nim_add(&fin(1)); // ω² + 1
        let c = Ordinal::monomial(fin(1), 5); // ω·5
                                              // associativity + commutativity
        assert_eq!(a.nim_add(&b).nim_add(&c), a.nim_add(&b.nim_add(&c)));
        assert_eq!(a.nim_add(&b), b.nim_add(&a));
        // identity + self-inverse
        assert_eq!(a.nim_add(&Ordinal::zero()), a);
        assert!(a.nim_add(&a).is_zero());
    }

    #[test]
    fn finite_nim_mul_agrees_with_nimber() {
        for a in 0..16u128 {
            for b in 0..16u128 {
                assert_eq!(fin(a).nim_mul(&fin(b)), Some(fin(nim_mul(a, b))));
            }
        }
    }

    #[test]
    fn omega_squared_is_omega_squared() {
        // The minimal computation: ω ⊗ ω = ω² (just polynomial multiplication
        // before any reduction kicks in).
        let omega = Ordinal::omega();
        assert_eq!(omega.nim_mul(&omega).unwrap(), Ordinal::omega_pow(fin(2)));
    }

    #[test]
    fn omega_cubed_is_two() {
        // The headline (Conway/DiMuro): ω is the nim cube root of 2. This is the
        // identity that makes F_2(ω) ≅ F_8 — the cube root x³ = 2 has no
        // solution in any finite F_{2^{2^k}}, so ω supplies it.
        let omega = Ordinal::omega();
        let omega_sq = omega.nim_mul(&omega).unwrap();
        let omega_cubed = omega_sq.nim_mul(&omega).unwrap();
        assert_eq!(omega_cubed, fin(2));
        // And ω² ⊗ ω² = ω⁴ = 2⊗ω.
        assert_eq!(
            omega_sq.nim_mul(&omega_sq).unwrap(),
            Ordinal::monomial(fin(1), 2)
        );
    }

    #[test]
    fn omega_plus_one_squared_and_cubed_by_hand() {
        // (ω+1)² in characteristic 2 = ω² + 1 (cross terms vanish since 1+1=0).
        let w_plus_1 = Ordinal::omega().nim_add(&fin(1));
        let sq = w_plus_1.nim_mul(&w_plus_1).unwrap();
        assert_eq!(sq, Ordinal::omega_pow(fin(2)).nim_add(&fin(1)));
        // (ω+1)³ = (ω+1)·(ω²+1) = ω³ + ω² + ω + 1 = 2 + ω² + ω + 1 = ω² + ω + 3,
        // since nim_add(2, 1) = 2 ⊕ 1 = 3.
        let cubed = sq.nim_mul(&w_plus_1).unwrap();
        let expected = Ordinal::from_omega3_coeffs([3, 1, 1]); // ω² + ω + 3
        assert_eq!(cubed, expected);
    }

    #[test]
    fn f4_adjoin_omega_is_a_field() {
        // The decisive check: F_4(ω) = F_64 (a genuine degree-3 extension of F_4
        // by ω, with ω³ = 2) is closed under the new nim-multiplication and
        // satisfies every field axiom. 64 elements ⇒ 64² × associativity, etc.
        let elems: Vec<Ordinal> = (0..64u128)
            .map(|i| Ordinal::from_omega3_coeffs([i & 3, (i >> 2) & 3, (i >> 4) & 3]))
            .collect();
        let zero = Ordinal::zero();
        let one = fin(1);

        // closure + commutativity (and incidentally that all 64 are distinct).
        for a in &elems {
            for b in &elems {
                let ab = a.nim_mul(b).expect("F_4(ω) is closed");
                assert!(elems.iter().any(|e| e == &ab), "product escaped F_4(ω)");
                assert_eq!(ab, b.nim_mul(a).unwrap(), "non-commutative");
            }
        }

        // associativity of × + distributivity over ⊕.
        for a in &elems {
            for b in &elems {
                for c in &elems {
                    let lhs = a.nim_mul(b).unwrap().nim_mul(c).unwrap();
                    let rhs = a.nim_mul(&b.nim_mul(c).unwrap()).unwrap();
                    assert_eq!(lhs, rhs, "× not associative");
                    let lhs = a.nim_mul(&b.nim_add(c)).unwrap();
                    let rhs = a.nim_mul(b).unwrap().nim_add(&a.nim_mul(c).unwrap());
                    assert_eq!(lhs, rhs, "× not distributive over ⊕");
                }
            }
        }

        // every nonzero element has a multiplicative inverse (search the field).
        for a in elems.iter().filter(|e| !e.is_zero()) {
            let inv = elems
                .iter()
                .find(|b| a.nim_mul(b).unwrap() == one)
                .unwrap_or_else(|| panic!("no inverse for {a:?}"));
            assert_eq!(a.nim_mul(inv).unwrap(), one);
        }

        // and zero is absorbing (sanity).
        for a in &elems {
            assert_eq!(zero.nim_mul(a).unwrap(), zero);
        }
    }

    #[test]
    fn cube_root_tower_relations() {
        // The generators gₙ = ω^(3ⁿ) and their cube-root relations gₙ³ = g_{n-1}.
        let omega = Ordinal::omega(); // g_0
        let w3 = Ordinal::omega_pow(fin(3)); // g_1 = ω^3
        let w9 = Ordinal::omega_pow(fin(9)); // g_2 = ω^9
                                             // (ω^3)² = ω^6, (ω^3) ⊗ ω = ω^4 (the worked examples)
        assert_eq!(w3.nim_mul(&w3).unwrap(), Ordinal::omega_pow(fin(6)));
        assert_eq!(w3.nim_mul(&omega).unwrap(), Ordinal::omega_pow(fin(4)));
        // g_1³ = g_0:  (ω^3)⊗³ = ω
        let w3_cubed = w3.nim_mul(&w3).unwrap().nim_mul(&w3).unwrap();
        assert_eq!(w3_cubed, omega);
        // g_2³ = g_1:  (ω^9)⊗³ = ω^3
        let w9_cubed = w9.nim_mul(&w9).unwrap().nim_mul(&w9).unwrap();
        assert_eq!(w9_cubed, w3);
    }

    #[test]
    fn consistency_with_below_omega3_path() {
        // The new tower path must agree, element-for-element, with the old
        // [c₀,c₁,c₂]-mod-(ω³−2) reduction on every pair of φ_{ω+1} elements — the
        // proof the generalization is faithful on the overlap.
        let elems: Vec<Ordinal> = (0..64u128)
            .map(|i| Ordinal::from_omega3_coeffs([i & 3, (i >> 2) & 3, (i >> 4) & 3]))
            .collect();
        for a in &elems {
            for b in &elems {
                let (ca, cb) = (a.as_below_omega3().unwrap(), b.as_below_omega3().unwrap());
                let mut p = [0u128; 5];
                for (i, &ai) in ca.iter().enumerate() {
                    for (j, &bj) in cb.iter().enumerate() {
                        p[i + j] ^= nim_mul(ai, bj);
                    }
                }
                let old = Ordinal::from_omega3_coeffs([
                    p[0] ^ nim_mul(2, p[3]),
                    p[1] ^ nim_mul(2, p[4]),
                    p[2],
                ]);
                assert_eq!(a.nim_mul(b).unwrap(), old, "tower path disagrees with old");
            }
        }
    }

    #[test]
    fn tower_multiplication_ring_axioms() {
        // The field generated by ω^3 (= g_1) is F_2(ω,ω^3) = F_{2^18} — far too big
        // to enumerate (g_0³=2 already drags in F_4, so it is *not* the naive
        // 0/1-combination of ω^0..ω^8). So the decisive Stage-A check is the
        // commutative-ring axioms on a varied sample of ordinals < ω^ω spanning
        // several generators (exponents up to 27 = 3³, i.e. g_3) and coeffs in
        // F_4 — exercising the digit-carry reduction across the whole tower.
        // Inverses/closure at the g_0 level remain exhaustively pinned by the
        // F_64 test above.
        let mut elems: Vec<Ordinal> = Vec::new();
        for &e in &[0u128, 1, 2, 3, 4, 5, 6, 8, 9, 10, 18, 27] {
            for c in 1..=3u128 {
                elems.push(Ordinal::monomial(fin(e), c));
            }
        }
        // a few genuinely multi-term ordinals.
        elems.push(Ordinal::omega().nim_add(&fin(1))); // ω + 1
        elems.push(
            Ordinal::omega_pow(fin(3))
                .nim_add(&Ordinal::omega())
                .nim_add(&fin(2)),
        ); // ω^3 + ω + 2
        elems.push(Ordinal::omega_pow(fin(9)).nim_add(&Ordinal::omega_pow(fin(3)))); // ω^9 + ω^3

        for a in &elems {
            for b in &elems {
                // every product is defined (all exponents finite ⇒ < ω^ω) …
                let ab = a.nim_mul(b).expect("< ω^ω is closed under ⊗");
                // … and commutative.
                assert_eq!(ab, b.nim_mul(a).unwrap(), "non-commutative");
                for c in &elems {
                    let l = ab.nim_mul(c).unwrap();
                    let r = a.nim_mul(&b.nim_mul(c).unwrap()).unwrap();
                    assert_eq!(l, r, "× not associative");
                    let l = a.nim_mul(&b.nim_add(c)).unwrap();
                    let r = ab.nim_add(&a.nim_mul(c).unwrap());
                    assert_eq!(l, r, "× not distributive over ⊕");
                }
            }
        }
    }

    #[test]
    fn staging_boundary_is_omega_omega() {
        // The boundary moved up from ω³ to ω^ω: ordinals with FINITE exponents
        // (< ω^ω) all multiply; the first INFINITE exponent (ω^ω) is staged.
        let omega = Ordinal::omega();
        // ω^3 (and any finite-exponent ordinal) now multiplies fine.
        assert!(Ordinal::omega_pow(fin(3)).nim_mul(&omega).is_some());
        assert!(Ordinal::omega_pow(fin(100)).nim_mul(&omega).is_some());
        // ω^ω and above (infinite exponent) are the staged Stage-B tower.
        let omega_omega = Ordinal::omega_pow(omega.clone());
        assert_eq!(omega_omega.nim_mul(&omega), None);
        assert_eq!(omega.nim_mul(&omega_omega), None);
        assert_eq!(omega_omega.nim_mul(&omega_omega), None);
    }
}
