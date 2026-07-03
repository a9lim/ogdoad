//! Bridge K — the **full `ℚ/ℤ` ungraded Brauer invariant** from cyclic algebras.
//!
//! Bridge F (`brauer_rational.rs`) computes the **2-torsion** rational Brauer class
//! as a set of ramified places (`inv_v ∈ {0, ½}`). This module lifts that surface to
//! the **full local Brauer group** `Br(K_v) ≅ ℚ/ℤ`, the image of a **cyclic algebra**
//! `(χ_σ, a)` under the local invariant map of class field theory. Standard math
//! (Serre, *Local Fields*, Ch. XII; Gille–Szamuely §6.3–6.4; Reiner §§31–32) made
//! computational — *not* a new theorem, the same status the shipped bridges hold.
//!
//! ## The cyclic algebra and its local invariant
//!
//! A cyclic extension `E/K` of degree `n` with distinguished generator `σ` and an
//! element `a ∈ K*` defines `(χ_σ, a) = ⊕_{i<n} E·uⁱ`, `uⁿ = a`, `u·x = σ(x)·u` — a
//! central simple `K`-algebra of degree `n`. When `K` is local and `E/K` is
//! **unramified** with `σ` the **arithmetic Frobenius** (the convention every
//! [`CyclicGaloisExtension`] `sigma()` in this crate uses), the invariant map sends
//!
//! ```text
//! inv_K[(χ_σ, a)] = v(a)/n  (mod ℤ) ∈ (1/n)ℤ/ℤ ⊂ ℚ/ℤ,
//! ```
//!
//! the **full** local Brauer group, not just its 2-torsion. The value reads only the
//! valuation `v(a)` and the degree `n = [E:K]`; `σ` fixes the *sign* convention
//! (`χ_σ(σ) = +1/n`, arithmetic Frobenius — a geometric-Frobenius choice negates it),
//! not the magnitude. So [`cyclic_algebra_invariant`] is a two-line function over any
//! [`Valued`] base — in practice [`Qq`](crate::scalar::Qq)`<P,N,F>` over
//! `Q_p = Qq<P,N,1>`, the only [`CyclicGaloisExtension`] whose base is local.
//!
//! ## The ℚ/ℤ class and the Bridge F embedding
//!
//! [`BrauerClass`] carries `inv_v ∈ ℚ/ℤ` per place, with additive (mod-`ℤ`) law. The
//! 2-torsion [`Brauer2Class`] embeds as the `½`-slice
//! ([`from_two_torsion`](BrauerClass::from_two_torsion) /
//! [`two_torsion`](BrauerClass::two_torsion)): all of Bridge F — quadratic-form Brauer
//! classes are 2-torsion — lands inside this ambient group, which additionally sees the
//! `n>2` classes Bridge F cannot. One ambient group, two constructors.
//!
//! ## Scope (honest boundaries)
//!
//! - [`cyclic_algebra_invariant`] is **unramified-at-`v` only**: the `v(a)/n`
//!   formula applies to the unramified cyclic character. The tame Kummer slice is
//!   separate: [`tame_symbol_exponent`] / [`tame_symbol_invariant`] implement the
//!   explicit residue tame symbol when `n | |κ*|`. Wild symbols remain out of scope.
//! - **Ungraded** Brauer group — kept strictly distinct from the graded
//!   [`BrauerWallClass`](crate::forms::bw_class_real), exactly as Bridge F insists.
//! - The archimedean place (`Br(ℝ) = ½ℤ/ℤ`) and the finite legs carry no `v(a)/n`
//!   invariant: over a finite field every central simple algebra splits (Wedderburn),
//!   so the Gold forms have no `inv`; their classifier is Arf/Brauer–Wall (Bridge B).
//!   The real place enters only through the 2-torsion [`from_two_torsion`] embedding.

use std::collections::{BTreeMap, BTreeSet};

use crate::forms::{Brauer2Class, Place};
use crate::scalar::{
    CyclicGaloisExtension, ExactFieldScalar, Fp, Fpn, Rational, ResidueField, Scalar, Valued,
};

/// The canonical representative in `[0, 1)` of a rational's class mod `ℤ`:
/// `(num mod den)/den` (the denominator is always `> 0`). Tiny exact arithmetic —
/// the inputs here are `deg·v/n` with all parts small.
fn frac_mod_one(r: &Rational) -> Rational {
    Rational::try_new(r.numer().rem_euclid(r.denom()), r.denom())
        .expect("a positive denominator stays valid under rem_euclid")
}

/// Finite residue fields whose multiplicative group can be enumerated to evaluate
/// the tame Kummer symbol. This is a form-theory capability, not a new scalar
/// supertrait: callers use it only when the local field contains the relevant
/// `n`th roots of unity (`n | |κ*|`).
pub trait TameSymbolResidueField: ExactFieldScalar + Copy {
    /// The residue-field order `|κ|`.
    fn tame_field_order() -> Option<u128>;

    /// Enumerate the field: `i in [0, |κ|)` maps to a distinct element.
    fn tame_from_index(i: u128) -> Self;
}

impl<const P: u128> TameSymbolResidueField for Fp<P> {
    fn tame_field_order() -> Option<u128> {
        Fp::<P>::modulus_is_prime().then_some(P)
    }

    fn tame_from_index(i: u128) -> Self {
        Fp::<P>::from_u128(i)
    }
}

impl<const P: u128, const N: usize> TameSymbolResidueField for Fpn<P, N> {
    fn tame_field_order() -> Option<u128> {
        Fpn::<P, N>::field_order_checked()
    }

    fn tame_from_index(mut i: u128) -> Self {
        let mut coeffs = [0u128; N];
        for c in &mut coeffs {
            *c = i % P;
            i /= P;
        }
        Fpn::<P, N>::from_coeffs(&coeffs)
    }
}

/// The tame-symbol exponent's signed power in the residue field: `base^e` for
/// `e ≥ 0`, `base⁻¹^|e|` for `e < 0`. Thin wrapper over [`Scalar::pow`] (the
/// unsigned case) — the signed extension is what earns this its own name.
fn residue_pow_signed<F: TameSymbolResidueField>(base: F, e: i128) -> Option<F> {
    if e >= 0 {
        Some(base.pow(e as u128))
    } else {
        Some(base.inv()?.pow(e.unsigned_abs()))
    }
}

fn residue_order<F: TameSymbolResidueField>(x: F) -> Option<u128> {
    if x.is_zero() {
        return None;
    }
    let group = F::tame_field_order()?.checked_sub(1)?;
    let mut cur = F::one();
    for k in 1..=group {
        cur = cur.mul(&x);
        if cur == F::one() {
            return Some(k);
        }
    }
    None
}

fn residue_primitive<F: TameSymbolResidueField>() -> Option<F> {
    let group = F::tame_field_order()?.checked_sub(1)?;
    for i in 1..F::tame_field_order()? {
        let g = F::tame_from_index(i);
        if residue_order(g) == Some(group) {
            return Some(g);
        }
    }
    None
}

fn residue_discrete_log<F: TameSymbolResidueField>(base: F, x: F) -> Option<u128> {
    if base.is_zero() || x.is_zero() {
        return None;
    }
    let order = residue_order(base)?;
    let mut cur = F::one();
    for e in 0..order {
        if cur == x {
            return Some(e);
        }
        cur = cur.mul(&base);
    }
    None
}

fn residue_tame_raw<F: TameSymbolResidueField>(
    alpha: i128,
    beta: i128,
    a_unit: F,
    b_unit: F,
) -> Option<F> {
    let mut raw = F::one();
    if alpha.rem_euclid(2) == 1 && beta.rem_euclid(2) == 1 {
        raw = raw.neg();
    }
    raw = raw.mul(&residue_pow_signed(a_unit, beta)?);
    raw = raw.mul(&residue_pow_signed(b_unit, -alpha)?);
    Some(raw)
}

fn residue_tame_symbol_exponent<F: TameSymbolResidueField>(
    n: u128,
    alpha: i128,
    beta: i128,
    a_unit: F,
    b_unit: F,
) -> Option<u128> {
    if n == 0 {
        return None;
    }
    let group = F::tame_field_order()?.checked_sub(1)?;
    if group % n != 0 {
        return None;
    }
    if n == 1 {
        return Some(0);
    }
    let raw = residue_tame_raw(alpha, beta, a_unit, b_unit)?;
    let primitive = residue_primitive::<F>()?;
    Some(residue_discrete_log(primitive, raw)? % n)
}

/// The **ungraded** Brauer class with values in `ℚ/ℤ`: the map `v ↦ inv_v` over the
/// places of a global field, each stored as its canonical representative in `[0, 1)`,
/// with zero entries omitted (so the split class is the empty map). The group law is
/// entrywise addition mod `ℤ`.
///
/// This is the full-`ℚ/ℤ` ambient group of which Bridge F's 2-torsion
/// [`Brauer2Class`] is the `½`-slice (see
/// [`from_two_torsion`](Self::from_two_torsion) / [`two_torsion`](Self::two_torsion)).
/// Keyed by [`Place`] (`ℝ` before `Prime(p)`, the order `Place` derives); the
/// function-field leg returns a `Vec<(FunctionFieldPlace, _)>` instead, since
/// [`FunctionFieldPlace`](crate::forms::FunctionFieldPlace) is not `Ord`.
///
/// (`PartialEq` only — [`Rational`] is `PartialEq` but not `Eq`.)
#[derive(Debug, Clone, PartialEq)]
pub struct BrauerClass {
    /// `inv_v ∈ ℚ/ℤ`, canonical representative in `[0, 1)`; zero entries omitted.
    local: BTreeMap<Place, Rational>,
}

impl BrauerClass {
    /// The split (trivial) class: `inv_v = 0` everywhere.
    pub fn split() -> Self {
        BrauerClass {
            local: BTreeMap::new(),
        }
    }

    /// Whether this is the split class.
    pub fn is_split(&self) -> bool {
        self.local.is_empty()
    }

    /// The nonzero local invariants `v ↦ inv_v ∈ [0, 1)`.
    pub fn local(&self) -> &BTreeMap<Place, Rational> {
        &self.local
    }

    /// The local invariant `inv_v ∈ ℚ/ℤ` at a place (its `[0, 1)` representative;
    /// `0` if the class is unramified there).
    pub fn local_invariant(&self, place: Place) -> Rational {
        self.local
            .get(&place)
            .cloned()
            .unwrap_or_else(Rational::zero)
    }

    /// Build a class from raw `(place, inv)` entries: each `inv` is reduced mod `ℤ`
    /// to `[0, 1)` and zero entries are dropped. Callers pass distinct places (a
    /// repeated place keeps the last value, not a sum — use [`add`](Self::add) to
    /// combine classes).
    pub fn from_local(entries: impl IntoIterator<Item = (Place, Rational)>) -> Self {
        let mut local = BTreeMap::new();
        for (place, inv) in entries {
            let r = frac_mod_one(&inv);
            if !r.is_zero() {
                local.insert(place, r);
            }
        }
        BrauerClass { local }
    }

    /// The Brauer-group sum (tensor product of algebras): entrywise addition of
    /// invariants mod `ℤ`, dropping places that cancel to `0`. Generalizes the
    /// 2-torsion XOR of [`Brauer2Class::add`] to all of `ℚ/ℤ`.
    pub fn add(&self, other: &Self) -> Self {
        let mut local = self.local.clone();
        for (place, inv) in &other.local {
            let sum = frac_mod_one(
                &local
                    .get(place)
                    .cloned()
                    .unwrap_or_else(Rational::zero)
                    .add(inv),
            );
            if sum.is_zero() {
                local.remove(place);
            } else {
                local.insert(*place, sum);
            }
        }
        BrauerClass { local }
    }

    /// The sum `∑_v inv_v` mod `ℤ` — the reduced value in `[0, 1)`. For a **global**
    /// Brauer class it is `0` (the Albert–Brauer–Hasse–Noether reciprocity law; the
    /// full-`ℚ/ℤ` strengthening of Bridge F's even-ramification statement).
    pub fn invariant_sum(&self) -> Rational {
        frac_mod_one(
            &self
                .local
                .values()
                .fold(Rational::zero(), |acc, inv| acc.add(inv)),
        )
    }

    /// Embed Bridge F's 2-torsion [`Brauer2Class`] as the `½`-slice: every ramified
    /// place `v` gets `inv_v = ½`. A group monomorphism onto the 2-torsion of
    /// `⊕_v ℚ/ℤ` (XOR of indicator sets = addition of `½`'s mod `1`).
    pub fn from_two_torsion(class: &Brauer2Class) -> Self {
        let half = Rational::try_new(1, 2).expect("1/2 is a valid rational");
        BrauerClass {
            local: class
                .ramified_places()
                .iter()
                .map(|&place| (place, half.clone()))
                .collect(),
        }
    }

    /// Recover the 2-torsion ramification set when this class **is** 2-torsion (every
    /// nonzero invariant equals `½`); `None` otherwise. The inverse of
    /// [`from_two_torsion`](Self::from_two_torsion) on the `½`-slice.
    pub fn two_torsion(&self) -> Option<BTreeSet<Place>> {
        let half = Rational::try_new(1, 2).expect("1/2 is a valid rational");
        let mut set = BTreeSet::new();
        for (place, inv) in &self.local {
            if *inv != half {
                return None;
            }
            set.insert(*place);
        }
        Some(set)
    }

    /// `display()` alias kept for Python callers.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for BrauerClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let local: Vec<(String, Rational)> = self
            .local
            .iter()
            .map(|(&place, inv)| (place.to_string(), inv.clone()))
            .collect();
        write!(f, "BrauerClass(local={local:?})")
    }
}

/// The local invariant `inv_K[(χ_σ, a)] = v(a)/n (mod ℤ)` of the **unramified**
/// cyclic algebra `(χ_σ, a)` over a local field `K`, where `n = [E:K]` is the degree
/// of the cyclic extension `E` and `σ` is the arithmetic Frobenius (the convention
/// every [`CyclicGaloisExtension::sigma`] uses). Returns the canonical representative
/// in `[0, 1)`.
///
/// Generic over `E`, but only the **degree** `[E:K]` and the base **valuation**
/// `v(a)` enter the value (the unramified hypothesis collapses the general local
/// symbol to `v(a)/n`); `σ` fixes the sign convention `χ_σ(σ) = +1/n`. In practice
/// `E = Qq<P,N,F>` over `Q_p = Qq<P,N,1>` — the only [`CyclicGaloisExtension`] whose
/// base is [`Valued`]. The image over a fixed `E` is exactly `(1/n)ℤ/ℤ`, the
/// `n`-torsion `Br(K)[n]` (a fixed degree-`n` unramified class generates that cyclic
/// subgroup, not all of `ℚ/ℤ`); the splitting law is `inv = 0 ⇔ n ∣ v(a)`.
///
/// `None` when `v(a)` is unreadable (`a = 0`, i.e. not in `K*`, or precision loss in
/// a capped model) — never a wrong value. Exact even over the capped-precision local
/// models, since only the valuation is read.
pub fn cyclic_algebra_invariant<E>(a: &E::Base) -> Option<Rational>
where
    E: CyclicGaloisExtension,
    E::Base: Valued,
{
    let n = i128::try_from(E::extension_degree()).ok()?;
    let v = a.valuation()?;
    Some(frac_mod_one(&Rational::try_new(v, n)?))
}

/// The exponent `e ∈ {0, …, n−1}` of the tame Kummer norm-residue symbol
/// `(a,b)_v ∈ μ_n`, using the explicit tame formula
///
/// ```text
/// (-1)^{v(a)v(b)} · ac(a)^{v(b)} / ac(b)^{v(a)}  in κ*
/// ```
///
/// projected to `μ_n` by the deterministic primitive-residue generator convention.
/// The returned exponent means `(a,b)_v = ζ_n^e`, where `ζ_n` is the first primitive
/// residue-field generator raised to `(|κ*|/n)`.
///
/// Returns `None` when `a` or `b` is zero, when `n = 0`, when `n ∤ |κ*|`, or when
/// the capped local model cannot supply the valuation/angular component. This is
/// the tame slice only; wild norm-residue symbols stay out of scope.
pub fn tame_symbol_exponent<K>(n: u128, a: &K, b: &K) -> Option<u128>
where
    K: ResidueField,
    K::Residue: TameSymbolResidueField,
{
    let alpha = a.valuation()?;
    let beta = b.valuation()?;
    residue_tame_symbol_exponent(n, alpha, beta, a.residue_unit()?, b.residue_unit()?)
}

/// The local invariant `e/n ∈ ℚ/ℤ` associated to [`tame_symbol_exponent`], reduced
/// to the canonical representative in `[0,1)`. This is the tamely ramified
/// counterpart to the unramified [`cyclic_algebra_invariant`] formula.
pub fn tame_symbol_invariant<K>(n: u128, a: &K, b: &K) -> Option<Rational>
where
    K: ResidueField,
    K::Residue: TameSymbolResidueField,
{
    let e = i128::try_from(tame_symbol_exponent(n, a, b)?).ok()?;
    let ni = i128::try_from(n).ok()?;
    Some(frac_mod_one(&Rational::try_new(e, ni)?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::forms::{brauer_local_invariants, try_hilbert_symbol_qp, try_is_isotropic_at_p};
    use crate::scalar::{FieldExtension, Fpn, Qq, Rational, Surcomplex, WittVec};

    fn half() -> Rational {
        Rational::try_new(1, 2).unwrap()
    }
    fn third() -> Rational {
        Rational::try_new(1, 3).unwrap()
    }
    fn two_thirds() -> Rational {
        Rational::try_new(2, 3).unwrap()
    }
    fn q(n: i128, d: i128) -> Rational {
        Rational::try_new(n, d).unwrap()
    }

    // ───────────────────── BrauerClass: the ℚ/ℤ group law ─────────────────────

    #[test]
    fn display_render_pin() {
        assert_eq!(BrauerClass::split().to_string(), "BrauerClass(local=[])");
        let c = BrauerClass::from_local([(Place::Prime(7), third()), (Place::Real, half())]);
        assert_eq!(
            c.to_string(),
            "BrauerClass(local=[(\"R\", 1/2), (\"Q_7\", 1/3)])"
        );
        assert_eq!(c.display(), c.to_string());
    }

    #[test]
    fn add_is_modular_and_drops_cancellations() {
        // 1/3 + 2/3 = 1 ≡ 0: the place cancels out of the map.
        let a = BrauerClass::from_local([(Place::Prime(7), third())]);
        let b = BrauerClass::from_local([(Place::Prime(7), two_thirds())]);
        assert!(a.add(&b).is_split(), "1/3 + 2/3 ≡ 0 at the place");
        // identity and commutativity.
        assert_eq!(a.add(&BrauerClass::split()), a);
        let c = BrauerClass::from_local([(Place::Prime(5), half())]);
        assert_eq!(a.add(&c), c.add(&a));
        // 1/3 + 1/3 = 2/3 (no cancellation).
        assert_eq!(a.add(&a).local_invariant(Place::Prime(7)), two_thirds());
    }

    #[test]
    fn from_local_reduces_mod_z_and_drops_zeros() {
        // 7/3 ≡ 1/3; 2/2 = 1 ≡ 0 (dropped); −1/3 ≡ 2/3.
        let c = BrauerClass::from_local([
            (Place::Prime(2), q(7, 3)),
            (Place::Prime(3), q(2, 2)),
            (Place::Real, q(-1, 3)),
        ]);
        assert_eq!(c.local_invariant(Place::Prime(2)), third());
        assert!(
            c.local().get(&Place::Prime(3)).is_none(),
            "integer ⇒ dropped"
        );
        assert_eq!(c.local_invariant(Place::Real), two_thirds());
        assert_eq!(c.local_invariant(Place::Prime(11)), Rational::zero());
    }

    #[test]
    fn invariant_sum_reduces_mod_z() {
        // 1/2 + 1/2 = 1 ≡ 0 (a global 2-torsion class).
        let c = BrauerClass::from_local([(Place::Real, half()), (Place::Prime(2), half())]);
        assert_eq!(c.invariant_sum(), Rational::zero());
        // 1/3 + 1/3 + 1/3 = 1 ≡ 0 (a global degree-3 class).
        let d = BrauerClass::from_local([
            (Place::Prime(2), third()),
            (Place::Prime(3), third()),
            (Place::Prime(5), third()),
        ]);
        assert_eq!(d.invariant_sum(), Rational::zero());
        // a non-global collection need not sum to 0.
        assert_eq!(
            BrauerClass::from_local([(Place::Prime(7), third())]).invariant_sum(),
            third()
        );
    }

    // ───────────────────── Bridge F as the 2-torsion slice ─────────────────────

    #[test]
    fn two_torsion_round_trips_with_bridge_f() {
        // Hamilton's quaternions (−1,−1): ramified {ℝ, Q_2}.
        let f = Brauer2Class::quaternion(-1, -1).unwrap();
        let k = BrauerClass::from_two_torsion(&f);
        assert_eq!(k.local_invariant(Place::Real), half());
        assert_eq!(k.local_invariant(Place::Prime(2)), half());
        // back down: every entry is ½, so it round-trips to the ramification set.
        assert_eq!(k.two_torsion().as_ref(), Some(f.ramified_places()));
    }

    #[test]
    fn non_two_torsion_class_has_no_ramification_set() {
        // a genuine degree-3 class is not 2-torsion ⇒ two_torsion() = None.
        let c = BrauerClass::from_local([(Place::Prime(7), third())]);
        assert_eq!(c.two_torsion(), None);
    }

    #[test]
    fn reciprocity_reread_through_brauer_class() {
        // The shipped quaternion reciprocity (Σ inv_v ≡ 0) re-read through the
        // ℚ/ℤ class: from_two_torsion ∘ quaternion has invariant_sum 0, pinning the
        // §5 embedding against `brauer_invariant_sum_is_zero_in_q_mod_z`.
        for (a, b) in [(-1i128, -1i128), (-1, 7), (2, 3), (-3, 5), (6, -7)] {
            let f = Brauer2Class::quaternion(a, b).unwrap();
            assert_eq!(
                BrauerClass::from_two_torsion(&f).invariant_sum(),
                Rational::zero(),
                "reciprocity for ({a},{b})"
            );
        }
    }

    #[test]
    fn from_two_torsion_is_additive() {
        // from_two_torsion is a group hom: XOR of ramification sets ↦ add of ½-slices.
        let x = Brauer2Class::quaternion(-1, -1).unwrap();
        let y = Brauer2Class::quaternion(2, 5).unwrap();
        let lhs = BrauerClass::from_two_torsion(&x.add(&y));
        let rhs = BrauerClass::from_two_torsion(&x).add(&BrauerClass::from_two_torsion(&y));
        assert_eq!(lhs, rhs);
    }

    // ───────────────── cyclic_algebra_invariant over the Qq local leg ─────────────────

    // Base elements live in Q_p = Qq<P,N,1>; the degree-F type parameter is read only
    // for n = [E:K], so the value tests never construct a degree-F element.
    type Qp = Qq<5, 4, 1>;

    #[test]
    fn degree_two_splitting_law() {
        // inv = v(a)/2 mod ℤ: 0 for even v, ½ for odd v (the n=2 splitting law).
        let cases = [(1i128, 0i128), (5, 1), (25, 2), (125, 3)];
        for (a, v) in cases {
            let elt = Qp::from_int(a);
            assert_eq!(elt.valuation(), Some(v), "v_5({a}) = {v}");
            let inv = cyclic_algebra_invariant::<Qq<5, 4, 2>>(&elt).unwrap();
            let expected = if v % 2 == 0 { Rational::zero() } else { half() };
            assert_eq!(inv, expected, "inv of v={v}");
        }
        // a = 0 has no invariant (not in K*).
        assert_eq!(
            cyclic_algebra_invariant::<Qq<5, 4, 2>>(&Qp::from_int(0)),
            None
        );
    }

    #[test]
    fn degree_two_compat_with_shipped_quaternion_invariant() {
        // The lift is a lift: for d = 2 (a nonsquare unit at 5), the degree-2 cyclic
        // invariant over the unramified quadratic equals the shipped quaternion
        // brauer_local_invariants(d, a) at Prime(5), place by place over a v-sweep.
        let d = 2i128; // nonsquare mod 5 (squares are {1,4})
        for (a, v) in [(1i128, 0i128), (5, 1), (25, 2), (125, 3)] {
            // Bridge K (Qq leg): v(a)/2 mod ℤ.
            let k = cyclic_algebra_invariant::<Qq<5, 4, 2>>(&Qp::from_int(a)).unwrap();
            // Bridge F (shipped): the inv at Prime(5) of the quaternion (d, a)_ℚ.
            let invs =
                brauer_local_invariants(&Rational::from_int(d), &Rational::from_int(a)).unwrap();
            let f = invs
                .iter()
                .find(|(pl, _)| *pl == Place::Prime(5))
                .map(|(_, r)| r.clone())
                .unwrap_or_else(Rational::zero);
            assert_eq!(k, f, "K vs F at Prime(5) for v_5(a)={v}");
            // and both equal ½ iff v is odd.
            assert_eq!(k, if v % 2 == 0 { Rational::zero() } else { half() });
        }
    }

    #[test]
    fn degree_three_image_additivity_and_convention() {
        // The image over n=3 is the full (1/3)ℤ/ℤ — not 2-torsion — and the convention
        // is +v/n: v=1 ↦ 1/3, v=2 ↦ 2/3 (a geometric-Frobenius sign would swap them).
        let p = Qp::from_int(5); // v = 1
        let p2 = Qp::from_int(25); // v = 2
        let p3 = Qp::from_int(125); // v = 3
        let i1 = cyclic_algebra_invariant::<Qq<5, 4, 3>>(&p).unwrap();
        let i2 = cyclic_algebra_invariant::<Qq<5, 4, 3>>(&p2).unwrap();
        let i3 = cyclic_algebra_invariant::<Qq<5, 4, 3>>(&p3).unwrap();
        assert_eq!(i1, third());
        assert_eq!(i2, two_thirds(), "convention pin: inv(a²)=2/3, not 1/3");
        assert_eq!(i3, Rational::zero(), "n ∣ v ⇒ splits");
        // additivity: inv(a·a) = inv(a) + inv(a) mod ℤ.
        let aa = p.mul(&p); // v = 2
        assert_eq!(
            cyclic_algebra_invariant::<Qq<5, 4, 3>>(&aa).unwrap(),
            frac_mod_one(&i1.add(&i1))
        );
        // n-torsion: 3·inv(a) ≡ 0.
        assert_eq!(frac_mod_one(&i1.add(&i1).add(&i1)), Rational::zero());
    }

    #[test]
    fn norm_classes_split() {
        // (χ_σ, N_{E/K}(x)) splits: a norm has valuation divisible by n, so inv = 0.
        // Uses a genuinely supported unramified quadratic Q_9/Q_3 (real field arithmetic).
        type Q9 = Qq<3, 3, 2>;
        let g = WittVec::<3, 3, 2>([1, 1]);
        let x = Q9::from_witt(g);
        let nm = FieldExtension::norm(&x); // a Qq<3,3,1> = Q_3 element
        assert_eq!(
            cyclic_algebra_invariant::<Q9>(&nm),
            Some(Rational::zero()),
            "norm class splits"
        );
        // a uniformizer-scaled norm: N(p·x) = p²·N(x), still valuation ≡ 0 mod 2.
        let px = Q9::from_int(3).mul(&x);
        let npx = FieldExtension::norm(&px);
        assert_eq!(cyclic_algebra_invariant::<Q9>(&npx), Some(Rational::zero()));
    }

    // ───────────────── tame ramified local symbols ─────────────────

    #[test]
    fn tame_quadratic_symbol_matches_hilbert_symbol_qp() {
        type Q5 = crate::scalar::Qp<5, 4>;
        for (a, b) in [(2i128, 5i128), (5, 2), (10, 25), (3, 50), (-5, 2)] {
            let exp = tame_symbol_exponent(2, &Q5::from_int(a), &Q5::from_int(b)).unwrap();
            let hilb = try_hilbert_symbol_qp(a, b, 5).unwrap();
            assert_eq!(exp, if hilb == 1 { 0 } else { 1 }, "a={a}, b={b}");
            assert_eq!(
                tame_symbol_invariant(2, &Q5::from_int(a), &Q5::from_int(b)).unwrap(),
                if hilb == 1 { Rational::zero() } else { half() },
                "invariant a={a}, b={b}"
            );
        }
    }

    #[test]
    fn tame_symbol_pins_kummer_sign_convention() {
        type Q5 = crate::scalar::Qp<5, 4>;
        let pi = Q5::from_p_power(1);
        let two = Q5::from_int(2); // first primitive residue generator in F_5*
        assert_eq!(tame_symbol_exponent(4, &two, &pi), Some(1));
        assert_eq!(tame_symbol_invariant(4, &two, &pi), Some(q(1, 4)));
        assert_eq!(
            tame_symbol_exponent(4, &pi, &two),
            Some(3),
            "the requested a^v(b)/b^v(a) convention gives the inverse"
        );
        assert_eq!(tame_symbol_invariant(4, &pi, &two), Some(q(3, 4)));
        assert_eq!(tame_symbol_exponent(3, &two, &pi), None, "3 ∤ |F_5*|");
        assert_eq!(
            tame_symbol_exponent(4, &Q5::zero(), &two),
            None,
            "0 is outside K*"
        );
    }

    #[test]
    fn tame_symbol_reads_extension_residue_field() {
        type Q9 = Qq<3, 3, 2>;
        let pi = Q9::from_p_power(1);
        let g = Q9::teichmuller(Fpn::<3, 2>::primitive_element());
        assert_eq!(
            tame_symbol_exponent(8, &g, &pi),
            Some(1),
            "residue field is F_9, so μ_8 is visible"
        );
        assert_eq!(tame_symbol_invariant(8, &g, &pi), Some(q(1, 8)));
        assert_eq!(tame_symbol_exponent(8, &pi, &g), Some(7));
        assert_eq!(tame_symbol_invariant(8, &pi, &g), Some(q(7, 8)));
    }

    // ───────────────── §6 trace-form tie: the degree-2 norm-form oracle ─────────────────

    #[test]
    fn degree_two_norm_form_oracle() {
        // The cyclic algebra (χ_σ, a) over E = ℚ(i)/ℚ (σ = conjugation) is the
        // quaternion (−1, a)_ℚ. Its reduced-norm form is ⟨1,1,−a,−a⟩ (= ½·Q₁ ⊥
        // (−a/2)·Q₁ with Q₁ = trace_twisted_form::<Surcomplex<Rational>>(1) = ⟨2,2⟩),
        // and the algebra splits at v ⇔ that form is isotropic over ℚ_v ⇔ inv_v = 0.
        // Ties Bridge K's invariant to the shipped Hasse–Minkowski layer.
        use crate::forms::trace_twisted_form;

        // the trace-form half of the tie: Q₁ = ⟨2,2⟩.
        let q1 = trace_twisted_form::<Surcomplex<Rational>>(1);
        assert_eq!(q1.q, vec![Rational::from_int(2), Rational::from_int(2)]);
        assert!(q1.b.is_empty());

        for a in [-7i128, -3, -2, -1, 2, 3, 5, 6, 7] {
            // the 2-torsion class of (−1, a)_ℚ (Bridge F), lifted into ℚ/ℤ (Bridge K).
            let class = BrauerClass::from_two_torsion(&Brauer2Class::quaternion(-1, a).unwrap());
            // the reduced-norm form ⟨1,1,−a,−a⟩.
            let nrd: Vec<i128> = vec![1, 1, -a, -a];
            // finite places: split (inv = 0) ⇔ Nrd isotropic over ℚ_p.
            for p in crate::forms::relevant_primes(&nrd) {
                let iso = try_is_isotropic_at_p(&nrd, p).unwrap();
                let splits = class.local_invariant(Place::Prime(p)).is_zero();
                assert_eq!(iso, splits, "norm-form oracle at p={p} for a={a}");
            }
            // real place: ⟨1,1,−a,−a⟩ is isotropic over ℝ iff indefinite iff a > 0.
            let real_iso = a > 0;
            let real_splits = class.local_invariant(Place::Real).is_zero();
            assert_eq!(real_iso, real_splits, "norm-form oracle at ℝ for a={a}");
        }
    }
}
