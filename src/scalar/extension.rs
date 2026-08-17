//! Finite field extensions with relative trace and norm.
//!
//! The [`FiniteField`](crate::scalar::FiniteField) trait already carries relative
//! trace/norm — but only *within* the finite-field tower, and to any intermediate
//! subfield. [`FieldExtension`] instead fixes **one** distinguished base
//! `F` and gives the same `(degree, embed, trace, norm)` interface across the three
//! kinds of finite separable extension the project builds, so the norm map that
//! feeds Hilbert symbols, the Brauer/Brauer–Wall group, and Hermitian forms has a
//! single name everywhere:
//!
//! | extension `E/F` | degree | flavour | trace / norm |
//! |---|---|---|---|
//! | [`Surcomplex`]`<S>` over `S` | 2 | algebraic, residue-extending (`i`) | `z+z̄`, `z·z̄ = a²+b²` |
//! | [`Fpn`]`<P,N>` over [`Fp`]`<P>` | `N` | the finite-field tower | the Galois `Σσⁱ`, `Πσⁱ` |
//! | [`Qq`]`<P,N,F>` over `Qq<P,N,1>` (= `Q_p`) | `F` | unramified local (char-0) | the Witt-Frobenius `Σσⁱ`, `Πσⁱ` |
//!
//! The `Fpn` implementation delegates to the shared
//! [`FiniteField`](crate::scalar::FiniteField) relative trace and norm.
//!
//! [`QuadraticInvolution`] is the companion capability for restriction of
//! Hermitian forms.  It names the involution-fixed world rather than the one
//! distinguished `FieldExtension::Base`, so it also covers the current
//! `F_16/F_4` intermediate-field cell exactly.
//!
//! # Exclusions
//!
//! Two functors are outside the implemented interface:
//!
//!   * [`Ramified`](crate::scalar::Ramified) — it is not generally Galois. Its
//!     trace and norm require trace and determinant of multiplication, which are
//!     not implemented over the capped-relative base models. Inseparable cases
//!     (`p | E` in equal characteristic) also have degenerate trace.
//!   * [`Gauss`](crate::scalar::Gauss) — a *transcendental* extension `S(t)` has
//!     **infinite degree**; there is no finite trace/norm at all.
//!
//! This is not a [`Scalar`] supertrait because most scalar worlds are not
//! extensions of a distinguished base.

use crate::scalar::{
    nim_square, nim_trace, Fp, Fpn, Nimber, Ordered, Qq, Scalar, Surcomplex, WittVec,
};

/// A scalar algebra with a distinguished order-two involution and an explicitly
/// represented fixed scalar world.
///
/// This is the structure needed to restrict a Hermitian form from `E` to the
/// ordinary quadratic form `q(v) = h(v,v)` over the fixed world `F`.  It is
/// deliberately separate from [`FieldExtension`]: `Fpn<P, 2k>` currently names
/// `Fp<P>` as its distinguished extension base, while its middle-Frobenius
/// involution fixes the intermediate field `Fpn<P, k>`.
///
/// The returned basis has exactly two elements because `E/F` is quadratic.
/// [`project_fixed`](Self::project_fixed) returns `None` when its argument is not
/// fixed by the involution or cannot be represented by the selected `Fixed`
/// backend.
pub trait QuadraticInvolution: Scalar {
    /// The scalar world fixed by the involution.
    type Fixed: Scalar;

    /// The nontrivial involution of `E/F`.
    fn involute(&self) -> Self;

    /// A distinguished `F`-basis of `E`.
    fn fixed_basis() -> [Self; 2];

    /// Embed an element of the fixed world into `E`.
    fn embed_fixed(value: &Self::Fixed) -> Self;

    /// Project an involution-fixed element of `E` into the represented fixed
    /// world.
    fn project_fixed(value: &Self) -> Option<Self::Fixed>;
}

/// A finite separable field extension `E/F` over a distinguished base `F`, with the
/// degree and the relative trace `Tr_{E/F}` and norm `N_{E/F}`.
pub trait FieldExtension: Scalar {
    /// The base field `F` (`Self = E`).
    type Base: Scalar;

    /// The **relative** degree `[E : F]` over the chosen `Base` field `F`.
    /// Distinct from [`FiniteField::ext_degree`](crate::scalar::FiniteField::ext_degree),
    /// which is the *absolute* degree over the prime field; the two coincide only when
    /// `Base` is the prime field.
    fn extension_degree() -> usize;

    /// The canonical embedding `F ↪ E`.
    fn embed(base: &Self::Base) -> Self;

    /// The relative trace `Tr_{E/F}(α) ∈ F`, equivalently the trace of
    /// multiplication by `α` (or the sum of conjugates in the separable case).
    fn trace(&self) -> Self::Base;

    /// The relative norm `N_{E/F}(α) ∈ F`, equivalently the determinant of
    /// multiplication by `α` (or the product of conjugates in the separable case).
    fn norm(&self) -> Self::Base;
}

// ───────────────────────── Surcomplex<S> / S  (degree 2) ─────────────────────────
//
// Adjoin `i`, a root of `x²+1`. The `Ordered` bound restricts this implementation
// to characteristic-zero ordered bases, where `x²+1` is irreducible.

impl<S: Ordered> QuadraticInvolution for Surcomplex<S> {
    type Fixed = S;

    fn involute(&self) -> Self {
        self.conj()
    }

    fn fixed_basis() -> [Self; 2] {
        [Self::one(), Self::i()]
    }

    fn embed_fixed(value: &S) -> Self {
        Surcomplex::new(value.clone(), S::zero())
    }

    fn project_fixed(value: &Self) -> Option<S> {
        value.im.is_zero().then(|| value.re.clone())
    }
}

impl<S: Ordered> FieldExtension for Surcomplex<S> {
    type Base = S;
    fn extension_degree() -> usize {
        2
    }
    fn embed(base: &S) -> Self {
        Surcomplex::new(base.clone(), S::zero())
    }
    fn trace(&self) -> S {
        // (a+bi) + (a−bi) = 2a
        self.re.add(&self.re)
    }
    fn norm(&self) -> S {
        // (a+bi)(a−bi) = a²+b² — exactly the |z|² Hermitian forms read.
        self.re.mul(&self.re).add(&self.im.mul(&self.im))
    }
}

// ───────────────────────── Fpn<P,N> / Fp<P>  (degree N) ─────────────────────────
//
// The finite-field tower over its prime field delegates to the shared
// `FiniteField::relative_trace` and `relative_norm` implementations.

impl<const P: u128, const N: usize> FieldExtension for Fpn<P, N> {
    type Base = Fp<P>;
    fn extension_degree() -> usize {
        N
    }
    fn embed(base: &Fp<P>) -> Self {
        Fpn::<P, N>::constant(base.value())
    }
    fn trace(&self) -> Fp<P> {
        use crate::scalar::FiniteField;
        // trace to the degree-1 (prime) subfield; the result is a constant element.
        Fp::<P>::from_u128(self.relative_trace(1).coeff(0))
    }
    fn norm(&self) -> Fp<P> {
        use crate::scalar::FiniteField;
        Fp::<P>::from_u128(self.relative_norm(1).coeff(0))
    }
}

impl<const P: u128> QuadraticInvolution for Fpn<P, 2> {
    type Fixed = Fp<P>;

    fn involute(&self) -> Self {
        use crate::scalar::FiniteField;
        self.frobenius()
    }

    fn fixed_basis() -> [Self; 2] {
        [Self::one(), Self::generator()]
    }

    fn embed_fixed(value: &Fp<P>) -> Self {
        Self::constant(value.value())
    }

    fn project_fixed(value: &Self) -> Option<Fp<P>> {
        use crate::scalar::FiniteField;
        if value.frobenius() != *value || value.coeffs()[1] != 0 {
            return None;
        }
        Some(Fp::<P>::from_u128(value.coeff(0)))
    }
}

// `F_16/F_4` is the one currently public Hermitian cell whose fixed field is
// not the prime field named by `FieldExtension::Base`.  The two `Fpn` backends
// use independently generated polynomial bases, so this implementation records
// an explicit isomorphism: a primitive generator of `F_4^*` maps to the unique
// order-three subgroup generator obtained from a primitive element of `F_16`.
impl QuadraticInvolution for Fpn<2, 4> {
    type Fixed = Fpn<2, 2>;

    fn involute(&self) -> Self {
        use crate::scalar::FiniteField;
        self.frobenius_iter(2)
    }

    fn fixed_basis() -> [Self; 2] {
        [Self::one(), Self::primitive_element()]
    }

    fn embed_fixed(value: &Self::Fixed) -> Self {
        use crate::scalar::FiniteField;
        if value.is_zero() {
            return Self::zero();
        }
        let fixed_generator = FiniteField::pow(&Self::primitive_element(), 5);
        let base_generator = Fpn::<2, 2>::primitive_element();
        let exponent = base_generator
            .discrete_log(*value)
            .expect("nonzero F_4 element has a discrete log to a primitive generator");
        FiniteField::pow(&fixed_generator, exponent)
    }

    fn project_fixed(value: &Self) -> Option<Self::Fixed> {
        if value.involute() != *value {
            return None;
        }
        (0..4).find_map(|code| {
            let base = Fpn::<2, 2>::from_coeffs(&[code & 1, (code >> 1) & 1]);
            (Self::embed_fixed(&base) == *value).then_some(base)
        })
    }
}

// ───────────────────────── Qq<P,N,F> / Qq<P,N,1> (= Q_p)  (degree F) ─────────────
//
// The unramified local extension Q_q = Frac(W_N(F_q)) over Q_p. It is Galois with
// cyclic group of order F generated by the (Witt) Frobenius σ, so trace and norm
// are the genuine `Σσⁱ` / `Πσⁱ`. The lift is built from the Teichmüller digits
// exposed by `witt_components` (`witt_components` ∘ Fpn-Frobenius ∘
// `from_witt_components`) — no precision loss, since Q_q multiplication is exact.
//
// The base is `Qq<P,N,1>`, which *is* `Q_p` (residue degree 1 — "Q_q for F = 1 is
// Q_p"). Staying inside the `Qq` family sidesteps the `Qp` const-kind mismatch
// (`Qp`'s precision is `u128`, `Qq`'s `N` is `usize`).

/// The Witt Frobenius `σ` on `W_N(F_q)`: raise every Teichmüller digit to the
/// `p`-th power. The lift of `x ↦ x^p` on `F_q`, a ring automorphism.
fn witt_frobenius<const P: u128, const N: usize, const F: usize>(
    w: WittVec<P, N, F>,
) -> WittVec<P, N, F> {
    use crate::scalar::FiniteField;
    let comps: Vec<Fpn<P, F>> = w.witt_components().iter().map(|c| c.frobenius()).collect();
    WittVec::<P, N, F>::from_witt_components(&comps)
}

/// `σ` lifted to `Q_q`: `σ(p^v·u) = p^v·σ(u)` (`p ∈ Q_p` is fixed).
fn qq_frobenius<const P: u128, const N: usize, const F: usize>(x: &Qq<P, N, F>) -> Qq<P, N, F> {
    match x.valuation() {
        None => Qq::zero(),
        Some(v) => Qq::<P, N, F>::from_p_power(v).mul(&Qq::from_witt(witt_frobenius(x.unit()))),
    }
}

/// Convert a `Q_q` element that lies in the `Q_p` subfield (residue in `F_p`, hence
/// Teichmüller digits in `F_p` ⇒ `.0[1..] = 0`) down to the base `Qq<P,N,1>` (= `Q_p`).
fn qq_to_base<const P: u128, const N: usize, const F: usize>(x: &Qq<P, N, F>) -> Qq<P, N, 1> {
    match x.valuation() {
        None => Qq::zero(),
        Some(v) => {
            let u = x.unit();
            debug_assert!(
                u.0[1..].iter().all(|&c| c == 0),
                "trace/norm of Q_q/Q_p must land in the Q_p subfield"
            );
            Qq::<P, N, 1>::from_p_power(v).mul(&Qq::from_witt(WittVec::<P, N, 1>([u.0[0]])))
        }
    }
}

impl<const P: u128, const N: usize, const F: usize> FieldExtension for Qq<P, N, F> {
    type Base = Qq<P, N, 1>;
    fn extension_degree() -> usize {
        F
    }
    fn embed(base: &Qq<P, N, 1>) -> Self {
        match base.valuation() {
            None => Qq::zero(),
            Some(v) => {
                let mut arr = [0u128; F];
                if F > 0 {
                    arr[0] = base.unit().0[0];
                }
                Qq::<P, N, F>::from_p_power(v).mul(&Qq::from_witt(WittVec::<P, N, F>(arr)))
            }
        }
    }
    fn trace(&self) -> Qq<P, N, 1> {
        let mut conj = *self;
        let mut tr = Qq::<P, N, F>::zero();
        for _ in 0..F {
            tr = tr.add(&conj);
            conj = qq_frobenius(&conj);
        }
        qq_to_base(&tr)
    }
    fn norm(&self) -> Qq<P, N, 1> {
        let mut conj = *self;
        let mut nm = Qq::<P, N, F>::one();
        for _ in 0..F {
            nm = nm.mul(&conj);
            conj = qq_frobenius(&conj);
        }
        qq_to_base(&nm)
    }
}

// ───────────────────────── Nimber / Fp<2>  (degree 128) ─────────────────────────
//
// The project's main char-2 field, F_{2^128}, as an extension of its prime field
// F_2. The Galois group is cyclic of order 128 generated by
// the nim-Frobenius `x ↦ x²` (`nim_square`); the absolute trace `nim_trace(·, 128)`
// is the relative trace to F_2, and the norm map onto F_2* = {1} sends every
// nonzero element to 1.

impl FieldExtension for Nimber {
    type Base = Fp<2>;
    fn extension_degree() -> usize {
        128
    }
    fn embed(base: &Fp<2>) -> Self {
        Nimber(base.value())
    }
    fn trace(&self) -> Fp<2> {
        Fp::<2>::from_u128(nim_trace(self.0, 128))
    }
    fn norm(&self) -> Fp<2> {
        // N_{F_{2^128}/F_2} maps onto F_2* = {1}, so every nonzero element norms to
        // 1 (and 0 to 0): N(x) = x^{(2^128−1)/(2−1)} = x^{2^128−1} = 1 for x ≠ 0.
        Fp::<2>::from_u128(u128::from(self.0 != 0))
    }
}

/// A finite **cyclic Galois** extension `E/F`: a [`FieldExtension`] whose Galois
/// group is cyclic, generated by a distinguished automorphism `σ` (Frobenius /
/// complex conjugation / the Witt–Frobenius), together with a distinguished
/// `F`-basis of `E`.
///
/// This is exactly the structure the **twisted trace form**
/// ([`trace_twisted_form`](crate::forms::trace_twisted_form)) needs: a basis to
/// index the form's generators, and `σ^k` to build the Frobenius-twisted product
/// `x · σ^k(x)`. The relative trace itself is already
/// [`FieldExtension::trace`] — `σ` and `basis` are the only new data, which is why
/// this is a thin subtrait rather than a reimplementation.
///
/// `Surcomplex` (`σ` is conjugation), the finite-field tower `Fpn` (`σ` is
/// Frobenius), `Qq` (`σ` is Witt--Frobenius), and `Nimber` (`σ` is nim
/// Frobenius) implement it. `Ramified` and
/// `Gauss` stay out: the former is not generally Galois, and the latter has
/// infinite degree.
pub trait CyclicGaloisExtension: FieldExtension {
    /// An `F`-basis of `E`; its length equals
    /// [`extension_degree`](FieldExtension::extension_degree).
    fn basis() -> Vec<Self>;

    /// The Galois generator `σ` (a field automorphism of `E` fixing `F`).
    fn sigma(&self) -> Self;

    /// `σ^k` — the `k`-fold composite of [`sigma`](CyclicGaloisExtension::sigma).
    fn sigma_power(&self, k: usize) -> Self {
        let mut x = self.clone();
        for _ in 0..k {
            x = x.sigma();
        }
        x
    }
}

impl<S: Ordered> CyclicGaloisExtension for Surcomplex<S> {
    fn basis() -> Vec<Self> {
        // {1, i}
        vec![
            Surcomplex::new(S::one(), S::zero()),
            Surcomplex::new(S::zero(), S::one()),
        ]
    }
    fn sigma(&self) -> Self {
        self.conj()
    }
}

impl<const P: u128, const N: usize> CyclicGaloisExtension for Fpn<P, N> {
    fn basis() -> Vec<Self> {
        // the standard coordinate basis e_j = (0,…,1,…,0)
        (0..N)
            .map(|j| {
                let mut a = [0u128; N];
                a[j] = 1;
                Fpn::<P, N>::from_coeffs(&a)
            })
            .collect()
    }
    fn sigma(&self) -> Self {
        use crate::scalar::FiniteField;
        self.frobenius()
    }
}

impl<const P: u128, const N: usize, const F: usize> CyclicGaloisExtension for Qq<P, N, F> {
    fn basis() -> Vec<Self> {
        // Teichmüller lifts of the standard F_p-basis of the residue field F_q.
        // Nakayama lifts this residue basis to a Q_p-basis of the unramified field.
        (0..F)
            .map(|j| {
                let mut a = [0u128; F];
                a[j] = 1;
                Qq::<P, N, F>::teichmuller(Fpn::<P, F>::from_coeffs(&a))
            })
            .collect()
    }

    fn sigma(&self) -> Self {
        qq_frobenius(self)
    }
}

impl CyclicGaloisExtension for Nimber {
    fn basis() -> Vec<Self> {
        // the bit basis {1, 2, 4, …, 2^127}: an F_2-basis under nim-addition (XOR).
        (0..128).map(|i| Nimber(1u128 << i)).collect()
    }
    fn sigma(&self) -> Self {
        Nimber(nim_square(self.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{FiniteField, Rational, Surreal};

    // ---------- Surcomplex (the algebraic-closure functor) ----------

    #[test]
    fn gaussian_trace_and_norm() {
        type G = Surcomplex<Rational>;
        let z = Surcomplex::new(Rational::from_int(2), Rational::from_int(1)); // 2+i
        assert_eq!(<G as FieldExtension>::extension_degree(), 2);
        assert_eq!(z.trace(), Rational::from_int(4)); // 2·2
        assert_eq!(z.norm(), Rational::from_int(5)); // 4+1
                                                     // norm = z·z̄ real part; trace = z+z̄ real part — agree with conj directly.
        assert_eq!(z.mul(&z.conj()).re, z.norm());
        assert_eq!(z.add(&z.conj()).re, z.trace());
        // embedding a base element: trace = 2·a, norm = a².
        let e = <G as FieldExtension>::embed(&Rational::from_int(3));
        assert_eq!(
            e,
            Surcomplex::new(Rational::from_int(3), Rational::from_int(0))
        );
        assert_eq!(e.norm(), Rational::from_int(9));
        // multiplicativity of the norm (it is a group hom on E*).
        let w = Surcomplex::new(Rational::from_int(1), Rational::from_int(-2));
        assert_eq!(z.mul(&w).norm(), z.norm().mul(&w.norm()));
    }

    #[test]
    fn surreal_complex_trace_and_norm() {
        // Over the surreal-complex field: ω + i has norm ω²+1, trace 2ω — exact.
        let z = Surcomplex::new(Surreal::omega(), Surreal::one());
        assert_eq!(
            z.norm(),
            Surreal::omega().mul(&Surreal::omega()).add(&Surreal::one())
        );
        assert_eq!(z.trace(), Surreal::omega().add(&Surreal::omega()));
    }

    // ---------- Fpn over Fp (delegating to the finite-field tower) ----------

    #[test]
    fn finite_field_trace_norm_match_the_galois_machinery() {
        type F9 = Fpn<3, 2>;
        assert_eq!(<F9 as FieldExtension>::extension_degree(), 2);
        for code in 0..9u128 {
            let x = Fpn::<3, 2>::from_coeffs(&[code % 3, code / 3]);
            // FieldExtension trace/norm = FiniteField relative trace/norm to F_3,
            // read as the prime-field element.
            assert_eq!(
                FieldExtension::trace(&x),
                Fp::<3>::from_u128(x.relative_trace(1).coeff(0))
            );
            assert_eq!(
                FieldExtension::norm(&x),
                Fp::<3>::from_u128(x.relative_norm(1).coeff(0))
            );
            // norm and trace land in the prime field; norm = x^{1+p} for F_{p²}.
            assert_eq!(
                FieldExtension::norm(&x),
                Fp::<3>::from_u128(x.mul(&x.frobenius()).coeff(0))
            );
        }
        // multiplicativity of the norm over F_9*.
        let a = Fpn::<3, 2>::from_coeffs(&[1, 1]);
        let b = Fpn::<3, 2>::from_coeffs(&[2, 1]);
        assert_eq!(
            FieldExtension::norm(&a.mul(&b)),
            FieldExtension::norm(&a).mul(&FieldExtension::norm(&b))
        );
        // embedding the prime field: norm = c^N = c² here.
        let c = <F9 as FieldExtension>::embed(&Fp::<3>::from_u128(2));
        assert_eq!(
            FieldExtension::norm(&c),
            Fp::<3>::from_u128(2).mul(&Fp::<3>::from_u128(2))
        );
    }

    #[test]
    fn f16_f4_quadratic_involution_has_an_exact_fixed_field_isomorphism() {
        type F4 = Fpn<2, 2>;
        type F16 = Fpn<2, 4>;

        let elements: Vec<F4> = (0..4)
            .map(|code| F4::from_coeffs(&[code & 1, (code >> 1) & 1]))
            .collect();
        for a in &elements {
            let embedded_a = <F16 as QuadraticInvolution>::embed_fixed(a);
            assert_eq!(embedded_a.involute(), embedded_a);
            assert_eq!(
                <F16 as QuadraticInvolution>::project_fixed(&embedded_a),
                Some(*a)
            );
            for b in &elements {
                assert_eq!(
                    <F16 as QuadraticInvolution>::embed_fixed(&a.add(b)),
                    embedded_a.add(&<F16 as QuadraticInvolution>::embed_fixed(b))
                );
                assert_eq!(
                    <F16 as QuadraticInvolution>::embed_fixed(&a.mul(b)),
                    embedded_a.mul(&<F16 as QuadraticInvolution>::embed_fixed(b))
                );
            }
        }

        let basis = <F16 as QuadraticInvolution>::fixed_basis();
        assert_ne!(basis[1].involute(), basis[1]);
    }

    // ---------- Qq over Qp (the unramified local extension, Witt Frobenius) ----------

    #[test]
    fn unramified_local_trace_and_norm() {
        type Q9 = Qq<3, 3, 2>; // residue F_9, degree 2 over Q_3
        assert_eq!(<Q9 as FieldExtension>::extension_degree(), 2);

        // a Witt unit with residue the F_9 generator g: its norm has residue
        // N_{F9/F3}(g) = g^{1+3} = g^4, its trace has residue g + g^3 (both ∈ F_3).
        let g = Fpn::<3, 2>::from_coeffs(&[0, 1]); // F_9 generator
        let x = Q9::from_witt(WittVec::<3, 3, 2>(g.into_coeffs()));
        let n = FieldExtension::norm(&x); // a Qq<3,3,1> = Q_3 element
                                          // its residue (∈ F_3) matches the finite-field norm of g.
        assert_eq!(
            n.unit().0[0] % 3,
            FieldExtension::norm(&g).value(),
            "norm residue = N_{{F9/F3}}(g)"
        );

        // F = 1 ⇒ Q_q is Q_p and trace = norm = identity.
        type Q3 = Qq<3, 3, 1>;
        let y = Q3::from_int(7);
        assert_eq!(FieldExtension::norm(&y), y);
        assert_eq!(FieldExtension::trace(&y), y);

        // multiplicativity of the norm and additivity of the trace.
        let a = Q9::from_witt(WittVec::<3, 3, 2>([1, 1]));
        let b = Q9::from_witt(WittVec::<3, 3, 2>([2, 1]));
        assert_eq!(
            FieldExtension::norm(&a.mul(&b)),
            FieldExtension::norm(&a).mul(&FieldExtension::norm(&b))
        );
        assert_eq!(
            FieldExtension::trace(&a.add(&b)),
            FieldExtension::trace(&a).add(&FieldExtension::trace(&b))
        );
        // the norm of p is p^F (= p² here): valuation 2.
        let p = Q9::from_int(3);
        assert_eq!(FieldExtension::norm(&p).valuation(), Some(2));
    }

    // ---------- generic use ----------

    #[test]
    fn field_extension_is_generic() {
        fn norm_is_multiplicative<E: FieldExtension>(a: &E, b: &E)
        where
            E::Base: PartialEq + std::fmt::Debug,
        {
            assert_eq!(a.mul(b).norm(), a.norm().mul(&b.norm()));
        }
        norm_is_multiplicative(
            &Surcomplex::new(Rational::from_int(2), Rational::from_int(1)),
            &Surcomplex::new(Rational::from_int(1), Rational::from_int(3)),
        );
        norm_is_multiplicative(
            &Fpn::<3, 2>::from_coeffs(&[1, 2]),
            &Fpn::<3, 2>::from_coeffs(&[2, 2]),
        );
    }

    // ---------- Nimber as a FieldExtension of F_2 ----------

    #[test]
    fn nimber_is_a_field_extension_of_f2() {
        assert_eq!(<Nimber as FieldExtension>::extension_degree(), 128);
        assert_eq!(
            <Nimber as FieldExtension>::embed(&Fp::<2>::from_u128(1)),
            Nimber(1)
        );
        assert_eq!(
            <Nimber as FieldExtension>::embed(&Fp::<2>::from_u128(0)),
            Nimber(0)
        );

        // the relative trace IS the absolute nim-trace to F_2, and it is additive.
        let a = Nimber(0b1011);
        let b = Nimber(0b0110);
        assert_eq!(
            FieldExtension::trace(&a),
            Fp::<2>::from_u128(nim_trace(a.0, 128))
        );
        assert_eq!(
            FieldExtension::trace(&a.add(&b)),
            FieldExtension::trace(&a).add(&FieldExtension::trace(&b))
        );

        // norm onto F_2* = {1}: every nonzero element has norm 1, zero has norm 0.
        assert_eq!(FieldExtension::norm(&Nimber(0)), Fp::<2>::from_u128(0));
        for x in [Nimber(1), Nimber(2), Nimber(0xabc), Nimber(u128::MAX)] {
            assert_eq!(
                FieldExtension::norm(&x),
                Fp::<2>::from_u128(1),
                "norm of {x:?}"
            );
        }
    }

    // ---------- CyclicGaloisExtension: basis + σ over the three legs ----------

    #[test]
    fn cyclic_galois_surcomplex() {
        type G = Surcomplex<Rational>;
        let basis = <G as CyclicGaloisExtension>::basis();
        assert_eq!(
            basis,
            vec![
                Surcomplex::new(Rational::from_int(1), Rational::from_int(0)),
                Surcomplex::new(Rational::from_int(0), Rational::from_int(1)),
            ]
        );
        let z = Surcomplex::new(Rational::from_int(2), Rational::from_int(3));
        assert_eq!(z.sigma(), z.conj()); // σ = conjugation
        assert_eq!(z.sigma_power(2), z); // order 2
    }

    #[test]
    fn cyclic_galois_fpn() {
        type F9 = Fpn<3, 2>;
        let basis = <F9 as CyclicGaloisExtension>::basis();
        assert_eq!(
            basis,
            vec![
                Fpn::<3, 2>::from_coeffs(&[1, 0]),
                Fpn::<3, 2>::from_coeffs(&[0, 1])
            ]
        );
        let x = Fpn::<3, 2>::from_coeffs(&[1, 2]);
        assert_eq!(x.sigma(), x.frobenius()); // σ = Frobenius
        assert_eq!(x.sigma_power(2), x); // Frobenius has order N = 2 on F_{3²}
    }

    #[test]
    fn cyclic_galois_qq() {
        type Q9 = Qq<3, 3, 2>;
        let basis = <Q9 as CyclicGaloisExtension>::basis();
        assert_eq!(basis.len(), 2);
        assert_eq!(basis[0], Q9::one());
        assert_eq!(
            basis[1].unit_residue(),
            Some(Fpn::<3, 2>::from_coeffs(&[0, 1]))
        );

        let x = Q9::teichmuller(Fpn::<3, 2>::from_coeffs(&[1, 1]));
        assert_eq!(x.sigma(), qq_frobenius(&x)); // σ = Witt-Frobenius
        assert_eq!(x.sigma_power(2), x); // unramified degree 2

        let over_base = <Q9 as FieldExtension>::embed(&Qq::<3, 3, 1>::from_int(5));
        assert_eq!(over_base.sigma(), over_base); // the base Q_p is fixed
    }

    #[test]
    fn cyclic_galois_nimber() {
        let basis = <Nimber as CyclicGaloisExtension>::basis();
        assert_eq!(basis.len(), 128);
        assert_eq!(basis[0], Nimber(1));
        assert_eq!(basis[7], Nimber(128)); // 2^7
        let x = Nimber(0b1101);
        assert_eq!(x.sigma(), Nimber(nim_square(x.0))); // σ = nim-Frobenius
        assert_eq!(x.sigma_power(128), x); // Frobenius has order 128 on F_{2^128}
    }
}
