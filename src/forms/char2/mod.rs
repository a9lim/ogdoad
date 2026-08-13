//! Characteristic-2 quadratic-form invariants.
//!
//! Characteristic 2 has two different but adjacent invariants:
//!
//! * `arf` classifies the quadratic form / Clifford algebra through the Arf
//!   invariant.
//! * `dickson` classifies orthogonal transformations by the Dickson invariant,
//!   the determinant replacement in characteristic 2.
//! * `brown` lifts the `ℤ/2` Arf bit to the `ℤ/8` Brown invariant of a
//!   `ℤ/4`-valued quadratic refinement — the char-2 cell of the mod-8 spine
//!   (Bridge M), with `β(2q′) = 4·Arf(q′)`.
//! * `extraspecial` turns a nonsingular `F_2` quadratic form into the
//!   extraspecial 2-group whose commutator is the polar form and whose squaring
//!   map is the quadratic form.
//!
//! plus `field`, the [`FiniteChar2Field`] capability trait — the additive
//! (Artin–Schreier) mirror of [`FiniteOddField`](crate::forms::FiniteOddField)
//! that the char-2 local–global layer is generic over.
//!
//! The public exports stay flat (`forms::arf_invariant`,
//! `forms::dickson_matrix`, `forms::FiniteChar2Field`, …), matching the rest of the
//! forms pillar.

mod arf;
mod brown;
mod dickson;
mod extraspecial;
mod field;

pub use arf::*;
pub(crate) use arf::{
    arf_nimber_at_degree, arf_ordinal_at_degree, min_field_degree, nimber_metric_max_val,
};
pub(crate) use brown::beta_from_gauss;
pub use brown::*;
pub use dickson::*;
pub use extraspecial::*;
pub use field::*;

#[cfg(test)]
mod coverage_gap_tests {
    // These coverage tests live here rather than at their home files:
    // `isometric_finite_char2` lives in
    // `equivalence.rs`, and the equal-degree splitter lives in scalar's
    // crate-private `poly_factor.rs`
    // (`pub(crate)`, so it's reachable crate-wide without editing that file).

    use crate::clifford::Metric;
    use crate::forms::isometric_finite_char2;
    use crate::forms::FiniteChar2Field;
    use crate::scalar::{Fpn, Poly, Scalar};
    use std::collections::BTreeMap;

    type F8 = Fpn<2, 3>;

    fn plane(q0: F8, q1: F8, b01: F8) -> Metric<F8> {
        let mut b = BTreeMap::new();
        b.insert((0usize, 1usize), b01);
        Metric::new(vec![q0, q1], b)
    }

    /// `isometric_finite_char2` had no in-tree caller outside the Python
    /// binding. Exercise it with a genuinely isometric pair — two hyperbolic
    /// planes (`Q=0` on both generators) written with different nonzero polar
    /// scalars, since with `q=0` the Arf contribution doesn't depend on which
    /// nonzero `b01` splits the pair — and a genuinely non-isometric pair
    /// (hyperbolic vs. the anisotropic plane `q=[1,1]`, whose Arf is
    /// `Tr_{F8/F2}(1*1) = 1` because `[F8:F2] = 3` is odd, so the trace of the
    /// fixed field element `1` is `1+1+1 = 1`).
    #[test]
    fn isometric_finite_char2_distinguishes_hyperbolic_from_anisotropic() {
        let zero = F8::zero();
        let one = F8::one();
        let gen = F8::generator();

        let hyp_a = plane(zero, zero, one);
        let hyp_b = plane(zero, zero, gen);
        assert_eq!(isometric_finite_char2(&hyp_a, &hyp_b), Some(true));

        let aniso = plane(one, one, one);
        assert_eq!(isometric_finite_char2(&hyp_a, &aniso), Some(false));
        assert_eq!(isometric_finite_char2(&aniso, &aniso), Some(true));
    }

    /// The old char-2 `poly_factor` regression test — `(t+1)^4` over `F_2` —
    /// reduces to a single repeated factor inside `squarefree_parts` and never
    /// reaches `split_equal_degree` with `n != d`, so the equal-degree splitter
    /// itself was never forced to actually split anything.
    ///
    /// `g1`, `g2` are the distinct monic irreducible quadratics `1 + a*t + t^2`
    /// and `1 + (a+1)*t + t^2` over `F4 = Fpn<2,2>` (`a^2 = a+1`; verified by
    /// direct evaluation that neither has a root among `F4`'s four elements, so
    /// each is irreducible). `f = g1*g2` is squarefree of degree 4 with no
    /// factor of degree < 2, so `distinct_degree_factors` hands the *whole*
    /// degree-4 block to `split_equal_degree(f, d=2, ...)`, which must search
    /// for and apply a genuine splitter rather than hitting the trivial
    /// `n == d` early return.
    ///
    /// (Independently traced against a from-scratch port of the exact
    /// algorithm: the split is found by the `p == 2` trace-based
    /// Cantor-Zassenhaus branch, not the early-exit gcd shortcut — the
    /// deterministic seed enumeration hits a genuine split before it would ever
    /// reach the seed at which `h` happens to equal a scalar multiple of `g1`
    /// or `g2`, which is the only way the early-exit path could fire here.)
    #[test]
    fn f4_product_of_two_irreducible_quadratics_forces_the_equal_degree_splitter() {
        type F4 = Fpn<2, 2>;
        let one = F4::one();
        let a = F4::generator();
        let a1 = a.add(&one);

        let g1 = Poly::new(vec![one, a, one]); // 1 + a*t + t^2
        let g2 = Poly::new(vec![one, a1, one]); // 1 + (a+1)*t + t^2
        assert_ne!(g1, g2);

        let f = g1.mul(&g2);
        let factors = crate::scalar::poly_factor::monic_irreducible_factor_support(
            &f,
            2,
            F4::field_order(),
            F4::from_index,
        );
        assert_eq!(
            factors.len(),
            2,
            "must split into two irreducible quadratics, not stay merged"
        );
        assert!(factors.contains(&g1));
        assert!(factors.contains(&g2));
    }
}
