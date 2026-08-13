//! Algebra-context operations for constructing and combining multivectors.
//! The context owns the metric; its dimension is always derived from that
//! metric.

use super::basis::{bits, grade, MAX_BASIS_DIM};
use super::metric::Metric;
use super::multivector::Multivector;
use super::terms::{merge, scale, wedge_terms};
use crate::scalar::Scalar;
use std::collections::BTreeMap;

/// A Clifford algebra: metric + derived dimension. Produces and combines multivectors.
///
/// ## Operator vs context-method policy
///
/// Metric-free additive operations (`+`, `-`, unary `-`, `&` for wedge) are
/// implemented directly on [`Multivector`] as operators. The geometric product
/// and all metric-dependent operations are methods on this type, which provides
/// the metric as context. Use `a + b` / `a & b` for the metric-free ops;
/// `alg.mul(&a, &b)` / `alg.wedge(&a, &b)` for the metric-dependent ones.
/// This mirrors the scalar policy: operators on the concrete type require no
/// extra context; everything that needs context goes through the algebra.
///
/// **Note:** `^` is reserved for scalar power (`x ^ k: u128`); `&` is wedge
/// (`∧` in grundy). See [`Multivector`]'s `BitAnd` impl for the precedence
/// caveat (Rust `&` binds looser than `+` and `*`).
#[derive(Clone, Debug, PartialEq)]
pub struct CliffordAlgebra<S: Scalar> {
    pub(crate) metric: Metric<S>,
}

impl<S: Scalar> CliffordAlgebra<S> {
    /// Constructs an algebra after validating that `metric` has dimension `dim`.
    pub fn new(dim: usize, metric: Metric<S>) -> Self {
        metric.validate_for_dim(dim);
        CliffordAlgebra { metric }
    }

    /// The number of generators, i.e. the dimension of the underlying vector space.
    /// Derived from the metric (not stored separately); always equal to `metric.dim()`.
    pub fn dim(&self) -> usize {
        self.metric.dim()
    }

    /// Read-only access to the metric of this algebra.
    pub fn metric(&self) -> &Metric<S> {
        &self.metric
    }

    /// The graded (super) tensor product Cl(self) ⊗̂ Cl(other) ≅ Cl(self ⟂ other).
    pub fn graded_tensor(&self, other: &CliffordAlgebra<S>) -> CliffordAlgebra<S> {
        CliffordAlgebra::new(
            self.dim() + other.dim(),
            self.metric.direct_sum(&other.metric),
        )
    }

    /// Embed a multivector of the first factor into `self ⊗̂ other`.
    ///
    /// `self` is ignored — this is a clone of the term map since first-factor
    /// blade masks need no shift. It exists as a method on the algebra for API
    /// symmetry with [`embed_second`](Self::embed_second).
    pub fn embed_first(&self, v: &Multivector<S>) -> Multivector<S> {
        Multivector {
            terms: v.terms.clone(),
        }
    }

    /// Embed a multivector of the second (right) graded-tensor factor into
    /// `left ⊗̂ self` by shifting blade masks left by `left.dim()`.
    ///
    /// The caller passes the left algebra so the shift is read from it directly:
    /// `product_alg.embed_second(&right_mv, &left_alg)`.
    pub fn embed_second(&self, v: &Multivector<S>, left: &CliffordAlgebra<S>) -> Multivector<S> {
        let shift = left.dim();
        assert!(shift <= MAX_BASIS_DIM, "basis shift out of range");
        let terms = v
            .terms
            .iter()
            .map(|(&blade, c)| {
                if blade != 0 {
                    let highest = (u128::BITS - 1 - blade.leading_zeros()) as usize;
                    assert!(
                        highest + shift < MAX_BASIS_DIM,
                        "embedded blade exceeds {MAX_BASIS_DIM} generators"
                    );
                }
                let shifted = if blade == 0 { 0 } else { blade << shift };
                (shifted, c.clone())
            })
            .collect();
        Multivector { terms }
    }

    /// The additive identity.
    pub fn zero(&self) -> Multivector<S> {
        Multivector {
            terms: BTreeMap::new(),
        }
    }

    /// Embeds a scalar as a grade-zero multivector.
    pub fn scalar(&self, s: S) -> Multivector<S> {
        let mut terms = BTreeMap::new();
        if !s.is_zero() {
            terms.insert(0u128, s);
        }
        Multivector { terms }
    }

    /// The basis vector `e_i`.
    pub fn e(&self, i: usize) -> Multivector<S> {
        assert!(i < self.dim(), "generator index {i} out of range");
        assert!(i < MAX_BASIS_DIM, "generator index {i} exceeds blade mask");
        let mut terms = BTreeMap::new();
        terms.insert(1u128 << i, S::one());
        Multivector { terms }
    }

    /// A single basis blade from a set of generators, coefficient 1.
    pub fn blade(&self, gens: &[usize]) -> Multivector<S> {
        let mut mask = 0u128;
        for &g in gens {
            assert!(g < self.dim(), "blade generator index {g} out of range");
            assert!(g < MAX_BASIS_DIM, "blade generator index {g} exceeds mask");
            assert!(
                mask & (1u128 << g) == 0,
                "blade expects a set of distinct generators"
            );
            mask |= 1 << g;
        }
        let mut terms = BTreeMap::new();
        terms.insert(mask, S::one());
        Multivector { terms }
    }

    /// Adds two multivectors.
    pub fn add(&self, a: &Multivector<S>, b: &Multivector<S>) -> Multivector<S> {
        let mut terms = a.terms.clone();
        merge(&mut terms, b.terms.clone());
        Multivector { terms }
    }

    /// Multiplies a multivector by a scalar.
    pub fn scalar_mul(&self, s: &S, a: &Multivector<S>) -> Multivector<S> {
        Multivector {
            terms: scale(a.terms.clone(), s),
        }
    }

    /// Geometric (Clifford) product.
    pub fn mul(&self, a: &Multivector<S>, b: &Multivector<S>) -> Multivector<S> {
        let mut out: BTreeMap<u128, S> = BTreeMap::new();
        for (&ba, ca) in &a.terms {
            for (&bb, cb) in &b.terms {
                let reduced = self.metric.geom_product_blades(ba, bb);
                let coeff = ca.mul(cb);
                merge(&mut out, scale(reduced, &coeff));
            }
        }
        Multivector { terms: out }
    }

    /// Exterior (wedge) product — metric-independent.
    pub fn wedge(&self, a: &Multivector<S>, b: &Multivector<S>) -> Multivector<S> {
        Multivector {
            terms: wedge_terms(&a.terms, &b.terms),
        }
    }

    pub(crate) fn ordinary_gauge_algebra(&self) -> CliffordAlgebra<S> {
        CliffordAlgebra::new(
            self.dim(),
            Metric::new(self.metric.q.clone(), self.metric.b.clone()),
        )
    }

    fn sorted_generator_product(&self, blade: u128) -> Multivector<S> {
        let mut out = self.scalar(S::one());
        for g in bits(blade) {
            out = self.mul(&out, &self.e(g));
        }
        out
    }

    fn assert_same_gauge_class(&self, target: &CliffordAlgebra<S>) {
        assert_eq!(
            self.dim(),
            target.dim(),
            "gauge transport requires equal dimensions"
        );
        assert!(
            self.metric.q == target.metric.q && self.metric.b == target.metric.b,
            "gauge transport requires matching q and b"
        );
    }

    fn gauge_basis_image_to(
        &self,
        target: &CliffordAlgebra<S>,
        blade: u128,
        memo: &mut BTreeMap<u128, Multivector<S>>,
    ) -> Option<Multivector<S>> {
        if let Some(image) = memo.get(&blade) {
            return Some(image.clone());
        }

        let source_word = self.sorted_generator_product(blade);
        let target_word = target.sorted_generator_product(blade);
        let lead = source_word
            .terms
            .get(&blade)
            .cloned()
            .unwrap_or_else(S::zero);
        let lead_inv = lead.inv()?;

        let mut image = target_word;
        for (&lower_blade, coeff) in &source_word.terms {
            if lower_blade == blade {
                continue;
            }
            let lower_image = self.gauge_basis_image_to(target, lower_blade, memo)?;
            image = target.add(&image, &target.scalar_mul(&coeff.neg(), &lower_image));
        }
        image = target.scalar_mul(&lead_inv, &image);
        memo.insert(blade, image.clone());
        Some(image)
    }

    pub(crate) fn transport_gauge_to(
        &self,
        target: &CliffordAlgebra<S>,
        v: &Multivector<S>,
    ) -> Option<Multivector<S>> {
        self.assert_same_gauge_class(target);
        let mut memo = BTreeMap::new();
        let mut out = target.zero();
        for (&blade, coeff) in &v.terms {
            let image = self.gauge_basis_image_to(target, blade, &mut memo)?;
            out = target.add(&out, &target.scalar_mul(coeff, &image));
        }
        Some(out)
    }

    /// Reversion: the anti-automorphism `ẽᵢ₁⋯ẽᵢₖ = eᵢₖ⋯eᵢ₁`. For ordinary
    /// `(q, b)` metrics this is implemented by reversing each wedge-basis blade
    /// and reducing through the Clifford product. In characteristic not equal to
    /// 2, a non-zero `a` is only an antisymmetric gauge; reversion is transported
    /// through the matching ordinary `(q, b, a=0)` algebra and then pulled back.
    ///
    /// # Panics
    ///
    /// Panics in characteristic 2 when the metric has a non-zero `a`
    /// (in-order / general-bilinear) component. There the antisymmetric-gauge
    /// argument is not available, so the explicit boundary remains.
    pub fn reverse(&self, a: &Multivector<S>) -> Multivector<S> {
        if self.metric.has_upper() {
            assert!(
                S::characteristic() != 2,
                "reverse() on general-bilinear (a != 0) metrics is transported through \
                 the antisymmetric gauge only in characteristic != 2"
            );
            let ordinary = self.ordinary_gauge_algebra();
            let in_ordinary = self
                .transport_gauge_to(&ordinary, a)
                .expect("gauge transport has unit leading terms");
            let reversed = ordinary.reverse(&in_ordinary);
            return ordinary
                .transport_gauge_to(self, &reversed)
                .expect("gauge transport has unit leading terms");
        }
        let mut out = self.zero();
        for (&blade, coeff) in &a.terms {
            let mut rev_blade = self.scalar(S::one());
            let mut gens = bits(blade);
            gens.reverse();
            for g in gens {
                rev_blade = self.mul(&rev_blade, &self.e(g));
            }
            out = self.add(&out, &self.scalar_mul(coeff, &rev_blade));
        }
        out
    }

    /// Grade-k projection.
    pub fn grade_part(&self, a: &Multivector<S>, k: usize) -> Multivector<S> {
        let terms = a
            .terms
            .iter()
            .filter(|&(&blade, _)| grade(blade) == k)
            .map(|(&blade, c)| (blade, c.clone()))
            .collect();
        Multivector { terms }
    }

    /// The grade-0 (scalar) coefficient.
    pub fn scalar_part(&self, v: &Multivector<S>) -> S {
        v.terms.get(&0).cloned().unwrap_or_else(S::zero)
    }

    /// Raises `v` to a nonnegative integer power under the geometric product.
    /// `pow(v, 0)` is the scalar identity. The implementation uses binary
    /// exponentiation.
    pub fn pow(&self, v: &Multivector<S>, k: u128) -> Multivector<S> {
        if k == 0 {
            return self.scalar(S::one());
        }
        let mut acc = self.scalar(S::one());
        let mut base = v.clone();
        let mut exp = k;
        // square-and-multiply (binary exponentiation)
        loop {
            if exp & 1 == 1 {
                acc = self.mul(&acc, &base);
            }
            exp >>= 1;
            if exp == 0 {
                break;
            }
            base = self.mul(&base, &base);
        }
        acc
    }
}
