//! Metric data for the Clifford engine. [`Metric`] keeps the quadratic
//! diagonal `q`, polar form `b`, and strictly upper contraction `a` distinct.
//! This is essential in characteristic two, where `q` is not determined by
//! the alternating polar form.

use super::basis::MAX_BASIS_DIM;
use crate::scalar::Scalar;
use std::collections::BTreeMap;

/// Owned metric storage: `(q, b, a)`.
pub type MetricParts<S> = (
    Vec<S>,
    BTreeMap<(usize, usize), S>,
    BTreeMap<(usize, usize), S>,
);

/// The metric of a possibly degenerate Clifford algebra.
///
/// For `i < j`, the stored data means
/// `B(e_i,e_i) = q[i]`, `B(e_i,e_j) = a[(i,j)]`, and
/// `B(e_j,e_i) = b[(i,j)] - a[(i,j)]`. Thus `b` is the polar or
/// anticommutator form and `a` selects a general bilinear representative.
#[derive(Clone, Debug, PartialEq)]
pub struct Metric<S: Scalar> {
    pub(crate) q: Vec<S>,
    pub(crate) b: BTreeMap<(usize, usize), S>,
    pub(crate) a: BTreeMap<(usize, usize), S>,
}

impl<S: Scalar> Metric<S> {
    /// Orthogonal metric from a list of squares (b = 0). `Cl(p,q,r)` style.
    pub fn diagonal(q: Vec<S>) -> Self {
        Metric {
            q,
            b: BTreeMap::new(),
            a: BTreeMap::new(),
        }
    }

    /// The fully-null metric: exterior/Grassmann algebra on `n` generators.
    pub fn grassmann(n: usize) -> Self {
        Metric {
            q: vec![S::zero(); n],
            b: BTreeMap::new(),
            a: BTreeMap::new(),
        }
    }

    /// An ordinary Clifford metric with squares `q`, anticommutators `b`, and
    /// no in-order contraction (`a` empty).
    ///
    /// `b` may be any `IntoIterator` of `((i, j), value)` pairs (a `BTreeMap`,
    /// a `Vec`, a slice, …) so call sites need not build the map explicitly.
    pub fn new(q: Vec<S>, b: impl IntoIterator<Item = ((usize, usize), S)>) -> Self {
        let metric = Metric {
            q,
            b: b.into_iter().collect(),
            a: BTreeMap::new(),
        };
        metric.validate_for_dim(metric.q.len());
        metric
    }

    /// A general-bilinear-form metric: squares `q`, polar form `b` (i<j), and the
    /// in-order contraction `a` (i<j). See the struct docs.
    ///
    /// Both `b` and `a` may be any `IntoIterator` of `((i, j), value)` pairs.
    pub fn general(
        q: Vec<S>,
        b: impl IntoIterator<Item = ((usize, usize), S)>,
        a: impl IntoIterator<Item = ((usize, usize), S)>,
    ) -> Self {
        let metric = Metric {
            q,
            b: b.into_iter().collect(),
            a: a.into_iter().collect(),
        };
        metric.validate_for_dim(metric.q.len());
        metric
    }

    /// The represented dimension, i.e. the length of the quadratic diagonal.
    pub fn dim(&self) -> usize {
        self.q.len()
    }

    /// Diagonal quadratic entries `q[i] = e_i^2`.
    pub fn q(&self) -> &[S] {
        &self.q
    }

    /// Polar/anticommutator entries `b[(i,j)] = {e_i,e_j}` with `i < j`.
    pub fn b(&self) -> &BTreeMap<(usize, usize), S> {
        &self.b
    }

    /// Strictly-upper/in-order contraction entries with `i < j`.
    pub fn a(&self) -> &BTreeMap<(usize, usize), S> {
        &self.a
    }

    /// Consume the metric into its invariant-carrying parts.
    pub fn into_parts(self) -> MetricParts<S> {
        (self.q, self.b, self.a)
    }

    pub(crate) fn validate_for_dim(&self, dim: usize) {
        assert!(
            dim <= MAX_BASIS_DIM,
            "CliffordAlgebra supports at most {MAX_BASIS_DIM} generators"
        );
        assert_eq!(
            self.q.len(),
            dim,
            "metric q length must equal algebra dimension"
        );
        Self::validate_keys("b", &self.b, dim);
        Self::validate_keys("a", &self.a, dim);
    }

    fn validate_keys(name: &str, map: &BTreeMap<(usize, usize), S>, dim: usize) {
        for &(i, j) in map.keys() {
            assert!(i < j, "{name}-keys must satisfy i < j");
            assert!(
                j < dim,
                "{name}-key ({i},{j}) is out of range for dimension {dim}"
            );
        }
    }

    /// Whether any in-order contraction entry is nonzero.
    pub fn has_upper(&self) -> bool {
        self.a.values().any(|v| !v.is_zero())
    }

    /// True iff the basis is orthogonal: no off-diagonal polar or upper
    /// contraction terms are present. Then a blade product reduces to one blade.
    pub(crate) fn is_orthogonal(&self) -> bool {
        self.b.values().all(|v| v.is_zero()) && self.a.values().all(|v| v.is_zero())
    }

    /// Orthogonal direct sum `M ⟂ M'`: a block-diagonal metric on the disjoint
    /// union of the two generator sets.
    pub fn direct_sum(&self, other: &Metric<S>) -> Metric<S> {
        let n = self.q.len();
        let mut q = self.q.clone();
        q.extend(other.q.iter().cloned());
        let mut b = self.b.clone();
        for (&(i, j), v) in &other.b {
            b.insert((i + n, j + n), v.clone());
        }
        let mut a = self.a.clone();
        for (&(i, j), v) in &other.a {
            a.insert((i + n, j + n), v.clone());
        }
        Metric::general(q, b, a)
    }

    pub(crate) fn q_val(&self, i: usize) -> S {
        self.q.get(i).cloned().unwrap_or_else(S::zero)
    }

    pub(crate) fn q_ref(&self, i: usize) -> &S {
        &self.q[i]
    }

    /// Applies `f` to every coefficient while preserving all `q`, `b`, and `a`
    /// indices. The caller is responsible for using a map compatible with the
    /// intended algebraic structure.
    pub fn map<T: Scalar>(&self, f: impl Fn(&S) -> T) -> Metric<T> {
        Metric {
            q: self.q.iter().map(&f).collect(),
            b: self.b.iter().map(|(&k, v)| (k, f(v))).collect(),
            a: self.a.iter().map(|(&k, v)| (k, f(v))).collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clifford::CliffordAlgebra;
    use crate::scalar::Rational;

    fn r(n: i128) -> Rational {
        Rational::from_int(n)
    }

    #[test]
    fn direct_sum_shifts_right_bs_and_as_by_left_dim() {
        let mut bl = BTreeMap::new();
        bl.insert((0usize, 1usize), r(5));
        let mut al = BTreeMap::new();
        al.insert((0usize, 1usize), r(7));
        let left = Metric::general(vec![r(1), r(2)], bl, al);

        let mut br = BTreeMap::new();
        br.insert((0usize, 2usize), r(11));
        let mut ar = BTreeMap::new();
        ar.insert((1usize, 2usize), r(13));
        let right = Metric::general(vec![r(3), r(4), r(5)], br, ar);

        let sum = left.direct_sum(&right);

        assert_eq!(sum.dim(), 5);
        assert_eq!(sum.q(), &[r(1), r(2), r(3), r(4), r(5)]);
        // Left's entries land unshifted.
        assert_eq!(sum.b().get(&(0, 1)), Some(&r(5)));
        assert_eq!(sum.a().get(&(0, 1)), Some(&r(7)));
        // Right's entries shift by left.dim() = 2: (0,2)->(2,4), (1,2)->(3,4).
        assert_eq!(sum.b().get(&(2, 4)), Some(&r(11)));
        assert_eq!(sum.a().get(&(3, 4)), Some(&r(13)));
        // No accidental cross-block entries and nothing extra was inserted.
        assert_eq!(sum.b().len(), 2);
        assert_eq!(sum.a().len(), 2);
    }

    /// Same shift, probed through the algebra's actual products rather than
    /// the metric accessors: within-block generators keep their documented
    /// `b`, while cross-block generators (no `b`/`a` between blocks by
    /// construction) purely anticommute — this is what makes `direct_sum` the
    /// graded tensor product, not just a naive concatenation.
    #[test]
    fn direct_sum_shift_takes_effect_in_the_joined_algebras_products() {
        let mut bl = BTreeMap::new();
        bl.insert((0usize, 1usize), r(1));
        let left = Metric::new(vec![r(2), r(3)], bl);

        let mut br = BTreeMap::new();
        br.insert((0usize, 1usize), r(1));
        let right = Metric::new(vec![r(5), r(7)], br);

        let left_alg = CliffordAlgebra::new(2, left);
        let right_alg = CliffordAlgebra::new(2, right);
        let joined = left_alg.graded_tensor(&right_alg);

        // e2,e3 are the shifted right block: {e2,e3} = 1, per right's b(0,1)=1.
        let e2 = joined.e(2);
        let e3 = joined.e(3);
        let anti23 = joined.add(&joined.mul(&e2, &e3), &joined.mul(&e3, &e2));
        assert_eq!(anti23, joined.scalar(r(1)));

        // e0 (left block) and e2 (right block) purely anticommute: {e0,e2}=0,
        // since direct_sum puts nothing in the cross-block (0,2) key.
        let e0 = joined.e(0);
        let anti02 = joined.add(&joined.mul(&e0, &e2), &joined.mul(&e2, &e0));
        assert!(anti02.is_zero());
    }
}
