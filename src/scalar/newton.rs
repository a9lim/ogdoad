//! The **Newton polygon** of a polynomial over a discretely-valued field — the
//! *tropical curve* of the place axis, and the payoff object of Bridge J.
//!
//! For `f = Σ aᵢ xⁱ ∈ K[x]` over a [`Valued`] field `K`, the Newton polygon is the
//! lower convex hull of the points `(i, v(aᵢ))`. Its sides are tropical line
//! segments whose **slopes are the negatives of the valuations of the roots**
//! (horizontal length = multiplicity) — the slope theorem (Bridge J, Theorem J.5;
//! Koblitz GTM 58 Ch. IV, Neukirch Ch. II). It is the same `(min, +)` arithmetic
//! that the games pillar's thermography computes on the *game* axis, applied to the
//! valuation read as the [tropicalization](crate::scalar::tropicalize) map of
//! [`Valued`].
//!
//! ## Orientation (the implementation trap)
//!
//! With points `(i, v(aᵢ))`, a side of slope `−λ` carries roots of valuation `+λ`.
//! To keep the public surface matching "slopes are the valuations of the roots",
//! [`root_valuations`](NewtonPolygon::root_valuations) returns the **negated**
//! slopes (with horizontal lengths = multiplicities), so callers never negate; the
//! literal hull slopes are available via [`slopes`](NewtonPolygon::slopes). Slopes
//! are [`Rational`] because root valuations can be fractional (the `Ramified`
//! `xᴱ − ϖ` case has roots of valuation `1/E`) even though the value group is `ℤ`.
//!
//! ## What it sees, and forgets
//!
//! The polygon is the image of the Springer decomposition
//! ([`springer_decompose_local`](crate::forms::springer_decompose_local)) under
//! tropicalization: it records `(valuation, multiplicity)` per layer and **forgets**
//! the residue square classes (the `disc_is_square` bit), giving the forgetful
//! hierarchy `NP(f) ≺ {initial forms} ≺ f` (Bridge J, Remark J.13). The
//! cross-check — every Newton slope *is* a Springer residue layer — is witnessed in
//! [`forms::springer`](crate::forms::springer)'s tests.
//!
//! ## Precision
//!
//! On the capped-relative models (`Qp`/`Qq`/`Laurent`/`Ramified`/`Gauss`) the
//! valuation of a *represented nonzero* coefficient is exact, so the polygon of
//! represented coefficients is exact; a coefficient whose true valuation exceeds the
//! precision horizon renders as `0` (its vertex is absent). The completion of
//! `F_q(t)` at a degree-1 finite place is literally the `Laurent` backend, so the
//! global function-field polygons are exact too (Corollary J.9).

use crate::scalar::{Rational, Valued};

/// The Newton polygon of a polynomial over a [`Valued`] field: the lower convex
/// hull of `{(i, v(aᵢ)) : aᵢ ≠ 0}`, plus the multiplicity of the root `0`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NewtonPolygon {
    /// Vertices `(i, v(aᵢ))` of the lower hull, left→right (strictly increasing
    /// `i`, strictly increasing side slopes).
    vertices: Vec<(usize, i128)>,
    /// Multiplicity of the root `0` (valuation `+∞`): the power of `x` dividing `f`,
    /// i.e. the number of vanishing lowest-order coefficients.
    zero_root_mult: usize,
}

/// The lower convex hull of points sorted by strictly increasing `x`. Walks from
/// the leftmost point, repeatedly choosing the next vertex of minimal slope (ties
/// broken by the farthest point), so the hull slopes strictly increase. `O(n²)`,
/// which is ample for the small polynomials this serves.
fn lower_hull(points: &[(usize, i128)]) -> Vec<(usize, i128)> {
    if points.len() <= 1 {
        return points.to_vec();
    }
    let mut hull = vec![points[0]];
    let mut cur = 0usize;
    while cur + 1 < points.len() {
        let (cx, cy) = points[cur];
        let mut best = cur + 1;
        for j in (cur + 1)..points.len() {
            let (jx, jy) = points[j];
            let (bx, by) = points[best];
            // Compare slope c→j against slope c→best by cross-multiplication; the
            // x-gaps are positive (j, best > cur), so the inequality direction is
            // preserved. Minimal slope wins; ties go to the larger x (farther point,
            // which absorbs the collinear interior point into the side).
            let (dxj, dxb) = ((jx - cx) as i128, (bx - cx) as i128);
            let (lhs, rhs) = ((jy - cy) * dxb, (by - cy) * dxj);
            if lhs < rhs || (lhs == rhs && jx > bx) {
                best = j;
            }
        }
        hull.push(points[best]);
        cur = best;
    }
    hull
}

impl NewtonPolygon {
    /// The Newton polygon of `f = Σ coeffs[i]·xⁱ` (coefficients low-degree-first).
    /// `None` for the zero polynomial (no nonzero coefficient). Coefficients reading
    /// as `0` — genuine zeros, or values below the precision horizon — are simply
    /// absent from the point set, matching the convex-hull definition.
    pub fn of<K: Valued>(coeffs: &[K]) -> Option<NewtonPolygon> {
        let points: Vec<(usize, i128)> = coeffs
            .iter()
            .enumerate()
            .filter_map(|(i, c)| c.valuation().map(|v| (i, v)))
            .collect();
        let zero_root_mult = points.first()?.0; // lowest nonzero index ⇒ x^m | f
        Some(NewtonPolygon {
            vertices: lower_hull(&points),
            zero_root_mult,
        })
    }

    /// The lower-hull vertices `(i, v(aᵢ))`, left→right.
    pub fn vertices(&self) -> &[(usize, i128)] {
        &self.vertices
    }

    /// The polynomial degree captured by the polygon (the largest index with a
    /// nonzero coefficient), or `0` for a constant.
    pub fn degree(&self) -> usize {
        self.vertices.last().map_or(0, |&(x, _)| x)
    }

    /// Multiplicity of the root `0` (valuation `+∞`): the power of `x` dividing `f`.
    pub fn zero_root_multiplicity(&self) -> usize {
        self.zero_root_mult
    }

    /// The literal **side slopes** `(slope, horizontal length)`, left→right and
    /// strictly increasing. A root of valuation `λ` sits on the side of slope `−λ`
    /// (see [`root_valuations`](Self::root_valuations) for the un-negated view).
    pub fn slopes(&self) -> Vec<(Rational, u128)> {
        self.vertices
            .windows(2)
            .map(|w| {
                let ((x0, y0), (x1, y1)) = (w[0], w[1]);
                (Rational::new(y1 - y0, (x1 - x0) as i128), (x1 - x0) as u128)
            })
            .collect()
    }

    /// The **valuations of the finite (nonzero) roots**, with multiplicities:
    /// `(λ, ℓ)` for each side of slope `−λ` and horizontal length `ℓ` (the slope
    /// theorem, J.5). Strictly *decreasing* in `λ`. Excludes the `0`-roots of
    /// valuation `+∞` (see [`zero_root_multiplicity`](Self::zero_root_multiplicity)).
    pub fn root_valuations(&self) -> Vec<(Rational, u128)> {
        self.vertices
            .windows(2)
            .map(|w| {
                let ((x0, y0), (x1, y1)) = (w[0], w[1]);
                // root valuation λ = −slope = (y0 − y1)/(x1 − x0).
                (Rational::new(y0 - y1, (x1 - x0) as i128), (x1 - x0) as u128)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{Fp, Laurent, Poly, Qp, Ramified, Scalar};

    fn rat(n: i128, d: i128) -> Rational {
        Rational::new(n, d)
    }

    type Q5 = Qp<5, 8>;

    /// Build `Σ cᵢ xⁱ` over `Q_5` from integer coefficients.
    fn qpoly(coeffs: &[i128]) -> Vec<Q5> {
        coeffs.iter().map(|&n| Q5::from_i128(n)).collect()
    }

    /// Eisenstein `xᴱ − p`: a single side of slope `−1/E`, every root valuation
    /// `1/E` (J.7) — and the `Ramified` renormalization sends `v(π) = 1`.
    #[test]
    fn eisenstein_single_slope() {
        // x³ − 5 over Q_5: coeffs [−5, 0, 0, 1].
        let np = NewtonPolygon::of(&qpoly(&[-5, 0, 0, 1])).unwrap();
        assert_eq!(np.root_valuations(), vec![(rat(1, 3), 3)]);
        assert_eq!(np.degree(), 3);
        assert_eq!(np.zero_root_multiplicity(), 0);
        // The cross-check to the renormalized ramified leg: π with πᴱ = p has v = 1.
        assert_eq!(Ramified::<Qp<5, 8>, 3>::pi().valuation(), Some(1));
    }

    /// `x² − p`: root valuation `1/2 ∉ ℤ`; p is a nonsquare (odd valuation).
    #[test]
    fn sqrt_p_slope_half() {
        let np = NewtonPolygon::of(&qpoly(&[-5, 0, 1])).unwrap();
        assert_eq!(np.root_valuations(), vec![(rat(1, 2), 2)]);
        // odd valuation ⇒ 5 is not a square in Q_5 (the analytic cross-check).
        assert_eq!(Q5::from_i128(5).is_square(), Some(false));
    }

    /// Distinct-slope factors concatenate; per-slope lengths add (Dumas, J.6).
    /// `(x − 5)(x − 1) = x² − 6x + 5`: one root of valuation 1, one of valuation 0.
    #[test]
    fn dumas_additivity() {
        let f = Poly::new(qpoly(&[-5, 1])); // x − 5  (root valuation 1)
        let g = Poly::new(qpoly(&[-1, 1])); // x − 1  (root valuation 0)
        let fg = f.mul(&g);
        let np = NewtonPolygon::of(fg.coeffs()).unwrap();
        // sorted by decreasing λ: (1, 1) then (0, 1).
        assert_eq!(np.root_valuations(), vec![(rat(1, 1), 1), (rat(0, 1), 1)]);

        // a higher-multiplicity check: (x²−5)(x−1) — two val-½ roots, one val-0 root.
        let h = Poly::new(qpoly(&[-5, 0, 1])).mul(&g);
        let nph = NewtonPolygon::of(h.coeffs()).unwrap();
        assert_eq!(nph.root_valuations(), vec![(rat(1, 2), 2), (rat(0, 1), 1)]);
    }

    /// Monic integral `f` has an all-flat polygon iff `a₀` is a unit iff every root
    /// is a unit (J.8). `x² + 3x + 2` over Q_5: all coeffs units ⇒ one flat side.
    #[test]
    fn flat_polygon_iff_unit_roots() {
        let np = NewtonPolygon::of(&qpoly(&[2, 3, 1])).unwrap();
        assert_eq!(np.root_valuations(), vec![(rat(0, 1), 2)]);
        assert_eq!(Q5::from_i128(2).valuation(), Some(0)); // a₀ a unit
        assert!(np.slopes().iter().all(|(s, _)| *s == Rational::zero()));

        // break it: x² + 3x + 5 has a₀ = 5 (valuation 1) ⇒ no longer all-flat.
        let np2 = NewtonPolygon::of(&qpoly(&[5, 3, 1])).unwrap();
        assert_ne!(np2.root_valuations(), vec![(rat(0, 1), 2)]);
        assert_eq!(np2.root_valuations(), vec![(rat(1, 1), 1), (rat(0, 1), 1)]);
    }

    /// Negative root valuations: `x − p⁻¹` has a root of valuation `−1`.
    #[test]
    fn negative_slope_for_pole_root() {
        let coeffs = vec![Q5::from_p_power(-1).neg(), Q5::one()]; // x − p⁻¹
        let np = NewtonPolygon::of(&coeffs).unwrap();
        assert_eq!(np.root_valuations(), vec![(rat(-1, 1), 1)]);
    }

    /// The root `0` (valuation `+∞`) is tracked separately: `x²·(x − 1)` has a
    /// double zero root plus one unit root.
    #[test]
    fn zero_roots_are_tracked() {
        // x³ − x²  = coeffs [0, 0, −1, 1].
        let np = NewtonPolygon::of(&qpoly(&[0, 0, -1, 1])).unwrap();
        assert_eq!(np.zero_root_multiplicity(), 2);
        assert_eq!(np.root_valuations(), vec![(rat(0, 1), 1)]);
    }

    /// The equal-characteristic leg `F_7((t))` (the completion of `F_7(t)` at a
    /// degree-1 place) is exact: Eisenstein `x² − t` gives root valuation `1/2`.
    #[test]
    fn laurent_leg_is_exact() {
        type L = Laurent<Fp<7>, 8>;
        let t = L::t();
        let minus_t = t.neg();
        let coeffs = vec![minus_t, L::zero(), L::one()]; // x² − t
        let np = NewtonPolygon::of(&coeffs).unwrap();
        assert_eq!(np.root_valuations(), vec![(rat(1, 2), 2)]);
    }

    /// The zero polynomial has no Newton polygon.
    #[test]
    fn zero_polynomial_is_none() {
        assert!(NewtonPolygon::of::<Q5>(&[]).is_none());
        assert!(NewtonPolygon::of(&qpoly(&[0, 0, 0])).is_none());
    }
}
