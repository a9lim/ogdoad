//! The **global rational function field** `F_q(t)` — the equal-characteristic
//! mirror of `ℚ` as a global field.
//!
//! It is a global **field** whose ring regular away from infinity is `F_q[t]`.
//! At a monic irreducible place `π`, its completion is isomorphic to a Laurent
//! field over the residue extension `F_{q^deg π}`; at infinity it is
//! `F_q((1/t))`. Its arithmetic feeds the
//! local–global form layer [`forms::function_field`](crate::forms) (Hilbert
//! reciprocity `∏_v (a,b)_v = +1` and Hasse–Minkowski over `F_q(t)`), the exact
//! char-`p` mirror of [`forms::padic`](crate::forms)/[`forms::adelic`](crate::forms).
//!
//! ## Exact, unlike the local precision models
//!
//! `RationalFunction` is **exact** over an exact finite base: a genuine commutative field
//! over an exact finite base, so it *joins* the fuzz suite. The product formula it
//! ultimately witnesses — `deg(zeros) = deg(poles)` — is combinatorial and exact,
//! the cleaner mirror of the `ℚ`-adele's archimedean absolute value.
//!
//! ## Representation
//!
//! `num(t) / den(t)` as a pair of [`Poly`]s, with numerator and denominator
//! gcd-reduced and the denominator normalized monic. This differs deliberately from
//! [`Gauss`](crate::scalar::Gauss), whose capped-precision valuation model keeps
//! unreduced fractions to avoid precision-unstable cancellation. `RationalFunction`
//! is exact, so canonical reduction is safe and keeps global-place arithmetic from
//! growing unnecessary common factors. Like [`Adele`](crate::scalar::Adele), it is
//! deliberately **not** `Valued` (no single canonical uniformizer); the forms layer
//! computes per-place valuations from [`num`](RationalFunction::num) and
//! [`den`](RationalFunction::den).

use crate::scalar::{ExactFieldScalar, Poly, Scalar};
use std::fmt;

/// Below this polynomial degree, constructing the products and reducing once
/// is cheaper than four exact divisions around the two cross-gcds.
const CROSS_CANCEL_MIN_DEGREE: usize = 32;

/// An element of `F_q(t)` (more generally `S(t)` over any field `S`): `num / den`
/// with `den` monic.
#[derive(Clone)]
pub struct RationalFunction<S: ExactFieldScalar> {
    num: Poly<S>,
    den: Poly<S>,
}

impl<S: ExactFieldScalar> RationalFunction<S> {
    /// Assemble `num / den` (already-`Poly`), gcd-reducing and normalizing the
    /// denominator to monic.
    fn from_polys(num: Poly<S>, den: Poly<S>) -> Self {
        assert!(!den.is_zero(), "RationalFunction: zero denominator");
        if num.is_zero() {
            return RationalFunction {
                num: Poly::zero(),
                den: Poly::one(),
            };
        }
        let gcd = num.gcd(&den);
        let (num, den) = if gcd == Poly::one() {
            (num, den)
        } else {
            let (nq, nr) = num.divrem(&gcd);
            let (dq, dr) = den.divrem(&gcd);
            debug_assert!(nr.is_zero() && dr.is_zero(), "gcd must divide both");
            (nq, dq)
        };
        Self::from_coprime_polys(num, den)
    }

    /// Assemble an already-coprime fraction, normalizing only the denominator.
    fn from_coprime_polys(num: Poly<S>, den: Poly<S>) -> Self {
        debug_assert!(!den.is_zero());
        if den.leading() == Some(&S::one()) {
            return RationalFunction { num, den };
        }
        let lead_inv = den
            .leading()
            .expect("nonzero denominator has a leading coefficient")
            .inv()
            .expect("a field's nonzero leading coefficient inverts");
        RationalFunction {
            num: num.scale(&lead_inv),
            den: den.scale(&lead_inv),
        }
    }

    /// Build `num / den` from low-degree-first coefficient vectors over `S`.
    pub fn new(num: Vec<S>, den: Vec<S>) -> Self {
        RationalFunction::from_polys(Poly::new(num), Poly::new(den))
    }

    /// A polynomial as a rational function `p / 1`.
    pub fn from_poly(p: Poly<S>) -> Self {
        RationalFunction {
            num: p,
            den: Poly::one(),
        }
    }

    /// Embed a base scalar as the constant `s / 1`.
    pub fn from_base(s: S) -> Self {
        RationalFunction::from_poly(Poly::constant(s))
    }

    /// The indeterminate `t`.
    pub fn t() -> Self {
        RationalFunction::from_poly(Poly::t())
    }

    /// The numerator polynomial.
    pub fn num(&self) -> &Poly<S> {
        &self.num
    }

    /// The (monic) denominator polynomial.
    pub fn den(&self) -> &Poly<S> {
        &self.den
    }

    fn has_unit_denominator(&self) -> bool {
        // Canonical denominators are monic, so a constant denominator is 1.
        self.den.degree() == Some(0)
    }

    fn is_one(&self) -> bool {
        self.has_unit_denominator()
            && self.num.degree() == Some(0)
            && self.num.leading() == Some(&S::one())
    }

    fn polynomial_is_one(polynomial: &Poly<S>) -> bool {
        polynomial.degree() == Some(0) && polynomial.leading() == Some(&S::one())
    }

    fn exact_quotient(dividend: &Poly<S>, divisor: &Poly<S>) -> Poly<S> {
        if Self::polynomial_is_one(divisor) {
            return dividend.clone();
        }
        let (quotient, remainder) = dividend.divrem(divisor);
        debug_assert!(remainder.is_zero(), "known factor must divide exactly");
        quotient
    }

    fn should_cross_cancel_with(&self, rhs: &Self) -> bool {
        [
            self.num.degree(),
            self.den.degree(),
            rhs.num.degree(),
            rhs.den.degree(),
        ]
        .into_iter()
        .flatten()
        .max()
        .is_some_and(|degree| degree >= CROSS_CANCEL_MIN_DEGREE)
    }
}

impl<S: ExactFieldScalar> PartialEq for RationalFunction<S> {
    /// Canonical pairs are equal exactly when both stored polynomials are equal.
    /// Every construction path gcd-reduces and makes the denominator monic.
    fn eq(&self, other: &Self) -> bool {
        self.num == other.num && self.den == other.den
    }
}

impl<S: ExactFieldScalar> fmt::Display for RationalFunction<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den == Poly::one() {
            write!(f, "{}", self.num)
        } else {
            // Fractions render as `(num)/(den)` with each polynomial side canonical.
            write!(f, "({})/({})", self.num, self.den)
        }
    }
}

impl<S: ExactFieldScalar> fmt::Debug for RationalFunction<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<S: ExactFieldScalar> Scalar for RationalFunction<S> {
    fn zero() -> Self {
        RationalFunction {
            num: Poly::zero(),
            den: Poly::one(),
        }
    }

    fn one() -> Self {
        RationalFunction {
            num: Poly::one(),
            den: Poly::one(),
        }
    }

    fn add(&self, rhs: &Self) -> Self {
        if self.is_zero() {
            return rhs.clone();
        }
        if rhs.is_zero() {
            return self.clone();
        }
        if self.has_unit_denominator() && rhs.has_unit_denominator() {
            return RationalFunction::from_poly(self.num.add(&rhs.num));
        }
        if self.den == rhs.den {
            return RationalFunction::from_polys(self.num.add(&rhs.num), self.den.clone());
        }
        // Knuth's gcd-first fraction addition. With g = gcd(b,d), form
        // t = a(d/g) + c(b/g), then cancel only gcd(t,g). This avoids building
        // the duplicated denominator factor and running a gcd over the two
        // full-size products.
        let common_denominator = self.den.gcd(&rhs.den);
        if Self::polynomial_is_one(&common_denominator) {
            let numerator = self.num.mul(&rhs.den).add(&rhs.num.mul(&self.den));
            if numerator.is_zero() {
                return Self::zero();
            }
            return RationalFunction::from_coprime_polys(numerator, self.den.mul(&rhs.den));
        }
        let left_reduced_denominator = Self::exact_quotient(&self.den, &common_denominator);
        let right_reduced_denominator = Self::exact_quotient(&rhs.den, &common_denominator);
        let numerator = self
            .num
            .mul(&right_reduced_denominator)
            .add(&rhs.num.mul(&left_reduced_denominator));
        if numerator.is_zero() {
            return Self::zero();
        }
        let cancellation = numerator.gcd(&common_denominator);
        let numerator = Self::exact_quotient(&numerator, &cancellation);
        let right_denominator = Self::exact_quotient(&rhs.den, &cancellation);
        RationalFunction::from_coprime_polys(
            numerator,
            left_reduced_denominator.mul(&right_denominator),
        )
    }

    fn neg(&self) -> Self {
        RationalFunction {
            num: self.num.neg(),
            den: self.den.clone(),
        }
    }

    fn mul(&self, rhs: &Self) -> Self {
        if self.is_zero() || rhs.is_zero() {
            return Self::zero();
        }
        if self.is_one() {
            return rhs.clone();
        }
        if rhs.is_one() {
            return self.clone();
        }
        if self.has_unit_denominator() && rhs.has_unit_denominator() {
            return RationalFunction::from_poly(self.num.mul(&rhs.num));
        }
        if !self.should_cross_cancel_with(rhs) {
            return RationalFunction::from_polys(self.num.mul(&rhs.num), self.den.mul(&rhs.den));
        }
        // Canonical inputs are internally coprime. Cancelling gcd(a,d) and
        // gcd(c,b) before multiplication therefore produces a canonical pair
        // directly while keeping polynomial intermediates small.
        let left_cross = if rhs.has_unit_denominator() {
            Poly::one()
        } else {
            self.num.gcd(&rhs.den)
        };
        let right_cross = if self.has_unit_denominator() {
            Poly::one()
        } else {
            rhs.num.gcd(&self.den)
        };
        let left_numerator = Self::exact_quotient(&self.num, &left_cross);
        let right_denominator = Self::exact_quotient(&rhs.den, &left_cross);
        let right_numerator = Self::exact_quotient(&rhs.num, &right_cross);
        let left_denominator = Self::exact_quotient(&self.den, &right_cross);
        RationalFunction::from_coprime_polys(
            left_numerator.mul(&right_numerator),
            left_denominator.mul(&right_denominator),
        )
    }

    fn characteristic() -> u128 {
        S::characteristic()
    }

    fn inv(&self) -> Option<Self> {
        if self.num.is_zero() {
            return None;
        }
        // (num/den)⁻¹ = den/num — total on nonzero, no gcd needed.
        Some(RationalFunction::from_coprime_polys(
            self.den.clone(),
            self.num.clone(),
        ))
    }

    fn is_zero(&self) -> bool {
        self.num.is_zero()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::Fp;

    type F = RationalFunction<Fp<5>>;

    fn rf(num: &[i128], den: &[i128]) -> F {
        RationalFunction::new(
            num.iter().map(|&n| Fp::<5>::from_int(n)).collect(),
            den.iter().map(|&n| Fp::<5>::from_int(n)).collect(),
        )
    }

    #[test]
    fn is_an_exact_field() {
        let samples = [
            F::t(),
            F::from_base(Fp::<5>::from_int(2)),
            rf(&[1, 1], &[1]),       // 1 + t
            rf(&[1], &[0, 1]),       // 1/t
            rf(&[2, 0, 1], &[1, 1]), // (2 + t²)/(1 + t)
        ];
        for x in &samples {
            let xi = x.inv().expect("nonzero inverts in a field");
            assert_eq!(x.mul(&xi), F::one(), "x·x⁻¹ ≠ 1 for {x:?}");
        }
        assert_eq!(F::zero().inv(), None);
        assert_eq!(F::characteristic(), 5);
    }

    #[test]
    fn canonical_structural_equality() {
        // t/t = 1; (2t)/2 = t; common factors are removed on construction.
        assert_eq!(rf(&[0, 1], &[0, 1]), F::one());
        assert_eq!(rf(&[0, 2], &[2]), F::t());
        assert_eq!(F::t().add(&F::zero()), F::t());
        assert_eq!(F::t().mul(&F::one()), F::t());
        assert_ne!(F::t(), F::one());
    }

    #[test]
    fn fractions_are_gcd_reduced_and_denominator_monic() {
        // (t + 1)(t + 2) / (2(t + 1)) = (t + 2) / 2 = 1 + 3t over F_5.
        let x = rf(&[2, 3, 1], &[2, 2]);
        assert_eq!(x.den(), &Poly::one());
        assert_eq!(
            x.num(),
            &Poly::new(vec![Fp::<5>::from_int(1), Fp::<5>::from_int(3)])
        );
    }

    fn linear(constant: i128) -> Poly<Fp<5>> {
        Poly::new(vec![Fp::<5>::from_int(constant), Fp::<5>::one()])
    }

    fn polynomial_power(mut base: Poly<Fp<5>>, mut exponent: usize) -> Poly<Fp<5>> {
        let mut out = Poly::one();
        while exponent > 0 {
            if exponent & 1 == 1 {
                out = out.mul(&base);
            }
            exponent >>= 1;
            if exponent > 0 {
                base = base.mul(&base);
            }
        }
        out
    }

    #[test]
    fn multiplication_cross_cancels_before_forming_products() {
        let p = polynomial_power(linear(0), 16);
        let q = polynomial_power(linear(1), 16);
        let u = polynomial_power(linear(2), 16);
        let v = polynomial_power(linear(3), 16);
        let w = polynomial_power(linear(4), 16);
        let z = polynomial_power(
            Poly::new(vec![Fp::<5>::from_int(2), Fp::<5>::zero(), Fp::<5>::one()]),
            16,
        );
        let left = RationalFunction::from_polys(p.mul(&u), q.mul(&v));
        let right = RationalFunction::from_polys(q.mul(&w), p.mul(&z));
        assert!(left.should_cross_cancel_with(&right));
        let expected = RationalFunction::from_polys(u.mul(&w), v.mul(&z));
        assert_eq!(left.mul(&right), expected);
    }

    #[test]
    fn addition_reduces_a_shared_denominator_before_products() {
        let p = linear(0);
        let q = linear(1);
        let u = linear(2);
        let v = linear(3);
        let w = linear(4);
        let left = RationalFunction::from_polys(u, p.mul(&q));
        let right = RationalFunction::from_polys(w, p.mul(&v));
        let expected_numerator = left.num.mul(&right.den).add(&right.num.mul(&left.den));
        let expected_denominator = left.den.mul(&right.den);
        let expected = RationalFunction::from_polys(expected_numerator, expected_denominator);
        assert_eq!(left.add(&right), expected);
    }

    #[test]
    fn ring_axioms_on_a_sample() {
        let es = [
            F::zero(),
            F::one(),
            F::t(),
            F::from_base(Fp::<5>::from_int(3)),
            rf(&[1, 1], &[1]), // 1 + t
            rf(&[1], &[0, 1]), // 1/t
        ];
        for a in &es {
            assert_eq!(a.add(&F::zero()), *a);
            assert_eq!(a.add(&a.neg()), F::zero());
            assert_eq!(a.mul(&F::one()), *a);
            for b in &es {
                assert_eq!(a.add(b), b.add(a));
                assert_eq!(a.mul(b), b.mul(a));
                for d in &es {
                    assert_eq!(a.add(b).add(d), a.add(&b.add(d)));
                    assert_eq!(a.mul(b).mul(d), a.mul(&b.mul(d)));
                    assert_eq!(a.mul(&b.add(d)), a.mul(b).add(&a.mul(d)));
                }
            }
        }
    }

    #[test]
    fn display_uses_parenthesized_fraction() {
        // Fractions use `(num)/(den)`; `[…]` is reserved for vectors.
        let frac = rf(&[1], &[0, 1]); // 1/t
        assert_eq!(frac.to_string(), "(1)/(t)");
        // den == 1 prints the numerator alone, unchanged.
        assert_eq!(rf(&[1, 2], &[1]).to_string(), "2⋅t + 1");
    }

    #[test]
    fn num_den_accessors_expose_polys_for_the_forms_layer() {
        let x = rf(&[0, 1], &[1, 1]); // t / (1 + t)
        assert_eq!(
            x.num(),
            &Poly::new(vec![Fp::<5>::from_int(0), Fp::<5>::from_int(1)])
        );
        assert_eq!(
            x.den(),
            &Poly::new(vec![Fp::<5>::from_int(1), Fp::<5>::from_int(1)])
        );
    }
}
