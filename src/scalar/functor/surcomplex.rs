//! The quadratic algebra `S[i] = S[x]/(x² + 1)` over a scalar backend.
//!
//! Generic over `S`, so `Surcomplex<Surreal>` is the complexification of the
//! implemented finite-support surreal backend. `Surcomplex<Rational>` is the
//! Gaussian rational field `ℚ[i]`.
//!
//! Over a field this algebra is a quadratic field extension when `x² + 1` is
//! irreducible and a split algebra when it has distinct roots. In characteristic
//! two, `(1+i)² = 0`, so the algebra is nonreduced and not a field.

use crate::scalar::Scalar;

/// An element `re + im·i` of `S[i]`, with `i² = −1`.
///
/// # Examples
///
/// Over `Rational` this is the Gaussian rationals. Over `F_5`, where `-1` is a
/// square, `S[i]` splits and has zero divisors; in characteristic two,
/// `(1 + i)² = 0`, so it is not even reduced.
///
/// ```
/// use ogdoad::scalar::{Fp, Nimber, Rational, Scalar, Surcomplex};
///
/// let z = Surcomplex::new(Rational::one(), Rational::one()); // 1 + i
/// assert_eq!(z.mul(&z), Surcomplex::new(Rational::zero(), Rational::from_int(2))); // 2i
/// let half = Rational::new(1, 2);
/// assert_eq!(z.inv(), Some(Surcomplex::new(half.clone(), half.neg()))); // (1 - i)/2
///
/// let w = Surcomplex::new(Fp::<5>::from_int(2), Fp::<5>::one()); // (2+i)(2-i) = 5 = 0
/// assert!(!w.is_zero() && w.mul(&w.conj()).is_zero() && w.inv().is_none());
///
/// let n = Surcomplex::new(Nimber(1), Nimber(1)); // (1+i)^2 = 0
/// assert!(!n.is_zero() && n.mul(&n).is_zero());
/// ```
#[derive(Clone, PartialEq)]
pub struct Surcomplex<S: Scalar> {
    /// Real coefficient.
    pub re: S,
    /// Imaginary coefficient.
    pub im: S,
}

impl<S: Scalar> std::fmt::Display for Surcomplex<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // A coefficient that itself mentions `i` (a nested extension) is
        // parenthesized, and so is a multi-term imaginary part, so `ω + 1·i`
        // and `(ω + 1)·i`, or an inner and an outer `i`, stay distinct.
        let wrap = |part: String, multi_term: bool| {
            if part.contains("·i") || (multi_term && part.contains(' ')) {
                format!("({part})")
            } else {
                part
            }
        };
        let re = wrap(self.re.to_string(), false);
        if self.im.is_zero() {
            return write!(f, "{re}");
        }
        let im = wrap(self.im.to_string(), true);
        if self.re.is_zero() {
            write!(f, "{im}·i")
        } else {
            write!(f, "{re} + {im}·i")
        }
    }
}

impl<S: Scalar> std::fmt::Debug for Surcomplex<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl<S: Scalar> Surcomplex<S> {
    /// Construct `re + im·i`.
    pub fn new(re: S, im: S) -> Self {
        Surcomplex { re, im }
    }

    /// The imaginary unit i.
    pub fn i() -> Self {
        Surcomplex {
            re: S::zero(),
            im: S::one(),
        }
    }

    /// Complex conjugate a − b·i.
    pub fn conj(&self) -> Self {
        Surcomplex {
            re: self.re.clone(),
            im: self.im.neg(),
        }
    }
}

impl<S: Scalar> Scalar for Surcomplex<S> {
    fn zero() -> Self {
        Surcomplex {
            re: S::zero(),
            im: S::zero(),
        }
    }
    fn one() -> Self {
        Surcomplex {
            re: S::one(),
            im: S::zero(),
        }
    }
    fn add(&self, rhs: &Self) -> Self {
        Surcomplex {
            re: self.re.add(&rhs.re),
            im: self.im.add(&rhs.im),
        }
    }
    fn neg(&self) -> Self {
        Surcomplex {
            re: self.re.neg(),
            im: self.im.neg(),
        }
    }
    fn mul(&self, rhs: &Self) -> Self {
        // (a+bi)(c+di) = (ac − bd) + (ad + bc) i
        let ac = self.re.mul(&rhs.re);
        let bd = self.im.mul(&rhs.im);
        let ad = self.re.mul(&rhs.im);
        let bc = self.im.mul(&rhs.re);
        Surcomplex {
            re: ac.sub(&bd),
            im: ad.add(&bc),
        }
    }
    fn characteristic() -> u128 {
        // adjoining i does not change the characteristic
        S::characteristic()
    }
    fn inv(&self) -> Option<Self> {
        // (a+bi)^{-1} = (a − bi)/(a²+b²), valid when the norm a²+b² inverts in S.
        let n = self.re.mul(&self.re).add(&self.im.mul(&self.im));
        let ninv = n.inv()?;
        Some(Surcomplex {
            re: self.re.mul(&ninv),
            im: self.im.neg().mul(&ninv),
        })
    }
    fn is_zero(&self) -> bool {
        self.re.is_zero() && self.im.is_zero()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::Nimber;
    use crate::scalar::Rational;

    type Gauss = Surcomplex<Rational>;

    fn g(re: i128, im: i128) -> Gauss {
        Surcomplex::new(Rational::from_int(re), Rational::from_int(im))
    }

    #[test]
    fn gaussian_arithmetic() {
        let i = Gauss::i();
        assert_eq!(i.mul(&i), g(-1, 0)); // i^2 = -1
        let one_plus_i = g(1, 1);
        assert_eq!(one_plus_i.mul(&one_plus_i), g(0, 2)); // (1+i)^2 = 2i
        assert_eq!(one_plus_i.mul(&one_plus_i.conj()), g(2, 0)); // |1+i|^2 = 2
    }

    #[test]
    fn gaussian_inverse() {
        let z = g(1, 1); // 1 + i
        assert_eq!(z.mul(&z.inv().unwrap()), Gauss::one());
        let z2 = g(3, -2);
        assert_eq!(z2.mul(&z2.inv().unwrap()), Gauss::one());
        assert!(Gauss::zero().inv().is_none());
    }

    #[test]
    fn nimber_surcomplex_is_degenerate() {
        // Over char 2: i^2 = -1 = 1, so (1+i)^2 = 0. Nonzero nilpotent ⇒
        // not a field.
        type NC = Surcomplex<Nimber>;
        let i = NC::i();
        assert_eq!(i.mul(&i), NC::one()); // i^2 = 1, not -1≠1
        let one_plus_i = NC::new(Nimber(1), Nimber(1));
        assert!(one_plus_i.mul(&one_plus_i).is_zero()); // (1+i)^2 = 0
        assert!(!one_plus_i.is_zero()); // but 1+i itself ≠ 0
    }

    #[test]
    fn display_parenthesizes_a_multi_term_imaginary_part() {
        use crate::scalar::Surreal;
        let w = Surreal::omega();
        let one = Surreal::one();
        let a = Surcomplex::new(w.clone(), one.clone());
        let b = Surcomplex::new(Surreal::zero(), w.add(&one));
        assert_ne!(a.to_string(), b.to_string());
        assert_eq!(b.to_string(), format!("({})·i", w.add(&one)));
        // An inner `i` as a real part is not the outer `i`.
        type Inner = Surcomplex<Rational>;
        let inner_i = Surcomplex::new(Inner::i(), Inner::zero());
        let outer_i = Surcomplex::new(Inner::zero(), Inner::one());
        assert_eq!(inner_i.to_string(), "(1·i)");
        assert_eq!(outer_i.to_string(), "1·i");
        let mixed = Surcomplex::new(Inner::one(), Inner::i());
        assert_eq!(mixed.to_string(), "1 + (1·i)·i");
    }
}
