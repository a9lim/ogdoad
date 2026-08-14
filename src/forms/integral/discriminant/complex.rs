//! Dependency-free complex arithmetic for Gauss sums and Weil matrices.

/// A tiny dependency-free complex number for Gauss sums and Weil matrices.
///
/// This type supplies the small `f64` surface needed by the discriminant-form
/// Weil representation.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Complex64 {
    /// Real component.
    pub re: f64,
    /// Imaginary component.
    pub im: f64,
}

impl Complex64 {
    /// Additive identity.
    pub fn zero() -> Self {
        Complex64 { re: 0.0, im: 0.0 }
    }

    /// Multiplicative identity.
    pub fn one() -> Self {
        Complex64 { re: 1.0, im: 0.0 }
    }

    /// Unit complex number with argument `theta`.
    pub fn cis(theta: f64) -> Self {
        Complex64 {
            re: theta.cos(),
            im: theta.sin(),
        }
    }

    /// `exp(pi*i*k/4)`.
    pub fn eighth_root(k: i128) -> Self {
        Complex64::cis((k.rem_euclid(8) as f64) * std::f64::consts::FRAC_PI_4)
    }

    /// Complex modulus.
    pub fn abs(&self) -> f64 {
        self.re.hypot(self.im)
    }

    /// Complex addition.
    pub fn add(&self, rhs: &Self) -> Self {
        Complex64 {
            re: self.re + rhs.re,
            im: self.im + rhs.im,
        }
    }

    /// Complex subtraction.
    pub fn sub(&self, rhs: &Self) -> Self {
        Complex64 {
            re: self.re - rhs.re,
            im: self.im - rhs.im,
        }
    }

    /// Complex multiplication.
    pub fn mul(&self, rhs: &Self) -> Self {
        Complex64 {
            re: self.re * rhs.re - self.im * rhs.im,
            im: self.re * rhs.im + self.im * rhs.re,
        }
    }

    /// Multiplication by a real scalar.
    pub fn scale(&self, c: f64) -> Self {
        Complex64 {
            re: self.re * c,
            im: self.im * c,
        }
    }

    /// Whether both values agree within Euclidean tolerance `tol`.
    pub fn approx_eq(&self, rhs: &Self, tol: f64) -> bool {
        self.sub(rhs).abs() <= tol
    }
}
