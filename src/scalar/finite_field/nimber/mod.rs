//! Nimbers: the ordinals under nim-addition and nim-multiplication, Conway's
//! Field On_2 of characteristic 2. Restricted here to `u128`, i.e. nimbers
//! below 2^128 — which *is* exactly the finite nim-field F_{2^128}, and contains
//! every smaller F_{2^{2^k}} (k <= 7: F_4, F_16, F_256, ... F_{2^128}).
//!
//! The implementation is split along the actual layers:
//!
//! * `arithmetic` — XOR addition, nim multiplication, Frobenius/sqrt, inverse.
//! * `artin_schreier` — trace and the `y² + y = c` solver.
//! * `galois` — degree, conjugates, minimal polynomial, relative trace/norm,
//!   multiplicative order, primitive elements, and discrete log.
//!
//! The public `nim_*` functions stay re-exported from this module, so callers can
//! keep using `scalar::nim_mul`, `scalar::nim_trace`, etc.

mod arithmetic;
mod artin_schreier;
mod galois;

pub use arithmetic::*;
pub use artin_schreier::*;
pub use galois::*;

use crate::scalar::Scalar;

/// A nimber, i.e. an element of On_2 truncated to F_{2^128}.
///
/// **Representation constructor vs ℤ-embedding:**
/// `Nimber(n)` is the *representation* constructor — it says "the nimber *n*",
/// treating the u128 as a nim-field element directly.
/// The ℤ-embedding `Scalar::from_int(n)` is `n mod 2` (the unique unital ring
/// homomorphism ℤ → F_{2^128}); for char-2, that is just 0 or 1.
///
/// # Examples
///
/// Addition is XOR and multiplication is Conway's nim product; on `u128` they
/// form exactly the field `F_{2^128}` (not the algebraic closure of `F_2`, which
/// needs [`Ordinal`](crate::scalar::Ordinal)).
///
/// ```
/// use ogdoad::scalar::{FiniteField, Nimber, Scalar};
///
/// assert_eq!(Nimber(2) * Nimber(2), Nimber(3)); // 2 ⊗ 2 = 3
/// assert_eq!(Nimber(4) * Nimber(4), Nimber(6)); // F ⊗ F = (3/2) F for a Fermat 2-power F
/// assert_eq!(Nimber(8) * Nimber(8), Nimber(13));
/// assert_eq!(Nimber(2).inv(), Some(Nimber(3))); // 2 ⊗ 3 = 1, so {0, 1, 2, 3} is F_4
/// assert_eq!(Nimber(5) + Nimber(3), Nimber(6)); // nim-sum is XOR
/// assert_eq!(Nimber::from_int(3), Nimber(1)); // the ℤ-embedding reduces mod 2
/// assert_eq!(Nimber::group_order(), u128::MAX); // |F_{2^128}^*| = 2^128 - 1
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Nimber(pub u128);

impl Nimber {
    /// The nimber/game-value fuzzy relation: distinct nimbers are incomparable.
    pub fn fuzzy(&self, other: &Self) -> bool {
        self != other
    }
}

impl std::fmt::Display for Nimber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "*{}", self.0)
    }
}

impl std::fmt::Debug for Nimber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl Scalar for Nimber {
    const REASSOCIATION_IS_EXACT: bool = true;

    fn zero() -> Self {
        Nimber(0)
    }
    fn one() -> Self {
        Nimber(1)
    }
    fn add(&self, rhs: &Self) -> Self {
        Nimber(nim_add(self.0, rhs.0))
    }
    fn neg(&self) -> Self {
        // characteristic 2: every element is its own additive inverse
        *self
    }
    fn mul(&self, rhs: &Self) -> Self {
        Nimber(nim_mul(self.0, rhs.0))
    }

    /// Square-and-multiply would cost `O(log e)` nim products; the Fermat-tower
    /// `nim_pow` is the sharper algorithm.
    fn pow(&self, exp: u128) -> Self {
        Nimber(nim_pow(self.0, exp))
    }
    fn characteristic() -> u128 {
        2
    }
    fn inv(&self) -> Option<Self> {
        nim_inv(self.0).map(Nimber)
    }
}

#[cfg(test)]
mod tests;
