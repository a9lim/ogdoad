//! Odd finite-field capability trait and scalar-level helpers.

use crate::scalar::{ExactFieldScalar, Fp, Fpn, Scalar};

/// Panics (rather than returning `Option`) because this guards internal
/// helpers (`is_square`, `hilbert_symbol`) that are only ever reached after a
/// `FiniteOddField` bound or `ensure_supported()` call has already validated
/// `P` — a failed check here is a programming-error invariant, not caller
/// input. Contrast `field_invariants.rs`'s `Option`-returning entry points,
/// which take an arbitrary `P` straight from the public API and must fail
/// gracefully.
pub(super) fn assert_odd_prime<const P: u128>() {
    Fp::<P>::assert_supported_params();
    assert!(P != 2, "odd-characteristic form theory needs P odd");
}

/// Finite fields of odd characteristic, with the operations the form classifiers
/// actually need: field-order metadata, base-field constants, and square classes.
/// This is intentionally narrower than [`Scalar`]: it is a form-theory façade, not
/// a new scalar-world requirement.
pub trait FiniteOddField: ExactFieldScalar + Copy {
    /// Characteristic prime `p`.
    fn characteristic_prime() -> u128;

    /// Field order `q = p^n`.
    fn field_order() -> u128;

    /// Whether this type is a supported finite field of odd characteristic.
    fn is_supported_odd_field() -> bool;

    /// Enumerate the field: index `i ∈ [0, field_order())` ↦ a distinct element,
    /// covering all of `F_q` exactly once. Used by deterministic finite-field
    /// polynomial factorization in the function-field place layer.
    fn from_index(i: u128) -> Self;

    /// Square-class test in the field. `0` counts as a square.
    fn is_square_value(x: Self) -> bool;

    /// Return `Some(())` exactly for supported odd finite fields.
    fn ensure_supported() -> Option<()> {
        Self::is_supported_odd_field().then_some(())
    }
}

impl<const P: u128> FiniteOddField for Fp<P> {
    fn characteristic_prime() -> u128 {
        P
    }

    fn field_order() -> u128 {
        P
    }

    fn is_supported_odd_field() -> bool {
        Fp::<P>::modulus_is_prime() && P != 2
    }

    fn from_index(i: u128) -> Self {
        Fp::<P>::from_u128(i)
    }

    fn is_square_value(x: Self) -> bool {
        is_square(x)
    }
}

impl<const P: u128, const N: usize> FiniteOddField for Fpn<P, N> {
    fn characteristic_prime() -> u128 {
        P
    }

    fn field_order() -> u128 {
        Fpn::<P, N>::field_order()
    }

    fn is_supported_odd_field() -> bool {
        Fpn::<P, N>::is_supported_field() && P != 2
    }

    fn from_index(i: u128) -> Self {
        // base-P digits of `i` are the polynomial-basis coordinates of the element.
        let mut digits = [0u128; N];
        let mut x = i;
        for d in digits.iter_mut() {
            *d = x % P;
            x /= P;
        }
        Fpn::<P, N>::from_coeffs(&digits)
    }

    fn is_square_value(x: Self) -> bool {
        x.is_square()
    }
}

/// Euler's criterion: is `x` a square in `F_P`? (`0` counts as a square.)
pub fn is_square<const P: u128>(x: Fp<P>) -> bool {
    assert_odd_prime::<P>();
    if x.is_zero() {
        return true;
    }
    x.pow((P - 1) / 2) == Fp::<P>::one()
}

/// Square-class predicate over any supported finite field of odd characteristic.
pub fn is_square_finite<F: FiniteOddField>(x: F) -> bool {
    assert!(
        F::is_supported_odd_field(),
        "odd-characteristic finite-field form theory needs odd finite fields"
    );
    F::is_square_value(x)
}

/// The Hilbert symbol `(a, b)` over `F_P`: `+1` iff `z² = a x² + b y²` has a
/// nontrivial solution. Over a finite field this is identically `+1` for nonzero
/// `a, b` (computed by an honest search, which always succeeds).
pub fn hilbert_symbol<const P: u128>(a: Fp<P>, b: Fp<P>) -> i128 {
    assert_odd_prime::<P>();
    for x in 0..P {
        for y in 0..P {
            for z in 0..P {
                if x == 0 && y == 0 && z == 0 {
                    continue;
                }
                let (fx, fy, fz) = (
                    Fp::<P>::from_u128(x),
                    Fp::<P>::from_u128(y),
                    Fp::<P>::from_u128(z),
                );
                let rhs = a.mul(&fx.mul(&fx)).add(&b.mul(&fy.mul(&fy)));
                if fz.mul(&fz) == rhs {
                    return 1;
                }
            }
        }
    }
    -1
}
