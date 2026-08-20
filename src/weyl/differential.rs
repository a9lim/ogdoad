use super::algebra::{WeylAlgebra, WeylError};
use super::element::WeylElement;
use super::product::embed_nat;
use crate::scalar::{Poly, Scalar};

impl<S: Scalar> WeylAlgebra<S> {
    /// Apply an element of the standard rank-one Weyl algebra to `S[t]`, with
    /// `x` acting by multiplication by `t` and `d` by formal differentiation.
    ///
    /// This representation respects multiplication over every scalar backend.
    /// It is not faithful in positive characteristic: for example, `d^p` acts as
    /// zero when the scalar characteristic is the prime `p`, while `d^p` remains
    /// a nonzero central Weyl element.
    pub fn act_on_poly(
        &self,
        operator: &WeylElement<S>,
        polynomial: &Poly<S>,
    ) -> Result<Poly<S>, WeylError> {
        self.validate_element(operator)?;
        if self.standard_pairs != Some(1) {
            return Err(WeylError::RequiresStandardRankOne);
        }
        let mut output = Poly::zero();
        for (monomial, operator_coefficient) in &operator.terms {
            let x_power = monomial.exponents()[0];
            let d_power = monomial.exponents()[1];
            for (degree, polynomial_coefficient) in polynomial.coeffs().iter().enumerate() {
                if polynomial_coefficient.is_zero() || d_power > degree as u128 {
                    continue;
                }
                let derivative_order = d_power as usize;
                let mut coefficient = operator_coefficient.mul(polynomial_coefficient);
                for offset in 0..derivative_order {
                    coefficient = coefficient.mul(&embed_nat::<S>((degree - offset) as u128));
                    if coefficient.is_zero() {
                        break;
                    }
                }
                if coefficient.is_zero() {
                    continue;
                }
                let remaining_degree = degree - derivative_order;
                let x_degree =
                    usize::try_from(x_power).map_err(|_| WeylError::PolynomialDegreeOverflow)?;
                let output_degree = remaining_degree
                    .checked_add(x_degree)
                    .ok_or(WeylError::PolynomialDegreeOverflow)?;
                output = output.add(&Poly::monomial(output_degree, coefficient));
            }
        }
        Ok(output)
    }
}
