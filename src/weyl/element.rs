use crate::scalar::Scalar;
use std::collections::BTreeMap;
use std::fmt;
use std::ops::{Add, Neg, Sub};

/// The exponent vector of one canonical PBW monomial
/// `z_0^a_0 ... z_(m-1)^a_(m-1)`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct WeylMonomial {
    pub(crate) exponents: Box<[u128]>,
}

impl WeylMonomial {
    pub(crate) fn new(exponents: Vec<u128>) -> Self {
        Self {
            exponents: exponents.into_boxed_slice(),
        }
    }

    /// The ordered exponent vector.
    pub fn exponents(&self) -> &[u128] {
        &self.exponents
    }

    /// The total PBW degree, or `None` if the `u128` sum overflows.
    pub fn total_degree(&self) -> Option<u128> {
        self.exponents
            .iter()
            .try_fold(0u128, |degree, exponent| degree.checked_add(*exponent))
    }

    pub(crate) fn is_scalar(&self) -> bool {
        self.exponents.iter().all(|exponent| *exponent == 0)
    }

    fn label(&self) -> String {
        self.exponents
            .iter()
            .enumerate()
            .filter_map(|(index, exponent)| match exponent {
                0 => None,
                1 => Some(format!("z{index}")),
                exponent => Some(format!("z{index}↑{exponent}")),
            })
            .collect::<Vec<_>>()
            .join("⋅")
    }
}

/// A finite sparse sum of canonical PBW monomials.
///
/// Zero coefficients are never stored. The dimension is retained on the
/// element so context-free additive operations cannot silently mix exponent
/// vectors from different free modules.
#[derive(Clone, Debug, PartialEq)]
pub struct WeylElement<S: Scalar> {
    pub(crate) dim: usize,
    pub(crate) terms: BTreeMap<WeylMonomial, S>,
}

impl<S: Scalar> WeylElement<S> {
    /// The number of ordered generators in every PBW monomial.
    pub fn dim(&self) -> usize {
        self.dim
    }

    /// The canonical sparse term map. It is empty exactly when the element is
    /// zero, and every key has [`Self::dim`] exponents.
    pub fn terms(&self) -> &BTreeMap<WeylMonomial, S> {
        &self.terms
    }

    /// Whether this element is zero.
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// The canonical human-readable PBW representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

pub(crate) fn add_term<S: Scalar>(
    terms: &mut BTreeMap<WeylMonomial, S>,
    monomial: WeylMonomial,
    coefficient: S,
) {
    if coefficient.is_zero() {
        return;
    }
    let entry = terms.entry(monomial.clone()).or_insert_with(S::zero);
    *entry = entry.add(&coefficient);
    if entry.is_zero() {
        terms.remove(&monomial);
    }
}

impl<S: Scalar> fmt::Display for WeylElement<S> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.terms.is_empty() {
            return write!(formatter, "{}", S::zero());
        }
        let one = S::one();
        let neg_one = one.neg();
        let mut parts = Vec::with_capacity(self.terms.len());
        for (monomial, coefficient) in &self.terms {
            if monomial.is_scalar() {
                parts.push(coefficient.to_string());
                continue;
            }
            let label = monomial.label();
            if coefficient == &one {
                parts.push(label);
            } else if coefficient == &neg_one {
                parts.push(format!("-{label}"));
            } else {
                parts.push(crate::scalar::poly::attach_coeff(coefficient, &label));
            }
        }

        let mut output = String::new();
        for (index, part) in parts.iter().enumerate() {
            if let Some(magnitude) = part.strip_prefix('-') {
                if index == 0 {
                    output.push('-');
                } else {
                    output.push_str(" - ");
                }
                output.push_str(magnitude);
            } else {
                if index != 0 {
                    output.push_str(" + ");
                }
                output.push_str(part);
            }
        }
        formatter.write_str(&output)
    }
}

impl<S: Scalar> Add for WeylElement<S> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        assert_eq!(
            self.dim, rhs.dim,
            "cannot add Weyl elements with different generator dimensions"
        );
        let mut terms = self.terms;
        for (monomial, coefficient) in rhs.terms {
            add_term(&mut terms, monomial, coefficient);
        }
        Self {
            dim: self.dim,
            terms,
        }
    }
}

impl<S: Scalar> Neg for WeylElement<S> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            dim: self.dim,
            terms: self
                .terms
                .into_iter()
                .map(|(monomial, coefficient)| (monomial, coefficient.neg()))
                .filter(|(_, coefficient)| !coefficient.is_zero())
                .collect(),
        }
    }
}

impl<S: Scalar> Sub for WeylElement<S> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}
