//! Dense univariate polynomials `S[x]` over a [`Scalar`] base, low-degree-first.
//!
//! The crate's shared polynomial primitive. It backs two clients:
//!
//!   * [`Gauss`](crate::scalar::Gauss) — the rational function field `S(t)` stores
//!     `num/den` as a pair of `Poly`s.
//!   * the global **function field** `F_q(t)` and its place/Hilbert-symbol layer
//!     in [`forms::function_field`](crate::forms) — which additionally needs
//!     division, gcd, and modular powers (the residue quadratic character is
//!     Euler's criterion `u^{(|κ|−1)/2}` computed in `F_q[t]/(π)`).
//!     The crate-private finite-field factorization pipeline lives beside this
//!     arithmetic in `poly_factor` rather than under either forms client.
//!
//! Representation is **trimmed** (no trailing zero coefficients; the zero
//! polynomial is the empty vector), so `PartialEq` is structural and exact. The
//! division-flavoured methods (`divrem`, `rem`, `make_monic`, `gcd`, `*_mod`)
//! assume the base is a **field** — they invert the divisor's leading coefficient
//! and panic if it is not invertible. Both clients are fields, so this is the same
//! honesty as `Gauss`'s `inv = den/num`.

use crate::scalar::{Scalar, Valued};

/// A dense univariate polynomial over `S`, coefficients low-degree-first and
/// trimmed (leading coefficient nonzero; the zero polynomial is empty).
#[derive(Clone, PartialEq)]
pub struct Poly<S: Scalar> {
    coeffs: Vec<S>,
}

/// A divisor whose degree and leading-coefficient inverse have been computed
/// once. Modular exponentiation performs many reductions by the same
/// polynomial, so rebuilding that information inside every multiply is pure
/// overhead. Monic divisors need no inversion at all.
struct PreparedDivisor<'a, S: Scalar> {
    divisor: &'a Poly<S>,
    degree: usize,
    lead_inv: Option<S>,
    /// Nonzero terms below the leading coefficient when the divisor is sparse
    /// enough for indirect traversal to beat a dense coefficient scan.
    sparse_lower_indices: Option<Vec<usize>>,
}

impl<'a, S: Scalar> PreparedDivisor<'a, S> {
    fn new(divisor: &'a Poly<S>) -> Self {
        let degree = divisor
            .degree()
            .expect("polynomial division by the zero polynomial");
        let leading = divisor
            .leading()
            .expect("nonzero polynomial has a leading coefficient");
        let lead_inv = if leading == &S::one() {
            None
        } else {
            Some(
                leading
                    .inv()
                    .expect("a field's nonzero leading coefficient inverts"),
            )
        };
        let sparse_lower_indices = if S::REASSOCIATION_IS_EXACT {
            let nonzero = divisor.coeffs[..degree]
                .iter()
                .filter(|coefficient| !coefficient.is_zero())
                .count();
            (nonzero.saturating_mul(4) <= degree).then(|| {
                divisor.coeffs[..degree]
                    .iter()
                    .enumerate()
                    .filter_map(|(index, coefficient)| (!coefficient.is_zero()).then_some(index))
                    .collect()
            })
        } else {
            None
        };
        Self {
            divisor,
            degree,
            lead_inv,
            sparse_lower_indices,
        }
    }

    fn quotient_factor(&self, leading: &S) -> S {
        match &self.lead_inv {
            Some(inverse) => leading.mul(inverse),
            None => leading.clone(),
        }
    }

    fn subtract_shifted_divisor(&self, rem: &mut Vec<S>, shift: usize, factor: &S) {
        if let Some(indices) = &self.sparse_lower_indices {
            // The exact quotient factor cancels the leading term identically.
            // Remove it directly and touch only the stored nonzero lower terms.
            rem.pop();
            for &index in indices {
                let coefficient = &self.divisor.coeffs[index];
                rem[shift + index] = rem[shift + index].sub(&factor.mul(coefficient));
            }
            return;
        }
        for (index, coefficient) in self.divisor.coeffs.iter().enumerate() {
            rem[shift + index] = rem[shift + index].sub(&factor.mul(coefficient));
        }
    }

    fn divrem_coeffs(&self, mut rem: Vec<S>) -> (Poly<S>, Poly<S>) {
        let mut quot = vec![S::zero(); rem.len().saturating_sub(self.degree).max(1)];
        loop {
            rem = trim(rem);
            let rdeg = match rem.len().checked_sub(1) {
                Some(degree) if degree >= self.degree => degree,
                _ => break,
            };
            let shift = rdeg - self.degree;
            let factor = self.quotient_factor(&rem[rdeg]);
            quot[shift] = factor.clone();
            self.subtract_shifted_divisor(&mut rem, shift, &factor);
        }
        (Poly::new(quot), Poly::new(rem))
    }

    fn rem_coeffs(&self, mut rem: Vec<S>) -> Poly<S> {
        loop {
            rem = trim(rem);
            let rdeg = match rem.len().checked_sub(1) {
                Some(degree) if degree >= self.degree => degree,
                _ => break,
            };
            let shift = rdeg - self.degree;
            let factor = self.quotient_factor(&rem[rdeg]);
            self.subtract_shifted_divisor(&mut rem, shift, &factor);
        }
        Poly::new(rem)
    }

    fn mul_mod(&self, left: &Poly<S>, right: &Poly<S>) -> Poly<S> {
        self.rem_coeffs(left.mul(right).coeffs)
    }

    /// In characteristic two the cross terms in a square vanish. Exact
    /// backends can therefore square in O(n) coefficient products before the
    /// usual reduction instead of performing a dense O(n^2) multiplication.
    fn square_mod_char_two(&self, value: &Poly<S>) -> Poly<S> {
        if value.is_zero() {
            return Poly::zero();
        }
        let mut squared = vec![S::zero(); 2 * value.coeffs.len() - 1];
        for (index, coefficient) in value.coeffs.iter().enumerate() {
            if !coefficient.is_zero() {
                squared[2 * index] = coefficient.mul(coefficient);
            }
        }
        self.rem_coeffs(squared)
    }
}

/// Whether a rendered coefficient can be attached to a monomial without
/// parentheses. A coefficient attaches bare
/// iff it contains no spaces and no operator character (`⋅ ∧ ↑ / + -`) outside
/// balanced parentheses; otherwise it is wrapped so `coeff⋅t↑i` stays
/// unambiguous (`(x + 1)⋅t↑2`, but `x⋅t↑2`).
pub(crate) fn atomic(s: &str) -> bool {
    let mut depth: i32 = 0;
    for ch in s.chars() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ' ' | '⋅' | '∧' | '↑' | '/' | '+' | '-' if depth == 0 => return false,
            _ => {}
        }
    }
    true
}

/// Attach a scalar coefficient to a label as `coeff⋅label`, parenthesizing the
/// coefficient only when its rendering is non-atomic. A single leading `-`
/// is a unary sign, not an internal operator, so it is checked separately and
/// carried through bare (`-2⋅e0∧e1`); the Multivector join rule then lifts it to
/// a ` - ` separator. Only a `-`/operator/space *inside* the magnitude forces
/// parens (`(x + 1)⋅e0∧e1`).
pub(crate) fn attach_coeff<S: Scalar>(c: &S, label: &str) -> String {
    let cs = c.to_string();
    let (sign, mag) = match cs.strip_prefix('-') {
        Some(rest) => ("-", rest),
        None => ("", cs.as_str()),
    };
    if atomic(mag) {
        format!("{sign}{mag}⋅{label}")
    } else {
        format!("({cs})⋅{label}")
    }
}

impl<S: Scalar> std::fmt::Display for Poly<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.coeffs.is_empty() {
            return write!(f, "0");
        }
        let one = S::one();
        let neg_one = one.neg();
        let mut parts = Vec::new();
        for (i, c) in self.coeffs.iter().enumerate().rev() {
            if c.is_zero() {
                continue;
            }
            parts.push(match i {
                0 => format!("{c}"),
                _ => {
                    let label = if i == 1 {
                        "t".to_string()
                    } else {
                        format!("t↑{i}")
                    };
                    if c == &one {
                        label
                    } else if c == &neg_one {
                        format!("-{label}")
                    } else {
                        attach_coeff(c, &label)
                    }
                }
            });
        }
        let mut out = parts.remove(0);
        for term in parts {
            if let Some(magnitude) = term.strip_prefix('-') {
                out.push_str(" - ");
                out.push_str(magnitude);
            } else {
                out.push_str(" + ");
                out.push_str(&term);
            }
        }
        write!(f, "{out}")
    }
}

impl<S: Scalar> std::fmt::Debug for Poly<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

/// Drop trailing zero coefficients so the leading term is nonzero.
fn trim<S: Scalar>(mut p: Vec<S>) -> Vec<S> {
    while p.last().map(|c| c.is_zero()).unwrap_or(false) {
        p.pop();
    }
    p
}

/// Dense balanced products cross over to Karatsuba well above this recursive
/// leaf size. Sparse and strongly unbalanced operands retain the schoolbook
/// path, whose zero skipping is substantially better for those shapes.
const KARATSUBA_THRESHOLD: usize = 32;

fn schoolbook_mul_coeffs<S: Scalar>(left: &[S], right: &[S]) -> Vec<S> {
    if left.is_empty() || right.is_empty() {
        return Vec::new();
    }
    let mut out = vec![S::zero(); left.len() + right.len() - 1];
    for (i, x) in left.iter().enumerate() {
        if x.is_zero() {
            continue;
        }
        for (j, y) in right.iter().enumerate() {
            if !y.is_zero() {
                out[i + j] = out[i + j].add(&x.mul(y));
            }
        }
    }
    out
}

fn add_coeff_slices<S: Scalar>(left: &[S], right: &[S]) -> Vec<S> {
    let overlap = left.len().min(right.len());
    let mut out = Vec::with_capacity(left.len().max(right.len()));
    out.extend(
        left[..overlap]
            .iter()
            .zip(&right[..overlap])
            .map(|(x, y)| x.add(y)),
    );
    if left.len() > overlap {
        out.extend_from_slice(&left[overlap..]);
    } else {
        out.extend_from_slice(&right[overlap..]);
    }
    out
}

fn accumulate_shifted<S: Scalar>(out: &mut [S], values: &[S], shift: usize, subtract: bool) {
    for (index, value) in values.iter().enumerate() {
        let value = if subtract { value.neg() } else { value.clone() };
        out[index + shift] = out[index + shift].add(&value);
    }
}

fn karatsuba_mul_coeffs<S: Scalar>(left: &[S], right: &[S]) -> Vec<S> {
    if left.is_empty() || right.is_empty() {
        return Vec::new();
    }
    let min_len = left.len().min(right.len());
    let max_len = left.len().max(right.len());
    if min_len <= KARATSUBA_THRESHOLD || max_len >= min_len.saturating_mul(2) {
        return schoolbook_mul_coeffs(left, right);
    }

    let split = max_len / 2;
    let (left_low, left_high) = left.split_at(left.len().min(split));
    let (right_low, right_high) = right.split_at(right.len().min(split));
    let low_product = karatsuba_mul_coeffs(left_low, right_low);
    let high_product = karatsuba_mul_coeffs(left_high, right_high);
    let left_sum = add_coeff_slices(left_low, left_high);
    let right_sum = add_coeff_slices(right_low, right_high);
    let sum_product = karatsuba_mul_coeffs(&left_sum, &right_sum);

    let mut out = vec![S::zero(); left.len() + right.len() - 1];
    accumulate_shifted(&mut out, &low_product, 0, false);
    accumulate_shifted(&mut out, &sum_product, split, false);
    accumulate_shifted(&mut out, &low_product, split, true);
    accumulate_shifted(&mut out, &high_product, split, true);
    accumulate_shifted(&mut out, &high_product, 2 * split, false);
    out
}

fn is_dense<S: Scalar>(coefficients: &[S]) -> bool {
    let nonzero = coefficients
        .iter()
        .filter(|coefficient| !coefficient.is_zero())
        .count();
    nonzero >= coefficients.len() - coefficients.len() / 4
}

fn should_use_karatsuba<S: Scalar>(left: &[S], right: &[S]) -> bool {
    let min_len = left.len().min(right.len());
    let max_len = left.len().max(right.len());
    S::REASSOCIATION_IS_EXACT
        && min_len > KARATSUBA_THRESHOLD
        && max_len < min_len.saturating_mul(2)
        && is_dense(left)
        && is_dense(right)
}

impl<S: Scalar> Poly<S> {
    /// Build a polynomial from low-degree-first coefficients (trimmed).
    pub fn new(coeffs: Vec<S>) -> Self {
        Poly {
            coeffs: trim(coeffs),
        }
    }

    /// The zero polynomial.
    pub fn zero() -> Self {
        Poly { coeffs: Vec::new() }
    }

    /// The constant polynomial `1`.
    pub fn one() -> Self {
        Poly::constant(S::one())
    }

    /// The constant polynomial `s`.
    pub fn constant(s: S) -> Self {
        Poly::new(vec![s])
    }

    /// The indeterminate `t`.
    pub fn t() -> Self {
        Poly::new(vec![S::zero(), S::one()])
    }

    /// `coeff · x^deg`.
    pub fn monomial(deg: usize, coeff: S) -> Self {
        let mut c = vec![S::zero(); deg];
        c.push(coeff);
        Poly::new(c)
    }

    /// The coefficient slice (low-degree-first; empty iff zero).
    pub fn coeffs(&self) -> &[S] {
        &self.coeffs
    }

    /// Whether this is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// The degree, or `None` for the zero polynomial.
    pub fn degree(&self) -> Option<usize> {
        self.coeffs.len().checked_sub(1)
    }

    /// The leading coefficient, or `None` for the zero polynomial.
    pub fn leading(&self) -> Option<&S> {
        self.coeffs.last()
    }

    /// The coefficient of `x^i` (zero past the degree).
    pub fn coeff(&self, i: usize) -> S {
        self.coeffs.get(i).cloned().unwrap_or_else(S::zero)
    }

    /// Coefficientwise polynomial addition.
    pub fn add(&self, rhs: &Self) -> Self {
        let n = self.coeffs.len().max(rhs.coeffs.len());
        let mut out = Vec::with_capacity(n);
        let overlap = self.coeffs.len().min(rhs.coeffs.len());
        for (left, right) in self.coeffs[..overlap].iter().zip(&rhs.coeffs[..overlap]) {
            out.push(left.add(right));
        }
        if self.coeffs.len() > overlap {
            out.extend_from_slice(&self.coeffs[overlap..]);
        } else {
            out.extend_from_slice(&rhs.coeffs[overlap..]);
        }
        Poly::new(out)
    }

    /// Coefficientwise additive inverse.
    pub fn neg(&self) -> Self {
        Poly {
            coeffs: self.coeffs.iter().map(|c| c.neg()).collect(),
        }
    }

    /// Polynomial subtraction.
    pub fn sub(&self, rhs: &Self) -> Self {
        let n = self.coeffs.len().max(rhs.coeffs.len());
        let mut out = Vec::with_capacity(n);
        let overlap = self.coeffs.len().min(rhs.coeffs.len());
        for (left, right) in self.coeffs[..overlap].iter().zip(&rhs.coeffs[..overlap]) {
            out.push(left.sub(right));
        }
        if self.coeffs.len() > overlap {
            out.extend_from_slice(&self.coeffs[overlap..]);
        } else {
            out.extend(rhs.coeffs[overlap..].iter().map(Scalar::neg));
        }
        Poly::new(out)
    }

    /// Polynomial multiplication.
    pub fn mul(&self, rhs: &Self) -> Self {
        if self.is_zero() || rhs.is_zero() {
            return Poly::zero();
        }
        let coefficients = if should_use_karatsuba(&self.coeffs, &rhs.coeffs) {
            karatsuba_mul_coeffs(&self.coeffs, &rhs.coeffs)
        } else {
            schoolbook_mul_coeffs(&self.coeffs, &rhs.coeffs)
        };
        Poly::new(coefficients)
    }

    /// Multiply every coefficient by `s`.
    pub fn scale(&self, s: &S) -> Self {
        Poly::new(self.coeffs.iter().map(|c| c.mul(s)).collect())
    }

    /// Evaluate at `x` by Horner's rule.
    pub fn eval(&self, x: &S) -> S {
        let mut acc = S::zero();
        for c in self.coeffs.iter().rev() {
            acc = acc.mul(x).add(c);
        }
        acc
    }

    /// Substitute `t := inner` by Horner's rule over polynomial arithmetic.
    pub fn compose(&self, inner: &Self) -> Self {
        let mut acc = Poly::zero();
        for c in self.coeffs.iter().rev() {
            acc = acc.mul(inner).add(&Poly::constant(c.clone()));
        }
        acc
    }

    /// Scale to a monic polynomial (divide through by the leading coefficient).
    /// Panics on the zero polynomial; requires the base to be a field.
    pub fn make_monic(&self) -> Self {
        let lead = self.leading().expect("make_monic of the zero polynomial");
        if lead == &S::one() {
            return self.clone();
        }
        let inv = lead
            .inv()
            .expect("a field's nonzero leading coefficient inverts");
        self.scale(&inv)
    }

    /// Euclidean division `self = q·divisor + r` with `deg r < deg divisor`,
    /// returning `(q, r)`. Requires `divisor` nonzero over a field.
    pub fn divrem(&self, divisor: &Self) -> (Self, Self) {
        PreparedDivisor::new(divisor).divrem_coeffs(self.coeffs.clone())
    }

    /// The remainder `self mod divisor`.
    pub fn rem(&self, divisor: &Self) -> Self {
        PreparedDivisor::new(divisor).rem_coeffs(self.coeffs.clone())
    }

    /// Whether `divisor` divides `self` exactly.
    pub fn divides(&self, multiple: &Self) -> bool {
        !self.is_zero() && multiple.rem(self).is_zero()
    }

    /// The monic gcd (the zero polynomial's gcd partner is returned monic).
    pub fn gcd(&self, other: &Self) -> Self {
        let mut a = self.clone();
        let mut b = other.clone();
        while !b.is_zero() {
            let r = a.rem(&b);
            a = b;
            b = r;
        }
        if a.is_zero() {
            a
        } else {
            a.make_monic()
        }
    }

    /// `self · other mod modulus`.
    pub fn mul_mod(&self, other: &Self, modulus: &Self) -> Self {
        PreparedDivisor::new(modulus).mul_mod(self, other)
    }

    /// `self^e mod modulus` by square-and-multiply.
    pub fn pow_mod(&self, mut e: u128, modulus: &Self) -> Self {
        let prepared = PreparedDivisor::new(modulus);
        let mut acc = prepared.rem_coeffs(Poly::one().coeffs);
        let mut base = prepared.rem_coeffs(self.coeffs.clone());
        let sparse_char_two_square = S::REASSOCIATION_IS_EXACT && S::characteristic() == 2;
        while e > 0 {
            if e & 1 == 1 {
                acc = prepared.mul_mod(&acc, &base);
            }
            e >>= 1;
            if e > 0 {
                base = if sparse_char_two_square {
                    prepared.square_mod_char_two(&base)
                } else {
                    prepared.mul_mod(&base, &base)
                };
            }
        }
        acc
    }
}

/// `S[t]` is itself a commutative ring — the **ring of integers** of the rational
/// function field [`RationalFunction`](crate::scalar::RationalFunction)`<S> = S(t)`.
/// Its units are the nonzero constants (so `inv` is partial), exactly as `ℤ` sits
/// inside `ℚ`. The trait methods delegate to the inherent ones (inherent shadows
/// trait at the receiver, so this delegates rather than recurses).
impl<S: Scalar> Scalar for Poly<S> {
    fn zero() -> Self {
        Self::constant(S::zero()) // trims to the empty polynomial
    }
    fn one() -> Self {
        Self::constant(S::one())
    }
    fn add(&self, rhs: &Self) -> Self {
        self.add(rhs)
    }
    fn neg(&self) -> Self {
        self.neg()
    }
    fn mul(&self, rhs: &Self) -> Self {
        self.mul(rhs)
    }
    fn characteristic() -> u128 {
        S::characteristic()
    }
    fn inv(&self) -> Option<Self> {
        // units of S[t] are the nonzero constants.
        match self.degree() {
            Some(0) => self.coeff(0).inv().map(Self::constant),
            _ => None,
        }
    }
    fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }
}

impl<S: Valued> Poly<S> {
    /// The minimum coefficient valuation (the Gauss valuation of the polynomial),
    /// or `None` for the zero polynomial.
    pub fn min_coeff_valuation(&self) -> Option<i128> {
        self.coeffs.iter().filter_map(|c| c.valuation()).min()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{Fp, Rational};

    type P5 = Poly<Fp<5>>;

    fn p(coeffs: &[i128]) -> P5 {
        Poly::new(coeffs.iter().map(|&n| Fp::<5>::from_int(n)).collect())
    }

    #[test]
    fn arithmetic_basics() {
        // (1 + x)(1 + x) = 1 + 2x + x²
        let one_plus_x = p(&[1, 1]);
        assert_eq!(one_plus_x.mul(&one_plus_x), p(&[1, 2, 1]));
        // (1 + x) + (4 + 4x) = 5 + 5x ≡ 0 in F_5
        assert_eq!(p(&[1, 1]).add(&p(&[4, 4])), P5::zero());
        assert_eq!(p(&[1, 1]).neg(), p(&[4, 4]));
        assert_eq!(P5::t().eval(&Fp::<5>::from_int(3)), Fp::<5>::from_int(3));
        assert_eq!(
            p(&[1, 1, 1]).eval(&Fp::<5>::from_int(2)),
            Fp::<5>::from_int(7)
        ); // 1+2+4=7
    }

    #[test]
    fn karatsuba_matches_schoolbook_on_dense_uneven_inputs() {
        type P3 = Poly<Fp<3>>;
        fn dense(len: usize, offset: usize) -> P3 {
            Poly::new(
                (0..len)
                    .map(|index| Fp::<3>::from_u128(((index + offset) % 2 + 1) as u128))
                    .collect(),
            )
        }

        for &(left_len, right_len) in &[
            (31, 35),
            (32, 64),
            (33, 35),
            (63, 69),
            (127, 121),
            (256, 257),
            (512, 512),
        ] {
            let left = dense(left_len, 0);
            let right = dense(right_len, 1);
            let expected = Poly::new(schoolbook_mul_coeffs(left.coeffs(), right.coeffs()));
            assert_eq!(left.mul(&right), expected, "{left_len} by {right_len}");
        }
    }

    #[test]
    fn sparse_large_products_stay_on_schoolbook_path() {
        let sparse = Poly::new(
            (0usize..512)
                .map(|index| {
                    if index.is_multiple_of(64) {
                        Fp::<5>::one()
                    } else {
                        Fp::<5>::zero()
                    }
                })
                .collect::<Vec<_>>(),
        );
        let dense = Poly::new(vec![Fp::<5>::one(); 512]);
        assert!(!should_use_karatsuba(sparse.coeffs(), dense.coeffs()));
        assert_eq!(
            sparse.mul(&dense),
            Poly::new(schoolbook_mul_coeffs(sparse.coeffs(), dense.coeffs()))
        );
    }

    #[test]
    fn karatsuba_requires_exact_reassociation_contract() {
        let finite_field = vec![Fp::<5>::one(); 64];
        assert!(should_use_karatsuba(&finite_field, &finite_field));

        // Rational arithmetic is mathematically exact but fixed-width: changing
        // the grouping can change which intermediate overflows, so it retains
        // the established schoolbook evaluation order.
        let fixed_width = vec![Rational::one(); 64];
        assert!(!should_use_karatsuba(&fixed_width, &fixed_width));
    }

    #[test]
    fn euclidean_division() {
        // x² − 1 = (x − 1)(x + 1) over F_5  (−1 ≡ 4)
        let x2m1 = p(&[4, 0, 1]);
        let xm1 = p(&[4, 1]); // x − 1
        let (q, r) = x2m1.divrem(&xm1);
        assert_eq!(q, p(&[1, 1])); // x + 1
        assert!(r.is_zero());
        assert!(xm1.divides(&x2m1));
        // a remainder that is genuinely nonzero
        let (_, r2) = p(&[1, 0, 1]).divrem(&xm1); // x² + 1 at x=1 → 2
        assert_eq!(r2, p(&[2]));
    }

    #[test]
    fn sparse_nonmonic_divisor_reconstructs_dividend_exactly() {
        let mut divisor_coefficients = vec![Fp::<5>::zero(); 33];
        divisor_coefficients[0] = Fp::<5>::from_int(2);
        divisor_coefficients[7] = Fp::<5>::one();
        divisor_coefficients[32] = Fp::<5>::from_int(3);
        let divisor = P5::new(divisor_coefficients);
        let quotient = p(&[1, 4, 2, 3]);
        let remainder = p(&[3, 0, 1, 4, 0, 2]);
        let dividend = quotient.mul(&divisor).add(&remainder);

        let (actual_quotient, actual_remainder) = dividend.divrem(&divisor);
        assert_eq!(actual_quotient, quotient);
        assert_eq!(actual_remainder, remainder);
        assert_eq!(dividend.rem(&divisor), remainder);
        assert_eq!(
            actual_quotient.mul(&divisor).add(&actual_remainder),
            dividend
        );
    }

    #[test]
    fn compose_substitutes_polynomials_by_horner() {
        let f = p(&[1, 0, 1]); // 1 + t²
        let g = p(&[1, 1]); // 1 + t
        assert_eq!(f.compose(&g), p(&[2, 2, 1])); // 1 + (1+t)²
        assert_eq!(P5::t().compose(&g), g);
        assert_eq!(f.compose(&P5::zero()), p(&[1]));
    }

    #[test]
    fn gcd_and_monic() {
        // gcd(x² − 1, x² + 2x + 1) = x + 1 (monic)
        let g = p(&[4, 0, 1]).gcd(&p(&[1, 2, 1]));
        assert_eq!(g, p(&[1, 1]));
        // make_monic divides through by the leading coeff: 2x + 2 → x + 1
        assert_eq!(p(&[2, 2]).make_monic(), p(&[1, 1]));
    }

    #[test]
    fn display_is_canonical_grundy() {
        use crate::scalar::Fpn;
        // Descending powers and atomic coefficients share the monomial family.
        assert_eq!(p(&[1, 2]).to_string(), "2⋅t + 1");
        assert_eq!(p(&[0, 0, 3]).to_string(), "3⋅t↑2");
        assert_eq!(P5::zero().to_string(), "0");
        // Non-atomic coefficients (an F_8 element `x + 1`) parenthesize.
        type Q = Poly<Fpn<2, 3>>;
        let xp1 = Fpn::<2, 3>::from_coeffs(&[1, 1]); // x + 1 (non-atomic)
        let x = Fpn::<2, 3>::from_coeffs(&[0, 1]); // x (atomic)
        let one = Fpn::<2, 3>::one();
        // (x + 1)⋅t↑2 + x⋅t + 1
        let poly = Q::new(vec![one, x, xp1]);
        assert_eq!(poly.to_string(), "(x + 1)⋅t↑2 + x⋅t + 1");
    }

    #[test]
    fn atomicity_rule() {
        assert!(atomic("42"));
        assert!(atomic("*5"));
        assert!(atomic("*ω"));
        assert!(atomic("x"));
        assert!(atomic("*(ω⋅7)")); // operators only inside balanced parens
        assert!(!atomic("x + 1"));
        assert!(!atomic("ω↑-1"));
        assert!(!atomic("3⋅x")); // bare `⋅`
    }

    #[test]
    fn modular_powers_for_eulers_criterion() {
        // In F_5[x]/(x² + 2) (x² ≡ −2 ≡ 3), the residue field is F_25.
        let modulus = p(&[2, 0, 1]); // x² + 2, irreducible over F_5 (−2=3 is a nonsquare)
                                     // x^(25−1) ≡ 1 (Fermat in F_25*), and x is a nonsquare ⇒ x^((25−1)/2) ≡ −1.
        assert_eq!(P5::t().pow_mod(24, &modulus), P5::one());
        assert_eq!(P5::t().pow_mod(12, &modulus), p(&[4])); // −1 ≡ 4
    }

    #[test]
    fn characteristic_two_sparse_squaring_matches_generic_square_and_multiply() {
        type P2 = Poly<Fp<2>>;
        let polynomial = P2::new(
            (0..32)
                .map(|index| Fp::<2>::from_u128(u128::from(index % 3 != 0)))
                .collect(),
        );
        let modulus = P2::new(
            (0..=32)
                .map(|index| Fp::<2>::from_u128(u128::from(matches!(index, 0 | 1 | 7 | 32))))
                .collect(),
        );
        let mut exponent = 257u128;
        let mut expected = P2::one().rem(&modulus);
        let mut base = polynomial.rem(&modulus);
        while exponent > 0 {
            if exponent & 1 == 1 {
                expected = expected.mul_mod(&base, &modulus);
            }
            exponent >>= 1;
            if exponent > 0 {
                base = base.mul_mod(&base, &modulus);
            }
        }
        assert_eq!(polynomial.pow_mod(257, &modulus), expected);
    }
}
