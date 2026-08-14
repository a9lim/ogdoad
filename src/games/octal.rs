//! Finite octal games and checked normal-play periodicity certificates.
//!
//! [`octal_moves`] is the shared take-and-break move generator. A
//! [`GuySmithWitness`] becomes a sealed [`GuySmithCertificate`] only after this
//! module recomputes its finite Grundy prefix and checks the full Guy--Smith
//! window. The standard theorem then extends that checked equality to every
//! later heap. A certificate proves the supplied eventual period; it neither
//! discovers nor claims a minimal period, and it says nothing about misere
//! quotients. The finite implication used here is the Guy--Smith periodicity
//! theorem as stated in Aaron N. Siegel, *Games of No Chance 5*, Theorem 2.4.

use crate::games::mex;
use std::fmt;

/// Canonical finite octal code, with each digit checked and trailing zero digits
/// removed.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OctalCode {
    digits: Vec<u8>,
}

/// Invalid finite octal-code input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OctalCodeError {
    /// Octal digits are exactly `0..=7`.
    InvalidDigit {
        /// Zero-based digit index.
        index: usize,
        /// Supplied value.
        value: u128,
    },
}

impl fmt::Display for OctalCodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidDigit { index, value } => {
                write!(f, "octal digit {index} has value {value}, outside 0..=7")
            }
        }
    }
}

impl std::error::Error for OctalCodeError {}

impl OctalCode {
    /// Validate and canonicalize a finite code `0.d_1...d_k`.
    pub fn try_new(raw: &[u128]) -> Result<Self, OctalCodeError> {
        let mut digits = Vec::with_capacity(raw.len());
        for (index, &value) in raw.iter().enumerate() {
            let digit = u8::try_from(value)
                .ok()
                .filter(|&digit| digit <= 7)
                .ok_or(OctalCodeError::InvalidDigit { index, value })?;
            digits.push(digit);
        }
        while digits.last() == Some(&0) {
            digits.pop();
        }
        Ok(Self { digits })
    }

    /// Canonical digits `d_1,...,d_k` without trailing zeros.
    pub fn digits(&self) -> &[u8] {
        &self.digits
    }

    /// One-based index of the last nonzero digit, or `None` for the zero code.
    pub fn last_nonzero_digit(&self) -> Option<usize> {
        (!self.digits.is_empty()).then_some(self.digits.len())
    }
}

/// Moves of an octal game `0.d_1d_2...` (`code[k-1] = d_k`) on a heap multiset.
/// Removing `k` tokens may leave zero, one, or two nonempty heaps according to
/// bits `1`, `2`, and `4` of `d_k`. Values above seven retain the historical
/// low-three-bit behavior; checked new APIs use [`OctalCode`].
pub fn octal_moves(code: &[u128], pos: &[u128]) -> Vec<Vec<u128>> {
    let mut out = Vec::new();
    for idx in 0..pos.len() {
        let n = pos[idx];
        let base: Vec<u128> = pos
            .iter()
            .enumerate()
            .filter(|&(i, _)| i != idx)
            .map(|(_, &heap)| heap)
            .collect();
        for removed in 1..=n {
            let digit = usize::try_from(removed - 1)
                .ok()
                .and_then(|index| code.get(index))
                .copied()
                .unwrap_or(0);
            let remainder = n - removed;
            if remainder == 0 {
                if digit & 1 != 0 {
                    let mut next = base.clone();
                    next.sort_unstable();
                    out.push(next);
                }
            } else {
                if digit & 2 != 0 {
                    let mut next = base.clone();
                    next.push(remainder);
                    next.sort_unstable();
                    out.push(next);
                }
                if digit & 4 != 0 {
                    for left in 1..=remainder / 2 {
                        let mut next = base.clone();
                        next.push(left);
                        next.push(remainder - left);
                        next.sort_unstable();
                        out.push(next);
                    }
                }
            }
        }
    }
    out
}

/// A finite candidate prefix and proposed eventual period.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuySmithWitness {
    preperiod: u128,
    period: u128,
    nim_values: Vec<u128>,
}

impl GuySmithWitness {
    /// Package a candidate finite prefix. Verification never trusts these values:
    /// it recomputes the exact octal recurrence entry by entry.
    pub fn new(preperiod: u128, period: u128, nim_values: Vec<u128>) -> Self {
        Self {
            preperiod,
            period,
            nim_values,
        }
    }

    /// Proposed preperiod.
    pub fn preperiod(&self) -> u128 {
        self.preperiod
    }

    /// Proposed period.
    pub fn period(&self) -> u128 {
        self.period
    }

    /// Candidate finite Grundy prefix, beginning with the empty heap at index 0.
    pub fn nim_values(&self) -> &[u128] {
        &self.nim_values
    }

    /// Check the recurrence and full Guy--Smith equality window, returning an
    /// unforgeable periodic certificate on success.
    pub fn verify(
        self,
        code: OctalCode,
        term_budget: usize,
    ) -> Result<GuySmithCertificate, GuySmithError> {
        let bounds = proof_bounds(&code, self.preperiod, self.period, term_budget)?;
        if self.nim_values.len() < bounds.required_terms {
            return Err(GuySmithError::WitnessTooShort {
                required: bounds.required_terms,
                actual: self.nim_values.len(),
            });
        }
        if self.nim_values[0] != 0 {
            return Err(GuySmithError::RecurrenceMismatch {
                heap: 0,
                expected: 0,
                found: self.nim_values[0],
            });
        }
        for heap in 1..bounds.required_terms {
            let expected = single_heap_grundy(&code, heap, &self.nim_values[..heap]);
            let found = self.nim_values[heap];
            if found != expected {
                return Err(GuySmithError::RecurrenceMismatch {
                    heap: heap as u128,
                    expected,
                    found,
                });
            }
        }
        for heap in bounds.preperiod..bounds.window_end {
            let shifted = heap + bounds.period;
            if self.nim_values[heap] != self.nim_values[shifted] {
                return Err(GuySmithError::PeriodMismatch {
                    heap: heap as u128,
                    shifted: shifted as u128,
                    value: self.nim_values[heap],
                    shifted_value: self.nim_values[shifted],
                });
            }
        }
        let mut nim_values = self.nim_values;
        nim_values.truncate(bounds.required_terms);
        Ok(GuySmithCertificate {
            code,
            preperiod: self.preperiod,
            period: self.period,
            nim_values,
            window_end: bounds.window_end as u128,
        })
    }
}

/// A checked finite witness to eventual normal-play octal periodicity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuySmithCertificate {
    code: OctalCode,
    preperiod: u128,
    period: u128,
    nim_values: Vec<u128>,
    window_end: u128,
}

impl GuySmithCertificate {
    /// Compute the exact required prefix and verify the proposed period in one
    /// call. The term budget is checked before allocation or recurrence work.
    pub fn compute(
        code: OctalCode,
        preperiod: u128,
        period: u128,
        term_budget: usize,
    ) -> Result<Self, GuySmithError> {
        let bounds = proof_bounds(&code, preperiod, period, term_budget)?;
        let mut nim_values = Vec::with_capacity(bounds.required_terms);
        nim_values.push(0);
        for heap in 1..bounds.required_terms {
            let value = single_heap_grundy(&code, heap, &nim_values);
            nim_values.push(value);
        }
        GuySmithWitness::new(preperiod, period, nim_values).verify(code, term_budget)
    }

    /// The checked finite octal code.
    pub fn code(&self) -> &OctalCode {
        &self.code
    }

    /// Certified eventual-period start. It is not claimed minimal.
    pub fn preperiod(&self) -> u128 {
        self.preperiod
    }

    /// Certified eventual period. It is not claimed minimal.
    pub fn period(&self) -> u128 {
        self.period
    }

    /// Half-open Guy--Smith equality window `[preperiod, window_end)`.
    pub fn proof_window(&self) -> (u128, u128) {
        (self.preperiod, self.window_end)
    }

    /// Exact finite prefix retained by the certificate.
    pub fn checked_nim_values(&self) -> &[u128] {
        &self.nim_values
    }

    /// Certified Grundy value of a single heap of arbitrary size.
    pub fn heap_grundy(&self, heap: u128) -> u128 {
        if let Ok(index) = usize::try_from(heap) {
            if let Some(&value) = self.nim_values.get(index) {
                return value;
            }
        }
        let reduced = self.preperiod + (heap - self.preperiod) % self.period;
        self.nim_values[usize::try_from(reduced)
            .expect("the reduced certified index lies inside the retained finite prefix")]
    }

    /// Grundy value of a disjunctive sum of certified heaps.
    pub fn position_grundy(&self, heaps: &[u128]) -> u128 {
        heaps
            .iter()
            .fold(0, |value, &heap| value ^ self.heap_grundy(heap))
    }

    /// Whether a heap multiset is a normal-play `P`-position.
    pub fn is_p_position(&self, heaps: &[u128]) -> bool {
        self.position_grundy(heaps) == 0
    }
}

/// Rejection reason for an alleged Guy--Smith certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GuySmithError {
    /// The theorem requires a nonzero finite code with a last nonzero digit.
    ZeroCode,
    /// This API uses the standard positive-preperiod theorem statement.
    ZeroPreperiod,
    /// A period must be positive.
    ZeroPeriod,
    /// The theorem window overflowed `u128` arithmetic.
    ArithmeticOverflow,
    /// The finite theorem window does not fit the platform's indexing space.
    IndexTooLarge {
        /// Mathematical number of required prefix terms.
        required_terms: u128,
    },
    /// The required exact prefix exceeds the caller's budget.
    TermBudgetExceeded {
        /// Required prefix length.
        required: usize,
        /// Caller-supplied term budget.
        budget: usize,
    },
    /// A supplied witness omits part of the required exact prefix.
    WitnessTooShort {
        /// Required prefix length.
        required: usize,
        /// Supplied prefix length.
        actual: usize,
    },
    /// A claimed entry disagrees with the exact octal mex recurrence.
    RecurrenceMismatch {
        /// Heap index of the mismatch.
        heap: u128,
        /// Recomputed exact Grundy value.
        expected: u128,
        /// Value carried by the witness.
        found: u128,
    },
    /// The exact sequence fails the proposed equality inside the theorem window.
    PeriodMismatch {
        /// Unshifted heap index.
        heap: u128,
        /// Heap index shifted by the proposed period.
        shifted: u128,
        /// Grundy value at `heap`.
        value: u128,
        /// Grundy value at `shifted`.
        shifted_value: u128,
    },
}

impl fmt::Display for GuySmithError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroCode => f.write_str("Guy--Smith certification needs a nonzero finite code"),
            Self::ZeroPreperiod => f.write_str("Guy--Smith preperiod must be positive"),
            Self::ZeroPeriod => f.write_str("Guy--Smith period must be positive"),
            Self::ArithmeticOverflow => {
                f.write_str("Guy--Smith proof window overflows u128 arithmetic")
            }
            Self::IndexTooLarge { required_terms } => write!(
                f,
                "Guy--Smith proof needs {required_terms} indexed terms, beyond this platform"
            ),
            Self::TermBudgetExceeded { required, budget } => write!(
                f,
                "Guy--Smith proof needs {required} terms, exceeding budget {budget}"
            ),
            Self::WitnessTooShort { required, actual } => write!(
                f,
                "Guy--Smith witness has {actual} terms but needs {required}"
            ),
            Self::RecurrenceMismatch {
                heap,
                expected,
                found,
            } => write!(
                f,
                "octal Grundy recurrence mismatch at heap {heap}: expected {expected}, found {found}"
            ),
            Self::PeriodMismatch {
                heap,
                shifted,
                value,
                shifted_value,
            } => write!(
                f,
                "Guy--Smith equality fails: G({heap})={value}, G({shifted})={shifted_value}"
            ),
        }
    }
}

impl std::error::Error for GuySmithError {}

struct ProofBounds {
    preperiod: usize,
    period: usize,
    window_end: usize,
    required_terms: usize,
}

fn proof_bounds(
    code: &OctalCode,
    preperiod: u128,
    period: u128,
    term_budget: usize,
) -> Result<ProofBounds, GuySmithError> {
    let last_digit = code.last_nonzero_digit().ok_or(GuySmithError::ZeroCode)? as u128;
    if preperiod == 0 {
        return Err(GuySmithError::ZeroPreperiod);
    }
    if period == 0 {
        return Err(GuySmithError::ZeroPeriod);
    }
    let window_end = preperiod
        .checked_mul(2)
        .and_then(|value| value.checked_add(period))
        .and_then(|value| value.checked_add(last_digit))
        .ok_or(GuySmithError::ArithmeticOverflow)?;
    let required_terms = window_end
        .checked_add(period)
        .ok_or(GuySmithError::ArithmeticOverflow)?;
    let required_terms_usize = usize::try_from(required_terms)
        .map_err(|_| GuySmithError::IndexTooLarge { required_terms })?;
    if required_terms_usize > term_budget {
        return Err(GuySmithError::TermBudgetExceeded {
            required: required_terms_usize,
            budget: term_budget,
        });
    }
    Ok(ProofBounds {
        preperiod: usize::try_from(preperiod).expect("required terms already fit usize"),
        period: usize::try_from(period).expect("required terms already fit usize"),
        window_end: usize::try_from(window_end).expect("required terms already fit usize"),
        required_terms: required_terms_usize,
    })
}

fn single_heap_grundy(code: &OctalCode, heap: usize, earlier: &[u128]) -> u128 {
    let mut options = Vec::new();
    let max_removed = heap.min(code.digits.len());
    for removed in 1..=max_removed {
        let digit = code.digits[removed - 1];
        let remainder = heap - removed;
        if remainder == 0 {
            if digit & 1 != 0 {
                options.push(0);
            }
            continue;
        }
        if digit & 2 != 0 {
            options.push(earlier[remainder]);
        }
        if digit & 4 != 0 {
            for left in 1..=remainder / 2 {
                options.push(earlier[left] ^ earlier[remainder - left]);
            }
        }
    }
    mex(options)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn octal_code_is_checked_and_canonical() {
        assert_eq!(OctalCode::try_new(&[2, 0, 0]).unwrap().digits(), &[2]);
        assert!(matches!(
            OctalCode::try_new(&[8]),
            Err(OctalCodeError::InvalidDigit { .. })
        ));
    }

    #[test]
    fn take_whole_heap_has_checked_eventual_zero_period() {
        // 0.1: G(0)=0, G(1)=1, and G(n)=0 thereafter.
        let certificate =
            GuySmithCertificate::compute(OctalCode::try_new(&[1]).unwrap(), 2, 1, 16).unwrap();
        assert_eq!(certificate.proof_window(), (2, 6));
        assert_eq!(certificate.heap_grundy(1), 1);
        assert_eq!(certificate.heap_grundy(1_000_000), 0);
        assert!(certificate.is_p_position(&[1, 1]));
    }

    #[test]
    fn subtraction_by_one_has_period_two() {
        // 0.2 has no move at heap 1, then alternates 1,0 from heap 2 onward.
        let certificate =
            GuySmithCertificate::compute(OctalCode::try_new(&[2]).unwrap(), 1, 2, 16).unwrap();
        assert_eq!(certificate.heap_grundy(1), 0);
        assert_eq!(certificate.heap_grundy(2), 1);
        assert_eq!(certificate.heap_grundy(101), 0);
        assert_eq!(certificate.heap_grundy(102), 1);
    }

    #[test]
    fn kayles_source_period_has_a_finite_certificate() {
        // Kayles 0.77 is periodic from heap 71 with period 12.
        let certificate =
            GuySmithCertificate::compute(OctalCode::try_new(&[7, 7]).unwrap(), 71, 12, 200)
                .unwrap();
        assert_eq!(certificate.proof_window(), (71, 156));
        for heap in 71..400u128 {
            assert_eq!(
                certificate.heap_grundy(heap + 12),
                certificate.heap_grundy(heap)
            );
        }
    }

    #[test]
    fn false_period_and_tampered_prefix_are_rejected() {
        let code = OctalCode::try_new(&[2]).unwrap();
        assert!(matches!(
            GuySmithCertificate::compute(code.clone(), 1, 1, 16),
            Err(GuySmithError::PeriodMismatch { .. })
        ));

        let valid = GuySmithCertificate::compute(code.clone(), 1, 2, 16).unwrap();
        let mut values = valid.checked_nim_values().to_vec();
        values[2] ^= 1;
        assert!(matches!(
            GuySmithWitness::new(1, 2, values).verify(code, 16),
            Err(GuySmithError::RecurrenceMismatch { heap: 2, .. })
        ));
    }

    #[test]
    fn certification_exposes_budget_and_parameter_failures() {
        let code = OctalCode::try_new(&[1]).unwrap();
        assert_eq!(
            GuySmithCertificate::compute(code.clone(), 2, 1, 5),
            Err(GuySmithError::TermBudgetExceeded {
                required: 7,
                budget: 5,
            })
        );
        assert_eq!(
            GuySmithCertificate::compute(code.clone(), 0, 1, 16),
            Err(GuySmithError::ZeroPreperiod)
        );
        assert_eq!(
            GuySmithCertificate::compute(code, 1, 0, 16),
            Err(GuySmithError::ZeroPeriod)
        );
        assert_eq!(
            GuySmithCertificate::compute(OctalCode::try_new(&[0]).unwrap(), 1, 1, 16),
            Err(GuySmithError::ZeroCode)
        );
    }
}
