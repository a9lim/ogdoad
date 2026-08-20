//! Focused before/after benchmarks for the major adversarial optimization passes.
//!
//! Run with `cargo bench --bench major_speedups`. Matrix and Grundy workloads
//! are deliberately absent; they have separate optimization sessions.

use ogdoad::clifford::{bits, CliffordAlgebra, Metric, Multivector};
use ogdoad::forms::IntegralForm;
use ogdoad::scalar::{Fp, Fpn, Poly, Qp, Rational, RationalFunction, Scalar, Zp};
use std::collections::BTreeMap;
use std::hint::black_box;
use std::time::{Duration, Instant};

const SAMPLES: usize = 5;

fn median_ns(mut samples: Vec<Duration>, iterations: usize) -> f64 {
    samples.sort_unstable();
    samples[SAMPLES / 2].as_nanos() as f64 / iterations as f64
}

fn measure(mut workload: impl FnMut() -> usize, iterations: usize) -> f64 {
    for _ in 0..2 {
        black_box(workload());
    }
    let mut samples = Vec::with_capacity(SAMPLES);
    for _ in 0..SAMPLES {
        let start = Instant::now();
        let mut checksum = 0usize;
        for _ in 0..iterations {
            checksum ^= black_box(workload());
        }
        black_box(checksum);
        samples.push(start.elapsed());
    }
    median_ns(samples, iterations)
}

fn compare(
    name: &str,
    iterations: usize,
    baseline: impl FnMut() -> usize,
    candidate: impl FnMut() -> usize,
) {
    let baseline_ns = measure(baseline, iterations);
    let candidate_ns = measure(candidate, iterations);
    println!(
        "{name:<42} baseline={baseline_ns:>13.1} ns  candidate={candidate_ns:>13.1} ns  speedup={:>9.2}x",
        baseline_ns / candidate_ns
    );
}

fn trim_fp<const P: u128>(mut coefficients: Vec<Fp<P>>) -> Vec<Fp<P>> {
    while coefficients.last().is_some_and(Scalar::is_zero) {
        coefficients.pop();
    }
    coefficients
}

/// Former polynomial remainder path: rediscover the divisor degree and invert
/// its leading coefficient on every call, including for a monic modulus.
fn rem_reference<const P: u128>(mut remainder: Vec<Fp<P>>, divisor: &Poly<Fp<P>>) -> Poly<Fp<P>> {
    let divisor_degree = divisor.degree().expect("nonzero benchmark modulus");
    let leading_inverse = divisor
        .leading()
        .unwrap()
        .inv()
        .expect("field coefficient inverts");
    loop {
        remainder = trim_fp(remainder);
        let Some(remainder_degree) = remainder.len().checked_sub(1) else {
            break;
        };
        if remainder_degree < divisor_degree {
            break;
        }
        let shift = remainder_degree - divisor_degree;
        let factor = remainder[remainder_degree].mul(&leading_inverse);
        for (index, coefficient) in divisor.coeffs().iter().enumerate() {
            remainder[shift + index] = remainder[shift + index].sub(&factor.mul(coefficient));
        }
    }
    Poly::new(remainder)
}

fn mul_mod_reference<const P: u128>(
    left: &Poly<Fp<P>>,
    right: &Poly<Fp<P>>,
    modulus: &Poly<Fp<P>>,
) -> Poly<Fp<P>> {
    rem_reference(left.mul(right).coeffs().to_vec(), modulus)
}

fn pow_mod_reference<const P: u128>(
    value: &Poly<Fp<P>>,
    mut exponent: u128,
    modulus: &Poly<Fp<P>>,
) -> Poly<Fp<P>> {
    let mut accumulator = rem_reference(Poly::one().coeffs().to_vec(), modulus);
    let mut base = rem_reference(value.coeffs().to_vec(), modulus);
    while exponent > 0 {
        if exponent & 1 == 1 {
            accumulator = mul_mod_reference(&accumulator, &base, modulus);
        }
        exponent >>= 1;
        if exponent > 0 {
            base = mul_mod_reference(&base, &base, modulus);
        }
    }
    accumulator
}

fn pow_mod_char_two_dense_reduction_reference(
    value: &Poly<Fp<2>>,
    mut exponent: u128,
    modulus: &Poly<Fp<2>>,
) -> Poly<Fp<2>> {
    let mut accumulator = rem_reference(Poly::one().coeffs().to_vec(), modulus);
    let mut base = rem_reference(value.coeffs().to_vec(), modulus);
    while exponent > 0 {
        if exponent & 1 == 1 {
            accumulator = mul_mod_reference(&accumulator, &base, modulus);
        }
        exponent >>= 1;
        if exponent > 0 {
            let mut squared = vec![Fp::<2>::zero(); 2 * base.coeffs().len() - 1];
            for (index, coefficient) in base.coeffs().iter().enumerate() {
                if !coefficient.is_zero() {
                    squared[2 * index] = coefficient.mul(coefficient);
                }
            }
            base = rem_reference(squared, modulus);
        }
    }
    accumulator
}

fn function_add_reference<const P: u128>(
    left: &RationalFunction<Fp<P>>,
    right: &RationalFunction<Fp<P>>,
) -> RationalFunction<Fp<P>> {
    let numerator = left
        .num()
        .mul(right.den())
        .add(&right.num().mul(left.den()));
    let denominator = left.den().mul(right.den());
    RationalFunction::new(numerator.coeffs().to_vec(), denominator.coeffs().to_vec())
}

fn function_mul_reference<const P: u128>(
    left: &RationalFunction<Fp<P>>,
    right: &RationalFunction<Fp<P>>,
) -> RationalFunction<Fp<P>> {
    let numerator = left.num().mul(right.num());
    let denominator = left.den().mul(right.den());
    RationalFunction::new(numerator.coeffs().to_vec(), denominator.coeffs().to_vec())
}

fn polynomial_power<const P: u128>(mut base: Poly<Fp<P>>, mut exponent: usize) -> Poly<Fp<P>> {
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

fn linear_factor<const P: u128>(root: i128) -> Poly<Fp<P>> {
    Poly::new(vec![Fp::<P>::from_int(-root), Fp::<P>::one()])
}

fn checksum_function<const P: u128>(function: &RationalFunction<Fp<P>>) -> usize {
    function
        .num()
        .coeffs()
        .iter()
        .chain(function.den().coeffs())
        .enumerate()
        .fold(0usize, |checksum, (index, coefficient)| {
            checksum ^ index.wrapping_mul(131) ^ coefficient.value() as usize
        })
}

fn brute_short_vector_count(form: &IntegralForm, bound: i128, radius: i128) -> usize {
    fn visit(
        form: &IntegralForm,
        bound: i128,
        radius: i128,
        index: usize,
        coordinates: &mut [i128],
        count: &mut usize,
    ) {
        if index == coordinates.len() {
            let norm = form.norm(coordinates);
            *count += usize::from(norm > 0 && norm <= bound);
            return;
        }
        for coordinate in -radius..=radius {
            coordinates[index] = coordinate;
            visit(form, bound, radius, index + 1, coordinates, count);
        }
    }

    let mut count = 0;
    visit(form, bound, radius, 0, &mut vec![0; form.dim()], &mut count);
    count
}

fn brute_diagonal_theta(form: &IntegralForm, terms: usize, radius: i128) -> Vec<i128> {
    fn visit(
        form: &IntegralForm,
        terms: usize,
        radius: i128,
        index: usize,
        coordinates: &mut [i128],
        coefficients: &mut [i128],
    ) {
        if index == coordinates.len() {
            let norm = form.norm(coordinates);
            if norm >= 0 && norm % 2 == 0 {
                let theta_index = usize::try_from(norm / 2).unwrap();
                if theta_index < terms {
                    coefficients[theta_index] += 1;
                }
            }
            return;
        }
        for coordinate in -radius..=radius {
            coordinates[index] = coordinate;
            visit(form, terms, radius, index + 1, coordinates, coefficients);
        }
    }

    let mut coefficients = vec![0; terms];
    visit(
        form,
        terms,
        radius,
        0,
        &mut vec![0; form.dim()],
        &mut coefficients,
    );
    coefficients
}

fn fp_theta_recompute_leaf_norm(form: &IntegralForm, terms: usize) -> Vec<i128> {
    fn ldl(gram: &[Vec<i128>]) -> (Vec<f64>, Vec<Vec<f64>>) {
        let n = gram.len();
        let mut d = vec![0.0f64; n];
        let mut lower = vec![vec![0.0f64; n]; n];
        for j in 0..n {
            let mut pivot = gram[j][j] as f64;
            for k in 0..j {
                pivot -= lower[j][k] * lower[j][k] * d[k];
            }
            d[j] = pivot;
            lower[j][j] = 1.0;
            for i in j + 1..n {
                let mut value = gram[i][j] as f64;
                for k in 0..j {
                    value -= lower[i][k] * lower[j][k] * d[k];
                }
                lower[i][j] = value / pivot;
            }
        }
        let mut upper = vec![vec![0.0f64; n]; n];
        for i in 0..n {
            for j in i + 1..n {
                upper[i][j] = lower[j][i];
            }
        }
        (d, upper)
    }

    #[allow(clippy::too_many_arguments)]
    fn search(
        form: &IntegralForm,
        i: usize,
        bound: i128,
        d: &[f64],
        upper: &[Vec<f64>],
        epsilon: f64,
        tail: f64,
        coordinates: &mut [i128],
        coefficients: &mut [i128],
    ) {
        if i == 0 {
            let norm = form.norm(coordinates);
            if norm > 0 && norm <= bound && norm % 2 == 0 {
                coefficients[usize::try_from(norm / 2).unwrap()] += 1;
            }
            return;
        }
        let index = i - 1;
        let center = (i..d.len())
            .map(|j| upper[index][j] * coordinates[j] as f64)
            .sum::<f64>();
        let remaining = bound as f64 - tail;
        if remaining < -epsilon {
            return;
        }
        let radius = (remaining.max(0.0) / d[index]).sqrt() + epsilon;
        let low = (-center - radius).ceil() as i128;
        let high = (-center + radius).floor() as i128;
        for coordinate in low..=high {
            coordinates[index] = coordinate;
            let shifted = coordinate as f64 + center;
            search(
                form,
                index,
                bound,
                d,
                upper,
                epsilon,
                tail + d[index] * shifted * shifted,
                coordinates,
                coefficients,
            );
        }
        coordinates[index] = 0;
    }

    let bound = i128::try_from(2 * terms.saturating_sub(1)).unwrap();
    let (d, upper) = ldl(form.gram());
    let epsilon = 1e-9 * (bound as f64).max(1.0) + 1e-9;
    let mut coefficients = vec![0i128; terms];
    coefficients[0] = 1;
    search(
        form,
        form.dim(),
        bound,
        &d,
        &upper,
        epsilon,
        0.0,
        &mut vec![0; form.dim()],
        &mut coefficients,
    );
    coefficients
}

fn wedge_is_negative_reference(a: u128, b: u128) -> bool {
    bits(a)
        .into_iter()
        .map(|index| (b & ((1u128 << index) - 1)).count_ones())
        .sum::<u32>()
        & 1
        == 1
}

fn dense_orthogonal_reference<const P: u128>(
    algebra: &CliffordAlgebra<Fp<P>>,
    left: &Multivector<Fp<P>>,
    right: &Multivector<Fp<P>>,
) -> BTreeMap<u128, Fp<P>> {
    let mut out = BTreeMap::new();
    for (&left_blade, left_coefficient) in left.terms() {
        for (&right_blade, right_coefficient) in right.terms() {
            let mut coefficient = left_coefficient.mul(right_coefficient);
            let mut common = left_blade & right_blade;
            while common != 0 {
                let index = common.trailing_zeros() as usize;
                common &= common - 1;
                coefficient = coefficient.mul(&algebra.metric().q()[index]);
            }
            if wedge_is_negative_reference(left_blade, right_blade) {
                coefficient = coefficient.neg();
            }
            if coefficient.is_zero() {
                continue;
            }
            let blade = left_blade ^ right_blade;
            let next = out
                .get(&blade)
                .map_or(coefficient, |current: &Fp<P>| current.add(&coefficient));
            if next.is_zero() {
                out.remove(&blade);
            } else {
                out.insert(blade, next);
            }
        }
    }
    out
}

fn dense_multivector<const P: u128>(
    algebra: &CliffordAlgebra<Fp<P>>,
    offset: u128,
) -> Multivector<Fp<P>> {
    let mut out = algebra.zero();
    for blade in 0..(1u128 << algebra.dim()) {
        let coefficient = Fp::<P>::from_u128((blade * 17 + offset) % (P - 1) + 1);
        out = algebra.add(
            &out,
            &algebra.scalar_mul(&coefficient, &algebra.blade(&bits(blade))),
        );
    }
    out
}

fn checksum_map<const P: u128>(terms: &BTreeMap<u128, Fp<P>>) -> usize {
    terms
        .iter()
        .fold(0usize, |checksum, (&blade, coefficient)| {
            checksum ^ blade as usize ^ coefficient.value() as usize
        })
}

fn main() {
    type LargeZp = Zp<65_537, 4>;
    type LargeQp = Qp<65_537, 4>;
    type LargeFpn = Fpn<65_537, 1>;
    let zp_left = LargeZp::from_u128(1_234_567_890_123_456_789);
    let zp_right = LargeZp::from_u128(987_654_321_987_654_321);
    compare(
        "Zp large-prime invariant reuse",
        100,
        || {
            LargeZp::assert_supported_params();
            LargeZp::assert_supported_params();
            black_box(zp_left).mul(&black_box(zp_right)).value() as usize
        },
        || black_box(zp_left).mul(&black_box(zp_right)).value() as usize,
    );

    let qp_left = LargeQp::from_int(1_234_567_890_123_456_789);
    let qp_right = LargeQp::from_int(987_654_321_987_654_321);
    compare(
        "Qp large-prime invariant reuse",
        100,
        || {
            LargeQp::assert_supported_params();
            LargeQp::assert_supported_params();
            black_box(qp_left).mul(&black_box(qp_right)).unit() as usize
        },
        || black_box(qp_left).mul(&black_box(qp_right)).unit() as usize,
    );

    let fpn_left = LargeFpn::from_coeffs(&[1_234_567_890_123_456_789]);
    let fpn_right = LargeFpn::from_coeffs(&[987_654_321_987_654_321]);
    compare(
        "Fpn large-prime invariant reuse",
        100,
        || {
            LargeFpn::assert_supported_params();
            black_box(fpn_left).mul(&black_box(fpn_right)).coeff(0) as usize
        },
        || black_box(fpn_left).mul(&black_box(fpn_right)).coeff(0) as usize,
    );

    type Function = RationalFunction<Fp<3>>;
    let polynomial = Poly::new(
        (0..=256)
            .map(|index| Fp::<3>::from_u128((index * 7 + 1) as u128))
            .collect(),
    );
    compare(
        "rational-function polynomial embed",
        100,
        || {
            Function::new(polynomial.coeffs().to_vec(), vec![Fp::<3>::one()])
                .num()
                .degree()
                .unwrap_or(0)
        },
        || {
            Function::from_poly(polynomial.clone())
                .num()
                .degree()
                .unwrap_or(0)
        },
    );
    let function_left = Function::from_poly(polynomial.clone());
    let function_right = Function::from_poly(Poly::new(
        (0..=256)
            .map(|index| Fp::<3>::from_u128((index * 11 + 2) as u128))
            .collect(),
    ));
    compare(
        "rational-function denominator-one add",
        100,
        || {
            let numerator = function_left
                .num()
                .mul(function_right.den())
                .add(&function_right.num().mul(function_left.den()));
            let denominator = function_left.den().mul(function_right.den());
            Function::new(numerator.coeffs().to_vec(), denominator.coeffs().to_vec())
                .num()
                .degree()
                .unwrap_or(0)
        },
        || {
            function_left
                .add(&function_right)
                .num()
                .degree()
                .unwrap_or(0)
        },
    );

    let odd_value = Poly::<Fp<5>>::new(
        (0..64)
            .map(|index| Fp::<5>::from_u128((index * 3 + 1) as u128))
            .collect(),
    );
    let odd_modulus = Poly::<Fp<5>>::new(
        (0..=64)
            .map(|index| Fp::<5>::from_u128(u128::from(matches!(index, 0 | 3 | 64))))
            .collect(),
    );
    assert_eq!(
        pow_mod_reference(&odd_value, 257, &odd_modulus),
        odd_value.pow_mod(257, &odd_modulus)
    );
    compare(
        "prepared monic polynomial modulus",
        10,
        || {
            pow_mod_reference(&odd_value, 257, &odd_modulus)
                .coeffs()
                .len()
        },
        || odd_value.pow_mod(257, &odd_modulus).coeffs().len(),
    );
    let dense_odd_modulus = Poly::<Fp<5>>::new(
        (0..=64)
            .map(|index| {
                if index == 64 {
                    Fp::<5>::one()
                } else {
                    Fp::<5>::from_u128((index % 4 + 1) as u128)
                }
            })
            .collect(),
    );
    assert_eq!(
        pow_mod_reference(&odd_value, 257, &dense_odd_modulus),
        odd_value.pow_mod(257, &dense_odd_modulus)
    );
    compare(
        "dense polynomial modulus guard",
        10,
        || {
            pow_mod_reference(&odd_value, 257, &dense_odd_modulus)
                .coeffs()
                .len()
        },
        || odd_value.pow_mod(257, &dense_odd_modulus).coeffs().len(),
    );

    let binary_value = Poly::<Fp<2>>::new(
        (0..128)
            .map(|index| Fp::<2>::from_u128(u128::from(index % 3 != 0)))
            .collect(),
    );
    let binary_modulus = Poly::<Fp<2>>::new(
        (0..=128)
            .map(|index| Fp::<2>::from_u128(u128::from(matches!(index, 0 | 1 | 2 | 7 | 128))))
            .collect(),
    );
    assert_eq!(
        pow_mod_char_two_dense_reduction_reference(&binary_value, 256, &binary_modulus),
        binary_value.pow_mod(256, &binary_modulus)
    );
    compare(
        "sparse characteristic-two modulus",
        10,
        || {
            pow_mod_char_two_dense_reduction_reference(&binary_value, 256, &binary_modulus)
                .coeffs()
                .len()
        },
        || binary_value.pow_mod(256, &binary_modulus).coeffs().len(),
    );

    type LargeFunction = RationalFunction<Fp<65_537>>;
    let factor = |root| polynomial_power(linear_factor::<65_537>(root), 64);
    let large_left = LargeFunction::new(
        factor(1).mul(&factor(3)).coeffs().to_vec(),
        factor(2).mul(&factor(4)).coeffs().to_vec(),
    );
    let cancellable_right = LargeFunction::new(
        factor(2).mul(&factor(5)).coeffs().to_vec(),
        factor(1).mul(&factor(6)).coeffs().to_vec(),
    );
    assert_eq!(
        function_mul_reference(&large_left, &cancellable_right),
        large_left.mul(&cancellable_right)
    );
    compare(
        "rational-function cross cancellation",
        25,
        || checksum_function(&function_mul_reference(&large_left, &cancellable_right)),
        || checksum_function(&large_left.mul(&cancellable_right)),
    );
    let coprime_right = LargeFunction::new(
        factor(5).mul(&factor(7)).coeffs().to_vec(),
        factor(6).mul(&factor(8)).coeffs().to_vec(),
    );
    assert_eq!(
        function_mul_reference(&large_left, &coprime_right),
        large_left.mul(&coprime_right)
    );
    compare(
        "rational-function no-cancel guard",
        25,
        || checksum_function(&function_mul_reference(&large_left, &coprime_right)),
        || checksum_function(&large_left.mul(&coprime_right)),
    );
    let shared_denominator_right = LargeFunction::new(
        factor(7).mul(&factor(8)).coeffs().to_vec(),
        factor(2).mul(&factor(6)).coeffs().to_vec(),
    );
    assert_eq!(
        function_add_reference(&large_left, &shared_denominator_right),
        large_left.add(&shared_denominator_right)
    );
    compare(
        "rational-function gcd-first addition",
        25,
        || {
            checksum_function(&function_add_reference(
                &large_left,
                &shared_denominator_right,
            ))
        },
        || checksum_function(&large_left.add(&shared_denominator_right)),
    );
    let small_left = LargeFunction::new(
        linear_factor::<65_537>(1).coeffs().to_vec(),
        linear_factor::<65_537>(2).coeffs().to_vec(),
    );
    let small_right = LargeFunction::new(
        linear_factor::<65_537>(3).coeffs().to_vec(),
        linear_factor::<65_537>(4).coeffs().to_vec(),
    );
    compare(
        "small rational-function mul guard",
        10_000,
        || checksum_function(&function_mul_reference(&small_left, &small_right)),
        || checksum_function(&small_left.mul(&small_right)),
    );
    compare(
        "small rational-function add guard",
        10_000,
        || checksum_function(&function_add_reference(&small_left, &small_right)),
        || checksum_function(&small_left.add(&small_right)),
    );
    for degree in [2usize, 4, 8, 16, 32] {
        let factor = |root| polynomial_power(linear_factor::<65_537>(root), degree);
        let left = LargeFunction::new(
            factor(1).mul(&factor(3)).coeffs().to_vec(),
            factor(2).mul(&factor(4)).coeffs().to_vec(),
        );
        let right = LargeFunction::new(
            factor(2).mul(&factor(5)).coeffs().to_vec(),
            factor(1).mul(&factor(6)).coeffs().to_vec(),
        );
        compare(
            &format!("rational-function mul degree {}", 2 * degree),
            500,
            || checksum_function(&function_mul_reference(&left, &right)),
            || checksum_function(&left.mul(&right)),
        );
    }

    let exact_rank4 = IntegralForm::diagonal(&[2; 4]);
    assert_eq!(
        brute_short_vector_count(&exact_rank4, 8, 2),
        exact_rank4.short_vectors(8).unwrap().len()
    );
    compare(
        "incremental exact-box lattice norms",
        1_000,
        || brute_short_vector_count(&exact_rank4, 8, 2),
        || exact_rank4.short_vectors(8).unwrap().len(),
    );

    let pruned_rank8 = IntegralForm::diagonal(&[2; 8]);
    assert_eq!(
        brute_short_vector_count(&pruned_rank8, 4, 2),
        pruned_rank8.short_vectors(4).unwrap().len()
    );
    compare(
        "pruned search instead of rank-8 box",
        5,
        || brute_short_vector_count(&pruned_rank8, 4, 2),
        || pruned_rank8.short_vectors(4).unwrap().len(),
    );

    let mut a12_gram = vec![vec![0i128; 12]; 12];
    for index in 0..12 {
        a12_gram[index][index] = 2;
        if index + 1 < 12 {
            a12_gram[index][index + 1] = -1;
            a12_gram[index + 1][index] = -1;
        }
    }
    let a12 = IntegralForm::new(a12_gram).unwrap();
    assert_eq!(
        fp_theta_recompute_leaf_norm(&a12, 7),
        a12.theta_series(7).unwrap()
    );
    compare(
        "incremental Fincke-Pohst exact norm",
        1,
        || fp_theta_recompute_leaf_norm(&a12, 7).iter().sum::<i128>() as usize,
        || a12.theta_series(7).unwrap().iter().sum::<i128>() as usize,
    );

    let theta_reference = brute_diagonal_theta(&pruned_rank8, 4, 2);
    assert_eq!(theta_reference, pruned_rank8.theta_series(4).unwrap());
    compare(
        "orthogonal-component theta convolution",
        5,
        || {
            brute_diagonal_theta(&pruned_rank8, 4, 2)
                .iter()
                .sum::<i128>() as usize
        },
        || pruned_rank8.theta_series(4).unwrap().iter().sum::<i128>() as usize,
    );

    let dense_algebra = CliffordAlgebra::new(
        9,
        Metric::diagonal(
            (0..9)
                .map(|index| Fp::<65_537>::from_u128(index as u128 + 2))
                .collect(),
        ),
    );
    let dense_left = dense_multivector(&dense_algebra, 3);
    let dense_right = dense_multivector(&dense_algebra, 11);
    let dense_reference = dense_orthogonal_reference(&dense_algebra, &dense_left, &dense_right);
    assert_eq!(
        &dense_reference,
        dense_algebra.mul(&dense_left, &dense_right).terms()
    );
    compare(
        "dense orthogonal Clifford accumulator",
        3,
        || {
            checksum_map(&dense_orthogonal_reference(
                &dense_algebra,
                &dense_left,
                &dense_right,
            ))
        },
        || checksum_map(dense_algebra.mul(&dense_left, &dense_right).terms()),
    );

    let polar = (0..6)
        .flat_map(|left| {
            (left + 1..6).map(move |right| {
                (
                    (left, right),
                    Rational::from_int((left + right + 1) as i128),
                )
            })
        })
        .collect::<Vec<_>>();
    let contraction = (0..6)
        .flat_map(|left| {
            (left + 1..6).map(move |right| {
                (
                    (left, right),
                    Rational::from_int((left * 2 + right + 1) as i128),
                )
            })
        })
        .collect::<Vec<_>>();
    let general_metric = Metric::general(vec![Rational::one(); 6], polar, contraction);
    let general = CliffordAlgebra::new(6, general_metric.clone());
    let mut mixed = general.scalar(Rational::one());
    for index in 0..6 {
        mixed = general.add(&mixed, &general.e(index));
        for other in index + 1..6 {
            mixed = general.add(&mixed, &general.wedge(&general.e(index), &general.e(other)));
        }
    }
    let expected = general.mul(&mixed, &mixed);
    assert_eq!(
        CliffordAlgebra::new(6, general_metric.clone()).mul(&mixed, &mixed),
        expected
    );
    compare(
        "persistent nonorthogonal Clifford memo",
        100,
        || {
            CliffordAlgebra::new(6, general_metric.clone())
                .mul(&mixed, &mixed)
                .terms()
                .len()
        },
        || general.mul(&mixed, &mixed).terms().len(),
    );
}
