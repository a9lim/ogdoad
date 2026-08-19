//! Comparative benchmarks for the post-audit algorithmic optimizations.
//!
//! Run with `cargo bench --bench optimization_followups`. The Grundy language
//! evaluator is deliberately excluded for a separate focused session.

use ogdoad::clifford::{char_poly, exterior_power_trace, CliffordAlgebra, LinearMap, Metric};
use ogdoad::forms::{DiscriminantForm, FiniteQuadraticModule, IntegralForm};
use ogdoad::games::{Color, Game, Hackenbush};
use ogdoad::scalar::{Rational, Scalar, Surreal};
use std::hint::black_box;
use std::time::{Duration, Instant};

const SAMPLES: usize = 7;

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
        "{name:<36} baseline={baseline_ns:>12.1} ns  candidate={candidate_ns:>12.1} ns  speedup={:>8.2}x",
        baseline_ns / candidate_ns
    );
}

fn report(name: &str, iterations: usize, workload: impl FnMut() -> usize) {
    let ns = measure(workload, iterations);
    println!("{name:<36} time={ns:>12.1} ns");
}

fn recursive_nim_heap(n: u128) -> Game {
    let options = (0..n).map(recursive_nim_heap).collect::<Vec<_>>();
    Game::new(options.clone(), options)
}

fn recursive_game_add(left_game: &Game, right_game: &Game) -> Game {
    let mut left = left_game
        .left()
        .iter()
        .map(|option| recursive_game_add(option, right_game))
        .collect::<Vec<_>>();
    left.extend(
        right_game
            .left()
            .iter()
            .map(|option| recursive_game_add(left_game, option)),
    );
    let mut right = left_game
        .right()
        .iter()
        .map(|option| recursive_game_add(option, right_game))
        .collect::<Vec<_>>();
    right.extend(
        right_game
            .right()
            .iter()
            .map(|option| recursive_game_add(left_game, option)),
    );
    Game::new(left, right)
}

fn exterior_char_poly(
    algebra: &CliffordAlgebra<Rational>,
    map: &LinearMap<Rational>,
) -> Vec<Rational> {
    (0..=algebra.dim())
        .map(|grade| {
            let coefficient = exterior_power_trace(algebra, map, grade);
            if grade % 2 == 1 {
                coefficient.neg()
            } else {
                coefficient
            }
        })
        .collect()
}

fn sigma_naive(terms: usize, power: u32) -> usize {
    let mut checksum = 0i128;
    for n in 1..terms {
        let mut sum = 0i128;
        for divisor in 1..=n {
            if n.is_multiple_of(divisor) {
                sum += (divisor as i128).pow(power);
            }
        }
        checksum ^= sum;
    }
    checksum as usize
}

fn sigma_sieve(terms: usize, power: u32) -> usize {
    let mut sums = vec![0i128; terms];
    for divisor in 1..terms {
        let value = (divisor as i128).pow(power);
        for multiple in (divisor..terms).step_by(divisor) {
            sums[multiple] += value;
        }
    }
    sums.into_iter()
        .fold(0i128, |checksum, value| checksum ^ value) as usize
}

fn nim_add_division(mut a: u128, mut b: u128, base: u128, coordinates: usize) -> u128 {
    let mut out = 0u128;
    let mut place = 1u128;
    for _ in 0..coordinates {
        out += ((a % base) ^ (b % base)) * place;
        place *= base;
        a /= base;
        b /= base;
    }
    out
}

fn surreal_series(count: usize, offset: i128) -> Surreal {
    (0..count).fold(Surreal::zero(), |sum, index| {
        sum.add(&Surreal::monomial(
            Surreal::from_int(offset + index as i128 * 2),
            Rational::from_int(index as i128 + 1),
        ))
    })
}

fn surreal_sort_merge_len(left: &Surreal, right: &Surreal) -> usize {
    let mut terms = left.terms().to_vec();
    terms.extend_from_slice(right.terms());
    terms.sort_by(|a, b| b.0.cmp(&a.0));
    let mut merged: Vec<(Surreal, Rational)> = Vec::with_capacity(terms.len());
    for (exponent, coefficient) in terms {
        if let Some(last) = merged.last_mut() {
            if last.0.cmp(&exponent).is_eq() {
                last.1 = last.1.add(&coefficient);
                continue;
            }
        }
        merged.push((exponent, coefficient));
    }
    merged.retain(|(_, coefficient)| !coefficient.is_zero());
    merged.len()
}

fn main() {
    println!("optimization follow-up benchmarks (median of {SAMPLES})");

    compare(
        "shared DAG nim heap n=10",
        30,
        || recursive_nim_heap(10).left().len(),
        || Game::nim_heap(10).left().len(),
    );
    let left_heap = Game::nim_heap(4);
    let right_heap = Game::nim_heap(4);
    compare(
        "memoized shared game sum *4+*4",
        10,
        || recursive_game_add(&left_heap, &right_heap).left().len(),
        || left_heap.add(&right_heap).left().len(),
    );

    let dimension = 7usize;
    let algebra = CliffordAlgebra::new(
        dimension,
        Metric::diagonal(vec![Rational::one(); dimension]),
    );
    let columns = (0..dimension)
        .map(|column| {
            (0..dimension)
                .map(|row| Rational::from_int(((row * 7 + column * 11 + 3) % 9) as i128 - 4))
                .collect()
        })
        .collect();
    let map = LinearMap::from_columns(columns);
    compare(
        "char poly dense rational n=7",
        20,
        || exterior_char_poly(&algebra, &map).len(),
        || char_poly(&algebra, &map).len(),
    );

    compare(
        "divisor powers through 2048",
        20,
        || sigma_naive(2_048, 5),
        || sigma_sieve(2_048, 5),
    );

    let packed_pairs = (0..4_096u128)
        .map(|value| {
            (
                value.wrapping_mul(0x9e37_79b9_7f4a_7c15),
                value.wrapping_mul(0xd1b5_4a32_d192_ed03),
            )
        })
        .collect::<Vec<_>>();
    compare(
        "packed nim add 4096 words",
        5_000,
        || {
            packed_pairs
                .iter()
                .map(|&(a, b)| nim_add_division(a, b, 16, 32))
                .fold(0u128, u128::wrapping_add) as usize
        },
        || {
            packed_pairs
                .iter()
                .map(|&(a, b)| a ^ b)
                .fold(0u128, u128::wrapping_add) as usize
        },
    );

    let left = surreal_series(128, 0);
    let right = surreal_series(128, 1);
    compare(
        "surreal merge 128+128",
        1_000,
        || surreal_sort_merge_len(&left, &right),
        || left.add(&right).terms().len(),
    );

    let rational_pairs = (1..=1_024i128)
        .map(|value| {
            (
                Rational::new(value, value + 1),
                Rational::new(value + 2, value + 3),
            )
        })
        .collect::<Vec<_>>();
    compare(
        "generic sign application 1024",
        2_000,
        || {
            rational_pairs
                .iter()
                .enumerate()
                .map(|(index, (a, b))| {
                    let sign = if index & 1 == 0 {
                        Rational::one()
                    } else {
                        Rational::one().neg()
                    };
                    a.mul(b).mul(&sign).numer() as usize
                })
                .fold(0usize, usize::wrapping_add)
        },
        || {
            rational_pairs
                .iter()
                .enumerate()
                .map(|(index, (a, b))| {
                    let product = a.mul(b);
                    let product = if index & 1 == 0 {
                        product
                    } else {
                        product.neg()
                    };
                    product.numer() as usize
                })
                .fold(0usize, usize::wrapping_add)
        },
    );

    for rank in [6usize, 8] {
        let lattice = IntegralForm::diagonal(&vec![2; rank]);
        let form = DiscriminantForm::from_lattice(&lattice).unwrap();
        report(
            &format!("discriminant phase order {}", 1usize << rank),
            if rank == 6 { 100 } else { 10 },
            || form.fqm_gauss_phase().unwrap().order,
        );
    }

    report("native FQM validation order 256", 20, || {
        FiniteQuadraticModule::cyclic(256, Rational::new(1, 256))
            .unwrap()
            .order() as usize
    });

    let bush = Hackenbush::new(
        (1..=10)
            .map(|vertex| ((vertex - 1) / 2, vertex, Color::Green))
            .collect(),
    );
    report("memoized Hackenbush 10 edges", 5, || {
        bush.to_game().birthday() as usize
    });
}
