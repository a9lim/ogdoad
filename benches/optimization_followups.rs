//! Comparative benchmarks for the post-audit algorithmic optimizations.
//!
//! Run with `cargo bench --bench optimization_followups`. The Grundy language
//! evaluator is deliberately excluded for a separate focused session.

use ogdoad::clifford::{
    char_poly, exterior_power_trace, is_blade, CliffordAlgebra, LinearMap, Metric, Multivector,
};
use ogdoad::forms::{
    e_8, even_unimodular_kneser_report, golay_code, leech, type_i_z2_code, DiscriminantForm,
    FiniteQuadraticModule, IntegralForm, PrimeCode,
};
use ogdoad::games::{heat, thermograph, Color, Game, Hackenbush, LoopyPartizanGraph};
use ogdoad::scalar::{Fp, Poly, Rational, Scalar, Surreal};
use std::collections::VecDeque;
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

fn unfolded_game_node_count(game: &Game) -> usize {
    let mut left = vec![Vec::new()];
    let mut right = vec![Vec::new()];
    let mut queue = VecDeque::from([(0, game.clone())]);
    while let Some((node, position)) = queue.pop_front() {
        for option in position.left() {
            let target = left.len();
            left.push(Vec::new());
            right.push(Vec::new());
            left[node].push(target);
            queue.push_back((target, option.clone()));
        }
        for option in position.right() {
            let target = left.len();
            left.push(Vec::new());
            right.push(Vec::new());
            right[node].push(target);
            queue.push_back((target, option.clone()));
        }
    }
    LoopyPartizanGraph::new(left, right).unwrap().node_count()
}

fn fp_mul_double_add<const P: u128>(mut a: u128, mut b: u128) -> u128 {
    let add = |a: u128, b: u128| {
        if a >= P - b {
            a - (P - b)
        } else {
            a + b
        }
    };
    let mut acc = 0u128;
    while b > 0 {
        if b & 1 == 1 {
            acc = add(acc, a);
        }
        b >>= 1;
        if b > 0 {
            a = add(a, a);
        }
    }
    acc
}

fn grade_masks_vec(n: usize, k: usize) -> Vec<u128> {
    if k == 0 {
        return vec![0];
    }
    if k > n {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut current = (1u128 << k) - 1;
    let limit = 1u128 << n;
    loop {
        out.push(current);
        let low = current & current.wrapping_neg();
        let next_high = current + low;
        let next = next_high + (((next_high ^ current) / low) >> 2);
        if next >= limit {
            return out;
        }
        current = next;
    }
}

fn higher_bits(mask: u128, index: usize) -> usize {
    (mask >> (index + 1)).count_ones() as usize
}

fn plucker_owned_reference(
    algebra: &CliffordAlgebra<Rational>,
    candidate: &Multivector<Rational>,
    grade: usize,
) -> bool {
    let i_masks = grade_masks_vec(algebra.dim(), grade - 1);
    let j_masks = grade_masks_vec(algebra.dim(), grade + 1);
    for i_mask in i_masks {
        for &j_mask in &j_masks {
            let mut acc = Rational::zero();
            let mut bits = j_mask;
            let mut position = 0usize;
            while bits != 0 {
                let index = bits.trailing_zeros() as usize;
                let bit = 1u128 << index;
                bits &= bits - 1;
                if i_mask & bit == 0 {
                    let left = candidate
                        .terms()
                        .get(&(i_mask | bit))
                        .cloned()
                        .unwrap_or_else(Rational::zero);
                    let right = candidate
                        .terms()
                        .get(&(j_mask ^ bit))
                        .cloned()
                        .unwrap_or_else(Rational::zero);
                    let mut term = left.mul(&right);
                    if (position + higher_bits(i_mask, index)) & 1 == 1 {
                        term = term.neg();
                    }
                    acc = acc.add(&term);
                }
                position += 1;
            }
            if !acc.is_zero() {
                return false;
            }
        }
    }
    true
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

    let graph_heap = Game::nim_heap(7);
    compare(
        "shared Game -> loopy graph *7",
        50,
        || unfolded_game_node_count(&graph_heap),
        || {
            LoopyPartizanGraph::from_game(&graph_heap, 8)
                .unwrap()
                .node_count()
        },
    );

    let unshared_thermo_heap = recursive_nim_heap(5);
    let shared_thermo_heap = Game::nim_heap(5);
    compare(
        "shared DAG thermograph *5",
        5,
        || {
            thermograph(&unshared_thermo_heap)
                .unwrap()
                .left_wall
                .points()
                .len()
        },
        || {
            thermograph(&shared_thermo_heap)
                .unwrap()
                .left_wall
                .points()
                .len()
        },
    );
    let heat_amount = Rational::one();
    compare(
        "shared DAG heat *5 by 1",
        5,
        || {
            heat(&unshared_thermo_heap, &heat_amount)
                .unwrap()
                .birthday() as usize
        },
        || heat(&shared_thermo_heap, &heat_amount).unwrap().birthday() as usize,
    );

    let modular_pairs = (0..4_096u128)
        .map(|value| {
            (
                value.wrapping_mul(31_337) % 65_537,
                value.wrapping_mul(47_101) % 65_537,
            )
        })
        .collect::<Vec<_>>();
    let fp_pairs = modular_pairs
        .iter()
        .map(|&(a, b)| (Fp::<65_537>::from_u128(a), Fp::<65_537>::from_u128(b)))
        .collect::<Vec<_>>();
    compare(
        "Fp checked-mul fast path 4096",
        100,
        || {
            modular_pairs
                .iter()
                .map(|&(a, b)| {
                    Fp::<65_537>::assert_supported_params();
                    fp_mul_double_add::<65_537>(a, b)
                })
                .fold(0u128, u128::wrapping_add) as usize
        },
        || {
            fp_pairs
                .iter()
                .map(|(a, b)| a.mul(b).value())
                .fold(0u128, u128::wrapping_add) as usize
        },
    );

    let blade_algebra = CliffordAlgebra::new(10, Metric::grassmann(10));
    let sparse_middle_blade = (0..5).fold(blade_algebra.scalar(Rational::one()), |blade, index| {
        blade_algebra.wedge(&blade, &blade_algebra.e(index))
    });
    compare(
        "sparse Plucker grade 5 in n=10",
        20,
        || plucker_owned_reference(&blade_algebra, &sparse_middle_blade, 5) as usize,
        || is_blade(&blade_algebra, &sparse_middle_blade) as usize,
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

    let shared_heap = Game::nim_heap(48);
    report("DAG birthday nim heap 48", 2_000, || {
        shared_heap.birthday() as usize
    });

    let leech_lattice = leech();
    report("one-pass definiteness rank 24", 2_000, || {
        leech_lattice.is_positive_definite() as usize
    });
    let e8 = e_8();
    report("visitor theta E8 through q^3", 500, || {
        e8.theta_series(4).unwrap().into_iter().sum::<i128>() as usize
    });
    report("prepared Kneser rank 16 report", 1, || {
        even_unimodular_kneser_report(16)
            .unwrap()
            .generated_neighbor_count
    });

    let q = vec![Rational::one(); 6];
    let polar = (0..6)
        .flat_map(|i| (i + 1..6).map(move |j| ((i, j), Rational::from_int((i + j + 1) as i128))))
        .collect::<Vec<_>>();
    let contraction = (0..6)
        .flat_map(|i| {
            (i + 1..6).map(move |j| ((i, j), Rational::from_int((i * 2 + j + 1) as i128)))
        })
        .collect::<Vec<_>>();
    let general = CliffordAlgebra::new(6, Metric::general(q, polar, contraction));
    let mut dense = general.scalar(Rational::one());
    for i in 0..6 {
        dense = general.add(&dense, &general.e(i));
        for j in i + 1..6 {
            dense = general.add(&dense, &general.wedge(&general.e(i), &general.e(j)));
        }
    }
    report("shared Clifford cache dense n=6", 100, || {
        general.mul(&dense, &dense).terms().len()
    });

    let binary = type_i_z2_code();
    report("packed code direct sum x8", 2_000, || {
        let mut sum = binary.clone();
        for _ in 1..8 {
            sum = sum.direct_sum(&binary);
        }
        sum.dim()
    });
    let ternary_left = PrimeCode::<3>::new(16, vec![vec![1; 16]]).unwrap();
    let ternary_right = PrimeCode::<3>::new(16, vec![vec![1; 16]]).unwrap();
    let ternary_sum = ternary_left.direct_sum(&ternary_right);
    report("prime-code RREF containment", 10_000, || {
        ternary_sum.contains(&ternary_sum) as usize
    });
    let golay = golay_code();
    report("cached MacWilliams Golay", 20, || {
        golay.macwilliams_transform().into_iter().sum::<i128>() as usize
    });

    let polynomial = Poly::<Fp<5>>::new((0..64).map(Fp::<5>::from_u128).collect());
    let modulus = Poly::<Fp<5>>::new(
        (0..33)
            .map(|degree| Fp::<5>::from_u128((degree == 0 || degree == 32) as u128))
            .collect(),
    );
    report("remainder-only polynomial power", 200, || {
        polynomial.pow_mod(257, &modulus).degree().unwrap_or(0)
    });
}
