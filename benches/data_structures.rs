//! Comparative microbenchmarks for bounded representation choices.
//!
//! Run with `cargo bench --bench data_structures`. This intentionally uses only
//! the standard library so the benchmark does not enlarge Ogdoad's dependency
//! surface. Matrices and Grundy evaluation are excluded by design.

use ogdoad::games::outcomes;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::hint::black_box;
use std::time::{Duration, Instant};

const SAMPLES: usize = 9;

fn median_ns_per_iteration(mut samples: Vec<Duration>, iterations: usize) -> f64 {
    samples.sort_unstable();
    samples[SAMPLES / 2].as_nanos() as f64 / iterations as f64
}

fn measure(mut workload: impl FnMut() -> usize, iterations: usize) -> f64 {
    for _ in 0..3 {
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
    median_ns_per_iteration(samples, iterations)
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
        "{name:<34} baseline={baseline_ns:>11.1} ns  candidate={candidate_ns:>11.1} ns  speedup={:>6.2}x",
        baseline_ns / candidate_ns
    );
}

fn fifo_vec_bool_remove_front() -> usize {
    let mut untouched = vec![true; 384];
    let mut queue = Vec::with_capacity(384);
    let mut checksum = 0usize;
    for coin in 0..384 {
        untouched[coin] = false;
        queue.push(coin);
        checksum ^= untouched.iter().filter(|&&value| value).count();
    }
    while !queue.is_empty() {
        checksum ^= queue.remove(0);
    }
    checksum
}

fn fifo_words_vec_deque() -> usize {
    let mut untouched = [u128::MAX; 3];
    let mut queue = VecDeque::with_capacity(384);
    let mut checksum = 0usize;
    for coin in 0..384 {
        untouched[coin / 128] &= !(1u128 << (coin % 128));
        queue.push_back(coin);
        checksum ^= untouched
            .iter()
            .map(|word| word.count_ones() as usize)
            .sum::<usize>();
    }
    while let Some(front) = queue.pop_front() {
        checksum ^= front;
    }
    checksum
}

fn map_terms(count: usize, stride: u128) -> BTreeMap<u128, i64> {
    (0..count)
        .map(|i| ((i as u128 * stride) % 4093, i as i64 + 1))
        .collect()
}

fn vec_terms(count: usize, stride: u128) -> Vec<(u128, i64)> {
    let mut terms = map_terms(count, stride).into_iter().collect::<Vec<_>>();
    terms.sort_unstable_by_key(|&(blade, _)| blade);
    terms
}

fn add_btree(a: &BTreeMap<u128, i64>, b: &BTreeMap<u128, i64>) -> usize {
    let mut out = a.clone();
    for (&blade, &coefficient) in b {
        *out.entry(blade).or_default() += coefficient;
    }
    black_box(out).len()
}

fn add_sorted(a: &[(u128, i64)], b: &[(u128, i64)]) -> usize {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].0.cmp(&b[j].0) {
            std::cmp::Ordering::Less => {
                out.push(a[i]);
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(b[j]);
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                out.push((a[i].0, a[i].1 + b[j].1));
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    black_box(out).len()
}

fn accumulate_btree(terms: &[(u128, i64)]) -> usize {
    let mut out: BTreeMap<u128, i64> = BTreeMap::new();
    for &(blade, coefficient) in terms {
        *out.entry(blade).or_default() += coefficient;
    }
    black_box(out).len()
}

fn accumulate_sorted(terms: &[(u128, i64)]) -> usize {
    let mut out = terms.to_vec();
    out.sort_unstable_by_key(|&(blade, _)| blade);
    let mut write = 0usize;
    for read in 0..out.len() {
        if write > 0 && out[write - 1].0 == out[read].0 {
            out[write - 1].1 += out[read].1;
        } else {
            out[write] = out[read];
            write += 1;
        }
    }
    out.truncate(write);
    black_box(out).len()
}

fn byte_rows(rows: usize, columns: usize) -> Vec<Vec<u8>> {
    (0..rows)
        .map(|row| {
            (0..columns)
                .map(|column| ((row * 17 + column * 29 + row * column) & 1) as u8)
                .collect()
        })
        .collect()
}

fn packed_rows(rows: &[Vec<u8>]) -> Vec<Vec<u64>> {
    rows.iter()
        .map(|row| {
            let mut packed = vec![0u64; row.len().div_ceil(64)];
            for (column, &bit) in row.iter().enumerate() {
                packed[column / 64] |= u64::from(bit) << (column % 64);
            }
            packed
        })
        .collect()
}

fn byte_code_kernel(rows: &[Vec<u8>], columns: usize) -> usize {
    let mut accumulator = vec![0u8; columns];
    let mut checksum = 0usize;
    for row in rows {
        for (target, &bit) in accumulator.iter_mut().zip(row) {
            *target ^= bit;
        }
        checksum ^= accumulator.iter().map(|&bit| bit as usize).sum::<usize>();
    }
    black_box(accumulator);
    checksum
}

fn packed_code_kernel(rows: &[Vec<u64>]) -> usize {
    let mut accumulator = vec![0u64; rows.first().map_or(0, Vec::len)];
    let mut checksum = 0usize;
    for row in rows {
        for (target, &word) in accumulator.iter_mut().zip(row) {
            *target ^= word;
        }
        checksum ^= accumulator
            .iter()
            .map(|word| word.count_ones() as usize)
            .sum::<usize>();
    }
    black_box(accumulator);
    checksum
}

struct GraphData {
    nested: Vec<Vec<usize>>,
    offsets: Vec<usize>,
    edges: Vec<usize>,
}

fn graph_data(nodes: usize, degree: usize) -> GraphData {
    let nested = (0..nodes)
        .map(|node| {
            (0..degree)
                .map(|edge| (node * 17 + edge * 101 + 1) % nodes)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut offsets = Vec::with_capacity(nodes + 1);
    let mut edges = Vec::with_capacity(nodes * degree);
    offsets.push(0);
    for row in &nested {
        edges.extend_from_slice(row);
        offsets.push(edges.len());
    }
    GraphData {
        nested,
        offsets,
        edges,
    }
}

fn traverse_nested(graph: &[Vec<usize>]) -> usize {
    graph
        .iter()
        .flat_map(|row| row.iter())
        .fold(0usize, |checksum, &target| checksum.wrapping_add(target))
}

fn traverse_csr(offsets: &[usize], edges: &[usize]) -> usize {
    offsets
        .windows(2)
        .flat_map(|bounds| edges[bounds[0]..bounds[1]].iter())
        .fold(0usize, |checksum, &target| checksum.wrapping_add(target))
}

const TRIANGULAR_LEN: usize = 128 * 129 / 2;

fn triangular_index(i: usize, j: usize) -> usize {
    let (i, j) = if i <= j { (i, j) } else { (j, i) };
    i * 128 - i * i.saturating_sub(1) / 2 + (j - i)
}

fn nim_memo_fill_hash() -> usize {
    let mut memo = HashMap::with_capacity(TRIANGULAR_LEN);
    for i in 0..128 {
        for j in i..128 {
            memo.insert((i, j), i * 128 + j + 1);
        }
    }
    black_box(memo).len()
}

fn nim_memo_fill_table() -> usize {
    let mut memo = [0usize; TRIANGULAR_LEN];
    for i in 0..128 {
        for j in i..128 {
            memo[triangular_index(i, j)] = i * 128 + j + 1;
        }
    }
    black_box(memo)[TRIANGULAR_LEN - 1]
}

fn main() {
    println!("Ogdoad data-structure comparisons (median of {SAMPLES} samples)");
    println!("baseline is the current/general representation; candidate is the compact one\n");

    compare(
        "Witt-FIFO 384 transitions",
        2_000,
        fifo_vec_bool_remove_front,
        fifo_words_vec_deque,
    );

    for (count, iterations) in [(16, 20_000), (128, 5_000), (512, 1_000)] {
        let map_a = map_terms(count, 2);
        let map_b = map_terms(count, 3);
        let vec_a = vec_terms(count, 2);
        let vec_b = vec_terms(count, 3);
        compare(
            &format!("multivector add {count}+{count}"),
            iterations,
            || add_btree(&map_a, &map_b),
            || add_sorted(&vec_a, &vec_b),
        );
    }
    let product_terms = (0..4_096)
        .map(|i| (((i * 73) ^ (i * 19 + 11)) as u128 & 1023, i as i64 + 1))
        .collect::<Vec<_>>();
    compare(
        "multivector batch accumulation",
        1_000,
        || accumulate_btree(&product_terms),
        || accumulate_sorted(&product_terms),
    );

    for (columns, iterations) in [(24, 20_000), (256, 5_000), (1024, 1_000)] {
        let bytes = byte_rows(64, columns);
        let packed = packed_rows(&bytes);
        compare(
            &format!("binary rows 64x{columns}"),
            iterations,
            || byte_code_kernel(&bytes, columns),
            || packed_code_kernel(&packed),
        );
    }

    let graph = graph_data(8_192, 8);
    compare(
        "graph traversal 8192x8",
        500,
        || traverse_nested(&graph.nested),
        || traverse_csr(&graph.offsets, &graph.edges),
    );

    let outcome_graph = graph_data(2_048, 4).nested;
    let cached_outcomes = outcomes(&outcome_graph);
    let mut recompute_cursor = 0usize;
    let recompute_ns = measure(
        || {
            recompute_cursor = recompute_cursor.wrapping_add(1);
            match outcomes(&outcome_graph)[black_box(recompute_cursor % outcome_graph.len())] {
                ogdoad::games::Outcome::Win => 1,
                ogdoad::games::Outcome::Loss => 2,
                ogdoad::games::Outcome::Draw => 3,
            }
        },
        100,
    );
    let mut cached_cursor = 0usize;
    let cached_ns = measure(
        || {
            cached_cursor = cached_cursor.wrapping_add(1);
            match cached_outcomes[black_box(cached_cursor % cached_outcomes.len())] {
                ogdoad::games::Outcome::Win => 1,
                ogdoad::games::Outcome::Loss => 2,
                ogdoad::games::Outcome::Draw => 3,
            }
        },
        1_000_000,
    );
    println!(
        "{:<34} recompute={recompute_ns:>10.1} ns  cached-read={cached_ns:>8.1} ns  speedup={:>8.1}x",
        "graph outcome reuse",
        recompute_ns / cached_ns
    );

    compare(
        "Nimber memo cold fill",
        500,
        nim_memo_fill_hash,
        nim_memo_fill_table,
    );

    let hash_memo = (0..128)
        .flat_map(|i| (i..128).map(move |j| ((i, j), i * 128 + j + 1)))
        .collect::<HashMap<_, _>>();
    let mut table_memo = [0usize; TRIANGULAR_LEN];
    for (&(i, j), &value) in &hash_memo {
        table_memo[triangular_index(i, j)] = value;
    }
    let keys = (0..4_096)
        .map(|x| ((x * 73) & 127, (x * 109 + 17) & 127))
        .collect::<Vec<_>>();
    compare(
        "Nimber memo 4096 hot lookups",
        5_000,
        || {
            keys.iter()
                .map(|&(i, j)| *hash_memo.get(&(i.min(j), i.max(j))).unwrap())
                .fold(0usize, usize::wrapping_add)
        },
        || {
            keys.iter()
                .map(|&(i, j)| table_memo[triangular_index(i, j)])
                .fold(0usize, usize::wrapping_add)
        },
    );
}
