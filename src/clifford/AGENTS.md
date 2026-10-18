# `src/clifford/` editing guide

This pillar owns the generic multivector engine and metric-dependent geometric
algebra. It must remain pure Rust and generic over `Scalar`.

## Map

| path | responsibility |
| --- | --- |
| `engine/metric.rs` | `Metric { q, b, a }` construction and validation |
| `engine/basis.rs` | `u128` blade masks, grades, wedge-sign parity, and the 128-generator cap `MAX_BASIS_DIM` |
| `engine/terms.rs`, `engine/multivector.rs` | canonical zero-eliding term maps and the metric-free operators |
| `engine/product.rs` | blade-level Chevalley and orthogonal products on `Metric`, plus the `reduce_word` test oracle |
| `engine/algebra.rs` | the algebra context: multivector `mul`, wedge, reverse, grade parts, `pow`, graded tensors, embeddings |
| `engine/inverse.rs` | `multivector_inverse`, a unit-pivot solve over the full blade basis |
| `versor.rs` | versors and Pin actions, contractions, duals, grade involution, conjugation, `versor_inverse`, even subalgebra, meet |
| `spinor_norm.rs` | raw multiplicative versor norms and grade parity |
| `spinor.rs` | idempotent-generated left ideals (not guaranteed minimal) with a complete left-regular fallback; characteristic two uses blade idempotents |
| `blade.rs` | blade analysis: decomposability tests and factorization (`is_blade`, `blade_subspace`, `factor_blade`) |
| `outermorphism.rs` | linear maps, their exterior extension, and determinants |
| `frobenius.rs` | Galois/Frobenius linear maps and outermorphisms |
| `cga.rs` | conformal and projective constructions requiring suitable scalar inverses |
| `hopf.rs`, `divided_power.rs` | the exterior Hopf algebra and the separate divided-power algebra |

## Metric contract

For generators `e_i`:

```text
e_i^2             = q_i
e_i e_j + e_j e_i = b_ij
e_i e_j           = e_i wedge e_j + a_ij    (i < j, general metric)
```

`q`, `b`, and `a` are independent stored data. In characteristic two, `b` is
alternating but `q` need not vanish; collapsing them silently changes the
algebra. Build metrics through `Metric::new`, `diagonal`, `grassmann`, or
`general`. Keys for `b` and `a` use `i < j`.

## Operation placement

- Metric-free additive operations and wedge live on `Multivector<S>` and may
  use operators (`+`, `-`, unary `-`, `&`).
- Metric-dependent operations live on `CliffordAlgebra<S>`:
  `alg.mul`, contractions, reverse/conjugation, duals, inverses, and powers.
- Use `alg.pow(&x, n)` for geometric powers. Scalar power and multivector power
  are separate APIs.

## Invariants and deliberate boundaries

- Wedge signs and product signs use `S::neg`; generic sign and product code
  never injects a literal `-1` or branches on characteristic. Characteristic
  checks belong only to constructions with a genuine characteristic
  precondition (spinor idempotents, CGA, divided-power embeddings, `reverse`
  on a general-bilinear metric).
- Orthogonal characteristic-two generators commute when `b` is zero. Set a
  nonzero polar entry to obtain a noncommutative example.
- General-bilinear characteristic-zero classification transports through the
  antisymmetric gauge. Characteristic two rejects nonzero `a` where that
  transport is unavailable.
- `versor_inverse` needs `v ṽ` to be a pure scalar with a representable
  inverse. `multivector_inverse` is the general unit-pivot solve: it inverts
  non-versors such as `1 + e0` with `e0^2 = -1`, but a versor whose norm is a
  non-monomial surreal defeats both.
- Characteristic-two spinors do not use `1/2(1+w)`. Preserve the blade-idempotent
  path and regular-representation fallback.
- `divided_power.rs` is a parallel algebra, not a view of the exterior/blade
  engine.
- `Ordinal` products inherit the scalar layer's checked Kummer boundary.
- Keep basis dimensions and masks within the existing width contract.

## Verification

Any product or metric change needs a focused regression plus the independent
oracles:

```sh
cargo test associativity_
cargo test general_product_reproduces_reduce_word_when_a_empty
cargo test -p ogdoad
cargo clippy -p ogdoad --all-targets -- -D warnings
```

If a public operation or rendering changes, also build the Python feature,
regenerate/check stubs, and run `demo.py`.
