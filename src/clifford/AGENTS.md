# `src/clifford/` editing guide

This pillar owns the generic multivector engine and metric-dependent geometric
algebra. It must remain pure Rust and generic over `Scalar`.

## Map

| path | responsibility |
| --- | --- |
| `blade.rs` | bitmask blades, grades, wedge signs |
| `engine/metric.rs` | `Metric { q, b, a }` construction and validation |
| `engine/product.rs` | blade and multivector geometric products |
| `engine/{terms,basis,multivector}.rs` | canonical sparse terms and basis operations |
| `engine/{algebra,inverse}.rs` | algebra context, powers, involutions, contractions, inverses |
| `outermorphism.rs` | linear maps and exterior extension |
| `versor.rs`, `spinor_norm.rs` | Pin/Spin actions and norms |
| `spinor.rs` | minimal-left-ideal and regular representations, including characteristic two |
| `frobenius.rs` | Galois/Frobenius linear maps and outermorphisms |
| `cga.rs` | conformal/projective constructions requiring suitable scalar inverses |
| `hopf.rs`, `divided_power.rs` | exterior Hopf and separate divided-power algebras |

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

- Wedge signs and product signs use `S::neg`; never inject a literal `-1` or
  branch on characteristic.
- Orthogonal characteristic-two generators commute when `b` is zero. Set a
  nonzero polar entry to obtain a noncommutative example.
- General-bilinear characteristic-zero classification transports through the
  antisymmetric gauge. Characteristic two rejects nonzero `a` where that
  transport is unavailable.
- `versor_inverse` requires a representable scalar inverse of the spinor norm.
  `multivector_inverse` is the general linear solve and may succeed when a
  finite-support surreal versor inverse cannot.
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
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
```

If a public operation or rendering changes, also build the Python feature,
regenerate/check stubs, and run `demo.py`.
