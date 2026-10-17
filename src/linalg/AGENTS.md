# `src/linalg/` editing guide

Crate-private algebraic and unit-pivot linear algebra shared across the
scalar, Clifford, forms, games, and Weyl pillars. Results are exact when the
scalar backend is exact and inherit a precision backend's semantics otherwise.

| file | responsibility |
| --- | --- |
| `f2.rs` | `nim_rank`: rank of raw `u128` nimber rows over `F_(2^128)` |
| `field.rs` | generic unit-pivot rank, square solves, inverse matrices, and nullspaces |
| `integer.rs` | exact integer relation-row normalization, vector reduction, Smith invariant factors, and gcd/factorization helpers |
| `mod.rs` | crate-private exports |

Rules:

- Keep this module crate-private; public APIs return domain-specific records.
- Validate rectangular dimensions before indexing.
- Use backend-native scalar operations and explicit nonunit-pivot failure.
  Never introduce floating tolerances or silent rank guesses into generic
  elimination.
- Preserve row/column transformation witnesses when an algorithm promises
  them.
- `usize` is appropriate for dimensions and indices; mathematical integer
  entries and public invariants follow the repository's `u128`/`i128` rule.
- Add a small independent matrix oracle or reconstruction test for every new
  elimination path, then run the core test and Clippy gates.
