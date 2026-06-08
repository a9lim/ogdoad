# AGENTS.md — `src/linalg/`

Crate-private shared linear algebra, deliberately placed BELOW the mathematical
pillars rather than exposed as a public API. `mod.rs` is `pub(crate)` only.

- **`field.rs`** — Gaussian solve / `inverse_matrix` / unit-pivot nullspace over a
  `Scalar` field. Used by `clifford::multivector_inverse`, blade analysis, and
  `inverse_outermorphism`.
- **`f2.rs`** — nim-field row rank for F₂/F_{2^k}-style Dickson computations.
- **`integer.rs`** — integer-relation row normalization + vector reduction for the
  game exterior algebra's lattice quotient (`games/game_exterior.rs`).

This module is matrix-heavy and walks index-parallel arrays; the crate-level
`#![allow(clippy::needless_range_loop)]` in `lib.rs` covers it (explicit indices
read clearer than iterator adapters when the body indexes several arrays by the
same `i`).
