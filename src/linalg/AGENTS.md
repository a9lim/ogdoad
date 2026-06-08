# AGENTS.md — `src/linalg/`

Crate-private shared linear algebra, deliberately placed BELOW the mathematical
pillars rather than exposed as a public API. `mod.rs` is `pub(crate)` only.

- **`field.rs`** — Gaussian solve / `inverse_matrix` / unit-pivot nullspace over a
  `Scalar` field. Used by `clifford::multivector_inverse`, blade analysis, and
  `inverse_outermorphism`.
- **`f2.rs`** — nim-field row rank for F₂/F_{2^k}-style Dickson computations.
- **`integer.rs`** — exact integer linear algebra over ℤ:
  - `normalize_relation_rows` (the crate's row **Hermite normal form**: increasing
    leading columns, positive pivots, zeros below each pivot, above-pivot entries
    reduced mod the pivot) + `reduce_integer_vector` — the original consumers are the
    game exterior algebra's lattice quotient (`games/game_exterior.rs`).
  - `ext_gcd` (Bézout `a·x + b·y = gcd`) and `smith_normal_form` (invariant factors
    `d₀ | d₁ | …` via unimodular `ext_gcd`-based row/column combines; `∏ dᵢ = |det|`,
    cokernel `ℤⁿ/Mℤⁿ ≅ ⨁ ℤ/dᵢ`) — added for the integral-lattice layer
    (`forms/lattice.rs` reads the discriminant group off SNF). M3 (`forms/genus.rs`)
    will add a dedicated HNF entry point when it needs basis-level Hermite form.

This module is matrix-heavy and walks index-parallel arrays; the crate-level
`#![allow(clippy::needless_range_loop)]` in `lib.rs` covers it (explicit indices
read clearer than iterator adapters when the body indexes several arrays by the
same `i`).
