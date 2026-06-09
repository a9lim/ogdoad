# AGENTS.md — `src/linalg/`

Crate-private shared linear algebra, deliberately placed BELOW the mathematical
pillars rather than exposed as a public API. `mod.rs` is `pub(crate)` only.

Fixed-width arithmetic payloads in this module are `u128`/`i128`; `usize` is only
for matrix dimensions and indices. Keep relation rows, Smith/Hermite pivots, and
integer solver data on the repo-wide width contract.

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
    (`forms/integral/lattice.rs` reads invariant factors off SNF, while
    `forms/integral/discriminant.rs` uses normalized relation rows to enumerate
    `Z^n/GZ^n` representatives).

This module is matrix-heavy and walks index-parallel arrays; the crate-level
`#![allow(clippy::needless_range_loop)]` in `lib.rs` covers it (explicit indices
read clearer than iterator adapters when the body indexes several arrays by the
same `i`).
