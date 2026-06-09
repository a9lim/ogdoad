# ROADMAP — cross-domain connections

This file is the *ambition* document: cross-pillar bridges worth building before
or shortly after the first public release. It is deliberately distinct from
`OPEN.md`:

- **`OPEN.md`** holds *genuine research problems* — things with no known answer
  (the natural Gold-quadric game rule, a game-native quadratic deformation of
  `GameExterior`, transfinite nim excesses past the verified table, and the
  transfinite Arf/Witt question for ordinal-nimber coefficients).
- **`ROADMAP.md`** (this file) holds *buildable bridges* — connections between the
  four mature pillars whose mathematics is largely standard. The first
  computational pass for all four now exists in the codebase; this document keeps
  the mathematical contract, the implemented surfaces, and the remaining honest
  boundaries in one place. Where a bridge brushes against an open question, it says
  so and points back to `OPEN.md`.

Use the project's claim-level discipline (`AGENTS.md` → "Claim levels and
non-claims") when these land: label each piece **standard math** / **implemented
and tested** / **interpretation** / **open**.

## Why these four

The five pillars currently connect like this:

```
            scalar ───coefficients──── clifford
              │  ╲                        │
        Hackenbush╲  trace_form/Gold      │ classifies
        Turning-  ╲      (forms)          │
         Corners   ╲        │             │
              │     ╲       │             │
            games ──Gold/Arf,──── forms ──┘
                    tropical       │
                    thermography   │
                                integral
```

Before this bridge pass, four edges were conspicuously **missing or partial**:

1. **`integral ↔ clifford` had no computational seam.** The lattice pillar and the
   Clifford engine now meet through `IntegralForm::clifford_metric*` and
   `integral::DiscriminantForm`. → **Bridge A.**
2. **The char-2 classifier spanned only one coefficient field.** It now classifies
   both `Nimber` and supported `Fpn<2,N>` metrics through the Arf façade. →
   **Bridge B.**
3. **`scalar` Galois theory and `clifford` outermorphisms were latent twins.** New
   Frobenius linear-map constructors feed the outermorphism spectral machinery. →
   **Bridge C.**
4. **The `No ↔ On₂` mirror was incomplete at the Clifford layer.** `Ordinal` now
   implements the checked/panic-on-escape `Scalar` surface, so
   `CliffordAlgebra<Ordinal>` builds and tests. → **Bridge D.**

Building the four closes the pillar graph: every pair of pillars that *can* talk
(modulo the game-group-isn't-a-ring constraint) then does.

---

## Bridge A — Lattice ↔ Clifford ↔ Brauer–Wall, via Milgram's Gauss sum

**Pillars:** `forms/integral/` ↔ `clifford/` ↔ `forms/witt/` ↔ `forms/char0`.
**Claim level:** standard math (Milgram/van der Blij; Conway–Sloane) made
computational. The headline bridge — it proves the project's spine crosses pillars.

### The mathematics

For an **even** integral lattice `L` (Gram `G`, so `G[i][i]` even), three objects
now meet in `integral/lattice.rs` and `integral/discriminant.rs`:

- the **signature** `σ = p − q`, computed by exact rational diagonalization,
- the **dual** `L# = G⁻¹L`, using the exact `Rational` inverse already used by `level`,
- the **discriminant group** `A_L = L#/L ≅ ⨁ ℤ/dᵢ`, `|A_L| = |det G|`, exposed
  through invariant factors and represented computationally as `Z^n / GZ^n`.

The bridge datum is the **discriminant quadratic form**

```text
q_L : A_L → ℚ/2ℤ,   q_L(x + L) = xᵀ G x   (mod 2ℤ),   x ∈ L#
b_L : A_L × A_L → ℚ/ℤ,   b_L(x,y) = xᵀ G y   (mod ℤ)
```

well-defined precisely because `L` is even. Its **Gauss sum**

```text
γ(q_L) = |A_L|^(−1/2) · Σ_{x ∈ A_L} exp(π i · q_L(x))
```

is a unit complex number, and **Milgram / van der Blij**:

```text
γ(q_L) = exp(2π i · σ / 8)
```

So the discriminant Gauss-sum **phase is the signature mod 8** — the *same* `ℤ/8`
that `witt/brauer_wall::bw_class_real` computes as the Bott index `(q−p) mod 8`,
that the char-0 8-fold table cycles through, and that makes `E₈` (signature 8 ≡ 0,
trivial `A_L`, `γ = 1`) the rank-8 even unimodular lattice. The bridge turns the
existing prose ("E₈ is where Bott and the lattice world coincide", `root_lattices.rs`)
into a theorem with a computation.

There is a **free internal oracle**: `genus.rs` already computes the `p=2` *oddity*
(trace mod 8), and the Conway–Sloane oddity formula `σ ≡ oddity − Σ_p p-excess
(mod 8)` must agree with the Milgram phase. Two independent routes to `σ mod 8`,
cross-checking each other.

### Implemented surface

- `integral/lattice.rs`
  - `IntegralForm::signature(&self) -> (usize, usize)` diagonalizes `G` over `ℚ`
    and counts signs of the rational pivots, so indefinite lattices are supported.
  - `IntegralForm::clifford_metric(&self) -> Metric<Rational>` — the warm-up rung:
    `q[i] = G[i][i]`, `b[(i,j)] = 2·G[i][j]`. Feeds `CliffordAlgebra<Rational>` and
    `classify_real`. `E₈ → Cl(8,0) → M₁₆(ℝ)`. Also a mod-2 reduction
    `clifford_metric_f2(&self) -> Option<Metric<Nimber>>` for even lattices,
    using `Q/2 mod 2` on the diagonal and `G_ij mod 2` off-diagonal.
- `integral/discriminant.rs`
  - `DiscriminantForm { group, reps, gram_inv }` is built from a nonsingular even
    `IntegralForm` using the standard `A_L ~= Z^n / GZ^n` presentation. The
    representative enumeration uses normalized integer relation rows rather than
    extending Smith normal form with transform matrices.
  - `quadratic_value_mod2`, `bilinear_value_mod1`, `GaussSum::phase_mod8`, and
    `milgram_signature_mod8() -> Option<i128>` make the finite quadratic module
    executable.
  - `verify_milgram(lattice) -> Option<bool>` compares the Gauss-sum phase to the
    exact signature and to the independent Conway-Sloane oddity route in `genus.rs`.

### Oracles / tests

Implemented tests cover `A_n`, `D_4`, `E₈`, `E₈ ⊕ E₈`, odd-lattice rejection, exact
signature on indefinite forms, and the rational / char-2 Clifford metric rungs.
The Milgram phase is checked against the exact signature and genus oddity route.

### Scope / caveats

- The clean Milgram statement is for **even** lattices. Odd (type-I) lattices need
  the oddity-corrected version; ship even-only first, document the boundary, and
  lean on the existing `genus.rs` oddity for the odd case rather than duplicating.
- The Gauss sum is an algebraic number; we compute it in `f64` and verify
  `|γ| = 1` + phase `= σ·45°`. An exact cyclotomic representation is a nice-to-have,
  not required for the check.

---

## Bridge B — the char-2 Arf classifier over the `Fpn<2,N>` fields

**Pillars:** `clifford/` (over `Fpn<2,N>`) ↔ `forms/char2/`.
**Claim level:** implemented-and-tested (standard Arf theory over finite char-2
fields); the *bridge* is new code, the math is classical.

### What landed

`CliffordAlgebra<Fpn<2,3>>` — a Clifford algebra over **F₈** (degree 3, which the
`u128` nimber backend cannot reach: it only holds subfields of 2-power degree) —
now builds **and** classifies. `Nimber` keeps its optimized `nim_trace` path, while
supported `Fpn<2,N>` fields use the same symplectic-reduction algorithm over
generic scalar operations plus the absolute trace.

### Implemented surface

- `char2/arf.rs`
  - `arf_char2<F: FiniteChar2Field>(metric) -> Option<ArfResult>` runs generic
    char-2 symplectic reduction over `Fp<2>` / `Fpn<2,N>`.
  - `arf_fpn_char2<const P, const N>(metric)` is the const-generic façade helper:
    it returns `None` unless `P = 2` and the extension polynomial is supported.
  - `ArfResult::arf` and the Artin-Schreier class are carried as `u128` bits, in
    line with the repo-wide integer-width policy.
- `classify.rs`
  - `Fpn<P,N>` now classifies to `FiniteFieldClass::{Odd, Char2}`, so the same
    monomorphized façade works for odd extensions and characteristic-2 extensions.
  - `WittClassify`, `IsometryClassify`, and `BrauerWallClassify` dispatch to the
    char-2 Arf invariant when `P = 2`.

### Oracles / tests

Implemented tests cross-check `arf_char2` against `arf_f2` when all entries are in
`F₂`, exercise genuine `F₈` coefficients through the absolute trace, verify
additivity over `⊥`, and brute-force the `F₈` zero-count bias for planes.

### Scope / caveats

Honest non-claim (`AGENTS.md`): this is *not* a new classification theorem for all
char-2 Clifford algebras — it computes Arf/BW for the finite `Fpn<2,N>` fields,
the same status the README states for the implemented finite char-2 legs.

---

## Bridge C — Frobenius as an outermorphism

**Pillars:** `scalar/finite_field` (Galois) ↔ `clifford/outermorphism` ↔
`forms/trace_form`.
**Claim level:** implemented-and-tested (the theorems are standard finite-field
theory); the bridge code and the cross-checks are new.

### The mathematics

The Frobenius `σ : F_{p^m} → F_{p^m}, x ↦ x^p` is `F_p`-**linear**. Pick an
`F_p`-basis (the project has them: `FiniteField` / `CyclicGaloisExtension::basis`),
form the matrix `M_σ`, and feed it as a `clifford::LinearMap<Fp<p>>` to the
outermorphism machinery. Then `outermorphism.rs` computes — char-faithfully, no
sign hardcoded — the full spectral suite of `σ`:

- **Characteristic polynomial.** By the normal basis theorem `F_{p^m}` is a free
  `F_p[σ]/(σ^m − 1)`-module of rank 1, so `char_poly(σ) = xᵐ − 1` (over `F₂`,
  `xᵐ + 1`). A clean, exact prediction `char_poly` must reproduce.
- **Vanishing intermediate exterior traces.** Since `xᵐ − 1` has no middle terms,
  the elementary symmetric functions `eₖ(σ) = tr Λᵏσ` satisfy `e₁ = … = e_{m−1} = 0`
  and `e_m = ±1`. Frobenius has a "flat" exterior spectrum — a striking,
  one-line-checkable consequence (`exterior_power_trace(alg, σ, k) == 0` for
  `0 < k < m`).
- **Determinant** `det(σ) = ∏ (m-th roots of unity) = ±1` — the constant term of
  the char poly; verifiable.

### The tie to `trace_form.rs`

`trace_form.rs` builds the **Frobenius-twisted** form `Tr_{E/F}(x · σᵏ(x))` (the
norm form over `Surcomplex`, the Gold form over the nim-fields). The trace itself
is `Tr = 1 + σ + σ² + … + σ^{m−1}` — a *polynomial in the very `σ` this bridge
realizes as a linear map*. So the bridge gives an outermorphism-level reading of
the trace-form construction: lift `σ` to the exterior algebra of `E`-as-`F`-space,
and the `Λᵏ` action organizes the twisted forms across grades. This is a genuine
conceptual link, not just a spectral cross-check.

### Implemented surface

- `clifford/frobenius.rs`
  - `CoordinateCyclicGaloisExtension` extends the cyclic Galois basis with a
    coordinate extractor.
  - `galois_linear_map::<E>(k)` and `frobenius_linear_map::<E>()` build
    `LinearMap<E::Base>` from the chosen basis.
  - `nimber_subfield_frobenius_linear_map(m, k)` gives small exact matrices for
    the represented nimber subfields, avoiding a 128-dimensional exterior-power
    computation when a four- or sixteen-dimensional one is the intended oracle.

Tests pin `char_poly = xᵐ ± 1`, the vanishing middle `Λᵏ`-traces, `det = ±1`, and
composition of Frobenius powers over `Fpn<2,m>`, odd-characteristic `Fpn`, and a
small nimber subfield.

### Scope / caveats

Pure cross-domain wiring + verification; no new theorem. Its value is that it makes
three pillars share one computation and gives `trace_form` a structural home.

---

## Bridge D — transfinite char-2 Clifford (`OrdinalAlgebra`)

**Pillars:** `scalar/big/ordinal` ↔ `clifford/`.
**Claim level:** implemented-and-tested for the checked engine/symmetry completion.
Classification of genuinely transfinite coefficients is still out of scope and
tracked in `OPEN.md`.

### The target and the totality boundary

`CliffordAlgebra<Ordinal>` would be the char-2 mirror of `SurrealAlgebra` (the
transfinite char-0 Clifford algebra), completing `No ↔ On₂` at the Clifford layer
exactly as `NimberGame` completed it at the games layer. A metric like
`q = [ω, ω+1]` would carry genuinely **infinite nimber squares**.

`Ordinal` now implements `Scalar`, but the totality issue remains explicit:
`Scalar::mul` is panic-on-escape and `Ordinal::checked_mul` is the non-panicking
mathematical surface. Products inside the source-verified Kummer tower are exact;
products past the verified table or outside the staged segment are rejected.

### The honest design

`Scalar for Ordinal` follows the **`Rational` precedent** (`Rational` is already an
overflow-prone `i128` engine-validation scalar, not the "real" char-0 home — that
is `Surreal`). The `mul` panic message names the verified-tower escape, while
`checked_mul` / `checked_inv` are available for callers that need an explicit
`Option` boundary.

### What it actually adds (be honest)

The finite odd-degree char-2 fields (`F₈`, `F₃₂`, …) are **already** reachable as
Clifford coefficients via `Fpn<2,N>` (and, with Bridge B, classifiable). So the
*genuine* novelty of `OrdinalAlgebra` is narrow but real: **transfinite**
coefficients — `ω`, `ω+1` as squares — the exact char-2 twin of `SurrealAlgebra`'s
`ω`/`ε`. It is a symmetry-completion and a demo of the `No ↔ On₂` mirror, not a new
computational capability over the finite case.

### Classification boundary

This bridge does not try to classify every `Metric<Ordinal>`.

- Purely finite ordinal entries delegate to the existing `Nimber` Arf route.
- Entries in the first transfinite finite window `F_4(ω) = F_64` use the same
  generic symplectic reduction and the six-term absolute trace.
- Larger staged finite fields and genuinely transfinite coefficients return `None`
  for Arf/Witt/Brauer-Wall. The general finite-subfield detector and the
  transfinite classifier are separate work; the latter remains an open problem.

### Implemented surface

- `scalar/big/ordinal/` — `impl Scalar for Ordinal` (panic-on-escape `mul`,
  `neg = id`, `characteristic() = 2`, `checked_mul`, and `checked_inv`).
- `clifford` tests build `CliffordAlgebra<Ordinal>` over `q = [ω, ω+1]`, check the
  Clifford relations, and exercise associativity over the transfinite metric.
- `forms/char2/arf.rs` and the classifier façade expose finite-window
  `Metric<Ordinal>` classification and deliberately return `None` outside it.

---

## Status Snapshot

All four bridges are independently implemented and tested in the Rust core:

- **A:** lattice signature, rational/char-2 Clifford metrics, discriminant forms,
  Milgram Gauss sums, and genus oddity cross-checks.
- **B:** generic finite characteristic-2 Arf classification over supported
  `Fpn<2,N>` fields, wired into classify/Witt/isometry/Brauer-Wall façades.
- **C:** Frobenius/Galois automorphisms as Clifford `LinearMap`s with
  outermorphism spectral tests.
- **D:** `Ordinal` as a checked/panic-on-escape `Scalar`, `CliffordAlgebra<Ordinal>`
  engine tests, and finite-window ordinal Arf classification.

Remaining open edges are not implementation TODOs inside this roadmap: the natural
Gold-quadric game rule, game-native quadratic deformation of `GameExterior`, and
the genuinely transfinite Arf/Witt classifier all stay in `OPEN.md`.
