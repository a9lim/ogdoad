# AGENTS.md — `src/forms/`

The PILLAR of quadratic forms and their invariants. The organizing principle is
the **characteristic trichotomy**: the classification of a quadratic form
(equivalently, of the Clifford algebra it builds) is *one* theory split three ways
by `char F`. This axis cuts ACROSS the place table that organizes `scalar/`.

> Read `NOTES.md` before touching `char2/`, `quadric_fit.rs`, `char0.rs`,
> `witt.rs`, or anything feeding the open play-semantics question.

`mod.rs` re-exports the legs + `classify` + diagonalize/equivalence + witt/
witt_ring + brauer_wall + padic + adelic + springer + the symplectic/hermitian
"form + involution" siblings, all flat.

## The façade

- **`classify.rs`** — the classifier FAÇADE: `ClassifyForm` + `WittClassify` +
  `IsometryClassify` + `WittDecompose` + `BrauerWallClassify`, keyed on the scalar
  so `metric.classify()` / `.witt_class()` / `.isometric_to()` / `.witt_decompose()`
  / `.bw_class()` pick the right leg **at compile time** (Surreal→CliffordType,
  Fp/Fpn→OddCharType, Nimber→ArfResult, …). Rational & Surcomplex impl
  `ClassifyForm` but not `WittClassify` (their Witt data isn't a single `WittClassG`
  — honest, not a gap).
- **`diagonalize.rs`** — congruence diagonalization (char ≠ 2): `gram`,
  `diagonalize`, `as_diagonal`. Returns `None` in char 2 (nonsingular char-2 forms
  have an alternating polar form and are NOT diagonalizable — use the char-2
  symplectic Arf reduction). This is what lets char0/oddchar classify ARBITRARY
  (non-diagonal) metrics.
- **`equivalence.rs`** — isometry (per backend, via the complete invariant) + Witt
  decomposition (k·H ⊥ anisotropic kernel) over ℝ and F_q.

## The three legs

- **`char0.rs`** — the char-0 Clifford classifier: Cl(p,q) → matrix algebra over
  ℝ/ℂ/ℍ via the 8-fold table (real-closed surreal/rational) and the 2-fold table
  (surcomplex). `classify_real(p,q,r)` / `classify_complex(n,r)` are the bare-
  signature entry points (no metric needed); non-diagonal metrics are diagonalized
  first.
- **`oddchar/`** — odd-characteristic forms (re-exported flat): `field.rs`
  (`FiniteOddField` unifies Fp and Fpn square classes), `invariants.rs`
  (`classify_finite_odd`/`finite_odd_witt`/`discriminant`/`hasse` ≡ +1 over finite
  fields — ONE generic implementation keyed off the trait, Fp and Fpn share the
  path). dim + disc complete.
- **`char2/`** — characteristic-2 invariants (re-exported flat): `arf.rs` (the Arf
  invariant: `arf_f2` F₂ bitmask + `arf_nimber` any nim-field, symplectic reduction
  + trace), `dickson.rs` (`dickson_matrix = rank(g−I) mod 2`, ker = SO;
  `dickson_of_versor` delegates to the generic versor grade parity).

The char0↔char2 classifier **symmetry** (the real 8-fold table mirrored by the
char-2 Arf/Brauer–Wall story) is one of the project's central threads.

## Witt / Brauer–Wall

- **`witt.rs`** — `WittClass`: the Witt group `W_q(F) ≅ ℤ/2` of a finite nim-field,
  Arf-classified. Plus `WittClassG`: the Char0/OddChar/Char2 trichotomy enum (odd-
  char is order-4) with the ring `mul` (Char2 panics — `W_q` is a module, not a ring).
- **`witt_ring.rs`** — the Witt RING: `tensor_form`, Pfister forms, fundamental
  ideal Iⁿ, the eₙ staircase (e0=dim, e1=disc, e2=Hasse). Stabilization per field
  (I²=0 over F_q; infinite ℝ tower via `e_real`). DON'T claim Arf=e2 (char-2
  indexing is Kato's, pinned).
- **`brauer_wall.rs`** — the Brauer–Wall group BW(F): `bw_class_real` (Bott index
  (q−p) mod 8 ⇒ BW(ℝ)=ℤ/8), `bw_class_complex` (ℤ/2), `bw_class_oddchar` (order-4 ≅
  W(F_q), DISCOVERED not asserted). Law = graded_tensor.

## Springer — the discrete-valuation trio (a local–global symmetry)

Three siblings, one per complete valued field, differing in the value group:

- **`springer.rs`** — over the surreals (char 0, residue ℝ). Value group 2-divisible
  ⇒ W(No)=W(ℝ)=ℤ; the ω-adic filtration itself is the novelty.
- **`springer_padic.rs`** — over `Q_p` (char 0, residue F_p). Value group ℤ NOT
  2-divisible ⇒ TWO residue layers survive (`parity_layer`) = W(Q_p)=W(F_p)⊕W(F_p).
- **`springer_laurent.rs`** — over `F_q((t))` (EQUAL characteristic p, residue F_q).
  Two parity layers = W(F_q((t)))=W(F_q)². Odd residue char only; residue char 2
  REJECTED (the char-2 Witt boundary).

## Local–global

- **`padic.rs`** — the GENUINE Hilbert symbol over Q_p (odd-p + p=2 mod-8) — nontrivial
  unlike oddchar's +1 — + Hasse–Minkowski `is_isotropic_q` over ℚ. Oracle: Hilbert
  reciprocity `∏_v=+1`.
- **`adelic.rs`** — local–global rational helpers: `hilbert_product` over all places,
  rank≥3 adelic Hasse–Minkowski breakdown (`isotropy_over_adeles`/`AdelicIsotropy`),
  Brauer local invariant sums. Reuses `padic.rs`.
- **`function_field.rs`** — the **equal-characteristic mirror** of `padic.rs`+`adelic.rs`
  over the global function field `F_q(t)` (`scalar::RationalFunction`). Places
  `FFPlace{Infinite, Finite(π)}` (monic irreducibles + the degree place), the **tame**
  Hilbert symbol `hilbert_symbol_ff` (the odd-`p` `hilbert_symbol_qp` branch with the
  residue Legendre → `χ_κ`; **no `p=2` branch** since `q` is odd), reciprocity
  `hilbert_reciprocity_product_ff`, `is_isotropic_ff`/`is_isotropic_at_place`/
  `isotropy_over_ff_adeles` (Hasse–Minkowski, u-invariant 4 like `Q_p`, but **no
  archimedean place** ⇒ no definiteness condition), and `ramified_places_ff` (even
  count). Names carry `_ff` where `padic.rs` collides (e.g. `hasse_at_place_ff`).
  Exact (the product formula is `deg`-counting); odd residue char only — the
  `springer_laurent` boundary. Cross-checked against `springer_decompose_laurent`.

## The "form + involution" siblings

- **`symplectic.rs`** — alternating forms: `SymplecticForm`, `hyperbolic`,
  `direct_sum`, `classify` (rank + radical_dim — the complete invariant, char-
  uniform). `classify_symplectic(gram)` convenience. The char-2 polar form of a
  nonsingular quadratic form lives here.
- **`hermitian.rs`** — Hermitian forms over Surcomplex (the involution `conj()` the
  symmetric leg never used): `HermitianForm` (conj-symmetric Gram), unitary
  congruence diagonalize → real diagonal, signature (Sylvester, the complete
  invariant = U(p,q)). `from_skew` handles the skew-Hermitian case via mult by i.

## Field invariants + the game bench

- **`invariants.rs`** — numeric FIELD invariants the Witt ring implies: level/Stufe
  s(F), pythagoras_number, u_invariant, is_sum_of_n_squares — computed over finite
  F_p (level≤2, u=2); ℝ/Q_p textbook constants documented.
- **`quadric_fit.rs`** — the "is this P-set a quadric?" research BENCH (split from the
  char2 classifier): `fit_f2_quadratic` (Gaussian elim over the 2^k membership
  equations) + `QuadricFit` + `is_genuinely_quadratic`. The instrument the game
  probes / misère_quotient / octal_hunt / loopy_quadric feed P-positions into —
  distinct from the classifier.

## Things that look like bugs but are not (forms layer)

- **`diagonalize`/`as_diagonal` return `None` in characteristic 2.** Not a bug: a
  nonsingular char-2 form has an alternating polar form and is not diagonalizable.
  The char-2 leg classifies via the symplectic Arf reduction (`char2/`) on the full
  (q, b) metric instead.
- **The odd-char Hasse invariant is ≡ +1** over a finite field — genuinely trivial
  there, unlike the p-adic Hilbert symbol in `padic.rs` (where Hasse does real work).
- **Rational & Surcomplex impl `ClassifyForm` but not `WittClassify`** — their Witt
  data isn't a single `WittClassG`. Honest, not a gap.
