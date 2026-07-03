# CORRECTNESS.md (the verification-status ledger)

The verification-status ledger: which shipped claims are **machine-verified**, which
are **source-pinned**, and which are **asserted-but-unproven** — valued like
[`COMPLETENESS.md`](COMPLETENESS.md) — a game value `g` on a pillar blade `e_B` (`e_s`
scalar, `e_c` clifford, `e_f` forms, `e_i` integral, `e_g` games, `e_o` ogham, `e_y`
py). Claim level **interpretation/engineering**: each entry is a status call on the
existing verification surface, checked against the actual oracles, not vibes. Numbers
≈ focused days to close a verification gap; `±n` flags an a9 scope call; `↑` is worth
less than any number but strictly positive; `*n` is real, on-thesis, unscheduled.

The standing verification surface is the baseline this ledger reads against: `cargo
test` (the `proptest` suites `tests/scalar_axioms.rs` and `tests/clifford_axioms.rs`,
the `associativity_*` oracles, and `general_product_reproduces_reduce_word_when_a_empty`),
the adversarial stdlib harnesses `experiments/echo_solver.py` and
`experiments/linking_game.py`, and the source-pinned finite tables inventoried in
[`TABLES.md`](TABLES.md). Its aesthetic sibling — structural/stylistic findings rather
than soundness — is [`CONSISTENCY.md`](CONSISTENCY.md).

---

## Status — audited 2026-07-02 (Rust core only; py/ and ogham/ out of scope)

Baseline at HEAD `30588ec`: `cargo test` green (913 tests — 895 lib + 18 across the
integration suites), `cargo clippy --all-targets` clean. Method: seven per-pillar
claim→oracle inventories, sixteen independent adversarial math audits over the dense
clusters (every formula, curated table, and algorithm checked against standard
references — Lam, SPLAG, ONAG, Serre, Winning Ways, …), and lead verification of every
error-grade finding against source.

**Headline: no mathematical error was found in any shipped computed value.** Every
error-grade finding below is a wrong *contract*, not a wrong number — a doc claiming
more than the code delivers, an unguarded boundary, or a test pinning less than its
name implies. Two pins were also *upgraded* by the audit itself: the OEIS A380496
excess table was re-fetched live and hand-diffed (all 126 rows match upstream — the
transcription is now attested twice), and the BW16 group orders were independently
re-derived from `2^{1+8}·#O⁺(8,2)` (the constants are right; they carry no in-repo
oracle, see `rank16-pins`).

## What holds (the baseline — don't dilute it on any cleanup pass)

- **The cross-validation spine is real.** `verify_milgram` checks three independently
  computed routes to `signature mod 8` on every call (exact FQM phase / `f64` Gauss sum
  / Conway–Sloane oddity) over an 11-lattice zoo; `nikulin_genus_iff…` pins two
  independently implemented algorithms (p-adic Jordan symbols vs finite-group
  isomorphism search) against each other; the Clifford engine is pinned to the
  brute-force `reduce_word` oracle on all three product paths; the ordinal tower's new
  generator path is cross-checked exhaustively (64×64) against the old
  `φ_{ω+1}`-polynomial path; `LocalQp`/`Qq`/`WittVec` each have an element-for-element
  cross-backend oracle.
- **Reciprocity is the gold oracle at every leg**: brute-forced `∏(a,b)_v = +1` over ℚ,
  the multiplicative sweep over `F_5(t)`, the additive XOR sweep over `F_2(t)`/`F_4(t)`,
  and the full-strength `n ∈ {2..5}` constant-extension sums over `F_q(t)`.
- **Source pins that were re-verified this audit**: A380496 (live b-file diff, 126/126),
  `LEECH_AUT_ORDER` / `D16_PLUS_AUT_ORDER` / the ADE data (recomputed), the 2-adic
  canonical-symbol Sage examples in `genus.rs` (literal pinned output — the one
  *executed* Sage oracle in the crate).
- **The games wing is honestly two-implementation tested where it claims to be**:
  lexicode greedy-vs-production-vs-mex three ways, Tartan against factored nim-product,
  canonical forms against the surreal round-trip (`dyadic_birthday == Game::birthday`,
  a genuine cross-pillar oracle). One caveat now on record: `thermograph_via_tropical`
  is *documented and tested as a naming bridge over the shared recursion* — it is not,
  and does not claim to be, an independent implementation of cooling. Don't cite it as
  a cross-check.

---

## numbers — contracts to fix (the error-grade findings, all small)

### ½·e_c: `spinor-norm-char2-claim`
**The char-2 spinor-norm doc claims a reduction that isn't the invariant.**
`clifford/spinor_norm.rs:9,52-54,63-65` states that the raw norm `N(v) = ⟨v ṽ⟩₀ = ∏q(vᵢ)`
read "modulo ℘ (char 2)" is the spinor-norm invariant in `F/℘(F)`. False: `F/℘(F)` is an
*additive* quotient and the raw norm is a *product* — rescaling a versor by `λ`
multiplies `N` by `λ²`, which shifts the ℘-class arbitrarily (`x² ≡ x mod ℘`, not `0`).
Concretely `τ_v∘τ_v = id` has versor `v·v = Q(v)·1` with `N = Q(v)² ≡ Q(v) mod ℘`, while
the identity's invariant must be `0` — so the recipe isn't even well-defined on `O(Q)`.
The standard char-2 invariant (Wall/Dye) is `Σ Q(vᵢ) mod ℘` over a *vector factorization*.
The code is fine (it returns the raw norm and the module doc's ¶2 already half-says
this); the fix is rewording the three doc sites, plus the honest additive invariant as
a buildable — see `COMPLETENESS.md` → `char2-spinor-norm`. Related asserted-only gap:
no Nimber-backed test ever calls `spinor_norm`/`classify_versor` (only the Dickson half
is char-2-tested).

### ½·e_i: `modular-overflow`
**The one silent-cap violation in the integral wing.** `modular.rs:32` `sigma_power`
runs unchecked `i128::pow` *before* its `checked_add` guard: `d^11` for `d ≳ 2600`
overflows `i128`, so `eisenstein_e12` past ~`q^2600` panics in debug and **silently
wraps in release** — under an "exact q-expansions" claim with no documented term cap.
Fix: `checked_pow` + the house `Option`/documented-cap boundary. Same file's neighbor
`mass_formula.rs:118-135`: the doc contract says `B_1 = −1/2` but the Akiyama–Tanigawa
loop yields `+1/2` (trace `n=1`: `a[0] = (1 − 1/2)·1`). All shipped consumers use even
indices, so nothing downstream is wrong — fix the stated convention (or negate `n=1`).

### ½·e_s: `p-adic-guard-gap`
**The `assert_supported_params` discipline stops short of the newest p-adic backends.**
`Zp`/`Qp`/`Fpn`/`Laurent` all validate their const-generics at every `Scalar` entry
point, each with an `invalid_parameters_are_rejected` test. `WittVec<P,N,F>` has no
guard at all (`WittVec::<4,3,1>` silently runs `Z/64` arithmetic and calls itself
`W_3(F_4)`; `F = 0` makes `zero() == one()`); `Qq<P,N,F>` likewise; `Ramified<S,E>` has
only a `debug_assert!(E >= 2)` inside `pi()` (with `E = 1`, `Valued::uniformizer` is an
index-out-of-bounds; `E = 0` is a non-unital "ring"). Compounding: `Qq::mul`/`inv` use
*unchecked* `val + rhs.val` / `-self.val` where sibling `Qp` deliberately uses
`checked_add` with a panic message (`qp.rs:237-240`). Give all three the guard + test +
checked valuation arithmetic. (The bare `pub` payload fields that let a struct literal
bypass any future guard are ledgered as taste — `CONSISTENCY.md` →
`encapsulation-stragglers`.)

### ½·(e_s∧e_c): `nullspace-skip`
**`unit_pivot_nullspace` gives up on columns it could skip.** `linalg/field.rs:93-98`
returns `None` the moment a column has a nonzero non-unit and no unit pivot — but a
kernel basis may need no division by that entry at all: `[[2, 1]]` over `Integer` has
kernel `(1, −2)` via the unit pivot in column 1, yet the doc's justification ("the point
where field Gaussian elimination would have to divide by a nonunit") is false there.
Failure direction is conservative (a spurious `None`, never a wrong basis; field
backends unaffected since nonzero ⇒ unit), but ring/precision callers can be denied
computable kernels. Fix: skip the column, pivot later, fail only if a leftover row is
nonzero solely in unskippable columns; add the `[2,1]` test. Also: `solve`/
`inverse_matrix` in the same file have zero same-file tests (all coverage is
cross-pillar incidental) — add the local round-trip oracle while in there.

---

## numbers — verification gaps (the claim is believed true; the oracle is missing)

### 1·e_s: `alpha-row-pins`
**"Exact for `u ≤ 709`" is machine-verified for `u ≤ 47`.** The *integer* excess table
is source-pinned for all 126 rows (twice, now). But the *ordinal reconstruction*
`alpha_ordinal(u)` — the value that actually participates in nim-multiplication — has
per-row value checks only for the first 14 primes (`tower.rs:467-494`) plus a genuine
independent certificate at `u=47` (`ordinal_excess_probe.py`); at `u=53` only
*definedness* is asserted (`tower.rs:704`), and rows `53..709` (89% of the table) have
no value oracle at all. One general algorithm, so a bug would likely break the tested
rows too — but this is precisely a bounded observation presented as a general fact.
Close cheaply: the probe already independently certifies `u ∈ {47, 89, 179}`; lift
those into `dimuro_rows…`-style value pins and sample a few more rows, and/or vendor
the b-file for the full-diff the test's own header comment already (falsely) claims to
do. Also narrow the prose (here, root `AGENTS.md`, `OPEN.md`) to say which half is
pinned to what depth.

### 1·e_f: `bw-ff-sweep`
**The function-field Brauer–Wall correction table is untested at residues 0,5,6,7.**
The rational leg's `clifford_correction` is swept at *all eight* residues against an
independently re-derived table plus two genuinely independent Clifford-side oracles.
Its equal-characteristic twin `clifford_correction_ff` (`brauer_wall.rs:626-653`) is
only ever reached with forms of length 2–4 — the `n mod 8 ∈ {0,5,6,7}` arms of a
hand-ported match table have zero coverage. Port the rational sweep. While in the file:
`witt/mod.rs:6` says Char2 `mul` "panics" — it returns
`Err(WittClassGError::Char2NotARing)`; and `cyclic.rs:338`'s "the full local Brauer
group" should read "the `n`-torsion `Br(K)[n]`" (a fixed degree-`n` unramified class
generates `(1/n)ℤ/ℤ`, not `ℚ/ℤ`).

### 1·e_i: `rank16-pins`
**The rank-16 wing's two headline constants and its closure test under-pin.**
(a) `BW16_AUTOMORPHISM_GROUP_ORDER`/`BW16_REAL_CLIFFORD_GROUP_ORDER`
(`clifford_lattices.rs:18-26`): the only test checks the two hand-entered constants are
consistent *with each other* (`× 2`). Neither is derived or sourced in-repo. Pin the
closed form `2^{1+8}·#O⁺(8,2) = 512 · 348,364,800 = 178,362,777,600` as a test
(Nebe–Rains–Sloane convention), with the index-2 relation giving the other. (b) The
Kneser rank-16 report discards its generated labels
(`even_unimodular_kneser_report`'s `_generated_class_labels`) and re-derives the
public ones from the static table — `rank16_report_finds_both_neighbor_classes…` would
still pass if neighbor generation never actually found `D16+`. Assert the *generated*
set equals the static labels. (c) `codes.rs`'s `D16_PLUS_AUT_ORDER` test is a tautology
(re-evaluates the defining formula `2^15·16!`); the real oracle is `theta.rs`'s
Siegel–Weil identity — this ledger records that pointer so nobody mistakes the
tautology for the pin.

### ½·e_i: `nikulin-negative-witnesses`
**The Nikulin/fqm machinery's failure branches are never forced.** No test produces
`NikulinExistenceObstruction::{OddPrimeDeterminant, TwoAdicDeterminant}` — a
square-class bug in `same_square_class_odd`/`…_2_up_to_sign`/`p_adic_discriminant`
would survive the suite; `DiscriminantForm::is_isomorphic`'s positive DFS is never
exercised on two *differently presented* isomorphic nontrivial forms; `fqm_witt_class`'s
full Wall/Nikulin normal-form claim rests on four small smoke cases (no noncyclic
anisotropic core, no exponent-8 two-primary block, no external Kawauchi–Kojima-style
row). ~150 lines of case logic at `genus.rs`/`discriminant/form.rs` coverage standards
would want an order of magnitude more.

### ½·e_f: `char2-decomp-coverage`
**Three char-2 forms surfaces ship with zero or wrong-branch coverage.**
`isometric_finite_char2` (`equivalence.rs:84`) — the generic `FiniteChar2Field` entry
point named in the pillar AGENTS — has no in-tree caller outside the Python binding.
`Char2WittDecomp`'s documented `radical_anisotropic: true` caveat (fields that are
basis-dependent, not isometry invariants) is never constructed by any test. And
`poly_factor.rs`'s char-2 equal-degree splitter is never forced to actually *split*
(the char-2 test input reduces to a single factor before the trace-splitter fires) —
one product of two distinct irreducible quadratics over `F_4` closes it.

### ½·(e_g∧e_f): `arf-vs-constant-bias`
**The quadric bench reports the homogeneous Arf as if it were the set's win-bias.**
`fit_f2_quadratic` returns `arf` of the homogeneous part while the fit may carry
`constant = true` — and the zero-set bias of `c + Q₀` *flips* with the constant
(`Q₀ = x₀x₁`: 3 zeros; `1 + Q₀`: 1 zero — same homogeneous Arf). The examples
(`misere_quotient.rs:59-63`, `bent_route.rs:45-52`) print `fit.arf.arf` directly as the
P-set bias. Add the honest `bias = arf XOR constant` (nonsingular case) helper + pin,
and route the example prints through it. Sibling probe gap: `loopy/mod.rs:324-333`'s
`quadric_probe_reads_both_sets` prose describes a draw-cycle rule but the rule
constructs no draws and `_draw_fit` is never read — the Draw-set branch of
`loopy_quadric_probe` is untested. (The `p_set_as_f2` group-axiom check is already
ledgered — `COMPLETENESS.md` → `octal-hunt-reframe`; this audit's finding strengthens
its motivation: the helper currently accepts non-group monoids.)

### ½·e_c: `clifford-test-gaps`
**Grouped engine-layer oracles that pin less than they name.** `even_subalgebra`'s only
test uses the all-ones metric, which cannot distinguish `fᵢ² = −qᵢq_p` from a hardcoded
`−1`, and neither documented `None` branch is tested; the char-2 spinor
nonsingularity gate (`char2_polar_rank`) is only ever exercised at dim 2 — the
pop-and-pair elimination has dim-≥4 failure modes no test reaches; `hopf.rs` pins
counit/coassociativity/antipode but not the bialgebra compatibility
`Δ(a∧b) = Δ(a)∧Δ(b)`; `Metric::direct_sum`'s `b`/`a` index-shift is untested for any
nonzero off-diagonal; the documented Surreal `versor_inverse` non-monomial `None`
(AGENTS "looks like a bug") has no regression test.

### ½·e_g: `partizan-oracle-breadth`
**The partizan wing's deepest claims rest on narrow windows.** `canonical()`'s
uniqueness/equality claim (canonical_string used as a value key) has no small-birthday
exhaustive sweep — a day-≤3 universe enumeration checking `canonical_string` equality
⟺ value equality would pin it; `norton_multiply`'s non-integer-unit recursion has no
external oracle case (Winning Ways worked example); `hackenbush.rs`'s "every blue/red
graph is a number" is tested only on strings — add one branched/cyclic blue-red oracle.
Also surface `GameExterior::new`'s default relation-search incompleteness (bound 3,
cap 100 — three generators already exceed the exhaustive box; callers must check
`relation_search_complete`, and no test shows the default-incomplete case).

---

## switches (a9's move first)

### ±1·e_f: `aj-second-engine`
**The char-2 Aravire–Jacob leg has no independent oracle — by structure, not neglect.**
Every other local leg is cross-checked against a second engine
(`springer_decompose_laurent` ↔ the function-field place layer; Milnor ↔ Springer over
`Q_5`), but the AJ decomposition's expected values are hand-worked applications of the
paper's formulas ("Codex source-pinned" in the test comments), because the odd-residue
engine *rejects* residue char 2 by design — there is no second implementation in the
repo to check against. This is the most intricate code in the local–global wing
(Hensel-series lifting, P-adic digit arithmetic in `asnf.rs`). The decision: build an
independent naive verifier (brute-force isotropy over truncated power series, or a
from-scratch second ASNF) as a test-only oracle, or accept hand-worked oracles as the
documented boundary. Either way, one wording pass is owed now: the module's
"source-pinned" language means "paper-derived worked example," which is *weaker* than
this ledger's source-pinned (external data pin, à la A380496) — reserve the term.

---

## ups (one-line pins; cheap, strictly positive)

### ↑·(e_s∧e_f∧e_i∧e_g∧e_c): `one-line-pins`
Grouped cheap oracles, each a line or three:
- `Nimber::from_int(3) == *1, from_int(4) == *0` — the doc's own worked example
  (defended at two sites against a future bit-cast override) has no regression test.
- `ORDER_FACTORS`: product is pinned; per-factor primality isn't — one
  `is_prime_u128` sweep line.
- Milnor second residue: the `p ≡ 3 (mod 4)` signed-discriminant twist has no direct
  Springer cross-check (only `p = 5`); add a `p = 3` case.
- Weyl versors: only `A_2`/`D_4`/`E_8` tested — sweep `E_6`/`E_7` and a couple of
  `A_n`/`D_n` ranks through `weyl_versor_report`.
- Extraspecial transvection intertwiners: the `Q(a) = 1` branch (`extraspecial.rs:604`,
  `λ = 1` vs `λ = i`) is never verified — `DONE.md`'s "verified" claim currently
  overreaches; one anisotropic-vector `verify_transvection_intertwines` call.
- `WittVec::teichmuller` for `F > 1`: multiplicativity (`τ(x)^q = τ(x)`) is tested only
  at `F = 1`; the `F > 1` claim is unconditionally stated.
- `adele_prec`'s overflow rationale ("so `(p^k)²` never overflows") describes a
  constraint `LocalQp::mul` was specifically rewritten (via `mul_mod_u128`) not to
  need — stale comment, possibly a needlessly tight cap.
- `FunctionFieldPlace::Finite` accepts non-irreducible payloads and silently computes
  meaningless symbols (`try_kappa_order` assumes `q^deg(π)` is a field order) — assert
  or document the precondition at the symbol entry points.
- Doc one-liners verified false as written: `oddchar/mod.rs:11` "computed the honest
  way by searching for a representing vector" (the shipped path returns `Some(1)`
  directly — correct, by Wedderburn, but not by search); `classify.rs:203`'s "may mean
  a non-diagonal char-2 form" example (non-diagonal char-2 *is* in-domain via Arf
  reduction); `tests/scalar_axioms.rs:164`'s "< ω^ω is where nim-multiplication is
  implemented" (the tower reaches far past it); `misere.rs:410`'s Dawson's-chess
  `0.137` aside (unpinned; fine, but it's the one uncited octal name).

### ↑: `proptest-depth-note`
Default proptest depth is smoke-sized (`FAST_CASES = 2`, `HEAVY_CASES = 1`) — a default
`cargo test` runs the surreal/ordinal ring-axiom fuzz on *one* random triple. The
sentinel tests carry the real regression weight (by design, and the file says so), but
root `AGENTS.md`'s "fuzzes the axioms across every backend" reads stronger than the
default reality. Add one Testing-section line naming `OGDOAD_PROPTEST_CASES` as the
step before trusting changes to core arithmetic.
