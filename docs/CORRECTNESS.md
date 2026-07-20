# CORRECTNESS.md (the verification-status ledger)

The verification-status ledger: which shipped claims are **machine-verified**, which
are **source-pinned**, and which are **asserted-but-unproven** — valued like
[`COMPLETENESS.md`](COMPLETENESS.md) — a game value `g` on a pillar blade `e_B` (`e_s`
scalar, `e_c` clifford, `e_f` forms, `e_i` integral, `e_g` games, `e_o` grundy, `e_y`
py). Claim level **interpretation/engineering**: each entry is a status call on the
existing verification surface, checked against the actual oracles, not vibes. Numbers
≈ focused days to close a verification gap; `±n` flags an a9 scope call; `↑` is worth
less than any number but strictly positive; `*n` is real, on-thesis, unscheduled.

The standing verification surface is the baseline this ledger reads against: `cargo
test` (the `proptest` suites `tests/scalar_axioms.rs` and `tests/clifford_axioms.rs` —
smoke-depth by default, `OGDOAD_PROPTEST_CASES=N` for real fuzzing — the
`associativity_*` oracles, and `general_product_reproduces_reduce_word_when_a_empty`),
the adversarial stdlib harnesses `experiments/echo_solver.py` and
`experiments/linking_game.py`, and the source-pinned finite tables inventoried in
[`TABLES.md`](TABLES.md). Its aesthetic sibling — structural/stylistic findings rather
than soundness — is [`CONSISTENCY.md`](CONSISTENCY.md).

---

## Status — audited 2026-07-02, PLAYED 2026-07-02 (same day)

The 2026-07-02 audit (baseline `30588ec`, sixteen adversarial math audits + seven
claim→oracle inventories; headline: **no mathematical error in any shipped computed
value — every error-grade finding was a wrong contract**) was played the same day in
four waves of sonnet agents plus lead fixups (`78a45bc..362ebed`), with an independent
codex review of the full diff returning PASS on every math-load-bearing area (one
comment-only transcription swap, fixed). Post-sweep baseline: **968 lib tests** (was
895), clippy clean both feature sets, cold rustdoc clean, `demo.py` green. The
archived play record is [`DONE.md`](DONE.md) → `revision-sweep-2026-07-02`; residuals
and standing switches below are what remains *of this ledger's scope*.

### Addendum — `under` numeric Norton descent, 2026-07-20

The positive-dyadic Norton regrading is a proved result, not merely a bounded
pattern: for `u=m/2^k`, `a=u-2^-k` (or `u-1` for an integer), nonnumeric finite
thermographs satisfy `mean(G.u)=u mean(G)` and
`temp(G.u)=u temp(G)+a`, and numeric inputs land strictly below `a`.
The proof in `writeups/thermo_newton.tex` was adversarially reread; that pass
caught and removed the false shortcut “numeric differences remain numeric,”
supplied the load-bearing numeric-image lemma, and isolated the
temperature-zero no-premature-meeting argument. Machine verification is
supporting rather than a formal proof: exact checks cover the complete 22-value
day-two census, a bounded day-three singleton-option census, dedicated numeric
images, quotient representatives, matching Berlekamp overheating, and the
non-associativity witness `A_2 A_(1/2)(*) != A_1(*)`. The Python binding probe
adds 210 thermic and 48 quotient/operator checks. Do not promote this family of
additive transports to a multiplicative action or an internal graded product.

## What holds (the baseline — don't dilute it on any cleanup pass)

- **The cross-validation spine is real, and this sweep widened it.** `verify_milgram`
  checks three independent routes to `signature mod 8`; `nikulin_genus_iff…` pins two
  independently implemented algorithms against each other — and the Nikulin machinery
  now also has both *negative* obstruction branches forced plus a positive
  `is_isomorphic` DFS witness on differently-presented forms; the Clifford engine is
  pinned to the brute-force `reduce_word` oracle on all three product paths, with the
  even-subalgebra, dim-4 polar-rank, bialgebra-compatibility, direct-sum-shift, and
  versor-inverse-`None` gaps now closed; the ordinal tower's generator path is
  cross-checked exhaustively against the `φ_{ω+1}`-polynomial path;
  `LocalQp`/`Qq`/`WittVec` each have an element-for-element cross-backend oracle, and
  the whole p-adic wing now carries the `assert_supported_params` +
  `invalid_parameters_are_rejected` discipline.
- **Reciprocity is the gold oracle at every leg**: brute-forced `∏(a,b)_v = +1` over ℚ,
  the multiplicative sweep over `F_5(t)`, the additive XOR sweep over `F_2(t)`/`F_4(t)`,
  and the full-strength `n ∈ {2..5}` constant-extension sums over `F_q(t)`.
- **Source pins**: A380496 is now diffed **in full** (all 126 rows) against a vendored
  b-file copy (`src/scalar/big/ordinal/b380496.txt`, fetched 2026-07-02);
  `LEECH_AUT_ORDER` and the ADE data are recomputed; the BW16 group orders now
  **derive in-repo** from Grove's `|O⁺(2m,q)|` closed form instead of being
  hand-entered; the 2-adic canonical-symbol Sage examples in `genus.rs` remain the one
  executed Sage oracle.
- **The games wing is honestly two-implementation tested where it claims to be**,
  now including a day-≤2 exhaustive canonical-form sweep recovering the known
  22-value census (day 3 bounded, labeled as such), a two-way Norton oracle, and a
  branched hackenbush ordinal-sum witness. `thermograph_via_tropical` remains a
  naming bridge over the shared recursion — not an independent cooling
  implementation; don't cite it as a cross-check.
- **"source-pinned" is now a reserved term** (external data pin, à la A380496). The
  Aravire–Jacob expected values are labeled "paper-derived worked examples" — weaker,
  and now worded as such at every site.

---

## Played 2026-07-02 — the audit items, with residuals

Every numbered item of the 2026-07-02 audit was played; full per-item detail is in
the four `Play wave …` commit messages and `DONE.md`. What each left behind:

- `spinor-norm-char2-claim` (½·e_c): the three doc sites reworded (raw norm only; the
  char-2 ℘-reduction is *not* the invariant), Nimber-backed `spinor_norm`/
  `classify_versor` pin added. **Residual**: the honest additive Wall/Dye invariant
  stays a buildable — [`COMPLETENESS.md`](COMPLETENESS.md) → `char2-spinor-norm`.
- `modular-overflow` (½·e_i): `sigma_power` overflow now a deterministic documented
  panic (`n = 2989` boundary at power 11, pinned both sides); `B_1 = +1/2` convention
  stated and pinned. The documented-cap route was chosen over `Option` to keep the
  public Eisenstein surface infallible.
- `p-adic-guard-gap` (½·e_s): WittVec/Qq/Ramified guarded + rejection-tested; Qq (and
  Qp, found during play) valuation arithmetic checked; `adele_prec`'s cap verified
  against `LocalQp::check`'s real bound and **widened** (~2^64 → ~2^127).
- `nullspace-skip` (½·(e_s∧e_c)): column-skip elimination with the load-bearing
  full-width sweep (a skipped column must keep being updated by later pivots — caught
  during play, membership-tested); `solve`/`inverse_matrix` local round-trips added.
- `alpha-row-pins` (1·e_s): integer table now full-diffed against the vendored
  b-file; ordinal reconstruction value-pinned at 16 rows (`{3..47} ∪ {73, 89}`).
  **Residual**: rows `97..709` still have no ordinal-value oracle, and the plan to
  lift `u = 179` FAILED for a real reason — `alpha_ordinal(179)` hits a compute cliff
  (Frobenius minimization over `χ(89)`'s subfield degree, 3+ min unterminated), so
  the "too costly" boundary bites at 179, far below 709. Documented in
  [`OPEN.md`](OPEN.md); any future pin of large rows needs an algorithmic idea, not
  patience.
- `bw-ff-sweep` (1·e_f): all-eight-residue sweep ported; genuinely independent
  Clifford-side oracles exist only at residues 2–3 (same boundary as the rational
  leg — Lam's table is itself the source for the other arms; the test says so).
- `rank16-pins` (1·e_i): BW16 orders derived from the `|O⁺(8,2)|` closed form; the
  Kneser reports now assert the **generated** labels equal the static catalogue
  (previously the generated set was silently discarded); the `D16_PLUS_AUT_ORDER`
  tautology is labeled as transcription-only, pointing at the Siegel–Weil pin.
- `nikulin-negative-witnesses` (½·e_i): both obstruction variants forced (27/8 at
  p=3, 16/3 at p=2 — each hand-derived and re-derived through an exact-fraction
  port), positive DFS on differently-presented `A_1⊕A_1` Grams, fqm cases for a
  noncyclic anisotropic core / an exponent-8 block (impossible-by-lemma: `q(4x)=0`
  forces order-4 Witt cancellation) / D_4 cross-checked against `brown_invariant`.
  **Residual**: coverage is witness-grade now, not exhaustive-grade; a
  Kawauchi–Kojima-cited row was deliberately not pinned (citation uncertainty —
  derive-twice used instead).
- `char2-decomp-coverage` (½·e_f): all three closed; the equal-degree-splitter input
  was *verified to fire the trace-splitter branch* (traced: split at seed 24, before
  any early-gcd coincidence) — the audit's "one product closes it" was optimistic
  about branch selection, recorded here so the next test author checks the branch.
- `arf-vs-constant-bias` (½·(e_g∧e_f)): `QuadricFit::bias() = arf XOR constant`
  shipped with the exhaustive k ≤ 4 both-polarities pin; examples routed through it;
  the loopy Draw-branch now constructed and tested.
- `clifford-test-gaps` (½·e_c): all five closed, no production bug found.
- `partizan-oracle-breadth` (½·e_g): played at the honest scope — day ≤ 2 exhaustive
  (22-value census), day 3 bounded-not-census (the 1,474-value day-3 universe is
  future work if ever wanted); Norton oracle is a second transcription, not a
  citation (none was certain enough to pin).
- `one-line-pins` + `proptest-depth-note` (↑): all bullets played.

## switches — closed

### ±1·e_f: `aj-second-engine` — CLOSED 2026-07-02 (accepted)
a9's call: **accept paper-derived worked examples as the documented boundary** — no
second engine. The decision is recorded at the source
(`springer/char2/mod.rs` module doc, "Oracle boundary (accepted, 2026-07-02)"): the
odd-residue engine rejects residue char 2 by structure, the hand-worked
Aravire–Jacob oracles are the contract, and a test-only brute-force verifier stays
welcome-if-ever-wanted rather than owed. "source-pinned" remains reserved for
external data pins.

### recorded boundaries (not gaps, decisions)
- `weight_enumerator` (both code types) keeps an infallible signature with a
  documented budget-referencing panic (`CODEWORD_ENUMERATION_BUDGET`); full
  `Option`-ification is a 3-caller follow-up (py, lexicode, theta) if ever wanted.
- The next audit of this kind should read `grundy/src/` and `src/py/` — both were out
  of scope for the 2026-07-02 pass (see [`CONTINUATIONS.md`](CONTINUATIONS.md) →
  `ogham-reflect` part (3)).
