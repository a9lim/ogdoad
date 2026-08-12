# PY.md — the Python-side audit ledger

Audit of everything Python-facing: `demo.py`, `experiments/**` (~15k lines, ~97
files), `scripts/generate_stubs.py`, `ogdoad.pyi`, `pyproject.toml`, plus the
bindings-vs-core gap analysis against `src/py/`. Snapshot: 2026-07-02, commit
`b16e40a`. Method: 21-agent fleet sweep (file-fenced reviewers + per-pillar gap
agents + cross-cutting census agents), an independent Codex consult, and a
synthesis pass that re-verified every headline claim against the source (the
`synth_verify` off-by-one, the sigma-bug structure, the `/tmp` import semantics,
and the SyntaxWarnings were each independently reproduced before landing here).

Severity vocabulary: **serious** = wrong output or a lying verifier; **issue** =
real problem worth fixing; **wart** = should fix; **nit** = taste. Fix-order
recommendations are in §9.

**Played 2026-07-03** (commits `589ef72` + `3a5d32f`): §9 items 1–8 and 10 are
done — two waves of file-fenced fix agents with lead gates; `ruff` went 571 → 0;
`echo_solver.py selftest` PASS throughout; demo/maintained-tier outputs verified
byte-identical modulo intended lines. Item 9 (the bindings wave) remains open.
Three findings were **corrected during play** and are annotated inline below
(§1.2 goldarf citation, §1.5 the cyclo assert, §2 the skeptic_nogo count); three
fixes were deliberately **not** applied — `exception_column_m4.py`'s Q_SET
monkey-patch (the sibling reads the module global internally; a parameterized fix
is semantic surgery on a pinned harness), `weil_gold_probe.py`'s `dsum` →
`direct_sum` swap (archival), and `asym2_fifo_bench.py`'s `direct_fifo_value2`
deletion — that "dead alias" carries the `# fix call shape` comment
`echo_solver.py` uses as its extraction end-marker, so it is load-bearing.

## 0. The shape of the problem

The Python side is **two codebases sharing a namespace**, and they deserve
different bars:

- **The maintained surface**: `demo.py`, the top-level `experiments/*.py`,
  `experiments/common.py`, `scripts/generate_stubs.py`. Census: 100% of
  top-level experiments have `__main__` guards, ~76% type-hint coverage, all
  docstringed. Held to the same bar as the Rust side below.
- **The rescued archive**: `experiments/{gold,audit,excess}/` — per their own
  READMEs, machine-generated research probes rescued from `/tmp` after the
  2026-06-10 fleet run, "not maintained or CI-tested". Census: ~2% type-hint
  coverage in `gold/`, 0% in `audit/`, almost no main guards, heavy
  duplication. The rescue was **textual**: the files came over, but their
  `/tmp` import paths, absolute home-directory paths, dead debugging branches,
  and abandoned first drafts came with them.

The single biggest structural problem is that these two tiers carry equal
apparent authority. A future reader (human or model) cannot tell a pinned
verified harness (`echo_solver.py`) from a superseded probe whose solver has a
known bug (`echo_charge_probe.py`) without reconstructing the genealogy from
docstrings. The archive needs a **manifest** (per-file status:
pinned / superseded-by-X / scratch) more than it needs any individual cleanup.

## 1. Serious — wrong output, lying verifiers, broken-as-checked-in

These are the findings that gate citing the archive's printed output.

1. **`experiments/gold/synth_verify.py:200-216` — a verification block that has
   been printing `False` and nobody noticed.** The "closed-form lam"
   cross-check derives `lam_closed` with exponent shift `(1 << t) - 1` while
   the `w` loop above uses `1 << t`; numerically `lam_closed(m) == Pw(2m)` for
   every tested `m` (8→138 vs 10, 16→32906 vs 138, 32→2147516554 vs 32906) —
   the fingerprint of a one-layer index shift. `P(w)` itself is correct (it
   matches `construct_round2.py`'s pinned `lam=10`/`lam16=138`). Unlike every
   other section of the file, **nothing here is asserted** — the script prints
   `P(w)==lam: False` and exits 0, in a file whose docstring calls this one of
   "the two load-bearing round-1 skeptic claims". Either the closed form is
   wrong (fix the loop bound) or the negative result is real (say so); either
   way add the assert.

2. **The `echo_charge_probe.py` solver lineage carries the documented "round-1"
   sigma bug.** `solve_form`'s minimax memoizes on `(u, o, last, mover_is_p1)`
   with a fixed `maximize = mover_is_p1 == p1_maximizes`
   (`echo_charge_probe.py:125,141`) — but with an XOR-accumulated payoff, the
   mover's preferred *future* charge is `target ^ prefix`, which flips with
   prefix parity. A memo key without sigma conflates positions reached with
   different prefixes. This is precisely the bug `asym2_probe.py`'s docstring
   documents finding and fixing ("CORRECT solver: sigma in the state"), and
   `echo_window2.py` in the same directory self-describes as "the CORRECT
   (sigma-in-key) solver" — the family knew. Inherited by
   `echo_frame_robust.py:35` and `echo_window_probe.py:28`, whose sweep results
   (the m=4 "exact hit" robustness numbers) are therefore suspect. **The
   headline 391,680/391,680 result is unaffected** — it comes from
   `echo_solver.py`'s independent corrected harness. Action: mark all three
   files superseded in the manifest, and check whether `writeups/goldarf.tex`
   cites any number produced by the buggy lineage.
   **Correction (2026-07-03, found during play):** the original triage grep
   reported goldarf.tex clean — wrong, because TeX escapes underscores
   (`echo\_charge\_probe`). goldarf **does** cite the file, in the
   corrected-results provenance paragraph. The record stands regardless: that
   table is independently re-derived by `echo_solver.py` stage `ko2` (validated
   against tree enumeration, reproducing the unique `(8,2)` miss `x=224`), and
   goldarf itself already quarantines the round-1-data blocker conjecture as
   "hypothesis to re-test". Fixed: goldarf's parenthetical now notes the rescued
   snapshot predates the memo-key fix, and the file's SUPERSEDED header says the
   same. Lesson for future greps: match TeX-escaped names.

3. **`experiments/audit/fp_full.py:3` — cannot run, at all, as checked in.**
   `exec(open('/tmp/fp_emulate.py').read().split('# scan')[0])` — an `exec` of
   an ephemeral temp path (the checked-in sibling is
   `experiments/audit/fp_emulate.py`), sliced on a comment substring, so even
   with the path fixed the reuse silently changes if that comment is ever
   reworded. The only file in the repo that is *hard*-broken by the `/tmp`
   fossils (§2). Fix: `from fp_emulate import ldl, fp_search, norm` plus a
   main guard on `fp_emulate.py`.

4. **`experiments/audit/dickson_audit.py:4-7` — `mat_mul` is a landmine.** It
   reduces over the empty list literal `[]` (so it always returns a zero
   matrix without ever calling the lambda) *and* the lambda body references an
   undefined `k_` (so it would `NameError` if the iterable weren't empty).
   Dead — the correct `mmul` below is what's used — but two-ways-broken code
   with a plausible name is exactly what gets copy-pasted later. Delete it.
   (Independently caught by two reviewers and by `ruff`'s F821.)

5. **`experiments/excess/cyclo_family.py:137` — a neutered assert.**
   `assert fmul(...) == fmul(...) or True` — precedence makes this
   `assert (…) or True`, unconditionally true. It reads as a real norm-identity
   check and verifies nothing (the next line happens to do the real check
   redundantly). This file is load-bearing for `writeups/excess.tex`'s k=1..4
   claims. Same file, line 80: `DET_LIMIT` is the 13-witness Miller-Rabin
   bound (needs bases through 41) but `SMALL_DET_BASES` stops at 37 — benign
   for the factor sizes actually used, but the "deterministic below this"
   comment asserts a guarantee the code doesn't provide. Add 41 or lower the
   limit to the 12-base bound.
   **Correction (2026-07-03, found during play):** "the next line does the real
   check redundantly" was wrong — the drafted identity is *false as written*
   (`β^(2^h+1) == γ·β`, one side multiplied by β), which is presumably why it
   was neutered rather than fixed. Enlivening it would have failed. Resolution:
   the dead assert was deleted with an explanatory comment; the live norm check
   below it is the verified one. The base list got its 41.

6. **`experiments/gold/ogdoad_misere_subgroup_sweep.py:28-147` — ~120 lines
   reimplementing a shipped binding, in a file named after the package it never
   imports.** `octal_moves`/`make_outcome`/`multisets`/`closed_quotient`
   rebuild `ogdoad.octal_misere_quotient` + `ogdoad.octal_moves` (bound;
   `Quotient` exposes `.multiplication`, `.class_is_p`,
   `.multiplication_consistent` — the exact tuple the script hand-builds), and
   `anf_quadric_fit` (lines 213-250) is a self-described "port of
   forms::quadric_fit::fit_f2_quadratic", also bound. No independent-oracle
   rationale is stated (contrast `octal_attack.py`, which states one). Either
   call the bindings or say why not.

## 2. The `/tmp` and absolute-path fossils — corrected account

17 files reference `/tmp`; 5 hardcode `/Users/a9lim/Work/ogdoad/...`. Getting
the severity right matters because the first fleet pass overclaimed it:

- **`sys.path.insert(0, "/tmp")` (11 files — corrected during play: 10 in
  `gold/asym2_*`/`gold/echo_*`/`gold/skeptic_indep`, plus
  `excess/cyclo_family2.py`; `skeptic_nogo_check.py`'s `/tmp` was a docstring
  mention only, no code) does NOT break the scripts.** CPython puts the running script's own directory at
  `sys.path[0]`, and every imported sibling lives in that same directory, so
  the `/tmp` entry never matches anything (verified by running one). What it
  *is*: a silent-shadowing hazard — any stale `asym2_probe.py`/
  `cyclo_family.py` left in `/tmp` from a past session would be imported in
  preference to the real one, with no error. Mechanical fix: delete the line
  (sufficient for direct execution) or use the `linking_game.py:317` idiom
  (`Path(__file__).parent`).
- **The absolute-path five** (`gold/center_reading_probe.py`,
  `echo_charge_probe.py`, `tier2_stratum_sweep.py`, `step1_term_checks.py`,
  `weil_gold_probe.py`) hardcode this checkout's location to reach
  `experiments/common.py`. Works here, breaks on any re-clone. Same
  mechanical fix. Note `tier2_stratum_sweep.py:21`'s insert exists to import
  the *installed* `ogdoad` package and is pure cargo-culting — delete.
- **Actually broken: only `fp_full.py`** (§1.3), because `exec(open(...))` has
  no fallback.
- **Naming casualty of the same history:** `asym2_final.py` calls itself final
  while carrying the `/tmp` insert; `loopy_audit2.py:2`'s docstring cites its
  sibling by `/tmp` path.

This cluster is one `sed` sweep plus a re-run to confirm; it is the cheapest
big win in the whole audit.

## 3. Taste — the maintained surface

### demo.py

Genuinely good as a tour — broad, well-ordered, honest printed prose — but the
back third (≈line 860 on) shows accretion fatigue:

- **Duplicate demonstrations that lie about coverage**: `demo.py:213-216`
  prints `f8h.isometric_to(...)` twice with byte-identical arguments under one
  four-value label (a reader assumes four distinct facts); `demo.py:262-263`
  prints the same `ω < ω²` comparison twice under near-identical labels.
- **Recompute-instead-of-reuse**: `pl.gold_form(4, 1)` rebuilt at 866 one line
  after being bound to `gold_alg`; `trace_form_arf(3)` and
  `classify_finite_algebra(trace_twisted_form(3, 2))` called verbatim twice
  (867-871); `extended_golay_generator_rows()` twice in one print (940-941);
  the `ff_local0` attributes printed three ways in one call (990); the `aj.psi`
  comprehension built twice in one print (1024-1025).
- **`A2` means two unrelated things 400 lines apart** (471: an anisotropic
  nimber plane; 874: the actual A₂ root lattice, which owns the name by the
  file's own printed labels). Rename the first.
- **Cross-section coupling**: `WittClassG.try_char2_from_metric(A)` at 421
  reads a variable defined at 141, a dozen section banners earlier — breaks
  the file's implicit reorderable-sections invariant. Rebuild locally.
- Nits: local `np` for a Newton polygon (1055 — false numpy cognate); one
  hand-rolled try/except at 252 where `raises_value_error` is the file's own
  idiom; a lone "Arc IV" banner with no Arcs I–III; no `__main__` guard (fine
  as a script, but it makes `demo.py` unimportable as example code).

### common.py — 32 lines serving ~97 files, and half of it shouldn't exist

- `frob`/`nim_trace` **reimplement bound functions**
  (`ogdoad.nim_frobenius_iter`, `ogdoad.nim_trace` — same algorithm,
  int-in/int-out, no wrapper convenience excuse). The shared helper module for
  the experiments reimplementing the library it fronts undercuts its whole
  framing. Make them one-line delegates (or rename to mark them as deliberate
  independent ports — but then they belong beside the other independent
  oracles, not in `common.py`).
- What `common.py` is *missing* is the actual demand (§5): `nim_mul`,
  lam-generalized `gold`/`polar`, a table-valued `gold_table`, and a
  `report(name, ok)` PASS/FAIL helper.

### The other top-level experiments

Mostly clean (this tier is genuinely well-kept — `cyclotomic_3k_family.py`,
`cubic_two_normal_countermodel.py`, and `misere_kernel.py` survived review
with only nits). Remaining:

- `linking_game.py:419` — stage dispatch via raw `sys.argv` **silently no-ops
  on a typo** (misspelled stage → nothing runs, exit 0). Its siblings use
  argparse; this one should too. Also: a 100×-inflated `setrecursionlimit`
  (line 72) and the tree's only redundant `sys.path` hack for a same-dir
  import (line 316).
- `framing_obstruction.py:71-89` — hand-rolls a memoized DAG P-position solver
  in exactly the input shape of the bound `pl.LoopyGraph(succ).loss_set()`,
  while its own docstring cites `loopy_quadric.rs` by name. Replace.
- `exception_column_m4.py:394` — monkey-patches a sibling module's global
  `Q_SET` at runtime instead of merging a local copy.
- `gold_family_survey.py:53` — `_frob`/`_trace` re-derive `common.py` helpers
  its sibling correctly imports.
- `under_descent.py:44` — round-trips `Game.temperature()` through
  `str()`/`Fraction()` instead of the structured dyadic/rational accessors;
  line 30 builds a 10-positional-arg dataclass (5 same-typed Fractions —
  transposition bait). Use keywords.

### generate_stubs.py and the stub

- `_is_constructible` (line 122) branches on **string-matching PyO3's internal
  error wording** — a dependency-version behavior contract, failing
  open (over-permissive) and silently. Pin the tested PyO3 version in a
  comment or warn loudly on unmatched wording.
- The stub is an index, not a type surface: 35,487 lines, 640 classes, 18,206
  defs — and **10,618 `*args: Any` signatures**. The curated override table
  (`FUNCTION_OVERRIDES`, lines 44-75) covers only headline entries; notably it
  omits the `nim_*` free functions the experiments call most. Expanding
  overrides for the README/demo surface would buy real editor value cheaply.
- CLI is substring-membership on `sys.argv` (line 305) and the usage string
  drops the `scripts/` prefix.
- Imports the compiled extension at module import time, so `--check` can't
  even report staleness without a built module.

### The `pl` alias — verdict

15/16 importing files use `import ogdoad as pl`; it's the pre-rename fossil of
*pleroma* (commit `97afa22`). It is at least *consistent*, and renaming is a
mechanical sweep — but a two-letter alias whose letters no longer mean
anything is the kind of thing this repo's Rust side would never tolerate.
Recommendation: either bless it explicitly in AGENTS.md ("house alias, for
gnostic-lineage reasons") or sweep to `og`. Deciding beats drifting.

## 4. Taste — the archive

Judged as an archive (not as maintained code), the recurring sins:

### Naming encodes chronology, not semantics

- `skeptic_indep.py` / `skeptic_independent_check.py` /
  `skeptic2_independent.py`: three near-identical stems, three unrelated
  claims. The first is also the weakest file in the family — it re-litigates
  the echo-ko reading already documented non-exact and superseded (delete, or
  rename `skeptic_echo_ko_adapted_check.py` with a superseded note).
- `nogo_synthesis_check.py` / `nogo_verify.py` / `synth_verify.py`:
  cross-wired names, distinct content.
- Version suffixes don't mean supersession: `fp_scan2` is a *narrower,
  different* search than `fp_scan`; `loopy_check2` vs `loopy_ge` is the real
  near-duplicate pair and the names hide it; `root_sim` **is** subsumed by
  `root_sim2` (the one true supersession found — and `root_sim3`'s better
  overflow detector was never re-run on the cbrt case `root_sim2` covered).
- `experiments/gold/step1_term_checks.py` is **misfiled** — it's
  ordinal-Kummer-tower content that belongs in `experiments/excess/`.
- A workable retroactive scheme (from the conventions census): directory
  carries provenance, suffix carries failure semantics (`_verify` =
  asserts-on-failure, `_probe`/`_sweep` = exploratory printout), and
  supersession lives in the manifest, never in a numeral.

### Dead code (the `if False` museum)

`weil_gold_probe.py:136` (a rank-3 test case permanently disabled inside a
list literal — in a probe presenting exhaustive-looking coverage);
`construct_round2.py:178` (dead ternary + `mixed` never read; `results`
accumulator built and never consumed); `tier2_stratum_sweep.py:158` (condition
computed, `pass`); `echo_window2.py:19` (loop whose generator condition is
always false); `extraspecial_adapted.py:24-59` (a ~36-line abandoned
symplectic-pair draft, self-annotated "implement properly below", fully redone
at line 61 — delete wholesale); `asym2_fifo_bench.py:87`
(`direct_fifo_value2` passthrough alias); `skeptic_check.py:53` (`q_from_tab`
dead with an overclaiming docstring); `ao_orbitals.py:91` (generator over an
empty tuple); `echo_solver.py:180` (`DUMMY` global declared, never used) and
`:379` (`exactness()`'s `positions`/`progress` params never exercised);
`nogo_synthesis_check.py:143` (`ok2m` initialized, never updated — an
abandoned misère gate). Plus ~10 unused imports (`ruff` F401 count for the
tree: 35).

### Import side effects

Almost nothing in the archive guards its driver code, which turns imports into
cascades: `dickson_audit.py` importing two helpers from `arf_audit.py` re-runs
and re-prints arf_audit's entire ~90-line audit; `skeptic_indep.py` importing
`build_adapted_frame` re-runs `extraspecial_adapted.py`'s full 7-form sweep;
importing one function from `asym2_sweep.py`'s chain transitively re-executes
five ancestors' validations. Files that are actually imported by siblings
(`arf_audit`, `extraspecial_adapted`, the `asym2` chain, `fp_emulate` after
the §1.3 fix) need guards; pure leaves can stay bare.

### Assorted bug-risks below the serious line

- `echo_solver.py:717` — `forms = forms or DEFAULT` truthy-or swallows an
  explicit empty list.
- `echo_frame_robust.py:74` — hardcoded `range(4)` where `range(m)` is meant;
  silently wrong if a non-m=4 case is ever added.
- `fp_scan2.py:74` — top-level brute scan, `K += 1` over ranges up to 650M ×
  24 combos, no progress output, no early exit: effectively unrunnable past
  the lucky prefix, and it starts on import.
- `criterion_calibration.py:86` — cycle "guard" that's a silent placeholder
  (correct only by caller discipline), beside a rigorous retrograde solver in
  the same bundle.
- `nogo_verify.py:279` — one L6 assert is vacuous (its disjunct is guaranteed
  by the next assert).
- Recursion limits escalate arbitrarily across the asym2 family (100k → 1M →
  2M) with no relation to actual depth.
- Two files emit `SyntaxWarning` on import (verified):
  `ogdoad_misere_subgroup_sweep.py:11` (`"\ "`), `sandwich_m4.py:6` (`"\{"`)
  — unescaped docstring backslashes; future CPython makes these errors.
- PASS/FAIL vocabulary drifts across the archive (PASS/FAIL, OK/FAIL,
  EXACT/FAILURES, ok/mismatch), and assert-crash vs printed-report are used
  interchangeably as verification mechanisms — sometimes non-overlapping
  (`nogo_synthesis_check.py:188`: functions that can only return True or
  raise, wrapped in `"PASS" if X() else "FAIL"` with an unreachable FAIL arm).

## 5. Duplication — the three-island problem

The dominant pattern isn't copy-paste so much as habitual from-scratch
reimplementation, and it has a redeeming discovery: **all 9 independent
`nim_mul` bodies were fuzz-verified against `pl.Nimber` (4,000 random pairs)
with zero mismatches** — the duplication cost is maintenance, not correctness.

- **Three disconnected helper islands**: `common.py` (imported by 8 files,
  mostly top-level), `extraspecial_core.py` (~12 gold siblings),
  `asym2_probe.py` (~9). None imports another. The `/tmp`-era path friction
  (§2) is *why* — reaching `common.py` from `gold/` required the absolute-path
  hack, so copy-paste won 14-to-2 among gold scripts.
- **The `gold()` signature disaster**: five mutually incompatible parameter
  orderings under overlapping names — `common.py:24` `gold(v, a, m)`;
  `octal_attack.py:54`/`skeptic_octal_check.py:54` `gold(v, lam, a, m)`;
  `construct_round2.py:67` `gold_q(v, a, m, lam=1)`;
  `extraspecial_core.py:51` `gold_q(m, a, lam=1)` (table-valued!);
  `skeptic_check.py:48` `gold_tab(lam, a, m)`. Copying a call between files
  silently permutes arguments. This is the audit's clearest genuine hazard
  from drift.
- **Byte-identical clusters**: the 6-function Fraction-Laurent toy algebra ×4
  (`inv_sim`, `root_sim{,2,3}`); `sum_game`/`left_survives_second` ×2
  (`loopy_check2`, `loopy_ge` — same algorithm, so running both adds no
  cross-check value, unlike the deliberately-different `loopy_audit`/`2`
  pair); `ldl` ×2 + `det3` ×3 across the `fp_*` family; `solve_coin` copied
  verbatim into `skeptic_supplement.py` whose stated purpose is *independent*
  verification of the file it copied from; the `charge()`+minimax recursion
  ×3 inside `echo_solver.py` itself (plus the sibling copy it extracts by
  string-slicing at line 651).
- **Reimplementations of bound API** (beyond §1.6): `framing_obstruction.py`'s
  kernel solver (= `LoopyGraph.loss_set`), `weil_gold_probe.py:54`'s `dsum`
  (= `IntegralForm.direct_sum`), `audit/gauss_teich.py`'s raw Teichmüller lift
  (= the bound `.teichmuller()`), `audit/root_sim*`'s series roots (= the
  bound `*_to_terms` — though here the independent implementation *is* the
  point; the miss is that they only self-check instead of also diffing against
  the bound output), `audit/arf_audit.py`'s Arf stack (same caveat).
- **The exemption principle** (keep it): where a file *declares*
  independence as its purpose (`echo_solver.py`, `octal_attack.py`,
  `synth_verify.py`, `extraspecial_core.py`'s oracle role), the duplication is
  methodology, not debt. The fix there is one line of docstring on the copies
  that don't declare it, plus a sampled diff against the bound API so the
  independence actually verifies something.
- **Consolidation plan**: `common.py` grows `nim_mul(a, b)`,
  `gold_lam(v, a, m, lam=1)`, `polar_lam(u, v, a, m, lam=1)`,
  `gold_table(a, m, lam=1)`, `report(name, ok)`; the Laurent toy algebra
  lands in `experiments/audit/_series.py`; `stopper_survival` shared between
  the two loopy twins; undeclared copies import, declared oracles stay.

## 6. Gaps — in the Rust core, absent from Python

Read against `src/py/AGENTS.md`'s binding-scope policy. Overall coverage is
*very* good — scalar, clifford, games are near-parity; the misses cluster in
`forms/` late-wave modules, none blocked by the const-generic or CGA-half
policies (all operate on already-bound types).

**Worth binding (oversights, roughly priority-ordered):**

1. `forms/integral/fqm_witt.rs` — the entire finite-quadratic-module
   Witt/Nikulin layer (`FiniteQuadraticModule`, `FqmWittClass`,
   `nikulin_existence_report`/`nikulin_even_lattice_exists`). Documented as a
   shipped fifth-wave bridge; zero pyi hits; plain `Vec<u128>`/`Rational`
   presentation, no generics.
2. `forms/char2/extraspecial.rs` — `Extraspecial2Group` +
   `HeisenbergWeilRepresentation` (constructors mirror the already-bound
   `arf_f2` raw pattern; matrices are bound `Complex64`). Ironic gap: the
   archive's `extraspecial_*` family spent 12 files probing this exact object
   in pure Python.
3. `forms/witt/brauer_wall.rs:223` — the odd-char function-field Brauer-Wall
   leg (`bw_class_function_field`, `FunctionFieldBrauerWallClass`); every
   sibling leg is bound and the surrounding F_q(t) machinery is fully bound.
4. `forms/integral/niemeier.rs` — the 24-class catalogue
   (`niemeier_classes()`, mass sum, weighted theta average) plus
   `eisenstein_e12`, so the rank-24 Siegel–Weil identity is checkable
   end-to-end from Python.
5. `forms/classify.rs:530` — `Char2FiniteFieldForm.witt_decompose()`; the odd
   sibling has it, the char-2 one doesn't.
6. `games/lexicode.rs:76` — `LexicodeTurningGame` (the bounded turning-game
   witness; only its solved `BinaryCode` output is reachable now). Follow the
   `NimLexicode` binding as template.
7. `clifford/cga.rs:85` — `Cga.alg()` on all 35 CGA backends (named in the
   pillar's own AGENTS.md as half of Cga's public accessor pair; the macro
   already builds the needed Arc). Related naming trap: Python's `Cga.meet`
   is wired to Rust's `outer_join`, recreating the exact confusion the Rust
   docs warn against — rename or docstring it.
8. `scalar/big/ordinal/subfield.rs` — `Ordinal.finite_subfield_degree()` (+
   the common-degree free function): the Nimber precedent (`Nimber.degree()`/
   `nim_degree`) is bound, and this diagnostic sits exactly on the project's
   open-problem boundary.
9. `grundy/error.rs` — `GrundyError`'s structured taxonomy (15+ kinds, span,
   hint) collapses to a stringified `ValueError`; `WittClassError` already
   sets the structured-exception precedent in the same bindings layer. And
   `grundy/eval.rs`'s `GrundySession` (stateful eval; `set_world`,
   `eval_line`, summaries) is the natural next binding if Python REPL/notebook
   use ever matters — `grundy_eval` alone is stateless.
10. Lower priority: `trace_form.rs`'s `cyclic_algebra_trace_form` (same
    dispatch pattern as the bound `trace_twisted_form`);
    `discriminant/phases.rs`'s `FqmGaussPhase`/`milgram_signature_mod8_fqm`;
    `weyl_versors.rs`'s constructive layer (the actual Pin versors/LinearMaps
    behind the bound summary report).
11. One rename: `Laurent.from_scalar` → `from_base` (Python kept the retired
    name; every sibling functor matches the new one).

**Verified deliberate (no action):** open const-generic backends, arbitrary
function-field rows, CGA where `1/2` is unavailable, `Metric::map`,
crate-private linalg, grundy parser/AST (documented WP6 boundary),
`heating.rs`'s composite predicates (reproducible from bound Game methods).

**Demo-coverage gaps** (bound, exercised nowhere): `d_n`/`e_6`/`e_7`
constructors (only A_n/E8 get the lattice tour); the modular q-expansion
arithmetic layer + `eisenstein_e6` (a `theta_E8 == E4` line from Python would
mirror the Rust test); `mex` and the naive-vs-bounded game-value pair;
`springer_decompose_local_char2`; `isometric_finite_algebra`; an
`IntegerAlgebra` exterior example (Integer as Clifford scalar, not just
coefficient ring); `Complex64` direct arithmetic. Most other "unused" pyi
classes are false positives (return types exercised through their fields, or
same-engine-different-prime backends deliberately demoed once).

## 7. Tooling

- **No lint config exists.** A cold `ruff check demo.py experiments/ scripts/`
  finds 571 violations: 402 E701/E702 (the archive's dense one-liner idiom —
  arguably style, ignore per-dir), 35 F401 unused-import, 37 F403/F405
  star-imports (the `extraspecial_*` family's `import *` — brittle in a family
  whose helpers kept evolving), 30 E741 ambiguous names, 14 E402 (fallout of
  the sys.path pattern; noqa'd inconsistently, 3 of 14), and 6 F821
  undefined-name including the real `dickson_audit.mat_mul` bug (§1.4).
  Recommended: a `[tool.ruff]` block with F-rules repo-wide and pycodestyle
  relaxed for `experiments/{gold,audit,excess}/**`; it would have caught §1.4
  and both SyntaxWarnings instantly.
- `pyproject.toml` is otherwise clean and complete (maturin config sane).
  Taste call: `Development Status :: 5 - Production/Stable` is a bold
  classifier for a package whose stub is 60% `*args: Any`.
- `.gitignore` lacks `.mypy_cache/` (mypy self-ignores its own directory, so
  status stays clean, but be explicit).
- No CI touches Python at all — even a `python -W error -m compileall
  experiments` smoke would have caught the SyntaxWarnings and `fp_full.py`.

## 8. What the audit did NOT find

Worth stating for calibration: no correctness bug in any *maintained* script's
mathematics; zero drift across the 9 independent `nim_mul` implementations;
the verified harnesses (`echo_solver.py`, `linking_game.py`,
`exception_column_m4.py`) survived adversarial re-review with only
hygiene findings; scalar/clifford/games binding coverage is near-parity with
documented-deliberate exceptions; and the `import ogdoad as pl` convention,
fossil or not, is applied consistently. The Python side is rough, but its
roughness is almost entirely *archival sediment*, not live rot.

## 9. Recommended fix order

*(Played state, 2026-07-03: items 1–8 and 10 ✔ done in commits `589ef72` +
`3a5d32f`, with the three deliberate non-applications listed in the header
block. Item 9, the bindings wave, is the open remainder.)*

1. **Truth repairs** (small, gates citation): `synth_verify` loop bound +
   assert; `cyclo_family` neutered assert + MR base list; delete
   `dickson_audit.mat_mul`; fix `fp_full.py`'s exec→import (+ guard
   `fp_emulate.py`); fix the two SyntaxWarning docstrings.
2. **Sigma-bug triage**: mark `echo_charge_probe.py` /
   `echo_frame_robust.py` / `echo_window_probe.py` superseded; grep
   `goldarf.tex` for any number they produced; re-run the frame-permutation
   sweep on the corrected solver if cited.
3. **Path-fossil sweep**: delete/replace all 16 `sys.path` fossils (§2);
   `sed`-mechanical; re-run touched scripts to confirm.
4. **Manifest**: a status table in each archive README (pinned /
   superseded-by / scratch), naming-taxonomy note in AGENTS.md, move
   `step1_term_checks.py` → `excess/`, retire `root_sim.py`.
5. **Lint floor**: `[tool.ruff]` per §7; fix the F-class findings it flags
   (unused imports, star-imports where cheap); gitignore `.mypy_cache/`.
6. **Guards**: `__main__ ` guards on the sibling-imported archive files
   (`arf_audit`, `extraspecial_adapted`, `fp_emulate`, the asym2 chain).
7. **common.py consolidation** (§5): delegate to bound fns, add
   `nim_mul`/`gold_lam`/`polar_lam`/`gold_table`/`report`, point undeclared
   copies at it, docstring the declared oracles.
8. **demo.py polish** (§3): the two duplicate demonstrations, the recompute
   cluster, `A2`, the stale-`A` coupling, `np`.
9. **Bindings wave** (§6 items 1–8; each is a self-contained PyO3 addition
   following an existing in-file pattern; regenerate stubs after).
10. **Stub quality**: expand `FUNCTION_OVERRIDES` for the `nim_*` family and
    the README/demo surface; harden `_is_constructible`.

Items 1–6 are a single focused session; 7–8 another; 9–10 are incremental and
can ride along future binding work.
