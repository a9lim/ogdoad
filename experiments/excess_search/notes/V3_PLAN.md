# V3 plan: the 0/1/4 counterexample search

Lead-architect synthesis of the three adversarial reviews (`exactness.md`,
`performance.md`, `redteam.md`) over SPEC, Codex's design, the five design
docs, v2 and the reference engine. No rows were computed for this plan.

Tags:
- **[checked]** means read in source or logs, or computed by a reviewer from
  existing files. Live process state was read at 00:45 EDT.
- **[derived]** means a short argument given here, not executed.
- **[estimate]** means a cost or probability model.

Units:
- **ch** is a jobe core-hour on the PCLMUL gf2x+bitpolymul stack.
- An M5 core with the PMULL build is about one ch up to 4e6-bit products, and
  4–6x slower above that.
- Effective capacity is about 12–16 cores on jobe at nice 19 (300–380 ch/day)
  and about 3–4 cores on the loaded M5 (about 80 ch/day) [estimate].

All masses are `sum 1/p` **net of everything already tested** (OEIS,
certificates, Peeters, and this session's ref, shortcuts and v2 runs), as of
the red-team snapshot, unless marked *gross*.

---

## 0. Decisions in one screen

1. **The reviews agree that v2 is sound but not yet safe to launch.**
   - No path to a false hit or a false pass was found, given NTL and the
     planner [derived, exactness §1].
   - Three gaps must close first:
     - a real hit can be filed as a crash or swallowed outright;
     - semantic facts live only in the planner;
     - ratio and finite non-hits have no element-level validation.
   - Milestones M0 and M1 close them before any new-row compute.
2. **Ancestor gating goes.** A run that passes every check certifies, at each
   closure prime, that the rule translate is not a power [derived, exactness §3;
   redteam §2.2]. A run that fails names an ancestor-failure candidate. So v3
   runs order-free, under the assumed rule. Every record carries its hypothesis
   vector and the ancestors it certified.
3. **The canonical record is `mu`.** That is the minimal polynomial over F_2
   of `T = N_{F_E/F_{2^h}}(target)`, which does not depend on the model or the
   root choices [derived]. It turns each comparison from one bit into h bits.
   It is the replay key, the cross-validation key and the hit certificate.
4. **Build order, by mass per engineering hour, with exactness first:**
   - M0 safety net;
   - M1 v3.0 assertions plus the PMULL/PCLMUL rebuild;
   - M1b mu cross-validation;
   - launch L1;
   - M3 single-big-component ("sz") path;
   - M4 Euler stage with the compact F_{2^h} final;
   - M5 tensor K;
   - M6 R3 and the flat path, optional and probably not built.
5. **Budget checkpoints** at 100, 300 and 1000 cumulative ch. Each one stops,
   writes a report and needs a9's go before continuing. Anything above
   1000 ch needs a separate decision.
6. **Honest yield.**
   - Through M5 at 1000 ch, about **0.29 net mass** is reached.
   - Under the random model that is P(≥1 hit) ≈ 25%. After the clean-record
     Bayes discount it is **about 5–11%** [estimate].
   - The near-certain deliverable is an exact excess table for most primes
     below 1e5 and a large slice of (1e5, 1e6], each row with its `mu`.
   - Describe it as a long shot with an exact-table byproduct, not by the
     20–40% figures in the older docs, which double-count covered rows.

---

## 1. Live hazard (act now, before any milestone)

`search_ref.py 60000 100000 10` is running on the M5. Its log has only the
header line ("638 rows to do, sum1/p=0.0215"), and `results_ref.jsonl` has
714 lines. Ten `refengine` processes were alive, the oldest at 15m50s
[checked, 00:45 EDT].

Its hit branch (`ref/search_ref.py:44-52`) has three faults [checked]:
- it loops `while True` over `m`, with no bound and no return-code check;
- it writes the record only after that loop finishes;
- it prints `!!! COUNTEREXAMPLE` only after that loop as well.

If a further translate changes `d(m)` and the engine errors, the worker hangs
forever. The hit is never written.

Two other faults:
- An ancestor failure prints `ERROR …`, writes no record, and the search
  moves on.
- `forced_ok = False` stores `known[p] = None`, which unblocks descendants.

Actions. These are run-time actions on the lead's side; this plan edits
nothing.
- **Do not kill it.** No hit or ERROR has appeared, and its rows are cheap
  coverage.
- When it prints `done`, or if it stops making progress, diff its `todo` set
  against `results_ref.jsonl`. Any p in `todo` with no record is a
  **suspected hit**:
  - rerun it at once under the M0 driver with the translate set `[0..rule]`
    only;
  - start §5 Level 0.
- The existing `tail | grep` monitor on `search_ref2.log` catches `ERROR`.
  Treat any `ERROR` as a possible ancestor failure (§5, Level 0b), not as a
  crash.
- Stuck-loop signature: `refengine` processes for one p that keep respawning
  (short-lived, with the same input program size), or a worker slot that never
  frees. Check `ps` once an hour.

---

## 2. Exactness fixes and runtime assertions

v3 lives in a new directory `search/v3/`, a copy of v2 that is then edited.
v2, its binaries and its logs stay frozen as the baseline. Ordered by
severity; no review found anything fatal.

### 2.1 Major (blocking for launch)

**X1. Ancestor and forced failures are evidence, not errors.** (exactness
M1; redteam §2.4)
- Driver classification. Any of these maps to the class shown, never to
  `error`:

  | engine outcome | class |
  | --- | --- |
  | `FATAL component exact degree` at component q of prime r, after A1 passes | `ANCESTOR_FAILURE_CANDIDATE r=…` |
  | `FATAL c not an ell-th power in k` for ell | `ANCESTOR_FAILURE_CANDIDATE r=ell's row` |
  | `verdict` with `forced_ok=False` | `FORCED_FAILURE` |
  | rule translate a p-th power | `HIT_CANDIDATE` |

- `FORCED_FAILURE` contradicts a paper theorem or reveals a bug. It is
  escalated and its descendants are blocked.
- For the top-prime case [derived]: `alpha_r` is an r-th power in K and
  r ∤ [K : F_2(alpha_r)], so it is one in F_2(alpha_r).
- Every attempted row writes exactly one record, flushed before anything else
  happens:
  - classes `ok`, `HIT_CANDIDATE`, `ANCESTOR_FAILURE_CANDIDATE`,
    `FORCED_FAILURE`, `refused`, `engine_error`, `timeout`;
  - `plan.py`'s re-raised `Refuse` inside the `except` (driver.py:151-157)
    becomes a `refused` record.
- The search stops scheduling descendants of any non-`ok` row. It pauses the
  whole queue on the first three classes (§4.3).
- Further-translate searches after a hit are optional and come later. They
  have a bounded m (≤ 8), a return-code check, and are never inside the
  scheduler loop.

**X2 (A1). Closure field certificate in the engine.** (exactness M2)
- Process components in order. Assert every rhs index `< i`; today `eval`
  silently reads zero for a later index (v2engine.cpp:247-256).
- Keep `L = lcm` of the checked component degrees, and assert
  `lcm(L, d_q) == ell_q · L` at every step.
- At the end assert `L == B`, or `B % L == 0` with `p ∤ B/L` for paths with
  extra translate fields.
- This is integer-only, and it is what separates "census wrong" from "rule
  fails at an ancestor".

**X3 (A4). The y2 p-th-power fact moves into the engine.** (exactness M3;
redteam rec 4)
- The planner tags the y2 factor and passes `R2` (ratio) or `k` (finite).
- Ratio path: assert `(R2·B) % h != 0`, which suffices because
  `d(y2) | R2·B` [derived]. Otherwise refuse.
- Finite path: assert `h ∤ 2^k`, using the built `chi_{2^k}`'s checked degree.
- sz path (M3): the translate z is checked to lie in k, and the top is a pure
  radical, so no y2 is involved.

**X4 (A5). Semantic header.** The planner sends `(arm, Q, rule, R_i,
exponents, path, y2 tag)`. The engine asserts:
- `R = Π R_i`, with the `R_i` pairwise coprime prime powers;
- exponents exactly `(R/R_1, −R/R_2)` (ratio) or `(1, −R_1)` (finite);
- translate labels exactly `0..rule` (singleton) or `{0}` (ratio, finite);
- `E = R·B`, recomputed from the checked top degrees and compared with the
  header.

**X5 (A6). Multiplicity identities, every run.**
- Assert `fa[0] == N_{K/k}(a)` (one relnorm) and `fa[D−1] == Tr_{K/k}(a)` (one
  reltrace). Together they catch a wrong `D/d` power or a wrong conjugate set.
- The `d < D` branch has never run [checked], so A10 must exercise it (§2.3).

**X6. Element-level validation before any non-hit counts as coverage.**
(redteam §5)
- Implemented in M1b:
  - v3 emits `mu` (the `--minpoly` route, or for free after M4) for every
    tested target;
  - the dual builder (`design/proto/dual.cpp`, which has its own planner)
    builds `F_2[Y]/P` for `beta`;
  - from its component images it forms the same target: `chi_R + m`, or
    `1 + y1/y2`, which is canonical because `aV` is a Gal(L/K)-conjugate of z
    [derived];
  - it takes the flat norm to F_{2^h} and the minpoly.
- Require bit-identical `mu` on at least 30 rows per path (singleton, ratio,
  finite; sz after M3), with E ≤ 3e5, p > 100 and as many distinct h as
  possible.
- Until this passes, ratio and finite non-hits are **provisional coverage**.
  That is 0.063 of v2's 0.098 net reach [checked, redteam §1.3].

### 2.2 Minor (land in M1, cheap)

- **A2.** Assert p prime (deterministic Miller–Rabin bases, p < 2^64),
  `p ∤ R`, `p ∤ B`, every prime of R and every component prime `< p`, and
  `Nh ≠ 0`.
- **A3.** Keep the per-l non-residue checks. Count them and require exactly
  `|Rprimes|` of them.
- **A7. Full-size H self-tests, once per H.**
  - `frob_apply` against repeated `H_sqr` on a random element, at one
    squaring-path length and one CompMod-path length.
  - Positive control: the Euler phase of `u^p`, for random `u ∈ H`, is
    exactly 1.
  - Do **not** count the arm-O `m = 0` translate as value validation. It is a
    p-th power for any radicand [derived, redteam §5.2]. It is only a control
    on the Euler code.
- **A9. Driver integrity.**
  - Verify the engine's SHA-256 against the build manifest. `v2engine.prelim`
    is never invoked.
  - Require every expected `CHECK` name with its expected count.
  - Record per result: binary hash, gf2x/NTL build id, machine, hypothesis
    vector `{r: rule(r)}` for the closure, the list of ancestors certified by
    this run's checks, path, `t`, seeds, and `mu` (SHA-256, with full hex in a
    sidecar).
- **Oracle hygiene.** The v3 reference fallback loads moduli through v3's
  Rabin-checked loader. The unpatched `refengine` does not Rabin-check cached
  moduli (refengine.cpp:206-217).
- **Validation accounting.** Report validation power as `sum 1/p` for one-bit
  agreements, separately from element-level `mu` agreements. Rule-translate
  agreement on rows with Rt > 3e4 is not counted as arithmetic validation.

### 2.3 Regression set (A10), run at every milestone gate

- The v2 final set (515 rows) and prelim set (838), on **both** builds.
- An encoding-independent oracle for small E: `ref/rowprog.py` + `census.py`,
  or the Rust `Ordinal` / `TermAlgebra`. Never `plan.ref_program`, which
  shares v2's `Closure` and `census2`.
- `t_mult > 1`: rerun about 20 rows with a non-minimal admissible cut and
  require identical `mu`.
- `d < D`: a planner-only census pass (seconds) finds ratio rows whose
  radicand has `d < D`. Run at least 3 of them and cross-check `mu` against
  the dual builder.
- Wieferich: 1093 is in the set already; 3511 once the sz path or a fallback
  reaches it.
- `--direct` on every row with Rt ≤ 3e4.

---

## 3. Build milestones (smallest first)

Engineering hours are Claude-session estimates and include validation.
Compute is for the milestone's own validation. Search compute is in §4.

| # | milestone | eng-h | validation compute | unlocks (net mass) |
| --- | --- | ---: | --- | --- |
| **M0** | Safety net: X1 driver classes, write-first records, bounded optional translate search, descendant blocking on non-ok, A9 hashing and manifest, record schema with hypothesis vector and mu sidecar. Applies to the v3 driver and a v3 copy of `search_ref`. | 2–3 | 0 | Nothing new; makes every later run safe |
| **M1** | v3.0 engine: X2–X5, A2, A3, A7 in a copy of `v2engine.cpp`. Rebuild against PMULL gf2x (M5) and tuned PCLMUL gf2x + bitpolymul (jobe), in a **persistent prefix** (not `/tmp/xb`). | 5–7 | A10 set on both builds: about 2 ch (jobe) + about 3 M5-core-h | v2's reach at 7–10x the speed |
| **M1b** | mu cross-validation (X6): dual-builder target formation, flat norm to F_{2^h}, minpoly, and comparison against v3 `mu`. This doubles as the Level-3 replay kit for hits with E ≤ 1e7. | 3–5 | about 100 rows at E ≤ 3e5: 3–10 ch (flat norms on jobe; builds on either machine) | Turns the 0.063 provisional ratio/finite mass into real coverage |
| — | **CP0** | — | — | Go/no-go for L1 |
| **M3** | sz path: Z rows with one big odd-prime component. Radicand `alpha_r`, translate `z = Σ small components ∈ k`, `B' = lcm(b_r, A)`, `t = lcm(t0, A)`, test `W_z = V^D F_a(z/V)`. Inherits X2–X5. | 4–6 | 105 Peeters rows of this shape (33 with E ≤ 2e4 also per-translate vs the unpatched ref with independent encoding), 10 rows of mu vs dual: 2–5 ch | 972 rows ≤ 1e5 (0.0254 gross) + 9,511 rows in (1e5, 1e6] (0.0246) [checked, perf §0] |
| **M4** | Euler stage. Own H ring: sparse k modulus, monomial c, Kronecker products straight into `gf2x_mul`. Compact final: minpoly `g_h` of `N_h` by BSGS power projection; Rabin on `g_h`, `g_h(N_h) = 0`, degree check; Euler test in `F_2[x]/g_h`. **`mu = g_h` for free on every row.** Lift the `Rt ≤ 4e6` policy cap. | 12–16 | Full A10 set; old-vs-new `mu` bit-equality on every validation row (strong h-bit regression); `--direct` agreement: 3–5 ch | 4–20x cheaper rows [estimate]; brings in the B ≤ 6e4, Rt > 4e6 class (0.0367 gross) |
| **M5** | K scale-up. Field interface with a flat sparse backend and a two-factor coprime tensor backend (`t | B1`, both factors ≤ 6e4, partial Frobenius). Hilbert-90 roots (crossing.md Thm B) for the crossing and for each component. Charpoly by power projection + half-gcd BM over k, with the X5 identities kept. | 25–35 | Tensor vs flat element equality and mu equality on 1487, 1307, 839, 359+1433. **Reproduce 719** (the only certificate-only row; `B = E(359) = 3,504,820 = 179·19,580` admits a coprime split with `179 | B1`, admissibility to be checked by the planner) [derived, rough]. 5–15 ch, 719 on the M5 if memory-heavy | Two-factor splits cover 0.0766 of the 0.0856 gross B > 6e4 mass ≤ 1e5, plus about 0.07 in (1e5, 1e6] [checked, perf §0] |
| M6 | *(optional)* R3 double crossing, and the dual-builder flat path for all-small multi rows with E in (6e4, 1e6]. Needs a GF2EX half-gcd resultant. | 20–30 | multicomponent V1 rows (617, 2003, 1303, 9199, 27281) | +0.012 at 1000 ch, about 0.0005 per eng-h. Build only if a9 wants a nearly complete table to 1e5. |

Not built: Theorem-C deep recursion (B > 1e9, 0.006 gross ≤ 1e5), R5/R6, a
truncated additive FFT, VPCLMULQDQ kernels, `(Q, m)` grouping beyond `h`, the
flat builder as a coverage engine, and ancestor gating.

**Cumulative reach.** These are the performance review's curves (gross,
both pools: ≤ 1e5 plus (1e5, 1e6]), shifted to net by subtracting about
0.025 of already-tested cheap mass [estimate].

| after | 100 ch | 300 ch | 1000 ch | 3000 ch | ceiling |
| --- | ---: | ---: | ---: | ---: | ---: |
| M1 (= perf B) | 0.14 | 0.15 | 0.16 | 0.17 | 0.19 |
| M3 (C) | 0.16 | 0.17 | 0.18 | 0.19 | 0.21 |
| M4 (D) | 0.18 | 0.19 | 0.20 | 0.21 | 0.21 |
| M5 (E) | 0.24 | 0.27 | 0.29 | 0.31 | 0.38 |
| M6 (F) | 0.25 | 0.28 | 0.30 | 0.32 | 0.40 |

- Sensitivity [estimate, perf §2]: with the B > 6e4 K side ×30 and Euler ×5,
  M5 at 300 ch drops from 0.27 to about 0.23 net. The ordering holds.
- The ≤ 1e5 pool alone reaches about 0.24 net at the M6 ceiling, of 0.2555.
  The residue is B > 1e9 chains (the 2879 type) and a few odd shapes.

---

## 4. Launch plan

### 4.1 Queue

- **One order-free queue** over net-uncovered rows in both pools.
  - Unit: one engine run per `(h, path-shape)` group; rows sharing h share a
    run.
  - Priority: mass/cost from the refit cost model, with per-job caps instead
    of fixed B and Rt caps.
- Every row runs under the assumed rule for unverified closure rows.
  - A passing run upgrades its uncertified ancestors to "certified
    rule-translate non-power", through X2 and the degree/non-residue checks.
  - With the forcing theorem that is `m_r = rule(r)`.
- The reference fallback for E ≤ 6e4 refused shapes uses the M0 driver.
- After each milestone, re-plan the remaining queue with the newly
  supported paths and refit costs from 10–20 timed rows. Large-Rt and large-B
  rows are deliberately included, because the fit is unmeasured past
  Rt = 1.07e6.

### 4.2 Machines

**jobe**
- Runs the bulk queue and every job whose H products exceed 8e6 bits (2Rt).
- Policy: `nice 19`, at most 12 concurrent jobs, at most 3 GB per job,
  `ulimit -v` set.
- CPU-only. a9's partner shares the box: if their pipeline is running, keep
  our load from crowding it, and drop to 8 jobs if load rises above 20.
- Builds live under a persistent prefix in jobe's home, outside the
  transformer and interpretability workspaces.
- C++ only. No ad hoc Python installs, per the dependency-ownership rule: the
  driver needs only the standard library plus the census pickle.

**M5**
- Runs jobs with products ≤ 4e6 bits, and K-side jobs that need more than
  about 8 GB (B ≥ 1e7, the 719 replay).
- Also runs the A10 regression suites, all dual-builder model builds, and the
  PARI/flint certificate checks (micromamba `excess` env).
- Replays every hit on the other multiplier.

**Records.** Results go to `v3/results.jsonl` on the M5, which is
authoritative. The jobe queue writes locally and syncs every 15 minutes. A
non-`ok` class triggers an immediate sync and a queue pause.

### 4.3 Order, budgets, checkpoints

Each checkpoint is a hard stop: write a report, then a9 decides whether to go
on.

1. **Now.** §1 hazard handling, then M0, M1 and M1b.
2. **CP0** (about 10–15 ch of validation spent).
   - Report the A10 results on both builds and the mu cross-validation table
     per path.
   - Any `mu` mismatch, or any A1–A9 failure on a known row, means **stop
     and debug**. No search.
3. **L1 = M1 engine on its reach** (net about 0.098 plus up to 0.008 of
   ref-fallback rows).
   - Budget **100 ch**, mostly jobe; expected wall time under a day.
   - Engineering on M3 and M4 continues in parallel.
4. **CP1** (100 ch cumulative).
   - Report rows, mass, per-path counts, cost refit, and the exact-table
     delta.
   - Start the Peeters-only replay lane, background and low priority, at most
     100 ch:
     - 99 rows, 0.0143 mass;
     - ref for E ≤ 6e4, the sz path where it applies, the dual builder plus
       flat Euler otherwise.
5. **L2 = M3 + M4 engines** on the re-planned queue, cumulative cap
   **300 ch**.
6. **CP2.** Same report, plus the go/no-go for M5, the largest engineering
   item.
7. **L3 = M5 engine**, cumulative cap **1000 ch**, about 3 days on both
   machines.
8. **CP3.** Final report. Anything further (to 3000 ch, the M6 build, or
   (1e6, 1e7]) needs a9's separate decision. The marginal mass per ch there
   is about 0.02 per 2000 ch.

**Pause on any detection.** On `HIT_CANDIDATE`,
`ANCESTOR_FAILURE_CANDIDATE` or `FORCED_FAILURE`:
- pause the queue and run §5 Levels 0–2 automatically;
- run Level 3 inside a separate certification budget of 50 ch;
- report to a9 before resuming the search or making any claim.

---

## 5. Hit-certification protocol

This adopts redteam §7, tightened with the exactness review's A8 and the
ancestor case.

**Level 0, detection (automatic).**
- Write and flush the record first.
- Archive the planner output, the engine program, the binary hash, the
  gf2x/NTL build ids, the moduli, the seeds and the full stdout/stderr.
- Freeze every row whose closure contains p, or r.
- No announcement.

**Level 0b, ancestor-failure candidate at r.** The FATAL itself is the
evidence:
- a root `y ∈ F_{2^{b_r}}` with `y^r = alpha_r`; or
- for the top prime, `c` an r-th power in k.

Extract an explicit witness `y` with the exact checks `y^r == alpha_r` and
`y^(2^{b_r}) == y`. Then certify **row r itself** through Levels 1–5, as a
top row if reachable, otherwise from this witness plus independent replay of
`alpha_r`.

**Level 1, internal replay (same code family).**
- Rerun with a different admissible t (`t_mult > 1`), a different K modulus,
  a different k generator and fresh seeds, on the other machine and so on the
  other multiplier.
- Add `--direct` when Rt allows.
- **`mu` must be bit-identical.** A mismatch is a bug, not a hit.

**Level 2, model-free certificate.**
- Emit `mu` and the exact exponent.
- In PARI, inside `a = ffgen(mu)`, check:
  - `polisirreducible(mu)` (or `deg mu < h`, which is itself a hit, since
    `f(p) = h`);
  - `a^((2^h-1)/p) == 1`;
  - a witness `delta = sqrtn(a, p)` with `delta^p == a`. This works for
    Wieferich p too.
- For ratio and finite rows, the certificate states that it covers `1 + z`.
  It also proves y2 is a p-th power from X3's exact `(R2·B) % h != 0`,
  re-derived by the replay and not taken from the planner.

**Level 3, independent replay.** An implementation sharing neither v3's
planner nor its arithmetic reproduces `mu` bit for bit:

| E | replay route |
| --- | --- |
| ≤ 6e4 | also the ref engine on `rowprog.py` + `census.py` |
| ≤ 1e7 | the dual builder with its own planner, its presentation certificate checked in PARI/flint (MulMod-only), then the flat norm and minpoly on jobe (the M1b kit) |
| > 1e7 | a second crossing implementation in python-flint (`crossing.md` path A/B with `xlib.py`; multicomponent R1–R3 for Z), with a **different cut** |

- Also replay 3–5 neighbouring non-hit rows of the same path and size, and
  require `mu` to match there too.
- Negative control: a Frobenius-twisted shared branch must change `mu`
  (`proto/negctl.py`).
- Asking Peeters to run the row is a9's call.

**Level 4, census and ancestry.**
- Re-derive by hand and with an independent census: `f(p)`, `Q(h)` with each
  exclusion decision, the arm, `rule(p)`, E, and the closure.
- For each closure prime, cite this run's exact-degree or non-residue
  certificate, or verify it independently.
- Cite the forcing theorem (proved in the paper) for `m_r = rule(r)`, and
  state its Lean boundary.

**Level 5, review and claim.**
- Codex adversarial read via gaslamp, sending raw `mu`, the programs and the
  census tree.
- A full-mode certificate script in `experiments/`, 719-style, with no quick
  mode that skips a link.
- Claim level per AGENTS.md: "implemented and tested (exact certificate)":
  - p is a counterexample to the 0/1/4 rule;
  - not "least";
  - no true `m_p` unless it was computed (impossible on ratio and finite
    paths);
  - Lenstra boundedness untouched;
  - what Lean does not check, stated.
- Then update `docs/OPEN.md`, invalidate cached descendants, and recompute
  them under the corrected `alpha_p` (degrees move only if `m_p ≥ 2`).

**Gates.**
- Levels 0–2 support "candidate" only.
- Level 3 supports "the conjecture is false": p, or the named ancestor.
- Levels 3, 4 and 5 together support "p is a counterexample".

---

## 6. Honest expected yield

The heuristic is the random model: row p fails with probability about 1/p,
independently [estimate]. Expected failures equal the mass reached. The
clean record so far (128 rows to 727, plus about 0.30 of clean mass above)
gives a Bayes factor of about 2.8–3.8 toward a hidden theorem, so P(random
model | data) is about 0.21–0.43 at an even prior [redteam §1.4; estimate].
shortcuts.md's wider range would raise the top end.

| stage (cumulative ch) | net mass | E[hits] (random model) | P(≥1), random model | P(≥1), discounted |
| --- | ---: | ---: | ---: | ---: |
| L1 (100 ch, M1 engine) | about 0.14 | 0.14 | 13% | about 3–6% |
| L2 (300 ch, M3 + M4) | about 0.19 | 0.19 | 17% | about 4–7% |
| L3 (1000 ch, M5) | about 0.29 | 0.29 | 25% | about 5–11% |
| M6 ceiling (>3000 ch) | about 0.40 | 0.40 | 33% | about 7–14% |

Caveats:
- All randomness evidence comes from E ≤ 8000. Every uncovered row has large
  E and deep chains (missing-list minimum E = 2.0e6), a regime where the model
  is untested in either direction.
- Engineering hours and the post-M4 cost curves are modelled. The B > 6e4 K
  side is unmeasured.
- Coverage on the ratio and finite paths is provisional until M1b passes.

Near-certain deliverables:
1. Exact `m_p` for every non-hit row run. For Z rows a pass means `m_p = 0`.
   For O/C/D rows it gives `m_p = rule(p)` via the forcing theorem. This
   extends A380496 well past 709, with gaps that are documented by shape.
2. A canonical `mu` per row, model-independent and reusable as a replay key.
3. Certified closure ancestors, including rows v3 cannot run as tops.
4. An exactness-hardened engine family with a standing certification kit.

Value per hour drops sharply after M5. Past CP3, further compute is mainly
completeness of the table rather than a better hit probability.

---

## 7. Open items for a9

- Peeters' provenance: source, method and version. The live paper and bib do
  not cite them [checked, redteam §3]. Whether to ask them to replay a
  candidate is a9's call.
- Go/no-go at each checkpoint, and whether M6 is wanted (a near-complete
  table to 1e5).
- Whether the exact table is worth a writeup independent of any hit. That
  prose would be a9's; the drafting would be bullets.
