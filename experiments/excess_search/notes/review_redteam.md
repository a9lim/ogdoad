# Red team: the overall counterexample-search plan

Scope: the reachable-mass and P(hit) estimates, the conditional-on-rule
falsification claim, how Peeters' values are used, and the certificate a hit
would need. No rows were computed. The only computations here are sums of
`1/p` and set operations over files that already exist (`peeters_records.json`,
`missing_below_12289.json`, `rows_100000.pkl`, `v2/coverage_100000.json`, the
validation logs, `ref/results_ref.jsonl`, `design/shortcuts/newrows.txt`).

Tags: **[checked]** means computed here from those files or read directly in
source. **[derived]** means a short argument given here and not executed.
**[estimate]** means an extrapolation.

**Snapshot caveat.** A reference-engine search (`search_ref.py 60000 100000 10`)
was running during this review. It was appending to `ref/results_ref.jsonl`,
which had 632 lines at 2026-10-20 00:32 EDT. Every count below that uses ref
results is a snapshot, and the "not yet done" numbers shrink as that search
runs.

---

## 0. Verdict

1. **Every planning document double-counts.** The P(hit) figures in SPEC §4,
   Codex's 0.25–0.38 mass, the models schedule (0.20 at 0.3 core-h, up to
   0.398), crossing's "13%", and shortcuts' "10–15%" are all computed on
   `(727, X]`. They ignore Peeters' 1,023 rows and the session's own runs. The
   cheap end of every curve has already been harvested.
   - Net uncovered mass up to 1e5 is **0.2555** (8,252 rows). v2's marginal
     reach is **0.098** (2,481 rows), not 0.116.
   - Under the random model with independence, that reach gives P(hit) =
     **9.3%**. Testing everything up to 1e5 would give 22.5% [checked mass;
     model assumption stated].
   - The clean record lowers these. Discounting by the data's Bayes factor at
     an even prior gives about **2–4%** for v2's reach and 5–10% for everything
     up to 1e5 [estimate].
2. **Dependency chains are currently a non-issue for v2's reach.** No
   v2-reachable uncovered row has a closure ancestor outside the set already
   computed by some source [checked]. Unverified ancestry matters only for rows
   v2 cannot run anyway.
3. **The conditional falsification claim is correct, and for v2 and ref it is
   stronger than stated.** Their exact-degree and irreducibility checks certify
   every closure ancestor's rule translate as a non-power. A fully checked hit
   is therefore a hit *at p*, modulo planner correctness and the paper's
   forcing theorem.
   - It is weaker for the dual builder.
   - **Operational hole:** an ancestor failure surfaces as a generic `FATAL`
     engine error, which both search drivers treat as an error and continue
     past.
4. **Validation is much weaker than "0 disagreements" suggests.**
   - Outcome agreement is one bit, which a value-randomizing bug matches with
     probability ≈ 1 − 1/p.
   - The arm-O `m = 0` forced translate is **value-blind**: it is a p-th power
     for any radicand.
   - The planner's term-algebra relations are shared by v2 and ref.
   - None of v2's ratio or finite rows has element-level external validation.
   - The dominant risk to the search's *value* is a false negative, which no
     current validation can detect.
5. **A hit needs a canonical certificate.** That is
   `mu = minpoly_F2(N_{F_E/F_{2^h}}(beta))`, plus a p-th-root witness. It must
   be reproduced bit for bit by an implementation that shares no planner code
   with v2. The protocol is in section 7.
6. **Two driver bugs.**
   - In `search_ref.py`, a hit whose further-translate run errors loops
     forever and is never written or printed.
   - `forced_ok = false` sets `known[p] = None`, which unblocks descendants
     with a `None` excess.

---

## 1. Mass accounting

### 1.1 What is actually covered [checked]

| range | rows | mass `sum 1/p` | status |
| --- | ---: | ---: | --- |
| 3..727 | 128 | 1.6525 | OEIS A380496 plus the 719/727 certificates |
| 733..12281, Peeters | 1,023 | 0.2741 | all obey the rule. 797 rows (0.2598) were reproduced, one bit each, by some session engine (v2 validation, ref, shortcuts' PARI tower). 99 rows (0.0143) are **Peeters-only**. |
| 733..12281, missing | 444 | 0.0780 | min E = 2,036,268, so "all E > 1e6" holds. v2 did 16 of them (0.0082). |
| 12289..1e5 | 8,123 | 0.2006 | ref and shortcuts already did 299 (0.0150) |
| **net uncovered ≤ 1e5** | **8,252** | **0.2555** | 428 (0.0698) below 12289, plus 7,824 (0.1856) above |

The missing list is exactly the complement of Peeters in the odd primes up to
12281, apart from 719, which is certificate-covered. The 719 certificate is
the only support for that row: v2 cannot reach it (`B = E(359)` is far above
6e4), and its quick mode does not establish the characteristic-polynomial link
(Codex). Its mass is 0.0014.

### 1.2 The SPEC §4 table, restated net of coverage [checked]

| E budget | SPEC: rows, mass, P | **not yet done: rows, mass, P** |
| --- | --- | --- |
| E ≤ 1e5 | 1,392, 0.2106, 19.0% | **555, 0.0129, 1.3%** |
| E ≤ 1e6 | 2,823, 0.3182, 27.3% | **1,696, 0.0452, 4.4%** |
| E ≤ 1e7 | 4,436, 0.3970, 32.8% | **3,234, 0.1038, 9.9%** |
| E ≤ 1e8 | 5,875, 0.4513, 36.3% | **4,665, 0.1540, 14.3%** |
| all ≤ 1e5 | 9,463, 0.5528, 42.5% | **8,253, 0.2555, 22.5%** |

The same correction applies to the other documents:

- **models.md §0.7 and §5.** "P(hit) ≥ 0.20 at 0.3 core-h" is entirely the
  Peeters-covered region. `schedule.py` filters on `727 < p` only.
- **crossing.md §0 and §11.** "98% of arm-O/C/D mass below 1e4" and "about 13%
  hit probability" use `(727, X]`. Most of that mass is in Peeters. What is
  left below 12289 is the 266 arm-O missing rows, and v2 reaches 107 of them
  (0.0221) at `B ≤ 6e4`, `Rt ≤ 4e6`.
- **Codex §6 and the v2 README "all" column.** Of the 0.3279 that v2-type
  paths reach on `(727, 1e5]` at `B ≤ 1e6` and `Rt ≤ 1e6`, about 72% was
  already covered.
- **shortcuts §0 and §3.5.** "Cheap mass about 0.30 below 1e4" and the 7–20%
  yield are on `(727, X]`.

### 1.3 Net uncovered rows by v2 status [checked]

All figures assume the rule for ancestors (census degrees).

| status | rows | mass |
| --- | ---: | ---: |
| **reachable** (`B ≤ 6e4`, `Rt ≤ 4e6`) | 2,481 | **0.0979** |
| refused: `B > 6e4` | 2,723 | 0.0856 |
| refused: `Rt > 4e6` | 1,522 | 0.0367 |
| refused: Z with ≥ 3 components | 1,176 | 0.0256 |
| refused: inherited level | 373 | 0.0106 |
| refused: ZF | 1 | 0 |

- The reachable mass splits as ratio 0.058, singleton 0.035, finite 0.005.
  **65% of v2's marginal mass is on the ratio and finite paths, the least
  validated ones** (section 5).
- The tensor K model would lift the B cap to 1e6 and give 0.119 (2,769 rows),
  a gain of 0.021.
- Of the 0.098 reach, 0.074 has `E ≤ 1e7` and 0.096 has `E ≤ 1e8`. This sets
  which independent replays are feasible (section 6).
- **CPU is not the binding constraint.** A rough model, scaled from the
  measured 16529 and 1487 runs (Euler ∝ effective h × Rt^1.1, K-side ∝ B²),
  puts the whole reach at about 100 core-hours on the M5 conda stack, with
  0.08 of mass in the first 13 core-hours [estimate]. Structure is what limits
  the reach.
- Cheap mass is still on the table: 555 not-yet-done rows with `E ≤ 1e5`
  (0.0129). The running ref search is eating the part with `E ≤ 6e4`.

### 1.4 P(hit), stated honestly

Under the random model, independence gives P = 1 − exp(−mass): **9.3%** for
v2's net reach, 11.2% with the tensor model, and 22.5% for everything up to
1e5.

The model itself needs a discount [estimate]:

- shortcuts §3.4 gives a Bayes factor of 2.1–2.8 toward a hidden theorem from
  the 128 rows up to 727 (generator-corrected).
- The 0.297 of further clean mass above 727 multiplies it by e^0.297 = 1.35,
  giving **2.8–3.8**. If small rows are discounted entirely, the lower bound is
  1.35.
- At an even prior, P(random | data) is therefore 0.21–0.43.
- So P(hit) is about **2.0–4.0%** for v2's reach and **4.7–9.7%** for all
  rows up to 1e5.
- Beyond 1e5 the next two decades carry 0.18 and 0.15 of mass, at unknown
  reach.

Also note: all randomness evidence (shortcuts §3.3) has `E ≤ 8000`. The
uncovered rows are all large-E, deep-chain rows (missing min E = 2.0e6), a
regime the model has never been tested in. The search remains defensible as a
long shot with an exact-table byproduct. It should be described that way, not
by the 20–40% figures.

### 1.5 Dependency chains [checked]

- **v2-reachable uncovered rows with any closure ancestor not computed by some
  source: 0.** The same holds with ancestors restricted to "neither done nor
  v2-reachable". Every ancestor of every reachable row is already in the OEIS,
  certificate, Peeters, ref, shortcuts or v2 results.
- Rows up to 1e5 with a Peeters-only ancestor: 119 (0.0032). None is
  v2-reachable.
- 643 rows in 12289..1e5 (0.0152) depend on a missing row, and 44 missing rows
  (0.0068) depend on another missing row. All are outside v2's reach.
- Both drivers wait for every closure prime to be `known`
  (`search_v2.py:63`, `search_ref.py:51`). Neither runs in order-free
  speculative mode, so the "assume ancestors" logic is not exercised today.
  Ancestors do enter as Peeters values, which equal the rule.

---

## 2. Conditional-on-rule falsification

### 2.1 The claim is correct [derived]

Let `H(p)` say that `m_r = rule(r)` for every r in the closure `D(p)`. Under
`H(p)` the presentation an engine builds is the term algebra, and that
includes the census Q sets and degrees.

- If `H(p)` holds and the run says the rule translate is a p-th power, then
  `m_p ≠ rule(p)`.
- If `H(p)` fails, the conjecture fails at some r.

Either way the conjecture is false.

Requirements:

- the computation is exact *under* `H(p)`;
- the census and degrees come from `H(p)`;
- no input reflects any other hypothesis. Cache keys must carry the
  hypothesis (Codex §5).

The forcing theorem is **not** needed for falsification: if some ancestor's
excess is not its rule value, the conjecture is already false.

### 2.2 v2 and ref prove more [derived from source]

Both engines build every closure component with an exact-degree check:

- `v2engine.cpp:747` "component exact degree" and `refengine.cpp:227`;
- for the top v2 radical, `v2engine.cpp:920` "c not an ell-th power in k".

Take an ancestor r with `kappa_{f(r)} + rule(r)` an r-th power in
`F_{2^{b_r}}`. Then all roots of `X^r − alpha_r` lie in `F_{2^{b_r}}`, because
`f(r) | b_r`. So `y^(2^{b_r}) = y` and the degree check fails.

For the ratio path, irreducibility of `X^{R1R2} − alpha_{r1}^{R2}/alpha_{r2}^{R1}`
over K certifies both top rows. This uses `r_i ∤ [K : F_2(alpha_{r_i})]`,
which the planner's `E = R B` refusal of inherited levels guarantees.

Hence a run that passes all checks certifies "rule translate not a power" for
every r in `D(p)`. With the paper's forcing theorem (smaller translates are
forced powers; proved here, with the Lean boundary to be stated), it gives
`m_r = rule(r)`. **A checked v2 or ref hit is a counterexample at p itself.**
It is not merely "p or an ancestor".

Caveat: this rests on facts the engine does not check. These are the
planner's relations, `h ∤ d(y2)`, and the translate encoding (section 5).

### 2.3 Where the claim is weaker

- **Dual builder (models.md).** `deg P = E` is "necessary but not sufficient"
  (§6). The presentation-ideal certificate's maximality cites Lenstra's
  theorem, which *presupposes* `H(p)`. If an ancestor fails, the quotient is a
  product of fields and nothing in the builder fails.
  - So dual-builder hits are only "p or an ancestor".
  - Naming p needs separate ancestor certification, for example by the
    component-image relations plus exact degree checks of each image.
- **Free chain moduli and cached norms.** `P_a(X^R)` is irreducible only under
  `H`. A norm cached by `(h, m)` is valid only for the hypothesis it was built
  under.

### 2.4 Operational holes [checked in source]

- **Ancestor failure looks like a crash.**
  - `need()` in v2 calls `die()`, which exits with code 2. `driver.py` stores
    this as `error`, and `search_v2.py` prints `!!!` and moves on.
  - `search_ref.py` prints `ERROR …` and continues, and **does not write the
    record** to `results_ref.jsonl`.
  - The check names above must instead be classified as
    `ANCESTOR_RULE_FAILURE r=…`, which stops the search and starts
    certification.
- **The ref hit can be swallowed.** On a hit, `search_ref.py` runs
  `while True: … if 'pth_power=0' in o2.stdout: break; m += 1`, which has no
  returncode check and no bound. If any further-translate run errors (larger
  m changes `d(m)`, hence E), the loop never ends. The worker hangs, and the
  `!!! COUNTEREXAMPLE` line is never printed or written.
  - Fix: write and flush the hit record first, then bound m and check the
    return code.
- **`None` excess propagates.** In `search_ref.py`, `forced_ok = false` gives
  `d['m'] = None` and `known[p] = None`. Since `deps ⊆ set(known)` then holds,
  descendants launch with a `None` excess. This should block them instead.
- **v2's planner refuses descendants of a hit** ("excess … != rule (not
  handled)"), and `verdict()` leaves `m` as `None`. That freeze is correct, but
  it means v2 cannot continue past a hit.

### 2.5 Claims never available

- "**Least** counterexample". Many smaller rows are refused or out of reach,
  for example the 2879 chain.
- The **true m_p** on ratio or finite rows. `beta + m` is not binomial there.

---

## 3. Peeters' values

- **Contents [checked]:** 1,023 odd rows up to 12281, all equal to the rule
  value. 797 of the 896 rows above 727 (0.2598 of 0.2741) were reproduced, one
  bit each, by v2 validation, ref, or the shortcuts tower.
- **Peeters-only rows:** 99 (0.0143). 97 are arm Z (51 with three
  components, which v2 refuses), and E runs from 8,568 to 1,874,628.
- **Role A, ancestor values.** They equal the rule, so using them is identical
  to assuming the rule. Falsification needs no trust in them (section 2.1).
- **Role B, coverage.** This *does* need trust. If Peeters' engine had a
  false-negative bug, up to 0.274 of mass would be wrongly retired. 0.0143 of
  it has no second implementation, and all of it has only one-bit
  corroboration.
- **Role C, census validation.** This is the strongest use. A mis-assigned arm
  or Q set changes the predicted value, so 1,023 agreements strongly validate
  the census logic up to 12281. They do not validate element values.
- **Provenance.** The live `writeups/excess.tex` and its `.bib` contain no
  Peeters citation; only a stale `excess.aux` does [checked]. Before any
  write-up uses these rows, record their source, method and version.
- **Action.** Replay the 99 Peeters-only rows. Use ref where `E ≤ 6e4`, and
  otherwise the dual builder plus a flat norm-first Euler test. At
  `E ≤ 1.9e6` that is at most about 1–2 core-h per row on jobe [estimate].

---

## 4. The canonical invariant (used by sections 5–7)

For the selected element `beta = kappa_{f(p)} + rule(p)` in `F_{2^E}`, with
`h = f(p)`, put

```text
T = N_{F_{2^E}/F_{2^h}}(beta),        mu = minpoly_{F_2}(T)   (degree d | h).
```

[derived]:

- Embeddings differ by Galois automorphisms, and the norm commutes with them,
  so `mu` is **independent of every model and root choice**.
- `beta^((2^E-1)/p) = T^((2^h-1)/p)`.
- Since `f(p) = h`, every element of a proper subfield is a p-th power. So the
  hit criterion is: `deg mu < h`, **or** `X^((2^h-1)/p) ≡ 1 (mod mu)`.
- Witness: for non-Wieferich p and `deg mu = h`, with `N' = (2^h-1)/p` and
  `delta = X^(p^{-1} mod N') mod mu`, we have `delta^p ≡ X`. Checking it takes
  seconds in PARI or flint for `h ≤ 1e5`, together with
  `polisirreducible(mu)`.
- Wieferich primes 1093 and 3511 need the full p-primary exponent.

For the ratio path, v2 tests `1 + z`, not beta. Its `mu` is for
`N(1 + z) = N(beta)/N(y2)`. The certificate must name which element it covers.
Ideally v2 also emits `N_h(y2)`, so that `mu(beta)` can be compared across
engines.

`mu` turns each comparison from one bit into about h bits.

---

## 5. Validation power: what "0 disagreements" means

### 5.1 One-bit agreement is weak [checked]

A bug that replaces the tested element by an unrelated one, with correct
degree, matches "not a power" with probability 1 − 1/p. The detection power
of the existing validation is about `sum 1/p` over the rows that exercise
each path.

| path (final binary) | rows | `sum 1/p` | `sum 1/p` over p > 100 |
| --- | ---: | ---: | ---: |
| singleton | 235 | 0.78 | 0.26 |
| ratio | 219 | 0.24 | 0.19 |
| finite | 61 | 0.23 | 0.08 |

The preliminary 838-row run is almost the same: ratio 0.26 and 0.22, finite
0.23 and 0.08.

So a value bug confined to the ratio path at p > 100 has about a 17% chance
of being detected [estimate under the uniform-bug model]. Peeters' and ref's
agreement has the same one-bit character.

### 5.2 The arm-O forced translate is value-blind [derived]

v2 computes `W_0 = N_{KH/H}(aV) = N_{K/k}(a) · V^D`.

- `p ∤ 2^t − 1`: h divides t only if R divides t, and r does not divide B,
  because every prime factor of `b_r` is below r.
- So `N(a) ∈ k^x` has order prime to p.
- `V^{R(2^t-1)} = 1` with `p ∤ R(2^t − 1)`.
- Both factors are therefore p-th powers in `F_{2^{Rt}}`, **for any nonzero
  c and a**.

The same argument in the full field shows that `chi_R` is a p-th power for any
radicand. "Forced translates OK" is a positive control on the Euler code. It
is not evidence that c, a, F_a, the components or the phases are right. Only
the arm C/D forced translates, from the torus mechanism, are plausibly
value-sensitive, and there are 7 such rows.

### 5.3 Common-mode surfaces

- **The planner is shared.** `plan.ref_program` emits ref programs "as
  `../ref/rowprog.py`", and `census2.py` is a copy of `census.py`. Per-translate
  ref agreement therefore does not test the term-algebra relations, the
  translate encoding, the ratio orientation, or the choice of y2.
- **NTL is trusted by both.**

### 5.4 What is element-level today

| evidence | source |
| --- | --- |
| v2 `thetacheck`: minpoly of `N(1 + chi_179)` equals the 359-certificate theta | one conductor, singleton path |
| dual builder P vs a numpy literal-term-algebra plus BM oracle, 96 rows with `E ≤ 6000`; vs a second builder, 10 rows | models.md §0.2 |
| crossing T1 and T3 | crossing.md |
| multicomponent R1/R2 element equality, 61 rows | multicomponent.md |

**None of these touches v2's ratio or finite paths.**

### 5.5 Consequence

Exact internal checks make false *positives* unlikely, and the protocol in
section 7 catches the rest. The unguarded failure mode is a false
*negative*: a valid field model of the wrong element that silently retires
mass. Until it is fixed, v2 non-hits on ratio and finite rows should be
counted as provisional coverage. The fix is recommendation 2.

---

## 6. Independent routes, and what each can replay

| route | shares with v2 | replay range for a hit | compares | status |
| --- | --- | --- | --- | --- |
| v2 rerun with another admissible t, another K modulus, another k generator, on the other machine (jobe PCLMUL vs M5 conda gf2x) | all code | all v2 rows | `mu` | detects model dependence, nondeterminism and hardware faults only |
| ref engine (full field) | census, relation emitter, NTL, Kummer-root method | `E ≤ 6e4` (sparse irreducible) | outcome; would need a small extension to emit `mu` | validated one bit |
| **models' dual builder plus flat Euler** | NTL GF2X only; own planner (`proto/terms.py`, `plan.py`) and own builder | build to `E ≈ 5e7`; norm-first Euler ≤ about 1 day at `E ≈ 1e7` on jobe [estimate from `schedule.py`'s CompMod model]. Covers 0.074 of the 0.098 reach. | `mu`; its presentation certificate checks in PARI/flint with only MulMod | element-level validated, but not on Euler rows above 727 |
| crossing.md prototype (python-flint `xlib.py`, path A/B, Hilbert-90 roots) | the crossing theorem only | singleton tops; multi-component radicands need arm-Z import | `mu`, `T_h` | element-level checks T1/T3 |
| multicomponent.md R1–R3 resultants | the pinning theorem only | Z rows; `n' = (1, 2)` checked only at 617 | element | prototype |
| shortcuts PARI tower / `crossed_row.py` | none (PARI) | small E; selected crossed rows | outcome, `T` | 349 rows |
| Rust `Ordinal` / `experiments` TermAlgebra | none | tiny fields | element | validates routes, cannot replay hits |
| Peeters' term algebra | none (external) | apparently `E ≲ 2e6` | value | asking Peeters is a9's call |

Above `E ≈ 1e7` no full-field replay is practical. Certification there needs
two crossing-type implementations in different libraries, with different
cuts, agreeing on `mu`.

---

## 7. Hit-certification protocol

**Level 0: detection.** The engine reports `rule translate pth_power=1`, or
an ancestor-rule check fails.

- Write the record before doing anything else.
- Freeze every row whose closure contains p (or r).
- Archive the program, the planner output, the binary hash, the NTL/gf2x
  versions, the moduli and the full log.
- No announcement.

**Level 1: internal replay** (same code).

- Rerun with a different admissible t (non-minimal if possible), a different
  K modulus, a different k generator and fresh randomness, on the other
  machine.
- Run `--direct` if `Rt` is feasible, and `--minpoly`.
- **`mu` must be bit-identical** across runs.
- A Level-1 mismatch is a bug, not a hit.

**Level 2: canonical certificate.**

- Emit `mu`, the witness `delta` (or `deg mu < h`), and the exact Euler
  exponent.
- For ratio and finite rows, also emit `mu(N_h(y2))` and `d(y2)`, with
  `h ∤ d(y2)` checked by the replay rather than taken from the planner.
- Check `mu` irreducible and `delta^p ≡ X (mod mu)` in PARI/flint. This
  settles the last step, model-free.

**Level 3: independent replay.** An implementation that shares neither
v2's planner nor its arithmetic reproduces `mu` bit for bit.

- `E ≤ 1e7`: the dual builder with its own census, its presentation
  certificate checked in PARI/flint, then a flat norm-first Euler test on
  jobe. Add ref if `E ≤ 6e4`.
- `E > 1e7`: a second crossing implementation in python-flint or PARI
  (crossing.md path A/B; multicomponent R1–R3 for Z), with a different cut.
- Both cases: run the same replay on 3–5 neighbouring non-hit rows of the
  same path and size, and require `mu` to match there too.
- Negative control: Frobenius-twist one shared-component branch and require
  `mu` to change (models `negctl.py`).
- If feasible, ask Peeters to run the row. That decision is a9's.

**Level 4: census and ancestry.**

- Re-derive by hand (the tree is small) and by an independent census:
  `f(p)`, `Q(h)` with its exclusion decisions, the arm, `rule(p)`, E, and the
  closure `D(p)`.
- For every r in `D(p)`, cite the run's exact-degree checks, or verify r
  independently.
- Cite the forcing theorem for `m_r = rule(r)`, and state its Lean boundary.
  For dual-builder-only evidence, add explicit ancestor checks (section 2.3).

**Level 5: review and claim.**

- Get an adversarial read from Codex (gaslamp) of the certificate and the
  census tree.
- Ship a full-mode certificate script in `experiments/`, in the style of 719
  but with no quick mode that skips a link.
- Claim level, per `AGENTS.md`: "implemented and tested (exact certificate)".
  Name p as a counterexample to the 0/1/4 rule. Lenstra boundedness is
  untouched.
- Say what Lean does not check.
- Do not claim "least", and do not claim the true `m_p` unless it was
  computed.
- Update `docs/OPEN.md`, invalidate cached descendants, and recompute
  descendants under the corrected `alpha_p` (degrees change if `m_p ≥ 2`).

Gate summary:

- Levels 0–2 support at most "candidate".
- Level 3 supports "the conjecture is false" (if Level 4 fails, it is
  "p or an ancestor").
- Levels 3, 4 and 5 together support "p is a counterexample".

---

## 8. Recommendations, in order

1. **Re-state every plan figure net of coverage** (tables 1.2–1.4), as
   expected count plus P conditional on the random model, with the Bayes
   discount alongside.
2. **Element-level cross-validation before counting v2 non-hits.** For
   about 30 rows per path (ratio and finite first), with `E ≤ 1e6`, compare
   v2 `--minpoly` (`mu` of `N_h(beta)`, with v2 extended to emit `N_h(y2)`)
   against the dual builder plus a flat norm. This is cheap. It turns v2's
   0.063 of ratio and finite mass from provisional coverage into real
   coverage.
3. **Fix the drivers.**
   - Classify the ancestor-rule checks as `ANCESTOR_RULE_FAILURE`.
   - Write hit records first.
   - Bound `search_ref`'s translate loop and check its return codes.
   - Block descendants on a `None` excess.
4. **Move planner facts into checks.** Make the engine (or the certificate
   checker) verify `h ∤ d(y2)` by an exact degree check, `E = R B`, and the
   translate encoding.
5. **Replay the 99 Peeters-only rows, and record Peeters' provenance.**
6. **Harvest the 555 cheap rows** (`E ≤ 1e5`, 0.0129). The running ref search
   covers the part with `E ≤ 6e4`.
7. **Build the certification kit now:** `mu` extraction, the witness, the PARI
   checker, and the dual-builder flat replay at 1e6–1e7. A hit should not be
   certified with improvised tools.
8. **Engineering priority by marginal mass** [checked]:
   - `B > 6e4` holds 0.086. The tensor model recovers about 0.021 of it.
   - `Rt > 4e6` holds 0.037. That cap is a cost choice; per the README, H
     needs no large irreducible.
   - Three-component Z rows hold 0.026, and inherited levels 0.011.
