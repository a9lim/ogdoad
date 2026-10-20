# v3 performance architecture: what to integrate, in what order

Role: performance architect. Inputs: SPEC, Codex's design, the five design
docs, v2 (README, engine, planner, driver, validator, timings) and the
reference engine. No row computation, sweep or benchmark was run. Everything
below comes from reading the docs and from small scripts over the census and
coverage files, each under 2 s.

Tags:
* **[checked]**: a census or structural computation done here, or a number
  copied from a measured log.
* **[derived]**: follows by stated reasoning.
* **[estimate]**: a cost-model number.

Scripts and data are in `review/perf/`:

| script | what it does |
| --- | --- |
| `fit.py` | fits a cost model to v2's measured timings |
| `cost.py` | per-row cost models |
| `rowstruct.py` | fast replica of `plan.py`, run on (1e5, 1e6] |
| `sz.py`, `szhi.py` | the new single-big-component path |
| `split.py` | coprime tensor splits |
| `final.py`, `sens.py`, `ewod.py` | milestone curves and sensitivity checks |

## 0. Verdict

1. **v2's shape refusals are mostly a planner limitation, not a missing
   algorithm.** [checked]
   * 972 of the 1,638 refused rows ≤ 1e5 (3+ components or inherited levels)
     carry mass 0.0254 of the 0.0408. They have exactly one "big" component,
     an odd prime power with a = 1.
   * For every one of the 972, all the components other than chi_R lie in
     a field F_A with `E = R·lcm(b_r, A)`, and the cut `t = lcm(t0, A)` is
     admissible.
   * So `kappa = chi_R + z` with `z ∈ k`, which is exactly v2's singleton
     machinery with the translate `m` replaced by the k-element `z`. The
     engine already accepts a general translate expression and checks that
     it lies in k.
   * In (1e5, 1e6] another 9,511 rows (mass 0.0246) qualify.
   * Engineering cost: a planner change plus validation.
2. **The coverage wall is the parent degree B, not the row shape.**
   * Uncovered v2-path rows with B > 6e4 carry 0.0856 mass ≤ 1e5. [checked]
   * A two-factor coprime tensor model `K = F_{2^B1} ⊗ F_{2^B2}`, with
     `t | B1` and both factors ≤ 6e4 (sparse moduli already cached or cheap),
     exists for rows carrying 0.0766 of that mass. [checked]
   * Hilbert-90 roots (crossing.md Thm B) and power-projection characteristic
     polynomials replace v2's B-bit exponent and its `BuildFromRoots`.
     This is the largest single gain. [estimate]
3. **Compute is dominated by the Euler step in H, and v2 does it in the wrong
   ring.**
   * Among the rows a v3 engine can do in ≤ 1 core-h, the Euler stage is
     346 core-h and the K side 52 core-h. [estimate]
   * v2 runs the h-bit exponent with Rt-bit H-multiplications on a conda gf2x
     that has no PMULL.
   * The fix: rebuild against PMULL / PCLMUL+bitpolymul, add a direct
     Kronecker H kernel over a sparse k modulus, and finish in a compact
     model of F_{2^h} by the minimal polynomial of N_h. Together that is about
     15–20x at Rt ≥ 5e5. [estimate, calibrated to v2's measured runs]
4. **Do not stop at 1e5.** The cheap rows in (1e5, 1e6] have better mass per
   core-hour than the tail below 1e5. Schedule both pools together, greedily
   by mass/cost (order-free search). [estimate]
5. **Low value per hour:**
   * (Q, m) grouping beyond grouping by h: saves about 15% of the K side,
     which is a minor share of cost.
   * The full Φ_h cyclotomic split: subsumed by the compact final stage.
   * Theorem-C recursion for B > 1e9: 0.006 mass ≤ 1e5, partly out of reach.
   * R5/R6 descent.
   * The flat dual builder as a coverage engine. Keep it as the certificate
     and replay engine for hits with E ≤ ~5e7.

## 1. The target, re-cut by what limits each row [checked]

Uncovered mass ≤ 1e5 is 0.2786: 0.0780 from the missing list below 12289 and
0.2006 from 12289..1e5. Split by what stops v2:

| class (≤ 1e5 uncovered) | rows | mass |
| --- | ---: | ---: |
| v2 path, B ≤ 6e4, Rt ≤ 4e6 (README's 0.1155) | 2,684 | 0.1155 |
| v2 path, B ≤ 6e4, Rt > 4e6 | 1,522 | 0.0367 |
| v2 path, 6e4 < B ≤ 1e6 | 1,310 | 0.0464 |
| v2 path, 1e6 < B ≤ 1e9 | 1,173 | 0.0331 |
| v2 path, B > 1e9 | 240 | 0.0061 |
| refused, single big prime component ("sz" path below) | 972 | 0.0254 |
| refused, all components small (E = e0; ref fallback at E ≤ 6e4: 0.0043) | 226 | 0.0058 |
| refused, two or three big components (R3 territory) | 420 | 0.0092 |
| refused, big prime-power component (a ≥ 2) | 19 | 0.0004 |

Notes:
* v2's `R t ≤ 4e6` cap is policy. The H side needs no large irreducible.
  The cost model says Rt up to ~1e8 is affordable when h is moderate.
* (1e5, 1e6] holds 68,906 rows, mass 0.1821:
  * singleton 0.0548, ratio 0.0757, finite 0.0057;
  * 3+ components 0.0374, inherited 0.0085.
  * v2-path rows with B ≤ 6e4 and Rt ≤ 4e6: only 0.0170.

## 2. Cost model (calibrated to v2) [estimate; the fit is checked]

**v2 as measured** (12 timed rows, loaded M5, conda NTL, CPU seconds):

* Euler ≈ 6.0e-10 · h_eff · Rt^1.227, with
  `h_eff = h (1-1/q1)(1-1/q2)` (v2's two-prime cyclotomic split).
  * 10 of the 12 rows fall within 0.8–1.3x.
  * 359 is 2x under the fit, and 56731 (h with five prime factors) is
    2.4x over it.
  * The fit is extrapolated beyond the measured Rt ≤ 1.07e6.
* K side ≈ 4.3e-9 · B² (four rows with B ≥ 2e4, fit within ±20%).

**v3 units:** jobe per core, NTL on PCLMUL gf2x plus bitpolymul (arithmetic.md
§2.1). The loaded M5 with the PMULL port is about equal per core up to 4e6
bits and 4–6x slower above that.

* `H_mul = 1.2·M(2Rt) + 2R·M(t)`. This is a Kronecker product plus folds,
  with a sparse k modulus and monomial c.
* Per 6-bit window, add one H Frobenius map: `R(6S(t) + 2M(t))`.
* Norm: `2 log2(t/s+1)` products.
* Compact final:

  ```text
  Norm + 2·sqrt(2h)·H_mul + (h_eff/6)·1.5·M(h)
  ```

  This is BSGS power projection for the minimal polynomial g of N_h, then the
  exponent in F_2[x]/g.
* K side: Hilbert-90 roots for the crossing and for each closure component,
  `(f/7 + 4 log D + 12)·M_K + f·S_K + 2 log D` ψ-powers. For B > 6e4,
  `M_K = 4·M(B)` (tensor) and a ψ-power uses the partial-Frobenius cost.
  Charpoly is `(4 sqrt(2D) + D/8)·M_K + 2D²·m_k(t) + BM`.

**Sanity check against v2's measured rows:**

* The v3 model predicts 3x faster on K-side-heavy rows (839, 1307, 1487).
* It predicts 15–20x faster on Euler-heavy rows (4507, 2819, 16529):
  0.5–1.5 s against 10–75 s.
* That is consistent with the measured kernel ratios: PMULL 7–10x,
  bitpolymul 1.5–2.5x, and compact-h 2–5x at large h.

**Sensitivity [estimate].** Multiply the B > 6e4 K side by 30 and the Euler
stage by 5. Level E of §3 still reaches 0.251 at 300 core-h (both pools),
against 0.290 nominal and 0.154 for v2 today. The ranking does not change.

**Corrections to inputs:**
* multicomponent.md's tensor-regime `eulerT` and crossing.md's `final` term
  both omit the h-bit exponent. Their large-h costs are optimistic by 10–50x.
  I used only the polynomial-regime multicomponent costs, divided by 5 for
  PMULL/bpm units.
* v2's README coverage table ignores the reference-engine fallback for
  E ≤ 6e4 (0.008 extra mass ≤ 1e5: level-A ceiling 0.1601 against 0.1522 for
  the v2 paths alone).

## 3. Milestones: reachable uncovered mass against compute

Levels are cumulative. The mass is greedy by mass/cost, with rows grouped by
(h, Q), so rows sharing h share one run.

Compute is in jobe-core-hours (ch). Level A is in loaded-M5 CPU hours,
because that is what v2 runs on today.

The pools are uncovered rows ≤ 1e5 (0.2786) plus (1e5, 1e6] (0.1821), total
0.4607. [estimate]

| level | adds | eng-h [estimate] | 10 ch | 100 ch | 300 ch | 1000 ch | 3000 ch | ceiling |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| A | v2 today (+ ref fallback E ≤ 6e4) | 0 | 0.108 | 0.141 | 0.154 | 0.166 | 0.176 | 0.213 |
| B | PMULL (M5) / PCLMUL+bitpolymul (jobe) rebuild | 3–4 | 0.139 | 0.164 | 0.174 | 0.184 | 0.192 | 0.213 |
| C | single-big-component ("sz") planner path | 4–6 | 0.152 | 0.181 | 0.194 | 0.205 | 0.213 | 0.236 |
| D | Euler stage: H kernel (sparse k, monomial c, direct Kronecker), compact F_{2^h} final with minpoly | 12–16 | 0.179 | 0.208 | 0.218 | 0.227 | 0.232 | 0.236 |
| E | K scale-up: coprime tensor K, Hilbert-90 roots, power-projection charpoly, k inside factor 1 | 25–35 | 0.216 | 0.268 | 0.290 | 0.313 | 0.333 | 0.407 |
| F | R3 double crossing (2–3 big components), flat dual-builder path for small-E multi rows | 20–30 | 0.224 | 0.278 | 0.302 | 0.326 | 0.346 | 0.421 |

The ≤ 1e5 pool alone, at 100 / 1000 ch:

| level | 100 ch | 1000 ch | ceiling |
| --- | ---: | ---: | ---: |
| A | 0.132 | 0.150 | 0.160 |
| B | 0.149 | 0.159 | 0.160 |
| C | 0.163 | 0.174 | 0.175 |
| D | 0.175 | 0.175 | 0.175 |
| E | 0.236 | 0.256 | 0.262 |
| F | 0.246 | 0.266 | 0.273 |

The 1e5–1e6 pool is where the extra core-hours go after level D: at level E it
takes 0.045 at 100 ch and 0.069 at 1000 ch.

**Mass per engineering hour** (both pools at 300 ch) [estimate]:

| level | gain | per eng-hour |
| --- | --- | --- |
| B | +0.021 | ≈ 0.006/h |
| C | +0.019 | ≈ 0.004/h |
| D | +0.025 | ≈ 0.0018/h |
| E | +0.072 | ≈ 0.0024/h |
| F | +0.012 | ≈ 0.0005/h |

* Doing E before D gives +0.054 for E and then +0.043 for D. The totals are
  the same.
* D goes first anyway: it is smaller and lower-risk, it keeps v2's structure,
  it cuts the cost of every row 4–20x immediately, and its field and kernel
  layer is reused by E.

**Wall clock [estimate].**
* jobe at nice 19 gives about 12–16 effective cores, roughly 300–380 ch/day.
* The M5 under the other sessions' load gives about 3–4 effective cores
  (≈ 80 ch/day), and only for products ≤ 4e6 bits.
* So 300 ch is about one day of both machines, and 1000 ch about three days.

**Random-model context (speculation; shortcuts.md audit):**
* expected failures = mass reached;
* 0.29 → P(≥1 hit) ≈ 25% under independence;
* discount by P(random model | data), roughly 0.26–0.8.

## 4. Item-by-item decisions

| item | decision | why |
| --- | --- | --- |
| PMULL gf2x port (`design/arith/b-pmull`) | **Integrate first (B).** | Kernel 9–17x [checked]; the NTL level about 7–10x [estimate]. Zero algorithm risk; rerun `validate_v2.py` on both builds. |
| bitpolymul2 FFT | **Integrate with B** (`bpm_wrap.c` behind `gf2x_mul`) on jobe and the M5. | H products are 2Rt ≈ 1e6–1e8 bits, where it gains 1.4–2.4x at the NTL level [checked]. Add a truncated (non-power-of-two) FFT later only if profiles show padding waste. |
| sparse squaring kernel (`sqrk.h`) | **In D/E field layer, low priority.** | 2.5–3x on squarings [checked], but squarings are not the bottleneck in H (t ≤ a few thousand bits). They matter for the K side only for B ≤ 6e4 ψ-powers outside the tensor model. |
| monomial-c normalization | **In D.** | 1–2 h. Turns the wrap fold of every H product and squaring into a shift. Worth 10–30% of an H product [estimate]. Exact: it is a change of variable V → gV with g ∈ k, as an explicit factor. |
| Itoh–Tsujii in the tower | **Already in v2** (`H_norm` doubling). | Extend the same doubling to K-side norms only through the Hilbert-90 root (E). Skip the full Φ_h split: with the compact final stage the exponent runs in an h-bit field and costs milliseconds. |
| splitting K into coprime factors | **Core of E.** | Two factors ≤ 6e4 cover 0.0766/0.0856 of the large-B mass ≤ 1e5 [checked]. Three factors or a custom sparse-irreducible search pick up the remaining 0.009. B > 1e9 is left out. |
| dual-sequence flat builder + certificates | **Not a coverage engine.** | Its floor is E·S(E) for the Euler step. Build it (F) for two jobs: the replay/certificate route for any hit with E ≤ ~5e7 (no Rabin needed, models.md §3), and the 0.0015 mass of all-small multi rows with E in (6e4, 1e6]. |
| multicomponent R1–R6 | **R2-with-translate = level C** (cheap, 0.025 + 0.025 mass). **R3 = level F.** **R4** only as an independent replay route for a hit. **Skip R5/R6** (tensor K covers the same rows more simply). | Each case trades mass gained against engineering cost. |
| recursive crossing (Theorem C) for deep chains | **Defer.** | B > 1e9: 0.006 mass ≤ 1e5. Rows such as 2879 are out of reach (K ≈ 113 GB per element). |
| grouping by (Q, m) | **Group by h (exists); cache K-side objects only opportunistically.** | 6,689 rows → 4,226 elements, but sharing saves only 15% of K-side cost, and the K side is ~13% of the ≤ 1 ch/row workload [estimate]. |
| M5 / jobe split | **jobe:** all rows with 2Rt > 8e6 bits and the bulk queue (nice 19, ≤ 3 GB/job, never beside a foreign GPU job). **M5:** rows with 2Rt ≤ 4e6, K-side-heavy rows with B ≥ 1e7 (128 GB), the regression suites, and the mandatory replay of every hit on the other multiplier. | On the M5 the PMULL build matches jobe per core up to 4e6 bits; above that the loaded M5 is 4–6x slower [checked kernels]. Replaying on the other architecture uses a different multiplier: PMULL gf2x vs PCLMUL gf2x vs bitpolymul. |

## 5. Concrete v3 milestone list

* **v3.0 (B, 3–4 eng-h).**
  * Rebuild `v2engine` against the M5 PMULL gf2x and the jobe tuned
    gf2x+bpm. jobe's `/tmp/excess-bench` and `/tmp/xb` builds may vanish;
    reinstall them under a persistent scratch prefix.
  * Gate: `validate_v2.py` agreement with OEIS, ref, Peeters and the
    certificate rows on both machines.
  * Start the cost-greedy queue across both pools, conditional on closure
    rows (order-free; ref fallback for E ≤ 6e4).
  * Target: 0.164 at 100 ch.
* **v3.1 (C, 4–6 eng-h).**
  * Planner path `sz`: Z rows with one big odd-prime component get radicand
    alpha_r, translate z = Σ (small components), parent `B' = lcm(b_r, A)`,
    `t = lcm(t0, A)`.
  * The engine test is the existing `W_z = V^D F_a(z/V)`.
  * Gate: 105 Peeters rows have this shape and are refused today (33 with
    E ≤ 2e4 for a per-translate reference comparison); add the multi rows
    ≤ 727 from OEIS.
  * Target: 0.194 at 300 ch.
* **v3.2 (D, 12–16 eng-h).**
  * Own H ring:
    * sparse k modulus (root of the dense trace-model g in F_2[y]/P_t, or k
      taken as a factor);
    * monomial c;
    * Kronecker H products straight into `gf2x_mul`;
    * Frobenius by sparse squarings / CompMod.
  * Compact final stage:
    * minimal polynomial g_h of N_h by BSGS power projection (transposed
      products via a trace functional);
    * exact checks: Rabin on g_h, g_h(N_h) = 0 by Paterson–Stockmeyer, and
      the degree;
    * then the Euler test in F_2[x]/g_h.
  * Side benefit: g_h is canonical, so replays and hits compare an h-bit
    polynomial exactly. Bonus: v2's `--minpoly` already matched the 359
    certificate this way.
  * Gate: the v2 validation set plus `--direct` cross-checks.
  * Target: 0.218 at 300 ch, with the B ≤ 6e4 ceiling (0.236) reached at
    ~3000 ch.
* **v3.3 (E, 25–35 eng-h).**
  * A field interface (`mul`, `sqr`, `frob(m)`, `inv`, subfield embed) with a
    flat sparse backend and a two-factor coprime tensor backend (partial
    Frobenius).
  * Port the component roots and the crossing root to Hilbert-90 (crossing.md
    Thm B, already checked to b = 19580).
  * Charpoly by power projection + half-gcd BM over k, with `deg = D` and
    `f(a) = 0` checks.
  * Gate: rerun 1487, 1307, 839 and 359+1433 in the tensor backend, with
    element equality against v2's flat model and minpoly(T_h) equality.
  * Target: 0.29 at 300 ch, 0.31 at 1000 ch, 0.33 at 3000 ch.
* **v3.4 (F, 20–30 eng-h).**
  * R3 double crossing (resultant of two crossed charpolys over F_ex; needs a
    GF2EX half-gcd resultant, which NTL lacks) and the dual-builder flat path.
  * Gate: multicomponent.md's V1 rows (617, 2003, 1303, 9199, 27281).
  * Target: about +0.012.
* **Deferred:** Theorem-C deep recursion, R5/R6, a truncated additive FFT,
  VPCLMULQDQ kernels.

**Every hit:**
* replay on the other machine with a different t;
* compare g_h;
* use a second route (R4 free factor, or path A vs path B);
* use the dual-builder flat replay when E ≤ 5e7;
* then certify the ancestors so the least counterexample can be named.

## 6. Risks to these numbers

* Every core-hour figure is a model. The v2 fit is extrapolated in Rt beyond
  1.07e6. The v3 K side for B > 6e4 is unmeasured, though the sensitivity
  check in §2 brackets it.
* Engineering hours are guesses for Claude sessions including validation.
* The structural claims are exact census facts: §1, the sz applicability
  (972/972 ≤ 1e5 and 9,511 in (1e5, 1e6]), and the tensor-split coverage.
  But the planner replica re-implements `plan.py`'s rules. It reproduced
  v2's coverage file on 12289..1e5 with 0 mismatches.
* The (1e5, 1e6] multi-row costs beyond the sz path come from a 250-row
  sample of the multicomponent model and are used only in level F.
