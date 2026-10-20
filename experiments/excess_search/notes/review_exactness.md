# v2 exactness audit (adversarial, code-level)

Scope: `v2/v2engine.cpp`, `v2/plan.py`, `v2/driver.py`, `v2/validate_v2.py`,
`v2/census2.py`, `v2/search_v2.py`, the reference engine `ref/refengine.cpp` +
`ref/rowprog.py` (which `v2/refengine_copy.cpp` matches byte for byte), and the
design notes. No row computation was run. The only executions were planner calls
on 9 rows, to check the closure-degree identity in A1, and reads of the existing logs.

Tags: **[checked]** means I read it in the code or the logs, or ran the planner.
**[derived]** means I argued it mathematically here. **[estimate]** is a judgement.

## Verdict

I found **no path to a false counterexample or a false pass**, provided NTL
arithmetic is correct and the planner encodes the term algebra correctly
[derived]. Every mathematical step the engine relies on is either an exact
identity or an exact runtime check. That covers the Kummer/Capelli
irreducibility, the crossing, the multiplicity, the norm-first Euler test and the
cyclotomic split. The weaknesses are of three kinds:

1. Semantic facts held only by the planner, which the engine does not see. The
   only cross-check of them is common-mode.
2. One missing field certificate, the closure-degree identity. It is a
   theoretical gap that a single integer assertion closes.
3. Failures that are classified as engine errors when they are actually
   counterexample evidence.

There is also a coverage consequence the README does not draw. A row run that
passes all of v2's checks already certifies the rule translate at every
closure ancestor. So the dependency gating is unnecessary for soundness (§3).

## 1. Topic-by-topic audit

### 1.1 Phase pinning of shared ancestors — sound [checked + derived]
* `Closure.add` deduplicates by `q` (`plan.py:69-71`) and emits a
  downward-closed dependency order (`plan.py:72-82`). The engine builds every
  component once, in one model `K` (`v2engine.cpp:737-748`).
* The real criterion is that `T = F_2[x_q]/(relations)` is free of rank
  `prod ell_q`, because each relation is monic in its newest variable. Any
  assignment satisfying the relations is a ring map `T -> K`, and it is
  injective iff `T` is a field. Embeddings of a finite field differ by
  Frobenius, so p-th-power status is canonical [derived]. No per-root phase
  choice exists to get wrong.
* `k = F_{2^t}` and `F_{2^h}` are not monomial subfields. All k-data (`c`, the
  `f_j` and the translates) go through one `theta` and one map
  (`v2engine.cpp:844-903`), each verified by `Q(theta) = x` (`:901`). `F_{2^h}`
  enters only through a norm, and the Euler bit is Frobenius-invariant. So no
  mixed-embedding hazard exists in v2 [checked].
* Ratio path: `alpha_r1` and `alpha_r2` come from one `Closure`, so a shared
  `chi_3` is one element (`plan.py:150-151`) [checked].

### 1.2 Closure field certificate — GAP (theoretical) [derived]
`has_degree(y_q, d_q)` (`v2engine.cpp:747`) checks each root against the
planner's degree. Field-ness of `T` needs more: at each step
`lcm(L_prev, d_q) == ell_q * L_prev`, equivalently final
`lcm(d_q) == prod ell_q`. Per-component degrees do not imply this. If census
degrees were wrong in a consistent way, a relation could be reducible over the
field built so far while each `d_q` still matched. The census predicts the
identity holds. I checked `lcm == prod == B` for 743, 1031, 1433, 4507, 797,
16529, 56731, 163 and 1459 via the planner [checked]. The engine never asserts
it. Cost: integer arithmetic. → Assertion A1.

### 1.3 Cut rule, Sylow and valuation conditions — sound [checked + derived]
* The planner's `t0 = lcm(h/gcd(h,R), d(rule), f(l), l^{v_l(B)})`
  (`plan.py:178-187`) is only a proposal. The engine rechecks exactly:
  * `t | B`;
  * `R` odd, with its primes listed exactly;
  * `gcd(D,R) = 1`;
  * `l | 2^t-1`;
  * `v_l(2^t-1) = v_l(2^B-1)`, as exact big integers;
  * `h | Rt`;
  * `f(p) = h`.

  These are at `v2engine.cpp:704-725`. Given `l | 2^t-1`, the valuation
  equality is equivalent to `l ∤ D` (lifting the exponent), so the two
  conditions are consistent [derived].
* Crossing (`:769-790`). The valuation check makes `w = n^{-1} mod G` exist.
  `c = N(A)^w ∈ k` is checked. `A/c = A^{1-nw}` lies in the order-`N/G`
  subgroup, and `gcd(R, N/G) = 1`. `a = (A/c)^{R^{-1} mod N/G}` is checked by
  `a^R = A/c`. The edge cases `N/G = 1` and `D = 1` (where `c = A` and `a = 1`)
  are handled [checked].
* Kummer roots (`:328-386`). The radicand is checked to lie in
  `F_{2^{deg/ell}}` and `ord_{ell^v}(2)` is checked. The Sylow generator has
  exactly order `ell^v`. The `v_ell(2^el-1) = v` precondition holds because
  `ell^v | 2^el - 1 | 2^dg - 1` [derived]. Every dlog digit is found, and the
  final `y^ell = a` is checked. Exact.

### 1.4 Irreducibility of `V^R - c` and `X^R - A` — sound [checked + derived]
* The check `c^{(2^t-1)/l} ≠ 1` for each `l | R` (`:920`) runs in the k-model
  that `H` actually uses. `Nt/l` is exact because `l | 2^t-1` was checked first
  (`:719`).
* By Capelli, with `R` odd, `V^R - c` is irreducible over `k`.
* The valuation equality makes `c` a non-l-th power in `K`, hence `A = c a^R`
  is too, so `X^R - A` is irreducible over `K`.
* This certificate also makes the planner-only `E = R B` check
  (`plan.py:136,154,166`) redundant for exactness. With an inherited level or a
  reducible top, `c` would be an l-th power and the engine dies [derived].

### 1.5 Characteristic polynomial multiplicity — correct; correction branch never run [checked]
* The degree-finding loop (`:800-804`) is correct. It ends at `d = d0`, and
  exactness is checked.
* `P_a` is checked three ways: monic of degree `d`, coefficients in `k`, and
  `P_a(a) = 0` (`:818-826`). That suffices for the minimal polynomial without
  trusting `BuildFromRoots`.
* `F_a = P_a^{D/d}` (`:828-831`) matches `N_{L/H}(m + a v) = v^D F_a(m/v)`.
  Each `k`-conjugate appears `D/d` times under `Gal(L/H) ≅ Gal(K/k)`, since
  `Frob^{Rt}` restricted to `K` generates, given `gcd(R,D) = 1` [derived].
* **Untested:** README and logs say `d = D` in every row run. So the
  `power(f, D/d)` line has never executed. Singleton rows always have `d = D`,
  because `k(A) = K` and `A ∈ k(a)` [derived]. Ratio radicands can have
  `d < D` (Codex). → A6 adds an in-run identity check that catches a
  multiplicity error.

### 1.6 Norm-first Euler and the cyclotomic split — exactly equivalent [derived]
* `β^{(2^{RB}-1)/p} = N_{L/H}(β)^{(2^{Rt}-1)/p} = N_h^{(2^h-1)/p}`. These are
  exact integer factorizations of the exponent and need only `h | Rt`, which is
  checked.
* The test "`x` is a p-th power iff `x^{n/p} = 1`" holds in any cyclic group of
  order `n` with `p | n`, whatever `v_p(n)` is. **Wieferich rows are not special.**
  1093 (`v_1093(2^364-1) = 2`) is in the final validation as a ratio row: it was
  direct-checked and agrees with ref and Peeters [checked]. 3511 is not in the
  validation; it has three components and is refused.
* Split: `P1 = Φ`-product over `d | h/q1`, and `P2 = Φ`-product over
  `d | h/q2` with `d ∤ h/(q1q2)`. These are disjoint sets of `d`, so
  `P1·P2 | 2^h-1` always, and the check at `:990` cannot fail. `p | Φ_h(2) | Rest`,
  and `p ∤ P1 P2` because `ord_p 2 = h`.
* `Y^{P1} = 1 ⇔ Y^{2^{h/q1}} = Y` for `Y ≠ 0`. For `h` prime, `P1 = P2 = 1` and
  the test becomes `Y^2 = Y ⇔ Y = 1`. Both cases are exact.
* **`p | E` edge case.** The status is invariant from `F_2(β)` to `L` iff
  `p ∤ [L : F_2(β)]`. That holds because every prime of `R` and `B` is below
  `p` (closure primes, since `f(r) < r`). It is structural and never asserted.
  → A2.
* The "phase sanity" check `(Y^p)^{2^{h/q1}} = Y^p` (`:1013-1015`) is a
  Fermat-type self-test of the exponentiation code (`Nh^{2^h-1} = 1`). It does
  catch wrong-exponent or wrong-product bugs. It is vacuous only when `Nh = 1`.

### 1.7 Translates and `d(m) | t` — sound [checked]
* Nimber encoding: `2^i = prod_{j ∈ bits(i)} chi_{2^{j+1}}` (`plan.py:26-40`).
  The AS relations (`plan.py:73-76`) match `chi_{2^k}^2 + chi_{2^k} = prod_{j<k} chi_{2^j}`.
* The engine checks that each translate lies in `k` (`:764`). This is what the
  `W = Σ f_j m^j V^{D-j}` formula (`:931-943`) needs. `m = 0` gives `f_0 V^D`
  correctly.
* Ratio and finite rows test the label-0 element `1`, i.e. `1 + z`
  (`plan.py:173`). `driver.verdict` maps label 0 to rule 0 (`driver.py:113-124`).

### 1.8 H arithmetic — sound [checked]
* `H_mul` does a single wrap reduction, which is enough since `deg < 2R`.
* `H_sqr` is a bijection `i -> 2i mod R` because `R` is odd.
* Frobenius: `V^{2^e} = C V^j` with `j = 2^e mod R` and `C = c^{(2^e-j)/R}`
  reduced mod `2^t-1`. The basis multipliers are `M[i] = C^i c^{⌊ij/R⌋}`, and
  the coefficients get `e mod t` squarings or `CompMod` (`:491-536`).
* `H_norm` doubling is correct, with count checked (`:595-616`). The sliding
  window with pending squarings is correct (`:556-592`).
* No integer overflow: `i*j < R^2 ≤ 1.6e13`.

### 1.9 Models and caching — sound [checked]
* `sparse_irred` reads `cache/` then `../ref/` (`:186-212`). Every load is then
  re-certified by deterministic Rabin (`:733-734`). The k-modulus is
  Rabin-checked with `g(θ) = 0` and `deg g = t` (`:859-863`).
* The only engine cache is `FrobCache`, keyed by length within one `H` per
  translate and per `p` (`:997`). It is safe.
* `results_v2.jsonl` is keyed by `p` only. It records no ancestor-excess vector
  and no binary hash, yet `load_sources` feeds it back as `known`
  (`driver.py:42-48`) (minor; see B9).
* **Oracle gap:** the reference engine does not Rabin-check its cached modulus
  (`ref/refengine.cpp:206-217`).

### 1.10 Fallback and refusal — not silent, but sometimes misrouted [checked]
* A `Refuse` falls back to the reference engine only when `E ≤ 60000`;
  otherwise the record is `path=None, refused` (`driver.py:151-166`).
* If the refusal came from the closure (excess unknown, or excess ≠ rule;
  `plan.py:57-62`), `ref_program` re-raises `Refuse` inside the `except` block
  (`plan.py:209-211`). The exception then escapes. In `search_v2.py:75-79` it
  is caught as `EXC`, and **no jsonl record is written** (log line only). It is
  reachable only after an ancestor already violated the rule.
* A FATAL marks the whole batch as `error` and discards partial `p=` lines
  (`driver.py:142-146`). Nothing is silently passed.

### 1.11 Checks held only by the planner, trusted by the engine [checked]
The engine never sees:
* `Q(h)`, the arm and the rule (`census2.py:100-126`);
* the semantics of the relation expressions;
* which factor is `y2`;
* the radicand exponents `(R2, -R1)` / `(1, -R1)` (`plan.py:156,168`);
* that `R` is the full prime-power component;
* that the `M` labels are `0..rule`;
* that `p` is prime;
* that rhs indices refer to earlier components. `eval` silently uses a zero
  `val` for a later index (`v2engine.cpp:247-256`).

Most important: **"`y2` is a p-th power"** (`h ∤ d(y2)`, `plan.py:143-146`) is
planner-only. `y2` is never built, so its degree is never certified. The finite
path's `y2 = chi_{2^k}` is built and degree-checked, but its p-th-power status
(`h ∤ 2^k`) is still not asserted.

**Validation is common-mode for the encoding.** The per-translate reference
comparison runs `plan.ref_program`, the same `Closure` and the same `census2`
(`validate_v2.py:58-63`, `driver.py:99-100`). It does not use the original
`ref/rowprog.py` and `census.py`. Only OEIS, the certificates and Peeters are
independent of the encoding, and they stop at 12281.

## 2. Findings by severity

There are no fatal findings.

**Major**
* **M1. Ancestor failures are reported as engine errors.** When the rule fails
  at a closure prime, the term algebra built from rule values is not a field.
  v2 then dies with one of:
  * `component exact degree` (`:747`), because every root lies in `F_{2^{b_r}}`;
  * `c not an ell-th power in k` (`:920`), when the failure is at the top prime.

  The driver records these as `error`. Nothing marks them as counterexample
  evidence [derived]. In assumed-ancestor mode this is exactly the hit the
  orchestrator cares about.
* **M2. No in-engine closure field certificate** (§1.2). → A1.
* **M3. The `y2` p-th-power claim and the radicand assembly are planner-only**
  (§1.11). A planner bug there yields a wrong but internally consistent element,
  which none of the engine's checks would detect. → A4, A5.
* **M4. The multiplicity branch `d < D` was never executed**, nor was
  `t_mult > 1` (`plan.py:185`; no caller passes it) [checked]. → A6, A10.

**Minor**
* **m1.** No assertion of `p` prime, `p ∤ R·B`, or closure primes `< p` (§1.6).
* **m2.** Agreement with sources on the rule translate is weak evidence. Garbage
  arithmetic says "not a p-th power" with probability `1 − 1/p`.
  * The strong validations are the direct check (364 rows, `Rt ≤ 29,820`) and
    the forced translates. 151 validated rows have `Rt > 30000` with no direct
    check [checked].
  * The README records `N_h(m=0) = 1` exactly for 359 and 1433. If that is
    structural, the `m = 0` forced translate exercises no exponentiation
    [estimate; generality unverified].
* **m3.** The driver does not verify the engine binary (`v2engine.prelim`, which
  lacks checks, sits beside it) or the expected set and counts of `CHECK` lines
  (`driver.py:62-79`).
* **m4.** `search_v2` drops `EXC` rows without a record (§1.10).
* **m5.** The reference oracle does not Rabin-check its cached modulus (§1.9).

## 3. Coverage consequence: ancestor gating is unnecessary [derived]

Every odd closure prime of a v2 row gets an exact irreducibility certificate,
in one of two ways:

* **Closure components.** For each `chi_r'`, `kummer_root` checks that the
  radicand lies in `F_{2^{dg/ell}}` (`:331`), and `has_degree(y, ell·dg/ell)`
  (`:747`) checks the root. A root of exact degree `ell·b` over `F_{2^b}` forces
  `X^ell − a` to be irreducible over `F_{2^b}`, so `alpha_{r'}` is not an
  `r'`-th power. This holds whatever the census says.
* **Top primes.** The `c` non-residue check certifies `alpha_r`, `alpha_r1` and
  `alpha_r2` as non-powers in `K ⊇ F_2(alpha)`.

Together with A1 (or the census degree consistency) and the paper's
forced-translate theorem for O/C/D, a passing v2 run on `p` proves
`m_{r'} = rule(r')` for every `r' ∈ closure_primes(p)`. So the gating in
`search_v2.py:65` and `driver.py:205` is not needed for soundness. A run
with assumed ancestors either:

* passes, which certifies the ancestors (no conditional state); or
* fails at one of the M1 checks, which is a counterexample candidate at a named
  ancestor.

The planner must exclude inherited levels first, and A1 separates census errors
from genuine failures. Ancestors that v2 refuses itself (≥3 components) are
certified as a side effect whenever they appear inside a descendant's `K` with
`B ≤ cap`.

## 4. Minimal runtime assertions v3 must add

* **A1. Closure field certificate.**
  * For each component in order, assert every rhs index is `< i`.
  * Keep `L = lcm` of the checked degrees and assert
    `lcm(L, d_q) == ell_q · L` at each step.
  * Assert `B % L == 0`, and `L == B` for the current paths.
* **A2.** Assert `p` prime (deterministic for `p < 2^64`), `p ∤ R`, `p ∤ B`,
  and every `l | R` and every component prime `< p`.
* **A3.** Keep the per-`l` non-residue checks. Assert `Nh ≠ 0` explicitly.
* **A4. `y2` certificate in-engine.**
  * The planner tags which radicand factor is `y2` and passes `R2`.
  * Ratio path: assert `(R2·B) % h != 0`. This suffices because
    `y2 ∈ F_{2^{R2 B}}`. Otherwise refuse, or certify `d(y2)` explicitly.
  * Finite path: assert `h ∤ 2^k`, using the built component's checked degree.
* **A5. Semantic header.** The planner states `(arm, Q, rule, R_i, exponents)`.
  The engine then asserts:
  * `R = Π R_i`, the `R_i` pairwise coprime, and the exponents equal
    `(R/R_1, −R/R_2)` or `(1, −R_1)`;
  * the translate labels are exactly `0..rule`;
  * `E = R·B` is recomputed from the checked top degrees.
* **A6. Multiplicity identities.** Assert `fa[0] == N_{K/k}(a)` (one `relnorm`)
  and `fa[D−1] == Tr_{K/k}(a)` (one `reltrace`). Together they catch a wrong
  `D/d` power or a wrong conjugate set.
* **A7. H self-tests at full size.** Once per `H`:
  * check `frob_apply` against repeated `H_sqr` on a random element, at one
    squaring-path length and one `CompMod`-path length;
  * run one positive control: the Euler phase of `u^p` for a random `u ∈ H`
    must be exactly 1.
* **A8. On a hit.** Replay with a second admissible `t` (`t_mult`), a different
  seed and modulus, and the `--direct` route when `Rt` allows. Require agreement
  and emit the certificate (moduli, roots, `c`, `a`, `F_a`, `W`, `N_h`, the
  exponent).
* **A9. Driver.**
  * Verify the engine hash.
  * Require every expected `CHECK` name with its expected count, for example
    the non-residue check `= |Rprimes|`.
  * Map FATALs at `component exact degree` (after A1 passes) and `c not an
    ell-th power` to `ANCESTOR_FAILURE_CANDIDATE` with the named prime. Do not
    record them as `error`.
  * Record the ancestor-excess vector and the binary version per result.
  * Never drop a row without a record.
* **A10. Validation.**
  * Exercise `d < D`, `t_mult > 1`, both Frobenius paths, and Wieferich rows.
  * Use an encoding-independent oracle: `ref/rowprog.py` and `census.py`, or
    the Rust `Ordinal` type / `TermAlgebra`, not `plan.ref_program`.
