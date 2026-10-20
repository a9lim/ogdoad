# Shortcuts and heuristic audit for the 0/1/4 counterexample search

Designer angle: mathematical shortcuts plus an adversarial audit of the random model.
Every claim carries a tag: **[checked]** means a computation in this session confirmed it,
**[derived]** means a short proof is given here, **[guessed]** means a heuristic or a prior.
Scripts and data are in `design/shortcuts/`, a subdirectory so they do not collide with other
designers' files. The scripts run in micromamba env `excess` with PARI/cypari2 and NTL.

## 0. Verdict

* There is no "magic small field". For every arm, the row test needs at least the information
  in the parent field `K = F_2(alpha_r)` (degree `b = E(r)`), together with a test field of degree at least
  `R * lcm(f(r) r^{v_r(b)}, s)`. **Crossed descent** reaches both bounds; it generalizes the 719
  certificate and covers arm O, arm Z, and multi-component Z. When `b >> f(r)` it collapses
  `E = R b` to `max(b, R t)`, a gain of 10x to 1000x on deep chain rows. Examples:
  `p=1433`: 3.5e6 -> (19580, 31862); `p=839`: 1.6e7 -> (37620, 175142).
* Four other exact shortcuts:
  * **Norm-first Euler** (Itoh-Tsujii): E squarings plus O(log E + h/w) multiplications,
    instead of about E/w multiplications.
  * **One element per (Q, m)**: batch every row prime of that element.
  * **Arm Z(2) = arm O type**: `chi_p(kappa) = chi_p(1+w)` with `w^{q1 q2}` in the previous level.
  * **Order-free conditional search**: a hit found while assuming the rule for ancestors already
    disproves the conjecture.
* Audit. The random model holds up. I found no structural mechanism that lowers the failure
  probability at row characters.
  * The only structure that moves probabilities is (i) subfield and generator effects in tiny
    fields and (ii) a torus-inversion mechanism. The torus mechanism *forces* p-th powers, so it
    can only *create* failures, and it provably and observably misses the selected elements.
  * The known data are unremarkable once tiny fields are modelled correctly. The expected number
    of failures among the 128 known rows is 1.01, not 1.65. P(0 failures) = 0.36, not 0.17.
  * Free (non-row, non-forced) characters of selected arm-Z elements are random:
    3879 non-row trials on 215 elements, z between -0.6 and -1.4, the same on non-selected translates.
    These counts are PARTIAL (section 3.3).
* Is the search well-motivated? Yes, as a long shot with a guaranteed byproduct.
  * Under the random model, P(a counterexample in (727, 1e4]) = 28% and in (727, 1e5] = 42.5%.
    The cheap mass that crossed descent reaches is about 0.30 (26%) below 1e4.
  * The data give at most a factor of about 2.8 in favour of a hidden theorem.
    With an even prior the realistic yield is about 10-15% **[guessed]**.
  * The byproduct is a large extension of A380496 beyond 709 that other engines can validate
    against. This session already verified 346 new rows with p > 727 (section 7).

## 1. Exact shortcuts

### 1.1 Norm-first Euler (Itoh-Tsujii) [standard; checked]

For `h = f(p) | D | E`: `x^((2^E-1)/p) = N_{E/D}(x)^((2^D-1)/p)`.

Compute `N_{E/h}(x) = x^{(2^E-1)/(2^h-1)}` with the chain `y_{2k} = y_k^{2^{kh}} y_k`,
`y_{k+1} = y_k^{2^h} x`. This costs about E squarings and 2 log2(E/h) multiplications. The
remaining exponent `(2^h-1)/p` costs h squarings and about h/5 multiplications.

* Checked with NTL on an irreducible sparse modulus, `E=20000`, `p=101`: the result equals plain
  `PowerMod`. Norm-first took 0.14 s (19900 squarings, 9 multiplications); `PowerMod` took 1.84 s.
  Source: `ntl/normfirst.cpp`.
* At `E=1e6`: 999,900 squarings plus 17 multiplications. That is 345 s on a machine at load
  average about 200, or about 41 s idle by the SPEC bench. Plain `PowerMod` needs about 1.7e5
  dense multiplications, roughly 6000 s idle.
* So the Euler step itself is never the bottleneck. Model building (component embedding) is.

### 1.2 One element per (Q, m); order-free search [derived]

The tested element depends only on `(Q(f(p)), m)`: `kappa_Q + m`.

* Below 1e4 there are 1100 rows but only 761 elements. Below 1e6 there are 78,369 rows and
  48,498 elements.
* All primes `p` with `Q(f(p)) = Q` and the same arm are rows of that one element. Arm O: every
  prime `p != r` of `L_{r,a}`. Arm Z: the primes of `Pi_h` for all `h` with `Q(h) = Q`.
* One norm computation per element serves all of them. Compute norms to `D0 = lcm(h_i)` and then
  down to each `h_i`. This also reaches rows far beyond any census bound (large prime factors),
  although their mass is negligible.
* **Order freedom.** Suppose row p fails in a model that *assumes* `m_r = rule(r)` for every
  ancestor r. Then either some ancestor violates the rule or p does. Either way the conjecture is
  false.
  * So SPEC requirement 4 (process strictly in increasing p) is needed only to *name* the least
    counterexample after a hit, not to find one.
  * Rows may be scheduled by cost. Ancestors are automatically cheaper:
    `E(r) = b_r | d(chi_q)/q`, so `E(r) <= E(p)/q`.

### 1.3 Arm Z with two components is an arm-O-type "1 + radical" test [derived; checked]

Let `Q = {q1 < q2}`. Lenstra's construction gives `q1 ∤ d(chi_{q2})`, because `q1` was added
precisely when it does not divide `d(kappa_g)`. It also gives `q2 ∤ d(chi_{q1})`, because
`b_{r1}` has only primes below `r1 < r2`. Hence `h` divides neither `d_i`, the p-character is
trivial on both `F_2(chi_i)`, and

  `chi_p(chi1 + chi2) = chi_p(1 + w)`, with `w = chi1/chi2` and `w^{q1 q2} = alpha1^{q2} / alpha2^{q1}`.

So `F_E = K'(w)` is a Kummer extension of degree `q1 q2` over `K' = F_{E/(q1 q2)}` (odd pair).

* Checked on 991, 2311, 1093 (Wieferich), 5347, 2791, 211, 547, and on 4817 = (4,43), where a
  2-power component makes `K'` slightly larger. Source: `onepw.py`.
* Consequence: arms O and Z(2) are the same problem, "`1 + theta` with `theta^R = A` in the
  previous level". Engines can share one code path.

### 1.4 Crossed descent (generalized 719 trick) [derived; identities checked on 21 rows]

**Single crossing.** Pick an odd component `chi = chi_R`, `R = r^a`, with `chi^R = alpha` in
`K = F_2(alpha_r)` (degree `b = E(r)`).

1. Choose `t | b` with `t = lcm(f(r) * r^{v_r(b)}, s, ...)`, so that `v_r(2^t - 1) = v_r(2^b - 1)`
   and `h | deg M`. Let `k = F_{2^t}`.
2. Put `c = N_{K/k}(alpha)^w` with `w = ((2^b-1)/(2^t-1))^{-1} mod r^{min(a, v_r(2^b-1))}`.
   Then `alpha/c` is an R-th power in K. Take `a = (alpha/c)^{1/R}` in K, so `chi = v a`
   with `v^R = c`.
3. `H = k[V]/(V^R - c)` has degree `R t` (Capelli: c is not an r-th power in k).
4. Let `u` be the remaining summands (other components plus the rule nimber), and
   `M = H * F_2(u)`. Then

  `N_{F_E/M}(chi + u) = v^n f_a(u/v)`, with `f_a` the characteristic polynomial of `a` over `K ∩ M`
  and `n = [K : K ∩ M]`.

**Why it is exact.** Gal(F_E/M) restricts isomorphically onto Gal(K/K∩M), because
`F_E = K M` and `r ∤ b/t`. The Euler test then runs in M, since `h | deg M`.

**Double crossing.** Cross two components, `chi_i = v_i a_i`. Use `K_all = lcm(b_i)` and
`M = lcm(R_i t_i, rest)`. The norm is `prod_j (u + sum_i v_i sigma^j(a_i))` with
`sigma = Frob^{gcd(K_all, deg M)}`. When `u = 0` this equals `N(a_2) v_1^n f_{a1/a2}(v_2/v_1)`.
Otherwise it is a bivariate norm form of degree n over `K_all ∩ M`.

**Checks.**

* Single-crossing identity and both Euler phases against direct computation in F_E on 18 rows
  (`crossing_check.py`): 881, 991, 1013, 1103, 1657, 2089, 2287, 2311, 2791, 3631 (R=121),
  3943, 4049, 4523, 4817, 5347, 11471, 32377, 57457.
* Double crossing (`crossing2_check.py`) against direct computation on 27281 (11,31), 9199 (7,73),
  and 1303 (7,31; n=4).
* A **stand-alone engine** (`crossed_row.py`) never builds F_E. It builds K from the parent tower,
  an abstract k (embedded into K by PARI `ffembed`), and H as the tower `k[V]/(V^R - c)`, asserting
  that c is not an r-th power in k. Every root extraction is checked exactly.
  * It reproduces the direct verdicts on 881, 1013, 1103, 2287, 3631, 4049, 11471, and 32377.
  * It settled **p = 797** (E = 394,020, never built): K = 1980, t = 396, n = 5, H = 78,804.
    Translate 0 is a power and translate 1 is not, so `m_797 = 1`. Time: 934 s in unoptimized
    PARI at load average about 120. The f_a step dominates, at about 200 s; the cost-table
    estimate of about 3 s assumes NTL on an idle core.
  * The runs for 839, 887, 1433, and 4507 were stopped by the lead before finishing. **No result.**

**Optimality [derived].** Any factorization `chi = v a` with `a` in K and `v` in a field H' must
have `v^R` in `K ∩ H'`. The class of alpha in `K^x / K^{xR}` is nontrivial, so `K ∩ H'` must
contain the whole r-primary part of `K^x`. That forces `f(r) r^{v_r(b)} | [K ∩ H' : F_2]`.
Since `h | deg H'`, `deg H' >= R * lcm(f(r) r^{v_r(b)}, s)`, and crossing attains this bound.
`f_a` carries exactly `b` bits (n coefficients of t bits each), so the K-level work cannot be
skipped by this route. Factoring `f_{alpha/c}(X^R)` over k to avoid the R-th root in K costs as
much as working in F_E.

**When it helps.** Crossing helps when `b >> f(r)`, typically for deep chains. It does not help
when the parent field barely contains `mu_r`:

* p=733: `b = f(61) = 60`.
* p=743: `t = b = 156`.
* p=4507: only 2x, because `f(751) = 375` and `s = 6` give `t = 750`.

**Crossed root extraction for model building [derived].** In a sparse-modulus model of F_E, embed
`chi_R` as `v * a`, with `a = (alpha/c)^{1/R}` (a b-bit exponent) and `v = c^{1/R}` in
`F_{2^{Rt}}` (an Rt-bit exponent, computed by AMM in that subgroup). This replaces one E-bit
exponentiation per component by `(b + R t)`-bit ones, about a factor R fewer multiplications.
It is legitimate by SPEC section 2 canonicity: it yields *a* root of the irreducible
`X^R - alpha`. Check `chi^R == alpha` exactly.

### 1.5 Reformulations that do not reduce work [derived]

* **Cubical coordinate Delta_h.** It acts after `T_h` is known, in `F_{2^h}`, which is cheap.
  It does not help compute `T_h`.
* **Torus / trace (Lucas) form.** For rows with `v_2(h) = v_2(E)`, i.e. `p | 2^{E/2}+1`,
  `chi_p(x)` depends only on `tau = Tr_{E/(E/2)}(x)^2 / N_{E/(E/2)}(x)` in `F_{E/2}`. The test is
  `V_{(q+1)/p}(tau) != 0`. This is the Fermat formula `u_n + u_n^{-1} = 1/a_{n-1}` in general
  form. It halves the field, but getting `tau` costs E/2 squarings in F_E, and the Lucas ladder
  then needs about E/2 multiplications. Norm-first wins.
* **Residue-symbol / Weil-reciprocity lifts.** Over `F_{2^h}[X]`, reciprocity for `(X+1)/P_1`
  is just `N_{E/h}(chi+1) = P_1(1)`: no new information. Number-field lifts are larger still.
  The paper's rank-one saturation (OPEN section 2) rules out multiplicative reciprocity words in
  general.
* **Gauss/Jacobi sums** give distributions over translate lines (Katz:
  `|sum_c chi(theta + c)| <= (R-1) sqrt q`), not single selected values.
* **Cyclotomic rows** (all components in `r` in {3, 5, 17, 257, 65537} families, mass 0.025)
  can be run in `F_2[X]/(X^N - 1)`, where Frobenius is a coordinate permutation. They are cheap
  anyway.

## 2. Rows reached (mass = sum 1/p over rows in (727, X])

From `reduce.py`, using the effective degree `max(deg M, deg K_all)` under the best crossing,
compared with E.

| budget | X = 1e4: direct | X = 1e4: crossed | X = 1e5: direct | X = 1e5: crossed |
| --- | --- | --- | --- | --- |
| <= 1e4 | 0.101 (9.6%) | 0.121 (11.4%) | 0.111 (10.5%) | 0.132 (12.4%) |
| <= 1e5 | 0.178 (16.3%) | 0.228 (20.4%) | 0.211 (19.0%) | 0.268 (23.5%) |
| <= 1e6 | 0.249 (22.0%) | 0.300 (25.9%) | 0.318 (27.3%) | 0.391 (32.3%) |
| <= 1e7 | 0.287 (25.0%) | 0.326 (27.8%) | 0.397 (32.8%) | 0.477 (38.0%) |
| <= 1e8 | 0.308 (26.5%) | 0.328 (28.0%) | 0.451 (36.3%) | 0.526 (40.9%) |
| all | 0.331 (28.1%) | | 0.553 (42.5%) | |

Per arm, mass below 1e5 by effective degree:

| arm | total | direct <= 1e6 | crossed <= 1e6 | direct <= 1e7 | crossed <= 1e7 |
| --- | --- | --- | --- | --- | --- |
| O | 0.221 | 0.104 | 0.141 | 0.131 | 0.179 |
| Z | 0.331 | 0.213 | 0.249 | 0.265 | 0.298 |

C and D together: 0.0012, already certificate-covered for `k <= 5`. ZF: 0.

Crossing's real value is larger than the degree table suggests. A crossed row of effective degree
D costs about `D^2`-ish work. A direct row of degree E needs either E-bit root extractions with a
sparse modulus, or squarings with a dense chain modulus. The cost table below shows 10^3 to 10^4
gaps.

## 3. Audit of the random-model heuristic

### 3.1 The counting claims [derived; checked]

* **Every odd prime is a row.** It has one `f(p)`, one `Q`, and one arm. So
  `E[#failures in (727, X]] = sum 1/p ~ log log X - log log 727`.
  The census agrees with Mertens: 0.3306 vs 0.3349 at 1e4, and 0.5528 vs 0.5581 at 1e5.
* Per-arm masses on (727, X]:
  * X = 1e4: Z 0.187, O 0.142, D 0.0007, C 0.0004.
  * X = 1e6: Z 0.458, O 0.276.
  * Arm Z's share grows (57% to 62%), because singleton Q gets rarer as h gains prime factors.
* **Divergence and boundedness.** Under independence, the second Borel-Cantelli lemma gives
  infinitely many failures almost surely. The same model predicts **m_p bounded**:
  `P(m_p >= rule + k) ~ p^{-k}` and `sum p^{-2}` converges. So the random model predicts
  "0/1/4 false, Lenstra's boundedness true", in line with the paper keeping them separate.
* **`v_p(2^E - 1) > 1`.** Every prime factor of `E = lcm d(chi_q)` is 2, a component prime
  `r | f(p) | p-1`, or (recursively) a factor of `b_r`. All are below p, so `p ∤ E` and
  `v_p(2^E-1) = v_p(2^h-1)`.
  * This exceeds 1 only at Wieferich primes. In range those are 1093 (arm Z, Q=(7,13), E=1092)
    and 3511 (arm Z, Q=(5,13,27), E=7020).
  * The exact Euler exponent `(2^E-1)/p` is still the correct test there. A uniform element is a
    p-th power with probability 1/p regardless of valuation.
  * Both rows are verified here: the selected element is not a 1093rd or 3511th power.
* **Proven bounds remove no small-p mass.** The arm-O large-factor bound, the packing bounds, and
  the packet bound all need `L/p` (or `Psi/p`) to be at most `2^{O(sqrt R)}`. Rows with
  `p <= 1e5` have `L/p` astronomically larger. They only exclude the giant cofactor primes,
  whose 1/p is about 0.

### 3.2 Structure: what is forced and what is free [derived, with checks]

* **Non-row characters are forced through norms.** For `ell | 2^E-1` with `f(ell) = h'`:
  `chi_ell` factors through `N_{E/D}` for every `h' | D`.
  * In arm O, every prime of `L_{r,a}` except r is a row. Every other character factors through
    `F_{r,a-1}`, where it sees `N(y_{r,a}) = y_{r,a-1}` (or `1 + alpha_r`), a structured element.
  * Example: the r-character of `y_{r,a}` is constant in a. If `m_r = 1`, then
    `1 + alpha_r = chi_{q'}` has order dividing `q'(2^{b'}-1)`, so it is forced.
  * Observed: arm-O selected elements at non-row ell are powers 28 times against 15.2 expected,
    all forced structure.
* **Row characters are free of every algebraic constraint I could find.**
  * They are trivial on each proper Kummer layer and on each subfield not containing `F_{2^h}`
    ("residue corestriction kills the new coordinate").
  * Norm compatibilities (`N y_{r,a} = y_{r,a-1}`, the parent norms) reach only non-row
    characters.
  * Distinct rows of one element are independent by CRT.
  * Quadratic characters are absent (odd p, characteristic 2).
  * Weil reciprocity reduces to the norm.
  * The paper proves multiplicative reciprocity words saturate.
* **Generator effect** (the selected element generates `F_E`). The exact probability is
  `#{p-th powers of degree E} / #{degree-E elements}`. This is 0 for p = 3, 5, 17, 257
  (all p-th powers lie in a proper subfield), 0.78/p for p = 7 and 13, and 1/p elsewhere to
  better than 10%. It matters only for p <= 257.
* **Torus-inversion mechanism** (the only probability-changing structure found). Let E be even,
  `sigma = Frob^{E/2}`, and p a row with `p | 2^{E/2} + 1`. Then
  `chi_p(sigma x) = chi_p(x)^{-1}`. So if `x = u (1 + w)` with `w^{2^{E/2}} = w^{-1}`
  (`w` in the norm-one torus) and `chi_p(u) = chi_p(w) = 1`, then x **is** a p-th power.
  * This is the mechanism behind arm D's forced translates and arm C's half-angle form.
  * Checked: arm-O translates `chi_{5^a} + omega` at rows 41, 7001, 28001 are forced powers.
    `chi_5/omega` and `chi_125/omega` lie in the torus; `chi_25 * omega` does too, which forces
    `chi_25 + omega^2`. The selected `chi_{5^a} + 1` is safe, because `ord(chi)` keeps a factor 3
    that the torus does not invert.
  * Checked: none of 46 all-cyclotomic arm-Z pairs (E <= 6000) has `chi1/chi2` or `chi1 chi2`
    in the torus. Derived reason: the 2-adic signatures `v_2(ord_ell 2)` of 3-power, Fermat, and
    5/17-chain components never agree.
  * This mechanism can only *add* failures. It is no argument that the rule holds.

### 3.3 Statistical tests with power [checked]

**Free characters of selected arm-Z elements.** All distinct elements with E <= 8000, all primes
`ell <= 50000` with `f(ell) | E`, non-row (`chars2.py`, `analyze.py`). Counts are final unless
noted: **PARTIAL**: the run was stopped by the lead after 54 minutes, at 215 of 221 elements, all with E <= 7644.

* Selected `kappa + 0`: 147 powers in 3879 trials, against 163.2 expected (z = -1.42).

* For comparison, the same characters on the non-selected translates `kappa + 1` and
  `kappa + omega`: `kappa + 1`: 156 / 3879, expected 163.2 (z = -0.63). `kappa + omega`: 149 / 3879 (z = -1.24).
  The small deficit is the same on selected and non-selected translates. It is most likely the
  small-field generator effect (section 3.2), which the naive 1/ell expectation ignores. I did not
  apply the generator correction to this table **[guessed]**.
* These are random in the same way. Selection leaves no visible multiplicative fingerprint.

**Forced classes, all as predicted.**

* Arm O, `kappa + 0` at rows: 107/107 powers.
* Arm C, `kappa + 0` at rows: 5/5 powers.
* Arm D, translates 0 and omega at rows: 3/3 powers each.
* Arm C elements at sibling arm-D rows: 4/4 powers. This is the arm-D forced translate seen from
  the C element.

**Row characters of selected elements.** 0 failures in 302 arm-Z and 127 arm-O row tests
(expected under the random model: 0.41 and 0.43), plus 797. Too little mass to say anything about
the heuristic; these are validation data.

**Arm-O non-row excess** (41 powers against 17.2 expected).
  * Derived: these characters factor through `F_{r,a-1}`, where they see structured norms.
  * Checked: the r-character of `y_{r,a}` is constant in a: always a power for r = 7 and 11,
    never for r = 5 and 13 (a = 0..3).
  * Not checked: I did not attribute each of the 41 hits individually.

**Gauss-period analog.** `gamma_N = zeta_N + zeta_N^{-1}` and `1 + zeta_N` over F_2, for prime N
(`gauss.py`): **PARTIAL**: 435 primes N <= 3967, ord_N(2) <= 2000; the run was stopped early, and the
gamma and 1+zeta classes are only partly covered.
  * Row analogs (`f(ell) = deg`), generator-corrected expectation: canonical gamma 0/195 (expected
    0.32); non-canonical gamma 1/237 (expected 0.61; the hit is N=2971, ell=881); 1+zeta 0/221
    (expected 0.35).
  * Non-row characters: z between -0.7 and -1.9, the same mild deficit as above.
  * Caveat: the N=2971 record conflicts with a re-check. With a different random root of unity,
    gamma came out primitive in `F_{2^55}`. The class of gamma is not canonical when
    `<2, -1> != (Z/N)^x`. So this sample mixes conjugacy classes, and the single hit means nothing
    either way **[checked: conflict observed; cause derived]**. The row-analog mass in that family converges, so the test has low power.
It is consistent with the random model and shows no excess of primitivity.

### 3.4 How surprising are the known data? [checked]

* Naive model over the 128 known rows (3..727): expected failures 1.65, P(0) = 0.170.
* Generator-corrected model: expected 1.006, P(0) = 0.359.
* Excluding the 13 rows the paper proves structurally (3, 5, 7, 13, 17, 19, 37, 73, 109, 151,
  241, 257, 641): expected 0.72, P(0) = 0.48.
* So the clean record is only a 1.0 to 2.8 Bayes factor toward a hidden theorem.
  * Prior 50/50: P(random model | data) is between about 0.26 and 0.5.
  * Prior 80/20 random: between about 0.6 and 0.8 **[guessed priors]**.
* Each new row verified with no failure lowers this a little: a total of about 0.1 of 1/p mass
  multiplies the odds by about e^{-0.1}.

### 3.5 Is the search well-motivated?

* Yes. The random model is the natural null hypothesis. No mechanism that suppresses failures is
  known, and the paper proves that the obvious families of such mechanisms (reciprocity words,
  norm fibres, cohomology) saturate. The data do not refute the model.
* Honest expected yield for the reachable mass of about 0.30 to 0.39 (crossed, E_eff <= 1e6,
  p <= 1e4 to 1e5): `P(hit) ~ (0.26..0.32) * P(rand | data) ~ 7-20%` **[guessed]**.
* The certain payoff is an extended exact table. Every verified row widens the Rust `Ordinal`
  exact window: for example, row 733 is verified below, which lifts the refusal at `m_733`.
* Do not oversell. A clean sweep to 1e4 would be mild evidence for structure (a Bayes factor of
  about 1.4), not a theorem.

## 4. Cost examples (single core, idle M5 NTL timings, model in `costmodel.py`) [derived estimates]

| p | arm / Q | E | direct (sparse modulus, root extraction plus norm-first) | crossed |
| --- | --- | --- | --- | --- |
| 733 | O (61) | 3,660 | ~5 ms (no gain: t=b=60) | n/a |
| 743 | Z (7,53) | 57,876 | ~8 s | none (t = b; 1+w gives the same degree) |
| 797 | O (199) | 394,020 | ~5 min | K=1980, H=78,804, n=5: ~3 s |
| 1031 | Z (5,103) | 210,120 | ~2.5 min | cross(103): M=105,060, K=408: ~1 min |
| 1433 | O (179), chain 179-89-11-5 | 3,504,820 | ~14 h (dense chain modulus: ~8 days) | K=19,580 (free chain modulus), H=31,862, n=110: ~10 s |
| 4507 | O (751) | 1,126,500 | ~45 min | K=1500, H=563,250 (t=750), n=2: ~3-4 min |
| 839 | O (419) | 15,762,780 | ~26 days | K=37,620, H=175,142, n=90: ~1 min |
| 887 | O (443) | 2,349,672 | ~5 h | K=5304, H=195,806, n=12: ~20 s |
| 9973 | Z (3,277) | 4,204,860 | ~2 days | cross(277): M=76,452, K=5060 |

Scaling:

* Direct cost is about `#comp * (E/6) M(E) + E S(E)`: roughly `E^2 log E`.
* Crossed arm-O cost is about `(b/6) M(b) + (n^2/2) M(b) + R t * R M(t)` for tower squarings in
  `H = k[V]/(V^R - c)`, plus O(R) multiplications.
* The gap is the factor `E / max(b, Rt) ~ min(R, b/t)`, squared.

## 5. Correctness risks

* **Wrong t (valuation condition).** If `v_r(2^t-1) < v_r(2^b-1)`, then `alpha/c` is not an
  R-th power. Mitigation: always verify `a^R == alpha/c` and `V^R == c` exactly. The prototype
  asserts both.
* **`K ∩ M` mis-identified** (for example `r | b/t`). Then `n` and `f_a` are wrong. Mitigation:
  build `f_a` from the actual Frobenius orbit and assert that the orbit closes after n steps and
  that the coefficients lie in the intended subfield.
* **Transport of k.** `c` and the coefficients of `f_a` must cross into H through the *same*
  embedding `k -> K`. Any one embedding is legitimate, but mixing two is not.
* **Shared components in the Z crossing.** The rest `u` and the crossed `v_i, a_i` must come from
  one model of the ancestors. Otherwise the relative phases are free (SPEC section 2).
* **Order-free search after a hit.** The certificate must say "assuming the rule for ancestors".
  Then rerun the ancestors to name the least counterexample. A failure at r with
  `m_r = 4` instead of 1 changes `b_r` and every descendant's degree.
* **Batching by element.** Use the full p-primary exponent for each p (Wieferich 1093 and 3511).
  Never use a combined `ord`-divisibility test.
* **PARI quirks seen here.** `polrootsmod` over `F_{2^5060}` overflowed a 4 GB stack; it was
  replaced by a trace-one Artin-Schreier solver. An `ffgen` element is not primitive, so derive
  roots of unity from random elements. Prototypes only; a production engine should use
  NTL/FLINT.
* **Statistical caveat.** All randomness evidence concerns E <= 8000. The large-E regime is
  untested by construction.

## 6. Implementation plan (for the shared engine)

1. **Scheduler.** Group rows by `(Q, m)` and process elements in increasing effective cost
   (order-free search, section 1.2). Ancestors come first automatically.
2. **Per element, choose the descent:**
   * `|Q| = 1` odd (arm O): crossed descent if `b/t >= 4`, otherwise direct.
   * `|Q| = 2`: use the `1 + w` form and cross over `K' = F_{E/(q1 q2)}` (composite R), or cross
     each component (section 1.4, double).
   * `|Q| = 3`: direct, with crossed root extraction for embedding.
   * C/D/ZF: existing certificates. Run cyclotomic rows in `F_2[X]/(X^N - 1)`.
3. **K-level.**
   * Chain parents get their free min poly as a dense modulus, `P_{chi'}(X^R + 1)`.
   * Z parents get a sparse model with components embedded by crossed root extraction, then the
     min poly of `alpha` by power projection.
   * Compute `c`, `a` (asserting `a^R == alpha/c`), the Frobenius orbit of `a`, and `f_a` by a
     subproduct tree.
4. **k transport.** Build `k = F_2[y]/P_k` from the min poly of a generator of k inside K, and
   express `c` and the coefficients of `f_a` in the y-basis (t x b F_2 linear solve).
5. **H-level.** Use the tower `k[V]/(V^R - c)`: squaring is coefficient squaring plus a fold by c.
   Compute `W = V^n f_a(u/V)`, then norm-first down to `F_{2^h}` and the Euler test for every
   row prime of the element.
6. **Exact checks** on every relation, plus a cross-check of crossed against direct on all rows
   with `E <= 1e5` (about 1400 rows below 1e5).
7. **On a hit.** Emit a certificate with K's modulus, `alpha`, `c`, `a` (with `a^R` check), `f_a`,
   `P_k`, H, V, W, and the Euler phase. Replay it independently in PARI, as the 719 certificate
   does.

## 7. New rows verified in this session (p > 727; ancestors all at most 709, hence unconditional)

**Unconditional**: every ancestor is at most 709, so it is covered by OEIS. Each row's selected
rule element was tested with the exact Euler exponent in an explicit model of F_E (PARI;
`Tower` in `tower.py`). The tower reproduces all 84 OEIS rows with E <= 3000 (`validate.py`).

* **Rows from the residue run** (E <= 7644, partial; section 3.3): 345 rows in (727, 49921]
  pass the rule. **No failures.** By arm: Z 254, O 88, C 2, D 1. Mass sum 1/p = 0.098.
  * This includes 733, the current refusal point of `Ordinal`, and both Wieferich rows (1093 and
    3511, full p-primary exponent).
  * Their forced translates (arm O `kappa + 0`, arm C/D `kappa + 0, omega`) all came out powers,
    as the paper proves.
  * The list (`newrows.py chars_merged.pkl`) begins: 733, 739, 751, 757, 761, 769, 811, 821, 877,
    881, 883, 911, 919, 937, 953, 971, 991, 1009, 1013, 1021, 1033, 1051, 1093, ...
  * Caveat: these come from a research prototype that the lead will replicate. Treat them as
    validation targets for the v2 engine, not as certificates.
* **797** (arm O, E = 394,020) by the stand-alone crossed engine: `m_797 = 1`.
* **Not completed**: 839, 887, 1433, 4507 (stopped). The rows above 49921 in the census with
  E <= 7644 were not covered.

