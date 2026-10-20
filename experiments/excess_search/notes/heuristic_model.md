# The random model for the 0/1/4 rule: statement, numbers, consequences

Each claim carries one tag:

- **[S]** standard or cited result;
- **[D]** derived here, with the proof given inline;
- **[N]** checked numerically (the script and output are named);
- **[H]** heuristic or speculation.

Everything numerical comes from `census_fast.py` (the arm census for all odd primes
`p <= 1e8`; it reproduces `../rows_1000000.pkl` with 0 mismatches),
`recip_sum.py` (exact `sum 1/p` and `sum log(1-1/p)` over `(727, X]` for `X <= 1e9`),
`model_calc.py` (output in `model_calc_1e8.out`), `struct_check.py` and `small_cells.py`.

## 0. Summary

- **The model is a statement about one marked phase per row.** Every odd prime
  `p` is exactly one row. The rule at `p` is the Euler phase
  `rho_p = beta_p^((2^E-1)/p) in mu_p` of `beta_p = kappa_f(p) + rule(p)`, and the
  rule fails exactly when `rho_p = 1`. The model says `rho_p` is uniform on `mu_p`,
  conditionally on all earlier rows and on the proven structure. Under that
  hypothesis the failure probability is exactly `1/p`, including at the
  Wieferich-type rows where `v_p(2^E-1) > 1` (§1.1).
- **What the observed data say.** The observed rows `11 <= p <= 727` have model
  likelihood **0.42 to 0.49**, so the data favour "the rule is a theorem" over the
  model by a Bayes factor of only about **2.0 to 2.4** [N].
- **Expected failures in `(727, X]`** [N up to `1e9`, Mertens beyond]:

  | `X` | expected failures | `P(no failure)` |
  | --- | --- | --- |
  | `1e4` | 0.33 | 0.72 |
  | `1e5` | 0.55 | 0.58 |
  | `1e6` | 0.73 | 0.48 |
  | `1e8` | 1.02 | 0.36 |
  | `1e9` | 1.14 | 0.32 |
  | `1e20` | 1.94 | 0.144 |
  | `1e100` | 3.55 | 0.029 |

- **Inside the model, the rule fails infinitely often almost surely** [D, by the
  second Borel–Cantelli lemma]. The conclusion survives without independence: it
  needs only a conditional lower bound `>= c/p` (Lévy's extension).
  - The failure count grows like `log log X`.
  - The first failure has `P(F > X) ~ 6.6 / ln X`, a log-Pareto tail. Its median
    is about `5.8e5` and its 90% quantile about `6e28`.
- **Where the failures land** [H, trend checked to `1e8`]:
  - Asymptotically all failures are in **arm Z**, where they give `m_p = 1` instead
    of 0. Arm Z carries the whole `log log` divergence.
  - The **arm O** share of the `1/p` mass decays like
    `~1.1 sigma_{-1}(b_r) / ln x`, so its total mass is finite. The expected number
    of arm O failures beyond 727 is about **0.62** (range 0.55 to 0.66), so
    `P(arm O never fails) ~ 0.54`.
  - Arms C, D and ZF have finite residual mass of `5.8e-5`, `7.7e-5` and `~1e-8`.
    The model predicts that all three hold for every `p` with probability about
    0.9999.
- **Boundedness survives the model.**
  - `P(m_p >= rule(p) + 2) = p^(-2)`, which is summable, so `sup m_p < infinity`
    almost surely. This needs only marginals, not independence.
  - `m_p in {rule(p), rule(p)+1}` for every `p > 727` with model probability
    `1 - 1.8e-4`.
  - **`m_p <= 4` for every `p` holds with model probability `1 - 7.8e-5`.** The only
    realistic way to exceed 4 is a failure in arm D, which gives `m_p = 5`.
  - The forced smaller translates never fail. They are identities, not random
    events.
- **A new unconditional statement for the success direction** [D].
  - Every arm O cell with squarefree prime-to-`r` order contains a row that obeys
    the rule.
  - A square factor in such a cell forces a base-2 Wieferich prime. The two known
    Wieferich primes (1093, 3511) both lie in Z cells.
  - So, if only finitely many base-2 Wieferich primes lie in O cells, the rule holds
    for infinitely many `p`.
  - The failure direction ("infinitely many counterexamples") has no comparable
    reduction. It is at least as hard as the infinitude of Wieferich primes (§5).

---

## 1. The precise model

### 1.1 Row events and the `1/p` probability

For an odd prime `p` put `h = f(p) = ord_p(2)` and
`beta_p = kappa_h + rule(p) in F_(2^E)`, where `E = d(beta_p)`. By the exact
power criterion (excess.tex, Prop. `power`), the rule fails at `p` exactly when

```text
rho_p := beta_p^((2^E-1)/p) = 1,   i.e. beta_p in (F_(2^E)^x)^p.
```

- **[D] The probability is `1/p` for every valuation.** In a cyclic group `G` of
  order `N` with `p | N`, the subgroup of `p`-th powers `pG` has index exactly `p`,
  whatever `v_p(N)` is. So a uniform element is a `p`-th power with probability
  exactly `1/p`. This is the right event; the weaker "`p` divides `ord`" event would
  have probability `1 - p^(-v)` and is not the row test (excess.tex stresses the
  full valuation).
- **[D] Which rows are Wieferich-type.** For every row, `v_p(2^E - 1) = w_p`, where
  `w_p := v_p(2^h - 1)`.
  - *Proof.* Lifting the exponent gives `v_p(2^E-1) = v_p(2^h-1) + v_p(E/h)`. Every
    prime factor of `E` is either a prime of `h` (and so `<= h < p`) or a prime of
    some `b_s` with `s < p`. Those are closure primes, all `< p`, so `p` does not
    divide `E`.
  - Also, `w_p >= 2` holds exactly when `p^2 | 2^(p-1) - 1`, i.e. when `p` is a
    base-2 Wieferich prime, because `ord_(p^2)(2)` is `h` or `ph`.
  - So the only rows with `v_p > 1` among `p < 6.7e15` are `p = 1093` (h = 364,
    `Q = {7, 13}`) and `p = 3511` (h = 1755, `Q = {5, 13, 27}`). Both are arm Z
    and both lie above the observed range [N, `small_cells.py`; the Wieferich search
    bound is cited in §4].
  - Their failure probability is still exactly `1/p`. The "Wieferich" concern
    affects only the cell-success lemma (§5.2), not the model's marginals.

### 1.2 Cells: the partition of rows by selected coordinate

By the four-arm reduction (excess.tex, Thm. `arms`) and the norm reduction, the
phase `rho_p` is the image of one selected coordinate `X_c`, which lives in a finite
cyclic group `G_c`. Several rows share one coordinate:

| cell `c` | `G_c` (cyclic) | selected `X_c` | rows `P_c` |
| --- | --- | --- | --- |
| `Z_h`: `Q(h)` not a singleton odd prime power, `h != 2^k` | `F_(2^h)^x / (F_(2^h)^x)^(Pi_h)`, order `Pi_h` | class of `T_h = N(kappa_h)` | `{p : f(p) = h}` |
| `ZF_n`: `h = 2^(n+1)` | torus `T_n`, order `F_n` | `u_n = (c_n+1)/c_n` | `{p : p \| F_n}` |
| `O_(r,a)`: `r >= 5`, `a >= 1` | `G_(r,a) = F_(r,a)^x / F_(r,a-1)^x`, order `L_(r,a) = Phi_(r^a)(2^(b_r))` | `y_(r,a) F_(r,a-1)^x` | `{p != r : p \| L_(r,a)}` |
| `C_k`: `h = 3^k` | quotient of order `Phi_(3^k)(2)` | `gamma_k` (equivalently `eta_k`) | `{p : f(p) = 3^k}` |
| `D_k`: `h = 2*3^k` | quotient of order `Psi_k` | `M_k` | `{p : p \| Psi_k}` |

- **[D] The cells partition the odd primes.**
  - Each `p` has one `h = f(p)`, and the arm is a function of `h`.
  - For the O cells: if `Q(f(p)) = {r^a}` then `f(p) = r^a g` with `g | b_r`, so
    `p | L_(r,a)`.
  - Conversely, if `p | L_(r,a)` and `p != r`, then `f(p) | r^a b_r` and
    `v_r(f(p)) = a`. All primes of `b_r` are smaller than `r`, so `r^a` is the
    innermost component. Each further prime power `s^j` of `f(p)` divides `b_r`, so
    it is absorbed. Hence `Q(f(p)) = {r^a}`.
  - The primes `p != r` are not in the kernel, because
    `gcd(Phi_(r^a)(x), x^(r^(a-1)) - 1)` is a power of `r`. So the `p`-primary part
    of `F_(r,a)^x` maps isomorphically onto that of `G_(r,a)`.
  - Within a cell, the CRT gives `G_c ~ prod_(p in P_c) Z/p^(v_p) x (rest)`. The row
    events are `X_c in pG_c`, one per CRT factor.
- **[D] Ancestry is compatible with numerical order.** Every closure prime of a cell
    is smaller than every row of that cell, because closure primes are `<= h < p`.
    Filtering by increasing `p` is therefore an ancestry filtration.
- **[D] The model does not depend on which coordinate is used.** Suppose two
    coordinates are related by an isomorphism of the `p`-quotient,
    `X' = phi(X) * (p-th power)` with `phi` an automorphism. Then they give the same
    row event. Uniformity transports between them, so it does not matter whether
    one randomizes `kappa_h`'s norm, `T_h`, the cubical primitive-support coordinate,
    `gamma_k` or `eta_k`.

### 1.3 The model, in three strengths

- **M (uniform cell model).** The coordinates `(X_c)_c` are independent across
  cells. Each `X_c` is uniform on `G_c`, conditioned on the proven constraints
  `K_c` (nontriviality and proven order lower bounds; see §1.4).
  - **Consequence [D].** For every row `p in P_c` with `|G_c| >> p * B_c * tau(|G_c|)`
    (with `B_c` the proven order bound), `P(rho_p = 1 | all other rows) = 1/p` up
    to a relative error `< B_c tau(|G_c|) p / |G_c|`. That error is astronomically
    small for every census row.
  - The row events are independent `Bernoulli(1/p)` variables: independent within a
    cell by the CRT, and across cells by hypothesis.
- **M_Levy (weak, the only input needed for infinitely many failures).** There is a
  `c > 0` and a set `R` of rows with `sum_(p in R) 1/p = infinity` such that
  `P(rho_p = 1 | F_(<p)) >= c/p` for `p in R`, where `F_(<p)` is generated by all
  phases at rows `q < p`.
  - This replaces independence by a conditional lower bound. It answers Codex's
    caveat (codex_design.md §7) that the step to `1 - exp(-sum)` needs independence:
    the infinitely-often conclusion does not.
- **M+ (translates, used only for the size of `m_p`).** For each row, the phases of
  `kappa_h + m` for `m > rule(p)` are uniform, independent of each other and of
  everything else, one per Frobenius orbit over `F_(2^E)` (§3.4).

### 1.4 What is deterministic, and therefore excluded

| kind | rows | treatment |
| --- | --- | --- |
| prime cell plus nontriviality | Fermat primes 3, 5, 17, 257, 65537 (`delta_n > 1` and `F_n` prime); `C_1, C_2, C_3` (`Phi_(3^k)(2) = 7, 73, 262657` prime); `D'_2, D'_3` (`Psi_k = 19, 87211` prime) | forced by `K_c` |
| other theorems | `Z` at `h = 12, 15, 24, 36, 40` (tensor proofs) | settled |
| exact finite certificates | `C_4, C_5`; `D'_4, D'_5`; ZF cells `n <= 11`; published factors of `F_12..F_18`; `m_359 = m_719 = m_727 = 1` | settled |
| conditional numeric | 1433, via the 359 norm (Codex; the norm link was not replayed) | kept as unsettled; it carries mass `7e-4` |
| size-forced | large-factor ranges: O bottom-ancestor (`L/p <= b_r r^a`), D packing, Fermat `p > 2^(2^n-n-2)`; also any O cell with `L'` prime | contain **no** census row `<= 1e8` [N]; their asymptotic mass is negligible |

The settled rows above 727 inside the census are 1459, 2593, 61681, 65537,
71119, 87211, 114689, 135433, 139483, 262657, 274177, 319489, 974849, 2424833,
6700417, 13631489, 26017793, 45592577, 63766529 and 97685839. Their total mass
is `0.00116` [N].

**[D] Nontriviality in arm O.** The image of `y_(r,a)` in the prime-to-`r` quotient
`G'` is nontrivial.

- `v_r(L_(r,a)) = 1` by lifting the exponent, because `f(r) | b_r`.
- So a trivial image means `y^r in K := F_(r,a-1)`.
- `K` contains `mu_r`, so by Kummer theory `y in K^x chi^j` for some `j`.
- But `y = 1 + chi` has two nonzero coordinates in the `K`-basis `1, chi, ..., chi^(r-1)`
  with `r >= 3`. That is a contradiction.

In the small O cells (`r <= 31`) checked by factoring `L'`, every `L'` is composite
and squarefree, so no row there is nontriviality-forced [N, `small_cells.py`].

**[D] Rule+1 failures never change a field degree, so the census does not depend on
the model's outcomes.**

- Every `b_r` is even, by induction: `b_3 = 2`, and `Q(f(r))` is nonempty. An odd
  component `chi_(s^k)` contributes `s^k b_s`, which is even; a 2-power component
  has even degree. [N] confirms no odd `b_r` for `r <= 1e6`.
- A failing row moves to `m_p = rule + 1`, and the degree is unchanged in each arm:
  - Z: `+1` lies in `F_2`.
  - O and C: `2` lies in `F_4`, which is inside `F_(2^(r^a b_r))`.
  - D: `5` lies in `F_16`, and `4` already divides the degree.
- So `d(alpha_p)`, every `Q`-set, every arm and every `E` are unchanged. Only
  radicands move, and descendants must be recomputed (the engine requirement in
  SPEC §6.4), but the cell structure is fixed.
- Degree changes need `m_p >= rule + 2`, which has total probability below
  `1.8e-4` (§3.4).

### 1.5 Evidence bearing on the hypothesis

- **Against naive uniformity [D].** "`kappa_h` is a uniform element" is false.
  - In arms O, C and D the smaller translates are provably `p`-th powers. For
    example, `chi_(r^a)` has image of order dividing `r` in `G_(r,a)`.
  - A naive model would predict `m_p = 0` for an O row with probability `1 - 1/p`,
    which contradicts 100% of the O rows.
  - So the model must be "uniform modulo known structure". Its real content is the
    claim that **no further structure** controls the rule-value phase. The
    conjecture "the rule always holds" is precisely a claim that such structure
    exists.
- **For independence across cells [S/D, from excess.tex].**
  - Cross-arm induction is primary-vacuous: ancestors live in fields `F_(2^d)` with
    `f(p)` not dividing `d`, so their `p`-Kummer images are trivial.
  - Rank-one reciprocity saturation (excess.tex, Prop. `reciprocity-saturation`)
    shows that every homogeneous multiplicative reciprocity word erases the phase or
    restates it.
  - The D norm-fibre result shows every birth-level fibre contains every Kummer
    class.
  - So no known multiplicative relation sees a new row's phase. The phase is born
    at an additive step (a sum of components, or `+ rule`), which is the classical
    setting for "multiplicatively random" heuristics.
- **A shared shape [D, after codex_design.md §2].** A two-component Z row has phase
  equal to that of `1 + z`, with `z = y_1/y_2` a radical of composite degree
  `R_1 R_2`. That is the same "one plus a Kummer radical" shape as `y_(r,a)` in
  arm O. A structure theorem forcing `1 + radical` to have full order would
  therefore break the model in arms O and Z at once. The model treats both arms
  identically.
- **Where averaging is provable [S/D].** By Katz's bound (§3.6), translates are
  equidistributed on average over a long line `kappa + F_q` with `q >> E^2`. The
  model's assertion is about a single translate, the regime where character-sum
  bounds are vacuous.

---

## 2. Numbers from the census

### 2.1 Likelihood of the observed data, `11 <= p <= 727` [N]

| variant | rows | `sum 1/p` | `P(no failure)` |
| --- | --- | --- | --- |
| conservative: drop every settled row (table §1.4) | 110 (Z 50, O 60) | 0.708 (Z 0.237, O 0.471) | **0.488** (Z 0.788, O 0.620) |
| data-inclusive: drop only the nontriviality-forced rows 17, 19, 73, 257; count certificate and tensor rows as observations | 121 | 0.847 | **0.423** |

- Rows `p < 11` are all forced: 3 and 5 are Fermat primes, and 7 is `C_1`.
- Against `H_0` ("the rule is a theorem", likelihood 1), the data give a Bayes factor
  of **2.0 to 2.4** in favour of `H_0`. That is weak evidence, worth about one
  coin flip. The 126 OEIS rows do not discriminate between the model and the rule.

### 2.2 Predictions on `(727, X]` with settled rows removed

| `X` | rows | `E[fail]` all | `E` in Z | `E` in O | `E` in C+D+ZF | `P(no failure)` |
| --- | --- | --- | --- | --- | --- | --- |
| `1e4` | 1098 | 0.3295 | 0.1874 | 0.1421 | 0 | 0.7192 |
| `1e5` | 9457 | 0.5516 | 0.3305 | 0.2210 | `1.2e-4` | 0.5760 |
| `1e6` | 78356 | 0.7337 | 0.4577 | 0.2758 | `1.3e-4` | 0.4801 |
| `1e7` | 664435 | 0.8878 | 0.5712 | 0.3165 | `1.4e-4` | 0.4115 |
| `1e8` | 5761306 | 1.0213 | 0.6732 | 0.3479 | `1.4e-4` | 0.3601 |
| `1e9` | — | 1.1391 | ~0.764 | ~0.373 (0.371–0.375) | `1.4e-4` | 0.3201 |
| `1e20` | — | 1.938 ± 0.0014 | ~1.43 | ~0.50 (0.47–0.51) | `1.4e-4` | 0.144 |
| `1e100` | — | 3.547 ± 0.0012 | ~2.92 | ~0.60 (0.54–0.63) | `1.4e-4` | 0.0288 |

How the rows were computed:

- **Up to `1e8`:** exact over the census [N].
- **`1e9`:** exact totals from `recip_sum.py`, `sum_(727<p<=1e9) 1/p = 1.1402488`, minus
  the settled mass `0.00116` [N]. The arm split is extrapolated.
- **`1e20` and `1e100`:** Mertens [S] plus the Rosser–Schoenfeld error bound
  `|sum_(p<=x) 1/p - lnln x - B| < 1/(2 ln^2 x)` for `x > 286` [S].
- **The product.** `P(no failure) = prod(1 - 1/p)`. Its second-order term
  `sum(-log(1-1/p) - 1/p)` over `p > 727` is `9.0e-5` [N]. By Le Cam's inequality the
  failure count is Poisson to within `l1` distance `2 sum p^(-2) <= 3.6e-4` [S].
- **The O column beyond `1e8`** uses the extrapolations in §2.3 [H].
- **The Z column** is the total minus the O column minus the column for arms C, D
  and ZF.

### 2.3 Shares by arm, and convergence of the O mass

Mass shares of the unsettled rows by decade [N]:

| decade | total mass | Z share | O share |
| --- | --- | --- | --- |
| `(1e3, 1e4]` | 0.2839 | 0.577 | 0.423 |
| `(1e4, 1e5]` | 0.2222 | 0.644 | 0.355 |
| `(1e5, 1e6]` | 0.1820 | 0.699 | 0.301 |
| `(1e6, 1e7]` | 0.1541 | 0.736 | 0.264 |
| `(1e7, 1e8]` | 0.1335 | 0.764 | 0.236 |

- **Form of the decay [N].** Over half-decades from `1e3` to `1e8`, `share * ln x`
  rises slowly (3.30 to 4.09), while `share * ln x / lnln x` falls slowly (1.64 to
  1.42). A power-law fit gives `share ~ 2.10 (ln x)^(-0.77)`, and the local exponent
  is steepening, from -0.72 early to -0.77 late.
- **Structural explanation [H, with the inputs checked].**
  - The per-conductor heuristic says that `sum_(f(p)=h) 1/p ~ 1/(h' ln h')` with
    `h' = lcm(2, h)`. Over `h in [100, 20000)`, the census-to-`1e8` mass is 1.20 to
    1.25 times the heuristic [N, `struct_check.py`].
  - An O cell `(r, a)` carries mass about `sigma_{-1}(b_r) / (r^a ln r^a)`, so the
    O share at height `x` is about `kappa sigma_{-1}(b_r) / ln x`.
  - The mean of `sigma_{-1}(b_r)` over `r` grows from 2.44 (`r ~ 1e1`) to 3.55
    (`r ~ 1e6..1e7`), about `1.51 + 0.755 lnln r` [N].
  - With that fit, `kappa ~ 1.1` matches the observed share at both ends of the
    range.
  - Gronwall gives `sigma_{-1}(n) <= (e^gamma + o(1)) lnln n` [S]. In the census, `ln b_r / ln r` is about 1.6 to 1.8 and growing slowly [N, median
    `log10 b_r` versus `log10 r` over the decades `1e4..1e7`]. That is consistent
    with `ln b_r = O(ln^2 r)`, so `lnln b_r = O(lnln r)`.
  - Together these give an O share `= O(lnln x / ln x)`, and
    `int lnln x/(x ln^2 x) dx < infinity`. **So the total O mass is finite**, while
    the total mass diverges. Hence **all of the divergence is in arm Z.**
- **Tail of the O mass beyond `1e8`:**

  | fit | O mass beyond `1e8` |
  | --- | --- |
  | `c / ln x` | 0.199 |
  | `c lnln x / ln x` | 0.305 |
  | power law | 0.275 |
  | structural fit `1.1(1.51 + 0.755 lnln u)/u` | 0.267 |

  - Expected O failures beyond 727 sum to `0.348 + (0.20 to 0.31)`, which is
    **about 0.62 (range 0.55 to 0.66)**.
  - `P(no arm O failure beyond 727) ~ e^(-0.62) ~ 0.54` [H]. None was observed
    through 727.
  - The finiteness can fail only if `sigma_{-1}(b_r)` grew like a power of `ln r`.
    That would need `ln b_r` to grow faster than any power of `ln r`, which the
    closure structure (a Pratt-like tree with `b_r <= r^(O(log r))`) seems to
    exclude [H].

### 2.4 The convergent arms C, D, ZF [N plus H for the tails]

- **Unsettled C rows `<= 1e8`:** 39367 (h = 3^7), 80191, 97687, 379081 (3^6),
  209953, 1299079 (3^8), 472393 (3^10) and 88219207 (3^12). Mass `5.84e-5`.
- **Unsettled D rows `<= 1e8`:** 17497, 5419387, 6049243 (h = 2*3^7), 52489,
  28934011 (2*3^8), 1220347 (2*3^9) and 86093443 (2*3^16). Mass `7.74e-5`.
- **ZF:** every ZF row `<= 1e8` is settled.
- **Tails beyond `1e8` [H].** The tail of each cell is about `1/(1e8 ln 1e8)`, so
  the tail mass for each arm is about `1e-8`. The conductors are so sparse
  (`3^k`, `2*3^k`, `2^(n+1)`) that the total mass is finite.
- **Consequence [H].** The model predicts that C, D and the Conway–Fermat arm hold
  for **every** `p` with probability about `1 - 1.4e-4`.
  - Wiedemann's sibling tower has the same cells, so the same prediction applies to
    Wiedemann's question.
  - These arms are "Wiedemann-type": convergent sums, so a universal conjecture is
    what the heuristic supports.

### 2.5 Planning the search

With the reachable mass from codex_design.md §6, `P(hit) = 1 - exp(-mass)`:

| route | mass | `P(hit)` |
| --- | --- | --- |
| degree-qualified rows through `1e5`, cap `1e5` | 0.265 | 23% |
| cap `1e6` | 0.384 | 32% |
| cap `1e7` | 0.471 | 38% |
| every row to `1e5` | 0.552 | 42% |
| every row to `1e6` | 0.734 | 52% |

- The marginal value of a row is its `1/p`.
- For scheduling, an O row and a Z row of the same `p` are worth the same. But a Z
  row is the kind the model expects to fail infinitely often, while O rows dominate
  the small-`p` mass (§2.3).

---

## 3. Consequences of the model

### 3.1 Infinitely many failures [D]

**Theorem (in model M_Levy).** Let `A_p = {rho_p = 1}`. If
`P(A_p | F_(<p)) >= c/p` on a set of rows with `sum 1/p = infinity`, then almost
surely `A_p` happens for infinitely many `p`.

- *Proof.* Lévy's extension of the Borel–Cantelli lemma [S] says that
  `limsup A_p = {sum_p P(A_p | F_(<p)) = infinity}` almost surely. The right-hand
  sum is `>= c sum_(p in R) 1/p = infinity` everywhere.
- In model M, the rows `p > 727` with the settled rows removed carry
  `sum 1/p = infinity`: Mertens [S], minus the settled mass, which is finite
  (§2.4). By §2.3 the Z rows alone already have divergent mass.
- **Mathlib.** The Lévy form is `MeasureTheory.ae_mem_limsup_atTop_iff`
  (`Mathlib/Probability/Martingale/BorelCantelli.lean`). The independent form is
  `ProbabilityTheory.measure_limsup_eq_one`. Divergence of the prime reciprocals is
  `Nat.Primes.not_summable_one_div`. A sibling `Ogdoad.ExcessRandomModel` file is
  being written beside this one (`axioms.lean` lists
  `RandomModel.ae_infinite_fails`), so the model-level theorem is directly
  formalizable.

### 3.2 The counting function [D in the model, from standard limit theorems]

Let `N(X)` count failures in `(727, X]`, with mean `mu(X) = sum 1/p = lnln X - lnln 727 + O(1)`.

- **Ratio limit.** `N(X)/mu(X) -> 1` almost surely. Under independence this is the
  strong law for independent Bernoulli variables with divergent mean sum. Under
  M_Levy it is Lévy's ratio form [S].
- **Fluctuations.** Under M,
  `(N(X) - mu(X)) / sqrt(mu(X)) -> N(0,1)` by Lindeberg–Feller, because the
  variance `mu - sum p^(-2)` tends to infinity.
- **Practical scale.** `mu(1e100) = 3.55`. "Infinitely many" is invisible in
  practice: about 3.5 failures are expected below a googol, and about 1.1 below
  `1e9`.

### 3.3 The first failure [D in the model, N numerically]

- `P(F > X) = prod_(727<p<=X, unsettled) (1 - 1/p)`. Mertens' third theorem [S]
  gives `P(F > X) ~ C / ln X` with `C = 6.63` (fitted at `X = 1e9`;
  `ln 727 = 6.59`).
- So `ln F / ln 727` is approximately `Pareto(1)`, and `E[ln F] = infinity`.
- The distribution, conditioned on no failure through 727:

  | `X` | `1e4` | `1e5` | `1e6` | `1e8` | `1e12` | `1e20` | `1e50` | `1e100` |
  | --- | --- | --- | --- | --- | --- | --- | --- | --- |
  | `P(F > X)` | 0.719 | 0.576 | 0.480 | 0.360 | 0.240 | 0.144 | 0.058 | 0.029 |

  | quantile | 10% | 25% | 50% | 75% | 90% | 99% |
  | --- | --- | --- | --- | --- | --- | --- |
  | `F` | 1549 | 6841 | `5.8e5` | `3.3e11` | `6.4e28` | `1e288` |

- **For the search.** There is a 28% chance below `1e4` and a 52% chance below
  `1e6`. Beyond that, each factor of 10 in `log X` buys only about 10 percentage
  points.

### 3.4 The value of `m_p` at a failure, and boundedness

Under M+, take the translates `t = rule(p), rule(p)+1, ...`. Each new Frobenius
orbit `{kappa + sigma(m)}` with `sigma in Gal(F_(2^E')/F_(2^E))` gives one fresh
`1/p` event.

- **[D] The first two translates are separate events.**
  - `E` is always even (§1.4), so `Frob^E` fixes `F_4`.
  - In arm D, `4 | E`, so `Frob^E` fixes `F_16`.
  - Hence `rule(p)` and `rule(p)+1` lie in distinct orbits in every arm, and
    **`P(m_p >= rule + 2) = p^(-2)` exactly** under M+.
  - More generally, `P(m_p >= rule + j) = p^(-o_j)`, where `o_j` is the number of
    orbits among `rule..rule+j-1`. Translates in `F_16 \ F_4` merge in pairs when
    `E = 2 mod 4`. Frobenius on the nimbers sends `4 -> 6 -> 5 -> 7 -> 4`, since
    `chi_4^2 = chi_4 + chi_2`.
- **At a failure, `m_p = rule + 1` with probability `1 - 1/p`.** That means
  `m_p = 1` in Z, `m_p = 2` in O and C, and `m_p = 5` in D.
- **Boundedness, almost surely [D].** `sum_p P(m_p >= rule + 2) = sum p^(-2) < infinity`.
  The first Borel–Cantelli lemma (marginals only, no independence) gives finitely
  many `p` with `m_p >= rule + 2`. Each `m_p` is finite (Lenstra), so
  `sup m_p < infinity` almost surely.
  - This holds even under strong positive correlation: any marginal
    `P(m_p >= rule + 2) <= C p^(-1-eps)` suffices.
  - Lenstra's question is therefore heuristically "yes", and much more robustly so
    than the rule is heuristically "no".
- **The predicted supremum, given the data through 727 [N/H].**
  - `P(some p > 727 has m_p >= rule + 2) = 1.80e-4`.
  - `m_p >= 5` arises from a failure in arm D, with probability `7.74e-5` (census)
    plus about `1e-8` (tail). Arm O would need four translates `1, 2, 3, 4` to be
    `p`-th powers (`sum p^(-4) ~ 1e-10`), and arm Z five.
  - So **`sup m_p = 4` with model probability `1 - 7.8e-5`.**
  - The values taken infinitely often are 0, 1 and 4.
  - The value 2 appears in arm O failures: finitely many, and none at all with
    probability about 0.54.
  - The value 3 needs a row where `kappa + 2` is a `p`-th power but `kappa + 3` is
    not, probability `O(p^(-2))`.
  - Hence the **value set** `{0, 1, 4}` survives with model probability about 0.54,
    even though the **arm assignment** fails almost surely.

### 3.5 The forced translates never fail [D]

The model predicts no failure among the translates below the rule value in arms O,
C and D. Those translates are `p`-th powers by algebraic identities that hold for
every element of the given shape.

- **Arm O.** `chi_(r^a)^r in F_(r,a-1)`, so the image of `chi` in `G_(r,a)` has order
  dividing `r`, and `p != r`.
- **Arm D.** This is the first-possible-translate proposition, `prop:d-lower`.
- These are probability-1 events, conditioned into `K_c`. There is no selected phase
  for the model to randomize.
- The model randomizes only the first coordinate that no known identity decides.
  Consequently every model failure is an upward move `m_p > rule(p)`; the model
  never produces `m_p < rule(p)`.

### 3.6 A model-free bound on `m_p` for each row [S + D]

**Katz's bound [S].** If `theta` generates `F_(q^n)` over `F_q` and `chi` is a
nontrivial multiplicative character, then
`|sum_(t in F_q) chi(theta + t)| <= (n-1) sqrt q`.

**Corollary [D].**

- Take `q = 2^(2^a)` (so `F_q = C_a`) and `n = E/gcd(E, 2^a)`.
- Sum over the characters of order `p`. If every translate `kappa + t` with
  `t in C_a` were a `p`-th power, then `q <= q/p + ((p-1)/p)(n-1) sqrt q`, which
  forces `sqrt q <= n - 1`.
- The extension `F_2(kappa + t) C_a / F_2(kappa + t)` has 2-power degree, which is
  prime to `p`. So whenever `2^(2^(a-1)) > E - 1`, some `t < q` works and `m_p < q`.
- Minimizing over `a` gives **`m_p < E(p)^4`** for every row.

This generalizes the paper's arm D bound (`prop:d-bound`). It depends on the level,
as the paper notes for D, so it does not prove absolute boundedness.

---

## 4. Analogous heuristics in the literature

The citations below are ones I am confident of. Exact search bounds are as I recall
them and should be rechecked against the papers before they are quoted in a
writeup.

- **Wieferich primes, `2^(p-1) = 1 mod p^2`.**
  - **[D] Same shape as a row.** By §1.1, `p` is Wieferich exactly when 2 is a
    `p`-th power in the cyclic group `(Z/p^2)^x`, whose order `p(p-1)` is divisible
    by `p` exactly once. The event is "a specified element lies in the index-`p`
    subgroup", probability `1/p` under a random model.
  - **[S] The heuristic.** The expected number of Wieferich primes in `[x, y]` is
    about `log(log y / log x)`: infinitely many, growing like `lnln`. See
    Crandall, Dilcher, Pomerance, *A search for Wieferich and Wilson primes*,
    Math. Comp. 66 (1997) 433–449.
  - **The data.** 1093 and 3511 are the only examples found up to `6.7e15` (Dorais,
    Klyve, *A Wieferich prime search up to 6.7×10^15*, J. Integer Seq. 14 (2011),
    Art. 11.9.2). The model expects about `ln(36.4/8.16) = 1.5` more in
    `(3511, 6.7e15]`, so finding none has probability about 0.22.
  - **What is proved.** Infinitude is open. The complementary statement, infinitely
    many non-Wieferich primes, is known only under abc (Silverman, *Wieferich's
    criterion and the abc-conjecture*, J. Number Theory 30 (1988) 226–237). This is
    the exact template for §5.
- **Base-`a` Wieferich primes, `q_p(a) = 0` [S].** The same `1/p` model applies,
  with sporadic solutions found by search (Montgomery, *New solutions of
  a^(p-1) = 1 (mod p^2)*, Math. Comp. 61 (1993) 361–363).
- **Wilson primes, `(p-1)! = -1 mod p^2` [S].** The heuristic is again `lnln`.
  Known examples are 5, 13 and 563 (Crandall–Dilcher–Pomerance 1997; Costa,
  Gerbicz, Harvey, *A search for Wilson primes*, Math. Comp. 83 (2014) 3071–3091).
- **Wall–Sun–Sun primes, `p^2 | F_(p - (p/5))` [S].** None are known, and the
  heuristic predicts infinitely many (Wall, *Fibonacci series modulo m*, Amer.
  Math. Monthly 67 (1960) 525–532; Sun & Sun, *Fibonacci numbers and Fermat's last
  theorem*, Acta Arith. 60 (1992) 371–388; McIntosh & Roettger, *A search for
  Fibonacci–Wieferich and Wolstenholme primes*, Math. Comp. 76 (2007) 2087–2094).
  - This is the closest psychological analogue: a `lnln`-divergent model with zero
    observed events. It shows that "no counterexample in a large search" is not
    evidence against a `lnln` model.
- **Wolstenholme primes, `binom(2p-1, p-1) = 1 mod p^4` [S].** The probability is
  `1/p`, the count is `lnln`, and 16843 and 2124679 are known (McIntosh, *On the
  converse of Wolstenholme's theorem*, Acta Arith. 71 (1995) 381–389;
  McIntosh–Roettger 2007).
- **Artin's primitive-root conjecture [S]** (Hooley, *On Artin's conjecture*, J. reine
  angew. Math. 225 (1967) 209–220, under GRH; Heath-Brown, *Artin's conjecture for
  primitive roots*, Quart. J. Math. Oxford (2) 37 (1986) 27–38, unconditionally for
  one of three bases).
  - This is the success direction, full order of a marked element. The rule is a
    primitivity statement for `X_c` in the row part of each cell.
  - In Artin's setting the local failure probabilities sum to a convergent product,
    which gives a positive density of successes.
  - Here the cell success probabilities are `prod_(p in P_c)(1 - 1/p)`, and their
    product over all cells is `prod_p (1 - 1/p) = 0`. Hence "almost every row
    passes" holds but "every row passes" does not. Heath-Brown's theorem is the
    model of a nonconstructive result, and it lives in the success direction.
- **Wiedemann's question [S as stated, H as modeled]** (Wiedemann, Fibonacci Quart.
  26 (1988); Voloch 2010).
  - Primes dividing `F_n` satisfy `p = 1 mod 2^(n+2)`. The mass of the cells is
    `sum_n O(2^(-n)/n) < infinity`, so the random model predicts that
    `ord(x_n) = F_n` holds for all `n` with probability about `1 - 1e-7`, given the
    complete checks through `F_11` and the published-factor checks from `F_12`
    upward. If the `F_18` factor 13631489 is untested in Wiedemann's tower, it alone
    carries `7e-8`.
  - The arms ZF, C and D have exactly this convergent shape. Arms O and Z do not.
- **Mersenne divisor heuristics [S]** (Wagstaff, *Divisors of Mersenne numbers*,
  Math. Comp. 40 (1983) 385–397). This is the source of the per-conductor mass
  heuristic used in §2.3: prime divisors of `Phi_h(2)` behave like primes `= 1 mod h`
  weighted by `phi(h)/(p-1)`.

---

## 5. Toward a nonconstructive proof

### 5.1 What is provable now [D]

The implication "model, therefore infinitely many failures" is a theorem (§3.1). It
is formalizable from Mathlib's Borel–Cantelli lemmas, and the sibling Lean file is
doing so. It is a theorem *about the model*, not about the Conway tower.

### 5.2 An unconditional result in the success direction [D]

**Cell-success lemma.** Let `c` be a cell whose row part
`G'_c = prod_(p in P_c) Z/p^(v_p)` is squarefree, and whose coordinate is nontrivial
in `G'_c`. Then some row of `c` obeys the rule.

- *Proof.* If every row fails, then `X_c in p G'_c` for every `p`. So
  `X_c in (prod p) G'_c = 0`, a contradiction.

**Application to arm O.**

- The coordinate is nontrivial in `G'` (§1.4).
- `v_p(L_(r,a)) = w_p` (§1.1), so `L'_(r,a)` is squarefree exactly when the cell
  contains no base-2 Wieferich prime.
- **So every O cell free of Wieferich primes contains a row with `m_p = 1`.**
- There are infinitely many O cells, one for each `(r, a)` with `r >= 5`, and the
  cells are disjoint. Each Wieferich prime lies in exactly one cell. Therefore:

  > If only finitely many base-2 Wieferich primes lie in O cells (in particular, if
  > there are finitely many base-2 Wieferich primes), the 0/1/4 rule holds for
  > infinitely many primes.

- Both known Wieferich primes lie in Z cells [N]. So every O cell contains a passing
  row, unless `p^2 | L'_(r,a)` for some (necessarily Wieferich) prime
  `p > 6.7e15`.
- Arm ZF behaves the same way: `p^2 | F_n` makes `p` a Wieferich prime (excess.tex),
  and `delta_n > 1`.
- With the proven packing bound `log_2 ord(y) >= (log_2 3)(1 - 1/r) sqrt(r^a) - O(1)`
  in place of nontriviality, a passing row exists unless the Wieferich part of
  `L'_(r,a)` exceeds about `3^sqrt(r^a)`.
- This lemma is my own and should be checked against excess.tex's least-counterexample
  analysis (`prop:o-ratio-packing` and its corollary), which isolates the same
  Wieferich boundary.

This is the exact analogue of Silverman's theorem (abc implies infinitely many
non-Wieferich primes), with "finitely many Wieferich primes in O cells" in place of
abc.

### 5.3 Why the failure direction is harder

- **The problem is open even in the analogues [S/H].** A nonconstructive proof that
  some row fails would show that some selected phase hits `1` without finding it.
  Every analogue in §4 with a `lnln` count (Wieferich, Wilson, Wall–Sun–Sun,
  Wolstenholme) has the same shape, "a marked residue vanishes for infinitely many
  `p`", and in each case infinitude is open. No nonconstructive technique is known
  for it.
  - Heath-Brown-type nonconstructive results exist only in the success direction,
    where sieve lower bounds for "large order" can be leveraged.
- **The possible routes, and what each needs [H].** I am not filing this as
  impossible; this is what an argument would need.
  1. **A forcing identity at some row.** This would be an algebraic relation making
     `X_c` a `p`-th power, like the forced translates but at the rule value. The
     reciprocity-saturation and norm-fibre results show that homogeneous
     multiplicative identities cannot do it. A forcing identity would have to be
     non-homogeneous, an ancestry identity "with independent arithmetic content" in
     the paper's words. If one existed it would be a structure theorem, and it would
     probably *construct* the counterexample row, not just prove it exists.
  2. **An averaging argument.** This would need a family over which the selected
     phase varies and equidistributes. Canonicity (SPEC §2) removes root-choice
     families. Translate families are equidistributed only for long lines (§3.6),
     which is the wrong regime. "Twisted towers" (other admissible radicands) would
     give averages, but the literal tower is one member, and an average says nothing
     about one member.
  3. **A pigeonhole on orders.** The rule is a set of lower bounds on orders
     (primitivity in the row part). No upper bound on `ord(X_c)` is known that could
     contradict them, and the model predicts none exists.
- **The realistic route is search.** The model gives about 28% below `1e4` and 52%
  below `1e6` (§3.3). A hit would come with an exact certificate (SPEC §6.5).

---

## 6. Proposed conjecture statements for the project

These are drafts for `docs/OPEN.md` §2 and `excess.tex`. The tags show the level each
statement can honestly carry.

1. **Heuristic conjecture: the rule has infinitely many exceptions [H].**
   - The 0/1/4 rule fails for infinitely many odd primes `p`.
   - Moreover, `#{p <= X : m_p != rule(p)} ~ lnln X`.
   - All but finitely many exceptions are in arm Z, where they have `m_p = 1`.
   - *Status:* a theorem in the uniform cell model (§3.1). It is supported by
     analogy with the Wieferich-type heuristics (§4). It is not supported by data,
     since the observed rows have likelihood 0.42 to 0.49 under the model.
2. **Conjecture B: one above the rule [H, strong].** For every odd prime `p`,
   `rule(p) <= m_p <= rule(p) + 1`.
   - The lower bound is a theorem in arms O, C and D and trivial in Z.
   - Model probability `1 - 1.8e-4`, given the data through 727.
3. **Conjecture B': sup is 4 [H, strong].** `m_p <= 4` for every odd prime `p`. This
   is Lenstra's boundedness with the bound 4.
   - Model probability `1 - 7.8e-5`. Under the model the only route above 4 is a
     failure in arm D (`m_p = 5`).
   - It is robust: boundedness alone needs only `P(two translates fail) = O(p^(-1-eps))`.
4. **Conjecture: the convergent arms hold universally [H].** Arms C (every `k`),
   D (every `k`) and the Conway–Fermat arm (`delta_n = F_n` for every `n`) hold for
   every `p`.
   - Model probability about `1 - 1.4e-4` in total. This is the same epistemic
     status as Wiedemann's question.
5. **Arm O: no conjecture [H].** The model puts even odds (about 0.54) on "arm O
   never fails". It should be stated as an open question, not as a conjecture
   either way.
6. **Unconditional (to be added as a proposition after review) [D].** If only
   finitely many base-2 Wieferich primes divide some `L'_(r,a)`, then
   `m_p = rule(p)` for infinitely many `p`. Every O cell that does not contain such
   a prime contains a passing row.

**Suggested reframing.**

- Present the 0/1/4 rule as the *generic* value of the excess: it holds for all but
  `O(lnln X)` primes up to `X` under the model, and for every observed row.
- Do not present it as a universal conjecture.
- Keep Z, O, C and D as named selected-order targets. Mark Z as "expected to fail
  infinitely often" and O as "undecided".

---

## 7. How the project could falsify the model

1. **Calibrate on phases that are not rows.**
   - For cheap rows (`E <= 1e5`), compute the Euler phases of the same selected
     non-forced elements (`kappa_h + 1` in arm Z, `kappa_h + 2` in arm O) at small
     primes `l | 2^E - 1`. Also use `l` with `f(l) | E`, `f(l) < h`, where the phase
     is not forced by a known identity.
   - The model predicts the frequency of a trivial phase is `1/l`. With
     `l = 3, 5, 7` over about 1000 rows, the model predicts about 333 ± 15 trivial
     phases at `l = 3`.
   - This test has real statistical power, unlike the rows themselves (total mass
     about 0.7 through 727). A clean departure would show hidden structure in
     selected elements, and it would tell us where.
2. **Use second translates.** Whenever the engine certifies a row, it should also
   record whether `kappa + rule + 1` is a `p`-th power. That event has probability
   `1/p` and nothing has been proved about it. It doubles the information per row.
3. **Track the O share.** Extending the census beyond `1e8` (cost: 3 minutes at
   `1e8` with `census_fast.py`) checks the `~ sigma_{-1}(b_r)/ln x` decay on which
   the arm O / arm Z split rests.

## 8. Files

The scratch directory is
`/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/b7db691f-f4bd-47a5-89a6-06b1f9fbbfc3/scratchpad/search/heuristic/`.
Nothing under `/Users/a9lim/Work/ogdoad` was modified.

| file | contents |
| --- | --- |
| `census_fast.py` | numpy arm census |
| `census_{1000000,10000000,100000000}.npz` | census arrays `p, h, arm, r, a, nq` |
| `recip_sum.py` | exact prime reciprocal sums |
| `model_calc.py` | the model computations |
| `model_calc_1e8.out` | full output of `model_calc.py` |
| `struct_check.py` | per-conductor calibration and `sigma_{-1}(b_r)` growth |
| `small_cells.py` | small O cells, `b_r` parity, Wieferich cells |
