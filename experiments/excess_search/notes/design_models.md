# Models, flattening, reuse and scheduling (designer angle 4)

Labels: **[checked]** means run here, with the artifact named. **[derived]** means a mathematical argument that was not executed. **[estimate]** means an extrapolated cost that was not measured end to end.
All paths are relative to `scratchpad/search/design/`.
Per the lead's instruction, no batch row jobs were run. The only rows tested were the known ones (p <= 727) used for validation.

## 0. Headlines

1. **Flat models are cheap; the Euler test is the cost.** A *dual (power-projection) calculus* builds the exact F_2 minimal polynomial P of `alpha_p = kappa_h + m` directly from the term algebra, with no K-level polynomial arithmetic and no root finding.
   - Timings on jobe, 1 core [checked]:

     | p | E | deg K | time | memory |
     | --- | --- | --- | --- | --- |
     | 967 | 1.06e5 | 4 | 0.02 s | 14 MB |
     | 4973 | 5.2e5 | 4 | 0.25 s | 45 MB |
     | 4391 | 5.77e6 | 4 | 2.6 s | 0.75 GB |
     | 9343 | 5.62e6 | 12 | 12.5 s | 2.1 GB |
     | 4463 | 5.89e6 | 16 | 20 s | 2.9 GB |

   - A dense Euler test at E = 5.8e6 costs about E x SqrMod, roughly 60 core-hours [estimate]. Model construction is therefore below 0.01% of the per-row cost at every size.
2. **Validation.**
   - All 106 known rows with E <= 30000 among p <= 727 (727 included) reproduce A380496 exactly. That includes the structural `alpha_p + 1` p-th-power check for every m = 1 row and the arm-D rows 19 and 163 [checked, `proto/validate_dual_out.txt`].
   - For E <= 6000 (96 rows), P equals the minimal polynomial computed by an independent oracle: the literal term algebra in its monomial basis (numpy), followed by Berlekamp–Massey (BM) over F_2.
   - For 6000 < E <= 30000 (10 rows), P equals Norm_{K/F_2} of the K-relative minimal polynomial from a second, independently coded builder (NTL GF2EX composed sums) [checked].
   - Further agreement:
     - The second builder reproduces the same 106 rows, apart from two harness bugs in the arm-D comparison, which were diagnosed and re-checked [checked, `proto/validate_out.txt`].
     - On jobe at E = 1.06e5 and 5.2e5 the two builders agree bit for bit (md5) [checked].
3. **Phase-correctness is enforced and tested.** Shared components are pinned by working over a base field `K = F(C')`, where C' is the union of every pairwise branch-closure intersection at every sum node, plus all 2-power components.
   - Negative control: Frobenius-twisting one branch's K-constant changes P in 9 of 9 rows tried [checked, `proto/negctl.py`]. The builder is phase-sensitive, as it must be.
4. **Conversion maps tower -> flat** use Shoup's trace-dual formula. Two exact checks pass on p = 743 and p = 61 [checked, `proto/dual_img.cpp`]:
   - the image ζ of K's generator satisfies `P_K(ζ) = 0`;
   - the image of the branch element θ_A satisfies `θ_A^7 = z_rel(ζ)`.

   These maps give a certificate that needs no irreducibility test (section 3) [derived].
5. **Reuse: the tested element depends only on `(Q(h), m)`.** Rows sharing it test the same β with one grouped exponentiation [derived; implemented in `proto/batch.cpp`, smoke-tested only].

   | p range, E filter | rows | elements |
   | --- | --- | --- |
   | p <= 1e6, all E | 78,369 | 48,502 |
   | p <= 1e6, E <= 1e6 | 6,492 | 2,398 |
   | p <= 1e5, E <= 1e5 | 1,392 | 607 |

6. **Hardware.** gf2x 1.3.0 built from source on jobe with PCLMUL (`-march=native`) is 5–18x faster per core than the M5 with conda's gf2x, which has no aarch64 PMULL kernel [checked, `bench/b2_{jobe,local}.txt`]. The build is at `jobe:/tmp/xb/inst`: static NTL 11.5.1 on gf2x, without GMP.
   - Full products: 37 ms vs 653 ms at 1e7 bits.
   - Dense MulMod: 10 ms vs 55 ms at 1e6.
   - On the M5, a PMULL schoolbook base case beats conda gf2x by 2–7x at 1–64 words [checked, `bench/pmull.c`]. Porting it into gf2x is the main local speedup available [estimate for the full-size gain].
7. **Schedule (flat-model engine, measured primitives, jobe core-hours)** [estimate, `schedule.py`, `schedule_out.txt`]:

   | P(hit) | cost |
   | --- | --- |
   | 0.20 | 0.3 core-h |
   | 0.25 | about 8 core-h |
   | 0.28 | about 300 core-h (all E <= 1e6, p <= 1e6) |
   | 0.32 | about 3,000 core-h (E <= 3e6) |
   | 0.35 | about 12,000 core-h |

   Beyond E of about 3e6 a flat model is the wrong place to run the Euler test. Tower or crossing engines from the other designs must take over. This design supplies the models, maps and certificates they consume.

## 1. Planner: from the term algebra to a build recipe

Code: `proto/terms.py` (structure), `proto/plan.py` (planner).

- `S = cl(alpha_p)` is the downward closure of components. deg S = prod prime(q) = E for every row p <= 1e5 (9,591 rows, 0 mismatches) [checked, `closure.py`].
- **Shared base.** At every sum node (`alpha_r = sum_{q in Q} chi_q + m_r`), take the pairwise intersections of the branch closures. Their union over all sum nodes in S, plus every 2-power component of S, is C'. Set `K = F(C')`, with generator θ_K equal to the sum of the maximal elements of C'. Its minimal polynomial P_K comes from linear algebra in the small tower, with a rank check that θ_K generates.
- **Size of the shared base.** Measured over rows 727 < p <= 1e5 before the 2-power completion, by sum 1/p mass [checked, `cglob.py`]:

  | deg | 1 | 2 | 4 | 6 | 12 | 20 | other |
  | --- | --- | --- | --- | --- | --- | --- | --- |
  | mass | 0.045 | 0.203 | 0.152 | 0.062 | 0.051 | 0.026 | <= 0.003 each |

  The maximum is 15,180 (one row) and there are 23 distinct bases in total.
- **Plan ops**, each producing a register θ with an exact relation over K:
  - `BINOM r z`: θ^r = z, with z in K.
  - `LIN v`: θ = v in K.
  - `SPREAD x r`: θ^r = x (Kummer chain step).
  - `SHIFT x c`: θ = x + c, with c in K. This covers both `+1` steps and K-constant parts of radicands.
  - `SUM a b`: θ = a + b.
- `Mod(q)` builds chi_q and `Rad(r)` builds alpha_r recursively, memoised per row. Components inside C' become K-constants.
- Example for p = 4391 (E = 5.77e6):

  ```
  K = F_16
  0 BINOM 5 z
  1 BINOM 3 z'
  2 SPREAD 1 3; 3 SHIFT 2 1
  4 SPREAD 3 73; 5 SHIFT 4 1
  6 SPREAD 5 439
  7 SUM 0 6
  ```
- **Coprimality invariant [derived].** Outside C', two branches never both contain a component of the same prime. Components of prime ℓ form a chain ℓ, ℓ², …, and any two branches containing ℓ-components share chi_ℓ, …, chi_{ℓ^min}, which then lie in C'. All 2-power components are in C'. The K-relative degrees of the two `SUM` operands are therefore coprime, so `K(a) ⊗_K K(b)` is a field and the composed sum is legitimate. The production planner must assert this. If the invariant were violated, `deg P = E` would *not* catch it, because a tensor product of non-coprime extensions is a product of fields and BM can still return a reducible polynomial of full degree.

## 2. Builders (three implemented, one recommended)

### 2.1 Free compositions: primal, sparse, free

- `P(X^R)` is a bit spread.
- `P(X+1)` is the Taylor shift by 1 over F_2, a word-level subset-sum transform: 1.0–1.2 ms at 1e7 bits [checked, `bench/b2`, verified against Horner composition].
- `P(X^2+X)` handles Artin–Schreier layers.
- Pure chains need no build. Up to 1e4, 49 rows have a modulus `P_alpha_s(X^q)` with 3–59 terms [checked, `proto/weights.py`]. Examples: 727 has weight 5; 1013 and 1069 have weight 55.
- A sparse modulus makes SqrMod 50–1000x cheaper than dense [checked, `bench/b2`]. Use these models directly for the Euler test.

### 2.2 Composed sums in characteristic 2

The Newton / power-sum composed sum breaks in characteristic 2: it divides by k, and even power sums are squares of the half-index ones. The char-2-safe identity is Lucas: `(x+y)^i = sum_{j ⊆ i} x^j y^{i\j}` (bitwise subset). So `L(θ_a+θ_b)^i = sum_{j ⊆ i} ℓ_a(θ_a^j) ℓ_b(θ_b^{i\j})` for `L = ℓ_a ⊗ ℓ_b` is a **subset convolution** of the two impulse sequences. It takes O(k² N) time with ranked zeta transforms, where N = 2^k >= 2E.

| method | what | measured |
| --- | --- | --- |
| (a) K-level BM | impulse sequences over K, subset convolution, NTL `GF2EX MinPolySeq` | quadratic: 0.5 s at D = 1e4, 51 s at D = 1e5 (jobe) [checked]; **reject** |
| (b) F_2 route + K-gcd (`proto/sum2.h`, `exec.cpp`) | trace to F_2, BM over F_2 (half-gcd), recover `G = gcd_K(P(W), ζ(W) - z)` | jobe: 1.2 s (E = 1.06e5), 7.2 s (5.2e5), 64–181 s (5.8e6), dominated by the GF2EX gcd [checked]; equals method (a) on 11 rows [checked] |
| **(c) dual calculus** (`proto/dual.cpp`) | keep every register as its functional sequence (bit-sliced K-planes); only the final sequence is traced and run through F_2 BM | 0.02 s / 0.25 s / 2.6–20 s at the sizes above [checked] |

Only (b) yields the K-relative minimal polynomial G. Use it when an Euler engine wants to work over K.

**Dual-calculus op table [derived; every row validated by section 0.2].** Each register carries `a_i = ℓ(θ^i)` for a nonzero K-linear functional ℓ:

| op | sequence update |
| --- | --- |
| `BINOM r z` | `a_i = z^{i/r}` if r divides i, else 0 (ℓ = coefficient of θ^0) |
| `SPREAD r` | `a'_i = a_{i/r}` if r divides i, else 0 |
| `SHIFT c` | `a'_i = c^i · ζ(c^{-j} a_j)_i` (subset-sum transform). For c = 1 this is just the transform. |
| `SUM` | ranked subset convolution with bit-sliced K-multiply |

At the end, `σ_i = Tr_{K/F_2}(λ s_i)`, `P = BM_{F_2}(σ_0..σ_{2E-1})`, and the builder refuses unless `deg P = E`.

- **Exactness [derived]:**
  - The register tree builds a field (coprimality), so `minpoly_{F_2}(θ)` is irreducible.
  - The F_2 sequence's recurrence divides it.
  - `deg P = E` means θ generates F and P is exactly its minimal polynomial.
  - Nothing is probabilistic, and failure is a hard error, never a skip.
- **Cost [derived, matches measurements]:**
  - Time is about `(k+1)(k+2)/2 · d² · N/64` word ANDs per sum.
  - Memory is about `3(k+1) · d · N` bits.
  - At E = 1e8, d = 4: N = 2^28 and roughly 40 GB [estimate]. That fits the Mac (128 GB) but not jobe (61 GB) without streaming the high-bit transform stages in blocks. A block-streamed ranked transform is the main engineering item if models beyond E of about 5e7 are wanted.

### 2.3 Alternative: root-finding into one fixed sparse model [derived / estimate]

- **Idea.** Choose a sparse irreducible P0 of degree E. Embed the components one at a time in dependency order: Kummer roots by generalised Tonelli–Shanks (Adleman–Manders–Miller) with an exact `y^ℓ = a` check, Artin–Schreier roots via ω with ω² + ω + 1 = 0, and so on.
- **Why it is valid.** By canonicity, any root extends the embedding. One model holds everything, so phases are automatically consistent.
- **Payoff.** On jobe at 1e7, SqrMod costs 1.4 ms with a pentanomial versus 75 ms dense (54x). An Euler test on P0 takes about 4 h instead of about 208 h dense.
- **Cost.** Each root is about one exponentiation: E·SqrMod_sparse + (E/20)·MulMod_sparse ≈ 9 h at E = 1e7. Finding P0 itself needs an irreducibility proof at degree E, which is hours more.
- **Net.** With c Kummer components, total ≈ 9c + 4 h. That beats a dense flat route for c <= 20 at E >= 1e7, but loses to tower engines with cheap Frobenius.
- **Recommendation.** Keep this as the fallback for large rows that must run flat and have few components. It is unneeded below E of about 3e6, where the dual builder plus a dense Euler test is simplest.

## 3. Conversion maps and certificates

- **Tower -> flat [derived; checked on 743 and 61].**
  - Inputs: P, a functional sequence `σ_i = ℓ(θ^i)`, and a "marked" sequence `τ_i = ℓ(u θ^i)`.
  - Formula: `u ≡ N_τ · N_σ^{-1} (mod P)`, where `N_x = (P · rev_E(x)) div X^E`. This is Shoup's power-projection duality.
  - Marked sequences come from the same calculus. For u = θ_leaf, shift the leaf's sequence by one, then push it through `SPREAD`, `SHIFT` and `SUM` with the same updates. This costs one extra pass per tracked leaf.
  - K elements map by Horner evaluation of their P_K-coordinates at ζ.
- **Flat -> tower.** The Euler test does not need this. Between two different flat models of the same field (dense P and sparse P0), a map needs a root of P in the other model, which is too expensive. Embed components directly instead (section 2.3).
- **Replayable certificate [derived].** It consists of:
  - P, ζ, and the image g_c of every component c;
  - the Euler phase of Y.

  The checker verifies, mod P:
  - every defining relation (`g_c^ℓ = rhs`, `g_{2^k}² + g_{2^k} = prod_{j<k} g_{2^j}`, `P_K(ζ) = 0`);
  - `Y = sum_{q ∈ Q} g_q + image(m)`;
  - the phase.

  Why this suffices: the presentation ideal I has F_2-dimension E (staircase monomial basis) and is maximal (Lenstra: the term algebra is a field). So `F_2[x]/I -> F_2[Y]/P` is an injective map from a field of dimension E into an E-dimensional ring, which makes it an isomorphism. That proves P irreducible and that Y is alpha_p, with **no Rabin test**.
  - Check cost is O(#components · log ℓ) MulMod(E): about 4 s at E = 1e6 with 20 components (jobe) [estimate].
  - The checker needs only GF2X MulMod, so python-flint or PARI can replay an NTL-produced certificate independently.

## 4. Caching and reuse

- **Element grouping [derived].**
  - kappa_h is the sum of chi_q over q in Q(h), so the element is determined by (Q, m).
  - Group Euler test: put `L = prod_{p in group} p` and `g = β^{(2^E-1)/L}`; then for each row, `t_p = g^{L/p}` is the exact Euler phase. L/p is an integer even when p² divides 2^E - 1.
  - The per-row extra cost is negligible.
  - Code: `batch.cpp`. Every t_p is also checked to be p-torsion.
- **What to cache.**
  - **(i)** For each closure node r: the F_2 minimal polynomial of alpha_r (b_r bits), its verified m_r, and its status. These feed `SPREAD` / free-chain reuse. Up to 1e6, 23,547 singleton-odd rows have only 12,576 distinct top nodes; the most shared node, r = 59, serves 28 rows [checked].
  - **(ii)** Per element: P and the component images, which form the certificate.
- **Not worth caching:** functional sequences of sub-registers. They depend on the row's base K: there are 2,949 distinct (node, C' ∩ cl(node)) pairs against 1,863 nodes up to 1e5. Rebuilding a model costs seconds.

## 5. Global schedule and parallelism

- **Unit and order.** The unit is an element, with mass = sum 1/p over its rows and cost = its Euler cost. Order by mass/cost, descending.
- **Dependencies.**
  - Up to 1e5 [checked]: 5,783 rows depend on no unverified closure row; the rest depend on 1, 2, 3 or 4 of them (3,071 / 556 / 48 / 5 rows). The maximum dependency depth is 5.
  - E(r) | E(p) for every dependency [checked, asserted]. Closure rows are therefore never more expensive and have more mass per row, so the greedy order already almost respects the DAG.
- **Speculative execution.**
  - Run rows assuming the rule holds for unverified closure rows, and store each result as conditional on D(p), its set of unverified closure rows.
  - A result is final once every row in D(p) is final.
  - On any conditional hit, promote D(p) to the front immediately. A certificate requires D(p) to be verified first.
  - If a closure row r fails, compute the true m_r, invalidate every row whose closure contains r, and rebuild with the corrected alpha_r. Degrees change only if m_r >= 2. Expected wasted work is about sum 1/r, which is small [derived].
- **Cost model** (`schedule.py`) uses measured jobe SqrMod, MulMod and CompMod times. It takes the cheaper of two routes:
  - brute force: E · SqrMod(E);
  - Frobenius norm: about `(2 log2 H + 3 log2(E/H) + 2)` CompMods, where `CompMod(1e6) ≈ 23 s` (jobe, baby-step count m = 1000), plus a small Euler test.
- **Simulated budget (whole range p <= 1e6, E <= 1e8, 1 jobe core) [estimate]:**

  | budget | elements | rows | P(hit) | core-h | max per element |
  | --- | --- | --- | --- | --- | --- |
  | E <= 1e5 | 830 | 2,349 | 0.193 | 1.0 | 0.01 h |
  | E <= 1e6 | 2,398 | 6,492 | 0.282 | 300 | 1.5 h |
  | E <= 3e6 | 3,691 | 9,565 | 0.316 | 3,000 | 15 h |
  | E <= 1e7 | 5,563 | 13,670 | 0.349 | 34,000 | 200 h |

  A Four-Russians CompMod would cut the large-E rows by 1.5–2x. The real lever beyond 3e6 is a tower engine with cheap Frobenius (the crossing trick), not flat arithmetic.
- **Parallelism.** Elements are embarrassingly parallel, one single-threaded job each. NTL GF2X products are not usefully threaded at these sizes.
- **Machine split.**
  - **Mac:** model building. It is bit-sliced, memory-heavy and needs no carry-less multiply, and the Mac has 128 GB. It also takes the small-E queue. Currently it shows load average 80 from other sessions, so its share is unknown.
  - **jobe:** every carry-less-multiply-heavy Euler test, at about 5–18x the Mac's per-core speed. Use nice 19 and cap memory per job. jobe is shared, with a partner pipeline and other users' processes (load 3–7 observed).
  - Transfer P as E/8 bytes (12.5 MB at 1e8).
  - Memory classes: E <= 1e6 needs <= 0.3 GB per job; E around 6e6 needs 0.75–2.9 GB for the build; Euler memory is O(E).
- **Wall clock [estimate].** With about 12 effective jobe threads plus Mac help, E <= 1e6 (P about 0.28) takes about a day of wall clock, and E <= 3e6 (P about 0.32) about 10 days.

## 6. Pitfalls found (all checked)

- K-relative arithmetic is slow:
  - NTL `GF2EX MinPolySeq` is quadratic.
  - A K-relative Euler test for 743 (D = 4823 over F_{2^12}) took **497 s** on the M5.
  - GF2EX MulMod is 4–6x slower than flat GF2X at equal bit size for small d.

  Always **flatten before the Euler test**.
- In arm D, kappa_h lies in a degree-E/2 subfield because chi_4 is outside it. Comparisons must use alpha_p itself (`plan.py --full`) or norms. This was the cause of the two "BAD" harness lines.
- `deg P = E` is necessary but **not sufficient**. The coprimality invariant (section 1) must be asserted by the planner.
- p = 719 (E = 1.26e9) cannot be reproduced on the flat route. It is a validation target for the crossing or tower engines only.

## 7. Files

- **Census structure:** `closure.py`, `stats*.py`, `cglob.py`, `e709.py`.
- **Prototype (`proto/`):**
  - `terms.py`, `tower.py` (numpy oracle and F_2 BM), `plan.py`
  - `dual.cpp` (recommended builder), `dual_img.cpp` (image maps)
  - `exec.cpp` + `sum2.h` (GF2EX builder, methods (a) and (b))
  - `batch.cpp` (grouped Euler; not run on rows)
  - `validate*.py` and their `*_out.txt` logs, `negctl.py`, `weights.py`
- **Benchmarks:** `bench/b2.cpp` (`b2_local.txt`, `b2_jobe.txt`), `bench/b3.cpp`, `bench/pmull.c`.
- **Schedule:** `schedule.py`, `schedule_out.txt`.
- **jobe:** `/tmp/xb/inst` holds the PCLMUL gf2x and NTL builds; `/tmp/xb/*.cpp` are benchmark sources.
