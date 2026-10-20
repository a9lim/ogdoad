# Arithmetic design: binary-field arithmetic for the 0/1/4 excess search

Angle: low-level arithmetic performance. Each claim is tagged **[checked]**
(I measured or verified it in this session), **[derived]** (follows from
checked facts by stated reasoning) or **[guessed]** (an estimate or a judgment
I have not tested).

All code and builds are under
`/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/b7db691f-f4bd-47a5-89a6-06b1f9fbbfc3/scratchpad/search/design/arith/`
(below, `arith/`). The jobe builds are in `/tmp/excess-bench/` on jobe. Nothing under the
repo was touched. None of my processes are still running on jobe or the M5.

## 0. Measurement conditions (read first)

* **The M5 was heavily loaded the whole time.** Other jobs (`blam`, `refengine`,
  `narrow`, several pythons) pushed the load average from 38 to 130 on 18 cores
  **[checked]**. M5 timings are therefore inflated and noisy: the same 1e6-bit
  `mul` took 18–27 ms at load 38 and 96 ms at load 120 **[checked]**. A ratio is
  trustworthy only when both runs happened back to back at the same load. Do not
  compare M5 absolute numbers with jobe.
* **jobe** (i9-12900K: PCLMULQDQ, VPCLMULQDQ, AVX2, GFNI, BMI2; 24 threads) ran at
  load about 3, so its numbers are clean **[checked]**. Every jobe run was a single
  thread and CPU only.
* Timings are best-of or mean over repeated calls, on one thread.

## 1. Headline findings

1. **The installed (conda) gf2x on arm64 does not use PMULL.** Configure picked
   `hwdir=generic64`, `GF2X_HAVE_PCLMUL_SUPPORT` is undefined, `gf2x_mul1` is the
   generated 3-bit table-lookup code, and the thresholds file reads
   `"placeholder"` with the stock FFT table (which its own comment calls "just
   plain crap") **[checked: `$ENV/include/gf2x/*.h`]**.
2. **Porting gf2x's x86 PCLMUL kernels to NEON `vmull_p64` gives 9–17x on
   small and medium products and more than 10x at 1e7 bits.** I wrote a
   12-intrinsic shim (`arith/gf2x-1.3.0/already_tuned/arm64_pmull/`) and
   configured with `hwdir=arm64_pmull`. All 45 tests in `make check` pass
   **[checked]**. Back-to-back curve at equal load (default `gf2x_mul`):
   * 1,024 bits: 7.7e-7 s (conda) vs 8.7e-8 s (PMULL);
   * 11,648 bits: 4.9e-5 vs 3.5e-6;
   * 132,800 bits: 2.25e-3 vs 1.33e-4 **[checked]**.

   At 1e7 bits, conda at load 38 took 1387 ms and PMULL at load 120 took 129 ms
   **[checked]**. With the gap in load, more than 10x is a lower bound.
3. **An additive FFT (bitpolymul2, Cantor/Gao–Mateer) beats gf2x's ternary FFT
   by 2.5–3.1x above about 2.6e5 bits on jobe.** I ported it to NEON with an
   AVX2→NEON shim; there it wins by 1.5–1.9x below 2^17 words and 2.3–4.9x above
   (noisy under load). Every size from 2^10 to 2^21 words matched gf2x bit for
   bit **[checked]**. Through a drop-in `gf2x_mul` wrapper it speeds up all of
   NTL. On jobe, NTL dense `MulMod` at 1e6 bits drops from 8.38 to 3.61 ms, and
   `PowerMod` by 359 over F_2^179 at degree 19,580 drops from 1.62 to 0.43 s
   **[checked]**.
4. **A custom PMULL/PCLMUL squaring kernel for a sparse modulus is 2.5–3x faster
   than NTL `SqrMod` on the same pentanomial.** It spreads bits with a carry-less
   self-multiply and reduces with two word-level folds. On jobe it takes
   0.050 ms at 1e6 bits, 0.57 ms at 1e7 and 8.5 ms at 1e8; NTL takes 0.133,
   1.42 and 25.3 ms. It is bit-exact against NTL after 1 and 5 iterated
   squarings at every size from 1e3 to 1e8, on both machines **[checked]**. At
   1e6 bits a sparse squaring costs 1/57 of a sparse `MulMod` and 1/110 of a
   dense `SqrMod` **[checked]**.
5. **Structured-Frobenius Euler test (norm, then a small exponent) in a Kummer
   field: 0.03–0.06 s at the p=719 crossing size (degree 64,261), against 69–72 s
   for the reference `PowerMod`.** That is about 1,500x on the same M5. The two
   agree on every trial: 2/2 at degree 64,261, and 30 trials each for 10 primes
   in F_2^110 **[checked]**. At the p=4507 size (degree 1,126,500) it takes
   6.3 s on jobe **[checked]**. A flat sparse model of the same degree costs at
   least E squarings, about 63 s **[derived]**.
6. **Composing the Frobenius (Brent–Kung `CompMod`) is never worth it with a
   sparse modulus at these sizes.** With a dense modulus it wins for every large
   Frobenius step. See §4 **[checked numbers, derived break-evens]**.
7. **Other libraries are not competitive for this workload:**
   * FLINT `nmod_poly` mod 2 is not bit-packed: 1.1 s at 1e7 bits, against 38 ms for gf2x on jobe **[checked]**.
   * python-flint `fq_default_poly` over F_2^179 is 4–9x slower than NTL `GF2EX` **[checked]**.
   * PARI `F2xqX` is 15x slower on `mul` and has a usable `polresultant` (5.0 s at n=2000) **[checked]**.
   * NTL `GF2EX` has no resultant and no `NormMod` (grep of the header) **[checked]**.

## 2. Measured tables

### 2.1 GF2X on jobe (NTL 11.6 built without GMP on tuned PCLMUL gf2x; "bpm" = same NTL with bitpolymul2 behind `gf2x_mul`)

Times in ms, single thread. "Sparse" means the pentanomial x^E+x^7+x^3+x^2+1.
The custom squaring is `arith/bench/sqrk.h`.

| E bits | mul gf2x / bpm | SqrMod sparse (NTL) | **custom sparse sqr** | MulMod sparse gf2x / bpm | MulMod dense gf2x / bpm | SqrMod dense gf2x / bpm | CompMod dense gf2x / bpm |
|---|---|---|---|---|---|---|---|
| 1e3 | 0.0001 | 0.00019 | 0.00010 | 0.0003 | 0.0002 | 0.0002 | 0.02 |
| 1e4 | 0.0024 | 0.00167 | 0.00061 | 0.0040 | 0.0073 | 0.0049 | 1.58 |
| 1e5 | 0.076 / 0.081 | 0.0163 | 0.0052 | 0.091 / 0.096 | 0.225 / 0.240 | 0.151 / 0.161 | 158 / 165 |
| 3e5 | 0.71 / 0.54 | 0.049 | 0.0159 | 0.79 / 0.59 | 2.17 / 1.65 | 1.46 / 1.08 | 2492 / 1918 |
| 1e6 | 2.77 / **1.15** | 0.133 | **0.050** | 2.87 / 1.34 | 8.38 / **3.61** | 5.66 / 2.40 | 19733 / 9737 |
| 3e6 | 9.7 / 4.8 | 0.41 | 0.160 | 10.2 / 5.4 | 29.8 / 14.3 | 20.5 / 9.9 | – |
| 1e7 | 37.6 / 23.6 | 1.42 | **0.572** | 38.6 / 26.3 | 110 / 78 | 74 / 50 | – |
| 3e7 | 114 / 54 | 4.39 | 1.76 | 120 / 60 | – | – | – |
| 1e8 | 452 / 261 | 25.3 | **8.5** | – | – | – | – |
**[checked]**

### 2.2 Raw product: gf2x vs bitpolymul2, power-of-two word counts (seconds)

| words | bits | jobe gf2x | jobe bitpolymul64 | M5 PMULL gf2x (my FFT table) | M5 NEON bitpolymul64 |
|---|---|---|---|---|---|
| 2^12 | 2.6e5 | 0.0005 | 0.0002 | 0.0005 | 0.0003 |
| 2^14 | 1.05e6 | 0.0027 | 0.0009 | 0.0022 | 0.0012 |
| 2^16 | 4.2e6 | 0.0120 | 0.0043 | 0.0092 | 0.0057 |
| 2^18 | 1.7e7 | 0.0633 | 0.0225 | 0.307 | 0.135 |
| 2^20 | 6.7e7 | 0.308 | 0.112 | 1.47 | 0.46 |
| 2^21 | 1.3e8 | 0.663 | 0.249 | 4.19 | 1.06 |
**[checked; M5 column at load 112–121]**

* Up to about 4e6 bits, the M5 with the PMULL port matched or beat jobe
  per core, even under load.
* Above that it was 4–6x slower. I attribute this to memory-bandwidth contention
  from the load **[guessed]**. Unloaded large-size M5 performance is unmeasured.
* bitpolymul pads to a power of two, so at awkward sizes the NTL-level gain
  falls to about 1.4–1.7x (1e7 and 1e8 in §2.1) **[checked]**. A non-power-of-two
  truncated additive FFT would recover it **[guessed]**.

### 2.3 M5 NTL stacks, back to back at load 120–130 (ms; conda / PMULL gf2x / PMULL gf2x + NEON bitpolymul)

| E | mul | custom sparse sqr | MulMod dense |
|---|---|---|---|
| 1e4 | 0.249 / 0.0178 / 0.026 | 0.0039 / 0.0038 / 0.0022 | 0.976 / 0.050 / 0.062 |
| 1e5 | 8.07 / 0.68 / 0.44 | 0.044 / 0.033 / 0.026 | 27.5 / 1.48 / 2.19 |
| 1e6 | 96 / 12.8 / 8.0 | 0.30 / 0.26 / 0.32 | 358 / 34 / 21 |
| 1e7 | 3933 / 129 / 177 | 3.8 / 3.5 / 2.6 | 12090 / 480 / 557 |
| 1e8 | 108500 / 3143 / 1680 | 34 / 35 / 22 | – |
**[checked]**

The squaring kernel does not depend on gf2x, so its three columns differ only
by noise. Under a lighter load (38), the conda run gave a custom squaring time
of 0.057 ms at 1e6, 1.0 ms at 1e7 and 8.1 ms at 1e8 **[checked]**. That is close to
jobe.

### 2.4 Polynomials over F_2^179 (the p=359/719 coefficient field), seconds

| | n=2000: mul | mulmod | PowerMod e=359 | GCD | CompMod | n=19580: mul | mulmod | PowerMod 359 | GCD |
|---|---|---|---|---|---|---|---|---|---|
| jobe NTL GF2EX | 0.0019 | 0.0057 | 0.060 | 0.046 | 0.534 | 0.050 | 0.152 | 1.62 | 0.91 |
| jobe NTL + bpm | 0.0012 | 0.0037 | 0.040 | 0.047 | 0.389 | **0.016** | **0.039** | **0.43** | 0.81 |
| M5 NTL conda | 0.0146 | 0.0445 | 0.80 | 0.35 | 8.04 | 1.09 | 3.57 | 38.9 | 13.3 |
| M5 python-flint fq_default_poly | 0.061 | 0.255 | 3.33 | 3.22 | – | 0.60 | 2.73 | 39.3 | 73.4 |
| M5 PARI F2xqX | 0.224 | 0.985 | – | 4.92 (resultant 5.02) | – | – | – | – | – |
**[checked]**

NTL `ProbMinPolyMod` over F_2^179 on the M5 with the conda build took:

| n | 250 | 500 | 1000 | 2000 | 4000 |
|---|---|---|---|---|---|
| seconds | 0.18 | 1.57 | 7.6 | 31.3 | 136 |
**[checked]**

That fits about n^2.1. Extrapolated to n=19,580 (the f_a of the crossing
trick), it is about 3,300 s with the conda build. jobe's `mulmod` is about 23x
faster at that size, so on jobe with bpm it is roughly 2–3 minutes
**[derived/extrapolated]**.

### 2.5 Sparse irreducible search (NTL `BuildSparseIrred`, M5 conda)

| n | 1000 | 3660 | 10007 | 30000 |
|---|---|---|---|---|
| seconds | 0.000 | 0.023 | 9.2 | 1380 |
| result | x^1000+x^5+x^4+x^3+1 | x^3660+x^61+1 | x^10007+x^2891+1 | x^30000+x^57+x^39+x^27+1 |
**[checked]**

NTL's search does not scale to the E values here. §5 gives the replacement.

## 3. The Euler test x^((2^E-1)/p): optimal algorithm

Let β be in a field L with [L:F_2] = D. Let p | 2^D−1, h = ord_p(2), and h | D.
β is a p-th power iff β^((2^D−1)/p) = 1.

**Step 1: norm down (Itoh–Tsujii).**
γ = N_{L/F_{2^h}}(β) = β^((2^D−1)/(2^h−1)) = Π_{j<n} σ^{hj}(β), with n = D/h.
The addition chain on the bits of n costs ⌊log₂ n⌋ + popcount(n) − 1
multiplications and as many Frobenius maps σ^{h·k}. Their total Frobenius
"degree" is D − h **[standard: Itoh–Tsujii]**. For n=179 that is 11 mults and
11 Frobenius maps **[checked in kummer.cpp counters]**. Then
β^((2^D−1)/p) = γ^u with u = (2^h−1)/p **[standard; SPEC §3]**.

**Step 2: small exponent.** u has about h − log₂ p bits. Use left-to-right
sliding windows. Squarings cost far less than multiplications in every model
here: 1/57 in the sparse flat model, nearly free in a Kummer tower. So the cost
is h·S + (h/(w+1) + 2^{w−1})·M, and the optimum is w ≈ 6–8 for h of 10^3–10^4
**[derived]**. For h=359, w=5 used 72 multiplications **[checked]**.

**Step 3 (composite h only): cyclotomic reduction.** Since ord_p(2) = h,
p | Φ_h(2). Let P^± = Π_{d|h, μ(h/d)=±1} (2^d − 1), so that Φ_h(2) = P^+/P^−.
Then (γ^{P^−})^{Φ_h(2)/p} = (γ^u)^m, with m = Π_{μ(h/d)=+1, d<h} (2^d−1).
No factor of m is divisible by p, because ord_p(2) = h > d. So the test
"(γ^{P^−})^{Φ_h(2)/p} = 1" is exactly equivalent to "γ^u = 1" **[derived;
empirically consistent in every trial: 10 primes × 30 trials in F_2^110, plus 3
trials at degree 64,261, all `consistent=1`]**.

γ^{P^−} is a few Itoh–Tsujii chains x ↦ x^(2^d−1), costing about 2 log₂ d
mults each when Frobenius is cheap. The remaining exponent has about φ(h)
bits instead of h. So multiplications fall by a factor of about h/φ(h): 3x
for h = 2·3·751. There is no gain for prime h: at h=359 both exponents are
350 bits **[checked]**. Squaring counts do not drop: Σ_{μ=−1} d + φ(h) ≈ h.
The step helps only when multiplications dominate, which is the tower model.

**Cost in the flat sparse model** F_2[x]/(pentanomial of degree E). Direct
exponentiation costs E·S + (E/w)·M. Norm-then-small-exponent costs
(E−h)·S + (log n + h/w)·M + h·S. At E=1e6 and h=1e3 on jobe that is
50 s + 478 s against 50 s + 0.2 s **[derived from §2.1]**. **The norm trick
removes essentially all multiplications, so the flat model's floor is E
sparse squarings.** Applied to the census (one squaring chain per row, jobe
per-core times):

| slice | rows | Σ1/p | E·S(E) summed |
|---|---|---|---|
| p ≤ 1e4, E ≤ 1e6 | 725 | 0.249 | 0.67 core-h |
| p ≤ 1e4, E ≤ 1e7 | 891 | 0.287 | 55 core-h |
| p ≤ 1e4, E ≤ 1e8 | 987 | 0.308 | 3,400 core-h |
| p ≤ 1e5, E ≤ 1e6 | 2,823 | 0.318 | 4.6 core-h |
| p ≤ 1e5, E ≤ 1e7 | 4,436 | 0.397 | 540 core-h |
| p ≤ 1e5, E ≤ 1e8 | 5,875 | 0.451 | 64,000 core-h |
**[derived: measured S(E) interpolated, applied to `rows_1000000.pkl`]**

This is a lower bound for the flat model. Embedding the components costs about
one exponentiation each, and the modulus search adds more (§5).

**Cost in a Kummer tower** H = k[V]/(V^R − c), k = F_2[x]/(P_t) sparse, D = R·t.
* **Frobenius is a monomial map.** σ^m(V) = γ_m V^(2^m mod R), and the
  coefficients take the k-Frobenius. That is O(R) k-ops plus coefficient
  squarings, with no polynomial multiplication **[checked: kummer.cpp
  `frobH`, bit-exact against PowerMod]**.
* **The norm costs only log n multiplications in H.**
* **Measured** (mults and Frobenius maps are counted inside the norm):

  | | D | h | n | norm | u-exp | total | reference |
  |---|---|---|---|---|---|---|---|
  | p=719 | 64,261 | 359 | 179 | 8–36 ms (11 mults, 11 Frobenius) | 21–43 ms | 30–57 ms (jobe and M5) | `PowerMod`: 69–72 s on the M5 |
  | p=4507 size | 1,126,500 | 4506 | 250 | 0.35 s (≈16 mults, 12 Frobenius) | 5.95 s | 6.3 s (jobe) | – |
  **[checked]**
* **In the p=4507 case the u-exponent dominates.** That is because my `sqrH`
  reduces modulo V^R − c with R full k-multiplications by a random c.
* **Make that reduction a shift.** Replace V by V·g with g in k. This changes c
  into c·g^R, so any representative of the class of c in k*/k*^R works. Pick
  c' = x^i: i comes from a discrete log in μ_R (baby-step giant-step over R
  elements), and g comes from one R-th root in k. Reduction is then a shift
  plus a sparse fold in k, and squaring in H costs O(R·t/64) word ops
  **[derived]**. In the actual search c comes from the term algebra; this step
  keeps it exact and fixes it up to a known R-th power.
* **Expected effect:** at the 4507 size, 4,494 squarings then cost well under
  a second, and the total falls to the roughly 750-multiplication floor, about
  3–4 s, or about 1.3 s with cyclotomic reduction **[guessed]**.

**Recommendation.**
* For any row where a Kummer or Artin–Schreier tower model is available, run
  the Euler test in the tower: norm, then the exponent u, plus cyclotomic
  reduction when h is composite. Never flatten to degree E.
* Use the flat sparse model only where the tower is unavailable. Its floor is
  E·S(E): about 0.5 s at E=1e5, 50 s at 1e6 and 1.6 h at 1e7 on one jobe core.

## 4. Frobenius: composition vs repeated squaring

NTL `CompMod` with a dense modulus on jobe:

| E | 1e4 | 3e4 | 1e5 | 3e5 | 1e6 |
|---|---|---|---|---|---|
| seconds | 0.00158 | 0.014 | 0.158 | 2.49 (1.92 bpm) | 19.7 (9.7 bpm) |
**[checked]**

That fits about E^2.1 at large E (memory-bound Brent–Kung baby steps).
Break-even step j* (composition = j squarings):

* **Sparse modulus:** j* = CompMod / S(E) = 2,600 (0.26E) at 1e4, 30,000 (0.3E)
  at 1e5, and 194,000 (0.19E, bpm) to 394,000 (0.39E, gf2x) at 1e6
  **[derived]**. In an Itoh–Tsujii chain only the top one or two steps
  (≈ E/2, E/4) exceed j*, so a hybrid saves at most about 35% at E=1e6, and
  nothing at E ≤ 3e5. Precomputing the x^(2^(h·2^i)) once per row and reusing
  it across several norms still loses: log₂ n CompMods ≈ 100 s against 50 s of
  squarings at 1e6 **[derived]**. **Verdict: with a sparse modulus, use
  repeated squaring with the custom kernel.**
* **Dense modulus:** SqrMod is 5.66 ms at 1e6 (2.4 ms with bpm), so
  j* ≈ 3,500–4,000. Composition wins for every Itoh–Tsujii step beyond the
  first few **[derived]**. **Verdict: if a dense, composition-built modulus is
  forced, do Itoh–Tsujii with CompMod (log n compositions).** It is still
  2–4x slower than sparse squaring at 1e6.
* **Tower:** Frobenius is structured (§3) and beats both by orders of
  magnitude **[checked at D=64,261: 11 Frobenius maps inside the 8–30 ms
  norm]**.

## 5. Choosing moduli

| choice | squaring | multiplication | cost to obtain | embedding of components |
|---|---|---|---|---|
| sparse irreducible pentanomial or trinomial of degree E | O(E/64) spread + 2 folds: 0.05 ms at 1e6 **[checked]** | ≈ M(E) | proof of irreducibility needed: one full test is about E·S(E) plus a gcd per prime q of E **[derived]**; NTL's search is far too slow (§2.5) | every component needs a root extraction in degree E, about one exponentiation of size E each, checked exactly by y^R = a or y²+y = a |
| chain-composed P_y(X) = P_a(X^R) (Kummer layers) | free to build and keeps the weight w of P_a, but P_a is a dense min poly (w ≈ b/2), so reduction is about w·E/64 word ops: about 90 passes for b=179 **[guessed: ≈1–3 ms at 3.5e6]** | M(E) + w·E/64 | free and canonical (the 727 certificate is exactly this) | χ_R = X for free; phases pinned by construction |
| chain with Artin–Schreier layers P(X²+X) | densifies (Lucas: weight 2^popcount) | dense | free | free |
| tower k[V]/(V^R − c), not flattened | O(R) k-squarings plus a shift once c is normalized to x^i | Kronecker M(R·2t) plus R k-ops | needs only a sparse P_t of the small degree t | components are the tower variables themselves |

**Custom sparse-irreducible search (if the flat model is needed)**
**[derived; not built]**:
* Enumerate trinomials, or pentanomials with all middle terms below E/2 so that
  two folds suffice.
* Early-abort each candidate with a distinct-degree sieve: compute x^(2^i) mod P
  for i ≤ B with the custom squaring and take gcd(x^(2^i) − x, P) every few
  steps.
* Run the full test (x^(2^E) = x, plus gcd(x^(2^(E/q)) − x, P) for each prime
  q | E) only on survivors.
* By Swan's theorem, many E ≡ 0 mod 8 have no irreducible trinomial; go
  straight to pentanomials there.
* Expected total: a small multiple of E·S(E), comparable to one Euler test.

**Recommendation.** Use the tower wherever one exists. When a flat model is
unavoidable, pay once for a sparse irreducible modulus and use the custom
squaring kernel; composition-built dense moduli are only for when the
embedding is otherwise intractable.

## 6. Stack per size range

| operand size | fastest measured | notes |
|---|---|---|
| ≤ 2e4 bits | NTL GF2X/GF2E on a PCLMUL/PMULL gf2x (unrolled Karatsuba with clmul basecase), plus the custom sparse squaring | the conda arm64 gf2x is 9–14x slower here and must not be used |
| 2e4 – 2.6e5 bits | gf2x Toom (jobe tuned; M5 PMULL port with `tune-toom`) | additive FFT is no better below 2^12 words |
| ≥ 2.6e5 bits | **bitpolymul2 additive FFT behind `gf2x_mul`** (`arith/bench/bpm_wrap.c`, threshold env `BPM_THRESHOLD`, default 3000 words) | 2.5–3.1x raw on jobe, 1.4–2.4x at NTL level; NEON port works on the M5 |
| sparse squaring, any size | custom kernel (`arith/bench/sqrk.h`, NEON and x86 paths) | 2.5–3x over NTL SqrMod |
| polynomials over F_2^t (resultants, min polys, gcd) | NTL GF2EX + bpm on jobe | add a half-gcd resultant (NTL GCD is half-gcd, 0.9 s at n=19,580; the classical Euclid in the 359 script is O(n²)); PARI `polresultant` works but is about 15x slower |
| FLINT nmod_poly / python-flint / PARI | not competitive | 4–30x slower; no bit-packed GF(2)[x] type in FLINT 3.3.1 **[guessed for the last clause]** |

**Machines.**
* Both are usable.
* Small and medium sizes: the M5 PMULL port matched or beat jobe per core even
  under load **[checked]**.
* Large sizes: the loaded M5 was 4–6x slower, so its unloaded large-size speed is
  unknown. jobe is shared, so plan on the M5 as the main pool and jobe's spare
  threads as a second.
* A hit must be replayed on the other architecture with a different multiplier
  (PMULL gf2x vs PCLMUL gf2x vs bitpolymul).

## 7. Exactness notes

* Every arithmetic path I built was cross-checked bit for bit against an
  independent path:
  * gf2x `make check` for the NEON port;
  * bitpolymul against gf2x at 12 sizes on each machine;
  * the custom squaring against NTL `SqrMod`;
  * the Kummer norm-and-u test against direct `PowerMod`: 2 trials at degree
    64,261, 340 trials at degree 110;
  * cyclotomic reduction against u
  **[checked]**.
* Probabilistic steps must be closed by an exact check before they are used:
  * `ProbMinPolyMod`: check f(a) = 0 with CompMod;
  * root finding: check y^R = a;
  * irreducibility: use a deterministic Rabin/Ben-Or test, not a probabilistic
    one.
* The Kummer constant normalization (§3) changes the variable by a k-multiple,
  so the term algebra's pinned phases carry over through the explicit factor
  g **[derived]**.

## 8. Not done / open

* `tune-fft` for gf2x on the M5 never finished; its fine step is far too slow.
  I hand-set the PMULL FFT table from my own curve. jobe uses the FFT table
  shipped for x86_64_pclmul plus locally tuned lowlevel and toom thresholds.
* No unloaded large-size M5 numbers.
* Monomial-c normalization and Frobenius-digit exponentiation are designed but
  not implemented.
* The custom sparse-irreducible search, a truncated additive FFT, and
  VPCLMULQDQ (4-lane) kernels on jobe are not built.

## Files

* `arith/gf2x-1.3.0/already_tuned/arm64_pmull/`: NEON port of gf2x's PCLMUL kernels.
* `arith/b-pmull/`: PMULL gf2x build with a hand-set FFT table.
* `arith/libgf2x_pmull_ren.a`: the same library with `gf2x_mul` renamed to `gf2x_mul_orig`, for wrapping.
* `arith/ext/neoninc/avx2neon.h` and `arith/ext/bpm-neon/*.o`: NEON bitpolymul2.
* `arith/bench/sqrk.h`: custom sparse squaring.
* `arith/bench/bpm_wrap.c`: `gf2x_mul` wrapper over bitpolymul.
* `arith/bench/kummer.cpp`: tower Euler test (methods B and C) with reference cross-check.
* `arith/bench/b1.cpp`, `b2.cpp`, `gfcurve.c`, `bpmcmp.c`: benchmarks.
* jobe, `/tmp/excess-bench/`: tuned PCLMUL gf2x, NTL 11.6 (no GMP) at `ntl/`, AVX2 bitpolymul2, and the same benchmarks.
