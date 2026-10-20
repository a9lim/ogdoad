# Crossing / norm-descent engine for singleton tops

Angle: arms O, C, D (singleton top `chi_R`, `R = r^e`) and the singleton odd
components inside arm Z. Author: one of five independent designers.

Evidence tags used throughout:

* **[checked]**: verified by an exact computation in this directory. The script
  and log are named.
* **[derived]**: proved here on paper. The proof is given or sketched.
* **[guessed]**: an estimate or heuristic. The basis is stated.

Scripts and logs live in `design/crossing/`. They use the micromamba env
`~/.local/micromamba/envs/excess` with python-flint 0.8. The C benchmarks
(`design/crossing/cbench/`) were run on jobe against a private gf2x 1.3 build in
`/tmp/xcross`. The M5 was not used for timing because its load average was
above 100 while the other designers' jobs ran.

---

## 0. Verdict in one paragraph

Cross at every level, but reuse each row's crossed model as the working model
of the next row's radicand field. Replace every exponentiation of length ~b by
a Hilbert-90 twisted trace that costs O(log D) multiplications. Choose the top
crossing degree `t` to minimise cost rather than taking the minimal `t`. Do
these three things and the full row field `F = F_2(chi_R)` (degree
`E = R*b`) is never built. Every row then costs a few hundred multiplications in
`K = F_2(alpha_r)` (degree `b = E(r)`), plus O(log) multiplications in one Kummer
field `H = k(v)`, plus an Euler test in `F_(2^h)`.

The field `K` is a floor for this method, not an artifact: the crossed char poly
`f_a` carries `b` bits, and picking it out is equivalent to an R-th root in
`k[Y]/G ≅ K` (section 9). Under the measured kernel costs, here is what the
method reaches:

* **p ≤ 1e4:** 98% of the arm-O/C/D `sum 1/p` mass (0.1407 of 0.1432) for about
  4 core-hours in total, and 99.4% for about 31 core-hours. That is 43% of all
  `1/p` mass in this range.
* **p ≤ 1e5:** 94% of that mass (0.2097 of 0.2222) for about 150 core-hours, and
  97% for about 900 core-hours.

With pessimistic constants (4x slower multiplication and costly Frobenius) the
p ≤ 1e4 figure becomes 97.7% in 7 core-hours. The rows out of reach are long
chains of the Sophie-Germain type, such as 2879 (1439 → 719 → 359 → ...).
There `b = E(1439) = 9e11` bits, so `K` alone is about 113 GB per element.
No rank-one method can handle these rows.

---

## 1. Setting and notation

Take a row `p` with `h = f(p)` and singleton `Q(h) = {R}`, where `R = r^e` and
`r` is an odd prime. The data are:

* `K = F_2(alpha_r)`, with `b = [K:F_2] = E(r)`.
* `chi = chi_R`, with `chi^R = alpha := alpha_r`.
* `F = K(chi)`, with `[F:F_2] = E = R b`.
* `h = R s` with `s | b` and `r ∤ s`.

The selected element is `beta = chi + m`, with `m = 1` in arms O/C and `m = 4`
in arm D.

**Target.** The quantity to compute is `T_h := N_(F/F_(2^h))(chi + m)`, an
element of `F_(2^h)`. Then for every row `p` with `f(p) = h`, the rule holds iff
`T_h^((2^h-1)/p) ≠ 1`. This is the norm reduction of SPEC §3, applied with
`e = h`. `T_h` depends only on `h`, so all rows sharing `h` share the work: for
p ≤ 1e4 the 451 singleton-top rows have 418 distinct `h`. The rows 359 and 1433
share `T_179`, which is exactly the stored `theta` of
`ordinary_359_hilbert_certificate.py`.

**Levels of a singleton chain.** Index the chain by `i`:

* `alpha_(r_i) = chi_(R_(i+1)) + m_i`.
* `K_i = F_2(alpha_(r_i)) = K_(i+1)(chi_(R_(i+1)))`, with `b_i = R_(i+1) b_(i+1)`.
* The top is `K_1 = K`.
* Row `r_i`'s own field is `K_(i-1)`.

The arm-Z case, where some lower radicand is a sum of components, is covered in
§12.

**Crossing data at a Kummer step `L = K(chi)`, `chi^R = alpha`.**

1. Choose a subfield `k ⊂ K` with `t = [k:F_2]`.
2. Set `D = b/t`, `S = (2^b-1)/(2^t-1)`, `g_K = gcd(R, 2^b-1)`, and
   `w = S^(-1) mod g_K`.
3. Set `c = N_(K/k)(alpha)^w ∈ k` and `z = alpha/c`.
4. Take `a ∈ K` with `a^R = z`, and set `v = chi/a`.
5. Set `H = k[V]/(V^R - c)`.
6. Set `f_a(X) = prod_(sigma in Gal(K/k)) (X - sigma a) ∈ k[X]`, of degree `D`.

---

## 2. Admissible crossing degrees

**(C)** The degree `t` is admissible iff `t | b`, `s | t`, `ord_r(2) | t`, and
`v_r(t) = v_r(b)`.

By lifting the exponent, `ord_r(2) | t` together with `v_r(t) = v_r(b)` is
equivalent to `v_r(2^t-1) = v_r(2^b-1)`, which is the spec's condition. It is
also equivalent to `r ∤ S`. **[derived]**

The minimal admissible degree is `t_min = lcm(ord_r 2, s, r^(v_r b))`. Section
10 shows that the cost-optimal `t` is often much larger.

---

## 3. Theorem A: the crossing identity

**Theorem A.** Let `t` be admissible. Then:

* (i) `alpha/c ∈ K^(xR)`.
* (ii) For any `a` with `a^R = alpha/c`, `v^R = c`, and `V^R - c` is irreducible
  over `K`, and hence over `k`.
* (iii) `F = K ⊗_k H`, via `V ↦ v`.
* (iv) `W := N_(F/H)(1 + chi) = V^D f_a(V^(-1)) mod (V^R - c)`. Explicitly, if
  `f_a = sum_i e_i X^i`, then the coefficient of `V^j` (for `j < R`) is
  `sum_(i : D-i ≡ j mod R) e_i c^((D-i-j)/R)`. If `D < R` there is no folding,
  and `W` is the reversed coefficient vector.
* (v) `T_h = N_(H/F_(2^h))(W)`.

In arm D, `N_(F/H)(chi_4 + chi) = V^D f_a(chi_4 V^(-1))` when `chi_4 ∈ k`.
Arms C and D are tiny anyway: `K = F_4` and `E ≤ 4·3^k`.

**Proof.** **[derived]**

* (i): `G = K^x/K^(xR)` is cyclic of order `g_K`. The class of `N(alpha)` is
  `[alpha]^S`, and `r ∤ S`, so `[c] = [alpha]^(Sw) = [alpha]`.
* (ii): `(chi/a)^R = alpha a^(-R) = c`. Since `[K(chi):K] = R`, the polynomial
  `X^R - alpha` is irreducible, so `alpha ∉ K^(xr)`. Since `c ≡ alpha`, also
  `c ∉ K^(xr) ⊇ k^(xr)`. Capelli's criterion (R odd) then gives
  irreducibility.
* (iii): `F = K(v)`, and `[F:K] = R = [H:k]`.
* (iv): `Gal(F/H) ≅ Gal(K/k)` by restriction, so
  `N(1 + av) = prod_sigma (1 + sigma(a) v) = v^D prod_sigma (v^(-1) + sigma a)`.
  In characteristic 2 the signs drop.
* (v): norms are transitive.

**Choice independence.** **[derived]** Every run fixes an explicit model `M` and
an embedding `F_abs → M` determined by images of the components that satisfy
their defining relations. Different choices of the model of `K`, of `k ⊂ K`, of
the root `a`, or of the root `v` differ by an isomorphism that fixes the
abstract field. So the computed `T` is the image of the abstract
`T_abs ∈ F_abs`. Its minimal polynomial over `F_2` is choice-free, and so is
every Euler symbol. Two runs in the same model must agree exactly.

**Check (T1).** **[checked]** The script `crossing/test1_crossing.py` compares
`minpoly_(F_2)(T_crossed)` with `minpoly_(F_2)(T_brute)`. Here `T_brute` is
computed in the full `F` as `(1+X)^((2^E-1)/(2^h-1))`. Every case matched, and
in every case the rule held:

| rows | h | R | b | t | D | H bits | E |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 23 and 89 | 11 | 11 | 20 | 10 | 2 | 110 | 220 |
| 727 | 121 | 121 | 20 | 10 | 2 | 1210 | 2420 |
| 179 | 178 | 89 | 220 | 22 | 10 | 1958 | 19580 |

* In row 727, `mu_121 ⊄ K`, which shows the identity does not need the R-th
  roots of unity in `k`.
* The non-minimal crossing degrees `t ∈ {44, 110}` for row 179 and `t = 20`
  (`D = 1`) for row 727 are run by `test1_crossing.py bigt`. See
  `test1_bigt.log` and §14.

---

## 4. Theorem B: Hilbert-90 root extraction without a b-bit exponent

This is the step that made the 719 root expensive. The exponent
`(1 - yS)/R` in `a = z^x · nu` (with `xR + yS = 1`) has periodic base-`2^t`
digits **[checked: digit formula `q_j = A·((D-1-j)y mod R) + eps_j`, six (b,t,R)
cases, including (3504820, 179, 359)]**. Even so, it still costs Θ(R)
multiplications. This section replaces it.

**Theorem B.** Let `r` be prime with `r | 2^t - 1`, let `psi = phi^t` generate
`Gal(K/k)`, and let `z ∈ K^(xr)`. Set `Q = 2^t`, `Z = z^((Q-1)/r)`, and
`u = Z^(-1)`. Then:

1. `N_(K/k)(u) = 1`.
2. For `theta ∈ K`, put `w = sum_(i<D) N_i(u) psi^i(theta)`, where
   `N_i(u) = prod_(j<i) psi^j(u)`. Then `psi(w) = Z w`.
3. `w ≠ 0` for every `theta` outside a proper k-subspace.
4. `omega := w^r / z` lies in `k^x ∩ K^(xr)`, which equals `k^(xr)`.
5. `a := w / omega^(1/r)`, using any r-th root taken in `k`, satisfies `a^r = z`.

**Proof.** **[derived]**

* (1): `N(Z) = N(a_0)^(Q-1) = 1` for any root `a_0`.
* (2): `u psi(w) = sum_(i=1)^D N_i psi^i(theta) = w`, since `N_D = 1` and
  `psi^D = 1`.
* (3): the map `theta ↦ w` is k-linear and nonzero, by Artin's independence of
  characters.
* (4): `psi(w^r/z) = w^r Z^r / z^Q = w^r/z`. Equality of the two groups follows
  from `r ∤ S`.
* (5) follows from (4).

**Doubling recursion.** **[derived and checked]** Start from
`(S_1, N_1) = (theta, u)`. Then

* doubling: `S_2m = S_m + N_m psi^m(S_m)`, `N_2m = N_m psi^m(N_m)`;
* increment: `S_(m+1) = theta + u psi(S_m)`, `N_(m+1) = u psi(N_m)`.

Applied left to right over the bits of `D`, this costs
`2(floor(log2 D) + popcount D)` multiplications and the same number of
`psi`-powers.

**Prime powers `R = r^e`.** Iterate `e` times. After each r-th root, multiply by
the element of `mu_r ⊂ k` that keeps the root inside `K^(x r^(e-j))`. The test
is in `k`: `N(x) ∈ k^(x r^m)`. This works because `K^x/K^(x r^m) → k^x/k^(x r^m)`
is an isomorphism, and `zeta^D` runs over `mu_r` since `r ∤ D`.

**Cost.** `Z = (z^((2^f-1)/r))^((2^t-1)/(2^f-1))`, where `f = ord_r 2`. That is
`f` squarings plus about `f/7` multiplications, followed by an Itoh–Tsujii
chain of length `log(t/f)`. The total is

```text
e · (f squarings + f/7 + 4 log2 D) multiplications in K,
```

with no b-bit exponent. Small-field work: one r-th root in `k`.

**Check (T2).** **[checked]** `crossing/test2_root.py` verifies `a^R == z`
exactly in each case:

| row | (b, t, R) | K-mults in doubling | psi-powers |
| --- | --- | --- | --- |
| 23/89 | (20, 10, 11) | 2 | 5 |
| 727 | (20, 10, 121), two steps with the `mu_11` adjustment | 4 | 9 |
| 179 | (220, 22, 89) | 8 | 11 |
| 359/1433 at real scale | (19580, 178, 179) | 20 | 23 |

The script `crossing/test3b_twolevel.py` reuses the same routine inside the
recursive model.

---

## 5. Theorem C: recursion, where the crossed model of row r becomes the radicand field of row p

At level 2 the crossing gives `chi_(R_2) = a_2 v_2`, with `a_2 ∈ K_2` (cached
from row `r_1`'s computation) and `v_2 ∈ H_2 = k_2[V]/(V^(R_2) - c_2)`.
Theorem A(iii) at level 2 says:

```text
K_1 = F_2(chi_(R_2)) = K_2 ⊗_(k_2) H_2,   chi_(R_2) ↦ a_2 ⊗ v_2,   alpha_(r_1) = m_1 + a_2 ⊗ v_2.
```

The map `X ↦ a_2 v_2` from `K_2[X]/(X^(R_2) - alpha_(r_2))` is a well-defined
`K_2`-algebra homomorphism, because `(a_2 v_2)^(R_2) = alpha_(r_2)`. It is
injective because the source is a field, and dimensions agree. So it is the
term-algebra field with **every lower component embedded identically**: the
shared phases are pinned. **[derived]**

Unrolling the recursion when each crossing field sits in the Kummer field below
it (`k_i ⊂ H_(i+1)`, as in the 179 → 89 → 11 chain):

```text
K_1 = G[Y]/g_L(Y),   G = k_L(v_L)(v_(L-1))...(v_2),   v_i^(R_i) = c_i ∈ k_i ⊂ G_(i+1).
```

Here `G` is a pure Kummer tower over the bottom crossing field. The polynomial
`g_L` (of degree `D_L`) is the minimal polynomial of the bottom radicand over
`k_L`. Every element of `K_1` is a polynomial of degree `< D_L` over `G`. If
`k_i ⊄ H_(i+1)`, use the compositum `H_(i+1) k_i` as the next coefficient field
instead.

**Check (T3).** **[checked]** `crossing/test3b_twolevel.py` builds this model for
the h=179 rows (359 and 1433). It uses:

* `K_2 = F_2(alpha_89) = k_2[Y]/g_2`, with `k_2 = F_(2^22)` and `D_2 = 10`.
* `H_2` as the flat `F_2[u]/M_c(u^89)`, of 1958 bits, with `k_2 → H_2` sending
  `c_2 → u^89`.
* `K_1 = H_2[Y]/g_2`, of 19580 bits, with `chi_89 = a_2 u`. The check
  `chi_89^89 == alpha_89` passes.

The top crossing is then carried out in this model by two paths, described in
§6. No field of degree `E = 3,504,820` is built.

---

## 6. The char poly of the crossed root, and the hybrid

**Path A: char poly over the crossing field `k`.** Use power projection.

1. Pick a k-linear form `l`. In `K = k[y]/P_A(y)`, take the coordinate of `y^0`.
   In the T3 model, take `Tr_(H_2/k_1)` of the `Y^0`-coefficient.
2. Compute `s_m = l(a^m)` for `m < 2D`. Use baby steps `a^j` (`j < s`) and
   giant steps `l ∘ (a^(si)·)` by transposed multiplication (a middle product),
   with `s = sqrt(2D)`.
3. Run Berlekamp–Massey over `k`. A half-gcd version costs
   `O(M_k(D) log D)`.
4. Verify `deg f = D` and `f(a) = 0`. Since `k(a) ⊇ k(a^R) = K`, this forces
   `f = f_a`. **[derived]**

Cost: `4 sqrt(2D) M(b)`, plus `2D^2` lazy k-multiply-accumulates, plus BM.

**Path B: char poly over an intermediate field `G` (the hybrid).** Let
`k ⊆ G ⊆ K`, with `K` an explicit `G`-algebra of rank `D_G`. Then:

```text
N_(F/GH)(1 + chi) = V^(D_G) f_a^(G)(V^(-1))   in GH = G[V]/(V^R - c),
T_h = N_(GH/F_(2^h))(that).
```

When `D_G < R` no folding is needed. **[derived; the same proof as Theorem A
with `G` in place of `k`.]**

**Check (T3).** **[checked]** For the h=179 rows:

* **Path A:** `f` over `k_1 = F_(2^178)`, of degree 110. `W` lies in `H_1`
  (31862 bits) and `T_A = N_(H_1/F_(2^179))(W)`.
* **Path B:** `f` over `H_2`, of degree 10. `W'` lies in `M = H_2[V]/(V^179 - c_1)`
  (350482 bits) and `T_B = N_(M/F_(2^179))(W')`.

The two paths agree exactly (`T_A == T_B`). Also,
`minpoly(T) == minpoly(theta_cert)`: the result is a Frobenius conjugate of the
p=359 certificate's stored theta, which is an independent computation by a
different route. Both Euler symbols are nontrivial: for p = 359, which is
consistent with the known `m_359 = 1`, and for p = 1433, which is a new row.
See `crossing/test3b_jobe.log` and §14.

**Which path to use.** **[guessed, from measured kernels]**

* Lazy small-field multiply-accumulate is cheap: about 5 ns at t = 179, 26 ns at
  t = 500, and 76 ns at t = 1000 (PCLMUL, measured). So path A with a small `k`
  is cheap whenever `D^2` is moderate.
* For deep chains the right move is to take `t` large, which is the
  "path B at the extreme" case. `k` is then a large subfield made of all the
  chain-prime tensor factors, `D` drops to the bottom co-degree (about
  50–800), and the inner products become `2D^2` big-field products.
* For row 1439 this cuts the model cost from about 1.3e6 s (`t = 359`,
  `D = 3.5e6`) to about 3e4 s (`t = 5.7e6`, `D = 220`).

---

## 7. Final descent: monomial Frobenius on `H = k[V]/(V^R - c)`

For `m ≥ 0`, reduce `2^m` modulo `R·ord(c)` and write `2^m = qR + rho`. Then

```text
phi^m(sum_j x_j V^j) = sum_j phi^m(x_j) · c^(qj + floor(rho j / R)) · V^(rho j mod R).
```

This costs `R` small-field Frobenius maps plus `R` small multiplications.
`N_(H/F_(2^h))` is a doubling product over `phi^h`, using about
`2 log2(t/s)` multiplications in `H`. The Euler tests then run in `F_(2^h)`,
whose size is at most `p` bits. **[derived; the sigma formula on
`M = H_2[V]/(V^179 - c_1)` was checked against 179 direct squarings in T3.]**

---

## 8. The algorithm per distinct h (singleton top)

```text
input: h, R = r^e, the level data for r (from row r's own computation):
       a representation of K = F_2(alpha_r) with cheap mult and Frobenius,
       alpha_r inside it, and cached crossed roots of the lower levels.
1. choose an admissible t minimising the §10 cost; build k ⊂ K as a coefficient
   field of the representation (sub-tensor / Kummer sub-tower).
2. c  = N_(K/k)(alpha)^w        (Itoh–Tsujii, or a resultant over k); check psi(c) = c
3. a  = HilbertRoot(alpha/c, R) (Theorem B); check a^R == alpha/c
4. f  = BM(l(a^m), m < 2D)      (path A or B); check deg f = D, f(a) = 0
5. W  = V^D f(1/V) mod (V^R - c);  T = N_(H/F_(2^h))(W)  (§7)
6. for each p with f(p) = h:  record  s_p = T^((2^h-1)/p) != 1
7. cache for later rows:  (k, c, a) and the model K ⊗_k H of F_2(chi_R)
```

Rows are processed in increasing `p` (SPEC §6.4), so the level data of `r < p`
always exist. If `m_r` ever changed from the rule, which would be a
counterexample, then `alpha_r` changes and every cached crossing above `r` is
recomputed. Field degrees do not change when `m` moves between 0 and 1.

---

## 9. Why `K = F_2(alpha_r)` is a floor for crossing-type methods

This section answers the "carry only small data up the chain" question.

**The selection problem is equivalent to an R-th root.** **[derived]** Set
`G(Y) = charpoly_k(alpha/c)`. This is computable from lower-level data by
polynomial norms. For `m_1 = 1` and `k ⊂ H_2`:

```text
G(Y) = c^(-D) · N_(H_2/k)[ V_2^(D_2) f_(a_2)((cY + 1)/V_2) ].
```

The degree-D irreducible factors of `G(X^R)` over `k` are exactly the `g_K`
twists `f_(zeta a)`, `zeta ∈ mu_(g_K) ⊂ k`. Every twist gives the same `W`,
because `V ↦ zeta^(-1) V` is a k-automorphism of `H`. So any factor works. But finding a factor of `G(X^R)` over `k` is
the same as choosing an R-th root of `Y` in `k[Y]/G ≅ K`. In one direction,
`f = Res_Y(G, X - a(Y))`. In the other, a factor determines the prime above
`G`, which determines the root.

**Information content.** **[derived]**

* `f_a` has `D t = b` bits.
* `W` has only `R t` bits, but in the hybrid with `D_G < R` the element `W'` is
  literally the coefficient vector of `f^(G)`, which has `b` bits again.

**Rank argument.** **[guessed, heuristic only]** Write any decomposition as `chi = x·y`
with `x ∈ X` and `y ∈ Y`, where `F = XY`. Then `x^R y^R = alpha` generates `K`.
`alpha = m + a_2⊗v_2` has tensor rank 2 in `K_2 ⊗ H_2`, so `chi` is never rank
one over a factor smaller than `K`. A rank-ρ element costs a determinant of
commuting `D×D` pencils, whose intermediate data is about `E` bits.

**Consequence.** A scheme carrying only `O(R t)`-bit data up the chain would be
an ancestry-recursive evaluation of the selected Kummer coordinate. That is
precisely the "nim reciprocity route" that OPEN.md §2 leaves open. Its
multiplicative and Galois-covariant forms are excluded by the proved rank-one
saturation. Theorem B is additive (a twisted trace), so additive identities are
not excluded, but none that avoids the `b`-bit root is known.

**What the recursion does achieve:**

* `F` (size `R·b`) is never built.
* `K` is never built by root-finding or by embedding a flat field. It is
  assembled from cached crossed data in one tensor step.
* No exponent of length `b` appears anywhere.

---

## 10. Primitive costs and the cost model

**Measured on jobe (x86-64, PCLMUL, gf2x 1.3, single thread, load about 10/24):**
**[checked]**

| `gf2x_mul` size | 1e5 bits | 1e6 | 3e6 | 1e7 | 3e7 | 1e8 | 3e8 | 1e9 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| time | 0.14 ms | 3.05 ms | 10.5 ms | 42.5 ms | 130 ms | 0.51 s | 2.0 s | 6.9 s |

The M5 with NTL was 30–180x slower under the current load (95 ms at 1e6 bits,
94 s at 1e8 bits). That gap was probably made worse by gf2x lacking a PMULL
kernel on arm64. For bulk compute, jobe-class x86, or a PMULL port, is the
platform.

Small field, lazy multiply-accumulate:

| t (bits) | 179 | 359 | 500 | 1000 | 2500 |
| --- | --- | --- | --- | --- | --- |
| time per term | 4.9 ns | 12.6 ns | 26 ns | 76 ns | 411 ns |

**Representation constants.** **[derived; not timed end to end]**

* `K = k[y]/P_A(y)` with flat `A`: packed Kronecker product (`P(2b)`) plus
  Barrett over `F_2[y]` (`2P(b)`). So `M ≈ 5P(b)`, doubled per extra tensor
  tier.
* `psi^m` acts only on `A`. It is a `D×D` bit-matrix applied to `t` bitplanes,
  with matrices precomputed for `D ≤ 3e4`, or recursively otherwise. So
  Frobenius costs about 1 M or less.

**Per-h cost.** **[guessed model; `costmodel4.py`]**

```text
root  = e (0.4 f + 4 log2 D + 5) M(b)
bsgs  = 4 sqrt(2D) M(b)
inner = 2 D^2 m_k(t) + 6 D P(t)
bm    = 30 D log2(D)^2 m_k(t)
final = (2 log2(t/s) + 4) · 5 P(R t)
build = 4 M(b)
```

`t` is optimised over the admissible divisors of `b`, with the largest field
held to at most 4e10 bits.

**Examples** (optimal t). `E` is the size of the full field the method avoids.

| row | arm | b | t | D | largest field | modelled cost |
| --- | --- | --- | --- | --- | --- | --- |
| 733 | O | 60 | 60 | 1 | 3660 | < 1 ms |
| 797 | O | 1980 | 396 | 5 | 78804 | 11 ms |
| 1433 | O, same h as 359 | 19580 | 178 | 110 | 31862 | 30 ms |
| 4507 | O | 1500 | 750 | 2 | 563250 | 0.2 s |
| 839 | O | 37620 | 418 | 90 | 175142 | 0.1 s |
| 719 | O | 3,504,820 | 3938 (or 179) | 890 (or 19580) | 3.5e6 | ≈ 25 s (≈ 65 s at `t_min`) |
| 1439 | O | 1.26e9 | 5.7e6 | 220 | 4.1e9 | ≈ 8 h (≈ 15 days at `t_min`) |
| 2879 | O | 9.0e11 | n/a | n/a | n/a | out of reach (`K` is 113 GB per element) |

The full fields avoided are `E = 3660` (733), 3.9e5 (797), 3.5e6 (1433),
1.1e6 (4507), 1.6e7 (839), 1.26e9 (719), 9.0e11 (1439) and 1.3e15 (2879).
At `t_min`, row 719's cost is dominated by its `4 sqrt(2D)` BSGS multiplications. The optimal `t` cuts that term.

Rows 743 and 1031 are arm Z with two odd components, so they are outside this
engine. They are tiny anyway: E = 57876 and 210120, with component radicand
fields of 6 and 156 bits (743) and 4 and 408 bits (1031). Any method handles
them in seconds.

**Scaling.**

```text
cost ≈ [e(0.4 f(r) + 4 log D) + 4 sqrt(2D)] · M(E(r)) + O(log) M(R t),
```

which is quasi-linear in the radicand degree `b = E(r)`. The cost compounds
along a chain only through `b`. So a singleton-top row costs about the same as
its radicand row `r`, times `O(f(r) + sqrt D)`.

---

## 11. Rows reached (sum 1/p mass)

The mass figures cover rows `727 < p ≤ X`. The arm-O/C/D mass is 0.1432 of
0.3306 total for p ≤ 1e4, and 0.2222 of 0.5528 total for p ≤ 1e5. **[guessed
model]**

| per-h budget | p ≤ 1e4: mass reached | cumulative core-h | p ≤ 1e5: mass reached | cumulative core-h |
| --- | --- | --- | --- | --- |
| 1 s | 0.1210 (84.5%) | 0.0 | 0.1406 (63.3%) | 0.0 |
| 60 s | 0.1369 (95.6%) | 0.2 | 0.1888 (85.0%) | 4.9 |
| 1 h | 0.1407 (98.2%) | 3.7 | 0.2097 (94.4%) | 146 |
| 10 h | 0.1424 (99.4%) | 31 | 0.2156 (97.0%) | 879 |
| 100 h | 0.1427 (99.7%) | 110 | 0.2186 (98.4%) | 5138 |

The pessimistic variant uses `M = 20P` and costs every Frobenius and squaring
at 1 M:

| per-h budget | p ≤ 1e4: mass reached | cumulative core-h | p ≤ 1e5: mass reached | cumulative core-h |
| --- | --- | --- | --- | --- |
| 1 h | 0.1398 (97.7%) | 6.9 | 0.2025 (91.1%) | 199 |
| 10 h | 0.1407 (98.2%) | 29 | 0.2099 (94.5%) | 1212 |
| 100 h | 0.1424 (99.4%) | 188 | 0.2157 (97.1%) | 8396 |

At the spec's random-model rate, reaching essentially all of the 0.142
arm-O/C/D mass below 1e4 is worth about 13% hit probability on its own.

**Caveat.** 55% of this mass has a multi-component lower radicand: `alpha_r` is
a sum of components, as in 797, where `alpha_199 = chi_9 + chi_11`. For those
rows the model assumes the arm-Z engine exports `K = F_2(alpha_r)` in a
representation with cheap Frobenius (§12). That engine already had to build
`K`, because `K` is row `r`'s own field.

Here is the split by radicand-field size for p ≤ 1e4:

| `b = [K:F_2]` | rows with multi-component radicand: mass | rows with singleton radicand: mass |
| --- | --- | --- |
| ≤ 1e4 | 0.0632 of 0.0784 | 0.0435 of 0.0648 |
| ≤ 1e5 | 0.0715 | 0.0518 |
| ≤ 1e6 | 0.0753 | 0.0596 |

For radicand fields up to about 3e4 bits, any exact dense method, such as the
term basis with Berlekamp–Massey, builds `K`.

---

## 12. Singleton components inside arm Z (interface)

For `kappa = sum_q chi_q`, every odd component crosses: `chi_q = a_q ⊗ v_q`,
with `a_q ∈ K_q = F_2(alpha_(r_q))` and `v_q ∈ H_q` small. Then `kappa` is a sum
of |Q| rank-one tensors.

**Two odd components.** Let `k' = K_1 ∩ K_2` and `G = k'·H_1·H_2·F_(2^h)`.
**If** `L = K_1K_2` and `G` are linearly disjoint over `k'`, then:

```text
N_(F/G)(a_1v_1 + a_2v_2) = Res_Y( f_(a_2)^(k')(Y),  v_1^(D_1) f_(a_1)^(k')(Y v_2 / v_1) ),
```

where the char polys are taken over the canonical `k'`. **[derived]**

Linear disjointness can be checked by integers: `[F:G] = [K_1:k'][K_2:k']`.
When it fails, the product over `Gal(K_1/k') × Gal(K_2/k')` over-counts. This
is the phase trap in SPEC §2. The fallback is the norm in the compositum
`L ⊗_(L∩G) G` by Itoh–Tsujii.

Phases are pinned because `a_1` and `a_2` are computed in models where the
shared lower components (for example `chi_3` in rows 743 and 13) are the same
elements (Theorem C). The crossing makes each component's data `b_q`-sized. The
combination step is owned by the arm-Z designs.

---

## 13. Exactness and certificates

* Every probabilistic choice is followed by an exact check:
  * `theta` in Theorem B: `w ≠ 0`;
  * small-field roots: `x^r == y`;
  * Berlekamp–Massey: `deg f = D` and `f(a) = 0`;
  * the random `k`-elements used for the Sylow generator are also checked.
  No step can silently skip a row: a failed check aborts the row.
* `c ∈ k` is checked by `psi(c) == c`. `a^R == alpha/c` is checked with one
  exponentiation by `R`. The tensor step is checked by
  `(a_2 v_2)^(R_2) == alpha_(r_2)`.
* **Certificate for a hit.** The certificate is the per-level tuples
  `(k_i model, c_i, a_i, v_i)` with their relation checks, plus `f_a`
  (`b` bits), `W`, `T_h`, and the Euler power `T_h^((2^h-1)/p) = 1`.
* **Independent replay.**
  * Recompute `T_h` with a different admissible `t`, or by path A against
    path B. These must agree exactly in a shared model, or up to Frobenius
    across models, which is compared through `minpoly_(F_2)`.
  * For rows with `E ≤ 1e7`, compute the full-field norm `N_(F/F_(2^h))`
    directly.
* **Validation set.**
  * All OEIS rows 3..709 that have singleton tops.
  * 719 and 727, which have certificates.
  * The structurally forced smaller translates: `T_h` must be
    `chi`-norm-compatible, and `m = 0` in arm O must be a p-th power, so
    `N(chi)^((2^h-1)/p) = 1`. This costs one extra norm, of `chi`.
  * The `T_179` cross-check against `theta`, already done (T3).

---

## 14. Status of the checks (all exact; all passed)

* **T1** (`crossing/test1_crossing.py`, `test1.log`). Crossed against brute
  force with the minimal `t`: rows 23/89, 727 and 179 match.
* **T1 bigt** (`test1_bigt.log`). Non-minimal `t`: row 179 with `t = 44`
  (`D = 5`) and `t = 110` (`D = 2`), and row 727 with `t = 20` (`D = 1`). All
  minimal polynomials match, and the rule holds for 179 and 727.
* **T2** (`test2_root.py`, `test2.log`).
  * The periodic-digit formula for the norm-split exponent holds on 6
    `(b,t,R)` cases, including `(3504820, 179, 359)`.
  * Hilbert-90 roots satisfy `a^R == z` for `(20,10,11)`, `(20,10,121)` (two
    steps with the `mu_11` fix), `(220,22,89)` and `(19580,178,179)`.
* **T3** (`test3b_twolevel.py`, `test3b_jobe.log`; 380 s on jobe via
  `uv run --with python-flint==0.8.0`):
  * the level-2 crossing in `K_2` (220 bits);
  * flat `H_2` (1958 bits) and the embedding `k_2 → H_2`;
  * `K_1 = H_2[Y]/g_2` with `chi_89 = a_2 v_2` and `chi_89^89 = alpha_89`;
  * structured Frobenius on `K_1` against direct squaring;
  * `c_1 ∈ k_1`;
  * the Hilbert-90 root `a_1^179 = alpha_179/c_1`;
  * the monomial `sigma` on `M` against 179 squarings;
  * **path A (char poly over k_1, degree 110) == path B (char poly over H_2,
    degree 10) exactly**;
  * **`minpoly(T_179) == minpoly(theta)` of the p=359 certificate**;
  * the Euler symbols for 359 and 1433 are both nontrivial.

  The first T3 run (`test3_twolevel.py`, killed) used squaring-based
  Frobenius and asserted that `T` was an `H_2`-constant. That assertion is
  wrong: `F_(2^179)` lies in `H_1 = k_1(V)`, not in `k_1`. It was corrected
  before the passing run.
* **Row 1433** **[checked twice]**. `theta^((2^179-1)/1433) ≠ 1` holds directly
  for the certificate's theta, and the independent T3 recomputation gives the
  same result. So **`m_1433 = 1` follows the rule**.
  * The primitive part of `2^179 - 1` is `359 · 1433 · q`, with `q` a 49-digit
    prime.
  * 359 and 1433 are the only `p ≤ 1e5` with `f(p) = 179`.
  * This rests on theta's full-mode certificate or on T3 (both exact).
  * It is a new row beyond OEIS and the 719/727 certificates, and it cost
    nothing because it shares `T_h` with 359.

## 15. Correctness risks

1. **Crossing-field embedding.** `k ⊂ K` must be a genuine subfield of the
   model. If `k` is taken from the wrong tensor factor, for example
   `F_(2^g)` versus the full prime-power factor, `c` will not be fixed by
   `psi`. The `psi(c) == c` check catches this, but it must never be skipped.
2. **The admissibility condition `v_r(t) = v_r(b)`.** Without it, the iso of
   r-power quotients fails. The symptoms are that `omega` has no r-th root in
   `k` (Theorem B), or that `c` is not congruent to `alpha` (Theorem A). Both
   are caught. But a model that skipped the `f(a) = 0` check could produce a
   wrong `W`.
3. **Twist and conjugation bookkeeping in path B.** `f^(G)` must be taken over
   the `G` that actually contains `c` and `v`. Using an `H_2` that does not
   contain `k_1` gives a wrong `M`. T3 shows paths A and B agree in one model,
   and that agreement is the regression test to keep.
4. **Multi-component radicands.** These rely on the arm-Z engine's phase
   correctness. A mismatched `k'` silently over-counts the Galois product.
   The integer degree identity must be asserted (§12).
5. **The cost model** is a model, not a timing of the full pipeline. The
   representation constants (`M ≈ 5–20 P`, Frobenius ≤ 1 M) are derived, not
   measured. Heavy rows (≥ 1e8-bit `K`) are where it matters. Their `D^2`
   term is safe because `t` is optimised.
6. **Propagation of a hit.** If some `m_r` ≠ rule, every row above `r` must be
   recomputed. Cached crossings carry the dependency list.

---

## 16. Implementation plan

1. **Small exact reference.** Python, extending
   `crossing/test1_crossing.py`: crossing plus brute force for all singleton
   rows with `E ≤ 2e5`, compared against the OEIS b-file (3..709). This is the
   regression oracle.
2. **C/C++ core on gf2x (x86 PCLMUL).** Optionally add a PMULL port for the M5.
   Components:
   * packed `k[y]/P_A` multiplication;
   * transposed middle product;
   * a Frobenius bit-matrix kernel (M4RI-style) for `psi^m`;
   * Hilbert-90 root;
   * BSGS power projection with an OpenMP inner-product matrix;
   * half-gcd Berlekamp–Massey over `F_(2^t)`;
   * monomial-Frobenius norm on `k[V]/(V^R - c)`.
3. **Level cache.** Per odd `r`: `(K` representation, `alpha_r`, crossed data
   per admissible `t)`. For multi-component `alpha_r`, an import hook from the
   arm-Z engine.
4. **Driver.**
   * Group rows by `h`, and order them by `p`.
   * Compute `t*` from the cost model; fall back to `t_min` if
     `max field > RAM/4`.
   * Run all checks.
   * On a hit, emit a certificate and immediately replay it with a second `t`
     and with path B.
5. **First targets.**
   * Row 1433, which is free: `T_179 = theta` from the existing certificate.
   * All arm-O rows with `b ≤ 1e4`: 297 rows below 1e4, mass 0.107. These are
     seconds-to-minutes jobs.
   * Then 719, as an end-to-end regression against its certificate. Compare
     `minpoly(T_359)`; the certificate's phase must be nontrivial.
   * Then the `b ≤ 1e8` frontier.

Files: this design (`design/crossing.md`); scripts `design/crossing/xlib.py`,
`test1_crossing.py`, `test2_root.py`, `test3b_twolevel.py` (passing run; `test3_twolevel.py` is the first, slower version), `costmodel4.py`
(plus `costmodel*.out`); `cbench/` (`gfbench.c`, `kmul.c`, `mulbench.cpp`).
