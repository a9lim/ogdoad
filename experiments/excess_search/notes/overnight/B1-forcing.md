# B1 — forced translates and the structure of possible excess values

Avenue B1 of the overnight run. Tags: [S] standard/cited, [D] derived here
with proof, [N] checked by a named small computation, [H] heuristic.

Status: complete. The global-forcing route is closed in all explicit families (§5), and arm C/D/O5/Z{3,4} failures force `m_p ≥ 16` (§4).

## 1. The CM forcing lemma, checked and generalized

### 1.0 Conventions [D]

Fix an odd prime `p`, `h = ord_p(2)`, and `x` in `F_{2^E}^x` with `h | E`.
Every field degree in Conway's tower below `alpha_p` has only prime factors
`< p`, so `p` does not divide `E/h` and `v_p(2^E-1) = v_p(2^h-1) =: e_p`.
Hence `x` is a `p`-th power in its defining field iff `p^{e_p}` does not
divide `ord(x)`. Write `Phi_p(x) in Z/p` for the Kummer character
(`x^{(2^E-1)/p} = theta^{Phi_p(x)}` for a fixed primitive `p`-th root `theta`).
`Phi_p` is a homomorphism with `Phi_p(Frob^j x) = 2^j Phi_p(x)`, and it kills
every element whose order is prime to `p`. A translate `c` is **forced at
level h** if `Phi_p(kappa + c) = 0` for every row prime `p` of level `h`
(that is, `ord_p(2) = h`).

### 1.1 The coordinator's lemma: correct, with one hypothesis made explicit [D]

The proof is right. It needs `P^+ = P cap M^+` to be **inert**, not
ramified, in `M/M^+`. "`c` lies in the decomposition group" alone is not
enough: if `P^+` ramifies, `c` acts trivially on `O/P` and the step
`red(c u) = red(u)^{2^{E/2}}` fails. For `M = Q(zeta_N)` with `N` odd, 2 is
unramified, so the cyclotomic uses in the digest are fine. Kronecker is
applied correctly: for CM `M`, `tau o c = conj o tau` for every embedding,
so `|tau(u/cu)| = 1`.

**Finite-field core (no number field needed) [D].** If `x^{2^g - 1} = rho`
with `ord(rho) = w`, then `ord(x) | w (2^g - 1)`. So `x` is a `p`-th power for
every `p` with `p ∤ w` and `h ∤ g`. The CM lemma is the case
`g = E/2`, `rho = red(u/cu)^{-1}`. Its finite content in the cyclotomic case
is the identity `(1+t)^{2^{E/2}} = 1 + t^{-1} = t^{-1}(1+t)` whenever
`2^{E/2} ≡ -1 (mod ord t)`. (Lean: `lean/B1Forcing.lean`, `twist_forcing`.)

**Subfield form [D].** More generally: if `u^n = zeta v` with `zeta` a root of
unity of order `w`, and `v` a `P`-unit of a subfield `L ⊂ M`, then
`ord(red u) | n w (2^{f(P cap L)} - 1)`. CM is the case `L = M^+`, `n = 2`,
`v = u c(u)`, and it bites only when `P^+` is inert, where
`f(P^+) = E/2`.

### 1.2 Norms when E/h is even: CM carries no information [D]

If `h | E/2`, the constraint `x^{2^{E/2}-1} in mu_w` defines the set
`mu_{w(2^{E/2}-1)}`, and this set contains the whole `p`-Sylow subgroup
`mu_{p^{e_p}} ⊂ F_{2^h}^x ⊂ F_{2^{E/2}}^x`. So the CM constraint says nothing
about `Phi_p(x)`, and hence nothing about the norm to `F_{2^h}` (on
`p`-primary parts, the norm is an isomorphism). Any information there has to
come from somewhere else. The next subsection gives one such source.

### 1.3 The general criterion: Euler-factor forcing (strictly extends CM) [D] using [S]

Every translate `kappa + c` with `kappa, c` nonzero is `c (1 + t)`, where
`t = kappa/c` is a root of unity of odd order `N`. Lift it to the cyclotomic
unit `1 + zeta_N` in `M = Q(zeta_N)`; `1 + zeta_N` is a unit for odd
`N > 1`. Let `G = (Z/N)^x` and `D = <2> ⊂ G` (so `|D| = E`). Call a Dirichlet
character `psi` mod `N` **relevant at level h** if it is even and `psi(2)` has
exact order `h`.

**Theorem A (forcing criterion).** Let `p` be a row prime of level `h` with
`p ∤ N phi(N)`.
(i) `Phi_p(1 + t) = sum over relevant psi` of `Phi~_P(e_psi (1+zeta_N))`;
non-relevant eigencomponents contribute 0.
(ii) For a relevant `psi` of conductor `f`,
`e_psi(1 + zeta_N)` is
`(psi(2)-1) * prod_{l | N, l ∤ f} (1 - psibar(l)) * e_psi(1 - zeta_f)`,
up to a root of unity, and `e_psi(1 - zeta_f) ≠ 0`.
(iii) Hence `kappa + c` is forced at level `h` (for all such `p`) if every
relevant `psi` is **Euler-killed**: some prime `l | N` has `psi_l = 1` and
`psi(l) = 1`. Conversely, if some relevant `psi` is not Euler-killed (for
example one with all local components `psi_l` nontrivial, which I call
**full support**), then no Galois-module identity forces `kappa + c`; its
status is a genuine Kummer/Chebotarev event at each row [H].

*Proof.* `p ∤ |G|`, so `O_M^x ⊗ Z_p[mu]` splits into `psi`-eigenspaces. The
`Z_p`-linear extension of `Phi_p o red_P` satisfies
`Phi(sigma_2 v) = 2 Phi(v)`. On the `psi`-part this reads
`(psi(2) - 2) Phi(e_psi v) = 0` in each residue field at `P | p`, so only
the `psi` with `psi(2) ≡ 2 mod P` survive. Those `psi(2)` have exact order
`h`, and odd `psi` kill units modulo torsion. That is (i). Part (ii) is
`1 + t = sigma_2(1-t)/(1-t)` together with the norm-compatibility/Euler-factor
computation of `sum_a psi(a) log|1 - zeta_N^a|` and `L(1, psi) ≠ 0`
[S: Washington, *Cyclotomic Fields*, Thm 4.9 and §8.1–8.2]. Part (iii)
follows. ∎

**Corollary (prime-power N recovers CM exactly) [D].** For `N = l^n`, every
nontrivial `psi` has `l | f`, so there are no Euler factors. Forcing then
holds iff no relevant `psi` exists, that is, iff `-1 in D` and `h ∤ E/2`.
That is the digest's lemma. When `-1 in D`, an even `psi` satisfies
`psi(2)^{E/2} = 1`. When `-1 ∉ D`, every character of `D` extends to an even
character of `G`.

**Example: Euler forcing beyond CM [D] (check in §1.4).**
`N = 3*61 = 183`, `E = ord_183(2) = 60`, `h = 3`, `p = 7`. Here `-1 ∉ D`
(`-1` is `2^1 mod 3` but `2^{30} mod 61`), so CM does not apply, and
`E/h = 20` is even. Every relevant `psi` has `psi_3 = 1`: a nontrivial `psi_3`
would force `psi_61` odd, giving `psi(2)` 2-part of order 4. Also
`psi(3) = psi_61(2)^6 = 1`, because `3 ≡ 2^6 (mod 61)` and `3 | 6`. So
`1 + t` is a 7th power for every `t` of order 183 in `F_{2^60}`. Elementary
form: `prod_{s in mu_3}(1 + ts) = 1 + t^3`. Then
`Phi(1+t^3) = 2^6 Phi(1+t_61) ≡ Phi(1+t_61)`, and the conjugate `t^{-2^{30}}`
gives `(1 + 2^{30}) Phi(1+t) = 2 Phi(1+t) = 0 (mod 7)`.

### 1.4 Sanity computations [N]

The scripts are scratch files, not part of the repo: `gf.py` and `checks.py`
do `GF(2^n)` arithmetic with a polynomial basis; `classes.py` and
`classes257.py` implement the Theorem A coefficient engine of §3. Each run
takes under 15 s.

- **Arm C, k = 1** (`F_{2^12}`, `p = 7`): `Phi(zeta+1) = 3` and
  `Phi(zeta+s) = 4 = -3` for all four `s in mu_5 \ {1}`, matching the
  prediction `-Phi(zeta+1)` of §3.1. All twelve `c in F_16 \ F_4` give
  non-7th powers.
- **Arm C, k = 2** (`F_{2^36}`, `p = 73`): `Phi(zeta+s) = 3 = 26 Phi(zeta+1)`
  for all four `s`. Here `26 = (2^5-1)/4 mod 73`, since `5 ≡ 2^5 (mod 27)`.
  **Arm D, k = 2** (`F_{2^36}`, `p = 19`): the `F_4` translates give
  `Phi = 0`, and all twelve `F_16 \ F_4` translates are non-19th powers.
- **Arm O, r = 5, a = 1** (`F_{2^20}`): at `p = 31` and `p = 11`,
  `Phi(1+omega xi) = Phi(1+omega^2 xi) = ((2^7-1)/2) Phi(1+xi)`, as
  predicted. At `p = 41` (top level), `Phi(1+xi) = 0` (CM-forced) and
  `Phi(1+omega xi) + Phi(1+omega^2 xi) = 0`.
- **Euler forcing at N = 183** (`F_{2^60}`, `p = 7`): `Phi_7(1+t^a) = 0` for
  all 120 primitive `t^a`. Control: for `u` of order 61,
  `Phi_7(1+u) = 6 ≠ 0`.
- **Lean** (`lean/B1Forcing.lean`, checks clean): `twist_forcing` (any
  monoid), `twist_forcing_field`, `dist3`
  (`(1+t)(1+t omega)(1+t omega^2) = 1+t^3`), and `kummer_lin_zero_iff` (the
  linear step used in §3.1/§4).

## 2. Frobenius / twist ties

**Lemma T1 (affine twist tie) [D].** Let `sigma = Frob^j` and suppose
`sigma(kappa) = zeta kappa + d`, where `zeta` has order prime to `Pi_h` and
`d` is a finite nimber. Then `kappa + c` and
`kappa + zeta^{-1}(sigma(c) + d)` have the same `p`-power status for every
row prime `p` of level `h`. In fact
`Phi_p(kappa + zeta^{-1}(sigma c + d)) = 2^j Phi_p(kappa + c)`.

*Proof.* `sigma(kappa + c) = zeta (kappa + zeta^{-1}(sigma c + d))`, and
`Phi_p(zeta) = 0`. ∎

The lemma includes the Artin–Schreier ties of the Fermat components
(`Frob^j c_n = c_n + sum_{i<j} pi_n^{2^i}`, where `pi_n = c_0...c_{n-1}`).
For example, in arm Z with `Q = {3^b, 2^a}`, `Frob^{2^{a-1}}` (suitably
lifted) fixes `zeta_b` and sends `c_{a-1}` to `c_{a-1}+1`, so `kappa + 1` is
tied to `kappa`.

**Lemma T2 (tie classes) [D].** Forcedness is constant on tie-connected sets.
If a tie chain joins `c*` to a forced `c'`, then `c*` is itself forced. So the
question "does a tie chain connect the predicted translate to a forced one?"
is the same as "is the predicted translate forced?". A fixed point of a tie
with `h ∤ j` is forced: `(kappa+c)^{2^j - 1} = zeta`, then use §1.1.

**Ties inside Theorem A [D].** Write `kappa + c = c(1 + t_c)`. For translates
with the same `N = ord(t_c)`, the ties are exactly `t_c -> t_c^{±2^j}`, the
action of `±D` on `G = (Z/N)^x`. Classes of one `N` correspond to cosets of
`G/±D`, and the ratio of their `Phi`-values is `2^j`, always a unit.
Linear dependence of the `psi`-vectors is strictly finer than ties. It comes
from distribution relations
`prod_{s in mu_l}(1+ts) = 1+t^l` and from Euler factors, and it can link
translates with **different** `N`. The decisive example is arm C, §3.1. In
the abstract, the possible excess values are not tie-class minima but
**new-direction translates**: those `c` whose `psi`-vector leaves the span of
the vectors of all smaller translates (§4.0).

## 3. Per-arm forced and tied translates

For each translate `c`, the engine (`classes.py`) builds the Theorem A vector
`v_c[psi] = [f_psi | N_c] * psibar(u_c) * prod_{l | N_c, l ∤ f_psi}(1 - psi(l))`
over the relevant `psi` mod `L` (one prime `P | p`, i.e. `psi(2) = e^{2 pi i/h}`),
where `t_c = zeta_{N_c}^{u_c}` in a compatible system. The vector is zero
exactly when `c` is forced. Proportional vectors mean the same status at every
row; that covers ties and the explicit relations below. The `c < 16` columns
are proved for all parameters [D]. The `< 256` lists are [N] at the stated
smallest instance and hold for generic `p` (all `p` outside the finite set
where a char-0 linear relation has `P` in a denominator).

| arm (instance) | level `h` | forced `c<16` | classes among `c<16` (same status) | new directions `c<256` [N] |
|---|---|---|---|---|
| C (all k; ran k=1,2) | `3^k` | {0} | {1,...,15}: one class | 1,16,18,24,26,64,65,67 |
| D (all k; ran k=2) | `2*3^k` | {0,1,2,3} | {4,...,15} | 4,16,18,24,26,64,65,67 |
| O r=5 (all a; ran a=1) | `5^a`, `2*5^a` | {0} | {1,...,15} | 1,16,18,20,24,26,28,33 |
| O r=5 | `4*5^a` | {0} ∪ `eps*mu_5` = {0,2,6,7,12,15} (a odd) | the other 10 | 1,16,18,20,24,26,28,30 |
| O r=17 (a=1) | 17, 34, 68 | {0} | [1,14],[2,9],[3,7],[4,6],[5,15],[8,13],[10],[11,12] | 1,2,3,4,5,8 (rank 6 of 8) |
| O r=17 (a=1) | 136 | {0,10} | the same minus [10] | 1,2,3,4,5,8,11 |
| O r=257 (a=1) | `257*2^s`, s=0..4 | {0} | 15 singletons | all of 1..15 new (rank 126–127 of 1024) |
| Z `Q={3^b,4}` (all b; ran b=1) | `4*3^b` | {4,5,6,7} | {0,1,2,3,8,...,15} | 0,16,18,24,26,64,65,67 |

Here `eps` is the `mu_3`-part of `kappa_{5^a}`: it is `2` for odd `a` and `3`
for even `a` [D], since `(kappa_{5^{a+1}})_3 = (kappa_{5^a})_3^2` because
`5^{-1} ≡ 2 (mod 3)`. The engine confirms `eps = 2` at `a = 1`. For `r = 17`
the 289-class is `c = eta = 10`, the `mu_5`-part of `kappa_17` [N].

### 3.1 Proofs of the `c < 16` columns [D]

- **Arm D** (as in Codex, confirmed). `c in F_4`: `kappa + c` is a root of
  unity times `1+t` with `ord t = 3^{k+1}` and `-1 in D`, `E = h`, so it is
  CM-forced. `c in F_16 \ F_4`: `t = zeta/c` is primitive of order
  `N = 5*3^{k+1}` and `G = ±D`, so all twelve are tied. The relevant `psi`
  is `lambda_5 psi_3` of full conductor.
- **Arm C.** `{1,2,3}` are tied, since `2` is a primitive root mod `3^{k+1}`.
  For the twelve `c in F_16 \ F_4`: apply `dist3` with `mu_5`, i.e.
  `prod_{s in mu_5}(zeta+s) = zeta^5+1 = Frob^j(zeta+1)` with
  `5 ≡ 2^j (mod 3^{k+1})`. The four `zeta+s`, `s ≠ 1`, are tied with ratio
  `2^j'`, where `j' ≡ 0 (mod 3^k)`. They have equal `Phi` because every
  relevant `psi` is trivial at 5. Therefore
  `Phi(zeta+s) = ((2^j-1)/4) Phi(zeta+1)`. Since `5 ≡ 2^5 (mod 9)` we get
  `j ≡ 5 (mod 6)`, so `3^k ∤ j` and `2^j ≢ 1 (mod p)`. With
  `kummer_lin_zero_iff`, all fifteen nonzero `c < 16` have the status of
  `kappa+1`. The other `c in F_16\F_4` are `omega^i s`, tied to these. This
  strengthens Codex §7, which needed both classes to fail separately.
- **Arm O, r = 5.** Class I: `c` with `c_3 ≠ eps`, so `N = 3*5^{a+1}`.
  Class II: `c in eps*mu_5`, so `N = 5^{a+1}`. Each class is one `±D`-orbit
  (`G = ±D` for both). Apply `dist3` to `t = kappa`:
  `(1+eps xi)(1+eps^2 xi)(1+xi) = 1+xi^3`, where `3 ≡ 2^{j'} (mod 5^{a+1})`
  with `j'` odd. Also `1+eps^2 xi` is tied to `1+eps xi` with ratio
  `2^{2*5^a}`. At `h = 4*5^a` that ratio is `-1`, consistent with class II
  being CM-forced. At `h in {5^a, 2*5^a}` the ratio is `+1`, so
  `2 Phi(I) = (2^{j'}-1) Phi(II)`. Here `2^{j'} ≢ 1`, because `h | j'` would
  need `j'` even (`h = 2*5^a`) or `3^4 ≡ 1 (mod 5^{a+1})` (`h = 5^a`), and
  both fail. So I and II have the same status at the two lower levels.
- **Arm Z, `Q = {3^b, 4}`** (`kappa = zeta_b + 4`, `E = h = 4*3^b`). For
  `c in {4,5,6,7}`, `kappa + c = zeta_b + (c xor 4)` lies in
  `F_{2^{2*3^b}}`, which has no `p`-part, so these are trivially forced.
  Otherwise `y = c xor 4 in F_16 \ F_4`, `t = zeta_b/y` has order
  `5*3^{b+1}`, and `G = ±D`, so all twelve are tied to `c = 0`.
  Concretely, `Frob^{2*3^b}` takes `4 -> 5`, and `y -> rho y^{-2^j}` gives
  the inverse ties.

## 4. Arm D failure value and exact theorems "m_p in S_X"

### 4.0 Possible-values principle [D]

Fix a level and a prime `P | p`. By Theorem A,
`Phi_p(kappa+c) = <v_c, X(p)>`, where `X(p)` is the vector of unknown Kummer
coordinates `Phi~_P(e_psi(1-zeta_{f_psi}))`, one per relevant `psi`. Suppose
`v_c = sum_{c'<c} a_{c'} v_{c'}` with `P`-integral coefficients `a_{c'}`.
Then "all `c' < c` are `p`-th powers" implies "`c` is a `p`-th power". Hence
`m_p in S_X = { c : v_c not in span(v_{c'} : c' < c) }`. For ties and for the
explicit relations of §3.1 the coefficients are `±2^j`, `(2^j-1)/4` and
`(2^j-1)/2`, all `p`-units, so the statements below that use only those
relations hold for **every** row prime.

### 4.1 Arm D: the parked value m_p = 6 is wrong; Codex is right [D]

The parked notes partitioned `F_16 \ F_4` into orbits under a proper
subgroup of the tie group. Two ingredients were missing: the inversion tie
`1 + t^{-1} = t^{-1}(1+t)`, and the observation that `G = ±D` for
`N = 5*3^{k+1}`. With both, all twelve translates form a single class, as in
Codex §7. So `m_p ≠ 4` implies `m_p ≥ 16`. The value 16 is **structurally
attainable**: `kappa + 16 = 16(1 + zeta/16)` with `ord(zeta/16) = 85*3^{k+1}`.
The relevant character with `psi_5 = lambda_5`, `psi_17 = lambda_17` (the
Legendre symbol mod 17, trivial on `<2>` and even) and `psi_3` of 2-part `+1`
and 3-part of order `3^k` has full support, so it gives a coordinate
independent of the 4-class.

### 4.2 Theorems [D] (all parameters, all row primes)

- **Arm C:** `m_p in {1} ∪ [16, ∞)`. This is new: the 4-class is tied to the
  1-class (§3.1).
- **Arm D:** `m_p in {4} ∪ [16, ∞)`.
- **Arm O, r = 5 (all a, all three levels):** `m_p in {1} ∪ [16, ∞)`.
- **Arm Z, `Q(h) = {3^b, 4}`, `h = 4*3^b`:** `m_p in {0} ∪ [16, ∞)`.

In all four cases a failing row has every translate below 16 a `p`-th power.
The value 16 itself is structurally attainable. In arm C the full-support
character at `c = 16` is `x_5 = x_17 = i`, `(x_3)_2 = -1`.

### 4.3 Sharper lists below 256 [N] (smallest instance, generic p)

In each of these arms, a single prime `P` has exactly 8 relevant `psi`. The
translates below 256 span all 8, so if every listed translate is a `p`-th
power then every `c < 256` is. That gives:

- C (k = 1, 2), D (k = 2), Z `{3,4}` (b = 1):
  `m_p in {pred} ∪ {16,18,24,26,64,65,67} ∪ [256, ∞)`.
- O r=5 (a = 1): `{1} ∪ {16,18,20,24,26,28,33} ∪ [256,∞)` at `h = 5, 10`,
  and `{1} ∪ {16,18,20,24,26,28,30} ∪ [256,∞)` at `h = 20`.

The count 8 = `[G : ±D]` for `N = 85*3^{k+1}` is independent of `k` [D]. That
the lists are independent of `k` is [N] for `k = 1, 2` only.

### 4.4 Contrast: larger `[G : ±D]` gives small failure values [N]

- **O, r = 17, a = 1:** `m_p in {1,2,3,4,5,8} ∪ [256,∞)` at
  `h in {17, 34, 68}`, and `{1,2,3,4,5,8,11} ∪ [256,∞)` at `h = 136`. A
  failing row may have `m_p = 2`.
- **O, r = 257:** every `c < 16` is a new direction, so there are no
  constraints below 16.

The "failure implies `m_p ≥ 16`" phenomenon belongs exactly to the arms
where `G = ±D` on `F_16`-translates.

## 5. Can forcing hit a predicted translate? No, in every explicit family

**Theorem 5.1 [D].** At every row level, the predicted translate admits a
relevant character that is not Euler-killed. Except for arm O r=5 at the two
lower levels (item 3), that character has full support. So by Theorem A and Lemma T2 it is not structurally forced, and no
tie chain or distribution/Euler relation links it to a forced translate.
This holds in:

1. **Arm C** (`1 + zeta_k`, `N = 3^{k+1}`): `h = 3^k` divides `E/2`, so a
   nontrivial relevant `psi` exists, and for prime-power `N` it has no Euler
   factor.
2. **Arm D** (`zeta_k + 4`, `N = 5*3^{k+1}`): `psi_D = lambda_5 psi_3`, with
   full conductor `N`.
3. **Arm O, r = 5** (`N = 3*5^{a+1}`): at `h = 4*5^a`, `lambda_3 psi_5` with
   full conductor. At `h in {5^a, 2*5^a}` every relevant `psi` is trivial at
   3, but `psi(3) = psi_5(2)^{j'} ≠ 1` (`j'` odd, `3^4 ≢ 1 (mod 25)`).
4. **Arm O, r = F_n, n = 2, 3, 4** (`N = F_1 ... F_{n-1} F_n^{a+1}`, using
   `ord(c_n) = F_1...F_n`). The components are `x_i = psi_{F_i}(2)` and
   `y = 2`-part of `psi_r(2)`, at levels `h = F_n^a 2^j`, `0 ≤ j ≤ n+1`.
   For `2 ≤ i ≤ n-1` take `x_i = 1` with `psi_i` nontrivial on
   `G_i/D_i ≠ 1`; this needs `2^{i+1} < 2^{2^i}`. For `j ≤ n` take
   `x_1 = -1` and `y = -tau_2`, where `tau_2` is the order-`2^j` target
   (so `y = -1, 1` for `j = 0, 1`, and `y` has order `2^j ≤ 2^n` for
   `j ≥ 2`; then `y^{2^n} = 1`). For `j = n+1` take `x_1 = ±i` and `y` of
   order `2^{n+1}`. `psi_r` is nontrivial through its `F_n`-part of order
   `F_n^a`. Parities multiply to 1 and
   every component is nontrivial. The same pattern covers `r = 65537`.
5. **Arm O at r = 7 and at every arm-C-derived r** (`alpha_r = 1+zeta_k`,
   `N = 3^{k+1} m r^{e+a}`, all `l | mr` with `ord_l(2) | 3^k` odd, so
   `-1 ∉ D_l`). Take `psi_l` odd with `x_l = 1` for `l | m`. Let
   `x_3 ≠ 1` carry the 2-part of the target and a nontrivial 3-part,
   compensating with `x_r in mu_{3^k r^a}` so that `psi(2)` has order
   `h = r^a s`. If `3 ∤ s`, put a cube root `nu` on `x_3` and `nu^{-1}` on
   `x_r`. Fix parity with the free `psi_r(-1)`. This is checked by hand for `r = 7` at all four levels;
   the general case is a sketch.
6. **Arm Z, `Q = {3^b, 2^a}`** (`a ≥ 2`; uses CHS `ord(c_n) | F_1...F_n`).
   Among Fermat-factor primes, `G_l = D_l` only for `l = 5`. Take
   `x_{F_{a-1}}` of order `2^a`, `x_5 = -1` if `5 | N`, and `(x_3)_2 = -1`.
   **`{3^b, 5^c}`**: the relevant `psi` has full conductor at all three
   levels `h = 3^b 5^c 2^{0,1,2}`. **`{5^c, 2^a}`**: same pattern as 6.

**Corollary 5.2 (route closed, exact obstruction) [D].** In these families
the zero-vector translates are exactly the ones forced by degree, CM or
Euler factors (§3). The 0/1/4 value is in every case **the least translate
whose Theorem A vector is nonzero**. So inside these families the rule is
equivalent to:

> the first structurally unforced translate is never accidentally a `p`-th
> power.

A failure is therefore an accidental vanishing `<v_{c*}, X(p)> = 0`. That is
a Chebotarev/Kummer event of Theorem C type: a `psi`-part of a class group,
or complete splitting of 2 in `K(mu_p, E^{1/p})`. It is never a
Galois-module identity. Global forcing cannot refute the rule.

**Near misses [D].** Euler forcing comes within one congruence of biting.
(a) **On the predicted class:** in arm O r=5 at `h in {5^a, 2*5^a}`, every
relevant character of the class `{1,3,...}` (`N = 3*5^{a+1}`) is trivial at
3. Forcing of `kappa+1` would need `psi(3) = 1`, i.e. `h | j'` with
`3 ≡ 2^{j'} (mod 5^{a+1})`. That fails because `j'` is odd (level
`2*5^a`) and because `3^4 ≢ 1 (mod 25)` (level `5^a`). Both are fixed
congruences, so no member of the family escapes in the other direction.
(b) **On a non-predicted class:** the arm C 4-class would be forced, not
tied, if `5 in <2^3> = {±1} (mod 9)`. In every other explicit family the
predicted translate carries a full-support character, so no Euler factor
can touch it.

**Beyond the explicit families [H].** Two families fall outside the
two-term cyclotomic lift: arm Z with three or more components, and
components of non-explicit order (general `alpha_r`). Then `kappa_h` is a sum
of at least three roots of unity, not a root of unity times a cyclotomic
unit, and I know of no structural mechanism that could force `T_h`. Any
forcing of a predicted translate would also be uniform across a family,
including its smallest instance. Many of these instances have verified
rows `p ≤ 72481` (for example C: 7, 73; D: 19; O5: 31, 11, 41;
Z`{3,4}`: 13), which independently rules out family-wide forcing there. Under this method the
literal Conway ancestry gives no certificate; no chain exists.

## 6. Summary

**Status: route closed, with partial theorems.** No disproof was found. The
global-forcing route is closed in every family where `kappa_h + c*` has a
two-term root-of-unity form, and the obstruction is exact: the predicted
translate always carries a relevant character that is not Euler-killed. It
has full support except in arm O r=5 at the lower levels, where it is saved
by the fixed congruences `j'` odd and `3^4 ≢ 1 (mod 25)`.

Headline results:

- [D] **Theorem A (Euler-factor forcing criterion).** It contains the CM
  lemma as the prime-power case and is strictly stronger: `N = 183`,
  `h = 3`, where CM is absent and `E/h = 20` [N]. The CM lemma needs `P^+`
  inert, and gives nothing when `E/h` is even.
- [D] **Ties are classes of `±D`.** Linear dependence of the `psi`-vectors is
  finer, and the possible excess values are the new-direction translates.
- [D] **Failure values:** C: `m_p in {1} ∪ [16,∞)` (new); D:
  `{4} ∪ [16,∞)` (confirms Codex, refutes the parked 6); O5:
  `{1} ∪ [16,∞)`; Z`{3^b,4}`: `{0} ∪ [16,∞)`. Sharper lists below 256 are
  [N].
- [D] **Theorem 5.1:** predicted translates are never structurally forced
  in arms C, D, O (r = 5, 17, 257, 65537, 7, arm-C-derived r) and Z
  (`{3^b,2^a}`, `{3^b,5^c}`, `{5^c,2^a}`). In these families the rule equals
  "the first unforced translate is not accidentally a `p`-th power".

**Best next step.** Use Theorem A plus the Codex/Gras template to write the
Theorem C-type row criterion for every explicit family at once. For
example, in arm O r=5 at `h in {5^a, 2*5^a}`, the row status equals that of
`1 + xi` with `ord xi = 5^{a+1}`, a prime-power-conductor unit of
`Q(zeta_{5^{a+1}})^+`, so Washington Thm 8.2 applies directly. That turns
every explicit arm into a class-group/splitting statement. A disproof
attempt should then aim at those Chebotarev events (for example `psi`-parts
of `Cl(Q(zeta_N)^+)[p]` for the listed `psi`), not at forcing. Separately,
the lists in §4.3 give engines a free consistency check: any computed
failure value must lie in `S_X`.
