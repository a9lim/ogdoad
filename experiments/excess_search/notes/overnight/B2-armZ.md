# B2 — arm Z: two-component criterion, selection, and three-component reciprocity

Tags: [S] standard/cited, [D] derived here with proof, [N] named small
computation, [H] heuristic. No rows were run beyond the named sanity checks.

## 0. Status

Done (all sections). Headlines:
- **Prop 1 [D]**: a two-component row is exactly "the selected prime of
  `Q(zeta_N)^+` over 2 does not make the real cyclotomic unit
  `eps = zeta_N + zeta_N^{-1}` a `p`-th power"; forced failure iff `h ∤ f^+`
  (generalized CM lemma, plus a cancellation branch).
- **Theorem A [D, using S]**: the row is the value at Conway's coset of an
  `m`-point function, `m = phi(N)/(2 f^+)`, whose `psi`-Fourier coefficients
  vanish by Euler factor, by `p | |A_psi|` (Gras/Mazur–Wiles), or by
  reciprocity; only the coset survives of the selection.
- **Theorem B [D, using S]**: `m = 1` exactly for `h = 4·3^k` (`N = 5·3^{k+1}`)
  and `h ∈ {1,2,4}·3^b5^c` (`N = 3^{b+1}5^{c+1}`): 2 is inert in `K^+`, the
  selection disappears, and the row criterion is Theorem C's shape — arm C's
  twins (`T_h`'s norm = the global norm to the degree-`h` subfield).
- **§4 [D+N]**: for `h = 2^a 3^b`, `a >= 3`, `m = 8, 2^10, 2^25, ...`; at `h = 24`
  the 8 primes over 2 give 8 different symbols — the selection is genuine.
- **§5 [D; 5.3 sketch]**: three components → S-units; primes over 2 dividing
  the lift are invisible; odd characters enter via Gauss sums of primes over
  `N(x)`; `K`- and `Q(zeta_p)`-rational reciprocity is vacuous (Lemma 5.2);
  mixed Gauss sums relocate the selection to wild symbols at `p`. No
  Chebotarev-type (horizontal) condition arises.
- **§6 [D]**: no forced outcome for `{2^a, r^c}` pairs or symmetric-free
  three-component sets; no infinite family proved.

## 1. Two components: reduction to a real cyclotomic unit

Notation. `Q(h) = {q1, q2}`, `z_i = kappa_{q_i}` in `F = F_{2^E}`, `E = d(kappa_h)`
(= `dsum(Q)` in every case below), `n_i = ord(z_i)` (odd). Put
`rho = z2/z1`, `N = ord(rho)` (odd, > 1), `t = rho^{(N+1)/2}` (so `t^2 = rho`,
`ord t = N`), `f = ord_N(2)`, and `ebar = t + t^{-1}`.

**Lemma 1.1 (two-component factorization) [D].** `kappa_h = z1 t ebar`. If `p`
is an odd prime with `p ∤ n1 N`, then `kappa_h` is a `p`-th power in `F` iff
`ebar` is.
*Proof.* `z1 t (t + t^{-1}) = z1 (t^2 + 1) = z1 (1 + rho) = z1 + z2`. The factor
`z1 t` has order dividing `lcm(n1, N)`, prime to `p`, and in a finite abelian
group an element of order prime to `p` is a `p`-th power (`y = (y^u)^p` with
`u p ≡ 1 mod ord y`; Lean `B2ArmZ.lean`, `pow_coprime_is_pth_power`). ∎

The hypothesis `p ∤ n1 n2` holds whenever `h ∤ d(z1)` and `h ∤ d(z2)` (a row
prime has `ord_p 2 = h`); it holds in every family below.

**Lift [D/S].** `K = Q(zeta_N)`, `K^+` its real subfield, `tau = zeta_N`,
`eps = tau + tau^{-1} = tau^{-1}(1-tau^4)/(1-tau^2)`, a unit of `K^+`
[S: ratios `(1-zeta^a)/(1-zeta^b)` with `a, b` prime to `N` are units]. Since
`Phi_N(t) = 0` in `F`, `zeta_N -> t` defines `Z[zeta_N] -> F` whose kernel is a
prime `P | 2`. Thus `ebar = red_P(eps)`, and the **selected prime** is
`p_C := P ∩ K^+`. Replacing `t` by `t^s` (`s ∈ (Z/N)^x`) replaces `P` by
`sigma_s^{-1} P`; so the Conway embedding's whole contribution is the choice of
one prime of `K^+` over 2. `G = (Z/N)^x`, `D = <2>` (order `f`), `G^+ = G/±1`,
`D^+` = image of `D`, `f^+ = |D^+|` (= `f/2` if `-1 ∈ <2>`, else `f`), and
`m := [G^+ : D^+] = phi(N)/(2 f^+)` = number of primes of `K^+` over 2; each has
residue field `F_{2^{f^+}}` and `ebar ∈ F_{2^{f^+}}`.

**Lemma 1.2 (descent of the test) [D].** For `x ∈ F_{2^e} ⊆ F_{2^E}` and odd
`p`: if `p ∤ 2^e - 1` then `x` is a `p`-th power in `F_{2^E}`; if `p | 2^e - 1`
and `p ∤ E/e`, then `x` is a `p`-th power in `F_{2^E}` iff it is one in `F_{2^e}`.
*Proof.* `x^{(2^E-1)/p} = (x^{(2^e-1)/p})^S` with `S = (2^E-1)/(2^e-1) ≡ E/e
(mod 2^e - 1)`, hence `mod p`; the first case is Lemma 1.1's group fact. ∎

**Proposition 1 (two-component row = selected unit reduction) [D].** Let `p`
be a row prime (`ord_p 2 = h`) with `p ∤ n1 N (E/f^+)`. Then
`m_p = 0  <=>  h | f^+  and  red_{p_C}(eps) ∉ (k_{p_C}^x)^p`, `k_{p_C} = F_{2^{f^+}}`.
In particular **if `h ∤ f^+` the row fails (forced `m_p >= 1`)**. This is the
generalized CM lemma: the digest's lemma is the sub-case `-1 ∈ <2 mod N>`
(`f^+ = f/2`, `E/h` odd); the other sub-case is `h ∤ f` (`rho` lives in a
field too small to see `p`). Both are decidable from `(N, h)` alone.
*Proof.* Lemmas 1.1, 1.2 with `e = f^+`. ∎

Family data [N, `scratchpad/b2/fam.py`, orders via `nim.py`/sympy]: in all of
`h = 4·3^k` (k ≤ 7), `h ∈ {1,2,4}·3^b 5^c` (b ≤ 3, c ≤ 2), `h = 2^a 3^b`
(a ≤ 5, b ≤ 2), `h = 9·7`, one has `-1 ∉ <2 mod N>` and `f^+ = f = E`, so no
forcing. `m = 1` for `h = 4·3^k` (`N = 5·3^{k+1}`) and for
`h ∈ {3^b5^c, 2·3^b5^c, 4·3^b5^c}` (`N = 3^{b+1}5^{c+1}`, `E = 4·3^b5^c`);
`m = 8` for `h = 8·3^b` (`N = 85·3^{b+1}`), `m = 2^10` for `h = 16·3^b`,
`m = 2^25` for `h = 32·3^b`; `m = 3` for `h = 9·7` (`N = 27·49`).
The `m = 1` facts hold for all `k` (resp. all `b, c`) [D]: 2 is a primitive
root mod every `3^j` and mod every `5^j` [S], so `f = lcm(2·3^k, 4) = 4·3^k`
(resp. `lcm(2·3^b, 4·5^c)`), `phi(N) = 2f`, and `-1 ∈ <2>` would need
`2^j ≡ -1` mod `5` (j ≡ 2 mod 4) and mod `3^{k+1}` (j odd): impossible.

## 2. The selection: what survives (Theorem A)

Hypotheses (H): `p` a row prime, `h | f^+`, `p ∤ 2 N phi(N) (E/f^+)`.
Let `chi : D^+ -> F_p^x`, `Frob_2 -> 2` (well defined since `h | f^+`), and
`Psi = {psi : G^+ -> Fbar_p^x : psi|_{D^+} = chi}`; `|Psi| = m`, all `psi ∈ Psi`
nontrivial. Let `U = E_{K^+} ⊗ Fbar_p` (additive). [S: Dirichlet–Herbrand,
`p ∤ |G^+|`, `p ∤ |mu_K|`] `U ≅ Fbar_p[G^+]/(norm)`, so each `U[psi]`,
`psi ≠ 1`, is a line. Also `E_K ⊗ Fbar_p = U` (index `Q ≤ 2`, `p` odd), and
complex conjugation acts trivially on it (Kronecker: `c(u)/u ∈ mu_K`).
Write `R_p : U -> Fbar_p` for the `Fbar_p`-linear extension of
`u -> class of red_p(u)` in `k_p^x/p ≅ F_p`.

**Theorem A (selected Fourier sum) [D, using S].** Under (H):
1. `R_p(sigma_2 u) = 2 R_p(u)`, hence `R_p` kills every `U[psi']` with
   `psi' ∉ Psi`, and `R_p(u) = sum_{psi ∈ Psi} lambda_psi(e_psi u)` where
   `lambda_psi = R_p|_{U[psi]}` is either `0` or an isomorphism.
2. Transport: `lambda_psi^{(g p)} = psi(g)^{-1} lambda_psi^{(p)}` for `g ∈ G^+`;
   so whether `lambda_psi = 0` does not depend on the prime, and
   `R_{g p_C}(eps) = sum_psi psi(g)^{-1} a_psi`, `a_psi := lambda_psi(e_psi eps)`.
   **The row is the value at the Conway coset of a function on the `m`-point
   set `G^+/D^+` whose Fourier coefficients are `a_psi`.** `m_p = 0` iff
   `sum_{psi ∈ Psi} a_psi ≠ 0`.
3. Coordinates of `eps`: `e_psi eps = 2 e_psi(1 - zeta_N)` (from
   `eps = tau^{-1} (sigma_4 - sigma_2)(1 - tau)` and `psi(2) = 2`; uses that
   `1 - zeta_N` is a unit, `N` not a prime power, true in all families), and by
   the norm relation [S: `N_{Q(zeta_N)/Q(zeta_M)}(1-zeta_N) = (1-zeta_M)^{prod_{l | N, l ∤ M}(1 - sigma_l^{-1})}`]
   `e_psi(1-zeta_N) = [K : Q(zeta_{f_psi})]^{-1} prod_{l | N, l ∤ f_psi} (1 - psi(l)^{-1}) e_psi(1 - zeta_{f_psi})`.
   `e_psi(1 - zeta_{f_psi})` spans the `psi`-part of Sinnott's cyclotomic units
   [S, Sinnott 1980], and its vanishing in `U[psi]` is `p | |A_psi|`, the
   `psi`-part of the `p`-class group of `K^+` [S: Gras's conjecture, a theorem of
   Mazur–Wiles 1984 (also Kolyvagin–Rubin) for `p ∤ [K^+:Q]`].
   Hence `a_psi = 0` iff (Euler) `psi(l) = 1` for some `l | N` with `l ∤ f_psi`,
   or (class) `p | |A_psi|`, or (reciprocity) `lambda_psi = 0`, i.e. the `psi`-line
   of `E/E^p` reduces to `p`-th powers at 2, i.e. the primes of `K^+` over 2
   split completely in `K^+(mu_p, eta_psi^{1/p})`.
*Proof.* (1) `red(sigma_2 x) = red(x)^2`; the eigen-decomposition is
semisimple since `p ∤ |G^+|`; a linear map from a line is 0 or injective.
(2) `red_{g p}(g x)` is the image of `red_p(x)` under the field isomorphism
`g : k_p -> k_{gp}`, which preserves `p`-th powers, and `g e_psi u = psi(g) e_psi u`.
(3) is the cited norm relation applied inside `e_psi`
(`e_psi x = [K:K']^{-1} e_psi N_{K/K'} x` for `psi` trivial on `Gal(K/K')`). ∎

**What survives of the selection.** Exactly the coset `g_C ∈ G^+/D^+`, i.e.
which of the `m` primes of `K^+` over 2 is the kernel of `zeta_N -> t`.
Nothing finer (the within-coset choice is a Frobenius twist, invisible to
`p`-th powers) and nothing coarser: for `m > 1` the row is a genuine `m`-term
sum, not governed by any single `psi`. The G-symmetric statements bracket it:
- all `a_psi = 0` (e.g. every `lambda_psi = 0`) ⇒ the row fails at every prime
  over 2, Conway's included;
- exactly one `a_psi ≠ 0` ⇒ the row holds at every prime over 2.
In between, the selected row is a codimension-one condition
(`e_chi eps ∉ H_{p_C}`, `H_p = ker R_p ∩ e_chi(E/E^p)`, a hyperplane of the
`m`-dimensional `chi`-isotypic space), which is the `1/p`-probability event the
random model charges. This is Theorem C with `1` replaced by `m`; for `m = 1`
it *is* Theorem C's shape (Section 3).

## 3. The m = 1 families: Theorem C shape (Theorem B)

**Theorem B [D, using S].** Let `(h, N, E)` be either
(i) `h = 4·3^k`, `k >= 1`, `kappa_h = 4 + zeta_k`, `N = 5·3^{k+1}`, `E = h`; or
(ii) `h ∈ {3^b5^c, 2·3^b5^c, 4·3^b5^c}`, `b, c >= 1`, `kappa_h = zeta_b + kappa_{5^c}`
(`kappa_{5^c} = 2 xi`, `ord xi = 5^{c+1}`), `N = 3^{b+1}5^{c+1}`, `E = 4·3^b5^c`.
Then `K^+ = Q(zeta_N)^+` is cyclic of degree `E` generated by `Frob_2`, **2 is
inert in `K^+`**, and `m = 1`. Let `K_h ⊆ K^+` be the subfield of degree `h`,
`psi : Gal(K_h/Q) -> F_p^x` the faithful character with `psi(Frob_2) = 2`, and
`eta_h = N_{K^+/K_h}(eps)`. Then `f_psi = N`, and for every row prime `p`
(`ord_p 2 = h`):

`m_p ≠ 0  <=>  p | |A(K_h)_psi|   or   red_2(E(K_h)_psi) ⊆ (F_{2^h}^x)^p`,

the second alternative meaning that `(2)` splits completely in
`K_h(mu_p, eta^{1/p})` for a unit `eta` spanning the `psi`-line of `E/E^p`.
Moreover `red_2(eta_h) = N_{F_{2^E}/F_{2^h}}(ebar)`, so `T_h = (root of unity of
order prime to p)·red_2(eta_h)`: **the finite-field norm in the definition of
`T_h` is the global norm `K^+ -> K_h`** (inertness makes reduction commute with
the norm).
*Proof.* §1 family data: `phi(N) = 2E`, `-1 ∉ <2>`, so `D = <2>` maps
isomorphically onto `G^+`, i.e. `G^+ = <Frob_2>` and 2 is inert; `m = 1`.
`chi(Frob_2) = 2` has order `h`, so `Psi = {psi}` with kernel `<Frob_2^h>`,
fixed field `K_h`. Conductor: `K_h` contains the degree-`3^b` (resp. `3^k`)
subfield of conductor `3^{b+1}` and, in (ii), the degree-`5^c` subfield of
conductor `5^{c+1}`; in (i) with `E = h`, `psi` is faithful on `Gal(K^+/Q)`
and `K^+` has conductor `N` (it contains `Q(sqrt5)` and `Q(zeta_{3^{k+1}})^+`).
So `f_psi = N`, no Euler factor occurs in Theorem A(3), and
`e_psi eps = 2 e_psi(1 - zeta_N)` spans the `psi`-part of the cyclotomic units;
its vanishing is `p | |A_psi|`, and `A(K^+)_psi = A(K_h)_psi` since
`p ∤ [K^+:K_h]`. With one prime over 2, Theorem A(2) reduces to `a_psi ≠ 0`.
Norm: 2 inert in `K^+` means `Gal(K^+/K_h)` maps onto `Gal(F_{2^E}/F_{2^h})`, so
`red(N x) = N(red x)`; `kappa_h = z1 t ebar` (Lemma 1.1) and `N(z1 t)` has order
prime to `p`. ∎

**Corollary B1 (selection-free Dickson form) [D].** Arm `Z` at `h = 4·3^k` is
equivalent to: `Pi_h | ord(t + t^{-1})` for one, equivalently every, primitive
`5·3^{k+1}`-th root of unity `t ∈ F_{2^h}`. Arm `Z` at
`h ∈ {1,2,4}·3^b5^c` is equivalent to `Pi_h | ord(N_{F_{2^E}/F_{2^h}}(t + t^{-1}))`
for every primitive `3^{b+1}5^{c+1}`-th root `t`. ("Every" because
`(Z/N)^x = <2, -1>`: all choices of `t` are Frobenius conjugates up to inversion.)
Compare arm C: `gamma_k = zeta + zeta^{-1}`, `ord zeta = 3^{k+1}`, primitive in
`F_{2^{3^k}}`. These families are **arm C's twins**: a Theorem-C criterion in a
layer of a cyclotomic `Z_3`- (resp. `Z_3 × Z_5`-) tower over `Q(zeta_15)^+`
(resp. `Q`), with 2 inert, `psi` new at the top layer, and `p ≡ 1 mod h`.

**Why the tower does not help (obstruction) [S as recalled + D].**
Washington (1978) bounds the `p`-part of class numbers in a cyclotomic
`Z_l`-tower for *fixed* `p ≠ l`; Horie-type results kill `p`-class groups in the
whole tower for `p` of large order mod `l^2`. Both work because for such `p` a
new `psi`-component is a module over a ring with large residue field, so a
nonzero `A_psi` is large and can be excluded. Row primes have `p ≡ 1 mod h`:
`psi` is `F_p`-valued, the residue degree is 1, and `p` grows with the layer.
The mechanism is unavailable exactly at the selected primes; likewise for the
reciprocity alternative. So Theorem B is as open as arm C, and heuristically
true by the same convergent sum [H] (one- or two-parameter family of `h`).

## 4. h = 2^a 3^b, a >= 3: the selection is genuine

Here `z1 = zeta_b` (order `3^{b+1}`), `z2 = c_{a-1}` (order `n2 | 2^{2^a}-1`,
divisible by a prime of `F_{a-1}` since `d(c_{a-1}) = 2^a`), `E = 2^a 3^b = f = f^+`
(§1), `N = 3^{b+1}·n2'` (`n2'` the prime-to-3 part of `n2`), and
`m = phi(n2')/2^{a-1}`: `m = 8` (a = 3), `2^10` (a = 4), `2^25` (a = 5) [N].

**Conductors [D].** For `psi ∈ Psi`, a prime `l | N` can be absent from `f_psi`
only if `chi` is trivial on `D ∩ I_l`, where `I_l = (Z/l^e)^x` and
`D ∩ I_l = <sigma_2^{ord_{N/l^e}(2)}>`.
- `l = 3`: `ord_{N/3^{b+1}}(2) = 2^a`, `chi(sigma_2^{2^a}) = 2^{2^a} ≢ 1 (mod p)`
  since `h ∤ 2^a`: so `3 | f_psi` for all `psi`.
- `l | F_{a-1}`: if `l` is the only such prime in `N` (true for `a <= 5`, as
  `F_1..F_4` are prime), `ord_{N/l^e}(2) = h/2` and `chi = 2^{h/2} = -1`: so
  `l | f_psi` for all `psi`. (If several primes of `F_{a-1}` divide `N`, each
  behaves like an intermediate prime below.)
- "intermediate" `l | F_j`, `1 <= j <= a-2` (e.g. `l = 5`): `D ∩ I_l` can be
  trivial, and then exactly a fraction `1/[I_l^+ D^+ : D^+]` of `Psi` has
  `l ∤ f_psi`; for these, `a_psi` carries the Euler factor `1 - psi(l)^{-1}`.
So Euler factors can kill only a proper subset of `Psi` (a = 3: 2 of 8, those
with `5 ∤ f_psi`, killed iff `psi(5) = 1`; a = 4: at most `1/4 + 1/16` of `Psi`).
**No forced outcome** in this family [D for a = 3, 4; the general-a union
bound is not checked].

**Check at h = 24 [N, `scratchpad/b2/four.py`]** (`kappa = 16 + omega`, `N = 765`,
`p = 241`, the only row prime): Lemma 1.1's identity holds; `ebar` is not a
241st power (row holds, as known); `F(s) := dlog_{241} red(t^s + t^{-s})`
satisfies `F(2s) = 2F(s)`, `F(-s) = F(s)`; on the 8 cosets (Conway's normalized
to 1) `F = 1, 170, 67, 218, 162, 153, 157, 213` — **eight different symbols at
the eight primes of `K^+` over 2**, so the row really depends on which prime is
selected. The 8 Fourier coefficients `a_psi` are all nonzero
(`213, 34, 214, 14, 218, 15, 109, 49`), and `sum a_psi = |G|·F(1)` (=143 mod 241)
as Theorem A(2) says. Exactly 2 of the 8 `psi` are trivial on `I_5`, none on
`I_17`, as the conductor analysis predicts; for those two `psi(5) ∈ {65, 176} ≠ 1`,
so Theorem A(3) predicts no Euler zero, consistent with `a_psi ≠ 0`. (This
checks the bookkeeping, not a vanishing case.)

## 5. Three or more components: S-units, Gauss sums, reciprocity

Let `Q(h) = {q1, q2, q3, ...}`, `kappa_h = z1 x̄`, `x̄ = 1 + rho2 + rho3 (+...)`,
`rho_i = z_i/z1 = t^{e_i}`, `N = ord t`; lift `x = 1 + tau^{e2} + tau^{e3} ∈ O_K`,
`K = Q(zeta_N)`. Then `x` is in general **not a unit and not real**: it is a
unit times a root of unity only in "symmetric" configurations
(`rho3 = rho2^{±1}`, `rho2 = rho3^2`, ..., where `1 + zeta + zeta^2` or
`1 + zeta + zeta^{-1}` is a cyclotomic unit), and those are excluded by
private prime powers (Lemma 6.0): no relation `z1 z3 = z2^2`, `z2 z3 = z1^2`, ...
holds [D]. Lemma 1.1/1.2 still apply (`p ∤ n1 N`), so the row is
`chi_P(x) := red_P(x)^{(2^f-1)/p} ≠ 1` (with the same descent).

**Ideal factorization [D].** `(x) = prod v^{v(x)}` with `v` over primes of `K`
dividing `N_{K/Q}(x)` (`|N(x)| <= 3^{phi(N)}`) and possibly *other* primes over
2 (a Galois-conjugate triple can sum to zero in `F_{2^f}`; never the selected
`P`, since `kappa_h ≠ 0`). Let `S` be the `G`-saturation of this support.

**Theorem A_S (S-unit version) [D, using S].** Replace `E` by `O_S^x` in
Theorem A, and `Psi` by `Psi_G` = the `2m` characters of `G` extending `chi`
(`m` even, `m` odd). Then `R_P(x) = sum_{psi ∈ Psi_G} lambda_psi(e_psi x)`, where
`U_S[psi] = U[psi] ⊕ (valuation part)[psi]` and the valuation part of `psi` is
nonzero only if `psi` is trivial on the decomposition group `D_v` of some
`v ∈ S`. Two consequences:
1. **Primes over 2 dividing `x` are invisible:** for `v | 2`, `D_v = D` and
   `psi|_D = chi ≠ 1`. Only odd primes `l | N(x)` with `chi|_{D ∩ D_l} = 1`
   feed the row.
2. **Odd characters enter.** For odd `psi` the line `U_S[psi]` is
   `(ideal (x))_psi` up to the class constraint; when `p ∤ B_{1,psi^{-1}}`
   (`A^-_psi = 0`, Mazur–Wiles [S]) it is spanned by `e_psi` of a Gauss sum
   `G_v` attached to a prime `v | l` (Stickelberger [S]: `(G_v^N) = v^{N theta}`).
   So `lambda_psi(e_psi x) = (psi-coefficient of (x)) · (Stickelberger factor)^{-1}
   · lambda_psi(e_psi G_v)`: the reduction **at the selected prime over 2** of a
   Gauss sum of the residue field of a prime dividing `x`.
So the three-component row is: unit part (Theorem A) + Gauss-sum part, each a
selected reduction. No new forcing appears (consequence 1 removes the only
candidates that see `D` directly).

**Lemma 5.2 (blind moduli) [D].** Let `L = K(mu_p)`, `Gal(L/Q) = G × (Z/p)^x`,
`Delta = <(sigma_2, 2)>` the decomposition group of `P_1 | P`. With `T` a
transversal of `G/D`, `T × (Z/p)^x` is a transversal of `Gal(L/Q)/Delta`, and
for `x ∈ K^x` prime to 2 and an ideal `I = prod (rho P_1)^{n(rho)}` over 2,
`(x/I)_p = prod_{tau ∈ T} chi_P(tau^{-1} x)^{c_tau}`, `c_tau = sum_{a} a·n(tau, a)`.
If `I` comes from `K` (`n` depends on `tau` only) or from `Q(zeta_p)` (`n` depends
on `a` only and `n(2a) = n(a)`, e.g. any Gauss sum of a `p`-power-order
character on `k_P`), then every `c_tau ≡ 0 (mod p)` and `(x/I)_p = 1`.
*Proof.* `(x/rho P_1) = rho((rho^{-1}x/P_1)) = chi_P(tau^{-1}x)^a`. Then
`sum_a a = 0`, resp. `sum_{a ∈ a0<2>} a = a0 (2^h - 1) ≡ 0`. ∎
So power reciprocity against `K`- or `Q(zeta_p)`-rational generators is
vacuous at the selected prime — the arm-Z instance of rank-one saturation.

**Remark 5.3 (mixed Gauss sums restate) [sketch; sign/normalization
conventions not checked].** For the Gauss sum `g` of a character of order `Np`
on `k_P` (`g ∈ L`), `n(tau, a)` is the Stickelberger weight
`sum_{j<f} <2^j b/(Np)>` of `b = (tau, a)`, not of product form, so the `c_tau`
are Stickelberger first moments and `(x/g)_p` is a *different* weighted product
over the primes over 2. Power reciprocity [S] then gives
`(x/g)_p = (g/x)_p · prod_{v | p} (x, g)_v^{±1}`: symbols of `g` at the primes
dividing `x`, and wild pairings at `p`. In the `m = 1` families `x = eps` is a
unit, `(g/eps) = 1`, and `(x/g) = chi_P(eps)^c` with one constant `c` (expected
to be a unit times a generalized Bernoulli number `B_{1, psi omega^{-1}}`, the
mirror (`omega psi^{-1}`) minus-part, by Spiegelung — [H]); when `c ≢ 0` the row
becomes `prod_{v|p} (eps, g)_v ≠ 1`: a **wild, Wieferich-type condition at `p`**
on the cyclotomic unit (`eps` enters through its Fermat quotient
`(eps^{p^{f_p}-1} - 1)/p` in an Artin–Hasse formula [H]). For three components
the `(g/v)_p`, `v | x`, are Gauss sums of `F_{2^f}` reduced into `F_v` and
tested for `p`-th powers.
**Is it horizontal? No [D, structural].** The primes `v | x`, the radicand `g`,
and `p` are all pinned by `h`; there is no family over which Chebotarev
averages, and as `h` moves all three move. Reciprocity relocates the selection
(2 → `p` and the primes over `N(x)`), it does not remove it.

## 6. Forced outcomes and provable families

**Lemma 6.0 (private prime powers) [D].** All prime factors of `b_r` are `< r`
(induction on `r`: `b_r = lcm(dsum Q(f(r)), 2^j)` with `f(r) < r`). Hence for
distinct `q_i, q_j ∈ Q(h)`, `q_i ∤ d(z_j)` (if `r_j < r_i` because `r_i` exceeds
every prime of `q_j b_{r_j}`; if `r_j > r_i` by the selection rule). Since
`q_i | d(z_i) = lcm_{l^e || n_i} ord_{l^e}(2)`, some `l^e || n_i` has
`q_i | ord_{l^e}(2)`, and then `v_l(n_j) < e` for all `j ≠ i`. So every component
has a private prime power that survives in every ratio `z_j/z_i`, and in
particular `q_i | f` for all `q_i ∈ Q(h)`.

**Proposition 6.1 (exact two-component forcing) [D].** By Proposition 1 a
two-component row is forced to fail iff `h ∤ f^+`, which happens iff
(CM) `-1 ∈ <2 mod N>` (all `l^e || N` have the same `v = v_2(ord_{l^e} 2) >= 1`)
and `v_2(h) = v`, or (cancellation) some prime power of `h` divides `E` only
through `l`-parts with `z1|_l = z2|_l` (cancelling in `rho`), so `h ∤ f`.
Both are decidable from the component orders alone. **If `Q(h) = {2^a, r^c}`
(`a >= 2`) neither occurs**: `z1 = c_{a-1}` has a private prime of `F_{a-1}`
with `v_2 = a`; every prime of `n_2` has `ord_l(2) | r^c b_r` and
`v_2(b_r) < a` (else `2^a | dsum`), so the profile is mixed; and every
non-private `l^e` of `n_2` has `ord_{l^e}(2) | 2^a`, giving `E | f`.
For odd pairs `{r1^{c1}, r2^{c2}}` (the `3^b5^c` family is mixed: `v = 1` at 3,
`v = 2` at 5) a CM forcing would need a component whose private primes all
have `v_2(ord) = v_2(h)`; for `{3^b, r^c}` this means `v_2(b_r) = 1`, `v_2(h) = 1`
and `kappa_{r^c}` (`D = r^c b_r`) **unitary**: `kappa_{r^c}^{2^{D/2}+1} = 1`,
a norm-one condition. Not searched (binding rule); heuristically a probability
`~2^{-D/2}` event per component, summable [H]. `kappa_5` (b=4) and `kappa_7`
(7 has odd order of 2) are not unitary [D, from the digest's orders]. Three or
more components: CM forcing needs `x` real up to a root of unity, i.e. a
symmetric configuration, excluded by Lemma 6.0 [D].

**Unit index [S].** Sinnott: `[E^+ : C^+] = 2^{b} h^+` with `b` depending only
on the number of prime factors of `N`; at odd `p` the index is invisible, and
the `psi`-index equals `|A_psi|` (Gras = Mazur–Wiles for `p ∤ [K^+:Q]`). So the
"unit index" contributes nothing beyond the `p | |A_psi|` alternative.

**Provable infinite families: none found.** The cleanest families (Theorem B)
are arm C's twins and are exactly as open as arm C; the `m > 1` families are a
selected `m`-term Fourier sum; reciprocity relocates the selection to wild
symbols at `p` (Remark 5.3). The only *unconditional* statements are negative:
no forced outcome in the families above (Prop. 6.1), and the
Washington/Horie tower mechanism is unavailable at row primes (§3). What
remains is a Wieferich-type selected statement in each case:
- Theorem B families: `p ∤ |A_psi(K_h)|` **and** `red_2(eta_psi) ∉ F_{2^h}^{x p}`
  for the faithful `psi` of order `h` with `psi(Frob_2) = 2` — one character, one
  prime, no selection (as arm C);
- general two-component: `sum_{psi ∈ Psi} a_psi ≠ 0` (selected coset);
- three components: the same plus the Gauss-sum part of Theorem A_S.

## 7. Checks (Lean, small computations)

- **Lean** `lean/B2ArmZ.lean`, checked with
  `cd formal && lake env lean ../experiments/excess_search/notes/overnight/lean/B2ArmZ.lean`
  (no errors, no `sorry`): `pow_coprime_is_pth_power` (order prime to `p` ⇒
  `p`-th power, any monoid), `two_component_factor` (`z1 t (t + t^{-1}) =
  z1 + z1 t^2`), `pow_geom_of_subfield` (`x^{q-1} = 1 ⇒ x^{1+q+...+q^{r-1}} = x^r`),
  `pth_power_descent` (`w^p = 1`, `p ∤ r` ⇒ (`w^r = 1 ↔ w = 1`)). Together these
  are Lemmas 1.1 and 1.2.
- **[N] `scratchpad/b2/fam.py`**: `Q(h)`, `dsum`, `f`, `-1 ∈ <2>`, `m` for the
  families in §1 (uses `census.py`'s `Qset/dsum` and `nim.py` orders
  `ord(4) = 15`, `ord(16) = 85`, `ord(256) = 21845`, `ord(65536) = 1431655765`).
- **[N] `scratchpad/b2/four.py`**: in `F_16[omega]/(omega^3 - 2)` and
  `F_256[omega]/(omega^3 - 2)`: Lemma 1.1's identity at `h = 12, 24`; the rows
  `p = 13`, `p = 241` hold (already known); at `h = 12` (`m = 1`) one coset; at
  `h = 24` the 8-coset symbol vector and its character transform (§4).
  Conjugate (non-selected) primes are not rows of the rule.

## 8. Best next step

1. **Adversarial read of Theorem A/B and Remark 5.3** (Codex): especially the
   transport rule in A(2), the norm-relation Euler factor in A(3), and the
   Stickelberger/reciprocity conventions in 5.3, which are only sketched. If
   5.3 survives with `c ≡ unit · B_{1, psi omega^{-1}}`, every `m = 1` row (and
   arm C) becomes "Bernoulli-nonvanishing ⇒ (row ⟺ a wild pairing at `p`)", the
   sharpest Wieferich-type form available.
2. **The only disproof lead from this avenue is Proposition 6.1**: a
   two-component (or multi-component) `Q(h)` with odd components whose
   ratio order `N` has uniform 2-adic profile `v = v_2(h)` (e.g. a unitary
   `kappa_{r^c}` with `v_2(b_r) = 1` paired with `3^b`), or a prime power of `h`
   carried only by a cancelling common `l`-part. It is decidable from component
   orders (no Kummer test), so a targeted check of the components with
   `v_2(b_r) = 1` is a cheap, non-row computation — but it is a search, so it
   needs the coordinator's go-ahead. Heuristically it should find nothing [H].
3. For the Theorem B twins, `h = 12` (`p = 13`) and `h = 36` (`p = 37, 109`)
   are small enough to compute `A_psi` and `lambda_psi` separately for
   `Q(zeta_45)^+` and `Q(zeta_135)^+` with a CAS (PARI `bnfinit` on degree 12 is
   instant; degree 36 is feasible): this would show which Theorem C regime the
   twins sit in, without touching new rows.

