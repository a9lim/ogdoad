# B3 — arm C: universal attack

Avenue B3 of the overnight run. Tags: [S] standard/cited, [D] derived here
with proof, [N] checked by a named small computation, [H] heuristic.

Target (arm C at level k): for every prime l with ord_l(2) = 3^k,
gamma_k = zeta + zeta^{-1} (zeta of order 3^{k+1}, char 2) is not an l-th
power in F_q, q = 2^{3^k}. Over all levels this is primitivity of every gamma_k.

Status: complete. Arm C is not proved. All four directions are closed, each
with an exact obstruction. New exact results: the coset-product identity
(Thm 3.4), which collapses explicit reciprocity; the Gauss-sum congruence
(Lemma 3.1); the Frobenius-group form of failure (Thm 1.1/Cor 1.2); the
balanced Selmer count (Prop 1.3); and the Gauss-lemma digit form (Thm 4.2).
Lean: `lean/B3ArmC.lean`, 5 lemmas, compiles with no `sorry`. Number checks:
scratchpad scripts, each under 1 s, run only at already-certified levels and
on analogue moduli.

## 0. Notation and reductions used throughout

`k >= 1`, `n = 3^k`, `q = 2^n`, `m = 3^(k+1)`, `K = K_k = Q(xi_m)^+`,
`G = Gal(K/Q) = <sigma_2>` cyclic of order `n`; `2` is inert in `K`,
`O_K/2 = F_q`. `l` is a prime with `ord_l(2) = n`, so `l = 1 mod 2n`,
`l != 3`, and `psi : G -> F_l^x`, `psi(sigma_2) = 2`, is a FAITHFUL character
(2 has order `n` mod `l`). `F = K(mu_l)`. `chi_l` = an order-`l` character of
`F_q^x`, `L = log_{chi_l} : F_q^x -> Z/l`. `gamma = gamma_k`, `zeta` of order `m`
in `F_(q^2)`, `zeta^q = zeta^(-1)`.

- **0.1 [D] (norm tower).** `N_{F_(2^(3^k))/F_(2^(3^(k-1)))}(gamma_k) = gamma_(k-1)`
  (the conjugates are the roots of `X^3 + X + gamma_(k-1)`; constant term). The
  same identity holds for the char-0 lifts `xi + xi^(-1)` (product of
  `(xi w^j + xi^(-1) w^(-j))` over cube roots `w` is `xi^3 + xi^(-3)`). So
  `(gamma_k)_k` is a norm-coherent cyclotomic unit in the cyclotomic
  `Z_3`-tower, 2 is inert in the whole tower, and arm C at all levels is the
  single statement that this norm-coherent unit generates the procyclic group
  `lim_N F_(2^(3^k))^x = prod_{l: ord_l(2) in 3^N} Z/l^(v_l)`.
- **0.2 [D].** Full valuation is automatic: `F_q^x` is cyclic, so "not an
  `l`-th power" already means `l^(v_l(q-1)) | ord(gamma)`.

## 1. Direction (b): the Galois/ray-class form and its obstructions

**Theorem 1.1 [D, given Mazur–Wiles/Gras = S].** For every `(k, l)`:
arm C holds at `(k,l)`  <=>  `e_psi (Cl_K(2 O_K) ⊗ Z_l) = 0`, where
`Cl_K(2O_K)` is the ray class group of modulus `2O_K`.

*Proof.* Tensor `O_K^x -> (O_K/2)^x -> Cl_K(2) -> Cl_K -> 0` with `Z_l` and
apply `e_psi` (exact: `l ∤ |G|`). `(O_K/2)^x ⊗ Z_l = Z/l^v` is entirely
`psi`-isotypic (Frobenius = squaring), so
`e_psi U -> Z/l^v -> e_psi Cl_K(2) -> e_psi Cl_K -> 0`. If `e_psi Cl_K != 0`
then by Gras (Mazur–Wiles, `l ∤ [K:Q]`) `l | [U:C]_psi`, so `e_psi(gamma)` is
an `l`-th power in `e_psi(U ⊗ Z_l)`: arm C fails and the ray group is nonzero.
If `e_psi Cl_K = 0`, then `e_psi(U ⊗ Z_l) = Z_l e_psi(gamma)` (Theorem C (2)),
and `e_psi Cl_K(2) = Z/l^v / <red gamma>`, which vanishes iff `red gamma` is
not an `l`-th power. ∎

**Corollary 1.2 [D] (the field L).** Arm C fails at `(k,l)` iff there is a
Galois `L/Q` with `Gal(L/Q) = Z/l ⋊ Z/n` (generator acting by `2`; a Frobenius
group, since `psi` is faithful), `L ⊃ K`, `L/K` cyclic of degree `l`
unramified outside `2O_K`. Every such `L` has:

1. at 2: `L/K` totally and tamely ramified at `2O_K`; decomposition group of
   2 in `L/Q` is the whole group, inertia `Z/l`, `Frob t Frob^(-1) = t^2` —
   exactly the shape of tame local Galois groups over `Q_2`, so the local
   extension exists (no local obstruction);
2. **every prime `v` of `K` with nontrivial decomposition group in `K/Q`
   splits completely in `L/K`**: `Frob_(sigma v) = psi(sigma) Frob_v`, and
   `psi(sigma) != 1` for `sigma != 1` because `psi` is faithful. In particular
   the unique prime over 3 splits, every prime over a rational `p ≢ ±1 mod m`
   splits, and when `l ≢ 1 mod m` the primes over `l` split; only primes
   over `p = ±1 mod m` can be inert. `L` is totally real;
3. the degree-`l` subfield `M_0 = L^(Z/n)` has `2 = P^l` and
   `3 = P_0 prod_(j=1)^(2t) P_j^n` (`t = (l-1)/(2n)`), with
   `disc(M_0) = 2^(l-1) 3^(2t S_k)`, `S_k = v_3(disc K_k) = (3^k(2k+1) - 1)/2`
   (conductor–discriminant; checks: 4, 22, 94, 364 for k = 1..4).

**Proposition 1.3 [D] (Galois cohomology is exactly balanced).** Put
`M = F_l(psi)`, `M* = F_l(omega psi^(-1))`. Local facts: `H^1(Q_3, M) = 0`
(`psi` is wildly ramified at 3, `omega` unramified there, so `h^0 = h^2 = 0`);
`h^1(Q_2, M) = 1` with `H^1_ur(Q_2, M) = M/(2-1)M = 0` (the whole local group
is tamely ramified, `h^2 = 1` because `omega psi^(-1)(Frob_2) = 2·2^(-1) = 1`);
`H^1(R, M) = 0`, `h^0(R, M) = 1`. With the Selmer condition
"anything at 2, unramified elsewhere" (= `Hom_G(Cl_K(2), M)` by
inflation–restriction), Greenberg–Wiles gives
`h^1_L(M) - h^1_{L*}(M*) = 0 - 0 + (-1)_inf + (+1)_2 + 0_3 + 0_l = 0`.
The dual Selmer group is the `psi`-eigenspace of `{x in F^x/l : (x) = a^l,
x in F_w^(x l) for w | 2}` — Theorem C's Kummer side.

*Exact obstruction for (b).* The local conditions at 3 are vacuous (local
`H^1 = 0`), the local condition at 2 is unobstructed, and the global
Euler-characteristic count is exactly `0`: the ray-class side and the Kummer
side have equal dimension, and nothing in the cohomological bookkeeping
prefers `0` over `1`. Scholz/Leopoldt reflection is precisely this equality;
it converts the problem into Theorem C and back, never into a vanishing
statement. The extra constraint 2 (split at all non-split primes) is forced
by equivariance and is consistent with Chebotarev (the Frobenius classes in
`Z/l \ 0` have density `(l-1)/(l n)`, all carried by `p = ±1 mod m`).

**Proposition 1.4 [D + S] (discriminant route dies at k = 4).**
`rd(L) = rd(K_k) · 2^((l-1)/l) = 3^(k + 1/2 - 1/(2·3^k)) · 2^(1 - 1/l)`.
`L` is totally real of degree `l·3^k`. The Odlyzko constants for totally
real fields are `4 pi e^(1+gamma_E) ≈ 60.8` (unconditional) and
`8 pi e^(gamma_E + pi/2) ≈ 215.3` (GRH) [S]. `rd(L) ≈ 28.8, 91.4, 277.6` for
`k = 2, 3, 4`. So discriminant bounds can at best exclude `L` for `k <= 3`
(GRH, using finite-degree tables for `k = 3` — not checked here), levels that
are already certified; from `k = 4` on `rd(L)` exceeds even the GRH
asymptotic constant and grows like `2·3^(k+1/2)`. Conductor bounds for the
`(l-1)/n` irreducible degree-`n` constituents of the permutation character
(each `Ind` of an order-`l` character, restricting to the regular
representation of `I_3`) give the same numbers. Closed.

**Local dimension check [D]** (rules out a hoped-for "case split at `l`").
Put `phi = omega psi^(-1)`. The `phi`-part of `⊕_{w|l} F_w^x/l` has
dimension 2 if `l = 1 mod m` (`l` splits in `K`; levels 1 and `l`) and 1 if
`l ≢ 1 mod m` (residue degree 3 in `K`; level 1 only). In both cases
"`l`-primary" (`L/K` unramified at `l`) is one linear condition, so neither
case is forced; failure probability stays `≈ 1/l` in both.

## 2. Direction (a): Dickson dynamics

Lean file: `lean/B3ArmC.lean` (checked: `lake env lean`, exit 0, no `sorry`).

**Lemma 2.1 [D; Lean `singer_relation`, `frob_eq_mobius`,
`mobius_order_three`; N at k = 1, 2].** Put `Q_k = 2^(3^(k-1))`,
`eta = gamma_k^(Q_k - 1)`. Since `gamma + gamma^Q + gamma^(Q^2) = 0` (trace
coefficient of `X^3 + X + gamma_(k-1)`), `eta^(Q+1) = eta + 1` and
`eta^Q = M(eta)`, `M(x) = 1 + 1/x`, a Möbius map of order 3. With
`rho = Q mod l` (a primitive cube root of unity in `F_l`) and `L` the
`l`-Kummer log: `L(eta) = (rho - 1) L(gamma)`, `L(eta + 1) = -rho^2 L(eta)`,
and (paper) `L(gamma) + 2 L(gamma + 1) = 0`.

**Proposition 2.2 [D] (lift obstruction).** All these relations are
reductions of identities among cyclotomic units of `Q(xi_m)`: e.g. the lift
`eta~ = w^(-1)(1 + w^2 x)/(1 + x)` (`x = xi^2`, `w` a cube root of unity)
satisfies `eta~ + 1 = -w (1 + w x)/(1 + x)`, again a cyclotomic unit; `D_3`
is the reduction of `z -> z^3`, and Frobenius is the reduction of `sigma_2`.
The `Z[G]`-annihilator of `gamma~` modulo `±1` is `(N_G)` (real cyclotomic
units are `Z[G]/(N_G)` on `gamma~`, Theorem C (2)). So any char-0 identity
`prod (sigma^i gamma~)^(a_i) = ±1` has `sum a_i sigma^i in (N_G)`, and its
Kummer image is `c (2^n - 1) L(gamma) = 0`: **every relation the dynamics
produces is satisfied identically, whatever `L(gamma)` is.** A proof must use
an identity that holds mod 2 and fails in characteristic 0. The backward
orbit, the stable map and the Möbius `M` supply none.

**Proposition 2.3 [D] (stability vs primitivity).**
(i) *Stability, one line.* `x^3 + x = s^3 + s^(-3)` for `x = s + 1/s`, so
`X^3 + X + gamma_(k-1)` has a root in `F_(Q_k)` iff `zeta_(k-1)` is a cube in
`F_(Q_k)^x` or in the norm-one torus `T_1` of order `Q_k + 1`. It is neither:
`zeta_(k-1) ∉ F_(Q_k)`, and it has order `3^k = 3`-part of `Q_k + 1`. So the
iterates are irreducible because a *root of unity* generates a *3-Sylow*,
which is automatic.
(ii) *Primitivity.* Since `mu_l ⊂ F_q`, Kummer + Capelli give: arm C at
`(k,l)` iff `P_k(X^l + 1)` is irreducible over `F_2`; otherwise it has exactly
`l` irreducible factors of degree `3^k`. The number of factors `r` is in
`{1, l}`, both odd, and `deg = l·3^k` is odd, so the
Stickelberger–Swan/Berlekamp discriminant parity `(-1)^(deg - r)` is the same
in both cases. **The parity tool behind stability results is blind to arm C.**
Closed: (a) produces only relations that hold identically or parity data
that is constant.

## 3. Direction (c): explicit reciprocity

Notation: `E = F_(q^2)`, `H = (E^x)^m`, `chi_3` an order-`m` character of
`E^x`, `L` an order-`l` discrete log on `E^x`,
`lambda = 1 - zeta_l`, `Tr = Tr_(E/F_2)`.

**Lemma 3.1 [D; N] (untwisted Gauss sums are `-1` mod `lambda^2`).** For
every order-`l` character of `F_(2^N)^x`, with `l` any odd prime dividing
`2^N - 1`: `g(chi) = sum chi(x)(-1)^(Tr x) ≡ -1 mod lambda^2`. *Proof:* the
`lambda`-coefficient is `S = 2 L(prod_{x in ker Tr \ 0} x) - L(prod_{x != 0} x)`.
Both products are 1: the first is the linear coefficient of the trace
polynomial `sum X^(2^i)`, the second because the group is cyclic of odd order.
∎ [N] `S ≡ 0` and the trace-zero product `= 1`, checked for
`(N,l) = (3,7),(9,73),(11,23),(11,89),(6,7),(18,73),(18,19)`.
*Correction to `heuristic_nonconstructive.md` §4.2 (R0):* the sum
`S = sum_x L(x)(-1)^(Tr x)` named there vanishes identically. The quantity
that actually appears is the twisted sum `S'` below.

**Lemma 3.2 [D].** Gauss sums of order-`l` characters lie in `Q(mu_l)`, and
they pair trivially with units of `K`. Each prime of `Q(mu_l)` above 2 splits
completely in `F/Q(mu_l)`, so the product formula gives
`prod_tau (tau^(-1) gamma~ / P) = (N_(K/Q) gamma~ / P) = 1`. The useful 2-unit
must lie in the `phi = omega psi^(-1)` component. It comes from
`G = g(chi_3 chi_l)` over `E`, where `g(chi_3) = c_0 = ±2^n` is pure
(semiprimitive: `2^n = -1 mod m`) [S], so `G/c_0 ≡ 1 - lambda S'/c_0`, with

`S' = sum_{x in E^x} chi_3(x) L(x) (-1)^(Tr x)  in Z[zeta_m]/l`.

The Frobenius substitution `x -> x^2` gives `sigma_2 S' = S'/2` [D; N], so
`S'` lies in a 1-dimensional `F_l`-eigenline.

**Theorem 3.3 [D, given S].** Inputs (cited): Stickelberger's factorization
(`phi`-coefficient `B ≡ unit · B_(1, omega^(-1) psi)`); the graded Hilbert
pairing of `U^(l-1)/U^(l)` with `U^(1)/U^(2)` (nondegenerate trace form, Serre
*Local Fields* XIV / Fesenko–Vostokov); Leopoldt's formula with the Kummer
congruence `L_l(1,psi) ≡ L_l(0,psi) = -B_(1, psi omega^(-1))`. From the
product formula for `(gamma~, G)`:

`B · L(gamma) = c · < q_psi(gamma~), S' >`,

where `q_psi` is the `psi`-part of the Fermat quotient `(u^(N_v - 1) - 1)/l`,
`< , >` is the trace pairing of the eigenlines `sigma_2 = 2` and
`sigma_2 = 1/2`, and `c` is a nonzero normalisation constant. The pairing is
exact, not a leading term, because levels `(l-1) + j > l` pair trivially for
`j >= 2`.

**Theorem 3.4 [D; N; last step in Lean `cyclotomic_product_step`] (the
coset-product identity — the reciprocity collapses).** Let `r = (q+1)/m`
(coprime to `m`, since `v_3(2^(3^k)+1) = k+1`). For `xi in mu_m`, put
`Pi(xi) = prod_{y in H, Tr(xi y) = 0} y`. Then

`Pi(xi) = (xi^r + xi^(-r))^(1 - q/2)`  for `xi != 1`,  and  `Pi(1) = 1`.

*Proof.* `q` is even, so `E^x = F_q^x × T_1` and `H = F_q^x × T_1^m`. Write
`y = s t` with `s in F_q^x` and `t in T_1^m`. Then
`Tr(xi s t) = Tr_(F_q/F_2)(s c_t)` with
`c_t = xi t + (xi t)^(-1) in F_q`. Here `c_t != 0` iff `xi t != 1`, and
`xi t = 1` only when `xi = t = 1`. For fixed `t`, the admissible `s` form
`c_t^(-1)(ker Tr \ 0)`, whose product is `c_t^(1 - q/2)` (Lemma 3.1's
subspace fact). The product of all `t` over the odd cyclic group `T_1^m` is 1,
so `Pi(xi) = (prod_t c_t)^(1 - q/2)`. Next,
`prod_t c_t = prod_{u^r = xi^r} u^(-1) (1 + u)^2`. In characteristic two
`prod (1 + u) = 1 + w` and `prod u = w`, where `w = xi^r`. Hence
`prod_t c_t = w^(-1)(1 + w)^2 = w + w^(-1)`. For `xi = 1`, the `t = 1` term
contributes `prod F_q^x = 1` and the rest is `r^2 = 1`. ∎

*Consequences.*
- Non-primitive `xi`: `xi^r + xi^(-r)` lies in a proper subfield, so
  `L(Pi(xi)) = 0`.
- Primitive `xi`: `L(Pi(zeta)) = (1 - q/2) 2^(j_r) L(gamma) = 2^(j_r - 1) L(gamma)`,
  where `2^(j_r) = ±r mod m`.

Decomposing `x = xi y` therefore gives

`S' = 2^(j_r) L(gamma) · sum_{i < 2n} 2^i zeta_m^(2^i)`,

with the last factor `E` nonzero. *Why:* write `2^i = e + 3^k f`. The
`zeta^e`, `e in (Z/3^k)^x`, are part of a `Z[omega_0]`-basis. Each
coefficient of `E` is `2^i omega_0^f (1 + rho w + rho^2 w^2)`, where `w` is a
primitive cube root of unity and `rho = 2^(2·3^(k-1)) mod l`. In the factor
of `Z[omega_0]/l = F_l × F_l` where `rho w = 1`, this coefficient is
`3 · unit != 0`. **`S'` is an explicit nonzero multiple of
`L(gamma)`, unconditionally.**

[N] The predicted ratio `L(gamma)/L(Pi(zeta)) = 2^(1 - j_r)` matched in all
six cases `(m, l) = (5,3), (9,7), (11,31), (25,11), (19,73), (27,73)`. The
moduli 5, 11, 19 and 25 are non-3-power analogues with 2 a primitive root
(e.g. `m = 25`: `r = 41 ≡ 2^4`, ratio `2^(-3) = 7 mod 11`). The identity is
exact: for every prime `p | (q^2-1)/m` where `1 + zeta` has a nontrivial
`p`-part, `log Pi / log(1 + zeta) = 2^(j_r) mod p^a`. Scripts (outside the repo, under 1 s each):
`/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/0d823db5-514b-4211-b6ff-3cb614bd36e4/scratchpad/b3check.py`, `/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/0d823db5-514b-4211-b6ff-3cb614bd36e4/scratchpad/b3ratio.py`, `/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/0d823db5-514b-4211-b6ff-3cb614bd36e4/scratchpad/b3exact.py`.

**Corollary 3.5 [D] (exact obstruction for (c)).** Substitute 3.4 into 3.3.
The result is `B · L(gamma) = c'' · q_psi(gamma~) · L(gamma)`:
- if `L(gamma) != 0`, this is the classical congruence
  `B_(1, omega^(-1) psi) ≡ unit · L_l(1, psi)`;
- if `L(gamma) = 0`, it is vacuous.

So explicit reciprocity, in any form (Artin–Hasse, Sen, Vostokov, Gauss-sum
reflection), is an involution on arm C: it maps the symbol to itself times
known constants. In particular the R0 "Gauss-sum side" is not independent
arithmetic. Neither regime R0 nor R1 forces anything. This also makes the
Theorem C/Stark closure (DIGEST) concrete at the finite-field level. Closed.

## 4. Direction (d): Ducci / Lucas form

**Lemma 4.1 [D; Lean `digit_lemma`; N].** For odd `l > 1`, `l | 2^h - 1`,
`d = (2^h - 1)/l`, and `i < h`: bit `i` of `d` equals
`floor(2 (2^(h-1-i) mod l) / l)`. That is, bit `i` is 1 iff
`2^(-(i+1)) mod l > l/2`, because `2^h ≡ 1`. The Lean statement is for
general `h, l, i` and does not assume `l | 2^h - 1`. [N] checked for
`(h,l) = (3,7),(9,73),(27,262657),(11,23),(11,89),(18,19)`.

**Theorem 4.2 [D] (Gauss-lemma form).** With `h = 3^k`:
arm C fails at `(k,l)`  iff
`prod_{j in [1,h] : (2^(-j) mod l) > l/2} (1 + zeta^(2^j)) = zeta^d`, where
`d ≡ -2 l^(-1) mod m`.
Equivalently, the "Gauss-lemma Galois element"
`Theta_l = sum_{j : 2^(-j) mod l in (l/2, l)} sigma^j` satisfies
`(1 + zeta~)^(Theta_l) ≡ root of unity mod 2O`. (Combine Lucas
`(1 + X^2)^d = prod_{i in supp d}(1 + X^(2^(i+1)))` with Lemma 4.1.)

*Exact obstruction.*
- In characteristic 0, `(1 + zeta~)^(Theta_l)` is never a root of unity:
  `Theta_l` has 0/1 coefficients on a proper nonempty set and is not in
  `(N_G, sigma^n - 1)`. So the entire content is a mod-2 coincidence.
- The digit sums `s_2(a d)` for `a in F_l^x` are exactly the 2-adic
  Stickelberger/Gross–Koblitz valuations of order-`l` Gauss sums over
  `F_(2^h)` [S]. Stickelberger theory sees the digit sums of all multiples;
  arm C needs the digit pattern of `1/l` itself.
- In the group ring `F_2[C_m] = F_2[X]/(X^h - 1) × F_(2^(2h))`, the
  condition says the subset-sum parity vector of
  `{2^j mod m : j in Theta_l}` is constant on cosets of the order-3 subgroup.
- [H] The two clocks `j -> 2^(-j) mod l` and `j -> 2^j mod 3^(k+1)` are
  linked only through `j`, and I found no mechanism correlating the
  Gauss-lemma half-set with the cosets. Closed as a proof route; it is a
  clean statement for experiments.

## 5. Universal fragments proved

All statements below hold for every `k >= 1` and every `l` with
`ord_l(2) = 3^k`.

1. **[D, given Gras = S] Thm 1.1 / Cor 1.2.** Arm C is equivalent to the
   vanishing of `e_psi Cl_K(2O_K)[l^∞]`, and also to the non-existence of a
   totally real Frobenius-group field `L ⊃ K_k` ramified in `L/K` only at 2.
   Any such `L` splits completely at every prime of `K` whose decomposition
   group in `K/Q` is nontrivial.
2. **[D] Prop 1.3.** The Selmer count is exactly balanced (`0 = 0`), and the
   local `H^1` at 3 vanishes.
3. **[D] Prop 1.4.** `rd(L) = 2^(1-1/l) 3^(k+1/2-1/(2·3^k))`. Discriminant
   bounds cannot reach `k >= 4`, even under GRH.
4. **[D] Prop 2.2.** Every relation coming from the Dickson/Möbius dynamics
   or the norm tower lifts to characteristic 0 and has trivial Kummer image.
5. **[D] Prop 2.3.** Stability is the trivial 3-Kummer statement. Arm C is
   equivalent to irreducibility of `P_k(X^l + 1)`, which discriminant parity
   cannot detect.
6. **[D, N] Lemma 3.1.** Every order-`l` Gauss sum over `F_(2^N)` is `≡ -1`
   mod `lambda^2`.
7. **[D, N, Lean step] Thm 3.4 (coset-product identity).**
   `prod_{y in (E^x)^m, Tr(xi y)=0} y = (xi^r + xi^(-r))^(1-q/2)`. The
   twisted Gauss-sum coefficient `S'` is an explicit nonzero multiple of
   `L(gamma)`. **Cor 3.5:** explicit reciprocity contains nothing beyond the
   Kummer congruence `B_(1,omega^(-1)psi) ≡ unit · L_l(1,psi)`.
8. **[D, Lean] Lemma 4.1 / Thm 4.2.** Exact Gauss-lemma digit form of the
   Ducci criterion.

**Not achieved.** I did not prove arm C at any new `(k, l)`. I did not prove
it for an infinite or positive-density class of `l`, did not improve the
packing lower bound, and found no conditional proof from a named standard
conjecture. The only conditional statement is the GRH–Odlyzko exclusion for
`k <= 3`, and those levels are already certified.

## 6. Summary and best next step

**Status: arm C not proved; all four directions closed with exact
obstructions.** Each route ends in one of three ways, and none of them can
force non-vanishing:

- (i) a reduction of a characteristic-0 cyclotomic-unit identity, which is
  automatically satisfied (directions a, d);
- (ii) an equality of two dimensions, `Hom_G(Cl_K(2), F_l(psi))` versus the
  2-split Kummer group (direction b; reflection = Greenberg–Wiles balance);
- (iii) an elementary multiple of the input, through the coset-product
  identity, Thm 3.4 (direction c; reciprocity is an involution).

**Meta-obstruction [D for uniformity; S for existence of failures].**
Props 1.3, 2.3 and Thm 3.4 are uniform in the conductor: the [N] checks used
`m = 5, 11, 19, 25` alongside 9 and 27. Non-primitive `xi_m + xi_m^(-1)` with
2 a primitive root mod `m` occur for some prime `m` (Breuer 2021, per
`LIT-*.md`). So any successful argument must use something special to
`m = 3^(k+1)`. The only 3-power-specific structure (norm tower, `D_3`
dynamics, Singer/Möbius line) lifts to characteristic 0 (Prop 2.2) and is
therefore inert.

**Best next step [H].** A proof needs a multiplicative relation that holds
mod 2, fails in characteristic 0, and is not forced by Frobenius
equivariance. Thm 3.4 shows that hyperplane products (additive condition,
multiplicative product) collapse to liftable powers of `xi^r + xi^(-r)`. The
first untested source of non-liftable relations is Moore determinants
`Delta(gamma, gamma^2, ..., gamma^(2^(d-1)))` of partial Frobenius flags.
These are products over `F_2`-subspaces of codimension `>= 2` that are not
`F_q`-stable, and equivariance does not constrain their `l`-Kummer classes.

Concrete test, in the style of `b3ratio.py`: compute
`L(Delta_d)/L(gamma) mod l` for `k = 1, 2` and small `d`, across the
analogue moduli. A ratio with visible structure, like the `2^(1-j_r)` that
exposed Thm 3.4, would be the first non-liftable relation. Random ratios
close this last door.

Separately, the coordinator should note that the R0 description in
`heuristic_nonconstructive.md` §4.2 needs the correction in Lemma 3.1 /
Thm 3.4.
