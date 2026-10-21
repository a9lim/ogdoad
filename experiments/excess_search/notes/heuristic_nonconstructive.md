# Toward a nonconstructive counterexample to the 0/1/4 rule: routes, obstructions, reductions

Companion to `model.md` in this directory, written in parallel by a sibling agent.
That file states the random model and works out its numbers. This file attempts
the two proofs the model suggests: a nonconstructive proof that the rule fails, and
a proof of structure that would force the rule. Neither proof exists. The useful
output is a set of exact statements: which routes are closed, why, and what each
open route reduces to.

Tags:

- **[S]** standard or cited result;
- **[D]** derived here, with the proof inline;
- **[N]** checked numerically (script and output named);
- **[H]** heuristic or speculation.

Notation follows `docs/OPEN.md` §2 and `writeups/excess.tex`. For a row `p`,
`h = f(p)`, the selected element is `beta_p = kappa_h + rule(p)` in `F_(2^E)`. Its
`p`-coordinate is `c_p(beta) = beta^((2^E-1)/p)` in `mu_p`, written additively in
`F_p`. The row fails exactly when `c_p(beta_p) = 0`.

---

## 0. Verdict and new results

**Verdict.** I found no nonconstructive proof that the rule fails, and no structure
that forces it. On the evidence below, the failure direction is "Wieferich-type":

- In arm C, the cleanest arm, the row condition is *equivalent* to a splitting
  statement. A fixed prime (the prime `2` of the real cyclotomic field
  `K_k = Q(zeta_(3^(k+1)))^+`) must split completely in a cyclic degree-`p`
  Kummer extension determined by `p` (§4, Theorem C). The selected element drops
  out of the statement.
- Wieferich's condition has the same shape: `p` splits completely in
  `Q(mu_p, 2^(1/p))`. For both, the heuristic count is `sum 1/p`. For neither is
  there any theorem, conditional or unconditional, that produces infinitely many
  instances.
- This is a reduction of the same type, **not an equivalence of difficulty**
  [H]. I have no argument that a proof for the rows would give one for
  Wieferich primes, or the reverse.

**What is new here.**

1. **Theorem C [D]: arm C without selection.** Fix a row `p` at level `k`.
   - If `p` does not divide `h^+(K_k)`, the row holds iff some unit of `K_k` is
     not a `p`-th power modulo 2. Equivalently, iff `2` does not split completely
     in `K_k(mu_p, (O_(K_k)^x)^(1/p))`.
   - If `p` divides the `psi_p`-part of `[O_(K_k)^x : C^+]`, the row fails.
   - So the rule implies a 3-adic Weber-type class-number statement (§4.3). It
     also identifies the only "global" mechanism by which a row could be *forced*
     to fail.
2. **Twist lemma [D, N].** Let the singleton component be `chi_(r^a)` with `r` a
   Fermat prime, so `mu_r` lies inside the finite nimbers.
   - Then the translates `kappa + c`, for `c` in `mu_r`, have exactly the same
     `p`-power status as `kappa + 1`, at every prime `p != r`.
   - For `r = 3` (arms C and D, which share `kappa = zeta_k`), add the
     Frobenius `Frob^(2*3^k)`, which fixes `zeta_k` and squares twice on
     `F_16`. The nimbers below 16 then fall into four tied classes:
     `{0}`, `{1,2,3}`, `{4,5,8,10,12,15}` and `{6,7,9,11,13,14}`.
   - Consequences:
     - **an arm C failure gives `m_p = 4`** (model probability `1 - 1/p`),
       not `m_p = 2`. That value is inside `{0,1,4}`;
     - **an arm D failure gives `m_p = 6`**, not 5.
     - **Correction (`overnight/B1-forcing.md` §3.1–4.2, Codex-confirmed):**
       both values are wrong. A distribution relation over `mu_5` and the
       inversion tie put all fifteen nonzero `c < 16` in one status class in
       arm C, and all twelve `c` in `F_16 \ F_4` in one class in arm D. So
       failures give `m_p >= 16` in both arms.
   - This **corrects `model.md` §3.4** in arms C and D. It treated translates as
     tied only under `Frob^E`, which fixes `beta`. The right group is the
     stabiliser of `kappa` up to a root of unity of order prime to `p`.
     - In arm C, `P(m_p >= 2) = P(m_p >= 4) = 1/p`.
     - In arm D, `P(m_p >= 5) = P(m_p >= 6) = 1/p`.
     - Arms O and Z are unaffected for `m <= 3`.
     - The masses of arms C and D are tiny, so the boundedness numbers barely
       move. The predicted values at failures change (§2.2).
   - [N] `orbit_check.py` (about 20 s) confirms the four classes at every prime
     `p != 3` dividing `2^12 - 1` and `2^36 - 1`.
3. **Window for translate-line arguments [D].** For every `theta` of degree `d`
   and every line of length `q >= d^2`, Katz's bound gives a non-`p`-th-power
   translate (`model.md` §3.6). Conversely, if `q log_2 p < d/2 - log_2(q+2)`,
   some `theta` of exact degree `d` has *every* translate in the line a `p`-th
   power.
   - So no argument that uses only degree information about `kappa` can bound
     `m_p` below about `d/(2 log_2 p)`.
   - Hence Lenstra's boundedness is itself a selected-point statement (§3.2).
4. **Multiplicative relations are constructive or silent [D].** An argument that
   uses only multiplicative relations among intrinsic elements cannot prove
   success without an inhomogeneous anchor. If it proves failure, it exhibits an
   explicit failure certificate. So that route cannot give a *non*constructive
   failure proof (§2.1).
5. **Control family: natural cyclotomic elements are biased *toward* `p`-th
   powers at inherited primes [D, N].**
   - For type-II Gaussian periods `alpha_l = zeta_l + zeta_l^(-1)` with
     `l = 5 mod 8` and 2 primitive mod `l`, `alpha_l` is a cube in `F_(2^n)` iff
     `eps_l` lies in `Z[sqrt l]` or `3 | h(Q(sqrt l))`. The proof is exact, and
     the formula was checked against direct computation in all 418 such `l <= 2*10^4`,
     with no mismatch.
   - Over the 3377 such `l <= 2*10^5` (computed via the proved formula),
     `P(cube) = 0.399` against the naive `1/3` (8 sigma). The fraction rises
     with `l`, from 0.355 to 0.411 across three bins, tracking `P(3 | h)`.
   - The mechanism is a class-number channel. In arm C rows, that channel is
     exactly the Weber-type index of Theorem C, which is expected to be closed.
   - Lesson: departures from `1/l` at small *inherited* primes measure global
     channels of small subfields. They neither confirm nor refute the row model
     (§6).
6. **Lean [D, machine-checked].** `ExcessHeuristic.lean` proves the logical
   skeleton (`model_consequences`) against the repository's pinned Mathlib, with
   axioms `propext`, `Classical.choice`, `Quot.sound`. The statement: if failures
   are independent with probability at least `1/p`, and `P(m_n > K) <= C/n^2`, then
   almost surely the rule fails infinitely often **and** `m_n <= K` eventually.
   - The boundedness half uses the first Borel–Cantelli lemma, with no
     independence.
   - The sibling `axioms.lean` imports `Ogdoad.ExcessRandomModel`, a richer
     formalization with uniform measures on cyclic groups. Mine is a minimal
     self-contained check, compiled with `lake env lean` from `formal/`. No
     repository file was modified.

---

## 1. What a nonconstructive failure proof would have to do

A failure at row `p` is the single equation `c_p(beta_p) = 0` in `F_p`. A
nonconstructive proof would show that the system "`c_p(beta_p) != 0` for every odd
prime `p`" is inconsistent, without naming the failing `p`. Classical
nonconstructive arguments of this kind come in a few shapes:

| shape | prototype | needs | status here |
| --- | --- | --- | --- |
| algebraic relation forcing a coordinate | `zeta_p` is a `p`-th power iff `p` is Wieferich | an identity tying `beta_p` to an anchor | §2: constructive or silent |
| equidistribution over a family | Chebotarev, Weil, Katz | a family containing the selected point with positive density | §3: the selected point has density 0 |
| pigeonhole / counting | Dirichlet boxes | more selected objects than good states | §3.3: one orbit per level |
| reciprocity / L-values | Jensen's proof of infinitely many irregular primes | the forcing quantity is a Bernoulli number | §4: the forcing quantity is a plus-part index, not a Bernoulli number |
| contradiction with a theorem | — | the rule implies something false | §5: it implies things believed true |

**Coordinates are row-local [S, from the paper].** This is primary vacuity
(`excess.tex`, cross-arm words). An element of `F_(2^d)` with `f(p)` not dividing
`d` has zero `p`-coordinate in every overfield.

- So the `p`-coordinate of any intrinsic element is the coordinate of its norm to
  a field containing `F_(2^h)`.
- Rows with different `h` read disjoint primary groups.
- Rows with the same `h` read CRT-independent coordinates of one element `T_h`.
- So no identity links the row coordinates of different rows, except through the
  definition of the elements. A global counting identity across rows has nothing
  to count.

---

## 2. Route (a): multiplicative relations

### 2.1 The homogeneity dichotomy [D]

Let `S` be any finite set of intrinsic elements in a field `F_(2^e)` with `h | e`.
Take any multiplicative relations among them of the form

```text
prod_i x_i^(n_i) = y,   y in (proper subfields) * (p-th powers),
```

for example Frobenius conjugation, Kummer and Artin–Schreier norms, the cubical
relation, or forced translates.

- Each relation gives the homogeneous linear equation `sum n_i c(x_i) = 0` over
  `F_p`.
- The solution set is a subspace containing `0`. So relations of this form can
  never prove `c(beta_p) != 0`: the all-zero assignment satisfies every one of
  them.
- They prove `c(beta_p) = 0` exactly when the unit vector `e_beta` lies in their
  row span. This means writing `beta_p` itself as a product of elements with known
  zero coordinate, up to a unit exponent, which is an explicit failure certificate.

**Consequence.** A failure proof by relations is automatically constructive. A
success proof by relations needs an **inhomogeneous anchor**: an element with
known *nonzero* coordinate. The canonical anchors are:

- `mu_p` itself, whose coordinate is nonzero iff `p` is not base-2 Wieferich, by
  lifting the exponent;
- elements of exactly known order, such as `u_n` in the Conway–Fermat torus of
  order `F_n`.

Connecting `beta_p` to an anchor is precisely what the paper's rank-one saturation
rules out for multiplicative reciprocity words.

### 2.2 Twist lemma [D, N]

This is the one place where translate relations are nontrivial.

**Lemma.** Let `kappa = chi_R`, `R = r^a`, be a singleton odd component over
`K = F_2(chi_(R/r))` or `F_2(alpha_r)`. Let `L` contain `kappa`, let `zeta` be in
`mu_R ∩ L`, and let `c` be in `L`. Then for every prime `p` not dividing `R`, and
every `p` with `f(p) | [L:F_2]`,

```text
c_p(kappa + c) = 2^j * c_p(kappa + sigma^(-1)(zeta^(-1) c))
```

for some Frobenius power `sigma = Frob^j` with `sigma(kappa) = zeta^(-1) kappa`.
In particular, for `c = 1` and `zeta` running over `mu_R ∩ L`, the translates
`kappa + zeta'` (`zeta'` in `mu_R ∩ L`) all have the `p`-power status of
`kappa + 1`.

*Proof.*

- `y^R - A` is irreducible over `K`, by Lenstra's construction.
- So `Gal(F_2(kappa)/K)` acts transitively on the roots `zeta kappa`. Some `sigma`
  has `sigma(kappa) = zeta^(-1) kappa`; extend it to `L`.
- Then `kappa + c = zeta * (zeta^(-1) kappa + zeta^(-1) c)
  = zeta * sigma(kappa + sigma^(-1)(zeta^(-1) c))`.
- The coordinate `c_p` is additive. It satisfies `c_p(sigma x) = 2^j c_p(x)`,
  since the Euler phase commutes with Frobenius.
- Finally `c_p(zeta) = 0`, because the order of `zeta` divides `R` and is prime
  to `p`.

**When it bites.** `mu_R` meets the finite nimbers `F_(2^(2^infinity))` only in
`mu_r`, and only if `f(r)` is a power of two, i.e. `r` is a Fermat prime
`3, 5, 17, 257, 65537`.

- `r = 3`. Here `mu_3 = {2, 3}` as nimbers, and `kappa = zeta_k` has degree
  `2 * 3^k`.
  - **Twist.** `sigma = Frob^j` with `sigma(zeta) = omega^(-1) zeta` needs `j`
    even and fixed mod `2 * 3^k`. By CRT it can also be taken `= 0 mod 4`, so
    `sigma` fixes `F_16`. This gives `c ~ 2c ~ 3c` (nim products) for `c < 16`.
  - **Frobenius.** `Frob^(2*3^k)` fixes `zeta`, and since `2 * 3^k = 2 mod 4`
    it acts on `F_16` as `x -> x^4`: `4 <-> 5`, `6 <-> 7`. So `c ~ c^4`.
  - **Classes.** Outside `F_4`, `x^4 = omega^i x` forces `x^9 = 1`, hence
    `x^3 = 1`. So the group generated by the twist and the Frobenius acts freely
    on `F_16 \ F_4`. It has two orbits of size 6: `{4,5,8,10,12,15}` and
    `{6,7,9,11,13,14}`.
  - Arm C: `0` is forced (`zeta` is a root of unity of 3-power order). The rule
    class is `{1,2,3}`. The next class starts at 4. **So a failure gives
    `m_p = 4`, unless the class of 4 also fails, in which case `m_p >= 6`.**
  - Arm D: `{0}` and `{1,2,3}` are forced (`prop:d-lower`, which the twist
    explains for 2 and 3). The rule class contains 4. **So a failure gives
    `m_p = 6`.**
  - `model.md` says 5 here. That is wrong, because 5 is Frobenius-conjugate to 4
    over `F_2(zeta_k)`.
- `r = 5, 17, ...`. The tied translates are the nimbers of order `r`. These are at
  least 4, so the tie is invisible for `m <= 3`.

**Check [N].** `twist_check.py` builds the exact towers for
`Q = (3), (9), (27), (5), (25), (17)` (`E` up to 136). At every prime
`l | 2^E - 1` with `l != r`, the translates `kappa + zeta`, `zeta` in `mu_r`, have
the status of `kappa + 1`. Every case is tied. `orbit_check.py` checks the full
four-class structure for `zeta_1, zeta_2` with `F_16` adjoined (`E = 12, 36`),
at every prime `p != 3` dividing `2^E - 1`. It reproduces `m_7 = 1`, `m_73 = 1`
(arm C) and `m_19 = 4` (arm D) as the first non-power translates.
`translate_coords.py`, a discrete-log version at larger `E`, was stopped before
it produced output.

**Correction to `model.md` §3.4.** The statement "rule(p) and rule(p)+1 lie in
distinct Frobenius orbits, hence `P(m_p >= rule+2) = p^(-2)` exactly" is false in
arm C.

- The relevant equivalence is "Frobenius conjugate up to a root-of-unity
  multiple", not "Frobenius conjugate".
- In arm C, `P(m_p >= 4) = P(m_p >= 2) = 1/p` under the model.
- In arm D, `P(m_p >= 5) = P(m_p >= 6) = 1/p`, and failures give `m_p = 6`.
- Arm C mass beyond 727 is `5.8e-5`, and arm C failures now land at
  `m_p = 4`. So `P(sup m_p = 4)` under the model is still about
  `1 - 7.8e-5`. The only route above 4 is still an arm D failure, which now
  gives 6. Arm C needs two failed classes to exceed 4, probability `p^(-2)`.
- **Value set.** Arm C failures stay inside `{0,1,4}`. So the model probability
  of the value set `{0,1,4}` is set by arm O failures (value 2) and arm D
  failures (value 6). This is essentially `model.md`'s 0.54.
- Arms O (with `r >= 5`) and Z are unaffected for `m <= 3`.

### 2.3 The listed relations, individually [D]

- **Norm compatibility in Kummer towers.** `N(1 + chi_(r^a)) = 1 + chi_(r^(a-1))`
  and `N(1 + chi_r) = 1 + alpha_r`, and similarly in the cyclotomic towers.
  - These identify the coordinates of `beta_p` at *inherited* primes (`f(l)`
    dividing a proper subfield degree) with coordinates of lower elements.
  - At row primes the norm lands in a field with zero `p`-part (primary
    vacuity), so the relation reads `0 = 0`.
- **Hilbert 90 / Artin–Schreier.** `c(c+1) = a` gives `N(c) = a`, which is the
  origin of the torus coordinate `u_n = c^(q-1)`. It is again a norm to a
  `p`-free field, so it reads `0 = 0`.
- **The cubical relation** `u_(n+1)(u_n+1)^3 = u_n(u_(n+1)+1)^2`. At `p | F_(n+1)`,
  `u_n` and `u_n + 1` lie in the level-`n` field and have coordinate 0. Hence
  `c(u_(n+1)) = 2 c(u_(n+1) + 1)`.
  - This transfers the row condition between `u_(n+1)` and `u_(n+1) + 1`.
  - It is homogeneous with no anchor, so it decides nothing.
- **Products over translate lines.** `prod_(c in F_q)(kappa + c) = kappa^q + kappa`.
  The right side has no known coordinate. In arms O and C it is tied back to the
  translates by the twist lemma.

**Conclusion for (a) [D].** Every relation available from the tower is
homogeneous. The only nontrivial ones are the twist ties and the
inherited-coordinate identities, and neither touches a row coordinate. By §2.1,
route (a) cannot produce a nonconstructive failure proof. A *constructive* failure
via a new relation would be a structure theorem; none is visible.

---

## 3. Routes (b) and (c): function-field equidistribution and counting

### 3.1 What the theorems give, and why one orbit defeats them [S + D]

| tool | statement in char 2 | what it would need |
| --- | --- | --- |
| Weil / RH for curves | `|sum_x chi(f(x))| <= (deg f - 1) q^(1/2)` | a sum over all `x` in a field |
| function-field Chebotarev (effective) | split proportion `1/p + O(g q^(-1/2))` among degree-`d` points of a fixed curve | a positive-density set of points |
| Katz 1989 | `|sum_(t in F_q) chi(theta + t)| <= (n-1) q^(1/2)` | a translate line of length `q > n^2` |
| equidistribution of Frobenius (Deligne–Katz) | angles of a family equidistribute | an algebraic family varying with a parameter |

Each one controls a set of test points of size at least the square root of the
field size. The selected data per level is one Frobenius orbit, of size at most
`E`. A concrete count for the Conway–Fermat chain [D]:

- The point `P_n` is defined over `F_q`, `q = 2^(2^(n+2))`.
- When `ord(P_n) = F_n`, the generators of `<P_n>` fall into
  `phi(F_n)/2^(n+2)` Frobenius orbits, using `|H_n| = 2^(n+2)` from `OPEN.md`.
  The selected orbit is one of them.
- Even the *averaged* statement over `<P_n>` is out of reach. `|<P_n>|` is about
  `q^(1/4)`, below the `q^(1/2)` threshold at which Weil-type bounds for
  character sums over subgroups of `E(F_q)` (Kohel–Shparlinski type [S]) become
  nontrivial.
- Over all of `E(F_q)` the Weil bound does give a `1/p` split proportion, but
  among about `q/2^(n+2)` orbits, of which the selected one is a single member.

The only families that contain every selected point are:

- the translate lines (§3.2);
- the alternative radicand towers `kappa_h + m'_r` (a finite average, in which the
  literal tower is one member);
- the set of rows sharing `h` (CRT-independent, no averaging).

None has the selected point at positive density.

### 3.2 The translate-line window [D]

`model.md` §3.6 gives the Katz upper end: `m_p < q` whenever
`2^(2^(a-1)) > n - 1`, hence `m_p < E^4`. Here is the matching lower end.

**Proposition.** Let `F_q` be contained in `F_(2^d)`, let `p | 2^d - 1` be odd,
and suppose

```text
q log_2 p < d/2 - log_2(q + 2).
```

Then some `theta` of exact degree `d` has `theta + t` a nonzero `p`-th power for
every `t` in `F_q`.

*Proof.*

- Let `chi` have order `p`. For `theta` outside `-F_q`, the product
  `prod_t (1/p) sum_(j=0)^(p-1) chi^j(theta + t)` is the indicator of the event.
- Expanding gives a main term `2^d p^(-q)`. The other terms are
  `p^(-q) sum_theta chi(prod_t (theta+t)^(j_t))` with `0 <= j_t < p`, not all zero.
- Each such polynomial has at most `q` distinct roots and is not a `p`-th power.
  So Weil bounds every sum by `(q-1) 2^(d/2)`.
- Removing `theta` in `-F_q` costs at most `q`. Removing `theta` in proper
  subfields costs at most `2^(d/2+1)`.
- What remains is at least `2^d p^(-q) - (q+1) 2^(d/2) - q`, which is positive
  under the hypothesis.

**Consequence.** Any proof of `m_p < q` that uses only the degree of `kappa` needs
`q >~ d/(2 log_2 p)`. Lenstra's question asks for a fixed `q` as `d -> infinity`,
so it cannot be answered by degree-uniform statements.

- Boundedness is therefore a selected-point statement too, although a much weaker
  one than the rule.
- The rule itself is the case `q = 1`.
- The model's confidence in boundedness (`model.md` §3.4) is real, but it is
  heuristic in exactly the same way.

### 3.3 Counting and pigeonhole [D]

- A pigeonhole contradiction needs the selected objects to outnumber the states
  compatible with success.
- Per level, the selected object is one orbit. The success set
  `F^x \ pF^x` has density `1 - 1/p`. So no single-level pigeonhole is possible.
- Across levels there is no linking identity (§1). So there is no multi-level
  counting either.
- The known order lower bounds point the wrong way for the failure direction:
  - packing gives `ord >= 2^(c sqrt h)`;
  - the Fermat packet bound gives `phi(delta_n) >= 2^(n+2)`;
  - Voloch-type bounds are similar.
  These are lower bounds of size about `2^(sqrt h)`. A failure needs an *upper*
  bound `ord(T_h) <= |G|/p`, and nothing in the tower supplies upper bounds on
  orders.
- Wiedemann's tower `x_n` has the same status. Its relation to `u_n` is not a
  power map (OPEN.md), so there is no transfer.

---

## 4. Route (d): reciprocity, and the arm C theorem

### 4.1 Theorem C [D]

**Setup.**

- Let `k >= 1`, `m = 3^(k+1)`, and `K = K_k = Q(zeta_m)^+`, which has degree
  `3^k`. It is the `k`-th layer of the cyclotomic `Z_3`-extension of `Q`.
- Let `G = Gal(K/Q)`. Since 2 is a primitive root mod 9, and hence mod every
  `3^j`, `G` is cyclic, generated by the Frobenius `sigma_2`, and `2` is inert
  in `K` with residue field `F = F_(2^(3^k))`.
- The paper's half-angle reduction shows that `zeta_k = kappa_(3^k)` is a
  primitive `m`-th root of unity and that arm C at level `k` is the primitivity of
  `gamma_k = zeta_k + zeta_k^(-1)` in `F`.
- So `gamma_k` is the reduction mod 2 of the real cyclotomic unit
  `eta = zeta_m + zeta_m^(-1)`, for the unique prime above 2, and up to Frobenius.
- The selected element of an arm C row `p` (`f(p) = 3^k`) is `zeta_k + 1`, of
  degree `2 * 3^k`. Its norm to `F` is `(1 + zeta)(1 + zeta^(-1)) = gamma_k`, so
  **row `p` fails iff `gamma_k` is in `F^(x p)`.**

Let `rho : O_K^x -> F^x / F^(x p) = Z/p` be reduction mod 2. Let
`psi : G -> F_p^x` be the character with `psi(sigma_2) = 2 mod p`. This is
well-defined because `2^(3^k) = 1 mod p`.

**Theorem C.**

1. `rho(sigma u) = psi(sigma) rho(u)`. Hence `rho` factors through the
   `psi`-eigenline `V_psi = e_psi(O_K^x ⊗ F_p)`, and `dim V_psi = 1`.
2. `eta` generates `C^+/{±1}` as a `Z[G]`-module, where `C^+` is the group of
   cyclotomic units, and `[O_K^x : C^+] = h^+(K)`.
3. Row `p` fails iff `rho(eta) = 0` iff
   (`e_psi(eta) = 0` in `V_psi`) or (`rho = 0` on `V_psi`).
   - The first alternative holds iff `p` divides
     `|e_psi((O_K^x / C^+) ⊗ Z_p)|`. By the Gras conjecture (a theorem for
     `p` not dividing `[K:Q]`), this is the same as `e_psi Cl(K) ⊗ Z_p != 0`.
   - The second alternative holds iff the prime `2 O_K` splits completely in
     `K(mu_p, (O_K^x)^(1/p))`.
4. In particular:
   - if `p` does not divide `h^+(K)`, **row `p` holds iff 2 does not split
     completely in `K(mu_p, (O_K^x)^(1/p))`**. This statement is independent of
     `eta`, so the selection has disappeared;
   - if `p` divides the `psi`-part of the unit index, row `p` fails.

*Proof.*

- (1) Mod `2 O_K`, `sigma_2(u) = u^2`. So `rho(sigma_2 u) = 2 rho(u)`, and `rho`
  is equivariant for the target character `psi`.
  - Since `p != 3`, `F_p[G]` is semisimple. Every character of `G` takes values in
    `mu_(3^k)`, which lies in `F_p` because `3^k | p - 1`. An equivariant map to
    the `psi`-isotypic target kills every other eigenspace.
  - By Dirichlet, `O_K^x/{±1} ⊗ Q_p = ⊕_(psi' != 1) Q_p(psi')`, and `psi` is
    nontrivial because `2 != 1 mod p`. Since `Z_p[G]` is a product of copies of
    `Z_p`, the lattice decomposes into rank-one pieces, and so `dim V_psi = 1`.
- (2) This is standard for prime-power conductor (Washington, *Cyclotomic Fields*,
  Lemma 8.1 and Thm 8.2).
  - The real cyclotomic units are generated by `-1` and
    `xi_a = zeta^((1-a)/2)(1-zeta^a)/(1-zeta)`.
  - We have `xi_(ab) = xi_a sigma_a(xi_b)`, and every `a` is `±2^j`, so the
    module is generated by `xi_2 = zeta^(1/2) + zeta^(-1/2)`.
  - Also `eta = sigma_2(xi_2)`, and the index is `h^+`.
- (3) `e_psi(C^+ ⊗ Z_p)` is the rank-one submodule generated by `e_psi(eta)`,
  inside the rank-one `e_psi(O^x ⊗ Z_p)`, with index `|e_psi(coker)|`.
  - The splitting criterion is Kummer theory. `K(mu_p)/K` is split at 2 because
    `mu_p` lies in `F`. A unit is a `p`-th power mod a prime above 2 iff that prime
    splits in the Kummer extension generated by its `p`-th root, and the residue
    field is `F` for every such prime.
  - The Gras step is cited: Mazur–Wiles; Kolyvagin and Rubin's Euler systems; see
    Washington, 2nd ed., Ch. 15.

**Checks [N].** For `k <= 5` arm C is proved or certified (OPEN.md). This is
consistent with the theorem if `h^+(K_k)` has no row-prime part at those levels.
PARI `bnfinit` (conditional on GRH, not certified) gives `h^+ = 1` for the
conductors 9, 27 and 81 (`k = 1, 2, 3`), so the Weber index is closed there and
the arm C rows at `k <= 3` are purely the unit-splitting statement of part 4.
I recall `h = 1` for conductor 243 from the literature, but did not compute it. I did not run a separate numerical check of
Theorem C: its content is the equivariance in part (1), which is the paper's
rank-one saturation `s_(j,c) = s^(2^j c)`.

### 4.2 The three regimes, and why Jensen's method does not transfer [S + D + H]

Put `F' = K(mu_p)`. Let `u` generate `V_psi`. Then `F'(u^(1/p))/F'` is cyclic of
degree `p` with Galois action `omega psi^(-1)`, an odd character.

- **(R0) `p` does not divide `B_(1, omega^(-1) psi)`.** Then the
  `omega psi^(-1)`-part of `Cl(F')[p]` is trivial (Herbrand–Ribet / Mazur–Wiles
  direction [S]). So `F'(u^(1/p))/F'` is ramified at `p`, and `rho(u)` is a
  Hilbert symbol at `p` of `u` against a Stickelberger (Gauss-sum) generator of
  a power of `P | 2`.
  - Its leading term pairs the `p`-adic logarithm (Fermat quotient) of `u` with
    `S = sum_x L(x)(-1)^(Tr x)`, the additive-character-weighted discrete
    (**Correction:** `S` vanishes identically mod `l`, because every order-`l`
    Gauss sum over `F_(2^N)` is `-1 mod lambda^2`; see `overnight/B3-armC.md`
    Lemma 3.1, Codex-confirmed. The leading term must be read from the
    twisted sum of B3 Thm 3.4.)
    logarithm.
  - `S` is a full-field sum, no easier than the original symbol.
- **(R1) `p` divides `B`, with the class line nontrivial.** Then `u` can be a local
  `p`-th power, the Kummer extension can be unramified, and `rho(u)` is an
  ideal-class character evaluated at `[P]`.
  - This is the paper's `r = 11`, `p = 23` situation in arm O ("one contributing
    Stickelberger scalar vanishes with exact 23-adic valuation one"). The row
    still holds there.
- **(R2) `p` divides `h^+_psi`.** This is forced failure.

**Why Jensen's method does not apply** [D for the structure, H for the
conclusion].

- The one classical nonconstructive "infinitely many `p` divide an arithmetic
  quantity" theorem in this circle is Jensen's proof that there are infinitely
  many irregular primes [S]. It works because `B_k` satisfies Kummer congruences
  and von Staudt–Clausen.
- In Theorem C the Bernoulli-controlled quantity only switches between regimes
  (R0) and (R1). Neither regime forces `rho(u) = 0`.
- The forcing quantity is the plus-part index `h^+_psi`, which has no Bernoulli
  formula.
  - Its `p`-adic analytic avatar `L_p(1, psi)` is a sum of `p`-adic logarithms of
    cyclotomic units (Leopoldt [S]). It agrees mod `p` with `B_(1, psi omega^(-1))`
    (Washington Cor. 5.13 [S]).
  - But divisibility of `L_p(1, psi)` measures whether units are locally `p`-th
    powers, which is regime (R1). It does not measure `h^+_psi` itself.
- **[H]** So a Jensen-type argument could at best produce infinitely many
  degenerate-regime rows, and those carry no forced failure.

### 4.3 The template, and the comparison with Wieferich [S + H]

| statement | prime that must split | in which degree-`p` Kummer extension |
| --- | --- | --- |
| `p` is base-2 Wieferich [S] | `p` (above `p` in `Q(mu_p)`) | `Q(mu_p, 2^(1/p))` |
| arm C row `p` fails, `p` not dividing `h^+` [D] | `2 O_(K_k)` | `K_k(mu_p, (O_(K_k)^x)^(1/p))` |
| arm O/Z row `p` fails | the prime over 2 on the inert ray | the marked ray-class Kummer line (excess.tex) |

In every line, a prime of controlled norm must split completely in a cyclic
degree-`p` extension determined by `p`.

- The heuristic probability is `1/p` [H] and the expected count is `lnln`.
- Infinitude is open in every known instance. Even the complementary "infinitely
  many non-Wieferich primes" needs abc (Silverman 1988 [S]).
- `model.md` §5.2 proves the success-direction analogue for arm O cells,
  conditional on finitely many Wieferich primes in O cells.

**Rule implies Weber-type [D, given Gras].** If arm C holds at level `k`, then by
Theorem C(3) the `psi_p`-part of `Cl(K_k) ⊗ Z_p` vanishes for every prime `p` with
`f(p) = 3^k`.

- This is a fragment of the conjecture that `h(K_k) = 1` for all `k`, the 3-adic
  analogue of Weber's class number problem. That conjecture has partial results
  by Horie, Morisawa and Fukuda–Komatsu; I cite the area, not specific bounds.
- The row primes satisfy `p = 1 mod 3^k`. They are therefore never primitive
  roots mod 9, which is the hypothesis of Horie's criterion as I recall it.
- So the rule implies something believed true, not something known. There is no
  contradiction to exploit.

### 4.4 Speculation: the Conway–Fermat chain is the CM analogue [H]

- The curve `y^2 + y = x^3 + x^2` has 5 points over `F_2`. So `a_2 = -2`, the
  Frobenius is `pi = -1 ± i`, and the curve is supersingular with Frobenius in
  `Z[i]` (computed by hand).
- Then `pi^8 = 16`, which gives
  `#E(F_(2^(2^(n+2)))) = (2^(2^(n+1)) - 1)^2`. This contains `F_n^2`, and
  `pi^(2^(n+2))` acts trivially on `E[F_n]`. This is consistent with `OPEN.md`'s
  `H_n` of order `2^(n+2)`.
- By Deuring lifting, `(E, pi)` lifts to a curve with CM by `Z[i]`. If `g` has
  torsion-supported divisor, then `u_(n+1) = g(P_n)` is the reduction of an
  elliptic unit in a ray class field of `Q(i)` of conductor dividing `F_n`.
- An analogue of Theorem C would then replace `h^+` by the elliptic-unit index,
  which Rubin's main conjecture for `Q(i)` relates to ray class numbers.
- Not checked; included as the natural next object if someone pursues route (d)
  in arm ZF.

---

## 5. Route (e): does the rule imply something false? [D + H]

The rule implies, among other things:

- primitivity of every `gamma_k`, which is the type-(3^k, 2) Gaussian-period
  primitivity. For Gaussian periods only order lower bounds are known: Gao,
  von zur Gathen, Panario (and the paper's packing). No non-primitivity theorem
  exists for any infinite family that I know of;
- `delta_n = F_n` for every Fermat number, which has no tension with any known
  factorization fact;
- the Weber-type vanishing of §4.3;
- for each `p`, that 2 does not split completely in the arm C Kummer field of
  Theorem C.

Each is either open or believed true. Implications into known-false territory
would require a theorem of the form "infinitely many members of a natural family
of cyclotomic or Gaussian-period elements are non-primitive". I know of none.
Trivial families (norm-one elements, subfield elements) are excluded by the forced
structure already accounted for.

---

## 6. Symmetric question: is there structure that forces the rule?

### 6.1 Known forcing mechanisms, and where they act [N]

All of them act where the model's failure mass is negligible, or on finitely many
tiny rows:

- **Degree-forced rows.** These are rows where the `p`-th powers of `F_(2^h)^x`
  form a proper subfield group, i.e. `(2^h-1)/p | 2^d - 1` for some `d | h`,
  `d < h`. Then any `T_h` of exact degree `h` succeeds.
  - Up to 727 these are `p = 3, 5, 7, 17, 31, 73, 127, 257` [N, `mass.py`]. They
    carry `0.79` of the `1.65` total `sum 1/p` mass in `[3, 727]`.
  - `P(all rows <= 727 succeed | model)` is `0.17` with them and `0.42` without
    them [N]. `model.md` §2.1 gives `0.42`–`0.49` for `11 <= p <= 727`.
- **Arm D with `Psi_k` prime, packing, and bottom-ancestor sections.** These prove
  rows with `|G'|/p` small, i.e. with `p` near the full primitive part.
  - The model's mass sits at small `p` relative to `Pi_h`.
  - So these theorems settle rows that the model already rates as almost surely
    successful. Within the model they are uninformative, though valuable as
    proofs.

### 6.2 Correlation tests

**On the Conway elements** [N, by sibling screens]. `design/chars.py` and
`design/shortcuts/chars2.py` record power-residue statuses at all small primes.

- At row primes, everything succeeds (expected failures 0.33 + 0.35).
- At non-row primes, arm Z looks random (`z = -0.39`).
- Arm O shows an excess of `l`-th powers (`z = +3.3`). The source is inheritance.
  - At `l` with `f(l)` dividing the base degree, the coordinate of `1 + chi_(r^a)`
    equals that of its norm `1 + chi_(r^(a-1))` or `1 + alpha_r` (§2.3).
  - For `m_r = 1`, `1 + alpha_r = kappa_(f(r))`, which is a forced `l`-th power at
    every arm O/C row `l` of conductor `f(r)`.
- So the excess is structure we already know.

The twist lemma accounts for the remaining exact ties.

**Control: canonical Gaussian periods** [D + N]. `gauss_chars.py` covers
`l <= 2*10^4` (839 primes) with 2 a primitive root mod `l`, so that `alpha_l` is canonical up to
Frobenius. It computes exact power statuses at 30 small primes by norm reduction
in `F_2[x]/(x^l - 1)`; squaring is a rotation, and `Phi_l`-membership is
`y xor 1 in {0, all-ones}`.

*Proposition G [D].* Let `l = 5 mod 8` be prime with 2 primitive mod `l`, and put
`n = (l-1)/2`. Then `alpha_l` is a cube in `F_(2^n)` iff `eps in Z[sqrt l]` or
`3 | h(Q(sqrt l))`.

*Proof.*

- Let `k = Q(sqrt l)` and `H` be the squares mod `l`. 2 is a non-square and 4 is a
  square.
- `N_(Q(zeta)/k)(eta) = N(zeta^(-1)) N(1-zeta^4)/N(1-zeta^2) = A/B`, where
  `A = prod_(a in H)(1 - zeta^a)` and `B` is the product over non-squares.
- By Dirichlet's class number formula, `B/A = ±eps^(±2h)`. Since `eta` is real,
  `N_(K/k)(eta)^2 = ±eps^(-+2h)`, so `N_(K/k)(eta) = ±eps^(-+h)`.
- 2 is inert in `K`, and `O_k/2 = F_4` because `l = 5 mod 8`. So
  `N_(F_(2^n)/F_4)(alpha) = (eps mod 2)^(-+h)`.
- `alpha` is a cube iff this norm is 1. Also `eps mod 2 = 1` iff `eps` lies in
  `Z + 2 O_k = Z[sqrt l]`.

*Data [N].*

- The formula agrees with direct exact computation in all 418 cases
  `l <= 2*10^4`, with 0 mismatches (`cube_formula.py`, `cubic_channel.py`).
- **Partial, direct, `l <= 2*10^4` (`gauss_all_2e4.log`).** At the 17 test
  primes with any tests, the aggregated power frequencies match `1/p`
  (`|z| <= 1.4`, except `p = 151` at `z = +2.3` on 2 hits).
  - At `p = 3` the direct frequency is `148/418 = 0.354`, `z = +0.9`. In this
    range the class-number channel is still small; the bias shows only in the
    larger range below.
  - A direct run to `10^5` at `p = 3, 7, 31, 127` was stopped by the lead before
    finishing, and no output was kept.
- Statistics up to `l <= 2*10^5` (3377 primes):
  - `P(eps in Z[sqrt l]) = 0.314`, the local channel. This is near `1/3`, i.e.
    `eps mod 2` roughly uniform on `F_4^x`, which is the Eisenstein-problem
    distribution.
  - `P(3 | h) = 0.124`.
  - `P(both) = 0.038`, against `0.039` for independence.
  - `P(cube) = 0.399`, against the naive `1/3`: `+8.1 sigma`.
- By range (`cube_bins_2e5.log`, formula-based):

  | `l` range | N | `P(eps in Z[sqrt l])` | `P(3 | h)` | `P(cube)` |
  | --- | --- | --- | --- | --- |
  | `(0, 2e4]` | 417 | 0.283 | 0.113 | 0.355 |
  | `(2e4, 1e5]` | 1385 | 0.308 | 0.128 | 0.399 |
  | `(1e5, 2e5]` | 1575 | 0.327 | 0.123 | 0.411 |

- [H] If `eps mod 2` is uniform on `F_4^x` and `3 | h` has its Cohen–Lenstra
  frequency `0.160` for real quadratic fields, then
  `P(cube) -> 1/3 + (2/3)(0.160) = 0.44`. The local channel tends to `1/3`; the
  class-number channel adds a permanent bias.

*Cubic channel at `l = 7` [D + N].* The same argument puts the `7`-coordinate of
`alpha_l` (when `3 | n`) on the unit lattice of the cyclic cubic field `K_3` of
conductor `l`. Here `[E:C] = h(K_3)`, and only the `psi`-component
(`sigma_2 -> 2 mod 7`) is seen by reduction mod 2.

Partial data, direct, `l <= 2*10^4` with `3 | n` (343 cases):

| case | N | 7th powers | frequency |
| --- | --- | --- | --- |
| 7 does not divide `h(K_3)` | 331 | 45 | 0.136 (naive 0.143) |
| 7 divides `h(K_3)` | 12 | 5 | 0.42 |

This is the same mechanism as at `p = 3`: the class-number channel raises the
power frequency and the unit channel stays near `1/7`. The 7-divisible sample is
small, and I did not split it by eigencomponent.

**What the control says about the row model [H].**

1. Natural selected cyclotomic elements are biased *toward* `p`-th powers wherever
   a global (class-group) channel exists.
2. In arm C rows, the global channel is exactly the Weber-type index of
   Theorem C, which is expected never to open for `p = 1 mod 3^k` large. So the
   row failure probability is the local channel, which has `1/p` scale.
3. A conjectural global channel in arms O/Z (a class line in the relevant
   eigen-component) would add `O(1/p)` and can only increase the failure
   probability.

So the divergence of the expected failure count is robust to every structural
correction I can identify. None of them pushes toward success.

**For `model.md` §7.1** (calibration on non-row phases). A departure from `1/l` at
small *inherited* primes is expected from global channels of small subfields. It
should not be read as evidence about row coordinates, and a clean `1/l` would not
be strong support either. The informative calibration is at *fresh* non-row primes
of the top layer, and in arm O there are none: the four-arm reduction makes every
fresh prime of the layer a row.

---

## 7. What it would take

- **A nonconstructive failure proof** needs one of the following:
  1. a theorem producing infinitely many `p` for which a prime of controlled norm
     splits completely in a `p`-dependent cyclic degree-`p` extension, as in the
     §4.3 template. No such theorem is known in any instance; Wieferich is the
     simplest.
  2. a non-homogeneous ancestry identity tying `beta_p` to an anchor (§2.1).
     This would be a structure theorem and would probably locate the failure, so
     it would be constructive.
  3. a positive proportion of plus-part divisibilities `p | h^+_psi(K_k)` along
     the 3-adic tower, which would force arm C failures. This is expected to be
     false (3-adic Weber).
- **A proof of the rule** would need, in arm C alone and given `p` not dividing
  `h^+`, that the prime 2 of every `K_k` never splits completely in the unit
  Kummer field at any row prime. This is a "never" statement for a `1/p`-type
  event. The model gives it probability `0.9999` overall (the arm C mass is tiny),
  but no mechanism exists.
- **Search remains the only route to a counterexample.** Arms Z and O carry the
  mass. The model places the first failure beyond `X` with probability
  `~ ln 727 / ln X`: median about `5e5`, and 24% beyond `10^12`.

---

## 8. Files

All files are in this directory.

- `nonconstructive.md`: this file.
- `ExcessHeuristic.lean`: Borel–Cantelli skeleton. Compile with
  `cd /Users/a9lim/Work/ogdoad/formal && lake env lean <path>`; it ends with
  `#print axioms`.
- `mass.py`: masses, record probabilities, degree-forced rows.
- `twist_check.py`, `orbit_check.py`, `tower_copy.py`: twist-lemma and
  translate-class checks on exact towers. `tower_copy.py` is a copy of
  `design/shortcuts/tower.py` with its import path fixed.
- `translate_coords.py` was stopped without output.
- `gauss_chars.py`: exact power statuses of canonical type-II Gaussian periods.
  Outputs `gauss_chars_<L>[_tag].pkl`; `gauss_all_2e4.log` is the completed run.
- `cube_formula.py`, `cube_stats_big.py` (`cube_bins_2e5.log`),
  `cubic_channel.py`: Proposition G checks and class-number channel statistics.

Nothing under `/Users/a9lim/Work/ogdoad` was modified. Sibling files (`model.md`,
`model_calc.py`, `census_fast.py`, `axioms.lean`, ...) were read, not edited.
