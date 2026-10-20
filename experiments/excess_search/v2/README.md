# Engine v2: crossed-binomial tests for rows of the 0/1/4 excess rule

Exact engine (C++/NTL) plus planner and driver. For a row `p` it tests the
selected element in two small fields, of degrees `B` and `R t`, instead of
one field of degree `E = R B`. Every structural fact the reduction uses is
checked exactly; anything outside the supported shapes is refused, and the
reason is reported.

All CPU times below are user+sys CPU seconds of the engine process. The M5
was heavily shared during this work (load average 50 to 130 on 18 cores), so
wall times are 2 to 6 times larger and are not meaningful. gf2x here is the
conda build, which has no PMULL path; `../design/arith/b-pmull` has a NEON port
measured about 10x faster. The engine has not been rebuilt against it.

## Files

| file | role |
| --- | --- |
| `v2engine.cpp` / `v2engine` | the engine (final binary) |
| `v2engine.prelim` | earlier binary used for the preliminary 838-row validation (no cyclotomic split, no explicit degree/multiplicity check) |
| `plan.py` | row planner: path choice, cut `t`, closure program; also emits reference-engine programs |
| `census2.py` | census functions (copy of `../census.py` logic without the argv-dependent sieve) |
| `driver.py` | runs a row (or rows sharing `h`) with v2 when a path applies, otherwise with the reference-engine copy when `E <= 60000`, otherwise refuses; reports `path` |
| `search_v2.py` | dependency-aware search over uncovered rows (stopped by the lead; see "By-product") |
| `validate_v2.py` | validation harness |
| `refengine_copy.cpp` / `refengine` | unmodified copy of `../ref/refengine.cpp`, run in `refcache/` |
| `thetacheck.cpp` | minimal polynomial and phases of the quoted 359-certificate theta |
| `coverage.py`, `coverage_100000.json`, `coverage_B1e6_Rt1e6.tsv` | structural coverage census and row list |
| `validation_log.jsonl` (final binary), `validation_log_prelim.jsonl` | per-row validation records |
| `timing/final_*.json` | timing records for the final binary |
| `results_v2.jsonl` | rows computed by the (stopped) search |
| `cache/` | sparse irreducible moduli built here (the engine also reads `../ref/irred_*.txt`, read-only) |

Usage:

```sh
python3 driver.py 1433            # one row; prints a JSON record with path, m, per-translate results, CPU by phase
python3 driver.py 359,1433        # rows sharing h = 179, one engine run
V2_MINPOLY=1 python3 driver.py 359,1433   # also print the F_2-minimal polynomial of each norm
V2_DIRECT=30000 python3 driver.py 733     # also run the full-exponent Euler test when R t <= 30000
python3 plan.py 1433 | ./v2engine [--direct N] [--minpoly]
```

## Mathematics

### Paths

* **singleton** (arms O, C, D): `Q(h) = {R}`, `R = r^a` odd. `z = chi_R`,
  `z^R = A = alpha_r`. Parent field `K = F_2(alpha_r, translates)`, degree
  `B = lcm(b_r, d(rule))`. Targets `z + m` for every `m = 0..rule`. The rule
  translate must not be a p-th power; the smaller translates must be.
* **ratio** (arm Z, `Q = {R1, R2}` odd prime powers): `beta = y1 + y2 =
  y2 (1 + z)`, `z = y1/y2`, `z^(R1 R2) = alpha_r1^R2 / alpha_r2^R1`.
  Requires `h` not dividing `d(y2)`, so `y2` is a p-th power, and
  `E = R1 R2 B` with `B = lcm(b_r1, b_r2)`. The second condition excludes
  inherited prime-power levels. Both alphas are built in one synchronized model,
  so a shared `chi_3` is one element.
* **finite** (arm Z, `Q = {2^k, R1}`): `y2 = chi_{2^k}` lies in `K`;
  `z^R1 = alpha_r1 / chi_{2^k}^R1`.
* Everything else is refused: Z rows with three or more components, inherited
  levels (`E != R B`), and arm ZF. The driver then falls back to the reference
  engine when `E <= 60000`.

### Crossing

The cut `t` is the smallest admissible value:
`t0 = lcm(h/gcd(h,R), d(rule), f(l), l^{v_l(B)} for primes l | R)`. Then
`D = B/t`, `k = F_{2^t}`, `N = 2^B - 1`, `G = prod_l l^{v_l(N)}`,
`n = (2^B-1)/(2^t-1)`, `w = n^{-1} mod G`, `c = N_{K/k}(A)^w`, and
`a = (A/c)^{R^{-1} mod N/G}`. These are Codex's formulas, and they check out.
`H = k[V]/(V^R - c)` and
`W_m(V) = N_{K(z)/H}(m + aV) = V^D F_a(m/V)`, where `F_a` is the characteristic
polynomial of `a` over `k`. This is reduced by `V^R = c`.

Why the reduction is exact. Write `L = K(z)`. Since `c` is not an l-th power in
`k` for each `l | R`, and `v_l(2^t-1) = v_l(2^B-1)`, `c` is also not an l-th
power in `K`. Hence `A = c a^R` is not an l-th power in `K`, and `X^R - A` is
irreducible over `K`. So `[L:K] = R` and `L = F_{2^{RB}} = F_{2^E}`. The planner
checks `E = R B`. Because `gcd(D, R) = 1`, `K ∩ H = k` and `KH = L`. The element
`aV` is a root of `X^R - A` in `L`, so it is a Gal(L/K)-conjugate of `chi_R`
(or of `y1/y2`), and the p-th-power status is unchanged. Gal(L/H) restricts
isomorphically onto Gal(K/k), which gives the formula for `W_m`.

### Euler test

* **Norm first.** `beta^((2^E-1)/p) = W^((2^{Rt}-1)/p) = N_h^((2^h-1)/p)`,
  where `N_h = N_{H/F_{2^h}}(W)` is a product of `Rt/h` conjugates under the
  `2^h`-Frobenius. That product is computed by doubling, in `O(log(t/s))` H-products.
* **Frobenius on H.** `V^(2^e) = C V^j` with `j = 2^e mod R` and
  `C = c^{((2^e - j)/R) mod (2^t-1)}`. This is a permutation-with-multipliers on
  the `V^i` basis plus coefficient Frobenius (modular composition in `k`).
  Squaring is binomial-aware: one coefficient square each, and a multiplication
  by `c` on wrap. Runs of squarings inside exponentiations are replaced by one
  Frobenius map.
* **Cyclotomic split (new; not in Codex's design).** Let `q1 < q2` be the two
  smallest primes of `h`. Then
  `2^h - 1 = P1 P2 Rest`, where `P1 = 2^{h/q1} - 1` and
  `P2 = (2^{h/q2}-1)/(2^{h/(q1 q2)}-1) = sum_{i<q1} 2^{i h/(q1 q2)}`. Since
  `p | Rest`, `N_h^((2^h-1)/p) = 1` holds iff `Y := (N_h^{Rest/p})^{P2}`
  satisfies `Y^{2^{h/q1}} = Y`. The exponent shrinks from `h` bits to about
  `h (1-1/q1)(1-1/q2)` bits; `P2` costs `q1 - 1` Frobenius maps, and the test
  is one Frobenius. On 4507 this cut the Euler step from 30.5 s to 10.0 s.

### Characteristic polynomial and the map to the k-model

* The exact degree `d` of `a` over `k` is the least `d | D` with
  `a^(2^{td}) = a`. `P_a = prod_{i<d}(T + a^(2^{ti}))` comes from NTL
  `BuildFromRoots` over `GF2E = K`. Its coefficients are checked to lie in `k`,
  and `P_a(a) = 0` is checked. Then `F_a = P_a^{D/d}`, Codex's multiplicity
  correction, applied explicitly. For singleton rows, `d = D` always (`a`
  generates `K` over `k`). In every row run here, `d = D`.
* The k-model is `F_2[y]/(g)`. Here `g` is the minimal polynomial of
  `theta = Tr_{K/k}(random)`, checked exactly: it has degree `t`, is Rabin
  irreducible, and `g(theta) = 0`. When `t = B`, the k-model is K's own sparse
  model.
* Elements `x` of `k` are mapped by power projection. Take
  `s_j = lambda(theta^j)` and `u_j = lambda(x theta^j)` for `j < t`, using NTL
  `ProjectPowers` and `UpdateMap`. Then `A_s = (g * rev(s)) >> t`, `A_u`
  likewise, and `Q = A_u A_s^{-1} mod g`. The result is verified per element
  by `Q(theta) = x`.

### Components in K

The method is the reference engine's: one sparse model, dependency order, and
exact roots. The Kummer root is cheaper here. The radicand lies in
`F_{2^{deg/ell}}`, which is checked. The engine computes
`y0 = a^{ell^{-1} mod ell-free part of 2^{deg/ell}-1}`, which is a
`deg/ell`-bit exponent, instead of the reference engine's E-bit exponent. It
then applies a Pohlig-Hellman correction in `mu_{ell^v}`, using a Sylow
generator obtained from a cheap relative norm to `F_{2^{ord_{ell^v}(2)}}` and
BSGS discrete logs.

## Exactness checks performed by the engine

Every run prints each check with its count (`CHECK <name> xN`).

* **Arithmetic and cut validity:** `t | B`; `R` odd > 1, with its primes listed
  exactly; `gcd(B/t, R) = 1`; for every `l | R`, `l | 2^t-1` and
  `v_l(2^t-1) = v_l(2^B-1)` (exact big integers); `h | R t`; `f(p) = h` for
  each tested `p`; `p | 2^h-1`; the cyclotomic split divides `2^h-1`; `p | Rest`.
* **Models:** the K modulus has degree `B` and is irreducible (Rabin's test).
  The k modulus is irreducible (Rabin), `g(theta) = 0`, and `theta` lies in `k`.
* **Components:** every component degree divides `B`. Each AS root satisfies
  `y^2 + y = a`. For Kummer roots: the radicand lies in `F_{2^{deg/ell}}`,
  `ell | 2^deg - 1`, `ord_{ell^v}(2)` is correct, the Sylow generator has
  exact order, every dlog digit is found, the radicand is an ell-th power in
  `F_{2^deg}`, and `y^ell = a`. Every component has exact degree, meaning
  `y^(2^deg) = y` and `y^(2^(deg/q)) != y` for each prime `q | deg`. Every
  radicand and AS constant is nonzero.
* **Crossing:** `c` lies in `k` and is nonzero; `a^R = A/c`; `a^(2^B) = a`.
  For each `l | R`, `c` is not an l-th power in `k`, which certifies that
  `V^R - c` and `X^R - A` are irreducible.
* **Characteristic polynomial:** the degree of `a` over `k` is exact. The
  minimal polynomial is monic of degree `d`, has coefficients in `k`, and
  annihilates `a`. The characteristic polynomial is monic of degree `D` with
  coefficients in `k`. The mapped characteristic polynomial is monic.
* **k-map:** `Q(theta) = x` for every mapped element.
* **Translates:** each lies in `k`.
* **Euler:** the target norm is nonzero; `N_h` lies in `F_{2^h}`; the
  Frobenius exponent splits exactly; the norm and relnorm doubling counts are
  correct. As a phase sanity check, `(Y^p)^(2^{h/q1}) = Y^p`.
* **Optional cross-checks:** with `--direct`, the plain h-bit Euler power
  agrees with the cyclotomic split, and the full `W^((2^{Rt}-1)/p)` equals the
  norm-route phase elementwise. With `--minpoly`, the minimal polynomial
  annihilates `N_h` and is irreducible with degree dividing `h`.

Not checked by the engine:

* **Planner (Python):** the term-algebra relations themselves (the same logic
  as `../ref/rowprog.py`), the census degrees used as targets of the degree
  checks, and `E = R B`.
* **NTL library:** the arithmetic of `BuildFromRoots`, `MinPolyMod` and
  GF2EX products is trusted. Its outputs are checked as listed above, and the
  direct cross-checks exercise the H arithmetic.

## Validation

**Final binary** (`validation_log.jsonl`): 515 rows, `7 <= p <= 5171`. The lead
asked for a bounded set, so the run was stopped there.

* Paths: 235 singleton, 219 ratio, 61 finite.
* Arms: 228 O, 280 Z, 4 C, 3 D. The C/D rows are 7, 19, 73, 163, 487, 1459
  and 2593.
* E from 6 to 4,994,220 (count by decade: 1, 23, 76, 135, 126, 126, 28).
  `R t` reaches 1,557,612.
* **Agreement with every source that has the row:** 0 disagreements. Sources:
  OEIS 119 rows, ref results 227, Peeters 515, certificate 1.
* **Per-translate comparison with the reference-engine copy:** 272 rows with
  `E <= 20000`, all agree. Every translate `m = 0..rule` was compared, so arm
  O/C/D rows also check the forced p-th-power translates.
* **Direct full-exponent check:** 364 rows with `R t <= 30000`. The plain
  h-bit power and the full `W^((2^{Rt}-1)/p)` both equal the norm-route and
  cyclotomic-split result elementwise. 0 failures.
* **Forced translates:** every arm O/C/D row has `m < rule` a p-th power and
  `m = rule` not.

**Preliminary binary** (`validation_log_prelim.jsonl`): all 838 known rows with
a v2 path, `p <= 12281` with `B <= 1e5` and `R t <= 1e6`: 0 disagreements. Of
these, 366 rows had a per-translate reference comparison and 437 a direct
full-exponent check. This binary differs from the final one only in the Euler
exponent routine and the absence of the explicit degree/multiplicity check.

**1433 cold and the 359 theta:** run cold (h = 179, B = 19580, t = 178, D = 110,
R t = 31862) in one engine run with 359. Results: `m_359 = m_1433 = 1`, with
`m = 0` a p-th power for both; 1.98 CPU-s total. The F_2-minimal polynomial of
`N_{L/F_{2^179}}(1 + chi_179)` is
`b66361eb7bc7c320933ab9e7e0a6ff4b153fdf65d5681`. This is identical to the
minimal polynomial of the quoted
`theta = 0x28494A54...CA4E6` in `F_2[X]/(X^179+X^4+X^2+X+1)` (`./thetacheck`).
So the 359-certificate theta is, up to Galois conjugacy, the selected norm. This
independently closes the link that Codex marked as an inherited dependency.
`thetacheck` also reproduces Codex's
`theta^((2^179-1)/1433) = 0x45bb1bf3...0909d` (not 1) and the certificate's
stored 359 phase `0x7f81a92c...2e87e`. For `m = 0` the norm is exactly 1.

**Errors in Codex's formulas:** none found. The cut rule, `w`, `c`, `a`,
`W = V^D F_a(V^{-1})` (with `m/V` for a general translate), the multiplicity
correction, and the non-diagonal Frobenius `V^q = C V^j` were all implemented as
written, and validated as described above. Codex's six-row parameter table
(B, t, R, D, Rt) matches the planner exactly. The 319 s Euler estimate for
4507 assumed the full `(2^{Rt}-1)/p` exponent. That estimate was not wrong for
the method it costed, but the norm-first route plus the cyclotomic split
measures 10.0 s.

## Measured per-row cost (final binary, CPU seconds)

"K-side" is model, components, crossing, characteristic polynomial and k-map.
"Euler" is the norm to `F_{2^h}` plus the exponent.

| p | path | h | B | t | D | R | R t | K-side | Euler | total | m |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 733 | singleton | 244 | 60 | 60 | 1 | 61 | 3,660 | 0.00 | 0.00 | 0.004 | 1 |
| 743 | ratio | 371 | 156 | 156 | 1 | 371 | 57,876 | 0.00 | 0.11 | 0.11 | 0 |
| 797 | singleton | 796 | 1,980 | 396 | 5 | 199 | 78,804 | 0.01 | 0.23 | 0.23 | 1 |
| 1031 | ratio | 515 | 408 | 204 | 2 | 515 | 105,060 | 0.00 | 0.35 | 0.35 | 0 |
| 359+1433 | singleton | 179 | 19,580 | 178 | 110 | 179 | 31,862 | 1.67 | 0.08 | 1.98 | 1, 1 |
| 839 | singleton | 419 | 37,620 | 418 | 90 | 419 | 175,142 | 5.41 | 0.67 | 6.08 | 1 |
| 1307 | singleton | 1306 | 52,812 | 652 | 81 | 653 | 425,756 | 10.47 | 3.98 | 14.45 | 1 |
| 1487 | singleton | 743 | 57,876 | 371 | 156 | 743 | 275,653 | 17.0† | 2.1† | 19.06 | 1 |
| 4507 | singleton | 4506 | 1,500 | 750 | 2 | 751 | 563,250 | 0.01 | 10.10 | 10.11 | 1 |
| 2819 | singleton | 2818 | 3,520 | 704 | 5 | 1409 | 991,936 | 0.03 | 21.02 | 21.05 | 1 |
| 16529 | finite | 8264 | 7,224 | 1032 | 7 | 1033 | 1,066,056 | 4.1* | 71.0 | 75.2 | 0 |
| 56731 | ratio | 56730 | 60 | 60 | 1 | 1891 | 113,460 | 0.00 | 7.48 | 7.48 | 0 |

`*` includes building the degree-7224 sparse modulus (4.1 s). `†` phase split from the preliminary-binary run of the same row (total 19.21 s); the final binary total is 19.06 s.

For comparison, the reference engine logged 254 s (wall, loaded) for 743. For
the 1e5 range, 1579 (B = 102180, t = 262, D = 390, R t = 68906) was attempted:
NTL `BuildSparseIrred(102180)` had not finished after 11.2 CPU minutes,
and the run was killed (see Limits).

Scaling, read off these runs:

* **K-side:** grows roughly like `B^2`. The crossing root is one B-bit
  exponent, about `B/6` sparse MulMods. The characteristic polynomial costs
  `log D` products of size `D B`.
* **Euler:** grows like `(h(1-1/q1)(1-1/q2)/6) * M_H(Rt)`, where `M_H` is an
  NTL GF2EX product of size about `2.5 * M(Rt)`, plus `log(t/s)` Frobenius
  maps. B rarely matters there; `h` and `R t` do.

## Reachable rows (structural, rule assumed for ancestors)

Rows `p <= 1e5` with a v2 path, `B <= 1e6` and `R t <= 1e6` are listed in
`coverage_B1e6_Rt1e6.tsv`. Mass is sum 1/p.

| set | rows (mass) | v2, B <= 1e6, Rt <= 1e6 | v2, B <= 6e4, Rt <= 1e6 | v2, B <= 6e4, Rt <= 4e6 |
| --- | --- | --- | --- | --- |
| all 727 < p <= 1e5 | 9463 (0.5528) | 2640 (0.3279) | - | - |
| all 3 <= p <= 1e5 | 9591 (2.2053) | 2760 (1.3769) | - | - |
| missing below 12289 (not in Peeters) | 444 (0.0781) | 166 (0.0382) | 130 (0.0293) | 211 (0.0408) |
| 12289 <= p <= 1e5 | 8123 (0.2006) | 1756 (0.0551) | 1686 (0.0531) | 2473 (0.0748) |
| uncovered total | 8567 (0.2787) | 1922 (0.0933) | 1816 (0.0823) | 2684 (0.1155) |

* **By path among the uncovered rows** (B <= 1e6, Rt <= 1e6): singleton 641
  (0.0408), ratio 1088 (0.0459), finite 193 (0.0066).
* **Arm-O rows of the missing list:** 94 of 266 fall inside B <= 1e6 and
  Rt <= 1e6. Allowing Rt <= 4e6 gives 169; allowing B <= 6e4 with Rt <= 4e6
  gives 107 rows, mass 0.0221.
* **Refused among 12289..1e5:** 1234 Z rows with three or more components, 383
  with inherited levels, 1 ZF.
* `R t` is a cost choice, not a structural limit: the H side needs no large
  irreducible polynomial. Raising the `R t` cap gains more than raising `B`.

## By-product: rows computed before the lead stopped the search

All 16 rows below come from `../missing_below_12289.json`, arm O, final binary.
All obey the rule, with `m = 1` and `m = 0` a p-th power:

839, 1019, 1307, 1433, 1487, 1619, 2027, 2153, 2477, 2767, 2819, 2963, 3229,
3581, 5381, 8609.

The h = 1076 group (2153, 3229, 5381, 8609) was one engine run. These rows
passed all of the engine's exact checks. None has an independent second
implementation; the Peeters and reference rows above are the evidence that the
method is correct.

## Limits and unverified points

* **Large B.** The 1D K model needs a sparse irreducible of degree `B`. NTL's
  `BuildSparseIrred` is fast up to about 6e4 (`../ref` cache) but did not
  finish 102180 within 11.2 CPU minutes. Moduli much beyond 1e5 are
  probably impractical by random search.
  * **Recommended fix (not implemented):** a tensor model
    `K = GF(2^{B1})[y]/(f2(y))` with `B = B1 B2`, `gcd(B1, B2) = 1`, both
    sparse moduli small, and `t | B1`. Squaring stays cheap. `k`, `c`, `F_a`
    and the translates then live in the small coefficient field. The
    characteristic polynomial becomes `N_{F/k}(minpoly_F(a)^{B2/d1})`, via
    GF2EX `MinPolyMod`. A split exists for most large-B rows (for example
    1579: 524 x 195; 2083: 2076 x 301; 1699: 188 x 1265).
* **Cost at large B.** The crossing root is a full B-bit exponent and cannot
  be avoided for a generic radicand. Expect minutes at B ~ 2-3e5 and over an
  hour near 1e6.
* **When the rule fails.** For a singleton row v2 reports `COUNTEREXAMPLE`
  when the rule translate is a p-th power, but it does not search larger
  translates: those change `d(m)`, hence `B` and `t`. For ratio and finite rows
  `beta + m` is not a binomial target, so v2 cannot compute the true excess.
  Any hit needs an independent replay.
* **Machine load.** CPU times are the measurement; wall times were inflated
  2 to 6 times by other jobs.
* **Possible speedups not done:**
  * the PMULL gf2x port;
  * a sparse k-model modulus via root finding in the dense k-model;
  * mapping `N_h` to a compact model of `F_{2^h}` when `t/s` is large;
  * the tensor K model.
