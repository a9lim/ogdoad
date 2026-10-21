# Overnight attack on the 0/1/4 rule — shared brief

Every agent in this run reads this file first. It states the problem, what is
already proved or closed, and the working rules. The authoritative sources are
`writeups/excess.tex` (4333 lines; sections listed below), `docs/OPEN.md` §2,
and the parked notes in `experiments/excess_search/notes/`.

## The problem

Conway's nim field `On_2`. For an odd prime `p`, `f(p) = ord_p(2)`. Lenstra
writes the Kummer radicand as `alpha_p = kappa_{f(p)} + m_p` with finite excess
`m_p = min{ m >= 0 : kappa_{f(p)} + m is not a p-th power in its defining
finite field }` (finite integers = finite nimbers).

`kappa_h` is the SUM of selected components `kappa_q`, `q in Q(h)`. `Q(h)` is
built recursively: with `r` the smallest prime of `h` and `q = r^{v_r(h)}`,
first compute `Q(h/q)`, then add `q` iff `q` does not divide the degree
`dsum(Q(h/q))` of the field spanned by those components (`experiments/excess_search/census.py`,
functions `Qset`, `dsum`, `b`). Component facts:

- `kappa_{2^a} = c_{a-1} = 2^{2^{a-1}}` (Fermat 2-power nimber), with
  `c_n^2 + c_n = c_0 c_1 ... c_{n-1}`; `c_0 = 2` is a primitive cube root of
  unity; nimber `4` has multiplicative order 15.
- For an odd prime `r`: `kappa_r^r = alpha_r`, `kappa_{r^{a+1}}^r = kappa_{r^a}`,
  `b_r = d(alpha_r)` (degree over F_2).
- `kappa_{3^k} = zeta_k` is a primitive `3^{k+1}`-th root of unity
  (`omega = kappa_3`, `omega^3 = 2`).
- Example: `alpha_5 = 4`, so `kappa_5` has order 75 and `kappa_{5^a}` is a
  primitive `3*5^{a+1}`-th root of unity.

**The 0/1/4 rule (conjecture).** `m_p = 0` if `Q(f(p))` is not a singleton odd
prime power; `m_p = 4` if `f(p) = 2*3^k` (k >= 1); `m_p = 1` otherwise.

**Four-arm reduction (proved, excess.tex Thm 3.1 `thm:arms`).** The rule is
equivalent to:

- `Z`: if `Q(h)` is not a singleton odd prime power, `Pi_h | ord(T_h)`, where
  `Pi_h` = full primary part of `2^h - 1` at primes with `ord_l(2) = h`, and
  `T_h = N_{F_{2^{d(kappa_h)}}/F_{2^h}}(kappa_h)`. Sub-case ZF: `h = 2^{n+1}`,
  the Conway–Fermat chain: `u_n = (c_n+1)/c_n` must generate the norm-one torus
  of order `F_n = 2^{2^n}+1` (sibling of Wiedemann's open conjecture).
- `O`: singleton `r^a`, `r != 3`: every prime `p != r` dividing
  `L_{r,a} = Phi_{r^a}(2^{b_r})` has full valuation in
  `ord(y_{r,a} F_{r,a-1}^x)`, `y_{r,a} = kappa_{r^a} + 1`.
- `C`: `gamma_k = zeta_k + zeta_k^{-1}` is primitive in `F_{2^{3^k}}^x`.
- `D`: `Psi_k | ord(M_k)`, `M_k = A_k^{q-1}`, `A_k = zeta_k^2 + zeta_k + omega`,
  `q = 2^{3^k}`, `Psi_k = Phi_{2*3^k}(2)/3`.

In arms O/C/D the bare `kappa` is FORCED to be a p-th power (its r^a-th power
lies in a field whose unit group has no p-part), which is why the predicted
values there are 1 and 4.

## Heuristic picture (random model, `notes/heuristic_model.md`)

Each row fails with probability about `1/p`. Arms C, D, O and ZF have
convergent failure sums (heuristically TRUE, finitely many failures, probably
none). Arm Z (multicomponent `kappa_h`, i.e. most primes) has divergent sum
`~ log log X`: the rule is heuristically FALSE, but the first failure is
expected far beyond reach. All rows `p <= 72481` obey the rule (exact engines),
plus Peeters' rows to 12281. So: a proof of the full rule would have to prove
arm Z for all h, against the heuristic; a disproof needs one failing row.

## Already proved or closed — do not re-derive, build on or around them

- Rank-one saturation (excess.tex §"Nim reciprocity saturation"): every
  multiplicative reciprocity word / Jacobi convolution / class function on one
  marked phase either erases it or restates it.
- Homogeneity dichotomy (`notes/heuristic_nonconstructive.md` §2.1):
  homogeneous multiplicative relations cannot prove success; a relation-based
  failure proof is automatically an explicit certificate.
- Katz window (same file §3.2): degree-only information cannot bound `m_p`
  below about `d/(2 log_2 p)`; boundedness is also a selected-point statement.
- Theorem C (same file §4, Codex-checked in `notes/codex_theoremC_and_D.md`):
  arm C row p fails iff `p | psi-part of h^+(K_k)` or `2O_K` splits completely
  in `K_k(mu_p, (O_K^x)^{1/p})`, `K_k = Q(zeta_{3^{k+1}})^+`; regimes R0/R1/R2;
  why a Jensen (irregular-primes) argument does not transfer to arm C.
- Translate ties / twist lemma: automorphisms moving kappa tie translates.
- Cross-arm primary vacuity (OPEN.md §2 "Missing step").
- Fermat chain: packet-degree bound, Voloch-transfer boundary (OPEN.md §2).
- Lower bounds `log ord >= c sqrt(field degree)` in arms C/D/O.

## Working rules (binding)

- **No searches, sweeps, or row runs.** Do not try to find a counterexample by
  computing rows. Any command must finish in under 2 minutes. A small
  computation is allowed only to sanity-check a specific lemma you have
  stated; say what it checks.
- Lean is welcome for algebraic/finite lemmas: put files in
  `experiments/excess_search/notes/overnight/lean/` and check with
  `cd formal && lake env lean ../experiments/excess_search/notes/overnight/lean/<File>.lean`
  (Mathlib v4.32.2 prebuilt; ~10 s for light imports). Do not edit `formal/`.
- Write your work to your own notes file named in your brief; edit nothing else
  in the repo.
- Tag every claim: **[S]** standard/cited, **[D]** derived here with proof,
  **[N]** checked by a named small computation, **[H]** heuristic. Never
  upgrade a finite check or heuristic to a theorem. A clean "this route is
  closed, here is the exact obstruction" is a valid result.
- Aim at the real problem: a proof, a disproof (constructive or not), or the
  sharpest exact theorem you can reach on the way. Ambition is expected;
  overclaiming is a failure.
