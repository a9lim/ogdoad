# Digest for budget-limited agents (read this instead of the whole paper)

Context budget is tight this run. Read `CONTEXT.md` and this file. Open
`writeups/excess.tex` only at the line ranges named for your avenue, with
`sed -n 'a,bp'`; never read the whole paper or whole notes files.

## Facts you may use (all proved in the repo or standard)

- Nimbers: `2` is a primitive cube root of unity (`2*2 = 3`, `2*3 = 1`).
  Orders [N, `scratchpad` nim script]: `ord(4) = 15`, `ord(16) = 85 = 5*17`,
  `ord(256) = 21845 = 5*17*257`, `ord(65536) = 5*17*257*65537`. In general
  `ord(c_n) | F_1 ... F_n` for `n >= 1` (Cagliero–Herman–Szechtman, FFA 2025,
  arXiv:2405.10159: `O(c_i) = O(a_i)` and a product formula; primitive
  candidate is `c_0 c_i`).
- `kappa_{3^k} = zeta_k`, primitive `3^{k+1}`-th root of unity, degree `2*3^k`.
  `gamma_k = zeta_k + zeta_k^{-1}` has degree `3^k`; `gamma_{k-1} =
  gamma_k^3 + gamma_k = gamma_k (gamma_k + 1)^2`; `b_j = gamma_j + 1` is a root
  of the j-th iterate of `X^3+X^2+1`, which is stable (Lin–Wang 2024).
  `ord(zeta_k + 1) = 3^{k+1} ord(gamma_k)` (excess.tex 2338–2365).
  Arm C half-angle / polynomial forms: excess.tex 2366–2440.
- `alpha_5 = 4`, `kappa_5` has order 75, `kappa_{5^a}` is a primitive
  `3*5^{a+1}`-th root of unity, field degree `4*5^a`; its `mu_3`-part is the
  nimber `2`. `alpha_17 = 16`, `kappa_17` has order `5*17^2`, degree 136.
  `alpha_7 = omega + 1` (arm C row, `m_7 = 1`), degree 6.
- Theorem C (arm C row criterion): `notes/heuristic_nonconstructive.md`
  lines 384–520 (regimes R0/R1/R2 and why Jensen fails), Codex corrections in
  `notes/codex_theoremC_and_D.md` (first 60 lines are the key part).
- Four-arm reduction and definitions: excess.tex 221–303. Arm O projective
  criterion: 1680–1700. Fermat torus: 375–470. Arm D target: 3316–3360.
- Literature (see `LIT-codex.md`, `LIT-gemini.md`): no published resolution of
  the rule, of Wiedemann's conjecture, or of 3-power Gauss-period primitivity.
  Relevant: Ugolini 2019 (order of alpha + alpha^{-1} in char 2), Blokhuis–
  Cao–Chou 2018 (roots of Dickson polynomials), Breuer–Shparlinski 2020
  (Ducci periods, `P(3^n) >= exp(c sqrt(3^n))`), Breuer 2021 (non-primitivity
  of zeta+zeta^{-1} detected by quadratic-field arithmetic for some prime
  conductors), Gao–Vanstone conjecture (safe-prime conductors), Popovych 2015.

## The coordinator's CM half-field lemma (proof below; check it, then use it)

**Lemma (CM forcing) [D].** Let `M` be a CM field, `P | 2` a prime of `M`
with residue field `F_{2^E}`, and suppose complex conjugation `c` lies in the
decomposition group of `P` (then it acts on `O/P` as `Frob^{E/2}`, `E` even).
Let `u` be a unit of `M` and `w = |mu(M)|`. Then `red(u)^{2^{E/2}-1}` lies in
`mu_w`, so `ord(red u)` divides `w (2^{E/2} - 1)`. Consequently, for every
odd prime `p` not dividing `w` with `h = ord_p(2)`, `h | E` and `E/h` odd,
`red(u)` is a `p`-th power in `F_{2^E}`.

*Proof.* `u / c(u)` has absolute value 1 at every complex embedding, so it is
a root of unity (Kronecker). Reducing, `red(u)^{2^{E/2}} = red(c u) = red(u)
red(zeta)`. If `E/h` is odd then `h` does not divide `E/2`, so `p` does not
divide `2^{E/2}-1`; `p` does not divide `w`; so `ord(red u)` is prime to `p`
and `red u` is a `p`-th power. ∎

For `M = Q(zeta_N)`, `N` odd, `c` lies in `<2 mod N>` iff all prime powers
`s^e || N` have the same positive value of `v_2(ord_{s^e}(2))`. A sum of two
roots of unity of odd order, `zeta_A + zeta_B = zeta_A (1 + rho)`, is a
root of unity times the cyclotomic unit `1 + rho` (`1 + zeta_X` is a unit for
odd `X > 1`), so the lemma applies to it with `N = ord(rho)`.

Examples: (i) arm D (`h = 2*3^k`): `kappa + 1 = 1 + zeta_{3^{k+1}}`,
`N = 3^{k+1}`, `E = h`: forced `p`-th power, and so are `kappa + 2`,
`kappa + 3` — this is the known forcing of `m_p >= 4`. (ii) Arm O at `r = 5`,
`h = 4*5^a = E`: `kappa_{5^a} = 2 xi` with `xi` of order `5^{a+1}`, so
`kappa + 2 = 2(xi + 1)` is a forced `p`-th power at those rows; the rule's
prediction there (`kappa + 1` not a `p`-th power) is not contradicted. (iii) Arm C (`h = 3^k` odd, `E/h = 2`): no forcing, consistent.

Coordinator's preliminary scan: components other than `kappa_{3^b}` and
`kappa_2 = 2` have mixed 2-adic profiles (`ord(c_n)` contains `F_1` and
`F_n`; `ord(alpha_7)` contains 7 with `ord_7(2) = 3` odd; `alpha_11 =
kappa_5 + 1` lives in `F_{2^20}` whose order has primes with
`v_2(ord) = 0, 1, 2`), so no arm-Z `kappa_h` is obviously CM-forced. This is a
lead, not a theorem.

## The Stark-type route (coordinator's assessment, A2 — treat as closed unless you see an error)

The arm C row condition is the `chi_2`-part (`sigma_2 -> 2 mod l`) of
`rec_2(units of K_k)` in `Cl_{K_k}(2) / l`. That extension of `K_k` is not
abelian over `Q` (an abelian extension of `Q` tamely ramified at 2 has no
`l`-part, since `mu_l` is not in `F_2`), so ETNC for abelian fields over `Q`
does not see it. Over the base `K_k` all relevant ray class characters have
odd order, hence are totally even: the relevant Stark statement is the
higher-rank (rank `3^k`) Rubin–Stark / Gross refined conjecture over a totally
real base, which is open; Dasgupta–Kakde–Silliman cover the rank-one CM case.
Even if known, the regulator side is exactly the unknown reciprocity image and
the L-side is a high-order derivative with no closed form.
