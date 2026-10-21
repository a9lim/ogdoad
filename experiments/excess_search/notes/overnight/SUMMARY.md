# Overnight run on the 0/1/4 rule — interim summary

**No proof and no disproof.** The rule is
still open. The run produced new exact results, closed several routes, and gave
one quantitative improvement in arm ZF. Everything here is research material
at the review level stated; nothing is in `writeups/excess.tex` or
`docs/OPEN.md` yet.

## Files

| file | what |
| --- | --- |
| `CONTEXT.md`, `DIGEST.md` | the agents' brief (note: `Qset` actually decides smaller primes after recursing on larger ones; "increasing order" in CONTEXT.md is loose, per Codex) |
| `LIT-codex.md`, `LIT-gemini.md` | literature sweep: no published resolution of the rule, Wiedemann, or 3-power Gauss-period primitivity |
| `B1-forcing.md` + `verify/B1-forcing-codex.md` | forced translates, excess-value structure |
| `B2-armZ.md` + `verify/B2-armZ-codex.md` | arm Z two-component criterion |
| `B3-armC.md` + `verify/B3-armC-codex.md` | arm C proof attempt |
| `codex/C2-fermat.md` + `codex/V-C2-codex.md`, `codex/V-C2-gemini.md` | Fermat chain: new lower bound (Codex), independently verified by Codex and Gemini |
| `codex/B4-moore.md` | Moore-flag / non-liftable relations (Codex) |
| `lean/B1Forcing.lean`, `B2ArmZ.lean`, `B3ArmC.lean` | elementary cores, compile with `lake env lean` |

## Results that survived adversarial review (Codex astra)

1. **Failure values jump to 16** [D, confirmed]. In every parameter:
   arm C `m_p ∈ {1} ∪ [16,∞)`; arm D `m_p ∈ {4} ∪ [16,∞)` (the parked claim
   "a D failure gives `m_p = 6`" is wrong); arm O at `r = 5`
   `m_p ∈ {1} ∪ [16,∞)`; arm Z with `Q = {3^b, 4}` `m_p ∈ {0} ∪ [16,∞)`.
   Proof: Frobenius/inversion ties plus the distribution relation
   `prod_{s in mu_5}(zeta+s) = zeta^5 + 1` (B1 §3.1, §4.2).
2. **CM / Euler-factor forcing** [D, fixable normalization]. A unit of a CM
   field whose complex conjugation acts as `Frob^{E/2}` at a prime over 2
   reduces into `mu * F_{2^{E/2}}`, so it is a `p`-th power for every row
   prime with `E/h` odd (needs the real prime inert, not ramified). This
   explains arm D's forced `kappa+1, +2, +3` and forces `kappa_{5^a} + 2` at
   `h = 4*5^a`. Euler factors of even characters extend it (example
   `N = 183`, `h = 3`). In every explicit family checked, the predicted
   translate carries a character no Euler factor kills (B1 Thm 5.1). Codex:
   this excludes rational Euler-factor cancellation only, not mod-`p`
   unit-lattice divisibility, so "route closed" is downgraded to that.
3. **Arm-Z families that are arm C's twins** [D, confirmed]. For
   `h = 4*3^k` (`kappa = 4 + zeta_k`) and `h ∈ {1,2,4}*3^b 5^c`, 2 is inert in
   `Q(zeta_N)^+`, the selection disappears, and the row criterion has exactly
   Theorem C's shape (class-group part or splitting of 2 in a Kummer
   extension). For general two-component rows the selection survives only as
   the coset of one prime of `K^+` over 2 (B2 Prop 1, Thm B; Thm A's transport
   formula needs Codex's equivariant restatement).
4. **Arm C identities** [D, confirmed]: every order-`l` Gauss sum over
   `F_{2^N}` is `≡ -1 mod lambda^2` (so the "R0" sum `S` in
   `notes/heuristic_nonconstructive.md` §4.2 is identically zero — that file
   is wrong there); the coset-product identity (B3 Thm 3.4) shows the twisted
   Gauss-sum coefficient produced by explicit reciprocity is a known nonzero
   multiple of `L(gamma)`; the Gauss-lemma digit form of arm C (B3 Lemma 4.1,
   Lean-checked). Arm C failure ⟺ a `psi`-part of the ray class group mod 2
   of `K_k` is nonzero, including an everywhere-unramified class-group branch
   (Codex correction).
5. **Fermat chain: quadratic, then superpolynomial lower bounds** [D].
   Here `d = 2^{n+1}` and `ell = n+1 = log_2 d`.
   - *Rank 2* (Codex `codex/C2-fermat.md`; verified by a second Codex
     session and by Gemini, `codex/V-C2-*.md`):
     `delta_n >= ceil((d+3)^2/10)`. On `y^2+y = x^3+x^2` with
     `P = (c_{n-1}, c_n)`, `g = (y+1)/y` and `v = g o iota`,
     `iota(x,y) = (x+1, y+x+1)`, take values `u_n`, `u_n^{±Q}` at `P`; a
     relation gives `g^a v^b - 1` of pole degree `|2a-b| + |a+2b|` vanishing at
     the `d` conjugates of `P` and to order 3 at `O`; Minkowski finishes. The
     paper's bound was linear in `d`.
   - *Unbounded rank* (Codex `codex/C5-rank3-reply.md`; verified by a fresh
     Codex session and by Gemini, `codex/V-C5-*.md`). Pass to the normal
     closure `L_m` of the generic Artin–Schreier tower
     `x_0^2+x_0 = t`, `x_j^2+x_j = x_{j-1}^3+x_{j-1}^2` over `F_2(t)`. Its
     fibre at `t = 1` is the Conway tower, so the Frobenius `tau` there is an
     `N`-cycle (`N = 2^{m+1}`) with `tau^r(x_m) = x_m + 1`, `r = 2^m`. Then
     `g_m, tau g_m, ..., tau^{r-1} g_m` (`g_m = (x_m+1)/x_m`) are
     multiplicatively independent because `X^r + 1 = Phi_{2r}` is irreducible
     over `Q`. At the fibre `t = a_{n-m-1}` they all take values in `<u_n>`, so
     `delta_n >= d^r / (r! H_m^r)` with `H_m = 3^m [L_m : K_m]`. The sibling
     identity gives `[L_m : F_2(t)] <= 2^{2^m}`, and with it
     `log_2 delta_n >= (3/16) ell^2 - ((log_2 3)/2) ell log_2 ell` for
     `n >= 3`. This is superpolynomial in `d`, but far below full order
     `2^{d/2}`. Gemini judges it new for the Conway tower (nearest prior work:
     Burkhart et al. 2009 modular towers; Dose–Mercuri–Pal–Stirpe 2022
     recursive towers; Voloch 2010, whose small-order hypothesis fails here).
   - *Growth law and the method's ceiling* (Codex `codex/C6-growth-reply.md`;
     verified by a fresh Codex session, `codex/V-C6-codex.md`). The per-level
     Artin–Schreier class ranks are `1, 1, 2, 3, 6, 12` for `j = 0..5`
     (exact), and `5*2^{j-4} + 1 <= rho_j <= 6*2^{j-4}` for `j >= 4`. The
     upper bound comes from the level-3 relation; the lower bound comes from a
     ramification-break comparison at infinity. Hence
     `[L_m : F_2(t)] = 2^{Theta(r)}`, the bound improves to
     `log_2 delta_n >= (8/27)(n+1)^2 - (8 log_2 3 / 9)(n+1) log_2(n+1)`
     (`n >= 4`), and this construction can never exceed `Theta((log d)^2)`:
     it cannot reach `exp(d^delta)`. A different mechanism is needed for that.

## What the run says about the problem

- Proof direction: arm Z remains the only heuristically divergent arm, and
  nothing found gives structure there; B2 reduces two-component rows to a
  selected-prime reduction of a real cyclotomic unit (Wieferich-type).
- Disproof direction: no global identity forces a predicted translate in any
  explicit family; a failure would have to be an accidental class-group or
  splitting event. No nonconstructive mechanism was found.
- Most promising thread: result 5 shows that lattice/zero-counting methods do
  bite on the selected Fermat orbit, but this construction is capped at
  `(log d)^2`. Getting past it needs functions with values in `<u_n>` at much
  lower pole cost than the normal closure. Also Codex's observation that
  binary linear forms on the arm-C Frobenius orbit carry the full
  multiplicative information (`codex/B4-moore.md` §7.2).
