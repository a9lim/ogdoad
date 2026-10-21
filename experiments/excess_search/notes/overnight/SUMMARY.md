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
5. **Fermat chain lower bound** [D; Codex proof, verified independently by a
   second Codex session and by Gemini]. With `d = 2^{n+1}`,
   `delta_n >= ceil((d+3)^2/10)` for `n >= 1`; rounding inside the progression
   `1 mod 2^{n+2}` sharpens it for `n >= 2`. Proof: on `y^2+y = x^3+x^2`
   with `P = (c_{n-1}, c_n)`, the functions `g = (y+1)/y` and
   `v = g o iota`, `iota(x,y) = (x+1, y+x+1)` (`iota^2 = [-1]`), satisfy
   `g(P) = u_n`, `v(P) = u_n^{±Q}`, `Q = 2^{2^{n-1}}`. Their relation lattice
   has index `delta_n`; a nonzero relation gives `g^a v^b - 1`, of pole degree
   `|2a-b| + |a+2b|`, vanishing at the `d` conjugates of `P` and to order at
   least 3 at `O`; Minkowski gives the bound. The previous bound was linear
   in `d`; this is quadratic. Both referees locate the wall at rank 2:
   Frobenius, doubling (`[2] = iota pi^2`), translations and the rational
   support supply no third independent function with values in `<u_n>`, and
   the Frobenius step that shifts `c_{n-2}` does not lift to the two-step
   tower curve.

## What the run says about the problem

- Proof direction: arm Z remains the only heuristically divergent arm, and
  nothing found gives structure there; B2 reduces two-component rows to a
  selected-prime reduction of a real cyclotomic unit (Wieferich-type).
- Disproof direction: no global identity forces a predicted translate in any
  explicit family; a failure would have to be an accidental class-group or
  splitting event. No nonconstructive mechanism was found.
- Most promising thread: the function-field lattice method behind result 5
  (more functions with values in `<u_n>`), and Codex's observation that
  binary linear forms on the arm-C Frobenius orbit carry the full
  multiplicative information (`codex/B4-moore.md` §7.2).
