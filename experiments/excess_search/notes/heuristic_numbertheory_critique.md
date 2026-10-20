# Number-theory critique of model.md (adversarial critic, verbatim substance)

Tags: [S] cited, [D] derived with proof, [N] checked numerically, [H] heuristic.

## 1. Main error: translate-orbit counting (model.md §3.4)

§3.4 counts one independent event per orbit of a translate under the Frobenius
power that fixes kappa + rule. It misses automorphisms that move kappa itself,
and scalars u that are already p-th powers. Two translates kappa+m and
kappa+m' have the same p-th-power status whenever
sigma(kappa+m) = u (kappa+m') with sigma an automorphism and u a p-th power.

(a) Z rows whose Q(f(p)) contains a 2-power 2^k (k >= 2 automatic) [D].
- Let D_o = d(kappa_g) for the odd part g of h. Membership of 2^k in Q(h)
  means 2^k does not divide D_o, so E = lcm(D_o, 2^k) has v_2(E) = k.
- sigma = Frob^(E/2) fixes every odd component and acts on F_(2^(2^k)) as
  Frob^(2^(k-1)), sending chi_(2^k) to chi_(2^k) + 1; so sigma(kappa) = kappa + 1.
- sigma fixes every nimber below 2^(2^(k-1)), so kappa+m and kappa+(m xor 1)
  always agree: m_p is never 1 or 3 there (m_p even unless >= 2^(2^(k-1))).
  ZF rows behave the same way. Checked exactly at h = 12, 24, 28
  (conj_check.py, orbit_check.py).
- Side result [D]: here the selected coordinate is u = (kappa+1)/kappa in a
  norm-one torus with u + 1/u = 1/(a_(k-1) + w^2 + w), w = sum of odd
  components: the Fermat torus coordinate (prop:z-torus) generalized to every
  such row — a second family of torus problems [H: Fermat-chain tools may transfer].

(b) Arm C: prop c-half already gives translates 2, 3 the same order as 1
(zeta -> omega zeta, omega a p-th power). Checked at k = 2.

(c) Arm D: prop d-norm: Frob^(2h) fixes zeta and swaps nimbers 4 and 5. The
model conflated d(kappa) = 2h with E = 4h. Checked at k = 2.

Combining (b),(c): translates in F_16 fall into four classes in arms C and D:
{0}, {1,2,3}, {4,5,8,10,12,15}, {6,7,9,11,13,14}. Hence
m_p in {1,4,6} or m_p >= 16 in arm C; m_p in {4,6} or m_p >= 16 in arm D [D].
m_p = 5 is impossible.

(d) Arm O: translates 1 and 2 are separate events (sigma(x) = x+3 would give
1 + omega x a class of order dividing r, excluded by the nontriviality
argument). Checked d(chi_7 + 2) = 42. Unchecked side conditions affect only
translates >= 4 (omega^{±1} alpha_r conjugate to alpha_r; Fermat-prime r).

(e) Odd-only Z rows: no pairing found at h = 15 (one case) [N]; general case unproved.

### Corrections
| model.md claim | corrected |
| --- | --- |
| m_p at a failure: 1 in Z, 2 in O and C, 5 in D | 1 in odd-only Z rows; 2 in 2-power Z rows, ZF, O; 4 in C; 6 in D |
| P(m_p >= rule+2) = p^-2 in every arm [D] | = 1/p in 2-power Z rows, ZF, C, D |
| Conjecture B (rule <= m_p <= rule+1), 1 - 1.8e-4 | about 0.80-0.86 [H]; restate as "m_p is the rule value or the first translate outside the rule's class" (then ~1 - 1.8e-4) |
| value set {0,1,4} survives w.p. 0.54 | about 0.43-0.46 (C failures give 4, inside the set) |
| sup m_p = 4 with 1 - 7.8e-5 | essentially unchanged; mechanism m_p = 6, not 5 |

- Type-(a) rows carry mass 0.0874 in (727, 1e8] [N, z2pow.out]; share by
  decade falls 0.129 -> 0.066 (~ (ln x)^-0.52); tail beyond 1e8 ~0.065-0.13 [H].
- "Failures change no field degree" is false for C (alpha_p = zeta + 4 has
  degree 4h; probability 5.8e-5); the O argument needs "x and x+1 not
  conjugate, by nontriviality" rather than "2 in F_4".
- §7.2 (record kappa + rule + 1) is wrong for 2-power Z, ZF, C, D: that
  translate is determined by the row (fake confirmations). §7.1 calibration
  must use the first translate outside the class (kappa+2 in 2-power Z, zeta+4 in C, zeta+6 in D).

## 2. Smaller issues
1. Under M_Levy only liminf N/mu >= c, not N/mu -> 1.
2. ExcessHeuristic.lean compiles (propext, Classical.choice, Quot.sound);
   it formalizes only the independent (iIndepSet) version, not Levy's.
3. "As hard as infinitely many Wieferich primes" is not a reduction: tag [H],
   "same shape, no known technique"; a single counterexample differs from infinitude.
4. ln b_r = O(ln^2 r) is provable [D]: odd component primes s <= (r-1)/2,
   b_r <= f(r) prod b_s d(m_r) with d(m_r) = O(log E) (Katz; trivially under
   the rule); induction gives log b_r <= C log^2 r for C > 1/(2 ln 2); with
   Gronwall, sigma_{-1}(b_r) = O(lnln r) unconditionally — finiteness of the
   arm O mass then rests only on the per-conductor heuristic.
5. 13631489 (an F_18 factor) should not be on the settled list (OPEN.md
   claims published factors of F_12-F_17 and residual blocks of F_15-F_18).
6. C_6 rows (80191, 97687, 379081) are treated as unsettled — conservative.

## 3. Checked and correct
Cell partition; v_r(L) = 1; Kummer nontriviality; v_p(L) = v_p(2^h - 1);
cell-success lemma and consequences (it extends to C cells and ZF); Q-sets of
1093 ({7,13}) and 3511 ({5,13,27}); b_r even; Katz bound and m_p < E^4;
per-conductor heuristic 1/(h_0 ln h_0); Mertens/Rosser-Schoenfeld; Le Cam;
first-failure quantiles; Mathlib names ae_mem_limsup_atTop_iff,
measure_limsup_eq_one, Nat.Primes.not_summable_one_div; citations real.
Sharper cell-success: a cell lacks a passing row only if every prime other
than r dividing ord(y) is a Wieferich prime with deficient valuation, whose
Wieferich part must then be at least B_(r,a)/r by packing.

## 4. Forcing structure
Nothing forces a failure. The pairings constrain the value of m_p, not whether
the rule fails. Exact theorem worth formalizing: in 2-power Z rows m_p not in
{1,3}; in arm C m_p in {1,4,6} or >= 16; in arm D m_p in {4,6} or >= 16.
