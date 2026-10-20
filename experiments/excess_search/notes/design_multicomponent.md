# Multi-component arm-Z rows: exact reductions, pinning, and cost

Designer angle: rows with |Q(h)| >= 2 (about 60% of rows; 0.187 of the
sum 1/p mass on (727, 1e4] and 0.331 on (727, 1e5]).  The p-Euler test of
beta = kappa_h = sum_{q in Q(h)} chi_q (rule value 0) is reduced to work in
fields far smaller than E = d(kappa_h), with every phase between components
fixed by the shared (monomial) subfield.

Claim tags: **[checked]** = verified by an experiment listed in section 11;
**[proved]** = short proof given here, not machine-checked beyond the
experiments; **[derived]** = follows from proved statements, not separately
tested; **[estimate]** = cost-model number from operation counts times the
SPEC.md NTL unit timings (the machine was at load ~120 during this work, so
timings measured here are inflated, about 1.6x in CPU time and more in wall
time, and are given only as ratios).

---------------------------------------------------------------------------

## 0. Summary of the method

For a row p with h = f(p) and components x_i = chi_{q_i}:

1. **Test field.** The Euler test may be run in any F_{2^e} with
   h | e | E (norm reduction).  For a resultant to give the *correctly
   phased* norm one needs in addition G | e, where G is the degree of the
   pairwise-shared field (section 1).  The minimal such field is
   **e0 = lcm(h, G)**.  For p <= 1e5, e0 <= 1e5 for 4459 of the 6140
   multi rows and e0 <= 1e6 for 6016 of them (median e0 = 42,036 vs
   median E = 4.9e6) [checked, census].
2. **Shared-subfield resultant (R1).**
   N_{E/e}(sum x_i) = iterated resultant over F_e of the minimal
   polynomials of the x_i over F_{gcd(D_i, e)}, all with coefficients
   embedded through one pinned copy of the shared field.  Exact as an
   element equality in 61 rows; the same resultant over F_h (G not dividing h)
   is wrong in every tested case [checked].
3. **Crossing a big component (R2).**  For y = chi_r over base F_b
   (alpha = alpha_r), put c = N_{F_b/F_{f(r)}}(alpha)^w in the *smallest*
   field F_{f(r)}, a = (alpha/c)^{1/r} in F_b, v = y/a (v^r = c,
   v in F_{r f(r)}).  For any test field ex with lcm(h, A, f(r)) | ex,
   **N_{E/ex}(z + y) = v^{n'} f_a(z/v)**, f_a the characteristic
   polynomial of a over F_t, t = gcd(b, ex), n' = b/t [checked, element
   equality].  The root a is computed with a Frobenius-structured exponent:
   ~3.5 b squarings and O(log^2 n' + f(r)) multiplications instead of a
   b-bit exponentiation [checked].
4. **Two big components (R3)** cross independently and meet in one
   resultant of degrees (n'_1, n'_2) over F_ex [checked, element equality:
   n' = (1,1) in 7 rows, (1,2) at p = 617; larger n' unverified].
5. **Free-factor lemma (R4).**  Without crossing, the minimal polynomial
   of y over F_s may be taken to be **any** irreducible factor of
   CP(alpha / F_{s'})(X^r) over F_s; all r choices give the same Euler bits
   and the same minimal polynomial of T_h [checked, every factor, 5 rows: 29, 151, 739, 911, 991];
   an unpinned F_{s'} embedding breaks every factor [checked].
6. **Descent (R5)** from ex to e0 inside the tensor model
   F_A (x) F_t[V]/(V^r - c), where Gal(F_ex/F_e0) acts on one tensor
   factor only: the expensive Euler sweep is paid at e0, not at ex
   [derived].
7. **Relative-model crossing (R6).**  The only datum needed from the base
   is P_t = CP(alpha_r / F_t): F_b is modelled as F_t[W]/(P_t(W)) with
   alpha = W, c = P_t(0)^w, and Frobenius over F_t is W -> W^{2^t}
   [checked at 991 only; the 829/929/1061 runs were stopped, unverified].
   P_t can itself be produced by R1-R6 one level down, so
   the whole computation becomes a recursion on *characteristic polynomials
   over pinned subfields*, whose sizes are linear in the component degrees
   and never reach E [derived].

**Cost.** [estimate] In the current NTL polynomial-basis regime, the median
multi row on (727, 1e5] drops from ~3,000 s (direct, in F_E) to ~15 s; at
<= 1 h/row the reachable multi mass rises from 0.252 to 0.310 (of 0.331).
On (727, 1e4], 648 of 649 multi rows cost <= 1 h each, about 5 CPU-hours
in total (direct: 570 rows, 23 h, and the rest are infeasible).  With coprime
tensor models (cheap Frobenius, section 9) these numbers improve again by
10-100x at the median.

---------------------------------------------------------------------------

## 1. Setting and monomial-field facts

Components: chi_{2^k} (AS layer, degree 2), chi_r (Kummer layer of prime
degree r over F_2(alpha_r)), chi_{r^k} (degree r over chi_{r^{k-1}}).
For a component q let S(q) be its closure (down-closed set of components
needed to define it), D_q = d(chi_q) = D(S(q)) where for a down-closed S,
D(S) = prod_{c in S} prime(c).  For odd q = r^a, D_q = r^a b_r with
b_r = d(alpha_r) = E(r).  Row p: Q = Q(h), S_i = S(q_i), D_i = D_{q_i},
E = lcm D_i = D(union S_i).

**(M1) [proved]** For each prime l the components of prime l form one chain
(chi_l, chi_{l^2}, ... resp. chi_2, chi_4, chi_8, ...), and a down-closed set
meets it in an initial segment.  Hence v_l(D(S)) = |S meet chain_l|,
D(S meet S') = gcd(D(S), D(S')) and **F(S) meet F(S') = F(S meet S')**
(inclusion plus equal degree).  Intersections of component fields are
generated by shared components: they are pinned by construction.

**(M2) [proved]** Put G = prod_l l^{second-largest of v_l(D_i)}.  Then
G = D(union_{i<j} (S_i meet S_j)), the pairwise-shared monomial field, and
G | e is equivalent to: for every prime l at most one i has
v_l(D_i) > v_l(e).

Also v_r(b_r) = 0 for odd r (every prime in the closure of alpha_r is
smaller than r) [proved].

---------------------------------------------------------------------------

## 2. Pinning theorem (what "correct phase" means)

**Theorem P [proved].**  Let Omega = F_{2^N} with its subfields Omega_d,
M a field containing a copy of Omega, and for i = 1..k let
lambda_i: Omega_{d_i} -> M be embeddings, N = lcm d_i.  There is one
embedding psi: Omega -> M restricting to every lambda_i **iff** lambda_i and
lambda_j agree on Omega_{gcd(d_i, d_j)} for every pair i, j.

*Proof.* Fix psi_0: Omega -> M.  Embeddings of Omega_{d_i} into M form a
torsor under Gal(Omega_{d_i}) = Z/d_i, so lambda_i = psi_0 o Frob^{k_i} with
k_i mod d_i.  psi = psi_0 o Frob^k works iff k = k_i mod d_i for all i,
which (generalized CRT) is solvable iff k_i = k_j mod gcd(d_i, d_j) for all
pairs, i.e. iff lambda_i, lambda_j agree on Omega_{gcd}.  QED

Consequences used throughout:

* Only *pairwise* intersections matter.  By (M1) these are monomial fields
  F(S_i meet S_j), so it suffices to build every shared component once (in a
  model of F_G) and transport it by field homomorphisms into every other
  model.  Everything else (each new component's root, each non-shared
  subfield's embedding) may be chosen freely.
* A subfield that is *not* monomial (F_t, F_{s'}, F_{f(r)} below) must be
  linked through the monomial field that contains it: build its generator
  inside the model where the monomial structure is explicit (the base F_b),
  and fix its embedding into the test field by the unique Frobenius twist
  that agrees with the pinned F_u, u = gcd of its degree with the other
  side (implemented as `fixemb` in `v2lib.gp`).
* Equivalent phrasing: over the pinned shared field F_g of x and y, *all*
  pairs of roots (x', y') of their minimal polynomials are conjugate
  (Z/(D_x/g) x Z/(D_y/g) acts transitively), so no further phase exists.
  A composed sum over F_2 mixes the g relative phases; the correct factor is
  the one computed over the pinned F_g.

Negative controls [checked]: replacing the small part z by sigma^1(z)
(not fixing F_g) changes minpoly(T_h) in 44 of 47 rows tested.  The three
exceptions are 151 (h = 15), 271 (h = 135) and 631 (h = 45): all have odd h,
Q = {a 3-chain component, chi_5}, g = 2 and E <= 540.  A chance minpoly
match in F_{2^135} has probability about 135 * 2^-135, so this is a
structural phase invariance I have not explained [observed, unexplained].
It cannot cause a false hit, because the Euler bits depend only on the
Frobenius class of T.  It does mean that a minpoly-level comparison (V2)
cannot detect a wrong phase in such rows; only element-level V1 can.
Replacing z by sigma^g(z) (fixes F_g) changes T_h as an element but never
its minimal polynomial (all 47 rows).  Twisting the F_{s'} embedding by
Frobenius breaks all r free factors (R4: 739, 911, 991).

---------------------------------------------------------------------------

## 3. R1: test field and shared-subfield resultant

**Norm reduction [standard].**  For h | e | E and p | 2^h - 1:
beta^{(2^E-1)/p} = N_{E/e}(beta)^{(2^e-1)/p} = N_{E/h}(beta)^{(2^h-1)/p}.
One T_h = N_{E/h}(kappa_h) serves every prime p with f(p) = h.

**Theorem R1 [proved, checked].**  Let h | e | E and G | e.  Put
s_i = gcd(D_i, e), n_i = D_i/s_i, and let P_i in F_{s_i}[X] be the minimal
polynomial of x_i over F_{s_i}, embedded in F_e through a pinned family
(Theorem P).  Then the n_i are pairwise coprime, prod n_i = E/e, and

    N_{E/e}(x_1 + ... + x_n) =
        Res_{X_1}(P_1(X_1), Res_{X_2}(P_2(X_2), ... P_n(X_1+...+X_{n-1}) ...)).

With z = sum of the components having n_i = 1 (they lie in F_e):
one big component gives N = P_y(z); two give N = Res_X(P_1(X), P_2(X + z)).

*Proof.* By (M2) the n_i are pairwise coprime, so
Gal(F_E/F_e) = Z/(E/e) = prod Z/n_i and the orbit of (x_1, ..., x_n) is the
full product of conjugate sets; the norm is the product over all tuples,
which is the iterated resultant (monic, characteristic 2 so signs vanish).
QED

* **Minimal resultant field: e0 = lcm(h, G).**  E/e0 is exactly the
  product of the "unneeded" layers: every layer of every closure that is
  neither shared nor required by h is normed out at once by P_i.
* **Without G | e the resultant is the product of gcd(n_x, n_y) twisted
  norms**, i.e. it multiplies the correct norm by wrongly phased ones.
  Checked: Res over F_h differs from N_{E/h}(kappa) in all 17 tested rows
  with G not dividing h (151, 911, 991, 2003, and 13 known rows below 727).
* Acquiring P_i: for a small component (n_i = 1) nothing is needed.  For a
  big one see R2/R4/R6.

---------------------------------------------------------------------------

## 4. R2: crossing a big Kummer component

Setting: y = chi_r (prime r, exponent a = 1), alpha = alpha_r in F_b,
b = b_r, f = f(r) (f | b, v_r(b) = 0), z = the sum of the other components,
lying in F_A with r not dividing A (otherwise see 4.3).

**Proposition R2 [proved, checked].**
Let M_f = (2^b - 1)/(2^f - 1), w = M_f^{-1} mod r (exists: v_r(M_f) = 0 by
LTE), c = N_{F_b/F_f}(alpha)^w in F_f.  Then

1. alpha/c is an r-th power in F_b; pick a with a^r = alpha/c;
2. v := y/a satisfies v^r = c, and X^r - c is irreducible over F_f, so
   v in F_{rf};
3. for every ex with lcm(h, A, f) | ex | E, with t = gcd(b, ex),
   n' = b/t and f_a = CP(a / F_t) (degree n'):

       N_{E/ex}(z + y) = v^{n'} * f_a(z / v).

*Proof.* (1) (alpha/c)^{(2^b-1)/r} = alpha^{(1 - w M_f)(2^b-1)/r} = 1.
(2) v^r = alpha/(alpha/c) = c; if c were an r-th power in F_f, alpha would
be one in F_b, contradicting [F_b(y):F_b] = r.  (3) z, v, F_t lie in F_ex;
F_E = F_ex(y) = F_ex(a) = F_ex F_b, so restriction gives
Gal(F_E/F_ex) = Gal(F_b/F_t), and the norm is
prod_tau (z + tau(a) v) = v^{n'} prod (z/v + tau(a)).  QED

Choices are free [proved]: y among the r roots of X^r = alpha (irreducible
over F_A F_b because r does not divide A); v among the r roots of X^r = c
(irreducible over F_{lcm(A,t)}); a then follows.  Pinning only concerns
F_u = F_A meet F_t, u = gcd(A, t), which lies in the shared field F_g.

* c can be taken in any F_t' with f | t' | b; the smallest, F_f, makes v
  live in F_{rf} (size r f(r) < r^2) and decouples the root field from
  the char-poly field F_t.
* Test field: ex = lcm(e0, f(r)) is the minimal choice.  Enlarging ex
  reduces n' (at ex containing b, n' = 1 and W = z + a v).
* **Crossing is the "norm descent through unneeded layers" of the base**:
  it turns the tower inside out (base F_b on top of F_t(v)) so the base
  layers not needed by ex are normed out by f_a = N_{F_b/F_t}(X - a).

### 4.1 Frobenius-structured r-th root [proved, checked]

With t | b, f | t, n = b/t (r does not divide n), M = sum_{j<n} 2^{tj}
(= n mod r), w = n^{-1} mod r, L = (2^t - 1)/r, k0 = (w n - 1)/r and
S = sum_{j<n} sum_{i<j} 2^{ti}:

    a = (alpha^S)^{-wL} * alpha^{-k0},     a^r = alpha / N_{F_b/F_t}(alpha)^w.

(Because w M - 1 = w (M - n) + (w n - 1) and M - n = (2^t - 1) S.)
alpha^S = prod_{j<n} N_j with N_j = prod_{i<j} sigma^{ti}(alpha), computed
by binary splitting:

    N(m1+m2) = N(m1) sigma^{t m1}(N(m2)),
    A(m1+m2) = A(m1) N(m1)^{m2} sigma^{t m1}(A(m2)),   A(m) = prod_{j<m} N_j.

Cost: O(log n) Frobenius applications (~3.5 b squarings in total in a
polynomial model), O(log^2 n) multiplications, plus one t-bit power.
Measured (`droot.cpp`): b = 9,984: identity holds in the field, 19,916
squarings, ~184 multiplications, 0.105 s vs 0.230 s for one dense b-bit
exponentiation; b = 99,996 (ring identity check): 350,376 squarings,
~251 multiplications, 13.1 s vs 74.8 s wall time (both under the same heavy contention).
The advantage grows with b because generic exponentiation costs
~b/6 multiplications.  For a = R = r^k, k >= 2 (225 big incidences up to
1e5) the identity needs ord_R(2) | t, impossible inside F_b; use k
successive crossed r-th roots, each followed by the F_f-correction that
keeps the branch an r^{k-1}-th power [derived].

### 4.2 Two (or more) big components: R3 [proved; checked (1,1) x7 and (1,2) at 617]

Hypothesis check (617, h = 154, Q = (7, 11), ex = 2310): crossing only
chi_7 fails (W != N_{E/ex}), and correctly so.  chi_11 is still big there
(A = 220 does not divide 2310), so z is not in F_ex and R2 does not apply.
Crossing chi_11 alone (z = chi_7 in F_ex) and crossing both (R3) give
element equality.  Planners must enforce A | ex for single crossings.

Cross both: y_i = a_i v_i, ex divisible by lcm(e0, f(r_1), f(r_2)),
n'_i = b_i / gcd(b_i, ex) coprime (from G | ex).  Then

    N_{E/ex}(z + y_1 + y_2) = Res_X( f_{a_1}(X), v_2^{n'_2} f_{a_2}((z + v_1 X)/v_2) ).

Same Galois argument with Gal(F_E/F_ex) = Gal(F_{b_1}/F_{t_1}) x
Gal(F_{b_2}/F_{t_2}).  Mixed strategies (one crossed, one by R4) use R1
with the crossed component's polynomial v^{n'} f_a(X/v) over F_ex.

### 4.3 Special cases

* r divides A (r's chain is shared, e.g. chi_9 in Q with chi_3 in the
  closure of chi_7): 967 such incidences up to 1e5, almost all with
  q in {9, 25, 27, 49}.  The layer is chi_{r^k}^r = chi_{r^{k-1}} over a
  pinned chi_{r^{k-1}}; handle by R1 inside the small field (these are
  small components in every observed case) [derived].
* 2-power components are always small (D = 2^k divides e0).

---------------------------------------------------------------------------

## 5. R4: free-factor lemma (non-crossed big components)

**Lemma R4 [proved, checked].**  Let y = chi_r, e with h | e, G | e,
s' = gcd(b, e), s = gcd(r b, e) = r s', n = b/s', and
P = CP(alpha / F_{s'}) with coefficients in a pinned F_{s'} (linked to F_A
through F_g, which lies in F_{s'}).  Then P(X^r) splits over F_s into r
irreducible factors of degree n, and for **every** factor Q the element
Q(z) is a correctly phased N_{E/e}(z + y) (it differs from the reference
value by an automorphism of F_e over F_A; Euler bits and minpoly(T_h) are
identical).

*Proof.* P(X^r) is the minimal polynomial of y over F_{s'} (degree nr); over
F_s (degree r, coprime to n) it splits into r conjugate factors.  Choosing
Q is choosing an embedding of F_{rb} = F_s[X]/(Q) extending F_{s'}; its
restriction to F_b sends alpha to an F_{s'}-conjugate of alpha, i.e. it is
the identity on F_{s'}, which contains F_g.  Theorem P applies to the pair
(F_A, F_{rb}), whose intersection is F_g.  QED

Use: a second, independent route to the same T_h (cross-check for a hit),
and the non-crossed strategy when f(r) would blow up the test field.  Its
cost is that of finding one factor (equivalently an r-th root in a model
of F_{rb} = F_{D_y}), so it is the right route only when D_y is moderate.

---------------------------------------------------------------------------

## 6. R5: descent from ex to e0 [derived]

Since A | e0, F_ex = F_A (x)_{F_u} F_{rt} with F_{rt} = F_t[V]/(V^r - c),
and Gal(F_ex/F_e0) = <sigma^{e0}> acts as id (x) sigma^{e0}.  In the Kummer
model, sigma^m(sum_j beta_j V^j) = sum_j sigma^m(beta_j) gamma_m^j
V^{j u_m mod r} (u_m = 2^m mod r, gamma_m in F_t computed once), i.e. a
monomial permutation plus Frobenius on the small field F_t.  Hence
N_{ex/e0}(W) costs o = ex/e0 tensor multiplications and o (A/u) r small
Frobenius evaluations; the Euler sweep is then paid at e0.  This matters
because f(r) usually inflates the field: up to 1e5, ex <= 1e6 for only
2664 rows while e0 <= 1e6 for 6016.

---------------------------------------------------------------------------

## 7. R6: relative-model crossing and the recursion

**Proposition R6 [checked on 991 only; others unverified].**  Let
P_t = CP(alpha / F_t) (degree n' over F_t, irreducible).  Then
K = F_t[W]/(P_t(W)) is a model of F_b with alpha = W; N_{F_b/F_t}(alpha)
= P_t(0); c = P_t(0)^w (w = ((2^b-1)/(2^t-1))^{-1} mod r); sigma^t acts
on K by W -> W^{2^t} mod P_t with F_t-coefficients fixed, so the
crossed-root recursion of 4.1 runs with O(log n') modular compositions;
f_a = CP(a / F_t) is a characteristic polynomial in K.  Nothing else
about F_b is used.

**Recursion [derived].**  P_t = CP(alpha_r / F_t) with
alpha_r = sum_{q' in Q(f(r))} chi_{q'} + m_r is again a norm of a sum of
components, now over F_t: if G_r | t, Theorem R1 at row r gives P_t as an
iterated resultant of CP(chi_{q'} / F_{gcd(D_{q'}, t)}); each of those is
either a chain polynomial (when the subfield lies in the base:
CP(chi_{q'} / F_s) = CP(alpha_{r'} / F_s)(X^{r'})) or, for a Kummer top,
v^{n''} f_{a'}(X/v) from R6 one level down.  All objects are
characteristic polynomials over pinned subfields; their size is the
component degree D (n coefficients of s bits each), never the
compositum.  The cost per level is quasi-linear in the base degree b
(O(log^2) multiplications and O(log) modular compositions in a field of
size b, plus a power projection for f_a); memory is O(b), not O(E).
Pinning across levels again uses Theorem P: every subfield used is linked
through the monomial fields of the row it belongs to.

---------------------------------------------------------------------------

## 8. Minimal field: what can and cannot be shrunk

* Euler bits need some field divisible by h; a resultant-type formula
  needs G | e (else phases mix, checked).  e0 = lcm(h, G) is the floor for
  every method in this document, and it is small (section 0).
* The *information* needed from a big component is its characteristic
  polynomial over F_{gcd(D, e)}: D bits.  Obtaining it requires either an
  r-th root in a model of F_D (R4) or an r-th root in F_b plus mu_r, i.e.
  f(r) | test field (R2).  Multiplying the r conjugate factors of
  P(X^r) gives the norm over the larger field and loses exactly the phase
  [proved].  I sketched, but did not prove or test, that no character-twist
  shortcut recovers the phase without an r-th root [guessed, unverified].
* Lower bound in practice: work ~ max(e0, b_big) in sweeps, plus
  multiplications at ex, plus an E-proportional but memory-light evaluation
  (n' multiplications at size ex, n' ex = E).

---------------------------------------------------------------------------

## 9. Field representations that make the reductions cheap

* **Polynomial basis, sparse modulus (NTL).**  Squaring O(n) (0.041 ms at
  1e6 bits), Frobenius sigma^m = m squarings; "sweep(n)" (n squarings)
  ~ 4.1e-11 n^2 s: 41 s at 1e6, 70 min at 1e7, 5 days at 1e8.  Finding a
  sparse irreducible of degree n is itself costly (NTL BuildSparseIrred took
  minutes at n ~ 1e4-5e4 under load); cache per degree, or avoid it (below).
* **Coprime tensor model [checked on a small case].**  For n = n1 n2,
  gcd(n1, n2) = 1: F_{2^n} = F_2[x,y]/(P1(x), P2(y)), P_i sparse
  irreducible of the small degrees n_i.  Partial Frobenius s_x: x -> x^2
  is a ring automorphism of order n1, and sigma = s_x s_y; so
  sigma^m = s_x^{m mod n1} s_y^{m mod n2} costs <= n1 + n2 linear-time
  partial squarings, about n (n1 + n2)/64 word operations instead of
  n m/64.  For n = 1e8 with n1 ~ n2 ~ 1e4 a Frobenius application is
  ~seconds instead of days.  Multiplication: bivariate Kronecker
  (~4x length).  No large irreducible polynomial is needed.  Every field
  here has highly composite degree (product of closure primes), so such
  splittings always exist.
* **Kummer models over a small field** (F_t[V]/(V^r - c)): Frobenius is a
  monomial permutation plus Frobenius on F_t.  Used for F_{rt} in R5.
* **Relative models** F_t[W]/(P_t) (R6): Frobenius over F_t is modular
  composition.

---------------------------------------------------------------------------

## 10. Exactness and certificates

Every step is deterministic except (i) irreducible-polynomial search,
(ii) root finding for tower components, (iii) choosing generators for
subfield embeddings; all three produce objects that are checked exactly
(irreducibility test, y^l == a or y^2 + y == a, image satisfies the minimal
polynomial).  No row is skipped silently: a row is either finished with all
its Euler bits or reported as over budget.  Certificate for a putative hit
(Euler power == 1):

1. models (moduli) and their irreducibility proofs (Ben-Or/Rabin replay);
2. pinned shared components as elements of a model of F_G, with relation
   checks, and every transport map (image of a generator, checked);
3. per big component: c, a with a^r c = alpha; v with v^r = c; f_a with
   f_a(a) = 0 and deg f_a = n' (or its product-of-conjugates recomputation);
4. W (or N), T = N_{ex/h}(W) and the power T^{(2^h-1)/p} = 1;
5. independent replay by a different route (R2 vs R4, or R1 with explicit
   min polys) in a different library (NTL vs PARI), plus the direct F_E
   brute force when E <= ~2e5.

A wrong phase turns T into an essentially unrelated element and could
produce a false hit with probability ~1/p, so the two-route replay is
mandatory for any hit, and the negative controls of section 2 belong in the
regression suite.

---------------------------------------------------------------------------

## 11. Verification performed

All files under `design/`.  `mcverify.cpp` (NTL) builds F_E for a row,
embeds the whole closure, computes T_h = N_{E/h}(kappa_h) directly, and then
evaluates each formula **in the same model**, so equality is element
equality (V1).  `v2lib.gp` (PARI) builds only small models (F_g, F_A, F_b,
F_t, F_ex or F_e0), pins F_g by transport, and compares minpoly(T) over F_2
and all Euler bits with V1 (V2, independent models).

V1 (element equality: R1 at e0, R2, R3, negative controls).  All runs below
completed.  Runs I stopped at the lead's request are listed as unverified.

| rows | what | result |
| --- | --- | --- |
| 13 29 37 61 151 739 761 911 929 991 2003 | R1 at e0; R2 (n' = 1, 1, 1, 1, 3, 2, 1); R3 (2003, n' = (1,1)); Res over F_h (negative) | all equal; negatives all differ |
| 829 (E = 45,540) | R1 at e0 = 828; R2 with t = 44, n' = 5, ex = 9,108 | equal |
| 1061 (E = 41,340) | R1 at e0 = 1060; R2 with t = 52, n' = 3, ex = 13,780 | equal |
| 48 known multi rows in [67, 701] | R1 at e0 (48/48 equal); G-less resultant over F_h (13/13 differ); 41 single crossings (40 equal, incl. n' = 2 for chi_11 x4 and n' = 3 for chi_43, chi_127); 7 double crossings (7/7 equal, incl. n' = (1,2) at 617) | the one failing single crossing (617, chi_7) violates the hypothesis A \| ex and is expected (section 4.2) |

Coverage of known rows: 53 of the 55 multi-component rows below 727 were run
(all except 599, E = 197,340, and 659, E = 4,994,220).  All 53 reproduce the
OEIS value m_p = 0.

**Unverified (stopped or never started):** V1 on 823 (killed mid-run), 743,
967, 947 and 1031.  V2 on 929.  R6 relative crossing on 829, 929 and 1061.

V2 (independent small models, minpoly(T) and Euler bits vs V1):

| row | R2 crossed | R4 every free factor | R4 unpinned (negative) | R6 relative |
| --- | --- | --- | --- | --- |
| 29 | equal (n'=1) | 7/7 equal | -- | -- |
| 151 | equal (n'=1) | 5/5 equal | -- | -- |
| 739 | equal (n'=1) | 41/41 equal | 0/41 equal | -- |
| 911 | equal (n'=1) | 13/13 equal | 0/13 equal | -- |
| 991 | equal (n'=2) | 11/11 equal | 0/11 equal | equal (n'=2), root and P(0) identities hold |

Other checks: the crossed-root identity (`droot.cpp`) holds at b = 9,984
(in the field; 19,916 squarings, ~184 multiplications) and at b = 99,996 and
999,960 (ring identity with a timing-only modulus; 350,376 and 2,942,368
squarings; ~251 and ~337 multiplications).  The partial-Frobenius tensor
model checks out at (n1, n2) = (7, 9) (`tensorfrob.gp`).  Unit timing under
the session's load (`cpubench.cpp`, CPU time): sqr 0.0074 / 0.065 ms and
mul 1.37 / 18.7 ms at 1e5 / 1e6 bits, against the SPEC.md values of
0.004 / 0.041 and 0.90 / 11.8.  Contention cost about 1.6x in CPU time and
more in wall time.

**By-product (rule confirmations, not counterexamples).**  V1 finds
kappa_h not a p-th power (m_p = 0) for p = 739, 761, 829, 911, 929, 991,
1061 and 2003, and for the larger primes sharing their h (165313, 54721,
3313, 18217, 318781, 853669, 5569, 8353, 3181, 51941).  V2 also confirms
739, 911 and 991.  Every closure row of these is <= 709, with alpha_r taken
from the census rule (which matches OEIS there).  So these are new values
beyond the known range, with the caveat that each rests on a single
implementation except where V2 also ran.

---------------------------------------------------------------------------

## 12. Cost model and census quantification

Unit costs (SPEC.md, NTL on the M5, sparse modulus): S(n) = 0.0005, 0.004,
0.041, 0.42 ms and M(n) = 0.026, 0.90, 11.8, 424 ms at n = 1e4..1e7,
log-log interpolated (`mcmodel.py`).  Per-row strategy = the best of
{direct in F_E; per big component R2 (crossed) or R4 (non-crossed); test
field e0, ex, or ex enlarged by b}.  Euler(e) = 2 e S(e) + (log e + h/6) M(e),
or with R5 descent 2 (log(e/h) + h/6 + o) M(e).  [estimate]

Multi-component arm-Z rows, per-row budget (rows / sum 1/p / total CPU):

| range | budget | direct in F_E | reductions (this design) |
| --- | --- | --- | --- |
| (727, 1e4] (649 rows, 0.1874) | 1 s | 311 / 0.113 | 504 / 0.163 |
| | 60 s | 475 / 0.154 / 0.6 h | 622 / 0.184 / 0.3 h |
| | 1 h | 570 / 0.173 / 23 h | 648 / 0.187 / 4.7 h |
| (727, 1e5] (6140 rows, 0.3305) | 1 s | 817 / 0.133 | 1763 / 0.209 |
| | 60 s | 1934 / 0.204 / 4.9 h | 3776 / 0.278 / 7.9 h |
| | 1 h | 3110 / 0.252 / 273 h | 5035 / 0.310 / 288 h |
| | 1 day | 3916 / 0.279 / 5600 h | 5660 / 0.323 / 4200 h |

Median per-row cost on (727, 1e5]: direct ~3,000 s, reduced ~13 s; 90th
percentile 1e9 s vs 3.6e4 s.  In the coprime-tensor regime (section 9)
the reduced medians are ~2 s (1e5) and 0.015 s (1e4), and on (727, 1e4]
643 rows fit in 1 h/row for 0.7 CPU-hours.

Field-size view (p <= 1e5; rows / mass):

| bound | E | e0 | ex | max b_big |
| --- | --- | --- | --- | --- |
| 1e4 | 345 / 0.077 | 1250 / 0.193 | 384 / 0.084 | 4898 / 0.299 |
| 1e5 | 1086 / 0.148 | 4459 / 0.300 | 1247 / 0.171 | 5503 / 0.316 |
| 1e6 | 2204 / 0.213 | 6016 / 0.328 | 2664 / 0.244 | 5915 / 0.326 |
| 1e7 | 3468 / 0.265 | 6133 / 0.330 | 4322 / 0.295 | 6039 / 0.329 |

**Scaling.**  Direct cost ~ sweep(E) ~ E^2.  Reduced cost ~ sweep(max(e0,
b_big)) + (n' + h/6 + o) M(ex) + E-proportional evaluation that needs only
O(ex) memory.  The gain E/max(e0, b_big) has median 21 and 90th
percentile 900 on (727, 1e5] (36,000 at the 99th).  Rows become cheap when
the big components' bases b_r = E(r) are moderate (b <= 1e6 covers 0.326
of the 0.331 multi mass to 1e5), whatever E is.  Expensive rows are those
whose big component has a deep base (b_r >= 1e7, e.g. 8599 with
chi_1433, b = 3.5e6, E = 1.5e10) or a large r (r f(r) ~ r^2 test fields,
e.g. 9059 with chi_647: ex = 8.8e6); the descent R5 and the recursion R6
address exactly these two cases.

Base reuse: up to 1e5 there are 634 distinct big components across 7958
big incidences (chi_17: 437 rows, chi_19 and chi_11: 353 each, ...), so
base models and CP(alpha_r / F_t) caches amortize about 12x.  Distinct h:
5785 of 6140 (little reuse of T_h itself).

Requested examples [estimate; polynomial regime / tensor regime]:

| p | arm | E | plan | direct | reduced |
| --- | --- | --- | --- | --- | --- |
| 733 | O, Q=(61) | 3,660 | crossing gives ex = E; direct test | 0.007 s | 0.002 s |
| 743 | Z, (7,53) | 57,876 | e0 = 2226; chi_53 by R4/R1 (D = 8268), n = 26 | 0.56 s | 0.04 s |
| 797 | O, (199) | 394,020 | crossed: ex = 78,804, t = 396, n' = 5 | 47 s | 0.6 s / 0.08 s |
| 1031 | Z, (5,103) | 210,120 | crossed chi_103: ex = 105,060, t = 204, n' = 2 | 6.5 s | 0.3 s / 0.08 s |
| 1433 | O, (179) | 3,504,820 | crossed: ex = 31,862, t = 178, n' = 110 | 1 h | 0.6 s / 2.5 s |
| 4507 | O, (751) | 1,126,500 | crossed: ex = 563,250, n' = 2 | 380 s | 31 s / 0.7 s |

(Singleton rows use R2 with z = 1, i.e. the 719 certificate's formula,
here with c in F_{f(r)}.)

---------------------------------------------------------------------------

## 13. Implementation plan

1. **Field layer.**  Polynomial-basis GF(2^n) with sparse moduli
   (NTL/gf2x now; a PMULL kernel later), a cache of sparse irreducibles,
   coprime tensor models with partial Frobenius, Kummer models over small
   fields, relative models F_t[W]/(P).  Uniform interface: mul, sqr,
   frob(m), inv, embed(generator image), project-to-subfield.
2. **Tower builder with pinning.**  For a row: closures S_i, G, e0;
   build F_G once (all shared components), transport by embeddings; build
   per-component models; non-monomial subfields linked by the
   Frobenius-twist rule (`fixemb`).  Every root and every embedding
   checked.
3. **Base cache per odd r:** model of F_b (or the relative model from
   CP(alpha_r / F_t)), N_{b/f}(alpha), c, the crossed root a, and
   f_a = CP(a / F_t) per needed t.  Shared by all rows using chi_r
   (about 12x reuse up to 1e5).
4. **Planner.**  Per row: cost-model choice among R1-only, R2/R3 crossing,
   R4, with test field e0 or ex and R5 descent.
5. **Evaluator.**  W (Horner or Paterson-Stockmeyer with F_t scalars),
   resultants for 2+ big components, N_{ex/e0}, T = N_{e/h}, Euler bit for
   every p with f(p) = h.
6. **Validation suite.**  All OEIS multi rows < 727 (m_p = 0), 719 and 727
   (singleton, R2 with z = 1), V1 brute force for E <= 2e5, V2 independent
   models, negative controls (unpinned twist must fail, G-less resultant
   must differ).
7. **Scheduling.**  Increasing p; a dependency index (row -> closure rows)
   so that a hit at r invalidates and recomputes every dependent row (field
   degrees stay fixed when m_r moves 0 -> 1, alpha_r changes).

---------------------------------------------------------------------------

## 14. Risks and open points

* The cost model is an operation-count estimate; the irreducible-poly search
  and subfield-embedding (linking) costs are underestimated for large b.
  The tensor model removes the first; the second needs measurement.
* R5 and R6 are derived, not implemented end to end; R6 was checked only
  where P_t was taken from a direct model of F_b (the recursion that would
  produce P_t without F_b is unimplemented).
* Big components with exponent a >= 2 need iterated crossed roots
  (derived, untested).
* For 3+ big components the iterated resultant has intermediate degree
  n_1 n_2; crossing all of them keeps it at sum n'_i per step only when the
  formula is applied pairwise into F_ex (derived).
* Timings in this session were taken at load ~120 on 18 cores; ratios are
  meaningful, absolute numbers are not.
* V2 compares minpoly(T) and Euler bits, not elements.  Section 2 shows
  rows (151, 271, 631) where a wrong F_g phase leaves minpoly(T) unchanged,
  so V2 agreement alone does not prove correct pinning.  It is harmless for
  the search (the same Euler bits), but a hit certificate needs the
  element-level route or two independently pinned routes.
* I verified nothing above E ~ 1e5 at element level.  The large-row cost
  claims rest on the proved formulas plus the cost model.

## 15. Files

* `mcstruct.py`, `mcstats.py`, `mccheck.py`, `mccost.py`: census structure
  (G, e0, ex, big components) and field-size statistics.
* `gentower.py`: closure tower emitter.  `mcverify.cpp` + `runv1.py`: V1.
* `v2lib.gp` + `runv2.py`: V2 (crossed, free factor, unpinned negative,
  relative crossing).
* `droot.cpp`: crossed-root identity and timing.  `tensorfrob.gp`: partial
  Frobenius check.
* `mcmodel.py`, `mcmass.py`, `mcmassT.py`: cost model and budget tables.
* Logs: `v1_big.txt`, `v1_known.txt`, `v2_rel.txt`, `droot_timing.txt`.
* `cpubench.cpp`: unit timing.  `mkv2r.py`: R6-only V2 scripts (not run).
