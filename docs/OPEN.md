# Open mathematical problems

Ogdoad has three live research problems. The first two are universal
conjectures with exact reductions; the third is a classification program with
an explicit completion criterion. This document
states their current form, known starting point, and missing step. The linked
papers carry the detailed arguments. Finite experiments and an implemented API
are evidence or infrastructure, never substitutes for the stated theorem or
construction.

## 1. Isolated-dummy FIFO linking

Let a finite simple graph on real vertices be augmented by one isolated dummy.
Each vertex is opened once and later closed; closes occur in opening order. A
one-step ko protects the most recently changed vertex, and a forced pass clears
ko when no ordinary move is legal. Closing the queue front toggles a bit when
that vertex has odd degree in the untouched real graph.

**Conjecture.** From the empty-queue, score-zero root, either designated seat
can force terminal score zero on every such graph.

This is stronger than the FIFO theorem used by the Gold--Arf realization. A
public Witt frame reduces that construction to matchings plus isolated
vertices, where a both-seat zero-score strategy is proved.

### Exact reduction

For a terminal history `h`, let `D(h)` be its live-star/disjointness vector in
the real-edge space over `F_2`. For any fixed attacker policy `S`, with terminal
histories `H_S`, affine separation gives

```text
S is harmless for every graph
    iff
0 lies in Aff{D(h) : h in H_S}.
```

`FifoPublicPolicyAffine.lean` defines this graph-free policy problem and
`FifoPublicPolicyDuality.lean` proves that it is equivalent to
`FifoLinkingTheorem`. The conjecture is therefore exactly the existence of an
odd response flow with zero real-edge moment for every initial public policy.

At a queue front `f`, the quotient

```text
T_f(z)_ij = z_ij + z_fi + z_fj
```

separates the cut star at `f` from the smaller carrier. The formal development
proves the local contraction identities, terminating strategy duality, matching
case, fixed-front and close-first reductions, and the following sharp normal
form for a hypothetical counterpolicy:

- choose a globally rank-minimal sheet-one occurrence with the dummy live;
- the selected move is a real separator-unit `OPEN v` into a complete
  sheet-zero defender fan;
- every legal fan edge has zero separator increment;
- the old queue is nonempty and contains a distinct separator-odd debt vertex;
- the last earlier unit-charged close is followed by a pointwise score-neutral
  suffix.

### Missing step

The debt vertex can either survive behind the last charged front or be opened
inside the neutral suffix. A proof must use the occurrence's actual ancestry to
select an odd family of earlier defender siblings whose prefixes and
continuation cosets cancel the remaining real-edge class in both cases.

Local Bellman tie-breaking, an unlabelled state-DAG cycle, score translation,
and unrestricted pair descent are insufficient: the formal counterexamples
show that each forgets either the selected edge label, the second correlated
continuation, or the isolated-dummy constraint. The required new object is an
ancestry-compatible multibranch contraction through the FIFO cut filtration.

### Evidence and authority

- Lean defines but does not prove `FifoLinkingTheorem`.
- Exact minimax proves every nonisomorphic board through eight real vertices
  plus the dummy, for both seats; larger targeted searches are consistent with
  the conjecture but are not exhaustive.
- The maintained executable oracle is `experiments/linking_game.py`.
- The authoritative mathematical account is
  [`../writeups/linking_affine.tex`](../writeups/linking_affine.tex).

## 2. Finite excess in transfinite nim multiplication

For an odd prime `p`, let `f(p) = ord_p(2)` and write the supported
Conway--Lenstra Kummer carry as

```text
alpha_p = kappa_f(p) + m_p.
```

**Conjecture.** The finite excess is

```text
m_p = 0   if Q(f(p)) is not a singleton odd prime power,
m_p = 4   if f(p) = 2 * 3^k with k >= 1,
m_p = 1   otherwise.
```

The implementation table and exact row certificates agree with this rule. No
universal proof is known.

### Exact reduction

The paper reduces the rule to four recursively selected order assertions.

| arm | case | unresolved selected assertion |
| --- | --- | --- |
| `Z` | nonsingleton support, including the singleton-even Conway--Fermat chain | the structural norm has full primary order in the canonical primitive-support quotient; equivalently, the marked supersingular function has full next-Fermat order at the Conway-selected point |
| `O` | singleton odd prime power away from `3` | a marked cyclotomic value has full primary order at the unique prime over `2` selected by Conway ancestry; globally it is a cyclotomic `S`-unit when the conductor is a prime power |
| `C` | the `3^k` chain | the selected Singer-trace orbit has full norm-one order, or equivalently the associated principal-ray and reduced circular-unit defects both vanish |
| `D` | the `2 * 3^k` chain | the marked conductor-five unit has trivial selected principal-ray/reduced-unit index |

For nonzero `beta` in `F_(2^E)`, the load-bearing test is

```text
beta has no p-th root
    iff
beta^((2^E - 1)/p) != 1.
```

The weaker statement `p | ord(beta)` does not control the full `p`-primary
coordinate when the ambient group contains a higher `p`-power.

### What is proved

The paper proves the four-arm equivalence, exact cyclic power criteria,
boundedness reformulation, structural norm identities, primitive-support
quotient, supersingular and Singer descriptions, the ordinary ray-class
decomposition, and the principal-ray/circular-unit factorization in the cubic
and exceptional arms.  In the cubic arm, packing over minimal coefficient
fields gives
`log_2 ord(eta_k) >= (log_2 3 + 5/6) sqrt(3^k) - O(k)`.  This follows
from the exact selected identity `o_(3,k) = 3 ord(eta_k)` and the Kummer
ratio bound below; its coefficient exceeds `2.4182`.  The separate
selector-retaining partition and section arguments prove that the first
possible nonempty one-sided relation
has weighted residue at least `2 * 3^k + 1`, sharply attained by the norm
triple.  At every weight, such a relation is exactly simultaneous
divisibility of the two non-killed residue sections by
`Y^(2H) + Y^H + 1`.  For a missing-current-prime quotient word those two
sections are padded reciprocals, so they give only one condition; equivalently
failure is `Y^(2H) + Y^H + 1 | T_(N/ell)` for the explicit cubic power-sum
recurrence `T_m=T_(m-1)+T_(m-2)+(1+Y)T_(m-3)`.  This one-polynomial selected
condition remains unresolved.  The full symmetric power state has an exact
composition law.  At exponents congruent to one modulo three its two trace
coordinates vanish together, and that zero state is preserved by every
current `ell`-power.  Hence the forced zero at `N=(N/ell)ell` has an exact
`ell`-element fibre in the specialized projective power map.  This fibre is
not itself the symmetric zero-state: it proves only that the recurrence and
projective raising equation do not select the literal `N/ell` preimage.
Any successful refinement must add selector-sensitive ancestry data.
The first two selected jets are now exact and give the same boundary.  Under
hypothetical failure, the divisor `G=Y^(2H)+Y^H+1` occurs only simply in
`T_(N/ell)`, and its quotient evaluates at a selected root `y` to
`(1+y)^(-(N/ell)(ell-1)/3)`.  The ordinary derivative therefore recovers
the unique Kummer preimage already forced by the projective fibre, while the
second Hasse derivative cancels for `k >= 2` by
`N/ell ≡ ell (mod 4)`.  The two-base-`q` digit span bound is also automatic:
for `d=N/ell > 1`, actual quotients already have digit gap at least `h+1`.
Thus symmetric composition, its first two jets, and those two digits contain
no further obstruction.
Equivalently, failure at a current prime `ell` is triviality of the explicit
marked `ell`-torsion class `[(1+w)^(N/ell)/w^2]` in
`F_(2^(2h))^times/F_(2^(2h/3))^times`.  Its cyclic `H^1` vanishes because
the coboundary operator is already bijective, so Hilbert--90 is provably
blind to that pointwise triviality question.
These bounds remain subexponential in the field degree and do not classify
higher-weight relations or imply primitivity.  At the correctly
indexed Conway--Fermat endpoint, a hypothetical
odd Fibonacci zero is equivalent to two simultaneous fourth-power residuals;
their polynomial gcd is exactly the target Fibonacci polynomial, but
the Binet parametrization shows that the inverse-Frobenius and partial-trace
residuals hold on every deficient torsion packet before the deterministic
Conway parent is selected.  Thus Frobenius extraction still ends at the
marked inverse-exponent seam.  The packet degree forces
`phi(delta_n) >= 2^(n+1)`, and the Fermat-divisor congruence improves this
for `n >= 2` to `phi(delta_n) >= 2^(n+2)`; consequently a missing prime
`p | F_n` must then satisfy `p <= 1 + 2^(2^n-n-2)`.  This is
ancestry-sensitive, but it still permits a single large missing prime in the
asymptotic range.  More sharply, at a globally least failing prime, every
prime factor of `F_n/delta_n` is at least `p` and congruent to
`1 mod 2^(n+2)`.  With `G` the maximum of `2^(n+2)` and the totient of the
fully selected lower-prime part, `phi(F_n) < G p(p-1)` forces
`F_n/delta_n = p`; if
`phi(F_n) < G(p-1)(p+2^(n+2)-1)`, the only alternative is
`p^2 | F_n/delta_n`.  The latter is an explicit base-2
Wieferich/repeated-Fermat-factor boundary, not a compound distinct-prime
defect.  Cohen's
specified-order trace theorem also gives, in arbitrarily large
power-of-two degrees, normal full-degree elements with any fixed common
finite tuple of absolute power traces but respective orders `2^d-1` and
`(2^d-1)/3`.  Hence normality and finitely many absolute traces cannot by
themselves remove even a single-prime order defect; this is a generic no-go,
not a counterexample on the selected Conway ancestry.  The exact one-edge
power-sum transport is kernel-checked as `conwayChild_powerSum`.  In the
ordinary arm, the bottom-ancestor polynomial
sections prove every current factor `p` with `L_(r,a)/p <= b_r r^a`, including
the case in which `L_(r,a)/r` is prime.  Retaining the opposite top
`r`-sections doubles this degree range whenever the literal bottom polynomial
`P_r` is not self-reciprocal: deficiency then forces
`L_(r,a)/p >= 2 b_r r^a + r`, so every cofactor at most `2 b_r r^a` is
settled.  The test is level-independent because the reciprocal of
`P_r(W^(r^(a-1)))` is `P_r^*(W^(r^(a-1)))`; it is automatic when
`ord_r(2)` is odd or `b_r/ord_r(2)` is even.  An affine odd-Kummer
power-basis lemma shows more: if the `0/1/4` row at `r != 3` is already
correct, then its literal `P_r` cannot be self-reciprocal.  Since every
arm-`O` row prime `p` has `r < p`, a least-prime counterexample therefore
has `P_r != P_r^*`, and its cofactor must be at least
`2 b_r r^a + r`.  The literal exception `P_3=X^2+X+1` is
self-reciprocal but belongs to the separate cubic/exceptional arms.  Thus a
self-reciprocal bottom at `r != 3` would already be an earlier failure of
the global rule, rather than an independent ordinary-arm obstruction.  This
still leaves all larger cofactors unresolved.  Kummer-ratio packing over
minimal coefficient fields strengthens this
unconditionally.  For `1 <= m <= a`, put `t_m=ord_(r^m)(2)`,
`D_m=r^(m-1)(r-1)`, and `R_m=b_r r^a/t_m`.  The selected top quotient
order `o` is at least the maximum over `m` of
`R(D_m,R_m/2)` when `R_m` is even, and
`R(D_m,(R_m-1)/2) + ceil((R(D_m,(R_m+1)/2)-R(D_m,(R_m-1)/2))/r)`
when `R_m` is odd, where
`R(D,s)=sum_(j=0)^s 2^j binom(D,j) binom(s,j)`.
The odd case retains the largest leading-`mu_r` phase fibre of the next
signed shell; the even case retains the entire ball through the degree
boundary.  This dominates the bound from every intermediate tower field
and gives
`log_2 o >= (log_2 3)(1-1/r) sqrt(r^a) - (log_2 3)/2`.
The same theorem includes `r=3` and yields the cubic bound above.  At a
globally least failing prime, enlarge this lower
bound `B` by the fully selected lower-prime part.  Then
`L_(r,a) < B p^2` forces the prime-to-`r` order defect to equal exactly `p`,
while below `B p(p+2r^a)` the only other possibility is a repeated
base-`2^b_r` Wieferich factor `p^2`.  Deficiency otherwise forces the same
lower bound on `L_(r,a)/p`.  The final `p`-rough arithmetic implication is
kernel-checked as `rough_defect_eq_prime`; the congruence-gap refinement is
kernel-checked as `rough_congruent_defect_eq_prime_or_square_dvd`.  The
finite-field ancestry, disjoint-factor comparison, lattice counts, and
minimality inputs remain paper-level; `ExcessOrdinaryPacking.lean` checks
the normalized rational evaluation injection and its cyclic-order bound.
`ExcessCubicPacking.lean` checks the coprime circle/real factor-of-three
order bridge and the resulting Singer bound; its finite-field and valuation
inputs remain paper-level.  The paper also proves several finite tensor-rank zero cases and shows why generic trace, norm,
conductor, factor-shape, reciprocity, and
unselected Kummer information cannot recover the marked Conway coordinate.
For the exceptional arm, automatic vanishing on the `X^h - 1` component
upgrades the three-equal-block failure condition to literal cyclic
palindromicity.  A one-third Frobenius compression reduces its primitive
component to a trinomial with complementary exponent congruent to `3` modulo
`3h`.  An exact relative-norm calculation removes the remaining
three-primary phase: for `r = Psi_k / ell`, the obstruction is the
parity-twisted equality `P^r = 1` when `k` is even and `P^r = omega^2` when
`k` is odd.  This proves the entire current factor when `r = 1`
(equivalently, when `Psi_k` itself is prime), but leaves the prime-to-three
coordinate at composite `Psi_k` levels open.
The same current Kummer class has the sharper Cayley representative
`V_k=(gamma_k+omega^2)/(gamma_k+omega)`.  With `Q=2^(3^(k-1))`, its
relative cubic Frobenius satisfies the scalar-corrected identity
`P=omega V_k^(Q^2-1)`, and the exponent and scalar are invertible/trivial on
every current `ell`-Kummer line.  Thus `M_k`, `P`,
`U=epsilon_k^(-1)P`, and `V_k` have the same current power obstruction.  The
exact ancestry law `Norm(V_k)=V_(k-1)^(-1)` for `k >= 2` makes an alternating
normalization norm coherent,
but cyclic-group arithmetic proves that every fixed birth-level norm fibre
contains every `ell`-Kummer class.  Hence even the complete literal norm
recurrence cannot evaluate the newly born selected symbol; the missing datum
is still the principal-ray Artin image at the chosen prime over two.
An intermediate-field exceptional ratio-packing sieve now proves `D` whenever
`Psi_k/ell < S_k`, where, for `m_j=3^j` and
`s_j=floor((3^(k-j)-1)/8)`,
`S_k=max_(0<=j<k) sum_(t=0)^min(2m_j,s_j) 2^t binom(2m_j,t) binom(s_j,t)`.
It satisfies `log_2 S_k >= c_0 sqrt(3^k)-O(k)` with `c_0>1.2306`.  This is a
selected composite large-factor range, not a universal proof: the bound is
exponential in the square root of the field degree, while `Psi_k` is
exponential in the field degree.
The selected singleton-even realization lies on
`y^2+y=x^3+x^2`; its function is supported on fixed five-torsion rather than
the Fermat-torsion point, so for positive levels it is not an `F_n`-Weil or
reduced-Tate pairing function attached to that point.  The full recursive
Artin--Schreier curve through depth `r` is geometrically connected, ramifies
only at its unique point above infinity, and has genus
`(3^(r+1)-2^(r+2)+1)/2`; hence every finite torsion packet has the same
trivial inertia, and the marked decomposition class remains unevaluated.
For the top quadratic cover, the identity generalized Prym with the reduced
zero/pole modulus has dimension `3^r`: its ordinary Prym quotient has
dimension `3^r-2^r` and its anti-invariant boundary torus has dimension
`2^r`.  The selected Kummer function gives only one Frobenius-stable tame
boundary line.  Its ray character is geometrically surjective on generalized
divisor classes, but this does not evaluate the literal totally inert place.
More strongly, every `F_2`-rational elliptic-curve `S`-unit supported on those
five rational torsion points evaluates into the same one-dimensional
odd-primary Kummer line as the target, so none is an independent detector.
After enlarging the support by the two translates of the complete selected
top Frobenius orbit, the `F_2`-rational anti-invariant principal-divisor
lattice has an exact three-vector basis.  The literal half-Frobenius selector
reduces all of its odd-primary evaluations to the two named function values
`g(P_n)` and
`Theta_n = M_n(x(P_n-T))/M_n(x(P_n+T))`.  These are two function generators,
not two independent value directions: the finite-field Kummer quotient is
cyclic and hence one-dimensional.  The order of the selected `Theta_n`
remains unevaluated.  A replayable generic `H = 32` certificate has
`[g(P)]_641 = 0` but nonzero `[Theta(P)]_641` (and a nonzero second
fixed-support-unit class); it violates the load-bearing selector
`x(P)^(2^16) = x(P)+1`, so it disproves an unmarked top-orbit inference but
is neither a Conway specialization nor evidence against arm `Z`.
The tempting curve
`y^2+y=x^3` is not isomorphic to the selected curve over `F_2`, and its
same-looking function has a trivial cubic Kummer class on positive-level
Fermat torsion. Perfectness of an alternating pairing still does not force a
prescribed pairing to be nonzero.

`formal/Ogdoad/Excess.lean` supplies ordinary kernel-checked Lean/algebra
without native evaluation.  Such theorems may still use Lean's standard
logical dependencies (`propext`, `Classical.choice`, and `Quot.sound`).  Its
declarations proved with `native_decide` are exact replayable finite evidence
and additionally depend on Lean's generated `_native.native_decide.ax_1_1`;
they are not ordinary kernel reductions. `DPrimeTarget` and the analogous
selected-order conditions encode open targets; they are not assumptions or
proofs of the rule.

### Missing step

Every arm ends at a one-dimensional value selected recursively by the literal
Conway tower. A complete proof must evaluate that marked coordinate uniformly
along its ancestry. Ambient statements about all points in the field do not
distinguish it from the formal countermodels with the same trace, norm,
torsion, or conductor data.

Cross-arm multiplicative induction has a sharp primary-vacuity boundary. If a
strict ancestor lies in `F_(2^d)` with `f(ell) ∤ d`, exactness of `f(ell)` gives
`ell ∤ 2^d - 1`, so the `ell`-power map on its multiplicative group is an
automorphism and its Kummer image is trivial. Thus cross-arm words built from
strict lower-level coordinates in such degrees are primary-vacuous. The next
`ell`-component does not repair this, because its radicand is defined as
`kappa_(f(ell)) + m_ell`; using its degree to identify `m_ell` with the
predicted `0`, `1`, or `4` is circular. A surviving cross-arm argument needs
a second, independently defined top-born `ell`-coordinate.

### Nim reciprocity program

This is a route into the same conjecture, not a fifth arm or a separate open
problem. For a relevant prime `ell` and nonzero selected element `beta` in
`F_(2^E)`, write

```text
rho_(ell,E)(beta) = beta^((2^E - 1)/ell) in mu_ell.
```

The target is an ancestry-recursive formula for these power-residue
coordinates in the literal Conway--Lenstra Kummer basis. It must satisfy all
of the following.

- Its input retains the marked compatible root sequence, rather than only an
  abstract finite field, conductor, or unselected Frobenius orbit.
- It is covariant under simultaneous absolute Frobenius on a compatible tower
  prefix, so conjugate choices give conjugate symbols and the same order.
- Where a coordinate is lifted to a number or ray-class field, its factors
  identify the selected prime over `2` and evaluate that term. A product
  formula over every conjugate, which is already forced to be trivial, is not
  enough.
- Applied to `T_h`, `y_(r,a)`, `gamma_k`, and `M_k`, it specializes to the
  marked primary coordinates in arms `Z`, `O`, `C`, and `D` respectively.

There is an exact rank-one saturation boundary. After adjoining `mu_ell`,
write a selected phase as `s` and index its absolute-Frobenius conjugates and
cyclotomic lifts by `(j,c)`. Covariance gives

```text
s_(j,c) = s^(2^j c).
```

Consequently every multiplicative reciprocity word in this entire two-axis
family is a single power `s^lambda`. If `lambda = 0 mod ell` it erases the
selected phase; otherwise it is equivalent to the original test `s != 1`.
The inverse-Frobenius/Teichmuller weighted projector recovers `s` exactly,
but does not evaluate it. Thus a successful reciprocity proof must import an
independently evaluable local class or a genuinely nonhomogeneous marked-
ancestry identity; adding further norm, character, or orbit-product axes to
the same Kummer class cannot create a second constraint.

Standard additive and nonabelian packages do not evade this boundary. A
Jacobi convolution at nonzero total `a` scales by the product-character value
at `a`, so on one Kummer line it is again a fixed scalar times one power of
the marked phase. In the split affine group, every one-step lift `(t,q)` with
fixed `q != 1` is conjugate to `(0,q)`, so class functions on that single
fixed-multiplier coset erase its frame coordinate. This does not apply to the
full-orbit element below: its `E`-th power is a pure translation, and an Artin
character over the cyclotomic base can distinguish zero from nonzero
holonomy, although evaluating it is the original selected problem.
A labeled off-diagonal Fourier coefficient exists after a root frame is
chosen, but that one-step coordinate is gauge-dependent. The intrinsic object
is the full `E`-step Frobenius-orbit holonomy

```text
T = sum_(j=0)^(E-1) 2^(E-1-j) t_j,
```

whose diagonal Fourier eigenvalue is the selected phase. Frame changes
modify the `t_j` by a telescoping coboundary and leave `T` fixed. Affine
composition does not evaluate it: every homomorphic cocycle is a coboundary
with trivial full-period holonomy, while every field value can occur as the
closing holonomy after the proper path has been normalized. Nim reciprocity
must therefore supply an independent Conway-ancestry evaluation of this
closed-cycle coordinate; constructing it from the selected symbol is only an
exact reformulation. An affine ancestry intertwiner does not supply the
missing source: its closed holonomy is only a scalar multiple of the source
holonomy, because every vertex-origin term telescopes. Thus a strict ancestor
with trivial `ell`-coordinate cannot create the required nonzero current
coordinate through an affine recursion.

Success is a uniform nonvanishing/full-primary-order proof for every resulting
coordinate, and therefore a proof of the `0/1/4` rule. Merely reconstructing a
residue symbol or its orbit product does not close the problem: existing norm,
Stickelberger, and reciprocity reductions already reach that boundary without
deciding the selected value.

### Evidence and authority

- Exact certificates establish the named implementation rows, not a universal
  formula.
- `experiments/ordinal_excess_probe.py`,
  `experiments/fermat_selected_screen.py`, and the guarded
  `experiments/ordinary_*_certificate.py` scripts are the maintained finite
  evidence.
- The implementation boundary is `src/scalar/big/ordinal/tower.rs`.
- The authoritative mathematical account is
  [`../writeups/excess.tex`](../writeups/excess.tex).

## 3. Natural realization of finite misère quotients

Let `A` be a set of finite impartial games closed under options and disjunctive
sum, and write `o^-(G)` for the misère outcome. Define

```text
G ~ H  iff  o^-(G + X) = o^-(H + X) for every X in A.
```

The quotient `Q(A) = A / ~` is a commutative monoid with identity `1` and a
distinguished subset `P` of previous-player wins. Thus the object to realize is
not a bare monoid but a reduced bipartite monoid `(Q, P)`: distinct elements
`x, y` must be separated by some `z` for which exactly one of `xz, yz` lies in
`P`. Misère terminal play also forces `1` not to lie in `P`.

The unrestricted finite realization question is already settled. A transition
table is a subset `T` of `Q × Pow(Q)`; its product is

```text
(x, E)(y, F) = (xy, xF ∪ yE).
```

Siegel's realization theorem says that a reduced `(Q, P)` with `1` outside
`P` is `Q(A)` for some closed set of impartial games exactly when it admits a
transition table that is parity-correct

```text
(x, E) in T  implies  [x in P  iff  E is nonempty and E ∩ P is empty],
```

complete over `Q`, closed under this product, and well-founded by a rank with
`R(1) = 0` that decreases along one option set for every element. The open
problem therefore begins only after imposing a natural ruleset class.

**Problem.** Characterize the finite reduced bipartite monoids that occur as
the exact misère quotients of finite-code octal games. The characterization
should be decidable from finite algebraic data and should either construct an
octal code and its quotient map or return an obstruction that rules out every
such code. An undecidability theorem, together with a maximal natural decidable
subclass, is an alternative resolution. In parallel, determine the exact
quotient of misère Grundy's game, whose single-heap positions satisfy

```text
opts(H_n) = {H_i + H_(n-i) : 1 <= i < n-i}.
```

For Grundy's game, decide first whether the full quotient is finite. If it is,
give a finite presentation, its `P`-portion, and a proved quotient map for all
heap sizes. If it is infinite, exhibit an infinite family of pairwise
distinguishable positions together with contexts that separate them.

The current exact reduction is in
[`../writeups/misere_natural_realization.tex`](../writeups/misere_natural_realization.tex).
In a reduced valid transition table, the option-value set determines its
value: a least-rank separating context would otherwise descend to a smaller
separating option. Thus a fixed octal code and table determine one exact heap
trace. The trace criterion is an if-and-only-if statement: all exact heap
records must lie in the table and their values must generate the target
monoid. For codes without split bits, a finite quotient forces this trace to
be ultimately periodic, since its next value is a deterministic function of
the last `d` values. Hence exact realization by a fixed finite no-split code
is decidable. Splitting introduces the unbounded convolution
`{x_i x_j : i + j = n}`; an already periodic trace still has a finite exact
certificate through the explicit bound `2N + p + d`, but automatic
periodicity is not proved for general split targets. Every value in a nontrivial valid
table has a context carrying it into `P`; combined with the meximal condition,
this proves that no transition value can occur among its own options. For an
octal trace this gives the absolute exclusions

```text
C_n                 => x_n != 1
A_k, k < n          => x_n != x_(n-k)
B_k, i+j = n-k      => x_n != x_i x_j.
```

These are exact obstruction filters, not a characterization.

For the periodic branch, a code-length bound is now proved. If an exact heap
word is periodic from `N >= 1` with period `p >= 1`, the same entire word
has a realizing code of length at most `3N+2p`. Keep the original bits up to
that bound and add bounded residue representatives of every persistent
offset. Translated original moves prove meximal safety, while stable split
convolutions supply the tail records. Terminal heaps require a separate
argument: all their smaller heaps have values `1` or the star `a`, so any
new safe option has value `a`. Thus synthesis for a supplied periodic word,
or for bounded preperiod and period, is decidable over all finite code
lengths. The proof permits enlargement of the valid table; it preserves the
word and exact quotient, not every original transition record.

The split recurrence also has an exact unary-language formulation. If
`X_q = {n : x_n = q}`, then the language where `q` occurs as an option is a
finite union of whole-removal constants, shifts of `X_q`, and shifted additive
convolutions `X_u + X_v` over `uv = q`; Boolean cells recover each complete
option-value set. The trace is total exactly when the union of cells on which
the partial decoder is undefined is empty. This dictionary is checked in
Lean. It does not collapse to a finite automaton: if the decoder is arbitrary
rather than a valid misère table, totality is `Pi^0_1`-complete already for
the fixed code `0.7`, by encoding unary unambiguous conjunctive-grammar
emptiness in a truncated multiset monoid. Thus any fixed-code decision theorem
must use closedness, parity, ranking, and reducedness essentially; finiteness
and commutativity alone are insufficient.

Validity does settle the hardness code itself: every nontrivial valid table
contains a star record `(a, {1})`, with `a^2 = 1`, and its positive transition
powers give the unique `0.7` trace `x_n = a^n`. The same proof covers every
code with only odd removal offsets and both whole-removal and one-remainder
moves at offset one. Its exact quotient is the two-element `C2`.

More generally, for **every split code targeting `C2`**, no-self forces all
options of a heap to have the same value. Comparing pairs at the same split
total proves `x_(n+2) = x_n` for every positive `n`. Only four two-letter
candidate words exist, and the constant-identity word is impossible. Lean
checks that testing the candidates through heap `d+5` decides totality for a
length-`d` code. The paper gives the equivalent explicit three-case mask
classification, including the terminal heaps; no period discovery is needed.

There is also a comparison normal-form theorem. Every nontrivial finite
valid quotient has an exact one-species numerical heap realization with a
finite source-local prefix, one inert padding heap, and the uniform tail move
`H_n -> H_(n-1)`. This is not a finite-octal realization: encoding a prefix
edge by an octal digit repeats that edge at every larger source heap. The
theorem isolates this translated cross-talk but does not prove it is the only
possible obstruction to a different octal gadget. More sharply, when the
quotient has more than two elements, no exact heapwise encoding of all chosen
descending prefix records can retain the later inert pad: some record needs a
nonidentity option, hence a persistent one- or two-remainder bit, and that bit
also gives the pad an option. An active bridge or a contextual generator
encoding remains possible.

Ordinary subtraction codes, whose digits lie in `{0,3}`, admit a complete
classification: their exact quotients are the trivial quotient, `C2`, and the
tame quotients `T_r` for `r >= 2`. For a nonempty finite subtraction set `S`,
let `g` be its normal SG sequence and `M = max g <= |S|`. The quotient is
`C2` if `M=1`, otherwise `T_r` where `2^(r-1) <= M < 2^r`. Ferguson's
zero/one shift and the resulting Bouton outcome law prove this for every
heap size and multiplicity. A finite SG window computes `M`; finite monoid
isomorphism tests decide synthesis over all ordinary subtraction codes,
without a code-length bound. The witnesses are the empty code, `0.3`, and
`2^(r-1)` consecutive digits `3`. This settles the entire ordinary
subtraction subclass, not general no-split codes or a maximal decidable class.

The parallel Grundy analysis is exact through heap 18: the quotient through
heap 13 has order 12, and the quotient through heap 18 has order 24, with
presentations, all-multiplicity outcome inductions, and separating translation
rows in the paper. These prefix theorems neither prove stabilization nor
supply an infinite distinguishable family. If the full Grundy quotient is
finite, finite Ramsey supplies unequal `i,j` with
`x_i = x_j = x_(i+j) = c`, so a heap record contains `c^2` among its options.
Closure and no-self force every two consecutive positive powers of `c` to
differ. Hence its power sequence has eventual period at least two, which is
compatible with tame behavior. A nontrivial kernel supplies no additional
Grundy obstruction: in every nontrivial valid quotient the star acts freely
by `q -> aq`, so every finite nonempty ideal already has even cardinality.

Global canonical theory does not automatically provide the missing Grundy
contexts. Write `a=*1`, `b=*2`, and `c={a,b,b^2}`, the canonical value of
`H_13`. The paper proves that no Grundy position is globally equivalent to
`k={0,b,b^2}` or `k+a`. Since `k` is the mate of canonical `c`, the global
value image of the Grundy universe is not closed under canonical mating.
The proof uses global cancellation and canonical-option lifting, followed
by descent in total counters and split rank; it is not a finite census.
Mating is not invariant under global equivalence, so this statement does
not identify the mate of the literal unreduced `H_13` tree. It excludes a
canonical-mate closure argument, not all possible separating contexts.

### Milestones and completion

1. Implement the valid-transition-table or minimex criterion as an exact
   certificate checker. This recovers the known abstract theorem and filters
   algebraically impossible candidates; it does not by itself address octal
   realization.
2. Produce a reproducible small-order atlas separating abstractly realizable
   quotients from those currently realized by finite octal codes. A bounded
   atlas is conjecture material unless the searched code class is itself
   proved exhaustive for the stated order.
3. Identify invariants preserved by finite-code octal realization but absent
   from arbitrary transition-table constructions, or prove a universality
   theorem showing that there are no additional obstructions.
4. For any claimed finite heap quotient, certify the infinite ruleset: prove
   the heap-value recurrence and the required eventual period or other
   induction, then verify surjectivity, reduction, and the `P`-portion. A
   stable bounded table is not enough.

The algorithmic gap has a fixed-trace layer and a synthesis layer. For fixed finite `(Q, P)`,
fixed valid `T`, and fixed split code, determinism makes the trace a partial
computable recurrence; deciding whether that recurrence is total remains
open for general targets beyond the solved classes above. The arbitrary-decoder `Pi^0_1`-completeness theorem identifies validity
as the precise missing restriction, but does not establish hardness for valid
tables, and valid-table totality for its own code `0.7` is automatic.
Periodic witness compression removes an independent code-length gap when
the preperiod and period are bounded. Monoid-level synthesis still needs a
computable bound on the necessary periodic complexity and an argument
accounting for realizations with nonperiodic heap words, or else an
undecidability theorem.

The octal-realization arm closes with the requested if-and-only-if theorem and
certified construction/obstruction algorithm. The Grundy arm closes with one
of the two exact finite/infinite certificates above. Calling a quotient
*wild* only means non-tame; it does not establish that the quotient is
infinite.

The starting theory is the [Plambeck--Siegel quotient
construction](https://arxiv.org/abs/math/0609825) and Siegel's
[valid-transition-table classification](https://arxiv.org/abs/math/0703070).
The algebraic determinism, meximal and no-self obstructions, exact quotient
sufficiency, periodic complete-record certificate, typed
prefix/pad/unary-tail normal form, inert-pad obstruction, unary-language
dictionary, safe saturation, terminal-prefix repair, actual compressed masks
and their all-heap record validity, star involution and free action,
odd-removal totality, binary
split periodicity and finite-candidate criterion, subtraction mex sequence
and all-position outcome law, and algebraic power-period obstruction are
checked in Lean. The formal-language hardness theorem, numerical rank-order
transport for the normal form, the exact-quotient interpretation of compressed
records and the bounded synthesis algorithm, explicit binary mask classification,
subtraction quotient identification and synthesis algorithm, exact
Grundy-prefix presentations, and canonical-mate obstruction are presently
paper proofs. The distinct-summand finite-color
bridge is checked from Mathlib's Hindman theorem.
The current `src/games/misere.rs` routines compare only bounded element and
test sets, so their signatures and multiplication flags are observational
evidence, not exact quotient certificates. The `misere_quotient` and
`octal_hunt` examples are useful census instruments under that boundary.
