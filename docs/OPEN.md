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
| `O` | singleton odd prime power away from `3` | a marked cyclotomic unit has full primary order at the unique prime over `2` selected by Conway ancestry |
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
and exceptional arms. It also proves several finite tensor-rank zero cases and
shows why generic trace, norm, conductor, factor-shape, reciprocity, and
unselected Kummer information cannot recover the marked Conway coordinate.
The selected singleton-even realization lies on
`y^2+y=x^3+x^2`; its function is supported on fixed five-torsion rather than
the Fermat-torsion point, so for positive levels it is not an `F_n`-Weil or
reduced-Tate pairing function attached to that point. The tempting curve
`y^2+y=x^3` is not isomorphic to the selected curve over `F_2`, and its
same-looking function has a trivial cubic Kummer class on positive-level
Fermat torsion. Perfectness of an alternating pairing still does not force a
prescribed pairing to be nonzero.

`formal/Ogdoad/Excess.lean` kernel-checks the algebraic reduction layer
without native evaluation.  Its declarations proved with `native_decide` are
exact replayable finite evidence and depend on Lean's generated native-decision
axiom; they are not ordinary kernel reductions. `DPrimeTarget` and the analogous
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
periodicity is not proved in that case. Every value in a nontrivial valid
table has a context carrying it into `P`; combined with the meximal condition,
this proves that no transition value can occur among its own options. For an
octal trace this gives the absolute exclusions

```text
C_n                 => x_n != 1
A_k, k < n          => x_n != x_(n-k)
B_k, i+j = n-k      => x_n != x_i x_j.
```

These are exact obstruction filters, not a characterization.

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

There is also a uniform positive family: for every `n >= 2`, the finite code
with `2^(n-1)` consecutive digits equal to `3` has exact quotient `T_n`, the
tame quotient of order `2^n + 2`. This realizes the entire tame arm of the
finite `|P| = 2` classification. The parallel Grundy analysis is exact through
heap 18: the quotient through heap 13 is a reduced monoid of order 12, and the
quotient through heap 18 is a reduced monoid of order 24, with presentations,
all-multiplicity outcome inductions, and separating translation rows in the
note. These prefix theorems neither prove stabilization nor supply an infinite
distinguishable family. There is also a global conditional obstruction: if
the full Grundy quotient is finite, finite Ramsey supplies unequal `i,j` with
`x_i = x_j = x_(i+j) = c`, so a heap record contains `c^2` among its options.
Closure and the no-self theorem force all consecutive positive powers of `c`
to differ. Hence the power sequence has eventual period at least two and the
kernel of the finite quotient is nontrivial. This is compatible with tame
period-two behavior and is not yet an infinity proof.

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

The algorithmic gap has two independent layers. For fixed finite `(Q, P)`,
fixed valid `T`, and fixed split code, determinism makes the trace a partial
computable recurrence; deciding whether that recurrence is total is still
open. The arbitrary-decoder `Pi^0_1`-completeness theorem identifies validity
as the precise missing restriction, but does not establish hardness for valid
tables. Even if every fixed-code instance became decidable, monoid-level
synthesis ranges over unbounded code lengths. A complete decision procedure
therefore also needs a computable length bound or pumping normalization, or
else an undecidability theorem.

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
dictionary, and algebraic power-period obstruction are checked in Lean. The
formal-language hardness theorem, numerical rank-order transport for the
normal form, tame-family strategy, kernel deduction, and exact Grundy-prefix
presentations are presently paper proofs. The distinct-summand finite-color
bridge is checked from Mathlib's Hindman theorem.
The current `src/games/misere.rs` routines compare only bounded element and
test sets, so their signatures and multiplication flags are observational
evidence, not exact quotient certificates. The `misere_quotient` and
`octal_hunt` examples are useful census instruments under that boundary.
