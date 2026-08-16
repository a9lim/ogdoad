# Open mathematical problems

Ogdoad has four live research problems. The first two are universal
conjectures with exact reductions; the remaining two are constructive or
classification programs with explicit completion criteria. This document
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

`formal/Ogdoad/Excess.lean` kernel-checks the algebraic reduction layer and
finite certificates used by the paper. `DPrimeTarget` and the analogous
selected-order conditions encode open targets; they are not assumptions or
proofs of the rule.

### Missing step

Every arm ends at a one-dimensional value selected recursively by the literal
Conway tower. A complete proof must evaluate that marked coordinate uniformly
along its ancestry. Ambient statements about all points in the field do not
distinguish it from the formal countermodels with the same trace, norm,
torsion, or conductor data.

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

## 3. Fast multiplication in canonical nim coordinates

Put `n = 2^k` and

```text
K_k = {0, ..., 2^n - 1} = F_(2^n),
```

represented by the literal `n`-bit nimber word. If
`c_i = 2^(2^i)`, these coordinates are the multivariate tower basis for

```text
c_i^2 + c_i = product_(j < i) c_j.
```

Thus finite nimbers are an explicit quadratic Artin--Schreier tower, not an
arbitrary polynomial-basis presentation of the same abstract finite field.

**Problem.** Construct a uniform family of exact multiplication algorithms

```text
mul_k : K_k x K_k -> K_k
```

whose inputs and output are canonical nim words and whose bit complexity is
`M(n) log^O(1)(n)`, where `M(n)` is binary-polynomial multiplication cost.
Auxiliary space and any level-dependent conversion data must also have
`n log^O(1)(n)` size; preprocessing may be reported separately but may not hide
a quadratic multiplication tensor or table.

### Known starting point

The standard direct tower recurrence takes `O(k 3^k)`, or
`O(n^(log_2 3) log n)`, bit operations. The current `u128` backend instead
distributes over the set bits and memoizes products of basis powers; it is an
exact fixed-width implementation, not an asymptotic result.

Quasi-linear arithmetic for arbitrary Artin--Schreier towers is already known:
the substantive target is therefore not an existence conjecture about finite
fields. It is an explicit specialization of the fast tower-isomorphism and
basis-conversion machinery to the literal Conway generators above, with a
proof that the returned bit string is the canonical nim product.

### Completion criterion

A completion consists of all four items.

1. Give forward and inverse transforms between canonical nim coordinates and a
   fast multiplication basis, uniformly in `k`.
2. Prove the tower equations, transforms, multiplication, and stated time and
   space bounds, including precomputation.
3. Supply an arbitrary-width implementation with exhaustive agreement against
   the mex/direct oracle on small fields and differential agreement against the
   existing backend on its full supported word widths.
4. Measure the crossover. Retaining the present `u128` path below it is
   compatible with solving the problem; a faster fixed-width table alone is
   not.

The mathematical starting point is the fast arbitrary-tower construction of
[De Feo--Schost](https://arxiv.org/abs/1002.2594). The implementation boundary
is `src/scalar/finite_field/nimber/arithmetic.rs`.

## 4. Natural realization of finite misère quotients

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

The octal-realization arm closes with the requested if-and-only-if theorem and
certified construction/obstruction algorithm. The Grundy arm closes with one
of the two exact finite/infinite certificates above. Calling a quotient
*wild* only means non-tame; it does not establish that the quotient is
infinite.

The starting theory is the [Plambeck--Siegel quotient
construction](https://arxiv.org/abs/math/0609825) and Siegel's
[valid-transition-table classification](https://arxiv.org/abs/math/0703070).
The current `src/games/misere.rs` routines compare only bounded element and
test sets, so their signatures and multiplication flags are observational
evidence, not exact quotient certificates. The `misere_quotient` and
`octal_hunt` examples are useful census instruments under that boundary.
