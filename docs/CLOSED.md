# CLOSED: Current Theorem Index

This file records solved research questions as mathematical results, not as a
development chronology. Implementation milestones remain in [`DONE.md`](DONE.md),
while the two unsolved fronts remain in [`OPEN.md`](OPEN.md).

Since 2026-08-12, five of the seven results share one flagship paper:
[`goldarf.tex`](../writeups/goldarf.tex), "Quadratic Refinements in Normal
Play: Realization and the Observation Boundary", absorbed the former
`gold_diagonal_source.tex` (as its diagonal-source section),
`brown_game_semantics.tex` (as its Brown-selector section), the
`game_exterior_deformation.tex`/`game_exterior_divisibility.tex` pair (as its
game-exterior appendix), and — same day, after an adversarial consult pass —
the block-compression note `observation_width.tex` (as its every-width
attainment corollary `cor:blocks`). The retired standalones survive in git
history.

| solved question | answer | authoritative paper |
|---|---|---|
| Gold quadratic zero sets in normal play | every finite characteristic-two quadratic refinement has a uniform normal-play realization, with an optimal observation bound | [`goldarf.tex`](../writeups/goldarf.tex) |
| diagonal sources for every Gold exponent | every unscaled Gold diagonal in the canonical quadratic nim tower is an Artin--Schreier value | [`goldarf.tex`](../writeups/goldarf.tex), diagonal-source section (`thm:all-diagonal-source`) |
| a game-native Clifford deformation on short-game values | ambient coherence forces all quadratic and polar values into `⋂ₖ4ᵏR` — identically zero over `ℤ`, in characteristic 2, and over `ℤ/4` — and every torsion square and polar pairing to vanish over every coefficient ring | [`goldarf.tex`](../writeups/goldarf.tex), game-exterior appendix (`sec:game-exterior`) |
| quadratic classification over the full nimber field | the nonsingular Witt and Brauer--Wall classes vanish; `(dim V, dim rad B, dim rad Q)` is the complete singular invariant — standard math applied to a new scalar world | [`transfinite_arf.tex`](../writeups/transfinite_arf.tex) |
| Brown game semantics | one partizan selector realizes all four local Brown residues; every ambient-coherent Brown colour on all short games is zero | [`goldarf.tex`](../writeups/goldarf.tex), Brown-selector section (`sec:brown-selector`) |
| thermography versus Newton polygons | positive numeric Norton units obey the exact thermic law `temp(G.u) = u·temp(G) + (u − δ_u)` with a classified composition defect; the shared shadow is tropical but no faithful full-dyadic graded ring exists | [`thermo_newton.tex`](../writeups/thermo_newton.tex) |
| observation width above weight one | block aggregation of the weighted-source rule attains the integral transcript-span bound `ceil(wt(x)/w)` exactly at every fixed width, under the same access contract at `(w_0, c) = (w, 1)` | [`goldarf.tex`](../writeups/goldarf.tex), block-compression corollary (`cor:blocks`) |

## 1. Gold quadratic zero sets have a normal-play realization

Let `V` be a finite `F_2`-space, let `B` be alternating, and let `Q` be any
quadratic refinement of `B`. There is a uniform finite normal-play game whose
`P`-set is exactly

```text
{x in V : Q(x) = 0}.
```

A deterministic public Witt frame turns the polar support into a matching plus
isolates. Active original coordinates contribute matched source pairs carrying
their singleton diagonal weights. The both-seat FIFO matching strategy forces
zero correction charge, and a phase-aware terminal claim compiles the resulting
bit to ordinary normal play. The Arf invariant and radical data therefore give
the exact second-player zero-set bias.

The construction is optimal at its access boundary. Any transcript-stable exact
realizer must observe directions spanning the input; weight-`w` observations on
a weight-`t` input require at least `t/w` observations. The singleton source
pairs attain this bound. Outcome-preserving terminal padding also proves that
reachable or unavoidable winning forks cannot by themselves certify
refinement-sensitive naturality.

The general isolated-dummy FIFO conjecture is not part of this theorem. Gold
boards reduce to matchings, for which the needed strategy is proved in every
dimension.

Proof surfaces:

- [`writeups/goldarf.tex`](../writeups/goldarf.tex)
- [`formal/Ogdoad/FifoMatching.lean`](../formal/Ogdoad/FifoMatching.lean)
- [`formal/Ogdoad/GoldMatchingAlgebra.lean`](../formal/Ogdoad/GoldMatchingAlgebra.lean)
- [`formal/Ogdoad/GoldSemantics.lean`](../formal/Ogdoad/GoldSemantics.lean)
- [`formal/Ogdoad/GoldNoEvaluator.lean`](../formal/Ogdoad/GoldNoEvaluator.lean)
- [`formal/Ogdoad/GoldForkPadding.lean`](../formal/Ogdoad/GoldForkPadding.lean)

## 2. Every Gold exponent has a constructive diagonal source

For every power-of-two degree `m >= 2` and every Gold exponent `a`, the
trace-dual of the canonical-basis diagonal of

```text
Q_a(x) = Tr(x * x^(2^a))
```

descends to the half-field and has absolute trace zero. Hence it is
`w^2 + w` for a deterministically constructed tower element `w`, and

```text
Q_a(e_i) = Tr((w^2 + w) e_i)
```

for every canonical basis coordinate. This holds for odd and even exponents.
The statement is deliberately unscaled: a general coefficient need not have a
trace-zero dual. The normal-play theorem above supplies the strategic layer
separately.

Proof surfaces:

- [`writeups/goldarf.tex`](../writeups/goldarf.tex), diagonal-source section
  (`thm:all-diagonal-source`): the one-line trace proof, the closed
  trace-dual bit basis, the scaled recursion and unscaled descent, and the
  tower-recursive Artin--Schreier solver
- [`formal/Ogdoad/GoldDiagonal.lean`](../formal/Ogdoad/GoldDiagonal.lean)
- [`src/forms/trace_form.rs`](../src/forms/trace_form.rs)

## 3. Ambient-coherent game Clifford data are Grassmann on torsion

Presentation-relative quadratic tables are valid local algebra: a chosen
finitely generated subgroup may satisfy the required null and polar-radical
relation checks. They do not define a quadratic datum intrinsic to game values.

Moews's structure theorem makes the additive group of short games
power-of-two divisible with power-of-two torsion (finite orders are powers of
two by Conway's Theorem 92). Divisibility alone forces, in any
coefficient-faithful additive grade-one realization,

```text
Q(x), B(x,y) in the intersection of all 4^k R,
```

which is identically zero over `Z`, in characteristic 2, and over `Z/4`.
On torsion, if `nt = 0`, rooting `t` and `x` separately (`ny = t`, `nz = x`)
forces

```text
Q(t) = 0,
B(t,x) = 0
```

over every coefficient ring. Thus every global datum, and every family
coherent over all finitely generated subgroups (the quantifier is essential),
factors through the torsion-free quotient. Characteristic two and torsion
coefficient rings do not evade the conclusion. Nonzero Gold forms remain valid
on the nimber field-like core because its multiplication and trace are extra
structure; they cannot extend coherently to all partizan games.

Proof surfaces:

- [`writeups/goldarf.tex`](../writeups/goldarf.tex), game-exterior appendix
  (`sec:game-exterior`): the sharpened `⋂ₖ4ᵏR` conclusion, the corrected
  root-x torsion anticommutator proof, the all-f.g.-subgroups coherence
  quantifier, and the framing as a negative answer to Altman--Lipparini
  Problem 5.3(j)
- [`formal/Ogdoad/GameExterior.lean`](../formal/Ogdoad/GameExterior.lean)

## 4. The full nimber field has no Arf or Witt bit

Over every perfect characteristic-two field with surjective Artin--Schreier
map, every nonsingular finite-dimensional quadratic form is hyperbolic. The
full nimber field `On_2` is algebraically closed of characteristic two, so
this applies there:

```text
W_q(On_2) = 0
```

and every nonsingular quadratic Clifford/Brauer--Wall class is split. A
possibly singular form is classified by the dimension triple
`(dim V, dim rad B, dim rad Q)`. Claim level: standard math (Arf, EKM,
Hoffmann--Laghribi) applied to a new scalar world; the note's contribution is
the application and the corrective observation that an Arf bit is relative to
a declared subfield and dies in the colimit.

The finite-field Arf bit remains correct relative to a declared finite nimber
subfield. It vanishes after scalar extension to a sufficiently large field and
therefore does not survive the directed limit. The executable ordinal backend
retains a separate representability boundary: the mathematical roots may lie
outside its checked Kummer window.

Proof surfaces:

- [`writeups/transfinite_arf.tex`](../writeups/transfinite_arf.tex)
- [`formal/Ogdoad/Off.lean`](../formal/Ogdoad/Off.lean)

## 5. Brown labels contain one linear and one quadratic bit

Every Brown refinement has the unique canonical decomposition

```text
ell = q mod 2,
q   = lift(ell) + 2 Q,
B_Q = b + ell tensor ell.
```

Its four residue classes are therefore the synchronized pair `(ell,Q)`, and its
Gauss phase is the correlated Walsh combination

```text
G(q) = ((1+i)/2) W(Q) + ((1-i)/2) W(Q+ell).
```

The linear bit has a local XOR realization and the Gold theorem supplies the
ordinary quadratic normal-play bit. For its exact ordinary arena `A_R(x)`, the
single partizan game

```text
B_q(x) = { A_(Q+ell)(x) | A_Q(x) }
```

has intrinsic outcome `N,R,P,L` for Brown residues `0,1,2,3`, respectively.
Only one follower is played; this is primitive partizan option formation, not
an external synchronized product, and there is no terminal evaluator. Its
outcome census recovers the full correlated Brown Gauss phase.

Globally, any ambient-coherent Brown datum on the additive group of all short
games vanishes by two-divisibility. A bare `Z/4 -> Z/8 -> Z/2` extension is
insufficient to recover a Brown phase without a chosen section.

Proof surfaces:

- [`writeups/goldarf.tex`](../writeups/goldarf.tex), Brown-selector section
  (`sec:brown-selector`): the canonical split, the correlated Walsh
  identity, Wood-coordinate phase formulas with the singular boundary, the
  intrinsic selector with the `*, ↓, 0, ↑` normalized forms, and the
  outcome census
- [`formal/Ogdoad/BrownGame.lean`](../formal/Ogdoad/BrownGame.lean)

## 6. Thermography and Newton polygons are two tropical objects

The paper's center (post the 2026-08-12 restructure) is the positive result:
every positive numeric Norton unit `u` obeys the exact thermic law

```text
temp(G.u) = u * temp(G) + (u - delta_u)
```

proved by a simultaneous birthday induction on raw wall identities
(`D_{A_u(G)}(a_u + u t) = u * D_G(t)`), with the composition defect
`Delta(u,v) >= 0` fully classified at zero. Temperature also obeys a
non-Archimedean maximum inequality, and exact thermograph recursion is a dual
max-plus/min-plus fold. This is the shared tropical shadow.

It cannot be upgraded to one faithful full-dyadic graded ring. The degree-zero
game residue contains the nonzero order-two class `[*]`; any invertible
coefficient representing `2` would have to kill it. Independently, numeric
Norton transports have a nonnegative composition defect that is positive for
`u = 1/2`, `v = 2`, so they do not form a multiplicative dyadic action even
after a temperature-preserving refinement.

Characteristic-two quotients, integer-only coefficient actions, nonunital or
nonassociative structures, and quotients killing `[*]` are not excluded. Each
drops a defining hypothesis of the proposed full-dyadic unification.

Proof surfaces:

- [`writeups/thermo_newton.tex`](../writeups/thermo_newton.tex)
- [`src/games/heating.rs`](../src/games/heating.rs)
- [`src/scalar/newton.rs`](../src/scalar/newton.rs)

## 7. The observation boundary is attained at every width

Let `B` be alternating on a finite `F_2`-space, `Q` any quadratic refinement,
`x` any input, and `w >= 1` a fixed width. Partition `supp(x)` into
`k = ceil(wt(x)/w)` blocks of size at most `w` with indicator vectors `z_i`;
the Gram data `B(z_i, z_j)` is an alternating form on `F_2^k` and the
restriction of `Q` along the block embedding is one of its quadratic
refinements, with diagonal `Q(z_i)` and all-ones value exactly `Q(x)`.
Playing the weighted-source rule on this induced instance, with each induced
singleton query implemented as the original-frame query `Q(z_i)`, satisfies
the F1–F3/N1–N2 access contract at `(w_0, c) = (w, 1)`, has root outcome `P`
exactly when `Q(x) = 0`, and has possible oracle support exactly the `k`
block vectors — total weight `wt(x)`, cardinality `ceil(wt(x)/w)`.

Since certificate cardinality is integral, the transcript-span lower bound
already forces `ceil(wt(x)/w)` observations, so the bound is attained
exactly, not merely up to a ceiling: the observation complexity of exact
transcript-stable realization under the contract is `ceil(wt(x)/w)` at every
fixed width, with the weight-one singleton support of the original rule as
the `w = 1` case. Overlapping observation geometries cannot beat the
partition count within the uniform contract, and a width-tagged disjoint
union serves every width at once.

The question was posed as the flagship's second residual open on 2026-08-12
and closed the same day: the reduction survived a sol-tier adversarial
consult, whose corrections (original-interface disjoint-union framing,
possible-oracle-support phrasing, the explicit `x = 0` case, and the integral
strengthening) are incorporated in the folded corollary.

Proof surfaces:

- [`writeups/goldarf.tex`](../writeups/goldarf.tex), block-compression
  corollary (`cor:blocks`)
- [`formal/Ogdoad/GoldBlockCompression.lean`](../formal/Ogdoad/GoldBlockCompression.lean)
- [`formal/Ogdoad/GoldNoEvaluator.lean`](../formal/Ogdoad/GoldNoEvaluator.lean)

## The remaining open fronts

Only the following research questions remain open:

1. the arbitrary-graph causal affine-contraction theorem for FIFO linking;
2. the universal Lenstra excess `0/1/4` rule;
3. the impartial uniform realizer;
4. the game-native extraspecial extension model.

Their exact current formulations and evidence boundaries are in
[`OPEN.md`](OPEN.md).
