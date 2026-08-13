# Open mathematical problems

Ogdoad has two unresolved mathematical claims. This document states only their
current form, proved reductions, and exact missing step. The linked papers carry
the definitions and arguments; finite experiments never substitute for either
universal theorem.

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
