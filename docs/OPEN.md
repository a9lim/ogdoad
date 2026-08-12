# Open mathematical problems

Exactly two research problems are open. This file states their present form
and proof boundary; the linked papers contain definitions, proofs, citations,
and fuller notation.

Evidence labels used here:

- **proved:** a paper proof, Lean theorem, or cited standard theorem;
- **certified:** an exact finite computation with replayable checks;
- **source-backed:** external mathematical data used with an identified source;
- **tested:** bounded computation consistent with the claim.

None of the last three labels implies a universal theorem.

## 1. Arbitrary-graph FIFO linking

### Conjecture

Let `G` be a finite simple graph on real vertices, augmented by one isolated
dummy vertex. Every vertex is opened once and later closed once. Closures occur
in FIFO order. A one-step ko protects the most recently changed vertex, with a
forced pass when no ordinary move is legal. Closing the queue front toggles a
binary score exactly when that vertex has odd degree in the untouched set.

**FIFO linking conjecture.** From the empty-queue, score-zero root, either
designated seat can force terminal score zero for every such graph.

This statement is stronger than the theorem used by the Gold--Arf
construction. A public Witt frame reduces that application to a disjoint union
of edges and isolated vertices, for which a both-seat strategy is proved.

### Affine form

For a complete history `h`, let `D(h)` be its universal live-star/disjointness
vector in the `F_2` edge space on the real vertices. Pairing `D(h)` with a
graph's adjacency vector gives the terminal score.

For a fixed attacker strategy `S` and its compatible terminal histories
`H_S`, finite-field separation gives

```text
S is harmless on every graph
    iff
0 lies in Aff{D(h) : h in H_S}.
```

Thus the defender needs an odd affine response flow with zero terminal edge
moment. When the queue front is `f`, the quotient

```text
T_f(z)_ij = z_ij + z_fi + z_fj
```

splits the current edge space into the cut star at `f` and the edge space after
deleting `f`. The missing theorem is a causal contraction through successive
front quotients while respecting the chosen strategy tree.

### What is proved

- `formal/Ogdoad/Fifo.lean` defines the exact terminating game, strategy
  predicates, score translation, queue/cut invariants, singleton tails,
  edgeless play, and close-first contractions. `FifoLinkingTheorem` is the open
  proposition, not an axiom or theorem.
- `formal/Ogdoad/FifoMatching.lean` proves the both-seat theorem for
  matching-plus-isolates boards. `ImpartialRealizer.lean` supplies the
  pass-free fixed-tempo compiler used by the Gold--Arf paper.
- `FifoNormalization.lean` proves complete pair-response fan identities and
  excludes close-first odd play at the isolated-dummy root.
- `FifoStrategy.lean`, `FifoAffine.lean`, and `FifoWinningRegion.lean` make the
  selected policy, its affine response space, and the Bellman-saturated region
  precise.
- The `FifoCross*`, `FifoCausal`, `FifoNeutralPair`, `FifoSameOpenBraid`,
  `FifoDummy*`, `FifoOuterFan`, `FifoProtectedFan`, `FifoRootSelector`,
  `FifoInterlace`, `FifoSymmetry`, and `FifoMinHotCurvature` modules prove local
  transport, fan, deletion, symmetry, and obstruction lemmas. They expose the
  surviving ancestry term rather than cancel it.
- Exact minimax agrees with the conjecture for every nonisomorphic board
  through eight real vertices plus the dummy, for both seats. This is tested
  evidence only.

### Remaining theorem

The local response fans contract, and descendants of a critical charged close
can be scalar-neutral. The missing causal contraction has two coupled parts:

1. prove that a lexicographically minimal bad node has either the candidate
   odd--odd charged-close ancestry or the protected-singleton/ko-wall ancestry;
2. in that ancestry, select compatible earlier defender siblings across FIFO
   front levels so that their prefixes and continuation cosets cancel the
   residual real-edge class with odd augmentation.

The paper proves the local ingredients of the proposed normal form but does
not claim their strategy-relative composition. The second part is the
multi-sibling factor extension.

Purely graph-local parity, fixed pairings, bounded-support affine circuits,
childwise continuation arguments, dummy deletion, and turn/score symmetry do
not supply this selection; explicit checked states delimit each route. A proof
must use causal information from the selected strategy tree, not only the
underlying graph or the set of terminal histories.

Authoritative paper: [`../writeups/linking_affine.tex`](../writeups/linking_affine.tex).
Executable model: `experiments/linking_game.py`.

## 2. Finite excess in transfinite nim multiplication

### Conjecture

For an odd prime `p`, the supported Conway--Lenstra Kummer carry has

```text
alpha_p = kappa_f(p) + m_p,       f(p) = ord_p(2),
```

where `m_p` is the finite excess. The conjectural universal rule is

```text
m_p = 0   if Q(f(p)) is not a singleton odd prime power,
m_p = 4   if f(p) = 2 * 3^k with k >= 1,
m_p = 1   otherwise.
```

The available table and exact certificates agree with this rule. The
universal statement is open.

### Four-arm reduction

The paper proves that the rule is equivalent to four selected order
assertions. None is known universally.

| arm | structural case | remaining selected assertion |
| --- | --- | --- |
| `Z` | non-singleton component support, including the singleton-even Conway--Fermat chain | the structural norm generates the primitive-support quotient; equivalently the terminal iterated norm/order coordinate is nonzero |
| `O` | singleton odd prime power with prime different from `3` | the selected projective class of `kappa_(r^a)+1` has the full required primary order |
| `C` | the cubic `3^k` chain | the selected Gaussian period `zeta + zeta^{-1}` is primitive, equivalently the final fixed cubic-norm coordinate is nontrivial |
| `D` | the exceptional `2*3^k` chain | the reconstructed selected Artin--Schreier/Dickson value is not a current-primary power; `DPrimeTarget` records this target |

If nonzero `beta` lies in `F_(2^E)` and `p` divides `2^E-1`, the exact
obstruction is

```text
beta has no p-th root
    iff
beta^((2^E - 1)/p) != 1.
```

Merely proving `p | ord(beta)` is insufficient when the ambient group contains
a higher `p`-power. The selected phase of the literal Conway tower is the
load-bearing datum; generic trace, norm, degree, factor shape, or Kummer
component information can lose it.

### What is proved or certified

- The four-arm equivalence, exact power criteria, boundedness reformulation,
  norm identities, and many phase-preserving reductions are proved in the
  paper.
- `formal/Ogdoad/Excess.lean` proves the first-non-power interface,
  group-theoretic lower bound, corrected sparse norm, exact cyclic/finite-field
  power tests, finite arithmetic screens, and algebraic lemmas used by the four
  reductions. `DPrimeTarget` is deliberately only a definition of the open
  universal target.
- The exceptional column has an unconditional effective bound depending on
  `k`; it does not prove an absolute bound on all `m_p`.
- The ordinary rows through the implementation cutoff include source-backed
  values and separate exact local certificates. They extend the operational
  Kummer window but do not establish a general formula.
- Exact finite screens and countermodels show that generic
  trace/norm/reciprocity, factor-shape, averaging, and unselected Kummer
  arguments cannot determine the distinguished Conway phase.

### Remaining theorem

Every arm has been reduced to a one-dimensional, recursively selected
nonvanishing/order coordinate. A complete proof must control that literal
coordinate uniformly along Conway ancestry. A generic statement about all
points in the ambient finite field, or about an unordered orbit of candidate
points, is not enough.

Authoritative paper: [`../writeups/excess.tex`](../writeups/excess.tex).
Implementation: `src/scalar/big/ordinal/tower.rs`.
Exact probes and certificates: top-level `experiments/*excess*`,
`experiments/ordinary_*`, and `experiments/fermat_selected_screen.py`.
