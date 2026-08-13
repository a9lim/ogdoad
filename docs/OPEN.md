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

- `formal/Ogdoad/Fifo.lean` defines the exact terminating game and the open
  proposition `FifoLinkingTheorem`. Matching-plus-isolates boards are proved
  both-seat even in `FifoMatching.lean`; this is sufficient for the Gold--Arf
  construction and does not use the conjecture.
- `FifoPublicPolicyAffine.lean` forgets graph scores while retaining the
  attacker's selected moves, every defender reply, and the affine live-star
  moments of compatible terminal histories. `FifoPublicPolicyDuality.lean`
  proves the exact equivalence
  `UniversalPublicPolicyAffine ↔ FifoLinkingTheorem`: if projected zero is
  absent, affine separation is represented by an isolated-dummy graph and
  reconstructs an odd counterstrategy. The graph-free affine target is
  therefore the conjecture itself, not a weaker sufficient condition.
- The strategy, affine, normalization, causal, cross-descent, dummy-deletion,
  outcome, and symmetry modules prove the local response identities and their
  exact failure surfaces. Minimizing a score-zero bad occurrence inside one
  odd strategy leaves only a charged-CLOSE spike or protected-singleton
  predecessor, with its actual root prefix and complete defender fan retained.
  Descendant-only, local third-sibling, fixed-pairing, scalar block, and
  graph-congruence arguments do not cancel the inherited continuation coset.
- `FifoPublicSeparatorAutomaton.lean`,
  `FifoPublicSeparatorAncestry.lean`, and
  `FifoPublicSeparatorQueueDebt.lean` give the sharp dual normal form. In a
  constantly-one public policy, a globally rank-minimal sheet-one occurrence
  with the dummy still live is attacker-selected and chooses a real
  separator-unit `OPEN v`. Its complete-fan child is sheet zero; every legal
  edge of that fan has separator increment zero; the old queue is nonempty;
  and handshaking supplies a distinct separator-odd vertex already in that
  queue. Thus the parity partner is debt, not a legal OPEN sibling. The forced
  CLOSE sibling enters a selected sheet-zero continuation but does not force
  further CLOSEs.
- `FifoCanonicalPositionalOdd.lean` proves that every odd-winning state has a
  full-state positional strategy whose equal-state occurrences have literally
  equal continuations. This closes the memoization gap but not the selection
  gap. `FifoPublicPolicyTopologyBoundary.lean` proves that the
  history-occurrence tree has injective edge boundary and no cycles.
  `FifoPositionalSelectedEdgeBoundary.lean` gives a positional Bellman policy
  which avoids both complementary edges of the relevant dummy diamond, while
  `FifoPositionalStateDAGBoundary.lean` shows that quotienting by equal full
  states can create a cycle whose live-star label still has nonzero real-edge
  projection. Neither history-tree topology nor state-DAG incidence alone
  yields the required zero moment.
- The separator minimum and the concrete minimal-bad node are genuinely
  different: separator sheet one minimizes potential
  `score + queueCut`, whereas the bad-ancestry theorem minimizes score zero.
  `FifoLastChargedCloseBoundary.lean` proves that every score-one occurrence
  reached from the initial root has a last unit-charged CLOSE followed by a
  pointwise score-neutral suffix. A queued separator-debt vertex either
  survived behind that front or was opened in the suffix. An exact
  initial-root public-policy occurrence realizes the survivor case with a
  charging neighbour distinct from the debt; the ko wall blocks moving the
  survivor opener later, while moving the charging neighbour earlier
  neutralizes the CLOSE. Legality and parity therefore do not synchronize the
  two minima.
- Controlled-outcome descent requires two score-coupled odd policies, not one
  sheet-zero continuation. The controlled-state modules prove that every
  reachable rank-minimal controlled state on an isolated-dummy graph has
  already consumed the dummy. However,
  `FifoSeparatorControlledBridgeBoundary.lean` gives the exact local
  obstruction to invoking that result at the separator minimum: the
  separator-zero complete-fan child and its forced CLOSE sibling can both be
  cold `BothOdd` with the dummy untouched, and score translation makes the
  child `BothEven`. No coupled right odd policy, hence no controlled descent,
  follows from separator minimality alone.
- The dynamic Gaussian route has a real but limited invariant. On an even
  carrier every opener has a distinct same-degree mate with zero second
  moment, and every alleged odd strategy at such a pair contains a strictly
  smaller score-zero descendant. The condition is not recursively preserved:
  a checked third-moment example breaks the natural next pair, and the
  five-vertex star gives an odd q=0 pair whose zero descendant has empty queue.
  That counterexample has no isolated vertex. After adjoining an isolated
  dummy, the displayed star pair is exactly even-winning. Thus the restricted
  isolated-dummy q=0 safety statement remains open and is evidence, not a
  proved induction.
- Exact minimax agrees with the conjecture for every nonisomorphic board
  through eight real vertices plus the dummy, for both seats. A separate
  five-minute targeted labelled search found no counterexample beyond that
  census. At total order ten (nine real vertices plus the dummy), 3,742
  distinct completed graphs all returned the fixed-even root value; the set
  comprised the sharp selector seed, all 36 one-edge flips, all deduplicated
  `7 × 256` one-new-real attachment extensions of seven order-eight
  no-dummy anti-mover seeds, and local one-to-four-edge mutations up to the
  time cap. At total order eleven, 346 completed sharp-seed-plus-one-real
  attachment patterns out of 512 also returned fixed-even; four in-flight
  cases at cutoff are excluded. These bounded results are tested evidence
  only, not an exhaustive certificate at either order.

### Remaining theorem

The exact task is to rule out a constantly-one initial public policy, or
equivalently prove that every initial public policy has projected affine
moment zero. At its rank-minimal sheet-one occurrence the local picture is
fully determined: a selected real unit OPEN moves to a complete sheet-zero
fan and leaves its parity partner as nonempty queued debt. The missing step is
global and ancestry-sensitive.

A proof must use the occurrence's path from the initial root to relate that
queued debt to the last charged CLOSE and then select an odd family of earlier
defender siblings whose prefixes and continuation cosets cancel the residual
real-edge class. It must handle both exact FIFO order branches: the debt may
survive behind the charged front or may be opened in the neutral suffix.
Neither branch can be reordered away using only ko legality and score parity.

The available no-go theorems delimit what this comparison must contain.
Canonical positionality does not force either edge of a commuting dummy
square; history trees have no cycles; full-state quotient cycles can carry
nonzero edge label; separator-zero children need not be controlled; and q=0
pair descent can lose every queued pair without an isolated dummy. Hence the
remaining factor cannot be a local Bellman tie-break, an unlabelled
state-DAG cycle, score translation alone, or an unrestricted scalar pair
induction. It must import a second correlated continuation from strictly
earlier initial-root ancestry. The isolated-dummy q=0 safety statement is a
possible auxiliary route, but it too requires a new invariant that survives
the dummy branch and the smaller zero descendant.

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
| `Z` | non-singleton component support, including the singleton-even Conway--Fermat chain | the cubical Frobenius coboundary of the structural norm has full primary order in the canonical primitive-support quotient; on the literal supersingular curve, the fixed function `(y+1)/y` has full next-Fermat order at the recursively selected point |
| `O` | singleton odd prime power with prime different from `3` | the marked cyclotomic unit has full primary order at the unique inert prime ray over `2` selected by Conway ancestry |
| `C` | the cubic `3^k` chain | the unique Frobenius orbit recursively selected inside the Singer trace set has full norm-one order; equivalently, both the relative principal `2`-ray kernel and the relative reduced unit/circular-unit kernel are trivial |
| `D` | the exceptional `2*3^k` chain | one marked conductor-`5` cyclotomic unit is a non-current-power globally and generates the current primary circular residues, but its principal-ray/reduced-unit index at the Conway-selected prime over `2` must still be proved trivial |

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
- The singleton-even chain has an exact supersingular-curve realization:
  its selected point has an exact Fermat annihilator, but the target value is
  a fixed ramified Kummer function rather than a pairing value. The ordinary
  cyclotomic primes form a unique inert ancestry ray, but residue-field
  norm/corestriction kills the new current coordinate. The cubic ancestry
  selects one exact Frobenius orbit in a Singer difference set, and its trace
  map is explicitly Möbius-conjugate to cubing. The resulting marked root is
  exactly the square of the selected primitive `3^(k+1)`-st root; this exposes
  rather than evaluates its cyclotomic-unit phase. That phase is equivalently
  constrained by a selected Singer sieve: unconditionally
  `ord(eta_k) >= h(h-1)+1`; if a current prime `ell` is missing, then
  `N/ell >= h(h-1)+1`, so every prime
  `ell > N/(h(h-1)+1)` occurs with its full valuation. This is a genuine
  ancestry-sensitive range, but its polynomial bound does not close the
  remaining factors. The phase is also equivalently
  parity of one explicit integer cyclotomic resultant; Lucas's theorem gives
  its exact binary support, but proper candidate exponents exceed the
  cyclotomic degree exponentially, so support and degree do not force oddness.
  The exceptional auxiliary
  recursion is an affine form of the same toric Dickson system, not a direct
  Drinfeld or smooth elliptic division tower; this does not identify the
  auxiliary value with the actual `D` target.
- In the ordinary arm, the ramified finite-log coordinates at primes over the
  current prime determine the Kummer ray character only modulo an unramified
  class-group character. The selected Artin exponent is exactly a ramified
  local term plus that character evaluated on the Conway-selected prime over
  `2`; the remaining assertion is noncancellation of these two marked terms.
  The unramified class is a quotient of an explicit decomposition-invariant
  Stickelberger module. Its semisimple obstruction is a generalized-Bernoulli
  half-sum (with conductor Euler factors); decomposition at `2` forces neither
  outcome, and nonsemisimple blocks retain higher augmentation data. Conway
  ancestry forces each contributing character to retain the full current
  `r`-part of the conductor, but leaves possible inherited Euler factors and
  the irregular half-sum unresolved. This is a genuine obstruction: at the
  actual Conway conductor `r = 11, a = 1, p = 23`, one contributing
  semisimple Stickelberger scalar vanishes while every omitted-conductor
  Euler factor is nonzero. Its generalized Bernoulli number has exact
  `23`-adic valuation one; Solomon's class-component theorem therefore
  gives an actual cyclic order-`23` irregular component in the associated
  degree-`22` field. An exact Hensel/Kummer certificate now proves more:
  the mirror cyclotomic unit defines the corresponding everywhere-unramified
  degree-`23` extension, and every prime over `2`, including the
  Conway-selected prime, has nontrivial Artin symbol and generates this
  class line. The literal row nevertheless has `m_23 = 1`. Thus a successful
  row can have a nonzero unramified marked-class term; in any fixed ray split,
  its ramified lift does not cancel that term. The unresolved universal
  assertion is the actual selected sum, not principality of the marked prime
  or uniform Bernoulli nonvanishing.
- For every residue degree `h`, an explicit cubical Frobenius coboundary has
  kernel equal to the product of all maximal proper subfield unit groups and
  image of exact order `Phi_h(2)`. It therefore gives a canonical coordinate
  on the primitive-support quotient and preserves every primary factor tested
  by `Z`. Separated additive cubes are nontrivial in this coordinate, but the
  selected structural norm is synchronized and can erase that raw class;
  nonidentity also does not imply full primary order.
- In the singleton-even chain, every compatible binary root-choice prefix is
  one absolute-Frobenius orbit, so ordinal lexicographic selection is a gauge
  rather than an extra phase. For each divisor `e` of the Fermat quotient
  order there is an exact primitive packet `C_e`; proper order is equivalent
  to the selected Conway minimal polynomial landing in that packet. Every
  packet factor has a unique irreducible child under the Conway resultant;
  trace one, relative trace/norm, residue degree, and unramifiedness hold for
  proper packets just as they do for the full packet. The exact parent/child
  conductor transition is a marked Dickson-word evaluation, and its image in
  child torus coordinates is the cubic equation `(A*Aq)^2=(A+Aq)^3`; hence an
  ambient proper-order child is irrelevant unless it lies in this recursively
  selected image. Iterating the equation gives a top-only torsion system, but
  its solution set is exactly the literal Frobenius/inverse packet, so meeting
  a proper subgroup is equivalent to the original order failure rather than a
  weaker dimension or Bezout question. Across all levels, a
  proper-order vector is equivalent to one marked prime over `2` satisfying
  the complete bivariate Conway resultant chain. The remaining conjecture is
  exclusion of every proper-conductor prime chain. Before those bivariate
  equations are imposed, the individual marked primes are globally
  independent: the relevant real cyclotomic fields are linearly disjoint,
  and every tuple of packet primes over `2` is realized by a prime of their
  compositum. The ancestry equations themselves define the single field
  `F_(2^(2^n))`; their Jacobian is a unit, so the scheme is reduced, etale,
  and one Frobenius orbit. Adding proper-packet equations therefore gives
  either that same literal orbit or the empty scheme. Common-prime
  compatibility, intersection multiplicity, and discriminant parity supply
  no further obstruction. An exact degree-16 witness
  has full parent conductor but a deterministic degree-32 child of proper
  conductor, so conductor-only induction is false. Uniform Dickson tangency
  shows why low Hasse jets cannot repair it: the first term distinguishing a
  missing-prime extraction appears only beyond the whole unreduced child
  basis. The familiar Wiedemann/Q-transform block recursion is also not the
  Conway block recursion: if `Omega(B)=[[B,I],[I,0]]`, the Conway step is
  exactly `Psi(B)=Omega(B)^(-1)(Omega(B)+I)^3`, a cubic Laurent map rather
  than the quadratic Q-transform. Its maximal Fibonacci-index assertion is
  therefore a distinct literal-word conjecture; Seyfarth--Ranade leave the
  analogous Wiedemann word open. Symplectic torus type alone again permits
  the proper child. The finite witness is exactly replayed by the
  selected-screen self-test; it is not
  promoted to a literal ancestry counterexample.
- In the cubic arm, the exact index of the selected subgroup in the norm-one
  torus factors as a relative principal `2`-ray kernel times a reduced
  unit/circular-unit kernel. The latter divides a relative real class-number
  quotient; even class number one would leave the principal ray factor, so
  ordinary circular-unit index theorems do not prove `C`. If `d_k` is the
  finite-field index of the reduced circular units in
  `Q(zeta_(3^(k+1)))^+`, then exactly
  `[U_k:<eta_k>]=d_k/d_(k-1)` and
  `d_k=(2^(3^k)-1)/ord(zeta_k+zeta_k^(-1))`. Thus `C` is equivalent to
  primitivity of these marked composite-conductor periods. Hoechsmann’s
  prime-conductor example at `37` has inert `2` and real class number one
  but defect `3`, proving those coarse hypotheses cannot kill the ray term.
- In the exceptional arm, the literal translate by four is the reduction of
  a marked conductor-`5` cyclotomic unit. An abelian height bound proves this
  unit is not a current-prime power anywhere in `Q^ab`, while an exact
  two-prime cubical coboundary identifies the same primitive-support
  coordinate as `D`. At each current prime, the full primary reduction of the
  circular-unit group is generated by this marked element, so the remaining
  index factors exactly as a principal `2`-ray kernel times a reduced
  unit/circular-unit quotient; the latter is class-number controlled. All
  conjugate first Kummer evaluations are scalar multiples of one marked
  value, so global nonpower and homogeneous orbit identities remain
  compatible with that selected value vanishing.
- Direct Gauss-sum reciprocity isolates the same marked scalar as a ratio of
  an untwisted and an additively twisted Gauss sum. The cubic current
  character is not semiprimitive; in the exceptional arm only the untwisted
  sum is semiprimitive, while evaluating the twisted sum is exactly the open
  residue symbol. The unavoidable conductor-five mixed Jacobi terms are not
  semiprimitive either. Jacobi congruence theorems identify the faithful
  projection of the first oriented coefficient family with the selected
  power-residue line, but inversion, Frobenius, and ancestry act homogeneously
  on it; the zero coefficient obeys every such symmetry.
- The current cubic and exceptional residue coordinates are orthogonal: their
  norm-one tori have coprime orders, the exceptional cubical operator kills
  the cubic subfield, and the local norm kills the exceptional torus. Thus
  the two principal-ray factors cannot force each other through the shared
  prime over `2`; each requires its own global-unit image calculation.
- In the exceptional real field, both remaining factors live in the faithful
  character sending Frobenius at `2` to multiplication by `2`. At the cubic
  step this character has zero invariants and zero norm despite being
  nonzero, so ambiguous-class, genus, and ordinary norm arguments are
  structurally blind to the exact component that must vanish.
- After faithful-character localization, reduction of the selected circular
  unit is multiplication by one scalar. Multiplication by a unit and by the
  current prime have identical character and norm data but opposite
  surjectivity behavior. Regulator, Fitting, or Stickelberger information
  must therefore compute this marked local scalar rather than only its source
  module or annihilator.
- Differentiating the adjacent-level norm polynomial does not determine the
  scalar: its derivative is a unit on the current character, but the resulting
  right-hand side is the unknown Bockstein/Selmer localization class. The
  faithful circulant regulator determinant likewise factors into the
  principal-ray and reduced unit/circular-unit lengths. These nonnegative
  obstructions cannot cancel, but the determinant does not make either one
  vanish.
- A two-block tensor-rank obstruction proves the multicomponent zero arm at
  `h = 12, 15, 24, 36, 40`. The `h = 15` proof retains the full synchronized
  norm phase, while `h = 36` checks both prime factors of `Phi_36(2)` by
  symbolic tensor minors. These are theorem-level finite advances, not a
  universal generation argument.
- `formal/Ogdoad/Excess.lean` proves the first-non-power interface,
  group-theoretic lower bound, corrected sparse norm, exact cyclic/finite-field
  power tests, toric semiconjugacy, alternating two-step cubic conjugacy,
  supersingular coordinate symmetry, cubical `C/D` orthogonality and
  faithful-character norm blindness, the Dickson tangency factorization, the
  Conway/Wiedemann Laurent distinction, the supplied `p = 23`
  grouped-coefficient dot product and Euler-factor product, and the supplied
  nontrivial binary Artin phase, finite screens, and algebraic lemmas used by
  the four reductions.
  `DPrimeTarget` is deliberately only a definition of the open universal
  target.
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
nonvanishing/order coordinate. A complete proof must evaluate that literal
coordinate uniformly along Conway ancestry. Degree, torsion, norm,
corestriction, conductor, factor parity, or a generic statement about all
points in the ambient field does not distinguish it from a proper-order or
power-residue countermodel.

Authoritative paper: [`../writeups/excess.tex`](../writeups/excess.tex).
Implementation: `src/scalar/big/ordinal/tower.rs`.
Exact probes and certificates: top-level `experiments/*excess*`,
`experiments/ordinary_*`, and `experiments/fermat_selected_screen.py`.
