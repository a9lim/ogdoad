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
- `FifoHub.lean` proves score-erased schedule equivariance, exact live-star
  transport, transposition-defect identities, and the corresponding
  characteristic-two graph-congruence formula. These are algebraic transport
  statements, not a strategy or root-value conjugacy.
- `FifoEmptyQueue.lean` proves that every nonterminal empty-to-empty block has
  equally many OPENs and CLOSEs, no PASS, even length, and the same mover at
  its two endpoints. `FifoBlockInduction.lean` kernel-checks an exact
  first-return splicing interface, while explicitly recording that its
  scalar/parity-only mover hypothesis is false. `FifoOutcome.lean` proves the
  exact four-valued debt involution `(M,N) -> (not N,not M)` on the
  mover/nonmover outcome sheet; `FifoOutcomeBlock.lean` proves that allowing
  precisely the favorable complete-outcome exits is equivalent to the
  original winning assertion, so that reformulation alone is circular.
  `FifoOutcomeAlgebra.lean` proves abstractly that a ko-locked neutral pair is
  not an operation on those four outcome classes. `FifoOutcomeSwitch.lean`
  gives the FIFO-realized obstruction: a dummy-deleted root is both-even, yet
  its front-dummy and rear-dummy active intervals have opposite outcomes for
  the same seat despite identical deleted real public data.
  `FifoTreeTrace.lean` and
  `FifoQPotential.lean` give small checked obstructions to the raw all-leaf
  sum and to maintaining the queue-cut potential pointwise.
  `FifoPairState.lean` proves that any score-zero mover failure with an OPEN
  available forces a lower minimum-hot singleton wall whose charged endpoints
  are real; it deliberately does not identify that globally minimal wall with
  a descendant of the original counterstrategy.
  `FifoStrategyBadAncestry.lean` repairs that ancestry defect by minimizing
  inside one supplied odd strategy. It retains exact root prefixes and the
  complete immediate defender fan, proves that the selected bad move is a
  charged CLOSE of a real front with a neutral translated continuation, and
  excludes the neutral-CLOSE predecessor. `FifoStrategyBadAncestryClear.lean`
  excludes the remaining clear-OPEN predecessor: its CLOSE sibling forces the
  next front to have unit charge, while all OPEN siblings make that front
  universal on the even carrier and hence give charge zero. Thus the exact
  strategy-relative normal form has only the charged-CLOSE spike and
  protected-singleton cases.
  `FifoFirstSeatRoot.lean` proves the exact first-seat root normal form: the
  first physical player wins precisely when some initial OPEN has a complete
  winning fan over every legal second OPEN. The stronger claim that every
  ordered initial pair is winning is sufficient, but remains unproved.
  `FifoFirstSeatStrategy.lean` extracts from one hypothetical odd root strategy
  its fixed-point-free selected second-opener map, exact common-root ancestry,
  and a nontrivial periodic orbit. `FifoBadArcCycle.lean` proves that every
  selected cycle has zero aggregate two-OPEN prefix. For an odd cycle the
  continuation sum has nonzero real-edge projection; for an even cycle it is
  only a homogeneous response direction. Thus the cycle alone does not
  contract the root strategy. `FifoFunctionalDigraphBoundary.lean` shows that
  adding the feeding in-trees does not create a graph-independent repair: an
  isolated-dummy separator can evaluate every selected arc prefix to one, so
  every odd arc subfamily still has nonzero real-edge projection.
  `FifoDummyFront.lean` proves the exact neutral diamond
  `CLOSE d; OPEN z = OPEN z; CLOSE d` below an initial dummy-first pair. It
  also proves that an even win there requires some even-winning
  dummy-consumed real-pair child. Thus opening the dummy first moves the
  selector obligation to a no-dummy pair rather than solving it.
  `FifoDummyFrontAffine.lean` proves that on the conjecture's odd total
  carrier, the complete dummy-front legal fan has even cardinality and its
  projected OPEN-prefix sum is the surviving real star of the second opener,
  not zero. No local odd response point can have that projection, so an
  earlier-ancestry affine point is genuinely required.
  `FifoStrategyInteraction.lean` proves that complementary-seat odd policies
  at the same state interact to a common odd terminal, so the direct diagonal
  is compatible rather than contradictory. `FifoSelfPlay.lean` isolates the
  exact contradictory target--same-seat odd subtrees at score-and-turn-
  conjugate states--and proves that neutral dummy moves cannot supply its
  score bit, while the dynamic cross-exit comparison retains a one-front
  queue lag. Thus two-copy strategy stealing also stops at the earlier-sibling
  factor extension.
  `FifoSeparatorFlow.lean` proves the corresponding conservation law: an odd
  zero-prefix fan has continuation residue of separator value one, even after
  adding any homogeneous root direction. `FifoThreeSiblingBoundary.lean`
  gives an exact same-tree countermodel to the naive repair: complete
  immediate OPEN ancestry need not contain a sibling whose selected move is
  the lag-removing CLOSE. The missing object is therefore an odd incidence
  across correlated continuation cosets, not merely an additional immediate
  branch.
  `FifoRootCongruence.lean` gives the exact graph-shear boundary. Opposite
  strategies on a graph and its elementary congruence interact to one common
  public trace and live-star moment; if the root winner changes, the
  congruence-row defect evaluates to one on that correlated moment. This is an
  obstruction identity, not root-value invariance.
- Exact minimax agrees with the conjecture for every nonisomorphic board
  through eight real vertices plus the dummy, for both seats. This is tested
  evidence only.

### Remaining theorem

The local response fans contract, descendants of a critical charged close can
be scalar-neutral, and the exact strategy-relative minimal-bad ancestry
classification is now proved. The sole remaining theorem is the causal factor
extension: in the charged-CLOSE spike and protected-singleton cases, select
compatible earlier defender siblings across FIFO front levels so that their
prefixes and continuation cosets cancel the residual real-edge class with odd
augmentation. Descendant-only, immediate-third-sibling, cycle-only, and
functional-digraph-incidence versions are all formally ruled out; the required
factor must use correlated continuation cosets from strictly earlier ancestry.

For the first-seat half there is also a sharper root-level target. A
hypothetical odd root strategy contains every first OPEN and selects one
second OPEN below each of them, so all of those bad ordered pairs share one
strategy ancestry. Proving that this selected first-two-OPEN fan has a safe
branch would settle the first-seat half. Treating the pair states as unrelated
conditioned games discards exactly this common ancestry and has not produced a
proof.

Finiteness does force a directed cycle in the selected reply map, and its
two-OPEN live-star prefixes cancel exactly. This does not finish the argument:
an odd cycle has the right affine augmentation but its continuation sum is
provably nonzero after real-edge projection, whereas an even cycle has only
the augmentation of a direction. A successful first-seat contraction must
therefore incorporate an in-tree branch or another earlier sibling in
addition to the cycle. Incidence alone is still insufficient even after all
in-tree branches are included: the explicit seven-vertex functional-digraph
separator evaluates each selected arc prefix to one, so every odd subfamily
remains nonzero in the real-edge quotient.

Choosing the isolated dummy as the first opener does not avoid this boundary.
At the resulting pair `[d,y]`, closing `d` before a real open `z` and opening
`z` before closing `d` reach the same score-zero state `[y,z]`. If every such
dummy-consumed child is odd-winning, the odd player uses the opposite side of
this diamond against either defender move and wins `[d,y]`. Hence a successful
dummy-first strategy already needs a winning consumed real pair; neutrality
alone is not a strategy steal.

The affine obstruction agrees exactly. On odd total order the legal fan
consisting of `CLOSE d` and every remaining `OPEN z` is even, while the sum of
the OPEN prefixes projects to the full real star of `y`. Graph evaluation
shows that no response point at `[d,y]` can project to that star. Hence the
missing repair cannot be manufactured inside the local dummy-front fan; it
must arrive from the common initial ancestry.

Purely graph-local parity, fixed pairings, bounded-support affine circuits,
childwise continuation arguments, dummy deletion, and turn/score symmetry do
not supply this selection; explicit checked states delimit each route. A proof
must use causal information from the selected strategy tree, not only the
underlying graph or the set of terminal histories.

Empty-queue blocking does not remove that requirement. Although a
nonterminal first-return block preserves the physical mover, neither forcing
every such block to score zero nor allowing only a residual-cardinality bit is
a valid universal induction hypothesis. Even with an isolated dummy, the
stronger demand that a neutral first return retain the dummy fails on
`K_3 + d` and `K_4 + d`, in the two seat orientations. Once the dummy has
been consumed, the exact residual datum is the two-seat outcome pair of the
remaining no-dummy root, together with the current score. Equivalently, the
next valid reduction must carry that outcome-valued debt or the full affine
continuation coset; one scalar block charge is insufficient.

The complete four-valued root sheet is still not a compositional substitute
for those continuations. Deleting the dummy reverses the controller of every
real event strictly inside its OPEN/CLOSE interval. A strategy interaction
would therefore have to switch the designated no-dummy seat at both interval
endpoints. Even a both-even no-dummy root does not make the opposite-seat
strategy available at a state selected by the first strategy. The three-label
active-interval example proves this failure exactly; interval order and
strategy ancestry are indispensable.

Direct self-interaction has the same sharp boundary. Two odd policies for
complementary designated seats at one public state can be played against each
other to a terminal node belonging to both trees; both require odd score, so
there is no contradiction. A contradiction would instead follow from two
same-seat odd subtrees rooted at `s` and at the score-and-turn conjugate of
`s`. An isolated dummy can reverse the controller phase inside its active
interval but never changes the score. At the singleton wall it leaves a ko
defect, and a charged real-front repair supplies a score bit only together
with a one-front queue lag and the corresponding real-edge curvature. Hence
two-copy self-play reproduces the causal factor gap: a strictly earlier
universal sibling must absorb the lag/edge defect and align the two
continuation cosets.

Even the phrase "an earlier sibling" must be interpreted as a multi-branch
incidence, not as one favorable immediate reply. In a one-dimensional
separator quotient the root affine space is `{1}` and its direction space is
`{0}`. Every complete-fan and curvature identity survives, while an odd
zero-prefix fan necessarily leaves continuation value one. A concrete
same-tree FIFO policy on an edgeless score-one state realizes the operational
counterpart: its CLOSE child selects an OPEN, but neither immediate OPEN
sibling selects the CLOSE needed to remove the queue lag. Hence fan
completeness plus homogeneous corrections cannot prove the conjecture; the
new theorem must correlate an odd family of continuation cosets across more
than one level of ancestry.

The apparent topological shortcut is also excluded. With history occurrences
retained, an attacker-pruned policy is a tree, so its edge-boundary map is
injective and supplies no nonzero cycle. Identifying publicly reconvergent
histories would add OPEN/CLOSE diamonds, but their live-star cochain has
curvature equal to the crossed real edge, and the two occurrences can carry
different continuation cosets. Similarly, deleting the dummy can require a
ko-wall exchange that changes one real edge moment and reverses control of the
repaired move. These facts force a history-indexed mapping-cone or equivalent
ancestry construction; ordinary oik cancellation and policywise dummy
deletion cannot prove the missing factor extension.

An exact nine-real-vertex root witness makes the surviving selector boundary
sharp: after one real opener, eight of the nine possible OPEN replies lose and
only the isolated dummy wins. The dummy is the opener's unique same-degree-
parity mate, and its child has an explicit parity-cell pairing certificate.
This is finite evidence, not a counterexample, but it rules out replacing the
existential root selector by a robust or universal reply claim.

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
  row can have both a nonzero ramified local term and a nonzero unramified
  marked-class term; the unresolved universal assertion is their actual
  selected sum, not principality of the marked prime or uniform Bernoulli
  nonvanishing.
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
