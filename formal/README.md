# Lean formalization

This standalone Lean 4 project tests how much of the current proof threads
can be moved from checked prose and exhaustive computation into a proof kernel.
It pins Lean and mathlib independently of the Rust workspace.

```sh
cd formal
lake update       # only when intentionally refreshing the pinned manifest
lake build
```

The sources contain no `sorry`, `admit`, or custom `axiom` declarations.

## Gold diagonal source

[`Ogdoad/GoldDiagonal.lean`](Ogdoad/GoldDiagonal.lean) kernel-checks the
load-bearing algebra of the all-exponent Gold diagonal theorem:

- the two relative-trace coordinate identities in a characteristic-two
  quadratic tower with `sigma(u) = u + 1`;
- reconstruction of the upstairs trace-dual from the two downstairs duals;
- vanishing of the absolute trace of a base-field element in a quadratic
  extension; and
- the full finite-field exact sequence
  `im(w ↦ w²+w) = ker(absolute trace)`, proved by rank--nullity and trace
  surjectivity, plus the additive and tower-lifting identities.

The concrete canonical nim-field recursion and its basis identifications are
implemented and exhaustively tested in `src/forms/trace_form.rs`. Lean proves
the abstract identities and the finite-field existence theorem from the stated
hypotheses; it does not encode the `u128` nim multiplication implementation.

## Brown game semantics

[`Ogdoad/BrownGame.lean`](Ogdoad/BrownGame.lean) kernel-checks the algebraic
resolution of the independent `over` invariant question:

- every Brown refinement on an exponent-two additive group splits canonically
  as `q = lift(ell) + 2Q`, with `ell = q mod 2` additive and `Q` an ordinary
  characteristic-two quadratic form;
- the corrected polar is `B_Q = b + ell tensor ell`, and Lean proves it is
  alternating, symmetric, and biadditive;
- the converse construction and pointwise round trip show that no Brown value
  is lost in the split;
- on a two-divisible source, every exponent-four Brown-compatible quadratic
  value is zero, and every additive exponent-two quotient is trivial; and
- the explicit abelian extension `Z/4 -> Z/8 -> Z/2` realizes the odd Brown
  line only after a section is chosen, proving that a bare central extension
  does not determine the phase; and
- the single partizan selector `{A_(Q+ell) | A_Q}` has outcomes `N,R,P,L`
  for residues `0,1,2,3`, with a kernel-checked fixed decoder back to `q`.

The external instantiation remains source-pinned: Moews proves the additive
short-game group is a direct sum of copies of `Z[1/2]` and `Z[1/2]/Z`, hence
is two-divisible.  The Lean file proves the full implication from that abstract
divisibility hypothesis but does not encode short games or Moews's theorem.
The Lean selector layer abstracts each shipped ordinary quadratic arena by its
proved `P iff bit = 0` contract; it checks the partizan root semantics and
four-class decoder rather than re-encoding the full weighted-source arena.

## Game-exterior divisibility obstruction

[`Ogdoad/GameExterior.lean`](Ogdoad/GameExterior.lean) formalizes the algebraic
core of the resolved `tisn` problem:

- an additive grade-one realization in an arbitrary associative ring;
- explicit `n`-th roots of a torsion game and of an arbitrary second input;
- the resulting square-zero and polar-anticommutator-zero identities; and
- coefficient-valued `Q(t)=0` and `B(t,x)=0` corollaries when the coefficient
  map into the Clifford algebra is injective;
- polarization forced by the Clifford relations, symmetry of the polar value,
  and `Q(x+t)=Q(x)`, the torsion-coset invariance behind quotient factorization.

The external game theorem remains source-pinned rather than axiomatized here:
Moews proves that the short-game group is a countable direct sum of
`Z[1/2]` and `Z[1/2]/Z`, hence power-of-two division is available, and that all
finite-order short games have power-of-two order.  The Lean file proves the
entire ring-theoretic implication from explicit roots, without encoding the
short-game group itself.

## `off`

[`Ogdoad/Off.lean`](Ogdoad/Off.lean) formalizes the load-bearing algebra of the
resolved full-`On₂` classification through a set-sized algebraically closed
characteristic-two field:

- Frobenius and Artin–Schreier surjectivity;
- an explicit change of every normalized symplectic pair to a hyperbolic pair,
  preserving its plane span;
- simultaneous conversion of a supplied symplectic family; and
- the polar-radical normal form `Q = ℓ²`, with either `ℓ = 0` or a
  codimension-one zero kernel after normalizing a vector with `ℓ(e) = 1`.

The set-sized field is a proxy, not an encoding of Conway's proper class.  The
mathematical reduction is that any finite form and its finitely many algebraic
roots lie in a set-sized algebraically closed subfield.  The standard
symplectic decomposition theorem for a finite-dimensional alternating form is
used as the interface to `hyperbolic_family_of_symplectic_family`; this project
does not yet re-formalize that general linear-algebra theorem.

## Lenstra excess

[`Ogdoad/Excess.lean`](Ogdoad/Excess.lean) formalizes theorem-level algebraic
ingredients used by the Lenstra-excess reductions, including the exceptional
`2·3^k` column:

- the first-non-`p`-th-power definition of finite excess;
- the group-theoretic lower bound: a shared order class coprime to `p` makes
  the `0,1,2,3` translates `p`-th powers, hence `m_p ≥ 4`;
- the corrected norm
  `(kappa+a)(kappa+a+1) = kappa²+kappa+(a²+a)`, specializing to
  `kappa²+kappa+omega`;
- the exact cyclic-group and finite-field Euler-quotient criteria for being a
  `p`-th power, including the prime-order shortcut used at Fermat-prime levels
  and the equivalence between maximal order and simultaneous non-`p`-power at
  every prime divisor of the ambient cyclic-group order;
- the full-primary quotient lemma behind the norm-blindness obstruction, and
  the simple-zero theorem showing that the cubic norm discards the current
  Kummer coordinate while its first transverse derivative survives;
- the cubic arm's square-zero exceptional-residue calculation modulo `3n`,
  including the distinguished lift `an - 1`;
- the denominator-free square-zero cross-product identity behind the
  exceptional arm's canonical four-Jacobi detector;
- the denominator-free alternating-determinant identity behind its quadratic-
  relative Eisenstein reduction;
- the exact coboundary-to-fibotomic projection, normalized
  Artin--Schreier quadratic, and symmetric cubic norm-coherence identity behind
  the Conway C-to-D selector bridge;
- the characteristic-two Mobius trace identity
  `M + M^(-1) = (w^2+w)^(-1)` behind the exceptional arm's selected
  one-variable Dickson critical value;
- the denominator-free cyclotomic Artin--Schreier identity used by the paper's
  trace-one, norm-coherent alternative coefficient; the finite-field trace,
  degree, norm, and primary-power consequences remain paper-level deductions;
- the general uniqueness lemma that transports compatible power roots through
  a multiplicative map when powering is injective, plus the symmetric
  pair-product coefficients (D, C*E, E^2) behind the iterated cubic Dickson
  fibre;
- the denominator-free quadratic-remainder norm
  `(U+xV)(U+x'V) = U^2 + YUV + Y^3V^2` used by the paper's one-branch
  Conway--Fermat descent;
- the denominator-free normalization of the selected Singer cubic to
  `tau^3 + d^2*tau^2 + 1 = 0`, together with the coefficient-ancestry identity
  `s_k^3 = s_(k-1)*tau_(k-1)^2`;
- the characteristic-two semiconjugacy transporting the cubic arm's
  cyclotomic critical factor back to the actual Conway cubic;
- the denominator-free cyclic-resolvent Artin--Schreier equation and
  orientation trace-shift identity behind the exceptional arm's explicit
  terminal cubic;
- the characteristic-two Berlekamp-numerator factorization and its literal
  vanishing on the selected reciprocal cubic;
- the denominator-free characteristic-two identity that depresses every
  trace--constant Dickson cubic to an Artin--Schreier cubic;
- the four-axis reciprocal-root factorization behind the theorem that a
  trace--constant cubic with anisotropic quadratic lift lies on the smaller
  (Q^2-Q+1) Dickson torus;
- the characteristic-two algebra behind the singleton-even relative-trace
  collision: Artin--Schreier additivity, the centered ratio identity, and the
  exact fixed-field versus norm-one Mobius alternatives; and
- the open target `DPrimeTarget M`, namely `Psi_k | orderOf (M k)` for every
  level.

Lean also reduces the complete `k=2,...,6` factor products and every recorded
`ord_p(2)=2·3^k` residue screen.  Primality is proved locally through `k=4`;
the larger factors retain the paper's explicit source-assisted boundary.
These are arithmetic input checks, not a proof that the distinguished circle
element `M_k` has the required order.  The universal `D'_k` assertion remains
open, as do the finite `M_k` computations beyond the separately maintained
Python certificate.

## FIFO linking

[`Ogdoad/Fifo.lean`](Ogdoad/Fifo.lean) gives an authoritative transition system
for the reduced odd-close parity game from `experiments/linking_game.py`:

- OPEN, FIFO CLOSE, forced PASS, ko delay, mover, and the `ZMod 2` score;
- score-translation equivariance for every transition, its exact
  even/odd strategy-sheet equivalences, and the singleton-wall reconvergence
  of `C_f; O_z; O_w` with `O_z; C_f; O_w` after the next real OPEN;
- the abstract fixed-front closure recursion, including kernel-checked
  exclusion of every affine sheet-one separator at a defender root and the
  sharp sheet-zero policy showing why a designated immediate-close leaf
  cannot generally be retained;
- strict rank descent, absence of nonterminal stuck states, and preservation of
  the queue/untouched invariant;
- an explicit existential/universal finite strategy tree;
- its explicit odd-forcing dual, kernel-checked finite determinacy and
  incompatibility (`EvenWins` iff no `OddWins` counterstrategy);
- explicit membership in one fixed `OddWins` strategy tree and a
  strategy-relative minimum theorem: every zero-sheet odd counterstrategy
  contains a selected charge-one CLOSE whose translated child has a fully
  score-neutral continuation tree; more generally, an explicit score-one
  subtree translates directly to a neutral tree.  Opponent-controlled
  moves have score-neutral child trees (`TreeNeutralWins.answer_child`), and
  singleton closes in such tails have charge zero, so any complete family of
  punctured singleton tails forces the induced untouched graph to be
  Eulerian.  The writeup's scalar dual-minimum argument supplies that family
  in case `(B)`;
- an absolute-target `CloseFirstWins` strategy tree, whole-queue drain
  identities, and the dummy-free `ConditionedCloseFirstTheorem`: from every
  coherent ko-clear defender checkpoint with nonempty queue, a close-first
  attacker cannot force the score to change;
- the isolated-dummy hypothesis and exact general theorem statement;
- the queue-cut potential, including CLOSE and PASS conservation and the fact
  that no flip is possible once the untouched set is empty; and
- the exact singleton-untouched queue scan used by the terminal repair
  corridor, together with a formal winning strategy for every queue satisfying
  that scan; and
- a complete strategy proof for the edgeless base class.

`FifoLinkingTheorem` is a proposition, not an axiom or claimed theorem.  The
general isolated-dummy result remains open: the missing mathematical step is
the global causal affine-contraction/factor-extension lemma identified in
`writeups/linking_affine.tex`.  In particular, the conditioned close-first
theorem controls final parity but not score-one STOPs at intermediate attacker
checkpoints; that stronger prefix-safe normalization is false locally and its
root-level sibling coupling is still open.  The Lean development therefore
hardens the semantics and the proved reduction spine without laundering the
finite census through `k = 8` into a proof for all finite graphs.

[`Ogdoad/FifoMatching.lean`](Ogdoad/FifoMatching.lean) closes the exact
subclass needed by the resolved Gold construction:

- `IsMatchingGraph` says every vertex has at most one neighbour, hence the
  board is a matching plus isolates;
- `evenWins_of_matching` gives a rank-inductive strategy from every score-zero
  state at the designated seat's turn, or at a safe opponent front;
- `evenWins_initial_of_matching` proves that either seat forces zero flip
  parity from the empty-queue root, without a dummy; and
- `evenWins_initial_of_every_submatching` formalizes the same public-branching
  induction for every edge-deleted submatching. Its move branches inspect only
  the public matching, although `EvenWins` does not expose a first-class policy,
  so the literal `exists policy, forall submatching` and per-close trace
  statements remain paper-level observations; and
- the abstract hyperbolic-plus-radical graph and induced-subgraph lemmas provide
  the matching target; the paper supplies the concrete Witt-frame and loaded-
  support instantiation.

This does **not** prove the arbitrary-graph isolated-dummy conjecture.  It
shows instead that the conjecture is an unnecessary strengthening for Gold.

## Gold normal-play semantics

[`Ogdoad/GoldMatchingAlgebra.lean`](Ogdoad/GoldMatchingAlgebra.lean)
kernel-checks the quadratic expansion in a supplied adapted basis: selected
basis diagonals plus the parity of hyperbolic pairs whose two coordinates are
active. It includes the exact split in which each adapted diagonal is a public
polar correction plus a transported original-frame linear source.
The standard existence of a symplectic-plus-radical basis for a finite
alternating form remains an ordinary linear-algebra input; the file proves the
identity once such a basis and the split-diagonal hypotheses are supplied. It
does not define the original-frame change-of-basis matrix or prove that its
concrete public correction is `P_B(f_i)`; that elementary polarization step
remains in the paper.

[`Ogdoad/GoldSemantics.lean`](Ogdoad/GoldSemantics.lean) proves the semantic
compiler independently of the FIFO mechanism:

- a recursive winning-status compiler models retaining every move and adding
  one terminal claim exactly when the current seat is designated by the charge;
- mutual backward induction proves winner equivalence at every subtree and phase, so
  stance one has a P-root exactly when the forced charge is zero;
- the Boolean complement identity behind the need for a mover/phase bit;
- outcome-dominance pruning makes mixed-successor criticality impossible in
  every two-class game; and
- the local Boolean swap identity for a two-action fork.

[`Ogdoad/GoldNoEvaluator.lean`](Ogdoad/GoldNoEvaluator.lean) proves the sharp
observation boundary. Coordinate-free, transcript stability and exactness
force the input into the span of the observed vectors. In the Boolean
coordinate frame it proves

```text
weight(x) <= number of observations * maximum observation weight
```

and rules out uniform exactness under a bounded total certificate. The paper's
weighted-source rule uses exactly the active singleton directions and attains
this support bound.

[`Ogdoad/GoldForkPadding.lean`](Ogdoad/GoldForkPadding.lean) proves generic
Bool-parameter fork padding. It replaces every terminal P-node of an arbitrary
finite normal-play tree by an outcome-equivalent forced wrapper leading to an
always-N swapping fork, and `win_padTerminals` proves the root outcome is
unchanged. The paper instantiates the Bool as a chosen refinement bit and
draws the fork-screen corollary.

These files kernel-check independent ingredients of the synthesis in
`writeups/goldarf.tex`; there is no single end-to-end Lean theorem constructing
the weighted-source arena and connecting every layer. In particular they do
not encode finite-field nim arithmetic, construct the standard Witt basis,
instantiate its concrete matrix coefficients, or build the compiled arena as a
second explicit move-graph datatype. `TranscriptStable`, `twist`, and `observe`
are abstract assumptions in Lean; their weighted-arena instantiation is also
part of the paper's synthesis.
