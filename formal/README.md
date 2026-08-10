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
  does not determine the phase.

The external instantiation remains source-pinned: Moews proves the additive
short-game group is a direct sum of copies of `Z[1/2]` and `Z[1/2]/Z`, hence
is two-divisible.  The Lean file proves the full implication from that abstract
divisibility hypothesis but does not encode short games or Moews's theorem.

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

[`Ogdoad/Excess.lean`](Ogdoad/Excess.lean) formalizes the theorem-level spine
of the exceptional `2·3^k` column:

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
  including the distinguished lift `an - 1`; and
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
- strict rank descent, absence of nonterminal stuck states, and preservation of
  the queue/untouched invariant;
- an explicit existential/universal finite strategy tree;
- its explicit odd-forcing dual, kernel-checked finite determinacy and
  incompatibility (`EvenWins` iff no `OddWins` counterstrategy);
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
- the explicit hyperbolic-plus-radical graph and induced-subgraph lemmas connect
  a public Witt frame and every loaded input support to that theorem.

This does **not** prove the arbitrary-graph isolated-dummy conjecture.  It
shows instead that the conjecture is an unnecessary strengthening for Gold.

## Gold normal-play semantics

[`Ogdoad/GoldMatchingAlgebra.lean`](Ogdoad/GoldMatchingAlgebra.lean)
kernel-checks the quadratic expansion in a supplied adapted basis: selected
basis diagonals plus the parity of hyperbolic pairs whose two coordinates are
active. It includes the exact split in which each adapted diagonal is a public
polar correction plus a transported original-frame linear source; this is the
step that rules out a hidden dense refinement query after the Witt change.
The standard existence of a symplectic-plus-radical basis for a finite
alternating form remains an ordinary linear-algebra input; the file proves the
entire identity once such a basis is supplied.

[`Ogdoad/GoldSemantics.lean`](Ogdoad/GoldSemantics.lean) proves the semantic
compiler independently of the FIFO mechanism:

- any finite Boolean-payoff move tree becomes an ordinary normal-play tree by
  retaining its moves and adding one terminal claim move exactly when the
  current seat is designated by the charge;
- backward induction proves winner equivalence at every subtree and phase, so
  stance one has a P-root exactly when the forced charge is zero;
- a phase-free terminal gadget cannot preserve seat identity across both path
  parities;
- outcome-dominance pruning makes mixed-successor criticality impossible in
  every two-class game; and
- the two-action edge fork has complementary values and its optimum swaps when
  one unread refinement source is toggled.

Together these three files kernel-check the load-bearing game theorem,
quadratic decomposition, and payoff-to-normal-play bridge of
`writeups/goldarf.tex`.  They do not encode finite-field nim arithmetic or the
standard Witt-basis existence theorem.
