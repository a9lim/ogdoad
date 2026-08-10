# OPEN: Current Research Docket

This ledger contains only unsolved mathematical questions. Solved research
questions and their exact theorem boundaries are indexed in
[`CLOSED.md`](CLOSED.md); implementation milestones remain in
[`DONE.md`](DONE.md). Work that does not require new mathematics belongs in
[`COMPLETENESS.md`](COMPLETENESS.md) or [`CONTINUATIONS.md`](CONTINUATIONS.md).

Three research problems are live:

| problem | present reduction | authoritative paper |
|---|---|---|
| arbitrary-graph FIFO linking | a causal affine-contraction problem in the edge space of a complete graph | [`linking_affine.tex`](../writeups/linking_affine.tex) |
| Brown four-outcome internalization | turn the canonical binary pair `(ell,Q)` into one intrinsic four-class game outcome | [`brown_game_semantics.tex`](../writeups/brown_game_semantics.tex) |
| finite excess in transfinite nim multiplication | prove the universal `0/1/4` rule through four exact order-theoretic arms | [`excess.tex`](../writeups/excess.tex) |

The evidence vocabulary is fixed throughout this file:

- **proved** means a proof appears in a cited paper, Lean module, or standard
  external theorem;
- **certified** means exact finite computation with locally checkable arithmetic
  inputs;
- **source-pinned** means an external table or computation is reproduced and
  identified but not independently proved here;
- **consistent** means that every tested case agrees while some factorization,
  primality certificate, or level remains incomplete.

Finite verification is never promoted to a universal theorem. A Lean
proposition that states a conjecture is likewise not a proof of that
conjecture.

## 1. Arbitrary-graph FIFO linking

### Problem

Let `G` be a finite simple graph on real vertices together with one isolated
dummy. Each vertex is opened once and later closed once. Closes occur in FIFO
order; the immediately opened or closed vertex is protected by the one-step ko
rule; a forced pass clears ko. Closing the queue front toggles the score exactly
when that vertex has odd degree in the still-untouched set.

**FIFO linking conjecture.** From the empty-queue, score-zero position, either
designated seat has a strategy forcing terminal score zero on every finite
graph with an isolated dummy.

This theorem is a strict combinatorial generalization. It is not needed for the
Gold–Arf construction: a Witt frame reduces that application to a matching plus
isolates, and the matching theorem is already proved in every dimension.

### Exact affine formulation

For a complete legal history `h`, let `D(h)` be its disjointness vector in the
`F_2` edge space of the complete graph on the real vertices. Pairing `D(h)` with
the adjacency vector of a graph gives the terminal flip score of `h` on that
graph.

Fix a deterministic attacker strategy `S`, and let `H_S` be the compatible
terminal histories. Finite-field separation gives the exact equivalence

```text
S is harmless on every graph  <=>  0 lies in Aff{D(h) : h in H_S}.
```

Equivalently, the defender must construct an odd formal response flow whose
terminal edge moment is zero. At a queue front `f`, the canonical quotient

```text
T_f(z)_ij = z_ij + z_fi + z_fj
```

splits the current edge space into the cut star at `f` and the smaller edge
space after deleting `f`. In simplicial language, `T_f(z)_ij=(delta z)_fij`;
successive front gauges absorb after the corresponding deletions. The theorem
is therefore a strategy-relative contraction across the FIFO cut filtration,
not a scalar parity identity.

### Proved structure

- The transition system terminates, has no nonterminal stuck state, and is
  finitely determined. `formal/Ogdoad/Fifo.lean` proves the dual even/odd
  strategy semantics, queue invariants, drain identities, the singleton tail,
  and the edgeless base case.
- A close-first attacker cannot change the score from any coherent, ko-clear
  defender checkpoint with nonempty queue. A stronger prefix-safe
  normalization is false; earlier odd-close siblings must be coupled.
- Matching graphs are solved for both seats, without a dummy.
  `formal/Ogdoad/FifoMatching.lean` proves the rank-inductive strategy used by
  the Gold–Arf paper.
- Graphs whose vertices admit a pairing with even edge parity between every two
  cells are solved by mate mirroring. This parity-cell theorem strictly extends
  the twin-pair case but is not universal.
- The initial cut moment contracts affinely, and a two-bit
  `(degree parity, odd-neighbour parity)` handshake controls the next FIFO cell.
  Neither invariant propagates through arbitrary later attacker pruning.
- In the Eulerian quotient, harmlessness is exactly intersection of the
  response affine space with the cut space. Eulerian graphs carry an odd-triple
  curvature `3`-oik, but the attacker can prune its ordinary wall pairing.
- Complete schedules admit an exact permutation-threshold normal form, and
  pass-free histories admit a response-factor normal form. Both expose the
  same missing causal extension rather than proving it.
- Exact minimax verifies the conjecture for every graph isomorphism class
  through eight real vertices plus the isolated dummy, for either designated
  seat. This is certified finite evidence only.

### Sharp obstructions to local proofs

The following stronger statements are false and must not reappear as proof
premises:

- a childwise common affine coset contracts at each defender node;
- a bounded-support odd certificate exists uniformly;
- one cap child plus one ancestor sibling always supplies a cancellation;
- degree, two-bit colour, queue charge, or a bounded number of transported
  defects is a sufficient Markov state;
- zero-normalized play for one graph is a graph-independent affine carrier for
  a second graph;
- each opening permutation can be contracted independently;
- symplectic rank or Witt class determines the FIFO outcome.

The paper gives explicit finite witnesses for each failure. These witnesses do
not refute the FIFO linking conjecture; they locate the information that a
proof must retain.

### Remaining theorem

For every deterministic attacker strategy, construct a strategy-compatible
odd response chain with zero terminal edge moment. An equivalent Eulerian form
asks for a chain with cut-valued terminal moment. The construction must couple
several sibling images across successive front levels while preserving odd
augmentation. In the response-factor language, it is a **causal
charge-balanced factor-extension theorem** that may carry an unmatched dummy
endpoint until a legal phase pivot absorbs it.

This is the only missing mathematical step. More exhaustive enumeration or a
new scalar queue invariant would be useful for falsification, but neither is
the stated target.

### Verification surfaces

- [`writeups/linking_affine.tex`](../writeups/linking_affine.tex)
- [`formal/Ogdoad/Fifo.lean`](../formal/Ogdoad/Fifo.lean)
- [`formal/Ogdoad/FifoMatching.lean`](../formal/Ogdoad/FifoMatching.lean)
- [`experiments/linking_game.py`](../experiments/linking_game.py)

## 2. Brown four-outcome internalization

### Completed algebraic reduction

Every Brown refinement

```text
q(x+y) = q(x) + q(y) + 2 b(x,y),    q : V -> Z/4
```

has the unique canonical split

```text
ell(x) = q(x) mod 2,
q(x)   = lift(ell(x)) + 2 Q(x),
B_Q    = b + ell tensor ell.
```

Here `ell` is linear and `Q` is an ordinary `F_2`-quadratic form. The four
residues are the synchronized pair `(ell,Q)`, and their phase is the correlated
Walsh combination

```text
G(q) = ((1+i)/2) W(Q) + ((1-i)/2) W(Q+ell).
```

The linear bit has a standard local XOR realization. The weighted-source
Witt–FIFO theorem realizes the quadratic bit as ordinary normal play. Thus a
synchronized pair of binary channels already computes every Brown label.

Two global obstructions are also proved. Ambient-coherent Brown data on the
additive group of all short games vanish because that group is two-divisible;
and a bare `Z/4 -> Z/8 -> Z/2` central extension does not select the Brown
phase without a section. `formal/Ogdoad/BrownGame.lean` checks the split,
converse, divisibility implication, and sharp cyclic model.

### Open semantic problem

Construct, or rule out under an explicit naturality contract, a **single fixed
game family** whose intrinsic four-way outcome realizes `q(x)` on every finite
Brown space. The target must specify the outcome convention—for example the
four partizan outcome classes—and must not use:

- an external synchronized product of two already evaluated games;
- terminal relabelling by a direct call to `q`, `ell`, or `Q`;
- a presentation-dependent Brown table that changes under ambient inclusion.

A satisfactory construction must retain the correlation between `Q` and
`Q+ell`, not merely reproduce their marginal zero counts. A no-go theorem must
state the structural axioms it excludes. This question is semantic: it neither
reopens the binary Gold–Arf theorem nor asks for a nonzero Brown colour on all
short-game values, which is impossible.

### Verification surfaces

- [`writeups/brown_game_semantics.tex`](../writeups/brown_game_semantics.tex)
- [`writeups/goldarf.tex`](../writeups/goldarf.tex)
- [`formal/Ogdoad/BrownGame.lean`](../formal/Ogdoad/BrownGame.lean)
- [`formal/Ogdoad/GoldSemantics.lean`](../formal/Ogdoad/GoldSemantics.lean)

## 3. Finite excess in transfinite nim multiplication

### Problem

For an odd prime `p`, Conway's Kummer carry below
`omega^(omega^omega)` has the form

```text
alpha_p = kappa_f(p) + m_p,    f(p) = ord_p(2),
```

where `m_p` is Lenstra's finite excess. The source-pinned table is consistent
with

```text
m_p = 0  when Q(f(p)) is not a singleton odd prime-power,
m_p = 4  when f(p) = 2 * 3^k with k >= 1,
m_p = 1  otherwise.
```

This universal `0/1/4` rule is open.

### Exact reduction

[`excess.tex`](../writeups/excess.tex) proves that the rule is equivalent to
four universal order assertions:

| arm | assertion | exact remaining target |
|---|---|---|
| `Z` | the structural norm of `kappa_h` generates the primitive-support quotient for every non-ordinary component set | exclude the selected reverse-Dickson divisor in the Conway–Fermat chain, prove generation for composite two-spine quotients, and control the general synchronized phase |
| `O` | the selected projective class of `kappa_(r^a)+1` has full primary order for every odd `r != 3` | prove selected binary-section nondivisibility at every remaining small primary factor |
| `C` | `gamma_k = zeta + zeta^(-1)` is primitive in `F_(2^(3^k))` | exclude the extremal prescribed-trace value at the recursively selected Conway fibre |
| `D` | `Psi_k` divides `ord(M_k)`, where `Psi_k = Phi_(2*3^k)(2)/3` | exclude the selected reciprocal cubic from the relevant Dickson factor list; equivalently prove the Capelli/antiunit condition `D'_k` |

The equivalence is a theorem. None of the four assertions is proved
universally.

### Shared power criterion

If a candidate translate `beta = kappa_f(p)+m` lies in `F_(2^E)`, then

```text
beta has no p-th root  <=>  beta^((2^E-1)/p) != 1.
```

Equivalently, `ord(beta)` contains the full `p`-primary part of `2^E-1`.
Checking only whether `p` divides `ord(beta)` is valid only when
`v_p(2^E-1)=1`; in general

```text
v_p(2^E-1) = v_p(2^f(p)-1) + v_p(E/f(p)).
```

This distinction is load-bearing at Wieferich primes and whenever `p` divides
the relative extension degree.

### Boundedness coordinate

Let `C_a = F_(2^(2^a))` be the complete finite Conway subfield at level `a`.
The paper proves

```text
sup_p m_p < infinity
  <=>
there is an a such that every p has a c in C_a
with kappa_f(p)+c not a p-th power.
```

Thus boundedness is uniform nonsaturation of one finite-Conway-subfield affine
line, not maximal order of the particular `0/1/4` candidates. On the
exceptional arm, the selected character sum gives the unconditional effective
bound `m_ell < 16 * 3^(4k)`. This grows with `k` and therefore does not prove
absolute boundedness.

### Established results by arm

- **`Z`.** Separate component norms lose a synchronized Frobenius phase. The
  paper retains that phase, gives an exact two-component resultant, proves
  primitive support and a cyclic-variation lower bound for the power-of-two
  two-spine family, and closes `h=12,24`. The singleton-even chain is exactly
  the Conway–Fermat quotient-order problem. Trace, norm, degree, fibotomic
  support, lower ancestry, and generic Kummer-cover symmetries are all proved
  insufficient without evaluating the selected factor.
- **`O`.** The selected class is a relative Hilbert–90 unit. An
  absolute-Frobenius signed-ball argument proves every primary factor above an
  explicit threshold. Mixed Jacobi sums and binary sections isolate the
  remaining selected coordinate exactly. Tower-faithful countermodels show
  that generic ancestry and bookkeeping do not determine it.
- **`C`.** The first three levels are proved analytically. Norm recursion,
  cyclic parity, primitive-CRT isolation, mixed Jacobi expansion,
  Singer–Wendt factorization, `S_3` descent, and the prescribed-trace character
  formulation all agree on one selected top-component test. Both distinguished
  period coordinates have absolute trace zero and are not normal, so
  primitive-normal and normal-Gaussian-period theorems do not apply. Generic
  Wendt factors and other trace fibres attain every structural value used by
  the obvious bounds.
- **`D`.** The corrected norm, current-factor formulation, quadratic-twist
  antiunit, mixed-Jacobi and binary-parity criteria, reciprocal sextic, and
  Dickson factorization reduce the arm to one selected cubic. The ambient
  Dickson polynomial contains many cubics with the same depressed equation;
  an exact nonselected countermodel also matches the selected two-trace
  fingerprint. The line criterion gives the effective polynomial bound above
  but not the required fixed window.

### Evidence boundary

- All 126 OEIS A380496 rows for odd primes `3 <= p <= 709` are vendored and
  diffed. These integer excesses are source-pinned; the next unsupported carry
  is `alpha_719`.
- The extended values at the two known base-2 Wieferich primes are
  source-pinned external computations, not local certificates.
- `C_1,C_2,C_3` are proved; `C_4,C_5` are certified; `C_6` is
  source-assisted; `C_7,C_8` are consistent with incomplete factorizations.
- The exceptional levels `k=2,...,5` are certified; `k=6` is source-assisted;
  `k=7,8` are consistent with incomplete factorizations.
- `formal/Ogdoad/Excess.lean` proves the reduction spine and finite arithmetic
  inputs stated in its README. Its `DPrimeTarget` is the open proposition, not
  a theorem.

### Verification surfaces

- [`writeups/excess.tex`](../writeups/excess.tex)
- [`formal/Ogdoad/Excess.lean`](../formal/Ogdoad/Excess.lean)
- [`experiments/ordinal_excess_probe.py`](../experiments/ordinal_excess_probe.py)
- [`experiments/cyclotomic_3k_family.py`](../experiments/cyclotomic_3k_family.py)
- [`experiments/exception_column_m4.py`](../experiments/exception_column_m4.py)
- [`src/scalar/big/ordinal/tower.rs`](../src/scalar/big/ordinal/tower.rs)
- [`src/scalar/big/ordinal/b380496.txt`](../src/scalar/big/ordinal/b380496.txt)

## References

- Berlekamp, Conway, and Guy, *Winning Ways for Your Mathematical Plays*.
- Brown, “Generalizations of the Kervaire invariant,” *Annals of Mathematics*
  95 (1972), 368–383.
- Conway, *On Numbers and Games*.
- DiMuro, “On `On_p`,” arXiv:1108.0962.
- Lenstra, “On the algebraic closure of two,” *Indagationes Mathematicae* 39
  (1977), 389–396.
- Moews, “The Abstract Structure of the Group of Games,” in *More Games of No
  Chance*, MSRI Publications 42 (2002), 49–58.
- Wall, “Quadratic forms on finite groups, and related topics,” *Topology* 2
  (1963), 281–298.
