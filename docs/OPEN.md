# OPEN: Current Research Docket

This ledger contains only unsolved mathematical questions. Solved research
questions and their exact theorem boundaries are indexed in
[`CLOSED.md`](CLOSED.md); implementation milestones remain in
[`DONE.md`](DONE.md). Work that does not require new mathematics belongs in
[`COMPLETENESS.md`](COMPLETENESS.md) or [`CONTINUATIONS.md`](CONTINUATIONS.md).

Two research problems are live:

| problem | present reduction | authoritative paper |
|---|---|---|
| arbitrary-graph FIFO linking | a causal affine-contraction problem in the edge space of a complete graph | [`linking_affine.tex`](../writeups/linking_affine.tex) |
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
- Close-first play contracts completely from either seat. The conditioned
  tail, its whole-live-face strengthening, and the stopped defender-first
  empty-root theorem are proved; their load-bearing strategy semantics and
  induction kernels are checked in `formal/Ogdoad/Fifo.lean`.
- Matching graphs are solved for both seats, without a dummy.
  `formal/Ogdoad/FifoMatching.lean` proves the rank-inductive strategy used by
  the Gold–Arf paper.
- Graphs whose vertices admit a pairing with even edge parity between every two
  cells are solved by mate mirroring. This parity-cell theorem strictly extends
  the twin-pair case but is not universal.
- The initial cut moment contracts affinely, and a two-bit
  `(degree parity, odd-neighbour parity)` handshake controls the next FIFO cell.
  Neither invariant propagates through arbitrary later attacker pruning.
- The complete pair-response potential is now kernel-checked.  For a
  well-formed state, after `OPEN x` the sum of the queue cuts over every second
  `OPEN y` is `|U|` copies of the post-`x` queue cut.  Thus an even untouched
  set gives an odd zero-sum OPEN fan; for odd `|U|` and a pre-existing queue,
  adjoining the translated CLOSE reply gives the same contraction.  The sole
  local exception is the nontrivial odd empty-queue ko fan.
- In the Eulerian quotient, harmlessness is exactly intersection of the
  response affine space with the cut space. Eulerian graphs carry an odd-triple
  curvature `3`-oik, but the attacker can prune its ordinary wall pairing.
- Complete schedules admit an exact permutation-threshold normal form, and
  pass-free histories admit a response-factor normal form. Both expose the
  same missing causal extension rather than proving it.
- The CLOSE-first attacker is contracted for both seats. Lean now rules out a
  CLOSE-first terminal-score-one strategy at the isolated-dummy root and proves
  that every hypothetical odd strategy contains a genuine clear-node OPEN
  deviation. The same module checks the live-star potential and the
  same-degree/balanced-front first-spoiler step of the least-root corridor.
- Every fixed-front attacker phase has zero in the affine hull of its remainder
  vectors, but the corresponding distinguished-leaf statement is false. The
  exact replacement is a relative-spine quotient together with a finite
  one-front-offset ladder whose holonomy is an explicit sum of token-opening
  edges.
- Minimum extraction inside an odd strategy tree produces a charged close with
  a translated neutral tail. The full family of punctured singleton tails
  makes the even untouched remainder Eulerian and excludes the
  zero-charge/even-untouched predecessor branch. At the remaining odd-odd spike,
  relative live-star incidence forces earlier siblings to carry the selected
  front star, leaving a canonical Schur class supported strictly away from that
  front. Exact response trees show that neither descendants alone nor the next
  two-bit coefficient kills this class.
- On the full two-sheet positional winning region, a minimum-rank flexible
  physical state is attacker-controlled and selects different moves on the two
  sheets. Any reconvergent CLOSE/OPEN fork there must have odd edge curvature.
  Thus a score-forgotten no-retraction proof is invalid: the remaining coupled
  cases are a neighbour CLOSE/OPEN fork, two distinct OPENs, and the singleton
  ko wall.
- On the unpruned force sets, a globally rank-minimal state at which one
  physical player can force both bits has an exact form: one untouched real
  vertex `z`, a ko-clear front `f` with `fz` an edge, and a queue tail
  nonadjacent to `z`.  Every strict descendant is cold zero for both players
  and every strict legal edge is neutral.  This minimum-hot singleton-wall
  theorem is now kernel-checked in `FifoNormalization.lean`.  It classifies
  the primitive wall but does not make it strategy-reachable from a bad root;
  the unpruned global minimum and the minimum dual bit inside one fixed pruned
  strategy tree are different quantifiers.
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
- an unweighted parity, cut-space, or four-strategy rectangle of minimum-hot
  wall labels contracts the ancestry.  Exact six-real witnesses leave a
  single non-cut edge or an order-dependent critical-tree moment.

The paper gives explicit finite witnesses for each failure. These witnesses do
not refute the FIFO linking conjecture; they locate the information that a
proof must retain.

### Remaining theorem

For every deterministic attacker strategy, construct a strategy-compatible
odd response chain with zero terminal edge moment. An equivalent Eulerian form
asks for a chain with cut-valued terminal moment. After the proved predecessor
reductions, the unresolved step is to kill the odd-spike/B-prime Schur class by
coupling earlier siblings with descendant continuation cosets. In the
response-factor language, this is a **causal charge-balanced factor-extension
theorem** simultaneously cancelling cut, continuation, pruning-frontier, and
frozen ko-wall moments while preserving odd augmentation.

The latest local descent makes the endpoint especially small.  A primitive
hot leaf is the last-untouched edge switch `C_f` versus `O_z`; tracing a
strategy-relevant occurrence backward yields either an odd-odd CLOSE spike or
the protected `B'` seed whose remaining live graph is the three-vertex star.
Busy-block analysis transports the latter through pendant odd closes but does
not kill an arbitrary chain.  The paper now contracts a single
pendant-to-star step by an explicit arbitrary-policy sibling strategy; a
longer broom can still rotate into the online draft-and-stop endpoint.  The
first unresolved cancellation lies in the earlier universal ko fan choosing
the dummy versus real replies.  Coupling that whole fan, not the terminal wall
or one busy block, is the remaining proof obligation.  The new complete-fan
identity makes its quotient form exact: outside the all-odd real-degree locus
the canonical immediate representatives already admit an odd zero selection;
on the all-odd locus the needed correction belongs to the sum of the child
continuation spaces iff the universal-full-row/common-coset obstruction
vanishes.  Lifting the canonical selection through attacker-pruned child
cosets, even outside that locus, is still the causal factor-extension step.

This is the only missing mathematical step. More exhaustive enumeration or a
new scalar queue invariant would be useful for falsification, but neither is
the stated target.

### Verification surfaces

- [`writeups/linking_affine.tex`](../writeups/linking_affine.tex)
- [`formal/Ogdoad/Fifo.lean`](../formal/Ogdoad/Fifo.lean)
- [`formal/Ogdoad/FifoNormalization.lean`](../formal/Ogdoad/FifoNormalization.lean)
- [`formal/Ogdoad/FifoMatching.lean`](../formal/Ogdoad/FifoMatching.lean)
- [`experiments/linking_game.py`](../experiments/linking_game.py)

## 2. Finite excess in transfinite nim multiplication

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
| `Z` | the structural norm of `kappa_h` generates the primitive-support quotient for every non-ordinary component set | in the singleton-even chain prove the iterated quadratic-norm terminal bit is `1`; also prove generation for composite two-spine quotients and control the general synchronized phase |
| `O` | the selected projective class of `kappa_(r^a)+1` has full primary order for every odd `r != 3` | exclude the selected full-conductor factor from the reduced reciprocal divisor, equivalently force a nonzero terminal selected section along every all-odd singleton dependency chain, stopping at each declared quadratic or synchronized boundary |
| `C` | `gamma_k = zeta + zeta^(-1)` is primitive in `F_(2^(3^k))` | prove the fixed cubic-norm terminal bit of `hatDelta_(N/ell)` is `1`, equivalently `Omega_(k,ell) != 1`, for every current prime |
| `D` | `Psi_k` divides `ord(M_k)`, where `Psi_k = Phi_(2*3^k)(2)/3` | prove the selected Dickson critical value at the reconstructed trace-one scalar is nonzero, equivalently the actual Artin--Schreier root is not a current primary power (`D'_k`) |

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
  the Conway–Fermat quotient-order problem. An exact selected-factor harness
  now reconstructs the literal Conway resultant rather than substituting a
  generic tower element. It finds nonzero Fibonacci residues at every
  published prime factor from `F_12` through `F_18` (six, four, one, three,
  two, two, and two factors respectively). These are falsification results only:
  the exact residual cofactors `C1133`, `C2391`, `C4880`, `C9808`, `C19694`,
  `C39395`, and `C78884` are proved composite but remain unfactored, so no level nor the
  all-level conjecture is certified. The optional FLINT backend agrees
  bit-for-bit with the dependency-free reducer at the orientation gate, and
  the per-factor hashes are only reproducibility fingerprints. In that chain, absolute
  trace is exactly the top binary coordinate, the selected ancestry is the least
  trace-one nimber, and failure is equivalent to a centered reverse-Dickson
  divisor of the trace-zero linearized polynomial. Adapted-basis countermodels
  realize this entire additive/Moore pattern while changing the multiplicative
  ancestry, so the special Fermat multiplication remains essential. Trace,
  norm, degree, fibotomic support, lower ancestry, and generic Kummer-cover
  symmetries are all proved insufficient without evaluating the selected
  factor. The exact one-step countermodel is stronger than a predecessor-only
  example: its degree-32 successor has order `(2^32-1)/3`, hence carries every
  preceding Fermat factor, while its following norm-one quotient still loses
  the factor `641`. The exact quadratic-remainder descent now pushes any
  selected divisibility through every actual Conway resultant edge to a binary
  tree at `A_(-1)=Y+1`; this prevents a wrong predecessor from certifying the
  actual path but leaves a leaf nonvanishing equivalent to the original
  selected Conway--Fermat obstruction. Taking the quadratic resultant instead
  compresses that whole binary tree to one iterated norm bit. Its first layer
  satisfies an explicit order-four recurrence, but the terminal bit is `1`
  exactly when the original selected Fibonacci value is nonzero, so this is a
  lossless normal form rather than a closure. As a word in the exponent, that
  terminal bit is exactly the zero-at-multiples indicator for `delta_n`; its
  least period, linear complexity plus one, and minimal binary-automaton state
  count are all `delta_n`. The unique lower `ell`-th root in the Dickson
  obstruction is now choice-free: with `d=(q+1)/ell`, it is
  `(a_(n-1)^d)^(q/2)`. This removes an auxiliary root but leaves the same
  selected Dickson nonvanishing. Thus even the automatic-sequence complexity
  is the unknown quotient order itself. A new trailing-zero compression makes
  the first continued-fraction obstruction explicit: if
  `d = 1 + 2^t h`, then
  `S_d = S_(h+1)^(2^t) + T_t S_h^(2^t)`, and hypothetical failure at a
  Fermat divisor forces `S_(h+1)/S_h = 1 + T_(2^n-t)`. This too is exact but
  circular: Binet and Cassini reduce it to the automatic congruence
  `h = 2^(2^n-t) (mod delta_n)` on every order-`delta_n` fibotomic stratum.
  Descending that forced ratio through the actual tower sends each relative
  trace to the lower level's unconditional full-Fermat ratio, so full trace
  ancestry gives no contradiction. In fact the full additive attack is now
  exact: under failure, translating the selected `ell`-root polynomial by
  every trace-zero element multiplies to the `ell`-th power of the complete
  trace-one polynomial. Every trace-one point is covered exactly `ell` times,
  so additive averaging is saturated rather than merely too weak. The
  classical binary `Q`-transform
  identifies the minimal polynomial of `(c_n+1)/c_n` exactly and proves its
  degree and self-reciprocal irreducibility, but every nontrivial divisor of
  `F_n` satisfies the same order-degree condition. The literal-top-bit
  multiplication matrix is a nested `2 by 2` Fibonacci companion block:
  its first projective return is exactly `delta_n`, while its characteristic
  polynomial is exactly the existing Conway resultant. Thus neither a hidden
  Singer conjugacy nor a characteristic-polynomial recursion is an independent
  maximality proof. The selected Kummer symbol now has an exact cyclotomic
  lift: after choosing an independent generator `omega` of the norm-one group
  and writing `w_n=omega^(r_n)`, its `ell`-th residue symbol at the associated
  prime above two is exactly `omega^(r_n*F_n/ell)`. Thus the conjecture is
  precisely `ell` not dividing the Conway-selected discrete logarithm `r_n`.
  The unit's minimal odd cyclotomic conductor is exactly
  `delta_n=F_n/gcd(F_n,r_n)`, so proving full conductor is equivalent to
  maximality rather than an independent route.
  Choosing the prime by sending a root of unity directly to `w_n` would assume
  maximality; local logarithms, principal-ideal/Stickelberger data, and
  circular-unit distribution do not determine the remaining residue of `r_n`.
  The canonical characteristic-zero Hensel lift makes this failure exact:
  two is inert and unramified through the lifted Conway chain, three is
  totally ramified, and the lifted norm-one ratio is a global unit already an
  `ell`-th power at three. Yet the prime above two splits into a full
  cyclotomic torsor after adjoining `mu_ell`; its local Hilbert symbols are
  `H^a` and their product is one for every `H`. Unweighted global reciprocity
  therefore leaves the selected symbol completely free. The exact weighted
  product formula says that a principal selector `x` would recover
  `H^(sum_a a*v_(q_a)(x))` from its local symbols above `ell`. But every
  element from either unmixed factor has weighted exponent zero: on the
  cyclotomic side `-1` lies in the decomposition group of two, so the `a` and
  `-a` valuation contributions cancel. This rules out ordinary
  Gauss/Jacobi/Stickelberger principalizers. The exact semiprimitive Gauss
  calculation is sharper: twisting the additive character by the complete
  Conway unit gives `G_a(w_n)=q*H^(-a)`, and the labelled periods have one
  large entry precisely at label `H^(-1)` and one common small value
  elsewhere. Thus their unordered multiset, every symmetric function,
  absolute values, principal ideals, and Stickelberger data are independent
  of `H`; ordering the exceptional label merely reads the original selected
  phase. Lower multiplicative characters pulled back through the norm either
  cancel that phase in weight-zero Jacobi quotients or retain exactly the same
  unknown. The natural mixed element
  `W_n^(F_n/ell)-zeta_ell` has support above two exactly when
  `w_n^(F_n/ell) != 1`, so even its existence as a selector is the original
  target. That circularity can now be removed: affine interpolation writes
  the selected residue `c_n=u+v*eta` over the lower residue field and lifts
  `x=C_n-U-V*zeta_ell` so that it has a simple zero at the distinguished
  prime above two and no zero at any conjugate. Simultaneous approximation
  also kills every pairing above `ell`, independently of the unknown symbol.
  Global reciprocity therefore gives the exact noncircular formula
  `H=T_R^(-1)`, where `T_R` is the oriented tame residue over the remaining
  divisor of `x`. Its relative norm is the explicit scalar
  `A_(n-1)+R+R^2`, but the two split orientations carry reciprocal values of
  `W_n`; the ordinary norm/resultant erases precisely the half selected by
  `x`. More strongly, this norm has valuation vector `(1,0,...,0)` on the
  `(ell-1)/2` primes of the cyclotomic layer above two. Its Galois stabilizer
  is therefore contained in `{+1,-1}`, so it has lower-field degree at least
  `(ell-1)/2` and cannot descend to any ancestral scalar. Even without the
  selector congruences, the exact norm-two equation
  `A_(n-1)+R+R^2=2` has no solution by the unique-quadratic-subfield and
  two-adic square-class comparison, while a general `{2,ell}`-unit value
  remains a genuine constrained S-unit problem.
  Classical power reciprocity now evaluates that half-resultant exactly:
  `T_R=(R/r)^2` and `H=(R/r)^(-2)`, with `R mod r=c_n`. Every lower
  ancestral unit cancels separately. Thus the affine selector is a
  noncircular principal representative but the resulting Jacobi formula is
  an exact normal form for the original selected Conway symbol, not a new
  nonvanishing invariant. The local oriented residue cover is rational,
  `r=-1/(1+z^ell)`, so its shape alone supplies no positive-genus Weil
  obstruction. Nor is the affine form an extra restriction at the
  ray-class level: every nonsymmetric principal element can be rescaled by
  an involution-fixed scalar into `C_n-R`; the added symmetric fractional
  divisor has reciprocal orientations and zero character. This normalization
  need not preserve integrality or local support, so it sharpens the identity
  without solving its nonvanishing.
  At an unramified/étale prime above `ell`, the first ramified local
  coefficient is now explicit: it is a recursively selected second-Witt
  polynomial built from the Teichmuller defects
  `D(c)=([c]+1-[c+1])/ell`. Its nonvanishing proves that the local Kummer
  character is nontrivial, but does not evaluate that character at the prime
  above two; in fact every local pairing of two elements descended from
  `K_n` is individually trivial at every `ell`-adic place by
  decomposition-stabilizer symmetry. A last simple ramified derivative stage
  is now controlled too: in the discriminant uniformizer its leading unit
  coefficient starts at `-1` and propagates by the exact factors
  `(3*c_j+2)/(2*c_j+1)`. Unless one of those branch-sensitive numerators
  vanishes, `W_n` is locally nontrivial; a kernel-checked equivariant
  two-coordinate toy model shows that the displayed local nonvanishing and
  orbit relations still do not determine the named
  prime-above-two value. A multiple discriminant zero, or a vanished
  `3*c_j+2`, requires a higher-filtration calculation. Globally,
  if `theta^ell=W_n`, the missing value is exactly
  `chi_W([q_1])=H` for the Artin character of `M(theta)/M`. Fixed/ambiguous
  classes and inverse pairs are annihilated, while equivariance permits both
  `H=1` and every `H!=1`; reflection and Chevalley--Gras formulas compare
  eigenspace ranks or count fixed ray classes but do not locate this named
  class. What remains is therefore one genuinely mixed Artin pairing; even
  after proving the ray character nontrivial, its value at the named class is
  still required, and classical cyclotomic reciprocity does not supply it.
  Equivalently, failure says that `2` is a global norm from the cyclic Kummer
  extension `M(W_n^(1/ell))/M`. If `y` is such a norm witness, then
  `Norm(y^P)=2^aug(P)` for every integral group-ring operation `P` in the
  cyclic Kummer direction. These operations retain a constant valuation
  vector across the primes over two and cannot produce the affine selector's
  one-point vector without the missing weighted `Delta`-operation. If `W_n`
  is not already a global `ell`-th power, its lower-field Galois closure is
  dihedral, and every abelian quotient
  of that specific extension kills the selected translation Frobenius. Thus no
  abelian quotient or descent factoring through that dihedral extension can
  decide the norm equation. There is, however, an exact nonabelian descent:
  if `L` is the degree-`ell` reflection fixed field, then
  `H=1 iff 2 in Norm(L/M_0)`. A cyclic witness `y` descends explicitly as
  `((y*s(y))^((ell+1)/2))/2`; this retains rather than removes the dihedral
  orientation. Explicitly `L=M_0(theta+theta^(-1))`, with defining Dickson
  equation `D^cl_ell(t)=W_n+W_n^(-1)`, where
  `D^cl_0=2`, `D^cl_1=T`, and `D^cl_(m+2)=T*D^cl_(m+1)-D^cl_m`.
  The symmetrization commutes with every completion. Combined with the
  cyclic Hasse norm theorem upstairs, it proves the Hasse norm principle for
  `L/M_0`: a base element is a global norm exactly when it is a local norm
  everywhere. At the selected prime over two, `H=1` makes `L` split
  completely, while `H!=1` makes the local factor unramified of degree
  `ell`; then norm valuations are divisible by `ell` and cannot contain the
  valuation-one element `2`. All local conditions away from the primes above
  two are automatic. The odd-dihedral norm-one torus also has weak approximation,
  so finitely many additional local open conditions on a hypothetical
  witness add no obstruction. Its classical Dickson discriminant is already
  a square in `M_0`, so discriminant parity and the quadratic resolvent cannot
  distinguish complete splitting from the nontrivial `ell`-cycle either.
  The local analytic package is equally sharp and equally circular: the
  reflection Euler factor is `(1-T)^(-ell)` on failure and
  `(1-T^ell)^(-1)` on success, so it sees exactly the original split/inert
  bit. Both cases are unramified, however, and with the conductor-zero
  additive character every Artin conductor exponent is zero and every local
  epsilon/root-number factor is one. Thus conductor, discriminant, epsilon
  factor, and root number are blind; the only analytic datum that sees the
  target is the named Euler factor already containing it.
  The complete global Artin package does not restore the missing bit. For the
  augmentation representation of the odd-dihedral reflection field,
  `L(s,Pi_0)=zeta_L(s)/zeta_(M_0)(s)` and the completed quotient has forced
  sign `+1`. Its conductor is the relative discriminant; at every ramified
  non-`ell` place the local induced representation is the direct sum of the
  trivial and ramified quadratic characters, and the product
  of the remaining `ell`-adic root numbers is forced to one. Multiplying all
  Euler factors above two distinguishes split from inert only because that
  product already contains `H`: it is `(1-T)^(-m*(ell-1))` on failure and
  `((1-T)/(1-T^ell))^m` on success. Thus a functional equation, conductor,
  or ramified Gauss package cannot reconstruct the named unramified factor.
  Its defining coefficient is already lower-ancestral:
  `W_n+W_n^(-1)=A_(n-1)^(-1)-2`, with
  `(W_n+W_n^(-1))^2-4=D_(n-1)/A_(n-1)^2`. The only selected datum is the
  factorization of this lower-defined polynomial at the named prime over two.
  Thus the reflection reformulation retains the marked
  nonabelian Frobenius but creates no new relative class-group obstruction:
  its norm equation is another exact form of the original selected local
  splitting question. In Brauer-group form all
  lower ancestral symbols
  with `2` vanish, while `beta={W_n,2}=-2*alpha` for the anti-invariant top
  class `alpha={C_n,2}`. Corestriction kills that class, so this formulation
  isolates the obstruction at the top edge but supplies no inductive
  nonvanishing.
  A complementary cross-level theorem shows that this Kummer coordinate is
  born only once. If `M=ell^e || F_n`, then the `M`-Kummer quotients vanish
  below `E_n`, are cyclic of order `M` from `E_n` onward, and every later
  inclusion is an isomorphism. Writing `kappa_j=[a_j]_M`, the exact transport
  is `kappa_j=(3/2)kappa_(j-1)`. Since `3/2` is a unit modulo `M`, success or
  failure persists unchanged through the infinite tail. At the selected
  character level this is `h_j=h_(j-1)^3`, so the actual Euler symbol is
  merely cubed at each future edge. Equivalently, for
  every `j>=n`, `A_j(X^ell)` is irreducible in the success case and splits
  into exactly `ell` full-degree factors in the failure case. Future ancestry
  therefore copies rather than constrains the missing birth coordinate. The
  universal Dickson--Conway resultant makes this closure coefficient-exact:
  each failed future Kummer lift factors into `ell` selected irreducible
  quadratics, whereas success gives one irreducible degree-`2*ell` polynomial.
  Compatible failed root towers form one `mu_ell`-torsor of parallel rays,
  transported by `zeta -> zeta^(3/2)`, rather than an accumulating branching
  tree.
  The resultant correspondence itself has rational normalization
  `Y=c^2+c`, `X=c^3+c^2` and a unique parent on trace-one irreducibles, but
  its critical portrait, degree growth, and cyclic splitting fields are
  universal. Hence its exact parent chain retains full Conway ancestry while
  supplying no shorter dynamical selector. Scheme-theoretically, the complete
  ancestry equations already present the field `E_(n-1)`: adjoining a
  fibotomic equation gives either that entire reduced Frobenius orbit or the
  unit ideal, and its multiplication determinant/resultant is exactly the
  existing terminal norm bit. Odd Fibonacci polynomials are squarefree
  (`S'_(2r+1)=S_r^2`), so local multiplicity and higher Hasse jets add no
  hidden contradiction. Proving the unit-ideal case remains literally the
  selected nondivisibility target. The natural ancestry weight filtration
  degenerates to `F_2[x_i]/(x_i^2)`, where Frobenius kills every positive
  graded class; exact quadratic-basis doubling then drops to lower grades
  with cancellable summands. Thus Newton/leading-monomial induction also
  needs new control of the full selected normal form. At a hypothetical
  first failure
  the old coefficient's
  maximal order only makes it a generator of the cube subgroup; exact Conway
  ancestry already makes that coefficient an explicit cube, and tripling on
  the fibotomic torus merely transports its cubic character to a translate-one
  character on the same stratum. The elliptic curve happens to be the good
  mod-2 reduction of `X_0(11)`, but successive Conway points are joined by an
  integral bidegree `(3,2)` fibre-product correspondence with zero elliptic/CM
  component. Its Kummer pullback transports only `c_(n-1)` and admits no
  monomial function-class relation with the new class `[c_n]`.
- **`O`.** The selected class is a relative Hilbert–90 unit. An
  absolute-Frobenius signed-ball argument proves every primary factor above an
  explicit threshold. Mixed Jacobi sums and binary sections isolate the
  remaining selected coordinate exactly. Tower-faithful countermodels show
  that generic ancestry and bookkeeping do not determine it. A fixed-translate
  countermodel now also matches full Kummer degree, all binary sections,
  norm-one reciprocity, and literal least-nonresidue labeling; it differs
  exactly in the lower ancestor's multiplicative order and cyclotomic
  conductor, isolating full Conway ancestry as indispensable. At the actual
  ordinary singleton step, even the canonical additive lower norm is
  current-Kummer blind: `Norm(1+x)=1+x^r`, while
  `ord_p(q_0)=r>1` makes `p`-powering an automorphism of the lower
  multiplicative group. Hence this norm is always a lower `p`-th power,
  independently of the upstairs selected status. At the actual
  full conductor, the full-valuation cyclotomic lift identifies the selected
  irreducible factor as `P_(alpha_r)(X^(r^a))`, and dependency-section descent
  pushes it through every actual odd-Kummer singleton `0/1` Lenstra edge
  satisfying its hypotheses. Two-primary nodes use their separate quadratic
  ancestry; multicomponent and excess-4 nodes still require synchronized orbit
  resultants. At each odd-Kummer singleton edge the simultaneous dependency
  sections also compress to one lower resultant whose selected evaluation is
  the relative norm of the selected value. Iteration gives one terminal scalar for each binary
  section, but its vanishing is exactly the original selected vanishing. The
  individual selected sections now have explicit reduced rational generating
  functions with denominator the reciprocal of the translated full-conductor
  minimal polynomial. Each has least period `ord(1+x_a)`, while their Boolean
  norm aggregate is exactly the zero-at-multiples word for the projective order
  `d_(r,a)`. Its minimal recurrence and DFA therefore recover, rather than
  bound, that unknown order. The
  full-conductor failure polynomial has a canonical monic self-reciprocal
  quotient; under hypothetical failure the selected factor occurs there
  simply, and its transverse
  derivative has terminal norm bit `1`. This proves the hypothetical
  intersection reduced, not empty. The final selected section nondivisibility
  remains open. A truncated-log Fermat
  regulator detects exactly whether
  the relative cyclotomic unit is locally a `p`-th power. Its nonzero values
  give conductor exactly `p^2`, and global reciprocity is an exact bilinear
  identity between Stickelberger valuations and the first mixed-Jacobi
  coefficients. Neither factor is known to be universally nonzero; if every
  local regulator vanishes, the resulting everywhere-unramified Kummer
  extension is either trivial or, if nontrivial, a `p`-class-group character.
  Simultaneous complex conjugation now gives an exact local reflection normal
  form. For the relative unit `rho`, the invariant realification is
  `u=rho*j(rho)=zeta_N^(1-q_0)*rho^2`; the root-of-unity factor is a global
  `p`-th power, so `u` and `rho` have the same Kummer class. The selected
  ordinary failure is therefore equivalent to `2` being a local norm from a
  degree-`p` reflection algebra at the named two-adic prime. The corresponding
  global norm equation is too coarse: it holds only when every prime of
  `Q(mu_N)` above two satisfies the power condition, hence detects simultaneous
  failure on every irreducible conductor-`N` factor rather than the selected
  one. Descending to the two-decomposition field erases `rho`, whose relative
  norm is one. Thus realification supplies a precise local norm formulation but
  cannot replace the missing mixed prime selector.
- **`C`.** The first three levels are proved analytically. Norm recursion,
  cyclic parity, primitive-CRT isolation, mixed Jacobi expansion,
  Singer–Wendt factorization, `S_3` descent, and the prescribed-trace character
  formulation all agree on one selected top-component test. Reciprocal cubic
  Kummer descent now identifies failure with two explicit Dickson power-sum
  equations over the preceding field and factors the Capelli composition into
  selected irreducible cubics. The equations already force irreducibility;
  after fixing the selected lower norm, their geometric fibre is reduced étale
  of size `ell^2`, with a singleton rational fibre at every lower level and
  exactly zero or `ell` rational points at the top. The top fibre is a
  `T[ell]`-torsor; its class is trivial exactly when the Euler representative
  `Omega = z_k^((q^2+q+1)/ell)/r_(k-1)` is one. Its complete extension-field
  point counts differ only by affine translation along one Frobenius-fixed line.
  After the unique cubic normalization `tau_k = z_k/d_k`, all current-prime
  torsors are the preimages `[ell]^(-1)(tau_k)` of this single norm-one
  element; `tau_k^((q^2+q+1)/ell)` is their mod-`ell` Euler obstruction. It
  has sparse cubic `X^3+s_k X^2+1`, and the coefficients
  obey the exact nonlinear ancestry `s_k^3=s_(k-1) tau_(k-1)^2`. The current
  obstruction is equivalently one selected critical resultant over `F_2`.
  Weighted homogeneity and the nonlinear ancestry compress that resultant
  further: a single fixed cubic norm operator carries it through every actual
  lower edge to one terminal bit in `F_2`. The bit is `1` exactly on success,
  so this is the cubic analogue of the Fermat one-branch descent, not an
  independent nonvanishing theorem. The critical polynomial also has an exact
  cyclotomic resultant factorization: its roots are the values attached to
  reciprocal pairs in `mu_u`, and at the selected coefficient its collision
  cubic is an affine/Frobenius transform of the actual Gaussian recursion.
  This identifies the selected factor with multiplicity but again reconstructs
  the same order class. A second normalization `h_k=1+gamma_k^(-1)` has the
  trace-recursive cubic `X^3+h_(k-1)X^2+X+1` and the same order as `tau_k` and
  `eta_k`; it is an invertible-power reparameterization, not an induction.
  The current Singer element itself has a different normal translate:
  `epsilon_k=eta_k+1` is absolutely normal over `F_2`, has the same order as
  `eta_k`, and generates the current torus exactly when `eta_k` does. Its
  Frobenius projectors hit every cyclotomic block, while the orbit of `eta_k`
  spans exactly the trace-zero hyperplane. The immediate trace-Gram and Moore
  determinants are explicit nonzero expressions in `epsilon_(k-1)` only.
  Thus the selected current subgroup already contains a normal translate of
  the same order, but its normal-basis determinants again transport only lower
  data. Complete normality of `epsilon_k` is not claimed.
  Keeping the full recursion reconstructs every finite Conway truncation up
  to Frobenius, and an infinite chain up to the corresponding pro-Frobenius;
  dropping it admits primitive-coefficient countermodels, so the normalization
  isolates but does not prove primitivity.
  The unpowered source cubic's Jacobian, discriminant, and Berlekamp trace are
  blind, while its reciprocal obstruction is the same selected Kummer class;
  by contrast the powered cubic's discriminant is precisely the critical
  obstruction above. None supplies an independent exclusion. Both distinguished
  period coordinates have absolute trace zero and are not normal, so
  primitive-normal and normal-Gaussian-period theorems do not apply. The inverse
  selector `beta_k=gamma_k^(-1)` behaves in the opposite extreme: it is
  unconditionally completely normal over `F_2`. More precisely the Frobenius
  orbit span of `gamma_k` has dimension `2*3^(k-1)`, that of `gamma_k+1`
  has dimension `2*3^(k-1)+1`, and that of `beta_k` has full dimension `3^k`.
  Hence even complete additive normality is present before the multiplicative
  primitivity question is asked; normal-basis or subspace-polynomial data cannot
  close the selected order gap. At each immediate cubic edge its three
  conjugates have trace Gram matrix `beta_(k-1)^2 I`, so after scaling they
  form a self-dual normal basis, but their Moore determinant is only
  `beta_(k-1)^3`. Absolutely, the multiplication matrix `M` of `beta_k`
  satisfies `det f(M)=Res(Q_k,f)`. For a current prime,
  `M^((2^(3^k)-1)/ell)-I` is either the zero matrix on failure or invertible
  with determinant one on success; this is exactly the original Euler test,
  with no intermediate rank. Norm-one Frobenius twists are conjugate to
  untwisted Frobenius by Hilbert 90, so crossed circulant determinants are
  blind as well. Generic
  Wendt factors and other trace fibres attain every structural value used by
  the obvious bounds.
  There is also an exact pure-radical reflection descent. With
  `K=Q(zeta_(3^(k+1))+zeta_(3^(k+1))^(-1))`,
  `B=K(zeta_ell+zeta_ell^(-1))`, and `theta^ell=c_k`, the reflection field
  `L_C=B(theta)` satisfies
  `C`-failure at `ell` iff `2 in Norm(L_C/B)`. Its norm torus satisfies the
  Hasse norm principle and weak approximation; every place above two is split
  on failure and unramified of degree `ell` on success, while every away-from-two
  condition for the element `2` is automatic. If `c_k` is already a global
  `ell`-th power the construction degenerates and failure is automatic. Thus the
  global norm equation is again exactly the original selected local splitting
  bit and creates no hidden class-group obstruction.
- **`D`.** The corrected norm, current-factor formulation, quadratic-twist
  antiunit, mixed-Jacobi and binary-parity criteria, reciprocal sextic, and
  Dickson factorization reduce the arm to one selected cubic. The surviving
  ray coordinate is also the first-order tangent of a canonical four-Jacobi
  cross-resolvent, the unique inversion-invariant zero-augmentation detector
  on the conductor-five phases. Quadratic-relative descent identifies that
  tangent with a two-by-two Eisenstein determinant; the first-order
  order-five Hasse--Davenport relation controls only the complementary
  symmetric coordinate and cannot force the target's nonvanishing. The ambient
  Dickson polynomial contains many cubics with the same depressed equation;
  an exact nonselected countermodel also matches the selected two-trace
  fingerprint. The selected fibotomic coefficient is now transported exactly
  through the C ancestry:
  `Z = (gamma_k^2 + gamma_k + 1)^(2^(2h/3)-2)`. The intermediate `g_k` form a
  norm-coherent tower, and the exceptional norm becomes one selected
  Artin--Schreier root pair. Current C and D primes are disjoint, so this bridge
  gives no direct primary-order transfer from C to D. A C-tower-faithful alternative coefficient
  `Z_k^circ = gamma_k^(-1)` has trace one, full degree, norm coherence, and is
  primitive under `C_k`, yet its Artin--Schreier root misses the entire current
  D-primary factor. This does not rule out an actual implication `C_k => D'_k`;
  any such implication remains open and must use the special coefficient above.
  Even retaining that literal rational coefficient is not enough without its
  selected lower norm: an exact degree-18 model has primitive degree-nine
  `gamma`, uses `Z=(gamma^2+gamma+1)^62`, and has the correct trace-one
  Artin--Schreier root, yet that root is a nineteenth power and its phase has
  order only `27`. The model deliberately has the wrong lower norm for
  `gamma^2+gamma+1`; full selected cubic ancestry would make it a Frobenius
  conjugate and preserve the power status. An exhaustive degree-nine census
  finds nine failures among 432 primitive scalars, all in one Frobenius orbit,
  but zero failures among the 60 points with the selected lower norm and zero
  among the nine points satisfying both selected norm and trace. This is exact
  finite evidence, not a universal implication. It isolates the selected norm
  ancestry as the remaining possible C-to-D coupling.
  The conductor-five antiunit now gives a second exact reflection descent.
  With `x=alpha+alpha^(-1)`, `F=Q(x)`, `K=F(sqrt(5))`, and
  `d_k=(x-s)/(x-s')`, the conductor-five involution sends `d_k` to its
  inverse. For each current `ell`, the resulting degree-`ell` reflection field
  over `F(zeta_ell)` is defined by
  `D^cl_ell(t)=2+5/(x^2+x-1)`, and `D'_k` fails exactly when `2` is a norm
  from that field. If `d_k` is already a global `ell`-th power, failure is
  automatic and the dihedral field degenerates. Otherwise this norm torus
  again satisfies the Hasse norm principle
  and weak approximation; locally, the named prime over two is split on
  failure and unramified of degree `ell` on success. Thus the D descent shares
  the Popovych reflection normal form but supplies no new C-to-D constraint:
  it collapses exactly to the original selected `-2`-eigenspace symbol, while
  C occupies the disjoint `+2` current eigenspace.
  This separation now holds for the actual global radicals, not just their
  rational-point group orders. For a C-current prime `ell_+` and a D-current
  prime `ell_-`, adjoining both root-of-unity groups preserves the two Kummer
  degrees; the pure-radical subfields cannot collapse inside an abelian
  cyclotomic compositum because they are non-Galois. The resulting compositum
  has Galois group `C_(ell_+) x C_(ell_-)`, and the Conway-compatible prime
  above two carries the two selected split/inert coordinates independently.
  Hence field intersections, common quotients, reflection descent, and shared
  reciprocity products cannot prove `C_k => D'_k`; only the special additive
  Artin--Schreier coefficient in the exact selector bridge remains capable of
  coupling the arms.
  Even the exact lower norm of the actual normalized root is automatically a
  current primary power downstairs. A coprime plus/minus decomposition now
  identifies the entire current primary order with the minus coordinate
  `P_k=M_k^(t+1)`, while the plus coordinate is the explicit `g_k` coboundary.
  The lower norm fixes only the already-known 3-part. Among ambient
  `Theta`-compatible pairs, norm and plus data can be held fixed while the
  current Sylow coordinate varies, but these variations need not remain on the
  trace-one Artin--Schreier locus. That locus is the remaining selected
  coupling. On the locus, aggregate norm and plus data determine the minus
  coordinate up to inversion; the exact selected norm chooses one root for
  `k>=3`. The resulting one-variable Dickson critical value is again exactly
  the unresolved full-primary test, so this rigidity reconstructs rather than
  estimates the selected order. More explicitly, the actual inverse coefficient
  has an irreducible cubic over the lower C field whose sole extra coefficient
  is an oriented resolvent `chi` satisfying
  `chi^2+chi=1+gamma_(k-1)^(-2)`. Its Dickson resultant is exactly the square
  of the already-known selected trace terminal. Reversing orientation preserves
  lower norm and absolute trace, proving those scalar shadows blind without
  treating reversal as an ambiguity of the selected Conway datum. The line
  criterion gives the effective polynomial bound above but not the required
  fixed window.

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
- [`experiments/fermat_selected_screen.py`](../experiments/fermat_selected_screen.py)
- [`experiments/fermat_selected_screen_results.md`](../experiments/fermat_selected_screen_results.md)
- [`src/scalar/big/ordinal/tower.rs`](../src/scalar/big/ordinal/tower.rs)
- [`src/scalar/big/ordinal/b380496.txt`](../src/scalar/big/ordinal/b380496.txt)

## References

- Berlekamp, Conway, and Guy, *Winning Ways for Your Mathematical Plays*.
- Brown, “Generalizations of the Kervaire invariant,” *Annals of Mathematics*
  95 (1972), 368–383.
- Conway, *On Numbers and Games*.
- DiMuro, “On `On_p`,” arXiv:1108.0962.
- Iwasawa, “On explicit formulas for the norm residue symbol,” *Journal of the
  Mathematical Society of Japan* 20 (1968), 151–165.
- Lenstra, “On the algebraic closure of two,” *Indagationes Mathematicae* 39
  (1977), 389–396.
- Moews, “The Abstract Structure of the Group of Games,” in *More Games of No
  Chance*, MSRI Publications 42 (2002), 49–58.
- Rohrlich, “Jacobi sums and explicit reciprocity laws,” *Compositio
  Mathematica* 60 (1986), 97–114.
- Vega, “A characterization and an explicit description of all primitive
  polynomials of degree two,” *Finite Fields and Their
  Applications* 109 (2026), 102716.
- Vega, “Necessary and sufficient conditions on the order of a finite field
  for the easy identification of primitive polynomials of degree 2,”
  arXiv:2607.01542 (2026).
- Wall, “Quadratic forms on finite groups, and related topics,” *Topology* 2
  (1963), 281–298.
- Zhu and Wu, “On binomial order and primitivity of irreducible quadratic
  polynomials over finite fields,” arXiv:2608.01327 (2026).
