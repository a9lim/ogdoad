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
- In the Eulerian quotient, harmlessness is exactly intersection of the
  response affine space with the cut space. Eulerian graphs carry an odd-triple
  curvature `3`-oik, but the attacker can prune its ordinary wall pairing.
- Complete schedules admit an exact permutation-threshold normal form, and
  pass-free histories admit a response-factor normal form. Both expose the
  same missing causal extension rather than proving it.
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
asks for a chain with cut-valued terminal moment. After the proved predecessor
reductions, the unresolved step is to kill the odd-spike/B-prime Schur class by
coupling earlier siblings with descendant continuation cosets. In the
response-factor language, this is a **causal charge-balanced factor-extension
theorem** simultaneously cancelling cut, continuation, pruning-frontier, and
frozen ko-wall moments while preserving odd augmentation.

This is the only missing mathematical step. More exhaustive enumeration or a
new scalar queue invariant would be useful for falsification, but neither is
the stated target.

### Verification surfaces

- [`writeups/linking_affine.tex`](../writeups/linking_affine.tex)
- [`formal/Ogdoad/Fifo.lean`](../formal/Ogdoad/Fifo.lean)
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
  the Conway–Fermat quotient-order problem. In that chain, absolute trace is
  exactly the top binary coordinate, the selected ancestry is the least
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
  is the unknown quotient order itself.
- **`O`.** The selected class is a relative Hilbert–90 unit. An
  absolute-Frobenius signed-ball argument proves every primary factor above an
  explicit threshold. Mixed Jacobi sums and binary sections isolate the
  remaining selected coordinate exactly. Tower-faithful countermodels show
  that generic ancestry and bookkeeping do not determine it. A fixed-translate
  countermodel now also matches full Kummer degree, all binary sections,
  norm-one reciprocity, and literal least-nonresidue labeling; it differs
  exactly in the lower ancestor's multiplicative order and cyclotomic
  conductor, isolating full Conway ancestry as indispensable. At the actual
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
- **`C`.** The first three levels are proved analytically. Norm recursion,
  cyclic parity, primitive-CRT isolation, mixed Jacobi expansion,
  Singer–Wendt factorization, `S_3` descent, and the prescribed-trace character
  formulation all agree on one selected top-component test. Reciprocal cubic
  Kummer descent now identifies failure with two explicit Dickson power-sum
  equations over the preceding field and factors the Capelli composition into
  selected irreducible cubics. The equations already force irreducibility;
  after fixing the selected lower norm, their geometric fibre is reduced etale
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
  Keeping the full recursion reconstructs every finite Conway truncation up
  to Frobenius, and an infinite chain up to the corresponding pro-Frobenius;
  dropping it admits primitive-coefficient countermodels, so the normalization
  isolates but does not prove primitivity.
  The unpowered source cubic's Jacobian, discriminant, and Berlekamp trace are
  blind, while its reciprocal obstruction is the same selected Kummer class;
  by contrast the powered cubic's discriminant is precisely the critical
  obstruction above. None supplies an independent exclusion. Both distinguished
  period coordinates have absolute trace zero and are not normal, so
  primitive-normal and normal-Gaussian-period theorems do not apply. Generic
  Wendt factors and other trace fibres attain every structural value used by
  the obvious bounds.
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
- Wall, “Quadratic forms on finite groups, and related topics,” *Topology* 2
  (1963), 281–298.
- Zhu and Wu, “On binomial order and primitivity of irreducible quadratic
  polynomials over finite fields,” arXiv:2608.01327 (2026).
