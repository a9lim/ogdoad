# OPEN: Genuine Research Problems

This file is intentionally narrow. It lists directions from repo audits, roadmap
splits, and the draft notes that look like genuine new research rather than
implementation of known formulas, standard algorithms, or already-source-pinned
theory. Implemented mathematical facts and maintenance context live in
`README.md` and `AGENTS.md`; buildable work lives in `docs/COMPLETENESS.md` and
`docs/CONTINUATIONS.md` (the game-valued ledgers — items there are referenced by
slug from here).

Numbering: an open problem is a loopy game, played without a termination
guarantee, so every entry wears a value from the loopy-stopper lexicon — the
shipped catalogue (`games/loopy/`: `on`, `off`, `over`, `under`, `dud`, `±`,
`tis`, `tisn`, and integer `s&t` tags). That loopy value rides a **pillar blade**
`e_B` exactly as in the buildable ledgers (`g·e_B`; `e_s` scalar, `e_c` clifford,
`e_f` forms, `e_i` integral, `e_g` games, `e_o` grundy, `e_y` py) — so an open
problem is a *loopy-valued* multivector term, the same labeling system as
[`COMPLETENESS.md`](COMPLETENESS.md), just with loopy coefficients in place of cold
numbers, switches, ups, and stars. The code can compute their finite
starter-pair outcomes; closure tombstones below record when the mathematical
problem has been settled independently of that naming vocabulary. The values
come in dual pairs, and so do the problems:

- **`tis`/`tisn`** (`{0|tisn}`/`{tis|0}` — "this is / this isn't") — the two
  game-native-quadratic-data questions are both resolved (2026-08-09). The
  outcome side uses the weighted-source Witt--FIFO normal-play rule and sharp
  observation boundary below; the
  coefficient side uses ambient short-game divisibility to force every
  torsion game square-zero and polar-radical.
- **`on`/`off`** — the two transfinite-On₂ questions: the tower that climbs past
  every verified rung (`on`) remains open; the classifier beyond the finite
  windows (`off`) was resolved on 2026-08-07.  Over full algebraically closed
  `On₂` the Artin–Schreier quotient and regular quadratic Witt group vanish, so
  the finite Arf bit switches off under scalar extension.
- **`over`/`under`** — the two mirror questions are now both resolved as
  independent directions.  Above the Arf bit, every Brown form canonically
  splits into a linear bit and an ordinary quadratic bit, while ambient
  short-game divisibility kills every global value-level Brown colour
  (`over`, 2026-08-09).  Beneath thermography, a substantive filtered transport
  exists while a faithful full-dyadic Newton-style ring is impossible
  (`under`, 2026-07-20).  Both are retained below as closure tombstones.

The games are the names: refer to a problem by its loopy value. `dud` stays
unassigned: `dud + G = dud` for every `G`, and no problem has yet earned
absorbing the whole roadmap. May none ever.

## open problems and closure tombstones

### ~~tis·(e_g∧e_f): `natural Gold-quadric game rule`~~ — resolved

**Resolved 2026-08-09.** The weighted-source Witt--FIFO rule is a fixed ordinary
normal-play rule whose P-positions are exactly the zero set `{Q = 0}` of every
finite `F_2`-valued quadratic refinement, hence of every Gold form. A q-blind
Witt frame makes the public polar graph a matching; one q-blind matched source
pair per active original coordinate uses its singleton diagonal bit as a local
overlap weight. The matching strategy is proved for both seats in every
dimension and a local claim lantern compiles forced charge to normal play.
The negative boundary is equally exact: every transcript-stable exact rule
must observe vectors spanning the input, so no constant total observation
budget works in unbounded dimension and the rule's active singleton support is
optimal. Outcome-preserving unavoidable fork padding proves that the basic
reachable, optimal, and unavoidable fork properties do not define
non-tautology. The proof is in
`writeups/goldarf.tex`; six Lean modules check its independent diagonal-source,
matching, algebra, compiler, observation, and padding ingredients.

The implemented bridge is already concrete. In a finite nimber field,

```text
x + y      = XOR = disjunctive sum of impartial game values
x * y      = nim product = Turning-Corners product value
x -> x^2   = Frobenius = diagonal product x*x
Tr(x)      = x + x^2 + ... + x^(2^(m-1))
Q_a(x)     = Tr(x * x^(2^a))
```

The Gold form `Q_a(x) = Tr(x^(1+2^a))` is therefore not just an abstract
characteristic-2 quadratic form; it is assembled from nim/game operations. The
Arf invariant then has the standard zero-count interpretation. For a nonsingular
quadratic form on `F_2^(2r)`,

```text
#{x : Q(x)=0} = 2^(2r-1) + (-1)^Arf * 2^(r-1).
```

For degenerate forms, the implementation uses the usual radical-adjusted count:
an anisotropic radical balances the values exactly, while an isotropic radical
scales the bias. For the resolved game, Arf therefore says which player wins
from more starting positions and by what square-root-scale margin.

Why this was research:
- The repo already builds the Gold forms and tests several game routes. The
  former missing datum was not code for `Q`; it was a play rule and a
  definition of "natural" strong enough to make the question non-ad-hoc.
- Normal-play sums do not solve it. For impartial normal play the P-condition is
  `g_1 xor ... xor g_n = 0`, hence linear in Grundy coordinates, while
  characteristic-2 quadrics obey `Q(u+v) = Q(u) + Q(v) + B(u,v)`. The polar form is
  exactly the XOR-closure obstruction.
- Frame-blind rules are too symmetric, while rules with a constant total
  outcome certificate cannot be exact at dense inputs. The resolved boundary
  is a fixed local-interaction rule attaining the necessary observation span;
  the basic reachable, optimal, and unavoidable outcome-only fork tests cannot
  strengthen that statement into an invariant definition of the adjective
  "natural".

The lexicode shadow (standard math + interpretation; the solved linear case):

The degree-1 version of the question is classically solved, and it is rich.
Conway-Sloane lexicodes ("Lexicographic codes: error-correcting codes from game
theory", IEEE Trans. Inform. Theory 32 (1986) 337-348) are built by the greedy
lexicographic rule, which is the mex rule: the codewords are the Grundy-value-0
positions of the shipped `LexicodeTurningGame` move structure, binary lexicodes are
linear *because of* Sprague-Grundy theory (XOR-closure is a game theorem, not a
coding theorem), and the length-24, d = 8 lexicode is the extended binary Golay
code. More generally, the shipped `NimLexicode` route verifies that lexicodes over
base `2^k` are closed under nim-addition and witnesses the stronger linearity
boundary: bases 4 and 16 are closed under finite-nim scalar multiplication, while
base 8 is not — exactly the Fermat-power distinction where nim-multiplication makes
the ordinals below the base a field. So natural, fixed, non-tautological rules
demonstrably realize rich *linear* codes as P-sets; and the matching no-go
(`writeups/goldarf.tex`, Theorem A:
every Winning Ways coin-turning P-set is the kernel of an `F_2`-linear map)
says linearity is also the ceiling for that architecture. Floor and ceiling
coincide at linear. `tis` asked whether the lexicode phenomenon admits
a quadratic refinement — a rule producing the XOR-closure failure that the
polar form `B` measures. Bridge O (built) makes the
lexicode chain executable (`LexicodeTurningGame` -> greedy = mex -> Golay ->
Construction A -> theta); that is context for this problem, not progress on it.

Current probe map:

- `forms::quadric_fit::fit_f2_quadratic` asks whether a subset of `F_2^k` is the
  zero set of a genuine quadratic polynomial rather than an affine set.
- `experiments/trace_form_arf.py` builds Gold forms and checks the Gold rank
  formula on the tested power-of-two fields.
- `experiments/gold_form_from_games.py` rebuilds the same form using literal
  Turning-Corners products on small fields.
- `experiments/tartan_bilinear.py` rebuilds the polar form from game products.
- `experiments/arf_win_bias.py` brute-forces value distributions and matches the
  Arf-predicted zero counts.
- `experiments/gold_family_survey.py` broadens from unscaled Gold forms to
  components `Tr(lambda*x^(1+2^a))`. Over `F_256`, for APN Gold exponents
  `gcd(a,m)=1`, 2/3 of nonzero `lambda` give bent components, reproducing the
  classical count. Bent forms are the cleanest target because `R(B) = {0}`.
- `experiments/framing_obstruction.py` shows that for tested Gold polar forms,
  the coordinate-frame quadratic refinement has Arf 0 and the diagonal term
  flips to the Gold form. Historically this exposed the diagonal-framing
  question later answered by the local weighted-source construction.
- `experiments/misere_kernel.py` verifies the Plambeck-Siegel kernel obstruction
  concretely on `R8`: the kernel is `(Z/2)^2`, `P cap K = {0}` is linear, and the
  genuine misere P-element lies outside the group where a vector-space quadric
  framing applies.
- `examples/interactive_kernel.rs` confirms that arbitrary P-sets and direct
  `Q`-evaluators are easy, while the tested polar-form rules do not reproduce the
  Gold zero set.
- `examples/loopy_quadric.rs` adds Draw as a third route. The symmetric `B` rule
  has Loss-set equal to the radical `R(B)`, so it explains one small coincidence
  and then fails away from it.
- `examples/bent_route.rs` tests a bent Gold component. A `B` plus coordinate-frame
  rule reaches a bent quadric of the correct Arf class but not the specific Gold
  zero set; adding the naive per-coin Ising field leaves the quadric variety.

Resolution state (2026-08-09):

- Weighted-source Witt--FIFO chooses a deterministic
  symplectic-plus-radical basis from public `B`, loads its active coordinates
  as a matching, and loads one q-blind source pair for each active original
  coordinate of `x`. Public basis coins carry the `B`-dependent triangular
  correction; the overlap of source pair `j` has weight `q_j`. Thus F1 is
  q-blind and F2/N2 hold with `(w0,c)=(1,1)` for transitions as well as
  legality; refinement data enters a play-dependent interaction rather than an
  invariant terminal label.
- On every matching-plus-isolates board, either seat keeps the opponent's FIFO
  front ko-protected or zero-live-degree. Applied to the q-blind potential
  matching, the same policy makes every close individually zero and hence
  forces every potential pair to overlap; the strategy itself is uniform in
  the refinement. A rank induction proves this for every finite board, with no
  dummy. Polarization then proves forced terminal charge `sigma=Q_q(x)` for all
  dimensions and refinements.
- A unique terminal claim move, enabled iff `sigma = 1 xor phase`, compiles the
  finite charge tree to ordinary normal play. At the root, P iff `Q_q(x)=0`.
  The phase is the existing mover bit and is necessary to preserve seat identity
  across both history parities.
- Transcript stability plus torsor-uniform exactness forces every outcome
  certificate at `x` to span `x`. With weight-`w` observations this gives
  `wt(x) <= #observations*w`; no constant total budget is possible, and the
  source pairs attain the singleton lower bound exactly.
- The old mixed-successor N3 is defeated by dominated escape edges, while
  dominance-pruned mixed-successor criticality is impossible. Stronger
  reachable/optimal/unavoidable fork tests also fail: every terminal of an
  arbitrary finite normal-play tree can be padded by an outcome-preserving
  forced wrapper into a refinement-sensitive fork. This is kernel-checked, so
  strategic liveness is retained as description rather than a naturality axiom.

Historical program state (2026-06-10 — retained as proof provenance):

- The naturality criterion asked for below had a draft formalization — N1
  (decision-nondegeneracy), N2 (bounded framing access), N3 (strategic
  relevance / anti-clock). The final audit proves that no reachability-only N3
  can do this job: outcome-preserving forced fork padding defeats even optimal
  and unavoidable variants. The transcript-span theorem is the replacement.
- A no-go ladder (Theorems B–H) kills Tier 1 outright and shows every known
  in-quarantine Tier-2 normal-play realizer is a clock. Five named escape hatches
  were catalogued: loopy-Draw semantics, `t ≥ 2r−2` with anisotropic complement,
  Frobenius-aware access (where both the symmetry and oracle methods are provably
  silent), non-quarantined rules using the game-native `℘` diagonal source, and
  rank-1 / radical-anisotropic degenerate layers.
- The abelian obstruction conjectured here is now Lemma `abelian` in the draft:
  no commutative game monoid's intrinsic squaring realizes a nondegenerate polar
  form, so the quadratic datum must come from the move relation's directedness.
- The formerly open even-`a` diagonal source is closed for every exponent
  (`writeups/gold_diagonal_source.tex`). The exact quadratic-tower recursion
  makes the unscaled trace-dual descend to the half-field, hence its absolute
  trace vanishes and it is `w²+w`. This supplies the whole Gold diagonal by
  game operations; weighted-source Witt--FIFO supplies the separate play rule.
- The leading Tier-2 candidate was the `echo`-ko charge-counting family on the
  extraspecial cocycle, and its `echo`-`fifo`+dummy variant is now **verified**
  (2026-06-10, pre-registered adversarial review, `experiments/echo_solver.py`):
  full `m = 8` exactness across all 765 scaled Gold forms, both stances,
  391,680/391,680 checks re-derived by a fresh direct full-state solver — no
  decomposition, σ in the memo key, validated against tree enumeration and the
  original direct solver, with a second-model cross-run. Decision-live in bulk
  (1.5–4.4M decision states per benchmark instance), torsor-uniform across
  refinements of each `B`. At that date three honest boundaries were: the
  realizer was **σ-valued** (the later claim-lantern theorem supplies normal
  semantics); the `echo`-ko table is stance-asymmetric (its exactness face is
  the σ=1 stance only, where `fifo`+dummy is exact at both); and the
  bounded-window blocker conjecture is untouched (the FIFO queue is unbounded
  memory). The
  Plambeck–Siegel Thm 6.4 regularity gate is still slug `ps-regularity`.
- The mechanism behind the verified realizer is now reduced and substantially
  sharpened (2026-06-10 and 2026-07-20 passes, goldarf §8 "linking reduction",
  `experiments/linking_game.py`): FIFO forces closes in opening order (no
  nesting, linked = overlap), the whole σ-game is equivalent to an
  **odd-close parity game** (only closing a queue front with an odd number
  of untouched neighbors flips the outcome bit), ko/passes localize away,
  and the **general-m linking theorem** — flips forced even on any board
  with an isolated coin, hence exactness for ALL m — is machine-verified
  for every graph isomorphism class through k = 8 real coins plus dummy
  (12,346 classes at k = 8, both seats), far beyond Gold-arising boards.
  Two new exact reductions delimit the proof route. Every maximal
  nonempty-queue block on b coins uses 2b touches, so the initial mover
  starts every block. And, with L the still-unclosed vertices when x opens,
  the flip parity is `sum_x deg_L(x) mod 2`: for the potential
  `P = e(queue,U)`, a close changes P by its flip bit and an open changes P
  by `deg_L(x)`. This second identity is FIFO-blind, so FIFO must enter the
  strategy through its forced close target rather than through the
  accounting itself.
- The old parity-local menu realization of the proof architecture is now
  falsified precisely rather than merely unfinished. The original
  prevention/debt menus remain strictly complete
  through k = 7, but graph6 class `GCRU]w` at k = 8 requires a proactive
  neighbor-open that creates an even odd-degree queue corridor even though
  safe non-neighbor opens exist; `GCZMmw` then requires leaving an odd front
  deliberately unrepaired. Thus a parity-local "repair whenever possible"
  induction cannot prove the theorem. The broader no-self-flip prevention
  envelope (every open plus even-front closes), paired with the existing
  debt menu, is strictly complete on all 12,346 k = 8 classes, both seats.
- A proof-level third pass (2026-08-07,
  `writeups/linking_affine.tex`) lifts the live-degree identity to the
  **disjointness vector** `D(h)` in the full `F_2` edge space.  For a fixed
  attacker strategy `S`, the general theorem is now exactly equivalent to
  `0 in Aff{D(h): h responds to S}`: if zero is absent, finite-field linear
  separation produces an actual graph on which `S` forces odd parity.  At a
  real FIFO front `f`, the edge space splits canonically as
  `E(K_L) = Cut(K_L) direct-sum E(K_{L-f})`, with quotient gauge
  `T_f(z)_ij = z_ij + z_fi + z_fj`.  Opens before `f` closes occupy the cut
  layer; later play occupies the smaller edge-space layer.  More canonically,
  `T_f(z)_ij = (delta z)_fij` is the two-graph/Seidel chart of the simplicial
  coboundary, and successive front gauges absorb: `T_g T_f = T_g` after the
  corresponding deletions.  This turns the
  remaining proof into one precise global affine-contraction lemma: construct
  an odd formal response flow with zero terminal edge moment.  A stronger
  branchwise common-coset induction is **false already on `P4+dummy`**: two
  defender-open children can have disjoint projected continuation affine
  hulls.  Any proof must transport nonzero target cosets and cancel across
  branches and filtration levels.  The global lemma is open.
- The cone calculation now identifies the exact correlated induction datum.
  If `p_f` is the indicator of vertices untouched when front `f` closes and
  `W_f` is the away-`f` continuation moment, then
  `D = sum_i p_i fi + W` and `T_f D = W + delta p`; a response chain cancels
  `D` exactly when it cancels **both** `p` and `W`.  The cut moment `p` alone
  does contract affinely at an attacker-opened initial front: a separating
  weight can always be answered by the zero-weight dummy or another
  weight-one vertex.  An explicit three-real-vertex broken diamond proves
  that this contraction does not lift independently through an arbitrary
  attacker continuation.  The remaining lemma is therefore joint-moment
  cancellation, not merely a quotient normalization.
- A proved two-bit handshake refinement now repairs the first degree-only
  pairing failure.  On every even-order graph, colouring `v` by
  `(deg(v) mod 2, number of odd-degree neighbors mod 2)` gives four
  even-cardinality colour classes.  Pairing equal colours makes all four
  residual `(degree parity, incidence into the first pair)` fibres even, so
  the defender has a second reply matching both the next opening charge and
  its cut against the first FIFO cell.  This is exactly the joint moment
  missing from the six-vertex degree-only witness.  It is not yet an
  induction: the second cell can split those four fibres unevenly, and a
  later close/open switch must then transport the resulting continuation
  offset.
- That refinement is now sharply bounded.  Equal two-bit colour does **not**
  make an ordered first cell safe under unrestricted play: on
  `01,03,05,07,12,14,15,17,24,26,27,34,37,45,46,47,57,67`, `Q=(6,7)`
  is losing while the reverse `Q=(7,6)` is winning.  More strongly, in the
  losing orientation the unique first spoiler is `OPEN(5)`, whose degree
  parity is opposite to 6 and 7.  Thus the least-counterexample witness map
  is not forced to preserve its odd routing set by the local unsafe-state
  hypotheses alone; a cycle argument would require a new closure consequence
  of global minimality.  Separately, in the
  class `G?ben[` opener 2 has only one same-colour mate, 7, and `Q=(2,7)`
  is losing.  Thus even the existential “some same-colour reply” selector is
  false at order eight.  These are counterexamples to the selector, not to
  the even-board or isolated-dummy theorems.
- The scalar force sets now have canonical roots `T(A), K_x(A), S_x(A),
  Q_xy(A)` with exact union/intersection recurrences.  This gives a rigorous
  least-counterexample reduction for the even-board subproblem.  If a least
  even counterexample opens `x`, the same-degree-parity reply set `Y` has odd
  size; on every `y in Y` the winning continuation must OPEN a third vertex
  and must survive every sibling reply at the next face.  A pointwise
  one-cut induction is false: the realized six-vertex witness
  `03,12,13,14,23,25,34` has even remainder `P4`, yet all three targets
  shifted by the front cut remain forceable.  The missing object is the
  joint distribution across the odd sibling family, not another color of a
  single `Q_xy` branch.
  Writing force-set membership as a Boolean polynomial sharpens the residual
  further.  If `P(H)` means `0 in S_z(H)` for every vertex, then a failure of
  `P(H) => T(H)={0}` forces one universal full row:
  `Q_xy(H)={0,1}` for every `y != x`.  The implication holds on the complete
  census through order eight (`1,4,18,262` `P`-classes in even orders
  `2,4,6,8`), because each such graph has an even-cross perfect pairing.
  This remains a finite certificate, not the proof: rowwise and same-degree
  Möbius parities already fail at orders four and six, and Eulerianity alone
  does not guarantee the pairing by order fourteen.  The exact missing scalar
  lemma is therefore a joint contraction internal to the ordered `Q_xy`
  subtrees which excludes the universal full row.
  With the isolated dummy this odd family now has a proved pointed corridor.
  In a least even-real root failure, `C_x` cannot first spoil a same-degree
  pair: `C_y` cancels it and reaches the smaller isolated-dummy root.  Every
  first spoiler is therefore OPEN.  For a real spoiler, the remaining real
  vertices in its `eta_xy` fibre form an odd nonempty reply fan; iterating
  preserves equal front charges and the untouched dummy until a CC exit, a
  zero OC phase pivot, or attacker `O_d`.  Summing over the odd root-mate set
  gives an odd aggregate exit chain.  The precise parity leak is the `O_d`
  exit: its real OPEN replies form an even fan, with `C_x` present only when
  its charge is zero.  Exact minimax says `O_d` is never the spoiler at such
  an unsafe root through the complete order-eight census, but this fan-level
  harmlessness remains unproved and is not a pairwise dummy diamond.
- The affine target now has an exact homogeneous recursion
  `Z(h) <= F_2 + E_real`: attacker nodes translate one child, defender nodes
  span translated child spaces, and the theorem asks for `(1,0) in Z(root)`.
  This rules out an ordinary tree contraction because the odd augmentation
  must be preserved with the edge label.  The scalar cut potential also gives
  an exact local poison classification: at `P=e(queue,U)=0` and even `|U|`,
  equal-charge replies always exist except after an even close when every
  untouched live degree and the next front degree are odd.  Matching charge
  restores `P` but mixed close/open rounds retain one flip debt, so this does
  not close the global recurrence.
- Augmentation parity is now resolved rather than hidden in `Z`.  At every
  history, even continuation moments form a linear space `W_h` and odd
  moments an affine coset `A_h`; a defender fan combines the child pairs by
  exact parity convolution.  The smallest essential coupling occurs with
  three real vertices plus dummy: no single reply coset contains zero, but
  the odd profile on all three replies cancels.  Dually,
  `N_h=Z(h)^perp` has an intersection recursion.  Any odd frontier flow of
  actual graph-charge zero from a bad node has an odd number of bad exits.
  This makes balanced-front transport monotone: it descends a dual
  counterexample by two live vertices.  Lexicographically minimizing first
  the number of live real vertices and then event rank sharpens the terminal
  obstruction completely.  Its predecessor is either a CLOSE with an odd
  next-front charge, or a ko-set singleton `(x)` after the dummy has already
  been touched, with a nonempty even real untouched set to which `x` is
  universal.  The untouched dummy rules out every OPEN predecessor.  The
  domination case also has a forced ancestry: the preceding empty-queue
  OPEN is zero, while the singleton-front defender CLOSE immediately before
  it must be odd.  If that CLOSE were even, an odd family of same-live-degree
  OPEN siblings would all be balanced bad checkpoints, and balanced-front
  transport would produce a bad exit with one fewer live real vertex.  Thus
  the domination form is created from a good defender node by an
  odd CLOSE and merely inserts one zero OPEN.  The CLOSE-spike alternative
  has two subcases: an odd predecessor gives the same good--bad--good pattern,
  while an even predecessor remains bad but can occur only with an even
  untouched set; an odd same-eta OPEN fan would otherwise give a smaller
  balanced bad exit.  The spike cannot be propagated farther backwards
  locally (an exact five-vertex counterexample has an earlier even close), so
  excluding these sibling-coupled terminal patterns is now the narrowest
  scalar proof obligation.
- The complete fixed-front prefix itself now contracts.  Stop every compatible
  response when the current front `y` closes and record the untouched
  remainder `R`.  For every deterministic attacker policy,
  `0 in Aff{R}`, hence the accumulated front-star labels `yR` admit an odd
  zero-moment response flow.  The proof is an exact two-line force recursion:
  for a separator `ell`, attacker-root forcing is
  `ell(S)=1 or exists w, D(S-w)`, while defender-root forcing is
  `ell(S)=1 and forall v, A(S-v)`; strong induction makes every `D(S)` false.
  This does not yet carry the minimum-bad branch.  When `ell(S)=1`, an
  attacker can make every leaf below a non-CLOSE first move have `ell(R)=0`,
  so no zero flow containing the immediate odd CLOSE need exist.  The prefix
  is therefore absolutely contractible but not relatively contractible at
  the selected (A)/(B') leaf; descendant continuation cosets or earlier
  siblings remain necessary.
- The exact relative target is now a single quotient-membership statement.
  For the frontier consisting of the chosen minimum-bad node `h` and every
  earlier off-spine defender child, write each decorated odd continuation as
  `b_q + W_q`.  The root chains with coefficient one at `h` have moments
  exactly `b_h + M_h`, where `M_h` is the sum of all continuation spaces and
  all even off-spine sums.  Hence the desired chain exists exactly when
  `b_h in M_h`.  Any scalar counterexample pairs to one with `b_h` and
  annihilates `M_h`.  This is the precise remaining ancestry contraction;
  forgetting the coefficient at `h` recovers only the already-proved absolute
  fixed-front result.
- The singleton ko wall is no longer an unformalized local defect.  Lean proves
  that, from a clear singleton queue, `C_f; O_z; O_w` and
  `O_z; C_f; O_w` reconverge after the next distinct real OPEN.  Their public
  states agree and their score difference is exactly the frozen edge `fz`.
  It also proves transition equivariance under score translation and the
  induced strategy-sheet equivalences.  This transports any chosen local
  square through a shared continuation; it does not choose a coherent family
  of squares across the complete defender fan.
- Cross-feeding two copies whose queues differ by one leading front gives a
  finite offset ladder.  Paired CLOSEs merely change the offset token and are
  flat; a paired OPEN `z` contributes exactly the token edge `az`, and a long
  front CLOSE diagonalizes the copies.  Thus the ladder holonomy is an
  explicit sum of frozen token-OPEN edges.  An odd ladder family through the
  selected branch would prove `b_h in M_h`, but score-sensitive strategy
  pruning does not presently give the required even internal incidence.
- A second Lean-checked minimum now lives inside the assumed `OddWins`
  strategy tree, avoiding irrelevant smaller states elsewhere in the game
  graph.  Every zero-sheet odd counterstrategy contains a selected unit CLOSE
  whose translated child is a completely score-neutral same-player tree.
  The scalar Bellman residual and actual accumulated score are complementary,
  so the lexicographic dual minimum supplies this neutral tail after every
  forced `(B)` puncture.  Opponent-controlled singleton closes in those tails
  have charge zero, and the even untouched remainder is therefore
  unconditionally Eulerian.  Minimum badness also forbids an
  immediate off-spine unit `C_y`.  More sharply, after every `(B')` defender
  `O_v` with `v` in the Eulerian remainder, the attacker must answer by an
  `O_w` of the opposite `y`-adjacency colour.  Outside the sole-neighbour cap
  (`yx=1` and `y` anticomplete to the remainder), the defender can force this
  first response to stay inside the Eulerian remainder; a zero `C_y` then
  exposes an adaptive cross-colour ordered pair.  These facts still do not
  close the local
  cap: on edges `{yx,xa,xb}`, with `Q=(y)` and `U={x,a,b}`, the selected
  `C_y,O_x,O_z,C_x` branch has charges `1,0,0,1`, while one attacker policy
  makes every off-spine subtree entirely neutral.  Adding isolated `d`, a
  processed `p`, edge `py`, and prefix `O_p,O_d,C_p,O_y,C_d` reaches this cap
  with odd score.  Thus the remaining proof must use still earlier root-to-cap
  siblings; Eulerianity plus the complete three-event ancestry is
  insufficient.  The four-real core cap graph itself is not a counterexample:
  this excludes the separate processed `p` and ancestry edge `py`.  The existing
  mutual star induction gives a symbolic both-seat, all-zero-charge root
  strategy for every star plus any nonempty set of isolates.  The complete
  earlier relative-spine frontier now yields a genuine global incidence
  theorem: it carries the entire live `yA` star.  Otherwise a linear
  functional separating that star from `P_y(M_h)` would have value one on
  every frontier cylinder (the second ko child fixes the off-spine constant),
  so replaying the history policy on its support star would force odd score,
  contradicting the both-seat star strategy.  After choosing
  `m_y in M_h` with `P_y(m_y)=yA`, the sole remaining `(B')` obstruction is
  the well-defined away-star Schur class
  `[d_r+m_y] in ker(P_y)/(M_h intersect ker(P_y))`; it vanishes exactly when
  the selected leaf belongs to `M_h`.  A truncation at the first off-spine
  response cannot prove this incidence—its columns are only even-weight
  `v+w_v`—so the global argument genuinely uses deeper or earlier siblings.
  Projecting the away-star class once more to the live `xU` star leaves only
  two bits: ko-sibling differences supply every even vector on `U-{s}`, so a
  dual obstruction is constant off the selected puncture `s`.  Equal bits
  recover the universal-cone colour; unequal bits give the genuinely relative
  pattern `h=1` and every off-spine cylinder `=0`.  The exact next target is
  the *joint* incidence `(yA, delta_s)` in the image of `M_h`, not either
  marginal separately.  Neutral tails and ko differences cannot supply that
  correlation, and coordinates away from both stars remain afterward.
  The first exact
  degree-one sibling explains the difficulty: on its `C_p,O_x,O_d,C_y`
  branch one reaches `Q=(x,d), U=H`, with `H` even Eulerian.  Closing `x,d`
  exposes the no-dummy empty-root force set `T(H)`, while the neutral puncture
  family gives the exact hypothesis `P(H)` of the universal-full-fan
  reduction.  Excluding `1 in T(H)` is therefore equivalent to ruling out one
  universal full `Q` row.  Even that root exclusion is not the whole endpoint:
  before `C_x,C_d`, the attacker may draft arbitrarily many real pairs, so the
  defender needs an online draft-and-stop lift whose every possible stopping
  checkpoint is safe.  Ordinary smaller-dummy-root or bare empty-root
  induction therefore stops at precisely the offset-ladder endpoint rather
  than closing the ancestry.
  A tempting sharper scalar target is false at order ten.  An explicit Euler
  graph with degree sequence `(8,8,4,4,6,6,4,4,6,8)` has, at the canonical
  state `Q=(2,9)`, both an all-zero-charge `TreeNeutralWins` and an odd-forcing
  strategy for the same physical attacker.  (The exclusivity happened to hold
  through order eight; off the Euler locus it fails already on four live
  vertices.)  Thus the `(B)` proof must use its simultaneous family of
  punctured neutral trees, not determinacy or Eulerianity at one ordered pair.
  That full family has a proved row contraction: at `Q=(x,y)` its selected
  neutral move either grounds `C_x` on `xy=0`, or opens a vertex `z` with
  `xz=xy`, after which the universal `C_x` child is neutral on the smaller
  ordered pair `(y,z)`.  It also supplies a neutral short root `T(H-x)`.
  Opening its first `y` places that short policy at ko-singleton `(y)` against
  the hypothetical full-row odd policy at long queue `(x,y)`, exactly the
  one-front-offset wall.  Only a long initial OPEN has a common OPEN which
  enters the clear offset recurrence.  A long initial CLOSE instead removes
  the token, after which one common defender OPEN reconverges the copies
  diagonally (or the empty tail drains); it therefore lands immediately in
  the same-state continuation-flex obstruction.  Eulerianity kills the complete `x`-star sum; the
  unresolved step is proving that the strategy-pruned ladder has the required
  even token-OPEN incidence.  More exactly, one coupled trunk records a rooted
  ancestry tree: use `xy` as the cut-equivalent seed for the initial `xU`,
  then attach each common OPEN `z` to the current offset token `a` by `az`;
  crossed CLOSEs only change the token.  It spans all vertices only in the
  full-drain case, and its pairing measures only the first diagonal/drain
  checkpoint.  A single such tree need not pair evenly with an Euler graph,
  nor do the different terminal targets force an odd pairing at a nonterminal
  diagonal because the same player may choose different continuations there.
  The missing global lemma must first define a recursive comparison past those
  diagonals and promote unused defender children to a branching response
  family, then extract an odd subfamily whose XOR is a cut.  Unrestricted
  recursion after a diagonal is not itself progress: the sum of the two odd
  continuation cosets meets the cut space exactly when their cut-quotient
  projections intersect, which is the original decorated-frontier common-coset
  problem.  Earlier off-spine sibling spaces must therefore enter essentially.
- The conditioned close-first tail is now closed without a dummy hypothesis.
  From any coherent clear defender state with nonempty queue, a close-first
  attacker cannot force future flip parity one.  A minimum-rank proof opens
  each untouched vertex before the forced front close; if every smaller child
  were odd, the front would dominate an even untouched set with zero current
  charge.  The singleton and two-front continuations then contradict the same
  minimality, with a separate whole-queue drain argument for exactly two
  untouched vertices.  The exact strategy semantics, drain identities, and full
  conditioned theorem are kernel-checked in `formal/Ogdoad/Fifo.lean`.
  Hence every leafmost voluntary attacker OPEN lies on residual
  target zero, behind an earlier odd CLOSE.  This does not iterate across
  residual switches: the reachable graph `{01,02,12,03}` at
  `U={0,2}, queue=(1,3)` has a target-one policy which is close-first on every
  target-one state and uses one indispensable target-zero singleton-wall
  OPEN.  The open root problem is therefore the coupling of those earlier
  odd-CLOSE siblings, not the post-OPEN tail.
- The same pass proves a strict extension of the twin-pair subclass.  If the
  vertices partition into 2-cells `A` with `e(A,B)` even for every two cells,
  the second player mirrors mates and forces even flips.  This is not general:
  64/1,044 seven-real-vertex classes plus dummy admit no such partition.  Exact
  `K2+dummy` and `P4+dummy` states also show why debt-sensitive and proactive
  wrong-parity opens are mandatory; same-degree pairing plus FIFO rotation is
  not an induction.  At three real vertices, a universal triangular
  three-history cancellation exists at the last nontrivial queue state, but a
  separate exact strategy shows that the fan over all second openings cannot
  be composed recursively.  Nor is support three a global bound: a fixed
  close-first attacker at five real vertices has 132 response vectors, no
  zero or zero-XOR triple, and an exact minimum odd certificate of support
  five.  A valid contraction must choose an odd subset of branches from their
  continuation data.
  This bounded-support obstruction is now proved to be unbounded even after
  quotienting by cuts.  A reachable singleton-front checkpoint with `r`
  untouched vertices and a close-first attacker projects all terminal labels
  onto the causal simplex cap
  `C_r = {1^r} union {1^r + e_i}`.  For `r >= 4` it contains neither zero nor
  a zero-sum triple; its unique nonempty relation has odd support `r` for odd
  `r` and `r+1` for even `r`.  At `r=4`, five explicit compatible histories
  attain the bound and XOR to a cut.  Hence no bounded affine-circuit theorem
  can work childwise.  A root proof must couple these caps to a wider
  collection of earlier sibling branches.
  Even pairwise ancestor escape is false.  At the preceding checkpoint
  `U={1,2,3,4,5}, Q=(dummy)`, one target-forcing attacker keeps the union of
  the two defender children `OPEN(1)` and `OPEN(5)` inside a pinned 52-point
  quotient cap.  That cap already has the five-circuit
  `7 xor 11 xor 13 xor 14 xor 15 = 0`, and the full defender fan has four
  further moves, so this is not a root or affine counterexample; it proves
  that cancellation cannot be reduced to a zero-or-triangle escape from a
  cap child plus one arbitrary sibling.
  The stronger ancestor-cap escape rule is false too.  A five-real-vertex
  spine ends in a child image `X={1,3}`, yet every sibling at every preceding
  defender fan admits a compatible deterministic attack whose complete image
  avoids `{0,2}={0} union (X+X)`.  These branch strategies coexist because
  their histories diverge at the defender choice.  Thus no single ancestor
  sibling need break a cap child; the missing proof must construct a larger
  odd dependence across several sibling images at once.
  The remaining question is whether that broader finite strategy has a
  general recursive certificate.
- Same-action adaptive pairing has a sharp first failure on the no-dummy
  order-eight classes `GCZN^{` and `GEjt~{`.  Exact minimax needs two action
  switches on each, not one.  The tail is now proved rather than merely
  observed: with `U={x,y}` and an odd queue whose consecutive pairs (after
  appending `x`) have equal adjacency to `y`, the defender opens `x`, pairs
  close responses, and closes once if the attacker opens `y`; all pair charges
  cancel.  Both witnesses enter this tail with `y` dominating.  What remains
  is the prefix theorem forcing a suitable corridor.  Abstract symplectic
  rank/Witt data cannot supply it: congruent alternating forms already have
  different FIFO outcomes at order three.
- A stronger finite target survives: on every even graph through order eight,
  the second player can return the **actual flip score to zero after every
  one of her moves**.  Its exact certificate is a ranked, noninjective repair
  forest on even queue checkpoints, with the singleton
  OPEN--pass--CLOSE tail treated as a terminal macro.  Pair-open replies
  extend the queue's
  consecutive matching, pair-closes delete its front edge, and a zero-close
  reply flips matching phase along the entire queue.  If the odd queue word is
  `W=(v0,...,v2r)`, the old/new matching difference is the path `P(W)` with
  `boundary P = v0+v2r`; coning that path produces a triangle fan whose
  residual charge is the two-graph holonomy `sum delta B(v0,vi,v{i+1})`.
  Tetrahedral `delta^2 B=0` makes the full sibling simplex coherent, but a
  fixed attacker strategy prunes interior faces and assigns non-flat
  continuation coefficients.  Ordinary injective-word shelling, a static
  matching, degree/two-bit colors, Krylov signatures, and symplectic flag data
  all have explicit small counterexamples.  The open theorem is construction
  of the strategy-relative repair forest/affine chain, not discovery of one
  more scalar invariant.
- Scalar zero normalization is not a graph-independent affine carrier.  An
  exact eight-vertex pair of Euler graphs `A,B` is pinned in
  `normalized_secondary_moment`: `A` has a repair forest, but one deterministic
  attack has 88 complete `A`-normalized response histories and every one has
  `B`-moment one.  Their affine hull therefore misses Cut.  This does not
  threaten the scalar `A` strategy; it rules out pruning to `A`-normal replies
  and then applying the Euler quotient contraction uniformly in a second
  graph.
- Complete schedules now have an exact permutation--threshold normal form.
  If `pi` is the common FIFO opening/closing order and `r_b` is the number of
  closes before the `b`th open, then `r` is nondecreasing,
  `0 <= r_b <= b-1`, ko says `r_b=b-1 => r_{b+1}=b-1`, and
  `pi_a pi_b` is disjoint exactly when `a <= r_b`.  This is an iff
  parametrization, including the unique terminal-pass case, rather than a
  schedule heuristic.  It also pins a new causal no-go: for one four-vertex
  block with fixed opening order `(a,d,b,c)`, an attacker prunes the five-point
  threshold lattice to a four-point square with affine moment
  `ac + span{ab}`, excluding zero.  The omitted fifth point is exactly the
  zero-moment correction.  Hence no proof can contract each opening
  permutation independently; opening-permutation branches must interact.
- The tempting Eulerian restriction is now proved to contain the whole
  even-board kernel.  Given any even graph `H`, add `x,y`, the edge `xy`, an
  odd neighbourhood `A` at `x`, and neighbourhood `A triangle O` at `y`, where
  `O` is the odd-degree set of `H`.  The enlarged graph is Eulerian, and from
  `Q=(x,y)` an odd close of `x` forces the odd close of `y`, leaving exactly
  the root game on `H`.  Thus universal Eulerian ordered-pair safety would
  prove universal even-board safety, and any counterexample to the latter
  lifts two vertices higher.
- Eulerianity nevertheless supplies a real higher-dimensional structure.  For
  adjacency cochain `B`, the odd-triple curvature
  `tau(i,j,k)=B_ij+B_ik+B_jk` is a 3-oik: every two-vertex wall lies in an even
  number of odd triangles.  It always has a coherently oriented integral
  multiset lift, and the queue phase-rotation defect is exactly its room parity
  over the matching fan.  Ordinary complementary pivoting still has the wrong
  boundary: its paths pair endpoints (even augmentation), while the desired
  response chain has odd augmentation, and attacker pruning destroys even
  wall incidence.  The precise missing theorem can therefore be named as a
  relative, strategy-pruned, charge-decorated 3-oik contraction.
- The exact Euler target is now smaller and cleaner than graph-free affine
  cancellation.  If a fixed attacker's response scores form `a+W`, then it is
  harmless on every Euler graph exactly when `(a+W)` meets the cut space;
  after choosing a front `f`, equivalently `0` lies in the affine hull of the
  quotient scores `T_f D(h)`.  A proposed requirement that response
  differences span all even cycles is false already at four vertices: for
  even order the bicycle directions `Cycle intersect Cut` are invisible to
  every Euler adjacency cochain.  Thus the correct missing object is an odd
  response flow with **cut-valued** terminal moment.
- The ambient Euler complex has a complete dichotomy.  Unless the graph is a
  disjoint union of two odd cliques, it has a three-vertex set spanning an
  even number of graph edges.  That single triangle `F` has odd augmentation
  and `<delta B,F>=0`, while its three-edge boundary `R` has `<B,R>=0`.
  The exceptional two-clique family is already solved: every partition into
  pairs satisfies the parity-cell theorem, including every prescribed
  initial pair.  Hence the unresolved step is no longer existence of an odd
  zero-curvature chain, but promotion of one compatible triangle through a
  deterministic attacker's pruning without losing odd augmentation or the
  cut-valued boundary.
- The corresponding wall parity has a local game form.  At an Eulerian
  ordered pair \`(x,y)\`, colour each remaining vertex by
  \`tau_xy(v)=Bxy+Bxv+Byv\`.  Both fibres are even, so after an attacker opens
  \`z\` the same-colour reply set excluding \`z\` is odd; every such reply
  \`w\` makes the immediate consecutive closes of \`x,y\` carry equal
  charges.  This is an honest odd 3-oik wall fan, but it does not survive
  attacker pruning: the pinned open-completion witness has all OPEN children
  losing and a phase-changing CLOSE as its unique safe reply.  The missing
  chain must mix strategy-selected OPEN and CLOSE children across front
  levels.
- The wall fan now has a genuine strategy-pruned extension while its ordered
  front remains fixed.  If both fibres of
  `eta_xy(u)=B(x,u)+B(y,u)` are even, every attacker OPEN branches over the odd
  set of remaining same-`eta` replies; when the attacker closes `x`, the
  responder closes `y`.  This transports odd augmentation through arbitrarily
  many OPEN rounds with zero scalar charge.  Its exact residue is the
  Eulerian, `B`-isotropic chain `kappa_xy(U)=sum_{u in U}(xu+yu)`.  For queued
  two-cells `P_i`, the prefix identity
  `sum_{i<=k} K(P_i,U) + sum_{i<=k<j} K(P_i,P_j) = delta(A_k)` converts that
  residue into cross-cell four-cycles.  A pinned Euler example has canonical
  exit imbalances `0,0,1`, so aggregate next-front balance is false; the
  four-cycle defect must be transported through later matching-phase pivots.
- Cell-cut transport is exact but not Markov.  The graph6 pair
  `Fz{ZG`/`FBp[?`, at the same checkpoint
  `Q=(6,1,5,4), U={0,2,3,d}`, agrees on every individual queue charge,
  homogeneous full-degree colour, cell defect, cross-cell parity, and formal
  cell-cut chain, yet the first state is unsafe even for terminal-score play
  and the second is zero-normalized safe.  The unsafe state is itself a
  canonical balanced-wall exit of an Eulerian ten-vertex extension.  Hence a
  proof must retain vertex-resolved continuation spaces and cancel across
  wall siblings before or during the next front; it cannot recurse on an
  aggregated cell state.
- The front filtration has an exact Schur-complement obstruction.  After an
  odd chain cancels the first-front untouched indicator `p_f`, its residual
  class is `[W_f(c)]` modulo moments of even chains in
  `ker(augmentation,p_f)`.  Real OC/CO phase diamonds send the edge `fz` to
  the next cut star, and their shifts create rooted triangles.  A minimal
  four-real pair realizes a genuine triangle first differential.  More
  sharply, an odd three-history chain cancels both the first cut and the
  triangle quotient but leaves the nonzero next-front cut `13+23`; its leaves
  occupy different residual phases, so the initial cut contraction cannot be
  reapplied childwise.  Ambient `delta^2=0` is therefore not a
  strategy-relative two-layer contraction.
- Complete pass-free histories also have a response-factor normal form.  Pair
  each coin's OPEN/CLOSE events and pair each attacker move with the following
  defender response.  The two matchings form alternating cycles when the
  defender moves second, or cycles plus one path when the defender moves
  first.  If a forced pass occurs, delete its whole terminal singleton macro
  and mark that zero-charge vertex outside the prefix factor.  Zero
  normalization is exactly the condition that every response edge is
  charge-balanced.  With the isolated dummy, exact minimax certifies that such
  factors exist for both seats on the complete graph census through eight real
  vertices; this remains a tested conjecture.  The precise open statement is
  now a **causal charge-balanced factor-extension theorem** under arbitrary
  attacker pruning, allowing an unmatched untouched defect endpoint until a
  legal phase pivot absorbs it.
- The strategy semantics is now two-sided in Lean.  `formal/Ogdoad/Fifo.lean`
  defines an explicit odd-forcing tree `OddWins`, proves finite determinacy and
  incompatibility with `EvenWins`, and exposes the pointwise target as exact
  counterstrategy exclusion.  It also proves the singleton-untouched terminal
  corridor: scan the even queue in pairs; a front bit zero is absorbable, while
  a front bit one must be followed by one before the scan continues.  This
  closes the terminal tail inside the proof kernel, but not the step which
  forces an arbitrary pruned strategy into that tail.
- A new unbounded family rules out repairing the missing step by tracking a
  bounded number of queue defects.  For any `r >= 1`, take
  `Q=(x1,y1,...,xr,yr)`, `U={a,b,d}`, and edges `xi-a`, `yi-b`, with `d`
  isolated.  Every queued cell initially has charge `11`.  After attacker
  `OPEN(d)`, a normalized defender must open `a` or `b`; either choice turns
  all `r` old cells simultaneously into `01` or `10`.  Nevertheless the
  branch is safe: the complementary `OPEN` and zero front `CLOSE` form a
  two-switch square, after which `U` is empty.  Thus clean matchings, one
  transported defect, monotone defect position, and any uniformly bounded
  defect count are all false induction objects.  A valid repair forest must
  recognize a factored terminally absorbable defect fan, not enumerate local
  defects.
- One genuinely unbounded attacker subclass is solved for all orders and both
  seats.  If the attacker always closes whenever legal, defender histories
  realize complements of Hamiltonian paths or path squares.  Affine separation
  shows their traces contain the complete real graph; when the first attacker
  opener is the dummy, a controlled second block supplies isolated-vertex plus
  Hamiltonian-path traces and repairs the otherwise false one-block span.
  Conversely, forcing the defender to OPEN whenever untouched vertices remain
  is false already on `K4+dummy` and `(K4-e)+dummy`: the winning unrestricted
  repair is a phase-changing front CLOSE.
- The broad prevention/debt menu also has a sharp block boundary.  A maximal
  FIFO block with opening order `v_i`, residual `S`, and threshold `t_i`
  scores `e(B,S)` plus the internal edges `v_i v_j` with `j>t_i`.  It ends in
  odd debt exactly when its last odd close belongs to the attacker.  On the
  path `a-f-u` plus isolated `d`, the legal line
  `O_a,O_d,C_a,C_d,O_f,O_u,C_f,C_u` reaches the terminal residual-`K2` debt
  trap; the losing fork is replying to the odd-degree opener `a` with the
  dummy.  Degree-matching repairs this two-close fork, but does not yet control
  longer blocks.  Hence the potential `debt + e(queue,U)` and fixed-front
  descent do not by themselves prove the menu globally.
- Even a tempting dynamic splice is false.  On
  `01,02,03,04,05,06,12,13,14,17,23,26,27,35,37,56,57`, the safe checkpoint
  `Q=(4,3), U={0,1,2,5,6,7}` has the following property: after attacker
  `OPEN(6)`, the unique safe normalized reply is `CLOSE(4)`.  All five OPEN
  replies lose.  Hence “a safe even-U state always has a safe OPEN
  completion” cannot lift a residual strategy through a dummy/suspension
  prefix; phase-changing OC branches are essential.
- Time reversal does preserve the disjointness vector on pass-free complete
  schedules, but it is not a strategy contraction.  It swaps seats, becomes
  anti-causal after reconvergent branches, and moves the unique terminal pass
  to an illegal pass immediately after the initial opening.  The minimal
  commuting diamond
  `C_f;OPEN(x)` versus `OPEN(x);C_f` differs by the edge coordinate `fx`;
  diamond-symmetrizing its two leaves has even augmentation.  A valid affine
  certificate may be one nonsymmetric leaf, so requiring diamond symmetry would
  destroy exactly the odd augmentation the theorem needs.
- Globally, pass-free reversal is fixed-point-free once at least two vertices
  remain.  Every reversal-invariant chain is therefore an orbit sum and has
  `(augmentation,D)=(0,0)`, never the required affine `(1,0)`.  Erasing the
  dummy is not a copycat escape: it can create a ko-illegal word, assign two
  consecutive projected events to the same controller, or require a
  state-dependent pass.  Reversal averaging and dummy projection are thus
  proved no-go templates, not candidate contractions.
- The cut boundary of a terminal response has an exact controller formula.
  If \`o_v,c_v\` are the OPEN/CLOSE positions among the \`2n\` touches on all
  real vertices plus dummy, then
  \`deg_Dhat(v) = n + o_v + c_v (mod 2)\`.  On the real edge space this
  becomes \`deg_D(v) = n + o_v + c_v + Dhat(v,d)\`, or, after formally
  deleting the two dummy events,
  \`deg_D(v) = k + obar_v + cbar_v\`.  Thus constant-coefficient topology
  misses an endpoint-controller local system coupled to whether the real
  interval overlaps the dummy.
- That formal deletion has a sharp ko wall.  The score-zero diamonds
  \`OPEN(d);CLOSE(f)\` and \`CLOSE(f);OPEN(d)\` commute statewise except when
  \`f\` is the singleton front; there they end with opposite ko bits.  The
  minimal word \`O0 Od C0 O1 Cd C1\` has real label \`01\`, but dummy
  deletion gives the illegal \`O0 C0 O1 C1\`, and the only legal same-order
  repair \`O0 O1 C0 C1\` has label zero.  A pass is illegal while \`1\` is
  untouched.  Hence a dummy-as-role-switch normalization cannot be repaired
  causally without transporting a genuine edge moment.
- The dummy defeats the empty-queue domination device at every root, matching
  the no-dummy Bad-graph census 1/4/34 at n = 3/5/7 (all mover-controlled),
  but that device is not the unique local squeeze. On the path `z-f-y-h`,
  state `queue=(f,h), U={y,z}` has an even front and no safe move: either
  open makes f odd, while closing f exposes odd h. The isolated dummy kills
  this squeeze while untouched, but once queued or spent it becomes exactly
  the recursive repair-potential problem.
- The debt corridor is locally well founded at a fixed front.  If the front
  has positive even untouched degree, opening a neighbour either lets the
  debt be discharged within the next round or forces the attacker to open a
  second neighbour, reducing that degree by exactly two.  The potential
  `H = debt + e(queue,U)` is invariant under every close, and `debt=1,H=0`
  rules out a singleton anticomplete firewall.  But opens change `H` by their
  full live-degree parity, and deleting the firewall shifts the queue front;
  neither fact supplies the missing global induction.
- Even retaining the ordered queue graph, every untouched vertex's full
  adjacency word into the queue, and its internal-degree parity is
  insufficient.  The proved five-active-vertex pair
  `queue=(0,1), U={2,3,4}` with edge sets `{23,04,14}` and
  `{23,24,02,12}` has the same signature multiset
  `{(00;1),(00;1),(11;0)}`, but the first state is zero-normalized safe and
  the second is unsafe.  Any adequate smaller state quotient therefore needs
  at least one further moment of adjacency correlations among untouched
  fibres; which moment closes the recurrence remains open.
- The earlier no-dummy heuristic also needed correction at order eight.  Seven
  exact classes are anti-mover-controlled: the second player can force either
  declared target parity, so the initial mover cannot always force even.  The
  narrower statement that the second-seat even player wins every even-order
  no-dummy board survives the finite screen but remains unproved.  This is not
  used as evidence for the isolated-dummy theorem.

The naturality dichotomy:

- **Tier 1: frame-blind, `G >= Sp(B)`: no.** If the move relation is invariant
  under the full symplectic group of the polar form, its P-set is a union of
  `Sp(B)`-orbits. In dimension at least 4, `Sp(B)` is transitive on `V \ {0}`, so
  invariant subsets are only `empty`, `{0}`, `V\{0}`, or `V`. These are not
  nondegenerate quadrics. Degenerate Gold forms require care because the no-go
  only constrains the nondegenerate core `V/R(B)`.
- **Tier 3: per-`x` evaluator circuit: yes, but tautological.** The circuit
  `Q_a(x) = Tr(x*x^(2^a))` is a fixed Galois-symmetric circuit of game operations,
  and Frobenius permutes its summands. Realized as a disjunctive sum of those
  subgames with inputs driven by `x`, its P-condition is exactly `{Q_a = 0}`.
  That is more structured than a lookup table, but the form is still fed in rather
  than produced by autonomous play.
- **Tier 2: fixed-rule middle: resolved.** Weighted-source Witt--FIFO is one
  q-blind structural rule for every `x`: it uses a public Witt frame, matched
  source pairs, singleton-local transition weights, and a phase-aware terminal
  claim. Its ordinary normal-play P-set is `{Q_a = 0}`. The transcript-span
  theorem gives the exact invariant boundary: dense inputs cannot have a
  constant total outcome certificate, and the construction's active singleton
  support attains the necessary span.

The extraspecial-group reframing (interpretation; explains the misère obstruction):

A characteristic-2 quadratic form `Q` on `V = F_2^n` with polar form `B` is **the same
data as an extraspecial-type central extension**

```text
1 -> Z/2 -> E -> V -> 0,
```

whose commutator pairing is `B` and whose **squaring map** `x -> x^2` (landing in the
center `Z/2`) **is** `Q`, because `(xy)^2 = x^2 y^2 (-1)^{B(x,y)}` gives
`Q(x+y) = Q(x) + Q(y) + B(x,y)` for free. The Arf invariant is exactly what classifies
the two extraspecial 2-groups of order `2^{1+2n}` (the `D_8`-central-product "+" type
versus the `Q_8`-central-product "-" type). This is standard math — the Heisenberg /
Weil-representation picture, adjacent to the already-built Bridge I (`weil_s`/`weil_t`).

It bites on the misère probe. `experiments/misere_kernel.py` found that on `R8` the
kernel `K = (Z/2)^2` and `P cap K` is **linear** — the genuine misère P-element lies
outside the group where a vector-space quadric framing applies. The reframing **predicts
that obstruction**: a misère quotient is a *commutative* monoid, so its unit group is
abelian, hence its intrinsic commutator pairing is trivial, hence its squaring map can
realize only the **split** refinement (`B = 0`, `Q = 0` on that part). A *nondegenerate*
`B` — which a Gold form has on its nonsingular core — is the commutator pairing of a
**nonabelian** extraspecial group and therefore **cannot** arise from any abelian
structure's own multiplication. So the linear obstruction is forced, not unlucky, and the
quadratic datum `q_i = Q(e_i)` must enter from a genuinely **noncommutative** source —
which, in game terms, is the one structural noncommutativity normal/partizan play has and
the symmetric polar form `B` discards: the **first-/second-player asymmetry** (the
directedness of the move relation).

This yields a candidate **Tier-2 naturality criterion** strictly between the two solved
tiers: require the rule to realize the *extraspecial squaring map* of `B` — equivariant
under the extension `E`, **not** merely under `Sp(B)`. That sits properly between
frame-blind `Sp(B)` (Tier 1, the no-go) and direct `Q_a`-evaluation (Tier 3,
tautological), because `E` is a proper central extension of `V`: it carries the `q_i`
data structurally without being a `Q`-evaluator. Status: developed into the Tier-2
screen and no-go ladder of `writeups/goldarf.tex` §§5–6. The resolved rule uses
that extension data covariantly in play rather than as an invariant lookup.

Closure of the former progress targets:
- ~~Adversarially verify or refute the `echo`-`fifo`+dummy `m = 8` exactness
  claim~~ — **done, CONFIRM** (2026-06-10; `experiments/echo_solver.py`, record
  in goldarf §8). ~~Recast forced charge into normal play~~ — **done** by the
  local claim-lantern compiler, kernel-checked for arbitrary finite payoff
  trees. The weighted-source construction supplies the all-dimension charge
  theorem needed at its input.
- The **arbitrary-graph general-n linking theorem** is now a strict optional
  generalization rather than a Gold obligation. The conjecture, reduced in
  2026-06-10 and sharpened in 2026-07-20, asks whether the odd-close parity
  game on any graph with an isolated coin forces an even flip count from both
  seats. Verified for all 12,346 classes at k = 8 real coins plus dummy
  (`experiments/linking_game.py`). The old R3/D3 induction fails first at
  `GCRU]w`; the live route is the block-turn plus live-degree-pairing
  formulation, with FIFO re-entering through forced front deletion and the
  proactive-debt witnesses above.  Balanced-front odd-flow transport and the
  complete close-first contraction are now proved.  Strategy-tree-relative
  minimum extraction and its neutral-tail/Eulerian consequence are now
  kernel-checked as well.  Dual descent reduces a
  hypothetical counterexample to an isolated odd/odd CLOSE spike or an
  after-dummy ko-protected universal-neighbour singleton, but the current exact
  target remains the global affine-contraction/causal-factor-extension lemma
  of `writeups/linking_affine.tex`, with the FIFO cut-space filtration as a
  coordinate system rather than a childwise induction.
  Its global affine-contraction lemma remains open, but a proof would strengthen
  FIFO combinatorics rather than the Gold result.
- ~~Repair or replace the anti-evaluator screen~~ — **done as a boundary
  theorem, not another N3**. Exactness forces transcript observations to span
  the input; constant total observation is impossible. Unavoidable fork
  padding proves that the basic reachable, optimal, and unavoidable
  strategic-liveness repairs remain decoration-vulnerable.
- ~~Exhibit the fixed uniform local rule~~ — **done** by weighted-source
  Witt--FIFO, with q-blind statics, `(w0,c)=(1,1)` transitions, the optimal
  singleton observation support, and ordinary normal-play P-set `{Q=0}`.
- ~~Construct an Artin--Schreier source for every Gold diagonal~~ — **done** by
  the half-field descent theorem and `gold_diagonal_artin_schreier_source`, for
  every exponent and every supported tower through `m = 128`.
- Family-boundary sweeps, Frobenius-aware enumeration, conjugation rules, and
  the Plambeck--Siegel regularity check remain useful historical calibrations,
  not conditions on the existence theorem.

Relevant surfaces:
- `writeups/goldarf.tex`
- `writeups/gold_diagonal_source.tex`
- `writeups/linking_affine.tex`
- `formal/Ogdoad/GoldDiagonal.lean`
- `experiments/open_question_probe.py`
- `experiments/framing_obstruction.py`
- `experiments/gold_family_survey.py`
- `experiments/misere_kernel.py`
- `examples/interactive_kernel.rs`
- `examples/loopy_quadric.rs`
- `examples/bent_route.rs`
- `src/forms/quadric_fit.rs`
- `src/games/kernel.rs`, `src/games/misere.rs`, `src/games/loopy/`

### ~~tisn·(e_g∧e_c∧e_f): `quadratic deformation of the game exterior algebra`~~ — resolved

**Resolved 2026-08-09**
([`writeups/game_exterior_divisibility.tex`](../writeups/game_exterior_divisibility.tex)).
The answer is negative for a quadratic datum that genuinely belongs to game
values rather than to one hand-chosen presentation.

The exact naturality contract is **ambient coherence**: a datum is defined on
the full additive group of short games, or on finitely generated subgroups with
injective structure maps along every inclusion.  Moews's structure theorem gives

```text
ShUg ≅ ⊕_N Z[1/2] ⊕ ⊕_N (Z[1/2]/Z),
```

and every torsion short game has power-of-two order.  Thus multiplication by
the order `n` of a torsion game is surjective.  If `nt=0`, choose `ny=t` and
`nz=x`.  For any additive grade-one realization `i` in an associative ring,

```text
n²y = 0,
i(t)² = (n i(y))² = (n² i(y)) i(y) = 0,
i(t)i(x) + i(x)i(t) = 0.
```

If the coefficient ring injects into the Clifford quotient, its square and
polar relations therefore force

```text
Q(t) = 0,
B(t,x) = 0  for every x.
```

This is coefficient-independent: characteristic two, `Z/4`, and every other
commutative coefficient target collapse alike.  Consequently every ambient-
coherent faithful datum factors through `ShUg / Tor(ShUg)`.  The local escape
`e_*²=1` over `F_2` survives only because `⟨*⟩` omits a partizan half `h` with
`2h=*`; it cannot survive an injective enlargement.  Likewise the nonzero Gold
forms on the nimber field-like core cannot extend coherently to general games.

This resolves the original distinction:

- `GameClifford::with_quadratic_data` remains a valid checked engineering API
  for hand-supplied data on one root-incomplete subgroup.  Such a table is not
  game-native because its value depends on the ambient subgroup.
- Mean-value and atomic-weight squares remain valid on torsion-free directions;
  the theorem predicts that they factor through the torsion-free quotient.
- A directed/noncommutative outcome construction changes the algebraic object
  rather than deforming the commutative-scalar `GameExterior`; the weighted-source
  FIFO rule now supplies that separate `tis` construction, not a residual `tisn`
  deformation.

The abstract ring proof and coefficient-valued corollaries are kernel-checked
in `formal/Ogdoad/GameExterior.lean`; Moews's short-game group theorem remains
an explicit source-pinned input, not a Lean axiom.

Relevant surfaces:
- `writeups/game_exterior_divisibility.{tex,pdf}` (complete proof and boundary)
- `writeups/game_exterior_deformation.tex` (the earlier local two-gate analysis)
- `formal/Ogdoad/GameExterior.lean`
- `src/games/game_exterior/` (`lambda.rs`, `clifford.rs`)

### on·e_s: `ordinal nim multiplication beyond the verified excess table`

**Status:** open. The proof source of truth is
[`writeups/excess.tex`](../writeups/excess.tex); this entry is the concise
research ledger and implementation boundary.

#### Problem

For an odd prime \(p\), Conway's Kummer carry below
\(\omega^{\omega^\omega}\) has the form
\[
\alpha_p=\kappa_{f(p)}+m_p,\qquad f(p)=\operatorname{ord}_p(2),
\]
where \(m_p\) is Lenstra's finite *excess*. Lenstra proved structural lower
bounds and conjectured absolute boundedness. Every source-pinned row presently
available is consistent with the sharper rule
\[
m_p=
\begin{cases}
0,&\mathcal Q(f(p))\text{ is not a singleton odd prime-power},\\
4,&f(p)=2\cdot3^k,\ k\ge1,\\
1,&\text{otherwise}.
\end{cases}
\]
This \(0/1/4\) rule is not proved.

#### Exact reduction

The paper proves that the rule is equivalent to four universal order
statements. They are the permanent coordinates for this problem:

| arm | exact assertion | proved so far | universal gap |
|---|---|---|---|
| \(Z\): zero | the structural norm of \(\kappa_h\) generates the full primitive-support quotient for every non-ordinary component set | synchronized multicomponent phase; exact two-component resultant; nontrivial primitive support on the power-of-two two-spine family; complete \(h=12,24\); Dickson dichotomy, reverse-Dickson trace divisor, and exact Kummer-coset transport | generation when the primitive quotient is composite; arbitrary synchronized phase; exclusion of the selected transported coset in the singleton-even Conway-Fermat case |
| \(O\): ordinary odd spine | the selected projective class of \(\kappa_{r^a}+1\) has full primary order for every odd \(r\ne3\) | transverse norm; relative Hilbert-90 unit; signed conjugate-ball lower bound; mixed-Jacobi formulas; projective minimal polynomial and binary-section ancestry; tower-faithful common-section no-go | selected-minimal-polynomial nondivisibility at the unscaled Conway value for the smaller primary factors |
| \(C\): cubic | \(\gamma_k=\zeta+\zeta^{-1}\in\mathbb F_{2^{3^k}}^\times\) is primitive for every \(k\) | \(C_1,C_2,C_3\) analytically; exact norm tower; partition bound; cyclic-parity and block reductions; Singer--Wendt factorization; selected \(S_3\)-quotient, reciprocal order seam, and prescribed-trace character boundary | exclusion of the recursively selected Wendt/trace fibre, equivalently the extra proper-subproduct relation, at the smaller current factors |
| \(D\): exceptional | \(\Psi_k\mid\operatorname{ord}(M_k)\) for every \(k\), with \(\Psi_k=\Phi_{2\cdot3^k}(2)/3\) | corrected norm; exact current-factor/Capelli forms; quadratic-twist antiunit; partition bound; mixed-Jacobi flatness and binary cyclic-parity equivalences; half-block norm and selected-trace form; selected reciprocal sextic and complete cubic Dickson-factor boundary; universal cubic-shape no-go and selected absolute-trace fingerprint | exclusion of the explicit recursively selected cubic from the Dickson factor list at the smaller current factors |

The reduction is a theorem. None of the four universal assertions is claimed
complete.

#### Shared finite-field criterion

If the candidate translate
\(\beta=\kappa_{f(p)}+m\) lies in \(\mathbb F_{2^E}\), then it has no
\(p\)-th root exactly when
\[
\beta^{(2^E-1)/p}\ne1,
\]
equivalently when \(\operatorname{ord}(\beta)\) contains the full
\(p\)-primary part of \(2^E-1\). Reducing this to
\(p\mid\operatorname{ord}(\beta)\) is valid only when
\(v_p(2^E-1)=1\). The correct valuation is
\[
v_p(2^E-1)
=
v_p(2^{f(p)}-1)+v_p(E/f(p)).
\]
Thus both base-2 Wieferich behavior and a factor of \(p\) in \(E/f(p)\)
must be retained. Relative norm to \(\mathbb F_{2^{f(p)}}\) gives the
exact smaller-field power test.

#### What the four arms now say

- **\(Z\), multicomponent phase.** Componentwise norms lose a synchronized
  Frobenius phase. The paper retains that phase exactly, expresses the
  two-component case by a resultant over the intersection field, and proves
  primitive support for a power-of-two two-spine family. The associated
  Hilbert-90 cross-ratio is exact, but the first divisor comparison has degree
  up to \(2r-2\); it does **not** imply the formerly claimed \(2^r-1\) order
  bound. That invalid bound has been removed.

- **\(Z\), singleton-even chain.** The condition is precisely maximal order of
  the Conway class in the quadratic quotient:
  \(\delta_n=F_n=2^{2^n}+1\). Fibotomic, resultant, elliptic, Kummer-cover, and
  generalized-Jacobian formulations all reduce to the same distinguished
  Miller-unit value. They prove that degree, trace, norm, quarter-turn
  symmetry, and the full natural boundary-character package do not decide
  nonvanishing. The exact \(\ell\)-root descent now shows that even the full
  lower trace/norm ancestry and the maximal predecessor order survive a
  hypothetical failure automatically; the top step is equivalent to one
  explicit Dickson power-sum equation. Its degree-\(\ell\) Dickson
  polynomial has an all-or-nothing factorization: it splits completely on
  failure and is irreducible on success, with an exact resultant and
  absolute Capelli composition. A reverse-Dickson transform gives a sharper
  exact criterion: failure occurs precisely when an explicit absolute norm
  polynomial containing the selected minimal polynomial of \(a_{n-1}\)
  divides the trace-one polynomial
  \(1+\sum_{j=0}^{2^n-1}Z^{2^j}\). On success that norm polynomial is one
  irreducible; on failure it is exactly \(\ell\) full-degree factors. The
  resulting root count and long leading-coefficient gap are both compatible
  with every composite Fermat case. More exactly, the trace-one hyperplane is
  the inversion quotient of the norm-one torus, and the reverse-Dickson
  factor is literally one multiplicative \(\mu_\ell\)-coset transported
  through that quotient. Its fibotomic support is explicit and has automatic
  capacity. Thus derivatives, root sums, coefficient gaps, and support are
  all realized by nonselected cosets: this is a selected-factor reduction,
  not yet a contradiction.

- **\(O\), ordinary odd spines.** These now have a structural theory: a
  projective quotient, a selected relative cyclotomic unit, and a signed
  conjugate-ball sieve. The missing theorem is full order at the remaining
  small primary factors. The unweighted reciprocity orbit cancels not only for
  the second argument \(2\), but for every selector from the base cyclotomic
  field. A Teichmuller-weighted product formula proves that pure
  \(\mathbb Q(\mu_p)\) selectors cancel as well; mixed Jacobi sums escape
  that cancellation and recover the target as one exact inverse-Fourier
  coefficient, but its local \(p\)-adic phase is the original unresolved
  Kummer datum. Equivalently, the selected relative unit has an explicit
  degree-\(r\) projective minimal polynomial, and failure means that all
  nonconstant binary sections of \((1+x)^{\mathcal L_{r,a}/p}\) vanish at
  \(x_{a-1}\). Descending the ancestry makes this simultaneous divisibility
  by the actual Conway minimal polynomial \(P_{\alpha_r}\). Relative norm and
  submask complementation are automatic on that pattern, so only the selected
  nondivisibility can close the arm. A character-sum construction makes the
  point sharp: complete irreducible \(r\)-power towers with smooth exact
  degree, the same bottom Kummer coset, matched multiplicative order, all
  section divisibilities, and full Wieferich-safe bookkeeping can fail
  abundantly. Only the unscaled Conway scalar remains distinguished. The
  table value \(m_{359}=1\) is known from A380496;
  what remains open at that row is an independent analytical evaluation of
  its selected trace/resultant phase.

- **\(C\), cubic spine.** The norm recursion carries old factors, while each
  level introduces a new factor \(\Phi_{3^k}(2)\). The paper proves the first
  three levels without order computation and gives several exact
  reformulations and lower bounds. The derivative regulator is rigorous but
  circular: its reduction is a power of the same unknown Gaussian period. An
  exact counterexample also shows that the polynomial coefficient recursion
  can carry a primitive irreducible input to an irreducible but nonprimitive
  output, so primitivity is not a formal inductive invariant. A new cyclic
  group-algebra reduction makes failure equivalent to a sharp subset-sum
  parity pattern: every residue modulo \(3^{k+1}\) occurs oddly except one.
  In the augmentation ideal this is an extra proper-subproduct relation;
  the full Frobenius product and its immediate \(\ell\)-th-power exponent
  consequence are unconditional, so they cannot supply the contradiction.
  A block compression now proves that submask complementation forces the
  unique even residue into exactly the position required by failure. Failure
  is also equivalent to the distinguished minimal polynomial and its
  reciprocal translate occurring in a binary Wendt gcd. Every factor of
  that gcd has degree \(3^k\) and translation pairs the factors, so neither
  Wendt-factor existence nor reciprocal symmetry singles out the selected
  pair. More sharply, an exact Singer-difference-set factorization gives
  the coset-intersection moments; when
  \(\ell-1<\sqrt q+1/\sqrt q\), every coset necessarily contains
  degree-\(3^k\) Wendt factors. The selected pair descends under the free
  \(S_3\) action to the lower trace value
  \(\eta_{k-1}^2+\eta_{k-1}+1=\gamma_{k-1}^{-2}\). The descended
  elements satisfy an irreducible cubic with trace and norm equal to the
  preceding one, and their orders factor exactly as the preceding order
  times the current norm-one selector order. Thus this is a lossless
  reciprocal formulation, not an induction. Equivalently, failure is the
  extremal value \(3\) of one prescribed-trace character sum at
  \(\eta_{k-1}\). Other trace fibres genuinely attain \(3\), so a uniform
  Weil or character bound cannot exclude the selected fibre.

- **\(D\), exceptional spine.** The corrected \(m=4\) norm is
  \(N_k=\zeta^2+\zeta+\omega\), and the exact conjecture is current-level
  \(D'_k\), not cumulative propagation of all old factors. The quadratic-twist
  antiunit and partition regulator prove an explicit large-factor range.
  Semiprimitive Fourier data, line saturation, Dirichlet coefficients,
  relative Dickson forms, and proper-subfield norms are all compatible with
  failure. Mixed Jacobi sums now give an exact first-order formulation:
  failure is equivalent to simultaneous congruences
  \(J_j\equiv-1\pmod{(\zeta_\ell-1)^2}\) for the full composite-conductor
  family. Equivalently, binary submasks of \((2^{4\cdot3^k}-1)/\ell\)
  occur evenly in residue zero modulo \(15\cdot3^k\) and oddly in every
  nonzero residue; raising this identity to \(\ell\) is again automatic.
  The binary exponent splits into two equal blocks, turning failure into a
  quadratic norm equation. Its involution-fixed residue pushforward is
  unconditional, and Hilbert--90 gives no obstruction. The remaining
  selected \(\ell\)-th root is nontrivial exactly when one explicit relative
  trace to \(\mathbb F_{2^{3^{k-1}}}\) is nonzero. More sharply, the
  selected phase has an explicit reciprocal sextic over that field, and
  failure is equivalent to one named irreducible cubic dividing
  \(D_e\), where \(e=(2^{2\cdot3^{k-1}}-2^{3^{k-1}}+1)/\ell\).
  The exact factorization of \(D_e\) is \(Y(Y+1)^2\) times squares of
  irreducible cubics, so the ambient structure supplies many admissible
  false positives. Every one of those cubics has constant coefficient equal
  to the square of its trace coefficient, exactly matching the selected
  cubic. The selected remaining coefficients have absolute traces \(1\) and
  \(k\bmod2\), but the factorization supplies no contradictory coordinate
  identity. The cubic and exceptional current groups also have coprime
  orders, so their analogous torus formulations cannot transfer the result.
  Excluding the recursively selected cubic, not generic
  cubic-factor existence, is the remaining Kummer evaluation.

#### Evidence boundary

Use four distinct evidence levels:

1. **Proved theorem / cited theorem.** A written proof in
   `writeups/excess.tex` or an identified external theorem.
2. **Certified exact finite computation.** Exact arithmetic plus locally
   checkable factorization and primality information for the stated finite
   levels only.
3. **Source-pinned external value.** Imported from an identified maintained
   source, without an independent proof in this checkout.
4. **Consistent incomplete evidence.** All known factors or sampled rows pass,
   but an unfactored cofactor, unproved primality claim, or untested level
   remains.

Current evidence:

- The implementation vendors and row-diffs all \(126\) A380496 entries for odd
  primes \(3\le p\le709\). These *integer excesses* are source-pinned. The next
  unsupported carry is \(\alpha_{719}\).
- The contributor-linked extended A380496 auxiliary table reports
  \(m_{1093}=m_{3511}=0\), the two known base-2 Wieferich rows. The calculator
  uses Lenstra's exact \((2^E-1)/p\) power test, so these values assert full
  \(p^2\)-primary order rather than radical support. They are external exact
  computations, however: they are outside the approved 126-row b-file and
  carry no compact remainder certificate in this checkout.
- The resulting ordinal carry is independently value-checked only at the named
  subset documented beside the tower tests; table coverage must not be confused
  with per-row ordinal verification or practical constructibility.
- Cubic: \(C_1,C_2,C_3\) are theorems; \(C_4,C_5\) are locally certified;
  \(C_6\) is source-assisted because the local path has only probable-prime
  evidence for its 42- and 90-digit factors; \(k=7,8\) are consistent only,
  with unfactored cofactors.
- Exceptional: \(k=2,\ldots,5\) are locally certified; \(k=6\) is
  source-assisted because its 78-digit factor lacks a local certificate;
  \(k=7,8\) are consistent only, again with unfactored cofactors.
- The finite exception rows do not prove \(D'_k\) universally, and the finite
  cubic rows do not prove \(C_k\) universally.

#### Current proof targets

1. **\(Z\).** Exclude the selected reverse-Dickson divisor and thereby prove
   the Conway-Fermat quotient order \(\delta_n=F_n\); prove generation of the
   composite two-spine primitive quotient; then control the general
   synchronized phase.
2. **\(O\).** Prove that at least one selected binary section is nonzero
   modulo \(P_{\alpha_r}\) at every remaining small primary factor
   (equivalently evaluate \(\Theta_{q,s}\)).
3. **\(C\).** Exclude the extremal prescribed-trace value at the Conway
   fibre \(\eta_{k-1}\), equivalently prove that every current primary
   factor of \(\Phi_{3^k}(2)\) occurs fully in
   \(\operatorname{ord}(\gamma_k)\).
4. **\(D\).** Exclude the explicit selected cubic of
   `prop:dk-selected-sextic` from its Dickson factor list at every factor
   of \(\Psi_k\); equivalently prove the Capelli/antiunit condition \(D'_k\).

Exact-order and factorization runs remain useful for falsification and audits,
but they are not the leading proof route. A solution must exploit the
distinguished Conway/cyclotomic value, because the paper now proves that the
obvious generic invariants are insufficient.

Relevant surfaces:
- `formal/Ogdoad/Excess.lean` (proved reduction spine and the unproved
  `DPrimeTarget`; not a universal column proof)
- `formal/README.md`
- `writeups/excess.tex`
- `writeups/excess.pdf`
- `experiments/ordinal_excess_probe.py`
- `experiments/cyclotomic_3k_family.py`
- `experiments/exception_column_m4.py`
- `experiments/excess/` (archive; honor its per-file status table)
- `src/scalar/big/ordinal/tower.rs`
- `src/scalar/big/ordinal/b380496.txt`
- `src/scalar/big/ordinal/mod.rs`
- `src/scalar/AGENTS.md`

### ~~off·(e_f∧e_s∧e_c): `transfinite Arf/Witt classification for ordinal-nimber coefficients`~~ — resolved

**Resolved 2026-08-07** (`writeups/transfinite_arf.tex`).  Nothing replaces the
finite-field bit over the scalar world actually named by full `On₂`: Conway's
nimber field is algebraically closed of characteristic 2, so both Frobenius and
the Artin–Schreier map `wp(t)=t²+t` are surjective.  Hence

```text
On₂ / wp(On₂) = 0,
W_q(On₂) = 0.
```

Every regular finite-dimensional ordinary `(q,b)` quadratic form (`metric.a`
empty) over `On₂` is hyperbolic.  The
proof is constructive after choosing roots: on a symplectic plane

```text
Q(xe+yf) = a x² + xy + b y²,
```

algebraic closure supplies `t²+t+ab=0`; if `a≠0`, the vector `(t/a)e+f` is
isotropic (and `e` already is when `a=0`).  Split that hyperbolic plane and
induct.

The complete singular normal form is just as small.  If `rank(B)=2r`,
`dim(rad B)=s`, and `epsilon` records whether `Q` is nonzero on `rad B`, then

```text
epsilon = 0:  Q ≅ H^r ⊥ 0^s
epsilon = 1:  Q ≅ H^r ⊥ <x²> ⊥ 0^(s-1).
```

Indeed, on the radical `Q` has zero polar form, and perfection gives a unique
linear functional `ell` with `Q|rad = ell²`; a nonzero linear functional has one
coordinate after a basis change.  Thus the full-`On₂` classifier is exactly
`(rank, radical_dim, radical_anisotropic)`, with no Arf coordinate.  On regular
forms, the associated characteristic-2 Clifford/Brauer-Wall class is split
because the form is a sum of hyperbolic planes.  Singular Clifford algebras are
not graded central simple on this surface: a nonzero polar-radical vector becomes
a non-scalar homogeneous graded-central element.  Thus the radical flag is not a
Brauer-Wall coordinate.

The finite classifier remains correct, but **relative to its recorded ground
field**.  A class in
`F_{2^d}/wp(F_{2^d}) ≅ F₂` dies over `F_{2^(2d)}` because every
Artin–Schreier polynomial acquires a root there.  Therefore the directed colimit
of the finite-field Arf/Witt classes inside `On₂` is zero; a finite bit cannot be
promoted to a stable transfinite bit.

The apparent mathematical middle case was empty.  Every element below
`omega^(omega^omega)` is algebraic over `F₂` and has finite degree, so any finite
metric there lies in the common finite field whose degree is the lcm of its entry
degrees.  `ordinal_common_finite_subfield_degree` certifies this when the needed
excess data and checked degree arithmetic are available.  Elements beyond
that staged segment belong to the ideal full `On₂` semantics, where the theorem
above applies, but the partial backend need not claim an executable isometry when
the required square or Artin–Schreier roots escape its verified multiplication
window.

So the old four targets close as follows: the ideal full scalar domain motivating
`Ordinal` is `On₂`; the invariant collapses to the radical normal-form data;
algebraic closure proves root existence without requiring a new in-window oracle;
and every regular quadratic Clifford class is zero.  A classifier over the
coefficient-generated subfield `K` could instead return a relative class in
`K/wp(K)`, but that class is not generally a complete higher-dimensional isometry
invariant.  It would be a separately declared base-field problem, not a replacement
invariant of `On₂`.

Relevant surfaces:
- `writeups/transfinite_arf.tex`
- `src/scalar/big/ordinal/subfield.rs`
- `src/forms/char2/arf.rs`
- `src/forms/witt/{class,brauer_wall}.rs`
- `src/clifford/`

### ~~over·(e_f∧e_g): `the mod-8 spine in game semantics`~~ — resolved as an independent charge/invariant problem

**Resolved 2026-08-09**
([`writeups/brown_game_semantics.tex`](../writeups/brown_game_semantics.tex)).
The Brown four-class output introduces no independent nonlinear quadratic
datum beyond the ordinary characteristic-two problem, and it cannot extend as
a nonzero disjunctive-sum-natural colour of all short-game values.

For every Brown refinement

```text
q(x+y) = q(x) + q(y) + 2*b(x,y),   q : V -> Z/4,
```

there is a canonical, basis-free split

```text
ell(x) = q(x) mod 2,
q(x)   = lift(ell(x)) + 2*Q(x),
B_Q    = b + ell tensor ell.
```

Here `ell` is linear, `Q` is an ordinary `F₂`-quadratic form, and `B_Q` is
alternating.  Conversely every such pair `(ell,Q)` gives a unique Brown form.
The four residues are exactly the synchronized terminal-label pair

```text
q = 0,1,2,3  <->  (ell,Q) = (0,0),(1,0),(0,1),(1,1).
```

The phase keeps the correlation rather than only the two marginal biases:

```text
G(q) = ((1+i)/2) W(Q) + ((1-i)/2) W(Q+ell),
W(R) = Sum_x (-1)^R(x).
```

For nonsingular `b`, this gives complete ordinary-quadratic formulas.  In even
dimension, if `B_Q(a,-)=ell`, then
`beta = 4*Arf(Q) + 2*Q(a) mod 8`.  In odd dimension,
`rad(B_Q)=<w>`, `ell(w)=1`, and
`beta = 4*Arf(Q|ker(ell)) + 1` or `+7` according as `Q(w)=0` or `1`.
Degenerate forms retain the existing radical rule: a nonzero `Q` on
`rad(b)` cancels the full Gauss sum; otherwise the pair descends to the
nonsingular quotient.

The exact semantic contract is a **synchronized charge/output** contract:
binary terminal-charge channels on the same loaded input may be paired and
deterministically relabelled.  Under that contract a Brown readout is
observationally exactly `(ell,Q)`. Once `ell` is supplied its linear channel
has the standard local XOR realization, and the weighted-source Witt--FIFO
theorem now supplies the nonlinear normal-play bit. On the doubled Gold slice
`ell=0`, `q=2Q`, this is the resolved `tis` construction. This is not a
factorization of game trees and does not construct a single canonical
normal/misère/loopy four-way outcome; demanding that internalization remains
the distinct residual Brown semantic boundary.

There are two complementary no-gos/corrections.

- Moews gives `ShUg = 2*ShUg`.  Any inclusion-compatible Brown-law family on
  finitely generated short-game subgroups has `b=0` after adjoining halves,
  then `q=0` after adjoining quarters.  Thus no nonzero Brown module is an
  additive quotient of the full short-game group.  This does **not** kill the
  intrinsic root-incomplete subgroup `ShUg[2]`, which contains `*` and admits
  local Brown tables.
- A bare `Z/4`-central extension does not determine a Brown form.  The abelian
  sequence `Z/4 -> Z/8 -> Z/2` gives `q(1)=1` or `q(1)=3` according to the
  chosen lift, with phases `1` and `7`.  A section/phase framing is essential;
  the old `Z/2` extraspecial abelian obstruction does not lift verbatim.

The canonical split, converse, global two-divisible collapse, and `Z/8`
sharpness model are kernel-checked in `formal/Ogdoad/BrownGame.lean`.  Moews's
short-game classification remains an explicit source-pinned input, not a Lean
axiom.  Bridge M itself remains shipped and unchanged in
`src/forms/char2/brown.rs`; the lattice identity `beta = signature mod 8`
remains standard-math infrastructure, not a claim that games compute lattice
signatures.

### ~~under·(e_g∧e_s): `thermography ↔ Newton polygons: one tropical object or two?`~~ — resolved

**Resolved 2026-07-20: two objects, with a substantive filtered shadow.**  The
project's two tropical consumers — thermography (`MaxPlus`, the games axis) and
the valuation/Newton-polygon stack (`MinPlus`, the place axis, Bridge J) — cannot
be one faithful Newton-style dyadic graded ring.  The exact closure is in
`writeups/thermo_newton.tex`; the implementation record lives in `docs/DONE.md`.

Why this was research:
- On the place axis the valuation axiom `v(x+y) >= min(v(x), v(y))` makes Newton
  polygons additive under multiplication (Dumas), and passing to the graded ring
  `gr_v` "freezes" leading terms; `scalar/newton.rs` plus the Springer tests pin
  the slopes to the valuation layers. The question is whether the game axis has a
  genuine peer of that structure or only the scalar shadow of it.
- The sign mirror `MinPlus ↔ MaxPlus` is a convention flip, not content. Content
  would be a single statement instantiating to "slopes = root valuations" on the
  place axis and to a thermographic fact (masts/temperatures of a one-parameter
  family) on the game axis. This pass found that the obvious candidate — the
  thermograph as a sum-compatible tropical object — provably fails, and replaced
  it with a sharper target.

The closed program state (2026-07-20 — `writeups/thermo_newton.tex` +
`experiments/under_descent.py`): a negative theorem at the thermograph level,
an unrestricted associated-graded obstruction, a positive exact descent theorem
for every numeric Norton unit, and two final no-go theorems excluding a faithful
dyadic-unital ring and a multiplicative Norton scalar action.

- **The thermograph is not a sum invariant (proved).** `G ↦ Th(G)` is not a
  congruence for disjunctive sum: no operation taking only `Th(G)` and `Th(H)` can
  return `Th(G+H)` for all short games. The witness sits in the temperature-zero
  layer — `Th(*) = Th(↑)` (both constant-zero walls, mean `0`, temp `0`), yet
  `* + * = 0` is a cold number while `↑ + *` stays a non-number of temperature `0`.
  So `(mean(G), temp(G))` **cannot** be the game-side analogue of `(ac(x), v(x))`:
  it forgets the leading thermic residue that decides cancellation. The Dumas
  additivity of Newton polygons has no thermograph-level mirror, and this is not a
  pathology of nested hot games — it is already present in the first infinitesimal
  layer.
- **Temperature alone *is* a tropical valuation (standard + tested).**
  `temp(G+H) ≤ max(temp G, temp H)` (numbers colder than all hot/infinitesimal
  games), so `v_T(G) = −temp(G)` satisfies `v_T(G+H) ≥ min(v_T G, v_T H)`;
  equal-temperature pairs are the game-side vanishing locus and can cancel to any
  lower layer. Probed over 324 small-game sums with no violations and every
  unequal-temperature pair at equality. This is exactly the tropical-hyperfield
  shape — but the *scalar* temperature law is too coarse to recover walls,
  sub-leading masts, or the resulting value.
- **The switch/binomial dictionary is real but one-parameter.** A switch
  `S_{m,τ} = {m+τ | m−τ}` has one wall equal to a one-side Newton polygon of a
  binomial `xⁿ − πᵏ` after an affine change of axes; it does **not** extend to a
  thermograph-level sum theorem (the no-congruence result blocks it).
- **The candidate single object is a residue-enriched associated graded.** Filter
  the game group by temperature, `F_{≤τ} = {G : temp(G) ≤ τ}` (additive subgroups,
  numbers in the cold bottom), and take `gr_T(Games) = ⊕_τ F_{≤τ}/F_{<τ}`. The
  leading thermic residue is the class of `G` at `τ = temp(G)`, *not* the pair
  `(mean, temp)`. At `τ = 0` this is already visible: the thermograph collapses
  `*, ↑, ↓, *2`; atomic weight (`atomic_weight.rs`) recovers one additive residue
  on all-small games (`aw(↑) = 1`, `aw(↓) = −1`, `aw(*) = 0`), but its kernel still
  contains nimber-like residues (`* + * = 0` shows the kernel matters) — so even the
  first graded piece is a genuine residual game object, not the mast.
- **Unrestricted descent fails.** Short games are not a ring. The repo now carries
  game-valued Norton multiplication / overheating operators as infrastructure, so
  the unrestricted answer is negative. In the
  `τ = 0` quotient, `*` and `* + 1` differ by the cold number `-1`, but Norton
  multiplication by the positive infinitesimal unit `↑` sends that hidden integer
  residue to a leading temperature-0 difference (`aw = -1`); the degenerate
  overheating operator `∫_↑^0` gives the same obstruction (`aw = -2`). Thus
  the unrestricted nonnumeric-unit family does **not** descend to the naive
  `gr_T(Games)` quotient (this proves existence of failure, not failure for every
  positive nonnumeric unit).
- **Numeric Norton descent is proved (new positive transport).** Let the positive
  dyadic unit be `u = m/2^k`, put `δ = 2^-k` (`δ = 1` for an integer), and
  `a = u - δ`. For every nonnumeric thermographic game,
  `mean(G.u) = u mean(G)` and `temp(G.u) = u temp(G) + a`. A cold number `x`
  with canonical mesh `ε = 1/den(x)` can become hot, but its exact temperature is
  `a-uε` when that is nonnegative and `-1` otherwise — always strictly below `a`.
  Standard Norton linearity therefore gives an additive graded map
  `gr_τ -> gr_(uτ+a)` for every `τ >= 0`; the identical recursion is Berlekamp
  overheating `∫_u^a`. For integer `u=n`, the shifted height `h=τ+1` scales
  exactly as `h -> n h`. `numeric_norton_regrade` and
  `numeric_norton_mean_temperature` compute the theorem without materializing the
  product. Rust tests pin the formula and quotient descent on the complete
  22-value day-two census plus a bounded day-three singleton-option census; the
  Python probe checked 210 thermic pairs and 24 representative pairs each for
  Norton/matching overheating with zero numeric-unit failures.
- **The internal-ring hope is impossible under the full-dyadic coefficient
  contract (proved).** The nonzero class `[*]` in `gr_0` has order 2.  In either
  an ordinary `ℤ[1/2]` algebra or a graded initial-form coefficient object for a
  valued dyadic field, the element representing 2 is homogeneous and invertible;
  lift-compatible action sends `[*]` to the initial class of `*+*=0` and would
  therefore force `[*] = 0`.  Thus a Rees or
  secondary valuation does not evade the theorem when the full dyadic field still
  acts.  A characteristic-2 nimber-only slice or a valuation-ring action can evade
  it only by omitting the `1/2` inverse.
- **The numeric transports are not a scalar action (proved exactly).** Their
  degree maps `r_u(τ)=uτ+u-δ_u` obey
  `r_v(r_u(τ)) = r_(uv)(τ) + Δ(u,v)`, where
  `Δ(u,v)=v(1-δ_u)-δ_v+δ_(uv) ≥ 0`.  At `u=1/2`, `v=2`, the defect is `1`:
  `A_2 A_(1/2)(*)` has temperature `1`, while `A_1(*)` has temperature `0`.
  No residue enrichment preserving temperature can repair an exact degree
  mismatch.  `numeric_norton_composition_defect` implements the formula; the
  Python probe checks 2,304 dyadic pairs and five materialized witnesses.
- **Resolution.** The mirror is substantive but stops before multiplication:
  the game side is a temperature-filtered abelian group with external numeric
  regradings, while the place side is an associated graded ring.  A
  characteristic-2 slice, valuation-ring/integer-only action without `1/2`,
  nonunital ringoid, hyperstructure, or quotient killing `[*]` may still be
  interesting, but each abandons a stated part of the full-dyadic unification
  contract and is not a reopening of `under`.

Closure checklist:
- ~~Formulate and test the lax law for `t(G+H)` as a hyperfield statement; locate
  the game-side vanishing locus.~~ **Done**: `temp(G+H) ≤ max(temp G, temp H)`
  holds with equal-temperature pairs as the vanishing locus, but it is provably too
  coarse to be the whole story (the thermograph itself is not a congruence).
- ~~Build the one-object switch/Newton-polygon probe.~~ **Done and bounded**: the
  dictionary works only in the trivial one-parameter switch family and does not
  extend to a sum theorem.
- ~~Test whether unrestricted Norton multiplication / overheating descends to
  the first temperature-filtration quotient.~~ **Done, negative for the
  unrestricted nonnumeric-unit family:** `* ≡ * + 1 (mod F_<0)`, but
  multiplying/overheating by `↑` leaves a non-lower temperature-0 residue.
  This existence witness rules out the naive full Berlekamp/Norton product on
  `gr_T(Games)`; it does not assert failure for every nonnumeric unit.
- ~~Decide whether numeric Norton units survive on the temperature associated
  graded.~~ **Done, positive for every positive dyadic unit:** the exact affine
  regrading is `τ -> uτ + (u-δ)`, and the image of every cold-number difference is
  strictly lower. This is the first substantive positive transport in `under`.
- ~~Decide whether anything larger survives under the Newton-style coefficient
  contract.~~ **Done, negative:** the `[*]` 2-torsion obstruction rules out any
  faithful dyadic-unital algebra, independently of the chosen internal product.
- ~~Promote the numeric composition failure from a witness to an exact theorem.~~
  **Done:** the nonnegative defect and all zero-defect pairs are classified;
  `u=1/2`, `v=2` rules out a multiplicative Norton action in exact temperature
  degree.

Relevant surfaces:
- `writeups/thermo_newton.tex`
- `experiments/under_descent.py`
- `src/scalar/tropical.rs`, `src/games/thermography.rs`, `src/games/heating.rs`,
  `src/games/atomic_weight.rs`
- `src/scalar/newton.rs`, `src/forms/springer/local.rs`
- `examples/tropical.rs` (the shipped thermography = tropical identity)

## references for the open threads

- Conway, *On Numbers and Games*: surreal numbers and nimbers.
- Lenstra, *On the algebraic closure of two*: the algebraically closed `On₂`
  field and its algebraic-closure beginning segment (for resolved `off`).
- Berlekamp-Conway-Guy, *Winning Ways*: coin-turning games, Turning-Corners/nim
  product theorem, and thermography.
- Siegel, *Combinatorial Game Theory*: temperature theory and thermography.
- Arf, *Untersuchungen uber quadratische Formen...*: quadratic forms in
  characteristic 2.
- Dickson, *Linear Groups*: binary quadratic forms and zero-count bias.
- Ovsienko, *Real Clifford algebras and quadratic forms over F_2*: useful
  char-0/char-2 analogy, not a blanket nim-field Clifford classification theorem.
- Lidl-Niederreiter, *Finite Fields*: finite-field trace/Frobenius background and
  Gold-rank checks.
- DiMuro, *On Onp*: source table and theorem for transfinite nim Kummer excesses.
- Brown, *Generalizations of the Kervaire invariant*, Ann. of Math. 95 (1972):
  `ℤ/4`-valued quadratic refinements and the `ℤ/8` invariant (for `over`).
- Wall, *Quadratic forms on finite groups*, Topology 2 (1963): the Witt group of
  finite quadratic forms (for `over`).
- Moews, *The Abstract Structure of the Group of Games*, MSRI Publications 42
  (2002): `ShUg` is a direct sum of dyadic and dyadic-mod-integer groups, hence
  two-divisible (for resolved `tisn` and `over`).
- Plambeck-Siegel, *Misere quotients for impartial games*, JCTA 115 (2008): the
  quotient/kernel theory behind the misère obstruction (for `tis`).
- Berlekamp, *The economist's view of combinatorial games*, in Games of No Chance
  (1996): the informal cooling dictionary (for `under`).
- Berlekamp, *Blockbusting and Domineering*, JCTA 49 (1988): generalized
  overheating, the numeric-unit surface used by the positive `under` theorem.
- Maclagan-Sturmfels, *Introduction to Tropical Geometry*; Viro, *Hyperfields for
  tropical geometry I*: valuations as (lax) tropicalization and the strictness
  repair (for `under`).
- De Feo-Randriam-Rousseau, standard lattices of compatibly embedded finite
  fields: the conjectured tower-aware Frobenius lever (for `on`).
