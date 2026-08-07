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
numbers, switches, ups, and stars. The code can now compute their finite
starter-pair outcomes; the open part is the game-semantic recasting problem, not
the vocabulary. The values come in dual pairs, and so do the problems:

- **`tis`/`tisn`** (`{0|tisn}`/`{tis|0}` — "this is / this isn't") — the two
  game-native-quadratic-data questions: the outcome side (`tis`, where every
  round of constructions and no-gos swings the apparent answer) and the
  coefficient side (`tisn`, where the obstructions lean *isn't*).
- **`on`/`off`** — the two transfinite-On₂ questions: the tower that climbs past
  every verified rung (`on`) remains open; the classifier beyond the finite
  windows (`off`) was resolved on 2026-08-07.  Over full algebraically closed
  `On₂` the Artin–Schreier quotient and regular quadratic Witt group vanish, so
  the finite Arf bit switches off under scalar extension.
- **`over`/`under`** — the two mirror questions: the mod-8 spine above the Arf
  bit (`over`) remains open; the MinPlus shadow beneath MaxPlus thermography
  (`under`) was resolved on 2026-07-20: a substantive filtered transport exists,
  while a faithful full-dyadic Newton-style ring is impossible.  It is retained
  below only as a closure tombstone.

The games are the names: refer to a problem by its loopy value. `dud` stays
unassigned: `dud + G = dud` for every `G`, and no problem has yet earned
absorbing the whole roadmap. May none ever.

## open problems

### tis·(e_g∧e_f): `natural Gold-quadric game rule`

Find, or rule out under a precise naturality condition, a non-tautological game
rule whose P-positions are the zero set `{Q = 0}` of a game-built Gold quadratic
form.

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
scales the bias. So if a game had P-positions exactly `{x : Q(x)=0}`, Arf would
say which player wins from more starting positions and by what square-root-scale
margin. That interpretation is meaningful, but it is conditional; it does not
exhibit the game.

Why this is research:
- The repo already builds the Gold forms and tests several game routes. The
  missing datum is not code for `Q`; it is a play rule, or a definition of
  "natural" strong enough to make the question non-ad-hoc.
- Normal-play sums do not solve it. For impartial normal play the P-condition is
  `g_1 xor ... xor g_n = 0`, hence linear in Grundy coordinates, while
  characteristic-2 quadrics obey `Q(u+v) = Q(u) + Q(v) + B(u,v)`. The polar form is
  exactly the XOR-closure obstruction.
- Frame-blind rules are too symmetric, while rules that directly evaluate `Q`
  are too tautological. The open core is the middle: a fixed play rule that reads
  the bilinear/game structure as a quadratic outcome without being a disguised
  evaluator.

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
coincide at linear. `tis` is exactly whether the lexicode phenomenon admits
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
  flips to the Gold form. The remaining problem is whether the diagonal framing
  `q_i = Q(e_i)` is itself game-natural.
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

The program state (2026-06-10 — `writeups/goldarf.tex` §§5–9, backed by the
`experiments/gold/` probes):

- The naturality criterion asked for below now has a draft formalization — N1
  (decision-nondegeneracy), N2 (bounded framing access), N3 (strategic
  relevance / anti-clock). N3's exact formulation is itself an open definitional
  problem: the escape-edge construction passes N1–N3 while being morally a clock,
  and the natural repairs run into two-game criticality being unsatisfiable in
  two-class outcome semantics.
- A no-go ladder (Theorems B–H) kills Tier 1 outright and shows every known
  in-quarantine Tier-2 normal-play realizer is a clock. Five named escape hatches
  remain: loopy-Draw semantics, `t ≥ 2r−2` with anisotropic complement,
  Frobenius-aware access (where both the symmetry and oracle methods are provably
  silent), non-quarantined rules using the game-native `℘` diagonal source, and
  rank-1 / radical-anisotropic degenerate layers.
- The abelian obstruction conjectured here is now Lemma `abelian` in the draft:
  no commutative game monoid's intrinsic squaring realizes a nondegenerate polar
  form, so the quadratic datum must come from the move relation's directedness.
- The leading Tier-2 candidate was the `echo`-ko charge-counting family on the
  extraspecial cocycle, and its `echo`-`fifo`+dummy variant is now **verified**
  (2026-06-10, pre-registered adversarial review, `experiments/echo_solver.py`):
  full `m = 8` exactness across all 765 scaled Gold forms, both stances,
  391,680/391,680 checks re-derived by a fresh direct full-state solver — no
  decomposition, σ in the memo key, validated against tree enumeration and the
  original direct solver, with a second-model cross-run. Decision-live in bulk
  (1.5–4.4M decision states per benchmark instance), torsor-uniform across
  refinements of each `B`. Three honest boundaries: the realizer is
  **σ-valued** (it realizes `Q` as a forced terminal charge — the central
  character of the play word — not yet as a P-set in normal/misère/loopy
  semantics); the `echo`-ko table is stance-asymmetric (its exactness face is
  the σ=1 stance only, where `fifo`+dummy is exact at both); and the
  bounded-window blocker conjecture is untouched (the FIFO queue is unbounded
  memory). The recasting is now the load-bearing open step; the
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
- **Tier 2: fixed-rule middle: open.** Positions should be indexed by field
  elements, with one rule independent of the chosen `x`, and the single-position
  Grundy-zero / kernel / Loss / Draw set should be `{Q_a = 0}`. The rule may use
  the nim product, Frobenius, or coordinate-frame data if a naturality criterion
  justifies them, but it must not simply evaluate `Q_a(x)`.

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
screen and no-go ladder of `writeups/goldarf.tex` §§5–6 (see the program-state block
above); it does not yet exhibit a game.

Concrete progress targets (aligned with the goldarf §9 ranked moves):
- ~~Adversarially verify or refute the `echo`-`fifo`+dummy `m = 8` exactness
  claim~~ — **done, CONFIRM** (2026-06-10; `experiments/echo_solver.py`, record
  in goldarf §8). The successor target: **recast the
  σ-valued charge readout into normal/misère/loopy outcome semantics**, or
  prove the recasting impossible — the step that converts the verified
  realizer into a Tier-2 witness in the original P-set sense. Alongside it:
  the family-boundary sweep (ko-window `w`, pass semantics, pair touches,
  no-dummy controls), which also puts the bounded-window blocker on valid data.
- Close the **general-n linking theorem** (the mechanism half, reduced
  2026-06-10 and sharpened 2026-07-20): prove that the odd-close parity game
  on any graph with an isolated coin forces an even flip count from both
  seats. Verified for all 12,346 classes at k = 8 real coins plus dummy
  (`experiments/linking_game.py`). The old R3/D3 induction fails first at
  `GCRU]w`; the live route is the block-turn plus live-degree-pairing
  formulation, with FIFO re-entering through forced front deletion and the
  proactive-debt witnesses above.  The current exact target is the global
  affine-contraction lemma of `writeups/linking_affine.tex`, with the FIFO
  cut-space filtration as a coordinate system but not a childwise induction.
  A proof upgrades the m∈{4,8} verification to exactness for all m.
- Repair or replace N3, the anti-clock axiom — the open definitional problem: the
  escape-edge construction passes N1–N3 while being morally a clock, and two-game
  criticality is unsatisfiable in two-class outcome semantics.
- Exhibit a fixed uniform rule satisfying N1, N2, and N3 simultaneously on a Gold
  quadric of core rank ≥ 6 — or close the remaining escape hatches (loopy-Draw,
  `t ≥ 2r−2` anisotropic, Frobenius-aware access, `℘`-sourced diagonals,
  rank-1/radical-anisotropic layers) with no-gos of their own.
- Enumerate the Frobenius-aware access window at `m = 4, 8` — the one hatch where
  both the symmetry-killing and oracle methods are provably silent.
- Decide whether the diagonal refinement `q_i = Q(e_i)` is game-native for all `a`:
  the `a = 1` case is answered affirmatively by the `℘`-construction
  (`Wp(w) = w·w + w`, verified at `m = 4..32`); the even-`a` analogue (the drifting
  dual `λ_a^{(m)}` tower) has no named preimage family beyond `m = 8`.
- Cheap gates: verify the Plambeck–Siegel Thm 6.4 regularity hypothesis (slug
  `ps-regularity`); enumerate conjugation-move rules on `E` (the left-translation
  kill of Theorem H does not apply to conjugation); exhaust the board-8 case of the
  `fifo` parity-pinning conjecture.

Relevant surfaces:
- `writeups/goldarf.tex`
- `writeups/linking_affine.tex`
- `experiments/open_question_probe.py`
- `experiments/framing_obstruction.py`
- `experiments/gold_family_survey.py`
- `experiments/misere_kernel.py`
- `examples/interactive_kernel.rs`
- `examples/loopy_quadric.rs`
- `examples/bent_route.rs`
- `src/forms/quadric_fit.rs`
- `src/games/kernel.rs`, `src/games/misere.rs`, `src/games/loopy/`

### tisn·(e_g∧e_c∧e_f): `quadratic deformation of the game exterior algebra`

Decide whether the current `GameExterior` construction admits a genuinely
game-native quadratic deformation on torsion-carrying game subgroups, rather than
only the all-zero Grassmann metric.

What is implemented:
- `GameExterior` is deliberately the exterior algebra of the game group. It uses
  the `Z`-module structure of games under disjunctive sum and can include non-number
  games such as `*` and `up`.
- Relation propagation is quotient-aware. If the game group imposes a relation,
  the exterior ideal respects it; for example, torsion in grade 1 propagates to
  torsion constraints in higher grades.
- `GameClifford::with_quadratic_data` is the checked engineering artifact: it
  accepts hand-supplied integer quadratic/polar tables on a chosen game subgroup
  only after verifying that every imposed game relation is null and polar-radical
  for the supplied data. The Python bindings expose the same checked surface.
- This does not pretend that arbitrary games form a scalar ring. The construction
  is an exterior algebra over an abelian group plus a checked integer-valued
  deformation, not a Clifford algebra over games.

Why this is research:
- A Clifford deformation would require extra quadratic data compatible with the
  game-group relations. Over torsion-free integer coefficients, a relation such as
  `2* = 0` forces any bilinear pairing involving `*` to vanish, and also forces a
  `Z`-valued quadratic value on `*` to vanish.
- Supplying an arbitrary quotient-compatible bilinear/quadratic table is a bounded
  implementation exercise. The research question is whether there is a natural,
  non-tautological source of such data from game structure itself.
- Torsion and mixed torsion/free subgroups make this sharper than "add a metric":
  the coefficient target, polarization identity, and relation compatibility all
  matter.

The program state (2026-06-17 — `writeups/game_exterior_deformation.tex`):

- **Two descent gates, not one.** A quadratic datum must descend through the game
  relations — `Q(r) = 0` and `B(r, e_j) = 0` for every relation row `r`, which are
  exactly the null and polar-radical checks the integer checker already runs. A
  Clifford quotient over a coefficient ring `R` must *also* keep the coefficient map
  `R -> Cl` injective: the relation vector `n·e_t` sits in a two-sided ideal, and
  `(n·e_t)·e_t = n·Q(t)` is a scalar the ideal can silently kill. Over `Z` both gates
  give the same visible answer; over torsion coefficient rings the faithfulness gate
  is strictly sharper.
- **The torsion obstruction is now proved, both gates.** For a torsion-free target
  and a torsion element `t` (`nt = 0`), `n·B(t,x) = 0` and `n²·Q(t) = 0` force
  `B(t,x) = 0` and `Q(t) = 0`. Hence every integer-valued deformation of a mixed
  subgroup `M = T ⊕ F` is **blind to `T`**: torsion generators stay
  exterior/nilpotent and polar-orthogonal to the free part, and all nonzero integer
  quadratic data factors through the free quotient `M/T`. This settles the
  torsion-free / `Z`-valued progress target below as a no-go, not a gap.
- **The `ℤ/4` Brown lift is not a faithful square quotient.** Trying `M = ⟨*⟩ ≅
  ℤ/2`, `R = ℤ/4`, `Q(*) = 1` passes the bare quadratic check (`Q(2*) = 4 = 0`), but
  `(2e_*)·e_* = 2` puts the scalar `2` in the relation ideal, silently collapsing
  `ℤ/4` toward characteristic 2. So the `over` Brown category (`forms/char2/brown.rs`)
  is a genuine quadratic-*module* target — but it does not by itself deform
  `GameExterior`'s algebra without changing the coefficient ring the quotient sees.
  The two problems touch here without coinciding.
- **The escapes that survive are tautological or off-core.** Over `F_2` the
  one-generator square `Q(*) = 1` survives (`2 = 0` already), and the canonical
  `R = Sym_{F_2}(M/2M)`, `Q(x) = x̄`, `B = 0` is relation-compatible and
  coefficient-faithful — but it has zero polar form and merely *records* the mod-2
  game class instead of explaining torsion. The additive-invariant family
  `Q_φ(x) = φ(x)²`, `B_φ(x,y) = 2·φ(x)·φ(y)` for a game-native additive `φ`
  (thermographic mean value, atomic weight — both re-confirmed additive this pass) is
  genuinely game-native on the **free** directions (`aw(↑) = 1`, `aw(*) = 0`,
  reproducing the mixed-subgroup split) but sends every torsion element to zero. The
  nimber Gold forms `Q_a(x) = Tr(x·x^(2^a))` are the one non-tautological torsion
  source, but they live on the field-like impartial core where the scalar story
  already applies — they do not extend over general partizan games.
- **The sharpened question.** A solving construction needs a game-built coefficient
  target and a square operation that (i) survives the coefficient-faithfulness test,
  (ii) is not the tautological polynomial ring on `M/2M`, (iii) does not factor
  through an additive invariant into a torsion-free ring, and (iv) reaches beyond the
  nimber core. The likely missing ingredient is not another commutative value
  invariant but a game-native **directed / noncommutative** structure whose square
  remembers first-/second-player asymmetry — the same obstruction recorded for `tis`
  (commutative game-value monoids make squaring additive, hence polar-zero).

Concrete progress targets:
- ~~Formalize the algebraic object: a quadratic map on a game subgroup, its
  coefficient ring or module, its polar pairing, and the exact compatibility
  condition with integer game relations.~~ **Done** (the two-gate descent above):
  quadratic descent plus the coefficient-faithfulness intersection of the relation
  ideal.
- ~~Prove obstruction results for torsion generators and mixed torsion/free subgroups
  under `Z`-valued or torsion-free coefficient targets.~~ **Done**: torsion is forced
  into the radical, and integer deformations are blind to `T`.
- Identify coefficient targets where torsion can support nonzero quadratic data, and
  decide whether those targets are game-native or merely chosen by hand. (Bounded
  from two sides now: char-2 targets keep nonzero torsion squares but the canonical
  one is tautological; `ℤ/4` is not faithful as a square quotient. A *non-tautological*
  char-2 or torsion target is still open.)
- Exhibit a nonzero deformation on a restricted class of games beyond the nimber
  core, or prove that every natural relation-respecting deformation collapses to
  Grassmann / the additive-invariant family / the tautological `Sym(M/2M)`.
- Build the directed/noncommutative coefficient source whose square encodes the
  first-/second-player asymmetry — shared with `tis`; no construction yet.
- Implementation guard: a future `GameClifford` over torsion coefficient rings must
  also check the scalar intersection of the two-sided relation ideal (the necessary
  conditions `nQ(t) = 0`, `nB(t,x) = 0` for every visible torsion relation `nt = 0`),
  not only the integer null/polar-radical checks; otherwise a datum can look
  quadratic while the quotient silently changes the coefficient ring.

Relevant surfaces:
- `writeups/game_exterior_deformation.tex`
- `src/games/game_exterior/` (`lambda.rs`, `clifford.rs`)
- `src/games/thermography.rs`, `src/games/atomic_weight.rs` (the additive sources)
- `src/forms/char2/brown.rs` (the `ℤ/4` module target; shared with `over`)
- `src/games/AGENTS.md`
- `examples/tour.rs`
- `demo.py`

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

### over·(e_f∧e_g): `the mod-8 spine in game semantics`

Decide whether the Brown invariant — the char-2 cell of the mod-8 spine, shipped as
Bridge M — has a game-theoretic reading the way the Arf bit does, i.e. whether the
conditional win-bias interpretation of `tis` lifts from `ℤ/2` to `ℤ/8`.

What is implemented (Bridge M, `forms/char2/brown.rs`): a `ℤ/4`-valued quadratic
refinement `q : V -> Z/4` has Gauss sum

```text
Sum_{x in V} i^(q(x)) = 2^(n/2) * zeta_8^beta,
```

read off the integer value-census Gaussian integer `(n0 - n2) + i*(n1 - n3)`, where
`n_k = #{x : q(x) = k}`. Doubling a classical char-2 form gives `beta = 4*Arf` — the
shipped win-bias bit embeds as the 2-torsion `{0, 4}` of `ℤ/8`.

Why this is research:
- The Arf reading is a **two**-class census: P-positions versus N-positions, bias
  `2^(r-1)` with sign `(-1)^Arf`. The Brown phase is a **four**-class census with a
  complex bias. No shipped outcome semantics has four classes: normal play has two,
  loopy play three (W/L/D). The question is whether any natural four-way outcome
  partition — loopy outcomes crossed with a parity, normal/misère outcome pairs, a
  mod-4 scoring residue, or something not yet named — produces the `zeta_8` phase of
  a game-built `ℤ/4`-form as its census.
- Game-built doubled forms only ever reach `beta in {0, 4}`. A genuinely odd `beta`
  needs `b` symmetric-but-not-alternating with `b_ii = q_i mod 2` — diagonal data
  again, one level up: this is the diagonal-framing problem of `tis` with the
  diagonal now *forced* by `q mod 2` rather than vanishing. The two problems are
  entangled, not parallel.
- The extraspecial picture of `tis` lifts: `ℤ/4`-valued forms correspond to
  central extensions by `ℤ/4` (the Pauli/complex-extraspecial family) exactly as
  `F₂`-forms correspond to extensions by `ℤ/2`. If the abelian obstruction
  (Lemma `abelian`) survives the lift, the four-class census also cannot come from
  any commutative game structure's own multiplication — which would make the
  first-/second-player asymmetry carry *three* extra bits instead of one.

Conditional claim, same shape as `tis`: if a game's positions admitted a natural
four-class outcome census matching `i^q` for a game-built `q`, then `beta` would be
the phase and magnitude of its outcome imbalance — `sign mod 8` as a win-bias octant.
That interpretation is meaningful but conditional; it does not exhibit the game.

Concrete progress targets:
- Census probe: tabulate `(n0, n1, n2, n3)` for `ℤ/4`-refinements of game-built
  polar forms (doubled Gold forms first) and check which Gaussian integers actually
  arise on the game-reachable slice.
- Decide whether any existing three-class route (loopy W/L/D, `examples/loopy_quadric.rs`)
  extends by one natural axis to a four-class census with nonvanishing phase.
- Formulate the `ℤ/4` analogue of the abelian obstruction and prove or refute it.
- Connect to the lattice side: on 2-elementary discriminant forms `beta ≡ sign mod 8`
  (shipped); a game realizing `beta` would be a game computing a lattice signature.

Relevant surfaces:
- `src/forms/char2/brown.rs`, `src/forms/integral/discriminant/` (Bridge M)
- `src/games/loopy/`, `src/games/misere.rs`
- `writeups/goldarf.tex` §5 (the extraspecial reframing this lifts)
- `tis` — the `ℤ/2` floor of this question

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
