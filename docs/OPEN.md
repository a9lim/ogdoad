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
  every verified rung (`on`), and the classifier that switches off beyond the
  finite windows (`off`).
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
  The remaining question is whether that broader finite strategy has a
  general recursive certificate.
- The dummy defeats the empty-queue domination device at every root, matching
  the no-dummy Bad-graph census 1/4/34 at n = 3/5/7 (all mover-controlled),
  but that device is not the unique local squeeze. On the path `z-f-y-h`,
  state `queue=(f,h), U={y,z}` has an even front and no safe move: either
  open makes f odd, while closing f exposes odd h. The isolated dummy kills
  this squeeze while untouched, but once queued or spent it becomes exactly
  the recursive repair-potential problem.

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
  proactive-debt witnesses above. A proof upgrades the m∈{4,8} verification
  to exactness for all m.
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

Push transfinite nim multiplication beyond the source-verified Lenstra-DiMuro
excess table. Historically the first missing carry in this checkout was
`alpha_47`; a local fixed-base finite-field oracle now verifies that carry, but
the general closed-form problem remains open.

What is implemented:
- The algebraic closure of `F_2` is represented by ordinals `< omega^(omega^omega)`
  under nim-arithmetic.
- The prime-power generator tower is implemented in `src/scalar/big/ordinal/tower.rs`.
  Products are exact when every Kummer carry uses a finite Lenstra excess `m_u` for an
  odd prime `u <= 709`: the finite `m_u` are sourced from OEIS A380496 ("Lenstra excess
  of the n-th odd prime"), the b-file's 126 known rows (odd primes `3..=709`; the first
  14 reproduce DiMuro Table 1 + the old `m_47`). The first OEIS-unknown row is `p=719`,
  so a carry at `u >= 719` returns `None`. The ordinal carry `alpha_u` is assembled in
  code from `f(u)=ord_u(2)`, DiMuro's recursive `Q(f(u))`, and the finite `m_u`.
- Stage 1 handles scalar excesses such as `alpha_3 = 2`, `alpha_5 = 4`, and
  `alpha_17 = 16`; Stage 2 handles nonscalar excesses such as `alpha_7 = omega+1`
  by branching the monomial and recursing to lower places.
- The 126 finite excess rows (the *integers* `m_u`) are source-pinned to OEIS A380496 in
  full — the vendored b-file is diffed against the table row-for-row by
  `excess_table_matches_vendored_b380496_in_full` (`src/scalar/big/ordinal/
  b380496.txt`, fetched 2026-07-02). Caveat: the table extends *reach*, not
  *feasibility* — for large primes `alpha_u` is in the table but its `Q(f(u))`/finite-
  subfield reconstruction over the degree-`e_u` component field (`e_u` in the millions
  for `u` near 709) is too costly to materialize in practice, so only the smaller-`e_u`
  rows are usable end-to-end today.
- "Exact for `u <= 709`" means the construction is *defined* there (`alpha_ordinal(u)`
  returns `Some`, since every input it needs — `f(u)`, `Q(f(u))`, and `m_u` — resolves).
  It is a separate, narrower claim that the resulting *ordinal value* has been checked
  against an oracle outside the construction itself: that per-row value pin currently
  covers `u` in `{3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 73, 89}`
  (DiMuro Table 1 for the first 14; `73`/`89` cross-checked against `experiments/
  ordinal_excess_probe.py`'s independently curated `Q_SET`/order-based excess
  certification; `47` additionally re-derived by raw repeated multiplication in
  `locally_verified_alpha_47_landmark`). The remaining rows up to `709` are defined and
  internally consistent (the field-axiom sweeps exercise engine consistency) but do not
  yet have an independent value oracle. The "large primes near 709" cost caveat above
  actually bites much earlier than 709: `alpha_ordinal(179)` (`f=178=2*89`,
  `Q(f)={89}`) already recurses into a `finite_subfield_degree` Frobenius minimization
  on `chi(89)=omega^(omega^22)` that does not finish in a unit-test budget, confirmed
  by hand while extending this table — so `179` is a genuine gap in the "cheap today"
  set, not merely an oversight.

The first fourteen rows (odd primes `3..=47`) are shown below for readability — the
historic DiMuro Table 1 + `m_47` landmarks, now also OEIS A380496 `a(1)..a(14)`;
production stores the finite `m_u` for all 126 rows (`3..=709`) and reconstructs the
displayed `alpha_u` values:

| u | alpha_u | u | alpha_u | u | alpha_u |
|---|---|---|---|---|---|
| 3 | 2 | 13 | omega+4 | 29 | omega^(omega^2)+4 |
| 5 | 4 | 17 | 16 | 31 | omega^omega+1 |
| 7 | omega+1 | 19 | omega^3+4 | 37 | omega^3+4 |
| 11 | omega^omega+1 | 23 | omega^(omega^3)+1 | 41 | omega^omega+1 |
| | | 43 | omega^(omega^2)+1 | 47 | omega^(omega^7)+1 |

Current external state:
- The first OEIS unknown in the extended table is now `p = 719`, where
  `f(719) = 359` and `Q(359) = {359}`. The calculator notes the required finite
  exponent as `e_719 = 1258230380`, which is the practical wall for the direct
  Lenstra power test.
- A tempting pattern matches the checked OEIS/calculator records from this pass:
  `m_p = 0` when `Q(f(p))` is not a singleton odd prime-power; `m_p = 1` for a
  singleton odd `Q(f(p))`, except the observed `f(p) = 2*3^k` cases have
  `m_p = 4`. A local audit matched this rule against the 950 calculator records
  with known `Q`-sets, and against every OEIS-known row covered by those `Q`-sets.
  This is still only a candidate rule, not a theorem.
- The exact finite-field reformulation is sharper than root-search language. If
  `beta = kappa_{f(p)} + m` lies in the component field `F_{2^E}`, then `beta`
  has no `p`-th root exactly when the multiplicative order of `beta` contains the
  full `p`-primary part of `2^E - 1`. When `v_p(2^E - 1) = 1` this reduces to
  `p | ord(beta)`; the full statement is required at base-2 Wieferich primes
  and whenever `p | E/f(p)`.
- The local fixed-base probe (`experiments/ordinal_excess_probe.py`) uses that
  criterion to verify `m_47 = 1` from the lower rows. Since `f(47) = 23` and
  `Q(23) = {23}`, this gives `alpha_47 = omega^(omega^7)+1` — historically the first
  row past DiMuro Table 1, now subsumed by the OEIS A380496 import (the shipped table
  is source-pinned, not per-row locally oracled).

Since the 2026-06 research pass (`writeups/excess.tex`, `experiments/excess/`,
`experiments/cyclotomic_3k_family.py`):

- The 3-power column is now structural: `C_k` — the exact formula
  `ord(kappa_{3^k} + 1) = 3^(k+1) * (2^(3^k) - 1)` with `gamma_k` primitive — is
  proved analytically for `k <= 3`, certified by exact-order computation for
  `4 <= k <= 6`, and consistent-but-uncertified for `k = 7, 8`, blocked only
  by the unfactored cofactors of `Phi_{3^7}(2)` and `Phi_{3^8}(2)` (FactorDB
  CF). Whether ECM/GNFS reaches those on a realistic budget is open.
- The analytical target inside `C_k` is now explicit at polynomial and torus level
  (2026-07-20, `writeups/excess.tex`). With `f(X) = X^3 + X`, the minimal
  polynomial of `gamma_k` is the irreducible Dickson iterate
  `P_k(X) = D_(3^k)(X,1) + 1 = f^k(X) + 1`, satisfying
  `P_(k+1) = P_k^3 + P_k^2 + 1`; hence `C_k` says exactly that `P_k` is
  *primitive*, not merely irreducible. Equivalently, for
  `q_k = 2^(3^(k-1))`, the new component
  `eta_k = gamma_k^(q_k - 1)` lies in the cubic norm-one torus
  `U_k` of order `q_k^2 + q_k + 1` and obeys the fully recursive equation
  `X^3 + eta_(k-1) X^2 + (eta_(k-1)+1) X + 1 = 0` (`eta_0 = 0`). Thus its
  norm, trace, and second elementary coefficient are respectively
  `1`, `eta_(k-1)`, and `eta_(k-1)+1`; `C_k` is precisely the remaining claim
  that this distinguished root generates `U_k`. The same element is the Möbius
  image `(omega + omega^2*zeta^2)/(1+zeta^2)`, with inverse
  `zeta^2 = (eta_k+omega)/(eta_k+omega^2)`. It also obeys
  `eta_k^(q_k+1) + eta_k + 1 = 0`, so it is a member of the planar Singer
  difference set of size `q_k+1` in `U_k`. Singer membership alone is
  formally order-neutral: `y -> y^(q_k+1)` is an order-6 automorphism of
  `U_k`, and the Singer equation merely says that this automorphism sends
  `y` to `y+1`. At `q=32`, a root of `X^3+X^2+1` lies in the analogous set
  but has order `7` inside the group of order `7*151`. The recursive
  coefficient `eta_(k-1)` is therefore essential.
- The exact remaining lemma now has a character form. For every prime
  `ell | |U_k|`, let `chi_(k,ell)` be an exact-order-`ell` character of
  `U_k`. Then `C_k` is equivalent to `C_(k-1)` plus
  `chi_(k,ell)(eta_k) != 1` for every such `ell`. Equivalently, the
  multiplicative character `rho(A) = chi(A^(q_k-1))`, trivial on the base
  field, must satisfy `rho(gamma_k) != 1`. All distinct kernel orders are
  pairwise coprime; in fact
  `Hom(F_(2^(3^(k-1)))^*, mu_ell)=1` for `ell | |U_k|`, so no
  multiplicative character or power-residue datum from a previous level
  can transfer an `ell`-part to this test.
- The same lemma now has two further exact analytical forms (2026-07-20).
  First, if `Q_0(X)=X`, `A=X^3+X+1`, `B=X^2+X`, and
  `Q_k(X)=B(X)^(3^(k-1)) Q_(k-1)(A/B)`, then `Q_k` is the degree-`3^k`
  minimal polynomial of `eta_k`; for each prime `ell | Phi_(3^k)(2)`,
  character nonvanishing is equivalent by Kummer theory and Capelli's
  lemma to irreducibility of `Q_k(X^ell)`. Notably
  `Q_4=X^81+X^64+X^16+X+1`, so the first composite level is an explicit
  pentanomial-composition reformulation; no known general irreducibility
  criterion turns it into a reduction. Second, in
  the real cyclotomic field `F_k=Q(zeta_(3^(k+1)))^+`, the conjugates of
  `c_k=2+zeta+zeta^(-1)` generate a 2-power-index subgroup of the real
  circular units and reduce modulo the inert prime `2` to the powers of
  `gamma_k`; the index disappears in the odd-order residue group. Hence `C_k` is
  exactly surjectivity of circular units onto `F_(2^(3^k))^*`. The index
  factors through the ray-class exact sequence as ray-class growth at
  modulus `(2)` times a quotient of the circular-unit index; away from
  primes dividing the ordinary class number, an `ell`-failure is exactly
  `ell`-part growth in that ray class group. This names rather than solves
  the obstruction: the ray group is defined by the same residue quotient,
  and the required ordinary-class-number exclusion is not uniform in `k`.
  The relative coboundary
  `sigma^(3^(k-1))(c_k)/c_k` reduces to `eta_k`.
- There is one unconditional analytical closure: if `Phi_(3^k)(2)` is
  prime, the nonidentity element `eta_k` automatically generates `U_k`.
  Hence `C_1`, `C_2`, and `C_3` follow without an order computation from
  the primality of `7`, `73`, and `262657`; only `k=4,5,6` retain the
  finite-field order-certificate label.
- The shifted unit `1+zeta_(3^(k+1))` is norm-coherent in the characteristic-
  zero cyclotomic `Z_3`-tower, and its real norm reduces modulo the unique
  prime above `2` to `gamma_k`. Thus the character lemma is an Artin-type
  fixed-prime power-residue problem for a cyclotomic unit, not merely an
  irreducible-polynomial question.
- The `f(p) = 2*3^k` exception column is settled at every prime current factor
  tables reach (2026-06-12, `experiments/exception_column_m4.py`): `m_p = 4`
  *exactly*, universally for `k <= 6` (fully factored levels — 14 rows, 11 of
  them new, anchors `19`/`163`/`1459` reproduced never assumed) and at every
  known prime of `k = 7, 8`. The enabling fact is a corrected compositum norm:
  `sigma(4) = 5` (the F_4-Artin-Schreier conjugate; the earlier draft's
  `(kappa+4)(kappa+6)` was a Frobenius slip), so
  `Norm(kappa+4) = (kappa+4)(kappa+5) = kappa^2 + kappa + 2`, which collapses
  the `m = 4` test into the same trinomial field as the `C_k` chain:
  `m_p = 4  <=>  p | ord(M_k)`, `M_k = Nbar/N`, `N = zeta^2 + zeta + zeta^h`.
  The per-level conjecture `D_k` (the prime-to-3 part of `ord(M_k)` is full) is
  the new column analogue of `C_k`; the norm tower is *twisted*
  (`Norm(N_k) = eta^2 + omega^2*eta + 1 != N_{k-1}`), so no `gamma`-style
  propagation exists and each level stands alone. An `m_p >= 5` example, if one
  exists, now hides strictly inside the unfactored cofactors of
  `Phi_{2*3^7}(2)` and beyond.
- Wieferich caveat: the order criterion `m_p = min m : p | ord(kappa_{f(p)} + m)`
  is valid only when `v_p(2^(f(p)) - 1) = 1`. The two known base-2 Wieferich
  primes `1093` and `3511` sit inside the extended range and need the full power
  criterion.
- Newly certified `m_r = 1` rows (`262657` at `f = 27`; `71119` and `97685839` at
  `f = 81`; representatives at `f = 243, 729, 2187, 6561`) keep the candidate
  `0/1/4` rule unbroken. Still no proof; boundedness outside the 3-power and
  `2*3^k` columns (the 11-chain, the 23/29/47 components) has no structural
  theory, and no `m_p >= 5` example is known.
- The `p = 719` dependency rehearsal advanced one rung and then hit a wall. The
  local fixed-base oracle certifies `m_89 = 1` (`E = 220`) and `m_179 = 1`
  (`E = 19,580`) via the fixed-base power path (`python3
  experiments/ordinal_excess_probe.py --deep`, ~1 min). `m_359 = 1` is the
  remaining rehearsal row before `m_719` — already source-pinned by A380496, but
  with no *independent* local certificate, and the 2026-06-16 pass diagnosed
  precisely why it is blocked (`writeups/excess.tex`, "the m359 rehearsal
  obstruction"):
  - The structurally cheap **top-step Kummer norm** is the wrong norm. With
    `f(359) = 179`, the tower has `F = F_{2^E}` over `B = F_{2^19580}`, and
    `Norm_{F/B}(κ_179 + 1) = κ_89 ∈ B` — but `359 ∤ 2^19580 − 1` (since
    `ord_359(2) = 179 ∤ 19580`), so `359` is *invisible* in `B`. The certified
    `m_89` / `m_179` rows do not propagate up through the easy norm.
  - The norm actually forced by the order criterion is the **transverse**
    `Norm_{F/L}(β)`, `L = F_{2^179}` (`gcd(179, 19580) = 1`, so `F = B·L`): the
    `F_{2^3504820} / F_{2^179}` norm is the genuinely required object.
  - In the current pure-Python term basis that target-subfield element is
    essentially **half-dense** (support `111/220` for the `p = 89` analogue,
    `9691/19580` for `p = 179`), so the direct fixed-base root-test exponent is
    slower than the cheap certificate — a representation diagnostic, not a no-go.
  - The Wieferich caveat is *absent* at the live pressure points: `2^179 ≢ 1
    (mod 359²)` and `2^359 ≢ 1 (mod 719²)`, so the order form equals the full
    power criterion for both `m_359` and the proposed `m_719` test.
  A practical `m_359` certificate now needs either dense/sliced GF(2) arithmetic
  (`gf2x` / NTL) or a tower-aware Frobenius representation that makes the
  transverse orbit cheap; the pure-Python oracle cannot reach it. The same
  `Norm_{E/K}(β) = ∏_i Frob^i(β)` orbit primitive is what Bridge K's
  cyclic-algebra reduced norm needs — a reusable
  `relative_norm_over_frobenius_orbit` is the shared engineering lever (not a
  claim that the bounded `Fpn` norm certifies `m_719`).
- `p = 719` feasibility: the direct test needs ~3.5 million Frobenius steps in
  `F_{2^1258230380}`; tower-aware Frobenius arithmetic (De Feo–Randriam–Rousseau
  standard lattices) is the conjectured 10–100x lever — a cost model, not a
  theorem.

Why this is research:
- The same-coverage implementation improvement is now done: the shipped code computes
  `f(u)`, `Q(f(u))`, and the `chi`-sum, while hardcoding only the finite excess
  integer. That changes provenance hygiene, not reach.
- Extending past the verified finite-excess table is different. DiMuro's theorem proves that the
  excess has a formulaic transfinite shape plus a finite correction, but the finite
  correction has no closed form in the cited theorem.
- Weaker "closed forms" already fail: `Q(f(p))` alone does not determine the
  excess, since `Q = {9}` gives `m_19 = 4` but `m_73 = 1`; similarly
  `Q = {81}` gives `m_163 = 4` but `m_2593 = 1`, and `Q = {243}` gives
  `m_1459 = 4` but `m_487 = 1`.
- The candidate `0/1/4` rule above would imply a global bound `m_p <= 4`. Lenstra
  explicitly left absolute boundedness open after proving lower-bound rules such
  as singleton-odd `Q(f(p))` forcing positive excess and `f(p)=2*3^k` forcing
  excess at least `4` (the matching upper bound `m_p = 4` is now certified at
  every visible prime of that column; see above).
- The candidate contains two independent explicit maximal-order problems. On the
  singleton-even side, put `c_n = kappa_(2^(n+1))` and let `delta_n` be the order
  of its coset in
  `F_(2^(2^(n+1)))^* / F_(2^(2^n))^*`, whose order is the Fermat number
  `F_n = 2^(2^n) + 1`. The zero arm for every prime divisor of `F_n` is exactly
  `delta_n = F_n`, the maximal-coset-order condition studied for Conway's
  quadratic tower. This is strictly weaker than primitivity of `c_n`, which
  already fails at `n = 2` (`ord(c_2) = 85 < 255`); Popovych instead uses the
  same condition to obtain primitive products involving the bottom generator.
  On the `3`-power side,
  the one arm through level `k` is
  exactly the assertion that the Gaussian period
  `gamma_k = zeta + zeta^(-1)` is primitive in `F_(2^(3^k))`. Irreducibility and
  field degree do not prove either statement: they force some new order factor,
  not every prime-power factor. In fact the cubic step splits as
  `F_(2^(3^k))^* = F_(2^(3^(k-1)))^* x U_k`, with
  `|U_k| = Phi_(3^k)(2)`, and the relative norm kills `U_k`. The norm recursion
  therefore supplies no order information about exactly the new-prime component
  that `C_k` must show is generated. The explicit `eta_k` recursion above recovers all
  three symmetric coefficients of that component, but maximal order still asks
  whether `eta_k` avoids every proper prime-index subgroup of `U_k`. Known
  Gaussian-period results provide large lower bounds, and the analogous
  prime-conductor primitivity statement of Gao–Vanstone is itself conjectural;
  neither result supplies this prime-power-conductor Singer assertion.
- These are the same species of obstruction in projective degree `2` and `3`.
  The even arm asks that `c_n` generate `E_n^*/E_(n-1)^*`; the cubic
  increment asks that `gamma_k` generate
  `F_(q_k^3)^*/F_(q_k)^*`, equivalently that its multiplication matrix
  generate a Singer cycle in `PGL_3(q_k)`. The candidate rule therefore
  contains two maximal-projective-coset-order conjectures.
- Every singleton-odd row now has one exact analytical target. If
  `Q(h) = {q = r^a}`, write `b = d(alpha_r)` and `h = q*s` with `s | b`. Then
  `kappa_q` is a `p`-th power for every `p` with `f(p) = h`, and `m_p = 1` is
  equivalent to the transverse norm
  `Theta_(q,s) = Norm_(F_(2^(q*b))/F_(2^(q*s)))(kappa_q + 1)` containing the
  full `p`-primary part of `2^(q*s) - 1`. The easy top-step Kummer norm lands in
  `F_(2^b)`, where that `p`-part is absent, so it cannot prove the claim.
- The order formulation explains the first weak-formula failures without appealing
  to the production table. In the independent probe, `ord(kappa_9 + 1) =
  3^3*(2^9 - 1)`, so `73 | ord(kappa_9 + 1)` but `19` does not divide it; adding
  `4` changes the order and picks up `19`. This is why the same `Q = {9}` gives
  both `m_73 = 1` and `m_19 = 4`.
- Shipping new values would require an independent oracle, a root-search theorem,
  or a new algorithmic proof. Otherwise the project would be numerology with a
  pleasant API.

Concrete progress targets:
- ~~Decide whether to import more known OEIS/calculator values through `p <= 709` as
  cited data, or keep requiring a local finite-field oracle for each shipped row.~~
  **Done (2026-06-13):** the finite `m_u` table is now the full OEIS A380496 b-file
  (126 rows, odd primes `3..=709`), source-pinned rather than per-row locally oracled.
  The remaining gap is *feasibility* (materializing `alpha_u` for large-`e_u` rows),
  not *coverage*.
- Prove or refute the Conway-Fermat quotient lemma `delta_n = F_n`. This is the
  whole singleton-even arm; the relative norm currently proves only
  `1 < delta_n | F_n`.
- Prove the new-prime lemma for the cubic spine: for every
  `ell^a | Phi_(3^k)(2)`, show `v_ell(ord(gamma_k)) = a`. Old factors already
  propagate down the norm tower, so this is exactly the missing step in `C_k`.
  In its smallest current form: prove that the distinguished root `eta_k` of
  `X^3 + eta_(k-1) X^2 + (eta_(k-1)+1) X + 1` generates the cyclic norm-one
  torus of order `Phi_(3^k)(2)`. A character or power-residue proof must exclude
  `eta_k` from every proper prime-index subgroup; irreducibility alone cannot.
  Precisely, prove `chi_(k,ell)(eta_k) != 1` for every
  `ell | Phi_(3^k)(2)`, or equivalently prove that the reduction modulo `2`
  of the norm-coherent cyclotomic unit `1+zeta_(3^(k+1))` is not an
  `ell`-th power. This is now the smallest named lemma for the cubic arm.
- Evaluate the power-residue symbol of the general transverse norm
  `Theta_(q,s)`. A uniform nonresidue theorem would prove the singleton-one arm
  for the non-cyclotomic chains (`11`, `23`, `29`, `47`, `179`, ...).
- Prove the corresponding new-prime statement `D_k` for the `m = 4` norm on the
  `2*3^k` column; the established twisted norm formula rules out the naive
  induction.
- Keep `m_359`, `m_719`, factorization, and exact-order runs as falsification and
  proof audits rather than the leading route. They remain valuable tests of any
  proposed residue-symbol lemma.
- Build a verified `u`-th-power/root-search oracle for the transfinite field.
- Prove enough about the search to avoid merely empirical extensions.
- ~~Decide what evidence is acceptable for shipping `alpha_53` and beyond.~~ Settled:
  OEIS A380496 (a maintained sequence, values verified upstream by CGSuite's calculator)
  is accepted as source-pinned evidence through `p <= 709`. The next question is what
  evidence justifies rows past `p = 719` (the first OEIS-unknown), which need a fresh
  computation, not a table lookup.

Relevant surfaces:
- `writeups/excess.tex`
- `experiments/ordinal_excess_probe.py`
- `experiments/cyclotomic_3k_family.py`
- `experiments/exception_column_m4.py`
- `src/scalar/big/ordinal/tower.rs`
- `src/scalar/big/ordinal/mod.rs`
- `src/scalar/AGENTS.md`
- `examples/tour.rs`

### off·(e_f∧e_s∧e_c): `transfinite Arf/Witt classification for ordinal-nimber coefficients`

Decide what, if anything, should replace the finite-field Arf/Brauer-Wall bit for
`CliffordAlgebra<Ordinal>` metrics whose coefficients do not all lie in one finite
nim-subfield.

What is implementation, not research:
- Bridge D is the tractable engine bridge: make `Ordinal` usable as a
  checked Clifford coefficient domain on the source-verified tower, and test the
  Clifford relations for genuinely transfinite squares such as `omega`.
- If all metric entries lie in a common finite nim-subfield `F_{2^d} ⊂ On₂`,
  classification should route through the generic finite characteristic-2 Arf
  classifier from Bridge B after detecting that subfield.
- The finite-field answer is an `F₂` bit because the absolute trace
  `Tr_{F_{2^d}/F₂}` exists. That finite-subfield case should stay separated from
  the genuinely transfinite case.

Why this is research:
- For genuinely transfinite ordinal-nimber coefficients there is no finite degree,
  so the finite trace-to-`F₂` definition of the Arf bit does not apply as-is.
- General characteristic-2 quadratic form theory has invariants over the
  coefficient field, such as Artin-Schreier quotient data, but the repo's current
  finite-nimber facade is an `F₂`-valued Arf/BW classifier. Deciding the right
  computable invariant for the represented ordinal-nimber domain is not just
  genericizing `arf_nimber`.
- The implemented ordinal multiplication itself is partial outside the verified
  Kummer tower. Any classifier that needs Artin-Schreier solving, roots, or field
  closure must respect that same source-verified boundary.

Concrete progress targets:
- Define the classification domain exactly: common finite subfields, the
  source-verified transfinite tower, or the ideal full `On_2` nimber field.
- ~~Implement and test common finite-subfield detection so Bridge D can honestly
  delegate those metrics to Bridge B.~~ Done 2026-06-11 as `subfield-detect`
  (git history) — implementation, not research.
- Decide whether genuinely transfinite metrics should expose no classifier, a
  coefficient-field Arf class, a direct-limit finite-subfield invariant, or some
  other replacement for the finite trace bit.
- If an Artin-Schreier quotient or root-search route is chosen, build a checked
  oracle and prove enough about its represented domain to avoid table-driven
  guesses.
- State separately whether a Brauer-Wall class exists on the same surface, and
  whether it agrees with any proposed Arf-like invariant.

Relevant surfaces:
- `src/scalar/big/ordinal/`
- `src/forms/char2/`
- `src/forms/witt/brauer_wall.rs`
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
