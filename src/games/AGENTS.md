# AGENTS.md — `src/games/`

The PILLAR of combinatorial game theory — the second column of the project,
mostly independent of the scalar/Clifford stack (the bridge is the number/nimber
subclasses, where Conway multiplication is defined). Games under disjunctive sum
are an abelian GROUP, not a ring; that constraint is *why* the Clifford story
lives on the scalar backends and not on all games.

> Read `docs/OPEN.md` before touching `coin_turning.rs`, `kernel.rs`, `misere.rs`, or
> the example probes — they preserve the proof history of the resolved Gold
> play-semantics question and still feed independent continuations.

`mod.rs` re-exports every module below flat.

Fixed-width game payloads use `u128`/`i128`: finite nim heaps, octal codes, Grundy
values, and scoring integers. `usize` is for graph nodes, option indices, collection
lengths, and the `Quotient` class machinery (indices, not payloads).

## Values & arithmetic

- **`partizan.rs`** — short partizan games (sum/neg/order/birthday/is_number) + the
  CANONICAL FORM (dominated/reversible reduction; `structural_string` vs
  `canonical_string` — the latter canonicalizes, a value key) + the game↔surreal
  bridge (`number_value`/`from_surreal`, numbers only). Also `Game::ordinal_sum`
  (G:H — Hackenbush strings are these), `Game::nim_heap` (⋆n), `Game::is_all_small`.
  The integer-value-of-a-game logic lives once in `partizan::integer_value` (callers
  route through it, no duplicate inline copies).
- **`number_game.rs`** — transfinite NUMBER games (ω, ε) carried by their Surreal
  value — value/birthday/sum/cmp delegate to surreal, no infinite option tree. Plus
  the FULL transfinite round trip via sign_expansion/from_sign_expansion (the
  run-length sign expansion is the finite encoding of the infinite {L|R} tree).
- **`nimber_game.rs`** — the CHAR-2 MIRROR of `number_game.rs`: transfinite NIMBER
  games (Nim heaps `⋆α`) carried by their `Ordinal` (On₂) Grundy value — grundy/
  add(=nim-add XOR)/cmp/to_finite_game delegate to `Ordinal`, no infinite option
  tree. `neg` is the identity (char 2: every impartial game is self-inverse);
  `turning_corners` is the nim-product (Conway's coin game, `ω³=2`); `None` only when
  a Kummer carry needs a prime past the verified table or at `≥ ω^(ω^ω)`. This is the
  `No ↔ On₂` symmetry at the games layer (the rest lives at the scalar layer via the
  shared CNF core, reaching Clifford through `Scalar for Ordinal` inside the checked
  Kummer boundary). Bound to Python as `NimberGame`.
- **`game_exterior/`** — the exterior algebra of the GAME group: Λ over ℤ on game
  generators (living on all of game-world, incl. non-numbers ⋆/↑ — needs only the
  ℤ-module structure). Split into three layers:
  - `game_exterior/relations.rs` — `GameRelation`, `GameRelationCertificate`,
    `RelationSearchCertificate` + certificate helpers (`pub(super)` to `lambda.rs`
    and `clifford.rs`).
  - `game_exterior/lambda.rs` — `GameExterior` (free Grassmann engine quotiented by
    integer game relations such as `2⋆=0`) + all private helpers; lattice
    normalization in `linalg/integer.rs`.
  - `game_exterior/clifford.rs` — `GameCliffordError` and `GameClifford`: the checked
    integer-valued deformation surface; hand-supplied `q`/polar tables are accepted
    only when every game relation is null and polar-radical, so torsion-free targets
    force the documented vanishings (for example, `2⋆=0` kills `Q(⋆)` and all
    pairings with ⋆). The global game-native question is now resolved negatively:
    ambient coherence across short-game subgroups plus coefficient faithfulness
    forces every torsion game to be square-zero and polar-radical, over every
    coefficient ring (`writeups/game_exterior_divisibility.tex`, kernel-checked in
    `formal/Ogdoad/GameExterior.lean`). Local root-incomplete hand tables remain this
    API's deliberate engineering scope.
  - `game_exterior/mod.rs` — hub; re-exports everything flat so `games::GameExterior`
    etc. remain unchanged.

## Temperature theory

- **`thermography.rs`** — the thermograph of a short game: left/right scaffolds,
  stops, cooling (`cooled_stops`), temperature, and mean (mast) value.
- **`heating.rs`** — game-valued heating, Berlekamp overheating `int_s^t G`, and
  Norton multiplication `G.U` by a positive unit. The `under` pass proved the exact
  positive-dyadic regrading: for `u=m/2^k`, `δ=2^-k`, numeric Norton multiplication
  induces `gr_τ -> gr_{uτ+u-δ}`; `numeric_norton_regrade` and
  `numeric_norton_mean_temperature` compute it without building the product, and
  `numeric_norton_composition_defect` gives the exact nonnegative failure of the
  dyadic action law. The completed separation theorem is stronger: `gr_0` retains
  the nonzero order-2 class `[*]`, so no faithful unital `ℤ[1/2]`-algebra can retain
  the needed residue at all. The game side is a filtered abelian group with external
  numeric transports, not the Newton side's associated graded ring; nonnumeric
  units can fail descent (the explicit unit `↑` is the minimal witness).
- **`atomic_weight.rs`** — atomic weight of ALL-SMALL games (finishes thermography):
  the two-ahead rule (Siegel Constructive Atomic Weight; Larsson–Nowakowski
  arXiv:2007.03949 Thm 10). `aw` IS additive on all-small games.
- **`piecewise.rs`** — `Pl`: exact rational piecewise-linear wall arithmetic used by
  thermography. `add_pl` (pointwise sum) is the tropical `⊗`; `sub_pl` is the arithmetic
  difference (`left_raw − right_raw`) in the meeting-temperature recursion, NOT a
  tropical operation.
- **`tropical_thermography.rs`** — names the latent tropical structure in
  thermography and machine-checks it. The option folds are tropical `⊕` in DUAL
  semirings — the left wall a `(max,+)` fold over the Left options' right walls, the
  right wall a `(min,+)` fold over the Right options' left walls — and cooling is
  tropical `⊗`. `Pl::oplus_max`/`oplus_min`/`otimes` name the wall operations;
  `thermograph_via_tropical` is a parallel recursion pinned EQUAL to
  `thermography::thermograph`. It reuses the identical `pub(crate)`
  freeze/meeting-temperature cooling tail — it only renames the folds, it does not
  reimplement cooling. The `Semiring`/`Tropical<C>` algebra it points at lives in
  `scalar/tropical.rs`.

## Impartial / outcome analysis

- **`coin_turning.rs`** — `nim_mul_mex`: nim-mult as Conway's Turning-Corners mex
  recurrence (a different *definition* from the algebraic `nim_mul`, proven equal).
  Plus general 1-D coin-turning (`grundy_1d`) and the 2-D Tartan product
  (`tartan_grundy`), with the Tartan/Product theorem verified.
- **`grundy.rs`** — general Sprague–Grundy (normal-play impartial center): `mex`
  (the crate's one minimal-excludant — `lexicode.rs` and every other caller route
  through `grundy::mex`, no re-implementations),
  `grundy_graph` (DAG; None on a cycle), closure-based `grundy`. P-position ⟺ g=0;
  SG theorem `g(G+H)=g(G)⊕g(H)` pinned vs Bouton.
- **`kernel.rs`** — normal-play Win/Loss/Draw outcomes of any finite game graph
  (retrograde analysis); `p_positions` = Loss. The interactive route to the open
  question. Plus `scoring_values`: the Milnor minimax `ScoreInterval { left, right }`
  (`i128`) on a DAG — the integer-valued scoring knob. The interactive route was
  part of the historical Gold search; the theorem now lives in the FIFO formalization.
- **`loopy/`** — loopy (cyclic) games, the third escape from XOR-linear P-sets: a
  cyclic rule admits a **Draw** outcome (a genuinely new degree of freedom). Split
  into five layers:
  - `loopy/catalogue.rs` — `LoopyWinner`, `LoopyPartizanOutcome`, `PartizanOutcome`,
    and the `LoopyValue` catalogue (`Zero`/`Star`/`On`/`Off`/`Over`/`Under`/
    `PlusMinus`/`Tis`/`Tisn`/`Dud` plus integer `s&t` tags, with exact
    starter-pair `outcome`, `partizan_outcome`, `sides`, neg/partial order/partial
    sum).
  - `loopy/graph.rs` — `LoopyGraph` (a thin computable wrapper over
    `kernel::outcomes` — loss/win/draw sets).
  - `loopy/partizan.rs` — `LoopyPartizanGraph`: validated finite two-sided
    Left/Right graphs; graph negation, budgeted reachable product sums and finite
    `Game` embedding; turn-expanded stopper detection with cycle witnesses;
    retrograde analysis returning exact starter pairs via `LoopyPartizanOutcome`
    and only projecting to `PartizanOutcome {P,N,L,R,Draw}` when that projection
    is honest.
  - `loopy/nim_values.rs` — `LoopyNimber`, `LoopyNimCertificate`,
    `loopy_nim_values`/`loopy_nim_values_certified`: Draw ⇒ `Side`/∞, else a
    nimber; exact on an acyclic non-Draw subgraph; bounded sidling only when the
    mex fixed point is unique; additive finite-nimber claims require the checked
    `recovery_condition_holds` flag.
  - `loopy/research.rs` — `loopy_decision_sets`/`loopy_quadric_probe`: read a
    cyclic rule's Loss-set AND Draw-set, each fit by `fit_f2_quadratic`.
  - `loopy/mod.rs` — hub; re-exports everything flat so `games::LoopyValue` etc.
    remain unchanged.
- **`misere.rs`** — checked misère-play outcomes (`try_misere_is_n`/`misere_is_p`)
  for finite acyclic impartial games; cycles return `None`. Covers misère Nim vs
  Bouton; the bounded indistinguishability quotient (`misere_quotient`,
  `AbstractGame`, `Quotient`); octal games (`octal_moves`, `octal_misere_quotient`).
  The non-linear route explored during the former open question.
- **`lexicode.rs`** — **Bridge O**, the games ↔ integral edge: greedy binary
  lexicodes `L(n,d)` (Conway–Sloane 1986). `lexicode`/`lexicode_naive`/
  `lexicode_bounded` (+ `LEXICODE_NODE_BUDGET`, an honest backstop → `None`, not a
  silent cap). `LexicodeTurningGame` is the bounded Conway-Sloane move structure:
  positions are packed binary words, legal moves go to smaller words whose changed
  coordinate set has size `< d`, and the zero-Grundy positions are `L(n,d)`. The
  greedy step is exactly `mex(Forbidden)` over radius-`(d−1)` Hamming balls
  (`grundy::mex`); linearity is the Sprague–Grundy theorem, *discovered* not
  assumed. Ships the `[7,4,3]` Hamming, `[8,4,4]` extended Hamming, and `[24,12,8]`
  Golay codes as lexicodes, chaining `turning game → mex → lexicode → Golay →
  Construction A → theta`.
  Also ships `nim_lexicode_naive`/`NimLexicode`, the literal base-`2^k` greedy over
  nim alphabets: closure under coordinatewise nim-addition is verified, and scalar
  closure witnesses the Fermat-base line (base 4/16 pass, base 8 fails).
  **Claim level:** the degree-1 (solved, linear) comparison in the Gold proof
  history; it is not evidence for the separate Witt--FIFO theorem.

## The bridge object

- **`hackenbush.rs`** — red/blue/green Hackenbush: `Hackenbush { edges }` (vertex 0
  is the ground by convention; edges colored by the `Color {Blue, Red, Green}` enum)
  with the `string` stalk constructor, `to_game()` (the universal evaluator),
  `value()` → surreal (blue–red), `grundy()` → nimber (all-green = Nim). The one
  structure tying surreals + nimbers + sign-expansion through a single object.

## Things that look like bugs but are not (games layer)

- **`Game`, `LoopyValue`, `NumberGame`, and `NimberGame` `impl Display`** — that is
  the canonical render now. `Game::display()` and `LoopyValue::name()` survive as thin
  aliases over `Display` for existing callers; `NumberGame`/`NimberGame` never had
  inherent render methods. New code can just `{}`-format.
- **`Game::canonical_string` canonicalizes; `structural_string` does not.**
  `structural_string` is an order-independent fingerprint of the tree *as given* (so
  `(↑−↑).structural_string() ≠ 0`); `canonical_string` reduces first, so it *is* a
  value key. Compare `a.canonical().structural_eq(&b.canonical())` or just compare
  `canonical_string`s.
- **Atomic weight's integer branch is NOT `1 + max_R aw(G^R)`.** It's a predicate
  over `A`'s raw option *games* (`A^R = aw(G^R)+2`) comparing an integer `n` via
  `le`/`fuzzy`, bounded by the *tightest* right option — so it stays correct when an
  option's atomic weight is a fraction (e.g. ½). The naive max-of-integers form
  misreads there. And atomic weight IS additive on all-small games.
- **`nim_mul_mex` is the slow *game* definition (the mex recurrence), for validation
  and small arguments only** — exponential in the argument size. For real computation
  use the algebraic product (`nim_mul`), which it is proven equal to.
- **`nim_moves` takes `&Vec<u128>` (not `&[u128]`) on purpose** (with a `ptr_arg`
  allow): it is passed as a `fn` matching the generic move-generator bound `Fn(&P)`
  with `P = Vec<u128>` in `misere_is_p`/`grundy`, where a `fn(&[u128])` pointer would
  not unify.
- **`Game` stays an acyclic `Arc` tree by construction** (it cannot represent cycles).
  Loopy games are separate `LoopyGraph` / `LoopyPartizanGraph` engines;
  `thermography` is finite-game-only (loopy games never freeze to a number).
- **`Pl` does NOT implement `Semiring`.** A `Pl` wall has no representable ∞-wall
  (the tropical `⊕`-identity), so the semiring law-checking lives on `Tropical<C>`
  (which has `Infinity`), not on `Pl`; `Pl` only gets the named wrappers
  `oplus_max`/`oplus_min`/`otimes` it actually uses. Do NOT fake an ∞-wall with empty
  `pts` — that breaks the `self.pts[0]` invariant `value_at` assumes. The
  `pub(crate)` `walls_with` (which internally calls `freeze`/`meeting_temperature`) is
  shared by `thermograph_via_tropical` so it reuses the identical cooling tail; the
  golden thermography tests pin that this sharing is inert.
