# Cross-pillar bridges — DONE (the go-forward ledger)

The running ledger of cross-pillar work **completed from here on**.

The cross-pillar bridge-building era (bridges **A–O** plus **K** — lattice/Clifford/
Brauer–Wall, the char-2 Arf classifier, Frobenius outermorphisms, the transfinite
Clifford engine, theta/modular forms, Construction-A codes, the Weil representation, the
rational and full-`ℚ/ℤ` Brauer invariants, Newton polygons, the Brown invariant, the
unification pass, lexicodes) closed with every non-deferred bridge shipped, as did the
ogham 0.1.x–0.2.x language work and the transfinite-excess thread. The working-notes summary
of all of it is in the `AGENTS.md` files (root + per-pillar); the historical entry-level
ledger is in git history.

What remains unbuilt is tracked in the two buildable ledgers —
[`COMPLETENESS.md`](COMPLETENESS.md) (completing symmetries and connections already in
the code) and [`CONTINUATIONS.md`](CONTINUATIONS.md) (genuinely new features), each
carrying its slice of the deferred stars `*1`/`*2`/`*4` (`*8` converted to
`CONTINUATIONS.md`'s numbered `ogham-0.3.0` when its sketch landed, 2026-07-09); genuine open problems
stay in [`OPEN.md`](OPEN.md). Solved research questions and their current theorem
boundaries are indexed separately in [`CLOSED.md`](CLOSED.md).

**Naming note (2026-07-15):** the language shipped through 0.3.6 as **ogham**;
it is renamed **grundy** (provisional — finalization at the 0.3.8 release
dress; see [`CONTINUATIONS.md`](CONTINUATIONS.md), the ladder). Entries below
keep the name they shipped under: `ogham-*` keys stay `ogham-*`.

## How to use this ledger

Completed items keep the game-multivector value `g·e_B` they carried as buildable
items — the legend is canonical in [`COMPLETENESS.md`](COMPLETENESS.md) → "How items
are valued" (`g` a game value, `e_B` a pillar blade) — recording what each item was
worth; in disjunctive-sum terms, DONE archives the terms that have been played out
of the live ledger. The completion date moves to the body.

When a new piece of cross-pillar work lands, add a short entry here:

```
## completed items

### <game value>·<blade>: `<name>`
**Completed:** <date>
**Summary:** <one-line what-it-connects>
**Pillars:** … ↔ …    **Claim level:** standard math / implemented-and-tested / …
- surface: the functions/types that shipped
- oracles: the tests that pin it
- boundaries: the honest non-claims
```

Fold the one-line structural fact into the relevant `AGENTS.md`; keep any longer
derivation alongside the code or in a `writeups/` note.

## completed items

### tis·(e_f∧e_g): `all-exponent-gold-diagonal-source`
**Completed:** 2026-08-09
**Summary:** at every power-of-two degree `m ≥ 2`, every Gold exponent,
including even exponents, has a constructive Artin–Schreier source for its full
coordinate diagonal in the canonical nim tower.
**Pillars:** forms ↔ scalar ↔ games    **Claim level:** proved synthesis, implemented-and-tested, kernel-checked algebra
- recursion: in `F_{2^{2M}}=F_{2^M}(u)`, the scaled trace-dual is
  `lambda_{a,c}=(L0+L1)+uL0`, where `L0,L1` are the downstairs duals for the two
  relative-trace blocks.
- descent: at scale `c=1`, `Tr_rel(1)=0`, so `L0=0` and the dual lies in the
  half-field. Its absolute trace upstairs is therefore zero.
- source: finite-field Artin–Schreier exactness gives `lambda=w²+w`, hence
  `Q_a(e_i)=Tr((w²+w)e_i)` for every basis coordinate and every exponent `a`.
- surface: `gold_component_diagonal_dual`, `gold_diagonal_dual`, and
  `gold_diagonal_artin_schreier_source` in `src/forms/trace_form.rs`, with all
  supported tower degrees through 128 covered by the tests.
- proof: `writeups/gold_diagonal_source.{tex,pdf}`; formal core:
  `formal/Ogdoad/GoldDiagonal.lean` checks the tower trace, dual reconstruction,
  absolute-trace descent, and the full Artin–Schreier image-equals-trace-kernel
  theorem without axioms.
- boundary: a general scale `c` need not have trace-zero dual. The separate
  weighted-source Witt--FIFO theorem below closes the natural play-rule and
  P-set realization questions without requiring a general scaled descent.

### tis·(e_g∧e_f): `gold-witt-fifo-normal-play`
**Completed:** 2026-08-09
**Summary:** a fixed, singleton-local normal-play rule has P-set exactly the
zero quadric of every finite `F_2`-valued refinement, while a sharp transcript
theorem identifies the exact observation cost that no torsor-uniform rule can
beat.
**Pillars:** games ↔ forms    **Claim level:** proved synthesis, kernel-checked ingredients
- weighted source: choose a deterministic symplectic-plus-radical basis from the
  public polar form `B`; active adapted coins form a matching and carry only
  public triangular corrections, while a matched pair for each active
  original coordinate uses its singleton refinement bit as a local overlap
  weight.
- identity: `Q_q(x)` is the XOR of adapted public diagonals, original singleton
  source-edge weights, and the parity of active hyperbolic pairs. No dense
  adapted-basis `Q` query or q-dependent loading is used.
- FIFO theorem: on every matching plus isolates, either designated seat keeps
  the opponent front ko-protected or zero-live-degree. Run on the q-blind
  potential matching, this makes every close individually zero, so every
  potential pair overlaps. The same strategy works for every refinement and
  every dimension, without a dummy.
- normal semantics: a unique terminal claim move enabled by `sigma xor phase`
  compiles any finite forced-charge tree to ordinary normal play; with stance
  one the root is P exactly when the forced charge is zero.
- observation boundary: q-blind loading and `(w0,c)=(1,1)` transition access
  satisfy N1--N2. Exactness plus transcript stability forces every observation
  certificate to span `x`, hence `wt(x) <= #queries*w0`; the rule's active
  singleton directions attain that bound. A constant total certificate is
  impossible in unbounded dimension.
- anti-decoration boundary: replacing every terminal by a forced wrapper into
  a refinement-sensitive two-action fork preserves every root outcome. Thus
  the basic reachable, optimal, and unavoidable fork properties cannot define non-tautology; the
  rule's weighted-interaction syntax and access discipline are stated directly.
- formal core: `formal/Ogdoad/FifoMatching.lean` proves the both-seat matching
  strategy; `GoldMatchingAlgebra.lean` proves abstract adapted identities;
  `GoldSemantics.lean` proves the claim-compiler winner recursion;
  `GoldNoEvaluator.lean` proves the span/support bounds; and
  `GoldForkPadding.lean` proves the padding obstruction. They are sorry-free
  ingredient proofs, not one end-to-end encoded arena theorem.
- boundary: the older isolated-dummy arbitrary-graph FIFO conjecture remains a
  strict combinatorial generalization in `writeups/linking_affine.tex`; it is no
  longer load-bearing for Gold.
- artifact: `writeups/goldarf.{tex,pdf}`.

### over·(e_f∧e_g): `brown-game-semantics-reduction`
**Completed:** 2026-08-09
**Summary:** the Brown four-class census is canonically a linearly graded
ordinary-quadratic census, while any ambient-coherent Brown colour of all
short-game values vanishes by two-divisibility.
**Pillars:** forms ↔ games    **Claim level:** proved synthesis, source-pinned input, kernel-checked algebra
- canonical split: every `q : V -> Z/4` is uniquely
  `q = lift(ell) + 2Q`, with `ell=q mod 2` linear and ordinary quadratic
  polar `B_Q=b+ell tensor ell`; conversely every `(ell,Q)` reconstructs `q`.
- phase: `G(q)=((1+i)/2)W(Q)+((1-i)/2)W(Q+ell)`.  For nonsingular `b`, even
  dimension gives `beta=4*Arf(Q)+2Q(a)` with `B_Q(a,-)=ell`; odd dimension
  gives `beta=4*Arf(Q|ker ell)+1/7` from the value on `rad(B_Q)`.
- semantic contract: under synchronized terminal-charge pairing and fixed
  relabelling, the four Brown classes are observationally `(ell,Q)`.  This is
  not a game-tree factorization or a single canonical normal/misère/loopy
  four-way outcome. The weighted-source theorem now supplies the nonlinear
  binary normal-play factor; combining the pair into one four-class outcome is
  a distinct Brown semantic boundary.
- global no-go: inclusion-compatible Brown-law data on finitely generated
  short-game subgroups vanishes after adjoining halves and quarters.  This
  rules out exponent-two additive quotients of full `ShUg`, not its nonzero
  root-incomplete 2-torsion subgroup.
- sharpness/correction: the abelian extension `Z/4 -> Z/8 -> Z/2` carries the
  odd Brown line only relative to a chosen section; a bare central extension
  neither fixes `q` nor supports a verbatim extraspecial abelian obstruction.
- artifact: `writeups/brown_game_semantics.{tex,pdf}`.
- formal core: `formal/Ogdoad/BrownGame.lean` kernel-checks the split,
  corrected polar, converse/round trip, two-divisible collapse, and `Z/8`
  model.  Moews's classification is source-pinned rather than a Lean axiom.

### tisn·(e_g∧e_c∧e_f): `game-exterior-divisibility-collapse`
**Completed:** 2026-08-09
**Summary:** a quadratic datum genuinely attached to short-game values is
Grassmann on all torsion: ambient subgroup coherence and coefficient faithfulness
force every torsion game to be square-zero and polar-radical over every
commutative coefficient target.
**Pillars:** games ↔ clifford ↔ forms    **Claim level:** source-pinned input, kernel-checked synthesis
- theorem: Moews gives `ShUg ≅ ⊕ Z[1/2] ⊕ ⊕ (Z[1/2]/Z)` and power-of-two
  torsion.  For `nt=0`, choose `ny=t` and `nz=x`; then `n²y=0`, so any additive
  grade-one realization has `i(t)²=0` and zero anticommutator with `i(x)`.
  Injectivity of the coefficient map gives `Q(t)=B(t,x)=0`.
- naturality boundary: the result covers one global datum and, equivalently,
  coherent data on finitely generated subgroups with injective maps along
  inclusions.  A hand table on one root-incomplete subgroup remains possible but
  is ambient-dependent and therefore not game-native.
- consequences: characteristic two and torsion coefficient rings do not escape;
  `Sym(M/2M)` vanishes globally because `ShUg=2ShUg`; nonzero nimber Gold forms
  cannot extend coherently to all short games; free-direction mean/atomic-weight
  squares survive through the torsion-free quotient.
- artifact: `writeups/game_exterior_divisibility.{tex,pdf}`.
- formal core: `formal/Ogdoad/GameExterior.lean` kernel-checks the abstract ring
  proof from explicit roots and the coefficient-valued corollaries.  Moews's
  short-game group theorem is an explicit external input, not a Lean axiom.

### off·(e_f∧e_s∧e_c): `transfinite-arf-collapse`
**Completed:** 2026-08-07
**Summary:** full `On₂` needs no transfinite Arf bit: algebraic closure makes
every regular quadratic form hyperbolic and leaves only the polar-radical normal
form data in the singular case.
**Pillars:** forms ↔ scalar ↔ clifford    **Claim level:** standard math, proved synthesis
- theorem: for `rank(B)=2r`, `dim(rad B)=s`, an ordinary `(q,b)` form
  (`metric.a` empty) over full `On₂` is
  `H^r ⊥ 0^s` when `Q|rad=0`, and `H^r ⊥ <x²> ⊥ 0^(s-1)` otherwise; hence
  `W_q(On₂)=0` and every regular quadratic Clifford/Brauer-Wall class is split.
- finite boundary: the `F_{2^d}` Arf bit remains correct relative to that field,
  but dies over `F_{2^(2d)}`; the directed colimit of finite-field classes is
  zero.
- implementation boundary: mathematically every finite metric below
  `omega^(omega^omega)` has a common finite subfield; the backend detects it only
  when the needed excess data and checked degree arithmetic are available.  The
  full-`On₂` theorem does not pretend to supply an in-window root or isometry witness.
- artifact: `writeups/transfinite_arf.tex` / `writeups/transfinite_arf.pdf`.
- formal core: `formal/Ogdoad/Off.lean` kernel-checks Artin–Schreier
  surjectivity, span-preserving hyperbolization of every supplied symplectic
  plane, and the zero-polar radical normal form.  The proper-class-to-set-sized
  reduction and the standard general symplectic decomposition are explicit
  boundaries in `formal/README.md`.

### 2·e_o: `ogham-0.3.6` (the second adversarial pass)
**Completed:** 2026-07-10
**Summary:** the release-gate pass, played same-day as its charter: a
seven-perspective sweep (four sol seats over the `ogham-036-*` gaslamp
threads + three independent implementation reviews, every finding verified
against the live evaluator), a9's decision round (the ladder — 0.3.7 →
0.3.8 → **0.4.0 = the public release** → 1.0.0 higher-order; ogdoad ships
with ogham as front door, crates.io `ogham` being taken; `if/then/else`
replacing the ternary — a9's move; the A+ binder triad; the poly-display
pin reversed; birthday presented-stratum; the docs split), the spec
rewritten as `docs/ogham/spec.md` + `implementation.md` + `README.md`, and
the build in eight gated stages (A–G sol over gaslamp `ogham-v36`, H the
lead close-out; fable gating and committing per stage, 8237a86…).
**Pillars:** ogham ↔ games    **Claim level:** implemented-and-tested
- verdicts: the nine-cell core survived adversarial review (projection
  re-derived from Siegel cell-for-cell; singles project the same difference
  outcome the doubles read; rotation/swap laws structural); the defect
  epicenter was §10.8 display — three independent display-law violations,
  all dead: anchors on every path, SCC condensation emitted
  dependency-first with nontrivial SCCs as adjacent mutual runs,
  collision-safe α-names with provenance validated against the live
  environment.
- language: mutual Element-`=:` systems (adjacent `;`-joined runs, no
  grammar change — pure error→value); total sort-checking at non-strict
  positions (`ones ⧺ true` errors, `ones ⧺ (1/0)` stays `ones`);
  guardedness by the language's own reduction (`g =: [g] ⧺ []` binds;
  `{if true then 0 else dead |}` degenerates); word conditionals (`:` freed
  for 0.3.7's ordinal sum, `?` solely the Bool binder mark); binder marks
  `#i`/`?p`/bare-Element-by-law with minimal-mark display; container
  totality (fixed/graded/free — `[1, 2, 3]` in `fp2[t]`); dyadic game
  literals + the recognition rung (`{0 | 1}` displays `1/2`, structurally);
  `birthday` (presented; the `#3`/`#1` teaching pair) and `integral` (no
  fake defaults); world respelling `fp2[t]`/`fp2(t)` + dim-0 shorthand;
  Display v4 (Poly joins the monomial family); `E_StackDepth`,
  `E_FixpointSort`; budgeted finite→loopy embedding and memoized `≡`
  (shared-DAG hangs → honest errors/fast values); the hint-field sweep.
- oracles: corpus 545 → 796 vectors (the 240-vector 0.3.6 staging slice
  merged plus the 11-vector final-review addendum;
  `conformance_v0.3.6.txt` retained as provenance; 19 blessed vectors
  migrated under five itemized operator-authorized classes; sol's
  end-of-build full-diff review caught one real semantic defect — the
  Element-`=:` reduction path skipped sort-checking, fixed test-first —
  and the stage-H merge/docs nits, all closed same-day);
  `tests/ogham_laws.rs` — seeded stopper-pair projection oracle vs an
  independent survival path, rotation/swap laws on fresh pairs, and the
  42-family display law (display → fresh session → `≡`); 1057 tests.
- boundaries: `canon` on loopy stays `E_Loopy` (fusion is 0.3.8,
  slip-tolerant); one-stopper comparison 0.3.8; games-pillar absorption,
  ordinal sum, and the floor are 0.3.7; mutual *function* groups are
  1.0.0; release packaging (binary, README reversal, gallery, writeup) is
  0.3.8 dress. Release now gates on the ladder, not on this pass.

### 2·e_o: `ogham-0.3.5` (the reflection release; ex-`ogham-reflect`)
**Completed:** 2026-07-10
**Summary:** the pre-release consolidation grown into a full release —
four-perspective reflection (sol adversarial-design + CGT-native reads;
terra implementation audit + cold-user playtest; every claim re-verified
live before acting) found **five real defects in conformance-green
0.3.0** (order-sensitive `≡`/recognition/`canon` falsifying the spec's own
retraction theorem; Index capture lowering to Element; eager `⧺` right
operand against the coinductive claim; a host abort through `:world`
metric parsing; hint-field drift) and produced the unified spec, the
nine-cell outcome relations, and the runtime unification. Designed
(a9 + fable), verified against Siegel by the codex seat, built in six
gated stages (sol over gaslamp thread `ogham-v35`, fable gating),
commits `dca5aba…` onward.
**Pillars:** ogham ↔ games (loopy)    **Claim level:** implemented-and-tested
- surface: `docs/ogham/ogham.md` rewritten as one 19-section contract
  (lisp-for-games identity; presentation<form<value<outcome strata; `=:`
  two-polarity honesty); `#` Index literals + `//`,`/* */` comments;
  `[…]` the two-face container, braces always barred; factorial cut, `!`
  = fuzzy sugar; `up`/`down`/`dim` literal atoms; full-expression ternary
  branches; multiset `≡` (cyclic: unordered bisimulation) + recognition
  chain (`[0]`≡`*1`, `[0,0]`≡`up`, `[*1]`≡`down`); right-lazy `⧺`; the
  nine outcome doubles over `G + neg(H)` product graphs (total on loopy)
  with value singles projected on stopper pairs ({>>,>‿}→>, {><}→∥,
  {<>,<‿,‿>,‿‿}→=, {‿<,<<}→<; Siegel GSM 146 Thm VI.2.1 p. 290, Def
  VI.1.8 p. 284, pinned); total loopy `+`/`-` with synthesized α-bound
  display names; `hasdraw`/`stopper`; witness-carrying `E_Loopy`;
  `E_GraphBudget` (default 2¹⁶, `:graph`/`@graph`); `LoopyPartizanGraph`
  `neg`/budgeted `sum`/turn-expanded stopper detection/outcome pairs;
  one shared `SharedRuntime` over a world-ops trait + persistent guarded
  worker (the world-decl abort killed).
- oracles: the conformance corpus grown ~390 → 550+ statements across
  the migrated 0.3.5-B/C/E families (per-cell witnesses for all nine
  cells, negation-rotation and operand-swap sweeps, the nine-to-four
  projection table, the `over` teaching triple, retraction laws,
  `⧺`-laziness, `#`-capture round-trips); the pillar's 256-graph
  retrograde-vs-independent-strategy-oracle suite; the catalogue pins
  (`on+off` and `over+under` draw/draw; `neg(over)` structurally
  `under`); `ones = ones` and `-ones` as error→value graduations.
- boundaries: `canon` on loopy stays `E_Loopy` (fusion is 0.4.0's item);
  one-stopper biased comparison and sidling stay future work; quote/
  macros/mutation/strings/floats stay never; **release stays gated on
  `ogham-0.3.6`** (CONTINUATIONS) — the second comprehensive adversarial
  pass, plus release scoping (front door vs crate, public name).

### 4·e_o: `ogham-0.3.0`
**Completed:** 2026-07-09
**Summary:** the recursion + games layer — `=:` μ-bindings, fuel-as-steps, the
two containers (Clifford arrays via `coef`/`dim`; game-world lists — cons
`{h | t}`, nil `{|} = 0`, `{1, 2, 3}` sugar, `⧺`/`++` append, `≡`/`===`
structural beside `=` value equality, `canon`), the `game` world over
`games::Game`, and loopy Element-`=:` streams with `drawn()` — designed
(a9 + fable) and built (sol implementing over gaslamp thread `ogham-v3`,
fable gating) in one day.
**Pillars:** ogham ↔ games (+ clifford for the array face)    **Claim level:** implemented-and-tested
- surface: `docs/ogham/ogham.md` §19 (the contract, status **shipped**);
  `src/ogham/{lex,ast,parse,unparse,eval}.rs` + `:fuel`/`@fuel`;
  `GameElement` = finite `Game` ⊕ `Arc`-shared regular graphs flattened into
  `LoopyPartizanGraph` at definition; μ-validation restored to definition
  time via sampled stubs; recursion-depth + data-depth guards keep every
  input an honest error, never an abort.
- oracles: the 129-vector v0.3 slice of `docs/ogham/conformance.txt`
  (hand-verified pre-build, engine-run at merge; `conformance_v0.3.txt` kept
  as blessing/provenance), incl. the grundy acceptance example, the
  `a = b ⟺ canon(a) ≡ canon(b)` coherence, `drawn(dud)`/`drawn(ones)`,
  and the fp5 definition-time regression pin.
- boundaries: §19.6's owed list, staged as the §20 v0.3.1 stub — grown and
  relabeled the v0.4.0 sketch same-day, behind the gate (loopy
  negation/comparison/sum envelope, mutual groups, per-mover outcomes,
  display prettification, trampoline evaluator to retire the conservative
  depth guards); coinductive append was decided and shipped same-day at
  a9's call (`ones ⧺ l = ones`, §19.4.5); `∥` (U+2225) became the
  canonical fuzzy relop same-day at a9's call, with `\` its lexer sugar
  (the TeX reflex, affordable under never-strings) — `|` is the
  structural braceform bar only, its relop reading removed with an
  `E_Parse` hint (§§1–3, §7.7, §11; live corpus re-blessed; the v0.3
  archive's two fuzzy vectors transcribed `| → ∥` under a dated header
  note so the blessed record stays parseable); `⋅` stays `E_WrongWorld` —
  games are a group, not a ring.

### ~6·(e_s∧e_c∧e_f∧e_i∧e_g): `py-sweep-2026-07-03` (the Python face)
**Completed:** 2026-07-03
**Summary:** played [`PY.md`](PY.md) §9 items 1–8 + 10 — the Python-side audit's
truth repairs, path-fossil sweep, guards, common.py consolidation, extraspecial/
demo/stub cleanups, and the archive STATUS-TABLE manifests — in two waves of
file-fenced sonnet agents with lead gates (commits `589ef72`, `3a5d32f`).
**Pillars:** the Python surface of all five    **Claim level:** implemented-and-tested
- surface: `ruff` 571→0 under the new `[tool.ruff]` floor; `common.py` grew
  `nim_mul`/`gold_lam`/`polar_lam`/`gold_table`/`report` and delegates to the
  bound engine; STATUS TABLEs (pinned/oracle/superseded-by/scratch) cover all
  78 archive files; `ogdoad.pyi` gained 30 real signatures.
- oracles: `echo_solver.py selftest` PASS end-to-end; maintained-tier and
  common-importer outputs byte-identical vs baselines; demo output diff =
  exactly the 3 intended lines; `synth_verify`'s closed-form check now asserts
  (and passes) at m=8/16/32.
- boundaries: PY.md §9.9 (the bindings wave) not played; three deliberate
  non-applications recorded in PY.md's header block; three audit findings
  corrected during play (goldarf DOES cite echo_charge_probe — TeX-escaped
  underscores beat the triage grep; the cyclo assert was false-as-written, not
  redundant; skeptic_nogo's /tmp was prose-only).

### ~12·(e_s∧e_c∧e_f∧e_i∧e_g): `revision-sweep-2026-07-02`
**Completed:** 2026-07-02
**Summary:** played both 2026-07-02 revision ledgers — [`CORRECTNESS.md`](CORRECTNESS.md)
(twelve numbered verification items + the one-line-pins/proptest ups) and
[`CONSISTENCY.md`](CONSISTENCY.md) (seven numbered taste items + three up-rosters) — in
four waves of ~19 file-fenced sonnet agents with lead gates between waves and an
independent codex review of the full diff (PASS on every math-load-bearing area; one
comment-only transcription swap found and fixed).
**Pillars:** scalar ↔ clifford ↔ forms ↔ integral ↔ games    **Claim level:**
interpretation (status calls) + implemented-and-tested (no shipped computed value changed;
one conservative-direction algorithm improvement in `unit_pivot_nullspace`)
- surface: default `Scalar::pow` (killed 8 hand-rolled loops; `FiniteField::pow` defaults
  onto it, `Nimber::nim_pow` stays the one override); `Rational::checked_add/mul`;
  `linalg::integer::prime_factors`; the valuation quartet + `rdiv` + `rational_mod_int`
  in `diagonal.rs`; one `binomial_checked`; `Option`-honest `misere_quotient`/
  `octal_misere_quotient`/`isotropy_over_adeles`/`fit_f2_quadratic`/`from_ordinal`/
  `a_n`/`d_n`/`codewords` (+ `CODEWORD_ENUMERATION_BUDGET`); `assert_supported_params`
  for WittVec/Qq/Ramified; encapsulated `DiscriminantCore`/`SpinorRep`/`Cga`/
  `LinearMap.cols`/`WittClass`/`Char2QuadForm` + `Zp`/`WittVec` reduce-in-neg;
  `QuadricFit::bias()`; Display for `WittClassG`/`FunctionFieldBrauerWallClass`/
  `SymplecticInvariants`/`HermitianSignature`/`FiniteHermitianInvariants` (py reprs
  collapsed onto core); `pure_scalar_norm`; engine `//!` headers; flattened
  `local_global/`+`integral/` shelves; `Omnific::from_floor`;
  `ensure_supported_finite_hermitian`; vendored `b380496.txt`.
- oracles: 968 lib tests (was 895 — +73), incl. the vendored-b-file full diff, alpha
  value pins at u∈{73,89}, both Nikulin obstruction branches + a positive
  differently-presented DFS witness, the all-eight-residue ff Brauer–Wall sweep, the
  day-≤2 exhaustive canonical census (22 values), the verified-to-fire char-2
  equal-degree splitter, dim-4 `char2_polar_rank` vs brute force, hopf bialgebra
  compatibility, BW16 orders from Grove's closed form, Kneser generated-labels
  assertion, `bias()` vs exhaustive zero counts, Weyl E6/E7 Coxeter sweep, the
  extraspecial λ-branch, and the full gate (fmt, clippy ×2, cold doc -D warnings,
  `--features python` check+clippy, `maturin develop` + `demo.py`, regenerated
  `ogdoad.pyi`).
- boundaries: `aj-second-engine` stays a9's switch (wording pass done; "source-pinned"
  reserved for external data pins); alpha rows 97..709 remain ordinal-value-unpinned
  behind the newly-discovered u=179 compute cliff ([`OPEN.md`](OPEN.md));
  `weight_enumerator` keeps an infallible signature over a documented budget panic;
  the ~20-type Display policy call and two ordinal-local factor helpers stay open ↑s;
  audit-finding corrections (unit_sign_odd ≠ odd_unit_residue; splitter branch
  selection) are recorded in [`CONSISTENCY.md`](CONSISTENCY.md).

### ~3·(e_s∧e_c∧e_f∧e_i∧e_g): `consistency-sweep`
**Completed:** 2026-06-20
**Summary:** played the 2026-06-20 [`CONSISTENCY.md`](CONSISTENCY.md) taste audit — a
crate-wide hygiene pass that made the newest wing reach back for the substrate the rest of
the crate already established, and unified the local–global place surface.
**Pillars:** scalar ↔ clifford ↔ forms ↔ integral ↔ games    **Claim level:**
interpretation (taste), implemented-and-tested (no mathematical content changed)
- surface: `linalg::integer::gcd`/`gcd_u128` (the one integer gcd; killed 8 copies);
  `is_prime`/`is_prime_power`/`checked_factorial`/`checked_pow2`/`matrix_rank`/`mex`/
  integer-value-of-game all routed to their single canonical home; `engine/basis::grade_k_masks`
  (one blade-mask enumerator); `NiemeierComponentKind::{E6,E7,E8}` + uniform `Option` returns;
  the merged `FunctionFieldPlace<S>` (= `GlobalField::Place`) replacing `FFPlace`/`Char2Place`,
  with char-2 `artin_schreier_*` core names; the `…Record`/`…Invariants` glossary fold
  (`NiemeierRecord`, `KneserMassRecord`, `WeylVersorInvariants`, `OddMilgramInvariants`, …);
  `Display` for the game value types; `Cga::outer_join`; accessor encapsulation
  (`DividedPowerAlgebra::dim()`, `DpVector::terms()`, `LinearMap::n()`); `from_base`,
  `Poly::t`, `assert_supported_params`, `Genus::from_lattice`, `NewtonPolygon::from_coeffs`.
- oracles: the full gate — 913 Rust tests, `clippy --all-targets` (both feature sets),
  cold `cargo doc -D warnings`, `cargo check/clippy --features python`, `maturin develop` +
  `demo.py`, regenerated `ogdoad.pyi`.
- boundaries: Python-facing names kept stable (every rename is internal; bindings track it).
  `WittClassG` and `ext_degree`/`extension_degree` were doc-clarified, not renamed (a rename
  would create trait-method-resolution ambiguity, and they name genuinely distinct invariants).
  The Artin–Schreier symbol stayed mathematically distinct from the Hilbert symbol (additive
  vs multiplicative — it cannot join the multiplicative `GlobalField` trait). One item,
  `precision-K`, was consciously deferred: unifying the `Qp`/`Laurent` precision-param width
  cascades across the whole p-adic const-generic surface, disproportionate to the nit.

### 1·(e_c∧e_i): `weyl-versors`
**Completed:** 2026-06-19
**Summary:** ADE simple roots now act as Clifford Pin versors whose twisted
adjoint action is the Weyl reflection.
**Pillars:** clifford ↔ integral    **Claim level:** standard math,
implemented and tested
- surface: `weyl_simple_root_versors`, `weyl_simple_reflection_map`,
  `weyl_simple_reflection_maps`, `weyl_versor_action_map`,
  `weyl_coxeter_versor`, `weyl_coxeter_action_order`,
  `WeylVersorReport`, and `weyl_versor_report`, plus Python
  `WeylVersorReport` and `weyl_versor_report(family, rank)`.
- oracles: `A2` simple-root versors act by the Cartan reflection matrices and
  have Coxeter order 3; `D4` reports Weyl order 192 rather than the full diagram
  automorphism order 1152 and has Coxeter order 6; `E8` reports
  `E8_WEYL_GROUP_ORDER` and Coxeter order 30. Every simple reflection determinant
  is checked as `-1` via the Clifford outermorphism determinant.
- boundaries: this realizes the Weyl group through its simple Pin generators and
  Coxeter element action; it does not enumerate all elements of large Weyl
  groups such as `E8`.

### 2·e_i: `kneser-neighbors`
**Completed:** 2026-06-19
**Summary:** explicit Kneser `p`-neighbor construction now sits beside the
integral genus and mass surfaces.
**Pillars:** integral    **Claim level:** standard math, implemented and tested
- surface: `kneser_neighbor`, `kneser_neighbors`, `isotropic_lines_mod_p`,
  `KneserNeighbor`, `KneserMassClass`, `KneserMassReport`, and
  `even_unimodular_kneser_report`, plus Python `IntegralForm.kneser_neighbor`,
  `IntegralForm.kneser_neighbors`, and matching module functions/classes.
- oracles: `E8` 2-neighbors stay even, unimodular, and in the same genus; bad
  non-isotropic/composite-prime/odd-lattice lines reject; the rank-8 report
  closes on the single `E8` mass term; and the rank-16 report finds both
  `E8+E8` and `D16+` from Kneser 2-neighbors and verifies
  `1/|Aut(E8+E8)| + 1/|Aut(D16+)| = mass_even_unimodular(16)`.
- boundaries: the constructor is explicit-lattice and denominator-checked. Rank
  24 remains represented by the shipped Niemeier root/glue/Aut catalogue and
  its mass/Siegel-Weil checks, not by generated glued Gram representatives for
  all 23 rooted Niemeier classes.

### 1·e_g: `overheating`
**Completed:** 2026-06-19; numeric associated-graded follow-up 2026-07-20
**Summary:** the games pillar now has game-valued heating, Berlekamp
overheating, and Norton multiplication beside the thermograph/cooling surface.
**Pillars:** games    **Claim level:** standard infrastructure + proved research follow-up, implemented and tested
- surface: `heat`, `norton_multiply`, `overheat`, `is_positive_game`, and
  `integer_game_value`; the follow-up adds `numeric_norton_regrade` and
  `numeric_norton_mean_temperature` plus matching Python `Game` methods.
- oracles: heating fixes numbers and sends `{1|-1}` heated by `2` to `{3|-3}`;
  non-dyadic heating temperatures reject honestly; Norton multiplication by unit
  `1` is the identity, nonpositive units reject, integer-unit Norton products
  have the expected mean, and Berlekamp overheating uses Norton multiplication
  on integer leaves.
- follow-up theorem: every positive dyadic unit `u=m/2^k` induces the exact
  additive regrading `gr_τ -> gr_{uτ+u-δ}` (`δ=2^-k`, or `1` for integers);
  even when a cold noninteger number becomes hot, its image stays strictly below
  the target layer. For integer `n`, shifted thermal height scales by `n`.
- boundaries: this is a family of external additive transports, not a
  multiplicative action and not an internal product on the associated graded.
  Indeed `A_2 A_(1/2)(*)` has temperature `1` while `A_1(*)` has temperature `0`.
  Nonnumeric units can fail descent, and the full residue object remains the narrower
  `under` problem resolved immediately below.

### under·(e_g∧e_s): `thermography-newton-separation`
**Completed:** 2026-07-20
**Summary:** thermography and Newton polygons are two tropical objects, joined by
a genuine filtered shadow but not by one faithful Newton-style dyadic graded ring.
**Pillars:** games ↔ scalar    **Claim level:** proved + implemented and tested
- arbitrary-product theorem: `gr_0` contains the nonzero order-2 class `[*]`.
  Any full dyadic coefficient object has an invertible homogeneous element
  representing 2 (and its `1/2` inverse); lift-compatible action sends `[*]` to
  the initial class of `*+*=0` and therefore kills it.  This covers both an ordinary unital `ℤ[1/2]` algebra and the
  graded initial-form coefficients of a valued dyadic field.
- Norton theorem: if `r_u(τ)=uτ+u-δ_u`, then
  `r_v(r_u(τ))-r_(uv)(τ)=v(1-δ_u)-δ_v+δ_(uv) ≥ 0`, with all zero-defect pairs
  classified.  The pair `u=1/2`, `v=2` has defect `1`, so the individual
  additive Norton transports are not a multiplicative dyadic action in any
  temperature-preserving refinement.
- surface: `numeric_norton_composition_defect`, the expanded
  `experiments/under_descent.py` arithmetic/game audit, and the complete proof in
  `writeups/thermo_newton.tex`; `docs/CLOSED.md` indexes the theorem.
- oracles: the Rust heating suite pins five materialized composition defects;
  the Python probe checks 2,304 positive-dyadic pairs for nonnegativity and the
  exact zero classification, alongside the prior 210 thermic predictions and
  quotient-descent witnesses.
- boundaries: characteristic-2 residue slices, valuation-ring/integer-only
  actions without `1/2`, nonunital/nonassociative structures, and quotients
  killing `[*]` are not ruled out.  Each drops a defining part of the stated
  full-dyadic unification contract, so they are follow-up structures rather than
  counterexamples.

### 1·(e_c∧e_f∧e_i): `heisenberg-weil`
**Completed:** 2026-06-19
**Summary:** the extraspecial char-2 group surface now has its finite
Heisenberg/Pauli representation and projective symplectic-transvection
intertwiners.
**Pillars:** clifford ↔ forms ↔ integral    **Claim level:** standard math,
implemented and tested
- surface: `HeisenbergWeilRepresentation`,
  `HEISENBERG_WEIL_MATRIX_RANK_CAP`,
  `Extraspecial2Group::heisenberg_weil_representation`,
  `heisenberg_weil_representation_f2`, and
  `heisenberg_weil_representation_nimber`.
- oracles: the Pauli action is checked against full multiplication tables on
  the plus/D8 and minus/Q8 cells and a rank-two nonsingular example; the center
  acts by `-I`, generator squares recover `Q`, commutators recover `B`, and
  transvection intertwiners are verified projectively on quotient generators.
- boundaries: this is the finite Stone-von Neumann / Pauli representation layer
  over `F_2`-valued extraspecial data, with dense matrices honestly capped by
  `HEISENBERG_WEIL_MATRIX_RANK_CAP`; it is adjacent to the Gold/Arf `tis`
  proof history but does not itself realize the later weighted-source game
  P-set.

### 2·(e_i∧e_s): `construction-a-p`
**Completed:** 2026-06-17
**Summary:** odd-prime codes now feed the same exact integer-coordinate
Construction-A lattice bridge as the binary code surface.
**Pillars:** integral ↔ scalar    **Claim level:** standard math, implemented and tested
- surface: `PrimeCode<P>` / `TernaryCode`, `PrimeCode::construction_a`,
  `complete_weight_enumerator`, the q-ary Hamming `macwilliams_transform`, and
  `ternary_golay_code`, plus Python `PrimeCode` and `ternary_golay_code`.
- oracles: generic `F_5` code duality and q-ary MacWilliams are checked; invalid
  `P = 2` / composite `P = 9` reject; non-self-orthogonal ternary codes keep the
  `None` Gram-integrality boundary; the extended ternary Golay `[12,6,6]` has weight
  enumerator `1 + 264 y^6 + 440 y^9 + 24 y^12`, and its plain `Z` Construction A
  lattice is odd unimodular rank 12 with minimum 2 and kissing number 264.
- boundaries: the complete weight enumerator is exposed as integer composition
  counts, while the exact MacWilliams transform exposed here is the Hamming/
  Krawtchouk specialization; the Coxeter-Todd `K12` lattice is not the plain
  over-`Z` p-ary Construction A lattice and remains part of the Eisenstein/CM
  lattice continuation.

### 1·(e_f∧e_s): `hermitian-finite`
**Completed:** 2026-06-17
**Summary:** the form-with-involution sibling now has the finite-field rank
classifier beside the Surcomplex signature classifier.
**Pillars:** forms ↔ scalar    **Claim level:** standard math, implemented and tested
- surface: `FiniteHermitianForm<F>` and `FiniteHermitianInvariants`, with Python
  `FiniteHermitianForm` / `FiniteHermitianInvariants` over the fixed even-degree
  finite fields `F_4/F_2`, `F_16/F_4`, `F_9/F_3`, and `F_25/F_5`.
- oracles: odd finite `F_9/F_3`, char-2 `F_16/F_4`, odd-degree rejection, and the
  nimber middle-Frobenius metadata boundary are pinned in Rust tests; the Python
  demo exercises the `F_9/F_3` runtime dispatcher.
- boundaries: the finite classifier uses the middle Frobenius on finite fields of
  even prime-field degree, so it honestly represents `F_{p^{2k}}/F_{p^k}` without
  pretending the existing `FieldExtension` trait has an intermediate-base associated
  type; Surcomplex Hermitian forms keep their separate signature classifier.

### 1·e_f: `bw-function-field`
**Completed:** 2026-06-17
**Summary:** the graded Brauer-Wall class now has the exact odd-characteristic
function-field mirror of the rational Wall-coordinate surface.
**Pillars:** forms    **Claim level:** standard math, implemented and tested
- surface: `FunctionFieldBrauerWallClass`, `FunctionFieldBrauer2Class`,
  `function_field_signed_discriminant_class`, `hasse_brauer_class_ff`,
  `clifford_brauer_class_ff`, and `bw_class_function_field`, with
  `ClassifyBrauerWall` generalized to an associated return type so
  `Metric<Rational>` and `Metric<RationalFunction<F_q>>` expose their richer
  global-field BW classes through `.bw_class()`.
- oracles: the rank-2 form `⟨t,2⟩` over `F_5(t)` has Clifford Brauer component
  the quaternion `(t,2)`, ramified exactly at the `t`-place and infinity;
  Wall's twisted group law is checked against `Metric::direct_sum`; radical
  projection matches the nonsingular core; and signed discriminants are compared
  modulo global squares.
- boundaries: this is the exact odd-characteristic `F_q(t)` surface using the
  shipped tame Hilbert-symbol place layer; characteristic-2 function fields stay
  on the separate Artin-Schreier/local-global path, and wild norm-residue
  symbols remain the deferred `*4` work.

### 1·(e_c∧e_f∧e_i): `extraspecial`
**Completed:** 2026-06-17
**Summary:** characteristic-2 Arf data now has the executable extraspecial
2-group central extension whose commutator is the polar form and whose squaring
map is the quadratic form.
**Pillars:** clifford ↔ forms ↔ integral    **Claim level:** standard math,
implemented and tested
- surface: `Extraspecial2Group`, `ExtraspecialElement`, `ExtraspecialType`,
  `ExtraspecialError`, `extraspecial_group_f2`, and
  `extraspecial_group_nimber`.
- oracles: the hyperbolic plane gives the plus/D8 cell, the anisotropic plane
  gives the minus/Q8 cell, group multiplication is checked for associativity and
  inverses on the order-8 cells, `[x,y] = B(x,y)` and `x^2 = Q(x)` are verified
  directly, and the nimber-metric route agrees with `arf_nimber`.
- boundaries: this is the standard group-extension side of the Gold/Arf
  reframing over `F_2`-valued metrics; the later weighted-source construction
  realizes `Q` as a P-set, while higher finite char-2 fields
  still route through the existing Arf classifiers rather than this bitmask
  extraspecial object.

### 2·e_f: `tame-symbols`
**Completed:** 2026-06-16
**Summary:** Bridge K now has the tamely ramified Kummer symbol beside the
unramified cyclic invariant.
**Pillars:** forms    **Claim level:** standard math, implemented and tested
- surface: local `tame_symbol_exponent` / `tame_symbol_invariant` over
  `ResidueField` legs with finite residue fields, plus the `F_q(t)` helpers
  `try_tame_symbol_exponent_ff`, `try_tame_symbol_invariant_ff`,
  `tame_symbol_invariants_ff`, and `tame_symbol_invariant_sum_ff`, with Python
  parity for the local and `*_ff` surfaces.
- oracles: the `n = 2` slice matches the existing `Q_p` / `F_q(t)` Hilbert
  symbols, the `a^v(b)/b^v(a)` convention is pinned by inverse swap tests,
  `Q_9` reads the extension residue field `F_9` and its `μ_8`, and the
  `F_5(t)` `μ_4` symbol satisfies reciprocity using one constant-field root
  convention across finite places and infinity.
- boundaries: this is the tame Kummer case `μ_n` in the residue/constant field;
  wild norm-residue symbols remain the deferred `*4`, and the function-field
  helpers stay on the existing odd-characteristic `F_q(t)` place layer.

### 1·e_i: `constructions-bd`
**Completed:** 2026-06-16
**Summary:** the code-to-lattice bridge now includes classical Constructions B
and scaled D beside Construction A.
**Pillars:** integral    **Claim level:** standard math, implemented and tested
- surface: `BinaryCode::contains`, `BinaryCode::construction_b`, and
  `construction_d`, plus Python `BinaryCode.contains`,
  `BinaryCode.construction_b`, `BinaryCode.construction_d`, and module-level
  `construction_d`.
- oracles: `B(Golay)` is even rank 24 with determinant 4, no norm-2 roots, and
  an exhibited norm-4 vector; one-level Construction D reproduces
  `construction_a`; non-nested towers reject; and `0 <= H_8` gives the expected
  two-level even lattice with determinant 256 and minimum 4.
- boundaries: Construction B is the classical doubly-even sublattice of
  Construction A, not the glued full Leech lattice; Construction D is the scaled
  increasing equal-length binary-code tower and keeps the same `None` boundary
  for invalid or non-integral Grams as the existing Construction A surface.

### ½·e_i: `reed-muller`
**Completed:** 2026-06-17
**Summary:** Reed-Muller codes now give the named Construction-D route to
the Barnes-Wall lattice `BW16`.
**Pillars:** integral    **Claim level:** standard math, implemented and tested
- surface: `reed_muller_code(order, variables)` builds `RM(order, variables)`
  from squarefree monomial evaluations over `F_2^m`, and `barnes_wall_16()`
  returns the Construction-D lattice from the Reed-Muller tower; Python mirrors
  both as `BinaryCode.reed_muller`, module-level `reed_muller_code`, and
  `barnes_wall_16`.
- oracles: `RM(r,4)` has dimensions `1,5,11,15,16`, minimum distances
  `16,8,4,2,1`, and the expected nesting chain. In the crate's scaled
  Construction-D convention the determinant-256 Barnes-Wall normalization is
  `RM(0,4) <= RM(2,4)`, with minimum 4 and kissing number 4320; the adjacent
  `RM(1,4) <= RM(2,4)` tower is separately pinned as the even unimodular
  rank-16 normalization with determinant 1, minimum 2, and kissing number 480.
- boundaries: the Reed-Muller generator matrix is generated, not a curated
  runtime table; invalid orders or unallocatable explicit matrices return
  `None` / `ValueError`. This is the code/lattice route that the later
  `clifford-lattices` certificate consumes, not by itself the Clifford-group
  invariant proof.

### 2·(e_c∧e_i): `clifford-lattices`
**Completed:** 2026-06-18
**Summary:** the Clifford-to-integral direction now has an explicit BW16
certificate.
**Pillars:** clifford, integral    **Claim level:** standard math, implemented and tested
- surface: `clifford_barnes_wall_16_numerator_rows`,
  `clifford_barnes_wall_16`, `clifford_barnes_wall_16_report`,
  `CliffordBarnesWall16Report`, and the constants
  `BW16_AUTOMORPHISM_GROUP_ORDER`, `BW16_REAL_CLIFFORD_GROUP_ORDER`, and
  `BW16_AUTOMORPHISM_INDEX_IN_CLIFFORD_GROUP`; Python mirrors the lattice,
  rows, report, and constants.
- oracles: the numerator rows use the real spinor weight basis indexed by
  `F_2^4`, quadratic-phase sign rows from a basis of `RM(2,4)`, and the
  coordinate weight rows `4e_x`; after the divisor `4`, their Gram is exactly
  the existing `RM(0,4) <= RM(2,4)` Construction-D `barnes_wall_16()` Gram,
  with determinant `256`, minimum `4`, and kissing number `4320`.
- boundaries: the report records `|Aut(BW16)| = 89,181,388,800` and the full
  real Clifford group order `|C_4| = 178,362,777,600` separately; for the usual
  BW16 lattice, the automorphism group is the index-2 Clifford/BRW subgroup,
  not the full `2_+^(1+8).O^+(8,2)` group.

### 2·e_c: `spinor-gauge`
**Completed:** 2026-06-16
**Summary:** characteristic-0 spinor reps and reversion now pass through the
antisymmetric general-bilinear gauge.
**Pillars:** clifford    **Claim level:** standard math, implemented and tested
- surface: `CliffordAlgebra::reverse`, `spinor_rep`, and `lazy_spinor_rep` now
  accept characteristic-0 `Metric::general(q, b, a)` by transporting through the
  matching ordinary `(q, b, a=0)` gauge; Python inherits the same behavior.
- oracles: the internal gauge transport is pinned against the shipped
  `reduce_word` oracle on ordered generator words, checked as a multiplicative
  transport on blade products, and exercised by transported reversion and
  spinor-action reconstruction tests.
- boundaries: characteristic-2 metrics still reject nonzero `a`; the gauge
  transport remains an internal engine bridge, not a new public classification
  API; spinor representations keep the existing nondegenerate / nonsingular and
  explicit-matrix dimension caps.

### 2·e_f: `bw-rational`
**Completed:** 2026-06-15
**Summary:** the rational Clifford invariant now lifts to the graded
Brauer-Wall class `BW(ℚ)` through Wall's exact-sequence coordinates.
**Pillars:** forms    **Claim level:** standard math, implemented and tested
- surface: `RationalBrauerWallClass`, `bw_class_rational`,
  `rational_signed_discriminant_class`, plus Python
  `RationalBrauerWallClass` / `bw_class_rational`.
- oracles: the class projects to Bridge F's ungraded `c(q)`, carries the
  `Z/2 × ℚ*/ℚ*²` quotient as dimension parity plus signed discriminant, obeys
  Wall's twisted product under direct sum, and extends along `ℚ -> ℝ` to the
  existing Bott index `bw_class_real`; the rational `<-1>` generator walks the
  order-eight real clock.
- boundaries: this is the graded rational BW class, not a replacement for the
  ungraded `Brauer2Class` / full `BrauerClass` surfaces; singular rational
  metrics are projected to `Q/rad`; tame and wild cyclic symbols remain on their
  separate Bridge K docket items.

### 1·e_g: `lexicode-game`
**Completed:** 2026-06-15
**Summary:** Bridge O now has the explicit Conway-Sloane turning-game witness whose
zero-Grundy positions are the binary lexicode `L(n,d)`.
**Pillars:** games    **Claim level:** standard math, implemented and tested
- surface: `LexicodeTurningGame`, `lexicode_turning_game`,
  `LEXICODE_TURNING_GAME_NODE_BUDGET`, plus bounded turning-mask, move-graph,
  Grundy-value, and P-position methods.
- oracles: legal moves are checked as lower lexicographic Hamming turns; the
  explicit successor graph agrees with the generic `grundy_graph`; zero-Grundy
  positions reproduce the greedy scan across small `(n,d)` windows and pin the
  `[7,4,3]` / `[8,4,4]` Hamming examples.
- boundaries: the explicit SG route is a bounded witness and inspection surface,
  not the production constructor for large codes; `lexicode(24,8)` remains the
  optimized Golay path, and this solved degree-1 bridge is independent of the
  later weighted-source Witt--FIFO resolution of the Gold play-rule question.

### 2·e_i: `odd-lattices`
**Completed:** 2026-06-15
**Summary:** Type I lattices now have the odd discriminant `Q/Z` surface, the
oddity-corrected Milgram/van der Blij verifier, Type I Construction A witnesses,
and a norm-indexed level-4 theta head.
**Pillars:** integral    **Claim level:** standard math, implemented and tested
- surface: `OddDiscriminantForm`, `OddMilgramReport`, `odd_milgram_report`,
  `verify_odd_milgram`, `IntegralForm::theta_series_level4`,
  `BinaryCode::direct_sum`, `repetition_code`, `type_i_z2_code`, and
  `type_i_z2_plus_e8_code`, plus matching Python bindings.
- oracles: `Z`, `⟨3⟩`, `⟨1⟩⊕A_1`, and `Z⊕E8`-style odd lattices verify
  `signature ≡ oddity - p_excess (mod 8)`; `q_L` is checked modulo `Z` on
  `⟨3⟩`; Type I Construction A from the `[2,1,2]` repetition code gives an
  odd unimodular rank-2 lattice with minimum 1 and kissing number 4; and
  `theta_series_level4` pins the `Z` and `Z^2` norm counts.
- boundaries: the original `DiscriminantForm`, Weil `S`/`T`, Brown slice,
  Nikulin discriminant-form isomorphism, and `theta_series(q^{Q/2})` remain
  even-lattice surfaces; odd theta is exposed only as the norm-indexed
  level-4 head, not as level-`N` modular-form identification.

### 2·e_i: `niemeier`
**Completed:** 2026-06-12
**Summary:** the rank-24 even-unimodular genus now has the Niemeier catalogue and the
non-degenerate Siegel-Weil identity against `E12`.
**Pillars:** integral    **Claim level:** standard math, implemented and tested
- surface: `NiemeierComponentKind`, `NiemeierRootComponent`, `NiemeierClass`,
  `NIEMEIER_CLASSES`, `niemeier_classes`, `niemeier_mass_sum`,
  `niemeier_weighted_theta_average`, and `eisenstein_e12`.
- oracles: the 24 class labels are unique; rooted classes have rank 24 and equal
  Coxeter-number components; `glue^2 = det(root lattice)`; root-lattice constructors
  match the catalogue determinants; anchor automorphism orders pin Leech, `A_1^24`,
  and `E_8^3`; `Σ 1/|Aut(N)| = mass_even_unimodular(24)`; and
  `(Σ θ_N/|Aut(N)|)/mass(24) = E12` exactly through the q-expansion check.
- boundaries: the 23 rooted classes are represented by the standard root/glue/Aut
  catalogue and Venkov weight-12 theta formula, not by 23 explicit glued Gram
  constructors; `leech()` remains the explicit rank-24 Gram constructor.

### 2·e_i: `padic-symbols`
**Completed:** 2026-06-12
**Summary:** Conway-Sloane `p`-adic genus symbols now give exact integral-lattice
genus comparison, with the canonical 2-adic train/compartment/oddity reduction
exposed on the Rust and Python `Genus` surface.
**Pillars:** integral    **Claim level:** standard math, implemented and tested
- surface: `Genus::of`, `Genus::symbol_at`, `Genus::canonical_symbol_at`,
  `are_in_same_genus`, and Python `Genus.canonical_symbol_at`.
- oracles: odd-prime determinant-square-class symbols, Sage/Allcock-style 2-adic
  canonical-symbol examples, random unimodular-congruence invariance, `Z^8` vs
  `E8`, `E8⊕E8` vs `D16+`, and Nikulin/discriminant-form agreement across the
  ADE zoo and Milnor pair.
- boundaries: full spinor-genus computation and level-`N` theta machinery stay on
  their separate docket items.
