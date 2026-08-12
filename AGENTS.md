# AGENTS.md — ogdoad

Working notes for agents editing this repo. Global rules still apply. This file is
the **summary**; each `src/` pillar has its own `AGENTS.md` with the file-by-file
breakdown and the layer-specific "things that look like bugs".

## What this is

Clifford algebras (with nilpotents) over commutative scalar worlds adjacent to
Conway's combinatorial games. Games under disjunctive sum are an abelian group,
**not a ring** — Conway multiplication is only defined on the number/nimber
subclasses. A Clifford algebra needs a commutative scalar ring, so the direct
game-valued Clifford story only lives on the field-like cores (nimbers, surreals,
surcomplex). The repo also carries comparison scalar worlds (Fp/Fpn, Zp/Qp/Qq,
Laurent, ramified/Gauss functors, an adelic precision model, and the exact global
function field `F_q(t)` = `RationalFunction` over `Poly` = `F_q[t]`) for form-theory
experiments. A pure Rust math core, generic over a `Scalar` trait, with PyO3
per-backend bindings on top. "With nilpotents" = the quadratic form may be
degenerate (`q[i]=0` ⇒ `eᵢ²=0`); all-zero `q` is the exterior/Grassmann algebra.

## Layout — the four pillars + bindings

`src/lib.rs` is the crate root: the four pillars + the (feature-gated) `py` module.
Each pillar's `mod.rs` re-exports its children flat, so public paths stay shallow
(`scalar::Nimber`, `clifford::Metric`, …).

| dir | pillar | detail |
|---|---|---|
| `src/scalar/`   | commutative coefficient worlds (the `Scalar` trait + every backend) | [`src/scalar/AGENTS.md`](src/scalar/AGENTS.md) |
| `src/clifford/` | the multivector engine + the GA layer | [`src/clifford/AGENTS.md`](src/clifford/AGENTS.md) |
| `src/forms/`    | quadratic forms & invariants, by the char trichotomy plus local-global and integral layers | [`src/forms/AGENTS.md`](src/forms/AGENTS.md) (+ [`integral/`](src/forms/integral/AGENTS.md)) |
| `src/games/`    | combinatorial game theory | [`src/games/AGENTS.md`](src/games/AGENTS.md) |
| `grundy/`       | the grundy expression-language crate at v0.3.6 — an UNPUBLISHED workspace member (`publish = false`; the ogdoad crate ships without it, and the name stays provisional till 0.3.8 — renamed from ogham 2026-07-15). Depends on ogdoad's public API only; carries its own `examples/repl.rs`, `tests/`, and `docs/` (spec + conformance corpus). Content: lex/parse/unparse + `session`, `runtime/` — the shared evaluator, one Index evaluator, `Apply`, `RuntimeState` — and `worlds/` incl. `game/`; mutual Element-`=:` systems with self-contained SCC equation display; word conditionals `if/then/else`; binder mark triad `#`/`?`/bare-Element; container totality fixed/graded/free; dyadic game literals; `birthday`/`integral`; world names `fp2[t]`/`fp2(t)` + dim-0 shorthand; budgeted embeddings, `E_StackDepth`/`E_FixpointSort` | root rules |
| `src/py/`       | PyO3 bindings (feature = "python") + the binding-scope policy | [`src/py/AGENTS.md`](src/py/AGENTS.md) |
| `src/linalg/`   | crate-private shared linear algebra | [`src/linalg/AGENTS.md`](src/linalg/AGENTS.md) |

`formal/` is the separately pinned Lean 4 + mathlib proof-kernel experiment:
`Ogdoad/Off.lean` formalizes the load-bearing algebra of the resolved full-`On₂`
classification through a set-sized algebraically closed char-2 proxy;
`Ogdoad/Excess.lean` formalizes the exceptional Lenstra-excess column's
unconditional lower bound, corrected norm, exact cyclic/finite-field power
criterion, finite factor/order screens, and open `D'_k` target;
`Ogdoad/Fifo.lean` formalizes the exact reduced FIFO game, its terminating
strategy semantics, cut invariant, and edgeless base theorem, while leaving the
general isolated-dummy proposition explicitly open;
`Ogdoad/GoldDiagonal.lean` kernel-checks the quadratic-tower trace blocks,
dual reconstruction, absolute-trace descent, and the full finite-field
Artin--Schreier image-equals-trace-kernel theorem
behind the all-exponent Gold diagonal source;
`Ogdoad/FifoMatching.lean` proves the both-seat zero-flip theorem for every
matching-plus-isolates board, formalizes the public-matching induction
parameterized over all edge-deleted submatchings, and connects it to adapted
hyperbolic coordinates;
`Ogdoad/ImpartialRealizer.lean` proves the pass-free matching transition, exact
even core clock, both-seat safe-front induction, and impartial charge-tail
compiler resolving the uniform realizer problem;
`Ogdoad/GoldMatchingAlgebra.lean` proves the adapted-basis quadratic expansion;
`Ogdoad/GoldSemantics.lean` preserves the earlier phase-aware partizan compiler
as a comparison surface; `Ogdoad/GoldNoEvaluator.lean` proves the sharp transcript-span and
query-weight lower bounds; `Ogdoad/GoldBlockCompression.lean` proves the
induced-instance algebra behind the every-width block-compression attainment;
`Ogdoad/GoldForkPadding.lean` proves that unavoidable
strategic-fork padding cannot certify non-tautology; and
`Ogdoad/GameExterior.lean` kernel-checks the root-collapse lemma and the
coefficient-faithful quadratic/polar consequences resolving `tisn`; and
`Ogdoad/BrownGame.lean` kernel-checks the canonical
`q = lift(ell) + 2Q` Brown split, its converse, the two-divisible global
collapse, the section-framed `Z/8` sharpness model, and the intrinsic partizan
selector resolving the full finite-space semantic content of `over`.  See
`formal/README.md` for the proof/non-proof boundary.

Beyond the library: `examples/` (Rust demos `tour`/`tropical` and the
research probes `interactive_kernel`, `octal_hunt`,
`loopy_quadric`, `misere_quotient`, `bent_route`; the grundy REPL lives in the
grundy crate — `cargo run -p grundy --example repl`), `experiments/` (Python research probes on top of the shipped
lib, two-tier by maintenance bar: top-level `experiments/*.py` + `scripts/` are
maintained — guards, type hints, docstrings, held to the Rust side's own bar —
while `experiments/{gold,audit,excess}/` is a rescued archive from the 2026-06-10
fable-fleet run, judged file-by-file in the STATUS TABLE each of those three
directories' `README.md` carries (`pinned`/`oracle`/`superseded-by`/`scratch`);
`docs/PY.md` is the audit ledger tracking both tiers), `demo.py` (the Python tour),
`docs/` (OPEN.md — the genuine research problems; COMPLETENESS.md — the game-valued
ledger of buildable items completing symmetries/connections already in the code;
CONTINUATIONS.md — the game-valued ledger of buildable items that are genuinely new
features (the grundy language work, the char-`p` Drinfeld mirror); the deferred stars
`*1`/`*2`/`*4` split across those two (`*8` — ogham 0.3.0 — converted when its
sketch landed and **shipped** the same day, 2026-07-09; see DONE.md); DONE.md — the go-forward ledger for new
work; CONSISTENCY.md — the aesthetic/structural ledger; CORRECTNESS.md — the
verification-status ledger (machine-verified / source-pinned / asserted); TABLES.md —
the inventory of curated hardcoded tables),
`grundy/docs/` (**split at the 0.3.6 pass, 2026-07-10**; moved from
`docs/grundy/` into the grundy crate at the workspace split, 2026-07-16:
spec.md — the
normative v0.3.6 language contract (the lisp-for-games identity,
grammar/precedence/sorts with the binder mark triad, worlds incl.
`fp2[t]`/`fp2(t)` spelling and container totality, the game world's
presentation<multiform<value strata with outcome-as-observation, dyadic
literals, mutual `=:` systems, self-contained equation-system display,
word conditionals, Display v4, errors, the three-part conformance suite);
implementation.md — the runtime architecture + resource-guard contract;
README.md — the transcript-first tour;
stance.md — non-normative (2026-07-19): the design tradition named —
total/codata (Turner, Agda-kin), lazy exactly where the objects are
coinductive, **⊥ refused** (divergence is a budgeted error, never a
value); cyclic vs productive coinduction split (loopy graphs =
eventually-periodic, 0.3.8 w/ Honsell–Lenisa; productive streams = 1.0.0
higher-order, `ω` genetically needs a generator); Haskell the
acknowledged cousin, not the semantics. The
**ladder** — 0.3.7 structural rung → 0.3.8 loopy-envelope completion +
release dress → 0.4.0 = the public release → 1.0.0 higher-order — lives
in CONTINUATIONS.md;
conformance.txt — the hand-verified corpus the language must pass (v0.3.6
merged), with conformance_v0.2/0.3/0.3.5/0.3.6.txt as
merged blessing/provenance, plus grundy/tests/laws.rs — the seeded law
tests (display round-trips, projection oracle, rotation laws) — and
grundy/tests/conformance.rs, the corpus runner),
and `writeups/`
(`goldarf.tex` — the unified flagship paper, "Quadratic Refinements in Normal
Play: Realization and the Observation Boundary" (merged 2026-08-12): the
resolved impartial Gold/Arf normal-play theorem with the Tier-2 no-go history
and pass-free weighted-source Witt--FIFO construction, the absorbed sharp all-exponent
diagonal-source criterion with closed trace-dual basis and tower-recursive
Artin--Schreier solver, the Brown-selector section (intrinsic partizan
outcomes for all four `Z/4` residues), and the game-exterior appendix
(ambient-coherent obstruction, `⋂ₖ4ᵏR` sharpening, framed as the negative
answer to Altman--Lipparini Problem 5.3(j)) — this one file absorbed the
retired `gold_diagonal_source.tex`, `brown_game_semantics.tex`,
`game_exterior_deformation.tex`, `game_exterior_divisibility.tex`, and
(2026-08-12) the block-compression note `observation_width.tex` (as the
every-width attainment corollary `cor:blocks`);
`excess.tex` — the
consolidated note on the transfinite nim excess problem;
`linking_affine.tex` — the proof-frontier note for the general FIFO linking
theorem: vector live-star score, affine-response equivalence, parity-cell
subclass, homogeneous response recursion, cut-space/two-graph and poison
filtrations, the correlated cut/continuation moment, initial cut contraction,
the two-bit handshake refinement, two-switch tail, the false
childwise/full-fan/bounded-support inductions, and the exact still-open global
odd-flow lemma;
`impartial_realizer.tex` — the resolved standalone theorem note for the
pass-free impartial construction, folded into the flagship the same day;
`extraspecial_model.tex` — the remaining flagship-residual frontier note for
the game-native extraspecial `E_{Q_a}` model (structural demands fixed;
ordinal-sum/`Q_8` quotient probe named); a third
note, `observation_width.tex`, lived hours — its block-compression
proposition survived a sol-tier adversarial consult the same day and was
absorbed into goldarf as the every-width attainment corollary `cor:blocks`
(kernel-checked algebra in `formal/Ogdoad/GoldBlockCompression.lean`; note
retired, survives in git history);
`thermo_newton.tex` — restructured 2026-08-12 as a theorem-first note centered
on the Norton thermic law `temp(G.u) = u·temp(G) + (u−δ_u)` with its
composition-defect classification, the tropical-shadow no-go demoted to a
closing section;
`transfinite_arf.tex` — the resolved quadratic-classification theorem, revised
2026-08-12 to state the result over any perfect Artin--Schreier-surjective
characteristic-2 field with full `On₂` as corollary: every nonsingular form is
hyperbolic, the quadratic Witt group vanishes, and
`(dim V, dim rad B, dim rad Q)` is the complete singular invariant).

## Claim levels and non-claims

Use these labels when changing prose, papers, examples, or comments:

- **Standard math**: external facts such as Sprague-Grundy, the Turning-Corners
  product theorem, Arf classification of nonsingular binary quadratic forms, the
  Gold rank formula, zero-count formulas over `F_2`, local Hilbert/Artin-Schreier
  reciprocity, and Conway-Sloane lattice theory.
- **Implemented and tested**: statements backed by the Rust tests, examples, Python
  experiments, or the `demo.py` tour in this checkout.
- **Proved synthesis**: the pass-free weighted-source Witt--FIFO theorem makes
  "Arf is a win-bias" literal for its impartial normal-play P-set; the transcript-span theorem gives
  the sharp observation boundary, while the standard Arf zero-count is external
  math and the formal files check independent proof ingredients rather than one
  end-to-end arena theorem.
- **Open**: transfinite nim multiplication beyond the source-verified excess
  table, the now-optional arbitrary-graph FIFO strengthening, and the
  flagship's game-native `E_{Q_a}` model. These live in `docs/OPEN.md`; the
  impartial uniform realizer and observation width above weight one both closed
  2026-08-12. The
  game-native `GameExterior` deformation question was resolved negatively under
  ambient subgroup coherence on 2026-08-09.

Scope boundaries to preserve:

- Not a Clifford algebra over arbitrary partizan games. A Clifford algebra needs a
  commutative scalar ring; the full game group is only an abelian group.
- Not a new classification theorem for all characteristic-2 Clifford algebras over
  arbitrary fields. The code computes Arf and Brauer-Wall data for `Nimber`,
  supported `Fpn<2,N>` fields, and the documented finite ordinal windows; it rejects
  singular metrics where a nonsingular Witt/BW class is required, and keeps
  rank/radical data explicit.
- Not a proof of the arbitrary-graph isolated-dummy FIFO conjecture. Gold uses a
  public Witt frame and singleton-weighted source pairs, reducing its boards to the
  separately proved matching-plus-isolates class.
- Not an algebraically closed finite backend. `Nimber(u128)` is `F_{2^128}` and
  contains only finite nimber subfields whose degrees divide 128.

## The symmetries (the intellectual spine — see README)

The two pillars are complementary views of the *same* table of numbers:
`scalar/` groups **by place** (each field beside its ring of integers); `forms/`
cuts ACROSS by **characteristic** (the one classification theory, three ways). The
recurring symmetries the project is built around:

- **char 0 ↔ char 2** classifiers (the real 8-fold table mirrored by Arf/Brauer–Wall).
- **surreal No ↔ ordinal On₂** (char-0 field and char-2 non-field sharing one CNF core).
- **(field, ring of integers)** pairings, made structural in `scalar/integrality.rs`.
- the **2×2 functor table** (algebraic|transcendental × residue|value-extending),
  with cyclic Galois/Frobenius maps also feeding Clifford outermorphisms.
- **local ↔ global** (the Springer trio + the local-global Hasse–Minkowski layer).

## Implemented mathematical state

The scalar landscape is broad, but not all backends have the same exactness claim:

| backend | role |
|---|---|
| `Nimber(u128)` | finite nim-field `F_{2^128}` with nim add/mul; main char-2 backend |
| `Surreal` | finite-support Hahn/CNF char-0 backend; real-table classification only on represented exact square classes |
| `Surcomplex` | `Surreal[i]`; complex-table classification only on represented exact square classes |
| `Integer`, `Omnific` | coefficient rings for exterior/nilpotent structures |
| `Fp`, `Fpn`, `Zp`, `WittVec` | comparison scalar worlds for the characteristic trichotomy |
| `Qp`, `Qq`, `Laurent`, `Ramified`, `Gauss` | local-field-style backends/functors, mostly capped-relative precision models |
| `Adele`, `LocalQp` | runtime-prime adelic precision model over `Q` |
| `RationalFunction` | exact global function field `F_q(t)` over `Poly = F_q[t]` |
| `Ordinal` | staged transfinite nimbers; a checked/panic-on-escape `Scalar` for Clifford metrics; nim-addition on represented CNF terms, nim-multiplication through Kummer carries `α_u` assembled from `ord_u(2)`, `Q(f(u))`, and the finite `m_u` rows below `ω^(ω^ω)` — the 126 OEIS A380496 b-file rows for odd primes `3..=709` are source-pinned and diffed in full, `m_719=m_727=1` are separately locally certified, and the first unsupported carry is `733`; the resulting `α_u` *ordinal* is independently value-checked only at a named subset (`docs/OPEN.md`) |

The ideal full-field semantics motivating the `Ordinal` classifier is now proved
rather than open (`writeups/transfinite_arf.tex`, 2026-08-07).  Every finite metric in the supported
`< ω^(ω^ω)` tower already lies in a common finite subfield and keeps the existing
degree-relative Arf bit.  After scalar extension to full algebraically closed
`On₂`, every regular ordinary `(q,b)` quadratic form (`metric.a` empty) is
hyperbolic, `W_q(On₂)=0`, and its quadratic Clifford/Brauer-Wall class is split;
singular forms retain exactly polar rank, radical dimension, and whether `Q` is
nonzero on the radical.  This is a
mathematical full-field result, not a claim that the partial backend can construct
every required Artin--Schreier root in-window.

The char-2 Clifford point is load-bearing. In characteristic 2, `q` and `b` are
independent:

```text
e_i^2             = q_i
e_i e_j + e_j e_i = b_ij
```

The polar form is alternating, so `b_ii = 0`, while `q_i` can be nonzero. If the
engine collapses `q` and `b`, the char-2 Clifford product becomes the wrong
commutative object. The char-2 form layer reports `ArfInvariants { arf: u128, rank,
radical_dim, radical_anisotropic }` plus the derived `o_type()` →
`OrthogonalType`; for degenerate forms, the Arf of the
nonsingular core is not the whole form. On nonsingular metrics over `Nimber`,
supported `Fpn<2,N>`, and the documented finite ordinal windows, the same Arf bit is
the Brauer-Wall class `BW(F_{2^m}) ≅ Z/2`; hyperbolic planes are `0`, the
anisotropic plane is `1`, and direct sum / graded tensor adds by XOR.
`clifford::spinor` has a separate char-2 route: no `1/2(1+w)`, blade idempotents
such as `e_i e_j` when they shrink a left ideal, and otherwise the full
regular/lazy left action. In characteristic 0, general-bilinear `a` metrics are
handled by transporting through the antisymmetric gauge to the matching ordinary
`(q,b)` metric; characteristic 2 keeps the explicit nonzero-`a` rejection.

The cross-pillar bridges live in the Rust core. `IntegralForm` exports rational and even-mod-2 Clifford metrics plus
even discriminant Gauss-sum/Milgram checks and odd-lattice `Q/Z` discriminant /
oddity-corrected Milgram reports; finite char-2 `Fpn<2,N>` classification runs
through the façade; finite Hermitian forms over `F_{p^{2k}}/F_{p^k}` use the middle
Frobenius and are classified by rank plus radical dimension; cyclic Galois/Frobenius
maps have Clifford linear-map constructors;
the **rational 2-torsion Brauer class** `Brauer2Class` (`witt/brauer_rational.rs`:
Hasse–Witt `s(q)` vs the Clifford invariant `c(q) = s(q) + δ(n mod 8, disc)`), the
graded rational Brauer-Wall wrapper `RationalBrauerWallClass`
(`witt/brauer_wall.rs`: Wall exact-sequence coordinates = dimension parity, signed
discriminant, and Bridge-F `c(q)`, with `ℚ→ℝ` recovering the Bott index), and its
**full `ℚ/ℤ` lift** `BrauerClass` (`witt/cyclic.rs`: `cyclic_algebra_invariant = v(a)/n`,
with full-strength reciprocity over `F_q(t)`); the **valuation as (lax) tropicalization**
with `NewtonPolygon` over the valued legs (`scalar/newton.rs`, slope = root valuation =
Springer residue layer); `Ordinal` serves as a Clifford scalar inside the verified Kummer
boundary;
`forms/integral/codes.rs` carries binary and odd-prime codes, MacWilliams, and
Constructions A/B/D (with scaled integer-coordinate Gram constructors and an `Option`
boundary when the scaled Gram is not integral), including Type I witnesses (`Z^2`,
`Z^2⊕E8`), the Type II length-16 code whose Construction-A lattice is `D16+`, the
`B(Golay)` half-Leech oracle, scaled nested-code Construction D, generated
Reed-Muller codes with `BW16` (`RM(0,4) <= RM(2,4)`, determinant 256, minimum 4,
kissing 4320), and the ternary Golay `[12,6,6]` odd unimodular rank-12 p-ary
Construction-A witness; `forms/integral/clifford_lattices.rs` gives the reverse
Clifford→integral certificate for `BW16` from the real spinor weight basis,
quadratic-phase `RM(2,4)` rows, and `4e_x` coordinate weights, recording
`|Aut(BW16)| = 2^21·3^5·5^2·7` as the index-2 real Clifford/BRW subgroup and the
full `C_4` order separately;
`forms/integral/{theta,modular}.rs` give exact theta coefficients and `E4`/`E6`/`E12`
identification (`theta_E8 = E4`, `theta_{E8+E8} = theta_{D16+} = E4^2`, the rootless
Leech `q^1` oracle), plus the norm-indexed level-4 theta head for odd lattices,
while `forms/integral/niemeier.rs` carries the 24-class
Niemeier root/glue/Aut catalogue and verifies the rank-24 mass plus weighted
Siegel-Weil identity against `E12` and the 691 coefficient;
`forms/integral/kneser.rs` carries explicit denominator-checked Kneser
`p`-neighbors plus mass-closed reports for the explicit rank-8/rank-16
even-unimodular genera (`E8`, `E8+E8`, `D16+`; rank 24 stays catalogue-backed);
`forms/integral/weyl_versors.rs` realizes ADE simple roots as Clifford Pin
versors, checking Cartan reflection actions, determinant `-1`, and Coxeter
orders through the Clifford outermorphism/twisted-adjoint surface;
and
`DiscriminantForm` exposes dependency-free `Complex64` Weil
`S`/`T` matrices, with the `S` prefactor the conjugate of the positive Milgram phase
and `verify_weil_relations` checking the honest metaplectic relations (not the
oversimplified `S^4 = I`), while the char-2 extraspecial surface carries the finite
Heisenberg/Pauli representation and projective symplectic-transvection intertwiners
over its `F₂` bitmask boundary. The fourth-wave joins are shipped too: Milnor's exact
sequence `W(ℤ)→W(ℚ)→⊕_p W(F_p)` (`witt/milnor.rs::global_residues`, odd `p`), the named
Scharlau transfer (`trace_form::transfer_diagonal`), Nikulin's genus criterion
(`DiscriminantForm::is_isomorphic`) plus the theorem-1.10.1 existence predicate
(`nikulin_existence_report` / `nikulin_even_lattice_exists`), exact Conway-Sloane
`p`-adic genus symbols (`Genus::canonical_symbol_at`, with the corrected 2-adic
train/compartment/oddity reduction), the games↔integral lexicode edge
(`games/lexicode.rs`: `LexicodeTurningGame` has P-set `L(n,d)`, greedy = mex, so the
`[24,12,8]` lexicode is Golay), and the
Brown `ℤ/8` invariant — the char-2 cell of the mod-8 spine (`char2/brown.rs`:
`brown_f2`/`double_f2`, with `β = 4·Arf`, plus `DiscriminantForm::brown_invariant`
giving the float-free `β ≡ sign(L) mod 8` on 2-elementary discriminant forms).
The independent game-output question `over` is resolved at the exact
synchronized-charge boundary: `q=lift(ell)+2Q`, with phase the correlated Walsh
pair of `Q` and `Q+ell`; ambient Brown colours of full `ShUg` vanish, while a
single partizan selector `{A_(Q+ell) | A_Q}` realizes residues `0,1,2,3` as
intrinsic outcomes `N,R,P,L` without an external product or terminal evaluator
(the Brown-selector section of `writeups/goldarf.tex`). The
fifth-wave Bridge K is shipped too: the full `ℚ/ℤ` ungraded Brauer invariant
(`witt/cyclic.rs`: `BrauerClass` + `cyclic_algebra_invariant` = `v(a)/n` for the
unramified local cyclic class over the `Qq` leg, plus `tame_symbol_exponent` /
`tame_symbol_invariant` for the tame Kummer slice) with full-strength reciprocity over
`F_q(t)` (`constant_extension_invariants`, `Σ_v deg(v)·v(a)/n = 0`, and
`tame_symbol_invariants_ff` / `tame_symbol_invariant_sum_ff` for `μ_n ⊂ F_q`); it
lifts the 2-torsion `Brauer2Class` (which embeds as its `½`-slice) to the full local
Brauer group. Wild norm-residue symbols remain deferred.

The checked game-Clifford deformation surface is implemented as an engineering
bridge, not as a game-native scalar claim. `GameClifford::with_quadratic_data` accepts
integer `q`/polar data on a chosen game-generator tuple only after verifying every
game relation in the quotient is null and polar-radical for that data; over the
torsion-free target `ℤ`, relations such as `2* = 0` force `Q(*)` and all pairings
with `*` to vanish. The stronger global question is now resolved: Moews's abstract
structure theorem makes the short-game group power-of-two divisible with
power-of-two torsion, so adjoining roots of `nt=0` forces `Q(t)=B(t,x)=0` over
every coefficient ring in any ambient-coherent faithful Clifford datum.  Thus
nonzero local torsion tables are necessarily root-incomplete and ambient-dependent;
the proof is the game-exterior appendix of `writeups/goldarf.tex` (with the
sharper `⋂ₖ4ᵏR` conclusion) and its algebraic core is
kernel-checked in `formal/Ogdoad/GameExterior.lean`.

The game-built Gold-form bridge and its normal-play rule are proved. The
standard chain is:

```text
x + y      = XOR = disjunctive sum of impartial game values
x * y      = nim product = Turning-Corners product value
x -> x^2   = Frobenius = diagonal product x*x
Tr(x)      = x + x^2 + ... + x^(2^(m-1))
Q_a(x)     = Tr(x * x^(2^a))
```

Implemented probes verify Gold ranks, Arf zero-count bias, literal Turning-Corners
reconstruction on small fields, frame-obstruction experiments, misère-kernel
obstruction examples, loopy Draw/Loss-set experiments, and bent Gold-component route
probes. The pass-free weighted-source Witt--FIFO rule now makes the Arf interpretation
unconditional: its impartial normal-play P-set is `{Q = 0}` for every finite
`F_2`-valued quadratic refinement. A deterministic public Witt frame makes the
strategic graph a matching, public adapted coins carry the triangular
`B`-correction, and one matched source pair per active original coordinate uses
its singleton `q_i` as a local overlap weight. Either seat forces zero correction parity on every such board by a
rank-inductive safe-front strategy. PASS is absent; CLOSE may cross ko only
after the untouched set empties, so the core has exact even tempo and one
seat-symmetric tail at charge one compiles the forced bit to normal play. Loading is q-blind,
transition access is `(w0,c)=(1,1)`, and its distinct observations are exactly
the active singleton directions. Any transcript-stable exact rule must observe
vectors spanning the input, so this support is optimal and a constant total
budget is impossible; block aggregation attains the integral
`ceil(wt(x)/w)` bound exactly at every fixed width. Outcome-preserving
unavoidable fork padding proves that
the basic reachable, optimal, and unavoidable fork properties do not certify
naturality. Lean checks these
independent ingredients in the `GoldDiagonal`, `FifoMatching`,
`ImpartialRealizer`, `GoldMatchingAlgebra`, `GoldNoEvaluator`,
`GoldBlockCompression`, and
`GoldForkPadding` formal modules.

The earlier σ-valued echo-fifo+dummy realizer remains **verified**
(2026-06-10, adversarial review:
`experiments/echo_solver.py`, 391,680/391,680 m=8 checks, zero misses — the
harness and `docs/PY.md` carry the record; the flagship paper no longer
narrates the superseded mechanism). Its arbitrary-graph mechanism is a strict
generalization, no longer a premise of Gold exactness. The
realizer's *mechanism* is reduced (2026-06-10 second pass,
`experiments/linking_game.py`; frontier note `writeups/linking_affine.tex`):
the σ-game is the
odd-close parity game on the support graph, and the linking theorem — an isolated
coin forces flips even, hence exactness for all m — is machine-verified on every
graph class through k = 8 real coins plus dummy (12,346 classes at k = 8, both
seats). The original prevention/debt menu is strictly complete only through k = 7;
two k = 8 witnesses require proactive debt, while the broader no-self-flip/debt
envelope is strictly complete across the full k = 8 census. The block-turn and
live-degree identities sharpen the proof route. The current proof note further
identifies the target with an odd affine response flow, interprets front deletion
as a two-graph/Seidel chart, proves contraction of the initial cut moment and a
two-bit handshake refinement, proves a two-switch endgame corridor, and proves
that cut and continuation moments must be cancelled jointly; the general-n
contraction remains open.

Appendix-grade shipped layers that should not be mistaken for new Gold/Arf claims:
tropical thermography (`Semiring` + dual `Tropical<MaxPlus/MinPlus>`) plus
game-valued heating/overheating/Norton operators and the proved positive-numeric-unit
regrading `gr_τ -> gr_{uτ+u-δ}`. The completed `under` theorem proves that the
game and place consumers are two tropical objects: `gr_0`'s nonzero `[*]`
2-torsion forbids a lift-compatible action by any full dyadic object
(ordinary or graded initial-form), and the exact nonnegative
Norton composition defect forbids a multiplicative dyadic action even after
any temperature-preserving residue refinement. The source-pinned (OEIS A380496) ordinal
nim Kummer tower below `ω^(ω^ω)`, the characteristic-2
Artin-Schreier local-global layer over `F_{2^m}(t)` including the Aravire-Jacob wild
summand, and the integral lattice/genus/mass/Leech/Niemeier/theta/code/Weil chain. These are
standard-math implementations and useful infrastructure; cite them as such.

## Commands

```sh
cargo test --workspace                        # the math core + grundy (pure Rust, no Python)
cargo clippy --workspace --all-targets        # lint (kept warning-clean)
cargo doc --no-deps --workspace               # rustdoc (intra-doc links warning-clean)
cargo run --example tour                      # Rust demo
cargo run --example tropical                  # tropical-semiring / thermography demo
cargo run -p grundy --example repl            # grundy expression-language REPL
cargo run --example interactive_kernel        # research probe
cargo run --example octal_hunt                # research probe
cargo run --example loopy_quadric             # research probe
cargo run --example misere_quotient           # research probe
cargo run --example bent_route                # research probe
(cd formal && lake build)                     # Lean off/FIFO proof-kernel check
python -m maturin build --profile dev -i python
python -m pip install --force-reinstall --no-deps target/wheels/ogdoad-*.whl
python demo.py
python experiments/framing_obstruction.py
python experiments/gold_family_survey.py
python experiments/misere_kernel.py
python3 experiments/echo_solver.py selftest   # echo adversarial-review harness (stdlib, no venv)
python3 experiments/linking_game.py all 5     # linking-reduction harness (stdlib, no venv; `all 7` ≈ 75 s)
python3 experiments/exception_column_m4.py    # 2·3^k excess column m=4 certification (stdlib, no venv; ≈ 2 min)
```

The debug-profile wheel avoids the malformed stripped Mach-O produced by the
current release build on this macOS beta. `cargo` must be on PATH
(`. "$HOME/.cargo/env"`).

## Hard rules

1. **The math core is generic over `Scalar` and pure Rust.** PyO3 lives behind the
   `python` feature; never `use pyo3` outside `src/py/`, never make it non-optional.
   This is what keeps `cargo test` from linking libpython. (Details: `src/py/AGENTS.md`.)
2. **The metric carries `q` and `b` independently — do not collapse them.** In char
   2, `b` is alternating yet `q[i]` can be nonzero; collapsing them makes every
   char-2 algebra commutative. The optional `a[(i,j)]` lifts the engine to a general
   bilinear form. Build with `Metric::new`/`::diagonal`/`::grassmann`/`::general`,
   never the bare struct literal. (Details: `src/clifford/AGENTS.md`.)
3. **Signs go through the scalar's own `neg()`, never a literal `-1` or a
   `characteristic()` branch.** For nimbers `neg` is identity, so char-2 sign-
   vanishing falls out for free; hardcoding signs breaks char 2.
4. **Surreal arithmetic recurses only on exponents** (strictly simpler than the
   number). That is the entire termination argument — never recurse on the number.
5. **Per-backend, no mixing.** Each Python backend monomorphises the engine to one
   concrete scalar type; mixing worlds raises `TypeError` by construction. Intended.
6. **Verify, don't claim.** The `associativity_*` tests catch product bugs and
   `general_product_reproduces_reduce_word_when_a_empty` pins the general engine to
   an independent oracle. Add a test before trusting a new operation.
7. **Fixed-width integer payloads are `u128`/`i128`.** Public arithmetic carriers,
   invariant bits/residues, counts, budgets, and signed integral data use those
   widths consistently. `usize` remains for indexing, dimensions, and platform ABI
   hooks such as Python hashing; otherwise do not introduce narrower fixed-width
   carriers without a hard external signature forcing it.

## Style

- Rust 2021, `cargo fmt` clean, `cargo clippy --workspace --all-targets` warning-clean (the one
  crate-level allow — `needless_range_loop` for the matrix code — is justified in
  `lib.rs`; targeted `#[allow]`s carry a one-line reason). License: AGPL-3.0-or-later.
- Numeric payload style is deliberate: non-index fixed-width integers are
  `u128`/`i128` throughout the core, docs, examples, and tests.
- Display is deliberate and canonical (grundy Display v4, `grundy/docs/spec.md` §12):
  blades render as wedge expressions `e0∧e1` (`∧` = U+2227); coefficients attach
  `coeff⋅label` (`⋅` = U+22C5) with coefficient-`1` elided and `-1` → `-label`
  (compared via `S::one().neg()`, never a literal). A term whose rendering starts
  with `-` joins with ` - ` (string-level, char-agnostic); the empty multivector
  renders as `S::zero()`'s display (`*0` in nim-worlds, `0` elsewhere). Nimbers
  print `*n`; ordinals are star-wrapped (`*5`, `*ω`, else `*(…)`: `*(ω + 1)`,
  `*(ω↑2)`, `*(ω⋅3)`, `*(ω↑(ω))`); surreals print CNF (`3⋅ω↑2 - ω + 5`, `ω↑(ω)`,
  `ω↑-1`, `ω↑(1/2)` — exponent bare iff a signed integer); `Fpn` `3⋅x↑2 + 2⋅x + 1`;
  `Poly` joined the monomial family at v4 (2026-07-10, reversing the old
  explicit-coefficient pin deliberately): descending exponents, unit
  coefficients elided on nonconstant terms, sign-aware join — `t↑2 - t + 1`,
  never `1 + -1⋅t + 1⋅t↑2`; `RationalFunction` `(num)/(den)` with v4 sides.
  Atomic = no spaces and no `⋅ ∧ ↑ / + -`
  outside balanced parens.
- Rust scalar operators: total-product backends have `+ - *` and unary `-`
  (concrete-only, via `impl_scalar_ops!`), plus `^ u128` for power (`x ^ 3` =
  square-and-multiply via `Scalar::mul`; `x ^ 0 == one()`). The `u128` RHS
  prevents element-element `^` from compiling — on `Nimber`, `x ^ x` would silently
  mean nim-addition (XOR), so no `BitXor<Self>` impl exists on any backend. **Rust
  `^` binds looser than `*`; parenthesize when mixing product and power.**
  `Multivector` has `&` (wedge, grundy `∧`) via `impl BitAnd`; **no `^` operator on
  `Multivector`** — the geometric product needs the metric, so use
  `CliffordAlgebra::pow(&self, v, k)` for repeated geometric multiplication.
  `Ordinal` deliberately omits owned `*` and `^` because transfinite
  nim-multiplication is partial at the verified Kummer boundary; use `nim_mul` and
  `nim_pow` for the checked paths. Generic engine code over `S: Scalar` still calls
  `.add(&x)`/`.mul(&x)` — operators are NOT a supertrait (see `src/scalar/AGENTS.md`).
- Python: `import ogdoad as pl` is the house alias (`pl` = *pleroma*, the crate's
  pre-rename name — kept deliberately).

## Testing

`cargo test --workspace` is the source of truth (ogdoad + the grundy crate) and
needs no Python. It does **NOT** compile the
`python` feature — after touching `src/py/` or any core API the bindings call, run
`cargo check --features python` (and `cargo clippy --features python --all-targets`).
After touching `clifford/` or `scalar/big/surreal/`, also rebuild + run `demo.py`
(display changes don't surface in `cargo test`).

After touching any doc comment (`//!` / `///`), run `cargo doc --no-deps` and keep it
warning-clean — intra-doc links to renamed/private items and `[i]`-style brackets in
prose are the common breakages. **Run it cold** (`rm -rf target/doc` first, or
`RUSTDOCFLAGS="-D warnings" cargo doc --no-deps`): an incremental `cargo doc` only
re-checks what it recompiles, so it silently under-reports stale-link warnings in
untouched modules.

Two property suites (dev-dep `proptest`, in `tests/`): `scalar_axioms.rs` fuzzes the
commutative-ring axioms across every backend, `clifford_axioms.rs` fuzzes geometric-
product associativity/distributivity over random metrics in char 0 and char 2. The
default depth is smoke-sized (`FAST_CASES = 2`, `HEAVY_CASES = 1` — the sentinel tests
carry the regression weight); before trusting changes to core arithmetic, run with
`OGDOAD_PROPTEST_CASES=N` for real fuzzing depth. The
capped-relative precision models (Qp/Qq/Laurent/Ramified/Gauss/Adele) are excluded
from the exact-ring fuzz by design; `ExactScalar`/`ExactFieldScalar`/`PrecisionScalar`
mark that boundary without becoming `Scalar` supertraits. (serde is intentionally NOT
shipped — the invariant-carrying types need custom deserialization, not a naive
derive.)

The resolved Gold/Arf tombstone and the genuine open problems live in `docs/OPEN.md`; the
draft notes are `writeups/goldarf.tex` (Gold/Arf) and `writeups/excess.tex`
(transfinite excess). Read `docs/OPEN.md` before touching `forms/char2/`,
`forms/quadric_fit.rs`, `forms/char0.rs`, `games/coin_turning.rs`, `games/kernel.rs`,
`games/misere.rs`, `games/loopy/`, `forms/witt/`, `experiments/`, or the
research example probes.
