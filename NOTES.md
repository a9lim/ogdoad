# Notes: Clifford algebras over games, and the Arf thread

Why this project has the shape it does, and where the genuinely open question is.

## The setup

Conway's combinatorial games, under disjunctive sum, form a partially ordered
abelian group — but **not a ring**: the game product is only a congruence on the
*numbers* (the surreals). A Clifford algebra needs a commutative scalar ring, so
"Clifford over games" forces you onto the field-like cores of game-world:

| core | structure | Clifford flavour |
|---|---|---|
| surreals `No` | real-closed field, char 0 | the ℝ-Clifford classification (8-fold periodicity), with infinite/infinitesimal metric entries |
| surcomplex `No[i]` | algebraically closed, char 0 | ℂ-Clifford, 2-fold periodicity |
| nimbers `On₂` | algebraically closed, char **2** | the genuinely different one |

Each is a backend here. The char-2 nimber case is the only one where Clifford
gets a new flavour rather than reproducing ℝ/ℂ with exotic scalars.

## The char-2 / Arf story (solid)

In characteristic 2 the quadratic form `Q` is **not** determined by a symmetric
bilinear form, so the engine carries the squares `q[i]=Q(eᵢ)` and the
alternating polar form `b[(i,j)]={eᵢ,eⱼ}` as independent data.

The classifying invariant of a nonsingular quadratic form over F₂ is the **Arf
invariant** (Arf 1941): for a symplectic basis `{aₖ,bₖ}`,
`Arf(Q) = Σₖ Q(aₖ)Q(bₖ) ∈ F₂`. Two forms are equivalent iff their Arf
invariants agree.

The payoff: Bertram, Kervaire et al. / the survey *"Real Clifford algebras and
quadratic forms over F₂: two old problems become one"* (arXiv:1601.07664) prove
that the classification of (real) Clifford algebras **is** the classification of
F₂ quadratic forms, with the Arf invariant complete. So computing the Arf
invariant of a nim-Clifford form (see `src/forms/char2.rs`, `pl.arf_invariant`) is not a
toy — it returns the isomorphism class of the char-2 Clifford algebra.

`A ⊕ A ≅ H ⊕ H` (two anisotropic planes ≅ two hyperbolic planes) is the
additivity of Arf made executable, and the tool confirms it.

The classifier works over any nim-subfield, not just F₂: a form with entries in
F_{2^{2^k}} is symplectically reduced over that field (pairs normalised with the
`nim_inv` from the versor layer), and the Arf sum is pushed down to F₂ by the
field trace `Tr_{F/F₂}(x) = x + x² + … + x^{2^{m-1}}`, realising the canonical
`k/℘(k) ≅ F₂`. Over F₄, e.g., `q=[*2,*2]` is anisotropic (O⁻) while `q=[*2,*3]`
is hyperbolic (O⁺).

## The games bridge (solid as far as it goes)

Games connect to the nim *field*, concretely:

> **Product Theorem for coin-turning games** (Berlekamp–Conway–Guy, *Winning
> Ways* vol. 3): the Grundy value of a product of coin-turning games (e.g.
> Turning Corners) is the **nim-product** of the factors' Grundy values.

So nim-addition (XOR) and nim-multiplication are literally the arithmetic of a
real class of impartial games. That is the bridge from games to `On₂`, the
scalar field underneath the nimber backend.

## The open question (where it stops)

The bridge above delivers **linear** structure (Grundy values are nim-sums of
single-coin values) and **bilinear** structure (coin-turning products are
nim-products). A quadratic form — the thing carrying an Arf invariant — is, in
char 2, *strictly more* than a bilinear form, and nothing in the standard theory
hands you one from a game:

- the nim-square map `x ↦ x⊗x` is the Frobenius, which is F₂-**linear**, so the
  "diagonal" of the coin-turning bilinear form carries no quadratic content;
- Welter's game has deep structure, but it lands in the representation theory of
  symmetric groups (Sato's conjecture, Irie 2018), not in Arf invariants.

So the genuinely open question this project points at:

> **Is there a natural quadratic refinement of the nim-bilinear form arising
> from a combinatorial game, whose Arf invariant is itself a game invariant?**

This is the char-2 game-theoretic analogue of a *quadratic refinement of a
symplectic form* — the same structure that produces the Arf–Kervaire invariant
from framings in topology. I have not found it in the literature, and I won't
claim it exists.

> **This framing is refined by the three sections below.** The probes show the
> answer is more than "open": the Arf-bearing forms *are* built from game
> operations, and the Arf invariant *is* a win-bias in the counting sense. What
> remains open narrows to one thing — a *natural game* whose P-positions are a
> form's zero set. Read on.

## Empirical probe: quadratic forms intrinsic to the nim-field

`experiments/trace_form_arf.py` runs the first probe — entirely on top of the
shipped library. The natural quadratic forms on a char-2 field are
`Q_a(x) = Tr(x·x^{2^a}) = Tr(x^{1+2^a})` (the Gold functions; `g = Frobenius^a`
is additive, so `Q_a` is genuinely quadratic). We build each over the bit-basis
of `F_{2^m}` and read off its Arf invariant.

Findings:

1. **Validation against known mathematics.** The classifier's polar-form rank
   reproduces the Gold-function rank formula `rank = m − 2·gcd(a,m)` exactly in
   all 15 cases tested (m up to 32) — independent confirmation that the nim
   arithmetic, trace, symplectic reduction, and Arf computation are all correct
   on nontrivial input, not just toy forms.
2. **The substrate carries real quadratic structure.** These forms are
   nondegenerate-of-positive-rank with nonzero Arf — the nim-field has genuine
   Arf-bearing structure beyond the linear (Grundy) and bilinear (coin-turning)
   game operations. Every positive-rank case in the family came out type O⁻.
3. **The bridge is still indirect.** This structure comes from the field's
   Frobenius/trace, not from a game's *move* structure. Connecting a specific
   game to a specific quadratic form remains the open step; the instrument to
   test candidates now exists and is validated.

## Chasing the bridge: the Gold form is game-built

`src/games/coin_turning.rs` implements nim-multiplication a second way — Conway's
Turning-Corners excludant recurrence,
`x ⊗ y = mex{(i⊗y) ⊕ (x⊗j) ⊕ (i⊗j) : i<x, j<y}` — which is the *game*
definition of the product. It agrees with the algebraic Fermat-power `nim_mul`
on every pair tested (x,y < 48). So "coin-turning = nim-multiplication" is now
realised and cross-validated in code, not just cited.

That promotes three operations to *game-realizable*:

- `⊗` nim-product = Turning-Corners Grundy value;
- `□` Frobenius `v ↦ v²` = `v ⊗ v`, the diagonal of Turning Corners;
- `⊕` XOR = disjunctive sum of single-coin positions;

and the trace `Tr(x) = x ⊕ x² ⊕ … ⊕ x^{2^{m-1}}` is iterated `□` and `⊕`. The
Gold form `Q_a(v) = Tr(v ⊗ v^{2^a})` is therefore a **composite of game
operations** on a position's nimber value (and under the 1-D game with
`g(n)=2ⁿ`, a position's value *is* a nimber). `experiments/gold_form_from_games.py`
rebuilds `Q_a` from literal Turning-Corners products and checks it equals the
algebraic form — so the Arf-bearing quadratic form really is *made of games*.

## So where does it actually stop now

The bridge closes at the level of **construction**: the Arf-bearing form is
game-built, and its Arf invariant is computed and validated. What is *not*
established is the **play-semantics**:

> `Q_a` is a derived quadratic quantity, not the Grundy value of a single
> position. Is its Arf invariant the answer to a *game* question — e.g. the
> outcome (or some misère/loopy invariant) of a game canonically attached to
> `Q_a`?

That is the sharp residue: the form is made of games; whether its Arf invariant
*means* something about play is open. The instrument to test a candidate game is
here and validated end to end.

### The Arf invariant *is* a win-bias (counting sense)

Dickson (1901): the Arf invariant of a quadratic form over F₂ is the value the
form takes most often. Quantitatively, for a nonsingular form on F₂^{2m'},
`#{v : Q(v)=0} = 2^{2m'-1} + (-1)^Arf · 2^{m'-1}`. So if a game had P-positions
(second-player wins) exactly `{v : Q(v)=0}`, the Arf invariant would be the
**sign of the win-bias**: which player wins from more starting positions, the
margin a fixed Gauss-sum `2^{m-rank/2-1}` (a square-root-scale fluctuation
around 50/50). `experiments/arf_win_bias.py` brute-forces the value
distribution of the game-built Gold forms and confirms the zero-count matches
the Arf-predicted bias exactly in every case.

So the Arf invariant *is* a win-bias — in the counting sense. The one missing
piece is a **natural game** whose P-positions are `{Q=0}`. Normal-play
disjunctive sums can't do it (their outcomes are XOR-linear, never quadratic),
so a candidate must be *interactive* (e.g. a coin-turning / lights-out style
game coupled through the polar form) or *misère* (where sums are genuinely
non-linear). Constructing or ruling out such a game is the open problem; the
win-bias check above is the target any candidate must hit.

### Sharpening the obstruction: it is exactly the polar form

`experiments/open_question_probe.py` pins down *why* normal play fails and what a
candidate must supply. The P-positions of a disjunctive sum of impartial games
are `{XOR of Grundy = 0}` — a **subspace**. The Gold zero set is a quadric, and in
char 2 the deviation is measured term-for-term by the polar form:

> `Q(u ⊕ v) = Q(u) ⊕ Q(v) ⊕ B(u,v)`, so for `u,v ∈ {Q=0}`:
> `u ⊕ v ∈ {Q=0} ⟺ B(u,v) = 0`.

The probe confirms this exactly: for the nondegenerate Gold forms (e.g. over F₂⁸)
`{Q=0}` is **not** a subspace, and its failure to be XOR-closed is governed
*precisely* by `B`. (Over F₂⁴ the low-rank/degenerate members collapse to a
subspace — there normal play is *not* excluded; the obstruction only bites once
the form is genuinely quadratic.)

This decomposes the problem into three layers, two already game-realizable:

- the **linear** part is Grundy/XOR — Sprague–Grundy;
- the **obstruction** to XOR-closure is exactly `B`, the coin-turning / nim-product
  bilinear form — the Product Theorem / Tartan games;
- the **only** genuinely missing ingredient is a *play rule* that couples
  positions through `B` and reads out the quadratic `Q` (not the bilinear `B`).

So the open question is now sharp and constructive: build (or rule out) an
interactive/misère game whose between-component coupling is the polar form `B`
and whose outcome is `Q`. The two game-realizable layers and the win-bias target
are all in place; what remains is the quadratic *play* rule. Concrete next steps:
misère coin-turning quotients (genuinely non-linear sums) and Tartan-product
couplings, both buildable on the shipped nim-product and the Arf/win-bias
instrument.

### Both next steps, built

*Tartan side — the bilinear layer is game-built.* `games/coin_turning.rs` now carries general
1-D coin-turning games (companion-set encoding, `grundy_1d`) and the 2-D Tartan
product (`tartan_grundy`), with the **Tartan/Product theorem verified**
(`tartan_grundy = nim-product of the component Grundy values`), recovering Turning
Corners as the tartan square of the game with `g(n)=n`. `experiments/tartan_bilinear.py`
then shows the Gold form's polar form `B(e_i,e_j) = Tr(e_i ⊗ e_j^{2^a} ⊕ …)` is
reproduced *exactly* by Turning-Corners products and the trace — so the obstruction
`B` identified above is, concretely, a composite of coin-turning games. Two of the
three layers (linear Grundy, bilinear `B`) are now realized in code from actual
games.

*Misère side — the non-linearity bar is cleared.* `games/misere.rs` is a memoised
misère-outcome evaluator for any finite impartial game, with misère Nim checked
against Bouton's theorem. The point it nails down: the misère P-set is **not**
`{⊕ = 0}` — `[1]` has nim-sum 1 yet is a P-position, `[1,1]` has nim-sum 0 yet is
an N-position — so it is neither a subspace nor a coset, and the outcome is not an
XOR-linear function of the position. That is exactly the property normal-play sums
*lack* and a quadratic `{Q=0}` P-set *requires*. So misère clears the bar that
ruled out normal play.

*Where it still stops.* Both prerequisites now hold in code — the coupling `B` is
game-built, and misère supplies genuine non-linearity — but neither yet exhibits a
game whose P-set is an actual Gold *quadric* `{Q=0}`. The misère Nim P-set is
non-linear but is not (a priori) a Gold quadric, and the Tartan layer realizes `B`
without yet a play rule that reads out `Q` rather than `B`. The remaining gap is
unchanged in kind — a *quadratic play rule* — but the surrounding scaffolding for
testing candidates (Tartan couplings + misère outcomes + the Arf/win-bias check)
is now all in place.

### Two probes, and a shared test bench

The instrument both probes feed into is `arf::fit_f2_quadratic`: given a set
`S ⊆ F₂^k`, it solves over F₂ for a quadratic form with `{Q=0}=S` (constant +
linear + quadratic terms by Gaussian elimination), returning `None` if `S` is no
quadric, and otherwise the form's Arf — and crucially whether it is *genuinely*
quadratic (nonzero polar-rank) or a mere affine flat. (Sanity: it finds exactly
`2^7` of the `2^8` subsets of F₂³ are quadrics.) So any candidate game's P-set can
be classified: not-a-quadric / linear / genuine quadric-with-Arf.

*Misère route (`games/misere.rs`, `examples/misere_quotient.rs`).* A bounded
indistinguishability-quotient computer (Plambeck–Siegel) over an abstract
impartial game; verified to give `⋆ ↦ ℤ/2`. Applied to small games it finds:
misère Nim heaps {1,2} has the order-6 quotient (matching the literature), {1,2,3}
likewise small — but these are *not* elementary-abelian 2-groups, so they do not
coordinatise as `F₂^k` and the quadric question doesn't even apply; and the one
that does, `⋆ ↦ ℤ/2`, has a rank-0 (linear) P-set. So no genuine quadric P-set
turns up among the tame games — consistent with tame ≈ linear. A *wild* quotient
of shape `(ℤ/2)^k`, `k ≥ 2`, with Arf-rank ≥ 2 is what would be needed.

*The octal hunt (`examples/octal_hunt.rs`).* `octal_misere_quotient` extends the
computer to octal games (heap-multiset positions, splitting moves and all). The
hunt sweeps 292 octal codes (length ≤ 3, `d₁` odd, heaps to 4 — 876 bounded
quotients) for that closing shape. Clean **negative**: the misère-quotient orders
that occur are `2, 6, 10, 12, 14` — *no power of 2 above 2 appears at all*, so no
`(ℤ/2)^{k≥2}` arises, and there are no quadric P-sets. The only
elementary-abelian-2 quotient in range is `ℤ/2` (a linear P-set); the wild ones
(orders 6/10/12/14) are not 2-groups. So the quadric P-set, if it exists, does not
come from an elementary-2-abelian octal misère quotient in this range — the open
question survives the hunt, now with the search scope on record.

*Interactive route (`games/kernel.rs`, `examples/interactive_kernel.rs`).* A
retrograde Win/Loss/Draw solver for any finite game graph (the P-positions are the
Loss positions). Two findings. (i) *Existence is trivial*: a hand-built acyclic
graph has P-set exactly `{Q=0}` (send every non-zero-of-`Q` to a fixed loss in the
set) — so the open question is never about existence, only about a *natural* rule.
(ii) Searching uniform downward (terminating) rules on `F₂^m`: the rule "move iff
you flip `Q`" reproduces `{Q=0}` exactly — but tautologically, since it references
`Q` itself in the move legality. The rules coupled only through `B` (the
game-legitimate, coin-turning ingredient) do *not*: B-coupled descent gives an
affine subspace, and a single-bit B-gated turn gives a *different* quadric (wrong
Arf). So the open problem reaches its sharpest form yet:

> a game whose moves are built from the combinatorial data (`B` / coin-turning)
> **alone — not from `Q` itself** — whose kernel is the Gold quadric `{Q=0}`.

Referencing `Q` is cheating; referencing only `B` does not (yet) integrate up to
`Q`. The kernel solver + `fit_f2_quadratic` are the bench any candidate runs on.

### The framing obstruction: why `B` can't, and what exactly is missing

`experiments/framing_obstruction.py` resolves the "`B` alone, not `Q`" dichotomy
into a **symmetry-breaking ladder**, turning the open question from "mysterious" to
"open in exactly one named corner." Two classical facts drive it: the quadratic
refinements of a fixed symplectic `B` form a **torsor under the linear duals `V*`**
(two forms share a polar form iff they differ by a linear functional — *Quadratic
forms and their duals*, arXiv:2506.23613), and `Sp(2m,2)` acts on those refinements
with **two orbits**, Arf the complete invariant, the stabiliser of a form its
orthogonal group `O(Q)` (the F₂ classification).

**The no-go (frame-blind games realise no quadric at all).** If a game's move
relation on `V = F₂^m` is built from a fixed nondegenerate symplectic `B` and the
F₂-linear structure *alone*, then every `g ∈ Sp(B)` is an automorphism of the move
graph, so retrograde Win/Loss outcomes are `Sp(B)`-invariant and the P-set is a
union of `Sp(B)`-orbits on `V`. But for nondegenerate `B`, `Sp(B)` is **transitive
on `V∖{0}`**, so the only invariant subsets are `∅, {0}, V∖{0}, V` — and a genuine
quadric (size `2^{m-1} ± 2^{m/2-1}`) is none of them. Verified over F₂⁴:
`|Sp(4,2)| = 720`, the orbit of `e₀` is all 15 nonzero vectors, and the
set-stabiliser of `{Q=0}` *is* `O(Q)` with `|O⁺| = 72` (orbit 10 = #Arf-0
refinements) / `|O⁻| = 120` (orbit 6 = #Arf-1 refinements). So a frame-blind game
**provably cannot** have a Gold quadric as its P-set — which subsumes and explains
*every* negative result above (B-coupled descent → subspace, single-bit → wrong
quadric): they were all hunting inside an `Sp(B)`-orbit, where no quadric lives.

**`B` + the coordinate frame gives the split quadric.** A concrete game escapes
`Sp(B)`-equivariance the moment it reads the standard basis. The all-downward rule
"move `v → w<v` iff `Q_frame(w) ≠ Q_frame(v)`", with the **frame quadric**
`Q_frame(v) = Σ_{i<j ∈ v} B(eᵢ,eⱼ)` (built from `B` + frame, zero diagonal, *no*
reference to a diagonal), has kernel **exactly `{Q_frame=0}`** — verified 119/119
over random nondegenerate `B` on F₂⁴, F₂⁶, F₂⁸. The proof is one line (any `Q=1`
point descends to `0 ∈ {Q=0}`; any `Q=0` point reaches only `Q=1` points). So a
*natural* `B`-game **does** realise a genuine quadric P-set — the existing probes
understated this. The catch: its Arf is pinned by `(B, frame)`.

**The gap to the Gold form is exactly the framing.** The Gold form decomposes as
`Q_gold = Q_frame ⊕ ℓ_diag`, where `ℓ_diag(v) = Σᵢ qᵢ vᵢ` is the linear functional of
the **diagonal** `qᵢ = Q_gold(eᵢ) = Tr(eᵢ^{1+2^a})` — the single-coin self-Gold
values (themselves coin-turning self-products, per `gold_form_from_games.py`). This
is a *framing* in the Arf–Kervaire sense: the datum a symplectic form needs to
become a quadratic one. And it is never free — for **every** genuinely-quadratic
Gold form (m up to 16) the frame quadric is split (`Arf 0`, O⁺) and the diagonal
flips it to the Gold O⁻ (`Arf 1`). The whole O⁻/Arf-1 content of the Gold form — the
reason `trace_form_arf.py` found every positive-rank Gold form is O⁻ — **is** the
framing; `B` and the frame contribute Arf 0.

So the ladder is `Sp(B)` (no quadric) → `O(Q_frame)` (the split frame quadric, via
the frame) → `O(Q_gold)` (the Gold quadric, via the diagonal framing). The open
question's residue is now sharp and small: **the `m`-bit diagonal framing**, not
derivable from `B`, is the only thing between a natural `B`-game and the Gold
quadric — the game-theoretic shadow of the topological framing behind Arf–Kervaire.
Whether *that* framing is itself game-natural (a marking, a misère/scoring twist, a
field-multiplicative coupling that carries the Frobenius non-locally) is the honest
open corner; the no-go closes every frame-blind and `Sp(B)`-symmetric route.

## The char-0 companion: a matrix-algebra classifier (`forms/char0.rs`)

The Arf invariant returns the isomorphism class of a *char-2* Clifford algebra.
Until now char 0 had the engine but no classifier — an asymmetry. `forms/char0.rs`
closes it: `Cl(p,q)` over a real-closed field follows the 8-fold Bott table
indexed by `s = (q − p) mod 8`, and over an algebraically closed field the 2-fold
table. Because the surreals are real-closed, this *is* the genuine ℝ-Clifford
classification — and the signature is read off the **signs** of the surreal
squares, which may be infinite (ω) or infinitesimal (ε); only the sign matters,
since a real-closed field has square roots of positives (`√ω = ω^{1/2}`).

Cross-checks worth keeping: it reproduces `Cl(1,3) ≅ M₂(ℍ)` but `Cl(3,1) ≅ M₄(ℝ)`
(the two spacetime conventions are genuinely different algebras), `Cl(4,1) ≅
M₄(ℂ)` (conformal GA), and — tying it to the even subalgebra — `Cl(3,0)⁰ ≅
Cl(0,2) ≅ ℍ`. So both characteristics now carry a real classifier: **Arf for
char 2, the matrix-algebra name for char 0.**

## Artin–Schreier ↔ Arf: one trace, two roles

The trace `Tr_{F_{2^m}/F₂}(x) = Σ x^{2^i}` that pushes the Arf invariant down to
F₂ (the canonical `k/℘(k) ≅ F₂`) is the *same* trace that obstructs the
Artin–Schreier equation `y² + y = c`: it is solvable iff `Tr(c) = 0`. So the two
halves of this repo — the Arf classifier and the field arithmetic of `On₂` — run
on one object. `scalar/nimber.rs` now exposes it directly: `nim_sqrt` (the inverse
Frobenius, `x^{2^{63}}` in F_{2^64}, always defined in char 2), `nim_trace`, and
`nim_solve_artin_schreier` (an exact F₂ linear solve, solvable exactly on the
trace-zero hyperplane — half the field).

This sharpens "the Arf invariant is a win-bias". Dickson's zero-count
`#{Q=0} = 2^{2m−1} + (−1)^Arf·2^{m−1}` is, term by term, counting how often the
form's value is Artin–Schreier-solvable; the win-bias sign *is* the trace
obstruction aggregated over the form. The field-level operation behind the bias
is now in the library, not just implied.

## Dickson: classifying `O(Q)`, not the form (`forms/char2.rs`)

In char 2 the determinant of any `g ∈ O(Q)` is forced to 1, so it cannot tell a
rotation from a reflection. The **Dickson invariant** `D(g) = rank(g − I) mod 2`
is the replacement, with `SO(Q) = ker D`: a single reflection has `D = 1`, a
product of k reflections `D = k mod 2`. `dickson_matrix` computes it over any
nim-field; `dickson_of_versor` reads it off a Clifford versor as its grade
parity. This is the companion to Arf on the *other* side of the same geometry:
**Arf classifies the form, Dickson classifies the form's isometries.**

## The Witt group makes additivity a group law (`forms/witt.rs`)

`A ⊕ A ≅ H ⊕ H` was checked pointwise via the Arf invariant. The Witt group
`W_q(F)` of nonsingular quadratic forms mod hyperbolics is the home of that fact:
over a finite nim-field it is `≅ ℤ/2`, classified completely by Arf, with `⊥` as
the group operation and the hyperbolic plane as identity. `WittClass` makes the
additivity a one-liner: `w(A) + w(A) = 0` *is* `A ⊕ A ≅ H ⊕ H`.

## General bilinear form: deforming the product (`clifford/engine.rs`)

The engine now computes `Cl(V, B)` for an *arbitrary* (not necessarily symmetric)
bilinear form `B`, via the Chevalley product `e_i e_j = e_i∧e_j + B(e_i,e_j)` in
the wedge basis. `B` is stored factored as `(q, b, a)`: diagonal `q`, symmetric
polar `b` (the anticommutator), and the new strictly-upper / in-order contraction
`a`. With `a` empty this is the ordinary Clifford algebra (and the general
Chevalley product is cross-validated, blade for blade, against the original
swap-reduction now kept as a `#[cfg(test)]` oracle).

Honest scope: the antisymmetric part of `B` is a *gauge* — `Cl(V, B)` is
isomorphic as an algebra to `Cl(V, sym B)`, so `a` does not create new algebras;
it deforms the *product* and the identification between the geometric and
exterior structures (the quantum-Clifford / normal-ordering setting of
Fauser–Oziewicz, interpolating toward the Weyl side). It is the right amount of
generality, faithfully implemented, not a claim of new isomorphism classes.

## The exterior algebra of the game group (`games/partizan.rs`)

A Clifford algebra needs a commutative scalar *ring*, which is exactly why this
project only reaches the three field-like cores. An **exterior algebra** needs
only a commutative ring of *coefficients* (ℤ) and a *module* of generators — and
the group of partizan games under disjunctive sum is a ℤ-module. So `Λ(game
group)` is well defined on **all** of game-world, the one Clifford-adjacent
structure that does not require the (nonexistent) game product.

`games/partizan.rs` ships a small short-game engine (sum, negation, the recursive
order, birthday, the number test) and the bridge `Λ¹ → (game group)`,
`e_i ↦ g_i`, built on the shipped Grassmann engine over the new ℤ scalar. The
point is the generators may be **non-numbers** (`⋆`, `↑`) — precisely where the
Conway product, and hence the entire Clifford story, is undefined — yet the wedge
structure (antisymmetry, grading) is perfectly well defined on them. The
2-torsion of `⋆` even surfaces as a relation: `value(2·e_⋆) = ⋆ + ⋆ = 0`. This is
the structural answer to "what lives on the whole game group, not just its
numbers."

# The expansion pass: more number systems, configurations, intricacies

A second arc widens the project along three axes — new scalar worlds, new
geometric-algebra structure on the engine, and deeper invariant theory — each
landed as an additive, `cargo test`-green module. The through-line is the same
char-0/char-2 mirror the rest of the repo runs on.

## New scalar worlds

### Odd characteristic: `Fp` and the invariant trichotomy (`scalar/fp.rs`, `forms/oddchar.rs`)

The classifier story had a hole. Char 0 is named by signature → a matrix algebra
(`forms/char0.rs`); char 2 by the Arf invariant (`forms/char2.rs`); **odd characteristic**
had neither backend nor classifier. `scalar/fp.rs` adds `Fp<const P>` — the prime field
`F_P`, carried in the *type* (a different prime is a different type, matching the
per-backend no-mixing discipline; the modulus can't live in the value because
`Scalar::zero()`/`one()` take no `self`). Unlike the nimbers, `neg` here is a
genuine negation (`P−a ≠ a`), so the Clifford antisymmetry signs are real.

`forms/oddchar.rs` then completes the trichotomy: over a finite field a nondegenerate form
is classified completely by **dimension + discriminant** (det mod squares) — the
odd-char analogue of Arf-completeness, verified here against an *independent*
brute-force congruence search. The **Hasse–Witt / Clifford invariant** is
computed honestly (a search for a representing vector) and comes out identically
`+1`: finite fields have trivial Brauer group, so it adds no classifying power —
we compute it to *exhibit* that, not to lean on it. `witt::WittClassG` is the
group-theoretic home: a `Char0/OddChar/Char2` enum whose odd-char part is the
order-4 Witt group `W(F_q)` — `ℤ/4` when `−1` is a nonsquare (`q≡3 mod 4`),
`ℤ/2×ℤ/2` when it is a square (`q≡1 mod 4`). The group law uses the **signed**
discriminant `(−1)^{m(m−1)/2}·det` (a genuine Witt invariant, unlike the bare
det); the `(−1)^{mn}` twist in its `⊥`-multiplication is exactly what produces
the `ℤ/4` — verified by walking the order of `⟨1⟩` in both fields. This is the
characteristic mirror of the existing Artin–Schreier↔Arf unification: **signature
/ discriminant+Hasse / Arf, one trichotomy across the three characteristics.**

### Omnific integers `Oz` (`scalar/omnific.rs`)

The surreal mirror of the `ℤ` backend: a *transfinite commutative ring*. A surreal
is an omnific integer iff its CNF has no infinitesimal terms and an integer
constant term (`ω`, `ω²+3`, `½ω` yes; `ε`, `ω+½`, `5/3` no). A Clifford algebra
needs only a commutative ring of scalars, so `Oz` supports the
Clifford-with-nilpotents / exterior structure — the headline being an **exterior
algebra with genuinely transfinite coefficients** (`ω·e₀ ∧ e₁ = ω·e₀e₁`), checked
against the `ℤ` backend on integer inputs. Only `±1` are units (it is a ring, not
a field: `1/ω = ε` leaves `Oz`).

### Transfinite (ordinal) nimbers (`scalar/onag.rs`)

The shipped `Nimber(u64)` backend is a *single* layer `F_{2^64}`; even `⋃ F_{2^{2^n}}`
is not algebraically closed (it lacks `F₈`, degree 3), despite the docs leaning on
On₂'s closure. `scalar/onag.rs` is the char-2 mirror of `scalar/surreal.rs`: ordinals in Cantor
normal form, with the same exponent-only recursion as the termination argument.
**nim-addition is complete and exact** — like-`ω`-power coefficients XOR, giving
the genuine transfinite characteristic-2 additive group (`ω⊕ω=0`, `ω⊕1=ω+1`,
`ω·2⊕ω=ω·3`). **nim-multiplication is now implemented across the whole field
`φ_{ω+1}`** — every ordinal strictly below `ω³` Cantor — via the DiMuro
construction (*arXiv:1108.0962*, extending Conway *ONAG* ch. 6 and Lenstra 1977
"On the algebraic closure of two"). The field tower has `φ_n = F_{2^{2^n}}`
(finite, the Fermat-power layers) and `φ_ω = ω = ⋃F_{2^{2^n}}`, which lacks
degree-3 roots; the lex-earliest irreducible is `x³ − 2`, so adjoining `ω` itself
as the root gives `φ_{ω+1}` with **`ω³ = 2`** — the missing `F₈` arrives via
`F_2(ω) ⊂ F_4(ω) ≅ F_{64}`. DiMuro Lemma 1.1 turns this into an algorithm: a
Cantor ordinal `[ω²·a + ω·b + c]` *equals* the field element `ω²⊗a ⊕ ω⊗b ⊕ c`,
so multiplication is polynomial mult in `(finite nimbers)[ω]` with the relations
`ω³ = 2`, `ω⁴ = 2⊗ω`. Verified end-to-end: `ω⊗ω = ω²`, `ω⊗ω⊗ω = 2`,
`(ω+1)³ = ω²+ω+3` (matches the char-2 binomial expansion by hand), and the full
**F₄(ω) ≅ F₆₄ field axioms checked exhaustively** (64³ associativity triples,
distributivity, every nonzero invertible). Above `ω³` it remains staged — the
next field would adjoin a degree-5 root and the general construction climbs the
Lenstra/DiMuro tower through `α_p` elements requiring nontrivial work in
successively larger finite fields.

## New geometric-algebra structure on the engine

### Outermorphisms and the determinant (`clifford/outermorphism.rs`)

A grade-1 linear map lifts to an algebra endomorphism by `f(a∧b)=f(a)∧f(b)`. The
**determinant** falls out as Grassmann defined it — the scalar by which the lift
scales the pseudoscalar, `f(I)=det(f)·I` — a computation structurally independent
of cofactor expansion, so it doubles as an engine check. Multiplicativity
`det(f∘g)=det(f)det(g)` is verified over Rational *and* Nimber: the char-2
determinant (= permanent) comes out right with no sign hardcoded, because the lift
inherits its signs from `wedge`.

### The exterior Hopf algebra (`clifford/hopf.rs`)

Coproduct (the unshuffle split on blades, `Δ(e_S)=Σ_{T⊆S} sign·(e_T⊗e_{S∖T})`,
the sign read straight off `wedge` so char 2 collapses it to `+`), counit, and
antipode, with the Hopf axioms — counit law, coassociativity, and the antipode
axiom `m∘(S⊗id)∘Δ=η∘ε` — checked over both characteristics. A worked subtlety: for
this primitively-generated coproduct the antipode is the **grade involution**
`(−1)^k`, *not* the reversion-twisted `(−1)^{k(k+1)/2}` — `S(v∧w)=+v∧w` by the
axiom, which the tests pin down.

### Conformal and projective GA, over the surreals (`clifford/cga.rs`)

The conformal model `Cl(n+1,1)` in a null basis (`up(p)=n_o+p+½|p|²n_∞`,
`up(p)·up(q)=−½|p−q|²`), generic over the scalar — so it runs over the **surreals**,
where a point sits at `ω`-scale and is *still* exactly null, and a sphere of
radius `ε` exactly contains a point at infinitesimal distance and excludes one at
`2ε`. Both are impossible with floating point. (A worked bug: the inner product
must be symmetrized `½⟨xy+yx⟩` — the engine carries the polar form in the
anticommutator, so `⟨xy⟩₀` alone is the asymmetric contraction.) CGA needs `½`, so
it is a char-0 feature. PGA `Cl(n,0,1)` adds the **exact nilpotent-motor
exponential**: `exp(B)=1+B+…` terminates when `B²=0`, giving exact translations
(`exp(e₀∧e₁)` translates `e₁↦e₁+2e₀`) with no transcendentals — the rotational
motor (`B²<0`, needing `cos`/`sin`) is honestly out of scope and returns `None`.

### Concrete spinor modules (`clifford/spinor.rs`)

Where `forms/char0.rs` *names* `Cl(p,q)≅M_d(K)`, this *builds* it: a primitive
idempotent `f=∏½(1+w)` from commuting `+1`-square blades, the minimal left ideal
`Cl·f`, and the matrices of left multiplication by each generator on it. Those
matrices satisfy the Clifford relations `Mᵢ²=qᵢ·I`, `MᵢMⱼ+MⱼMᵢ=0` automatically,
and the ideal dimension matches the classifier's `matrix_dim·dim_ℝ(K)` — verified
on `Cl(2,0)`, `Cl(3,0)` (Pauli), `Cl(0,2)` (quaternion), `Cl(1,1)`, `Cl(4,0)`. The
abstract classification, realized as explicit operators on column spinors.

## Deeper invariant theory

### Non-Archimedean Springer decomposition (`forms/springer.rs`)

The surreal Hahn field `ℝ((ω^No))` is real-closed but non-Archimedean, with the
ω-adic valuation. `springer_decompose` splits a diagonal form into
**valuation-graded residue forms** over ℝ — the form's entries bucketed by leading
exponent, each piece a residue ℝ-signature. The honest headline: because the value
group `No` is **2-divisible** (`Γ/2Γ=0`), Springer gives `W(No)≅W(ℝ)=ℤ` — *no
bigger Witt group*. The novelty is the valuation **filtration** itself, which no
Archimedean Clifford library exposes (over ℝ every nonzero entry has valuation 0);
the built-in check is that the residue signatures sum to the ordinary
`classify_surreal` signature.

# The expansion pass II: completing the trichotomy mirror, again

A third arc, same discipline as the first two: every item **completes an asymmetry
the repo already had**, lands additively, and is pinned by a `cargo test` oracle.
Eight items in four waves. `On_p` (odd-characteristic ordinal nimbers) is *deferred*
to its own future arc — in odd characteristic nim-addition is **not** XOR, so
`onag.rs`'s `canonicalize` would have to be replaced, and the field tower and the
lex-least irreducibles differ; the DiMuro construction (*On On_p*, arXiv:1108.0962)
must be pinned before any code is correct.

## New scalar worlds

### Finite extension fields `Fpn` (`scalar/fpn.rs`)

The odd-characteristic leg had only the *prime* fields `Fp<P>`; char 2 had the whole
nimber tower. `Fpn<const P, const N>` = `F_{p^N}` closes that gap, **and** supplies
the char-2 *odd-degree* fields the nimbers cannot reach (the finite nimbers realise
only `F_{2^{2^k}}`, degrees that are powers of two — so `F_8`, `F_32`, … are *not*
nimber subfields; `Fpn<2,3>` is the only `F_8` here). Representation: the `N`
coefficients over `F_p` of an element of `F_p[x]/(m)`, `m` a verified-irreducible
reduction polynomial selected by a `(P,N)` lookup (Conway-substitutable later for
canonical embeddings). `mul` is schoolbook-then-reduce — `onag.rs`'s "reduce mod
ω³=2" at degree `N`, odd `p`; `inv` is Fermat `x^{p^N−2}`; `characteristic()` is the
prime `p`, not the order. Exhaustively brute-force-tested over F_4/F_8/F_9/F_25/F_27
(the field axioms catch any reducible reduction polynomial).

### The p-adic integers `Zp` = `Z/p^k` (`scalar/zp.rs`)

The **ring of integers** of `Q_p` to precision `k` — not `Q_p` itself (`p` is a
**non-unit**, so a local *ring*, not a field; named `Zp`, not `Qp`, for that reason).
The Omnific/`Integer` posture: `characteristic()` = 0 (a truncation of the char-0
ring `Z_p`), and `inv` inverts units only (iff `p ∤ a`), returning `None` otherwise —
never leaving the ring with a spurious `1/p`. A Clifford algebra over `Z/p^k` is a
genuine non-semisimple object (`p` a zero divisor) — the engine's nilpotent path
exercised at the *scalar* level.

### Witt vectors `WittVec` = `W_N(F_q)` (`scalar/wittvec.rs`)

The canonical char-`p` → char-`0` lift (the Witt *vectors*, unrelated to the Witt
*group* of forms). Realised via the exact, manifestly-correct identification
`W_N(F_q) ≅ (Z/p^N)[t]/(f̃)`, the truncated **unramified** extension, with `f̃` the
naive lift of `Fpn`'s irreducible (Hensel keeps it irreducible; the extension is
unramified as `f̃ mod p` is separable). This **sidesteps the ghost-inversion (Witt
addition) polynomials** whose division-by-`p` is the classic correctness trap:
arithmetic is just `Fpn`'s, coefficient field `F_p` swapped for the coefficient
*ring* `Z/p^N`; `inv` is a Newton/Hensel lift from the residue inverse. The genuine
**Witt/Teichmüller coordinates** (`witt_components`, `from_witt_components`,
`teichmuller`) are built on top; the proof it really is the Witt ring is that ring
addition reproduces the classical carry `S₀ = x₀+y₀`, `S₁ = x₁+y₁−x₀y₀` in those
coordinates (oracle), plus `W_N(F_p) ≅ Z/p^N` checked against `Zp`. (The ghost map
itself degenerates over `F_q`: in char `p` every `pⁱ` term vanishes, `w_n = x₀^{pⁿ}`,
so its additivity is just the Frobenius — the carry polynomials, not the ghost map,
carry the information.) The on-brand hook: `W(F₂)` ↔ `Z/2^N` and Artin–Schreier–Witt
generalise the `y²+y=c` solver in `nimber.rs` to `Z/p^n`-extensions.

## New invariant theory

### The Witt ring, `Iⁿ`, Pfister forms, and the `eₙ` staircase (`forms/witt_ring.rs`)

`witt.rs` carried only the additive group; tensor product of forms makes `W` a
**ring**, and its fundamental-ideal filtration `W ⊇ I ⊇ I² ⊇ …` is the home of the
cohomological invariants. The retro-unification: `e₀ = dim mod 2`, `e₁ =` signed
**discriminant** (reusing `oddchar`'s `sclass`), `e₂ =` **Hasse** (reusing
`hasse_invariant`) — discriminant and Hasse stop being separate functions and become
successive steps `e₁, e₂` of one staircase, generated by the **n-fold Pfister forms**
`⟨⟨a₁,…,aₙ⟩⟩ = ⊗⟨1,−aᵢ⟩`. Stabilization is the field's `u`-invariant story, all
tested: over finite `F_q`, `I² = 0` (every 2-fold Pfister is hyperbolic — checked
over `F_5`, `F_3`, *and* the extension `F_9` via `Fpn`); over `Q_p`, `I³ = 0` with
`e₂` = Hasse genuinely nontrivial (the payoff below); over `ℝ` the tower is infinite,
`eₙ` reading the 2-adic expansion of the signature. `WittClassG::mul` makes `W` a ring
at the class level too — `Char0` signatures multiply; `OddChar` is `ℤ/4` (via
`z = e0 + 2·sclass`) or `F₂[ℤ/2]`, both pinned against the concrete `tensor_form`.

**Char-2 caveat, pinned not asserted:** in characteristic 2 the staircase does *not*
index-match. `W_q(F)` is a **module over** the bilinear Witt ring, not a ring (so
`WittClassG::mul` panics on `Char2`); its filtration is Kato's (differential forms),
not the Milnor `Iⁿ`; `dim` is always even so `e₀ ≡ 0`; the **Arf invariant is the
leading invariant**, and its cohomological degree is left as a convention we do not
force. We expose Arf as *the* char-2 invariant and do **not** claim "Arf = e₂".

### p-adic Hilbert symbol and Hasse–Minkowski (`forms/padic.rs`)

Where the Hasse invariant finally **does classifying work**. `oddchar`'s Hilbert
symbol is identically `+1` (finite fields have trivial Brauer group); the `p`-adic
one is genuinely nontrivial (`(−1,−1)_2 = −1` — Hamilton's quaternions ramify at 2
and ∞). Standard explicit formulas (Serre III.1): odd `p` via valuations + Legendre,
`p = 2` via the mod-8 table (the fiddly case). `is_isotropic_q` makes **Hasse–
Minkowski** executable — a `Q`-form is isotropic iff isotropic over `ℝ` and every
`Q_p`, by rank (Serre IV): rank 1 never, rank 2 iff `−ab` a global square, rank ≥ 3
real-indefinite + the local condition at each prime dividing `2·∏aᵢ`. Square-free
reduction keeps the `i128` arithmetic exact. Gold oracle: **Hilbert reciprocity**
`∏_v (a,b)_v = +1`; classic checks: `⟨1,1,1⟩` anisotropic, `⟨1,1,−1⟩` isotropic,
`x²+y²=3z²` (= `⟨1,1,−3⟩`) anisotropic.

### The Brauer–Wall group `BW(F)` (`forms/brauer_wall.rs`)

The abstract home all three classifiers are shadows of: graded-central-simple
algebras under the **graded tensor product** `⊗̂` (which already exists as
`graded_tensor`/`direct_sum`). `Q ↦ [Cl(Q)]` sends `⊥` to `⊗̂` and hyperbolics to 0,
so it factors through the Witt group. The unifier: **`BW(ℝ) ≅ ℤ/8` *is* `char0`'s
Bott clock `s = (q−p) mod 8`** — the periodicity table, now a group. `BW(ℂ) ≅ ℤ/2`
(dimension parity). `BW(F_q)` (Brauer group trivial) is the order-4 graded part
`≅ W(F_q)` — but we **do not assert** its structure: the tests *discover* the order
and the `q mod 4` dichotomy (`ℤ/4` over `F_3`, `(ℤ/2)²` over `F_5`) by walking the
subgroup generated by `[Cl⟨a⟩]` under the *actual* `graded_tensor`. The homomorphism
`[Cl(V)⊗̂Cl(W)] = [Cl(V)]+[Cl(W)]` is checked against `direct_sum` in every leg.

## New geometric-algebra structure

### The spinor norm `N: O(Q) → F*/F*²` (`clifford/spinor_norm.rs`)

The char-0/odd companion to char-2 Dickson (`char2.rs`), the same exact sequence
`1 → Spin → Pin → O → 1` from the other side. A versor `v = v₁⋯v_k` has spinor norm
`∏ q(vᵢ) = ⟨v ṽ⟩₀` (exactly `versor::norm2`); `classify_versor` returns `(spinor
norm, Dickson parity)`. The Dickson grade parity is now the generic
`versor_grade_parity`, off which `char2::dickson_of_versor` is the `Nimber`
specialisation. **Char-2 caveat:** there the codomain is the *additive* `F/℘(F)`
(Artin–Schreier group, the trace's target), not `F*/F*²` — Frobenius makes every
element a square, so the multiplicative norm collapses; we expose the raw `⟨v ṽ⟩₀`
and leave the mod-squares / mod-℘ reduction to the field.

## New game structure

### Scoring (Milnor) games (`games/kernel.rs`)

Normal play (`outcomes`) already handled loopy Win/Loss/**Draw**; the genuinely new
knob is *scoring*. `scoring_values` computes the Milnor minimax **interval**
`(left, right)` of every position on a finite acyclic graph — `left = max_w R(w)`,
`right = min_w L(w)`, Left maximising / Right minimising — with scored terminals
(`None` on a cycle: loopy scoring is out of scope). The point for the open question:
where `outcomes` returns a single Win/Loss **bit**, the scoring value is an
**integer**, rich enough to carry a quadratic form's *value* `Q(v)` at a position
rather than only its zero set — the extra structure a quadratic play rule needs.

## Math pinned this pass (recorded, not asserted)

- the **char-2 `eₙ` indexing** — Arf is the leading invariant of `W_q`, but `W_q` is
  a module not a ring and the Kato filtration differs; no "Arf = e₂" claim;
- the **`p = 2` Hilbert symbol** — verified against the standard mod-8 table and
  Hilbert reciprocity, not hand-asserted;
- the **Witt-vector representation** — the unramified ring `(Z/p^N)[t]/(f̃)`, dodging
  the ghost-inversion polynomials, with the carry formula as the after-the-fact check;
- **`BW(F_q)`** — order and group structure *discovered* by a subgroup walk, never
  hardcoded.

## References

- C. Arf, *Untersuchungen über quadratische Formen in Körpern der
  Charakteristik 2* (1941).
- J. H. Conway, *On Numbers and Games*, ch. 6 (the field On₂ of ordinal nimbers;
  ω³ = 2; algebraic closure below ω^{ω^ω}).
- H. W. Lenstra, *On the algebraic closure of two* (1977) and *Nim
  multiplication* (Séminaire de Théorie des Nombres, 1978).
- J. DiMuro, *On On_p* (arXiv:1108.0962, 2015) — the explicit field-tower
  construction `φ_Δ` and Lemma 1.1 (the ordinal `[Σ φⁱ αᵢ]` equals the field
  element `Σ φⁱ ⊗ αᵢ`) that makes ordinal nim-multiplication concrete in
  `scalar/onag.rs` across the whole of `φ_{ω+1}`.
- T. Y. Lam, *Introduction to Quadratic Forms over Fields* (the Witt group of a
  finite field; signed discriminant and Hasse invariant).
- T. A. Springer, *Quadratic forms over fields with a discrete valuation* (1955).
- D. Hestenes & G. Sobczyk, *Clifford Algebra to Geometric Calculus* (the
  outermorphism and the determinant as the pseudoscalar action).
- H. Li, *Invariant Algebras and Geometric Reasoning* / D. Hestenes, *Conformal
  geometric algebra* (the null-cone model `up(p)=n_o+p+½|p|²n_∞`).
- B. Fauser & Z. Oziewicz, *Clifford Hopf gebra* (the exterior/Clifford Hopf
  structure: coproduct, counit, antipode).
- P. Lounesto, *Clifford Algebras and Spinors*, ch. on minimal left ideals (the
  primitive-idempotent construction of spinor modules).
- Berlekamp, Conway, Guy, *Winning Ways for Your Mathematical Plays*, vol. 3
  (coin-turning games; Turning Turtles / Turning Corners; the Product Theorem).
- Conway, *On Numbers and Games* (the surreal/nimber fields; `On₂`).
- "Real Clifford algebras and quadratic forms over F₂: two old problems become
  one", arXiv:1601.07664.
- Y. Irie, *p-Saturations of Welter's Game and the Irreducible Representations
  of Symmetric Groups* (2018).
- P. Lounesto, *Clifford Algebras and Spinors* (2nd ed.), Table 16.4 — the
  `Cl(p,q)` classification by `(q−p) mod 8` used in `forms/char0.rs`.
- C. Chevalley, *The Algebraic Theory of Spinors* (1954); B. Fauser & Z.
  Oziewicz, *Clifford Hopf gebra for two-dimensional space* / "Clifford algebra
  of an arbitrary bilinear form" — associativity of the deformed product.
- L. E. Dickson, *Linear Groups* (1901) — the Dickson invariant; the value a
  binary quadratic form takes most often (the Arf win-bias).
- E. Artin, *Geometric Algebra* (1957) — `SO(Q) = ker D` in characteristic 2.
- J.-P. Serre, *A Course in Arithmetic* (1973), Ch. III–IV — the `Q_p` Hilbert
  symbol formulas, Hilbert reciprocity, and Hasse–Minkowski (`forms/padic.rs`).
- C. T. C. Wall, *Graded Brauer groups* (Crelle, 1964) — the Brauer–Wall group
  `BW(F)`, `BW(ℝ) ≅ ℤ/8` (`forms/brauer_wall.rs`).
- J. Milnor, *Algebraic K-theory and quadratic forms* (1970); V. Voevodsky, the
  Milnor conjecture — `Iⁿ/Iⁿ⁺¹ ≅ Hⁿ(F,ℤ/2)`, the `eₙ` staircase (`forms/witt_ring.rs`).
- T. Y. Lam, *Introduction to Quadratic Forms over Fields* — the Witt *ring*,
  fundamental ideal, and Pfister forms.
- J. Milnor, *Sums of positional games* (1953); A. Ettinger, scoring-game theory —
  the minimax value interval (`games/kernel.rs` `scoring_values`).
- E. Witt, *Zyklische Körper und Algebren …* (1937) — the ring of Witt vectors;
  J.-P. Serre, *Local Fields*, II.6 (Witt vectors and the unramified extension,
  `scalar/wittvec.rs`).
