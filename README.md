# ogdoad

[![CI](https://github.com/a9lim/ogdoad/actions/workflows/ci.yml/badge.svg)](https://github.com/a9lim/ogdoad/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/ogdoad)](https://crates.io/crates/ogdoad)
[![PyPI](https://img.shields.io/pypi/v/ogdoad)](https://pypi.org/project/ogdoad/)
[![docs.rs](https://img.shields.io/docsrs/ogdoad)](https://docs.rs/ogdoad)
[![License: AGPL v3](https://img.shields.io/badge/License-AGPL_v3-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)

The **Ogdoad** were eight Egyptian gods of the primordial waters, arranged in four
pairs — the world before there was a world. This `ogdoad` keeps a smaller pantheon:
eight number-systems, also in four pairs, also a little primordial. Surreals and
omnific integers; p-adics and Witt vectors; rational functions and polynomials; and
the plain old rationals and integers. Each pair is a **field beside its ring of
integers**. Off to one side sit the finite fields and the nimbers, who are their own
rings of integers and answer to no one. Eight, plus the loners.

The conceit is that these exotic worlds are not a curiosity cabinet. They are **cells
of one table**, and the number eight is not an accident: read the table one way and
you get Clifford algebras, read it the other way and you get the classification of
quadratic forms, and the *same* structures keep surfacing cell after cell with the
characteristic and the place politely swapped. The eightfold periodicity of the real
Clifford table, `BW(ℝ) ≅ ℤ/8`, Bott, `E₈` — it is all one spine, and the code is laid
out to make the rhyming visible.

One honest caveat up front, because it shaped everything. Conway's games, under
disjunctive sum, form an abelian **group but not a ring**: you can add games freely,
but multiplication only makes sense on the numbers and nimbers hiding *inside* them. A
Clifford algebra demands a commutative *ring* of scalars. So this is emphatically
**not** "Clifford algebras over all games." It is a generic Clifford engine over the
commutative worlds that live next door to game theory, plus a forms layer to classify
whatever it builds.

## Two readings of one table

Every backend is a cell in a table with two axes:

- **place** — *where* a number lives (Archimedean, p-adic, finite, transfinite), and
  whether it is a field or a ring of integers. This is how `src/scalar/` is grouped.
- **characteristic** — *which* classification theory applies (char 0 / odd / 2). This
  is how `src/forms/` is grouped.

The axes are independent. The place axis is what pairs each **field** with its **ring
of integers** — the four pairs of the Ogdoad:

| | field | ring of integers |
| --- | --- | --- |
| Archimedean (char 0) | `Rational` ℚ | `Integer` ℤ |
| transfinite | `Surreal` (No) | `Omnific` (Oz) |
| p-adic (char 0) | `Qp`, `Qq` | `Zp`, `WittVec` |
| function field (char p) | `RationalFunction` F_q(t) | `Poly` F_q[t] |
| finite | `Fp`, `Fpn`, `Nimber` | — (already their own) |

The pairing is structural, not decorative. The `HasFractionField` / `HasRingOfIntegers`
trait pair makes ℤ⊂ℚ, Oz⊂No, Zp⊂Qp, W_N⊂Qq, and F_q[t]⊂F_q(t) explicit *in the type
system* (with ℤ[i]⊂ℚ[i] following for free via the surcomplex transport). The rest of
the local-field furniture is type-level too — the valuation and uniformizer (`Valued`),
and the residue field `k = 𝒪/𝔪` with its angular component and Teichmüller section
(`ResidueField`) — so the whole package `(K, 𝒪, 𝔪, k, Γ, ϖ)` lives in the types rather
than the comments.

## The symmetries

The project is built around a handful of these rhymes. Each is the same theorem seen
twice, once on each side of a mirror.

**char 0 ↔ char 2.** Classifying a quadratic form is one theorem wearing three hats,
sorted by `char F`. Over a real-closed field it is the famous 8-fold periodic Cl(p,q)
table, `M_n(ℝ/ℂ/ℍ)` marching around the Bott clock. Drop to characteristic 2 and the
quadratic form and its polar form file for divorce; the **Arf invariant** and the
**Brauer–Wall group** take over custody. On the finite char-2 legs (`Nimber`, generated
`Fpn<2,N>`, the documented finite ordinal windows) a nonsingular form carries both the
Arf bit and the `BW(F_{2^m}) ≅ ℤ/2` class, under the same XOR law. `metric.classify()` /
`.bw_class()` pick the right leg from the scalar type at compile time. Over ℚ, the graded
Brauer–Wall story is separate and exact-sequence-shaped: `bw_class_rational` records
dimension parity, signed discriminant, and the ungraded Clifford class `c(q)`, with
scalar extension to ℝ recovering the same Bott clock.

**No ↔ On₂.** The surreals (a char-0 field) and the ordinal nimbers (a char-2
non-field) are the same Cantor-normal-form tower seen in two mirrors — both are
finite-support towers over recursive exponents, sharing one canonicalizer. They differ
in *exactly three places*: how exponents order, whether coefficients add or XOR, and
what counts as zero. That is why the shared machinery is a **function, not a type** —
forcing No and On₂ into one type would assert a field equals a non-field. The mirror
reads out again at the games layer: `NumberGame` (a surreal-valued game) and
`NimberGame` (a transfinite Nim heap `⋆α`) are the two views, one per characteristic.

**four ways to grow a field.** A 2×2 of (algebraic | transcendental) ×
(residue-extending | value-extending), and all four corners are filled:

| | residue-extending | value-extending |
| --- | --- | --- |
| **algebraic** | `Surcomplex` (adjoin `i`) | `Ramified` (adjoin `π = ϖ^{1/e}`) |
| **transcendental** | `Gauss` (adjoin a unit `t`) | `Laurent` (adjoin a uniformizer `t`) |

`Laurent` over a finite field is the equal-characteristic twin of `Qp`; `Ramified` is
the ramified twin of the unramified `Qq`. The separable extensions among these share one
relative trace/norm (`FieldExtension`) feeding Hilbert symbols, the Brauer–Wall group,
and Hermitian forms; the cyclic-Galois refinement (`CyclicGaloisExtension`) feeds the
**twisted trace form** `Tr(x·σ^k(x))`, which lands back in the classifiers — and over
the nim-fields becomes the Arf-classified **Gold form** `Tr(x^{1+2^a})`. The same Galois
data builds Frobenius linear maps in `clifford::frobenius`, so scalar trace maps and
Clifford outermorphism spectra share one computation.

**local ↔ global.** Springer's decomposition appears over every complete valued field,
and the value group decides how much survives: over the surreals it is 2-divisible, so
`W(No) = W(ℝ) = ℤ`, but over `Q_p`, `Q_q`, and `F_q((t))` it is ℤ, so two residue layers
live (`W(Q_p) = W(F_p)²`). The discretely-valued legs share **one** generic engine keyed
on `ResidueField`; the surreal leg keeps its own, *precisely because* its value group is
divisible — that mismatch **is** the symmetry, not a gap. Glue the local data and you get
Hasse–Minkowski over ℚ and Hilbert reciprocity `∏_v (a,b)_v = +1`; the per-prime residues
also assemble into Milnor's exact sequence `0 → W(ℤ) → W(ℚ) → ⊕_p W(F_p) → 0`. The whole
package re-runs in **equal characteristic** over `F_q(t)` — tame Hilbert symbols at every
place, reciprocity, Hasse–Minkowski, the split Milnor map — and there it is **exact**, no
precision model, the char-`p` mirror of the ℚ stack. Both global fields answer **one**
interface: the `GlobalField` trait, with ℚ and `F_q(t)` as its two implementors.

**the games bridge.** Red/blue/green Hackenbush is the showpiece: the same picture reads
out as a surreal (blue − red), a nimber (all-green is Nim), or a general partizan game —
and nim-multiplication itself is realized by Conway's Turning-Corners coin game. The game
pillar even reaches the lattice world: a greedy binary **lexicode** is built by the
**mex** rule, so the Conway–Sloane codes are Sprague–Grundy P-sets, feeding straight into
the integral lattices — `turning game → mex → lexicode → Golay → Construction A → theta`,
one chain across three pillars. And thermography turns out to **be** tropical arithmetic
in disguise: the option-folds are the tropical `⊕`, cooling is the tropical `⊗`, and the
two scaffold walls live in the dual `(max,+)`/`(min,+)` semirings — named in
`scalar/tropical.rs` and machine-checked equal to the golden thermograph.

**the lattice wing.** The mod-8 spine surfaces one more place: integral lattices. `E₈` is
the unique rank-8 even unimodular lattice, and from it the wing fans out — discriminant
forms with their Weil `S`/`T` matrices and the Brown `ℤ/8` invariant; Conway–Sloane
`p`-adic genus symbols and explicit Kneser neighbors with mass-closed reports; codes
feeding Construction A/D up to `BW16` and `D16+`; ADE roots acting as Clifford Pin
versors and replaying the Weyl reflections; exact theta series identified inside
`ℂ[E₄, E₆]`; Leech pinned by rootlessness in weight 12; and the 24-class Niemeier
catalogue checking the rank-24 mass against `E₁₂` and the 691. Lattice signature, real
Brauer–Wall mod-8 cycle, and Clifford classifier all become directly comparable in the
core.

## The char-2 point

This is the load-bearing technical detail, so it gets its own heading. In characteristic
2 the quadratic form and its polar form carry **different data**, and the engine stores
them separately:

```text
e_i^2             = q_i      # the quadratic form
e_i e_j + e_j e_i = b_ij     # the polar / anticommutator (alternating: b_ii = 0)
```

For nimbers `−1 = 1`, so an orthogonal basis (`b = 0`) gives a *commutative* Clifford
product; a nonzero off-diagonal `b[(i,j)]` is what makes a characteristic-2 example
noncommutative. Collapse `q` and `b` into one symmetric form and you have silently thrown
away the entire point of the nimber backend. (An optional third field `a` lifts the
engine to a general, non-symmetric bilinear form.)

The spinor module has its own characteristic-2 route — no `½(1+w)` idempotent, blade
idempotents like `e_i e_j` when they shrink a left ideal, otherwise an honest fallback to
the full left-regular action. In characteristic 0, general-bilinear metrics are handled
by transporting through the antisymmetric `a` gauge to the matching ordinary `(q,b)`
metric; characteristic 2 keeps the explicit nonzero-`a` boundary.

## Quickstart

Requires Rust and Python ≥ 3.9.

```sh
python3 -m venv .venv
.venv/bin/pip install maturin
VIRTUAL_ENV=.venv .venv/bin/maturin develop
.venv/bin/python demo.py
```

```python
import ogdoad as pl

# characteristic-2 nimber Clifford: non-orthogonal => noncommutative
A = pl.NimberAlgebra(q=[pl.Nimber(2), pl.Nimber(3)], b={(0, 1): 1})
e0, e1 = A.gen(0), A.gen(1)
e0 * e1 + e1 * e0                   # *1  (the anticommutator b[(0,1)])

# surreal metric: infinite and infinitesimal squares are exact
S = pl.SurrealAlgebra(q=[pl.omega(), pl.epsilon()])
(S.gen(0) * S.gen(1)) ** 2         # -1

# the games bridge: Hackenbush reads out as a surreal OR a nimber
B, G = pl.Color.blue(), pl.Color.green()
pl.Hackenbush.string([B, B]).value()      # a surreal number
pl.Hackenbush.string([G, G]).grundy()     # a nimber (all-green = Nim)

# char 0 <-> char 2: a classification on each leg
pl.classify_real(1, 3)             # Cl(1,3) over R, the 8-fold table
pl.arf_nimber(A)                   # the char-2 mirror invariant
pl.bw_class_nimber(A)              # the char-2 Brauer-Wall class, if nonsingular

# local <-> global: Hasse-Minkowski + Hilbert reciprocity over Q
pl.is_isotropic_q([1, 1, 1])       # False (anisotropic over Q)
pl.hilbert_product((-1, 1), (-1, 1))  # +1  (reciprocity)
```

The Python surface is **runtime-friendly parity**: every backend that is a plain runtime
type is bound, while open-ended const-generic families (arbitrary `Qp<P,K>`, `Qq<P,N,F>`,
…) stay Rust-only unless they get an explicit fixed dispatch slice. See
[`src/py/AGENTS.md`](src/py/AGENTS.md) for the full bound surface and the policy.

Prefer no Python? The Rust tour needs none:

```sh
cargo run --example tour
```

## Layout

A pure Rust math core, generic over a `Scalar` trait, with PyO3 per-backend bindings on
top. Each `src/` pillar has its own `AGENTS.md` with the file-by-file breakdown:

- `src/scalar/` — the `Scalar` trait and every coefficient world, grouped by place.
- `src/clifford/` — the multivector engine, geometric product, and the GA layer
  (versors, outermorphisms, Hopf/divided-power structures, conformal/projective GA,
  spinors, Frobenius maps, including the characteristic-2 nimber spinors).
- `src/forms/` — the quadratic-form classifiers across the characteristic trichotomy,
  plus Witt/Brauer–Wall, the Springer trio, `local_global/` for Hasse–Minkowski and
  Hilbert symbols, and `integral/` for lattices, genus, Kneser neighbors, Weyl-versor
  reports, discriminant forms and Weil matrices, codes, theta/modular forms, `BW16`,
  `D16+`, Leech, and the Niemeier catalogue.
- `src/games/` — normal-, misère-, and loopy-play impartial games, finite loopy-partizan
  graphs, short partizan games, thermography/atomic weight, Hackenbush, the exterior
  algebra of the game group, and the checked integer Clifford deformation surface.
- `src/ogham/` — the Ogham expression-language core: lexer/parser/AST/unparser,
  fixed-world evaluator (Clifford worlds plus polynomial/ratfunc function worlds), error
  taxonomy, and conformance support.
- `src/py/` — the optional PyO3 bindings behind the `python` feature.
- `src/linalg/` — crate-private shared linear algebra (exact integer HNF/Smith, F₂/nim
  rank, generic field solves).

See `AGENTS.md` for the working-notes summary, `docs/OPEN.md` for the genuine open
problems, the other `docs/` ledgers for the cross-pillar bookkeeping, `docs/ogham/` for
the language contract, and `writeups/` for the draft notes.

## The bridges — a traveller's catalog

The pillars are joined by named **bridges** (summarized in the `AGENTS.md` files; the
catalog below walks them). Five islands: **S**calar, **C**lifford, **F**orms (the
classifier core), the **I**ntegral wing, **G**ames. Eighteen crossings — Bridge N is four
footbridges — each listed with its banks. A bridge with both feet on one island is a
loop; crossing it counts like any other.

| bridge | banks | what it carries |
|---|---|---|
| A | I–C | even lattice → Clifford metric; bounded FQM Witt class and Milgram phase = signature mod 8 |
| `clifford-lattices` | C–I | `BW16` from Clifford/spinor module rows; `Aut(BW16)` as the index-2 real Clifford subgroup |
| B | C–F | char-2 Arf/Brauer–Wall classification over the `Fpn<2,N>` coefficient fields |
| C | S–C | Frobenius/Galois maps as outermorphisms, with flat exterior spectrum |
| D | S–C | `Ordinal` as a checked Clifford scalar — genuinely transfinite char-2 squares |
| E | I–I | theta series identified in `ℂ[E₄,E₆]`; the Milnor isospectral pair, executable |
| F | C–F | the rational Clifford invariant `c(q) = s(q) + δ(n mod 8, disc)`, corrected, and its graded `BW(ℚ)` lift via dimension parity + signed discriminant |
| H | I–I | Construction A: codes ↔ lattices; MacWilliams ↔ the theta transformation |
| I | I–F | the Weil representation of the discriminant form; a third route to σ mod 8 |
| J | S–F | the valuation as (lax) tropicalization; Newton slopes **are** Springer layers |
| K | S–F | the full `ℚ/ℤ` cyclic-algebra Brauer invariant, unramified plus tame Kummer; reciprocity over `F_q(t)` |
| M | F–I | the Brown `ℤ/8` invariant — the char-2 cell of the mod-8 spine, float-free |
| N.1 | F–I | Milnor's exact sequence: the Springer residues go global over `ℚ` and `F_q(t)` |
| N.2 | S–F | the Scharlau transfer, named and tested |
| N.3 | I–I | Nikulin: genus and existence via signature + discriminant form |
| N.4 | I–I | one Bernoulli source for the Eisenstein constants and the mass formula |
| O | G–I | lexicodes: the turning-game P-set is greedy = mex; the `[24,12,8]` lexicode is Golay |
| `game-clifford-checked` | C–G | checked integer Clifford data on game generators; quotient-compatible, not game-native |

(G and L were never built under those letters — they became the deferred stars `*1`
(spinor genus, `docs/COMPLETENESS.md`) and `*2` (the char-`p` Drinfeld mirror,
`docs/CONTINUATIONS.md`). The alphabet still has two pontoons missing;
`game-clifford-checked` is the later unlettered C–G span and `clifford-lattices` is the
later unlettered C–I return span.)

**The traveller's question** (Euler, 1736): can you cross every bridge exactly once and
end where you began? Count the bridge-ends per island:

| island | S | C | F | I | G |
|---|---|---|---|---|---|
| degree | 5 | **7** | **8** | 14 | 2 |

An Euler circuit needs every island even. **Forms — the island the mod-8 spine runs
through — stays balanced, at degree exactly 8.** The Integral wing, long the lone odd
island, is even now too: the `clifford-lattices` return span (C–I) is the bridge that
balanced it (13 → 14). But the very same span tipped **Clifford** odd (6 → 7), so the
obstruction did not vanish — it *moved*. Today the odd islands are **Scalar and
Clifford**, so an open Euler *stroll* exists (Scalar → Clifford), but the closed grand
tour still does not. The integral wing, with its four loops (E, H, N.3, N.4), remains the
one place a traveller may wander in circles.

Closing the tour now wants a *third* Scalar–Clifford span — bridges C and D are the two
it already has. None of the pending threads supplies one: **`*2` (S–I)**, the
Drinfeld/Carlitz mirror, would even Scalar but tip the Integral wing odd in turn; `*1`
(the spinor genus), `*4` (the wild local symbol), and `under` (a constructive
thermography ↔ Newton-polygon bridge) each matter on their own terms but land elsewhere
on the map. The round trip stays open — and the obstruction has simply walked from the
Integral shore to the Clifford one.

## The research thread

The narrow mathematical thread in `docs/OPEN.md` and `writeups/goldarf.tex` is *not* a
claim of a new Clifford classification theorem. It is an investigation of game-built
quadratic forms in the nimber backend:

1. Turning-Corners games realize nim multiplication.
2. Frobenius squaring and traces are built from nim multiplication and XOR.
3. Gold-style trace forms `Tr(λ · x^{1+2^a})` are therefore expressible from game-value
   operations.
4. The Arf invariant gives the standard zero-count bias for a quadratic zero set.
5. **The open question:** is there a natural, non-tautological game rule whose
   P-positions are exactly such a zero set? Current probes span normal play, misère
   quotient, interactive (`kernel`), loopy (Draw-set), and bent-form searches; they
   narrow the target but do not hit it.

If you want to play along, the open-problem examples (`interactive_kernel`, `octal_hunt`,
`loopy_quadric`, `misere_quotient`, `bent_route`) are the doors in.

## Status and limits

Active research code with tests, examples, and experiments. Treat green tests as
regression evidence, not as proof of the mathematical program. CI runs `cargo fmt
--check`, `cargo clippy --all-targets` (warning-clean), `cargo test`, `cargo check
--features python`, `cargo check --examples`, and `cargo doc --no-deps`.

Scope boundaries, stated plainly:

- `Nimber(u128)` is exactly `F_{2^128}`. It holds the nim subfields of degree dividing
  128; it is not the proper-class field of all nimbers.
- `Ordinal` nim-addition is general on the represented CNF terms, and it implements
  `Scalar` for Clifford experiments inside the checked Kummer boundary.
  Nim-multiplication works below `ω^(ω^ω)` whenever every carry uses a verified finite
  Lenstra excess row (OEIS A380496 b-file, 126 rows, odd primes `3..=709`); a carry
  needing a prime past that table (the first unknown is `719`) returns `None`. Finite
  ordinal-nimber metrics classify through their detected `F_{2^m}`; genuinely transfinite
  metrics stay outside the classifier.
- `Surreal` uses finite support and rational coefficients — the honest truncation of true
  CNF. Non-monomial inverses are infinite Hahn series and are not represented.
- `Qp`, `Qq`, `Laurent`, `Ramified`, `Gauss`, and `Adele` are finite-precision
  (capped-relative) models, not exact infinite-memory local fields. They are useful for
  local/global form experiments and excluded from the exact-ring fuzz.
  `ExactScalar` / `ExactFieldScalar` / `PrecisionScalar` name that boundary explicitly —
  opt-in markers, not `Scalar` supertraits.
- Fixed-width integer payloads are consistently `u128`/`i128` for arithmetic carriers,
  residues, invariants, counts, and budgets. `usize` is for indices, dimensions, and ABI
  hooks.
- The Gold/Arf game thread is conditional: *if* a game has P-set `{Q = 0}`, Arf predicts
  the win-bias. No non-tautological natural game with that P-set has been found.

License: AGPL-3.0-or-later (see `LICENSE`).
