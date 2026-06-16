# Cross-pillar bridges — DONE (the go-forward ledger)

The running ledger of cross-pillar work **completed from here on**.

The cross-pillar bridge-building era (bridges **A–O** plus **K** — lattice/Clifford/
Brauer–Wall, the char-2 Arf classifier, Frobenius outermorphisms, the transfinite
Clifford engine, theta/modular forms, Construction-A codes, the Weil representation, the
rational and full-`ℚ/ℤ` Brauer invariants, Newton polygons, the Brown invariant, the
unification pass, lexicodes) closed with every non-deferred bridge shipped, as did the
ogham 1.x–2.x language work and the transfinite-excess thread. The working-notes summary
of all of it is in the `AGENTS.md` files (root + per-pillar); the historical entry-level
ledger is in git history.

What remains unbuilt is tracked in the two buildable ledgers —
[`COMPLETENESS.md`](COMPLETENESS.md) (completing symmetries and connections already in
the code) and [`CONTINUATIONS.md`](CONTINUATIONS.md) (genuinely new features), each
carrying its slice of the deferred stars `*1`/`*2`/`*4`/`*8`; genuine open problems
stay in [`OPEN.md`](OPEN.md), loopy-valued: `tis`/`tisn`, `on`/`off`, `over`/`under`
(the old numerals §1–§4 survive as aliases).

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
  optimized Golay path, and this solved degree-1 bridge is not progress on the
  open Gold-quadric play-rule question.

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
