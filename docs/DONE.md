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
stay in [`OPEN.md`](OPEN.md), loopy-valued: `tis`/`tisn`, `on`/`off`, `over`/`under`.

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
**Completed:** 2026-06-19
**Summary:** the games pillar now has game-valued heating, Berlekamp
overheating, and Norton multiplication beside the thermograph/cooling surface.
**Pillars:** games    **Claim level:** standard math, implemented and tested
- surface: `heat`, `norton_multiply`, `overheat`, `is_positive_game`, and
  `integer_game_value`, plus Python module functions and `Game` methods for
  `heat`, `norton_multiply`, and `overheat`.
- oracles: heating fixes numbers and sends `{1|-1}` heated by `2` to `{3|-3}`;
  non-dyadic heating temperatures reject honestly; Norton multiplication by unit
  `1` is the identity, nonpositive units reject, integer-unit Norton products
  have the expected mean, and Berlekamp overheating uses Norton multiplication
  on integer leaves.
- boundaries: this is finite short-game infrastructure only. It does not claim
  that Norton multiplication descends to a product on the temperature
  associated graded; that compatibility remains the `under` open problem.

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
  program but does not realize a game P-set or solve the loopy-valued open
  problem.

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
  reframing over `F_2`-valued metrics; the game realization of `Q` as a P-set
  remains the loopy-valued `tis` open problem, and higher finite char-2 fields
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
