# Cross-pillar work — CONTINUATIONS (genuinely new features)

The ledger of buildable items that **extend ogdoad past what it currently covers** —
new directions and features, not the completion of a connection already in the code.
The two exemplars are the **ogham** language work (a whole sub-language growing toward
recursion + games) and the **char-`p` Drinfeld/Carlitz mirror** (a candidate second
headline pillar). Items that round out an existing symmetry or bridge — most of the
standing content — live in [`COMPLETENESS.md`](COMPLETENESS.md); newly completed work
goes in [`DONE.md`](DONE.md); genuine research questions in [`OPEN.md`](OPEN.md).

Claim-level discipline (`AGENTS.md` → "Claim levels and non-claims") applies to every
item: each is **standard math** or **engineering** when built — not a new theorem.

Items are valued exactly as in [`COMPLETENESS.md`](COMPLETENESS.md) — a game value `g`
on a pillar blade `e_B` (the "How items are valued" legend is canonical there). Numbers
are cold/buildable, `±n` switches are a9's scope call first, `↑` ups are infinitesimal,
`*n` stars are deferred not-yet-numbers; reference items by **slug**.

---

## numbers — ogham (the language)

(`ogham-0.3.0` — the recursion + games build, converted from star `*8` when
its sketch landed — shipped on 2026-07-09, the same day; its entry moved to
[`DONE.md`](DONE.md).)

(`ogham-reflect` — the consolidation pass, grown into the **0.3.5
reflection release** — shipped 2026-07-10; its entry moved to
[`DONE.md`](DONE.md) as `ogham-0.3.5`.)

### 2·e_o: `ogham-0.3.6`
**The second comprehensive adversarial pass — REQUIRED before release**
(a9's call, 2026-07-09, at the 0.3.5 charter review: "we found enough bugs
here that I want to do a second comprehensive adversarial pass"). Plays
after the 0.3.5 build ships, in a fresh session with fresh eyes: the full
four-perspective + codex-seat discipline re-run against the *unified* spec
and the *unified* runtime (the reflection pass reviewed 0.3.0; nobody has
adversarially reviewed 0.3.5's own new surface — the nine-cell
implementation, the multiset `≡` bisimulation, the product-graph sums, the
runtime unification). Also carries the deferred **release scoping, a9's
call**: ogham as ogdoad's front door vs an `ogham` crate re-exporting the
core, README/writeup (the CGSuite comparison lives there, not in the
spec), and the public name. Nothing releases before this pass. (Value
provisional; a9 to re-value.)

Seed punch-list from the 0.3.5 build's own gate (sol, 2026-07-10, plus
fable's gate finds): consolidate the four `eval_index` copies (keep the
`@`-inside-Index regression); re-attack the singles' seam — tight-budget
error precedence when the stopper gate passes but the difference build
exceeds `E_GraphBudget`, and randomized stopper-pair agreement between
projected singles and the nine cells (a bounded graph-level projection
oracle); synthesized display names `g1, g2, …` allocate without a
collision set against user-rooted names — mixed named/anonymous
composites may read as capture; pin multi-SCC / shared-subgraph /
duplicate-edge / nested-negated-sum displays and first-reach stability
under equivalent presentations; add parse/display round-trips for
synthesized multi-equation bodies beyond the blessed representatives.

### 4·e_o: `ogham-0.4.0`
**The higher-order release** — slimmed at the reflection pass
(2026-07-09): 0.3.5 absorbed the old sketch's entire envelope program
(the pillar stage — `neg`/`sum`/stopper detection/survival on
`LoopyPartizanGraph` — and the language stage — stopper relations via
the nine-cell projection, total loopy `+`/`-`, `stopper()`,
witness-carrying `E_Loopy` — plus the persistent worker). What remains,
per `docs/ogham/ogham.md` §18, in order: (1) the **higher-order gate**,
0.4.0's opener — map/fold, functions-as-values, decided against the
Index-recursion pain 0.3.x makes measurable; no Sequence sort; (2)
**mutual `=:` groups** (adjacent-binding grammar, pure error→value);
(3) **`canon` on stoppers** (fusion/simplest form — the largest
genuinely-new math item, independently slippable, last); (4)
**one-stopper biased comparison** (the sided machinery loosening the
both-stoppers gate; onside/offside sidling for non-stoppers stays open
beyond it); (5) the measured **floor** (trampoline vs `stacker` vs
targeted work-stacks — the dependency question is a9's — retiring the
depth guard; array-side envelope on measured pain). Plays after
`ogham-0.3.6` and release. Value proposed at `4·e_o`; a9 to re-value.

---

## numbers — cross-pillar (new bridges)

### 2·(e_f∧e_i): `z4-codes`
**`ℤ/4`-linear codes and the Gray map — making Brown's Bridge-M cell load-bearing.**
Bridge M ships the `ℤ/4`-valued quadratic refinement and its Brown `ℤ/8` invariant
(`forms/char2/brown.rs`), but nothing in the code/lattice wing consumes the `ℤ/4`
structure. `ℤ/4`-linear codes are the join: a `ℤ/4`-code carries exactly a Brown-type
`ℤ/4` quadratic form, its **Gray map** sends it to a (usually nonlinear) binary code, and
the **Kerdock/Preparata** pair — formal duals under the `ℤ/4` MacWilliams identity, the
classical resolution of their long-mysterious binary "duality" — head the family
(Hammons–Kumar–Calderbank–Sloane–Solé, IEEE-IT 1994). The same `ℤ/4` data feeds
Construction-A-style lattices (the `ℤ/4`-Construction-A route to `BW` lattices, tying back
to `clifford-lattices`). This makes the Brown cell a **hub instead of a leaf**: `over`
(`OPEN.md`) asks whether the `ℤ/4` census has a *game* reading; this asks the parallel
*code/lattice* question, which is standard math and fully buildable. New `ℤ/4`-code type,
the Gray map, `ℤ/4` MacWilliams, and Kerdock/Preparata witnesses.

### 2·(e_c∧e_i): `barnes-wall-tower`
**The whole `BW_{2^n}` family, generalizing the `BW16` certificate.**
`clifford-lattices` + `reed-muller` (DONE) build `BW₁₆` two ways — Construction D
from `RM(0,4) ⊆ RM(2,4)`, and the reverse Clifford certificate from the real spinor
weight basis indexed by `F₂⁴` with quadratic-phase rows — both hard-coded to `n = 4`.
The Barnes–Wall lattices `BW_{2^n}` are an infinite tower
(`BW₂ = ℤ², BW₄ = D₄, BW₈ = E₈, BW₁₆, BW₃₂, …`) built from the same data at every
scale: the Reed–Muller tower `RM(k,n)` for Construction D, and the real spinor module
of `Cl(2n)` with degree-`≤ 2` quadratic phases for the Clifford side, with
automorphism group the **real Clifford / Bolt–Room–Wall group** `2^{1+2n}.O⁺(2n,2)`
(its index-2 subgroup is `Aut(BW_{2^n})` for `n ≥ 3`). The shipped BW16 constants
(`BW16_REAL_CLIFFORD_GROUP_ORDER`, the index-2 relation) are the `n = 4` row of a
closed formula. Build `barnes_wall(n)` — Gram + Clifford certificate + the
general-`n` group order — for the whole tower; the determinant and certificate stay
exact at any `n`, while the geometry oracles (`minimum` / `kissing_number`) verify
only the small rungs before the short-vector search explodes (note that ceiling
honestly, no silent cap). Makes the C–I Clifford-lattice span a *family* rather than
a single witness. References: Barnes–Wall; Nebe–Rains–Sloane, *The invariants of the
Clifford groups*.

### 2·e_c: `weyl-algebra`
**The CCR mirror of the Clifford engine — the missing corner of the deformation
square.** The repo ships the exterior algebra `Λ` (the blade engine / game-exterior)
and its char-faithful symmetric dual `Γ(V)` (`divided_power.rs`, the deconcatenation
co-side of `Sym`). The Clifford algebra is the **CAR** (anticommutator) deformation
of `Λ`: `eᵢeⱼ + eⱼeᵢ = bᵢⱼ`. Its mirror across the square is the **Weyl algebra** —
the **CCR** (commutator) deformation of `Sym`: `∂x − x∂ = 1` — and char-faithfully
the **divided-power / Hasse-derivative** Weyl algebra (the hyperalgebra
`⟨x^{(i)}, ∂^{(j)}⟩`, `∂^{(j)}x^{(i)} = binom · x^{(i−j)}`, where the char-`p`
binomial collapses make `∂^{(p)} ≠ 0` survive exactly as `γ^{(2)} ≠ 0` does in char
2). Completes:

```text
            antisymmetric        symmetric
deformed    Clifford (CAR) ✓     Weyl (CCR)  ← new
free        exterior  Λ    ✓     divided Γ   ✓
```

A standalone engine paralleling `divided_power.rs` (own monomials, Python
`<World>WeylAlgebra`), char-faithful via Hasse derivatives so it runs over
nimbers / `Fp` / surreals like the rest. The payoff is the one the Clifford engine
already has — a representation theory (Weyl-algebra modules = `D`-modules; the
Fock/oscillator rep mirrors the spinor module) — now on the symmetric side. Standard
math (Weyl algebra; divided-power/hyperalgebra in char `p`: Berthelot–Ogus, Gros).
A genuinely new fourth algebra engine, the one the `hopf` / `divided_power` mirror
has been pointing at — not a completion of an existing bridge.

### 1·(e_f∧e_i): `pointed-mtc`
**The pointed modular tensor category `C(A,q)` — reading `DiscriminantForm` as an
anyon theory.** The data is already shipped: the finite quadratic module *is* the
fusion group + twists (`θ_x = e^{2πi q(x)}`), the Weil `S`/`T` matrices *are* the
modular data, and Gauss–Milgram *is* the central charge `c ≡ sign(L) mod 8`. The
continuation is the thin categorical layer that makes it official: fusion ring
(group algebra), Verlinde check (`S` diagonalizes fusion), twist/braiding
consistency, and the central-charge identity — all exact or `Complex64`-bounded on
the existing surface. Cheapest item on this list relative to what it reframes:
Bridges I/M become an executable abelian-anyon engine, and Nikulin's
discriminant-form theory gets its modern physics reading. References: Rowell–Stong–
Wang; Bakalov–Kirillov; Nikulin.

### 1·(e_f∧e_g): `polar-spaces`
**Finite polar spaces and generalized quadrangles from the char-2 form surface.**
The symplectic/quadratic `F₂` layer, the extraspecial group, and the Pauli
commutation relations all describe the same finite incidence geometry — and the
crate never exposes it *as* geometry. Build the polar space: points = projective
points, collinearity = polar-form orthogonality, totally-isotropic subspaces,
`W(3,2)` (the doily) from `Sp(4,2)`, ovoids/spreads censuses, quadric point-sets as
the geometric face of the Arf zero-count. Consumers on both sides: the extraspecial/
Pauli layer (commutation graphs) and the quadric P-set bench (incidence data for the
probes) — with no claim on the open Gold rule (`OPEN.md` tis stays untouched; this
is the geometry, not the game). References: Payne–Thas; Taylor.

### 1·(e_i∧e_g): `matroid-tutte`
**Matroids, deletion/contraction, and Greene's theorem.** Represented matroids from
the shipped generator matrices (`BinaryCode`/`PrimeCode`), rank/nullity and Tutte
polynomial via deletion–contraction, and **Greene's theorem** — the weight enumerator
as a Tutte-polynomial evaluation — pinned against the MacWilliams/WE surface already
in `codes.rs`. Joins the games→lexicode→Golay→Construction-A chain with a genuinely
new combinatorial invariant layer (and graphic-matroid examples from the ADE
diagrams fall out for free). More mechanical than deep, but every oracle is already
shipped. References: Greene 1976; Oxley; Brylawski–Oxley.

### 2·(e_c∧e_i∧e_s): `octonions`
**Composition algebras — the Cayley–Dickson tower over any `Scalar`.** Quaternions,
octonions, and their split forms as a new (nonassociative!) algebra engine beside
Clifford/exterior/divided-power: Moufang laws and norm multiplicativity proptested
over the scalar worlds, char-2 behavior honest (the norm form degenerates the same
way the rest of the char-2 story does), and the **integral octonions** whose norm
form is `E₈` — with the shipped `e_8()` lattice as the oracle (Coxeter's order,
240 units). Triality adjacency to the spinor layer is the long-game payoff. A real
new engine (nonassociativity means the blade machinery doesn't carry over), which
is what the `2` prices in. References: Conway–Smith; Springer–Veldkamp; Baez.

### 2·(e_i∧e_c): `lorentzian`
**`II_{25,1}` — the Lorentzian mirror of the Niemeier wing.** The integral wing is
positive-definite; the Conway-est extension is the even unimodular Lorentzian
lattice: exact indefinite Gram, Leech roots (`r² = 2`, `r·w = −1`), the Weyl vector
`w = (0,1,…,24 | 70)` (the sum-of-squares coincidence made load-bearing),
reflections through the shipped Weyl-versor machinery, and Conway's identification
of the reflection group with the Leech affine structure — with the 24-class Niemeier
catalogue as the *verification oracle* (deep holes ↔ the 23 rooted classes, the holy
constructions recovering their root systems). Honest boundaries stated up front:
geometry oracles (`minimum`/`kissing_number`) stay `None` for indefinite forms, and
the first build is named checks (Weyl-vector identities, root recognition, per-class
hole data) — the full deep-hole classification machinery is the follow-on, not the
item. References: Conway–Sloane SPLAG chs. 26–27; Conway 1983; Borcherds.

---

## switches (a9's move first)

### ±3·e_s: `surreal-exp`
**Gonshor's exp/log on No.** The exact surreal backend growing genuine analytic
structure: `exp(ω) = ω^ω`-flavored normal forms (Ressayre), `log` on positive
surreals, the induced ordered-exponential-field structure — all exact on represented
CNF windows, `None` beyond, matching the house precision honesty. Conceptually the
strongest scalar-world extension available (No becomes an exponential field, which
is what it *is* in the literature), but the scope risk is the highest on this list:
Gonshor's recursion is subtle, the interaction with the finite-support Hahn
representation needs real design, and the value is `±3` only if sharply bounded to
exp/log on monomial-representable arguments first — otherwise it drifts starward.
a9's call on whether the exact leg wants analysis at all (the same conversation
`surreal-completion` opens from the capped side). References: Gonshor ch. 10;
Berarducci–Mantova; van den Dries–Ehrlich.

### ±3·(e_i∧e_f): `cm-lattices`
**Hermitian lattices over the CM rings `ℤ[i]`, `ℤ[ω]`, and the Hurwitz quaternions.** The
integral wing is all `ℤ`-lattices; the on-thesis enrichment is the "(field, ring of
integers)" axis — the project's spine — applied to the complex/quaternionic worlds:
Hermitian Gram matrices over an imaginary-quadratic or quaternion order, with the
underlying real lattice recovered by restriction of scalars. The payoffs are canonical —
the **Coxeter–Todd `K₁₂`** as a rank-6 `ℤ[ω]`-lattice from the Eisenstein Construction A
lift adjacent to the ternary-Golay real shadow, the **complex Leech** as rank-12 over
`ℤ[ω]`, and the **quaternionic Leech** as rank-6 over the Hurwitz order, each with its
automorphism group as a unitary/symplectic group. The decision is a9's: how much
complex/quaternionic lattice arithmetic the integral wing wants to own (a Hermitian-Gram
type, a `complex_construction_a`, CM theta as Hilbert/Jacobi forms) versus keeping
`ℤ`-lattices as the deliberate boundary, with CM lattices appearing only through
restriction of scalars. Pairs with `hermitian-finite` (the finite mirror) and
`construction-a-p` (the plain `ℤ` p-ary shadow).
References: Conway–Sloane SPLAG ch. 7 & 10; Nebe's Hermitian-lattice catalogue.

---

## stars (deferred — the not-yet-numbers, confused with zero)

The star numbers are one shared nim-sum scheme across both buildable ledgers; the
sibling stars `*1` (spinor genus) and `*4` (the wild local symbol) live in
[`COMPLETENESS.md`](COMPLETENESS.md).

### *2: `the char-p Drinfeld/Carlitz mirror of the integral pillar` (large)

The entire `integral/` wing — even-unimodular `ℤ`-lattices, `θ`-series,
`M_*(SL₂ℤ) = ℂ[E₄, E₆]`, Construction-A codes, Leech — is char 0. The project already
ships **exact** `F_q[t] ⊂ F_q(t)`, the char-`p` global field, whose arithmetic carries a
complete mirror:

- the **Carlitz module** `C_t(x) = t·x + x^q` is the char-`p` analogue of `exp` / the
  lattice exponential; the mirror of `E₄, E₆` are **Drinfeld modular forms** for
  `GL₂(F_q[t])`, with Goss `ζ`-values mirroring the Eisenstein constants;
- rank-`r` `F_q[t]`-lattices mirror even-unimodular `ℤ`-lattices and their reduction
  theory;
- **Goppa / algebraic-geometry codes** from function fields tie straight back into the
  existing `codes.rs` Construction-A machinery — the same code↔lattice seam in char `p`.

This is the `No ↔ On₂` / char-0 ↔ char-2 move applied to the richest pillar — the most
on-thesis possible "new structure." But it is a genuine new wing (Drinfeld modules, the
Carlitz exponential, rank-`r` reduction theory): weeks of specialized work, worth starting
only as a *second headline pillar* rather than a task. References: Goss, *Basic Structures
of Function Field Arithmetic*; Gekeler, Drinfeld modular forms; Goppa / AG codes.

(The former `*16` — `ogham 0.3.1 — the envelope release` — relabeled
**ogham 0.4.0** and converted to the numbered `4·e_o: ogham-0.4.0` entry when
its sketch landed in `docs/ogham/ogham.md` §20, 2026-07-09, per this
section's own hold-until-sketch rule; the envelope program grew into
base-program work and moved behind the functions-as-values gate. Nim-sum
naming stays honest: `*9`–`*15` were sums of stars that have existed
(1, 2, 4, 8).)

(The former `*8` — ogham 0.3.0 — converted to the numbered `4·e_o: ogham-0.3.0`
entry when its sketch landed, 2026-07-09, and shipped the same day; see
`DONE.md`.)
