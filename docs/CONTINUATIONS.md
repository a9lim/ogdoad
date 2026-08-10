# Cross-pillar work — CONTINUATIONS (genuinely new features)

The ledger of buildable items that **extend ogdoad past what it currently covers** —
new directions and features, not the completion of a connection already in the code.
The two exemplars are the **grundy** language work (a whole sub-language growing toward
recursion + games) and the **char-`p` Drinfeld/Carlitz mirror** (a candidate second
headline pillar). Items that round out an existing symmetry or bridge — most of the
standing content — live in [`COMPLETENESS.md`](COMPLETENESS.md); newly completed work
goes in [`DONE.md`](DONE.md); solved research questions are indexed in
[`CLOSED.md`](CLOSED.md), and genuine research questions in [`OPEN.md`](OPEN.md).

Claim-level discipline (`AGENTS.md` → "Claim levels and non-claims") applies to every
item: each is **standard math** or **engineering** when built — not a new theorem.

Items are valued exactly as in [`COMPLETENESS.md`](COMPLETENESS.md) — a game value `g`
on a pillar blade `e_B` (the "How items are valued" legend is canonical there). Numbers
are cold/buildable, `±n` switches are a9's scope call first, `↑` ups are infinitesimal,
`*n` stars are deferred not-yet-numbers; reference items by **slug**.

---

## numbers — grundy (the language)

(`ogham-0.3.0` — the recursion + games build, converted from star `*8` when
its sketch landed — shipped on 2026-07-09, the same day; its entry moved to
[`DONE.md`](DONE.md).)

(`ogham-reflect` — the consolidation pass, grown into the **0.3.5
reflection release** — shipped 2026-07-10; its entry moved to
[`DONE.md`](DONE.md) as `ogham-0.3.5`.)

**The ladder** (set 2026-07-10 at the 0.3.6 pass, a9's calls): the bug
count at 0.3.5 read as immaturity, so release moved out two rungs —
**0.3.6 → 0.3.7 → 0.3.8 → 0.4.0 = the public release → 1.0.0**. The old
0.4.0 sketch was split by kind: envelope extensions (error→value) and
floor engineering matured *inside* the prereleases; the identity change
(higher-order) became 1.0.0's question. Release shape decided with the
ladder: **ogdoad ships with grundy as its front door** — no separate crate;
the installed `ogdoad` binary launches the REPL; one public version clock
(ogdoad 0.4.0 contains grundy 0.4.0).

**The name** (2026-07-15, a9's call, provisional): the language — **ogham**
from birth through 0.3.6 — is renamed **grundy**, after P. M. Grundy of the
Sprague–Grundy theorem: a person-name in the Haskell tradition, honoring the
value the language deliberately keeps as four lines of user code rather than
a primitive. Context: crates.io `ogham` was taken 2026-06-13 by an unrelated
live crate (verified 2026-07-10, re-verified 2026-07-15); `grundy` is free as
of 2026-07-15. Name finalization — confirm grundy or settle otherwise, and
decide whether the language claims its own crate slot or stays inside ogdoad
only — is a 0.3.8 release-dress item. History keeps the shipped name: DONE
entry keys, gaslamp threads (`ogham-036-*`/`ogham-v36`), and the merged
provenance corpora (`grundy/docs/conformance_v*.txt`) are not rewritten.

(`ogham-0.3.6` — the second comprehensive adversarial pass — **shipped
2026-07-10**, same day as its sweep and spec rewrite; its entry moved to
[`DONE.md`](DONE.md) as `ogham-0.3.6`. The contract is
`grundy/docs/spec.md`; the sweep verdicts, decisions, and build record live
in the DONE entry and the `ogham-036-*`/`ogham-v36` gaslamp threads.)

### 2·e_o: `grundy-0.3.7`
**The structural rung.** (1) **Ordinal sum `G:H`** — the CGT seat's top
demand ("the mathematical colon belongs in this stroke language"); engine
already ships `Game::ordinal_sum`, and 0.3.6's conditional-word move freed
the colon entirely — remaining work is the precedence/associativity choice
and the corpus family. (2) **Games-pillar absorption** — regular-game mathematics
(rooted multiplicity-preserving graphs, short-game exits, neg/sum, stopper
witnesses, nine-cell outcomes, regular-tree bisimilarity) moves to
`src/games/loopy/`, killing the double-model seam; language keeps
lowering/guardedness/provenance/recognition/display. (3) **The floor** —
trampoline vs `stacker` vs targeted work-stacks (dependency question is
a9's), retiring the `E_StackDepth` frame guard; array-side envelope on
measured pain. (4) **Adversarial pass #3** — fresh eyes on the 0.3.6
surface (the mutual-system closure, the new display, the design tranche).

### 2·e_o: `grundy-0.3.8`
**The loopy-envelope completion + release dress.** Error→value work:
(1) **left/right stops** (`lstop`/`rstop` — dyadic display has bedded in);
(2) **`temperature`/`mean`** as thin calls (thermograph value type stays
refused); (3) **`canon` on stoppers** (fusion/simplest form — the largest
genuinely-new math item; slip-tolerant by design: nothing depends on it,
it slides to 1.x rather than blocking); (4) **one-stopper biased
comparison** (the sided machinery loosening the both-stoppers gate;
onside/offside sidling for non-stoppers stays open beyond it). Release
dress: REPL promoted to installed binary (`src/bin/ogdoad.rs`), README
reversal (transcript-first), `examples/grundy/*.og` gallery, the writeup
(`writeups/grundy.tex` — identity essay, the extended why-this-is-art
argument, the honest CGSuite comparison), corpus split thematically +
`stage_*` tests renamed by law; **name finalization** (the 2026-07-15
ogham→grundy rename is provisional — confirm the name and the crate-slot
question). Theory citation for the loopy envelope: Honsell–Lenisa 2011
(loopy Conway games as a final coalgebra) — the stance note
(`grundy/docs/stance.md`, 2026-07-19) pins the data/codata reading of the
shipped constructs; whether spec §1 states the coalgebraic identity out
loud is a release-dress decision beside name finalization. Final
full-surface pass gates the release.

### `grundy-0.4.0` — **the public release** (after 0.3.8's gate; not a
feature rung). Package/version alignment, publish decision execution.

### 4·e_o: `grundy-1.0.0`
**The higher-order release** — the one identity change left standing:
map/fold, functions-as-values, decided against the Index-recursion pain
0.3.x/0.4.0 makes measurable. No Sequence sort: if Function is promoted it
earns it through **one symmetric map/fold story over the three container
shapes** (fixed/graded/free — the 0.3.6 container totality made this a
three-world question, a better one than the two-world sketch). Mutual
*function* `=:` groups land here (Function representation changes anyway;
Element systems shipped at 0.3.6). **Productive streams** are the codata
face of this rung (`grundy/docs/stance.md`): `ω = {0, 1, 2, … |}`
genetically has a non-periodic option stream — no finite cyclic
presentation exists — so a generator is a function, and lazy transfinites
arrive with higher-order rather than as a separate tack; the
Escardó–Oliva selection monad is the strategy-shaped star to steer by.
Whatever the release soak surfaces
joins the docket. Value proposed at `4·e_o`; a9 to re-value.

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
probes). This is the incidence-geometry continuation of the now-resolved Gold
rule, not an alternate proof of the Witt--FIFO theorem. References: Payne–Thas;
Taylor.

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
