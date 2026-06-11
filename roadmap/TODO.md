# Cross-pillar work — TODO (the game-valued ledger)

Every bridge that was *explicitly on the build order* is done — the full record is in
[`roadmap/CODA.md`](CODA.md), and newly completed work goes in the
[`roadmap/DONE.md`](DONE.md) ledger. This file is the ledger of what is **buildable
but not built**: standard math made computational, verification harnesses, and elbow
grease. Nothing here is a genuine research question — those live in
[`OPEN.md`](../OPEN.md) (which carries the loopy-valued entries; open problems give
no termination guarantee).

Claim-level discipline (`AGENTS.md` → "Claim levels and non-claims") applies to every
item: each is **standard math** or **engineering** when built — not a new theorem.

## How items are valued

Natural numbers don't do roadmap items justice, so the ledger is a **game-valued
multivector**: each item is a term `g·e_B` — a game value `g` (its size and temper)
on a pillar blade `e_B` (which pillars it joins; the blade's grade is how
cross-cutting the item is). Blades: `e_s` scalar, `e_c` clifford, `e_f` forms,
`e_i` integral, `e_g` games, `e_y` py; pure-prose chores are scalar-grade (no blade).

| value | temper | meaning |
|---|---|---|
| `n` (numbers) | cold | buildable now; `n` ≈ focused days; `½` ≈ an afternoon |
| `±n` (switches) | hot | a real scope decision belongs to a9 first; size `n` either way |
| `↑` (ups) | infinitesimal | worth less than any number, still strictly positive |
| `*n` (stars) | confused with `0` | deferred not-yet-numbers: real, on-thesis, unscheduled |

Reference items by **slug**. The ledger's total value is the disjunctive sum; play it
in any order, though `echo-solver` is the hottest cold item on the board.

---

## numbers — forms & Witt (the classifier spine)

### `echo-solver` — 2·(e_g∧e_f)
**The decisive-experiment harness** (`writeups/goldarf.tex` §§8–9, ranked moves 1–2).
Build the fresh direct stateful solver — no decomposition extrapolation, full state in
the memo key including `σ`, validated against explicit tree enumeration at `m = 4` —
and run (a) the echo-fifo+dummy `m = 8` benchmarks plus ≥ 20 stratified `λ`, then (b)
the pre-registered echo-ko family sweep. The echo-fifo+dummy exactness claim is the
single most load-bearing **unverified** result in the Gold/Arf program; either CONFIRM
or KILL is informative, and the sweep is minutes per candidate on existing
infrastructure. The harness is tractable engineering; the *outcome* feeds `OPEN.md` §1.

### `milnor-d2` — 1·e_f
**The `p = 2` cell of Milnor's exact sequence** (the CODA N.1 boundary). Implement the
dyadic residue `∂₂ : W(ℚ) → W(F₂)` by Milnor's hand-defined convention
(Milnor–Husemoller Ch. IV; it is *not* Springer's residue — that's why N.1 omitted it)
and extend `witt/milnor.rs::global_residues` to full support. Oracles: exactness on
2-support forms (`⟨2⟩`, `⟨1,2⟩`, `⟨−2⟩`…), reconstruction of the Witt class from
`(signature, all residues)`, cross-check against the shipped Hasse–Minkowski layer.

### `milnor-ff` — 1·e_f
**The `F_q(t)` split-exact twin** of N.1 (the "noted follow-on" in CODA):
`0 → W(F_q) → W(F_q(t)) → ⊕_v W(F_{q^{deg v}}) → 0` (Milnor–Husemoller; Harder). The
local residue engine already exists (`local_global/function_field.rs` per-place
valuations + `springer` buckets); the build is the global assembly and the splitting
(evaluation at the `∞` place). Mirrors `global_residues` field-for-field — the
local↔global symmetry made literal on the equal-characteristic leg.

### `bw-rational` — 2·e_f
**The graded rational Brauer–Wall class** — the lift Bridge F deliberately stopped
short of ("do not conflate `Brauer2Class` with the graded `BrauerWallClass` *until a
rational Brauer–Wall story is separately modeled*"). Model `BW(ℚ)` by Wall's exact
sequence `0 → Br(ℚ) → BW(ℚ) → Q(ℚ) → 0`, `Q(k) = ℤ/2 × k*/k*²` with the twisted
cocycle multiplication (Wall 1964; Lam GSM 67). Oracles: `BW(ℝ) ≅ ℤ/8` recovers the
Bott index `bw_class_real`; the graded class of `Cl(q)` over ℚ projects to Bridge F's
`c(q)` and to disc/dimension data.

### `tame-symbols` — 2·e_f
**Tamely ramified cyclic symbols for Bridge K.** K's local invariant is scoped
unramified-at-`v` (`inv = v(a)/n`). For tame ramification (`n | q−1`) the norm-residue
symbol is explicit (the tame symbol `(a,b)_v = (−1)^{v(a)v(b)} a^{v(b)}/b^{v(a)} mod 𝔪`
in `μ_n`); shipping it widens `BrauerClass` to ramified cyclic classes at tame places
on the `Qq`/`F_q(t)` legs. The **wild** symbol stays out — that is star `*4` below.

### `cyclic-trace-form` — ½·(e_f∧e_s)
**The general-`n` cyclic trace form** `T_A(z) = Trd(z²)` block-decomposed over the
lines `E·uⁱ` — CODA K §6(c) records it as "a composition, not new math; not shipped".
Build `cyclic_algebra_trace_form` through `assemble_twisted_form`; oracle: the degree-2
case reproduces the shipped `⟨1,1,−a,−a⟩` reduced-norm form.

### `brown-reduce` — 1·e_f
**Brown by reduction, not enumeration.** `brown_f2` enumerates `2^rank` vectors and
panics past rank 26. Nondegenerate ℤ/4-valued forms split into rank ≤ 2 pieces with
known `β` (Wall 1963, *Quadratic forms on finite groups*); implement the plane-by-plane
reduction (the `arf_f2` idiom one level up) and retire `BROWN_MAX_ENUM_RANK`. Oracle:
equality with the enumeration route for every rank ≤ 26 input.

### `fqm-witt` — 3·(e_i∧e_f)
**The full Witt group of finite quadratic modules** — the "further rung" CODA M names.
Implement the `p`-local decomposition with Wall/Nikulin/Kawauchi–Kojima generators and
relations: `ℤ/2^{k+1}`-valued refinements for higher 2-power torsion, odd-`p` Gauss
sums exact (Legendre data, no `f64`), per-prime signatures summing to `σ mod 8`.
Payoffs: a float-free `σ mod 8` on **all** discriminant forms (retiring the `f64`
`GaussSum` as an oracle-only route, and closing Brown's 2-elementary boundary); the
exact cyclotomic Gauss sum falls out for free; and Nikulin's *existence* theorem
(1.10.1 — which `(sig, FQM)` pairs are realized by even lattices) becomes buildable
on top as a later rung.

## numbers — the integral wing

### `niemeier` — 3·e_i
**The Niemeier zoo and the non-degenerate Siegel–Weil.** Bridge E's Siegel–Weil check
is degenerate at `n = 16` (both classes share `θ = E₄²`). Build the 24 Niemeier
lattices (root systems + glue codes, Conway–Sloane Ch. 16/18 — curated tables per
`TABLES.md` discipline; Kneser 2-neighbors from Leech is the principled alternative)
with their `|Aut|` orders, then verify the genuine statement at weight 12:
`(Σ_L θ_L/|Aut L|) / mass(24) = E₁₂ = 1 + (65520/691)Σσ₁₁(m)qᵐ` — the Eisenstein
congruence prime **691** appearing in the codebase, and the first Siegel–Weil instance
where the classes genuinely differ. Free cross-checks: `Σ 1/|Aut| = mass_even_unimodular(24)`,
rootless-class uniqueness (Leech), and 24 new Nikulin/N.3 test points.

### `padic-symbols` — 3·e_i
**Conway–Sloane `p`-adic genus symbols** (Ch. 15, incl. the canonical 2-adic symbol
with trains/compartments/oddity fusion). Gives exact genus equality without the
budgeted `is_isomorphic` search — un-capping `ISO_GROUP_CAP` for genus decisions and
turning N.3 from "budgeted cross-check" into "exact symbol comparison". Oracle: full
agreement with the shipped `are_in_same_genus` + `DiscriminantForm::is_isomorphic`
route across the ADE zoo and the Milnor pair.

### `odd-lattices` — 2·e_i
**Type I (odd) lattices for the discriminant chain.** `DiscriminantForm::from_lattice`,
Milgram, Brown, and `theta_series` are all even-only. Ship the odd-lattice discriminant
form (`q_L` valued in `ℚ/ℤ` rather than `ℚ/2ℤ`), the oddity-corrected Milgram statement
(the `genus.rs` oddity is already the independent oracle), and odd Construction A
(`ℤⁿ` from the `[n,1]` repetition code's complement, `ℤ ⊕ E₈`, …). Document the theta
boundary honestly (odd `θ` lives at level 4).

### `constructions-bd` — 1·e_i
**Constructions B and D** (Conway–Sloane Ch. 5/8), extending Bridge H's code↔lattice
seam: B from doubly-even subcode data (oracle: `B(golay)` has the right det/min), D
from nested code towers. Keeps the same `Option`-on-non-integral-Gram boundary as
`construction_a`.

### `eichler` — ½·(e_i∧e_c)
**Eichler's theorem as a documented predicate** — the one cheap honest piece of star
`*1`: *indefinite, rank ≥ 3 ⇒ spinor genus = isometry class*, letting `Genus` upgrade
to a class statement in exactly that regime. No adelic machinery; just the predicate,
its citation (Eichler; Cassels), and tests on indefinite Grams. The full definite
computation stays `*1`.

## numbers — scalar worlds

### `fpn-gen` — 1·e_s
**Open the `Fpn` field table.** The supported-pair set is seven `(P,N)` pairs behind a
panic wall, and `TABLES.md` itself flags the `N = 1` row. Ship either a build-time
irreducible-polynomial generator (deterministic search + Rabin irreducibility test,
recording provenance) or a wider curated Conway-polynomial table. Unblocks Bridge B
coverage (`F₃₂`, `F₆₄`, `F₁₂₈` …), the AS-layer beyond `N ≤ 4`, and the odd-`q`
function-field legs at more constant fields.

### `ordinal-principled` — 1·e_s
**The principled tower route** (OPEN §3 names it "implementation, not research"):
compute `f(u) = ord_u(2)` and `Q(f(u))` and assemble the `χ`-sum in-code, hardcoding
*only* the finite excess integer `m_u`. Independently cross-checks every DiMuro row
the table currently transcribes, and makes shipping a future certified `m_u` a
one-integer diff instead of an ordinal-expression transcription.

### `subfield-detect` — ½·(e_s∧e_f)
**The finite nim-subfield detector** (OPEN §4's implementation-grade target): given a
`Metric<Ordinal>`, find the minimal finite nim-subfield containing every entry, so
Bridge D delegates *all* finite-window metrics to Bridge B honestly — not just the
hardcoded `F₆₄` window. Returns the subfield degree or `None` past the staged segment.

### `hyperfield` — ½·e_s
**Viro's tropical hyperfield**, making Bridge J's lax tropicalization strict (Remark
J.2 names this exact repair): a small multivalued-addition type
(`x ⊞ y = {min}` off the vanishing locus, the interval/set on it) with the hyperfield
laws as tests and `tropicalize` factoring through it. A leaf, but it converts the one
"lax" asterisk in the J appendix into a theorem about a shipped type.

## numbers — games

### `nim-lexicodes` — 1·(e_g∧e_i)
**Lexicodes over nim-field bases** — Bridge O's documented-context-not-shipped
statement made executable: greedy lexicodes over base `2^k` are closed under
nim-addition, and are *linear* exactly when the base is a Fermat power `2^(2^k)`
(Conway–Sloane 1986, the sizes where nim-multiplication makes a field). Implement the
base-`2^k` greedy with nim-addition closure checks; witness linearity at base 4/16 and
its failure at base 8. Discover-don't-assert, like `lexicode_naive`.

### `lexicode-game` — 1·e_g
**The turning-game realization of lexicodes** — Bridge O cites the Conway–Sloane
game construction "for transcription in a formalization pass". Build the actual
turning-game move structure whose Grundy-0 positions are `L(n,d)`, so greedy = mex is
a `Game`-level theorem witnessed in code, not a comment. Subordinate to `OPEN.md` §1
(the solved degree-1 shadow), exactly as Bridge O says.

### `guy-smith` — 1·e_g
**Octal periodicity certificates.** Implement the Guy–Smith periodicity theorem (if
the Grundy sequence of an octal game repeats with period `p` over a window long enough
relative to the largest take, it is periodic forever — Winning Ways; Siegel CGT) as a
checked certificate, turning `octal_hunt`-style sweeps into proofs-of-periodicity
rather than bounded observations. The *conjecture* that every finite octal game is
ultimately periodic is famous, external, and not ours to claim — the checker is.

### `loopy-partizan` — 3·e_g
**The partizan loopy engine** — `games/loopy.rs` explicitly defers: two-sided
Left/Right retrograde outcomes, unbounded sidling, the `±`/`tis`/`tisn` stopper
arithmetic, and onside/offside (`s & t`) values (Siegel CGT Ch. VI). Include the
Smith/Conway recovery-condition check that `loopy_nim_values` currently documents but
does not verify, so additivity-over-sums claims become checked instead of caveated.

### `game-clifford-checked` — 2·(e_g∧e_c)
**The checked deformation engine** OPEN §2 separates from its research claim: a
`GameClifford::with_quadratic_data` that accepts hand-supplied bilinear/quadratic
tables over a game subgroup and *verifies* quotient-compatibility (torsion relations
like `2* = 0` force the documented vanishings over torsion-free targets; torsion
targets may carry more). The engine ships; whether any such data is game-*native*
stays exactly where it is — `OPEN.md` §2.

## numbers — engine & bindings

### `spinor-gauge` — 2·e_c
**Spinor reps and reversal through the antisymmetric gauge.** `spinor_rep` and
`reverse()` reject general-bilinear (`a ≠ 0`) metrics; in char ≠ 2 the general engine
is gauge-equivalent to the orthogonal one (the antisymmetric part is a "gauge", the
symmetric part fixes the iso class). First pin the gauge isomorphism against the
shipped `reduce_word` oracle on this engine's conventions, then transport the spinor
construction and the reversal anti-automorphism through it. Char 2 keeps its own
boundary.

### `py-waves` — 1·e_y
**Python exposure for waves J/K/M/N/O.** Verified absent from `src/py/`: `lexicode`,
`brown_f2`/`brown_invariant`, `global_residues`, `transfer_diagonal`, `is_isomorphic`,
`NewtonPolygon`/`tropicalize`, `BrauerClass`/`cyclic_algebra_invariant`/
`constant_extension_invariants` — while waves A/E/H/I (theta, Weil, Construction A,
discriminant forms) are bound. Bind per the `catalog.rs` policy (these are
fixed-monomorph-friendly, mostly `i128`/`u128` payloads), and add the matching
`demo.py` rungs.

---

## switches (a9's move first)

### `surreal-completion` — ±2·e_s
**The ω-place completion of No** — a capped Hahn-window backend (`PrecisionScalar`
discipline, finite window of CNF terms) that finally represents `1/(ω+1)`, `√2`-as-
series, and divisible-Γ Newton polygons, completing the (exact global, capped local)
pattern every other leg has. The decision: whether No gets an inexact leg at all —
Surreal is currently the *exact* char-0 home, and the precedent (`Rational` as an
engine-validation scalar) cuts both ways. Divisible-Γ polygons are the research-edged
corner (CODA J: "definable but not claimed or scheduled").

### `theta-level` — ±3·e_i
**Level-`N` theta identification** — `θ_L ∈ M_{n/2}(Γ₀(N), χ)` for non-unimodular
even lattices. The decision: how much modular-forms machinery this crate wants to own
(dimension formulas, level-`N` Eisenstein bases, Sturm bounds) versus keeping the
full-level `SL₂(ℤ)` story as the deliberate boundary tied to `level()`. Worth a
design conversation before any code.

### `mass-32` — ±1·e_i
**Mass past rank 24.** `mass_even_unimodular` caps at 24 because the `i128` rational
model overflows. Serre's "more than 80 million classes" at rank 32 is one
factored-rational representation away — but the repo's fixed-width-carrier policy is
deliberate. Decision: admit a factored/big-rational carrier for this one corner, or
keep the cap as the honest model boundary.

---

## ups (infinitesimal, strictly positive)

### `ps-regularity` — ↑
Verify the regularity hypothesis of Plambeck–Siegel Thm 6.4 against the published
JCTA 2008 paper — load-bearing for goldarf Theorem C, flagged there as the cheap gate
(ranked move 5a). Literature work, no code.

### `octal-hunt-reframe` — ↑
`examples/octal_hunt.rs` hunts `(ℤ/2)^k` misère quotients with `k ≥ 2` — a target
goldarf Theorem C proves **empty** (group misère quotients have order ≤ 2). Retarget
the probe at non-group monoids / kernels where the quadric framing can still apply,
and have `p_set_as_f2` check its labeling is a monoid homomorphism.

### `docs-experiments` — ↑
Root `AGENTS.md` and `README.md` don't mention the `experiments/{gold,excess,audit}`
subdirectories (the rescued 2026-06-10 research-run probes backing `goldarf.tex`,
`excess.tex`, and `AUDIT.md`) or their not-CI-tested status. One layout-table line
plus a sentence each.

---

## stars (deferred — the not-yet-numbers, confused with zero)

## `*1` — spinor genus (was Bridge G)

Refine `genus → spinor genus → isometry class` via the spinor norm (Eichler;
Cassels–Hall). `clifford/spinor_norm.rs` is the right primitive in spirit, but the full
bridge is **not buildable from the current surface**: `spinor_norm` computes one versor's
norm, whereas the spinor genus needs the local spinor-norm *images* `θ(O(L ⊗ ℤ_p))` at
every prime, adelic class-group bookkeeping, and the proper/improper class distinction.

The one cheap, honest piece is **Eichler's theorem** as a documented predicate —
*indefinite, rank ≥ 3* ⇒ spinor genus = isometry class — which would let `Genus` upgrade
to a class statement in exactly that regime (now filed as the buildable `eichler` above).
The full definite-lattice computation is the larger build; it sits adjacent to the
roadmap, not inside it.

## `*2` — the char-`p` Drinfeld/Carlitz mirror of the integral pillar (large)

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

## `*4` — the wild local symbol (full local class field theory)

Bridge K's invariant is unramified-only; `tame-symbols` (above) would add the tame
slice. The remainder — norm-residue symbols for **wildly ramified** cyclic extensions
(degree divisible by the residue characteristic: Lubin–Tate formal groups, or Dwork's
explicit formula; the dyadic Hilbert symbol's big siblings) — is a genuine wing of
machinery over the capped local models, and the precision-model honesty questions are
real (wild symbols read deep unit structure, not just `v(a)`). Deferred, not rejected.
Nimbered `*4` rather than `*3`, since `*3 = *1 + *2` is already spoken for as the sum
of the other two stars.
