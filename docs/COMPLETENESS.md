# Cross-pillar work — COMPLETENESS (completing what's there)

The ledger of buildable items that **complete a symmetry or connection already
present in the code**: the old bridges' deliberately-deferred lifts, the even↔odd
and exact↔capped mirrors a leg is still missing, verification harnesses, and elbow
grease. Genuinely new directions — features that extend ogdoad past what it covers
today — live in [`CONTINUATIONS.md`](CONTINUATIONS.md) (the ogham language work, the
char-`p` Drinfeld mirror). Newly completed work goes in the
[`DONE.md`](DONE.md) ledger. Nothing here is a genuine research question — those
live in [`OPEN.md`](OPEN.md) (which carries the loopy-valued entries; open problems
give no termination guarantee).

Claim-level discipline (`AGENTS.md` → "Claim levels and non-claims") applies to every
item: each is **standard math** or **engineering** when built — not a new theorem.

## How items are valued

(Canonical for both buildable ledgers — [`CONTINUATIONS.md`](CONTINUATIONS.md) values
its items the same way.) Natural numbers don't do ledger items justice, so the ledger
is a **game-valued multivector**: each item is a term `g·e_B` — a game value `g` (its
size and temper) on a pillar blade `e_B` (which pillars it joins; the blade's grade is
how cross-cutting the item is). Blades: `e_s` scalar, `e_c` clifford, `e_f` forms,
`e_i` integral, `e_g` games, `e_o` ogham, `e_y` py; pure-prose chores are
scalar-grade (no blade).

| value | temper | meaning |
|---|---|---|
| `n` (numbers) | cold | buildable now; `n` ≈ focused days; `½` ≈ an afternoon |
| `±n` (switches) | hot | a real scope decision belongs to a9 first; size `n` either way |
| `↑` (ups) | infinitesimal | worth less than any number, still strictly positive |
| `*n` (stars) | confused with `0` | deferred not-yet-numbers: real, on-thesis, unscheduled |

Reference items by **slug**. The ledger's total value is the disjunctive sum; play it
in any order. (`echo-solver`, the formerly hottest cold item, was played 2026-06-10
with outcome **CONFIRM** — see `writeups/goldarf.tex` §8; its successor move is the
σ-recasting target in `OPEN.md` tis, which is loopy-valued, not a number.)

---

## numbers — forms & Witt (the classifier spine)

### 1·(e_g∧e_f): `echo-family-sweep`
**The remaining pre-registered family axes** (`writeups/goldarf.tex` §§8–9, ranked
move 2), on the shipped harness `experiments/echo_solver.py`: ko-memory window
`w ∈ {1,2,3}`, pass semantics (clears-ko / forbidden / loses), single-coin plus pair
touches (the tartan-companion axis), and no-dummy controls — mapping which disciplines
besides fifo+dummy are exact. No longer decisive for existence (the fifo+dummy verdict
is in); it bounds the *mechanism* and finally puts the bounded-window blocker
conjecture on valid data. (Partially advanced by the 2026-06-10 `linking-reduction`
pass: the no-dummy controls are fully mapped at the abstract-graph
level — the Bad census — and the fifo+dummy mechanism is identified
(`experiments/linking_game.py`, goldarf §8 `sec:linking`); the `w ≥ 2` ko-window and
pass/pair axes remain unswept, and the general-n linking *proof* is loopy-valued in
`OPEN.md` tis, not a number here.)

### 1·(e_s∧e_f): `brauer-algebras`
**Explicit algebra representatives for the Brauer invariants.** Bridges F/K
compute Brauer *invariants* — `Brauer2Class` (a ramified-place set), `BrauerClass`
(`ℚ/ℤ` local invariants), `cyclic_algebra_invariant` — and `Brauer2Class::quaternion()`
already names the `½`-slice's quaternion. The completion is to materialize the
**actual central simple algebra** behind a general class: the cyclic algebra
`(E/F, σ, a)` for the unramified/tame data, with checked `split` / `tensor` (class
addition = algebra ⊗) and `localization` (the local invariant = the algebra's
Hasse invariant at each place) round-trips against the invariant surface. Turns
"this class is `1/3` at `v`" into "this is *this* degree-3 cyclic algebra, and here
is why." The trace-form half is already built (`cyclic_algebra_trace_form` over
exactly these `(E/F,σ,a)`). Standard math (Brauer group / cyclic algebras);
completes Bridge K from invariants to algebras.

## numbers — the integral wing

### ½·(e_i∧e_c): `eichler`
**Eichler's theorem as a documented predicate** — the one cheap honest piece of star
`*1`: *indefinite, rank ≥ 3 ⇒ spinor genus = isometry class*, letting `Genus` upgrade
to a class statement in exactly that regime. No adelic machinery; just the predicate,
its citation (Eichler; Cassels), and tests on indefinite Grams. The full definite
computation stays `*1`.

### 2·e_i: `kneser-neighbors`
**Genus enumeration by `p`-neighbors, with mass as the stopping certificate.** The
genus surface today can *compare* (`Genus::of` / `are_in_same_genus`), *weigh*
(`mass_even_unimodular`), and *decide existence* (`nikulin_even_lattice_exists`) —
but it cannot *list* the isometry classes in a genus. Kneser's `p`-neighbor method
is the standard closure: from one lattice, form its `p`-neighbors (re-glue along an
isotropic line mod `p`), dedup by `IntegralForm` isometry, and walk the neighbor
graph until `Σ 1/|Aut| = mass` — the **already-shipped mass *is* the completeness
certificate**. This makes the rank-8/16/24 even-unimodular genera (1, 2, 24 classes,
all already mass-anchored) enumerable end-to-end, turning the Niemeier catalogue
from a curated table into a *generated-and-mass-closed* list. A second I–I loop
joining E/H/N.3/N.4. **Modular deepening (Codex):** the neighbor adjacency matrix is
the genus's **Brandt/Hecke operator** on the span of the class theta series;
checking that the mass-weighted theta average is its Eisenstein eigenvector — and
that the spectrum is Hecke eigenvalues — turns enumeration into another route into
`ℂ[E₄,E₆]` (Bridges E/H). Boundary: `|Aut|` past the node budget returns `None`, so
the certificate closes cleanly only where `automorphism_group_order` does (≤ rank
24). Standard math (Kneser; Conway–Sloane SPLAG ch. 15; Eichler/Brandt).

### 1·(e_c∧e_i): `weyl-versors`
**ADE roots as Clifford versors; the Weyl group inside Pin.** `root_lattices.rs`
carries the ADE roots and `clifford/versor.rs` carries `reflect` / `sandwich` /
`versor_inverse`, but nothing connects them. Each root `α` is a grade-1 vector whose
Clifford reflection `−α x α⁻¹` is the simple reflection `s_α`, so the **Weyl group
`W(R)` is the versor (Pin) subgroup generated by the root vectors**, and `|W(R)|`
(already tabled — `E8_WEYL_GROUP_ORDER`, the `A_n`/`D_n` formulas) is that versor
group's order. Build the Pin-image of `W(R)` from the root vectors; check it against
the tabled Weyl orders and against `outermorphism` determinants (reflections have
det `−1`); recover the Coxeter element as the product of all simple-root versors
(its order = the already-computed Coxeter number). Draws the
roots↔reflections↔versors triangle the two pillars currently only half-draw —
a C–I *reflection* span beside the `clifford-lattices` C–I span. Standard math
(Clifford/Pin realization of Weyl groups; Dechant's `E₈` construction).

### ½·e_i: `pary-theta`
**The odd-prime leg of MacWilliams↔theta (Bridge H).** `construction-a-p` (DONE)
shipped `PrimeCode<P>` → Construction-A lattices and the q-ary Hamming MacWilliams
transform, but `theta_series_via_weight_enumerator` is binary-doubly-even only — the
code→theta half of Bridge H has no odd-prime mirror. The Broué–Enguehard / Hecke
`p`-ary theta map sends a `p`-ary code's (complete or symmetrized) weight enumerator
to its Construction-A lattice theta series, the exact odd analogue of the binary
transformation already pinned for `E₈`/Golay; it would pin the ternary-Golay
rank-12 lattice's theta against its weight enumerator. Standard math (Broué–Enguehard;
SPLAG ch. 7). Closes Bridge H over the leg `construction-a-p` opened.

## numbers — scalar worlds

### ½·e_s: `hyperfield`
**Viro's tropical hyperfield**, making Bridge J's lax tropicalization strict (Remark
J.2 names this exact repair): a small multivalued-addition type
(`x ⊞ y = {min}` off the vanishing locus, the interval/set on it) with the hyperfield
laws as tests and `tropicalize` factoring through it. A leaf, but it converts the one
"lax" asterisk in the J appendix into a theorem about a shipped type.

## numbers — games

### 1·e_g: `guy-smith`
**Octal periodicity certificates.** Implement the Guy–Smith periodicity theorem (if
the Grundy sequence of an octal game repeats with period `p` over a window long enough
relative to the largest take, it is periodic forever — Winning Ways; Siegel CGT) as a
checked certificate, turning `octal_hunt`-style sweeps into proofs-of-periodicity
rather than bounded observations. The *conjecture* that every finite octal game is
ultimately periodic is famous, external, and not ours to claim — the checker is.

### 1·e_g: `overheating`
**Cooling's named inverse: heating, overheating `∫`, and Norton multiplication.**
`thermography.rs` ships cooling (the tropical `⊗`), stops, temperature, and mean —
but the inverse transforms are absent. Heating and **overheating** `∫_s^t G` (the
formal inverse of cooling that recovers a hot game from its cooled form) and
**Norton multiplication** `G.U` (overheating against a unit game `U`) are standard
CGT operators on the existing `Pl` piecewise-linear machinery; the cooling↔heating
round-trip and `mean(G.U) = mean(G)·mean(U)` are the oracles. Completes the
temperature surface (cooling ↔ its inverse). **Boundary (flagged independently by
Codex):** build these as Games infrastructure *only* — the claim that
Norton/overheating gives cooling an associated-graded *product* (a homomorphism
`gr_t`) is exactly the `under` open problem (`OPEN.md`) and stays research. This is
to `under` what `lexicode-game` is to `tis`: the executable tool the open question
needs, not progress on it. Standard math (Conway ONAG; Siegel CGT ch. on temperature).

---

## switches (a9's move first)

### ±2·e_s: `surreal-completion`
**The ω-place completion of No** — a capped Hahn-window backend (`PrecisionScalar`
discipline, finite window of CNF terms) that finally represents `1/(ω+1)`, `√2`-as-
series, and divisible-Γ Newton polygons, completing the (exact global, capped local)
pattern every other leg has. The decision: whether No gets an inexact leg at all —
Surreal is currently the *exact* char-0 home, and the precedent (`Rational` as an
engine-validation scalar) cuts both ways. Divisible-Γ polygons are the research-edged
corner — definable but not claimed or scheduled.

### ±3·e_i: `theta-level`
**Level-`N` theta identification** — `θ_L ∈ M_{n/2}(Γ₀(N), χ)` for non-unimodular
even lattices. The decision: how much modular-forms machinery this crate wants to own
(dimension formulas, level-`N` Eisenstein bases, Sturm bounds) versus keeping the
full-level `SL₂(ℤ)` story as the deliberate boundary tied to `level()`. Worth a
design conversation before any code.

### ±1·e_i: `mass-32`
**Mass past rank 24.** `mass_even_unimodular` caps at 24 because the `i128` rational
model overflows. Serre's "more than 80 million classes" at rank 32 is one
factored-rational representation away — but the repo's fixed-width-carrier policy is
deliberate. Decision: admit a factored/big-rational carrier for this one corner, or
keep the cap as the honest model boundary.

---

### ±2·e_f: `dyadic-springer`
**The local Witt/Springer decomposition at the dyadic place `Q₂`** — the one place
the local story skips. The generic Springer engine (`springer/local.rs`) and every
named leg (`Q_p`, `Q_q`, `Laurent`) are **odd-residue-char only**, and `milnor.rs`
reaches `p = 2` only through Milnor's hand-built global boundary, never a standalone
local object. The mixed-characteristic dyadic cell — `W(Q₂)` via the 2-adic Jordan
splitting, the mod-8 ε/ω Hilbert data already in `local_global/padic.rs`, and the
2-adic square-class structure — is the missing mirror of the char-2 equal-char work
(`springer/char2/`, the Aravire–Jacob `(φ₀,ψ,φ₁)` engine that residue char 2 *did*
get). The decision is a9's: does the local Springer surface want its hardest cell —
genuinely fiddly 2-adic quadratic-form theory — given that `genus.rs` already carries
the `p = 2` Jordan/oddity calculus internally and `milnor.rs` covers the global map?
Worth a design read before code: how much of the 2-adic structure becomes a clean
`LocalSpringerDecomp`-shaped object versus staying inside the genus/Milnor machinery.

## ups (infinitesimal, strictly positive)

### ↑: `ps-regularity`
Verify the regularity hypothesis of Plambeck–Siegel Thm 6.4 against the published
JCTA 2008 paper — load-bearing for goldarf Theorem C, flagged there as the cheap gate
(ranked move 5a). Literature work, no code.

### ↑: `functor-compose`
The 2×2 functor table (`Surcomplex`/`Ramified`/`Gauss`/`Laurent`) is "all four corners
filled," but each functor is generic over its input and the *compositions* are untested:
`Surcomplex<Qp>` should be `Q_p(i)` (the unramified quadratic extension for `p ≡ 3 mod 4`,
split for `p ≡ 1`), `Ramified<Qq>` a ramified-over-unramified local field, `Gauss<Laurent>`
a two-step valuation. A handful of tests pinning that stacked functors realize the expected
`(K, 𝒪, 𝔪, k, Γ, ϖ)` package — no new types, just confirming the corners compose the way
the place table claims they do.

### ↑: `octal-hunt-reframe`
`examples/octal_hunt.rs` hunts `(ℤ/2)^k` misère quotients with `k ≥ 2` — a target
goldarf Theorem C proves **empty** (group misère quotients have order ≤ 2). Retarget
the probe at non-group monoids / kernels where the quadric framing can still apply,
and have `p_set_as_f2` check its labeling is a monoid homomorphism.

### ↑: `docs-experiments`
Root `AGENTS.md` and `README.md` don't mention the `experiments/{gold,excess,audit}`
subdirectories (the rescued 2026-06-10 research-run probes backing `goldarf.tex`,
`excess.tex`, and the 2026-06-10 correctness sweep) or their not-CI-tested status. One
layout-table line plus a sentence each.

### ↑: `res-cores`
Restriction/corestriction (transfer) functoriality for the invariant groups under
`E/F`: `res` is base change (`Metric::map` / scalar extension), `cores` is the
**Scharlau transfer** already shipped (`transfer_diagonal`, N.2). State and test the
standard relations across the Witt, Brauer–Wall, and Clifford-invariant surfaces —
the projection formula `cores(res(x)·y) = x·cores(y)`, `cores∘res = ·[E:F]`, and
naturality of `c(q)` / `bw_class` / the Milnor residue under both. Mostly a
coherence layer over existing maps; literature + tests, little new code.

---

## stars (deferred — the not-yet-numbers, confused with zero)

The star numbers are one shared nim-sum scheme across both buildable ledgers; the
sibling stars `*2` (Drinfeld) and `*8` (ogham 3.0) live in
[`CONTINUATIONS.md`](CONTINUATIONS.md).

### *1: `spinor genus` (was Bridge G)

Refine `genus → spinor genus → isometry class` via the spinor norm (Eichler;
Cassels–Hall). `clifford/spinor_norm.rs` is the right primitive in spirit, but the full
bridge is **not buildable from the current surface**: `spinor_norm` computes one versor's
norm, whereas the spinor genus needs the local spinor-norm *images* `θ(O(L ⊗ ℤ_p))` at
every prime, adelic class-group bookkeeping, and the proper/improper class distinction.

The one cheap, honest piece is **Eichler's theorem** as a documented predicate —
*indefinite, rank ≥ 3* ⇒ spinor genus = isometry class — which would let `Genus` upgrade
to a class statement in exactly that regime (now filed as the buildable `eichler` above).
The full definite-lattice computation is the larger build; it sits adjacent to the
ledger, not inside it.

### *4: `the wild local symbol` (full local class field theory)

Bridge K's invariant now carries the unramified and tame Kummer slices. The remainder
— norm-residue symbols for **wildly ramified** cyclic extensions
(degree divisible by the residue characteristic: Lubin–Tate formal groups, or Dwork's
explicit formula; the dyadic Hilbert symbol's big siblings) — is a genuine wing of
machinery over the capped local models, and the precision-model honesty questions are
real (wild symbols read deep unit structure, not just `v(a)`). Deferred, not rejected.
Nimbered `*4` rather than `*3`, since `*3 = *1 + *2` is already spoken for as the sum
of the other two stars.
