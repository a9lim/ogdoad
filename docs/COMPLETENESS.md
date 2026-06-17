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
σ-recasting target in `OPEN.md` tis (§1), which is loopy-valued, not a number.)

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
`OPEN.md` tis (§1), not a number here.)

### 1·(e_f∧e_s): `hermitian-finite`
**Hermitian forms over the finite legs** — the involution sibling the classifier is
missing. `forms/hermitian.rs` classifies Hermitian forms only over `Surcomplex`
(signature, via the `conj()` involution); the same theory over a degree-2
`CyclicGaloisExtension` `F_{q²}/F_q` (involution = the relative Frobenius `σ`, already
shipped for `Fpn` and the `Nimber` subfields) is **rank-complete** — every nondegenerate
Hermitian form of a given rank is equivalent, because the norm `N: F_{q²}* → F_q*` is
onto, so the discriminant in `F_q*/N` is trivial. A classifier generic over
`CyclicGaloisExtension`-of-degree-2 mirrors the quadratic-form trichotomy's char-0↔finite
span onto the "form + involution" siblings (`forms/AGENTS.md` → "form + involution"), with
`U(n, F_{q²}/F_q)` as the matching complete-invariant group. The char-2 finite case
(`Fpn<2,2k>/Fpn<2,k>`, `Nimber` subfields) falls out of the **same** rank statement, so
one build spans the odd and char-2 finite legs at once. Standard math (Grove, *Classical
Groups and Geometric Algebra*).

## numbers — the integral wing

### ½·(e_i∧e_c): `eichler`
**Eichler's theorem as a documented predicate** — the one cheap honest piece of star
`*1`: *indefinite, rank ≥ 3 ⇒ spinor genus = isometry class*, letting `Genus` upgrade
to a class statement in exactly that regime. No adelic machinery; just the predicate,
its citation (Eichler; Cassels), and tests on indefinite Grams. The full definite
computation stays `*1`.

### 2·(e_i∧e_s): `construction-a-p`
**Construction A over odd `F_p`** — Bridge H is binary-only; the `p`-ary completion is the
same code↔lattice seam over the shipped `Fp` backend (`A_p(C) = {x ∈ ℤⁿ : x mod p ∈ C}`,
inner products scaled by `p`), with the matching `p`-ary / complete-weight-enumerator
MacWilliams identity beside the binary one in `codes.rs`. The headline oracle is the
**ternary Golay** `[12,6,6]` → the **Coxeter–Todd lattice K₁₂** (the `F_3` analogue of
binary-Golay→half-Leech), a rank-12 even lattice with its catalogued
det/minimum/kissing/|Aut| — the first time the integral wing exercises an odd prime, and
the natural rung between `construction_a` and the deferred CM-lattice wing (`cm-lattices`,
`CONTINUATIONS.md`). Standard math (Conway–Sloane SPLAG ch. 7); the theta side stays the
existing even-`ℂ[E4,E6]` boundary, since a ternary-Construction-A theta is a level-3 form
(deferred with `theta-level`).

### ½·e_i: `reed-muller`
**Reed–Muller codes + `BW₁₆` via the shipped Construction D** — the Construction-D surface
currently ships only the toy `0 ≤ H_8` two-level tower; the Reed–Muller chain
`RM(0,m) ⊂ RM(1,m) ⊂ … ⊂ RM(m,m)` is the classical nested family Construction D was built
for, and `RM(1,4) ⊂ RM(2,4)` gives the **Barnes–Wall lattice `BW₁₆`** with its catalogued
det/minimum/kissing. A small, pure-`integral/` completion that turns the demo into a named
lattice — and supplies the code-side route into the `clifford-lattices` bridge
(`CONTINUATIONS.md`), where `BW₁₆` reappears as a Clifford-group invariant.

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
