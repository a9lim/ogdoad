# Cross-pillar work — COMPLETENESS (completing what's there)

The ledger of buildable items that **complete a symmetry or connection already
present in the code**: the old bridges' deliberately-deferred lifts, the even↔odd
and exact↔capped mirrors a leg is still missing, verification harnesses, and elbow
grease. Genuinely new directions — features that extend ogdoad past what it covers
today — live in [`CONTINUATIONS.md`](CONTINUATIONS.md) (the grundy language work, the
char-`p` Drinfeld mirror). Newly completed work goes in the
[`DONE.md`](DONE.md) ledger. Nothing here is a genuine research question: solved
questions are indexed in [`CLOSED.md`](CLOSED.md), and unsolved questions live in
[`OPEN.md`](OPEN.md).

Claim-level discipline (`AGENTS.md` → "Claim levels and non-claims") applies to every
item: each is **standard math** or **engineering** when built — not a new theorem.

## How items are valued

(Canonical for both buildable ledgers — [`CONTINUATIONS.md`](CONTINUATIONS.md) values
its items the same way.) Natural numbers don't do ledger items justice, so the ledger
is a **game-valued multivector**: each item is a term `g·e_B` — a game value `g` (its
size and temper) on a pillar blade `e_B` (which pillars it joins; the blade's grade is
how cross-cutting the item is). Blades: `e_s` scalar, `e_c` clifford, `e_f` forms,
`e_i` integral, `e_g` games, `e_o` grundy, `e_y` py; pure-prose chores are
scalar-grade (no blade).

| value | temper | meaning |
|---|---|---|
| `n` (numbers) | cold | buildable now; `n` ≈ focused days; `½` ≈ an afternoon |
| `±n` (switches) | hot | a real scope decision belongs to a9 first; size `n` either way |
| `↑` (ups) | infinitesimal | worth less than any number, still strictly positive |
| `*n` (stars) | confused with `0` | deferred not-yet-numbers: real, on-thesis, unscheduled |

Reference items by **slug**. The ledger's total value is the disjunctive sum; play it
in any order. (`echo-solver`, the formerly hottest cold item, was played 2026-06-10
with outcome **CONFIRM** — see `writeups/goldarf.tex` §8; its former
σ-recasting successor was resolved by the later claim-lantern theorem.)

---

## numbers — forms & Witt (the classifier spine)

### 1·(e_c∧e_f∧e_s): `clifford-center`
**The center of the Clifford algebra as an actual object — the third Scalar–Clifford
span.** Materialize `Z(Cl(V,q))` / `Z(Cl⁰(V,q))` as the discriminant étale algebra
`F[x]/(x² − δ)` (parity-dependent), with split/field detection per scalar leg
(`Rational`, `Surreal`, odd finite fields, odd `F_q(t)`), cross-checked against the
Brauer–Wall dimension-parity and signed-discriminant coordinates the crate already
computes. Standard math (Lam; Knus–Merkurjev–Rost–Tignol). This is the span the
README's Königsberg section says is missing — Scalar and Clifford are the two odd
islands, and this bridge is what closes the crate's Euler tour. Distinct from
`brauer-algebras` (which materializes CSA representatives for Brauer *invariants*;
this materializes the scalar center the Clifford algebra itself generates).

### 1·(e_f∧e_s): `milnor-k`
**Mod-2 Milnor K-theory symbols behind the shipped `eₙ` staircase — degrees ≤ 2.**
`witt/ring.rs` names the `Iⁿ/Iⁿ⁺¹` staircase and computes `e₀/e₁/e₂`;
`witt/milnor.rs` ships the residue exact sequences. The missing sibling is the object
those invariants land in: symbols `{a₁,…,aₙ}` with the Steinberg relation, addition/
product, residue maps, and the classical comparison `k^M_n(F)/2 ≅ Iⁿ/Iⁿ⁺¹` verified
where it is classical — finite fields (trivial fast), ℚ (Tate), odd `F_q(t)` (Milnor)
— against the Pfister/eₙ and Hilbert/Springer surfaces already shipped. Bounded to
degrees ≤ 2 at this value; degree 3 (`e₃`, needing the full Merkurjev-level story)
would make it a `2` — don't scope-creep it. References: Milnor 1970; Gille–Szamuely.

### 1·(e_f∧e_s): `hermitian-restriction`
**Restriction of scalars for Hermitian forms — back into the trichotomy.**
`hermitian.rs` classifies Hermitian forms; `trace_form.rs` builds Scharlau transfers —
but the two never compose. Build `trace_metric`: send `h` over `E/F` to the `F`-valued
quadratic form `x ↦ Tr_{E/F}(h(x,x))`, then compare classifier outputs — Surcomplex
`U(p,q)` ↔ the real signature table, `FiniteHermitianInvariants` ↔ the odd/char-2
finite classifiers through the façade. (Two independent audit takes converged on
exactly this gap.) Standard math (Scharlau; Lam's transfer chapter). Not
`cm-lattices` — that is integral Hermitian lattice arithmetic; this is the field-level
forms bridge.

### 1·(e_f∧e_s): `springer-ramified`
**The ramified leg of the Springer engine.** `springer_decompose_local` requires only
`K::Residue: FiniteOddField`, and `Ramified<S,E>` satisfies it through its base
residue field — but no named wrapper or test exercises it, and the mathematics is not
a freebie: the value group is `(1/E)ℤ` relative to the base, so the valuation-parity
grading needs honest re-derivation (the ramified story is genuinely different from
the unramified one). A `springer_decompose_ramified` entry point with worked oracles
fills the one discretely-valued leg the trio skips. (`Gauss` is correctly excluded —
transcendental residue field.)

### ½·(e_s∧e_f): `finite-field-invariants`
**`level`/`pythagoras_number`/`u_invariant` for every shipped finite-field leg, not
just `Fp`.** `field_invariants.rs` is prime-fields-only and `u_invariant` hard-rejects
`P = 2` — but `u(F_q) = 2` for *every* finite field including characteristic 2
(Chevalley–Warning), the level of a char-2 field is trivially 1, and `Fpn<P,N>` is
first-class everywhere else in the classifier machinery. Generalize the three
invariants over `FiniteOddField`/`FiniteChar2Field` with formula-backed tests. (The
audit's original finding was the char-2 gap; the honest completion is all finite
legs.)

### ½·e_c: `char2-spinor-norm`
**The honest additive char-2 spinor norm.** The correctness audit
([`CORRECTNESS.md`](CORRECTNESS.md) → `spinor-norm-char2-claim`) established that
reducing the raw norm `∏q(vᵢ)` mod `℘` is *not* the char-2 invariant (it isn't
well-defined under versor rescaling). The completion is the real one: compute
`Σ Q(vᵢ) mod ℘(F)` from a factorization of the versor into vector symmetries (Wall/
Dye), pair it with the shipped Dickson parity, and test on nimber-backed versors —
finishing the char-2 half of `classify_versor` that the doc repair leaves honestly
open.

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
pass/pair axes remain unswept. The arbitrary-graph general-n linking proof remains
an optional research generalization, while the Gold problem itself is closed by
the proved Witt-matching route recorded in `DONE.md`.)

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

### 1·(e_i∧e_c∧e_f): `spine-closure`
**Wire the lattice→Clifford metrics into the classifiers — make the "visible meeting
point" claim a test.** `IntegralForm::clifford_metric` feeds only Pin-versor geometry
(never `.classify()`/`bw_class_rational`), and `clifford_metric_f2` has *no* Rust
consumer at all — so the mod-8 spine's lattice leg is asserted, not verified. Build
the closure: `E₈`/`D16+`/`Zⁿ` → `clifford_metric` → `classify_real`/
`bw_class_rational`, Bott index ↔ `signature() mod 8`; even 2-elementary lattice →
`clifford_metric_f2` → Arf → `4·Arf` ↔ `DiscriminantForm::brown_invariant` ↔ the
Milgram routes — extending `verify_milgram`'s three-way cross-check to the
Clifford/BW leg it never got. A convention drift in either endpoint currently cannot
fail a test; after this it can.

### 1·(e_c∧e_f∧e_i): `weil-coherence`
**One finite Weil representation, two shipped incarnations, never compared.** The
integral side has `DiscriminantForm`'s Weil `S`/`T` and metaplectic relation checks;
the char-2 side has the extraspecial Heisenberg/Pauli representation with projective
transvection intertwiners. Build the adapter from a nonsingular `F₂` quadratic form
to its 2-elementary discriminant module and assert the two packages agree
projectively on shared generators (Brown/Milgram phases, `S`/`T` vs the intertwiner
matrices). Only the cross-adapter and coherence checks are new — the transvection
work itself is DONE (`heisenberg-weil`). References: Scheithauer; Gurevich–Hadani.

### ½·(e_i∧e_f): `genus-hasse-crosscheck`
**Two complete local invariants of the same object, never run against each other.**
`genus.rs`'s Conway–Sloane symbols and `local_global/padic.rs`'s Hasse/Hilbert
invariant classify the same local data by genuinely different algorithms, each
oracled externally, with zero cross-references. Add agreement tests on shared Grams
(genus-implied local isotropy at odd `p` ↔ `try_is_isotropic_at_place` on the same
diagonal). A sign/normalization drift in either engine is currently invisible to
`cargo test`.

### ½·(e_i∧e_c): `eichler`
**Eichler's theorem as a documented predicate** — the one cheap honest piece of star
`*1`: *indefinite, rank ≥ 3 ⇒ spinor genus = isometry class*, letting `Genus` upgrade
to a class statement in exactly that regime. No adelic machinery; just the predicate,
its citation (Eichler; Cassels), and tests on indefinite Grams. The full definite
computation stays `*1`.

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

### 1·e_s: `laurent-galois`
**The Galois leg of the equal-characteristic local pair.** `(Qp, Qq)` carries
`FieldExtension`/`CyclicGaloisExtension` (Frobenius, relative trace/norm); `Laurent`
— the documented "char-p mirror of Qp" — has no unramified-extension twin at all,
and no boundary text excludes it the way Ramified ("non-Galois") and Gauss
("transcendental") are excluded. The extension is available by coefficient-field
substitution (`Laurent<Fpn<P,NF>>` over `Laurent<Fpn<P,N>>`, coefficientwise
Frobenius, valuation-preserving) — the const-generic plumbing (no `N·F` arithmetic
in stable generics, so concrete monomorphized impls) is what makes this a `1` rather
than a `½`. Feeds the same trace-form/cyclic-algebra consumers `Qq` already has.

### ½·e_s: `hyperfield`
**Viro's tropical hyperfield**, making Bridge J's lax tropicalization strict (the
`Valued` trait doc names this exact repair — `valued.rs`, the "strictness is restored
only by the tropical hyperfield [Viro 2010]" sentence beside Lemma J.1): a small
multivalued-addition type
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

### ±3·e_i: `general-mass`
**The Smith–Minkowski–Siegel mass formula for arbitrary genera.** `mass_even_unimodular`
is the clean closed Bernoulli case; the general formula (odd, non-unimodular, any
genus) needs local densities at every prime — real machinery, and it is what would let
`KneserMassInvariants` close masses outside the even-unimodular world (the neighbor
*constructor* is already general; only the mass-closure reporting is capped by the
formula's scope). The decision is how much local-density machinery the crate wants to
own — same conversation as `theta-level`, one shelf over. Conway–Sloane SPLAG ch. 15;
Kitaoka.

### ±2·e_i: `kneser-24`
**Explicit rank-24 genus representatives by neighbor walk.** `kneser-neighbors` (DONE)
deliberately stopped at rank 16; the 23 rooted Niemeier classes still have no shipped
Gram matrices (the catalogue is root/glue/Aut data plus the explicit Leech). Walking
the rank-24 `p`-neighbor graph from Leech until all 24 classes are hit — with the
catalogue as the identification oracle — would upgrade the catalogue-backed boundary
to constructed witnesses. Scope call first: the walk plus per-class identification is
genuinely bigger than the rank-16 version (hence a switch, not a number), and it
half-overlaps what a definite-lattice `*1` spinor-genus build would need anyway.

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
filled," but each functor is generic over its input and two of the three named
*compositions* are untested: `Surcomplex<Qp>` should be `Q_p(i)` (the unramified
quadratic extension for `p ≡ 3 mod 4`, split for `p ≡ 1`) and `Ramified<Qq>` a
ramified-over-unramified local field. A handful of tests pinning that stacked functors
realize the expected `(K, 𝒪, 𝔪, k, Γ, ϖ)` package — no new types. (Narrowed
2026-07-02: the `Gauss<Laurent>` corner is already tested —
`composes_over_a_laurent_base`, `gauss.rs` — and `Surcomplex<Nimber>` is a
mathematically degenerate cell (`i² = 1`), so the sweep should skip it as n.a., not
test it as a field.)

### ↑: `octal-hunt-reframe`
`examples/octal_hunt.rs` hunts `(ℤ/2)^k` misère quotients with `k ≥ 2` — a target
goldarf Theorem C proves **empty** (group misère quotients have order ≤ 2). Retarget
the probe at non-group monoids / kernels where the quadric framing can still apply,
and have `p_set_as_f2` check its labeling is a monoid homomorphism.

### ↑·(e_s∧e_f∧e_i∧e_g): `verification-roster`
Small missing cells and agreement harnesses from the 2026-07-02 audit, grouped (the
*oracle-for-shipped-claims* siblings live in [`CORRECTNESS.md`](CORRECTNESS.md); these
are missing legs, not unpinned claims): `NewtonPolygon` over `Qq` (compiles against
the `Valued` bound today, zero tests — the unramified-extension polygon is textbook);
`Ordinal::nim_sqrt` (Frobenius inverse inside the verified Kummer window — `Nimber`
has it, `Ordinal` doesn't, and no boundary text says why); the `gold_form` ↔
`trace_form_arf` agreement test at their one overlap point (`m = 2` — both are only
pinned to the external rank formula, never to each other); the trace–Frobenius square
(build `σ^a` once, assert the polar matrix of `Tr(x·σ^a x)` matches the
Clifford/Frobenius linear map's, and `trace_form_arf` ↔ `gold_form` ↔ zero-count —
"same data, two machines" made executable); add `Omnific`/`Fpn`/`Zp`/`WittVec`/`Poly`
to the `scalar_axioms.rs` proptest roster (all `ExactScalar`-marked, none fuzzed —
the root AGENTS "every backend" claim currently overstates); either impl
`ClassifyWitt` for `RationalFunction` via the shipped `global_residues_ff` or
document the boundary the way Rational/Surcomplex's is documented (currently
`RationalFunction` silently lacks even `ClassifyForm`); an explicit
`lexicode(24,8) ≅ golay_code()` equivalence certificate (the permutation, not just
the uniqueness-theorem citation), making Bridge O's endpoint inspectable.

### ↑: `docs-experiments`
Root `AGENTS.md` and `README.md` don't mention the `experiments/{gold,excess,audit}`
subdirectories (the rescued 2026-06-10 research-run probes backing `goldarf.tex`,
`excess.tex`, and the 2026-06-10 correctness sweep) or their not-CI-tested status. One
layout-table line plus a sentence each.

### ↑: `res-cores`
Restriction/corestriction (transfer) functoriality for the invariant groups under
`E/F`: `res` is base change (`Metric::map` / scalar extension), `cores` is the
**Scharlau transfer** already shipped (`trace_form::transfer_diagonal` — unlettered;
it sits beside Bridge N.1 in the fourth-wave joins). State and test the
standard relations across the Witt, Brauer–Wall, and Clifford-invariant surfaces —
the projection formula `cores(res(x)·y) = x·cores(y)`, `cores∘res = ·[E:F]`, and
naturality of `c(q)` / `bw_class` / the Milnor residue under both. Mostly a
coherence layer over existing maps; literature + tests, little new code.

---

## stars (deferred — the not-yet-numbers, confused with zero)

The star numbers are one shared nim-sum scheme across both buildable ledgers; the
sibling stars `*2` (Drinfeld) and `*8` (ogham 0.3.0) live in
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
