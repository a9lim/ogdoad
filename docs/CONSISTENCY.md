# CONSISTENCY.md (the aesthetic ledger)

The aesthetic ledger: a structural/stylistic read of the core, valued like
[`COMPLETENESS.md`](COMPLETENESS.md) — a game value `g` on a pillar blade `e_B` (`e_s` scalar,
`e_c` clifford, `e_f` forms, `e_i` integral, `e_g` games, `e_o` ogham, `e_y` py). Claim
level **interpretation**: one reviewer's eye, but every item is checked against
the actual source, not vibes. Numbers ≈ focused days; `±n` flags an a9 scope
call (API-churn, mostly); `↑` is worth less than any number but strictly
positive; `*n` is real, on-thesis, unscheduled. Its soundness sibling — claims that
are machine-verified vs source-pinned vs merely asserted, not taste — is
[`CORRECTNESS.md`](CORRECTNESS.md).

---

## Status — audited 2026-07-02 (Rust core only; py/ and ogham/ out of scope)

Second full-tree taste pass. The tree is byte-identical to the played 2026-06-20 sweep
(`be5f4a4`), so this audit hunted three things: what the last audit's altitude missed
(it read the newest wing hard and everything else lightly), what the sweep's own plays
introduced, and the pillars nobody had taste-read closely (the scalar core, the engine
internals, games, big scalars). Every sweep play was spot-verified against source
before anything below was written — **the sweep held**: gcd/is_prime/mex/blade-mask
consolidations, the glossary fold, the place-type merge, games `Display`, Niemeier
partiality — all intact, none re-flagged. `precision-K` stays consciously deferred (its
standing note is preserved in the `consistency-sweep` DONE entry and git history).

The recurring shape this time is one octave below last audit's. That one found "the new
wing didn't reach back for the substrate floor." This one finds **the floor itself is
missing tiles**: a handful of primitives that should *be* substrate (scalar `pow`,
prime factorization, checked rational arithmetic, p-adic valuation helpers) never got a
home, so every pillar quietly rolled its own — the same disease, but the cure is
building the missing floor rather than pointing at an existing one. Everything else is
edge-drift: partiality and encapsulation outliers against strong local norms, and two
sweep-pattern stragglers the last pass didn't reach.

---

## What still holds (0 — listed so a cleanup pass doesn't destroy it)

- **The sweep's consolidations are all load-bearing and un-drifted** (verified by
  grep, not trust): one gcd, one `is_prime_u128`, one `mex`, one grade-k mask
  enumerator, `hermitian.rs` delegating to `unit_pivot_nullspace`.
- **Partiality discipline is the crate norm, not the exception.** The ~150
  domain-limited functions across `witt/`/`local_global/`/`springer/` thread `Option`
  scrupulously; `big/`'s `nim_mul`/`nim_pow`/`checked_inv`/`as_ordinal` all sit on
  honest `None` boundaries; the budget-`None` discipline (`AUTO_NODE_BUDGET`,
  `FQM_WITT_*_CAP`, `ISO_*`, lexicode budgets) is uniform and documented. The
  `partiality-outliers` roster below is short *because* the norm is strong.
- **Encapsulation is the norm too**: the games pillar is fully accessored
  (`Game`/`GameExterior`/`LexicodeTurningGame`/loopy graphs), `IntegralForm`/`Metric`/
  `Multivector`/`Surreal`/`Ordinal` all guard their invariants. The stragglers below
  are the residue, not the rule.
- **`GlobalField` is the best abstraction in the crate** — five primitives + four
  default theorem methods written once over ℚ and `F_q(t)`, tested by one generic body
  instantiated at both. The springer shelf's "one generic engine + one documented
  odd-one-out" and `cnf::merge_descending`'s share-the-shape-not-the-algebra design
  are the same idea executed at trait, module, and function scale. This is the house
  style at its best; new bridges should copy it.
- The triple Arf implementation (`arf_f2`/`arf_nimber_at_degree`/`arf_char2_core`) is
  deliberate cross-checked redundancy, not duplication — don't "simplify" it.

---

## numbers — buildable now

### 1·(e_s∧e_f): `pow-times-eight`
**Square-and-multiply is hand-rolled eight times against an operator that already
exists.** `impl_scalar_ops!` generates `^ u128` (square-and-multiply via `Scalar::mul`)
for every total-product backend — yet the crate carries eight private copies of the
same loop: `Fp::pow` (`fp.rs:143`), `Fpn`'s `FiniteField::pow` (`fpn.rs:500`),
`WittVec::pow` (`wittvec.rs:126`), `spow` (`small/analytic.rs:44`), `residue_pow` +
its signed wrapper (`witt/cyclic.rs:103,117`), `finite_pow`
(`local_global/function_field.rs:411`), `s_pow` (`springer/char2/asnf.rs:15`), and the
`oddchar/field.rs` copy — the last four in *generic* code that can't reach the
concrete-type operator, which is exactly why the fix is a **default `Scalar::pow`**
(square-and-multiply over `mul`/`one`, mirroring `from_int`'s default-method
precedent), with `impl_scalar_ops!`'s `BitXor` delegating to it and all eight sites
deleted or delegated. Cherry on top: `fq_sqrt` (`analytic.rs:206-219`) is written
*concretely* over `Fpn<P,N>` and still calls the duplicate `.pow()` four times where
the `^` operator is in scope. This is this audit's `gcd`-times-eight.

### 1·(e_i∧e_f∧e_s): `helper-commons`
**The p-adic/rational helper floor was never built, so the integral wing triplicated
it.** The roster, verified byte-similar (in some copies even the return *width*
drifts):
- **The valuation quartet ×3**: `v_p_i128`/`unit_part_i128`/`rat_val`/`unit_mod8`
  copy-pasted across `genus.rs:73-116`, `fqm_witt.rs:964-997`,
  `discriminant/form.rs:109-134` (genus's `v_p` returns `u128`, the others `i128`),
  plus the same quadratic-residue wrapper under two names (`unit_sign_odd` vs
  `odd_unit_residue`).
- **`rational_mod_int` ×2** (`discriminant/form.rs:18` / `fqm_witt.rs:934`, identical
  to the panic message); **`rdiv` ×2** (`diagonal.rs:13` / `genus.rs:136`).
- **Trial-division prime factorization ×5**: `genus::relevant_primes`,
  `fqm_witt::prime_factors_u128`, `discriminant::prime_factors_i128`,
  `ordinal/subfield::prime_factors`, `tower::smallest_prime_factor` (and `fpn.rs`'s
  `distinct_primes` makes six) — no shared primitive despite `linalg::integer` being
  the crate's stated home for exactly this kind of thing.
- **`base_digits`/`checked_pow` ×2** in the *same module* (`ordinal/tower.rs:246-262`
  vs `ordinal/subfield.rs:92-107` — and `subfield.rs` already imports `pub(super)`
  items from `tower.rs`, so there is no visibility excuse).
- **`binomial` ×3 in one file** (`codes.rs:180,195,603` — panic / `Option`-usize /
  `Option`-i128 variants of the same recurrence).
Fix shape: the quartet + `rdiv` + `rational_mod_int` into `diagonal.rs` (already the
declared shared home both `genus.rs` and `discriminant/` import);
`linalg::integer::prime_factors` beside `gcd`/`ext_gcd`; one `binomial_checked` with
thin wrappers; `tower.rs` exports its pair `pub(super)`. Mostly deletion.

### ½·e_s: `rational-checked-ops`
**`Rational` should own its checked arithmetic.** `surreal/analytic.rs:161-194`
re-derives `Rational`'s exact cross-gcd-reduction `mul`/`add` privately with `?` in
place of `.expect()` — and the `mass_formula.rs`/`kneser.rs` raw-`(i128,i128)`
fraction kits exist for the same reason (they need an `Option` overflow boundary the
`Scalar` impl doesn't offer, and `kneser::add_frac` is `mass_formula::checked_rat_add`
under another name). Give `Rational` `checked_add`/`checked_mul` (the `Scalar` impls
become thin `.expect()` wrappers), delete the analytic.rs re-derivation, and let the
two integral-wing kits collapse to calls.

### 1·(e_f∧e_g∧e_i∧e_s): `partiality-outliers`
**Seven panics against the house `Option` rule, each verified against a sibling that
does it right.** Worst first:
- `isotropy_over_adeles` (`adelic.rs:81-86`) `assert!`s rank ≥ 3 — *in a function
  already returning `Option`*, in a file where every other exit is `None`-threaded.
- `misere_quotient`/`octal_misere_quotient` (`misere.rs:399,470`) `.expect()` on the
  module's own documented-partial primitives; the module even has a dedicated
  `cyclic_abstract_game_returns_none_not_panic` test — but a cyclic `AbstractGame`
  through the *quotient builders* panics. Return `Option<Quotient>`.
- `root_lattices::a_n`/`d_n` (`:60-79`) assert on out-of-domain rank while
  `niemeier.rs` documents (and implements) the opposite contract for the *same shape
  of input* one file over.
- `BinaryCode::codewords`/`PrimeCode::codewords` (`codes.rs:332,669`) assert/expect
  where the whole wing otherwise uses budget-`None` (`AUTO_NODE_BUDGET`, the fqm/iso
  caps).
- `fit_f2_quadratic` (`quadric_fit.rs:49-60`) panics on a point outside `F_2^k`
  despite returning `Option` (keep the `MAX_ANF_DIM` capacity assert — that one is
  house-legal).
- `Surreal::from_ordinal` (`sign_expansion.rs:97`) `.expect()`s on coefficient
  overflow — the *inverse* of `as_ordinal`, which returns `Option`; reachable from
  Python (`py/scalars.rs:4513`), so the panic crosses the FFI boundary.
- `classify_real`/`classify_complex` (`char0.rs:191-225`) are unbounded `pub fn`s
  whose `p2()` panics past dimension 127 with an incidental overflow message instead
  of the crate's named `MAX_BASIS_DIM` boundary.
One micro-call folded in rather than separately valued: `ord_add`/`ord_mul`
(`cantor.rs:43-73`) panic on coefficient overflow where sibling nim ops return
`Option` — either `Option`-ify or keep the panic with a one-line comment invoking the
`Rational::add` precedent; the current silent asymmetry on one struct is the only
wrong option.

### ½·(e_c∧e_i∧e_f∧e_s): `encapsulation-stragglers`
**The engine's accessor discipline, unevenly applied to its own satellites.** The
earlier sweeps encapsulated the engine; these never got the treatment:
- `DiscriminantForm`/`OddDiscriminantForm` (`discriminant/form.rs:630,645`) — all
  three invariant-carrying fields bare `pub`, while *every* sibling form type
  (`IntegralForm`, `SymplecticForm`, `HermitianForm`, `FiniteQuadraticModule`,
  `BinaryCode`, `PrimeCode`) guards its Gram behind a checked constructor. The two
  types also share an identical field layout and a byte-identical
  `bilinear_value_mod1` — a shared private core struct would fix the duplication and
  the encapsulation in one move.
- `SpinorRep` (`spinor.rs:45-70`) — every field `pub`, no constructor validation, a
  documented pairing invariant (`diagonalized_metric` ⇔
  `orthogonal_basis_in_original`) enforced by nothing; same-module code mutates
  fields post-construction. `LazySpinorRep.algebra` likewise.
- `Cga` (`cga.rs:43-50`) — `alg/n/no/ninf` bare `pub`, so `Cga::new`'s char-0 and
  ½-invertibility checks are bypassable by struct literal; the type carries both raw
  index fields *and* derived accessors (`n_o()`/`n_inf()`) for the same data.
- `LinearMap.cols` (`outermorphism.rs:26`) — `from_columns` validates squareness, but
  the field is `pub` and even `identity()`/`compose()`/`inverse_outermorphism()`
  bypass the checking constructor in its own module. (The sweep fixed `LinearMap.n`;
  `cols` was the other half.)
- `WittClass` (`witt/class.rs:82-88`) — bare `pub field_degree/arf` vs every Brauer
  sibling in the same shelf private-with-checked-constructors.
- `Zp(pub u128)`/`WittVec(pub [u128; F])` — unlike `Nimber(pub u128)` (every value
  legal), these carry a reduced-into-`[0, modulus)` invariant that `neg()` trusts
  without re-checking: `Zp::<3,2>(20).neg()` underflows. Reduce in `neg` or go
  private. (`Char2QuadForm.blocks/singular` is the same shape, newer and lower
  stakes.)
Explicitly *not* on this list: `KneserMassRecord`'s plain fields — plain-bag
`…Record`/`…Certificate` types are a real, documented convention (the games pillar
runs on it); the split to standardize is "has an invariant ⇒ accessors; pure catalogue
row ⇒ bag," which every case above fails on the invariant side.

### ½·e_f: `display-mirrors`
**Three classifier reports and one mirror pair missing the house `Display`.**
`SymplecticInvariants`, `HermitianSignature`, `FiniteHermitianInvariants` lack
`Display`+`display()` while every sibling report in the cluster has both — and the
consequence is concrete: `py/forms.rs` hand-rolls the same `rank=…, radical=…`
formatting three times, which is precisely the duplication the convention exists to
prevent. Sharper: `FunctionFieldBrauerWallClass` — documented in its own doc comment
as carrying "the same Wall coordinates" as `RationalBrauerWallClass` — lacks the
`Display` its mirror has, *in the same file*; and `WittClassG`, the type the classify
façade actually returns, has no `Display` while the narrower `WittClass` does. (The
cross-sweep inventoried ~20 more glossary types with no `Display`; whether "every
classifier report renders" becomes policy is a9's call — the five above are drift
against *local* norms regardless.)

### ½·e_c: `engine-cohesion`
Three small things, one home:
- `versor_inverse` and `spinor_norm` carry a verbatim six-line "is `v·ṽ` a pure
  invertible scalar" gate (`versor.rs:85-94`, `spinor_norm.rs:66-75`) — the
  `spinor_norm` doc even *names* the sharing ("the same invertibility gate as
  `versor_inverse`") that the code doesn't do. One private
  `pure_scalar_norm(&self, v) -> Option<S>` on `CliffordAlgebra`.
- `engine/terms.rs`'s `add_term`/`merge` (the canonical insert-and-drop-zero term-map
  primitive, self-described as shared infrastructure) is `pub(super)`-walled inside
  `engine`, so `hopf.rs:64-70` re-implements the identical `u128`-keyed logic by
  hand. Loosen to `pub(crate)`. (`divided_power`'s `Multidegree` case would need
  generifying — lower priority, note and skip.)
- The seven `engine/` files are the only production files in the core with no `//!`
  module headers (checked against every other split directory — universal compliance
  elsewhere); the per-file breakdown lives only in `AGENTS.md`. One paragraph each,
  and `AGENTS.md` can slim to match.

---

## ups — worth less than any number, still strictly positive

### ↑·(e_g∧e_c∧e_i): `dead-weight-2`
The `report-dead-weight` pattern, round two: `WeylVersorInvariants.coxeter_versor_order`
is `Option<u128>` but the only constructor `?`-unwraps before wrapping in `Some` — the
`None` is unreachable, the field should be `u128` (a survivor of the exact sweep item
that cleaned this struct once); `Quotient.num_classes` stores what `class_rep.len()`
already knows; `game_as_int` (`atomic_weight.rs:34`) is a private no-op alias for
`integer_value` (call it directly; keep `heating::integer_game_value`, which earns its
`pub`); `hackenbush.rs:169`'s test module re-implements `Game::nim_heap` byte-for-byte
(the "cross-check" it feeds is the same recursion twice); `GameClifford::new` hardcodes
literal `3` for `lambda.rs`'s private `DEFAULT_RELATION_BOUND` (make it `pub(super)`);
`Ramified::pi()`'s `debug_assert!(E >= 2)` reads as release-mode protection but the
next line's index panic is what actually guards — one honest comment or drop it.

### ↑·(e_s∧e_f): `micro-naming-2`
Grouped one-liners, same spirit as last audit's `micro-naming`:
- `Omnific::floor(s: &Surreal)` is a constructor wearing an instance-method name, and
  collides with the unrelated `Surreal::floor(&self)` — `from_floor` matches its own
  file's `from_*` convention.
- The two `strip_factor`s return `i128` vs `usize` for the same multiplicity concept
  (`function_field.rs:68` vs `function_field_char2.rs:81`); `asnf.rs:104` immediately
  casts the `usize` one back to `i128`. Width rule 7 territory.
- `arf_nimber_at_degree` bare-`.unwrap()`s the same provably-nonzero inverse its
  documented mirror `arf_char2_core` threads through `?` (`char2/arf.rs:392` vs
  `:290`); and `brown_f2` carries input asserts its declared "mirrors field-for-field"
  twin `arf_f2` lacks — align, or soften the wording to "same data shape."
- `finite_hermitian_in_domain` does the `ensure_supported()` job under an unrelated
  name (`hermitian.rs:79`) — genuine trait mismatch, but the name should signal the
  kinship.
- `AdelicIsotropy`/`FFAdelicIsotropy` are self-described decompositions outside the
  `…Decomp` glossary — rename or bless "…Isotropy" as a named pattern in the glossary
  the way `…Signature` is.
- `fpn.rs:305`'s "beyond the curated rows" prose survives a world where production
  generation is fully generated (the `Conway`/`Irreducible` tags are test-oracle
  vocabulary now) — stale, actively misleading about a boundary that no longer exists.
- `Ordinal`'s CNF renders `base⋅coeff` (`ω⋅3`) against the crate-wide `coeff⋅label`
  rule — almost certainly *correct* (CNF is conventionally `ω^β·n`; ordinal
  multiplication is non-commutative and the order carries meaning) but it's a silent
  exception: one doc line on `fmt_cnf` so a future pass doesn't "fix" it.
- `Fpn::generator()` returns *zero* for `N = 1` (a value that is definitely not a
  generator) where the file's own style would return `Option` or panic like
  `primitive_element()`.

### ↑·(e_f∧e_s∧e_c): `idiom-splits`
Two-standards situations to collapse or document, no code wrong:
- `field_invariants.rs` guards `Fp<P>` domain via `Option` while `oddchar/field.rs`
  panics via `assert_odd_prime` for the identical check — either align, or doc-note
  the deliberate two-contract split (validated-`P` helpers vs arbitrary-`P` entry
  points).
- `linalg/field.rs` uses `debug_assert_eq!` for shape preconditions where
  `linalg/integer.rs` uses always-on `assert!` with messages — if the field kernels'
  choice is a perf trade under the Clifford solves, say so next to the asserts.
- `local_global/mod.rs` (and `integral/mod.rs`) use `pub mod` children where every
  other shelf keeps children private behind the flat re-export — and `witt/milnor.rs`
  imports through the resulting nested path. Pick the flat convention; it's the one
  `forms/AGENTS.md` describes.
- `HermitianForm`/`SymplecticForm` lack the `.gram()` accessor their own sibling
  `FiniteHermitianForm` (and the whole integral wing) exposes — symplectic's tests
  reach around via a module-local helper, which is the tell.

---

## the disposition (one paragraph, hat off)

The macro-verdict from last time still stands — the spine, the symmetries, the honesty
boundaries are all intact, and this pass confirmed the sweep's plays held rather than
regressed. What this audit adds is a diagnosis one level deeper: the crate's substrate
discipline is *reactive* — a helper gets a home when an audit catches the copies, but
nothing in the house style says "if you write a private fn that isn't about your
module's math, stop." Hence `pow` eight times, prime factorization five times, the
valuation quartet three times — all *after* a sweep that consolidated gcd eight-fold.
If I play one move first it's `pow-times-eight` + the `Scalar::pow` default method,
because it's the only item that *prevents* recurrence structurally (the next backend
inherits the default instead of writing its own); `helper-commons` follows as the same
afternoon's momentum. The partiality and encapsulation rosters are real but bounded —
outliers against norms strong enough that the fix list is short, which is the crate
working. And one meta-note: the three ledgers now genuinely cross-reference each other
(the p-adic guard gap is CORRECTNESS's to play, the plain-bag Record convention is
documented here, the char-2 spinor norm completion is COMPLETENESS's) — play them as
one hand.

---

The next taste-style audit after this one: `src/ogham/` and `src/py/` remain the
standing out-of-scope candidates — see [`CONTINUATIONS.md`](CONTINUATIONS.md) →
`ogham-reflect` (its part (3) is a CONSISTENCY-style audit of `src/ogham/` after three
builds of growth).
