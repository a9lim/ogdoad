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

## Status — audited 2026-06-20 (Rust core only; py/ and ogham/ out of scope)

The 2026-06-11 `taste-sweep` (in git history) played the last audit's findings and the
macro-aesthetic it praised has held: the narrated docs, the honesty boundaries, the
pillar symmetries, the `…Class`/`…Decomp`/`…Invariants` glossary, the `linalg/`
substrate floor — all intact and mostly load-bearing exactly as the sweep left them.
This audit is therefore almost entirely about **the newest wing**. Since 2026-06-11 the
crate grew the integral lattice chain (Kneser, Niemeier, Weyl-versors, codes,
clifford-lattices, theta/modular, discriminant) and the char-2 local–global leg, and that
growth happened *fast and in isolation*. The single recurring failure is that the new code
**did not reach back for the substrate the rest of the crate already established** — it
re-rolled helpers, re-opened a corner of the played glossary, and grew report structs with
dead weight. None of it touches mathematical content; the whole list is one consolidation
pass, and the diagnosis below names which standard each item fails to meet (which is the
useful kind of finding — the baseline is high enough that every item is the code failing
*itself*).

---

## What still holds (0 — listed so a cleanup pass doesn't destroy it)

- **The substrate floor is real and mostly used.** `linalg::field::unit_pivot_nullspace`
  is the one Gauss–Jordan kernel, and `symplectic.rs:111` + `clifford/blade.rs:170` call
  it correctly; `scalar::is_prime_u128` (`scalar/mod.rs:194`) is shared by `padic.rs`,
  `ordinal/tower.rs`, and the bindings. The duplications below are findings *because* this
  floor exists and the older code respects it.
- **The symmetry discipline is intact** where it was built: the No↔On₂ mirror, the
  place-table grouping, the char0↔char2 classifier mirror, the verb-first façade. The
  drift this audit finds is at the *edges the newest code added*, never in the spine.
- **The honesty boundaries survived growth.** Node budgets return `None` not silent caps;
  non-integral scaled Grams return `None`; the catalogue-backed rank-24 boundary is
  documented. None of that is on this ledger — it's the house aesthetic working.

---

## numbers — buildable now

### 1·(e_s∧e_c∧e_f∧e_i∧e_g): `substrate-bypass`
**The newest code re-rolls helpers the crate already exports as substrate.** This is the
flagship finding — one mechanical consolidation pass, on-thesis (the crate *has* a
substrate floor; the new wing ignored it), and the highest-grade blade in the audit
because it reaches five pillars. The roster:

- **Integer GCD, eight ways.** `linalg::integer::ext_gcd` (`integer.rs:130`) already
  computes a gcd as its by-product, yet there are eight independent Euclidean copies:
  `scalar/big/surreal/analytic.rs:160`, `scalar/big/ordinal/subfield.rs:108`,
  `scalar/exact/rational.rs:19` (all `u128`); `forms/equivalence.rs:115` (`u128`);
  `forms/integral/kneser.rs:337` and `forms/integral/mass_formula.rs:65` (byte-identical
  `i128`); `forms/integral/lattice/core.rs:19` (`gcd_i128`, already `pub(super)` — and its
  own sibling `kneser.rs` *still* didn't reach for it); `forms/integral/discriminant/form.rs:220`
  (`gcd_usize`). Fix: one `linalg::integer::gcd` (plus the `u128` width) and `ext_gcd(a,b).0`
  where Bézout isn't needed. This is the largest single scatter in the crate.
- **`is_prime` reinvented.** `forms/integral/kneser.rs:62` rolls its own primality test
  next to the exported `scalar::is_prime_u128` that every older file uses. Plus
  `is_prime_power_order` written twice — `discriminant/form.rs:536` (`usize`) vs
  `fqm_witt.rs:1069` (`u128`), same loop, mismatched width.
- **`checked_factorial`/`checked_pow2` re-copied.** `lattice/geometry.rs:20,28` exports
  both `pub(super)`; `niemeier.rs:474,482` re-copies them privately rather than lifting the
  pair to the lattice hub. (Note the *intended* divergence: `scalar/mod.rs:215`'s
  `checked_factorial_i128` is a different thing — the ogham `33!` host roof — so it's not a
  third copy to fold.)
- **A lone hand-rolled Gauss–Jordan rank.** `forms/hermitian.rs:87`'s private
  `matrix_rank` is the one place outside `linalg/` that re-implements the pivot kernel
  `unit_pivot_nullspace` already provides (`rank = ncols − nullspace.len()`). Its siblings
  `symplectic.rs` and `clifford/blade.rs` delegate correctly; `hermitian.rs` is the holdout.
- **`mex` and "integer value of a game," twice each.** `coin_turning.rs:30` has a private
  `mex(&HashSet)` while `grundy::mex` (`grundy.rs:25`, `IntoIterator`) is the public one
  `loopy/nim_values.rs` calls. `atomic_weight.rs:34` (`game_as_int`) and `heating.rs:25`
  (`integer_game_value`) are the same `number_value()?.as_dyadic()?`-then-check-integer
  extraction — one belongs `pub(crate)` in `partizan.rs` beside the primitives it composes.
- **Two enumerations of grade-`k` blade masks.** `clifford/blade.rs:41` (`combinations`,
  recursive) and `clifford/outermorphism.rs:122` (`grade_k_masks`, Gosper's hack) both
  enumerate `u128` masks with `k` bits set; the latter is strictly better and handles the
  `n=128` edge. Their home is `engine/basis.rs` beside `bits`/`grade`.
- **The `r` tell.** `fn r(n)->Rational` is a test-local helper in ~8 files, but
  `weyl_versors.rs:36` makes it a *non-test module-level* fn and `genus.rs:69` renames it
  `r_int`. Trivial on its own — it's the fingerprint of copy-paste assembly, which is what
  the whole item diagnoses.

### ½·e_i: `niemeier-partiality`
**Four sibling methods on a public enum, three panic and one returns `None`.**
`NiemeierComponentKind::E(usize)` is `pub` (`niemeier.rs:22`); `coxeter_number` (`:41`),
`determinant` (`:58`), and `root_lattice` (`:85`) all `panic!("unsupported exceptional
root rank")` on `E(_)`, while `weyl_group_order` (`:74`) honestly returns `None` for the
same input. So `NiemeierComponentKind::E(10).determinant()` panics but
`.weyl_group_order()` doesn't — partiality decided four times, three ways wrong. The crate's
own house style (partial math returns `Option`/`None`, never a pretty panic — `Ordinal`
*omits* `*` rather than panic) makes the three panics the outliers. Two clean fixes,
either fine: `Option`-ify the three (matching `weyl_group_order`), or make the
exceptional rank un-misconstructable with an `E6 | E7 | E8` variant set so the `E(_)` arm
can't exist. The newtype is larger churn but kills the footgun at the type level — worth
a9's call which.

---

## switches (a9's move first)

### ±1·e_f: `local-global-parallelism`
**The three characteristic legs of the local–global layer name the same concepts on three
different axes, so a symmetry that's structural in the math is invisible in the API.** The
place types are named by *nothing* / *role* / *characteristic*: `Place` (ℚ, `padic.rs`),
`FFPlace` (odd `F_q(t)`, `function_field.rs:36`), `Char2Place` (char-2 `F_q(t)`,
`function_field_char2.rs:60`). "Which places are relevant" is `relevant_primes` (returns
primes, no `try_`, `padic.rs:297`), `try_relevant_places_ff` (`try_`, `Vec`,
`function_field.rs:223`), and `relevant_places_char2` (no `try_`, takes a whole form,
`springer/char2/global.rs:53`) — three input shapes, two `try_` disciplines, three suffix
conventions. This is a switch, not a number, for two honest reasons: (1) the
`as_symbol_*` naming for the char-2 Artin–Schreier symbol is a *legitimate* math
distinction (`[a,b)` is not the Hilbert symbol) and AGENTS.md documents it, so that
specific pair should NOT be flattened; (2) reconciling the rest is rename churn across a
`pub`-within-crate surface a9 should bless. My honest lean: I'd parallel at least the
*place types* (`Place`/`FFPlace`/`Char2Place` named on three different axes is exactly the
kind of thing that hides the local↔global symmetry the project is built to display), and
leave the symbol names distinct because the underlying symbols genuinely are.

---

## halves — an afternoon each

### ½·(e_f∧e_i): `glossary-fray`
**The `…Class` glossary the sweep played has frayed at the integral edge.**
`record-suffix-zoo` (played 2026-06-11) reserved `…Class` for *an element of an actual
group/classifying set carrying a law* (`WittClass`, `BrauerClass`, …) and `…Invariants`
for a classifier's report record. The new integral types broke both ends: `NiemeierClass`
(`niemeier.rs:99`) and `KneserMassClass` (`kneser.rs:39`) are *static catalogue records*
((label, |Aut|), root-system data) with no group law — they want `…Record`/`…Entry`. And
the integral wing introduced a fourth suffix, `…Report` (`KneserMassReport`,
`WeylVersorReport`, `CliffordBarnesWall16Report`), that isn't in the glossary at all;
"report" reads fine but it should be *in* the glossary or folded into `…Invariants`, not a
silent fifth convention. Re-enforcing the played glossary on the newest types; mechanical.

---

## ups — worth less than any number, still strictly positive

### ↑·e_g: `games-display-gap`
**The `Display` discipline the sweep established never reached the games value types.**
`debug-as-display` (played) made `Display` a `Scalar` supertrait and gave `Multivector`
+ the record types real `Display` impls with `display()` as thin aliases. The games pillar
still renders three different ways and none of them is `Display`: `Game::display() ->
String` (`partizan.rs:182`), `LoopyValue::name()` + `LoopyValue::form()`
(`catalogue.rs:125–159`), and `NumberGame`/`NimberGame` with no string form at all. The
crate decided this question already; games should `impl fmt::Display` (canonical form for
`Game`, `name()` for `LoopyValue`) with the bracket/`form()` view as a named method.

### ↑·e_c: `cga-meet-shadow`
**`Cga::point_pair` and `Cga::meet` are byte-identical, and `meet` collides with a
different contract.** Both bodies are `self.alg.wedge(a, b)` (`cga.rs:157–167`) — the
"point pair" and "IPNS meet" distinction was named but never made real (neither guards
its inputs by grade). Worse, `Cga::meet` is the *infallible* wedge while
`CliffordAlgebra::meet` (`versor.rs:231`) is the *fallible* regressive product
(`Option`, needs an invertible pseudoscalar) — same name, opposite fallibility, both
re-exported flat. Rename the CGA one (`outer_join`?), which also dissolves the duplicate.

### ↑·e_c: `divided-power-encapsulation`
**`divided_power.rs` didn't get the engine's encapsulation sweep.**
`engine-encapsulation-split` (played) made `CliffordAlgebra::dim()` a method and
`Multivector::terms` a `pub(crate)` field behind a `terms()` accessor — but
`DividedPowerAlgebra.dim` (`divided_power.rs:50`) and `DpVector.terms` (`:57`) are bare
`pub` fields, the exact pattern the sweep removed next door. Same shape in
`outermorphism.rs:27`: `LinearMap.n` is a `pub` field always equal to `cols.len()` — a
redundant field a struct-literal caller can desync. Bring all three in line (accessor or
derive-from-`cols`).

### ↑·e_i: `report-dead-weight`
**The newest report structs carry fields that compute nothing.**
`WeylVersorReport.simple_reflection_count` (`weyl_versors.rs:26`) is set to `kind.rank()`
on the line after `rank: kind.rank()` — tautologically equal, a field that invites the
reader to wonder when it differs (never). `clifford_lattices.rs:112–132` calls
`clifford_barnes_wall_16_numerator_rows()` twice (once inside the lattice build, once for
`rows.len()`) to derive counts that are compile-time constants. `KneserMassReport`
(`kneser.rs:46–56`) stores `generated_class_labels` redundantly with `classes[].label`.
All three want to be dropped or made derived methods.

### ↑·(e_s∧e_c∧e_f): `micro-naming`
Pure one-line naming drift, grouped so they don't each take a heading:
- **`from_scalar` outlier** (e_s): `Laurent::from_scalar` (`laurent.rs:98`) against
  `Gauss`/`Ramified`/`RationalFunction::from_base` (`gauss.rs:88`, `ramified.rs:66`,
  `function_field.rs:88`). Laurent is the only one of the four not spelled `from_base`.
- **`ext_degree` vs `extension_degree`** (e_s): `FiniteField::ext_degree`
  (`finite_field/mod.rs:54`) abbreviates what `FieldExtension::extension_degree`
  (`extension.rs:53`) spells out — and `Fpn`/`Nimber` carry both for the same number.
- **guard-name drift** (e_s): the const-generic validators are `assert_prime_modulus`
  (`fp.rs:61`), `assert_supported_field` (`fpn.rs:311`, `qp.rs:60`),
  `assert_supported_ring` (`zp.rs:33`), `assert_supported_precision` (`laurent.rs:56`) —
  four names for one job, and `qq.rs`/`wittvec.rs` have no guard at all.
- **`WittClassG` opacity** (e_f): the `G` suffix (`class.rs:219`, and the shared
  `WittClassGError`) is unexplained — no doc says it's the trichotomy-spanning *generic*
  Witt class vs the nimber-specific `WittClass`. One doc line, or `…Tri`.
- **`Poly::x()` prints `t`** (e_s): the constructor is `x()` (`poly.rs:126`) but Display
  hardcodes `t` (`:81`) and the three extension types build via `t()`. `Poly::t()` matches
  everything that consumes it.
- **`of` vs `from_*`** (e_s/e_i): `Genus::of` (`genus.rs:342`) and `NewtonPolygon::of`
  (`newton.rs:93`) are the crate's only two `of`-constructors; everything else taking a
  foreign type and returning `Option<Self>` is `from_*`. Reads fine, but it's a two-author
  convention break.
- **precision-width mismatch** (e_s): the relative-precision cap is `const K: u128` on
  `Qp` (`qp.rs:42`) but `const K: usize` on `Laurent` (`laurent.rs:47`) — the two closest
  cousins disagree on the width of the same parameter.

### ↑·e_s: `stale-debug-comment`
`scalar/tropical.rs:199` justifies a `{r:?}` format with the comment "`Rational` is
`Debug`-only (no `Display`)" — false since the `debug-as-display` sweep made `Display` a
`Scalar` supertrait, so every backend including `Rational` impls it. A stale comment that
actively misdirects the next editor; delete it (and switch to `{r}`).

---

## the disposition (one paragraph, hat off)

The macro-aesthetic the last audit praised is exactly as strong as it was — this audit
found nothing wrong with the spine, the symmetries, or the honesty boundaries. The whole
list is one shape: **the integral wing and the char-2 local–global leg grew fast and
didn't reach back for the substrate the rest of the crate established.** Helpers got
re-rolled (the gcd-times-eight is the emblem), the played glossary frayed at its newest
edge, report structs accreted dead fields, and a couple of the older disciplines (the
`Display` layer, the encapsulation sweep) simply never reached the new code. None of it is
hard, none of it is mathematical, and the fix is a single consolidation pass that mostly
*deletes* code. If I play one move first it's `substrate-bypass` — it's the most code
removed per hour, it re-establishes the floor as the floor (so the *next* new wing inherits
the habit), and it's the cheapest way to make the crate's micro-aesthetic match the macro
one it's been coasting on.
