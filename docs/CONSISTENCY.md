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

## Status — audited 2026-07-02, PLAYED 2026-07-02 (same day)

The second full-tree taste audit (baseline `be5f4a4`-identical tree at `30588ec`) was
played the same day, in the same four-wave sweep as its CORRECTNESS sibling
(`78a45bc..362ebed`; archived as [`DONE.md`](DONE.md) → `revision-sweep-2026-07-02`).
The audit's diagnosis — **the floor itself was missing tiles** — was answered by
building the floor: `Scalar::pow` is now a default trait method every backend
inherits (the one play that *structurally prevents* recurrence — the next backend
cannot re-roll its own loop), the p-adic/rational helper quartet + prime
factorization + checked rational arithmetic all have single canonical homes, and the
partiality/encapsulation/Display outlier rosters were cleared. Post-sweep the tree
is fmt/clippy/doc-clean at 968 lib tests with a codex PASS on the full diff.

## What still holds (0 — listed so a cleanup pass doesn't destroy it)

- **Both sweeps' consolidations are load-bearing**: one gcd, one `is_prime_u128`, one
  `mex`, one grade-k mask enumerator, one `prime_factors`, one `binomial_checked`,
  one square-and-multiply (`Scalar::pow`, with `Nimber`'s Fermat-tower `nim_pow` as
  the one deliberate override via `FiniteField::pow`), the valuation quartet in
  `diagonal.rs`, `Rational`'s owned `checked_add`/`checked_mul`.
- **Partiality discipline is the crate norm** — and the seven-outlier roster from
  this audit is now zero: the quotient builders, `isotropy_over_adeles`,
  `fit_f2_quadratic`, `from_ordinal`, ADE constructors, `codewords`, and
  `classify_real/complex` all sit on honest `Option`/named boundaries. The one
  deliberate exception is documented where it lives: `weight_enumerator` keeps an
  infallible signature over a documented budget panic (recorded in
  [`CORRECTNESS.md`](CORRECTNESS.md) → recorded boundaries).
- **Encapsulation is the norm**: the stragglers (`DiscriminantForm`/
  `OddDiscriminantForm` via the shared private `DiscriminantCore`, `SpinorRep`/
  `LazySpinorRep`, `Cga`, `LinearMap.cols`, `WittClass`, `Zp`/`WittVec` reduce-in-neg,
  `Char2QuadForm`) are done. The plain-bag `…Record`/`…Certificate` convention stands:
  has an invariant ⇒ accessors; pure catalogue row ⇒ bag.
- **`GlobalField` is still the best abstraction in the crate**; the `…Isotropy`
  suffix is now a *blessed* glossary pattern beside it (per-place breakdown + derived
  `is_global()`), and `local_global/`/`integral/` children now sit private behind the
  flat re-export like every other shelf.
- The triple Arf implementation (`arf_f2`/`arf_nimber_at_degree`/`arf_char2_core`) is
  deliberate cross-checked redundancy, not duplication — don't "simplify" it. (The
  mirrors are now genuinely field-for-field: input asserts and `?`-threading aligned
  by the sweep.)

---

## Played 2026-07-02 — corrections to the audit's own findings

Recorded so the next auditor inherits the truth, not the first read:

- `helper-commons` claimed `unit_sign_odd` vs `odd_unit_residue` were "the same
  quadratic-residue wrapper under two names." **They answer different questions**
  (the decided ±1 square-class sign vs the raw pre-test residue); the byte-identical
  *arithmetic core* was consolidated under `odd_unit_residue` in `diagonal.rs`, and
  genus keeps a six-line ±1 wrapper. Both names survive on purpose.
- `char2-decomp-coverage`'s "one product of two distinct irreducible quadratics over
  F_4 closes it" was optimistic: a bad pair can be caught by the early-exit gcd
  before the trace splitter fires. The shipped pair is verified (by tracing) to hit
  the genuine Cantor–Zassenhaus branch.
- Two ordinal-local trial-division helpers (`ordinal/subfield::prime_factors`,
  `tower::smallest_prime_factor`) were deliberately left un-consolidated — the sweep
  fenced ordinal/ to one agent for the correctness items; folding them into
  `linalg::integer::prime_factors` is a residual ↑ for any future pass (note
  `smallest_prime_factor` is a different shape — early-exit smallest factor, not a
  factor list).

## ups — still open (worth less than any number, strictly positive)

- **↑·(e_s∧e_i): `ordinal-factor-fold`** — the two ordinal-local helpers above.
- **`display-policy` — PLAYED 2026-07-02.** a9 made it policy: **every classifier
  report renders.** All 34 remaining glossary record types (the suffix net over
  `…Invariants`/`…Decomp`/`…Class`/`…Record`/`…Isotropy`/certificates plus
  `Genus`/`ScaleSymbol`/`QuadricFit`/`Quotient`) got core `Display` + `display()`
  with exact-string render pins; py `__repr__`s delegate to core (byte-preserving
  where the old repr was already honest, deliberately richer where it was a
  `{:?}` dump — Genus now renders its per-prime Conway–Sloane symbols). The policy
  line lives in `src/forms/AGENTS.md`'s glossary. Discovered en route and
  documented in root `AGENTS.md`: coefficient-`1` elision is the Multivector-blade
  rule only — the polynomial family's `1⋅t` is conformance-pinned, don't "fix" it.
- **↑·e_y: `py-repr-audit`** — the Display-policy pass collapsed every glossary-type
  repr onto core `Display`; what remains for the standing ogham/py audit
  ([`CONTINUATIONS.md`](CONTINUATIONS.md) → `ogham-reflect` part (3)) is the
  non-glossary py surface (game values, scalars, engine types).

---

## the disposition (one paragraph, hat off)

The 2026-07-02 audit diagnosed the crate's substrate discipline as *reactive* — a
helper got a home only when an audit caught the copies. The sweep's answer was
structural where it could be: a default trait method can't be re-rolled by the next
backend, a private field can't be bypassed by the next struct literal, a flattened
shelf can't grow a second import convention. What can't be made structural is now
*named*: the reserved meaning of "source-pinned," the blessed `…Isotropy` suffix,
the recorded weight-enumerator boundary, the branch-selection trap in the splitter
test. The three-ledger cross-referencing held up in practice — the char-2 spinor
completion still lives in COMPLETENESS, the AJ switch in CORRECTNESS, the taste
corrections here — play them as one hand, and when the next audit comes, start it
at `src/ogham/` and `src/py/`, the two wings no taste pass has read.
