# AGENTS.md — `src/scalar/`

The PILLAR of commutative coefficient worlds: the `Scalar` trait and every
concrete backend the Clifford engine and forms layer run over. Pure Rust,
generic; the per-backend Python wrappers live in `src/py/scalars.rs`.

## Two orthogonal organizing axes

The directory is grouped **by place** (the "any number" table: each field beside
its ring of integers). A *second* axis — the **characteristic trichotomy** (char
0 / odd / 2) — cuts ACROSS the table and is what organizes `forms/` instead. Hold
both: the place table says *where a number lives* (Archimedean, p-adic, finite,
transfinite); the trichotomy says *which classification theory applies*.

```
              FIELD                     RING OF INTEGERS
 Archimedean  Rational (ℚ)              Integer (ℤ)               exact/
 transfinite  Surreal (No)              Omnific (Oz)              big/
 p-adic       Qp, Qq                    Zp, WittVec              small/, finite_field/
 finite       Fp, Fpn, Nimber           —                        finite_field/
```

The (field, ring-of-integers) pairing is made **structural** in `integrality.rs`
(`HasFractionField` / `HasRingOfIntegers`); the local-field view is made
structural in `valued.rs` (`Valued`); root-taking in `analytic.rs`.

## The `Scalar` trait + the trait layer (`mod.rs` and friends)

- **`mod.rs`** — the `Scalar` trait (`add`/`neg`/`mul`/`zero`/`one`/`is_zero`/
  `inv`/`characteristic`) + the "any number" table doc + the flat re-export hub.
  Also `impl_scalar_ops!`: every backend gets concrete-type operators (`+ - *`
  and unary `-`) forwarding to the trait methods (so `Surreal + Surreal`,
  `-nimber` work). `/` stays a method (inv is partial). **The operators are NOT a
  `Scalar` supertrait** — see "things that look like bugs".
- **`integrality.rs`** — the (field, ring-of-integers) pairing made structural:
  `HasFractionField {Frac; to_fraction}` + `HasRingOfIntegers {Int; is_integral/
  to_integer}` (with `Int: HasFractionField<Frac=Self>` tying the loop). Impl'd
  for the four distinct-type rows (ℤ⊂ℚ, Oz⊂No, Zp⊂Qp, W_N⊂Qq) PLUS the blanket
  Surcomplex transport (ℤ[i]⊂ℚ[i] falls out). Laurent/Ramified `F_q[[t]]`/`O[π]`
  are same-type valuation subrings, so they stay out (`is_integral` only) — honest.
- **`valued.rs`** — the `Valued` trait: a discrete valuation + canonical
  uniformizer ϖ, impl'd for the local FIELDS (Qp/Qq/Laurent). The spine of the
  "local fields" view (cuts across `small/` + `functor/`); the datum `Ramified`
  folds from its base. NOT a `Scalar` supertrait (rings of integers + exact
  Archimedean worlds excluded).
- **`analytic.rs`** — the ANALYTIC layer unified as two traits split on where
  precision lives. `ExactRoots {is_square; sqrt}` (no precision arg — exact, or
  exact to the type's K) for Rational, Nimber, Fp, Fpn, Zp, Qp, Qq, WittVec,
  Surreal (exact via the fixed-point bridge over the lazy roots), Laurent, AND the
  blanket `Surcomplex<R: ExactRoots+Ordered>` (the algebraic-closure √(a+bi)).
  `SeriesRoots {sqrt_to_terms; nth_root_to_terms; inv_to_terms}` (caller-chosen n)
  is the lazy interface — Surreal-only (the one world with unbounded, not
  type-fixed, precision). `Ordered {sign}` is the branch-picking datum the
  Surcomplex blanket needs. The residue Tonelli roots (`fp_sqrt`/`fq_sqrt`) live
  here (shared with `small/analytic`'s Hensel seed). Gauss/Ramified excluded
  honestly. NOT a `Scalar` supertrait, like `Valued`.

## `exact/` — the Archimedean char-0 base (field + ring of integers)

- **`rational.rs`** — exact ℚ over i128, NOT a game backend: the char-0 scalar
  that validates the geometric product against the known Cl(p,q) classification
  before the exotic backends are trusted. (Overflow is a known limit; the surreal
  backend is the real char-0 home.)
- **`integer.rs`** — exact ℤ, the coefficient ring for the exterior algebra of the
  game group (`games/game_exterior.rs`): games are a ℤ-module, not a ring, so Λ
  over ℤ is the structure that lives on all of game-world. Only ±1 invertible.

## `big/` — the transfinite worlds (the number may be infinite)

- **`cnf.rs`** — `merge_descending`, the descending-CNF canonicalizer parameterized
  by the 3 places surreal & ordinal differ (exponent order: No value-order vs
  ordinal lex; coeff merge: + vs XOR; zero test). Deliberately a shared FUNCTION,
  not a `Cnf<C>` TYPE — the orders/algebras diverge (No is a field, On₂ isn't), so
  a shared type would be a false identity.
- **`surreal/`** — finite-support surreal Hahn/CNF backend (char 0), all `impl Surreal`:
  - `mod.rs` — CNF core: `Vec<(exponent: Surreal, coeff: Rational)>`, recursive
    exponents, Hahn arithmetic `ω^a·ω^b = ω^{a+b}`, Scalar, Debug, `truncate()`.
  - `simplicity.rs` — the {L|R}/simplicity bridge (dyadic): `as_rational`/
    `as_dyadic`/`dyadic_birthday` + `simplest_above`/`_below`/`_between`, floor/frac
    (the Oz bridge).
  - `sign_expansion.rs` — exact `sign_expansion`/`from_sign_expansion` (dyadic,
    round-trips, length = birthday) + `as_ordinal`/`from_ordinal` + the transfinite
    (Gonshor) `SignExpansion` + `birthday_ordinal` + the transfinite inverse.
  - `analytic.rs` — the LAZY field layer (the `SeriesRoots` primitives):
    `inv_to_terms` (Neumann series) + `sqrt_to_terms`/`nth_root_to_terms` (real-closed
    roots to n terms; `Some` iff the leading coeff is a perfect ℚ-power).
- **`omnific.rs`** — the omnific integers Oz: `Omnific(Surreal)`, a transfinite
  commutative RING (not field). The surreal mirror of `Integer`.
- **`ordinal/`** — transfinite (ordinal) NIMBERS On₂, the char-2 mirror of surreal:
  - `mod.rs` — CNF core: `Ordinal = Vec<(exponent: Ordinal, coeff: u128)>`, the lex
    cmp, `as_finite`, Debug.
  - `nim.rs` — char-2 NIM arithmetic: `nim_add` (coeff XOR) COMPLETE; `nim_mul`
    implemented below ω^ω via the degree-3 tower (returns `None` at ω^ω and above).
  - `cantor.rs` — ORDINARY (Cantor) `ord_add`/`ord_mul` (ω+ω=ω·2, 1+ω=ω) — the
    surreal birthday's run-length arithmetic. A distinct algebra, sharing only CNF.

The surreal↔ordinal **mirror** (No char 0 / On₂ char 2, sharing `cnf.rs`) is one of
the project's central symmetries.

## `small/` — the non-Archimedean (p-adic) local world

- **`qp.rs`** — `Qp<const P, const K>`: the p-adic FIELD Q_p (the p-adic mirror of
  ℚ / of Omnific⊂Surreal). `p^val·unit`, char 0, inv total on nonzero. CAPPED-
  RELATIVE precision: mul/inv exact, addition NOT associative across precision
  boundaries (a precision model, like float). EXCLUDED from the exact-ring fuzz.
- **`zp.rs`** — `Zp<const P, const K>`: the p-adic integers Z_p (= Z/p^k), the ring
  of integers of Q_p. A LOCAL RING (p a non-unit), residue field F_p; Cl over it is
  non-semisimple.
- **`qq.rs`** — `Qq<const P, const N, const F>`: the UNRAMIFIED extension Q_q =
  Frac(W_N(F_q)), residue degree F (residue field F_q). To WittVec what Qp is to Zp;
  Qq with F=1 IS Qp.
- **`analytic.rs`** — the p-adic ANALYTIC layer over all four backends (mirror of
  `surreal/analytic`): Hensel-lifted `is_square`/`sqrt` (Newton, ODD p only) + the
  Teichmüller rep τ. These inherent methods are what `ExactRoots` delegates to.

## `finite_field/` — the finite residue worlds (the trichotomy's finite leg)

- **`mod.rs`** — the `FiniteField` TRAIT: the shared Galois engine (degree,
  conjugates, min_poly, relative_trace/_norm, multiplicative_order, is_primitive,
  discrete_log) as default methods. An impl supplies only `frobenius`, integer
  `pow`, `ext_degree`, `group_order`, `group_order_factors`. nimber + fpn both
  impl it — one verified algorithm, two backends.
- **`fp.rs`** — `Fp<const P>`: the prime field F_P (odd char), residue field of Zp.
- **`fpn.rs`** — `Fpn<const P, const N>`: F_{p^N} via a (P,N)-keyed irreducible
  reduction poly. Completes the odd-char tower AND the char-2 odd-DEGREE fields
  nimbers can't reach (F_8). (NB the static `order()` = field order p^N, ≠
  `multiplicative_order(&self)`.)
- **`nimber/`** — On₂ in u128 (= F_{2^128}), split by layer, re-exporting `nim_*`
  flat: `mod.rs` (wrapper + Scalar), `arithmetic.rs` (`nim_add`=XOR; `nim_mul` via
  Fermat-power recursion; `nim_square`/`nim_sqrt`/`nim_inv`), `artin_schreier.rs`
  (`nim_trace` + y²+y=c solver), `galois.rs` (impl FiniteField, with Pohlig–Hellman
  + BSGS overrides for `is_primitive`/`discrete_log`).
- **`wittvec.rs`** — `WittVec<const P, const N, const F>`: Witt vectors W_N(F_q) as
  the truncated unramified ring (Z/p^N)[t]/(f̃). The char-p analogue of Z_p; its
  field of fractions is `small/qq.rs`.

## `functor/` — the root-level functors (ways to GROW a field)

Orthogonal to the place table: a 2×2 of (algebraic|transcendental) ×
(residue|value-extending), **all four corners filled**.

| | residue-extending | value-extending |
|---|---|---|
| **algebraic** | `surcomplex.rs` (root of x²+1) | `ramified.rs` (root of Eisenstein xᴱ−ϖ) |
| **transcendental** | `gauss.rs` (adjoin t as a unit, v(t)=0) | `laurent.rs` (adjoin t as uniformizer, v(t)=1) |

- **`surcomplex.rs`** — `Surcomplex<S>` = adjoin i over ANY backend (carries
  `conj()`). Only meaningful over char-0 worlds (over nimbers i²=1, degenerate).
- **`laurent.rs`** — `Laurent<S, const K>` = S((t)) to relative precision K. Over a
  finite field, the EQUAL-characteristic local cell F_q((t)) (the char-p mirror of
  Qp); ring of integers F_q[[t]] = the val≥0 subring. Capped-relative; EXCLUDED
  from the fuzz.
- **`ramified.rs`** — `Ramified<S, const E>` = adjoin a root of xᴱ−ϖ over a Valued
  base. The RAMIFIED local cell Q_p(p^{1/E}), the ramified twin of Qq. Always a
  field (Eisenstein), incl. wild/inseparable p|E. EXCLUDED from the fuzz.
- **`gauss.rs`** — `Gauss<S>` = S(t) with the Gauss valuation (v(t)=0, transcendental
  residue ⇒ residue field k(t̄)). The last corner, Laurent's residue-extending twin.
  Valued itself; precision model, EXCLUDED.

## `global/` — the adelic/global place

`Adele` is a finite-precision restricted-product model over ℚ, with `LocalQp` as
the runtime-prime p-adic cell. Useful for product-formula / Hilbert-reciprocity /
Hasse–Minkowski experiments in `forms/adelic.rs`; not an exact infinite-memory
adele. `LocalQp` (runtime prime, NOT const-generic) is the analogue of
`forms`'s runtime `FiniteFieldForm`.

## Things that look like bugs but are not (scalar layer)

- **Scalar `+ - *` operators are concrete-only, NOT a `Scalar` supertrait.**
  Making `Scalar: Add+Sub+Mul+Neg` brings the ops into scope for every generic
  `S`, where `Mul::mul(self, Self)` shadows `Scalar::mul(&self, &Self)` at
  owned-receiver sites and forces clones the borrow-based engine avoids (70+
  generic sites broke when tried). Don't promote them; don't migrate the engine's
  `.add()`/`.mul()` to operators.
- **`ExactRoots`/`SeriesRoots`/`Ordered`/`Valued` are NOT `Scalar` supertraits.**
  Not every world takes roots or has a valuation, so the bounds stay opt-in. The
  trait impls *delegate to inherent methods of the same name* (inherent-shadows-
  trait makes that delegate-not-recurse).
- **`Surreal` has two square roots, by design.** `sqrt_to_terms(n)` is the lazy
  `SeriesRoots` primitive; `ExactRoots::sqrt(&self)` (0 args) is the exact value.
  Different arities, different precision contracts — don't unify them. (Python:
  `Surreal.sqrt(n)` lazy, `Surreal.exact_sqrt()` exact.)
- **`ExactRoots::sqrt`/`is_square` on `Zp`/`Qp`/`Qq`/`WittVec` panic at p=2.** They
  inherit the inherent odd-p assertion (the dyadic case is the forms mod-8 story).
  The finite fields and `Laurent` handle char 2 natively.
- **Surcomplex over nimbers is degenerate.** `i²=1`, `(1+i)²=0`, not a field.
  Surcomplex is only meaningful over char-0 worlds.
- **Surreal coefficients are ℚ, not ℝ.** The honest finite truncation of true CNF.
  Exponents *are* fully recursive surreals. `√2`, `√(2ω)` are honestly `None` (the
  leading coeff must be a perfect ℚ-power); `√ω = ω^{1/2}` IS exact (monomial).
- **`Surreal::inv` returns `None` for any non-monomial.** `1/(ω+1)` is an infinite
  Hahn series; finite support can't hold it.
- **`Surreal::birthday_ordinal`/`transfinite_sign_expansion` are `None` outside the
  representable subclass** (`√ω`, `ω−1`, `½ω`, mixed). Every *ordinal* (incl. ω^ω)
  is handled; `ε` is the one infinitesimal pinned. The honest Gonshor scope boundary.
- **`Qp` addition is not associative across precision boundaries.** Capped-relative
  (the standard p-adic model, like float). No finite-memory exact Q_p exists.
- **`nim_mul`'s `1u128 << (1u128 << n)` is not overflow-prone** for valid u128:
  bit positions < 128 ⇒ Fermat indices n ≤ 6, shift ≤ 64.
- **`Fpn::order()` is the field order `p^N` (static, no self); the element's
  multiplicative order is `multiplicative_order(&self)`.** Different things.
- **The `nim_*` Galois free fns delegate to the `FiniteField` trait; don't re-add
  inherent `Nimber` Galois methods.** An inherent `Nimber::degree` would shadow and
  recurse forever back through the free fn. To add a Galois op, add a default method
  to the trait (both nimber and fpn get it free). Nimber *overrides* `is_primitive`/
  `discrete_log` for the sharper large-field algorithms — intended, not duplication.
- **`scalar * multivector` works via the scalar's `__mul__` returning
  `NotImplemented`** so Python falls back to the MV's `__rmul__`. Don't make the
  scalar ops raise on a non-scalar operand.

## Math facts worth not re-deriving

- nim-field: `F_{2^{2^k}}` = nimbers `< 2^{2^k}`. `F_n ⊗ F_n = (3/2)F_n` for a
  Fermat 2-power `F_n = 2^{2^n}`; distinct Fermat powers multiply ordinarily.
- Surreal CNF = finite-support Hahn series with ℚ coefficients; the ω-map is the
  monomial map and `ω^a·ω^b = ω^{a+b}` is a group homomorphism on represented
  monomials.
