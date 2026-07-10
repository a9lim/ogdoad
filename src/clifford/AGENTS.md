# AGENTS.md — `src/clifford/`

The PILLAR holding the multivector engine and the geometric-algebra layer on top.
Everything here is generic over `S: Scalar` — the same code runs over nimbers
(char 2), surreals (char 0), surcomplex, integers, etc. Python wrappers (the
`backend!` macro) live in `src/py/engine.rs`.

`mod.rs` is a thin hub re-exporting the engine + versor + the structured-algebra
modules flat, so public paths stay shallow (`clifford::Metric`,
`clifford::coproduct`, … — note `sandwich` is an inherent `CliffordAlgebra` method,
called as `alg.sandwich(…)`, not a free path).

Fixed-width mathematical payloads here are `u128`/`i128`: blade masks,
divided-power exponents, spinor/Dickson parities, and Frobenius subfield data.
`usize` is for dimensions, basis indices, and matrix indexing.

## The engine (`engine.rs` + `engine/`)

`engine.rs` is a thin hub (+ the engine's integration test suite: algebra
construction, the GA ops, Cayley, even subalgebra, exercised over the Ordinal/Surreal
backends). The associative-algebra core is split by concept under `engine/`; every
file there now carries its own `//!` module doc — read those for the full
breakdown. The load-bearing facts worth knowing before opening a file:

- **`metric.rs`** (`Metric {q, b, a}`) — **carries `q` and `b` independently, see
  the hard rules.** `map` does coefficient base-change `Metric<S>→Metric<T>` (e.g.
  lifting an `F_2` trace form into `Metric<Nimber>` for the Arf classifier, or
  consuming `IntegralForm::clifford_metric*` from the integral-lattice bridge).
- **`algebra.rs`** (`CliffordAlgebra<S>`) — `dim()` delegates to `metric.dim()`
  (no stored field). `embed_second(v, left)` takes a left-algebra reference (not
  a bare `usize`) to derive its shift. `reverse` on general-bilinear (`a ≠ 0`)
  metrics is antisymmetric-gauge-transported in characteristic ≠ 2; characteristic
  2 still panics on nonzero `a`.
- **`multivector.rs`** (`Multivector<S>`) — `terms` field is `pub(crate)`; use the
  `terms()` accessor for external reads. `impl fmt::Display` is the canonical
  ogham renderer (Display v4, `docs/ogham/spec.md` §12).
- **`basis.rs`** — `grade_k_masks` is the one grade-k blade-mask enumerator,
  shared by `blade.rs` and `outermorphism.rs`.
- **`terms.rs`** — `add_term`/`merge` are `pub(crate)` (shared beyond this engine,
  e.g. `hopf::coproduct` reuses `add_term` instead of hand-rolling the
  insert-and-drop-zero pattern); `scale`/`wedge_terms` stay `pub(super)`.
- **`product.rs`**, **`inverse.rs`** — see their module docs; nothing here they
  don't already say.

## The GA layer

- **`versor.rs`** — the layer on top of the associative core: `versor_inverse`
  (built on the private `pure_scalar_norm` gate — `Some(v ṽ)` iff it's a pure
  invertible scalar — also reused by `spinor_norm.rs::spinor_norm`, so the two no
  longer carry duplicate copies of that check), `sandwich`, `twisted_sandwich`
  (Pin action), `reflect`, left/right_contract,
  dual/undual, grade_involution, norm2, even_part / even_subalgebra. Plus the
  product/involution suite: `clifford_conjugate`, `scalar_product ⟨ab⟩₀`,
  commutator/anticommutator (½-free, char-faithful), the regressive meet `a∨b`. Plus
  the CAYLEY transform: `cayley` and `cayley_inverse` both apply `(1−X)(1+X)⁻¹` (the
  map is an involution; `cayley_inverse` delegates to `cayley`, named for intent) —
  the exact RATIONAL bivector↔rotor map (Lie algebra ↔ Spin group, no cos/sin,
  char≠2).
- **`blade.rs`** — blade analysis: `blade_subspace {x : x∧A=0}`, `is_blade`,
  `factor_blade` (decompose a blade into grade-1 vectors). Char-faithful.
- **`outermorphism.rs`** — lift a grade-1 `LinearMap<S>` to all grades
  (`f(a∧b)=f(a)∧f(b)`); determinant as the pseudoscalar action `f(I)=det·I`; compose,
  `inverse_outermorphism`. Plus the char poly via exterior powers
  (`exterior_power_trace`, `trace`, `char_poly`). Char-faithful (the char-2
  determinant/permanent too). The lift enumerates each grade's blade masks through the
  shared `grade_k_masks` enumerator (the one grade-k blade-mask source, shared with
  `basis.rs`). `LinearMap`'s dimension and matrix data are the `n()`/`cols()`
  accessors (methods, not fields); `from_columns` is the sole constructor — even
  `identity`/`compose`/`inverse_outermorphism` route through it, so the squareness
  check is never bypassable.
- **`frobenius.rs`** — the scalar-Galois ↔ Clifford bridge: turns a
  `CoordinateCyclicGaloisExtension` (a coordinate-aware narrowing of
  `CyclicGaloisExtension`, defined here, that adds `coordinates()`) into
  `LinearMap<E::Base>` values via `galois_linear_map` / `frobenius_linear_map`, plus
  `nimber_subfield_frobenius_linear_map` for small represented nimber subfields. Its
  tests pin the outermorphism spectrum (`char_poly`, determinant, exterior traces)
  against Frobenius.
- **`hopf.rs`** — the exterior Hopf algebra: unshuffle coproduct (sign read off
  wedge) into the graded-tensor codomain `tensor_square`, counit, antipode = grade
  involution. Hopf axioms tested over Rational AND Nimber.
- **`divided_power.rs`** — the CHAR-FAITHFUL symmetric mirror of `hopf.rs`: the
  divided power algebra Γ(V) (dual of Sym), with a BINOMIAL product and
  DECONCATENATION coproduct. Binomials reduce mod char: `(γᵢ⁽¹⁾)²=2γᵢ⁽²⁾=0` in char 2
  while `γᵢ⁽²⁾≠0` — the honest Γ≠Sym (mirror of exterior `eᵢ²=0`). Standalone (own
  monomials, not the blade engine); Python exposes it via the
  `<World>DividedPowerAlgebra` / `<World>DpVector` backend family. State is
  encapsulated like the engine: read `DividedPowerAlgebra` dimension through the
  `.dim()` accessor and `DpVector`'s terms through `.terms()`, not bare fields.
- **`cga.rs`** — conformal (Cl(n+1,1) null basis: `up`/`down`/`inner`/`sphere`/
  `plane`/`point_pair`/`outer_join`, with `n_o()`/`n_inf()` null-basis accessors —
  the underlying `no`/`ninf` generator indices are private; `alg()`/`n()` expose
  the underlying algebra/dimension) + projective GA (`pga(n)` = `Cl(n,0,1)`, with the
  terminating `exp_nilpotent` motor exp). Char-0 (needs ½); surreal ∞/ε radii are
  exact. `Cga::outer_join` is the CGA IPNS wedge join (infallible) — NOT to be
  confused with `CliffordAlgebra::meet`, the fallible regressive product (see
  "things that look like bugs").
- **`spinor.rs`** — concrete left-ideal spinor matrices. Three paths, keyed on
  `characteristic()` and whether the polar form `b` is diagonal: char-0 *orthogonal*
  uses the `∏½(1+w)` idempotent search and matches the real-table classifier when it
  reaches a minimal ideal; char-0 *nonorthogonal* (`b ≠ 0`) first diagonalizes by
  congruence (tracking the transform), builds the ideal in the orthogonal basis, then
  pulls generator matrices back — recording `SpinorRep::diagonalized_metric` and
  `::orthogonal_basis_in_original`; char-0 general-bilinear metrics first drop the
  antisymmetric `a` gauge, build the ordinary `(q,b)` representation, then transport
  the idempotent and basis back to the original wedge coordinates; char-2 (rejects
  general-bilinear `a ≠ 0` and singular `b`, so any nonsingular char-2 metric,
  Nimber the main one) a separate no-half path takes blade idempotents like
  `e_i e_j` when they shrink the ideal and otherwise keeps the complete
  left-regular action. `SpinorRep` carries private fields behind
  `idempotent()`/`basis()`/`gen_matrices()`/`is_left_regular()` accessors plus the
  paired `diagonalized_metric()`/`orthogonal_basis_in_original()` (kept `Some`
  together by construction via a private `with_diagonalization` helper, never set
  independently), and `into_parts()` for callers that need to consume it (e.g. the
  Python bindings). `spinor_rep`/`SpinorRep` build the explicit matrix up to
  `MAX_EXPLICIT_SPINOR_DIM`; `lazy_spinor_rep`/`LazySpinorRep` (its `algebra` field
  likewise private, behind `algebra()`) give the sparse, unbounded-dimension
  left-regular action beyond that cap. Clifford relations hold.
- **`spinor_norm.rs`** — the RAW spinor norm `⟨v ṽ⟩₀ = ∏q(vᵢ)` (`pure_scalar_norm`,
  shared with `versor.rs::versor_inverse` as the same invertibility gate) + the
  generic `versor_grade_parity` (Dickson; `forms::dickson_of_versor` delegates
  here) + `classify_versor` → `VersorInvariants<S>` (the raw-norm + Dickson-parity
  record; Python exposes the Python class under the legacy name `VersorClass`). In
  char ≠ 2 the raw norm mod squares IS the classifying spinor-norm invariant
  (`F*/F*²`); in char 2 it is NOT — `F/℘(F)` is an additive quotient, the raw norm
  is a product, and there is no valid reduction from one to the other (see the
  module's own doc for the counterexample). The honest char-2 invariant (Wall/Dye,
  `Σ Q(vᵢ) mod ℘` over a witnessed vector factorization) is not implemented here.

## Operator vs context-method policy

Metric-free additive operations (`+`, `-`, unary `-`, `&` for exterior product) are
implemented as operators directly on `Multivector<S>` — no algebra context required.
Every metric-dependent operation (geometric product `mul`, `reverse`, contractions,
dual, spinor norm, …) is a method on `CliffordAlgebra<S>`, which provides the metric
as context. Use `a + b` / `a & b` for the metric-free ops; `alg.mul(&a, &b)` /
`alg.wedge(&a, &b)` (or the free wedge `alg.wedge(…)`) for metric-dependent ones.
Use `alg.pow(&v, k)` for repeated geometric multiplication — `^` is reserved for
scalar power (`x ^ k: u128`), not multivector power.
This mirrors the scalar layer: operators on the concrete type carry no extra context;
everything that needs context threads through the algebra value. (Python bindings:
`&` / `__and__` is wedge; `**` / `__pow__` is MV power; `^` / `__xor__` now raises the
Ogham `E_ExpSort` hint — `^` is power, the wedge is `∧`/`&`.)

## Hard rules (clifford-specific)

1. **The metric carries `q` and `b` independently — do not collapse them.**
   `q[i] = eᵢ²` (quadratic form); `b[(i,j)] = {eᵢ,eⱼ}` (polar/anticommutator, i<j).
   In char ≠ 2 they're linked; in char 2 they are NOT — `b` is alternating
   (`b(i,i)=0`) yet `q[i]` can be nonzero. Collapsing to one symmetric bilinear form
   silently makes every char-2 algebra commutative. There is a THIRD, *optional*
   field `a[(i,j)]` (i<j): the in-order/asymmetric contraction that lifts the engine
   to a general (non-symmetric) bilinear form `B` — `e_i e_j = e_i∧e_j + a_{ij}` for
   i<j; `b` stays the symmetric anticommutator. `a` empty ⇒ the ordinary Clifford
   algebra. Build with `Metric::new`, `::diagonal`, `::grassmann`, or
   `::general(q, b, a)`, never the bare struct literal (`a` is keyed i<j only).
   Both `b` and `a` in `Metric::new`/`::general` accept any `IntoIterator<Item =
   ((usize, usize), S)>` — a `BTreeMap`, a `Vec`, an empty `[]`, etc.
2. **Signs go through the scalar's own `neg()`, never a literal `-1` or a
   `characteristic()` branch.** The product emits `S::one().neg()` from the wedge
   antisymmetry. For nimbers `neg` is identity, so `-1 = 1` and char-2 sign-vanishing
   falls out for free. Hardcoding signs breaks char 2.
3. **Verify, don't claim.** The `associativity_*` tests (incl.
   `associativity_general_bilinear_form`) catch product bugs, and
   `general_product_reproduces_reduce_word_when_a_empty` pins the general engine to
   the independent oracle. Add a test before trusting a new operation.
4. **Respect the width contract.** Non-index fixed-width integer payloads are
   `u128`/`i128`. Use `usize` for basis indices and dimensions only.

## Things that look like bugs but are not (clifford layer)

- **Char-2 Clifford over an orthogonal basis is commutative.** `e0*e1 == e1*e0` when
  `b` is empty and the scalar is a nimber. Correct: `{e0,e1}=2B=0` and `-1=1`. Set an
  off-diagonal `b[(i,j)]` to get non-commutativity.
- **`versor_inverse` succeeds iff the spinor norm `v ṽ` is a scalar *and* a monomial**
  (over surreals): `1/(ω+1)` is an infinite Hahn series, so a non-monomial norm has no
  representable inverse. Use `multivector_inverse` (the general linalg solve) when
  `1+B` isn't a versor — that's why the Cayley transform calls it.
- **The `neg_one` branch in `Multivector`'s `Display` impl never fires for nimbers.**
  `neg(one)=one` in char 2, so the `coeff==one` branch catches it first. Harmless.
  (`display()` is now a thin `to_string()` alias over `fmt::Display`.)
- **`divided_power.rs` is a standalone parallel algebra, not a layer on the blade
  engine.** Γ(V) is the dual of Sym, not a view of the exterior algebra; Python
  therefore binds it as separate `DividedPowerAlgebra`/`DpVector` classes.
- **`Ordinal` is a Clifford scalar only inside its checked nim-product boundary.**
  `Scalar::mul` panics if a product escapes the source-verified Kummer tower; use
  `Ordinal::nim_mul` before constructing computations that need an explicit `Option`
  boundary.
