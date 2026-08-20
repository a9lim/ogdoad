# ogdoad

[![CI](https://github.com/a9lim/ogdoad/actions/workflows/ci.yml/badge.svg)](https://github.com/a9lim/ogdoad/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/ogdoad)](https://crates.io/crates/ogdoad)
[![PyPI](https://img.shields.io/pypi/v/ogdoad)](https://pypi.org/project/ogdoad/)
[![docs.rs](https://img.shields.io/docsrs/ogdoad)](https://docs.rs/ogdoad)
[![License: AGPL v3](https://img.shields.io/badge/License-AGPL_v3-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)

Ogdoad is a pure-Rust library for Clifford and Weyl algebras, quadratic forms,
and related arithmetic over exact, finite, local, transfinite, and game-adjacent
coefficient systems. Optional PyO3 bindings expose selected concrete backends
without entering the generic math core.

The library supports degenerate metrics. In characteristic two it keeps the
quadratic and polar data independent:

```text
e_i^2             = q_i
e_i e_j + e_j e_i = b_ij
```

An optional upper-triangular `a_ij` records ordered contraction for a general
bilinear metric. Generic product code obtains signs through `Scalar::neg` and
does not special-case the characteristic.

## Scope

A Clifford scalar is a commutative ring. Arbitrary partizan games form only an
abelian group under disjunctive sum, so Ogdoad is not a Clifford algebra over
all games. The scalar pillar includes field-like game subclasses such as finite
nimbers and represented surcomplex numbers; genuinely game-theoretic
constructions live in the separate games pillar.

Representation limits are part of the API:

- `Nimber(u128)` is `F_(2^128)`, not the algebraic closure of `F_2`.
- `Surreal` stores finite-support Conway-normal-form expressions, not arbitrary
  surreal series.
- valued and local models have explicit precision caps and do not silently
  claim exact field laws outside them.
- `Ordinal::nim_mul`, `nim_pow`, `checked_inv`, and `checked_sqrt` preserve the
  supported Kummer-tower boundary through `Option`; the `Scalar` multiplication
  wrapper panics if that checked boundary is ignored.
- fixed-width mathematical payloads use `u128` or `i128`; `usize` is reserved
  for dimensions, indices, and ABI hooks.

## Architecture

| path | role |
| --- | --- |
| `src/scalar/` | coefficient traits and exact, finite, valued, global, surreal, and ordinal backends |
| `src/clifford/` | metrics, blades, multivectors, products, versors, spinors, and geometric-algebra constructions |
| `src/weyl/` | alternating commutator forms, budgeted sparse PBW products, Darboux tensor coordinates, typed canonical transformations, symbols/Poisson brackets, and rank-`n` polynomial actions |
| `src/forms/` | quadratic-form classification, Clifford centers, Witt/Brauer and low Milnor-symbol theory, Springer and local--global arithmetic |
| `src/forms/integral/` | lattices, discriminant forms, codes, theta series, genera, neighbors, and Weyl bridges |
| `src/games/` | impartial, partizan, misere, loopy, thermographic, Witt--FIFO/Brown, octal-certificate, Hackenbush, and game-exterior constructions |
| `src/py/` | optional per-backend PyO3 bindings; scalar worlds never mix at runtime |
| `src/linalg/` | crate-private shared linear algebra |
| `grundy/` | unpublished expression-language workspace crate using only Ogdoad's public API |
| `formal/` | separately pinned Lean 4 development |
| `writeups/` | current mathematical papers and BibTeX sources |

Public pillars re-export their children shallowly. Each source pillar has an
`AGENTS.md` with its local invariants; [`docs/README.md`](docs/README.md)
indexes the current project documentation.

The Weyl pillar constructs
`T(V)/(z_i*z_j - z_j*z_i - omega_ij)` from an alternating scalar-valued
commutator form. `WeylAlgebra::standard(n)` uses PBW order
`x_0,...,x_(n-1),d_0,...,d_(n-1)` with `[d_i,x_j] = delta_ij`. Elements have
finite sparse support, while the algebra remains infinite-dimensional. In
positive characteristic the enlarged center is retained explicitly; the
ordinary polynomial differential action is therefore not claimed faithful.
Materialized products and actions accept explicit term/work budgets, and the
general normalizer groups contractions so its work follows the available
contraction degree rather than a potentially enormous appended exponent.
Over exact fields, certified Darboux coordinates expose the standard Weyl
factor and central radical polynomial factor. Affine homomorphisms, standard
automorphisms, formal adjoint, Bernstein/differential-order symbols, the
constant Poisson bracket, and the polynomial `hbar` deformation preserve their
homomorphism, characteristic, and finite-support boundaries explicitly.

## Use

Rust:

```sh
cargo add ogdoad
cargo run --example tour
cargo run --example weyl
```

Python 3.9 or newer:

```sh
python -m maturin build --profile dev -i python
python -m pip install --force-reinstall --no-deps target/wheels/ogdoad-*.whl
```

```python
import ogdoad as og

# q and b are independent in characteristic two.
A = og.NimberAlgebra(q=[og.Nimber(2), og.Nimber(3)], b={(0, 1): 1})
e0, e1 = A.gen(0), A.gen(1)
assert e0 * e1 + e1 * e0 == A.scalar(og.Nimber(1))

# Exact finite-support surreal monomials.
S = og.SurrealAlgebra(q=[og.omega(), og.epsilon()])
assert (S.gen(0) * S.gen(1)) ** 2 == S.scalar(og.Surreal.from_int(-1))

# A Hermitian form restricts to the ordinary quadratic form q(v)=h(v,v)
# over the involution-fixed field; dimension doubles.
H = og.HermitianForm.diagonal([1, -1])
Q = H.restrict_scalars()
assert Q.dim == 4 and og.surreal_signature(Q) == (2, 2, 0)

# Checked game constructors preserve their proof and validation boundaries.
arena = og.WittFifoArena(diagonal=[True], polar=[0], input=1)
assert arena.quadratic_value and arena.grundy(state_budget=100_000) != 0

selector = og.BrownSelector(q4=[3], brown_polar=[0], input=1)
outcome = selector.outcome_class(state_budget_per_follower=100_000)
assert og.BrownSelector.decode_outcome(outcome) == selector.residue

code = og.OctalCode([2])
certificate = og.GuySmithCertificate.compute(code, 1, 2, term_budget=16)
assert certificate.heap_grundy(10**30) == 1
```

The Python layer monomorphizes a documented slice of the Rust backends. It
does not provide a runtime-tagged any-scalar algebra. Its typed report surface
includes finite quadratic modules and Nikulin criteria, extraspecial and
Heisenberg--Weil objects, function-field Brauer--Wall classes, Niemeier data,
finite-field Witt decompositions and numeric-invariant reports,
characteristic-two additive spinor norms and symmetry certificates, lexicode
turning games, conformal-algebra accessors, represented ordinal finite-subfield
degrees, checked Witt--FIFO and Brown constructors, Hermitian restriction to
typed ordinary quadratic backends, and sealed Guy--Smith periodicity
certificates. Python
`repr` delegates to canonical Rust rendering where the core provides it.

## Mathematical status

The papers under `writeups/` form one current research suite:

| paper | result |
| --- | --- |
| `transfinite_arf.tex` | classification over perfect Artin--Schreier-surjective characteristic-two fields and its full-nimber specialization |
| `goldarf.tex` | quadratic-refinement realization in normal play, Gold specialization, Brown selector, and game-exterior obstruction |
| `witt_realization.tex` | quadratic Witt coordinates over `F_2(t)`, finite impartial realization, explicit ramified naturality, and finite-static and singular no-go theorems |
| `thermo_newton.tex` | thermic regrading under Norton multiplication and its separation from Newton tropicalization |
| `semiring_stability.tex` | stable quadratic-pair classification over Hessenberg and supertropical semirings, the universal scalar-extension quotient, and the thermograph wall obstruction |
| `linking_affine.tex` | proved reductions and exact remaining obstruction for isolated-dummy FIFO linking |
| `excess.tex` | exact four-arm selected-order reduction, proved arithmetic boundaries, and authoritative open status of the transfinite nim-excess `0/1/4` rule |
| `nim_fast_multiplication.tex` | quasi-linear canonical-word multiplication via explicit affine transforms to a primitive Artin--Schreier tower |
| `misere_natural_realization.tex` | exact octal trace calculus, finite-exception heap normal form, realization of every tame finite quotient, and exact misere Grundy quotients through heap 18 |

The unresolved universal claims and their sharp proof boundaries are in
[`docs/OPEN.md`](docs/OPEN.md). Lean checks named algebraic components and
end-to-end finite constructions including the literal Gold--Arf root; cited
bridges and the open propositions remain outside that boundary. See
[`formal/README.md`](formal/README.md) for the theorem map.

## Verification

The default gate covers the published Ogdoad core:

```sh
cargo fmt -p ogdoad --check
cargo test -p ogdoad
cargo clippy -p ogdoad --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps -p ogdoad
```

The unpublished `grundy/` language, standalone `formal/` Lean development,
Python bindings, and papers have explicit opt-in gates in
[`docs/VERIFY.md`](docs/VERIFY.md). Contributions should identify mathematical
claims as standard/cited, implemented and tested, proved here, or open; see
[`CONTRIBUTING.md`](CONTRIBUTING.md).

Ogdoad is licensed under AGPL-3.0-or-later.
