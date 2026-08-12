# ogdoad

[![CI](https://github.com/a9lim/ogdoad/actions/workflows/ci.yml/badge.svg)](https://github.com/a9lim/ogdoad/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/ogdoad)](https://crates.io/crates/ogdoad)
[![PyPI](https://img.shields.io/pypi/v/ogdoad)](https://pypi.org/project/ogdoad/)
[![docs.rs](https://img.shields.io/docsrs/ogdoad)](https://docs.rs/ogdoad)
[![License: AGPL v3](https://img.shields.io/badge/License-AGPL_v3-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)

Ogdoad is a pure-Rust Clifford-algebra and quadratic-forms library over exact,
finite, local, transfinite, and game-adjacent scalar worlds. The same core
supports degenerate metrics: if `q[i] = 0`, then `e_i^2 = 0`, and an all-zero
quadratic form gives the exterior algebra. Optional PyO3 bindings expose the
runtime-friendly backends without entering the Rust math core.

The organizing idea is two-dimensional:

- `src/scalar/` groups coefficient worlds by place: exact, finite,
  Archimedean/transfinite, valued, and global;
- `src/forms/` cuts across those worlds by characteristic and classification
  theory.

This exposes recurring correspondences: real Clifford periodicity and
characteristic-two Arf/Brauer--Wall theory; fields and their rings of integers;
residue and value extensions; local Springer data and global reciprocity; and
codes, lattices, discriminant forms, and Weil representations.

## Scope

The Clifford engine is generic over a commutative `Scalar` ring. Conway games
under disjunctive sum form an abelian group, not a ring, so Ogdoad is **not** a
Clifford algebra over arbitrary partizan games. Direct scalar backends include
the field-like game subclasses (nimbers, represented surreals, and surcomplex
numbers); the games pillar supplies separate game-theoretic constructions.

In characteristic two the quadratic and polar data are independent:

```text
e_i^2             = q_i
e_i e_j + e_j e_i = b_ij
```

The polar form is alternating, while `q_i` may be nonzero. This separation is a
hard invariant of the engine. An optional upper-triangular `a_ij` records the
in-order contraction for a general bilinear metric.

Other important boundaries:

- `Nimber(u128)` is the finite field `F_{2^128}`, not the algebraic closure of
  `F_2`.
- `Surreal` is a finite-support Hahn/CNF representation, not every surreal
  number or every infinite series.
- `Qp`, `Qq`, `Laurent`, `Ramified`, `Gauss`, `Adele`, and runtime `LocalQp`
  are capped-precision models; their documented contracts differ from exact
  fields.
- `Ordinal::nim_mul` returns `None` when a product escapes the supported Kummer
  tower; its `Scalar::mul` wrapper panics if a caller ignores that boundary.
- Finite computation and source-pinned tables are evidence, not universal
  proofs. The exact open boundary is in [`docs/OPEN.md`](docs/OPEN.md).

## Architecture

| path | role |
| --- | --- |
| `src/scalar/` | `Scalar`, exactness/valuation/extension traits, and coefficient backends |
| `src/clifford/` | metrics, blades, multivectors, geometric products, outermorphisms, versors, spinors, CGA, Hopf and divided-power structures |
| `src/forms/` | characteristic-specific classifiers, Witt and Brauer groups, Springer theory, local--global arithmetic, and integral forms |
| `src/forms/integral/` | lattices, discriminant forms, genus and mass, codes, theta/modular forms, Kneser neighbors, and Weyl versors |
| `src/games/` | impartial, partizan, misere, and loopy games; thermography; Hackenbush; lexicodes; checked game-exterior data |
| `src/py/` | optional per-backend PyO3 bindings |
| `src/linalg/` | crate-private shared/unit-pivot linear algebra |
| `grundy/` | unpublished expression-language workspace member built over Ogdoad's public API |
| `formal/` | standalone Lean 4 project for load-bearing proof ingredients and explicit open propositions |
| `writeups/` | the current mathematical papers and their BibTeX bibliographies |

Each source pillar has a short `AGENTS.md` recording its invariants and file
map. [`docs/README.md`](docs/README.md) indexes the current documentation.

## Implemented mathematical surface

The scalar layer includes:

- exact `Integer`, `Rational`, `Fp`, `Fpn`, `Nimber`, `RationalFunction`, and
  `Poly` arithmetic when the coefficient backend is exact;
- finite-support `Surreal`, `Omnific`, `Surcomplex`, and staged ordinal nimbers;
- `Zp`, `Qp`, `WittVec`, `Qq`, Laurent, ramified, and Gauss valuation models;
- adelic and function-field global interfaces;
- finite-field Galois operations, residue/integrality traits, Newton polygons,
  and dual tropical semirings.

The forms layer includes characteristic-zero, odd-characteristic, and
characteristic-two classification; Arf, Brown, Witt, Brauer, and Brauer--Wall
invariants; Hermitian and symplectic forms; Springer decompositions; rational
and function-field local--global arithmetic; and an integral wing covering
codes, lattices, discriminant forms, Weil matrices, genus symbols, mass
formulae, Kneser neighbors, theta series, Niemeier data, and Clifford/Weyl
bridges.

The games layer includes normal-play Grundy evaluation, misere quotients,
finite loopy impartial and partizan graphs, short partizan games, thermography
and Norton operations, coin turning, Hackenbush, lexicodes, and the exterior
algebra of the game group.

## Quickstart

Rust:

```sh
cargo test --workspace
cargo run --example tour
```

Python 3.9 or newer:

```sh
python -m maturin build --profile dev -i python
python -m pip install --force-reinstall --no-deps target/wheels/ogdoad-*.whl
python demo.py
```

```python
import ogdoad as og

# Characteristic-two Clifford data: q and b are independent.
A = og.NimberAlgebra(q=[og.Nimber(2), og.Nimber(3)], b={(0, 1): 1})
e0, e1 = A.gen(0), A.gen(1)
assert e0 * e1 + e1 * e0 == A.scalar(og.Nimber(1))

# Exact represented surreal monomials.
S = og.SurrealAlgebra(q=[og.omega(), og.epsilon()])
assert (S.gen(0) * S.gen(1)) ** 2 == S.scalar(og.Surreal.from_int(-1))

# One Hackenbush object, different evaluators.
blue, green = og.Color.blue(), og.Color.green()
og.Hackenbush.string([blue, blue]).value()
og.Hackenbush.string([green, green]).grundy()
```

Python binds plain runtime types and a documented fixed dispatch slice of the
const-generic families. Extending that slice is deliberate; mixing scalar
worlds inside one algebra remains a `TypeError`.

## Research status

Two mathematical fronts remain open:

1. the arbitrary-graph isolated-dummy FIFO linking conjecture;
2. the universal `0/1/4` rule for finite excess in transfinite nim
   multiplication.

Their exact statements, proved reductions, counterexample boundaries, and
verification surfaces are in [`docs/OPEN.md`](docs/OPEN.md). The active papers
are:

- [`goldarf.tex`](writeups/goldarf.tex): quadratic refinements in normal play,
  the observation bound, Brown selectors, and the ambient game-exterior
  obstruction;
- [`linking_affine.tex`](writeups/linking_affine.tex): the open FIFO linking
  problem;
- [`excess.tex`](writeups/excess.tex): the open transfinite nim-excess problem;
- [`thermo_newton.tex`](writeups/thermo_newton.tex): Norton thermic laws and the
  separation from Newton-polygon tropicalization;
- [`transfinite_arf.tex`](writeups/transfinite_arf.tex): quadratic forms over
  perfect Artin--Schreier-surjective characteristic-two fields and full
  `On_2`.

Lean checks independent algebraic and combinatorial ingredients. It does not
replace the paper-level synthesis with a single end-to-end arena theorem; see
[`formal/README.md`](formal/README.md).

## Verification

```sh
cargo fmt --all --check
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --workspace
(cd formal && lake build --wfail)
npm ci
python scripts/check_writeups.py
```

The last command compiles each paper, converts it with Pandoc to standalone
HTML, and renders every math fragment with the pinned KaTeX version.

## Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md). New mathematical claims must be
identified as standard/cited, implemented and tested, proved in the project, or
open. The public API uses `u128`/`i128` for fixed-width mathematical payloads
and `usize` only for dimensions and indices.

Ogdoad is licensed under AGPL-3.0-or-later.
