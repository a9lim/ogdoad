# ogdoad

[![CI](https://github.com/a9lim/ogdoad/actions/workflows/ci.yml/badge.svg)](https://github.com/a9lim/ogdoad/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/ogdoad)](https://crates.io/crates/ogdoad)
[![PyPI](https://img.shields.io/pypi/v/ogdoad)](https://pypi.org/project/ogdoad/)
[![docs.rs](https://img.shields.io/docsrs/ogdoad)](https://docs.rs/ogdoad)
[![License: AGPL v3](https://img.shields.io/badge/License-AGPL_v3-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)

Ogdoad is a pure-Rust library for Clifford algebras, quadratic forms, and
related arithmetic over exact, finite, local, transfinite, and game-adjacent
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
| `src/forms/` | quadratic-form classification, Witt/Brauer theory, Springer and local--global arithmetic |
| `src/forms/integral/` | lattices, discriminant forms, codes, theta series, genera, neighbors, and Weyl bridges |
| `src/games/` | impartial, partizan, misere, loopy, thermographic, Hackenbush, and game-exterior constructions |
| `src/py/` | optional per-backend PyO3 bindings; scalar worlds never mix at runtime |
| `src/linalg/` | crate-private shared linear algebra |
| `grundy/` | unpublished expression-language workspace crate using only Ogdoad's public API |
| `formal/` | separately pinned Lean 4 development |
| `writeups/` | current mathematical papers and BibTeX sources |

Public pillars re-export their children shallowly. Each source pillar has an
`AGENTS.md` with its local invariants; [`docs/README.md`](docs/README.md)
indexes the current project documentation.

## Use

Rust:

```sh
cargo add ogdoad
cargo run --example tour
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
```

The Python layer monomorphizes a documented slice of the Rust backends. It
does not provide a runtime-tagged any-scalar algebra.

## Mathematical status

The papers under `writeups/` form one current research suite:

| paper | result |
| --- | --- |
| `transfinite_arf.tex` | classification over perfect Artin--Schreier-surjective characteristic-two fields and its full-nimber specialization |
| `goldarf.tex` | quadratic-refinement realization in normal play, Gold specialization, Brown selector, and game-exterior obstruction |
| `thermo_newton.tex` | thermic regrading under Norton multiplication and its separation from Newton tropicalization |
| `linking_affine.tex` | proved reductions and exact remaining obstruction for isolated-dummy FIFO linking |
| `excess.tex` | four-arm reduction and exact remaining selected-order problem for transfinite nim excess |

The last two universal claims remain open. Their concise statements and sharp
proof boundaries are in [`docs/OPEN.md`](docs/OPEN.md). Lean checks named
ingredients and several end-to-end finite constructions, not the open
propositions; see [`formal/README.md`](formal/README.md).

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

[`docs/VERIFY.md`](docs/VERIFY.md) records the optional Python-binding gates,
exactness contracts, certificate boundary, and claim classes. Contributions
should identify mathematical claims as standard/cited, implemented and tested,
proved here, or open; see [`CONTRIBUTING.md`](CONTRIBUTING.md).

Ogdoad is licensed under AGPL-3.0-or-later.
