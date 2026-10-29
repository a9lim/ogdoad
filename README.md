# ogdoad

[![CI](https://github.com/a9lim/ogdoad/actions/workflows/ci.yml/badge.svg)](https://github.com/a9lim/ogdoad/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/ogdoad)](https://crates.io/crates/ogdoad)
[![PyPI](https://img.shields.io/pypi/v/ogdoad)](https://pypi.org/project/ogdoad/)
[![docs.rs](https://img.shields.io/docsrs/ogdoad)](https://docs.rs/ogdoad)
[![License: AGPL v3](https://img.shields.io/badge/License-AGPL_v3-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)

Ogdoad is a pure-Rust library for Clifford and Weyl algebras, quadratic forms,
and combinatorial games over exact, finite, local, and transfinite coefficient
systems. Optional PyO3 bindings expose selected concrete backends without
entering the generic math core.

Metrics may be degenerate, and characteristic two is first-class: the
quadratic and polar data stay independent,

```text
e_i^2             = q_i
e_i e_j + e_j e_i = b_ij
```

and an optional upper-triangular `a_ij` records the ordered contraction of a
general bilinear metric. Generic product code takes signs from `Scalar::neg`
and never branches on the characteristic.

## Scope and non-claims

A Clifford scalar is a commutative ring. Partizan games form only an abelian
group under disjunctive sum, so Ogdoad is not a Clifford algebra over all
games. Field-like game subclasses, such as finite nimbers and represented
surcomplex numbers, live in the scalar pillar; genuinely game-theoretic
constructions live in the games pillar.

Representation limits are part of the API:

- `Nimber(u128)` is `F_(2^128)`, not the algebraic closure of `F_2`.
- `Surreal` stores finite-support Conway-normal-form expressions, not
  arbitrary surreal series.
- Valued and local models have explicit precision caps and claim exact field
  laws only inside them.
- `Ordinal::nim_mul`, `nim_pow`, `checked_inv`, and `checked_sqrt` return
  `None` when a computation would need a Kummer row beyond the supported table
  or leave the represented segment; the `Scalar` multiplication wrapper panics
  if that boundary is ignored.
- Weyl algebras are infinite-dimensional with finite-support elements. In
  positive characteristic their enlarged centre is kept explicit, so the
  polynomial differential action is not claimed faithful.
- `Integer` and `Rational` panic on `i128` overflow rather than wrapping;
  `Rational::checked_add` and `checked_mul` return `None` instead.
- Fixed-width algebraic values and group orders use `u128` or `i128`;
  `usize` is for dimensions, indices, in-memory counts, and ABI hooks.

## Architecture

| path | role |
| --- | --- |
| `src/scalar/` | coefficient traits and exact, finite, valued, global, surreal, and ordinal backends |
| `src/clifford/` | metrics, blades, multivectors, products, versors, spinors, and geometric-algebra constructions |
| `src/weyl/` | alternating commutator forms, budgeted PBW products, Darboux coordinates, canonical transformations, symbols, centres, finite central fibres, and `p`-symbols |
| `src/forms/` | quadratic-form classification, characteristic-two Arf/Brown/Dickson theory, Clifford centers, Witt/Brauer and low Milnor symbols, Springer and local--global arithmetic, Hermitian and symplectic forms |
| `src/forms/integral/` | lattices, discriminant forms, codes, theta series, genera, neighbors, and Weyl-group reflections as Pin versors |
| `src/games/` | impartial, partizan, misère, loopy, thermographic, Witt--FIFO/Brown, octal-certificate, Hackenbush, and game-exterior constructions |
| `src/py/` | optional per-backend PyO3 bindings; scalar worlds never mix at runtime |
| `src/linalg/` | crate-private shared linear algebra |
| `grundy/` | unpublished typed ruleset language built on the public API |
| `formal/` | separately pinned Lean 4 development |
| `writeups/` | mathematical papers and BibTeX sources |

Public pillars re-export their children shallowly. Each source pillar carries
an `AGENTS.md` with its module map and local invariants, and
[`docs/README.md`](docs/README.md) indexes the project documentation.

The Weyl pillar builds `T(V)/(z_i z_j - z_j z_i - omega_ij)` from an
alternating scalar-valued form. `WeylAlgebra::standard(n)` orders generators
`x_0,...,x_(n-1),d_0,...,d_(n-1)` with `[d_i,x_j] = delta_ij`. Every
expanding operation has a variant with explicit term and work budgets, and
finite fibres require explicit size caps.
Over exact fields it certifies Darboux coordinates; in characteristic `p` it
certifies the centre, reduces to bounded central fibres, identifies
characteristic-two fibres with Clifford algebras, and gives executable
`p`-symbol presentations whose Brauer interpretation remains cited.

`grundy/` is a typed language for combinatorial games over Ogdoad: positions
are data, moves are functions, and every answer states its scope — exact,
a verified claim, or a sampled `Bounded` value. It is a workspace member with
`publish = false`; see [`grundy/docs/`](grundy/docs/README.md).

## Use

As a dependency:

```sh
cargo add ogdoad
python -m pip install ogdoad    # Python 3.9 or newer
```

The [API documentation](https://docs.rs/ogdoad) opens each pillar with
runnable examples, including the headline constructions of the papers below.
From a checkout, the examples tour the library and its research
instruments:

```sh
cargo run --example tour        # verified core
cargo run --example weyl        # Weyl algebras, centres, p-symbols
cargo run --example tropical    # thermography as tropical arithmetic
cargo run --release --example octal_hunt
```

`bent_route`, `interactive_kernel`, `loopy_quadric`, and `misere_quotient`
are further bounded experiments. To build the Python extension from source:

```sh
python -m maturin build --profile dev -i python
python -m pip install --force-reinstall --no-deps target/wheels/ogdoad-*.whl
```

A taste of the Python surface:

```python
import ogdoad as og

# q and b are independent in characteristic two.
A = og.NimberAlgebra(q=[og.Nimber(2), og.Nimber(3)], b={(0, 1): 1})
e0, e1 = A.gen(0), A.gen(1)

# Weyl backends remain monomorphic too; budgets stay explicit.
W = og.NimberWeylAlgebra(1)
x, d = W.x(0), W.d(0)
assert W.commutator(d, x) == W.one()
P = W.psymbol([og.Nimber(2), og.Nimber(3)], 4)
assert P.p_residue(x * d) == og.Nimber(1)
assert P.cyclic_factor(0, 4) == (og.Nimber(3), og.Nimber(1))

# Fp3 supplies the odd-characteristic split and residue/trace certificates.
W3 = og.Fp3WeylAlgebra(1)
P3 = W3.psymbol([og.Fp3(2), og.Fp3(1)], 9)
assert P3.certify_split([og.Fp3(2), og.Fp3(1)], 9, 100, 1_000_000)
assert P3.split_trace_matches_residue(
    W3.monomial([2, 2], 1), [og.Fp3(2), og.Fp3(1)],
    9, 100, 1_000_000,
)
assert W.clifford_fiber_products_agree(
    d * x, x + d, [og.Nimber(2), og.Nimber(3)], 4,
    max_terms=32, max_steps=1_000,
)
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

The Python layer monomorphizes a documented slice of the Rust backends and has
no runtime-tagged any-scalar algebra: cross-world arithmetic raises
`TypeError`, and cross-world equality compares unequal. Beyond
the algebras above it exposes typed reports for finite quadratic modules and
Nikulin criteria, extraspecial and Heisenberg--Weil objects, function-field
Brauer--Wall classes, Niemeier data, finite-field Witt decompositions,
characteristic-two spinor norms and symmetry certificates, lexicode turning
games, conformal algebras, ordinal finite-subfield degrees, Witt--FIFO and
Brown constructors, Hermitian restriction, and Guy--Smith certificates.
Most Python `repr`s delegate to the canonical Rust rendering.

## Mathematical status

The papers under `writeups/` form one research suite:

| paper | result |
| --- | --- |
| `transfinite_arf.tex` | classification over perfect Artin--Schreier-surjective characteristic-two fields and its full-nimber specialization |
| `goldarf.tex` | quadratic-refinement realization in normal play, Gold specialization, Brown selector, and game-exterior obstruction |
| `witt_realization.tex` | quadratic Witt coordinates over `F_2(t)`, finite impartial realization, explicit ramified naturality, and finite-static and singular no-go theorems |
| `thermo_newton.tex` | thermic regrading under Norton multiplication and its separation from Newton tropicalization |
| `semiring_stability.tex` | stable quadratic-pair classification over Hessenberg and supertropical semirings, the universal scalar-extension quotient, and the thermograph wall obstruction |
| `nim_fast_multiplication.tex` | quasi-linear canonical-word nim multiplication via explicit affine transforms to a primitive Artin--Schreier tower |
| `linking_affine.tex` | exact affine reductions and the remaining causal step for isolated-dummy FIFO linking |
| `excess.tex` | disproof of the piecewise nim-excess `0/1/4` rule, an infinite counterexample family, and remaining boundedness and selected-order questions |
| `misere_natural_realization.tex` | exact octal traces and periodic code compression, split and subtraction classifications, and exact misère Grundy quotients through heap 18 |

The last three papers carry the live open problems; their statements and
sharp proof boundaries are in [`docs/OPEN.md`](docs/OPEN.md). Lean checks
named algebraic components and end-to-end finite constructions, including the
literal Gold--Arf root; cited bridges and the open propositions stay outside
that boundary. See [`formal/README.md`](formal/README.md) for the theorem map.

## Verification

The default gate covers the published core:

```sh
cargo fmt -p ogdoad --check
cargo test -p ogdoad
cargo clippy -p ogdoad --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps -p ogdoad
```

`grundy/`, the Python bindings, the Lean development, and the papers have
opt-in gates in [`docs/VERIFY.md`](docs/VERIFY.md). Contributions label each
mathematical claim as standard/cited, implemented and tested, proved here, or
open; see [`CONTRIBUTING.md`](CONTRIBUTING.md).

Ogdoad is licensed under AGPL-3.0-or-later.
