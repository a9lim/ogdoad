# pleroma

`pleroma` is a Rust research playground for Clifford algebras, quadratic forms,
and combinatorial-game arithmetic, with optional Python bindings.

The central constraint is mathematical, not just architectural: Conway games
under disjunctive sum form an abelian group, not a scalar ring. Conway
multiplication is defined on the number/nimber sides, not on arbitrary games.
So this project does **not** build Clifford algebras over all games. It builds a
generic Clifford engine over commutative scalar backends that are adjacent to
game theory:

| backend | implemented object | Clifford/form role |
| --- | --- | --- |
| `Nimber(u128)` | the finite nim-field `F_{2^128}` | characteristic-2 Clifford examples, Arf/radical data, finite-field experiments |
| `Surreal` | finite-support Hahn/CNF surreals with rational coefficients | a represented subdomain of real-closed Clifford theory, including infinite/infinitesimal monomials |
| `Surcomplex<Surreal>` | adjoining `i` to the implemented surreal backend | represented subdomain of complex Clifford theory |
| `Rational`, `Integer`, `Omnific`, `Fp`, `Fpn`, `Zp`, `Qp`, `Qq`, `WittVec`, `Laurent`, `Ramified`, `Gauss`, `Adele` | comparison rings/fields and precision models | form invariants, local/global tests, exterior/game-group constructions |

"With nilpotents" means the quadratic form may be degenerate. If `Q(e_i) = 0`,
then `e_i^2 = 0`; the all-zero metric is the exterior/Grassmann algebra.

## The Char-2 Point

In characteristic 2, the quadratic form and its polar form carry different
data. The engine stores

```text
e_i^2 = q_i
e_i e_j + e_j e_i = b_ij
```

separately. For nimbers, `-1 = 1`, so an orthogonal basis with `b = 0` gives a
commutative Clifford product. A nonzero off-diagonal `b[(i,j)]` is what makes a
characteristic-2 example noncommutative.

## Quickstart

Requires Rust and Python >= 3.9.

```sh
python3 -m venv .venv
.venv/bin/pip install maturin
VIRTUAL_ENV=.venv .venv/bin/maturin develop
.venv/bin/python demo.py
```

```python
import pleroma as pl

# characteristic-2 nimber Clifford, non-orthogonal => noncommutative
A = pl.NimberAlgebra(q=[pl.Nimber(2), pl.Nimber(3)], b={(0, 1): 1})
e0, e1 = A.gen(0), A.gen(1)
e0 * e1 + e1 * e0      # *1
e0 ** 2                # *2

# surreal metric: infinite and infinitesimal squares
S = pl.SurrealAlgebra(q=[pl.omega(), pl.epsilon()])
(S.gen(0) * S.gen(1)) ** 2     # -1

# finite-support surreal arithmetic
w = pl.omega()
(w + 1) * (w - 1)              # ω^2 - 1
pl.omega_pow(pl.omega())       # ω^(ω)
```

Python exposes the main Clifford backends (`NimberAlgebra`, `SurrealAlgebra`,
`SurcomplexAlgebra`, `IntegerAlgebra`, `OmnificAlgebra`), scalar classes
(`Nimber`, `Surreal`, `Surcomplex`, `Integer`, `Omnific`, `Ordinal`), form
helpers (`arf_invariant`, `classify_surreal`, `FiniteFieldForm`, `hilbert_symbol_qp`,
`is_isotropic_q`, `bw_class_*`, ...), and game helpers (`Game`, `GameExterior`,
`Hackenbush`, `nim_mul_mex`, `grundy_graph`). `Ordinal` is currently exposed as
a scalar object, not as a Clifford-algebra backend in Python.

Run the Rust tour without Python:

```sh
cargo run --example tour
```

## Layout

- `src/scalar/` defines the `Scalar` trait and the coefficient worlds.
  The place-organized table includes exact (`Rational`, `Integer`), big
  (`Surreal`, `Omnific`, `Ordinal`), small/local (`Zp`, `Qp`, `Qq`), finite-field
  (`Fp`, `Fpn`, `Nimber`, `WittVec`), functor (`Surcomplex`, `Laurent`,
  `Ramified`, `Gauss`), and global (`Adele`, `LocalQp`) modules. Several local
  and global backends are finite-precision models, not exact scalar fields.
- `src/clifford/` contains the generic multivector engine, geometric product,
  inverse, versor operations, outermorphisms, Hopf/divided-power structures,
  conformal/projective GA, and spinor helpers.
- `src/forms/` contains quadratic-form classifiers and invariants: characteristic
  0, odd characteristic, characteristic 2, Witt/Brauer-Wall utilities, Springer
  decompositions, symplectic/hermitian forms, and the adelic local-global layer
  over rational forms.
- `src/games/` contains normal-play and misere impartial game code, short
  partizan games, thermography/atomic weight, Hackenbush, loopy finite graphs,
  and the exterior algebra of the game group over `Integer`.
- `src/py/` contains the optional PyO3 bindings behind the `python` feature.

## Research Thread

The narrow mathematical thread in `NOTES.md` and `writeup/pleroma.tex` is not a
claim of a new Clifford classification theorem. It is a draft investigation of
game-built quadratic forms in the nimber backend:

1. Turning-Corners games realize nim multiplication.
2. Frobenius squaring and traces are built from nim multiplication and XOR.
3. Gold-style trace forms `Tr(lambda * x^(1+2^a))` are therefore expressible from
   game-value operations.
4. The Arf invariant gives the standard zero-count bias for a quadratic zero set.
5. The open question is whether a natural game rule has such a zero set as its
   P-positions. Current probes include normal-play, misere quotient, interactive,
   loopy, and bent-form searches; they narrow the target but do not solve it.

## Status And Limits

This is active research code with tests, examples, and experiments. Treat green
tests as regression evidence, not as a proof of the mathematical program.

Useful checks:

```sh
cargo fmt --check
cargo test
cargo check --features python
cargo check --examples
git diff --check
```

Important scope boundaries:

- `Nimber(u128)` is exactly `F_{2^128}`. It contains nim subfields whose degrees
  divide 128; it is not the proper-class field of all nimbers and not all finite
  characteristic-2 fields.
- `Ordinal` nim-addition is implemented generally on the represented CNF terms.
  Nim-multiplication is implemented below `ω^ω` through the current degree-3
  tower; ordinals with infinite CNF exponents return `None`.
- `Surreal` uses finite support and rational coefficients. Non-monomial inverses
  are generally infinite Hahn series and are not represented by `inv()`.
- `Qp`, `Qq`, `Laurent`, `Gauss`, and `Adele` are finite-precision models in the
  current implementation. They are useful for local/global form experiments, but
  they are not exact infinite-memory local fields.
- The Gold/Arf game thread is conditional: if a game has P-set `{Q = 0}`, Arf
  predicts the win-bias. The repo has not found a non-tautological natural game
  with that P-set.
