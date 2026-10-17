# Contributing

Thanks for the interest. Ogdoad is a research codebase, so the bar is
correctness first: a new operation lands with a test that pins it to an
independent oracle, not on a "looks right" basis.

## Read the working notes first

[`AGENTS.md`](AGENTS.md) is the map of the five public pillars (`scalar/`,
`clifford/`, `forms/`, `games/`, `weyl/`), the PyO3 bindings, the `grundy/`
language, and the Lean project. Each pillar has a short local `AGENTS.md`
with its module map and invariants. Read [`docs/OPEN.md`](docs/OPEN.md)
before changing a research claim or an open-problem probe.

## The invariants everything rests on

The full list lives in `AGENTS.md` and the pillar notes; these are the ones a
first contribution most often trips over.

- **The math core is pure Rust and generic over `Scalar`.** PyO3 lives behind
  the `python` feature: never `use pyo3` outside `src/py/`, never make it a
  default dependency. That is what keeps `cargo test` from linking libpython.
- **A metric keeps `q`, `b`, and the optional `a` distinct.** In
  characteristic two the polar form `b` is alternating while `q[i]` can be
  nonzero; collapsing them makes every characteristic-two algebra the wrong
  object. Build metrics through `Metric::new`, `diagonal`, `grassmann`, or
  `general`.
- **Generic signs go through `Scalar::neg`,** never a literal `-1` or a
  characteristic branch. For nimbers `neg` is the identity, so
  characteristic-two sign vanishing falls out for free.
- **Weyl monomials are checked PBW multidegrees, not Clifford blades.**
  Positive-characteristic centres and the non-faithful polynomial action stay
  explicit.
- **Surreal arithmetic recurses only on exponents,** which are strictly
  simpler than the number; that is the whole termination argument.
- **Representation limits are API.** Precision caps, finite representations,
  and checked boundaries return exactly what they document; no silent
  defaults.
- **Verify, don't claim.** Add a focused test before trusting a new operation.

## Test plan

The normal gate is the published core:

```sh
cargo fmt -p ogdoad --check
cargo test -p ogdoad
cargo clippy -p ogdoad --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps -p ogdoad
```

Changes to `grundy/`, `src/py/` (or a core API it calls), Lean, or a paper
have their own gates in [`docs/VERIFY.md`](docs/VERIFY.md). `cargo test` does
**not** compile the `python` feature, so binding changes always need the
Python gate. After touching `clifford/`, `scalar/big/surreal/`, or their
bindings, also rebuild the extension and run the Python tour, which checks
canonical displays such as `e0∧e1`, `*n`, and CNF:

```sh
python -m maturin build --profile dev -i python
python -m pip install --force-reinstall --no-deps target/wheels/ogdoad-*.whl
python demo.py
```

## Claim levels

When you change prose, comments, examples, or a paper, separate **standard
and cited**, **implemented and tested**, **proved here**, and **open**
claims. A new mathematical assertion needs a proof, a source, or an explicit
open label.

## Releasing

The version in `Cargo.toml` is the single source of truth; `pyproject.toml`
and the maturin build inherit it. A push to `main` whose version has no tag
yet runs the release workflow: it publishes to crates.io and PyPI through
OIDC trusted publishing, then tags `vX.Y.Z` and cuts a GitHub release. Each
target is probed independently, so a partially failed run resumes cleanly.
The unpublished `grundy/` workspace member (`publish = false`) is outside the
pipeline.

## License

By contributing you agree that your contributions are licensed under
AGPL-3.0-or-later, like the rest of the project.
