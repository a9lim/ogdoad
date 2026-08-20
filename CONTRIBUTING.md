# Contributing

Thanks for the interest. ogdoad is a research codebase, so the bar is correctness
first: a new operation lands with a test that pins it to an independent oracle, not
on a "looks right" basis.

## Read the working notes first

`AGENTS.md` is the map: the five pillars (`scalar/`, `clifford/`, `forms/`,
`games/`, `weyl/`) plus the PyO3 bindings. Each layer has a short local `AGENTS.md` with its
module map and invariants. Read `docs/OPEN.md` before changing research claims or
the open-question probes.

## The non-negotiables

These are the invariants the whole thing rests on (full list in
`AGENTS.md` under “Non-negotiable mathematical invariants”):

- **The math core is generic over `Scalar` and pure Rust.** PyO3 lives behind the
  `python` feature — never `use pyo3` outside `src/py/`, never make it
  non-optional. This is what keeps `cargo test` from linking libpython.
- **The metric carries `q` and `b` independently — do not collapse them.** In
  characteristic 2 the polar form `b` is alternating yet `q[i]` can be nonzero;
  collapsing them makes every char-2 algebra commutative (the wrong object).
- **Signs go through the scalar's own `neg()`**, never a literal `-1` or a
  `characteristic()` branch — for nimbers `neg` is identity, so char-2
  sign-vanishing falls out for free.
- **Weyl monomials are checked PBW multidegrees, not Clifford blades.** Preserve
  positive-characteristic centers and the explicit non-faithfulness of the
  ordinary polynomial action.
- **Surreal arithmetic recurses only on exponents** (strictly simpler than the
  number). That's the entire termination argument.
- **Verify, don't claim.** Add a test before trusting a new operation.

## Test plan

```sh
cargo test --workspace                      # the math core + grundy — source of truth, no Python
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --all --check
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --workspace
(cd formal && lake build --wfail)
npm ci
python scripts/check_writeups.py
```

`cargo test` does **not** compile the `python` feature. After touching `src/py/` or
any core API the bindings call:

```sh
cargo check -p ogdoad --features python
cargo clippy -p ogdoad --features python --all-targets -- -D warnings
python scripts/generate_stubs.py --check
```

After touching `clifford/`, `scalar/big/surreal/`, or their bindings, rebuild
and run the Python tour to verify the bound surface, including canonical
displays such as `e0∧e1`, `*n`, and CNF:

```sh
python -m maturin build --profile dev -i python
python -m pip install --force-reinstall --no-deps target/wheels/ogdoad-*.whl
python demo.py
```

## Claim levels

When you change prose, comments, examples, or a paper, separate **standard and
cited**, **implemented and tested**, **proved here**, and **open** claims. A new
mathematical assertion needs a proof, a source, or an explicit open label.

## Releasing

The version in `Cargo.toml` is the single source of truth (pyproject and the
maturin build inherit it). On a push to `main` carrying a new version, the release
workflow publishes to crates.io and PyPI (both via OIDC trusted publishing), tags
`vX.Y.Z`, and cuts a GitHub release. Each target is checked independently, so a
partial-failure run resumes cleanly. The unpublished `grundy/` workspace member
(`publish = false`) is deliberately outside the pipeline.

## License

By contributing you agree your contributions are licensed under AGPL-3.0-or-later,
same as the rest of the project.
