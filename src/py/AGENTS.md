# `src/py/` editing guide

This is the only directory allowed to depend on PyO3. It exposes selected
monomorphizations of the pure-Rust core behind the optional `python` feature.

## Map

| path | responsibility |
| --- | --- |
| `mod.rs` | module registration and shared Python helpers |
| `catalog.rs` | fixed dispatch catalogue and generated backend families |
| `scalars.rs` | scalar wrappers and arithmetic |
| `engine.rs` | Clifford, multivector, divided-power, and CGA wrappers |
| `forms.rs` | classifiers, local--global reports, integral forms |
| `games.rs` | game values, evaluators, thermography, lexicodes |
| `weyl.rs` | Rational/Nimber Weyl algebras, elements, centres, and bounded fibres |

## Binding policy

- Bind plain runtime Rust types and an explicit fixed slice of const-generic
  families. Python cannot instantiate arbitrary `Qp<P,K>`, `Fpn<P,N>`,
  `Laurent<S,K>`, and related compile-time worlds without a deliberate runtime
  dispatcher.
- `OddFiniteFieldForm`, `Char2FiniteFieldForm`, and `LocalQp` are runtime
  façades where that design is useful; they do not erase the core's type
  distinctions.
- CGA is exposed only when `1/2` exists and the backend has a compatible
  multivector carrier.
- Crate-private kernels stay private. Bind stable high-level operations instead
  of exporting implementation machinery.
- Each algebra is monomorphic. Mixed backend operands raise `TypeError`; do not
  add an any-scalar wrapper.

## Operator and rendering contract

- `*`: geometric product; `&`: wedge; `<<`/`>>`: contractions; `~`: reverse;
  `**`: multivector power; `/`: supported scalar/versor division.
- Scalar power follows each scalar wrapper's documented API. Ordinal arithmetic
  keeps an explicit checked nim-power path.
- A scalar `__mul__` must return `NotImplemented` for a multivector so Python
  can dispatch to the multivector's `__rmul__`.
- Python `repr`/display delegates to canonical Rust `Display` whenever a core
  report or value exists.

## Rules

- Never import PyO3 outside `src/py/`; never make it a default dependency.
- Keep registrations, exports, and the generated `ogdoad.pyi` synchronized.
- Validate Python integer conversions against the core `u128`/`i128` widths;
  do not narrow payloads for convenience.
- Preserve domain errors and optional/unknown distinctions instead of mapping
  them to plausible-looking defaults.
- Changes to a core method used here are binding changes even when `src/py/`
  itself is untouched.

## Verification

```sh
cargo check -p ogdoad --features python
cargo clippy -p ogdoad --features python --all-targets -- -D warnings
python -m maturin build --profile dev -i python
python -m pip install --force-reinstall --no-deps target/wheels/ogdoad-*.whl
python demo.py
python scripts/generate_stubs.py --check
```

Also run the default workspace tests; they remain the authority for the math
core without libpython linkage.
