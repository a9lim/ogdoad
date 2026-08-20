# AGENTS.md — Ogdoad editing contract

This file records only the current architecture, mathematical boundaries, and
verification contract. Public orientation belongs in `README.md`; research
statements belong in `docs/OPEN.md` and the papers; detailed module guidance
belongs in each pillar's `AGENTS.md`.

## Read first

Before changing a subsystem, read its local instructions:

| scope | instructions |
| --- | --- |
| scalars | `src/scalar/AGENTS.md` |
| Clifford engine and GA | `src/clifford/AGENTS.md` |
| forms and invariants | `src/forms/AGENTS.md` |
| integral forms and lattices | `src/forms/integral/AGENTS.md` |
| games | `src/games/AGENTS.md` |
| Weyl algebras | `src/weyl/AGENTS.md` |
| Python bindings | `src/py/AGENTS.md` |
| shared linear algebra | `src/linalg/AGENTS.md` |
| expression language | `grundy/docs/spec.md` and `grundy/docs/implementation.md` |
| Lean | `formal/README.md` |

For mathematical claims, also read the relevant live paper and
`docs/OPEN.md`. Git history is the historical record; current docs do not carry
changelogs.

## Architecture

Ogdoad is a pure-Rust math core with optional PyO3 bindings. The five public
pillars are `scalar`, `clifford`, `forms`, `games`, and `weyl`; `linalg` is
crate-private. Their public modules re-export children shallowly.

- `scalar/` groups coefficient worlds by place and exactness.
- `forms/` groups classification theory by characteristic, then adds Witt,
  Springer, local--global, Hermitian/symplectic, and integral layers.
- `clifford/` owns metrics, multivectors, products, and metric-dependent GA.
- `games/` is separate from scalar arithmetic except where a genuine
  commutative scalar subclass or checked bridge exists.
- `weyl/` owns finite-support PBW algebras attached to alternating commutator
  forms; it shares scalar and symplectic-form infrastructure without reusing
  the finite Clifford blade representation.
- `py/` monomorphizes selected Rust backends; PyO3 is never part of the default
  build.
- `grundy/` is an unpublished workspace crate depending only on Ogdoad's public
  API.
- `formal/` is a separately pinned Lean project. It proves named components
  and selected end-to-end finite constructions; paper-level syntheses must
  state what Lean does and does not check.

## Non-negotiable mathematical invariants

1. **A Clifford scalar is a commutative ring.** Arbitrary partizan games form
   only an abelian group. Do not describe the project as a Clifford algebra
   over all games.
2. **`Metric` keeps `q`, `b`, and optional `a` distinct.** In characteristic
   two, `q[i] = e_i^2` is independent of the alternating polar data
   `b[(i,j)] = e_i e_j + e_j e_i`. `a[(i,j)]` records the ordered contraction
   for a general bilinear metric. Construct metrics with `Metric::new`,
   `diagonal`, `grassmann`, or `general`, never a struct literal.
3. **Signs use `Scalar::neg`.** Never branch on characteristic or inject a
   literal `-1` into generic product code. For characteristic two, negation is
   the identity.
4. **Backend limitations are part of the API.** Precision models, finite
   representations, unsupported field parameters, and checked ordinal escape
   boundaries must return/refuse exactly as documented; do not hide them with
   silent defaults.
5. **Fixed-width mathematical payloads are `u128`/`i128`.** `usize` is for
   dimensions, indices, and ABI hooks.
6. **Per-backend Python types do not mix.** Do not add a runtime-tagged
   any-scalar escape hatch.
7. **Weyl PBW exponents are not Clifford blades.** Weyl algebras are
   infinite-dimensional and use checked `u128` multidegrees. Positive-
   characteristic centers and non-faithful polynomial actions remain explicit.

## Claim discipline

Use four levels:

- **standard/cited:** an external theorem with an academic citation;
- **implemented and tested:** a property exercised by Rust/Python tests or an
  exact certificate;
- **proved here:** a paper theorem, with the Lean boundary stated separately;
- **open:** an explicit conjecture or constructive/classification problem in
  `docs/OPEN.md`.

Do not upgrade a finite census, source-pinned table, experimental script, or
Lean definition of a proposition into a universal theorem.

The current open fronts are exactly:

- arbitrary-graph isolated-dummy FIFO linking;
- the universal `0/1/4` transfinite nim-excess rule, including its selected
  nim-reciprocity program;
- natural-ruleset realization of finite misère quotients, including the exact
  quotient of misère Grundy's game.

In particular, the Gold--Arf construction uses the proved
matching-plus-isolates theorem and does not depend on general FIFO linking.
The full `On_2` classification is a mathematical theorem after scalar
extension; it does not make the finite `Nimber(u128)` backend algebraically
closed or make the partial `Ordinal` backend construct every root.
Quasi-linear multiplication in canonical finite-nimber coordinates has an
explicit proved transform; its arbitrary-width implementation and crossover
measurement are engineering work in `docs/ROADMAP.md`.

## Code conventions

- Rust 2021; AGPL-3.0-or-later.
- Keep the generic core dependency-light and pure Rust. `pyo3` may appear only
  under `src/py/` and behind the `python` feature.
- Prefer the existing trait layer (`Scalar`, exactness markers, `Valued`,
  `ResidueField`, `FieldExtension`) to backend-specific branches.
- Concrete scalar operators are convenience APIs; generic engine code uses
  borrow-based trait methods.
- Public rendering is deliberate. Preserve canonical `Display` forms and
  update exact-string tests when a format intentionally changes.
- Preserve unrelated work. Use focused diffs and tests that exercise the
  changed causal surface.

## Verification

Minimum core Rust gate:

```sh
cargo fmt -p ogdoad --check
cargo test -p ogdoad
cargo clippy -p ogdoad --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps -p ogdoad
```

Additional gates:

- after changing the optional `grundy/` expression language:

  ```sh
  cargo fmt -p grundy --check
  cargo test -p grundy
  cargo clippy -p grundy --all-targets -- -D warnings
  RUSTDOCFLAGS="-D warnings" cargo doc --no-deps -p grundy
  ```

- after changing `src/py/` or a core API it calls:

  ```sh
  cargo check -p ogdoad --features python
  cargo clippy -p ogdoad --features python --all-targets -- -D warnings
  python scripts/generate_stubs.py --check
  ```

- after changing Lean or a load-bearing proof claim:

  ```sh
  (cd formal && lake build --wfail)
  ```

- after changing a paper or bibliography:

  ```sh
  npm ci
  python scripts/check_writeups.py
  ```

The Clifford product tests `associativity_*` and
`general_product_reproduces_reduce_word_when_a_empty` are its core independent
oracles. The Weyl product independently compares its optimized standard path to
the general PBW normalizer. Add a focused test before trusting a new operation.

## Documentation contract

- `README.md`: public description, supported surface, sharp non-claims.
- `docs/OPEN.md`: only unresolved mathematical statements and their best
  current reductions.
- `docs/ROADMAP.md`: unfinished engineering or new-feature work.
- `docs/VERIFY.md`: evidence classes, generated data, experiments, and build
  commands.
- `writeups/*.tex` + matching `.bib`: self-contained mathematical papers,
  compilable as PDF and convertible by Pandoc to standalone KaTeX HTML.
- `formal/README.md`: theorem map and proof/non-proof boundary.

Do not recreate completion ledgers, dated audit diaries, retired mechanisms,
or provenance narratives in live docs. If history matters, cite a stable
source or use Git history.
