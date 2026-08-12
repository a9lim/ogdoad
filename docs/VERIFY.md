# Verification and evidence contract

## Claim classes

Every mathematical statement in code or prose should be identifiable as one
of:

| class | acceptable support |
| --- | --- |
| standard/cited | an academic source cited at the point of use |
| implemented and tested | deterministic tests, property tests, or exact replayable certificates |
| proved here | a complete paper proof, with the Lean-covered subset stated separately |
| open | an explicit statement in `OPEN.md` |

A finite census, experiment, source-backed table, or Lean definition of a
conjecture never moves a statement into the proved class.

## Authoritative gates

```sh
cargo fmt --all --check
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --workspace
cargo check -p ogdoad --features python
cargo clippy -p ogdoad --features python --all-targets -- -D warnings
python scripts/generate_stubs.py --check
(cd formal && lake build --wfail)
npm ci
python scripts/check_writeups.py
```

The scalar and Clifford property suites live in `tests/`. Increase
`OGDOAD_PROPTEST_CASES` for deeper fuzzing. Product changes must exercise the
`associativity_*` tests and the independent word-reduction oracle.

## Exactness and representation

| surface | contract |
| --- | --- |
| exact scalar markers | full ring/field laws within fixed-width overflow limits |
| `Qp`, `Qq`, Laurent, ramified, Gauss, `Adele`, and runtime `LocalQp` | capped precision; cancellation can lose associativity at the represented boundary |
| `Surreal` | exact finite-support expressions; unrepresentable infinite expansions return `None` |
| `Nimber` | exact `F_{2^128}` arithmetic |
| `Ordinal` | exact within the checked Kummer window; checked `nim_mul` returns `None` outside it, while `Scalar::mul` panics on ignored escape |
| bounded searches | report budget/exhaustion separately from mathematical truth |

## Lean boundary

`formal/` contains no `sorry`, `admit`, or custom `axiom`. Its modules fall into
three groups:

- `Off`, `BrownGame`, and `GameExterior` prove algebraic cores while external
  theorems about full nimbers or the additive group of short games remain cited
  paper inputs.
- `GoldDiagonal`, `FifoMatching`, `ImpartialRealizer`,
  `GoldMatchingAlgebra`, `GoldNoEvaluator`, `GoldBlockCompression`,
  `GoldExtraspecial`, `GoldForkPadding`, and `GoldSemantics` prove independent
  ingredients of the Gold/Brown/game-exterior paper. There is no single Lean
  theorem constructing the full weighted arena from finite-field data.
- `Fifo*` formalizes the open FIFO transition system, reductions, local
  contractions, and obstructions. `FifoLinkingTheorem` remains a proposition.
  `Excess` proves reduction algebra and exact finite criteria;
  `DPrimeTarget` remains a proposition.

See `formal/README.md` for the per-module map.

## Python and experiments

The maintained Python surface is:

- `demo.py` and `scripts/generate_stubs.py`;
- top-level `experiments/*.py`, each with its own guards and documented budget;
- exact certificate payloads and their local verifiers under
  `experiments/certificates/`.

`experiments/gold/`, `experiments/excess/`, and `experiments/audit/` are
exploratory archives. They are not imported by the package, not run by CI, and
not authoritative for current theorem statements. Promote a useful result by
moving a guarded, documented implementation to the maintained top level and
adding a test or paper reference.

## Curated production data

These tables are intentional because they encode named finite objects,
factored arithmetic, or compile-time API vocabulary:

| data | source |
| --- | --- |
| factors of `2^128-1` used for nimber orders | `src/scalar/finite_field/nimber/galois.rs` |
| finite Lenstra excess rows and certified extensions | `src/scalar/big/ordinal/tower.rs` |
| named binary and ternary code generators | `src/forms/integral/codes.rs` |
| exceptional ADE diagrams, determinants, Coxeter and Weyl orders | `src/forms/integral/root_lattices.rs`, `src/forms/integral/niemeier.rs` |
| Niemeier root/glue/automorphism catalogue | `src/forms/integral/niemeier.rs` |
| exceptional lattice/Clifford automorphism orders | `src/forms/integral/` |
| real Clifford and rational Brauer--Wall mod-eight cases | `src/forms/char0.rs`, `src/forms/witt/` |
| finite loopy-value names | `src/games/loopy/` |
| Python const-generic dispatch cells and aliases | `src/py/catalog.rs`, `src/py/forms.rs`, `src/py/games.rs` |

Closed-form Hilbert factors, generated Reed--Muller matrices, Bernoulli-derived
Eisenstein constants, blade signs, and linear-algebra reductions are not
curated tables and should remain computed.

## Paper artifacts

Each live `writeups/<name>.tex` has a matching `<name>.bib`. The TeX source is
the authority; the tracked PDF is regenerated from it. `check_writeups.py`
also creates untracked standalone HTML in `target/writeups/html/` with
Pandoc's citation processor and `--katex`, then rejects unresolved citations,
LaTeX errors, and raw unsupported math commands.
