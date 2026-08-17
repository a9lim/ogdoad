# Verification and evidence

## Claim classes

| class | required support |
| --- | --- |
| standard/cited | an academic source cited where the result is used |
| implemented and tested | deterministic tests, property tests, or a replayable exact certificate |
| proved here | a complete mathematical proof, with the Lean-covered subset stated separately |
| open | an exact statement in [`OPEN.md`](OPEN.md) |

Finite censuses, bounded searches, external tables, and Lean definitions of
propositions do not prove universal claims.

## Repository gates

```sh
cargo fmt --all --check
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --workspace
```

For changes to `src/py/` or a core API used by Python:

```sh
cargo check -p ogdoad --features python
cargo clippy -p ogdoad --features python --all-targets -- -D warnings
python scripts/generate_stubs.py --check
```

For Lean or load-bearing proof claims:

```sh
(cd formal && lake build --wfail)
```

For papers or bibliographies:

```sh
npm ci
python scripts/check_writeups.py
```

`check_writeups.py` compiles each paper, rejects unresolved citations and
overfull boxes, converts it to standalone HTML, and renders every math fragment
with the pinned KaTeX version. The `.tex` source is authoritative; tracked PDFs
are regenerated artifacts and must also receive page-level visual review.

## Representation contracts

| surface | exact boundary |
| --- | --- |
| exact scalar markers | full laws within fixed-width overflow limits |
| valued/local models | capped precision; cancellation may lose represented associativity at the boundary |
| `Surreal` | exact finite-support expressions only |
| `Nimber` | exact `F_(2^128)` arithmetic |
| `Ordinal` | exact inside the checked Kummer window; checked multiplication, inversion, and square roots refuse escape |
| Hermitian restriction | `q(v)=h(v,v)` over the represented involution-fixed field, with trace used only for the polar form; dimension doubles and refuses past 128 |
| bounded search | budget and exhaustion are reported separately from mathematical truth |

The `associativity_*` tests and
`general_product_reproduces_reduce_word_when_a_empty` are the independent
product oracles. New generic operations should add a focused test before broad
suite verification.

## Lean boundary

The standalone `formal/` project contains no `sorry`, `admit`, or custom
`axiom`. It proves named finite constructions and algebraic reductions. It does
not prove `FifoLinkingTheorem`, the universal excess rule, or an end-to-end
theorem merely by defining their propositions. The current theorem and module
map is [`../formal/README.md`](../formal/README.md).

## Maintained experiments

The maintained scripts have narrow roles:

- `linking_game.py` and `echo_solver.py`: FIFO executable oracle, minimax, and
  cross-checks;
- `gold_form_from_games.py`, `trace_form_arf.py`, and `under_descent.py`:
  independent checks for the solved Gold and thermic constructions;
- `ordinal_excess_probe.py`, `cyclotomic_3k_family.py`,
  `exception_column_m4.py`, `fermat_selected_screen.py`, and
  `cubic_two_normal_countermodel.py`: bounded excess screens or explicit
  non-Conway countermodels;
- `ordinary_*_certificate.py` and `ordinary_359_full_conductor.py`: exact
  named-row certificates, with resource requirements stated in each script;
- `experiments/certificates/`: versioned binary payloads consumed by those
  certificate verifiers.

These programs support only the claims documented in their module docstrings.

## Curated data

Named finite objects and source-backed arithmetic tables remain data when
recomputing them is either meaningless or prohibitively expensive. Current
examples include nimber-order factors, finite Lenstra rows and certificates,
named code and lattice catalogues, ADE and Niemeier data, real Clifford and
Brauer--Wall cases, finite loopy values, and Python dispatch cells. Generated
matrix reductions, blade signs, Hilbert factors, and closed-form coefficients
should remain computed rather than copied into tables.
