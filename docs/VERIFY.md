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

## Core gate

```sh
cargo fmt -p ogdoad --check
cargo test -p ogdoad
cargo clippy -p ogdoad --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps -p ogdoad
```

`cargo test` includes the runnable examples in the API documentation. The
workspace's `default-members` make bare Cargo commands at the root select the
same core package. CI runs this gate on pushes to `main` and `dev`, the core
tests again in the release profile the wheels ship with, feature-enabled
Clippy, and the built-wheel, Python test-suite, and stub checks; `grundy/`,
Lean, and the papers are opt-in.

## Sidecar gates

For the `grundy/` ruleset language:

```sh
cargo fmt -p grundy --check
cargo test -p grundy
cargo clippy -p grundy --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps -p grundy
```

For `src/py/` or a core API it calls:

```sh
cargo check -p ogdoad --features python
cargo clippy -p ogdoad --features python --all-targets -- -D warnings
python scripts/generate_stubs.py --check
python -m unittest discover -s tests/python
```

The stub check imports the *installed* extension and compares it byte for
byte with `ogdoad.pyi`, so it is meaningful only after rebuilding and
installing the wheel (see `CONTRIBUTING.md`). The `tests/python` suite uses only
the standard library and tests the installed extension the same way: binding
laws and contracts per scalar world, the Clifford, forms, games, and Weyl
surfaces, stub-versus-runtime drift, the README and `demo.py` examples, and
child-process probes for inputs that must raise rather than crash. Known
defects are pinned as `expectedFailure` tests that name the defect.

For Lean or a load-bearing proof claim:

```sh
(cd formal && lake build --wfail)
```

For papers or bibliographies:

```sh
npm ci
python scripts/check_writeups.py
```

`check_writeups.py` needs `tectonic`, `pandoc`, and `node`. For each paper it
compiles the PDF (overwriting the tracked copy in `writeups/`), rejects
unresolved citations and cross-references, overfull boxes, uncited or
duplicate bibliography keys, and inline bibliographies, converts the paper to
standalone HTML with `pandoc --citeproc --fail-if-warnings`, rejects leaked raw
LaTeX commands, and renders every math fragment with the pinned KaTeX version
in strict mode. The `.tex` source is authoritative; regenerated PDFs also need
a page-level visual review.

## Representation contracts

| surface | exact boundary |
| --- | --- |
| exact scalar markers | full laws within fixed-width limits; `Integer` and `Rational` panic on `i128` overflow |
| valued/local models | capped precision; cancellation may lose represented associativity at the boundary |
| `Surreal` | exact finite-support expressions only |
| `Nimber` | exact `F_(2^128)` arithmetic |
| `Ordinal` | exact inside the checked Kummer window (excess rows through prime `727`); checked multiplication, inversion, and square roots refuse escape |
| Weyl algebras | finite sparse PBW support with checked `u128` exponents and explicit term/work budgets; exact-field Darboux reduction certifies basis, inverse, and radical witnesses; affine maps check commutators; symbols and the polynomial `hbar` family stay finite-support; positive-characteristic centres are commutator-checked; central fibres need a basis cap, while split modules and matrix certificates add matrix-entry and work caps; `p`-symbol reports keep cited presentations apart from exact split certificates; the polynomial action is not claimed faithful in positive characteristic |
| Hermitian restriction | `q(v)=h(v,v)` over the represented involution-fixed field, with trace used only for the polar form; dimension doubles, so Hermitian dimension above 64 is refused |
| mod-two Milnor symbols | degrees `0..=2` over `Q`, supported odd finite fields, and `F_q(t)`; strict `e_n` maps require membership in `I^n`; characteristic-two Kato and wild local symbols are outside the surface |
| Clifford centers | for nonsingular forms, materialized full/even central generators with Kummer or characteristic-two Artin--Schreier relation; split class and parity are compared independently with Brauer--Wall coordinates; degenerate centers are refused |
| bounded search | budget exhaustion is reported separately from mathematical truth |

## Independent oracles

The Clifford tests `associativity_*` and
`general_product_reproduces_reduce_word_when_a_empty` in
`src/clifford/engine.rs` are the product oracles. New generic operations add a
focused test before broad suite verification.

The Weyl suites are organized by layer:

- `tests/weyl_axioms.rs` checks the optimized standard product against the
  grouped general PBW normalizer, and the normalizer against a literal
  adjacent-word reducer; associativity and distributivity of the general
  product over `Q`, `F_5`, `F_2`, and `Z/4`; polynomial-action
  multiplicativity in ranks one and two over `Q` and `F_5`; and budget,
  overflow, and huge-exponent boundaries.
- `tests/weyl_transformations.rs` checks Darboux reconstruction and transport,
  automorphism product preservation and inverses, anti-multiplicativity,
  direct sums and embeddings, both principal-symbol product laws, Poisson
  Leibniz/Jacobi and leading-commutator laws, and `hbar = 0/1`
  specialization. Its random Fourier family is independent of the
  constructors' certificates; its random form family reruns the Darboux
  verifier and checks the dimension identity.
- `tests/weyl_central_fibers.rs` checks transported radical and
  characteristic-power centre generators against the commutator oracle,
  lazy and bounded bases over the centre, central reduction as an algebra
  homomorphism, every split-module matrix relation, an exact full-rank odd
  matrix certificate, and characteristic-two fibre products against the
  Clifford engine, with random finite-field families on both multiplication
  paths.
- `tests/weyl_psymbols.rs` checks the residue against exact split-module
  trace in tensor ranks one and two (both signs of `(-1)^n`), every
  cyclic-presentation relation and the nonunit refusal, central-character
  pullbacks including the characteristic-two shear correction, and
  multiplication in an arbitrary alternating presentation against its bounded
  Darboux-transported fibre.

## Lean boundary

The standalone `formal/` project contains no `sorry`, `admit`, or custom
`axiom`. `Excess.lean` and five FIFO route-limit modules prove named finite
propositions with `native_decide`; those declarations additionally depend on
Lean's generated native-decision axiom. Lean proves named finite constructions
and algebraic reductions. The excess disproof has kernel-checked equal-norm,
translation-rigidity, norm-synchronization, and primitive-prime components; its
finite-field and literal Conway synthesis is a paper theorem. Lean does not
prove `FifoLinkingTheorem` or any theorem merely by defining its proposition. The
theorem map is [`../formal/README.md`](../formal/README.md).

The nonzero-translate support theorems additionally use kernel-checked cubic
and quartic exponent collision and coefficient-proportionality lemmas. Their finite-field
tensor and rational-function arguments remain paper-level, and aggregate
primitive support is distinct from a full primary order test at each prime.
The five-power excess gap uses kernel-checked transformation and
eigencharacter identities; its cycle count and literal finite-field
specialization remain paper-level.

## Maintained experiments

Each script supports only the claims in its module docstring.

- `linking_game.py`, `echo_solver.py`: the FIFO executable oracle, exact
  minimax, and cross-checks.
- `gold_form_from_games.py`, `trace_form_arf.py`, `under_descent.py`: checks
  of the Gold and thermic constructions through the built `ogdoad` Python
  module (`trace_form_arf.py` reads Arf invariants with Ogdoad's own
  classifier; `common.py` is its helper).
- `ordinal_excess_probe.py`, `cyclotomic_3k_family.py`,
  `exception_column_m4.py`, `fermat_selected_screen.py`: bounded excess
  screens. The Fermat screen runs on Conway's tower or, with
  `--tower wiedemann`, on Wiedemann's; `--complete-level` decides a fully
  factored level `n <= 11`. `fermat_selected_screen_results.md` records the
  published-factor runs for both towers.
- `cubic_two_normal_countermodel.py`, `fermat_top_orbit_countermodel.py`:
  explicit non-Conway countermodels to overstrong lemmas, not counterexamples
  to the `0/1/4` rule.
- `ordinary_*_certificate.py`, `ordinary_359_full_conductor.py`: exact
  named-row certificates. The python-flint verifiers state their resource
  requirements; the stdlib ones run in seconds.
- `wiedemann_sibling.py`: the exact checks behind `excess.tex`'s Wiedemann
  subsection: the trace and norm identities and nonconjugacy for `n <= 5`,
  the ordinary-curve realization of Wiedemann's tower, and the Frobenius
  image on the supersingular points `P_n`, with `ord(P_n) = F_n` for
  `2 <= n <= 6`.
- `excess_search/`: exact row engines for the `0/1/4` excess search.
  - The reference engine (one sparse model, checked roots) reproduces every
    OEIS row with `E <= 60000`.
  - The crossed-binomial v2 engine is validated against OEIS, the reference
    engine and Peeters' records.
  - Also included: their row results past 727, Peeters' records as data, and
    parked design, review and random-model notes.
  - Rows are finite data; the notes' theorems are not yet in the paper.
- `certificates/`: versioned binary payloads for the certificate verifiers,
  documented in its README.

## Curated data

Named finite objects and source-backed arithmetic tables remain data when
recomputing them is meaningless or prohibitively expensive: nimber-order
factors, finite Lenstra rows and certificates, named code and lattice
catalogues, ADE and Niemeier data, real Clifford and Brauer--Wall cases,
finite loopy values, and Python dispatch cells. Matrix reductions, blade
signs, Hilbert factors, and closed-form coefficients stay computed rather than
copied into tables.
