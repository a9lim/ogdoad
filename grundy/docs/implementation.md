# grundy implementation contract

Companion to the normative [`spec.md`](spec.md). This document records the
current runtime architecture, resource guards, error discipline, and
verification gates.

## Architecture

One evaluator owns AST traversal, strictness, sorts, bindings, application,
conditionals, relations, sequences, and recursion budgets. Per-world runtimes
receive evaluated values and implement literals, algebraic operations,
relations, containers, and builtins. Syntax reaches a world directly only
where the language requires a thunk or structural closure: lazy append,
application, Element fixpoints, and surreal monomial construction.

`World` is an explicit enum of monomorphized worlds. This is how the one-active-
world rule is enforced; Grundy is not a runtime plugin system.

```text
grundy/src/
  ast.rs, lex.rs, parse.rs, unparse.rs, error.rs
  eval.rs                  public evaluation surface and guard constants
  session.rs               persistent worker, declarations, source guards
  runtime/
    mod.rs                 shared evaluator and WorldOps contract
    state.rs               environment, fuel, graph budget, call state
    value.rs               Value, FunctionValue, Binder, DataSort
    function.rs            substitution, application, composition, recursion
    validate.rs            sort, arity, shadowing, and world validation
    index.rs               single Index evaluator
    transform.rs           substitution, normalization, AST audits
  worlds/
    clifford.rs            scalar/Clifford worlds and metric parsing
    polynomial.rs          polynomial worlds
    rational_function.rs   rational-function worlds
    game/
      mod.rs               game operations
      fixpoint.rs          guarded recursive systems and SCC closure
      display.rs           recognition and self-contained display
      equiv.rs             multiform equivalence
```

The language owns lowering, guardedness, recognition, and display. Reusable
loopy-game mathematics belongs in Ogdoad's `src/games/loopy/` pillar.

## Structural decisions

- `Apply { callee, args }` is a real AST node. Argument frames are not value
  tuples.
- `DataSort` is exactly `Element | Index | Bool`; functions carry a separate
  typed signature. Binder marks are AST data and round-trip through display.
- `runtime/index.rs` is the single Index evaluator. Worlds contribute only
  primitive Index calls such as `dim`, `deg`, `nleft`, and `nright`.
- Game Elements enter recursive calls through temporary binding, not AST
  substitution, because cyclic graph values cannot be lowered as finite
  substituted syntax.
- Definition-time validation checks every operand, including non-strict
  positions. Evaluation may skip a branch; validation may not skip its sort.
- Presentation, multiform, value, and outcome are observational strata, not
  separate runtime representations.
- Loopy display finds anchors on every path, condenses SCCs, emits a
  reverse-topological equation system, and allocates names against all ambient
  collisions. The result must rebuild in a fresh session.

## Host-resource guards

All limits are code constants and fail with typed errors, never partial values.

| guard | current contract |
| --- | --- |
| worker stack | one persistent 64 MiB worker for REPL, API, and corpus execution |
| recursion depth | 1024 frames; `E_StackDepth`, distinct from language fuel |
| source/AST depth | 1536; `E_Parse` before recursive consumers run |
| graph materialization | default 65536 distinct nodes; `E_GraphBudget` on every construction path |
| shared-DAG walks | pointer-keyed memoization for equivalence, recognition, and fingerprints |

Fuel counts language-level recursive unfolding. Stack depth and graph nodes are
host safeguards; their errors must not masquerade as fuel exhaustion.

## Error discipline

`GrundyError` carries `kind`, `span`, `message`, and optional `hint`.
Construct errors through the centralized helpers in `error.rs`.

- The message states what failed.
- Direct corrective guidance belongs in `hint`.
- Live messages contain no release history.
- Partial work never escapes after a budget or validation failure.

Corpus vectors with hints assert the hint field explicitly.

## Verification

```sh
cargo fmt -p grundy --check
cargo test -p grundy
cargo clippy -p grundy --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps -p grundy
```

The conformance corpus is the semantic oracle. Law tests cover display
round-trips, retractions, relation symmetries, projections, and lazy totality;
differential tests compare graph algorithms with independent evaluators.
Randomized families use fixed/reported seeds so failures replay.
