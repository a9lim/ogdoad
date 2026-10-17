# grundy implementation contract

Companion to the normative [`spec.md`](spec.md). This document records the
runtime architecture, resource guards, error discipline, and verification
gates.

## Architecture

```text
grundy/src/
  lib.rs                 public surface: GrundySession, parse/unparse, errors
  worker.rs              the persistent large-stack worker behind GrundySession
  session.rs             statements: data declarations, check, evaluate, display
  error.rs               GrundyError, kinds, stable E_* codes
  syntax/                lexer, AST, recursive-descent parser, minimal-paren unparser
  types/
    mod.rs               Ty, classes and instances, level-based unifier, defaulting
    infer.rs             Damas–Milner inference and elaboration to Core
  core.rs                the elaborated core language
  builtins.rs            builtin names and signatures (surface type syntax)
  eval/
    value.rs             values, persistent environments, closures, generics
    interp.rs            the evaluator, budgets, patterns, Form equation systems
    builtins.rs          builtin implementations and dispatch
  games/
    game.rs              sealed canonical Game: interner and structural order
    form.rs              presented Forms: loopy graphs, display, bisimilarity
    rules.rs             rulesets, component exploration, sum-state graphs
    claims.rs            witnesses, verify, claims, Bounded, misère
  algebra/
    scalar.rs            the scalar backends as one ScalarV
    poly.rs              polynomial rings and rational-function fields
    clifford.rs          Clifford algebras and multivectors
  display.rs             every value as a program
```

Reusable game mathematics belongs in Ogdoad's `src/games/` pillar:

- the certifying retrograde solver (`games::loopy::certificate`);
- the Guy–Smith checker;
- graph sums and stopper witnesses.

The language owns ruleset exploration, guardedness, recognition, display, and
the evidence types.

## Structural decisions

- **One authoritative path.** Source parses to an AST. The checker infers
  and elaborates to `Core`, which is the only thing the evaluator runs.
  Every literal in `Core` carries its resolved type, possibly a type
  parameter of an enclosing generalized binding. Every reference to a
  generalized binding carries its instantiation.
- **Runtime types instead of dictionaries.** A generalized lambda is stored
  as a `Generic` value and re-evaluated under each instantiation's type
  environment. Operators dispatch on runtime values; only literal
  construction and type-indexed builtins (`sum`'s zero, `grassmann`) read
  the types.
- **No reference cycles.** A recursive group holds its definitions and
  captured environment, never itself. Calling a member rebuilds the group's
  bindings in the call environment.
- **Closures capture globals at definition** through an immutable snapshot of
  the global map. A statement commits its new globals only after it fully
  succeeds.
- **Sealed games.** `GameV` is an id in the engine's `GameArena`, which interns
  each canonical form once and keeps order, sum, and negation memos for the
  thread's lifetime. Options are sorted by birthday and then recursively by
  children. Equality and hashing are id comparisons; the order is
  deterministic across sessions.
- **Positions as keys.** Ruleset positions hash through a structural
  `PosKey`. Sum-states are multisets of components, normalized by the
  structural total order on values.
- **Iterative exploration.** Component graphs, topological valuation, sum-state
  graphs, and the misère solver use explicit worklists, not host recursion.
- **Evidence is checked where it is sealed.** Producers build a witness and
  pass it through the same `verify` that user-constructed witnesses go
  through.

## Host-resource guards

All limits fail with typed errors; no partial value escapes.

| guard | contract |
| --- | --- |
| worker stack | one persistent 256 MiB worker per session |
| source nesting | 1536 delimiters, and 1536 levels of expression nesting, checked before or inside the parser (`E_Parse`) |
| call depth | 4096 frames (`E_StackDepth`, distinct from fuel) |
| game depth | `Game` and `Form` literals and every `Game` result are born by day 2¹⁴ (`E_StackDepth`): game algorithms recurse on depth |
| canonical games | one per-thread `ogdoad::games::GameArena`; its steps are charged to fuel, so values met before are free |
| display | one fuel unit per atom written (`E_Fuel`) |
| fuel | default 2²²: closure calls, produced list elements, generated option and sum-state components, term-count products of growing algebra values, game-literal sizes (`E_Fuel`) |
| exact coefficients | an exact backend's i128 overflow fails the statement with `E_Overflow`; only those documented engine panics are contained |
| node budget | default 2¹⁶: distinct positions, sum-states, graph nodes, misère memo entries (`E_GraphBudget`) |
| shared-DAG walks | pointer-keyed memoization in equivalence, recognition, and canonical interning |

## Error discipline

`GrundyError` carries `kind`, `span`, `message`, and optional `hint`.

- The message states what failed.
- Direct corrective guidance belongs in the hint.
- Spans come from the innermost node that knows its source position.
- Runtime invariant violations (a well-typed program reaching an impossible
  state) report `E_Domain` with an `internal:` message, so they are visible.
  No test vector may expect one.

## Verification

```sh
cargo fmt -p grundy --check
cargo test -p grundy
cargo clippy -p grundy --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps -p grundy
```

`tests/conformance.rs` runs the corpus. `tests/laws.rs` runs randomized laws
against independent oracles, with fixed seeds so that failures replay. Engine
changes under `src/games/` also run `cargo test -p ogdoad`.
