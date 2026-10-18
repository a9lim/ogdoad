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
    interp.rs            the explicit-stack evaluator, budgets, patterns, Form equation systems
    builtins.rs          builtin implementations and dispatch
  games/
    game.rs              the sealed GameV handle over the engine's GameArena, birthday guard, fuel metering
    form.rs              presented Forms: loopy graphs, display, bisimilarity
    rules.rs             rulesets, component exploration, sum-state graphs
    claims.rs            witnesses, verify, claims, Bounded, misère
  algebra/
    mod.rs               dispatch of algebra literals, operators, and builtins to the backends
    scalar.rs            the scalar backends as one ScalarV
    poly.rs              polynomial rings and rational-function fields
    clifford.rs          Clifford algebras and multivectors
  display.rs             every value as a program
```

Reusable game mathematics belongs in Ogdoad's `src/games/` pillar:

- canonical games and their memos (`games::arena::GameArena`);
- the certifying retrograde solver and its checker (`games::loopy::certificate`);
- the Guy–Smith checker (`games::octal::GuySmithCertificate`) and octal moves;
- graph sums and stopper status (`games::loopy::LoopyPartizanGraph`).

The language owns ruleset exploration, guardedness, recognition, display, the
evidence types, and its misère solver.

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
- **Closures capture what they mention.** A closure keeps only the local
  bindings its body names, plus an immutable snapshot of the global map taken
  at definition. A statement commits its new globals, and keeps its type
  unifications, only after it fully succeeds.
- **Displays are structural.** A pre-pass hash-conses every composite
  subvalue by structure and counts its occurrences in the value read as a
  tree; repeated long texts and deep spines become bindings. The result
  depends on the value, not on how it was built.
- **Sealed games.** `GameV` is an id in the engine's `GameArena`, which interns
  each canonical form once and keeps order, sum, and negation memos for the
  thread's lifetime. Games are ordered by birthday, then by left and right
  option counts, then option by option. Equality and hashing are id
  comparisons; the order is deterministic across sessions.
- **Positions as keys.** Ruleset positions hash through a structural
  `PosKey`. Sum-states are multisets of components, normalized by the
  structural total order on values.
- **Iterative exploration.** Component graphs, topological valuation, sum-state
  graphs, and the misère solver use explicit worklists, not host recursion.
- **Explicit-stack evaluation.** The evaluator is a machine whose pending work
  is a heap stack of frames, each holding the shared `Core` node it came
  from. Calls, expression nesting, comprehensions, and `map`, `filter`,
  `fold`, `any`, and `all` push frames rather than host stack. Quick
  expressions (a leaf, or at most four levels of operators, tuples, and
  conditionals over leaves) run directly. Within one step, host recursion is
  bounded by the source nesting limit (quick expressions, patterns, a
  binding's free variables, a game equation's braces) or by the 2¹⁴ depth
  guards. Host code re-enters the machine only to run a ruleset's move
  function or a game equation's operand.
- **Evidence is checked where it is sealed.** Producers build a witness and
  pass it through the same `verify` that user-constructed witnesses go
  through.

## Host-resource guards

Every limit fails with a typed error, and no partial value escapes.

| guard | contract |
| --- | --- |
| worker stack | one persistent 256 MiB worker per session. It holds parsing, checking, the bounded host recursion inside one evaluation step, and nested evaluations; the evaluator's own frames are on the heap |
| source nesting | 1536 delimiters, and 1536 levels of expression nesting (each operand of a flat operator chain counts as a level), checked before or inside the parser (`E_Parse`) |
| call depth | 4096 closure frames (`E_StackDepth`, distinct from fuel), counted on the evaluator's heap stack: the same depth succeeds in every build profile however deeply the call sits in its body, and recursion through the higher-order builtins and comprehensions counts the same way. The heap stack's length is bounded by this budget times the source nesting limit |
| nested evaluation | a ruleset's move function or a game equation's operand runs in a fresh evaluation called from host code; a chain of them is refused once it has used half the worker stack (`E_StackDepth`), so how long such a chain may grow depends on the build profile |
| game depth | `Game` and `Form` literals and every `Game` result are born by day 2¹⁴ (`E_StackDepth`): game algorithms recurse on depth |
| canonical games | one per-thread `ogdoad::games::GameArena`; its steps are charged to fuel, so values met before are free |
| value depth | data, closures, recursive groups, and generics nest at most 2¹⁴ levels (`E_StackDepth`); lists and tuples record their depth when built, so the check is constant time |
| display | one fuel unit per atom written (`E_Fuel`); shared and deep subvalues are bound, so displays are linear in the value |
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
