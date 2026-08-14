# grundy

grundy is Ogdoad's executable notation for scalar, Clifford, polynomial, and
game worlds. It has first-order functions, explicit world selection, guarded
game equations, canonical display, and typed resource failures. Games remain
an additive-group world; algebra products are available only where the active
world supports them.

Examples:

```text
:world game
[0] ≡ *1                  // the one-element list IS star — lists are games
over =: {0 | over}        // a loopy game, defined by its own equation
over = over               // true — survival
over ‿‿ over              // true — and yet both starters draw in over − over
1/2 = {0 | 1}             // numbers are games, past the integers

:world nimber
*3 ⋅ *5                   // nim-multiplication in F_{2^128}
```

## The documents

| file | role |
|---|---|
| [`spec.md`](spec.md) | **the normative language contract** — identity, grammar, sorts, semantics, display, errors, conformance obligations |
| [`implementation.md`](implementation.md) | the runtime contract — architecture, resource guards, validation gates |
| [`stance.md`](stance.md) | non-normative — the design tradition (total/codata, lazy where the objects are coinductive, ⊥ refused) |
| [`conformance.txt`](conformance.txt) | the authoritative hand-checked corpus; harness in `tests/conformance.rs` |
| `../../docs/ROADMAP.md` | proposed language work |

## Running it

```sh
cargo run -p grundy --example repl              # interactive; :help is task-first
cargo run -p grundy --example repl < file.og    # piped session
```

Start with `:help`, then select a world. The REPL prints canonical source and
keeps corrective guidance in each error's hint.
