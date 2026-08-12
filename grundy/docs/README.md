# grundy

**grundy is ogdoad's executable notation.**
Games are equations (`on =: {on |}` is Siegel's `on`, verbatim as
a program); nimbers, surreal monomials, and Clifford coordinates are
literals; the outcome partition is a set of relation glyphs whose geometry
*is* the mathematics (negate both games and the relation grid rotates 180°).
Computation is deliberately thin — substitution, one equation binder,
non-strictness only where the mathematics never looks — so that every
construct coincides with a piece of CGT or algebra.

Ten lines, three delights:

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

Start with `:help`, then `:world game`. The REPL is the tutor: every echo is
canonical, every error carries the mathematics in its message and the
teaching in its hint.
