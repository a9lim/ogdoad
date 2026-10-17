# grundy

grundy is a typed language for combinatorial games over Ogdoad. Positions are
ordinary data and moves are functions; games arise by exploring a ruleset
from a position. Answers state their scope: exact on finite objects, verified
claims with re-checkable certificates, and sampled answers typed `Bounded`.
Ogdoad's nimbers, ordinals, surreals, finite fields, polynomials, and Clifford
algebras are types that coexist in one program.

```text
grundy_game := impartial(n ↦ [[a, n - a] for a in 1..n if 2⋅a < n])
[sg(grundy_game, n) for n in 0..12]       // [0, 0, 0, 1, 0, 2, 1, 0, 2, 1, 0, 2]
winning(grundy_game, [7, 5], Left)        // the moves to second-player wins

kayles := octal([7, 7])
periodic(kayles, 71, 12)                  // a Guy–Smith claim for every heap

over =: {0 | over}                        // a loopy game, by its own equation
over = over                               // true — survival
over ‿‿ over                              // true — yet both stall in over − over
certify(over)                             // verify(outcome_witness(…)) /* claim: … */

nim := impartial(n ↦ [[k] for k in 0..n])
sampled(misere_quotient(nim, [1], 3, 3))  // a sampled quotient, typed as sampled

*3 ⋅ *5                                   // *15 : Nimber
(t↑2 + 1 : F5[t])(2)                      // 0 : F5
```

## The documents

| file | role |
|---|---|
| [`spec.md`](spec.md) | **the normative language contract**: syntax, types, games, rulesets, evidence, display, errors |
| [`implementation.md`](implementation.md) | the runtime contract: architecture, resource guards, verification gates |
| [`stance.md`](stance.md) | non-normative: rulesets as coalgebras, answers that carry their scope, budgeted recursion |
| [`conformance.txt`](conformance.txt) | the authoritative hand-checked corpus; harness in `tests/conformance.rs` |
| `../../docs/ROADMAP.md` | proposed language work |

## Running it

```sh
cargo run -p grundy --example repl              # interactive; :help lists commands
cargo run -p grundy --example repl < file.og    # piped session
```
