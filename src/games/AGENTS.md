# `src/games/` editing guide

This pillar implements combinatorial games and checked bridges to scalar,
forms, and integral structures. A game value is not automatically a scalar
ring element.

## Map

| path | responsibility |
| --- | --- |
| `grundy.rs`, `kernel.rs` | finite impartial evaluation and P/N kernels |
| `misere.rs` | bounded misere quotient machinery |
| `loopy/` | finite cyclic impartial and partizan graphs |
| `partizan.rs`, `piecewise.rs` | short partizan values and piecewise dyadic data |
| `number_game.rs`, `nimber_game.rs` | number- and nimber-valued game subclasses |
| `coin_turning.rs` | turning games and nim-product oracle |
| `hackenbush.rs` | one graph with partizan, surreal, and all-green nim evaluators |
| `heating.rs`, `thermography.rs`, `tropical_thermography.rs` | cooling/heating, Norton operations, thermographs, tropical comparison |
| `atomic_weight.rs` | all-small atomic weight |
| `lexicode.rs` | mex/turning-game construction of binary and nim lexicodes |
| `game_exterior/` | exterior algebra of the game group and checked local Clifford data |

## Category boundaries

- Short games under disjunctive sum form an abelian group, not a commutative
  ring. The exterior algebra over `Integer` is valid; a generic Clifford
  scalar structure on all games is not.
- `Game` is an acyclic `Arc` tree. Cyclic positions belong in `LoopyGraph` or
  `LoopyPartizanGraph`; thermography is finite short-game machinery.
- `NumberGame` and `NimberGame` expose genuine field-like subclasses with their
  own arithmetic. Do not generalize their multiplication to arbitrary games.
- `GameClifford::with_quadratic_data` validates data on a chosen finite quotient.
  It does not provide ambient-coherent nonzero torsion data; the paper proves
  such data collapse on torsion under the stated coherence hypotheses.

## Operational conventions

- Canonical `Display` is the public rendering. `structural_string` fingerprints
  a supplied tree; `canonical_string` reduces first and is a value key.
- `nim_mul_mex` is the exponential game-definition oracle for small values.
  Use algebraic nim multiplication for computation.
- `nim_moves(&Vec<u128>)` intentionally matches a generic `Fn(&P)` signature.
- Atomic weight's integer branch compares raw option games; do not replace it
  by a maximum of rounded option weights.
- `Pl` thermograph walls do not implement `Semiring` because they lack a
  representable infinite identity. Law tests belong to `Tropical<MaxPlus>` and
  `Tropical<MinPlus>`.
- Preserve the shared cooling tail between direct and tropical thermography;
  golden tests pin equality.

## Research boundaries

- The pass-free weighted-source Witt--FIFO construction realizes finite
  `F_2`-valued quadratic zero sets in impartial normal play. It uses a public
  matching frame.
- General isolated-dummy FIFO linking remains open. Bounded graph censuses are
  evidence only.
- The intrinsic Brown selector is one partizan game, not a synchronized product
  or terminal relabeling.
- Thermography and valued-field Newton polygons share tropical algebra but do
  not admit the stronger dyadic-compatible identification ruled out in the
  thermography paper.

## Verification

Run focused game-law/golden tests and `cargo test --workspace`. For changes to a
paper theorem, also build the relevant Lean module and paper. New bounded search
code must expose its budget and distinguish exhaustion from a mathematical
negative result.
