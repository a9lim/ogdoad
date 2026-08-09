# Lean formalization

This standalone Lean 4 project tests how much of the two current proof threads
can be moved from checked prose and exhaustive computation into a proof kernel.
It pins Lean and mathlib independently of the Rust workspace.

```sh
cd formal
lake update       # only when intentionally refreshing the pinned manifest
lake build
```

The sources contain no `sorry`, `admit`, or custom `axiom` declarations.

## `off`

[`Ogdoad/Off.lean`](Ogdoad/Off.lean) formalizes the load-bearing algebra of the
resolved full-`On₂` classification through a set-sized algebraically closed
characteristic-two field:

- Frobenius and Artin–Schreier surjectivity;
- an explicit change of every normalized symplectic pair to a hyperbolic pair,
  preserving its plane span;
- simultaneous conversion of a supplied symplectic family; and
- the polar-radical normal form `Q = ℓ²`, with either `ℓ = 0` or a
  codimension-one zero kernel after normalizing a vector with `ℓ(e) = 1`.

The set-sized field is a proxy, not an encoding of Conway's proper class.  The
mathematical reduction is that any finite form and its finitely many algebraic
roots lie in a set-sized algebraically closed subfield.  The standard
symplectic decomposition theorem for a finite-dimensional alternating form is
used as the interface to `hyperbolic_family_of_symplectic_family`; this project
does not yet re-formalize that general linear-algebra theorem.

## FIFO linking

[`Ogdoad/Fifo.lean`](Ogdoad/Fifo.lean) gives an authoritative transition system
for the reduced odd-close parity game from `experiments/linking_game.py`:

- OPEN, FIFO CLOSE, forced PASS, ko delay, mover, and the `ZMod 2` score;
- strict rank descent, absence of nonterminal stuck states, and preservation of
  the queue/untouched invariant;
- an explicit existential/universal finite strategy tree;
- the isolated-dummy hypothesis and exact general theorem statement;
- the queue-cut potential, including CLOSE and PASS conservation and the fact
  that no flip is possible once the untouched set is empty; and
- a complete strategy proof for the edgeless base class.

`FifoLinkingTheorem` is a proposition, not an axiom or claimed theorem.  The
general isolated-dummy result remains open: the missing mathematical step is
the global causal affine-contraction/factor-extension lemma identified in
`writeups/linking_affine.tex`.  The Lean development therefore hardens the
semantics and the proved reduction spine without laundering the finite census
through `k = 8` into a proof for all finite graphs.
