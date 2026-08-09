# Lean formalization

This standalone Lean 4 project tests how much of the current proof threads
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

## Lenstra excess

[`Ogdoad/Excess.lean`](Ogdoad/Excess.lean) formalizes the theorem-level spine
of the exceptional `2·3^k` column:

- the first-non-`p`-th-power definition of finite excess;
- the group-theoretic lower bound: a shared order class coprime to `p` makes
  the `0,1,2,3` translates `p`-th powers, hence `m_p ≥ 4`;
- the corrected norm
  `(kappa+a)(kappa+a+1) = kappa²+kappa+(a²+a)`, specializing to
  `kappa²+kappa+omega`;
- the exact cyclic-group and finite-field Euler-quotient criteria for being a
  `p`-th power; and
- the open target `DPrimeTarget M`, namely `Psi_k | orderOf (M k)` for every
  level.

Lean also reduces the complete `k=2,...,6` factor products and every recorded
`ord_p(2)=2·3^k` residue screen.  Primality is proved locally through `k=4`;
the larger factors retain the paper's explicit source-assisted boundary.
These are arithmetic input checks, not a proof that the distinguished circle
element `M_k` has the required order.  The universal `D'_k` assertion remains
open, as do the finite `M_k` computations beyond the separately maintained
Python certificate.

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
