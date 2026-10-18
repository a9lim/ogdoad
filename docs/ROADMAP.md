# Roadmap

This file tracks unfinished engineering and new-feature work, plus research
directions not yet sharp enough to state as open problems. Every entry names
its completion criterion. Unresolved theorems belong only in
[`OPEN.md`](OPEN.md).

## Toward the open problems

Engineering whose output is evidence or infrastructure for the live problems.
None of it closes a problem by itself.

| work | completion criterion |
| --- | --- |
| exact misère table checker | check Siegel's valid-transition-table conditions (parity, completeness, product closure, a supplied rank) and the trace criterion as an exact certificate in `games`, independent of the bounded quotient search; reject the known no-self and inert-pad obstructions with the violated condition named |
| small-order realization atlas | a reproducible atlas of abstract misère quotients of small order, each marked realized by a certified finite octal code (trace criterion plus periodic certificate), excluded by a proved obstruction, or unresolved; bounded search over codes is reported as such unless the searched class is proved exhaustive |
| Grundy prefix certificates | extend the exact all-multiplicity quotient presentations of misère Grundy's game past heap 18, with every translation row and separating context exported as a replayable certificate |
| certified misère quotients in grundy | a sampled quotient becomes a `Claim` exactly when a checked theorem (periodicity or pretension) covers the whole universe, with the `OPEN.md` §3 boundary stated in the claim |
| FIFO certificate search | a Rust solver for the linking game that exports, per graph and seat, a strategy certificate checkable independently of the solver; reproduce the eight-real-vertex census, then extend exact evidence past it |

## Mathematical joins

Additions that connect already public subsystems.

| work | completion criterion |
| --- | --- |
| ramified Springer | a named ramified-extension path with correct value-group parity and independent tests |
| explicit Brauer representatives | materialize cyclic or quaternion algebras for computed classes and check them against the existing Brauer, Brauer--Wall, and Weyl `p`-symbol reports |
| quadratic algebras | the rank-two context `S[u]/(u^2 - t*u + n)` with canonical conjugation, trace, norm, partial inverse, and split/étale/nonreduced classification on supported fields; recover `Surcomplex` as `u^2 = -1` and materialize computed Clifford centers as operational quadratic algebras |
| stabilizer states as Brown refinements | represent a stabilizer state by an affine support and a `Z/4`-valued quadratic refinement (Dehaene--De Moor, *Phys. Rev. A* 68, 2003), so its phase function is a Brown refinement; in support coordinates with `q(0) = 0` and a nonsingular Brown polar form (diagonal included), check that the unnormalized phase sum over a `d`-dimensional support is `2^(d/2) exp(2 pi i beta/8)`, with `beta` the Brown invariant in `src/forms/char2/brown.rs`'s convention, against the existing Brown and discriminant-form Gauss-phase code; derive CSS codes from supported linear codes with bounded parameter and logical-operator certificates whose commutation agrees with the symplectic and Heisenberg--Weil representations |

## New mathematics

New areas begin with one auditable construction and an explicit law or
certificate boundary.

| work | completion criterion |
| --- | --- |
| Hermitian lattices | exact Gaussian- and Eisenstein-integral Hermitian Gram forms with dual, discriminant, and restriction-of-scalars bridges; Construction A for the corresponding codes; the Coxeter--Todd lattice, with its ordinary integral invariants verified through the existing lattice, genus, and theta surfaces |
| representable matroids | finite-field representable matroids with rank, circuits, flats, duality, deletion/contraction, and a budgeted Tutte polynomial; Greene's theorem checked against independently computed code weight enumerators |
| Weyl D-modules | admissible and weighted elimination PBW orders; certificate-producing left reduction and `S`-polynomials over supported exact fields; a budgeted Buchberger procedure with distinct complete, exhausted, and unsupported-coefficient outcomes; left-ideal membership, cyclic module presentations, symbol ideals, and bounded characteristic-variety or holonomicity reports. Every positive membership carries a replayable combination certificate, and a small source-backed example suite agrees with an independent source before restriction, integration, de Rham, or Bernstein--Sato work begins |
| Weyl endomorphisms and the `p`-centre | checked polynomial (not only affine) Weyl endomorphisms whose generator images are verified to satisfy the commutator relations; composition under budgets; reduction of integral endomorphisms modulo `p`; and, for the standard algebra `A_n(k)` over a field of characteristic `p`, the induced polynomial map on the centre `k[x_i^p, d_i^p]`. On every example, check that images of central generators are central and polynomial in them, and test the cited Azumaya criterion that a `k`-algebra endomorphism of `A_n(k)` is an automorphism exactly when its centre restriction is (Belov-Kanel--Kontsevich, *Moscow Math. J.* 7, 2007; Adjamagbo--Charbonnel--van den Essen, arXiv:math/0509188) rather than assuming it; degenerate alternating presentations need their own statement |

## Engineering and API

| work | completion criterion |
| --- | --- |
| arbitrary-width nim multiplication | implement the proved affine transforms and primitive Artin--Schreier tower of `writeups/nim_fast_multiplication.tex`; agree exhaustively with the mex/direct oracle on small fields and differentially with the `u128` backend on every supported width; measure the crossover and keep the current path below it |

New Python bindings preserve per-backend type separation and update the
generated stub in the same commit.

## Grundy language

The contract is `grundy/docs/spec.md`: typed rulesets whose answers are
exact values, verified claims, or sampled `Bounded` values. The crate stays
unpublished until the publication row is complete.

| work | completion criterion |
| --- | --- |
| loopy impartial values | generalized Sprague--Grundy values (infinite labels with counters) for cyclic rulesets, distinguishing ambiguous, absent, and over-budget, building on and checked against the engine's certified loopy nim values and sidling solver |
| sided loopy values | onside/offside and stopper canonical forms, so `Form` relations and `canon` extend beyond finite forms and stopper pairs |
| ordinal sum | expose the engine's `Game::ordinal_sum` and add a `Form` version, with surface syntax that does not collide with `:` annotation, display recognition, and law tests |
| exported certificates | outcome, Grundy, and separation witnesses accepted by a checker in `formal/` |
| host-independent nested evaluation | resumable ruleset exploration and game-equation reduction, so a move function or equation operand runs on the evaluator's heap stack and recursion through them is held to the call budget; today each is a fresh evaluation from host code, and a chain of them is refused by a measured host-stack guard whose reach depends on the build |
| publication | the name and package boundary settled, an installable binary, curated examples, and a mathematical language note |

## Papers

- Give every paper an author read-through and check all cited theorem numbers.
- Check the thermography novelty boundary against *Winning Ways*, Chapter 8,
  and Siegel, Section III.3, before making a literature claim.
- Prepare the characteristic-two classification for a Mathlib contribution.
- Prepare stable submission artifacts for the finished papers; the tracked
  `.tex` and `.bib` files remain the source of truth.

## Research directions

Longer-horizon programs, each with a first concrete target. An entry
graduates when it has a precise conjecture, construction problem, or
classification target with an auditable completion criterion; it then moves
to `OPEN.md`, and the front list in `AGENTS.md` changes in the same commit.

| direction | first concrete target |
| --- | --- |
| Wiedemann siblings | `excess.tex` proves that the Conway--Fermat torus element `u_n` and Wiedemann's `x_n` are distinct selections of the same Fermat torus from level three on (their trace-compatible towers differ in relative norm), and that Voloch's lower bound for `x_n`, which uses the 2-primary torsion of an ordinary curve, does not carry over in its standard form to the supersingular realization `u_(n+1) = g(P_n)`, on which Frobenius acts through a thin subgroup of order `2^(n+2)`. Search for a realization that would transfer it: `u_n` (or `c_n`) as a fixed function of torsion points whose order is polynomial in their degree and whose cyclic group is Frobenius-stable, on the ordinary curves over `F_2` and `F_4` at levels `n <= 6`, or a proof that no fixed function of bounded degree on those curves gives one; even and non-integer multipliers on the supersingular curve are the other untested routes. Decide also whether `ord(P_n) = F_n` for every `n` (true for `2 <= n <= 6`), on which the sharp form of the thinness statement depends. A realization would be the independent ancestry input `OPEN.md` §2 says a proof needs |
| ko thermography | a machine-checked thermograph for loopy games with kos, validated against the known generalized-thermography examples, then its tropical structure; the linking arena's one-step ko is the in-house test case |
| lexicode residuals | decide whether a lexicographic construction reaches a rootless rank-24 lattice — binary Construction A always contains the coordinate roots, so the Golay lexicode `L(24, 8)` gives the Niemeier lattice with root system `A_1^24`, not Leech — or state exactly which nimber-subfield scalars preserve base-`2^k` lexicodes when `k` is not a power of two |

## Deliberately deferred

Spinor genera, wild norm-residue symbols, general local-density machinery,
rank-24 neighbor enumeration, infinite Hahn completions, and a
Drinfeld--Carlitz analogue of the integral wing each require a new subsystem.
They should not be approximated through ad hoc branches in the current APIs.
