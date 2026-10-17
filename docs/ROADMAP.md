# Engineering roadmap

This file tracks unfinished engineering and publication work, plus research
directions not yet sharp enough to state as conjectures. Unresolved theorems
belong only in [`OPEN.md`](OPEN.md).

## Core mathematical joins

Highest-value additions are the joins between already public subsystems:

| work | completion criterion |
| --- | --- |
| ramified Springer | add a named ramified-extension path with correct value-group parity and independent tests |
| explicit Brauer representatives | materialize cyclic or quaternion algebras for computed classes |

## Additional mathematics

New self-contained mathematical areas begin with one auditable construction
and an explicit law or certificate boundary. They remain engineering programs
here unless they produce a sharp unresolved statement for `OPEN.md`.

| work | completion criterion |
| --- | --- |
| quadratic algebras | implement the rank-two context `S[u]/(u^2 - t*u + n)` with canonical conjugation, trace, norm, partial inverse, and split/etale/nonreduced classification on supported fields; recover `Surcomplex` as the `u^2 = -1` specialization and materialize computed Clifford centers as operational quadratic algebras |
| Hermitian lattices | add exact Gaussian- and Eisenstein-integral Hermitian Gram forms with dual, discriminant, and restriction-of-scalars bridges; implement the corresponding code Construction A, construct the Coxeter--Todd lattice, and independently verify its ordinary integral invariants through the existing lattice, genus, and theta surfaces |
| representable matroids | construct finite-field representable matroids with rank, circuits, flats, duality, deletion/contraction, and a budgeted Tutte polynomial; verify Greene's theorem against independently computed code weight enumerators |
| stabilizer codes | construct finite symplectic Pauli spaces and isotropic stabilizers, derive CSS codes from supported linear codes, and return bounded certificates for parameters and logical operators whose commutation and encoded dimension agree with the independent symplectic and Heisenberg representations |

## API and maintenance

| work | completion criterion |
| --- | --- |
| arbitrary-width nim multiplication | implement the proved affine transforms and primitive Artin--Schreier tower from `writeups/nim_fast_multiplication.tex`; exhaustively agree with the mex/direct oracle on small fields, differentially agree with the `u128` backend on every supported width, and measure the crossover while retaining the current path below it |
| Weyl pillar | carry out the certified computational D-module wave in [`WEYL.md`](WEYL.md), preserving finite-support, characteristic, and budget boundaries at every layer |

New Python bindings must preserve per-backend type separation and update the
generated stub in the same commit.

## Grundy language

The current contract is `grundy/docs/spec.md`: typed rulesets whose answers
are exact, verified claims, or sampled `Bounded` values.

| work | completion criterion |
| --- | --- |
| certified misère quotients | a sampled quotient becomes a `Claim` exactly when a checked theorem (periodicity or pretension) covers the whole universe, with the `docs/OPEN.md` §3 boundary stated in the claim |
| loopy impartial values | generalized Sprague–Grundy values (infinite labels with counters) for cyclic rulesets, distinguishing ambiguous, absent, and over-budget, checked against the engine's sidling solver |
| sided loopy values | onside/offside and stopper canonical forms, so `Form` relations and `canon` extend beyond finite forms and stopper pairs |
| ordinal sum | `G:H` on `Game` and `Form`, with display recognition and law tests |
| exported certificates | outcome, Grundy, and separation witnesses accepted by a checker in `formal/` |
| host-independent depth | an explicit-stack evaluator, so recursion depth is a budget rather than a host limit |
| publication | the name and package boundary settled, an installable binary, curated examples, and a mathematical language note |

The crate remains unpublished until publication is complete.

## Papers

- Give every paper an author read-through and check all cited theorem numbers.
- Check the thermography novelty boundary against *Winning Ways*, Chapter 8,
  and Siegel, Section III.3 before making a literature claim.
- Prepare the characteristic-two classification for a Mathlib contribution.
- Prepare stable submission artifacts for the finished papers; the tracked
  `.tex` and `.bib` files remain the source of truth.

## Research directions

Longer-horizon mathematical programs. No entry here is yet sharp enough for
the live research docket; each names its first concrete target. An entry
graduates when it has a precise conjecture, construction problem, or
classification target with an auditable completion criterion. It then moves to
`OPEN.md`, with the front list in `AGENTS.md` updated in the same commit.

| direction | first concrete target |
| --- | --- |
| lexicode residuals | sharpen one of: asymptotic goodness of lexicodes; greedy reachability of a rootless rank-24 endpoint (the current constructor terminates at a root-full even unimodular lattice); the exact field-linearity boundary for nim-alphabet lexicodes |
| ko thermography | a machine-checked thermograph for loopy games with kos, validated against the known generalized-thermography examples, then its tropical structure; the linking arena's one-step ko is the in-house test case |

## Deliberately deferred

Spinor genera, wild norm-residue symbols, general local-density machinery,
rank-24 neighbor enumeration, infinite Hahn completions, and a
Drinfeld--Carlitz analogue of the integral wing each require a new subsystem.
They should not be approximated through ad hoc branches in the current APIs.
