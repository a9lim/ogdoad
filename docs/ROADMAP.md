# Engineering roadmap

This file tracks unfinished engineering and publication work, plus research
directions not yet sharp enough to state as conjectures. Unresolved theorems
belong only in [`OPEN.md`](OPEN.md).

## Core mathematical joins

Highest-value additions are the joins between already public subsystems:

| work | completion criterion |
| --- | --- |
| Clifford centers | construct centers and even centers as discriminant etale algebras and compare their classes with the Brauer--Wall coordinates |
| Milnor symbols | expose the degree-at-most-two mod-two symbols underlying the existing residue and `e_n` maps |
| Hermitian restriction | compose trace/restriction of scalars with the ordinary quadratic classifiers |
| ramified Springer | add a named ramified-extension path with correct value-group parity and independent tests |
| finite-field invariants | lift level, Pythagoras number, and u-invariant reporting from prime fields to supported extensions |
| characteristic-two spinor norm | construct the additive spinor norm from vector-symmetry factorizations |
| explicit Brauer representatives | materialize cyclic or quaternion algebras for computed classes |

## API and maintenance

No unfinished API-maintenance work is currently tracked. New Python bindings
must preserve per-backend type separation and update the generated stub in the
same commit.

## Grundy language

The current contract is `grundy/docs/spec.md`. The path to publication is:

1. add ordinal sum and remove host stack depth as a semantic limit while
   retaining explicit fuel and graph budgets;
2. integrate the loopy-game model, stops, mean, temperature, and sided
   comparison;
3. settle the public name and package boundary, then ship an installable binary
   with curated examples and a mathematical language note;
4. add higher-order traversal over the three container shapes.

The crate remains unpublished until step 3 is complete.

## Papers

- Give every paper an author read-through and check all cited theorem numbers.
- Check the thermography novelty boundary against *Winning Ways*, Chapter 8,
  and Siegel, Section III.3 before making a literature claim.
- Prepare the characteristic-two classification for a Mathlib contribution.
- Prepare stable submission artifacts for the finished papers; the tracked
  `.tex` and `.bib` files remain the source of truth.

## Research directions

Longer-horizon mathematical programs. No entry here is a sharp statement; each
names its first concrete target. An entry graduates when it yields a precise
conjecture with a proved reduction — that statement then moves to `OPEN.md`,
with the front list in `AGENTS.md` updated in the same commit.

| direction | first concrete target |
| --- | --- |
| nim reciprocity | an explicit Frobenius action in Conway-tower coordinates; success would evaluate the marked coordinates of `OPEN.md` §2 uniformly along ancestry and subsume all four selected-order arms |
| fast nimber multiplication | essentially-linear multiplication in nim coordinates on the Fermat tower, or a documented barrier; either outcome feeds the `scalar` backends directly |
| lexicode residuals | sharpen one of: asymptotic goodness of lexicodes; greedy reachability of a rootless rank-24 endpoint (the current constructor terminates at a root-full even unimodular lattice); the exact field-linearity boundary for nim-alphabet lexicodes |
| Witt realization over imperfect fields | extend the Gold--Arf realization pattern from finite nimber fields (perfect) to `F_2(t)`, where bilinear and quadratic classification diverge and the `Metric` `q`/`b` split carries independent content |
| semiring forms | a bilinear/quadratic layer over the `Semiring` siblings: supertropical forms (Izhakian--Knebusch--Rowen) on the idempotent side, the Hessenberg ordinal semiring on the other; motivated by the thermic-regrading obstruction — the thermic structure is not a ring, so ring-based Witt theory cannot see it. The Clifford scalar-ring boundary is untouched |
| misère realization | which finite commutative monoids occur as indistinguishability quotients; the bounded machinery in `games::misere` turns quotient censuses into conjecture material, with misère Grundy's game the canonical wild target |
| ko thermography | a machine-checked thermograph for loopy games with kos, validated against the known generalized-thermography examples, then its tropical structure; the linking arena's one-step ko is the in-house test case |

## Deliberately deferred

Spinor genera, wild norm-residue symbols, general local-density machinery,
rank-24 neighbor enumeration, infinite Hahn completions, and a
Drinfeld--Carlitz analogue of the integral wing each require a new subsystem.
They should not be approximated through ad hoc branches in the current APIs.
