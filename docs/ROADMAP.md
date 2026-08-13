# Engineering roadmap

This file tracks unfinished engineering and publication work. Unresolved
theorems belong only in [`OPEN.md`](OPEN.md).

## Core mathematical joins

Highest-value additions are the joins between already public subsystems:

| work | completion criterion |
| --- | --- |
| Clifford centers | construct centers and even centers as discriminant etale algebras and compare their classes with the Brauer--Wall coordinates |
| Milnor symbols | expose the degree-at-most-two mod-two symbols underlying the existing residue and `e_n` maps |
| Hermitian restriction | compose trace/restriction of scalars with the ordinary quadratic classifiers |
| ramified Springer | add a named ramified-extension path with correct value-group parity and independent tests |
| finite-field invariants | lift level, Pythagoras number, and u-invariant reporting from prime fields to shipped extensions |
| characteristic-two spinor norm | construct the additive spinor norm from vector-symmetry factorizations |
| explicit Brauer representatives | materialize cyclic or quaternion algebras for computed classes |
| integral coherence | test lattice, discriminant, Weil, Clifford, Brown, and signature invariants across the existing bridges |
| local/global coherence | cross-check genus symbols, Hilbert/Hasse isotropy, and restriction/corestriction formulas |

The games pillar still needs Rust constructors for the proved weighted-source
Witt--FIFO arena and the intrinsic four-outcome Brown selector. Octal
periodicity should become a checked Guy--Smith certificate before entering the
public API.

## API and maintenance

- Finish canonical Python `repr` coverage.
- Keep Python parity focused on already public Rust surfaces: finite quadratic
  modules, extraspecial/Heisenberg--Weil objects, function-field Brauer--Wall,
  Niemeier data, characteristic-two Witt decomposition, lexicode games, CGA
  accessors, and ordinal finite-subfield degree.

Every binding change must preserve per-backend type separation and update the
generated stub in the same commit.

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

## Deliberately deferred

Spinor genera, wild norm-residue symbols, general local-density machinery,
rank-24 neighbor enumeration, infinite Hahn completions, and a
Drinfeld--Carlitz analogue of the integral wing each require a new subsystem.
They should not be approximated through ad hoc branches in the current APIs.
