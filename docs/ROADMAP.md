# Engineering and feature roadmap

This file contains work that is not an unresolved theorem in `OPEN.md`.
Entries are proposals, not commitments; a new implementation must still earn
its scope against the current architecture.

## Complete existing joins

| slug | current missing join |
| --- | --- |
| `clifford-center` | materialize centers/even centers as discriminant etale algebras and compare with Brauer--Wall coordinates |
| `milnor-k` | expose degree-at-most-two mod-2 Milnor symbols behind the existing `e_n` and residue maps |
| `hermitian-restriction` | compose Hermitian forms with trace/restriction of scalars and the ordinary classifiers |
| `springer-ramified` | add a named, tested ramified-extension Springer path with the correct value-group parity |
| `finite-field-invariants` | generalize level, Pythagoras number, and u-invariant reports from prime fields to shipped extension fields |
| `char2-spinor-norm` | implement the additive characteristic-two spinor norm from vector-symmetry factorizations |
| `brauer-algebras` | construct explicit cyclic/quaternion algebra representatives for computed Brauer classes |
| `spine-closure` | test lattice-to-Clifford-to-Brauer/Brown/signature agreement end to end |
| `weil-coherence` | compare discriminant-form Weil matrices with extraspecial/Heisenberg intertwiners projectively |
| `genus-hasse-crosscheck` | cross-check canonical local genus symbols against independent Hilbert/Hasse isotropy |
| `eichler` | expose the indefinite rank-at-least-three genus-to-class predicate |
| `pary-theta` | add the odd-prime code weight-enumerator to Construction-A theta map |
| `laurent-galois` | implement unramified coefficient extensions of Laurent fields with Frobenius/trace/norm |
| `hyperfield` | make valuation tropicalization strict through a tropical hyperfield type |
| `guy-smith` | turn bounded octal periodicity observations into checked Guy--Smith certificates |
| `witt-fifo-arena` | materialize the paper's weighted-source matching arena as a Rust object |
| `brown-selector` | expose the intrinsic four-outcome Brown selector as a game constructor |
| `res-cores` | test restriction/corestriction and projection formulas across Witt and Brauer surfaces |

Small verification joins:

- Newton polygons over `Qq`;
- checked ordinal square roots inside the supported tower;
- `gold_form`/trace-form agreement at the shared field sizes and agreement of
  the trace--Frobenius polar matrix with the Clifford outermorphism;
- stacked `Surcomplex<Qp>` and `Ramified<Qq>` local-functor tests;
- property-law coverage for every exact scalar marker;
- either a `RationalFunction` classification facade or an explicit domain
  boundary;
- an explicit coordinate permutation between `lexicode(24,8)` and the shipped
  Golay code.

Small structural cleanup: fold the ordinal-local factor helpers together,
move the crate-private polynomial factorizer beside the polynomial arithmetic,
and finish canonical Python `repr` coverage for nonglossary game, scalar, and
engine types.

Python API parity remains incomplete at a small set of already-public Rust
surfaces. Bind, in priority order: finite quadratic modules and Nikulin
existence; extraspecial groups and the Heisenberg--Weil representation; the
function-field Brauer--Wall class; the Niemeier/Eisenstein catalogue;
characteristic-two `witt_decompose`; `LexicodeTurningGame`; the `Cga.alg`
accessor together with an unambiguous `Cga.meet` contract; and ordinal finite
subfield degree. Keep the generated stub and per-backend type separation in
the same change as each binding.

Lower-priority parity work covers `cyclic_algebra_trace_form`, algebraic FQM
Gauss phases, constructive Weyl versors, and the Laurent constructor name.

## Paper and publication checks

| paper | remaining work |
| --- | --- |
| `goldarf` | author read-through; pin the companion-repository citation to an exact public revision; prepare cover letter and arXiv/submission package |
| `thermo_newton` | before asserting literature novelty, manually check *Winning Ways* Chapter 8 and Siegel Section III.3; rerun the bounded deep stress harness for publication counts |
| game-exterior appendix | record the exact theorem number for the cited Moews structure theorem in Siegel's *Combinatorial Game Theory* |
| misere-quotient corollary | verify the regularity hypothesis of Plambeck--Siegel Theorem 6.4 before relying on the conditional group-quotient bound |
| `transfinite_arf` | prepare the proved reusable characteristic-two classification for an upstream Mathlib contribution |

Reference files need not be vendored, but every cited result must have complete,
checked bibliographic metadata.

## Grundy language

The normative current language is `grundy/docs/spec.md`. Proposed sequence:

1. structural work: ordinal sum, consolidation with the games loopy model,
   and a host-stack floor or trampoline that removes `E_StackDepth` as a
   semantic limit while retaining explicit fuel and graph budgets;
2. loopy envelope: stops, mean/temperature access, stopper canonicalization,
   and sided comparison;
3. public-release gate: settle the public name and package boundary, ship an
   installable binary, curate runnable examples and a mathematical language
   note, and complete crate metadata;
4. higher-order map/fold over the three container shapes.

The crate remains `publish = false` until the public-release gate is met.

## New mathematical features

| slug | feature |
| --- | --- |
| `z4-codes` | quaternary codes and Gray-map joins to Brown invariants and lattices |
| `barnes-wall-tower` | recursive Barnes--Wall lattices beyond the rank-16 certificate |
| `weyl-algebra` | Clifford realization of Weyl-algebra/differential operators |
| `pointed-mtc` | pointed modular tensor categories from finite quadratic modules |
| `polar-spaces` | finite orthogonal/symplectic polar spaces and incidence games |
| `matroid-tutte` | matroid/Tutte bridges for codes, isotropic systems, and games |
| `octonions` | octonionic/triality layer tied to `Cl_8` and integral lattices |
| `lorentzian` | Lorentzian lattices and hyperbolic reflection data |

## Design decisions before implementation

- a capped Hahn completion for infinite surreal series;
- level-`N` modular-form machinery for non-unimodular theta series;
- general Smith--Minkowski--Siegel local densities;
- explicit rank-24 neighbor enumeration;
- a wider exact carrier for rank-32 mass calculations;
- a standalone dyadic `Q_2` Witt/Springer decomposition;
- surreal exponentiation and CM-lattice arithmetic.

## Deferred research-sized infrastructure

- spinor genera require local spinor-norm images and adelic class bookkeeping;
- wild norm-residue symbols require genuine local class field theory;
- the characteristic-`p` Drinfeld/Carlitz mirror of the integral wing is a
  separate large project.

## Exploratory instruments

- Complete the echo-family sweep over ko windows, pass semantics, pair touches,
  and no-dummy controls. This maps the mechanism; it is not a prerequisite for
  the Gold--Arf theorem.
- Retarget the octal search from elementary-abelian group quotients to
  nongroup monoids whose kernel admits an explicitly checked `F_2` labeling.
  Verify that the labeling is a monoid homomorphism before fitting a quadric.
