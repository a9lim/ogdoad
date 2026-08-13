# Lean formalization

`formal/` is a standalone Lean 4 project pinned by `lean-toolchain` and
`lake-manifest.json`. It kernel-checks load-bearing algebraic and combinatorial
ingredients from the live papers. It contains no `sorry`, `admit`, or custom
`axiom` declarations.

```sh
cd formal
lake build --wfail
```

The Rust implementation, finite-field arithmetic, external academic theorems,
and paper-level compositions are not silently imported into Lean. Each group
below states its boundary.

## Closed algebraic results

| module | checked content | external or paper-level boundary |
| --- | --- | --- |
| `Off.lean`, `SymplecticBasis.lean`, `CharTwoClassification.lean` | exact Frobenius/Artin--Schreier plane lemmas, a complete recursive orthogonal symplectic basis, an explicit `QuadraticMap.IsometryEquiv` to the two coordinate normal forms, and the iff classification by ambient, polar-radical, and quadratic-radical dimensions | a set-sized algebraically closed characteristic-two field is the finite-form proxy for full `On_2`; Conway's proper-class field is not a Lean type |
| `BrownGame.lean`, `BrownSelectorPGame.lean` | canonical `q = lift(ell)+2Q` split and converse, corrected polar form, two-divisible collapse, and one directly defined finite partizan game tree whose four normal-play outcomes decode `Z/4` | Moews's short-game group theorem remains an external cited input |
| `GameExterior.lean` | the `intersection_k 4^k R` coefficient theorem, root-free two-primary torsion collapse, polarization, torsion-coset invariance, and the named four-zero and integral vanishing consequences | two-divisibility and two-primary torsion for short games are supplied by Moews's theorem |
| `GoldDiagonal.lean` | quadratic-tower trace blocks, trace-dual reconstruction, Artin--Schreier lifting, and image-equals-trace-kernel over finite fields | concrete nim arithmetic and basis recursion remain in Rust |
| `GoldExtraspecial.lean`, `GoldExtraspecialTrace.lean` | biadditive cocycle group, its actual field-trace/Frobenius Gold specialization, square/commutator/center laws, the `(c,1)` cocycle-preserving basis for every trace-one cardinality-four field, and an explicit multiplicative equivalence from the resulting Gold extension to Mathlib's quaternion group, instantiated on Mathlib's canonical `GF(4)` | identifying Mathlib finite-field operations with the Rust/nimber implementation is an executable cross-backend question |

## Gold--Arf realization ingredients

| module | checked content |
| --- | --- |
| `FifoMatching.lean` | both-seat zero-flip strategy for matching-plus-isolates boards |
| `ImpartialRealizer.lean` | pass-free transition, exact even clock, safe-front induction, and one-move charge tail |
| `PhysicalDeferred.lean` | literal second-opening and close-charge transitions, two involutive ledger conjugacies, and bidirectional transport of complete normal-play strategy trees |
| `GoldMatchingAlgebra.lean` | quadratic expansion in an adapted public Witt frame |
| `WittFrame.lean` | deterministic flattening of the symplectic decomposition to an actual basis with a certified public partial matching |
| `GoldArena.lean` | original-frame source, active-coordinate loading, public and weighted matching graphs, exact edge/close ledger totals, and `gold_literal_root_isP_iff` |
| `GoldNoEvaluator.lean` | transcript-span and observation-weight lower bounds |
| `GoldBlockCompression.lean` | induced block quadratic form and independent block indicators |
| `GoldForkPadding.lean` | outcome-preserving unavoidable-fork padding |
| `GoldSemantics.lean` | independent phase-aware terminal compiler retained as a comparison surface |

`GoldArena.gold_literal_root_isP_iff` is the end-to-end realization theorem: for every
finite binary quadratic refinement, ordered public basis, and input, the
constructed loaded root is a `P`-position exactly when the quadratic value is
zero. Its root score is zero; OPEN charges a weighted edge exactly when its
second endpoint opens, and CLOSE charges the public strategic label. Lean
proves that this literal tree is conjugate, state by state and strategy tree by
strategy tree, to the deferred safe-front compiler, and separately proves that
the root edge and close potentials are exactly the three quadratic ledgers.
The public graph is independent of the refinement, and refinement-sensitive
source edges read only the active original-basis singleton values.

The Rust finite-field/nimber implementation is not definitionally equated to
Mathlib's abstract finite fields. `GoldDiagonal.lean` checks the field-theoretic
source construction, while runtime agreement remains covered by the separate
executable verification surface.

## Open FIFO linking frontier

`Fifo.lean` defines the authoritative transition system, proves termination,
strategy determinacy interfaces, queue and cut invariants, score translation,
singleton tails, the edgeless case, and close-first contractions. It defines

```lean
FifoLinkingTheorem : Prop
```

but does not prove or assume it.

The companion modules isolate the exact remaining causal obstruction:

| modules | role |
| --- | --- |
| `FifoStrategy`, `FifoAffine`, `FifoWinningRegion` | data-carrying policies, strategy-indexed affine response spaces, and exact Bellman saturation |
| `FifoNormalization`, `FifoRootSelector` | complete local reply fans, close-first exclusion, and the asymmetric root-selector boundary |
| `FifoCausal`, `FifoNeutralPair` | charged-close transport, dummy intervals, and ko-wall repair |
| `FifoCrossDescent`, `FifoCrossClose`, `FifoMixedCross` | OPEN/OPEN, CLOSE/CLOSE, and mixed crossed descendants with their phase defects |
| `FifoSameOpenBraid`, `FifoMinHotCurvature` | same-OPEN carrier and the surviving minimum-hot curvature |
| `FifoDummyDeletion`, `FifoDummyExitCarrier` | exact dummy-deletion walls and the parent-plus-even-children carrier |
| `FifoOuterFan`, `FifoProtectedFan`, `FifoCrossExitIncidence` | prefix-free fans and the residual continuation-incidence target |
| `FifoInterlace`, `FifoSymmetry` | endpoint-word/local-complementation and turn/score symmetry limits |
| `FifoHub` | score-erased schedule relabelling, live-star transport, transposition defects, and graph-congruence algebra; no root-value conjugacy |
| `FifoEmptyQueue`, `FifoBlockInduction`, `FifoOutcome`, `FifoOutcomeBlock` | empty-to-empty block parity, conditional first-return splicing, exact four-valued score-debt transport, and the proof that stopping at complete favorable outcome sheets is equivalent to the original game; the scalar/parity mover premise is false |
| `FifoOutcomeAlgebra`, `FifoOutcomeSwitch` | the four-valued sheet is not contextual under a ko-locked neutral pair; even a both-even dummy-free root has reversed active dummy orders with opposite outcomes for one seat |
| `FifoTreeTrace`, `FifoQPotential` | kernel-checked obstructions to the raw complete-leaf sum and to pointwise queue-cut-potential normalization |
| `FifoPairState` | every score-zero mover failure with an OPEN available yields a lower minimum-hot singleton wall whose charged endpoints are real; ancestry from the original strategy is not supplied |
| `FifoStrategyBadAncestry`, `FifoStrategyBadAncestryClear` | minimize the residual target inside one exact odd strategy, retain root prefixes and the complete immediate parent fan, and reduce every minimal bad predecessor to the charged-CLOSE spike or protected-singleton case; the neutral-CLOSE and clear-OPEN cases are impossible |
| `FifoFirstSeatRoot` | exact first-seat Bellman normal form: one chosen initial OPEN followed by the complete universal second-OPEN fan; the existence of such a winning opener remains open |
| `FifoBadArcCycle`, `FifoFirstSeatStrategy` | one first-seat odd strategy supplies a fixed-point-free selected reply map with common-root ancestry; cycle prefixes cancel, but continuation augmentation still obstructs contraction |
| `FifoFunctionalDigraphBoundary` | even cycles plus genuine feeding in-trees still admit an isolated-dummy separator evaluating every selected arc prefix to one; functional-digraph incidence alone cannot supply the odd contraction |
| `FifoDummyFront` | exact neutral dummy-front commuting diamond and the necessary consumed-pair selector; opening the dummy first relocates rather than removes the real-pair obligation |
| `FifoDummyFrontAffine` | the odd-order dummy-front legal fan is even and its projected OPEN-prefix sum is the surviving real star, which no local odd response point can equal; earlier ancestry is necessary |
| `FifoStrategyInteraction`, `FifoSelfPlay` | complementary-seat odd policies share a compatible odd terminal, whereas same-seat policies at score-and-turn-conjugate states are impossible; dummy timing supplies only the controller phase and real-front curvature leaves a one-front/edge defect, so two-copy self-play still needs an earlier sibling |
| `FifoSeparatorFlow`, `FifoThreeSiblingBoundary` | an odd zero-prefix fan retains separator value one in its continuation residue, and immediate fan completeness does not force any earlier OPEN sibling to select the lag-removing CLOSE; the missing repair must be an odd cross-coset incidence |
| `FifoRootCongruence` | cross-graph strategy interaction produces one common public trace and moment; a winner change under an elementary graph congruence forces the exact row-defect functional to evaluate to one, rather than proving root-value invariance |

Every theorem in these modules is subsidiary. None yet supplies the selection
of compatible earlier siblings and continuation cosets in the two surviving
minimal-bad ancestries. That causal factor extension is the mathematical
frontier summarized in `docs/OPEN.md` and proved up to its exact boundary in
`writeups/linking_affine.tex`.

## Open Lenstra-excess frontier

`Excess.lean` checks algebraic ingredients of the four-arm reduction:

- the first-non-`p`-th-power interface and group-theoretic lower bound;
- the corrected characteristic-two sparse norm;
- exact cyclic-group and finite-field power criteria;
- finite primality/order/factor screens used by replayable certificates;
- two-face cross-ratio and three-face parity identities for the cubical
  primitive-support coordinate in the multicomponent zero arm;
- the two-prime coboundary identity placing the exceptional arm in that same
  cubical primitive-support coordinate;
- polynomial, trace, norm, Frobenius, Kummer, and recurrence identities used
  to reduce the selected `Z`, `O`, `C`, and `D` coordinates.

It defines

```lean
DPrimeTarget ... : Prop
```

as the universal exceptional-column target. The declaration is neither an
axiom nor a proof. More generally, the Lean reductions recover selected order
coordinates but do not prove their universal nonvanishing. External finite
certificates and source-backed rows remain explicitly separate from kernel
theorems. See `writeups/excess.tex` and `docs/OPEN.md`.

## Build and review rules

- Keep the project warning-clean and placeholder-free.
- Prefer transparent definitions and ordinary `decide` when finite evaluation
  remains practical; use stronger evaluators only with a documented reason.
- State external inputs as theorem parameters or paper assumptions, not custom
  axioms.
- When a paper claim changes, update this theorem map and the paper's formal
  verification section together.
- A passing `lake build` verifies only the declarations actually present. It
  does not validate a prose composition that has not been encoded.
