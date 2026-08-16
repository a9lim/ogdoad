# Lean formalization

`formal/` is a standalone Lean 4 project pinned to Lean and Mathlib `v4.32.2`.
`Ogdoad.lean` is the umbrella import. The imported development contains no
`sorry`, `admit`, or custom `axiom` declarations.

```sh
cd formal
lake build --wfail
```

Lean checks only the declarations in this project. Rust implementations,
finite computations, source-backed data, cited theorems, and paper-level
compositions are separate evidence unless a theorem below explicitly connects
them. In particular, a declaration ending in `Target` or `Theorem` may merely
*define* a proposition; inspect whether it is followed by a proof.

## Closed results

| area | modules | kernel-checked result and boundary |
| --- | --- | --- |
| characteristic-two quadratic forms | `Off`, `SymplecticBasis`, `WittFrame`, `CharTwoClassification` | Frobenius and Artin--Schreier plane reductions, a recursive orthogonal symplectic decomposition, a deterministic adapted basis, explicit canonical-form isometries, and classification by ambient, polar-radical, and quadratic-radical dimensions. A set-sized algebraically closed field is the formal proxy for each finite piece of Conway's proper-class `On_2`. |
| game-valued obstructions and Brown selectors | `GameExterior`, `BrownGame`, `BrownSelectorPGame` | Root-divisibility forces the stated exterior/Clifford coefficients to vanish; Brown refinements split as `lift(ell) + 2Q`; one explicit finite partizan tree realizes the four Brown outcome classes. Moews's structure theorem for short games is a cited external input, not a Lean axiom. |
| Gold sources and extensions | `GoldDiagonal`, `GoldExtraspecial`, `GoldExtraspecialTrace` | Quadratic-tower trace reconstruction, Artin--Schreier lifting and trace-kernel exactness, the universal cocycle group, the trace/Frobenius Gold specialization, and the order-eight quaternion cell over the canonical `GF(4)`. Lean's abstract finite fields are not definitionally identified with the Rust nimber backend. |
| Gold--Arf arena | `FifoMatching`, `ImpartialRealizer`, `PhysicalDeferred`, `GoldMatchingAlgebra`, `GoldArena` | Both seats force zero on matching-plus-isolates boards; the pass-free compiler has exact tempo and charge semantics; literal and deferred ledgers are conjugate with strategy trees transported both ways. `GoldArena.gold_literal_root_isP_iff` is the end-to-end literal-root theorem for every finite binary quadratic refinement, public basis, and input. It does not use arbitrary-graph FIFO linking. |
| realization bounds and comparison surfaces | `GoldNoEvaluator`, `GoldBlockCompression`, `GoldForkPadding`, `GoldSemantics` | Transcript-span and observation-weight lower bounds, induced block refinements, an outcome-preserving fork-padding obstruction, and an independent payoff-to-normal-play compiler. These are auxiliary theorems, not alternate end-to-end arena constructions. |
| imperfect-field Witt realization | `WittRealizationExact`, `WittRealization`, `WittTransfer`, `WittRamification`, `WittRamifiedRestriction`, `WittSingularBoundary` | The concrete parity-zero presented coordinate space has a finite sparse trace-character compiler into literal `0/*` arenas, with equality of all outcomes equivalent to equality of presented classes. The development also checks the trace-dual Scharlau Arf calculation, finite unit-jet substitution and exact Artin--Schreier normalization, one-place and fixed-finite-family obstructions, and the quasilinear absorption isometry. The Aravire--Jacob exact sequence and local decomposition, their equivalence with the actual `W_q(F_2(t))`, and the local quadratic-form interpretation of ramified generators remain the cited bridge. |
| stable semiring quadratic pairs | `SemiringQuadratic` | Additive cancellation gives uniqueness and diagonal balance of companions; the finite polynomial model has no half of one or nonzero self-double; a symmetric balanced permutation Gram matrix is a fixed-point-free involution with zero quadratic basis labels; a cancellative additive target kills an observation identified with its double; and a generator killed by its double has only parity multiples, with noncollapse certified by a parity detector. The unique-base theorem, classical diagonalization, the Hessenberg CNF--polynomial identification, connected graph presentation, supertropical companion classification, and thermograph facts remain cited or paper-level inputs. |
| finite misere transition algebra | `MisereTransition` | A least-rank separator proves that equal option-value sets have equal values in every reduced ranked parity-correct closed table; every option lies in the corresponding meximal set; and an ultimately periodic heap word has an ultimately periodic two-heap split convolution with an explicit preperiod-crossing bound. The exact octal trace criterion, tame-family strategy, and Grundy quotients through heap 18 are paper-level theorems in `writeups/misere_natural_realization.tex`, not Lean-checked end-to-end. |

## Arbitrary-graph FIFO linking: open

`Fifo.lean` defines the terminating FIFO game and proves its basic Bellman,
rank, score-translation, queue-cut, singleton-tail, and stopped CLOSE-first
theorems. It also defines

```lean
FifoLinkingTheorem : Prop
```

for arbitrary finite graphs with an isolated dummy. The proposition is not
proved or assumed. `FifoPublicPolicyAffine` defines the graph-free target
`UniversalPublicPolicyAffine`; `FifoPublicPolicyDuality` proves

```lean
UniversalPublicPolicyAffine ↔ FifoLinkingTheorem
```

so the public-policy affine problem is an exact reformulation, not a weaker
sufficient condition. `FifoMatching` proves the matching-plus-isolates case
used by `GoldArena`.

The FIFO modules are grouped below by their current role. Modules ending in
`Boundary`, together with the small explicit countermodel modules, prove that
a proposed inference fails; none is a counterexample to the initial
isolated-dummy conjecture.

| role | modules | checked content |
| --- | --- | --- |
| semantics and affine targets | `Fifo`, `FifoStrategy`, `FifoAffine`, `FifoPublicPolicyAffine`, `FifoPublicPolicyDuality` | Exact game semantics; data-carrying fixed policies; strategy-indexed and graph-free public affine response spaces; projection away from dummy coordinates; affine separation by an isolated-dummy graph. |
| local causal calculus | `FifoCausal`, `FifoNormalization`, `FifoSymmetry`, `FifoCrossDescent`, `FifoCrossClose`, `FifoMixedCross`, `FifoSameOpenBraid`, `FifoDummyDeletion`, `FifoNeutralPair`, `FifoInterlace`, `FifoHub`, `FifoBlockReversalBoundary` | Live-star and queue-cut identities, stopped CLOSE-first exclusion, OPEN/OPEN and CLOSE/CLOSE transport, mixed and same-OPEN curvature, the exact two-wall dummy-deletion law, dummy-interval timing, relabelling, and the limits of local complementation or time reversal. |
| fan and factor geometry | `FifoDummyExitCarrier`, `FifoCrossExitIncidence`, `FifoOuterFan`, `FifoProtectedFan`, `FifoRootSelector`, `FifoMinHotCurvature`, `FifoSeparatorFlow`, `FifoThreeSiblingBoundary`, `FifoProtectedFactorBoundary`, `FifoGlobalSpliceBoundary` | Prefix cancellation for complete fans, augmentation bookkeeping, the proved first-seat root selector, minimum-hot curvature, and exact local obstructions showing why a further earlier continuation coset is required. |
| outcome and minimal-ancestry reductions | `FifoEmptyQueue`, `FifoBlockInduction`, `FifoOutcome`, `FifoOutcomeBlock`, `FifoOutcomeSwitch`, `FifoPairState`, `FifoStrategyBadAncestry`, `FifoStrategyBadAncestryClear`, `FifoProtectedBlockBoundary`, `FifoOddSpikeFactor`, `FifoOddSpikeDummyReply` | Empty-to-empty block parity, four-valued score-debt transport, exact stopped-strategy splicing, and minimization inside one odd policy. The clear-OPEN and neutral-CLOSE predecessors are excluded; the charged-CLOSE spike and protected-singleton predecessors retain a nonlocal factor obligation. |
| root, parity, and controlled-policy routes | `FifoFirstSeatRoot`, `FifoFirstSeatStrategy`, `FifoBadArcCycle`, `FifoFunctionalDigraphBoundary`, `FifoDummyFront`, `FifoDummyFrontAffine`, `FifoParitySeat`, `FifoParitySeatCloseFirst`, `FifoParityCounterNormal`, `FifoParitySeatDeviationBoundary`, `FifoParityControlledRoot`, `FifoControlledDivergence`, `FifoSingletonForkBoundary`, `FifoLiveDummyOpenFork`, `FifoCommonDummyEventBoundary` | Exact first-seat Bellman form and common-root reply map, parity-seat fan reductions, score-coupled policy divergence, and elimination of local singleton or distinct-OPEN minima. Functional-digraph, dummy-front, and leafmost-deviation data do not select the missing correlated sibling. |
| Gaussian and pair routes | `FifoRootCongruence`, `FifoGaussianElimination`, `FifoPairGaussian`, `FifoPairZeroMomentSafety`, `FifoPairZeroMomentNormal`, `FifoPairZeroMomentAdjacentBoundary`, `FifoCongruenceOutcomeBoundary`, `FifoConsumedDummyShearBoundary` | Exact graph-shear debt laws and constructive parity mates. Every alleged zero-moment-pair counterstrategy has a smaller score-zero descendant, but the condition is not recursively preserved; FIFO outcome is not an alternating-form congruence invariant. |
| positional and separator normal forms | `FifoCanonicalPositionalOdd`, `FifoPositionalSelectedEdgeBoundary`, `FifoPositionalStateDAGBoundary`, `FifoPublicPolicyTopologyBoundary`, `FifoPublicSeparatorAutomaton`, `FifoPublicSeparatorAncestry`, `FifoPublicSeparatorQueueDebt`, `FifoSeparatorBadSynchronizationBoundary`, `FifoSeparatorControlledBridgeBoundary`, `FifoLastChargedCloseBoundary` | Canonical full-state positional policies, exact one-bit separator recurrence, and the rank-minimal selected real OPEN. Its parity partner is already queued debt; history trees, state-DAG cycles, and controlled-outcome descent do not by themselves cancel it or synchronize it with the last charged CLOSE. |
| additional exact route limits | `FifoTreeTrace`, `FifoPublicPrefixQueueCutBoundary`, `FifoPublicQueueCutCounterexample`, `FifoCellSwapOutcomeBoundary`, `FifoConsumedDummyBoundary`, `FifoDistinctOpenForkBoundary`, `FifoRootGadgetBoundary`, `FifoPrivateLeafBoundary` | Exact finite Bellman certificates and structural no-go theorems rule out a raw complete-leaf sum, ancestry-local queue-cut targets, cell-swap outcome transport, reachability-only controlled descent, and purely local root-gadget or private-leaf repairs. |

The remaining theorem is global and ancestry-sensitive. At a rank-minimal
separator-one occurrence, the selected real `OPEN` enters a complete
separator-zero fan while its separator-odd partner is trapped in the existing
queue. A proof must relate that debt to the last charged `CLOSE` on the path
from the initial root and select an odd family of earlier defender siblings
whose prefixes and continuation cosets cancel the residual real-edge class.
It must cover both FIFO orders: the debt vertex may survive behind the charged
front or may open in the later neutral suffix. No current module supplies that
selection. See `../docs/OPEN.md` and `../writeups/linking_affine.tex`.

## Finite Lenstra excess: open

The module `Excess` (`Excess.lean`) proves algebraic ingredients of the
four-arm `Z/O/C/D` reduction, including:

- exact finite-cyclic-group and finite-field power/order criteria;
- the corrected characteristic-two sparse norm;
- trace, norm, Frobenius, Kummer, Dickson--Lucas, Singer, and cubical-support
  identities used by the selected-order reductions;
- transparent finite primality, factor, modular, and order screens for the
  rows explicitly encoded in the file.

The file defines `SelectedLogUnitTarget`, `ExceptionalColumnTarget`, and
`DPrimeTarget`. These declarations expose universal propositions; they do not
assume or prove them. `DPrimeTarget` is the exceptional `2 * 3^k`-column
divisibility target, not the full universal `0/1/4` theorem. Source-assisted
factor data and Python certificates remain external evidence.

For a nonzero element of a finite field, the relevant obstruction is the
exact Euler test

```text
beta^((|F^×|)/p) != 1.
```

Merely proving `p | order(beta)` loses the required primary valuation when
the ambient order contains a higher power of `p`. The selected Conway phase
is still the missing datum in each universal arm. See `../docs/OPEN.md` and
`../writeups/excess.tex`.

## Review contract

- Keep `Ogdoad.lean` synchronized with the intended build surface.
- Keep the project warning-clean and placeholder-free.
- Prefer transparent definitions and ordinary `decide` for finite proofs when
  practical; document any stronger evaluator.
- State cited inputs as theorem parameters or paper hypotheses, never as
  custom axioms.
- Update this map when a theorem boundary changes. A successful build proves
  only the declarations present, not an unencoded prose synthesis.
