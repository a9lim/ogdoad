# Lean formalization

`formal/` is a standalone Lean 4 project pinned to Lean and Mathlib `v4.32.2`.
`Ogdoad.lean` is the umbrella import. The imported development contains no
`sorry`, `admit`, or custom `axiom` declarations.

Some named finite arithmetic declarations use `native_decide`.  For those
declarations, `#print axioms` reports Lean's generated native-decision axiom:
they are exact replayable evaluator results, but they are not ordinary kernel
reductions.  Ordinary theorems may still report Lean's standard logical
dependencies (`propext`, `Classical.choice`, and `Quot.sound`); the distinction
here is ordinary kernel-checked Lean/algebra without native evaluation versus
the additional `_native.native_decide.ax_1_1` evaluator boundary.

```sh
cd formal
lake build --wfail
```

Lean checks only the declarations in this project. Rust implementations,
finite computations, source-backed data, cited theorems, and paper-level
compositions are separate evidence unless a theorem below explicitly connects
them. In particular, a declaration ending in `Target` or `Theorem` may merely
*define* a proposition; inspect whether it is followed by a proof.

## Module architecture

The formal tree has one declaration owner for each theorem and thin,
import-only paper entry points:

| layer | modules | contract |
| --- | --- | --- |
| shared algebra | `Algebra.ZModTwo`, `Algebra.ArtinSchreier` | Paper-independent binary-scalar facts, Artin--Schreier additivity and tower algebra, the finite-field trace exact sequence, and the trace-one irreducibility criterion. No FIFO, Gold, Witt, excess, or nim module is imported here. |
| certificate support | `Certificate.BinaryPolynomial` | One executable bit-polynomial multiplication, powering, remainder, and gcd evaluator shared by named finite-field certificates. It supplies computation only; each consumer separately owns its modulus, irreducibility check, constants, and mathematical claim. |
| reusable mathematical components | `Quadratic.CharTwo` (bundling `Off`, `SymplecticBasis`, `WittFrame`, and `CharTwoClassification`), `FifoMatching`, and the other theorem-bearing modules below | Each definition or theorem is proved once in the narrowest domain module that owns it. Domain bundles and paper modules import these components; they do not restate them. |
| open-frontier bundle | `FifoFrontier` | The complete arbitrary-graph FIFO research surface used by the linking paper. Solved consumers such as Gold--Arf import only `FifoMatching`, not the whole frontier. |
| paper entry points | `Papers.TransfiniteArf`, `Papers.GoldArf`, `Papers.WittRealization`, `Papers.LinkingAffine`, `Papers.Excess`, `Papers.NimFastMultiplication`, `Papers.SemiringStability`, `Papers.MisereNaturalRealization` | Import-only manifests matching the eight papers that currently have Lean content. These are the preferred focused build targets. |
| project root | `Ogdoad` | Imports the paper entry points, so the full build still covers every declaration while keeping paper composition explicit. |

For example, both Gold--Arf and transfinite Arf import
`Quadratic.CharTwo`; neither paper entry point imports the other. Both
Gold--Arf and fast nim multiplication import
`Algebra.ArtinSchreier`; neither owns a private copy of the trace-kernel or
trace-one polynomial facts. Witt realization, Gold--Arf, and the FIFO
development share `Algebra.ZModTwo` rather than reaching through the FIFO
namespace for binary-scalar lemmas. The three exact binary-field certificates
inside `Excess` share `Certificate.BinaryPolynomial`; they do not carry private
copies of the evaluator.

## Closed results

| area | modules | kernel-checked result and boundary |
| --- | --- | --- |
| shared characteristic-two algebra | `Algebra.ZModTwo`, `Algebra.ArtinSchreier` | The common `F2` coefficient type and binary scalar lemmas; Artin--Schreier additivity, companions, and tower lifting; the finite-field Artin--Schreier image/absolute-trace-kernel equality; and irreducibility of `X^2 + X + a` exactly at trace one. These modules are paper-independent dependencies. |
| characteristic-two quadratic forms | `Off`, `SymplecticBasis`, `WittFrame`, `CharTwoClassification` | Frobenius and Artin--Schreier plane reductions, a recursive orthogonal symplectic decomposition, a deterministic adapted basis, explicit canonical-form isometries, and classification by ambient, polar-radical, and quadratic-radical dimensions. A set-sized algebraically closed field is the formal proxy for each finite piece of Conway's proper-class `On_2`. |
| game-valued obstructions and Brown selectors | `GameExterior`, `BrownGame`, `BrownSelectorPGame` | Root-divisibility forces the stated exterior/Clifford coefficients to vanish; Brown refinements split as `lift(ell) + 2Q`; one explicit finite partizan tree realizes the four Brown outcome classes. Moews's structure theorem for short games is a cited external input, not a Lean axiom. |
| Gold sources and extensions | `Algebra.ArtinSchreier`, `GoldDiagonal`, `GoldExtraspecial`, `GoldExtraspecialTrace` | Shared Artin--Schreier lifting and trace-kernel exactness, Gold-specific quadratic-tower trace reconstruction, the universal cocycle group, the trace/Frobenius Gold specialization, and the order-eight quaternion cell over the canonical `GF(4)`. Lean's abstract finite fields are not definitionally identified with the Rust nimber backend. |
| Gold--Arf arena | `FifoMatching`, `ImpartialRealizer`, `PhysicalDeferred`, `GoldMatchingAlgebra`, `GoldArena` | Both seats force zero on matching-plus-isolates boards; the pass-free compiler has exact tempo and charge semantics; literal and deferred ledgers are conjugate with strategy trees transported both ways. `GoldArena.gold_literal_root_isP_iff` is the end-to-end literal-root theorem for every finite binary quadratic refinement, public basis, and input. It does not use arbitrary-graph FIFO linking. |
| realization bounds and comparison surfaces | `GoldNoEvaluator`, `GoldBlockCompression`, `GoldForkPadding`, `GoldSemantics` | Transcript-span and observation-weight lower bounds, induced block refinements, an outcome-preserving fork-padding obstruction, and an independent payoff-to-normal-play compiler. These are auxiliary theorems, not alternate end-to-end arena constructions. |
| imperfect-field Witt realization | `WittRealizationExact`, `WittRealization`, `WittTransfer`, `WittRamification`, `WittRamifiedRestriction`, `WittSingularBoundary` | The concrete parity-zero presented coordinate space has a finite sparse trace-character compiler into literal `0/*` arenas, with equality of all outcomes equivalent to equality of presented classes. The development also checks the trace-dual Scharlau Arf calculation, finite unit-jet substitution and exact Artin--Schreier normalization, one-place and fixed-finite-family obstructions, and the quasilinear absorption isometry. The Aravire--Jacob exact sequence and local decomposition, their equivalence with the actual `W_q(F_2(t))`, and the local quadratic-form interpretation of ramified generators remain the cited bridge. |
| stable semiring quadratic pairs | `SemiringQuadratic` | `hessenbergPolynomial_regular_isometric_hyperbolic` is the end-to-end finite-polynomial Hessenberg proxy: from bijectivity of the actual companion adjoint it proves Gram invertibility, proves internally that every invertible `MvPolynomial (Fin d) Nat` matrix is a permutation matrix, constructs its fixed-point-free transposition decomposition, and returns even rank plus an actual linear isometry of quadratic pairs with canonical hyperbolic planes. The module also proves that finite basis coefficients determine the entire pair, exposes Mathlib's characteristic-not-two diagonalization, and gives an explicit additive equivalence from the exact cyclic/hyperbolic/parity presentation to `ZMod 2`. The ordinal CNF--polynomial identification, connected-graph stable quotient, concrete supertropical semiring and lift presentation, and thermograph facts remain cited or paper-level bridges. |
| canonical nim multiplication | `Algebra.ArtinSchreier`, `NimFastMultiplication` | The shared finite-field trace-one irreducibility criterion, then the nim-specific trace carry through a quadratic generator, three-variable-product quadratic split, affine Artin--Schreier generator shift, involutive two-block coordinate transform, preservation of the canonical tower equations under ring equivalence, and exact recovery of source-basis product coordinates. The concrete Conway tower, De Feo--Schost algorithms, and asymptotic bounds remain cited or paper-level inputs. |
| finite misere quotient realization | `MisereTransition`, `MisereOctalCertificate`, `MisereNaturalUniversality`, `MisereTraceLanguage`, `MisereGrundyObstruction` | A least-rank separator proves transition determinism. Every value has a `P`-reaching context, so no transition value is one of its own options; the whole-, one-, and two-remainder octal exclusions are checked explicitly. Rank plus table parity proves outcome correctness, and multiplicativity, surjectivity, and reducedness identify exact quotient fibers. An asserted ultimately periodic octal word has periodic complete option records past `2*N + p + d`, so a finite prefix through one tail period certifies all heap records. The typed finite-prefix/pad/unary-tail construction realizes every nontrivial finite valid table at the abstract heap level, while the later-terminal-pad theorem rules out its verbatim heapwise octal encoding for quotients with more than two elements. The unary Boolean-language module identifies exact option cells and the failure language coefficientwise. Mathlib's Hindman theorem supplies distinct positive `i < j` with equal finite colors at `i`, `j`, and `i+j`; for a finite Grundy trace this produces a square-valued option, which forces distinct consecutive powers and an eventual period of length at least two. The external unary-grammar hardness reduction, transport to numerical heap sizes and multisets, strict finite-octal synthesis, tame-family strategy, Grundy kernel argument, and quotients through heap 18 remain paper-level or open exactly as stated in `writeups/misere_natural_realization.tex`. |

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

- exact finite-cyclic-group and finite-field power/order criteria, including
  norm reduction, coprime-exponent invariance, and strict-ancestor primary
  vacuity;
- the corrected characteristic-two sparse norm;
- trace, norm, Frobenius, Kummer, Dickson--Lucas, Singer, and cubical-support
  identities used by the selected-order reductions;
- weighted two-axis Frobenius-word normalization: all multiplicative
  reciprocity expressions in this model formed from one Kummer class remain
  rank one, regardless of Frobenius, character, and multiplicity indices;
- affine-Frobenius conjugacy and marked Jacobi-sum scaling: class functions on
  one split fixed-multiplier affine coset erase its translation coordinate, while
  additive convolution retains only the summed weight of the same Kummer
  phase; a labeled Fourier-line pullback exposes a gauge-dependent one-step
  coordinate, while the full affine-path holonomy is gauge invariant; a
  separate identity identifies a closed Kummer ratio with the Euler phase.
  Every homomorphic affine composition cocycle
  is a coboundary with zero full-period holonomy, and every closing holonomy
  remains possible after the proper path has been normalized; affine
  intertwiners contribute only a scalar multiple plus a telescoping endpoint
  term;
- the singleton-even auxiliary-cubic and abstract pairing no-gos:
  positive-level Fermat torsion has trivial cubic Kummer class, a perfect
  alternating pairing may vanish on a prescribed line, and coprime adjacent
  annihilators kill a proposed ancestry homomorphism; the selected elliptic
  curve, divisor, and Miller-function interpretation remain paper-level;
- oriented Frobenius-prefix evaluation and its block cocycle, including the
  faithful unit-exponent-prefix/full-orbit-trivial dichotomy; these identities
  only re-encode a marked power-residue phase and do not evaluate it;
- executable finite primality, factor, modular, and order screens for the rows
  explicitly encoded in the file.  The declarations proved with
  `native_decide` are native-decided finite evidence in the sense stated
  above, not ordinary kernel reductions.

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

## Natural finite misere realization: open

`MisereTransition`, `MisereOctalCertificate`,
`MisereNaturalUniversality`, `MisereTraceLanguage`, and
`MisereGrundyObstruction` check the finite-table determinism, exact periodic
trace certificate, abstract prefix/pad/unary-tail construction and its inert-pad
obstruction, unary option-language dictionary, and finite-Grundy power-period
obstruction listed in the closed-results table.

They do not characterize exact quotients of finite-code octal games, prove
automatic periodicity for split traces, or determine whether the full misere
Grundy quotient is finite. The numerical transport, tame-family construction,
and exact Grundy prefixes through heap 18 remain paper proofs. See
`../docs/OPEN.md` and `../writeups/misere_natural_realization.tex`.

## Review contract

- Put a reusable declaration in a paper-independent domain module; paper entry
  points remain import-only manifests.
- Keep each `Papers.*` entry point synchronized with its live paper and keep
  `Ogdoad.lean` synchronized with the complete set of Lean-backed paper entry
  points.
- Keep the project warning-clean and placeholder-free.
- Prefer transparent definitions and ordinary `decide` for finite proofs when
  practical; document any stronger evaluator.
- State cited inputs as theorem parameters or paper hypotheses, never as
  custom axioms.
- Update this map when a theorem boundary changes. A successful build proves
  only the declarations present, not an unencoded prose synthesis.
