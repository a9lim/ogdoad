# Lean formalization

`formal/` is a standalone Lean 4 project pinned to Lean and Mathlib `v4.32.2`.
`Ogdoad.lean` is the umbrella import.

```sh
cd formal
lake build --wfail
```

The development contains no `sorry`, `admit`, or custom `axiom`. Ordinary
theorems may report Lean's standard logical dependencies (`propext`,
`Classical.choice`, `Quot.sound`). `Excess.lean` and five FIFO route-limit
modules (`FifoPublicSeparatorAutomaton`, `FifoCommonDummyEventBoundary`,
`FifoPublicPrefixQueueCutBoundary`, `FifoTreeTrace`,
`FifoPairZeroMomentSafety`) also prove named finite propositions with
`native_decide`; for those declarations `#print axioms` adds Lean's generated
`<decl>._native.native_decide.ax_1_1`. They are exact replayable evaluator
results, not ordinary kernel reductions. No Misère module uses native
evaluation.

Lean checks only the declarations in this project. Rust implementations,
finite computations, source-backed data, cited theorems, and paper-level
compositions are separate evidence unless a theorem below connects them. A
`Prop`-valued definition — whether named `...Target`, `...Theorem`, or used as
the hypothesis of a conditional reduction — is not a proof; check whether a
theorem discharges it.

## Module architecture

Each paper-level theorem has one owning module, and paper entry points are
thin import-only manifests. (A few small private helpers, and the
`TwoDivisible` predicate in `GameExterior` and `BrownGame`, are duplicated.)

| layer | modules | contract |
| --- | --- | --- |
| shared algebra | `Algebra.ZModTwo`, `Algebra.ArtinSchreier` | paper-independent binary-scalar facts and Artin--Schreier tower algebra; neither imports a FIFO, Gold, Witt, excess, or nim module |
| certificate support | `Certificate.BinaryPolynomial` | one executable bit-polynomial multiplication, powering, remainder, and gcd evaluator; each consumer owns its modulus, constants, and claim |
| reusable components | `Quadratic.CharTwo` (bundling `Off`, `SymplecticBasis`, `WittFrame`, `CharTwoClassification`), `FifoMatching`, and the theorem-bearing modules below | each theorem lives in the narrowest domain module that owns it; bundles and paper modules import rather than restate |
| open-frontier bundle | `FifoFrontier` | the complete arbitrary-graph FIFO surface used by the linking paper; solved consumers such as Gold--Arf import only `FifoMatching` |
| paper entry points | `Papers.TransfiniteArf`, `Papers.GoldArf`, `Papers.WittRealization`, `Papers.LinkingAffine`, `Papers.Excess`, `Papers.NimFastMultiplication`, `Papers.SemiringStability`, `Papers.MisereNaturalRealization` | import-only manifests for the eight papers with Lean content (`thermo_newton.tex` has none); the preferred focused build targets |
| project root | `Ogdoad` | imports the eight entry points, so the full build covers every tracked module |

Gold--Arf and transfinite Arf both import `Quadratic.CharTwo` and neither
imports the other. `Papers.GoldArf` and `Papers.NimFastMultiplication` both
import `Algebra.ArtinSchreier`, whose only current consumer inside a theorem is
`NimFastMultiplication`. The three binary-field certificates in `Excess` share
`Certificate.BinaryPolynomial`:
the degree-110 ordinary-23 certificate (Rabin conditions, `native_decide`),
the degree-81 cubic countermodel (Rabin conditions, kernel `decide`), and the
degree-32 Fermat countermodel (`native_decide`, no irreducibility check). The
Rabin conditions are evaluated numerically; no theorem links them to Mathlib's
`Irreducible`.

## Closed results

| area | modules | kernel-checked result and boundary |
| --- | --- | --- |
| shared characteristic-two algebra | `Algebra.ZModTwo`, `Algebra.ArtinSchreier` | The common `F2` coefficient type and binary scalar lemmas; Artin--Schreier additivity, companions, and tower lifting; the finite-field Artin--Schreier image/absolute-trace-kernel equality; and irreducibility of `X^2 + X + a` exactly at trace one. Both are paper-independent; the trace-kernel and irreducibility theorems are standalone results with no downstream consumer yet. |
| characteristic-two quadratic forms | `Off`, `SymplecticBasis`, `WittFrame`, `CharTwoClassification` | Frobenius and Artin--Schreier plane reductions, a recursive orthogonal symplectic decomposition, a deterministic adapted basis, explicit canonical-form isometries, and classification by ambient, polar-radical, and quadratic-radical dimensions. A set-sized algebraically closed field is the formal proxy for each finite piece of Conway's proper-class `On_2`. |
| game-valued obstructions and Brown selectors | `GameExterior`, `BrownGame`, `BrownSelectorPGame` | Root-divisibility forces the stated exterior/Clifford coefficients to vanish; Brown refinements split as `lift(ell) + 2Q`; one parametrized finite partizan tree realizes the four Brown outcome classes. Moews's structure theorem for short games is a cited external input, not a Lean axiom. |
| Gold sources and extensions | `GoldDiagonal`, `GoldExtraspecial`, `GoldExtraspecialTrace` | Gold-specific quadratic-tower trace reconstruction, the universal cocycle group, the trace/Frobenius Gold specialization, and the order-eight quaternion cell over the canonical `GF(4)`. Lean's abstract finite fields are not definitionally identified with the Rust nimber backend. |
| Gold--Arf arena | `FifoMatching`, `ImpartialRealizer`, `PhysicalDeferred`, `GoldMatchingAlgebra`, `GoldArena` | Both seats force zero on matching-plus-isolates boards; the pass-free compiler has exact tempo and charge semantics; literal and deferred ledgers are conjugate with strategy trees transported both ways. `GoldArena.gold_literal_root_isP_iff` is the end-to-end literal-root theorem for every finite binary quadratic refinement, public basis, and input. It does not use arbitrary-graph FIFO linking. |
| realization bounds and comparison surfaces | `GoldNoEvaluator`, `GoldBlockCompression`, `GoldForkPadding`, `GoldSemantics` | Transcript-span and observation-weight lower bounds, induced block refinements, an outcome-preserving fork-padding obstruction, and an independent payoff-to-normal-play compiler. These are auxiliary theorems, not alternate end-to-end arena constructions. |
| imperfect-field Witt realization | `WittRealizationExact`, `WittRealization`, `WittTransfer`, `WittRamification`, `WittRamifiedRestriction`, `WittSingularBoundary` | The concrete parity-zero presented coordinate space has a finite sparse trace-character compiler into literal `0/*` arenas, with equality of all outcomes equivalent to equality of presented classes. The development also checks the trace-dual Scharlau Arf calculation, finite unit-jet substitution and exact Artin--Schreier normalization, one-place and fixed-finite-family obstructions, and the quasilinear absorption isometry. The Milnor--Scharlau exact sequence, the Aravire--Jacob classification and local decomposition, their equivalence with the actual `W_q(F_2(t))`, and the local quadratic-form interpretation of ramified generators remain the cited bridge. |
| stable semiring quadratic pairs | `SemiringQuadratic` | `hessenbergPolynomial_regular_isometric_hyperbolic` is the end-to-end finite-polynomial Hessenberg proxy: from bijectivity of the actual companion adjoint it proves Gram invertibility, proves internally that every invertible `MvPolynomial (Fin d) Nat` matrix is a permutation matrix, constructs its fixed-point-free transposition decomposition, and returns even rank plus an actual linear isometry of quadratic pairs with canonical hyperbolic planes. The module also proves that finite basis coefficients determine the entire pair, exposes Mathlib's characteristic-not-two diagonalization, and gives an explicit additive equivalence from the exact cyclic/hyperbolic/parity presentation to `ZMod 2`. The ordinal CNF--polynomial identification, connected-graph stable quotient, concrete supertropical semiring and lift presentation, and thermograph facts remain cited or paper-level bridges. |
| canonical nim multiplication | `NimFastMultiplication` (with `Algebra.ArtinSchreier`) | Artin--Schreier additivity, then the nim-specific trace carry through a quadratic generator, three-variable-product quadratic split, affine Artin--Schreier generator shift, involutive two-block coordinate transform, preservation of the canonical tower equations under ring equivalence, and exact recovery of source-basis product coordinates. The concrete Conway tower, De Feo--Schost algorithms, and asymptotic bounds remain cited or paper-level inputs. |
| finite misere quotient realization | `MisereTransition`, `MisereOctalCertificate`, `MisereNaturalUniversality`, `MisereTraceLanguage`, `MisereParityTrace`, `MisereSubtraction`, `MisereSaturation`, `MisereOctalTerminal`, `MisereOctalCompression`, `MisereGrundyObstruction` | Least-rank separation proves transition determinism; meximality and a `P`-reaching context exclude self-options. Exact quotient fibers and a finite periodic-record certificate are checked. The typed prefix/pad/unary-tail construction realizes every nontrivial valid table at the abstract heap level, with a no-go for retaining the inert pad in a verbatim octal encoding when the quotient has more than two elements. The unary-language dictionary exposes the exact failure cells. Safe meximal saturation preserves validity with the explicit terminal parity condition, and the actual octal terminal-prefix repair returns new safe records to the original table. The actual compressed masks have length at most `3*N+2*p`, and every compressed heap record belongs to the valid saturated table. The star value is a free involution; every nontrivial valid table has the total parity trace for `0.7` and the odd-removal family. For a two-element quotient with any split bit, every positive heap trace has period two, and totality is equivalent to four candidates checked through heap `d+5`. The actual finite-subtraction mex sequence satisfies Ferguson's shift and the exact misere outcome recursion for every finite heap list. Hindman's theorem supplies a square-option heap in every finite Grundy trace, forcing unequal consecutive positive powers. The exact-quotient interpretation of compressed records and bounded periodic-complexity synthesis, the explicit binary mask classification, subtraction monoid identification and synthesis, numerical normal-form transport, grammar hardness reduction, Grundy prefix presentations, and canonical-mate obstruction remain paper-level; general octal synthesis and the full Grundy quotient remain open. |


## Arbitrary-graph FIFO linking: open

`Fifo.lean` defines the terminating FIFO game and proves its win recursion and
determinacy, rank, score-translation, queue-cut, singleton-tail, and stopped
CLOSE-first theorems. It also defines

```lean
FifoLinkingTheorem : Prop
```

for arbitrary finite graphs with an isolated dummy; the proposition is neither
proved nor assumed. `FifoPublicPolicyAffine` defines the graph-free target
`UniversalPublicPolicyAffine`, and `FifoPublicPolicyDuality` proves

```lean
UniversalPublicPolicyAffine ↔ FifoLinkingTheorem
```

so the public-policy problem is an exact reformulation. `FifoMatching` proves
the matching-plus-isolates case used by `GoldArena`.
`FifoCongruenceOutcomeBoundary` also proves conditional reductions from the
unproved propositions `DummyShearNormalForm`, `DummyRootShearForward`, and
`DummyRootShearBothEvenForward` to `FifoLinkingTheorem`, alongside its
negative result.

The FIFO modules are grouped by role. `Boundary` modules and the small
countermodel modules prove that a proposed inference fails — some also carry
positive structural lemmas — and none is a counterexample to the conjecture.

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
from the root and select an odd family of earlier defender siblings whose
prefixes and continuation cosets cancel the residual real-edge class, in both
FIFO orders. No current module supplies that selection. See
[`../docs/OPEN.md`](../docs/OPEN.md) §1 and `../writeups/linking_affine.tex`.

## Finite excess: disproof and remaining open questions

The piecewise `0/1/4` rule is false: `writeups/excess.tex` proves an infinite
family of literal Conway rows with two components and positive excess.
`ExcessEqualNorm` checks the equal-half-norm quotient and factorization,
full-primary power transfer, and coprime radical uniqueness. Its
`kummer_half_norm_synchronized` proves the norm-synchronization step from
Kummer, Frobenius-period, coprimality, and congruence hypotheses.
`ExcessKummerDegree` checks translation rigidity for an irreducible binomial
and separation of two components fixed through their sum. `ExcessSeed`
checks the primes 37 and 109, their binary order 36, synchronization at
every level `18t`, and half-field coprimality for all levels.
`ExcessPrimitive.exists_primitive_row_prime` proves that for every `a > 0`
there is a prime of binary order `36 * 37^a * 109^a`, directly from
cyclotomic polynomials. These modules use ordinary kernel proofs, without
`native_decide` or custom axioms.

`ExcessTranslateSupport` checks bounded integer exponent collisions under a
primitive cubic-root congruence and the ensuing coefficient-proportionality
step. In the paper these support a theorem that every nonzero common-base
translate of the synchronized sum recovers nontrivial primitive support.
The tensor basis, finite-field specialization, and rational-function divisor
argument remain paper-level. Nontrivial support does not prove full primary
order at a particular prime or determine an excess value.
`ExcessQuarticSupport.bounded_quartic_relation` proves the stronger bounded
support separation used to retain a nonzero primitive coordinate in both
coprime factors of the half-field torus order. It checks the explicit
integral norm, its zero criterion, and its coefficient bound. The Laurent
divisor and finite-field evaluation remain paper-level arguments.

`ExcessFiveGap` checks the rational transformation and eigencharacter
identities used in the five-power gap theorem: when `ord_p(2) = 4 * 5^a`
with `a >= 1`, the literal excess is one or at least sixteen. The five/ten
cycle decomposition on `F_16`, finite-field specialization, and Conway
identification remain paper-level. The theorem does not establish a failed
first translate; the large-excess branch is still open.

The seed tensor expansions and minors are already checked by
`Excess.z36_expansions`, `z36_expansion_109`, `z36_minor_37`, and
`z36_minor_109`. Their finite-field tensor interpretation proves the two
seed excesses zero in the paper. The full finite-field specialization and
literal Conway component recursion remain paper-level: this is not an
end-to-end Lean formalization of the disproof. Exact excesses in the new
family, the range-only assertion `m_p in {0,1,4}`, absolute boundedness,
and the ordinary/cubic/exceptional/singleton-even assertions remain open.

`Excess`, `ExcessOrdinaryPacking`, and `ExcessCubicPacking` prove algebraic
ingredients of the four-arm `Z/O/C/D` reduction. Kernel-checked content
includes:

- finite-cyclic-group and finite-field power and order criteria: norm
  reduction, coprime-exponent invariance, strict-ancestor primary vacuity, and
  the exact order-defect criterion. `rough_defect_eq_prime` shows that a
  positive `p`-rough defect with `N < B p^2` is exactly `p`;
  `rough_congruent_defect_eq_prime_or_square_dvd` shows that when every prime
  divisor is `1 mod M` and `N < B p(p+M)`, the defect is `p` or divisible by
  `p^2`;
- the ordinary-arm algebra: the coprime-factor degree-sum lemma
  (`polynomial_natDegree_add_le_of_isCoprime_dvd`), padded-mirror divisibility
  (`selfMirror_dvd_paddedMirror_iff`), and the characteristic-two Frobenius
  expansion (`affine_frobenius_product_expansion`);
- the cubic power-sum recurrence, its first value (`cubicPowerSum_three`) and
  zero residue classes, the pairwise-root invariants of the composition law,
  and the degree-three torsion action whose norm operator vanishes and whose
  coboundary is surjective (the algebraic core of the Hilbert-90 no-go);
- the corrected characteristic-two sparse norm (`CorrectedNorm`) and the
  exceptional cyclic-compression algebra;
- the exceptional Cayley coordinate and its coboundary identities
  (`exceptionalCayley_eq_traceMobius`, `exceptional_cayley_coboundary_cross`,
  `exceptionalCayleyNum_cubic_product`, `exceptionalCayleyDen_cubic_product`,
  `exceptional_coboundary_isPthPower_iff`,
  `exceptional_scaled_coboundary_isPthPower_iff`);
- trace, norm, Frobenius, Kummer, Dickson--Lucas, Singer, and minimal-polynomial
  collision identities, including `conwayChild_powerSum` (power sums across one
  selected quadratic edge), the two-binomial fourth-power residual for an odd
  Fibonacci zero, and the packet-universal Binet parametrization;
- the reciprocity calculus: weighted two-axis Frobenius-word normalization
  (rank one), affine-Frobenius conjugacy, Jacobi-sum scaling, gauge invariance
  of full affine-path holonomy, triviality of homomorphic cocycles, and the
  scalar behaviour of affine intertwiners;
- for the packing bounds, top-coefficient cancellation, injectivity of
  normalized rational evaluations, and the cyclic-order bound
  (`ExcessOrdinaryPacking`), and the coprime circle/real splitting, the
  factor-of-three order identity, and transfer to the Singer coordinate
  (`ExcessCubicPacking`);
- executable finite primality, factor, modular, and order screens for named
  rows, some through `native_decide`.

Paper-level, not formalized: the Conway component-field induction and the
minimal-coefficient-field ancestry behind the packing sieves, their ball and
shell counts and asymptotics, the opposite-section reciprocity and power-basis
separation, the cubic first-relation and composition theorems, the first-jet
quotient and digit-gap boundary, the relative-norm evaluation and
norm-fibre no-go in the exceptional arm, its intermediate-field sieve, and all
elliptic-curve, Artin--Schreier ramification, generalized-Prym, and top-orbit
divisor-lattice synthesis. `experiments/fermat_top_orbit_countermodel.py`
replays a generic degree-32 point that violates the literal Conway selector;
it is evidence against an unmarked inference, not against arm `Z`.

`Excess.lean` defines `SelectedLogUnitTarget`, `ExceptionalColumnTarget`, and
`DPrimeTarget := ExceptionalColumnTarget psi M`. These expose universal
propositions; they are neither assumed nor proved, and `DPrimeTarget` is the
exceptional-column target, not the full `0/1/4` rule. The load-bearing test in
every arm is the Euler criterion `beta^(|F^x|/p) != 1`; `p | ord(beta)` loses
the primary valuation when `p^2` divides the ambient order. See
[`../docs/OPEN.md`](../docs/OPEN.md) §2 and `../writeups/excess.tex`.

`ExcessRandomModel.lean` proves theorems about the random model only, not
about `On_2`. If independent events indexed by odd primes have probabilities
at least `c/p` (in particular `1/p`, as for a uniform element being a `p`-th
power, `uniformOn_units_pthPowers`), then almost surely infinitely many of
them occur (`ae_infinite_oddPrime_of_div_le`, `ae_infinite_fails`). The
expected count over a finite set is the sum of the probabilities
(`integral_card_filter_oddPrime_eq_sum_inv`). The modelling hypothesis, that
the selected Conway elements behave like independent uniform elements, is
neither assumed nor proved about the tower.

## Natural misère realization: open

The Misère modules check the results in the closed-results table with ordinary
logical axioms only. `finite_subtraction_outcome` connects the mex-defined SG
sequence to the literal misère recursion on arbitrary finite heap lists;
`binary_split_total_iff_finite_candidate` connects a four-candidate check
through heap `d+5` to every future heap record; and
`compressed_records_mem_saturation` checks every heap record of the bounded
compressed masks.

They do not characterize exact quotients of all finite-code octal games, prove
automatic periodicity for general split targets, or decide whether the misère
Grundy quotient is finite. The exact-quotient interpretation of compressed
records and the bounded synthesis algorithm, the binary mask classification,
the subtraction quotient presentation and synthesis algorithm, the numerical
normal-form transport, the Grundy prefixes through heap 18, and the
canonical-mate obstruction are paper-level. See
[`../docs/OPEN.md`](../docs/OPEN.md) §3 and
`../writeups/misere_natural_realization.tex`.

## Review contract

- Put a reusable declaration in a paper-independent domain module; paper entry
  points stay import-only manifests.
- Keep each `Papers.*` entry point synchronized with its paper, and
  `Ogdoad.lean` synchronized with the complete set of entry points.
- Keep the project placeholder-free and `--wfail` clean. Nine modules disable
  specific linters with `set_option linter.* false`; do not widen that.
- Prefer transparent definitions and ordinary `decide` for finite proofs when
  practical; document any stronger evaluator.
- State cited inputs as theorem parameters or paper hypotheses, never as custom
  axioms.
- Update this map when a theorem boundary changes. A successful build proves
  only the declarations present, not an unencoded prose synthesis.
