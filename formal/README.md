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
| `Off.lean` | Frobenius/Artin--Schreier surjectivity consequences, hyperbolization of symplectic planes, and the polar-radical normal form | a set-sized algebraically closed characteristic-two field is the finite-form proxy for full `On_2`; the general symplectic decomposition is a standard input |
| `BrownGame.lean` | canonical `q = lift(ell)+2Q` split and converse, corrected polar form, two-divisible collapse, framed `Z/8` sharpness, and an exact four-class starter-profile decoder | Moews's short-game group theorem and the ordinary quadratic followers are external/paper inputs; the decoder is not yet an actual `PGame` construction |
| `GameExterior.lean` | root-collapse, square-zero and polar-zero consequences for torsion, polarization, and torsion-coset invariance | the short-game divisibility/torsion structure is supplied by Moews's theorem |
| `GoldDiagonal.lean` | quadratic-tower trace blocks, trace-dual reconstruction, Artin--Schreier lifting, and image-equals-trace-kernel over finite fields | concrete nim arithmetic and basis recursion remain in Rust |
| `GoldExtraspecial.lean` | biadditive cocycle group, square/commutator laws, center criterion, and order-four lifts | specialization to the Gold trace cocycle and game terms is composed in the paper |

## Gold--Arf realization ingredients

| module | checked content |
| --- | --- |
| `FifoMatching.lean` | both-seat zero-flip strategy for matching-plus-isolates boards |
| `ImpartialRealizer.lean` | pass-free transition, exact even clock, safe-front induction, and one-move charge tail |
| `GoldMatchingAlgebra.lean` | quadratic expansion in an adapted public Witt frame |
| `GoldNoEvaluator.lean` | transcript-span and observation-weight lower bounds |
| `GoldBlockCompression.lean` | induced block quadratic form and independent block indicators |
| `GoldForkPadding.lean` | outcome-preserving unavoidable-fork padding |
| `GoldSemantics.lean` | independent phase-aware terminal compiler retained as a comparison surface |

These modules prove independent ingredients. They do not construct one
end-to-end object combining finite-field arithmetic, a concrete Witt basis,
weighted source loading, the arena, and its observation contract. That
composition is proved in `writeups/goldarf.tex`.

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

Every theorem in these modules is subsidiary. None supplies either the full
strategy-relative minimum-bad ancestry classification or the subsequent
selection of compatible earlier siblings and continuation cosets. The
mathematical frontier is summarized in `docs/OPEN.md` and proved up to that
boundary in `writeups/linking_affine.tex`.

## Open Lenstra-excess frontier

`Excess.lean` checks algebraic ingredients of the four-arm reduction:

- the first-non-`p`-th-power interface and group-theoretic lower bound;
- the corrected characteristic-two sparse norm;
- exact cyclic-group and finite-field power criteria;
- finite primality/order/factor screens used by replayable certificates;
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
