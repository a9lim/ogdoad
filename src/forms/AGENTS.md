# `src/forms/` editing guide

This pillar classifies quadratic and related forms. Its primary axis is the
characteristic trichotomy; valuation, global, and integral shelves cut across
that axis. Read `docs/OPEN.md` before changing a claim used by a live paper.

## Map

| path | responsibility |
| --- | --- |
| `classify.rs` | scalar-dispatched classification façades and domain errors |
| `diagonalize.rs`, `equivalence.rs` | congruence diagonalization and isometry/Witt decomposition |
| `char0.rs` | real/complex/rational Clifford classifiers |
| `oddchar/` | finite odd-characteristic invariants |
| `char2/arf.rs` | symplectic reduction and Arf invariants |
| `char2/brown.rs` | `Z/4`-valued quadratic refinements and Brown invariant |
| `char2/{dickson,extraspecial,field}.rs` | Dickson parity, extraspecial groups, finite char-two abstraction |
| `witt/` | Witt rings/groups, rational and function-field Brauer data, Brauer--Wall, cyclic classes, Milnor residues |
| `springer/` | valued-field residue decompositions, including characteristic two |
| `local_global/` | rational, adelic, and function-field reciprocity/isotropy |
| `trace_form.rs` | trace, twisted trace, Gold-form, and Scharlau-transfer bridges |
| `symplectic.rs`, `hermitian.rs` | form-plus-involution siblings |
| `field_invariants.rs` | level and u-invariant reports |
| `quadric_fit.rs` | research instrument fitting Boolean P-sets to quadrics |
| `integral/` | lattice wing; see `integral/AGENTS.md` |

`mod.rs` re-exports the public surface. `poly_factor.rs` and shared matrix
kernels remain crate-private.

## Classification contract

- The façade reports why a metric is outside a classifier's domain. Preserve
  `GeneralBilinearMetric`, `SingularForm`, `UnsupportedFieldOrWindow`, and
  `DiagonalizerFailure` distinctions.
- Characteristic zero and odd characteristic may diagonalize non-diagonal
  polar forms. In characteristic two, nonsingular alternating polar forms are
  not diagonalizable; use symplectic reduction on the full `(q,b)` metric.
- A degenerate characteristic-two form is not determined by the Arf invariant
  of a chosen nonsingular complement. Keep polar rank, radical dimension, and
  the restriction of `Q` to the radical explicit.
- Brauer--Wall functions have backend-specific singular-domain contracts. Do
  not silently make characteristic-two nonsingular-only APIs imitate
  characteristic-zero radical projection.
- `Nimber`, supported `Fpn<2,N>`, and supported finite ordinal windows are
  finite-field classifiers. Full `On_2` statements occur only after scalar
  extension in the mathematical paper.

## Algebraic distinctions

- Brown's `Z/4` bilinear form is symmetric with diagonal `q mod 2`; it is not
  the Clifford engine's alternating characteristic-two polar form.
  `double_f2` is the explicit bridge.
- `Brauer2Class` is the ungraded two-torsion Brauer class.
  `RationalBrauerWallClass` adds grading data.
  `BrauerClass` is the full `Q/Z` local invariant. Do not merge these types.
- The tame symbol uses valuation plus angular component and assumes the
  required roots of unity. Wild norm-residue symbols remain roadmap work.
- `WittClassG::try_mul` rejects the characteristic-two quadratic Witt group,
  which is a module rather than the same ring object used in odd
  characteristic.
- `FieldExtension::extension_degree` and finite-field absolute degree are
  different invariants.
- Odd finite-field Hasse invariants are trivial; p-adic Hasse/Hilbert data are
  not.

## Reports and rendering

Use suffixes consistently:

- `Class` for an element of a classifying group/set with a law;
- `Decomp` for a decomposition;
- `Invariants` for a computed classifier record;
- `Record` for static catalogue entries;
- `Signature` and `Isotropy` for those literal structures.

Public reports implement canonical `Display`; Python `repr` delegates to the
core. Preserve honesty markers such as incomplete searches and
complement-dependent characteristic-two data.

## Claim boundaries

- The Gold--Arf normal-play construction is a proved paper-level synthesis.
  Its Lean modules check independent ingredients, not a single theorem building
  the entire arena.
- The arbitrary-graph FIFO theorem is open and not a premise of the Gold
  construction.
- `quadric_fit` discovers bounded Boolean structure; it is not a classifier or
  universal proof.
- The universal transfinite excess rule remains open even when finite rows are
  certified.

## Verification

Run tests for the affected characteristic and bridge, then the workspace gate.
For claim-bearing changes, also build Lean and all affected papers. Preserve
the public `u128`/`i128` payload convention.
