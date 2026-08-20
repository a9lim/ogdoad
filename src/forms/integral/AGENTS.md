# `src/forms/integral/` editing guide

This directory joins integral lattices, finite quadratic modules, codes,
modular forms, and Clifford/Weyl constructions. Integral/rational arithmetic
and algebraic phase classifiers are exact unless an API explicitly returns a
checked failure; complex Gauss sums and Weil matrices are numerical and use
documented tolerances.

## Map

| path | responsibility |
| --- | --- |
| `lattice/` | Gram matrices, duals, determinant, signature, minima, roots |
| `diagonal.rs` | integral diagonal and parity data |
| `discriminant/` | finite quadratic modules, Gauss phases, and Weil matrices |
| `fqm_witt.rs` | bounded Witt reduction for finite quadratic modules |
| `genus.rs` | canonical p-adic symbols and Nikulin criteria |
| `mass_formula.rs` | exact mass and Bernoulli/Eisenstein constants |
| `kneser.rs` | denominator-checked p-neighbors and mass closure |
| `codes.rs` | binary/p-ary codes and Constructions A, B, and D |
| `theta.rs`, `modular.rs` | exact theta coefficients and modular-form identities |
| `root_lattices.rs`, `niemeier.rs` | ADE and Niemeier catalogues |
| `clifford_lattices.rs` | Clifford/spinor certificates for Barnes--Wall data |
| `weyl_versors.rs` | roots and Weyl reflections realized by Pin versors |

## Invariants

- Integral Gram matrices are symmetric and dimension-checked at construction.
- Scaling conventions in Constructions A/B/D are part of the API. Return
  `None` when the requested scaled Gram is not integral; do not round.
- Discriminant-form arithmetic and algebraic phase classification are exact.
  Complex Gauss sums and `Complex64` Weil matrices are numerical realizations
  with explicit tolerances. The Weil `S` prefactor uses the conjugate positive
  Milgram phase, and verification checks the metaplectic relations rather than
  the false shortcut `S^4 = I`.
- Odd lattices require the oddity correction. Do not apply the even-lattice
  Milgram formula unchanged.
- Canonical 2-adic symbols require train, compartment, sign-walking, and oddity
  normalization. Preserve equivalent-symbol tests when editing reduction.
- Kneser neighbors must validate denominators and isotropic lines before
  constructing an integral Gram matrix.
- Catalogue data are standard/source-backed inputs. Separate catalogue checks
  from generated theorem claims.
- Automorphism-group orders, counts, discriminants, and other fixed-width
  mathematical data use `u128`/`i128`.

## Cross-pillar boundaries

- `IntegralForm` may export rational and mod-two Clifford metrics, but the
  Clifford engine remains generic and owns geometric multiplication.
- Brown invariants of 2-elementary discriminant forms and real signatures meet
  through Milgram's relation; they are computed by different exact paths.
- Code-to-lattice and Clifford-to-lattice constructors must retain explicit
  witnesses rather than asserting an isomorphism from matching headline
  invariants alone.
- Rank-24 Niemeier statements may be catalogue-backed even when lower-rank
  genera have explicit neighbor enumeration. State that distinction.

## Verification

Use focused determinant, parity, theta, mass, and Weil-relation tests for the
changed object, then `cargo test -p ogdoad` and core Clippy. New catalogue rows
need a cited source and a test of every consumed field.
