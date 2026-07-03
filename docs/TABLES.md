# Production Hardcoded Tables

This file records production hardcoded tables and finite case tables found in the
runtime library and Python bindings. It excludes tests, examples, and experiment
oracles, and it also excludes trivial enum display strings unless the mapping is a
semantic catalogue.

## Remaining Data Tables

These are still real production tables because the finite data is curated,
sourced, or public API vocabulary rather than a theorem with a simpler closed
form.

| table | source | should stay a table? | note |
|---|---|---|---|
| Prime factors of `2^128 - 1` for nimber multiplicative orders | `src/scalar/finite_field/nimber/galois.rs::ORDER_FACTORS` | Yes. | The coarse identity is `2^128 - 1 = prod_{i=0..6} (2^(2^i)+1)`, but the prime factors of `F_5` and `F_6` are still recorded arithmetic data. |
| Finite Lenstra excess integers `m_u`, odd primes `3..=709` | `src/scalar/big/ordinal/tower.rs::finite_excess` | Yes. | OEIS A380496 ("Lenstra excess of the n-th odd prime"), the b-file's 126 known rows (the first 14 reproduce DiMuro Table 1 + the old `m_47`; first OEIS-unknown row is `p=719`). Indexed by odd-prime place; diffed in full (all 126 rows) against the vendored b-file copy (`src/scalar/big/ordinal/b380496.txt`, fetched from OEIS 2026-07-02) by `excess_table_matches_vendored_b380496_in_full`, with `excess_table_matches_oeis_a380496` keeping the landmark rows plus the 0/1-except-`m_19`,`m_163` invariant. `alpha_u` is assembled from `ord_u(2)`, `Q(f(u))`, and this finite integer. Provenance: Conway/Lenstra/Le Bruyn/Siegel/Peeters via CGSuite's calculator. |
| Named code generator matrices: binary Hamming `[7,4,3]`, extended Hamming `[8,4,4]`, the indecomposable Type II `[16,8,4]`, extended binary Golay `[24,12,8]`, and extended ternary Golay `[12,6,6]` | `src/forms/integral/codes.rs::{hamming_code,extended_hamming_code,type_ii_len16_code,extended_golay_generator_rows,ternary_golay_code}` | Yes. | These are finite named representatives for the Construction A/B/D and odd-prime Construction A bridges. The split length-16 Type II code is derived from the extended Hamming code; the indecomposable length-16 generator is sourced from the Harada-Munemasa self-dual-code table; binary Golay is shared with the Leech construction and the `B(Golay)` half-Leech oracle; ternary Golay pins the honest odd unimodular rank-12 `Z`-lattice from p-ary Construction A. |
| `E_6`, `E_7`, `E_8` Dynkin edge lists | `src/forms/integral/root_lattices.rs::{e_6,e_7,e_8}` | Yes. | These are exceptional finite diagrams. They could be generated from branch specs, but that would still encode the same exceptional data. |
| Exceptional automorphism-order constants: `E_6/E_7/E_8` orders, the `E_8` Weyl-group order, the Conway-group `Co_0` order (Leech / rootless Niemeier class), the `D16+` order, and the `BW16` Clifford/BRW orders | `src/forms/integral/lattice/::RootComponentKind::automorphism_order`, `src/forms/integral/root_lattices.rs::E8_WEYL_GROUP_ORDER`, `src/forms/integral/mass_formula.rs::LEECH_AUT_ORDER`, `src/forms/integral/codes.rs::D16_PLUS_AUT_ORDER`, `src/forms/integral/clifford_lattices.rs::{BW16_AUTOMORPHISM_GROUP_ORDER,BW16_REAL_CLIFFORD_GROUP_ORDER}` | Yes. | The infinite `A_n`/`D_n` families are formulaic; the exceptional orders are curated constants. `E8_WEYL_GROUP_ORDER` and `D16_PLUS_AUT_ORDER = 2^15·16!` anchor the rank-8/rank-16 theta/Siegel-Weil bridge; `weyl_versor_report` checks the ADE Weyl orders against Clifford Pin simple-reflection actions and Coxeter orders. `LEECH_AUT_ORDER = Co_0 = 2^22·3^9·5^4·7^2·11·13·23` is returned by `Niemeier::automorphism_group_order` for the rootless class. `BW16_AUTOMORPHISM_GROUP_ORDER = 2^21·3^5·5^2·7` records the index-2 Clifford/BRW subgroup, while `BW16_REAL_CLIFFORD_GROUP_ORDER` is twice it for the full `2_+^(1+8).O^+(8,2)` group. These constants are also exported to Python. |
| Exceptional Coxeter numbers `h(E_6)=12`, `h(E_7)=18`, `h(E_8)=30` | `src/forms/integral/niemeier.rs::NiemeierComponentKind::coxeter_number` | Yes. | The `A_n` (`n+1`) and `D_n` (`2n-2`) cases are formulaic; the exceptional `E` Coxeter numbers are constants. Used with rank to count roots per Niemeier class for the theta-series weighting. |
| Exceptional root-lattice determinants `det(E_6)=3`, `det(E_7)=2`, `det(E_8)=1` | `src/forms/integral/niemeier.rs::NiemeierComponentKind::determinant` | Yes. | The `A_n` (`n+1`) and `D_n` (`4`) cases are formulaic; the exceptional `E` determinants are curated constants — the sibling of the `coxeter_number` row in the same `impl` block, load-bearing for the Niemeier glue-index arithmetic (`glue² = det(R)`). The `(rank, root-count)` detection pairs `(6,72)/(7,126)/(8,240)` in `src/forms/integral/lattice/geometry.rs::RootComponentKind::from_rank_and_roots` are the same class of exceptional data, used for classification-by-shape. |
| Exceptional Weyl-group orders `#W(E_6) = 51,840`, `#W(E_7) = 2,903,040` | `src/forms/integral/niemeier.rs::NiemeierComponentKind::weyl_group_order` | Yes. | The `A_n`/`D_n` cases are formulaic (factorial/power); the exceptional `E_6`/`E_7` orders are curated constants (`E_8` delegates to the tabled `E8_WEYL_GROUP_ORDER`). Distinct from `lattice/geometry.rs::RootComponentKind::automorphism_order`, which carries the doubled lattice-`Aut` orders (`E(6)=103,680`, …) — these are the bare Weyl orders feeding the Niemeier `Aut(N)/W(R)` quotients and the mass-sum cross-check. |
| Niemeier root-system, glue-index, and `Aut(N)/W(R)` catalogue | `src/forms/integral/niemeier.rs::NIEMEIER_CLASSES` | Yes. | This is the 24-class rank-24 even-unimodular catalogue from Conway-Sloane's Niemeier table, cross-checked by the glue-square determinant, mass sum, and weight-12 Siegel-Weil identity. The code builds root sublattices and the explicit Leech lattice; it does not encode 23 full glued Gram matrices. |
| Clifford-invariant vs Hasse-Witt correction `delta(n mod 8, d)` | `src/forms/witt/brauer_rational.rs::clifford_correction` | Yes. | The `n mod 8` -> `{(-1,-1), (-1,d)}` correction between `c(q)` and `s(q)` (Bridge F), from Lam GSM 67 pp. 117-119, machine-verified by an in-test all-eight-residues re-derivation plus two genuinely independent Clifford-side oracles (`C(⟨a,b⟩) ≅ (a,b)`, `C₀(⟨a,b,c⟩) ≅ (−ab,−ac)`). Agreement with SageMath's `clifford_invariant` is a doc-comment claim only — no executed Sage oracle exists here (the model for a literal one is `genus.rs`'s Sage-pinned canonical-symbol examples). The eight residue cases have no simpler closed form. |
| Real Clifford 8-fold (Bott) classification table `s = (q-p) mod 8 -> R/C/H` | `src/forms/char0.rs::real_core` | Yes. | The mod-8 period of the real Clifford classification (`0,6,7 -> R`; `1,5 -> C`; `2..=4 -> H`). Load-bearing for `classify_real`; the char-0 mirror of the `clifford_correction` `delta(n mod 8)` table above, with no simpler closed form than the eight cases. |
| Rational `BW(ℚ)` class extended to the real Bott index | `src/forms/witt/brauer_wall.rs::RationalBrauerWallClass::real_bott_index` | Yes. | The eight combinations of dimension parity, signed-discriminant sign, and real ramification of `c(q)` reconstruct the class in `BW(ℝ) ≅ ℤ/8`. This is the Wall exact-sequence coordinate table behind `ℚ -> ℝ`, derived from the Bott table rather than a new catalogue. |
| Finite loopy-value catalogue (`0`, `*`, `on`, `off`, `over`, `under`, `±`, `tis`, `tisn`, `dud`, plus integer `s&t` tags) | `src/games/loopy/::LoopyValue` methods | Yes. | The named finite catalogue and onside/offside tag surface are the intended public boundary; full loopy equality remains outside this table. |
| Python finite odd-field dispatch table | `src/py/forms.rs::finite_field_order`, `with_finite_odd_metric`, `with_finite_odd_metrics`, `with_finite_odd_value` | Yes for now. | Rust must monomorphise concrete const-generic types; replacing this needs a dynamic finite-field type or a generated support macro, not a numeric formula. |
| Python prime-field dispatch table | `src/py/forms.rs::with_prime_field`, `is_sum_of_n_squares` | Yes for now. | A formula such as "all primes" would not instantiate Rust types. |
| Python char-2 finite-field dispatch table | `src/py/forms.rs::{with_finite_char2_field, with_finite_char2_metric, with_finite_char2_metrics}` | Yes for now. | Degree in `{1,2,3,4}` dispatch to `Fpn<2,N>` monomorphs; the char-2 companion to the finite odd-field dispatch. Same monomorphisation constraint. |
| Python local-field Springer dispatch tables | `src/py/forms.rs::{springer_decompose_qp, springer_decompose_qq, springer_decompose_laurent, springer_decompose_ramified_qp4_e2, springer_decompose_ramified_qp4_e3, springer_decompose_local}` | Yes for now. | Finite `(p)`, `(p, residue_degree)`, `(p, degree)`, and local-algebra-type dispatch over the supported `Qp/Qq/Laurent/Ramified` monomorphs. Rust must instantiate concrete const-generic field types, so the supported cells are an explicit table, not a formula. |
| Python coin-family string aliases | `src/py/games.rs::parse_coin_family` | Yes. | API vocabulary. |

## Out of scope (deliberately not tables)

Recorded so a future sweep does not re-flag them as gaps:

- **Eisenstein normalization constants** (`240`, `-504`, `65520/691`, ...) are computed
  at runtime from the single Bernoulli source (`forms/integral/mass_formula.rs::bernoulli`);
  the literals live only in `forms/integral/modular.rs` tests as pinned oracles. Keeping
  them derived rather than tabled is a deliberate discipline (see the comment in
  `eisenstein_constants_derive_from_the_shared_bernoulli_source`).
- **Local Hilbert-symbol factors** `eps(u) = (u-1)/2 mod 2` and `omega(u) = (u^2-1)/8 mod 2`
  (`forms/local_global/padic.rs::{eps2, omega2}`) are closed-form number-theoretic
  functions, not curated data.
- **Reed-Muller generator matrices** (`forms/integral/codes.rs::reed_muller_code`)
  are generated from squarefree monomial evaluations over `F_2^m`; the shipped
  `BW16` constructor consumes that generated family rather than adding a new
  curated code table.
- **The ogham language surface** — the world catalogue, builtin-function names, and reserved
  keywords (`src/ogham/{eval,parse,lex}.rs`) — is public API vocabulary but is owned by the
  language spec `docs/ogham/ogham.md`, not this inventory.
- **`clifford/` and `linalg/`** carry no curated lookup tables: signs go through `Scalar::neg`
  and blade products / reductions are computed index arithmetic.
