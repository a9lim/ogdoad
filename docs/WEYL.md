# Weyl pillar plan

The Weyl pillar grows along its own mathematical spine rather than mirroring
the finite Clifford blade engine mechanically:

```text
PBW algebra
    -> canonical transformations
    -> filtrations and symbols
    -> representations and central fibres
    -> p-symbols and Brauer evidence
    -> ideals and D-modules
```

Every layer remains generic over the commutative `Scalar` contract where its
laws are integral. Field-only structure, characteristic-specific theorems, and
computations that can expand without a practical bound receive explicit traits,
errors, or caller-supplied budgets. Finite PBW support never turns the
infinite-dimensional algebra into a finite regular representation.

## Wave 1: robust operator kernel (implemented)

The first wave makes the existing PBW engine safe as a foundation for every
later layer.

- Replace exponent-by-exponent general normal ordering with grouped
  contractions whose work is controlled by the available contraction degree,
  not merely by a possibly enormous appended exponent.
- Add an explicit expansion budget covering intermediate and output PBW terms.
  Exponent overflow and resource exhaustion remain different errors.
- Thread the budget through multiplication, powers, and commutators while
  retaining the existing checked and panicking convenience tiers.
- Add checked constructors for dimensions, generator indices, standard layout,
  and monomial exponent vectors.
- Add coefficient base change for commutator contexts and PBW elements.
- Add a finite-support sparse multivariate polynomial type with checked `u128`
  multidegrees and canonical zero-eliding support.
- Extend the standard polynomial action from rank one on dense `S[t]` to rank
  `n` on sparse `S[t_0,...,t_(n-1)]`, with an explicit action budget.
- Keep the dense rank-one action as a compatibility convenience backed by the
  same mathematical contract.

Wave 1 is complete when:

1. large exponents with small contraction degree do not cause linear work in
   the large exponent;
2. every materialized expansion can be bounded without conflating exhaustion
   with a mathematical zero or overflow;
3. the optimized standard product, general grouped normalizer, literal-word
   reducer, and polynomial action agree on their shared exact test domain;
4. associativity is exercised directly over exact characteristic-zero,
   prime-characteristic, characteristic-two, and composite-characteristic
   backends; and
5. the root Rust formatting, test, clippy, and rustdoc gates pass.

## Wave 2: transformations and symbols (implemented)

- Alternating-form reduction returns a certified Darboux basis, inverse change
  of basis, and radical basis under the `ExactFieldScalar` capability.
- The Weyl layer materializes the decomposition
  `A(V, omega) ~= A_r(S) tensor S[c_1,...,c_s]` and transports elements through
  it.
- Checked affine-linear Weyl homomorphisms provide composition, inverse,
  direct-sum, and coordinate-embedding operations under expansion budgets.
- Standard Fourier, scaling, symmetric momentum shear, translation, and parity
  maps return `WeylAutomorphism`; formal adjoint returns the distinct
  `WeylAntiAutomorphism` type and reverses products during substitution.
- Bernstein and differential-order filtrations return principal symbols in the
  sparse commutative polynomial type. The constant Poisson bracket uses the
  convention `{z_i,z_j} = omega[i][j]` and has an explicit expansion budget.
- The polynomial `hbar` deformation has checked element specializations at
  `hbar = 0` and `hbar = 1`.

Wave 2's verification contract is that transformations preserve multiplication
and round-trip through their inverses, anti-automorphisms reverse products,
principal symbols satisfy the product law, the leading commutator agrees with
the Poisson bracket, and Darboux coordinates reconstruct both the source form
and its radical. These are exercised over exact characteristic-zero and
characteristic-two backends, with randomized low-dimensional laws.

## Wave 3: modular representations and pillar joins (implemented)

- Exact-field Darboux coordinates provide transported radical generators in all
  characteristics. In positive characteristic they also provide the full
  centre generators: characteristic powers of paired coordinates and linear
  radical coordinates. Every reported source-coordinate element is checked
  independently against all algebra generators.
- The characteristic-`p` centre carries a lazy PBW basis over it, indexed by
  little-endian base-`p` digits with paired exponents below `p`. Complete
  materialization requires an explicit element cap.
- Standard central characters produce bounded quotients with basis
  `0 <= exponent_i < p`. Split characters with checked `p`-th roots produce
  exact `p^n`-dimensional truncated-polynomial modules and generator action
  matrices under basis, matrix-entry, and work budgets.
- In characteristic two, the central fibre
  `x_i^2 = a_i`, `d_i^2 = b_i` with the existing Clifford algebra whose polar
  pairing satisfies `B(x_i,d_j) = delta_ij` is implemented by checked reductions
  in both directions. Clifford multiplication is an independent oracle for the
  reduced Weyl product.
- In odd characteristic, supported split fibres are certified as full matrix
  algebras by exact unit-pivot rank of every reduced PBW basis image.
- Python exposes separate `RationalWeylAlgebra`/`RationalWeylElement` and
  `NimberWeylAlgebra`/`NimberWeylElement` types. Products, transformations,
  centre transports, finite reductions, Clifford comparisons, and split-module
  matrices retain the Rust budget and error distinctions.

The standard nonsingular input here is that, in characteristic `p`, the rank-
`n` Weyl algebra has centre generated by the `p`-th powers and is Azumaya over
that centre; see Mariusz Wodzicki, [*Algebras of p-symbols, noncommutative
p-residue, and the Brauer group*](https://math.berkeley.edu/~wodzicki/prace/Henrifest.pdf),
Proposition 4.2. Ogdoad uses the certified Darboux decomposition to add the
polynomial radical variables in the degenerate case. This cited theorem is not
proved in the repository: the implementation independently checks the central
generators, quotient relations, module relations, and the supported finite
matrix and Clifford certificates.

This wave is complete when every reported central generator commutes
independently, each central reduction is a tested algebra homomorphism, and the
characteristic-two fibre agrees exactly with the Clifford engine.

## Wave 3.5: p-symbol classification surface (implemented)

- Every bounded standard central fibre has an executable tensor presentation
  by rank-one `p`-symbols `S_(a_i,b_i)`, backed by the existing reduced-fibre
  multiplication engine rather than a second presentation-specific product.
- The tensor noncommutative `p`-residue is the top reduced PBW coefficient. On
  a verified splitting module it is compared exactly with matrix trace, with
  the source convention `residue = (-1)^n trace`.
- When `b_i` is invertible, the factor `S_(a_i,b_i)` converts to the cyclic
  presentation `(b_i,a_i b_i]`. The Artin--Schreier power, multiplicative
  power, and crossed relation are all rechecked inside the finite fibre.
- Brauer reports distinguish an executable, cited `p`-symbol presentation from
  an internally computed split certificate. A presentation alone returns
  unknown split status; only the existing exact full-rank matrix certificate
  upgrades it to split.
- Central characters pull back through canonical automorphisms by reducing
  `phi(z_i)^p` in the relevant fibre. This calculation retains the extra
  quadratic term of mixed characteristic-two coordinates instead of applying
  a characteristic-zero formula.
- Arbitrary exact-field alternating presentations acquire bounded central
  fibres through their certified Darboux decomposition. Paired characteristic-
  power values and linear radical values remain distinct; multiplication is
  independently compared after lifting back to source coordinates.
- The Rational, `Fp3`, and Nimber Python families now expose the stable
  computational surface of Waves 1--3.5: sparse polynomials and actions, both
  filtrations,
  principal symbols and Poisson brackets, the polynomial `hbar` family,
  Darboux transport, affine/canonical maps, centres and finite fibres,
  p-symbols, character pullbacks, and transported-fibre checks. Raw Rust map
  and fibre structs remain implementation-facing rather than runtime-tagged
  Python containers.

The Azumaya and `p`-torsion Brauer interpretation remains the cited theorem
from Wodzicki used in Wave 3. Wave 3.5 implements and checks its concrete
presentations, conversions, residues, transports, and supported splitting
certificates; it does not relabel that external theorem as proved here.

This wave is complete when the cyclic relations, residue/trace identity,
character pullbacks (including the characteristic-two shear correction), and
source-versus-Darboux fibre products all pass independent exact tests.

## Wave 4: certified computational D-modules

- Add admissible PBW monomial orders, leading terms, and weighted elimination
  orders.
- Add certificate-producing left reduction and `S`-polynomials over supported
  exact fields.
- Implement a budgeted Buchberger procedure with separate complete,
  exhausted, and unsupported-coefficient outcomes.
- Add left-ideal membership, cyclic module presentations, symbol ideals, and
  bounded characteristic-variety or holonomicity reports.
- Validate a small source-backed suite before considering restriction,
  integration, de Rham, or Bernstein--Sato algorithms.

This wave is complete when every positive membership result carries a replayable
combination certificate, incomplete searches report exhaustion rather than a
mathematical answer, and the curated examples agree with an independent source.

## Deliberate boundaries

- No full-basis enumeration or generic finite regular-representation inverse.
- No analytic exponential or metaplectic implementer represented as a finite
  PBW element; these belong to actions or explicitly completed algebras.
- No generic Moyal coefficients until the scalar contract states which integer
  denominators are representably invertible.
- No field centre theorem generalized silently to quotient or precision rings.
- No q-Weyl, generalized Weyl, or large D-module facade before the classical
  spine above is complete and independently verified.
