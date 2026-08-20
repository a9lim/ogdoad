# Weyl pillar plan

The Weyl pillar grows along its own mathematical spine rather than mirroring
the finite Clifford blade engine mechanically:

```text
PBW algebra
    -> canonical transformations
    -> filtrations and symbols
    -> representations and central fibres
    -> ideals and D-modules
```

Every layer remains generic over the commutative `Scalar` contract where its
laws are integral. Field-only structure, characteristic-specific theorems, and
computations that can expand without a practical bound receive explicit traits,
errors, or caller-supplied budgets. Finite PBW support never turns the
infinite-dimensional algebra into a finite regular representation.

## Wave 1: robust operator kernel

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

## Wave 2: transformations and symbols

- Extend alternating-form reduction to return a certified Darboux basis,
  inverse change of basis, and radical basis on supported exact fields.
- Materialize the decomposition
  `A(V, omega) ~= A_r(S) tensor S[c_1,...,c_s]` and transport elements through
  it.
- Add checked affine-linear Weyl homomorphisms and their composition, inverse,
  direct-sum, and embedding operations.
- Provide standard Fourier, scaling, shear, translation, parity, and formal
  adjoint maps with explicit automorphism versus anti-automorphism types.
- Add Bernstein and differential-order filtrations, principal symbols, and the
  constant Poisson bracket.
- Add an `hbar` deformation with checked specializations at `hbar = 0` and
  `hbar = 1`.

This wave is complete when transformations preserve multiplication and
round-trip through their inverses, while principal symbols satisfy the product
law and the leading commutator agrees with the Poisson bracket.

## Wave 3: modular representations and pillar joins

- Compute radical and centre generators on field-gated domains while retaining
  a generic generator-commutation centrality check.
- Expose the characteristic-`p` centre and a lazy or budgeted PBW basis over it.
- Construct bounded central-character modules and exact action matrices.
- In characteristic two, identify the central fibre
  `x_i^2 = a_i`, `d_i^2 = b_i` with the existing Clifford algebra whose polar
  pairing satisfies `B(x_i,d_j) = delta_ij`; provide checked reductions in both
  directions and an independent multiplication oracle.
- In odd characteristic, certify the supported matrix-algebra central fibres.
- Bind monomorphic Rational and Nimber Weyl algebras and elements in Python,
  preserving per-backend separation and all budget/error distinctions.

This wave is complete when every reported central generator commutes
independently, each central reduction is a tested algebra homomorphism, and the
characteristic-two fibre agrees exactly with the Clifford engine.

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
