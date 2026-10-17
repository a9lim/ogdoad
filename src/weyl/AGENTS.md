# `src/weyl/` editing guide

This pillar owns finite-support PBW Weyl algebras over the generic commutative
[`Scalar`](crate::scalar::Scalar) layer. It is a sibling of the Clifford engine,
not a view of its blade representation: Clifford basis monomials are finite
subsets, while Weyl PBW monomials carry arbitrary natural-number exponents.
The one deliberate meeting point is the characteristic-two central-fibre
bridge in `clifford_fiber.rs`.

## Layers

The pillar grows along its own mathematical spine:

```text
PBW algebra
    -> canonical transformations
    -> filtrations and symbols
    -> centres and finite central fibres
    -> p-symbols and Brauer evidence
```

Every layer stays generic over `Scalar` where its laws are integral.
Field-only structure takes the `ExactFieldScalar` capability,
characteristic-specific theorems return explicit errors, and every
computation that can expand without a practical bound has a variant taking
caller-supplied budgets. Ideals,
Gröbner bases, and D-modules are the next layer; they are roadmap work and no
code for them exists yet.

## Map

| path | responsibility |
| --- | --- |
| `mod.rs` | public surface and mathematical boundary |
| `element.rs` | PBW monomials, sparse elements, additive operations, rendering |
| `algebra.rs` | alternating commutator contexts, construction, base change, multiplication, powers, filtration degree, `WeylError` and `WeylExpansionBudget` |
| `product.rs` | the grouped general normal-ordering path and the optimized standard-pair product |
| `polynomial.rs` | sparse commutative multivariate polynomials for actions and symbols |
| `differential.rs` | the standard rank-`n` polynomial action, plus the unbudgeted dense rank-one convenience |
| `normal_form.rs` | Darboux tensor presentation `A ~= A_r(S) ⊗ S[c_1,...,c_s]` and coordinate transport, over the reduction in `forms/symplectic.rs` |
| `transform.rs` | checked affine homomorphisms, automorphisms, and anti-automorphisms |
| `symbol.rs` | Bernstein and differential-order filtrations, principal symbols, and the constant Poisson bracket |
| `deformation.rs` | the polynomial `hbar` commutator family and its specializations |
| `center.rs` | centrality tests, radical generators, the certified characteristic-`p` centre, and its lazy PBW basis |
| `fiber.rs` | bounded central quotients, split modules, and odd-characteristic matrix certificates |
| `clifford_fiber.rs` | the characteristic-two central-fibre isomorphism with Clifford algebras |
| `psymbol.rs` | `p`-symbol presentations, residues, cyclic factors, character pullbacks, and Darboux-transported fibres |

## Algebra contract

For ordered generators `z_0 < ... < z_(m-1)` and an alternating matrix `omega`,

```text
z_i z_j - z_j z_i = omega[i][j].
```

`WeylAlgebra::standard(n)` orders the generators as
`x_0,...,x_(n-1),d_0,...,d_(n-1)` and uses `[d_i,x_j] = delta_ij`.
Multiplication returns canonical PBW order. The general normalizer groups
contractions, so its work follows the available contraction degree rather than
a possibly enormous appended exponent. Integer coefficients enter a scalar
world only through its canonical integer embedding; never cast an exponent to a
backend representation and never divide by a factorial in generic code.

## What each layer certifies

- **Transformations.** Generator images are affine-linear and every
  commutator is checked on construction. Standard Fourier, scaling, symmetric
  momentum shear, translation, and parity maps return `WeylAutomorphism`;
  formal adjoint returns the distinct `WeylAntiAutomorphism`, which reverses
  substitution order. Application takes an expansion budget; composition,
  inverse, direct sum, and embeddings do not expand elements.
- **Symbols.** Principal symbols land in the sparse commutative polynomial
  type. The Poisson bracket uses `{z_i,z_j} = omega[i][j]`. The `hbar` family
  is polynomial, not a power series, with checked specializations.
- **Centres.** Exact-field Darboux coordinates give radical generators in
  every characteristic and, in characteristic `p`, the full centre:
  characteristic powers of paired coordinates and linear radical coordinates.
  The centre description re-checks every reported generator against all
  algebra generators. Its lazy PBW basis over the centre is indexed by base-`p`
  digits, and full materialization needs an element cap.
- **Fibres.** Standard central characters give bounded quotients with basis
  `0 <= exponent_i < p` under a basis-dimension cap. Split modules (with
  checked `p`-th roots) and odd-characteristic full-matrix certificates add
  matrix-entry and work caps. In characteristic two the fibre with
  `x_i^2 = a_i`, `d_i^2 = b_i` is identified in both directions with the
  Clifford algebra whose polar pairing has `B(x_i,d_j) = delta_ij`, and
  Clifford multiplication is an independent oracle for the reduced product.
- **`p`-symbols.** A bounded standard fibre has an executable tensor
  presentation by rank-one symbols `S_(a_i,b_i)`, backed by the fibre's own
  multiplication. The residue is the top reduced PBW coefficient and equals
  `(-1)^n` times the trace on a verified splitting module. When `b_i` is a
  unit, a factor converts to the cyclic presentation `(b_i, a_i b_i]`, whose
  relations are rechecked in a rank-one fibre built from the pair. Central
  characters pull back through automorphisms by reducing `phi(z_i)^p`, which
  keeps the extra quadratic term of characteristic-two coordinates. Arbitrary
  alternating presentations reach bounded fibres through Darboux transport,
  with paired-power and linear-radical character values kept distinct.

## Cited input

In characteristic `p`, the rank-`n` Weyl algebra is Azumaya over the centre
generated by `x_i^p` and `d_i^p`, with Brauer class of order `p` (M. Wodzicki,
[*Algebras of p-symbols, noncommutative p-residue, and the Brauer
group*](https://math.berkeley.edu/~wodzicki/prace/Henrifest.pdf), Prop. 4.2;
the residue sign is Prop. 2.1(c) with (1.14), and the cyclic presentation is
Prop. 8.1). The pillar adds polynomial radical variables in the degenerate
case through the certified Darboux decomposition. The cited theorem is not
proved here; the implementation independently checks central generators,
quotient relations, module relations, residues, cyclic relations, and the
supported matrix and Clifford certificates. A Brauer report from a
presentation alone has unknown split status; only an exact full-rank matrix
certificate upgrades it to split.

## Boundaries

- Elements have finite PBW support, but the algebra is infinite-dimensional.
  Do not add a full-basis enumeration or a finite regular-representation
  inverse.
- Positive characteristic is first-class. In characteristic `p`, standard
  `x_i^p` and `d_i^p` are central, and the ordinary polynomial action is not
  faithful.
- In characteristic two, the Clifford bridge keeps generator squares in
  `Metric::q` and the Weyl pairing in `Metric::b`; neither determines the
  other.
- A `WeylPSymbolPresentation` is a theorem-facing view of an existing bounded
  fibre, not a second multiplication engine.
- Degenerate alternating forms are valid; radical generators are central.
- Darboux witnesses are field-gated through `ExactFieldScalar`. Generic ring
  backends may still use the PBW algebra, maps whose relations check, and the
  unit-pivot invariant classifier.
- An anti-automorphism reverses PBW substitution order. Do not represent formal
  adjoint as an ordinary homomorphism because its generator images are
  affine-linear.
- `u128` exponent overflow is an explicit `WeylError`, with panicking
  convenience wrappers only where a checked method is also public.
- Expanding operations have `*_with_budget` variants taking term and work
  budgets; exhaustion is distinct from exponent overflow and from a
  mathematical zero. The unbudgeted convenience methods (products, actions,
  map application, fibre products, and the dense rank-one action) are for
  trusted inputs; Python's operators use them.
- Precision backends inherit their reassociation boundary. Tests over exact
  backends are not a proof for represented truncation models.
- No analytic exponential or metaplectic implementer as a finite PBW element;
  no generic Moyal coefficients until the scalar contract states which integer
  denominators are invertible; no field-centre theorem silently generalized to
  quotient or precision rings; no q-Weyl, generalized Weyl, or D-module facade
  before its layer is independently verified.

## Verification

Product changes require the public relation tests, agreement among the
optimized standard product, the grouped general normalizer, and the literal
adjacent-word reducer in `tests/weyl_axioms.rs`, associativity over exact
characteristic-zero, prime, characteristic-two, and composite-characteristic
backends, budget-boundary tests, and the rank-`n` polynomial-action oracle.
Transformation and symbol work requires the multiplication, inverse,
Poisson, and leading-commutator oracles in `tests/weyl_transformations.rs`.
Centre and fibre work requires independent centrality, quotient-homomorphism,
module-relation, and Clifford or full-matrix oracles in
`tests/weyl_central_fibers.rs`; `p`-symbol work requires the residue/trace,
cyclic-relation, pullback, and transported-fibre checks in
`tests/weyl_psymbols.rs`. Then run the root Rust gate.
