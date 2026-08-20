# `src/weyl/` editing guide

This pillar owns finite-support PBW Weyl algebras over the generic commutative
[`Scalar`](crate::scalar::Scalar) layer. It is a sibling of the Clifford engine,
not a view of its blade representation: Clifford basis monomials are finite
subsets, while Weyl PBW monomials carry arbitrary natural-number exponents.

## Map

| path | responsibility |
| --- | --- |
| `mod.rs` | public surface and mathematical boundary |
| `element.rs` | PBW monomials, sparse elements, additive operations, rendering |
| `algebra.rs` | alternating commutator contexts, construction, multiplication, filtration |
| `product.rs` | general normal ordering and the standard-pair product |
| `differential.rs` | the rank-one action on `Scalar::Poly` |

## Algebra contract

For ordered generators `z_0 < ... < z_(m-1)` and an alternating matrix `omega`,

```text
z_i z_j - z_j z_i = omega[i][j].
```

`WeylAlgebra::standard(n)` orders the generators as
`x_0,...,x_(n-1),d_0,...,d_(n-1)` and uses `[d_i,x_j] = delta_ij`.
Multiplication returns canonical PBW order. Integer coefficients enter a scalar
world only through its canonical integer embedding; never cast an exponent to a
backend representation and never divide by a factorial in generic code.

## Boundaries

- Elements have finite PBW support, but the algebra is infinite-dimensional.
  Do not add a full-basis enumeration or a finite regular-representation inverse.
- Positive characteristic is first-class. In characteristic `p`, standard
  `x_i^p` and `d_i^p` are central, and the ordinary polynomial action is not
  faithful.
- Degenerate alternating forms are valid; radical generators are central.
- `u128` exponent overflow is an explicit `WeylError`, with panicking convenience
  wrappers only where a checked method is also public.
- Precision scalar backends inherit their existing reassociation boundary. Do
  not describe generic tests over exact backends as a proof for represented
  truncation models.

## Verification

Product changes require the public relation tests, agreement between the
standard and general normalizers, associativity over exact characteristic-zero
and positive-characteristic backends, and the polynomial-action oracle. Then run
the root Rust gate.
