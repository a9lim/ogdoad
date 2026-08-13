# `src/scalar/` editing guide

This pillar defines coefficient worlds. Group code by mathematical role, not by
which consumer currently uses it. `mod.rs` re-exports the public surface.

## Map

| path | responsibility |
| --- | --- |
| `mod.rs` | borrow-based `Scalar` ring interface and public exports |
| `exactness.rs` | exact/field marker traits used by law tests and generic algorithms |
| `analytic.rs` | opt-in exact and series root interfaces |
| `valued.rs`, `residue.rs` | valuations, uniformizers, angular components, residue fields |
| `integrality.rs` | field/ring-of-integers and fraction-field relationships |
| `extension.rs` | finite and cyclic Galois extension interfaces |
| `exact/` | `Integer` and `Rational` |
| `finite_field/` | `Fp`, `Fpn`, `Nimber`, `WittVec`, and shared Galois algorithms |
| `big/` | shared CNF canonicalization, `Surreal`, `Omnific`, and `Ordinal` |
| `small/` | `Zp`, `Qp`, `Qq`, and local analytic operations |
| `functor/` | `Surcomplex`, `Laurent`, `Ramified`, and `Gauss` extensions |
| `global/` | exact `F_q(t)` plus finite-precision adelic cells |
| `poly.rs` | polynomial arithmetic, exact when its coefficients are exact |
| `poly_factor.rs` | crate-private finite-field factorization over `Poly` |
| `newton.rs` | Newton polygons over valued coefficients |
| `tropical.rs` | dual idempotent semirings; deliberately not `Scalar` |

## Exactness boundary

- Exact rings/fields participate in the full scalar law tests.
- `Qp`, `Qq`, `Laurent`, `Ramified`, `Gauss`, `Adele`, and runtime `LocalQp`
  are represented precision models. Do not claim exact associativity across
  truncation or cancellation boundaries.
- `LocalQp` has runtime prime/precision data and therefore does not implement
  the compile-time `Scalar` interface.
- `Nimber(u128)` is exactly `F_{2^128}`.
- `Surreal` stores finite-support Hahn/CNF expressions with rational
  coefficients. Non-monomial inverses and many algebraic roots require
  infinite support and correctly return `None`.
- `Ordinal` uses checked Kummer carries. `nim_mul`, `nim_pow`, `checked_inv`,
  and `checked_sqrt` return the explicit escape boundary; its `Scalar::mul`
  wrapper may panic when callers ignore that boundary.

## Invariants

- Keep `Scalar` borrow-based. Do not make `Add`, `Mul`, or related owned
  operators supertraits: method shadowing changes generic resolution and adds
  unnecessary clones.
- Capability traits (`ExactRoots`, `SeriesRoots`, `Ordered`, `Valued`,
  `ResidueField`, `FieldExtension`) remain opt-in. A scalar need not support
  every capability.
- Generic signs use `Scalar::neg`; never branch on characteristic.
- `Tropical<C>` is a `Semiring`, not a `Scalar`, because tropical addition has
  no inverse. `MaxPlus` and `MinPlus` are distinct types.
- The common surreal/ordinal CNF code is a canonicalization function, not a
  shared algebraic type. The two worlds have different orders and operations.
- Surreal recursion descends through exponents only. Recursing on the whole
  number breaks the termination argument.
- `FieldExtension::extension_degree` is relative to its declared base;
  `FiniteField::ext_degree` is absolute over the prime field.
- `Poly<S>` intentionally has inherent arithmetic and a `Scalar` impl: the
  former serves fraction-field code; the latter makes `F_q[t]` a typed ring of
  integers.
- `Fpn::field_order()` is the size of the field; an element's order is
  `multiplicative_order(&self)`.
- Nimber Galois free functions delegate to `FiniteField`; add shared operations
  to the trait instead of duplicating inherent methods that can recurse through
  name shadowing.

## Local conventions

- P-adic square APIs distinguish unknown from known nonsquare:
  `Option<bool>` and `Option<Option<T>>` are intentional.
- `Surcomplex` is a field construction only over suitable characteristic-zero
  bases; over characteristic two, adjoining `i^2=-1=1` is degenerate.
- `RationalFunction` is exact and global, so it is not itself `Valued`; place
  valuations are supplied separately. `Gauss` is a valued transcendental
  extension and is a precision model.
- Preserve source/certificate boundaries in ordinal excess tables. A table row
  extends the implemented window; it does not prove the universal excess rule.

## Verification

Run focused backend tests, then:

```sh
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
```

Changes to `Scalar`, rendering, or a bound backend also require the Python
feature and stub checks listed in the root `AGENTS.md`.
