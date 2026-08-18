import Mathlib

/-!
# The all-exponent Gold-diagonal source

This file kernel-checks the algebraic identities behind the recursive source
for the canonical-basis diagonal of every Gold form.  The concrete nim tower
and its relative traces remain implemented in Rust; Lean proves the
load-bearing facts used by the construction:

* if the quadratic conjugation sends `u` to `u + 1`, the trace pairing on the
  lower and upper basis blocks recovers `B` and `A + B` from `A + u*B`; and
* elements from the base of a quadratic extension have zero absolute trace
  upstairs.

The reusable Artin--Schreier exact sequence and tower-source algebra live in
`Ogdoad.Algebra.ArtinSchreier` rather than in this Gold-specific module.

No custom axiom supplies the final source.
-/

namespace Ogdoad.GoldDiagonal

open scoped CharTwo

section QuadraticTraceBlocks

variable {K : Type*} [CommRing K] [CharP K 2]

/-- The relative trace attached to a quadratic conjugation. -/
def relativeTrace (sigma : K ≃+* K) (x : K) : K := x + sigma x

/-- On a quadratic tower with `sigma(u)=u+1`, the lower basis block extracts
the upper coefficient `B` from `A+uB`. -/
theorem relativeTrace_lower_block (sigma : K ≃+* K)
    (u A B e : K) (hu : sigma u = u + 1)
    (hA : sigma A = A) (hB : sigma B = B) (he : sigma e = e) :
    relativeTrace sigma ((A + u * B) * e) = B * e := by
  simp only [relativeTrace, map_mul, map_add, hu, hA, hB, he]
  linear_combination (A * e + u * B * e) *
    (CharTwo.add_self_eq_zero (1 : K))

/-- The upper basis block `u*e` extracts `A+B` from the same element. -/
theorem relativeTrace_upper_block (sigma : K ≃+* K)
    (u A B e : K) (hu : sigma u = u + 1)
    (hA : sigma A = A) (hB : sigma B = B) (he : sigma e = e) :
    relativeTrace sigma ((A + u * B) * (u * e)) = (A + B) * e := by
  simp only [relativeTrace, map_mul, map_add, hu, hA, hB, he]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (A * u * e + u ^ 2 * B * e + u * B * e) * htwo

/-- The block reconstruction used by the Rust recursion.  If `lambda0` is the
dual of the lower diagonal and `lambda1` the dual of the upper diagonal, then
`(lambda0+lambda1)+u*lambda0` has exactly those two trace-pairing blocks. -/
theorem dual_block_reconstruction (sigma : K ≃+* K)
    (u lambda0 lambda1 e : K) (hu : sigma u = u + 1)
    (h0 : sigma lambda0 = lambda0) (h1 : sigma lambda1 = lambda1)
    (he : sigma e = e) :
    relativeTrace sigma (((lambda0 + lambda1) + u * lambda0) * e) =
        lambda0 * e ∧
      relativeTrace sigma (((lambda0 + lambda1) + u * lambda0) * (u * e)) =
        lambda1 * e := by
  constructor
  · exact relativeTrace_lower_block sigma u (lambda0 + lambda1) lambda0 e hu
      (by rw [map_add, h0, h1]) h0 he
  · have h := relativeTrace_upper_block sigma u (lambda0 + lambda1) lambda0 e hu
      (by rw [map_add, h0, h1]) h0 he
    have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hsum : (lambda0 + lambda1 + lambda0) * e = lambda1 * e := by
      linear_combination lambda0 * e * htwo
    exact h.trans hsum

end QuadraticTraceBlocks

section AbsoluteTrace

/-- Every element of the base of a quadratic characteristic-two extension has
zero absolute trace upstairs.  This is the formal reason the recursively
descended Gold diagonal dual lies in the Artin--Schreier image. -/
theorem absolute_trace_of_quadratic_base_zero
    {F K : Type*} [Field F] [Field K]
    [Algebra (ZMod 2) F] [Algebra F K] [Algebra (ZMod 2) K]
    [IsScalarTower (ZMod 2) F K]
    [FiniteDimensional (ZMod 2) F] [FiniteDimensional F K]
    (hdeg : Module.finrank F K = 2) (lambda : F) :
    Algebra.trace (ZMod 2) K (algebraMap F K lambda) = 0 := by
  letI : CharP F 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  rw [← Algebra.trace_trace (R := ZMod 2) (S := F) (T := K)]
  rw [Algebra.trace_algebraMap, hdeg]
  simp

end AbsoluteTrace

end Ogdoad.GoldDiagonal
