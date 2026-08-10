import Mathlib

/-!
# The all-exponent Gold-diagonal source

This file kernel-checks the algebraic identities behind the recursive source
for the canonical-basis diagonal of every Gold form.  The concrete nim tower
and its relative traces remain implemented in Rust; Lean proves the
load-bearing facts used by the construction:

* if the quadratic conjugation sends `u` to `u + 1`, the trace pairing on the
  lower and upper basis blocks recovers `B` and `A + B` from `A + u*B`; and
* an Artin--Schreier source in the lower field lifts through the tower generator;
  and
* over every finite characteristic-two field, the Artin--Schreier image is
  exactly the kernel of absolute trace.

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

section FiniteFieldArtinSchreier

/-- The Artin--Schreier endomorphism of a finite characteristic-two field,
viewed as an `F_2`-linear map. -/
noncomputable def artinSchreierLinear
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod 2) K] :
    K →ₗ[ZMod 2] K :=
  (FiniteField.frobeniusAlgHom (ZMod 2) K).toLinearMap - LinearMap.id

@[simp]
theorem artinSchreierLinear_apply
    {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K] (x : K) :
    artinSchreierLinear K x = x ^ 2 + x := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  simp [artinSchreierLinear]

/-- Absolute trace is invariant under the characteristic-two Frobenius. -/
theorem absoluteTrace_sq_eq_absoluteTrace
    {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K]
    (x : K) :
    Algebra.trace (ZMod 2) K (x ^ 2) = Algebra.trace (ZMod 2) K x := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  apply (algebraMap (ZMod 2) K).injective
  rw [trace_eq_sum_automorphisms (K := ZMod 2) (L := K) (x ^ 2)]
  calc
    ∑ sigma : Gal(K / ZMod 2), sigma (x ^ 2) =
        ∑ sigma : Gal(K / ZMod 2), (sigma x) ^ 2 := by simp
    _ = (∑ sigma : Gal(K / ZMod 2), sigma x) ^ 2 := by
      rw [sum_pow_char]
    _ = (algebraMap (ZMod 2) K (Algebra.trace (ZMod 2) K x)) ^ 2 := by
      rw [trace_eq_sum_automorphisms (K := ZMod 2) (L := K) x]
    _ = algebraMap (ZMod 2) K (Algebra.trace (ZMod 2) K x) := by
      rw [← map_pow, ZMod.pow_card]

/-- Every Artin--Schreier value has zero absolute trace. -/
theorem absoluteTrace_artinSchreier_zero
    {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K]
    (x : K) :
    Algebra.trace (ZMod 2) K (x ^ 2 + x) = 0 := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  rw [map_add, absoluteTrace_sq_eq_absoluteTrace]
  exact CharTwo.add_self_eq_zero _

/-- The kernel of the Artin--Schreier map is exactly the prime field. -/
theorem ker_artinSchreierLinear
    {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K] :
    LinearMap.ker (artinSchreierLinear K) = (ZMod 2) ∙ (1 : K) := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker, artinSchreierLinear_apply] at hx
    have hfac : x * (x + 1) = 0 := by
      calc
        x * (x + 1) = x ^ 2 + x := by ring
        _ = 0 := hx
    rcases mul_eq_zero.mp hfac with hx0 | hx1
    · subst x
      exact Submodule.zero_mem _
    · have hxone : x = 1 := by
        have := eq_neg_of_add_eq_zero_left hx1
        simpa using this
      subst x
      exact Submodule.mem_span_singleton_self 1
  · intro hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [LinearMap.mem_ker, artinSchreierLinear_apply]
    simp only [Algebra.smul_def, mul_one]
    rw [← map_pow, ZMod.pow_card]
    exact CharTwo.add_self_eq_zero _

/-- Rank--nullity and trace surjectivity identify the Artin--Schreier image
with the absolute-trace kernel. -/
theorem range_artinSchreierLinear_eq_ker_trace
    {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K] :
    LinearMap.range (artinSchreierLinear K) =
      LinearMap.ker (Algebra.trace (ZMod 2) K) := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  apply Submodule.eq_of_le_of_finrank_eq
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    rw [LinearMap.mem_ker, artinSchreierLinear_apply]
    exact absoluteTrace_artinSchreier_zero x
  · have hAS :=
      LinearMap.finrank_range_add_finrank_ker (artinSchreierLinear K)
    rw [ker_artinSchreierLinear,
      finrank_span_singleton (by exact one_ne_zero)] at hAS
    have htrSurj : Function.Surjective (Algebra.trace (ZMod 2) K) :=
      Algebra.trace_surjective (ZMod 2) K
    have htrRange : LinearMap.range (Algebra.trace (ZMod 2) K) = ⊤ :=
      LinearMap.range_eq_top.mpr htrSurj
    have htr :=
      LinearMap.finrank_range_add_finrank_ker (Algebra.trace (ZMod 2) K)
    rw [htrRange, finrank_top] at htr
    norm_num at htr
    omega

/-- The finite-field Artin--Schreier exact sequence, in the exact form used by
the Gold-diagonal theorem. -/
theorem trace_eq_zero_iff_exists_artinSchreier
    {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K]
    {lambda : K} :
    Algebra.trace (ZMod 2) K lambda = 0 ↔
      ∃ w : K, w ^ 2 + w = lambda := by
  constructor
  · intro htrace
    have hmem : lambda ∈ LinearMap.ker (Algebra.trace (ZMod 2) K) := htrace
    rw [← range_artinSchreierLinear_eq_ker_trace] at hmem
    rcases hmem with ⟨w, hw⟩
    exact ⟨w, by simpa using hw⟩
  · rintro ⟨w, rfl⟩
    exact absoluteTrace_artinSchreier_zero w

end FiniteFieldArtinSchreier

section ArtinSchreier

variable {K : Type*} [CommRing K] [CharP K 2]

/-- The Artin--Schreier map is additive in characteristic two. -/
theorem artinSchreier_add (x y : K) :
    (x + y) ^ 2 + (x + y) = (x ^ 2 + x) + (y ^ 2 + y) := by
  ring_nf
  simp

/-- One quadratic-tower lift of an Artin--Schreier source.  If `u^2+u=t`,
`b` is a bit, and `v` sources `lambda+b*t` downstairs, then `v+b*u` sources
`lambda` upstairs. -/
theorem artinSchreier_tower_lift (u t b v lambda : K)
    (hu : u ^ 2 + u = t) (hb : b ^ 2 = b)
    (hv : v ^ 2 + v = lambda + b * t) :
    (v + b * u) ^ 2 + (v + b * u) = lambda := by
  rw [artinSchreier_add, hv]
  rw [mul_pow, hb]
  calc
    lambda + b * t + (b * u ^ 2 + b * u) =
        lambda + b * (t + (u ^ 2 + u)) := by ring
    _ = lambda := by rw [hu, CharTwo.add_self_eq_zero]; simp

/-- The two Artin--Schreier sources differ by one. -/
theorem artinSchreier_companion (w lambda : K)
    (hw : w ^ 2 + w = lambda) :
    (w + 1) ^ 2 + (w + 1) = lambda := by
  rw [artinSchreier_add, hw]
  have hone : (1 : K) ^ 2 + 1 = 0 := by
    simp
  rw [hone, add_zero]

end ArtinSchreier

end Ogdoad.GoldDiagonal
