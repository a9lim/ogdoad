import Ogdoad.Algebra.ZModTwo

/-!
# Shared Artin--Schreier algebra

This module collects paper-independent characteristic-two Artin--Schreier
facts used by the Gold and canonical-nim developments.  It also removes the
unused local copy formerly carried by the excess development.  The module has
no dependency on any paper-specific surface.
-/

namespace Ogdoad.ArtinSchreier

open Polynomial
open scoped CharTwo

noncomputable section

section Basic

variable {K : Type*} [CommRing K] [CharP K 2]

/-- The Artin--Schreier map is additive in characteristic two. -/
theorem add (x y : K) :
    (x + y) ^ 2 + (x + y) = (x ^ 2 + x) + (y ^ 2 + y) := by
  ring_nf
  simp

/-- If `u` has source `t` and `v` sources `lambda + b*t`, then `v + b*u`
sources `lambda` whenever `b` is idempotent. -/
theorem tower_lift (u t b v lambda : K)
    (hu : u ^ 2 + u = t) (hb : b ^ 2 = b)
    (hv : v ^ 2 + v = lambda + b * t) :
    (v + b * u) ^ 2 + (v + b * u) = lambda := by
  rw [add, hv]
  rw [mul_pow, hb]
  calc
    lambda + b * t + (b * u ^ 2 + b * u) =
        lambda + b * (t + (u ^ 2 + u)) := by ring
    _ = lambda := by rw [hu, CharTwo.add_self_eq_zero]; simp

/-- The two sources of one Artin--Schreier value differ by one. -/
theorem companion (w lambda : K) (hw : w ^ 2 + w = lambda) :
    (w + 1) ^ 2 + (w + 1) = lambda := by
  rw [add, hw]
  have hone : (1 : K) ^ 2 + 1 = 0 := by simp
  rw [hone, add_zero]

end Basic

section FiniteField

/-- The Artin--Schreier endomorphism of a finite characteristic-two field,
viewed as an `F_2`-linear map. -/
noncomputable def linear
    (K : Type*) [Field K] [Finite K] [Algebra F2 K] : K →ₗ[F2] K :=
  (FiniteField.frobeniusAlgHom F2 K).toLinearMap - LinearMap.id

@[simp]
theorem linear_apply
    {K : Type*} [Field K] [Finite K] [Algebra F2 K] (x : K) :
    linear K x = x ^ 2 + x := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F2 K).injective 2
  simp [linear]

/-- Absolute trace is invariant under the characteristic-two Frobenius. -/
theorem absoluteTrace_sq
    {K : Type*} [Field K] [Finite K] [Algebra F2 K] (x : K) :
    Algebra.trace F2 K (x ^ 2) = Algebra.trace F2 K x := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F2 K).injective 2
  apply (algebraMap F2 K).injective
  rw [trace_eq_sum_automorphisms (K := F2) (L := K) (x ^ 2)]
  calc
    ∑ sigma : Gal(K / F2), sigma (x ^ 2) =
        ∑ sigma : Gal(K / F2), (sigma x) ^ 2 := by simp
    _ = (∑ sigma : Gal(K / F2), sigma x) ^ 2 := by rw [sum_pow_char]
    _ = (algebraMap F2 K (Algebra.trace F2 K x)) ^ 2 := by
      rw [trace_eq_sum_automorphisms (K := F2) (L := K) x]
    _ = algebraMap F2 K (Algebra.trace F2 K x) := by
      rw [← map_pow, ZMod.pow_card]

/-- Every Artin--Schreier value has zero absolute trace. -/
theorem absoluteTrace_apply_zero
    {K : Type*} [Field K] [Finite K] [Algebra F2 K] (x : K) :
    Algebra.trace F2 K (x ^ 2 + x) = 0 := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F2 K).injective 2
  rw [map_add, absoluteTrace_sq]
  exact CharTwo.add_self_eq_zero _

/-- The kernel of the Artin--Schreier map is exactly the prime field. -/
theorem ker_linear
    {K : Type*} [Field K] [Finite K] [Algebra F2 K] :
    LinearMap.ker (linear K) = F2 ∙ (1 : K) := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F2 K).injective 2
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker, linear_apply] at hx
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
    rw [LinearMap.mem_ker, linear_apply]
    simp only [Algebra.smul_def, mul_one]
    rw [← map_pow, ZMod.pow_card]
    exact CharTwo.add_self_eq_zero _

/-- The Artin--Schreier image is the absolute-trace kernel. -/
theorem range_linear_eq_ker_trace
    {K : Type*} [Field K] [Finite K] [Algebra F2 K] :
    LinearMap.range (linear K) = LinearMap.ker (Algebra.trace F2 K) := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F2 K).injective 2
  apply Submodule.eq_of_le_of_finrank_eq
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    rw [LinearMap.mem_ker, linear_apply]
    exact absoluteTrace_apply_zero x
  · have hAS := LinearMap.finrank_range_add_finrank_ker (linear K)
    rw [ker_linear, finrank_span_singleton (by exact one_ne_zero)] at hAS
    have htrSurj : Function.Surjective (Algebra.trace F2 K) :=
      Algebra.trace_surjective F2 K
    have htrRange : LinearMap.range (Algebra.trace F2 K) = ⊤ :=
      LinearMap.range_eq_top.mpr htrSurj
    have htr := LinearMap.finrank_range_add_finrank_ker (Algebra.trace F2 K)
    rw [htrRange, finrank_top] at htr
    norm_num at htr
    omega

/-- The finite-field Artin--Schreier exact sequence in elementwise form. -/
theorem trace_eq_zero_iff_exists
    {K : Type*} [Field K] [Finite K] [Algebra F2 K] {a : K} :
    Algebra.trace F2 K a = 0 ↔ ∃ w : K, w ^ 2 + w = a := by
  constructor
  · intro htrace
    have hmem : a ∈ LinearMap.ker (Algebra.trace F2 K) := htrace
    rw [← range_linear_eq_ker_trace] at hmem
    rcases hmem with ⟨w, hw⟩
    exact ⟨w, by simpa using hw⟩
  · rintro ⟨w, rfl⟩
    exact absoluteTrace_apply_zero w

end FiniteField

section Polynomial

variable {K : Type*} [Field K] [CharP K 2]

/-- The quadratic Artin--Schreier polynomial with source `a`. -/
abbrev polynomial (a : K) : K[X] := X ^ 2 + X + C a

@[simp]
theorem isRoot_polynomial_iff (a x : K) :
    (polynomial a).IsRoot x ↔ x ^ 2 + x = a := by
  rw [Polynomial.IsRoot.def]
  simp only [polynomial, eval_add, eval_pow, eval_X, eval_C]
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

omit [CharP K 2] in
@[simp]
theorem natDegree_polynomial (a : K) : (polynomial a).natDegree = 2 := by
  simpa [polynomial] using
    (natDegree_quadratic (a := (1 : K)) (b := 1) (c := a) one_ne_zero)

omit [CharP K 2] in
theorem monic_polynomial (a : K) : (polynomial a).Monic := by
  have h := Polynomial.isMonicOfDegree_add_add_two (R := K) (1 : K) a
  simpa [polynomial] using h.monic

/-- Over a finite characteristic-two field, `X^2 + X + a` is irreducible
exactly when `a` has absolute trace one. -/
theorem irreducible_polynomial_iff_trace_eq_one
    [Finite K] [Algebra F2 K] (a : K) :
    Irreducible (polynomial a) ↔ Algebra.trace F2 K a = 1 := by
  have hp0 : polynomial a ≠ 0 := (monic_polynomial a).ne_zero
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three
    (p := polynomial a)
    (by rw [natDegree_polynomial])
    (by rw [natDegree_polynomial]; omega)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  simp only [Polynomial.mem_roots hp0, isRoot_polynomial_iff]
  constructor
  · intro hnoroot
    apply Ogdoad.zmod2_eq_one_of_ne_zero
    intro hzero
    obtain ⟨w, hw⟩ := (trace_eq_zero_iff_exists (K := K)).mp hzero
    exact hnoroot w hw
  · intro hone w hw
    have hzero : Algebra.trace F2 K a = 0 :=
      (trace_eq_zero_iff_exists (K := K)).mpr ⟨w, hw⟩
    rw [hone] at hzero
    exact one_ne_zero hzero

end Polynomial

end

end Ogdoad.ArtinSchreier
