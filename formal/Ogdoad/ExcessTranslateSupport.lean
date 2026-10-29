import Mathlib

/-!
# Sparse support separation under a cubic Frobenius action

These lemmas check the small-exponent arithmetic and coefficient separation
used to show that a nonzero base-field translate of the synchronized sum has
nontrivial total primitive support. The finite-field tensor basis, Frobenius
specialization, and rational-function divisor argument remain paper-level.
Nontrivial total support does not imply full primary multiplicative order.
-/

namespace Ogdoad.Excess

/-- A primitive-cube-root exponent cannot identify two differences of size
at most four modulo a modulus larger than 48. The hypotheses use divisibility,
so no primality or chosen representative of the cube root is needed. -/
theorem small_cubic_collision
    (r u d e : ℤ) (hr : 48 < r)
    (hu : r ∣ u ^ 2 + u + 1)
    (hd : -4 ≤ d ∧ d ≤ 4) (he : -4 ≤ e ∧ e ≤ 4)
    (hcollision : r ∣ d + u * e) : d = 0 ∧ e = 0 := by
  have hnorm : r ∣ d ^ 2 - d * e + e ^ 2 := by
    have h₁ : r ∣ (d + u * e) * (d - (u + 1) * e) :=
      dvd_mul_of_dvd_left hcollision _
    have h₂ : r ∣ (u ^ 2 + u + 1) * e ^ 2 := dvd_mul_of_dvd_left hu _
    have hid : (d + u * e) * (d - (u + 1) * e) +
        (u ^ 2 + u + 1) * e ^ 2 = d ^ 2 - d * e + e ^ 2 := by ring
    rw [← hid]
    exact dvd_add h₁ h₂
  have hdprod : 0 ≤ (d + 4) * (4 - d) := mul_nonneg (by omega) (by omega)
  have heprod : 0 ≤ (e + 4) * (4 - e) := mul_nonneg (by omega) (by omega)
  have hd₂ : d ^ 2 ≤ 16 := by nlinarith
  have he₂ : e ^ 2 ≤ 16 := by nlinarith
  have hnonneg : 0 ≤ d ^ 2 - d * e + e ^ 2 := by
    nlinarith [sq_nonneg (d - e), sq_nonneg d, sq_nonneg e]
  have hlt : d ^ 2 - d * e + e ^ 2 < r := by
    nlinarith [sq_nonneg (d + e)]
  have hzero : d ^ 2 - d * e + e ^ 2 = 0 := by
    have hm := Int.emod_eq_of_lt hnonneg hlt
    have hz := Int.emod_eq_zero_of_dvd hnorm
    omega
  constructor <;> nlinarith [sq_nonneg (d - e), sq_nonneg d, sq_nonneg e]

/-- The 5-by-5 exponent grid used by a rational function of degree at most
four and its cubic conjugate is injective modulo the Kummer degree. -/
theorem cubic_exponent_grid_injective
    (r u i j i' j' : ℤ) (hr : 48 < r)
    (hu : r ∣ u ^ 2 + u + 1)
    (hi : 0 ≤ i ∧ i ≤ 4) (hj : 0 ≤ j ∧ j ≤ 4)
    (hi' : 0 ≤ i' ∧ i' ≤ 4) (hj' : 0 ≤ j' ∧ j' ≤ 4)
    (hcollision : r ∣ (i + u * j) - (i' + u * j')) :
    i = i' ∧ j = j' := by
  have hcollision' : r ∣ (i - i') + u * (j - j') := by
    convert hcollision using 1; ring
  have h := small_cubic_collision r u (i - i') (j - j') hr hu
    (by omega) (by omega) hcollision'
  omega

/-- Separated coefficient comparison in a tensor basis forces the two
coefficient vectors on one side to be proportional. This is the algebraic
step turning cubic invariance of a bounded rational function into constancy. -/
theorem proportional_of_separated_coefficients
    {K I J : Type*} [Field K]
    (p q : I → K) (p' q' : J → K)
    (h : ∀ i j, p i * q' j = q i * p' j)
    (j₀ : J) (hq : q' j₀ ≠ 0) :
    ∃ a : K, ∀ i, p i = a * q i := by
  refine ⟨p' j₀ / q' j₀, ?_⟩
  intro i
  apply (mul_right_cancel₀ hq)
  calc
    p i * q' j₀ = q i * p' j₀ := h i j₀
    _ = (p' j₀ / q' j₀ * q i) * q' j₀ := by field_simp

end Ogdoad.Excess
