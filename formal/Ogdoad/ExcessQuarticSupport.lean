import Mathlib

/-!
# Bounded quartic cyclotomic support

The sparse-support arithmetic used in the synchronized-family Suzuki-factor
argument. A coefficient vector bounded by 48 cannot vanish at a square root
of -1 and a primitive cube root modulo N when N exceeds 192^4. The norm is
handled by an explicit integral quartic polynomial, with its zero criterion
proved using nonsquareness of 3 over the rationals.

This module does not formalize the finite-field rational functions, divisor
argument, literal Conway components, or the primitive-support interpretation.
-/

namespace Ogdoad.ExcessQuarticSupport

def quarticNorm {F : Type*} [CommRing F] (a b c d : F) : F :=
  let U := a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2
  let V := 2 * a * c + 2 * b * d - c ^ 2 - d ^ 2
  U ^ 2 - U * V + V ^ 2

theorem quarticNorm_rat_eq_zero_iff (a b c d : ℚ) :
    quarticNorm a b c d = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro hn
    let U := a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2
    let V := 2 * a * c + 2 * b * d - c ^ 2 - d ^ 2
    change U ^ 2 - U * V + V ^ 2 = 0 at hn
    have hu : U = 0 := by
      nlinarith [sq_nonneg U, sq_nonneg V, sq_nonneg (U - V)]
    have hv : V = 0 := by nlinarith [sq_nonneg V]
    let n := c ^ 2 + d ^ 2
    have hdet : (2 * (a * d - b * c)) ^ 2 = 3 * n ^ 2 := by
      dsimp [U] at hu
      dsimp [V] at hv
      dsimp [n]
      linear_combination 4 * (c ^ 2 + d ^ 2) * hu -
        (2 * a * c + 2 * b * d + c ^ 2 + d ^ 2) * hv
    have hn0 : n = 0 := by
      by_contra hne
      have hsquare : IsSquare (3 : ℚ) := by
        refine ⟨2 * (a * d - b * c) / n, ?_⟩
        field_simp
        nlinarith [hdet]
      norm_num at hsquare
    have hc : c = 0 := by dsimp [n] at hn0; nlinarith [sq_nonneg c, sq_nonneg d]
    have hd : d = 0 := by dsimp [n] at hn0; nlinarith [sq_nonneg d]
    dsimp [U] at hu
    have ha : a = 0 := by rw [hc, hd] at hu; nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by rw [hc, hd] at hu; nlinarith [sq_nonneg b]
    exact ⟨ha, hb, hc, hd⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    norm_num [quarticNorm]

theorem quarticNorm_int_eq_zero_iff (a b c d : ℤ) :
    quarticNorm a b c d = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    have hq : quarticNorm (a : ℚ) b c d = 0 := by
      dsimp [quarticNorm] at h ⊢
      exact_mod_cast h
    obtain ⟨ha, hb, hc, hd⟩ := (quarticNorm_rat_eq_zero_iff _ _ _ _).mp hq
    exact_mod_cast (show (a : ℚ) = 0 ∧ (b : ℚ) = 0 ∧ (c : ℚ) = 0 ∧ (d : ℚ) = 0 from
      ⟨ha, hb, hc, hd⟩)
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    norm_num [quarticNorm]

theorem quarticNorm_vanishes_of_relation {F : Type*} [CommRing F]
    (a b c d q s : F)
    (hq : q ^ 2 + 1 = 0) (hs : s ^ 2 + s + 1 = 0)
    (h : a + b * q + c * s + d * q * s = 0) :
    quarticNorm a b c d = 0 := by
  let U := a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2
  let V := 2 * a * c + 2 * b * d - c ^ 2 - d ^ 2
  have hpair : U + V * s = 0 := by
    dsimp [U, V]
    linear_combination (a - b * q + c * s - d * q * s) * h +
      (b + d * s) ^ 2 * hq - (c ^ 2 + d ^ 2) * hs
  have hs3 : s ^ 3 - 1 = 0 := by linear_combination (s - 1) * hs
  change U ^ 2 - U * V + V ^ 2 = 0
  linear_combination (U + V * s ^ 2) * hpair - U * V * hs - V ^ 2 * hs3

private theorem int_sq_le_of_abs_le {x B : ℤ} (h : |x| ≤ B) : x ^ 2 ≤ B ^ 2 := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  nlinarith [mul_nonneg (show 0 ≤ B - x by omega) (show 0 ≤ B + x by omega)]

theorem quarticNorm_abs_le_of_coefficients_le
    (a b c d : ℤ) (ha : |a| ≤ 48) (hb : |b| ≤ 48)
    (hc : |c| ≤ 48) (hd : |d| ≤ 48) :
    |quarticNorm a b c d| ≤ 192 ^ 4 := by
  have ha2 := int_sq_le_of_abs_le ha
  have hb2 := int_sq_le_of_abs_le hb
  have hc2 := int_sq_le_of_abs_le hc
  have hd2 := int_sq_le_of_abs_le hd
  let U := a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2
  let V := 2 * a * c + 2 * b * d - c ^ 2 - d ^ 2
  have hu : |U| ≤ 4608 := by
    apply abs_le.mpr
    dsimp [U]
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hv : |V| ≤ 13824 := by
    apply abs_le.mpr
    dsimp [V]
    constructor <;> nlinarith [sq_nonneg (a + c), sq_nonneg (a - c),
      sq_nonneg (b + d), sq_nonneg (b - d), sq_nonneg c, sq_nonneg d]
  have hu2 := int_sq_le_of_abs_le hu
  have hv2 := int_sq_le_of_abs_le hv
  have huv : |U * V| ≤ 4608 * 13824 := by
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg V) (by norm_num)
  change |U ^ 2 - U * V + V ^ 2| ≤ 192 ^ 4
  apply abs_le.mpr
  obtain ⟨huvl, huvu⟩ := abs_le.mp huv
  constructor
  · nlinarith [sq_nonneg U, sq_nonneg V, sq_nonneg (U - V)]
  · nlinarith

/-- A bounded linear relation in the quartic cyclotomic basis cannot vanish
modulo an integer larger than the norm bound. Positivity/nonvanishing of the
integer norm is proved internally; it is not an assumption. -/
theorem bounded_quartic_relation
    (N : ℕ) (hN : 192 ^ 4 < N) (q s : ZMod N)
    (hq : q ^ 2 + 1 = 0) (hs : s ^ 2 + s + 1 = 0)
    (a b c d : ℤ) (ha : |a| ≤ 48) (hb : |b| ≤ 48)
    (hc : |c| ≤ 48) (hd : |d| ≤ 48)
    (h : (a : ZMod N) + b * q + c * s + d * q * s = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hz := quarticNorm_vanishes_of_relation (a : ZMod N) b c d q s hq hs h
  have hcast : ((quarticNorm a b c d : ℤ) : ZMod N) = 0 := by
    simpa only [quarticNorm, Int.cast_sub, Int.cast_add, Int.cast_pow,
      Int.cast_mul, Int.cast_ofNat] using hz
  have hdiv : (N : ℤ) ∣ quarticNorm a b c d :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  have hbound := quarticNorm_abs_le_of_coefficients_le a b c d ha hb hc hd
  have hlarge : (192 : ℤ) ^ 4 < N := by exact_mod_cast hN
  exact (quarticNorm_int_eq_zero_iff a b c d).mp
    (Int.eq_zero_of_abs_lt_dvd hdiv (lt_of_le_of_lt hbound hlarge))

end Ogdoad.ExcessQuarticSupport
