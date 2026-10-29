import Mathlib

/-!
# The two shared-radicand seed primes

Kernel-checked elementary arithmetic for the structural excess construction.
These are fixed small proof obligations, not a search for excess values.
The identification of the actual Conway components remains a separate input.
-/

namespace Ogdoad.ExcessSeed

theorem prime_37 : Nat.Prime 37 := by norm_num
theorem prime_109 : Nat.Prime 109 := by norm_num

private theorem prime_dvd_36 {p : ℕ} (hp : p.Prime) (hd : p ∣ 36) :
    p = 2 ∨ p = 3 := by
  have h : p ∣ 2 ^ 2 * 3 ^ 2 := by norm_num at hd ⊢; exact hd
  rcases hp.dvd_mul.mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
      (hp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
      (hp.dvd_of_dvd_pow h))

theorem order_two_mod_37 : orderOf (2 : ZMod 37) = 36 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · decide
  · intro p hp hd
    rcases prime_dvd_36 hp hd with rfl | rfl <;> decide

theorem order_two_mod_109 : orderOf (2 : ZMod 109) = 36 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · decide
  · intro p hp hd
    rcases prime_dvd_36 hp hd with rfl | rfl <;> decide

theorem half_power_mod_37 : (2 : ZMod 37) ^ 18 = -1 := by decide
theorem half_power_mod_109 : (2 : ZMod 109) ^ 18 = -1 := by decide

theorem seed_coprime_37 : Nat.Coprime 37 (2 ^ 18 - 1) := by norm_num
theorem seed_coprime_109 : Nat.Coprime 109 (2 ^ 18 - 1) := by norm_num

theorem seed_degree_lcm : Nat.lcm 4 18 = 36 := by norm_num

/-- The common half-field unit-group order. -/
abbrev seedModulus : ℕ := 2 ^ 18 - 1

/-- A common synchronizing exponent for the two fixed seed primes. -/
def seedExponent : ℕ := 18

theorem seedExponent_pos : 0 < seedExponent := by
  norm_num [seedExponent]

theorem synchronized_37 : Nat.ModEq seedModulus (37 ^ seedExponent) 1 := by
  decide

theorem synchronized_109 : Nat.ModEq seedModulus (109 ^ seedExponent) 1 := by
  decide

theorem synchronized_37_mul (t : ℕ) :
    Nat.ModEq seedModulus (37 ^ (seedExponent * t)) 1 := by
  simpa only [pow_mul, one_pow] using synchronized_37.pow t

theorem synchronized_109_mul (t : ℕ) :
    Nat.ModEq seedModulus (109 ^ (seedExponent * t)) 1 := by
  simpa only [pow_mul, one_pow] using synchronized_109.pow t

/-- Exact residue degree 36 excludes a seed prime from every odd multiple
of the degree-18 half-field. -/
theorem coprime_half_period_of_order {p : ℕ} (hp : p.Prime)
    (horder : orderOf (2 : ZMod p) = 36) (n : ℕ) (hn : Odd n) :
    Nat.Coprime p (2 ^ (18 * n) - 1) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hmod : Nat.ModEq p (2 ^ (18 * n)) 1 :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow (18 * n) 2 (by decide))).mpr hd).symm
  have hz : (2 : ZMod p) ^ (18 * n) = 1 := by
    have hcast := (ZMod.natCast_eq_natCast_iff (2 ^ (18 * n)) 1 p).mpr hmod
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast
  have hdiv : 36 ∣ 18 * n := by
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hz
  have htwo : 2 ∣ n :=
    (Nat.mul_dvd_mul_iff_left (by decide : 0 < 18)).mp hdiv
  rcases hn with ⟨k, hk⟩
  rcases htwo with ⟨j, hj⟩
  omega

theorem coprime_half_field_37 (a : ℕ) :
    Nat.Coprime (37 ^ a) (2 ^ (18 * 37 ^ a) - 1) := by
  apply Nat.Coprime.pow_left
  exact coprime_half_period_of_order prime_37 order_two_mod_37 (37 ^ a)
    ((by decide : Odd 37).pow)

theorem coprime_half_field_109 (a : ℕ) :
    Nat.Coprime (109 ^ a) (2 ^ (18 * 109 ^ a) - 1) := by
  apply Nat.Coprime.pow_left
  exact coprime_half_period_of_order prime_109 order_two_mod_109 (109 ^ a)
    ((by decide : Odd 109).pow)

end Ogdoad.ExcessSeed
