import Ogdoad.ExcessSeed

/-!
# Primitive row primes for the shared-radicand construction

For every positive `a`, every prime divisor of the cyclotomic value at
`36 * 37^a * 109^a` has that exact residue degree. A prime divisor exists
because the cyclotomic value has absolute value greater than one. This
avoids any use of an external primitive-divisor theorem.
-/

namespace Ogdoad.ExcessPrimitive

open Polynomial
open Ogdoad.ExcessSeed

private theorem two_square_mod_three : (2 : ZMod 3) ^ 2 = 1 := by decide

def obstructionDegree (a : ℕ) : ℕ := 36 * 37 ^ a * 109 ^ a

theorem obstructionDegree_gt_one (a : ℕ) : 1 < obstructionDegree a := by
  have hR := Nat.one_le_pow a 37 (by decide)
  have hS := Nat.one_le_pow a 109 (by decide)
  unfold obstructionDegree
  nlinarith

private theorem prime_dvd_obstructionDegree {a p : ℕ}
    (hp : p.Prime) (hd : p ∣ obstructionDegree a) :
    p = 2 ∨ p = 3 ∨ p = 37 ∨ p = 109 := by
  unfold obstructionDegree at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · have h36 : p ∣ 2 ^ 2 * 3 ^ 2 := by norm_num at hd ⊢; exact hd
      rcases hp.dvd_mul.mp h36 with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
          (hp.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
          (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp prime_37).mp (hp.dvd_of_dvd_pow hd))))
  · exact Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hp prime_109).mp (hp.dvd_of_dvd_pow hd))))

private theorem cyclotomic_root_not_dvd_degree (a : ℕ) (ha : 0 < a)
    (p : ℕ) (hp : p.Prime)
    (hroot : (cyclotomic (obstructionDegree a) (ZMod p)).IsRoot 2) :
    ¬p ∣ obstructionDegree a := by
  letI : Fact p.Prime := ⟨hp⟩
  intro hd
  rcases prime_dvd_obstructionDegree hp hd with rfl | rfl | rfl | rfl
  · have hc := coprime_of_root_cyclotomic (by
      have := obstructionDegree_gt_one a
      omega) hroot
    norm_num at hc
  · let m := 4 * 37 ^ a * 109 ^ a
    have hcop : Nat.Coprime 3 m :=
      (((by norm_num : Nat.Coprime 3 4).mul_right
        ((by norm_num : Nat.Coprime 3 37).pow_right a)).mul_right
        ((by norm_num : Nat.Coprime 3 109).pow_right a))
    letI : NeZero (m : ZMod 3) :=
      NeZero.of_not_dvd (ZMod 3) (hp.coprime_iff_not_dvd.mp hcop)
    have hn : obstructionDegree a = 3 ^ 2 * m := by
      dsimp [obstructionDegree, m]
      ring
    rw [hn] at hroot
    have hprim : IsPrimitiveRoot (2 : ZMod 3) m :=
      isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hroot
    have hdiv : m ∣ 2 := hprim.dvd_of_pow_eq_one 2 two_square_mod_three
    have hle : m ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    have hR := Nat.one_le_pow a 37 (by decide)
    have hS := Nat.one_le_pow a 109 (by decide)
    dsimp [m] at hle
    nlinarith
  · let m := 36 * 109 ^ a
    have hcop : Nat.Coprime 37 m :=
      (by norm_num : Nat.Coprime 37 36).mul_right
        ((by norm_num : Nat.Coprime 37 109).pow_right a)
    letI : NeZero (m : ZMod 37) :=
      NeZero.of_not_dvd (ZMod 37) (hp.coprime_iff_not_dvd.mp hcop)
    have hn : obstructionDegree a = 37 ^ a * m := by
      dsimp [obstructionDegree, m]
      ring
    rw [hn] at hroot
    have hprim : IsPrimitiveRoot (2 : ZMod 37) m :=
      isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hroot
    have hm : m = 36 := hprim.eq_orderOf.trans order_two_mod_37
    have hpow : 1 < 109 ^ a := one_lt_pow₀ (by decide) ha.ne'
    dsimp [m] at hm
    nlinarith
  · let m := 36 * 37 ^ a
    have hcop : Nat.Coprime 109 m :=
      (by norm_num : Nat.Coprime 109 36).mul_right
        ((by norm_num : Nat.Coprime 109 37).pow_right a)
    letI : NeZero (m : ZMod 109) :=
      NeZero.of_not_dvd (ZMod 109) (hp.coprime_iff_not_dvd.mp hcop)
    have hn : obstructionDegree a = 109 ^ a * m := by
      dsimp [obstructionDegree, m]
      ring
    rw [hn] at hroot
    have hprim : IsPrimitiveRoot (2 : ZMod 109) m :=
      isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hroot
    have hm : m = 36 := hprim.eq_orderOf.trans order_two_mod_109
    have hpow : 1 < 37 ^ a := one_lt_pow₀ (by decide) ha.ne'
    dsimp [m] at hm
    nlinarith

/-- Every prime at which the cyclotomic polynomial vanishes has the exact
obstruction degree as its binary multiplicative order. -/
theorem order_of_cyclotomic_root (a : ℕ) (ha : 0 < a)
    (p : ℕ) (hp : p.Prime)
    (hroot : (cyclotomic (obstructionDegree a) (ZMod p)).IsRoot 2) :
    orderOf (2 : ZMod p) = obstructionDegree a := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnot := cyclotomic_root_not_dvd_degree a ha p hp hroot
  letI : NeZero (obstructionDegree a : ZMod p) :=
    NeZero.of_not_dvd (ZMod p) hnot
  exact (isRoot_cyclotomic_iff.mp hroot).eq_orderOf.symm

/-- A row prime exists at every positive-level obstruction degree. -/
theorem exists_primitive_row_prime (a : ℕ) (ha : 0 < a) :
    ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = obstructionDegree a := by
  let n := obstructionDegree a
  let c := ((cyclotomic n ℤ).eval 2).natAbs
  have hc : 1 < c := by
    have := sub_one_lt_natAbs_cyclotomic_eval (obstructionDegree_gt_one a)
      (by decide : (2 : ℕ) ≠ 1)
    simpa [c, n] using this
  let p := c.minFac
  have hp : p.Prime := Nat.minFac_prime (ne_of_gt hc)
  letI : Fact p.Prime := ⟨hp⟩
  have hroot : (cyclotomic n (ZMod p)).IsRoot 2 := by
    rw [IsRoot.def, ← map_cyclotomic_int n (ZMod p), eval_map]
    have hcast : (Int.castRingHom (ZMod p)) ((cyclotomic n ℤ).eval 2) = 0 := by
      rw [Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
      apply Int.dvd_natAbs.1
      exact_mod_cast Nat.minFac_dvd c
    simpa [eval₂_hom] using hcast
  exact ⟨p, hp, order_of_cyclotomic_root a ha p hp hroot⟩

end Ogdoad.ExcessPrimitive
