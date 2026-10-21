import Mathlib

/-!
# B1 forcing: finite cores

* `twist_forcing`: the finite-field content of the CM / twist forcing lemma.
  If `x ^ a` is torsion of order dividing `w` and the prime `p` divides
  neither `a` nor `w`, then `x` is a `p`-th power.  In the application
  `a = 2^g - 1` with `h ∤ g` (so a row prime of level `h` does not divide `a`),
  and `x ^ a` is an explicit root of unity.
* `twist_forcing_field`: the same statement for units of a field.
* `dist3`: the distribution relation `∏_{s ∈ μ₃} (1 + t s) = 1 + t³`, valid in
  any commutative ring, which drives Euler-factor forcing and the arm C / arm O
  (r = 5) proportionality relations.
* `kummer_lin_zero_iff`: the linear step `4 Y = (2^j - 1) X` with
  `2^j ≠ 1` in `ZMod p` gives `X = 0 ↔ Y = 0`.
-/

theorem twist_forcing {G : Type*} [Monoid G] (x : G) (a w p : ℕ) (hp : p.Prime)
    (hζ : (x ^ a) ^ w = 1) (hpaw : ¬ p ∣ a * w) : ∃ y : G, y ^ p = x := by
  have hord : orderOf x ∣ a * w := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul]; exact hζ
  have hcop : Nat.Coprime p (orderOf x) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h; exact hpaw (dvd_trans h hord)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact ⟨x ^ m, by rw [← pow_mul, mul_comm, pow_mul]; exact hm⟩

theorem twist_forcing_field {K : Type*} [Field K] (x : Kˣ) (g w p : ℕ) (hp : p.Prime)
    (hζ : (x ^ (2 ^ g - 1)) ^ w = 1) (hpa : ¬ p ∣ 2 ^ g - 1) (hpw : ¬ p ∣ w) :
    ∃ y : Kˣ, y ^ p = x :=
  twist_forcing x (2 ^ g - 1) w p hp hζ (by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · exact hpa h1
    · exact hpw h1)

theorem dist3 {R : Type*} [CommRing R] (t ω : R) (hω : ω ^ 2 + ω + 1 = 0) :
    (1 + t) * (1 + t * ω) * (1 + t * ω ^ 2) = 1 + t ^ 3 := by
  linear_combination (t + t ^ 2 * ω + t ^ 3 * (ω - 1)) * hω

theorem kummer_lin_zero_iff {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (X Y : ZMod p) (j : ℕ)
    (hrel : 4 * Y = (2 ^ j - 1) * X) (hj : (2 : ZMod p) ^ j ≠ 1) : X = 0 ↔ Y = 0 := by
  have h4 : (4 : ZMod p) ≠ 0 := by
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hj' : (2 : ZMod p) ^ j - 1 ≠ 0 := sub_ne_zero.mpr hj
  constructor
  · intro hX; rw [hX, mul_zero] at hrel
    exact (mul_eq_zero.mp hrel).resolve_left h4
  · intro hY; rw [hY, mul_zero] at hrel
    exact (mul_eq_zero.mp hrel.symm).resolve_left hj'
