import Mathlib

/-!
# B2 (arm Z) finite-field core lemmas

* `pow_coprime_is_pth_power`: an element of order prime to `p` is a `p`-th power
  (used for the root-of-unity factor `z1 * t` in Lemma 1.1).
* `two_component_factor`: `z1 * t * (t + t⁻¹) = z1 + z1 * t ^ 2` (Lemma 1.1).
* `pow_geom_of_subfield`: if `x ^ (q - 1) = 1` then `x ^ (1 + q + ... + q^(r-1)) = x ^ r`
  (the norm-degree identity behind Lemma 1.2).
* `pth_power_descent`: the descent of the `p`-th power test in Lemma 1.2.
-/

namespace B2ArmZ

theorem pow_coprime_is_pth_power {G : Type*} [Monoid G] (y : G) {p n : ℕ}
    (hy : y ^ n = 1) (hpn : Nat.Coprime p n) : ∃ x : G, x ^ p = y := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hpn hn
    refine ⟨y ^ u, ?_⟩
    rw [← pow_mul, mul_comm u p, ← Nat.div_add_mod (p * u) n, hu, pow_add, pow_mul, hy,
      one_pow, one_mul, pow_one]
  · interval_cases n
    · -- n = 0: coprime p 0 forces p = 1
      have hp : p = 1 := by simpa using hpn
      exact ⟨y, by simp [hp]⟩
    · exact ⟨1, by simpa using hy.symm⟩

theorem two_component_factor {F : Type*} [Field F] (z1 t : F) (ht : t ≠ 0) :
    z1 * t * (t + t⁻¹) = z1 + z1 * t ^ 2 := by
  field_simp
  ring

theorem pow_geom_of_subfield {G : Type*} [CommMonoid G] (x : G) {q : ℕ} (hq : 1 ≤ q)
    (hx : x ^ (q - 1) = 1) (r : ℕ) :
    x ^ (∑ i ∈ Finset.range r, q ^ i) = x ^ r := by
  have hxq : x ^ q = x := by
    calc x ^ q = x ^ (q - 1 + 1) := by rw [Nat.sub_add_cancel hq]
      _ = x := by rw [pow_succ, hx, one_mul]
  have hxqi : ∀ i : ℕ, x ^ (q ^ i) = x := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, pow_mul, ih, hxq]
  induction r with
  | zero => simp
  | succ r ih => rw [Finset.sum_range_succ, pow_add, ih, hxqi, pow_succ]

/-- Lemma 1.2 core: for `w` with `w ^ p = 1` (`p` prime) and `p ∤ r`, `w ^ r = 1 ↔ w = 1`. -/
theorem pth_power_descent {G : Type*} [Group G] (w : G) {p r : ℕ} (hp : p.Prime)
    (hw : w ^ p = 1) (hr : ¬ p ∣ r) : w ^ r = 1 ↔ w = 1 := by
  constructor
  · intro h
    have hcop : Nat.Coprime r p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hr))
    have h1 : w ^ Nat.gcd r p = 1 := (pow_gcd_eq_one).2 ⟨h, hw⟩
    simpa [Nat.Coprime.gcd_eq_one hcop] using h1
  · rintro rfl; simp

end B2ArmZ
