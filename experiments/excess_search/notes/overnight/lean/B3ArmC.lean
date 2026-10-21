import Mathlib

/-!
# B3 (arm C): small finite-field / arithmetic lemmas

* `singer_relation`: if `y ≠ 0` has relative trace zero
  (`y + y^q + y^(q^2) = 0`, `q = p + 1`) in characteristic two, then
  `η = y^(q-1)` satisfies `η^(q+1) = η + 1`.  Applied to `y = γ_k`,
  `q = 2^(3^(k-1))`, this is the Singer-line relation `η_k + 1 = η_k^(q+1)`.
* `frob_eq_mobius`: under the same relation, `η^q = 1 + η⁻¹`.
* `mobius_order_three`: `M x = 1 + x⁻¹` has order three away from `0, 1`
  in characteristic two.
* `cyclotomic_product_step`: `w⁻¹ (1 + w)^2 = w + w⁻¹` in characteristic two
  (last step of the coset-product identity `Π(ζ) = (ζ^r + ζ^(-r))^(1 - q/2)`).
* `digit_lemma`: bit `i` of `(2^h - 1)/l` is `⌊2 (2^(h-1-i) mod l) / l⌋`.
-/

theorem singer_relation {F : Type*} [Field F] [CharP F 2] (y : F) (hy : y ≠ 0) (p : ℕ)
    (htr : y + y ^ (p + 1) + y ^ ((p + 1) ^ 2) = 0) :
    (y ^ p) ^ (p + 2) = y ^ p + 1 := by
  have e1 : y * (y ^ p) ^ (p + 2) = y ^ ((p + 1) ^ 2) := by
    rw [← pow_mul, ← pow_succ']
    congr 1
    ring
  have e2 : y ^ ((p + 1) ^ 2) = y + y ^ (p + 1) := by
    rw [eq_neg_of_add_eq_zero_right htr, CharTwo.neg_eq]
  have key : y * (y ^ p) ^ (p + 2) = y * (y ^ p + 1) := by
    rw [e1, e2]
    ring
  exact mul_left_cancel₀ hy key

theorem frob_eq_mobius {F : Type*} [Field F] (η : F) (hη : η ≠ 0) (p : ℕ)
    (h : η ^ (p + 2) = η + 1) : η ^ (p + 1) = 1 + η⁻¹ := by
  have : η ^ (p + 2) = η ^ (p + 1) * η := pow_succ η (p + 1)
  rw [this] at h
  field_simp
  linear_combination h

theorem mobius_order_three {F : Type*} [Field F] [CharP F 2] (x : F) (h0 : x ≠ 0)
    (h1 : x + 1 ≠ 0) :
    1 + (1 + (1 + x⁻¹)⁻¹)⁻¹ = x := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hA : 1 + x⁻¹ = (x + 1) / x := by field_simp
  have hA0 : (x + 1) / x ≠ 0 := div_ne_zero h1 h0
  have hB : 1 + ((x + 1) / x)⁻¹ = (2 * x + 1) / (x + 1) := by field_simp; ring
  rw [hA, hB, h2, zero_mul, zero_add]
  field_simp
  linear_combination h2

theorem cyclotomic_product_step {F : Type*} [Field F] [CharP F 2] (w : F) (hw : w ≠ 0) :
    w⁻¹ * (1 + w) ^ 2 = w + w⁻¹ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  field_simp
  linear_combination (w) * h2

theorem digit_lemma (h l i : ℕ) (hl : 1 < l) (hodd : ¬ 2 ∣ l) (hi : i < h) :
    (2 ^ h - 1) / l / 2 ^ i % 2 = 2 * (2 ^ (h - 1 - i) % l) / l := by
  have hlpos : 0 < l := by omega
  -- l does not divide any power of two
  have hnd : ∀ j : ℕ, ¬ l ∣ 2 ^ j := by
    intro j hj
    have hcop : Nat.Coprime l 2 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_two).mpr hodd))
    have : l ∣ 1 := (Nat.Coprime.pow_right j hcop).dvd_of_dvd_mul_left
      (by simpa using hj)
    have := Nat.le_of_dvd Nat.one_pos this
    omega
  obtain ⟨t, rfl⟩ : ∃ t, h = i + 1 + t := ⟨h - i - 1, by omega⟩
  have hsplit : 2 ^ (i + 1 + t) = 2 ^ i * 2 ^ (t + 1) := by
    rw [← pow_add]; congr 1; omega
  have hsub : i + 1 + t - 1 - i = t := by omega
  rw [hsub, Nat.div_div_eq_div_mul, hsplit]
  -- write 2^(t+1) = l * Q + R with 0 < R < l
  set Q := 2 ^ (t + 1) / l with hQ
  set R := 2 ^ (t + 1) % l with hR
  have hRpos : 0 < R := by
    rcases Nat.eq_zero_or_pos R with h0 | h0
    · exact absurd (Nat.dvd_of_mod_eq_zero h0) (hnd _)
    · exact h0
  have hRlt : R < l := Nat.mod_lt _ hlpos
  have hdecomp : 2 ^ (t + 1) = l * Q + R := (Nat.div_add_mod _ _).symm
  have h2i : 0 < 2 ^ i := by positivity
  have hR1 : 1 ≤ 2 ^ i * R := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hle : 1 ≤ 2 ^ i * (l * Q + R) :=
    le_trans hR1 (Nat.mul_le_mul_left _ (Nat.le_add_left R (l * Q)))
  have hq1 : (2 ^ i * 2 ^ (t + 1) - 1) / (l * 2 ^ i) = Q := by
    rw [hdecomp]
    apply Nat.div_eq_of_lt_le
    · rw [Nat.le_sub_iff_add_le hle]
      nlinarith
    · have hRl : 2 ^ i * R ≤ 2 ^ i * l := Nat.mul_le_mul_left _ hRlt.le
      calc 2 ^ i * (l * Q + R) - 1 < 2 ^ i * (l * Q + R) := Nat.sub_lt (by omega) Nat.one_pos
        _ ≤ (Q + 1) * (l * 2 ^ i) := by nlinarith
  rw [hq1]
  -- now Q % 2 = 2 * (2^t % l) / l, using 2^(t+1) = 2 * 2^t
  set Q' := 2 ^ t / l
  set R' := 2 ^ t % l
  have hd' : 2 ^ t = l * Q' + R' := (Nat.div_add_mod _ _).symm
  have hR'lt : R' < l := Nat.mod_lt _ hlpos
  have hQeq : Q = 2 * Q' + 2 * R' / l := by
    rw [hQ, pow_succ, hd']
    have : (l * Q' + R') * 2 = 2 * R' + l * (2 * Q') := by ring
    rw [this, Nat.add_mul_div_left _ _ hlpos]
    ring
  have hb : 2 * R' / l < 2 := by
    apply Nat.div_lt_of_lt_mul; omega
  rw [hQeq]
  generalize 2 * R' / l = B at hb ⊢
  omega
