import Mathlib

/-!
# Artin--Schreier algebra and orbit minima for mixed cubic excess rows

The algebraic lemmas check the powers of the three quadratic generators used
for the literal finite component 16. The finite permutation records the
semilinear action on its sixteen offsets, and the minimum theorem transfers
power-status invariance to the four possible first failures.

The Conway component selection, finite-field Frobenius specialization, and
identification of ordinal excess with these offsets remain paper-level inputs.
No positive excess in the mixed cubic family is asserted.
-/

namespace Ogdoad.Excess

open scoped CharTwo

section Algebra

variable {K : Type*} [CommRing K] [CharP K 2]

private theorem mixedGap_square_add (a b : K) :
    (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  ring_nf
  simp

private theorem mixedGap_as_square (a b : K) (h : a ^ 2 + a = b) :
    a ^ 2 = a + b := by
  calc
    a ^ 2 = (a ^ 2 + a) + a := by simp
    _ = b + a := by rw [h]
    _ = a + b := add_comm _ _

/-- The first nontrivial Frobenius displacement of the component 16. -/
theorem mixedGap_fourth_power
    (omega b c : K)
    (homega : omega ^ 2 + omega = 1)
    (hb : b ^ 2 + b = omega)
    (hc : c ^ 2 + c = omega * b) :
    c ^ 4 = c + b + 1 := by
  have hw2 := mixedGap_as_square omega 1 homega
  have hb2 := mixedGap_as_square b omega hb
  have hc2 := mixedGap_as_square c (omega * b) hc
  calc
    c ^ 4 = (c ^ 2) ^ 2 := by ring
    _ = (c + omega * b) ^ 2 := by rw [hc2]
    _ = c ^ 2 + omega ^ 2 * b ^ 2 := by
      rw [mixedGap_square_add, mul_pow]
    _ = (c + omega * b) + (omega + 1) * (b + omega) := by
      rw [hc2, hw2, hb2]
    _ = c + b + 1 := by
      ring_nf
      rw [hw2]
      ring_nf
      simp

/-- The fourth Frobenius translates the new quadratic generator by one. -/
theorem mixedGap_sixteenth_power
    (omega b c : K)
    (homega : omega ^ 2 + omega = 1)
    (hb : b ^ 2 + b = omega)
    (hc : c ^ 2 + c = omega * b) :
    c ^ 16 = c + 1 := by
  have hw2 := mixedGap_as_square omega 1 homega
  have hb2 := mixedGap_as_square b omega hb
  have hc4 := mixedGap_fourth_power omega b c homega hb hc
  have hb4 : b ^ 4 = b + 1 := by
    calc
      b ^ 4 = (b ^ 2) ^ 2 := by ring
      _ = (b + omega) ^ 2 := by rw [hb2]
      _ = b ^ 2 + omega ^ 2 := mixedGap_square_add _ _
      _ = b + 1 := by rw [hb2, hw2]; simp [add_assoc]
  calc
    c ^ 16 = ((c ^ 4) ^ 2) ^ 2 := by ring
    _ = ((c + b + 1) ^ 2) ^ 2 := by rw [hc4]
    _ = c ^ 4 + b ^ 4 + 1 := by
      simp only [mixedGap_square_add, one_pow]
      ring
    _ = c + 1 := by rw [hc4, hb4]; ring_nf; simp

/-- The other odd cubic parity gives the displacement by the component 4. -/
theorem mixedGap_sixtyFourth_power
    (omega b c : K)
    (homega : omega ^ 2 + omega = 1)
    (hb : b ^ 2 + b = omega)
    (hc : c ^ 2 + c = omega * b) :
    c ^ 64 = c + b := by
  have hc4 := mixedGap_fourth_power omega b c homega hb hc
  have hc16 := mixedGap_sixteenth_power omega b c homega hb hc
  calc
    c ^ 64 = ((c ^ 16) ^ 2) ^ 2 := by ring
    _ = ((c + 1) ^ 2) ^ 2 := by rw [hc16]
    _ = c ^ 4 + 1 := by
      simp only [mixedGap_square_add, one_pow]
      ring
    _ = c + b := by rw [hc4]; simp [add_assoc]

end Algebra

/-- The offset permutation in binary coordinates `(1, omega, b, omega*b)`.
The Boolean chooses whether the displacement is `b` or `b+1`. -/
def mixedGapTransform (e : Bool) (m : Fin 16) : Fin 16 :=
  ⟨Nat.xor (if e then 5 else 4)
      (Nat.xor m.val (Nat.xor (m.val / 4 % 2) (2 * (m.val / 8 % 2)))), by
    fin_cases m <;> cases e <;> decide⟩

/-- Evaluate the binary offset in the indicated four-element basis. -/
def mixedGapOffset {K : Type*} [CommRing K] (omega b : K) (m : Fin 16) : K :=
  (↑(m.val % 2) : K) + (↑(m.val / 2 % 2) : K) * omega +
    (↑(m.val / 4 % 2) : K) * b + (↑(m.val / 8 % 2) : K) * (omega * b)

/-- The bit permutation is the actual affine action of a ring map fixing
`omega` and translating `b` by one. -/
theorem mixedGap_offset_action
    {K : Type*} [CommRing K] [CharP K 2]
    (sigma : K →+* K) (omega b : K)
    (homega : sigma omega = omega) (hb : sigma b = b + 1)
    (e : Bool) (m : Fin 16) :
    b + (if e then 1 else 0) + sigma (mixedGapOffset omega b m) =
      mixedGapOffset omega b (mixedGapTransform e m) := by
  fin_cases m <;> cases e <;>
    norm_num [mixedGapOffset, mixedGapTransform, homega, hb] <;>
    ring_nf <;> simp <;> ring

/-- The semilinear displacement of the finite component transfers the
literal translated expression to the corresponding binary offset. -/
theorem mixedGap_translate_action
    {K : Type*} [CommRing K] [CharP K 2]
    (sigma : K →+* K) (omega b c z : K) (e : Bool)
    (homega : sigma omega = omega) (hb : sigma b = b + 1)
    (hc : sigma c = c + b + (if e then 1 else 0))
    (hz : sigma z = z) (m : Fin 16) :
    sigma (z + c + mixedGapOffset omega b m) =
      z + c + mixedGapOffset omega b (mixedGapTransform e m) := by
  rw [map_add, map_add, hz, hc]
  have h := mixedGap_offset_action sigma omega b homega hb e m
  rw [← h]
  ring

/-- The four orbit representatives, in increasing ordinal-offset order. -/
def mixedGapOrbitMin (m : Fin 16) : Fin 16 :=
  if m ∈ ({0, 1, 4, 5} : Finset (Fin 16)) then 0
  else if m ∈ ({2, 3, 6, 7} : Finset (Fin 16)) then 2
  else if m ∈ ({8, 9, 14, 15} : Finset (Fin 16)) then 8
  else 10

/-- Squaring the affine action changes just the lowest offset bit. -/
theorem mixedGap_transform_square :
    ∀ (e : Bool) (m : Fin 16),
      ((mixedGapTransform e)^[2] m).val = Nat.xor m.val 1 := by
  decide

/-- Both parity choices give an action of order four on the offsets. -/
theorem mixedGap_transform_fourth :
    ∀ (e : Bool) (m : Fin 16), (mixedGapTransform e)^[4] m = m := by
  decide

/-- Every offset is reached from its stated representative in fewer than
four steps, for either parity of the cubic degree. -/
theorem mixedGap_orbit_cover :
    ∀ (e : Bool) (m : Fin 16),
      ∃ n : Fin 4, (mixedGapTransform e)^[n.val] (mixedGapOrbitMin m) = m := by
  decide

/-- The representatives really are minima and have exactly four values. -/
theorem mixedGap_orbit_minimum :
    ∀ m : Fin 16,
      (mixedGapOrbitMin m).val ≤ m.val ∧
        ((mixedGapOrbitMin m).val = 0 ∨ (mixedGapOrbitMin m).val = 2 ∨
          (mixedGapOrbitMin m).val = 8 ∨ (mixedGapOrbitMin m).val = 10) := by
  decide

private theorem mixedGap_property_iterate
    {A : Type*} (T : A → A) (P : A → Prop)
    (hinv : ∀ a, P (T a) ↔ P a) (n : ℕ) (a : A) :
    P ((T^[n]) a) ↔ P a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', hinv, ih]

/-- An invariant property is constant on each of the four displayed orbits. -/
theorem mixedGap_property_at_orbit_min
    (P : Fin 16 → Prop) (e : Bool)
    (hinv : ∀ m, P (mixedGapTransform e m) ↔ P m) (m : Fin 16) :
    P m ↔ P (mixedGapOrbitMin m) := by
  obtain ⟨n, hn⟩ := mixedGap_orbit_cover e m
  have h := mixedGap_property_iterate (mixedGapTransform e) P hinv n.val
    (mixedGapOrbitMin m)
  simpa only [hn] using h

/-- If zero is a power, offsets one, four, and five are powers as well. -/
theorem mixedGap_zero_power_propagates
    (P : Fin 16 → Prop) (e : Bool)
    (hinv : ∀ m, P (mixedGapTransform e m) ↔ P m)
    (hzero : P 0) : P 1 ∧ P 4 ∧ P 5 := by
  have h1 := mixedGap_property_at_orbit_min P e hinv 1
  have h4 := mixedGap_property_at_orbit_min P e hinv 4
  have h5 := mixedGap_property_at_orbit_min P e hinv 5
  norm_num [mixedGapOrbitMin] at h1 h4 h5
  exact ⟨h1.mpr hzero, h4.mpr hzero, h5.mpr hzero⟩

/-- The least offset without an invariant property is an orbit minimum,
or lies beyond the sixteen-offset palette. -/
theorem mixedGap_first_failure
    (P : ℕ → Prop) (e : Bool)
    (hinv : ∀ m : Fin 16, P (mixedGapTransform e m).val ↔ P m.val)
    (m : ℕ) (hfail : ¬ P m) (hbefore : ∀ j < m, P j) :
    m = 0 ∨ m = 2 ∨ m = 8 ∨ m = 10 ∨ 16 ≤ m := by
  by_cases hsmall : m < 16
  · let a : Fin 16 := ⟨m, hsmall⟩
    have hmin := mixedGap_orbit_minimum a
    have hprop := mixedGap_property_at_orbit_min (fun j => P j.val) e hinv a
    have hminfail : ¬ P (mixedGapOrbitMin a).val := by
      intro hp
      exact hfail (hprop.mpr hp)
    have heq : (mixedGapOrbitMin a).val = m := by
      have hle : (mixedGapOrbitMin a).val ≤ m := hmin.1
      by_contra hne
      have hlt : (mixedGapOrbitMin a).val < m := lt_of_le_of_ne hle hne
      exact hminfail (hbefore _ hlt)
    rcases hmin.2 with h | h | h | h
    · exact Or.inl (heq.symm.trans h)
    · exact Or.inr (Or.inl (heq.symm.trans h))
    · exact Or.inr (Or.inr (Or.inl (heq.symm.trans h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (heq.symm.trans h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Nat.le_of_not_gt hsmall))))

end Ogdoad.Excess
