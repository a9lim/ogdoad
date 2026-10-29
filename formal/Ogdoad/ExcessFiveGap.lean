import Mathlib

/-!
# Orbit algebra for the five-power excess gap

These lemmas check the rational transformation and character-orbit mechanism
used in the paper's `m = 1` or `m ≥ 16` theorem. The identification of the
literal Conway tower, its finite-field arithmetic, and the five/ten cycle
decomposition remain paper-level arguments. No universal nonvanishing of the
remaining character amplitude is asserted.
-/

namespace Ogdoad.Excess

/-- The semilinear inversion acting on the fifteen nonzero constants. -/
def fiveGapTransform {K : Type*} [Field K] (lam c : K) : K := lam / c ^ 4

/-- Twice applying semilinear inversion becomes an order-five scaling when
the constants lie in the field of sixteen elements. -/
theorem fiveGapTransform_twice
    {K : Type*} [Field K] (lam c : K)
    (hlam : lam ≠ 0) (hc : c ≠ 0) (hc16 : c ^ 16 = c) :
    fiveGapTransform lam (fiveGapTransform lam c) = c / lam ^ 3 := by
  have hcalc : fiveGapTransform lam (fiveGapTransform lam c) = c ^ 16 / lam ^ 3 := by
    dsimp [fiveGapTransform]
    field_simp
  rw [hcalc, hc16]

/-- The prefactor in the character transfer is a product of the old tower
element and finite constants, whose fresh-prime characters are trivial. -/
theorem fiveGap_character_factorization
    {K : Type*} [Field K] (x c lam : K)
    (hx : x ≠ 0) (hc : c ≠ 0) :
    lam / x + c ^ 4 = (c ^ 4 / x) * (x + fiveGapTransform lam c) := by
  dsimp [fiveGapTransform]
  field_simp
  ring

/-- An eigencharacter accumulates the corresponding power under iteration. -/
theorem orbit_eigen_iterate
    {A K : Type*} [CommRing K] (T : A → A) (f : A → K) (q : K)
    (heigen : ∀ c, f (T c) = q * f c) (n : ℕ) (c : A) :
    f ((T^[n]) c) = q ^ n * f c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', heigen, ih, pow_succ]
    ring

/-- A five-cycle is forced to have zero additive character when the
Frobenius multiplier has fifth power minus one and two is invertible. -/
theorem five_cycle_eigen_zero
    {A K : Type*} [Field K] (T : A → A) (f : A → K) (q : K)
    (heigen : ∀ c, f (T c) = q * f c)
    (hq : q ^ 5 = -1) (htwo : (2 : K) ≠ 0)
    (c : A) (hcycle : (T^[5]) c = c) : f c = 0 := by
  have h := orbit_eigen_iterate T f q heigen 5 c
  rw [hcycle, hq] at h
  have hzero : (2 : K) * f c = 0 := by linear_combination h
  exact (mul_eq_zero.mp hzero).resolve_left htwo

/-- Vanishing at the marked point propagates to every point in its orbit. -/
theorem eigen_zero_on_marked_orbit
    {A K : Type*} [CommRing K] (T : A → A) (f : A → K) (q : K)
    (heigen : ∀ c, f (T c) = q * f c)
    (c : A) (hc : f c = 0) (n : ℕ) : f ((T^[n]) c) = 0 := by
  rw [orbit_eigen_iterate T f q heigen n c, hc, mul_zero]

/-- If every point belongs either to a five-cycle or to the marked orbit,
the marked amplitude is the only possible nonzero character parameter. -/
theorem five_gap_orbit_amplitude_dichotomy
    {A K : Type*} [Field K] (T : A → A) (f : A → K) (q : K)
    (heigen : ∀ c, f (T c) = q * f c)
    (hq : q ^ 5 = -1) (htwo : (2 : K) ≠ 0)
    (marked : A)
    (hcover : ∀ c, (T^[5]) c = c ∨ ∃ n, c = (T^[n]) marked) :
    f marked ≠ 0 ∨ ∀ c, f c = 0 := by
  by_cases hmarked : f marked = 0
  · right
    intro c
    rcases hcover c with hcycle | ⟨n, rfl⟩
    · exact five_cycle_eigen_zero T f q heigen hq htwo c hcycle
    · exact eigen_zero_on_marked_orbit T f q heigen marked hmarked n
  · exact Or.inl hmarked

end Ogdoad.Excess
