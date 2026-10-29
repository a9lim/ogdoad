import Mathlib

/-!
# Additive separation of odd Kummer components

The lemmas here check the algebraic degree argument used for a sum of two
Kummer components. They do not construct the Conway components or prove the
component-set recursion.
-/

namespace Ogdoad.Excess

open Polynomial

/-- A nonzero coefficient-field translation cannot take a root of an
irreducible binomial of degree greater than one to another binomial root of
the same degree, when that degree is nonzero in the coefficient field. -/
theorem translation_eq_zero_of_binomial_minpoly
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : L) (a b v : K) (n : ℕ) (hn : 1 < n)
    (hncast : (n : K) ≠ 0)
    (hmin : minpoly K x = X ^ n - C a)
    (htranslate : (x + algebraMap K L v) ^ n = algebraMap K L b) :
    v = 0 := by
  let P : K[X] := (X + C v) ^ n - C b
  have hPmonic : P.Monic := by
    have h := (monic_X_pow_sub_C b (by omega : n ≠ 0)).comp (monic_X_add_C v)
    simpa [P, Polynomial.sub_comp, Polynomial.pow_comp] using h
  have hroot : aeval x P = 0 := by
    simp [P, htranslate]
  have hdeg : P.natDegree ≤ (minpoly K x).natDegree := by
    simp [P, hmin, natDegree_pow]
  have heq : P = X ^ n - C a := by
    rw [← hmin]
    exact eq_of_monic_of_dvd_of_natDegree_le
      (by rw [hmin]; exact monic_X_pow_sub_C a (by omega))
      hPmonic (minpoly.dvd K x hroot) hdeg
  have hc := congrArg (fun Q : K[X] => Q.coeff (n - 1)) heq
  have hnm : n - 1 ≠ 0 := by omega
  have hlt : n - 1 ≠ n := by omega
  have hsub : n - (n - 1) = 1 := by omega
  have hchoose : n.choose (n - 1) = n := by
    rw [Nat.choose_symm (by omega : 1 ≤ n), Nat.choose_one_right]
  simp only [P, coeff_sub, coeff_X_add_C_pow, hsub, pow_one,
    hchoose, coeff_C, hnm, if_false, sub_zero, coeff_X_pow,
    hlt] at hc
  exact (mul_eq_zero.mp hc).resolve_right hncast

/-- Characteristic-two odd Kummer degrees satisfy the nonzero-degree
hypothesis in the preceding translation theorem. -/
theorem translation_eq_zero_of_odd_binomial_minpoly
    {K L : Type*} [Field K] [Field L] [Algebra K L] [CharP K 2]
    (x : L) (a b v : K) (n : ℕ) (hn : 1 < n) (hodd : Odd n)
    (hmin : minpoly K x = X ^ n - C a)
    (htranslate : (x + algebraMap K L v) ^ n = algebraMap K L b) :
    v = 0 := by
  apply translation_eq_zero_of_binomial_minpoly x a b v n hn _ hmin htranslate
  have hncast : (n : K) = 1 :=
    natCast_eq_one_of_odd_of_two_eq_zero hodd (by simpa using CharP.cast_eq_zero K 2)
  rw [hncast]
  exact one_ne_zero

/-- If two component fields intersect in `K`, a fixed sum gives a
coefficient-field translation of either component. An irreducible binomial
of invertible degree rules out that translation, so both components are
fixed separately. The endomorphism need not fix `K` pointwise. -/
theorem fixed_sum_iff_fixed_components_of_binomial_minpoly
    {L : Type*} [Field L] (K S T : Subfield L)
    (hinter : S ⊓ T = K) (σ : L →+* L) (x y : L)
    (hxS : x ∈ S) (hyT : y ∈ T)
    (hsxS : σ x ∈ S) (hsyT : σ y ∈ T)
    (a b : K) (n : ℕ) (hn : 1 < n) (hncast : (n : K) ≠ 0)
    (hmin : minpoly K x = X ^ n - C a)
    (hpower : (σ x) ^ n = (b : L)) :
    σ (x + y) = x + y ↔ σ x = x ∧ σ y = y := by
  constructor
  · intro hsum
    have hdisplace : σ x - x = y - σ y := by
      have hsum' : σ x + σ y = x + y := by simpa using hsum
      linear_combination hsum'
    have hmem : σ x - x ∈ K := by
      rw [← hinter]
      exact ⟨S.sub_mem hsxS hxS, hdisplace ▸ T.sub_mem hyT hsyT⟩
    let v : K := ⟨σ x - x, hmem⟩
    have htranslate : (x + algebraMap K L v) ^ n = algebraMap K L b := by
      change (x + (σ x - x)) ^ n = (b : L)
      have heq : x + (σ x - x) = σ x := by ring
      rw [heq]
      exact hpower
    have hv : v = 0 :=
      translation_eq_zero_of_binomial_minpoly x a b v n hn hncast hmin htranslate
    have hfixed : σ x = x := by
      have hv' : σ x - x = 0 := congrArg (fun z : K => (z : L)) hv
      exact sub_eq_zero.mp hv'
    refine ⟨hfixed, ?_⟩
    have hsum' : σ x + σ y = x + y := by simpa using hsum
    rw [hfixed] at hsum'
    exact add_left_cancel hsum'
  · rintro ⟨hx, hy⟩
    simp [hx, hy]

end Ogdoad.Excess
