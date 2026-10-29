import Mathlib

/-!
# Fifth-root product and odd-character transfer for the cubic excess gap

The exact product over the five roots is obtained from Mathlib's Kummer
factorization, without enumerating a finite field. The character lemmas
transfer a known norm character and four equal translated characters to
their common value. Literal Conway specialization and the orbit calculation
that makes those four characters equal remain paper-level inputs.
-/

namespace Ogdoad.Excess

open scoped BigOperators

/-- The fifth-root norm product in characteristic two. -/
theorem fifth_root_translate_product
    {K : Type*} [Field K] [CharP K 2]
    (z r : K) (hr : IsPrimitiveRoot r 5) :
    (∏ i ∈ Finset.range 5, (z + r ^ i)) = z ^ 5 + 1 := by
  have hpoly := X_pow_sub_C_eq_prod hr (by norm_num : 0 < 5)
    (by simp : (1 : K) ^ 5 = 1)
  have heval := congrArg (Polynomial.eval z) hpoly
  simpa only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod, mul_one, sub_eq_add_neg,
    CharTwo.neg_eq] using heval.symm

/-- Indexed by `Fin 5`, so that the factor at one separates directly from
the four nontrivial fifth-root translates in a multiplicative character. -/
theorem fifth_root_translate_product_fin
    {K : Type*} [Field K] [CharP K 2]
    (z r : K) (hr : IsPrimitiveRoot r 5) :
    (∏ i : Fin 5, (z + r ^ (i : ℕ))) = z ^ 5 + 1 := by
  calc
    (∏ i : Fin 5, (z + r ^ (i : ℕ))) =
        ∏ i ∈ Finset.range 5, (z + r ^ i) :=
      Fin.prod_univ_eq_prod_range (fun i : ℕ => z + r ^ i) 5
    _ = z ^ 5 + 1 := fifth_root_translate_product z r hr

/-- An element of odd order cannot be a nontrivial fourth root of unity. -/
theorem eq_one_of_fourth_power_and_odd_power
    {G : Type*} [Monoid G] (b : G) (p : ℕ) (hp : Odd p)
    (hfour : b ^ 4 = 1) (hporder : b ^ p = 1) : b = 1 := by
  have hcop : Nat.Coprime 4 p := by
    simpa using hp.coprime_two_left.pow_left 2
  have hd : orderOf b ∣ Nat.gcd 4 p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hfour)
      (orderOf_dvd_of_pow_eq_one hporder)
  rw [hcop.gcd_eq_one] at hd
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hd)

/-- The fifth-root norm character is the fourth power of the common
nontrivial-root character when the factor at one has trivial character. -/
theorem four_equal_characters_fourth_power
    {M G : Type*} [CommMonoid M] [CommMonoid G]
    (χ : M →* G) (u : Fin 5 → M) (b : G)
    (hproduct : χ (∏ i : Fin 5, u i) = 1)
    (hzero : χ (u 0) = 1)
    (hequal : ∀ i : Fin 4, χ (u i.succ) = b) : b ^ 4 = 1 := by
  rw [map_prod, Fin.prod_univ_succ] at hproduct
  simpa only [hzero, hequal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, one_mul] using hproduct

/-- The norm product forces the four common translated characters to be
trivial when their values have odd order. -/
theorem four_equal_odd_characters_eq_one
    {M G : Type*} [CommMonoid M] [CommMonoid G]
    (χ : M →* G) (u : Fin 5 → M) (b : G)
    (p : ℕ) (hp : Odd p) (hporder : b ^ p = 1)
    (hproduct : χ (∏ i : Fin 5, u i) = 1)
    (hzero : χ (u 0) = 1)
    (hequal : ∀ i : Fin 4, χ (u i.succ) = b) : b = 1 := by
  exact eq_one_of_fourth_power_and_odd_power b p hp
    (four_equal_characters_fourth_power χ u b hproduct hzero hequal) hporder

end Ogdoad.Excess
