import Ogdoad.Excess

/-!
# Rational evaluation in the ordinary-arm packing argument

These generic field lemmas check the algebraic injection used after choosing
an intermediate coefficient field.  They do not assert the finite-field
ancestry, the unique-factorization comparison of the ratio stars, or the
number of integer vectors in the selected ball and shell.
-/

namespace Ogdoad.Excess

open Polynomial

/-- Cancelling the top coefficient of two degree-at-most-`n + 1`
polynomials leaves a difference of degree at most `n`.  Unlike a hypothesis
on their leading coefficients, this remains correct when either degree is
already smaller. -/
theorem natDegree_sub_le_of_top_coeff_eq
    {K : Type*} [Field K] (A B : K[X]) (n : ℕ)
    (hA : A.natDegree ≤ n + 1) (hB : B.natDegree ≤ n + 1)
    (hphase : A.coeff (n + 1) = B.coeff (n + 1)) :
    (A - B).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_sub]
  by_cases htop : k = n + 1
  · simp [htop, hphase]
  · have hlarge : n + 1 < k := by omega
    rw [coeff_eq_zero_of_natDegree_lt (hA.trans_lt hlarge),
      coeff_eq_zero_of_natDegree_lt (hB.trans_lt hlarge), sub_self]

/-- Normalized rational functions cannot collide at an algebraic point when
their cross products have at most one degree beyond its minimal polynomial,
their boundary coefficient cancels, and symbolic cross-product equality
already distinguishes the indices.  This permits the entire inner ball
together with one leading-phase fibre of the next shell. -/
theorem rational_aeval_injective_of_normalized_boundary
    {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    (x : L) (num den : ι → K[X])
    (hx : IsIntegral K x)
    (hmin : (minpoly K x).coeff 0 ≠ 0)
    (hden : ∀ i, aeval x (den i) ≠ 0)
    (hnum0 : ∀ i, (num i).coeff 0 = 1)
    (hden0 : ∀ i, (den i).coeff 0 = 1)
    (hdegree : ∀ i j,
      (num i * den j).natDegree ≤ (minpoly K x).natDegree + 1)
    (hphase : ∀ i j,
      (num i * den j).coeff ((minpoly K x).natDegree + 1) =
        (num j * den i).coeff ((minpoly K x).natDegree + 1))
    (hsymbolic : ∀ i j, num i * den j = num j * den i → i = j) :
    Function.Injective (fun i ↦ aeval x (num i) / aeval x (den i)) := by
  intro i j heq
  apply hsymbolic i j
  apply polynomial_eq_of_aeval_eq_of_natDegree_le_minpoly_of_coeff_zero
    x (num i * den j) (num j * den i) hx
  · exact natDegree_sub_le_of_top_coeff_eq _ _ _
      (hdegree i j) (hdegree j i) (hphase i j)
  · simp [hnum0, hden0]
  · exact hmin
  · simpa only [map_mul] using (div_eq_div_iff (hden i) (hden j)).mp heq

/-- Once the normalized ratios are known to be powers of the same unit,
their algebraic injection is an actual order lower bound, independent of
the choice of the intermediate coefficient field. -/
theorem card_le_orderOf_of_normalized_rational_packing
    {K L ι : Type*} [Field K] [Field L] [Finite L] [Algebra K L]
    (x : L) (num den : ι → K[X]) (u : Lˣ)
    (hx : IsIntegral K x)
    (hmin : (minpoly K x).coeff 0 ≠ 0)
    (hden : ∀ i, aeval x (den i) ≠ 0)
    (hnum0 : ∀ i, (num i).coeff 0 = 1)
    (hden0 : ∀ i, (den i).coeff 0 = 1)
    (hdegree : ∀ i j,
      (num i * den j).natDegree ≤ (minpoly K x).natDegree + 1)
    (hphase : ∀ i j,
      (num i * den j).coeff ((minpoly K x).natDegree + 1) =
        (num j * den i).coeff ((minpoly K x).natDegree + 1))
    (hsymbolic : ∀ i j, num i * den j = num j * den i → i = j)
    (hcyclic : ∀ i, ∃ w : Subgroup.zpowers u,
      (w.val : L) = aeval x (num i) / aeval x (den i)) :
    Nat.card ι ≤ orderOf u := by
  classical
  choose value hvalue using hcyclic
  have hinj : Function.Injective value := by
    intro i j heq
    apply rational_aeval_injective_of_normalized_boundary
      x num den hx hmin hden hnum0 hden0 hdegree hphase hsymbolic
    dsimp only
    rw [← hvalue i, ← hvalue j, heq]
  calc
    Nat.card ι ≤ Nat.card (Subgroup.zpowers u) :=
      Nat.card_le_card_of_injective value hinj
    _ = orderOf u := Nat.card_zpowers u

end Ogdoad.Excess
