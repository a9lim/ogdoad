import Ogdoad.Fifo
import Mathlib.LinearAlgebra.QuadraticForm.Basis

/-!
# Quadratic expansion in a public Witt frame

This file kernel-checks the algebraic split used by the Gold--Arf normal-play
construction: adapted-basis diagonal contributions plus the parity of active
hyperbolic pairs.
-/

noncomputable section

open scoped BigOperators

namespace Ogdoad.GoldMatching

variable {M : Type*} [AddCommGroup M] [Module F2 M]

/-- A quadratic map is additive on a finite orthogonal family. -/
theorem quadratic_sum_of_pairwise_polar_zero
    (Q : QuadraticMap F2 M F2) {I : Type*} [DecidableEq I]
    (s : Finset I) (v : I → M)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      QuadraticMap.polar Q (v i) (v j) = 0) :
    Q (∑ i ∈ s, v i) = ∑ i ∈ s, Q (v i) := by
  induction s using Finset.induction_on with
  | empty => simp [QuadraticMap.map_zero]
  | @insert a s ha ih =>
      have hrest : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
          QuadraticMap.polar Q (v i) (v j) = 0 := by
        intro i hi j hj hij
        exact horth i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij
      have hpolar : QuadraticMap.polar Q (v a) (∑ i ∈ s, v i) = 0 := by
        rw [← QuadraticMap.polarBilin_apply_apply, map_sum]
        apply Finset.sum_eq_zero
        intro i hi
        exact horth a (Finset.mem_insert_self a s) i
          (Finset.mem_insert_of_mem hi) (Ne.symm (ne_of_mem_of_not_mem hi ha))
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        QuadraticMap.map_add Q, ih hrest, hpolar, add_zero]

/-- In a hyperbolic plane over `F₂`, the quadratic value is its two
coordinate diagonals plus the active-pair bit. -/
theorem quadratic_hyperbolic_plane
    (Q : QuadraticMap F2 M F2) (e f : M) (a b : F2)
    (hef : QuadraticMap.polar Q e f = 1) :
    Q (a • e + b • f) = a * Q e + b * Q f + a * b := by
  have ha : a * a = a := by
    by_cases ha0 : a = 0
    · simp [ha0]
    · have ha1 : a = 1 := Ogdoad.zmod2_eq_one_of_ne_zero a ha0
      simp [ha1]
  have hb : b * b = b := by
    by_cases hb0 : b = 0
    · simp [hb0]
    · have hb1 : b = 1 := Ogdoad.zmod2_eq_one_of_ne_zero b hb0
      simp [hb1]
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul,
    QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right, hef]
  simp [ha, hb]

/-- Bilinearity expands the polar form of two finite coordinate sums into
the double sum of their coordinate pairings. -/
theorem polar_finset_sum
    (Q : QuadraticMap F2 M F2)
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (A : Finset I) (B : Finset J) (v : I → M) (w : J → M) :
    QuadraticMap.polar Q (∑ i ∈ A, v i) (∑ j ∈ B, w j) =
      ∑ i ∈ A, ∑ j ∈ B, QuadraticMap.polar Q (v i) (w j) := by
  rw [← QuadraticMap.polarBilin_apply_apply]
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  simp only [QuadraticMap.polarBilin_apply_apply]

/-- The parity of hyperbolic pairs whose two coordinates are active. -/
def activePairParity {P : Type*} [DecidableEq P]
    (A B : Finset P) : F2 :=
  ((A ∩ B).card : F2)

theorem sum_pair_indicator_eq_activePairParity
    {P : Type*} [DecidableEq P] (A B : Finset P) :
    (∑ p ∈ A, ∑ q ∈ B, if p = q then (1 : F2) else 0) =
      activePairParity A B := by
  classical
  have inner (p : P) :
      (∑ q ∈ B, if p = q then (1 : F2) else 0) =
        if p ∈ B then 1 else 0 := by
    simp
  simp_rw [inner]
  simp [activePairParity]

/-- Coordinate expansion in a public adapted basis.  `e p,f p` are the
named hyperbolic pairs and `r i` are radical/isolated basis vectors.  Thus
the quadratic value is exactly the selected basis diagonals plus the parity
of pairs for which both coordinates are selected. -/
theorem quadratic_adapted_support
    (Q : QuadraticMap F2 M F2)
    {P I : Type*} [DecidableEq P] [DecidableEq I]
    (e f : P → M) (r : I → M)
    (A B : Finset P) (C : Finset I)
    (hee : ∀ p q, p ≠ q → QuadraticMap.polar Q (e p) (e q) = 0)
    (hff : ∀ p q, p ≠ q → QuadraticMap.polar Q (f p) (f q) = 0)
    (hrr : ∀ i j, i ≠ j → QuadraticMap.polar Q (r i) (r j) = 0)
    (hef : ∀ p q, QuadraticMap.polar Q (e p) (f q) =
      if p = q then 1 else 0)
    (her : ∀ p i, QuadraticMap.polar Q (e p) (r i) = 0)
    (hfr : ∀ p i, QuadraticMap.polar Q (f p) (r i) = 0) :
    Q ((∑ p ∈ A, e p) + (∑ p ∈ B, f p) + (∑ i ∈ C, r i)) =
      (∑ p ∈ A, Q (e p)) + (∑ p ∈ B, Q (f p)) +
        (∑ i ∈ C, Q (r i)) + activePairParity A B := by
  have hQE : Q (∑ p ∈ A, e p) = ∑ p ∈ A, Q (e p) := by
    apply quadratic_sum_of_pairwise_polar_zero Q A e
    intro p hp q hq hpq
    exact hee p q hpq
  have hQF : Q (∑ p ∈ B, f p) = ∑ p ∈ B, Q (f p) := by
    apply quadratic_sum_of_pairwise_polar_zero Q B f
    intro p hp q hq hpq
    exact hff p q hpq
  have hQR : Q (∑ i ∈ C, r i) = ∑ i ∈ C, Q (r i) := by
    apply quadratic_sum_of_pairwise_polar_zero Q C r
    intro i hi j hj hij
    exact hrr i j hij
  have hEF : QuadraticMap.polar Q (∑ p ∈ A, e p)
      (∑ p ∈ B, f p) = activePairParity A B := by
    rw [polar_finset_sum]
    simp_rw [hef]
    exact sum_pair_indicator_eq_activePairParity A B
  have hER : QuadraticMap.polar Q (∑ p ∈ A, e p)
      (∑ i ∈ C, r i) = 0 := by
    rw [polar_finset_sum]
    simp [her]
  have hFR : QuadraticMap.polar Q (∑ p ∈ B, f p)
      (∑ i ∈ C, r i) = 0 := by
    rw [polar_finset_sum]
    simp [hfr]
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q,
    QuadraticMap.polar_add_left, hQE, hQF, hQR, hEF, hER, hFR]
  abel

/-- Any linear diagonal source sums to its evaluation on the represented
support vector.  This is the abstract finite-sum form of the Gold
Artin--Schreier/trace source substitution. -/
theorem diagonal_source_sum
    (ell : M →ₗ[F2] F2) {I : Type*} [DecidableEq I]
    (S : Finset I) (v : I → M) :
    (∑ i ∈ S, ell (v i)) = ell (∑ i ∈ S, v i) := by
  simp

/-- If the adapted-basis diagonal is supplied by one public linear source,
the entire quadratic value is that source evaluated once on `x`, plus the
active hyperbolic-pair parity. -/
theorem quadratic_adapted_support_of_linear_diagonal
    (Q : QuadraticMap F2 M F2) (ell : M →ₗ[F2] F2)
    {P I : Type*} [DecidableEq P] [DecidableEq I]
    (e f : P → M) (r : I → M)
    (A B : Finset P) (C : Finset I)
    (hee : ∀ p q, p ≠ q → QuadraticMap.polar Q (e p) (e q) = 0)
    (hff : ∀ p q, p ≠ q → QuadraticMap.polar Q (f p) (f q) = 0)
    (hrr : ∀ i j, i ≠ j → QuadraticMap.polar Q (r i) (r j) = 0)
    (hef : ∀ p q, QuadraticMap.polar Q (e p) (f q) =
      if p = q then 1 else 0)
    (her : ∀ p i, QuadraticMap.polar Q (e p) (r i) = 0)
    (hfr : ∀ p i, QuadraticMap.polar Q (f p) (r i) = 0)
    (hQe : ∀ p, Q (e p) = ell (e p))
    (hQf : ∀ p, Q (f p) = ell (f p))
    (hQr : ∀ i, Q (r i) = ell (r i)) :
    Q ((∑ p ∈ A, e p) + (∑ p ∈ B, f p) + (∑ i ∈ C, r i)) =
      ell ((∑ p ∈ A, e p) + (∑ p ∈ B, f p) +
        (∑ i ∈ C, r i)) + activePairParity A B := by
  rw [quadratic_adapted_support Q e f r A B C hee hff hrr hef her hfr]
  simp_rw [hQe, hQf, hQr]
  rw [diagonal_source_sum, diagonal_source_sum, diagonal_source_sum]
  simp only [map_add]

/-- Change-of-frame form of the source identity. The adapted diagonal need
not equal the old linear source: it may contain a public correction `d`
computed from the polar form and the basis change. The correction sums
coordinatewise, while the transported source still evaluates only once on
the represented vector. -/
theorem quadratic_adapted_support_of_split_diagonal
    (Q : QuadraticMap F2 M F2) (ell : M →ₗ[F2] F2)
    {P I : Type*} [DecidableEq P] [DecidableEq I]
    (e f : P → M) (r : I → M)
    (dE dF : P → F2) (dR : I → F2)
    (A B : Finset P) (C : Finset I)
    (hee : ∀ p q, p ≠ q → QuadraticMap.polar Q (e p) (e q) = 0)
    (hff : ∀ p q, p ≠ q → QuadraticMap.polar Q (f p) (f q) = 0)
    (hrr : ∀ i j, i ≠ j → QuadraticMap.polar Q (r i) (r j) = 0)
    (hef : ∀ p q, QuadraticMap.polar Q (e p) (f q) =
      if p = q then 1 else 0)
    (her : ∀ p i, QuadraticMap.polar Q (e p) (r i) = 0)
    (hfr : ∀ p i, QuadraticMap.polar Q (f p) (r i) = 0)
    (hQe : ∀ p, Q (e p) = dE p + ell (e p))
    (hQf : ∀ p, Q (f p) = dF p + ell (f p))
    (hQr : ∀ i, Q (r i) = dR i + ell (r i)) :
    Q ((∑ p ∈ A, e p) + (∑ p ∈ B, f p) + (∑ i ∈ C, r i)) =
      (∑ p ∈ A, dE p) + (∑ p ∈ B, dF p) +
        (∑ i ∈ C, dR i) +
        ell ((∑ p ∈ A, e p) + (∑ p ∈ B, f p) +
          (∑ i ∈ C, r i)) + activePairParity A B := by
  rw [quadratic_adapted_support Q e f r A B C hee hff hrr hef her hfr]
  simp_rw [hQe, hQf, hQr, Finset.sum_add_distrib]
  rw [diagonal_source_sum, diagonal_source_sum, diagonal_source_sum]
  simp only [map_add]
  abel

end Ogdoad.GoldMatching
