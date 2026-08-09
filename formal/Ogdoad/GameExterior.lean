import Mathlib

/-!
# The game-exterior divisibility obstruction

This file formalizes the algebraic core of the resolved `tisn` problem.  A
globally coherent game-native Clifford datum is defined on the full additive
group of short games, rather than independently on each finitely generated
subgroup.  Moews's structure theorem identifies that group abstractly as a
direct sum of copies of the dyadic rationals and dyadic rationals modulo the
integers, so multiplication by every power of two is surjective.  Moews also
proves that every torsion short game has two-power order.

The external structure theorem is not encoded here.  Instead, the results below
prove the exact reusable implication from explicit roots: an additive
grade-one realization in a ring makes a torsion element square to zero and
anticommute trivially with every element whenever the required roots exist.  An
injective coefficient map then forces the corresponding quadratic and polar
values themselves to vanish.
-/

namespace Ogdoad.GameExterior

noncomputable section

variable {A C R : Type*}
variable [AddCommGroup A]

private theorem nsmul_mul_nsmul [Ring C] (n : ℕ) (a b : C) :
    (n • a) * (n • b) = (n * n) • (a * b) := by
  simp only [nsmul_eq_mul, Nat.cast_mul]
  let N : C := n
  have ha : a * N = N * a := by
    simpa [N] using (Nat.cast_comm n a).symm
  change (N * a) * (N * b) = (N * N) * (a * b)
  calc
    (N * a) * (N * b) = N * (a * (N * b)) := mul_assoc _ _ _
    _ = N * ((a * N) * b) :=
      congrArg (fun q => N * q) (mul_assoc _ _ _).symm
    _ = N * ((N * a) * b) := by rw [ha]
    _ = (N * (N * a)) * b := (mul_assoc _ _ _).symm
    _ = ((N * N) * a) * b :=
      congrArg (fun q => q * b) (mul_assoc _ _ _).symm
    _ = (N * N) * (a * b) := mul_assoc _ _ _

private theorem nsmul_mul_left [Ring C] (n : ℕ) (a b : C) :
    n • (a * b) = (n • a) * b := by
  simp [nsmul_eq_mul, mul_assoc]

private theorem nsmul_mul_right [Ring C] (n : ℕ) (a b : C) :
    n • (a * b) = a * (n • b) := by
  simp only [nsmul_eq_mul]
  have ha : (n : C) * a = a * (n : C) := Nat.cast_comm n a
  calc
    (n : C) * (a * b) = ((n : C) * a) * b := (mul_assoc _ _ _).symm
    _ = (a * (n : C)) * b := by rw [ha]
    _ = a * ((n : C) * b) := mul_assoc _ _ _

/-- If an additive group embeds as grade one in a ring, divisibility makes the
square of every torsion element vanish.  No quadratic-map axioms are needed:
the statement follows directly from taking an `n`-th root of the torsion
element and multiplying its relation by that root. -/
theorem torsion_square_eq_zero [Ring C] (gradeOne : A →+ C)
    {t y : A} {n : ℕ} (ht : n • t = 0) (hroot : n • y = t) :
    gradeOne t * gradeOne t = 0 := by
  have hnny : (n * n) • y = 0 := by
    rw [mul_nsmul, hroot, ht]
  calc
    gradeOne t * gradeOne t = (n • gradeOne y) * (n • gradeOne y) := by
      rw [← gradeOne.map_nsmul, hroot]
    _ = (n * n) • (gradeOne y * gradeOne y) := by
      exact nsmul_mul_nsmul n _ _
    _ = ((n * n) • gradeOne y) * gradeOne y := by
      exact nsmul_mul_left (n * n) _ _
    _ = gradeOne ((n * n) • y) * gradeOne y := by
      rw [gradeOne.map_nsmul]
    _ = 0 := by rw [hnny]; simp

/-- The same root argument kills the polar anticommutator between a torsion
element and every other element.  Divisibility of the second input supplies
the second factor of `n`; the relation `n² • y = 0` then kills both products. -/
theorem torsion_anticommutator_eq_zero [Ring C] (gradeOne : A →+ C)
    {t x y z : A} {n : ℕ} (ht : n • t = 0)
    (hrootT : n • y = t) (hrootX : n • z = x) :
    gradeOne t * gradeOne x + gradeOne x * gradeOne t = 0 := by
  have hnny : (n * n) • y = 0 := by
    rw [mul_nsmul, hrootT, ht]
  have hit : gradeOne t = n • gradeOne y := by
    rw [← gradeOne.map_nsmul, hrootT]
  have hix : gradeOne x = n • gradeOne z := by
    rw [← gradeOne.map_nsmul, hrootX]
  calc
    gradeOne t * gradeOne x + gradeOne x * gradeOne t =
        (n • gradeOne y) * (n • gradeOne z) +
          (n • gradeOne z) * (n • gradeOne y) := by
      rw [hit, hix]
    _ = ((n * n) • gradeOne y) * gradeOne z +
          gradeOne z * ((n * n) • gradeOne y) := by
      rw [nsmul_mul_nsmul, nsmul_mul_nsmul]
      rw [nsmul_mul_left, nsmul_mul_right]
    _ = gradeOne ((n * n) • y) * gradeOne z +
          gradeOne z * gradeOne ((n * n) • y) := by
      rw [gradeOne.map_nsmul]
    _ = 0 := by rw [hnny]; simp

/-- A coefficient-faithful Clifford realization of additive generators.  The
only structure used by the obstruction is the additive grade-one map, the
square and anticommutator relations, and injectivity of the coefficient map. -/
structure FaithfulDatum [CommRing R] [Ring C] [Algebra R C] where
  gradeOne : A →+ C
  quadratic : A → R
  polar : A → A → R
  coeff_injective : Function.Injective (algebraMap R C)
  square_relation : ∀ x, gradeOne x * gradeOne x = algebraMap R C (quadratic x)
  polar_relation : ∀ x y,
    gradeOne x * gradeOne y + gradeOne y * gradeOne x = algebraMap R C (polar x y)

/-- Additivity of grade one and the Clifford relations force the usual
polarization identity; it need not be assumed separately. -/
theorem FaithfulDatum.polarization [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C)) (x y : A) :
    datum.quadratic (x + y) =
      datum.quadratic x + datum.quadratic y + datum.polar x y := by
  apply datum.coeff_injective
  rw [← datum.square_relation, datum.gradeOne.map_add]
  calc
    (datum.gradeOne x + datum.gradeOne y) *
          (datum.gradeOne x + datum.gradeOne y) =
        datum.gradeOne x * datum.gradeOne x +
          datum.gradeOne y * datum.gradeOne y +
            (datum.gradeOne x * datum.gradeOne y +
              datum.gradeOne y * datum.gradeOne x) := by
      noncomm_ring
    _ = algebraMap R C (datum.quadratic x) +
          algebraMap R C (datum.quadratic y) +
            algebraMap R C (datum.polar x y) := by
      rw [datum.square_relation, datum.square_relation, datum.polar_relation]
    _ = algebraMap R C
          (datum.quadratic x + datum.quadratic y + datum.polar x y) := by
      simp

/-- The polar function is symmetric because its defining anticommutator is. -/
theorem FaithfulDatum.polar_symm [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C)) (x y : A) :
    datum.polar x y = datum.polar y x := by
  apply datum.coeff_injective
  rw [← datum.polar_relation, ← datum.polar_relation]
  exact add_comm _ _

/-- In a coefficient-faithful realization, an explicit root of a torsion element
forces its quadratic value to vanish. -/
theorem FaithfulDatum.quadratic_eq_zero [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C))
    {t y : A} {n : ℕ} (ht : n • t = 0) (hroot : n • y = t) :
    datum.quadratic t = 0 := by
  apply datum.coeff_injective
  rw [map_zero]
  rw [← datum.square_relation]
  exact torsion_square_eq_zero datum.gradeOne ht hroot

/-- In the same realization, every torsion element lies in the polar radical. -/
theorem FaithfulDatum.polar_eq_zero [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C))
    {t x y z : A} {n : ℕ} (ht : n • t = 0)
    (hrootT : n • y = t) (hrootX : n • z = x) :
    datum.polar t x = 0 := by
  apply datum.coeff_injective
  rw [map_zero]
  rw [← datum.polar_relation]
  exact torsion_anticommutator_eq_zero datum.gradeOne ht hrootT hrootX

/-- A torsion translation does not change the quadratic value once roots of the
torsion element and the translated point are available.  This is the formal
coset-invariance statement behind factorization through the torsion-free quotient. -/
theorem FaithfulDatum.quadratic_add_torsion [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C))
    {t x y z : A} {n : ℕ} (ht : n • t = 0)
    (hrootT : n • y = t) (hrootX : n • z = x) :
    datum.quadratic (x + t) = datum.quadratic x := by
  rw [datum.polarization]
  rw [datum.quadratic_eq_zero ht hrootT]
  rw [datum.polar_symm]
  rw [datum.polar_eq_zero ht hrootT hrootX]
  simp

end

end Ogdoad.GameExterior
