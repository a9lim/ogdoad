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

/-- Multiplication by two is onto.  Moews's theorem supplies this property for
the additive group of short-game values; the algebra below uses only this
explicit interface. -/
def TwoDivisible (A : Type*) [AddCommGroup A] : Prop :=
  ∀ x : A, ∃ y : A, 2 • y = x

/-- Repeated halving produces a root for every power of two. -/
theorem twoPow_smul_surjective (hdiv : TwoDivisible A) (k : ℕ) :
    Function.Surjective (fun x : A => (2 ^ k) • x) := by
  induction k with
  | zero =>
      intro x
      exact ⟨x, by simp⟩
  | succ k ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      obtain ⟨z, hz⟩ := hdiv y
      refine ⟨z, ?_⟩
      calc
        (2 ^ (k + 1)) • z = (2 ^ k) • (2 • z) := by
          rw [show 2 ^ (k + 1) = 2 ^ k * 2 by omega]
          simpa [Nat.mul_comm] using (mul_nsmul z 2 (2 ^ k))
        _ = (2 ^ k) • y := by rw [hz]
        _ = x := hy

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

private theorem nsmul_mul_nsmul_mixed [Ring C] (m n : ℕ) (a b : C) :
    (m • a) * (n • b) = (m * n) • (a * b) := by
  calc
    (m • a) * (n • b) = m • (a * (n • b)) :=
      (nsmul_mul_left m a (n • b)).symm
    _ = m • (n • (a * b)) :=
      congrArg (fun c : C => m • c) (nsmul_mul_right n a b).symm
    _ = (m * n) • (a * b) :=
      by simpa [Nat.mul_comm] using (mul_nsmul (a * b) n m).symm

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

/-- Quadratic values scale by the square of every natural multiplier. -/
theorem FaithfulDatum.quadratic_nsmul [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C)) (n : ℕ) (x : A) :
    datum.quadratic (n • x) = (n * n) • datum.quadratic x := by
  apply datum.coeff_injective
  rw [← datum.square_relation, datum.gradeOne.map_nsmul,
    nsmul_mul_nsmul, map_nsmul, datum.square_relation]

/-- Polar values scale by the product of the two natural multipliers. -/
theorem FaithfulDatum.polar_nsmul [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C))
    (m n : ℕ) (x y : A) :
    datum.polar (m • x) (n • y) = (m * n) • datum.polar x y := by
  apply datum.coeff_injective
  rw [← datum.polar_relation, datum.gradeOne.map_nsmul,
    datum.gradeOne.map_nsmul]
  calc
    (m • datum.gradeOne x) * (n • datum.gradeOne y) +
          (n • datum.gradeOne y) * (m • datum.gradeOne x) =
        (m * n) • (datum.gradeOne x * datum.gradeOne y) +
          (n * m) • (datum.gradeOne y * datum.gradeOne x) := by
            rw [nsmul_mul_nsmul_mixed, nsmul_mul_nsmul_mixed]
    _ = (m * n) • (datum.gradeOne x * datum.gradeOne y) +
          (m * n) • (datum.gradeOne y * datum.gradeOne x) := by
            rw [Nat.mul_comm n m]
    _ = (m * n) • (datum.gradeOne x * datum.gradeOne y +
          datum.gradeOne y * datum.gradeOne x) := (nsmul_add _ _ _).symm
    _ = (m * n) • algebraMap R C (datum.polar x y) := by
          rw [datum.polar_relation]
    _ = algebraMap R C ((m * n) • datum.polar x y) := by rw [map_nsmul]

/-- Membership in the coefficient intersection `⋂ k, 4^k R`, stated
without choosing an ideal convention. -/
def InFourPowerIntersection [CommRing R] (r : R) : Prop :=
  ∀ k : ℕ, ∃ s : R, r = (4 ^ k) • s

/-- Ambient two-divisibility forces every quadratic coefficient into
`intersection_k 4^k R`. -/
theorem FaithfulDatum.quadratic_mem_fourPowerIntersection
    [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C))
    (hdiv : TwoDivisible A) (x : A) :
    InFourPowerIntersection (datum.quadratic x) := by
  intro k
  obtain ⟨u, hu⟩ := twoPow_smul_surjective hdiv k x
  refine ⟨datum.quadratic u, ?_⟩
  rw [← hu, datum.quadratic_nsmul]
  have hpow : (2 ^ k) * (2 ^ k) = 4 ^ k := by
    calc
      (2 ^ k) * (2 ^ k) = (2 * 2) ^ k := (mul_pow 2 2 k).symm
      _ = 4 ^ k := by norm_num
  rw [hpow]

/-- Ambient two-divisibility forces every polar coefficient into the same
four-power intersection. -/
theorem FaithfulDatum.polar_mem_fourPowerIntersection
    [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C))
    (hdiv : TwoDivisible A) (x y : A) :
    InFourPowerIntersection (datum.polar x y) := by
  intro k
  obtain ⟨u, hu⟩ := twoPow_smul_surjective hdiv k x
  obtain ⟨v, hv⟩ := twoPow_smul_surjective hdiv k y
  refine ⟨datum.polar u v, ?_⟩
  rw [← hu, ← hv, datum.polar_nsmul]
  have hpow : (2 ^ k) * (2 ^ k) = 4 ^ k := by
    calc
      (2 ^ k) * (2 ^ k) = (2 * 2) ^ k := (mul_pow 2 2 k).symm
      _ = 4 ^ k := by norm_num
  rw [hpow]

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

/-- The ambient theorem needs no separately supplied torsion root: repeated
halving constructs it from two-divisibility. -/
theorem FaithfulDatum.quadratic_eq_zero_of_twoPow_torsion
    [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C))
    (hdiv : TwoDivisible A) {t : A} {k : ℕ} (ht : (2 ^ k) • t = 0) :
    datum.quadratic t = 0 := by
  obtain ⟨y, hy⟩ := twoPow_smul_surjective hdiv k t
  exact datum.quadratic_eq_zero ht hy

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

/-- Every two-primary torsion element lies in the polar radical under the
ambient two-divisibility hypothesis. -/
theorem FaithfulDatum.polar_eq_zero_of_twoPow_torsion
    [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C))
    (hdiv : TwoDivisible A) {t : A} {k : ℕ} (ht : (2 ^ k) • t = 0)
    (x : A) : datum.polar t x = 0 := by
  obtain ⟨y, hy⟩ := twoPow_smul_surjective hdiv k t
  obtain ⟨z, hz⟩ := twoPow_smul_surjective hdiv k x
  exact datum.polar_eq_zero ht hy hz

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

/-- The quadratic function is constant on two-primary torsion cosets.  This
is the root-free ambient statement used by the paper. -/
theorem FaithfulDatum.quadratic_add_twoPow_torsion
    [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C))
    (hdiv : TwoDivisible A) {t : A} {k : ℕ} (ht : (2 ^ k) • t = 0)
    (x : A) : datum.quadratic (x + t) = datum.quadratic x := by
  rw [datum.polarization]
  rw [datum.quadratic_eq_zero_of_twoPow_torsion hdiv ht]
  rw [datum.polar_symm]
  rw [datum.polar_eq_zero_of_twoPow_torsion hdiv ht]
  simp

/-- Complete coefficient and torsion conclusion of the ambient game-exterior
obstruction, with no redundant root hypotheses. -/
theorem FaithfulDatum.ambient_obstruction
    [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C))
    (hdiv : TwoDivisible A) :
    (∀ x, InFourPowerIntersection (datum.quadratic x)) ∧
      (∀ x y, InFourPowerIntersection (datum.polar x y)) ∧
      (∀ (t : A) (k : ℕ), (2 ^ k) • t = 0 →
        datum.quadratic t = 0 ∧
          ∀ x, datum.polar t x = 0 ∧ datum.polar x t = 0) := by
  refine ⟨datum.quadratic_mem_fourPowerIntersection hdiv,
    datum.polar_mem_fourPowerIntersection hdiv, ?_⟩
  intro t k ht
  refine ⟨datum.quadratic_eq_zero_of_twoPow_torsion hdiv ht, ?_⟩
  intro x
  refine ⟨datum.polar_eq_zero_of_twoPow_torsion hdiv ht x, ?_⟩
  rw [datum.polar_symm]
  exact datum.polar_eq_zero_of_twoPow_torsion hdiv ht x

/-- In any coefficient ring where four vanishes, the four-power
intersection is zero.  This covers every characteristic-two ring and
`ZMod 4`. -/
theorem eq_zero_of_fourPowerIntersection_of_four_eq_zero
    [CommRing R] (hfour : (4 : R) = 0) {r : R}
    (hr : InFourPowerIntersection r) : r = 0 := by
  obtain ⟨s, hs⟩ := hr 1
  rw [pow_one] at hs
  simpa [nsmul_eq_mul, hfour] using hs

/-- The integral four-power intersection is zero. -/
theorem int_eq_zero_of_fourPowerIntersection {r : ℤ}
    (hr : InFourPowerIntersection r) : r = 0 := by
  by_contra hr0
  obtain ⟨s, hs⟩ := hr (r.natAbs + 1)
  have hdiv : (4 ^ (r.natAbs + 1) : ℤ) ∣ r := by
    refine ⟨s, ?_⟩
    simpa [nsmul_eq_mul] using hs
  have hlarge : r.natAbs < 4 ^ (r.natAbs + 1) := by
    exact (Nat.lt_succ_self r.natAbs).trans
      (Nat.lt_pow_self (by decide : 1 < 4))
  have hle : 4 ^ (r.natAbs + 1) ≤ r.natAbs := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hdiv hr0
  exact (not_lt_of_ge hle) hlarge

/-- Named coefficient-ring consequence used by the flagship theorem. -/
theorem FaithfulDatum.ambient_obstruction_vanishes_of_four_eq_zero
    [CommRing R] [Ring C] [Algebra R C]
    (datum : FaithfulDatum (A := A) (R := R) (C := C))
    (hdiv : TwoDivisible A) (hfour : (4 : R) = 0) :
    (∀ x, datum.quadratic x = 0) ∧ (∀ x y, datum.polar x y = 0) := by
  exact ⟨fun x ↦ eq_zero_of_fourPowerIntersection_of_four_eq_zero hfour
      (datum.quadratic_mem_fourPowerIntersection hdiv x),
    fun x y ↦ eq_zero_of_fourPowerIntersection_of_four_eq_zero hfour
      (datum.polar_mem_fourPowerIntersection hdiv x y)⟩

/-- Integral coefficient specialization of the ambient obstruction. -/
theorem FaithfulDatum.ambient_obstruction_vanishes_int
    [Ring C] [Algebra ℤ C]
    (datum : FaithfulDatum (A := A) (R := ℤ) (C := C))
    (hdiv : TwoDivisible A) :
    (∀ x, datum.quadratic x = 0) ∧ (∀ x y, datum.polar x y = 0) := by
  exact ⟨fun x ↦ int_eq_zero_of_fourPowerIntersection
      (datum.quadratic_mem_fourPowerIntersection hdiv x),
    fun x y ↦ int_eq_zero_of_fourPowerIntersection
      (datum.polar_mem_fourPowerIntersection hdiv x y)⟩

end

end Ogdoad.GameExterior
