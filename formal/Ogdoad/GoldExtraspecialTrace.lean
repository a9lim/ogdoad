import Ogdoad.GoldExtraspecial
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Trace-specialized Gold--Heisenberg extensions

The generic cocycle group in `GoldExtraspecial.lean` is specialized here to
the actual finite-field map

`phi_(a,c)(x,y) = Tr(c * x * y^(2^a))`.

The construction uses Mathlib's field trace and iterated Frobenius ring
homomorphism, so biadditivity is proved rather than assumed.  The final
section gives the anisotropic two-dimensional (quaternion) order-eight cell
explicitly.
-/

noncomputable section

namespace Ogdoad.GoldExtraspecialTrace

open Ogdoad.GoldExtraspecial

abbrev F2 := ZMod 2

variable {K : Type*} [Field K] [Finite K] [CharP K 2]
  [Algebra F2 K] [FiniteDimensional F2 K]

/-- The oriented Gold half-polar map built from actual field trace and
Frobenius. -/
def goldHalfPolar (a : ℕ) (c : K) : HalfPolar K where
  toFun x :=
    { toFun := fun y => Algebra.trace F2 K
        (c * x * iterateFrobenius K 2 a y)
      map_zero' := by simp
      map_add' := by
        intro y z
        rw [map_add, mul_add, map_add] }
  map_zero' := by
    ext y
    simp
  map_add' := by
    intro x z
    ext y
    change Algebra.trace F2 K
        (c * (x + z) * iterateFrobenius K 2 a y) =
      Algebra.trace F2 K (c * x * iterateFrobenius K 2 a y) +
        Algebra.trace F2 K (c * z * iterateFrobenius K 2 a y)
    rw [show c * (x + z) * iterateFrobenius K 2 a y =
        c * x * iterateFrobenius K 2 a y +
          c * z * iterateFrobenius K 2 a y by ring, map_add]

omit [Finite K] [FiniteDimensional F2 K] in
@[simp] theorem goldHalfPolar_apply (a : ℕ) (c x y : K) :
    goldHalfPolar a c x y =
      Algebra.trace F2 K (c * x * y ^ (2 ^ a)) := by
  rfl

/-- The Gold trace quadratic form is the diagonal of the specialized
half-polar map. -/
def goldQuadratic (a : ℕ) (c x : K) : F2 :=
  Algebra.trace F2 K (c * x * x ^ (2 ^ a))

/-- Its polar form is the symmetrization of the oriented trace cocycle. -/
def goldPolar (a : ℕ) (c x y : K) : F2 :=
  Algebra.trace F2 K
    (c * (x * y ^ (2 ^ a) + y * x ^ (2 ^ a)))

omit [Finite K] [FiniteDimensional F2 K] in
theorem goldHalfPolar_diagonal (a : ℕ) (c x : K) :
    goldHalfPolar a c x x = goldQuadratic a c x := by
  rfl

omit [Finite K] [FiniteDimensional F2 K] in
theorem goldHalfPolar_symmetrization (a : ℕ) (c x y : K) :
    goldHalfPolar a c x y + goldHalfPolar a c y x =
      goldPolar a c x y := by
  simp only [goldHalfPolar_apply, goldPolar]
  rw [← map_add]
  congr 1
  ring

omit [Finite K] [FiniteDimensional F2 K] in
/-- Polarization identity for the trace-specialized Gold form. -/
theorem goldQuadratic_add (a : ℕ) (c x y : K) :
    goldQuadratic a c (x + y) =
      goldQuadratic a c x + goldQuadratic a c y + goldPolar a c x y := by
  rw [← goldHalfPolar_diagonal]
  change goldHalfPolar a c (x + y) (x + y) = _
  simp only [map_add, AddMonoidHom.add_apply]
  rw [goldHalfPolar_diagonal, goldHalfPolar_diagonal]
  have hsymm := goldHalfPolar_symmetrization a c x y
  rw [← hsymm]
  abel

/-- The actual Gold--Heisenberg group. -/
abbrev GoldExtension (a : ℕ) (c : K) :=
  Extension (goldHalfPolar a c)

omit [Finite K] [FiniteDimensional F2 K] in
/-- Squaring in the trace-specialized extension recovers the Gold form. -/
theorem goldExtension_square (a : ℕ) (c : K)
    (p : GoldExtension a c) :
    p * p = ⟨goldQuadratic a c p.vector, 0⟩ := by
  rw [Extension.square, goldHalfPolar_diagonal]

omit [Finite K] [FiniteDimensional F2 K] in
/-- Swapping two factors recovers the Gold polar form. -/
theorem goldExtension_swap_defect (a : ℕ) (c : K)
    (p q : GoldExtension a c) :
    p * q =
      (⟨goldPolar a c p.vector q.vector, 0⟩ : GoldExtension a c) *
        (q * p) := by
  rw [Extension.swap_defect, goldHalfPolar_symmetrization]

omit [Finite K] [FiniteDimensional F2 K] in
/-- The center criterion specialized to the trace Gold polar form. -/
theorem goldExtension_isCentral_iff (a : ℕ) (c : K)
    (p : GoldExtension a c) :
    (∀ q : GoldExtension a c, p * q = q * p) ↔
      ∀ y : K, goldPolar a c p.vector y = 0 := by
  rw [Extension.isCentral_iff]
  constructor <;> intro h y
  · rw [← goldHalfPolar_symmetrization]
    exact h y
  · rw [goldHalfPolar_symmetrization]
    exact h y

omit [Finite K] [FiniteDimensional F2 K] in
/-- Complete trace-level specialization of the universal cocycle theorem. -/
theorem gold_trace_extension_specification (a : ℕ) (c : K) :
    (∀ p : GoldExtension a c,
      p * p = ⟨goldQuadratic a c p.vector, 0⟩) ∧
    (∀ p q : GoldExtension a c,
      p * q =
        (⟨goldPolar a c p.vector q.vector, 0⟩ : GoldExtension a c) *
          (q * p)) ∧
    (∀ p : GoldExtension a c,
      (∀ q, p * q = q * p) ↔
        ∀ y, goldPolar a c p.vector y = 0) := by
  exact ⟨goldExtension_square a c, goldExtension_swap_defect a c,
    goldExtension_isCentral_iff a c⟩

/-! ## The actual `F₄` Gold cell -/

def goldExtensionEquiv (a : ℕ) (c : K) : GoldExtension a c ≃ F2 × K where
  toFun p := (p.central, p.vector)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype K] (a : ℕ) (c : K) : Fintype (GoldExtension a c) :=
  Fintype.ofEquiv (F2 × K) (goldExtensionEquiv a c).symm

omit [CharP K 2] [FiniteDimensional F2 K] in
/-- At degree two, a trace-one scale makes the `a=1` Gold form anisotropic:
all three nonzero field elements have quadratic value one. -/
theorem goldQuadratic_one_eq_one_of_card_four
    (hcard : Nat.card K = 4) (c : K) (hc : Algebra.trace F2 K c = 1)
    {x : K} (hx : x ≠ 0) : goldQuadratic 1 c x = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card K = 4 := by simpa [Nat.card_eq_fintype_card] using hcard
  have hx3 : x ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one x hx
    simpa [hcard'] using h
  simp only [goldQuadratic, pow_one]
  rw [show c * x * x ^ 2 = c * (x ^ 3) by ring, hx3, mul_one, hc]

omit [FiniteDimensional F2 K] in
/-- The trace-one `F₄` Gold extension is the order-eight anisotropic
(quaternion) cell: it has eight elements, every noncentral quotient lift has
square the central involution, and distinct nonzero quotient directions
anticommute.  These properties distinguish `Q₈` from the dihedral cell. -/
theorem gold_f4_is_quaternion_cell
    [Fintype K]
    (hcard : Nat.card K = 4) (c : K) (hc : Algebra.trace F2 K c = 1) :
    Fintype.card (GoldExtension (K := K) 1 c) = 8 ∧
      (∀ x : K, x ≠ 0 →
        (⟨0, x⟩ : GoldExtension (K := K) 1 c) * ⟨0, x⟩ =
          Extension.center (goldHalfPolar 1 c)) ∧
      (∀ x y : K, x ≠ 0 → y ≠ 0 → x ≠ y →
        (⟨0, x⟩ : GoldExtension (K := K) 1 c) * ⟨0, y⟩ =
          Extension.center (goldHalfPolar 1 c) * (⟨0, y⟩ * ⟨0, x⟩)) := by
  have hcard' : Fintype.card K = 4 := by simpa [Nat.card_eq_fintype_card] using hcard
  constructor
  · rw [Fintype.card_congr (goldExtensionEquiv 1 c), Fintype.card_prod,
      ZMod.card, hcard']
  constructor
  · intro x hx
    rw [goldExtension_square, goldQuadratic_one_eq_one_of_card_four hcard c hc hx]
    rfl
  · intro x y hx hy hxy
    have hxy0 : x + y ≠ 0 := by
      intro h
      have : x = y := by
        calc x = x + 0 := by simp
             _ = x + (x + y) := by rw [h]
             _ = (x + x) + y := by rw [add_assoc]
             _ = y := by rw [Extension.add_self_eq_zero]; simp
      exact hxy this
    have hpolar : goldPolar 1 c x y = 1 := by
      have hadd := goldQuadratic_add 1 c x y
      rw [goldQuadratic_one_eq_one_of_card_four hcard c hc hxy0,
        goldQuadratic_one_eq_one_of_card_four hcard c hc hx,
        goldQuadratic_one_eq_one_of_card_four hcard c hc hy] at hadd
      simpa using hadd.symm
    rw [goldExtension_swap_defect, hpolar]
    rfl

/-- An `F₄` Gold extension satisfying the quaternion-cell specification
exists; trace one is obtained from separability rather than accepted as an
extra existence premise. -/
theorem exists_gold_f4_quaternion_cell
    [Fintype K] (hcard : Nat.card K = 4) :
    ∃ c : K, Algebra.trace F2 K c = 1 ∧
      Fintype.card (GoldExtension (K := K) 1 c) = 8 ∧
      (∀ x : K, x ≠ 0 →
        (⟨0, x⟩ : GoldExtension (K := K) 1 c) * ⟨0, x⟩ =
          Extension.center (goldHalfPolar 1 c)) ∧
      (∀ x y : K, x ≠ 0 → y ≠ 0 → x ≠ y →
        (⟨0, x⟩ : GoldExtension (K := K) 1 c) * ⟨0, y⟩ =
          Extension.center (goldHalfPolar 1 c) * (⟨0, y⟩ * ⟨0, x⟩)) := by
  obtain ⟨c, hc⟩ := Algebra.trace_surjective F2 K (1 : F2)
  exact ⟨c, hc, gold_f4_is_quaternion_cell hcard c hc⟩

/-! ## The order-eight anisotropic cell -/

abbrev Plane := F2 × F2

/-- The oriented cocycle whose diagonal is
`Q(x₁,x₂)=x₁+x₁x₂+x₂`, the anisotropic binary plane. -/
def q8HalfPolar : HalfPolar Plane where
  toFun x :=
    { toFun := fun y => x.1 * y.1 + x.1 * y.2 + x.2 * y.2
      map_zero' := by simp
      map_add' := by intro y z; rcases y with ⟨y₁, y₂⟩; rcases z with ⟨z₁, z₂⟩; simp; ring }
  map_zero' := by ext y; simp
  map_add' := by
    intro x z
    ext y
    rcases x with ⟨x₁, x₂⟩
    rcases z with ⟨z₁, z₂⟩
    rcases y with ⟨y₁, y₂⟩
    simp
    ring

abbrev Q8Cell := Extension q8HalfPolar

def q8i : Q8Cell := ⟨0, (1, 0)⟩
def q8j : Q8Cell := ⟨0, (0, 1)⟩

def q8CellEquiv : Q8Cell ≃ F2 × Plane where
  toFun p := (p.central, p.vector)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Q8Cell := Fintype.ofEquiv (F2 × Plane) q8CellEquiv.symm

theorem q8Cell_card : Fintype.card Q8Cell = 8 := by
  rw [Fintype.card_congr q8CellEquiv]
  decide

theorem q8i_square : q8i * q8i = Extension.center q8HalfPolar := by
  decide

theorem q8j_square : q8j * q8j = Extension.center q8HalfPolar := by
  decide

theorem q8ij_square : (q8i * q8j) * (q8i * q8j) =
    Extension.center q8HalfPolar := by
  decide

theorem q8i_q8j_anticommute :
    q8i * q8j = Extension.center q8HalfPolar * (q8j * q8i) := by
  decide

/-- Kernel-checked identification of the eight-element anisotropic cell by
the quaternion presentation: three generating noncentral lifts square to the
central involution and the two basis lifts anticommute. -/
theorem q8Cell_is_quaternion_cell :
    Fintype.card Q8Cell = 8 ∧
      q8i * q8i = Extension.center q8HalfPolar ∧
      q8j * q8j = Extension.center q8HalfPolar ∧
      (q8i * q8j) * (q8i * q8j) = Extension.center q8HalfPolar ∧
      q8i * q8j = Extension.center q8HalfPolar * (q8j * q8i) := by
  exact ⟨q8Cell_card, q8i_square, q8j_square, q8ij_square,
    q8i_q8j_anticommute⟩

/-- The explicit anisotropic cell is the quaternion group of order eight,
not merely a group satisfying a partial presentation. -/
def quaternionToQ8 : QuaternionGroup 2 →* Q8Cell where
  toFun
    | .a k => q8i ^ k.val
    | .xa k => q8j * q8i ^ k.val
  map_one' := by rfl
  map_mul' := by
    rintro (i | i) (j | j)
    all_goals fin_cases i <;> fin_cases j <;> decide

theorem quaternionToQ8_bijective : Function.Bijective quaternionToQ8 := by
  apply (Fintype.bijective_iff_injective_and_card quaternionToQ8).2
  constructor
  · intro a b
    rcases a with a | a <;> rcases b with b | b
    all_goals fin_cases a <;> fin_cases b <;> decide
  · rw [QuaternionGroup.card, q8Cell_card]

/-- Kernel-checked group isomorphism between the coordinate anisotropic cell and
Mathlib's `QuaternionGroup 2`. -/
noncomputable def q8CellMulEquivQuaternion : Q8Cell ≃* QuaternionGroup 2 :=
  (MulEquiv.ofBijective quaternionToQ8 quaternionToQ8_bijective).symm

/-! ## Identification of the trace Gold cell

For a cardinality-four field and trace-one scale `c`, the ordered basis
`(c, 1)` identifies the actual trace cocycle with `q8HalfPolar`.  This closes
the central-extension join: the `MulEquiv` below starts at `GoldExtension`, not
at a parallel coordinate presentation. -/

section GoldQ8Bridge

variable [Fintype K]

omit [Finite K] [CharP K 2] [FiniteDimensional F2 K] in
/-- A cardinality-four extension of `F₂` has vector-space dimension two. -/
theorem finrank_eq_two_of_card_four (hcard : Nat.card K = 4) :
    Module.finrank F2 K = 2 := by
  have hcard' : Fintype.card K = 4 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  apply Nat.pow_right_injective (by norm_num : 1 < 2)
  calc
    2 ^ Module.finrank F2 K = Fintype.card K := by
      simpa [ZMod.card] using
        (@Module.card_eq_pow_finrank F2 K _ _ _ _).symm
    _ = 4 := hcard'
    _ = 2 ^ 2 := by norm_num

omit [Finite K] [CharP K 2] [FiniteDimensional F2 K] in
/-- The relative trace of one vanishes in a cardinality-four extension of
`F₂`. -/
theorem trace_one_eq_zero_of_card_four (hcard : Nat.card K = 4) :
    Algebra.trace F2 K (1 : K) = 0 := by
  rw [show (1 : K) = algebraMap F2 K 1 by simp, Algebra.trace_algebraMap,
    finrank_eq_two_of_card_four hcard]
  decide

omit [CharP K 2] [FiniteDimensional F2 K] in
/-- In degree two, the finite-field trace is `x + x²`. -/
theorem trace_eq_self_add_sq_of_card_four (hcard : Nat.card K = 4) (x : K) :
    algebraMap F2 K (Algebra.trace F2 K x) = x + x ^ 2 := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow,
    finrank_eq_two_of_card_four hcard]
  simp [Finset.sum_range_succ, Nat.card_eq_fintype_card, ZMod.card]

/-- Coordinates in the ordered basis `(c, 1)`. -/
def planeToField (c : K) : Plane →ₗ[F2] K where
  toFun x := x.1 • c + x.2 • (1 : K)
  map_add' x y := by
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    simp [add_smul]
    abel
  map_smul' r x := by
    rcases x with ⟨x₁, x₂⟩
    simp [mul_smul, smul_add]

omit [Finite K] [CharP K 2] [FiniteDimensional F2 K] in
theorem planeToField_injective (hcard : Nat.card K = 4) (c : K)
    (hc : Algebra.trace F2 K c = 1) : Function.Injective (planeToField c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rcases x with ⟨x₁, x₂⟩
  have ha : x₁ = 0 := by
    have htrace := congrArg (Algebra.trace F2 K) hx
    simpa [planeToField, map_add, map_smul,
      hc, trace_one_eq_zero_of_card_four hcard] using htrace
  have hb : x₂ = 0 := by
    have hmap : algebraMap F2 K x₂ = 0 := by
      simpa [planeToField, ha, Algebra.smul_def] using hx
    exact (algebraMap F2 K).injective
      (hmap.trans (map_zero (algebraMap F2 K)).symm)
  simp [ha, hb]

omit [Finite K] [CharP K 2] [FiniteDimensional F2 K] in
theorem planeToField_bijective (hcard : Nat.card K = 4) (c : K)
    (hc : Algebra.trace F2 K c = 1) : Function.Bijective (planeToField c) := by
  apply (Fintype.bijective_iff_injective_and_card (planeToField c)).2
  have hcard' : Fintype.card K = 4 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  exact ⟨planeToField_injective hcard c hc, by rw [hcard']; decide⟩

/-- The trace-one scale and one form a basis of the cardinality-four field. -/
noncomputable def planeToFieldEquiv (hcard : Nat.card K = 4) (c : K)
    (hc : Algebra.trace F2 K c = 1) : Plane ≃ₗ[F2] K :=
  LinearEquiv.ofBijective (planeToField c)
    (planeToField_bijective hcard c hc)

omit [Finite K] [CharP K 2] [FiniteDimensional F2 K] [Fintype K] in
theorem trace_one_scale_ne_zero (c : K)
    (hc : Algebra.trace F2 K c = 1) : c ≠ 0 := by
  intro h
  rw [h, map_zero] at hc
  exact zero_ne_one hc

omit [CharP K 2] [FiniteDimensional F2 K] in
theorem trace_one_scale_square (hcard : Nat.card K = 4) (c : K)
    (hc : Algebra.trace F2 K c = 1) : c ^ 2 = c + 1 := by
  have hc' := congrArg (algebraMap F2 K) hc
  rw [trace_eq_self_add_sq_of_card_four hcard] at hc'
  simp only [map_one] at hc'
  calc
    c ^ 2 = 0 + c ^ 2 := by simp
    _ = (c + c) + c ^ 2 := by rw [Extension.add_self_eq_zero]
    _ = c + (c + c ^ 2) := by abel
    _ = c + 1 := by rw [hc']

omit [Finite K] [CharP K 2] [FiniteDimensional F2 K] in
theorem trace_one_scale_cube (hcard : Nat.card K = 4) (c : K)
    (hc : Algebra.trace F2 K c = 1) : c ^ 3 = 1 := by
  have hcard' : Fintype.card K = 4 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have h := FiniteField.pow_card_sub_one_eq_one c
    (trace_one_scale_ne_zero c hc)
  simpa [hcard'] using h

omit [FiniteDimensional F2 K] [Fintype K] in
theorem goldHalfPolar_scale_scale (hcard : Nat.card K = 4) (c : K)
    (hc : Algebra.trace F2 K c = 1) : goldHalfPolar 1 c c c = 1 := by
  rw [goldHalfPolar_diagonal]
  exact goldQuadratic_one_eq_one_of_card_four hcard c hc
    (trace_one_scale_ne_zero c hc)

omit [FiniteDimensional F2 K] in
theorem goldHalfPolar_scale_one (hcard : Nat.card K = 4) (c : K)
    (hc : Algebra.trace F2 K c = 1) : goldHalfPolar 1 c c 1 = 1 := by
  rw [goldHalfPolar_apply]
  simp only [pow_one, one_pow, mul_one]
  rw [show c * c = c ^ 2 by ring, trace_one_scale_square hcard c hc,
    map_add, hc, trace_one_eq_zero_of_card_four hcard]
  decide

omit [Finite K] [FiniteDimensional F2 K] in
theorem goldHalfPolar_one_scale (hcard : Nat.card K = 4) (c : K)
    (hc : Algebra.trace F2 K c = 1) : goldHalfPolar 1 c 1 c = 0 := by
  rw [goldHalfPolar_apply]
  simp only [pow_one]
  rw [show c * 1 * c ^ 2 = c ^ 3 by ring,
    trace_one_scale_cube hcard c hc, trace_one_eq_zero_of_card_four hcard]

omit [Finite K] [FiniteDimensional F2 K] [Fintype K] in
theorem goldHalfPolar_one_one (c : K) (hc : Algebra.trace F2 K c = 1) :
    goldHalfPolar 1 c 1 1 = 1 := by
  simp [goldHalfPolar_apply, hc]

theorem f2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 :=
  eq_zero_or_one_of_sq_eq_self (ZMod.pow_card x)

omit [FiniteDimensional F2 K] in
theorem goldHalfPolar_scale_scale_add_one (hcard : Nat.card K = 4) (c : K)
    (hc : Algebra.trace F2 K c = 1) : goldHalfPolar 1 c c (c + 1) = 0 := by
  rw [map_add, goldHalfPolar_scale_scale hcard c hc,
    goldHalfPolar_scale_one hcard c hc]
  decide

omit [Finite K] [FiniteDimensional F2 K] in
theorem goldHalfPolar_one_scale_add_one (hcard : Nat.card K = 4) (c : K)
    (hc : Algebra.trace F2 K c = 1) : goldHalfPolar 1 c 1 (c + 1) = 1 := by
  rw [map_add, goldHalfPolar_one_scale hcard c hc, goldHalfPolar_one_one c hc]
  decide

omit [FiniteDimensional F2 K] in
/-- In the basis `(c, 1)`, the actual trace Gold cocycle is exactly the
coordinate anisotropic cocycle. -/
theorem goldHalfPolar_planeToField (hcard : Nat.card K = 4) (c : K)
    (hc : Algebra.trace F2 K c = 1) (x y : Plane) :
    goldHalfPolar 1 c (planeToField c x) (planeToField c y) =
      q8HalfPolar x y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  rcases f2_eq_zero_or_one x₁ with rfl | rfl <;>
    rcases f2_eq_zero_or_one x₂ with rfl | rfl <;>
    rcases f2_eq_zero_or_one y₁ with rfl | rfl <;>
    rcases f2_eq_zero_or_one y₂ with rfl | rfl
  all_goals norm_num [planeToField, q8HalfPolar,
    goldHalfPolar_scale_scale hcard c hc, goldHalfPolar_scale_one hcard c hc,
    goldHalfPolar_one_scale hcard c hc, goldHalfPolar_one_one c hc,
    goldHalfPolar_scale_scale_add_one hcard c hc,
    goldHalfPolar_one_scale_add_one hcard c hc,
    show (2 : F2) = 0 by decide, show (3 : F2) = 1 by decide]
  all_goals decide

/-- A linear coordinate change preserving the half-polar cocycle induces a
group isomorphism of the associated central extensions. -/
def extensionMulEquivOfLinearEquiv
    {V W : Type*} [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W]
    (phi : HalfPolar V) (psi : HalfPolar W) (e : V ≃ₗ[F2] W)
    (h : ∀ x y, psi (e x) (e y) = phi x y) :
    Extension phi ≃* Extension psi where
  toFun p := ⟨p.central, e p.vector⟩
  invFun p := ⟨p.central, e.symm p.vector⟩
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_mul' p q := by
    ext
    · simp only [Extension.mul_central]
      rw [h]
    · simp only [Extension.mul_vector, map_add]

/-- The coordinate cell is isomorphic to the actual trace Gold extension. -/
noncomputable def q8CellMulEquivGold
    (hcard : Nat.card K = 4) (c : K) (hc : Algebra.trace F2 K c = 1) :
    Q8Cell ≃* GoldExtension (K := K) 1 c :=
  extensionMulEquivOfLinearEquiv q8HalfPolar (goldHalfPolar 1 c)
    (planeToFieldEquiv hcard c hc) (goldHalfPolar_planeToField hcard c hc)

/-- The actual trace Gold extension over any cardinality-four field, at any
trace-one scale, is Mathlib's quaternion group of order eight. -/
noncomputable def goldF4MulEquivQuaternion
    (hcard : Nat.card K = 4) (c : K) (hc : Algebra.trace F2 K c = 1) :
    GoldExtension (K := K) 1 c ≃* QuaternionGroup 2 :=
  (q8CellMulEquivGold hcard c hc).symm.trans q8CellMulEquivQuaternion

end GoldQ8Bridge

/-! A completely discharged instance on Mathlib's canonical field `GF(4)`. -/

abbrev CanonicalF4 := GaloisField 2 2

local instance : Fintype CanonicalF4 := Fintype.ofFinite CanonicalF4

theorem canonicalF4_card : Nat.card CanonicalF4 = 4 := by
  simpa using GaloisField.card 2 2 (by decide : (2 : ℕ) ≠ 0)

/-- A chosen trace-one element of Mathlib's canonical `GF(4)`. -/
noncomputable def canonicalTraceOne : CanonicalF4 :=
  Classical.choose (Algebra.trace_surjective F2 CanonicalF4 (1 : F2))

theorem canonicalTraceOne_trace :
    Algebra.trace F2 CanonicalF4 canonicalTraceOne = 1 :=
  Classical.choose_spec (Algebra.trace_surjective F2 CanonicalF4 (1 : F2))

/-- Gap-free concrete endpoint: the trace Gold extension on Mathlib's
canonical `GF(4)` is explicitly isomorphic to `QuaternionGroup 2`. -/
noncomputable def canonicalGoldF4MulEquivQuaternion :
    GoldExtension (K := CanonicalF4) 1 canonicalTraceOne ≃*
      QuaternionGroup 2 :=
  goldF4MulEquivQuaternion canonicalF4_card canonicalTraceOne
    canonicalTraceOne_trace

end Ogdoad.GoldExtraspecialTrace
