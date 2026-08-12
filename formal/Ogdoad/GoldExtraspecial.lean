import Mathlib.Algebra.Module.ZMod

/-!
# The game-native Gold--Heisenberg extension

This file kernel-checks the load-bearing algebra of the game-native
extraspecial-extension construction.  A biadditive ``half-polar'' map
`phi : V -> V -> F2` defines a central extension on `F2 x V`; its diagonal is
the squaring form and its symmetrization is the commutator form.  The paper
specializes

`phi_a x y = Tr (x * y^(2^a))`

on a finite nimber field.  Turning-Corners multiplication, Frobenius, and
disjunctive trace build that specialization from game operations.  Lean checks
the universal cocycle/group argument here; it does not re-encode finite nimber
arithmetic or the trace implementation.
-/

noncomputable section

-- The extension declarations share one ambient `F2`-module context; several
-- cocycle-only lemmas need only its underlying additive group.
set_option linter.unusedSectionVars false

namespace Ogdoad.GoldExtraspecial

abbrev F2 := ZMod 2

@[simp] theorem two_eq_zero : (2 : F2) = 0 := by decide

variable {V : Type*} [AddCommGroup V] [Module F2 V]

/-- A biadditive half-polar map.  Its diagonal will be the quadratic form. -/
abbrev HalfPolar (V : Type*) [AddCommGroup V] := V →+ V →+ F2

/-- The carrier of the central extension attached to `phi`. -/
@[ext] structure Extension (phi : HalfPolar V) where
  central : F2
  vector : V
deriving DecidableEq

namespace Extension

variable (phi : HalfPolar V)

/-- Every `F2`-module has exponent two additively. -/
@[simp] theorem add_self_eq_zero (x : V) : x + x = 0 := by
  have htwo : (1 : F2) + 1 = 0 := by decide
  calc
    x + x = (1 : F2) • x + (1 : F2) • x := by simp
    _ = ((1 : F2) + 1) • x := (add_smul 1 1 x).symm
    _ = 0 := by rw [htwo, zero_smul]

/-- Bilinearity is exactly the normalized two-cocycle identity. -/
theorem cocycle (x y w : V) :
    phi x y + phi (x + y) w = phi y w + phi x (y + w) := by
  rw [phi.map_add, AddMonoidHom.add_apply, (phi x).map_add]
  abel

/-- Multiplication by the bilinear two-cocycle `phi`. -/
def mul (p q : Extension phi) : Extension phi :=
  ⟨p.central + q.central + phi p.vector q.vector, p.vector + q.vector⟩

/-- The identity of the extension. -/
def one : Extension phi := ⟨0, 0⟩

/-- Inversion in the extension. -/
def inv (p : Extension phi) : Extension phi :=
  ⟨p.central + phi p.vector p.vector, p.vector⟩

instance : Mul (Extension phi) := ⟨mul phi⟩
instance : One (Extension phi) := ⟨one phi⟩
instance : Inv (Extension phi) := ⟨inv phi⟩

@[simp] theorem mul_central (p q : Extension phi) :
    (p * q).central = p.central + q.central + phi p.vector q.vector := rfl

@[simp] theorem mul_vector (p q : Extension phi) :
    (p * q).vector = p.vector + q.vector := rfl

@[simp] theorem one_central : (1 : Extension phi).central = 0 := rfl
@[simp] theorem one_vector : (1 : Extension phi).vector = 0 := rfl

@[simp] theorem inv_central (p : Extension phi) :
    p⁻¹.central = p.central + phi p.vector p.vector := rfl

@[simp] theorem inv_vector (p : Extension phi) : p⁻¹.vector = p.vector := rfl

theorem mul_assoc (p q r : Extension phi) : p * q * r = p * (q * r) := by
  ext
  · simp only [mul_central, mul_vector]
    rw [phi.map_add, AddMonoidHom.add_apply, (phi p.vector).map_add]
    ring
  · simp only [mul_vector]
    exact add_assoc _ _ _

@[simp] theorem one_mul (p : Extension phi) : 1 * p = p := by
  ext <;> simp

@[simp] theorem mul_one (p : Extension phi) : p * 1 = p := by
  ext <;> simp

@[simp] theorem inv_mul (p : Extension phi) : p⁻¹ * p = 1 := by
  ext
  · simp only [mul_central, inv_central, inv_vector, one_central]
    ring_nf
    simp
  · simpa only [mul_vector, inv_vector, one_vector] using
      add_self_eq_zero p.vector

instance : Group (Extension phi) where
  mul_assoc := mul_assoc phi
  one_mul := one_mul phi
  mul_one := mul_one phi
  inv_mul_cancel := inv_mul phi

/-- The distinguished central involution. -/
def center : Extension phi := ⟨1, 0⟩

/-- Projection to the elementary abelian quotient. -/
def quotient (p : Extension phi) : V := p.vector

theorem quotient_surjective : Function.Surjective (quotient phi) := by
  intro x
  exact ⟨⟨0, x⟩, rfl⟩

@[simp] theorem center_mul_central (p : Extension phi) :
    (center phi * p).central = p.central + 1 := by
  simp [center, add_comm]

@[simp] theorem center_mul_vector (p : Extension phi) :
    (center phi * p).vector = p.vector := by
  simp [center]

@[simp] theorem mul_center_central (p : Extension phi) :
    (p * center phi).central = p.central + 1 := by
  simp [center]

@[simp] theorem mul_center_vector (p : Extension phi) :
    (p * center phi).vector = p.vector := by
  simp [center]

theorem center_commutes (p : Extension phi) : center phi * p = p * center phi := by
  ext <;> simp only [center_mul_central, mul_center_central,
    center_mul_vector, mul_center_vector]

theorem center_ne_one : center phi ≠ 1 := by
  intro h
  have h' := congrArg central h
  norm_num [center] at h'

@[simp] theorem center_square : center phi * center phi = 1 := by
  ext
  · simp only [mul_central, center, one_central]
    simp only [map_zero]
    ring_nf
    simp
  · simp only [mul_vector, center, one_vector, add_zero]

/-- The two points over a quotient coordinate differ by the center. -/
theorem center_retags (s : F2) (x : V) :
    center phi * (⟨s, x⟩ : Extension phi) = ⟨s + 1, x⟩ := by
  ext
  · exact center_mul_central phi ⟨s, x⟩
  · exact center_mul_vector phi ⟨s, x⟩

/-- Squaring reads the diagonal of the half-polar map. -/
theorem square (p : Extension phi) :
    p * p = ⟨phi p.vector p.vector, 0⟩ := by
  ext
  · simp only [mul_central]
    ring_nf
    simp
  · simpa only [mul_vector] using add_self_eq_zero p.vector

/-- Swapping two factors costs the symmetrization of `phi`, i.e. the polar
commutator bit.  This form avoids any convention about commutator order. -/
theorem swap_defect (p q : Extension phi) :
    p * q =
      (⟨phi p.vector q.vector + phi q.vector p.vector, 0⟩ : Extension phi) *
        (q * p) := by
  ext
  · simp only [mul_central, mul_vector, map_zero, AddMonoidHom.zero_apply]
    ring_nf
    simp
  · simp only [mul_vector, zero_add]
    exact add_comm _ _

/-- An element is central exactly when its quotient coordinate lies in the
radical of the symmetrized half-polar form. -/
theorem isCentral_iff (p : Extension phi) :
    (∀ q : Extension phi, p * q = q * p) ↔
      ∀ y : V, phi p.vector y + phi y p.vector = 0 := by
  constructor
  · intro hp y
    have h := congrArg central (hp ⟨0, y⟩)
    simp only [mul_central] at h
    have heq : phi p.vector y = phi y p.vector := by
      apply add_left_cancel (a := p.central)
      simpa only [add_zero, zero_add] using h
    rw [heq]
    exact add_self_eq_zero (phi y p.vector)
  · intro hp q
    ext
    · simp only [mul_central]
      have h := hp q.vector
      have heq : phi p.vector q.vector = phi q.vector p.vector := by
        calc
          phi p.vector q.vector = phi p.vector q.vector + 0 := by simp
          _ = phi p.vector q.vector +
              (phi q.vector p.vector + phi q.vector p.vector) := by
                rw [add_self_eq_zero]
          _ = (phi p.vector q.vector + phi q.vector p.vector) +
              phi q.vector p.vector := by abel
          _ = phi q.vector p.vector := by rw [h]; simp
      rw [heq]
      ac_rfl
    · simp only [mul_vector]
      exact add_comm _ _

/-- Nonzero symmetrization makes the extension noncommutative. -/
theorem noncommutative_of_polar_ne_zero {x y : V}
    (h : phi x y + phi y x ≠ 0) :
    (⟨0, x⟩ : Extension phi) * ⟨0, y⟩ ≠ ⟨0, y⟩ * ⟨0, x⟩ := by
  intro hcomm
  have hc := congrArg central hcomm
  simp only [mul_central, zero_add] at hc
  apply h
  rw [hc]
  exact add_self_eq_zero (V := F2) (phi y x)

/-- A diagonal-one lift has order four: its square is the nontrivial center. -/
theorem order_four_of_diagonal_one {x : V} (h : phi x x = 1) :
    let p : Extension phi := ⟨0, x⟩
    p * p = center phi ∧ p * p ≠ 1 ∧ (p * p) * (p * p) = 1 := by
  dsimp
  constructor
  · rw [square, h]
    rfl
  constructor
  · rw [square, h]
    exact center_ne_one phi
  · have hsquare :
        (⟨0, x⟩ : Extension phi) * ⟨0, x⟩ = center phi := by
      rw [square, h]
      rfl
    rw [hsquare]
    exact center_square phi

end Extension

end Ogdoad.GoldExtraspecial
