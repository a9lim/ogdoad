import Mathlib

/-!
# Shared binary scalar facts

This module owns the elementary `ZMod 2` interface used across the quadratic-
form, FIFO, Gold, Witt-realization, and nim-multiplication developments.  These
facts are algebraic infrastructure, not part of any one paper's formal surface.
-/

namespace Ogdoad

/-- The common binary coefficient field used throughout the formal project. -/
abbrev F2 := ZMod 2

/-- A nonzero binary scalar is the unit bit. -/
theorem zmod2_eq_one_of_ne_zero (x : F2) (hx : x ≠ 0) : x = 1 := by
  apply ZMod.val_injective
  have hxval : x.val ≠ 0 := by
    intro h
    exact hx ((ZMod.val_eq_zero x).mp h)
  have hxlt : x.val < 2 := x.val_lt
  change x.val = 1
  omega

/-- A binary scalar different from the unit bit is zero. -/
theorem zmod2_eq_zero_of_ne_one (x : F2) (hx : x ≠ 1) : x = 0 := by
  by_contra hx0
  exact hx (zmod2_eq_one_of_ne_zero x hx0)

/-- Every binary scalar is idempotent. -/
theorem zmod2_sq_eq_self (x : F2) : x * x = x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [zmod2_eq_one_of_ne_zero x hx]
    simp

/-- Distinct binary scalars differ by the unit bit. -/
theorem zmod2_add_one_add_eq_zero_of_ne (x y : F2) (hxy : x ≠ y) :
    x + 1 + y = 0 := by
  have hsum0 : x + y ≠ 0 := by
    intro h
    have : x = y := by
      calc
        x = x + (y + y) := by rw [CharTwo.add_self_eq_zero, add_zero]
        _ = (x + y) + y := by abel
        _ = y := by rw [h, zero_add]
    exact hxy this
  have hsum1 : x + y = 1 := zmod2_eq_one_of_ne_zero _ hsum0
  calc
    x + 1 + y = (x + y) + 1 := by abel
    _ = 0 := by rw [hsum1, CharTwo.add_self_eq_zero]

end Ogdoad
