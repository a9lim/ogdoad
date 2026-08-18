import Ogdoad.WittRealizationExact
import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Concrete quasilinear absorption in characteristic two

The abstract cancellation theorem in `WittRealizationExact` assumes an
absorption relation.  This file proves the actual quadratic-form isometry
used by the paper:

```text
<c> orthogonal-sum <c>  isometric-to  <c> orthogonal-sum <0>.
```

The isometry is the involutive shear `(x,y) |-> (x+y,y)`.  Consequently the
paper's obstruction is no longer resting on an unformalized coordinate
change; only passage to a chosen isometry-class monoid is external.
-/

namespace Ogdoad.WittSingularBoundary

open scoped CharTwo

noncomputable section

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [CharP F 2]

/-- The one-dimensional quasilinear form `<c>`. -/
def quasilinearLine (c : F) : QuadraticForm F F :=
  c • QuadraticMap.sq

@[simp]
theorem quasilinearLine_apply (c x : F) :
    quasilinearLine c x = c * x ^ 2 := by
  simp [quasilinearLine, QuadraticMap.sq_apply, pow_two]

/-- The characteristic-two shear `(x,y) |-> (x+y,y)`, which is its own
inverse. -/
def shear : (F × F) ≃ₗ[F] (F × F) where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 + p.2, p.2)
  left_inv := by
    intro p
    ext <;> simp
  right_inv := by
    intro p
    ext <;> simp
  map_add' := by
    intro p q
    ext <;> simp <;> abel
  map_smul' := by
    intro a p
    ext <;> simp [mul_add]

@[simp]
theorem shear_apply (p : F × F) : shear p = (p.1 + p.2, p.2) :=
  rfl

/-- Concrete quasilinear absorption isometry. -/
def absorptionIsometry (c : F) :
    ((quasilinearLine c).prod (quasilinearLine c)).IsometryEquiv
      ((quasilinearLine c).prod (quasilinearLine 0)) where
  toLinearEquiv := shear
  map_app' := by
    intro p
    simp [QuadraticMap.prod_apply, CharTwo.add_sq]
    ring

theorem absorption_value_identity (c x y : F) :
    quasilinearLine c x + quasilinearLine c y =
      quasilinearLine c (x + y) + quasilinearLine 0 y := by
  simp [CharTwo.add_sq]
  ring

end

end Ogdoad.WittSingularBoundary
