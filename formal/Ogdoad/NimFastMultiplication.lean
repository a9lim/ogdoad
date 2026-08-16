import Ogdoad.Algebra.ArtinSchreier

/-!
# Fast multiplication in canonical nim coordinates: algebraic glue

The asymptotic algorithms used in the paper live outside Lean.  This module
checks the load-bearing algebraic identities in their specialization to the
literal characteristic-two Conway tower:

* an Artin--Schreier generator may be shifted by a downstairs solution of the
  source difference;
* relative trace one carries the source trace upward;
* the direct quadratic product has the stated three-variable-product split;
* the corresponding two-coordinate basis change is an involution and evaluates
  to the same field element;
* ring equivalences preserve the canonical tower equations; and
* transporting multiplication through a ring equivalence returns exactly the
  original basis coordinates.

No complexity claim, concrete nimber construction, or De Feo--Schost algorithm
is formalized here.  The paper entry point imports the reusable finite-field
trace-one irreducibility criterion from `Ogdoad.Algebra.ArtinSchreier`.
-/

namespace Ogdoad.NimFastMultiplication

noncomputable section

open scoped CharTwo

section ArtinSchreierShift

variable {K : Type*} [CommRing K] [CharP K 2]

/-- If `u` has Artin--Schreier source `g` and `delta` has source `a + g`,
then the shifted generator `u + delta` has source `a`. -/
theorem shifted_generator_source (u delta g a : K)
    (hu : u ^ 2 + u = g) (hdelta : delta ^ 2 + delta = a + g) :
    (u + delta) ^ 2 + (u + delta) = a := by
  rw [ArtinSchreier.add, hu, hdelta]
  calc
    g + (a + g) = a + (g + g) := by ac_rfl
    _ = a := by rw [CharTwo.add_self_eq_zero, add_zero]

/-- Change the two coefficients for the generator replacement
`s = u + delta`: `A + B*s = (A + B*delta) + B*u`. -/
def shiftPair (delta : K) (p : K × K) : K × K :=
  (p.1 + p.2 * delta, p.2)

/-- In characteristic two the coefficient change for `u <-> u + delta` is its
own inverse. -/
@[simp]
theorem shiftPair_involutive (delta : K) (p : K × K) :
    shiftPair delta (shiftPair delta p) = p := by
  rcases p with ⟨A, B⟩
  apply Prod.ext
  · change (A + B * delta) + B * delta = A
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rfl

/-- Evaluation of a pair of coefficients in a quadratic generator. -/
def evalPair (u : K) (p : K × K) : K := p.1 + p.2 * u

omit [CharP K 2] in
/-- The affine coefficient shift represents the same field element. -/
theorem evalPair_shift (u delta : K) (p : K × K) :
    evalPair (u + delta) p = evalPair u (shiftPair delta p) := by
  rcases p with ⟨A, B⟩
  simp only [evalPair, shiftPair]
  ring

end ArtinSchreierShift

section TraceCarry

variable {F E L : Type*} [Field F] [Field E] [Field L]
  [Algebra F E] [Algebra E L] [Algebra F L]
  [IsScalarTower F E L]
  [FiniteDimensional F E] [FiniteDimensional E L]

/-- If a new quadratic generator has relative trace one, multiplying it by
the old source preserves absolute trace. -/
theorem trace_carry (a : E) (u : L)
    (hu : Algebra.trace E L u = 1) :
    Algebra.trace F L (algebraMap E L a * u) =
      Algebra.trace F E a := by
  rw [← Algebra.trace_trace (R := F) (S := E) (T := L)]
  rw [← Algebra.smul_def, LinearMap.map_smul, hu, smul_eq_mul, mul_one]

end TraceCarry

section ThreeMultiplySplit

variable {K : Type*} [CommRing K] [CharP K 2]

/-- Karatsuba form of multiplication across one canonical quadratic level.
The three variable products are `x0*y0`, `x1*y1`, and
`(x0+x1)*(y0+y1)`; multiplication by the fixed source `a` is linear data. -/
theorem canonical_quadratic_mul_split (u a x0 x1 y0 y1 : K)
    (hu : u ^ 2 + u = a) :
    (x0 + u * x1) * (y0 + u * y1) =
      (x0 * y0 + a * (x1 * y1)) +
        u * ((x0 + x1) * (y0 + y1) + x0 * y0) := by
  rw [← hu]
  ring_nf
  simp

end ThreeMultiplySplit

section TowerEquations

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The source in the literal Conway quadratic tower. -/
def towerRhs (c : Nat → A) (i : Nat) : A :=
  ∏ j ∈ Finset.range i, c j

/-- Abstract form of the canonical equations `c_i^2 + c_i = prod_{j<i} c_j`. -/
def IsCanonicalTower (c : Nat → A) : Prop :=
  ∀ i, c i ^ 2 + c i = towerRhs c i

/-- A ring equivalence carries every canonical tower equation to the
corresponding equation for the image generators. -/
theorem IsCanonicalTower.map (sigma : A ≃+* B) {c : Nat → A}
    (h : IsCanonicalTower c) :
    IsCanonicalTower (fun i => sigma (c i)) := by
  intro i
  simpa [towerRhs] using congrArg sigma (h i)

end TowerEquations

section CoordinateTransport

variable {F A B I : Type*}
  [Field F] [Ring A] [Ring B] [Algebra F A]

/-- Multiply basis-coordinate vectors by transporting their decoded elements
through a ring equivalence and returning through the same equivalence. -/
noncomputable def transportedCoordinateMul
    (basis : Module.Basis I F A) (sigma : A ≃+* B)
    (x y : I →₀ F) : I →₀ F :=
  basis.repr
    (sigma.symm
      (sigma (basis.repr.symm x) * sigma (basis.repr.symm y)))

/-- Transported multiplication returns exactly the coordinates of the product
in the original basis.  This is the formal exact-output boundary used for the
canonical nim word after the fast-basis multiplication. -/
theorem transportedCoordinateMul_eq
    (basis : Module.Basis I F A) (sigma : A ≃+* B)
    (x y : I →₀ F) :
    transportedCoordinateMul basis sigma x y =
      basis.repr (basis.repr.symm x * basis.repr.symm y) := by
  simp [transportedCoordinateMul]

end CoordinateTransport

end

end Ogdoad.NimFastMultiplication
