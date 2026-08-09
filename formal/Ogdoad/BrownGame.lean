import Mathlib

/-!
# The Brown-phase obstruction for short-game values

This file formalizes three algebraic layers of the `over` problem.  First,
2-divisibility kills every ambient Brown-compatible refinement with values in
an exponent-four group.  Second, the abelian cyclic extension
`Z/4 -> Z/8 -> Z/2` shows that a local odd Brown line exists only relative to a
chosen section.  Third, every Brown refinement on an exponent-two source
splits canonically as `q = lift(ell) + 2Q`, with an ordinary characteristic-two
quadratic form `Q`, and the converse recovers the refinement pointwise.

The external theorem that the additive group of short games is 2-divisible
remains source-pinned; it is not encoded as an axiom here.
-/

namespace Ogdoad.BrownGame

noncomputable section

/-- Multiplication by two is surjective on an additive group. -/
def TwoDivisible (A : Type*) [AddCommGroup A] : Prop :=
  ∀ x : A, ∃ y : A, 2 • y = x

variable {A C : Type*} [AddCommGroup A] [AddCommGroup C]

/-- An additive-group version of a Brown quadratic refinement.  In the
classical case `C = ZMod 4`; `polar` is the embedded `2 * b`, so all its values
have order at most two. -/
structure BrownDatum (A C : Type*) [AddCommGroup A] [AddCommGroup C] where
  quadratic : A → C
  polar : A →+ A →+ C
  polar_two_torsion : ∀ x y, 2 • polar x y = 0
  polarization : ∀ x y, quadratic (x + y) = quadratic x + quadratic y + polar x y

/-- Two-divisibility kills every exponent-two biadditive polar defect. -/
theorem BrownDatum.polar_eq_zero (datum : BrownDatum A C)
    (hdiv : TwoDivisible A) (x y : A) :
    datum.polar x y = 0 := by
  obtain ⟨z, rfl⟩ := hdiv x
  calc
    datum.polar (2 • z) y = 2 • datum.polar z y := by simp
    _ = 0 := datum.polar_two_torsion z y

/-- Once the polar defect vanishes, the quadratic function is additive. -/
theorem BrownDatum.quadratic_add (datum : BrownDatum A C)
    (hdiv : TwoDivisible A) (x y : A) :
    datum.quadratic (x + y) = datum.quadratic x + datum.quadratic y := by
  rw [datum.polarization, datum.polar_eq_zero hdiv]
  simp

/-- A Brown datum on a two-divisible source is an additive homomorphism after
its polar defect has collapsed. -/
def BrownDatum.toAddMonoidHom (datum : BrownDatum A C)
    (hdiv : TwoDivisible A) : A →+ C where
  toFun := datum.quadratic
  map_zero' := by
    have h := datum.quadratic_add hdiv (0 : A) 0
    have h' : datum.quadratic 0 + 0 =
        datum.quadratic 0 + datum.quadratic 0 := by
      simpa using h
    exact (add_left_cancel h').symm
  map_add' := datum.quadratic_add hdiv

/-- The complete abstract obstruction.  An exponent-four target cannot carry
a nonzero Brown quadratic refinement of a two-divisible additive group. -/
theorem BrownDatum.quadratic_eq_zero (datum : BrownDatum A C)
    (hdiv : TwoDivisible A) (hexp4 : ∀ c : C, 4 • c = 0) (x : A) :
    datum.quadratic x = 0 := by
  obtain ⟨y, hy⟩ := hdiv x
  obtain ⟨z, hz⟩ := hdiv y
  have hfour : 4 • z = x := by
    rw [show 4 = 2 * 2 by norm_num, mul_nsmul, hz, hy]
  let qhom := datum.toAddMonoidHom hdiv
  change qhom x = 0
  rw [← hfour, map_nsmul]
  exact hexp4 (qhom z)

/-- Specialization to the classical Brown target `ZMod 4`. -/
theorem brown_zmod_four_trivial (datum : BrownDatum A (ZMod 4))
    (hdiv : TwoDivisible A) (x : A) :
    datum.quadratic x = 0 := by
  apply datum.quadratic_eq_zero hdiv
  intro c
  have hfour : (4 : ZMod 4) = 0 := by decide
  simp [nsmul_eq_mul, hfour]

/-- A two-divisible group has no nonzero additive quotient of exponent two.
This rules out a nontrivial `F₂` Brown module as a quotient or homomorphic
image of all short-game values; it does not kill root-incomplete exponent-two
subgroups. -/
theorem addMonoidHom_eq_zero_of_twoDivisible {B : Type*} [AddCommGroup B]
    (hdiv : TwoDivisible A) (hexp2 : ∀ b : B, 2 • b = 0)
    (f : A →+ B) : f = 0 := by
  ext x
  obtain ⟨y, rfl⟩ := hdiv x
  rw [map_nsmul, hexp2]
  rfl

/-! ## Sharpness: a bare abelian extension is not the obstruction

The cyclic extension `0 → Z/4 → Z/8 → Z/2 → 0` carries the odd Brown line
after a section has been chosen.  Changing the lift changes its double, so the
bare extension does not determine the Brown refinement.  This is why the
global theorem above uses ambient coherence of the quadratic function itself,
not a false claim that every Brown central extension must be noncommutative.
-/

/-- The injective central map `Z/4 → Z/8`, `a ↦ 2a`. -/
def z4Center : ZMod 4 →+ ZMod 8 where
  toFun a := (2 * a.val : ℕ)
  map_zero' := by decide
  map_add' a b := by
    fin_cases a <;> fin_cases b <;> decide

/-- The quotient map `Z/8 → Z/2`. -/
def z8Quotient : ZMod 8 →+ ZMod 2 :=
  (ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)).toAddMonoidHom

/-- The standard representatives `0,1` of `Z/8 → Z/2`. -/
def z8Section (x : ZMod 2) : ZMod 8 := x.val

/-- The odd Brown line `<1>`. -/
def oddLine (x : ZMod 2) : ZMod 4 := x.val

/-- Its full `Z/4` polar correction. -/
def oddLinePolar (x y : ZMod 2) : ZMod 4 := 2 * x.val * y.val

theorem oddLine_polarization (x y : ZMod 2) :
    oddLine (x + y) = oddLine x + oddLine y + oddLinePolar x y := by
  fin_cases x <;> fin_cases y <;> decide

theorem z4Center_injective : Function.Injective z4Center := by
  let half : ZMod 8 → ZMod 4 := fun x => ((x.val / 2 : ℕ) : ZMod 4)
  apply Function.LeftInverse.injective (g := half)
  intro a
  fin_cases a <;> decide

theorem z8Quotient_surjective : Function.Surjective z8Quotient := by
  intro x
  exact ⟨z8Section x, by fin_cases x <;> decide⟩

theorem z8_exact (x : ZMod 8) :
    z8Quotient x = 0 ↔ ∃ a, z4Center a = x := by
  fin_cases x <;> decide

theorem z8_section_right_inverse (x : ZMod 2) :
    z8Quotient (z8Section x) = x := by
  fin_cases x <;> decide

/-- Doubling the chosen lift is precisely the central odd Brown value. -/
theorem z8_double_section (x : ZMod 2) :
    2 • z8Section x = z4Center (oddLine x) := by
  fin_cases x <;> decide

/-- The same quotient element has lifts with different doubles. -/
theorem z8_double_not_fiber_invariant :
    z8Quotient (1 : ZMod 8) = z8Quotient (3 : ZMod 8) ∧
      2 • (1 : ZMod 8) ≠ 2 • (3 : ZMod 8) := by
  decide

theorem oddLine_polar_nonzero : oddLinePolar 1 1 ≠ 0 := by
  decide

/-- A kernel-checked abelian, section-framed model of the odd Brown line. -/
theorem odd_brown_line_has_abelian_cyclic_model :
    Function.Injective z4Center ∧
      Function.Surjective z8Quotient ∧
      (∀ x, z8Quotient x = 0 ↔ ∃ a, z4Center a = x) ∧
      (∀ x, z8Quotient (z8Section x) = x) ∧
      (∀ x, 2 • z8Section x = z4Center (oddLine x)) ∧
      oddLinePolar 1 1 ≠ 0 := by
  exact ⟨z4Center_injective, z8Quotient_surjective, z8_exact,
    z8_section_right_inverse, z8_double_section, oddLine_polar_nonzero⟩

end

/-! ## Canonical finite Brown decomposition

The remaining declarations prove, on any exponent-two additive source, the
canonical split `q = lift(ell) + 2 * Q`.  All scalar facts are closed `ZMod 2`
and `ZMod 4` decisions; no enumeration of vectors is used. -/

def doubleBit (a : ZMod 2) : ZMod 4 := (2 * a.val : ℕ)
def parity (a : ZMod 4) : ZMod 2 := a.val
def liftBit (a : ZMod 2) : ZMod 4 := a.val
def residualBit (a : ZMod 4) : ZMod 2 := ((a.val / 2 : ℕ) : ZMod 2)

theorem scalar_decomposition (a : ZMod 4) :
    a = liftBit (parity a) + doubleBit (residualBit a) := by
  exact (by decide : ∀ a : ZMod 4,
    a = liftBit (parity a) + doubleBit (residualBit a)) a

theorem parity_doubleBit (a : ZMod 2) : parity (doubleBit a) = 0 := by
  exact (by decide : ∀ a : ZMod 2, parity (doubleBit a) = 0) a

theorem parity_add (a b : ZMod 4) : parity (a + b) = parity a + parity b := by
  exact (by decide : ∀ a b : ZMod 4,
    parity (a + b) = parity a + parity b) a b

theorem parity_liftBit (a : ZMod 2) : parity (liftBit a) = a := by
  exact (by decide : ∀ a : ZMod 2, parity (liftBit a) = a) a

theorem residual_lift_double (a b : ZMod 2) :
    residualBit (liftBit a + doubleBit b) = b := by
  exact (by decide : ∀ a b : ZMod 2,
    residualBit (liftBit a + doubleBit b) = b) a b

theorem residual_brown_sum (a b : ZMod 4) (p : ZMod 2) :
    residualBit (a + b + doubleBit p) =
      residualBit a + residualBit b + p + parity a * parity b := by
  exact (by decide : ∀ a b : ZMod 4, ∀ p : ZMod 2,
    residualBit (a + b + doubleBit p) =
      residualBit a + residualBit b + p + parity a * parity b) a b p

theorem lift_carry (a b : ZMod 2) :
    liftBit (a + b) = liftBit a + liftBit b + doubleBit (a * b) := by
  exact (by decide : ∀ a b : ZMod 2,
    liftBit (a + b) = liftBit a + liftBit b + doubleBit (a * b)) a b

theorem brown_diagonal_scalar (a : ZMod 4) (p : ZMod 2) :
    0 = a + a + doubleBit p → p = parity a := by
  exact (by decide : ∀ a : ZMod 4, ∀ p : ZMod 2,
    0 = a + a + doubleBit p → p = parity a) a p

theorem recompose_scalar (e f u v p : ZMod 2) :
    liftBit (e + f) + doubleBit (u + v + p) =
      (liftBit e + doubleBit u) + (liftBit f + doubleBit v) +
        doubleBit (p + e * f) := by
  exact (by decide : ∀ e f u v p : ZMod 2,
    liftBit (e + f) + doubleBit (u + v + p) =
      (liftBit e + doubleBit u) + (liftBit f + doubleBit v) +
        doubleBit (p + e * f)) e f u v p

variable {V : Type*} [AddCommGroup V]

/-- A Brown refinement written with its `F₂` polar form. -/
structure BrownRefinement (V : Type*) [AddCommGroup V] where
  quadratic : V → ZMod 4
  polar : V → V → ZMod 2
  quadratic_zero : quadratic 0 = 0
  polarization : ∀ x y,
    quadratic (x + y) = quadratic x + quadratic y + doubleBit (polar x y)
  polar_add_left : ∀ x y z, polar (x + y) z = polar x z + polar y z
  polar_add_right : ∀ x y z, polar x (y + z) = polar x y + polar x z
  polar_symm : ∀ x y, polar x y = polar y x
  source_two : ∀ x : V, x + x = 0

/-- The canonical mod-two linear part. -/
def BrownRefinement.linearPart (q : BrownRefinement V) (x : V) : ZMod 2 :=
  parity (q.quadratic x)

/-- The residual ordinary quadratic part. -/
def BrownRefinement.classicalPart (q : BrownRefinement V) (x : V) : ZMod 2 :=
  residualBit (q.quadratic x)

/-- The corrected alternating polar form `b + ell tensor ell`. -/
def BrownRefinement.classicalPolar (q : BrownRefinement V)
    (x y : V) : ZMod 2 :=
  q.polar x y + q.linearPart x * q.linearPart y

theorem BrownRefinement.linearPart_zero (q : BrownRefinement V) :
    q.linearPart 0 = 0 := by
  simp [BrownRefinement.linearPart, q.quadratic_zero, parity]

theorem BrownRefinement.linearPart_add (q : BrownRefinement V) (x y : V) :
    q.linearPart (x + y) = q.linearPart x + q.linearPart y := by
  change parity (q.quadratic (x + y)) =
    parity (q.quadratic x) + parity (q.quadratic y)
  rw [q.polarization, parity_add, parity_add, parity_doubleBit, add_zero]

theorem BrownRefinement.decomposition (q : BrownRefinement V) (x : V) :
    q.quadratic x =
      liftBit (q.linearPart x) + doubleBit (q.classicalPart x) :=
  scalar_decomposition _

theorem BrownRefinement.classicalPart_zero (q : BrownRefinement V) :
    q.classicalPart 0 = 0 := by
  simp [BrownRefinement.classicalPart, q.quadratic_zero, residualBit]

theorem BrownRefinement.classicalPart_add (q : BrownRefinement V) (x y : V) :
    q.classicalPart (x + y) =
      q.classicalPart x + q.classicalPart y + q.classicalPolar x y := by
  change residualBit (q.quadratic (x + y)) =
    residualBit (q.quadratic x) + residualBit (q.quadratic y) +
      (q.polar x y + parity (q.quadratic x) * parity (q.quadratic y))
  rw [q.polarization]
  simpa [add_assoc] using residual_brown_sum
    (q.quadratic x) (q.quadratic y) (q.polar x y)

/-- Brown's forced diagonal identity `b(x,x) = q(x) mod 2`. -/
theorem BrownRefinement.polar_self (q : BrownRefinement V) (x : V) :
    q.polar x x = q.linearPart x := by
  apply brown_diagonal_scalar
  have h := q.polarization x x
  rw [q.source_two x, q.quadratic_zero] at h
  exact h

theorem BrownRefinement.classicalPolar_self (q : BrownRefinement V) (x : V) :
    q.classicalPolar x x = 0 := by
  rw [BrownRefinement.classicalPolar, q.polar_self]
  exact (by decide : ∀ a : ZMod 2, a + a * a = 0) (q.linearPart x)

theorem BrownRefinement.classicalPolar_add_left (q : BrownRefinement V)
    (x y z : V) :
    q.classicalPolar (x + y) z =
      q.classicalPolar x z + q.classicalPolar y z := by
  change q.polar (x + y) z + q.linearPart (x + y) * q.linearPart z =
    (q.polar x z + q.linearPart x * q.linearPart z) +
      (q.polar y z + q.linearPart y * q.linearPart z)
  rw [q.polar_add_left, q.linearPart_add, add_mul]
  abel

theorem BrownRefinement.classicalPolar_add_right (q : BrownRefinement V)
    (x y z : V) :
    q.classicalPolar x (y + z) =
      q.classicalPolar x y + q.classicalPolar x z := by
  change q.polar x (y + z) + q.linearPart x * q.linearPart (y + z) =
    (q.polar x y + q.linearPart x * q.linearPart y) +
      (q.polar x z + q.linearPart x * q.linearPart z)
  rw [q.polar_add_right, q.linearPart_add, mul_add]
  abel

theorem BrownRefinement.classicalPolar_symm (q : BrownRefinement V) (x y : V) :
    q.classicalPolar x y = q.classicalPolar y x := by
  rw [BrownRefinement.classicalPolar, BrownRefinement.classicalPolar,
    q.polar_symm, mul_comm]

/-- Ordinary characteristic-two quadratic data. -/
structure F2Quadratic (V : Type*) [AddCommGroup V] where
  quadratic : V → ZMod 2
  polar : V → V → ZMod 2
  quadratic_zero : quadratic 0 = 0
  polarization : ∀ x y,
    quadratic (x + y) = quadratic x + quadratic y + polar x y
  polar_add_left : ∀ x y z, polar (x + y) z = polar x z + polar y z
  polar_add_right : ∀ x y z, polar x (y + z) = polar x y + polar x z
  polar_symm : ∀ x y, polar x y = polar y x
  source_two : ∀ x : V, x + x = 0

/-- The decomposition lands in the ordinary characteristic-two quadratic
category, including an alternating polar form. -/
def BrownRefinement.classicalForm (q : BrownRefinement V) : F2Quadratic V where
  quadratic := q.classicalPart
  polar := q.classicalPolar
  quadratic_zero := q.classicalPart_zero
  polarization := q.classicalPart_add
  polar_add_left := q.classicalPolar_add_left
  polar_add_right := q.classicalPolar_add_right
  polar_symm := q.classicalPolar_symm
  source_two := q.source_two

/-- Converse construction `q = lift(ell) + 2Q`, with Brown polar
`b = B_Q + ell tensor ell`. -/
theorem brownRefinement_converse
    (ell : V → ZMod 2) (Q : F2Quadratic V)
    (hell0 : ell 0 = 0)
    (helladd : ∀ x y, ell (x + y) = ell x + ell y) :
    ∃ q : BrownRefinement V,
      (∀ x, q.quadratic x = liftBit (ell x) + doubleBit (Q.quadratic x)) ∧
      (∀ x y, q.polar x y = Q.polar x y + ell x * ell y) := by
  let q : BrownRefinement V :=
    { quadratic := fun x => liftBit (ell x) + doubleBit (Q.quadratic x)
      polar := fun x y => Q.polar x y + ell x * ell y
      quadratic_zero := by simp [hell0, Q.quadratic_zero, liftBit, doubleBit]
      polarization := by
        intro x y
        rw [helladd, Q.polarization]
        exact recompose_scalar _ _ _ _ _
      polar_add_left := by
        intro x y z
        rw [Q.polar_add_left, helladd, add_mul]
        abel
      polar_add_right := by
        intro x y z
        rw [Q.polar_add_right, helladd, mul_add]
        abel
      polar_symm := by
        intro x y
        rw [Q.polar_symm, mul_comm]
      source_two := Q.source_two }
  exact ⟨q, by simp [q], by simp [q]⟩

/-- The scalar decomposition is unique and the converse round-trips
pointwise. -/
theorem brownRefinement_converse_roundtrip
    (ell : V → ZMod 2) (Q : F2Quadratic V)
    (q : BrownRefinement V)
    (hq : ∀ x,
      q.quadratic x = liftBit (ell x) + doubleBit (Q.quadratic x)) :
    (∀ x, q.linearPart x = ell x) ∧
      (∀ x, q.classicalPart x = Q.quadratic x) := by
  constructor
  · intro x
    rw [BrownRefinement.linearPart, hq, parity_add, parity_liftBit,
      parity_doubleBit, add_zero]
  · intro x
    rw [BrownRefinement.classicalPart, hq]
    exact residual_lift_double _ _

end Ogdoad.BrownGame
