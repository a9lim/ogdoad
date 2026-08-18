import Ogdoad.WittRamification
import Mathlib.FieldTheory.Finite.Trace

/-!
# Ramified unit-jet substitution

This file supplies the concrete substitution layer omitted from
`WittRamification`.  For a ramified parameter change `pi = u * varpi^e`, the
coefficient `unitInv n r` represents the `r`th coefficient of `u⁻ⁿ`.  A base
principal part is expanded into a finite target principal part, then passed
through the exact descending Artin--Schreier normalizer proved in
`WittRamification`.

The construction kernel-checks the unit-jet coefficient formula, a sharp
finite support bound, preservation of the unit-jet constant term by
normalization, elimination of every positive even pole, and triangular
dependence.  Identifying a supplied jet with the coefficients of an actual
local-field unit, and the separate unramified/ramified generator calculation,
remain the local quadratic-form bridge.
-/

namespace Ogdoad.WittRamifiedRestriction

open scoped CharTwo

noncomputable section

abbrev PrincipalPart := WittRamification.PrincipalPart

variable {k ell : Type*} [Field k] [Field ell]

/-- Contribution of one source pole `c*pi⁻ⁿ` after substituting
`pi = u*varpi^e`.  Index `j` is the target pole order, so the required unit-jet
coefficient is `e*n-j`. -/
noncomputable def substitutedTerm (embed : k →+* ell) (e n : ℕ)
    (unitInv : ℕ → ℕ → ell) (c : k) : PrincipalPart ell := by
  classical
  exact Finsupp.onFinset (Finset.range (e * n + 1))
    (fun j ↦ if j ≤ e * n then embed c * unitInv n (e * n - j) else 0)
    (by
      intro j hj
      simp only [Finset.mem_range]
      by_contra hnot
      have hlt : e * n < j := by omega
      simp [Nat.not_le.mpr hlt] at hj)

@[simp]
theorem substitutedTerm_apply (embed : k →+* ell) (e n : ℕ)
    (unitInv : ℕ → ℕ → ell) (c : k) (j : ℕ) :
    substitutedTerm embed e n unitInv c j =
      if j ≤ e * n then embed c * unitInv n (e * n - j) else 0 := by
  classical
  exact Finsupp.onFinset_apply

/-- Finite unit-series substitution on a whole principal part. -/
noncomputable def substitute (embed : k →+* ell) (e : ℕ)
    (unitInv : ℕ → ℕ → ell) (psi : PrincipalPart k) : PrincipalPart ell :=
  psi.sum fun n c ↦ substitutedTerm embed e n unitInv c

@[simp]
theorem substitute_apply (embed : k →+* ell) (e : ℕ)
    (unitInv : ℕ → ℕ → ell) (psi : PrincipalPart k) (j : ℕ) :
    substitute embed e unitInv psi j =
      psi.sum fun n c ↦
        if j ≤ e * n then embed c * unitInv n (e * n - j) else 0 := by
  classical
  simp [substitute]

/-- Largest possible target pole order after ramification. -/
def substitutionBound (e : ℕ) (psi : PrincipalPart k) : ℕ :=
  e * psi.support.sup id

/-- The substituted principal part has no coefficient above the sharp
ramification-scaled source bound. -/
theorem substitute_apply_of_bound_lt (embed : k →+* ell) (e : ℕ)
    (unitInv : ℕ → ℕ → ell) (psi : PrincipalPart k) {j : ℕ}
    (hj : substitutionBound e psi < j) :
    substitute embed e unitInv psi j = 0 := by
  classical
  rw [substitute_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro n hn
  have hnle : n ≤ psi.support.sup id :=
    Finset.le_sup (f := fun m : ℕ ↦ m) hn
  have hen : e * n ≤ substitutionBound e psi := by
    exact Nat.mul_le_mul_left e hnle
  simp only [if_neg (not_le.mpr (hen.trans_lt hj))]

/-- The paper's unit-jet constant contribution before applying the residue
field trace. -/
def unitConstant (embed : k →+* ell) (e : ℕ)
    (unitInv : ℕ → ℕ → ell) (psi : PrincipalPart k) : ell :=
  substitute embed e unitInv psi 0

theorem unitConstant_eq_sum (embed : k →+* ell) (e : ℕ)
    (unitInv : ℕ → ℕ → ell) (psi : PrincipalPart k) :
    unitConstant embed e unitInv psi =
      psi.sum fun n c ↦ embed c * unitInv n (e * n) := by
  simp [unitConstant]

section CharacteristicTwo

variable [CharP ell 2] [PerfectField ell]

/-- Concrete ramified wild-coordinate transformation: perform the unit-jet
substitution and then the exact descending Artin--Schreier normalization. -/
noncomputable def transform (embed : k →+* ell) (e : ℕ)
    (unitInv : ℕ → ℕ → ell) (psi : PrincipalPart k) : PrincipalPart ell :=
  WittRamification.perfectNormalizeUpTo (substitutionBound e psi)
    (substitute embed e unitInv psi)

/-- The transformation is a canonical odd-pole normal form. -/
theorem transform_isOddNormalForm (embed : k →+* ell) (e : ℕ)
    (unitInv : ℕ → ℕ → ell) (psi : PrincipalPart k) :
    (∀ j, substitutionBound e psi < j →
      transform embed e unitInv psi j = 0) ∧
    (∀ j, 0 < j → Even j → transform embed e unitInv psi j = 0) := by
  exact WittRamification.perfectNormalizeUpTo_isOddNormalForm
    (substitute embed e unitInv psi) (substitutionBound e psi)
    (fun j hj ↦ substitute_apply_of_bound_lt embed e unitInv psi hj)

/-- Artin--Schreier pole cancellation does not alter the new constant created
by the unit jet. -/
@[simp]
theorem transform_zero (embed : k →+* ell) (e : ℕ)
    (unitInv : ℕ → ℕ → ell) (psi : PrincipalPart k) :
    transform embed e unitInv psi 0 = unitConstant embed e unitInv psi := by
  change WittRamification.normalizeUpTo WittRamification.perfectSquareRoot
      (substitutionBound e psi) (substitute embed e unitInv psi) 0 =
    substitute embed e unitInv psi 0
  exact WittRamification.normalizeUpTo_zero_apply _ _ _

/-- The transformed coefficient at order `j` depends only on substituted
coefficients at orders at least `j`. -/
theorem transform_congr_above (embed : k →+* ell) (e : ℕ)
    (unitInv : ℕ → ℕ → ell) (psi chi : PrincipalPart k) (j N : ℕ)
    (hpsi : ∀ q, j ≤ q → substitute embed e unitInv psi q =
      substitute embed e unitInv chi q) :
    WittRamification.perfectNormalizeUpTo N
        (substitute embed e unitInv psi) j =
      WittRamification.perfectNormalizeUpTo N
        (substitute embed e unitInv chi) j := by
  exact WittRamification.normalizeUpTo_congr_above
    WittRamification.perfectSquareRoot hpsi

section Trace

variable [Algebra (ZMod 2) ell]

/-- The exact unramified bit contributed by the wild unit jet. -/
def eta (embed : k →+* ell) (e : ℕ) (unitInv : ℕ → ℕ → ell)
    (psi : PrincipalPart k) : ZMod 2 :=
  Algebra.trace (ZMod 2) ell (transform embed e unitInv psi 0)

theorem eta_eq_trace_unitConstant (embed : k →+* ell) (e : ℕ)
    (unitInv : ℕ → ℕ → ell) (psi : PrincipalPart k) :
    eta embed e unitInv psi =
      Algebra.trace (ZMod 2) ell (unitConstant embed e unitInv psi) := by
  simp [eta]

end Trace

end CharacteristicTwo

end

end Ogdoad.WittRamifiedRestriction
