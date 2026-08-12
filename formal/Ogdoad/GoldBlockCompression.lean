import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Block aggregation for quadratic refinements

This file kernel-checks the algebraic core of the block-compression
corollary: aggregating the coordinates of a quadratic refinement into
blocks induces a well-formed quadratic refinement on the block
coordinates -- diagonal the block values, polar the Gram data -- whose
value at the all-ones input is the original value at the block sum.
Together with indicator-block bookkeeping (a disjoint block family sums
to the indicator of its union and is linearly independent), this is the
ingredient behind attaining the transcript-span observation bound at
every width: the strategic content (the access contract and the
weighted-source arena) is checked elsewhere and synthesized in the
paper, not here.
-/

noncomputable section

open scoped BigOperators

namespace Ogdoad.GoldBlock

abbrev F2 := ZMod 2

variable {M : Type*} [AddCommGroup M] [Module F2 M]

/-- Over an `F₂`-valued target the polar form is alternating. -/
theorem polar_self_eq_zero (Q : QuadraticMap F2 M F2) (v : M) :
    QuadraticMap.polar Q v v = 0 := by
  have h2 : (2 : F2) = 0 := by decide
  rw [QuadraticMap.polar_self, two_smul, ← two_mul, h2, zero_mul]

/-- The polarization expansion of a quadratic map over a finite family:
diagonal values plus the off-diagonal polar pairs.  This is mathlib's
`QuadraticMap.map_sum`, re-exported as the display used by the paper. -/
theorem quadratic_sum_expansion {ι : Type*} [DecidableEq ι]
    (Q : QuadraticMap F2 M F2) (s : Finset ι) (z : ι → M) :
    Q (∑ i ∈ s, z i) = ∑ i ∈ s, Q (z i)
      + ∑ ij ∈ s.sym2 with ¬ ij.IsDiag, QuadraticMap.polarSym2 Q (ij.map z) :=
  QuadraticMap.map_sum Q s z

section Induced

variable {k : ℕ}

/-- The linear map carrying block coordinates to the block vectors. -/
def blockMap (z : Fin k → M) : (Fin k → F2) →ₗ[F2] M where
  toFun c := ∑ i, c i • z i
  map_add' a b := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' r a := by
    simp [Finset.smul_sum, mul_smul]

@[simp] theorem blockMap_apply (z : Fin k → M) (c : Fin k → F2) :
    blockMap z c = ∑ i, c i • z i := rfl

theorem blockMap_single (z : Fin k → M) (i : Fin k) :
    blockMap z (Pi.single i 1) = z i := by
  rw [blockMap_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem blockMap_one (z : Fin k → M) :
    blockMap z (fun _ => 1) = ∑ i, z i := by
  simp

/-- The induced quadratic map on block coordinates. -/
def induced (Q : QuadraticMap F2 M F2) (z : Fin k → M) :
    QuadraticMap F2 (Fin k → F2) F2 :=
  Q.comp (blockMap z)

@[simp] theorem induced_apply (Q : QuadraticMap F2 M F2) (z : Fin k → M)
    (c : Fin k → F2) : induced Q z c = Q (blockMap z c) :=
  QuadraticMap.comp_apply Q (blockMap z) c

/-- The induced diagonal is the block values. -/
theorem induced_diagonal (Q : QuadraticMap F2 M F2) (z : Fin k → M)
    (i : Fin k) : induced Q z (Pi.single i 1) = Q (z i) := by
  rw [induced_apply, blockMap_single]

/-- The polar form of a pullback is the pullback of the polar form. -/
theorem polar_comp_linear (Q : QuadraticMap F2 M F2) {k : ℕ}
    (f : (Fin k → F2) →ₗ[F2] M) (u v : Fin k → F2) :
    QuadraticMap.polar (Q.comp f) u v = QuadraticMap.polar Q (f u) (f v) := by
  simp [QuadraticMap.polar, QuadraticMap.comp_apply, map_add]

/-- The induced polar form is the Gram data of the blocks. -/
theorem induced_polar (Q : QuadraticMap F2 M F2) (z : Fin k → M)
    (i j : Fin k) :
    QuadraticMap.polar (induced Q z) (Pi.single i 1) (Pi.single j 1) =
      QuadraticMap.polar Q (z i) (z j) := by
  rw [induced, polar_comp_linear, blockMap_single, blockMap_single]

/-- The induced polar form is alternating. -/
theorem induced_alternating (Q : QuadraticMap F2 M F2) (z : Fin k → M)
    (c : Fin k → F2) : QuadraticMap.polar (induced Q z) c c = 0 :=
  polar_self_eq_zero (induced Q z) c

/-- The headline identity: the induced refinement evaluated at the
all-ones block input is the original refinement at the block sum. -/
theorem induced_total (Q : QuadraticMap F2 M F2) (z : Fin k → M) :
    induced Q z (fun _ => 1) = Q (∑ i, z i) := by
  rw [induced_apply, blockMap_one]

/-- Specialization to a loaded input: if the blocks sum to `x`, the
induced value at all-ones is `Q x`. -/
theorem induced_total_loaded (Q : QuadraticMap F2 M F2) (z : Fin k → M)
    (x : M) (hx : ∑ i, z i = x) : induced Q z (fun _ => 1) = Q x := by
  rw [induced_total, hx]

end Induced

section Indicator

variable {ι : Type*} [DecidableEq ι]

/-- The `F₂` indicator vector of a finite coordinate block. -/
def indicator (Z : Finset ι) : ι → F2 := fun a => if a ∈ Z then 1 else 0

@[simp] theorem indicator_apply (Z : Finset ι) (a : ι) :
    indicator Z a = if a ∈ Z then 1 else 0 := rfl

variable {k : ℕ}

/-- Pairwise disjoint blocks: the indicator vectors sum to the indicator
of the union. -/
theorem indicator_sum_partition (Z : Fin k → Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Z i) (Z j)) :
    ∑ i, indicator (Z i) = indicator (Finset.univ.biUnion Z) := by
  funext a
  simp only [Finset.sum_apply]
  by_cases ha : ∃ i, a ∈ Z i
  · obtain ⟨i₀, hi₀⟩ := ha
    have huniq : ∀ j, j ≠ i₀ → a ∉ Z j := fun j hj hja =>
      Finset.disjoint_left.mp (hdisj j i₀ hj) hja hi₀
    have hmem : a ∈ Finset.univ.biUnion Z :=
      Finset.mem_biUnion.mpr ⟨i₀, Finset.mem_univ i₀, hi₀⟩
    rw [Finset.sum_eq_single i₀
      (fun j _ hj => by simp [indicator, huniq j hj])
      (fun h => absurd (Finset.mem_univ i₀) h)]
    simp [indicator, hi₀, hmem]
  · have ha' : ∀ i, a ∉ Z i := fun i hi => ha ⟨i, hi⟩
    have hmem : a ∉ Finset.univ.biUnion Z := fun h => by
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
      exact ha' i hi
    simp [indicator, ha', hmem]

/-- Pairwise disjoint nonempty blocks give linearly independent
indicator vectors. -/
theorem indicator_linearIndependent (Z : Fin k → Finset ι)
    (hne : ∀ i, (Z i).Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Z i) (Z j)) :
    LinearIndependent F2 (fun i => indicator (Z i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i₀
  obtain ⟨a, ha⟩ := hne i₀
  have huniq : ∀ j, j ≠ i₀ → a ∉ Z j := fun j hj hja =>
    Finset.disjoint_left.mp (hdisj j i₀ hj) hja ha
  have := congrFun hg a
  rw [Finset.sum_apply] at this
  rw [Finset.sum_eq_single i₀ (fun j _ hj => by
    simp [indicator, huniq j hj]) (fun h => absurd (Finset.mem_univ i₀) h)]
    at this
  simpa [indicator, ha] using this

end Indicator

end Ogdoad.GoldBlock
