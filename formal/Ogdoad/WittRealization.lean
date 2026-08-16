import Ogdoad.ImpartialRealizer
import Ogdoad.WittRamification
import Ogdoad.WittRealizationExact
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.Finset.Sigma
import Mathlib.LinearAlgebra.DFinsupp

/-!
# End-to-end realization of presented Witt coordinates

The Aravire--Jacob classification presents `W_q(F_2(t))` by one constant
coordinate, finitely supported odd principal parts in the residue fields, and
finitely supported ramified Arf bits satisfying one parity relation.  Mathlib
does not currently contain the characteristic-two quadratic Witt group or the
Aravire--Jacob residue sequence, so this file takes that cited classification
at exactly one boundary: a linear equivalence from the actual Witt group to
the concrete type `PresentedWitt` below.

Everything after that boundary is constructed here.  In particular this file

* defines the parity-zero global coordinate space;
* defines every constant, ramified, and trace-character observation;
* proves that the observation family is additive, finitely supported on each
  class, and faithful;
* realizes every observation by the literal empty-core impartial `0/*` tail;
* proves one end-to-end theorem saying that equality of all P/N outcomes is
  equivalent to equality of presented Witt classes; and
* transports that theorem across any supplied Aravire--Jacob classification
  equivalence.

Thus no coordinate extraction, trace-separation, sparsity, game construction,
or faithfulness join is left as a theorem premise.  The sole external bridge
is the classification equivalence itself.
-/

namespace Ogdoad.WittRealization

open Ogdoad.Fifo

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- Finite principal parts with no constant or positive even pole. -/
def oddPrincipalPartSubmodule (k : Type*) [Field k] [Algebra F2 k] :
    Submodule F2 (WittRamification.PrincipalPart k) where
  carrier := {f | f 0 = 0 ∧ ∀ n, 0 < n → Even n → f n = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf0, hf⟩ ⟨hg0, hg⟩
    constructor
    · simp [hf0, hg0]
    · intro n hn he
      simp [hf n hn he, hg n hn he]
  smul_mem' := by
    rintro a f ⟨hf0, hf⟩
    constructor
    · simp [hf0]
    · intro n hn he
      simp [hf n hn he]

/-- The canonical odd-pole local residue space at one place. -/
abbrev OddPrincipalPart (k : Type*) [Field k] [Algebra F2 k] :=
  oddPrincipalPartSubmodule k

/-- Sum of the finitely supported ramified Arf bits. -/
def ramifiedParity (Place : Type*) : (Place →₀ F2) →ₗ[F2] F2 :=
  Finsupp.lsum F2 fun _ ↦ LinearMap.id

@[simp]
theorem ramifiedParity_apply {Place : Type*} (r : Place →₀ F2) :
    ramifiedParity Place r = r.sum fun _ b ↦ b := by
  rfl

/-- Ramified bits satisfying the unique global reciprocity relation. -/
abbrev RamifiedData (Place : Type*) := LinearMap.ker (ramifiedParity Place)

/-- Finitely supported odd-pole data in the varying residue fields. -/
abbrev WildData (Place : Type*) (kappa : Place → Type*)
    [∀ v, Field (kappa v)] [∀ v, Algebra F2 (kappa v)] :=
  Π₀ v : Place, OddPrincipalPart (kappa v)

/-- The concrete global coordinate object in the Aravire--Jacob
classification: constant, wild residue, and parity-zero ramified residue. -/
abbrev PresentedWitt (Place : Type*) (kappa : Place → Type*)
    [∀ v, Field (kappa v)] [∀ v, Algebra F2 (kappa v)] :=
  F2 × WildData Place kappa × RamifiedData Place

/-- Labels for every basis-free binary observation. -/
inductive Observation (Place : Type*) (kappa : Place → Type*) where
  | constant
  | ramified (v : Place)
  | wild (v : Place) (pole : ℕ) (lambda : kappa v)

variable {Place : Type*} {kappa : Place → Type*}
  [∀ v, Field (kappa v)] [∀ v, Finite (kappa v)]
  [∀ v, Algebra F2 (kappa v)]

/-- The bit attached to one canonical coordinate label. -/
def bit (x : PresentedWitt Place kappa) : Observation Place kappa → F2
  | .constant => x.1
  | .ramified v => x.2.2.1 v
  | .wild v n lambda =>
      Algebra.trace F2 (kappa v) (lambda * (x.2.1 v).1 n)

@[simp]
theorem bit_constant (x : PresentedWitt Place kappa) :
    bit x .constant = x.1 :=
  rfl

@[simp]
theorem bit_ramified (x : PresentedWitt Place kappa) (v : Place) :
    bit x (.ramified v) = x.2.2.1 v :=
  rfl

@[simp]
theorem bit_wild (x : PresentedWitt Place kappa)
    (v : Place) (n : ℕ) (lambda : kappa v) :
    bit x (.wild v n lambda) =
      Algebra.trace F2 (kappa v) (lambda * (x.2.1 v).1 n) :=
  rfl

/-- Orthogonal sum becomes xor at every observation label. -/
theorem bit_add (x y : PresentedWitt Place kappa)
    (o : Observation Place kappa) :
    bit (x + y) o = bit x o + bit y o := by
  cases o with
  | constant => rfl
  | ramified v => rfl
  | wild v n lambda =>
      simp only [bit, Prod.fst_add, Prod.snd_add, DFinsupp.add_apply,
        Submodule.coe_add, Finsupp.add_apply, mul_add, map_add]

@[simp]
theorem bit_zero (o : Observation Place kappa) :
    bit (0 : PresentedWitt Place kappa) o = 0 := by
  cases o <;> simp [bit]

/-- Trace-character observations determine every presented coordinate. -/
theorem bit_injective :
    Function.Injective (bit (Place := Place) (kappa := kappa)) := by
  intro x y hxy
  apply Prod.ext
  · exact congrFun hxy .constant
  · apply Prod.ext
    · apply DFinsupp.ext
      intro v
      apply Subtype.ext
      apply Finsupp.ext
      intro n
      apply WittRealizationExact.traceBitPresentation_injective (kappa v)
      apply LinearMap.ext
      intro lambda
      simpa [WittRealizationExact.traceBitPresentation_apply] using
        congrFun hxy (.wild v n lambda)
    · apply Subtype.ext
      apply Finsupp.ext
      intro v
      exact congrFun hxy (.ramified v)

/-- A finite directory containing every nonzero observation of one class.
For each nonzero wild coefficient it includes all trace labels in the finite
residue field; redundancy is deliberate and basis-free. -/
noncomputable def activeLabels (x : PresentedWitt Place kappa) :
    Finset (Observation Place kappa) := by
  classical
  letI (v : Place) : Fintype (kappa v) := Fintype.ofFinite (kappa v)
  let ramified : Finset (Observation Place kappa) :=
    x.2.2.1.support.image Observation.ramified
  let wildSigma : Finset (Σ v : Place, Σ _n : ℕ, kappa v) :=
    x.2.1.support.sigma fun v ↦
      (x.2.1 v).1.support.sigma fun _n ↦ Finset.univ
  let wild : Finset (Observation Place kappa) :=
    wildSigma.image fun q ↦ Observation.wild q.1 q.2.1 q.2.2
  exact {.constant} ∪ ramified ∪ wild

/-- Outside the finite active directory every observation is the zero game. -/
theorem bit_eq_zero_of_not_mem_activeLabels
    (x : PresentedWitt Place kappa) (o : Observation Place kappa)
    (ho : o ∉ activeLabels x) : bit x o = 0 := by
  classical
  letI (v : Place) : Fintype (kappa v) := Fintype.ofFinite (kappa v)
  cases o with
  | constant =>
      exact False.elim (ho (by simp [activeLabels]))
  | ramified v =>
      have hv : v ∉ x.2.2.1.support := by
        intro hv
        apply ho
        simp only [activeLabels, Finset.mem_union, Finset.mem_singleton]
        exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
      rw [bit_ramified, Finsupp.notMem_support_iff.mp hv]
  | wild v n lambda =>
      by_cases hv : v ∈ x.2.1.support
      · by_cases hn : n ∈ (x.2.1 v).1.support
        · apply False.elim
          apply ho
          simp only [activeLabels, Finset.mem_union, Finset.mem_singleton]
          apply Or.inr
          apply Finset.mem_image.mpr
          refine ⟨⟨v, ⟨n, lambda⟩⟩, ?_, rfl⟩
          simp only [Finset.mem_sigma]
          exact ⟨hv, hn, Finset.mem_univ _⟩
        · rw [bit_wild, Finsupp.notMem_support_iff.mp hn, mul_zero, map_zero]
      · have hv0 : x.2.1 v = 0 := DFinsupp.notMem_support_iff.mp hv
        rw [bit_wild, hv0]
        simp

/-- In particular the complete labelled bit function has finite support. -/
theorem bit_support_finite (x : PresentedWitt Place kappa) :
    (Function.support (bit x)).Finite := by
  refine (activeLabels x).finite_toSet.subset ?_
  intro o ho
  by_contra hnot
  exact ho (bit_eq_zero_of_not_mem_activeLabels x o hnot)

/-- The actual finite sparse family emitted by the compiler. -/
noncomputable def sparseCompiler (x : PresentedWitt Place kappa) :
    Observation Place kappa →₀ F2 :=
  Finsupp.ofSupportFinite (bit x) (bit_support_finite x)

@[simp]
theorem sparseCompiler_apply (x : PresentedWitt Place kappa)
    (o : Observation Place kappa) : sparseCompiler x o = bit x o := by
  simp [sparseCompiler, Finsupp.ofSupportFinite_coe]

/-- The finite sparse compiler is itself faithful. -/
theorem sparseCompiler_injective :
    Function.Injective (sparseCompiler (Place := Place) (kappa := kappa)) := by
  intro x y hxy
  apply bit_injective
  funext o
  simpa only [sparseCompiler_apply] using DFunLike.congr_fun hxy o

@[simp]
theorem sparseCompiler_zero :
    sparseCompiler (0 : PresentedWitt Place kappa) = 0 := by
  ext o
  simp

/-- Orthogonal sum is coordinatewise xor on the emitted finite families. -/
theorem sparseCompiler_add (x y : PresentedWitt Place kappa) :
    sparseCompiler (x + y) = sparseCompiler x + sparseCompiler y := by
  ext o
  simp [bit_add]

/-- Boolean presentation of a binary charge for the impartial tail compiler. -/
def bitBool (z : F2) : Bool := decide (z = 1)

theorem bitBool_eq_false_iff (z : F2) : bitBool z = false ↔ z = 0 := by
  by_cases hz : z = 1
  · simp [bitBool, hz]
  · have : z = 0 := Ogdoad.zmod2_eq_zero_of_ne_one z hz
    simp [bitBool, this]

/-- The literal normal-play `0/*` arena for one observation.  Its FIFO core
has no coins; the terminal one-move tail is present exactly when the bit is
one. -/
def CoordinateIsP (x : PresentedWitt Place kappa)
    (o : Observation Place kappa) : Prop :=
  ImpartialRealizer.TailWins (⊥ : SimpleGraph Empty) true
    (ImpartialRealizer.initial (V := Empty)
      (ImpartialRealizer.scoreBit (bitBool (bit x o))))

private theorem emptyGraph_isMatching :
    IsMatchingGraph (⊥ : SimpleGraph Empty) := by
  intro v
  exact Empty.elim v

/-- One labelled arena is a P-position exactly when its Witt coordinate bit
vanishes. -/
theorem coordinateIsP_iff (x : PresentedWitt Place kappa)
    (o : Observation Place kappa) :
    CoordinateIsP x o ↔ bit x o = 0 := by
  exact (ImpartialRealizer.root_isP_iff_charge_zero
    emptyGraph_isMatching le_rfl (bitBool (bit x o))).trans
      (bitBool_eq_false_iff (bit x o))

/-- Flagship theorem for the presented class: two classes have identical P/N
outcome families exactly when they are equal. -/
theorem same_outcomes_iff (x y : PresentedWitt Place kappa) :
    (∀ o, CoordinateIsP x o ↔ CoordinateIsP y o) ↔ x = y := by
  constructor
  · intro h
    apply bit_injective
    funext o
    have hz : bit x o = 0 ↔ bit y o = 0 := by
      simpa only [coordinateIsP_iff] using h o
    by_cases hx0 : bit x o = 0
    · rw [hx0, hz.mp hx0]
    · have hy0 : bit y o ≠ 0 := by
        intro hy
        exact hx0 (hz.mpr hy)
      rw [Ogdoad.zmod2_eq_one_of_ne_zero _ hx0,
        Ogdoad.zmod2_eq_one_of_ne_zero _ hy0]
  · rintro rfl
    exact fun _ ↦ Iff.rfl

/-- The only bridge required from a quadratic Witt-group formalization: the
cited classification equivalence to the concrete coordinates above. -/
structure ClassificationBridge (W : Type*) [AddCommGroup W] [Module F2 W]
    (Place : Type*) (kappa : Place → Type*)
    [∀ v, Field (kappa v)] [∀ v, Algebra F2 (kappa v)] where
  coordinates : W ≃ₗ[F2] PresentedWitt Place kappa

/-- End-to-end theorem transported to any Witt group equipped with the cited
classification bridge.  No later construction is accepted as a premise. -/
theorem witt_same_outcomes_iff
    {W : Type*} [AddCommGroup W] [Module F2 W]
    (bridge : ClassificationBridge W Place kappa) (x y : W) :
    (∀ o, CoordinateIsP (bridge.coordinates x) o ↔
      CoordinateIsP (bridge.coordinates y) o) ↔ x = y := by
  rw [same_outcomes_iff, bridge.coordinates.injective.eq_iff]

section PlaceSpikes

/-- The canonical simple odd pole with coefficient one. -/
noncomputable def simplePole (K : Type*) [Field K] [Algebra F2 K] :
    OddPrincipalPart K := by
  classical
  refine ⟨Finsupp.single 1 1, ?_⟩
  constructor
  · simp
  · intro n hn he
    by_cases hn1 : n = 1
    · subst n
      exact (Nat.not_even_one he).elim
    · simp [Finsupp.single_apply, hn1]

theorem simplePole_ne_zero (K : Type*) [Field K] [Algebra F2 K] :
    simplePole K ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : OddPrincipalPart K ↦ p.1 1) h
  simpa [simplePole] using hcoeff

/-- Coordinate class supported by one simple pole at one place.  Under the
Aravire--Jacob bridge this is the residue pattern of the paper's binary plane
`[1,P⁻¹]`. -/
noncomputable def placeSpike (v : Place) : PresentedWitt Place kappa := by
  classical
  exact (0, DFinsupp.single v (simplePole (kappa v)), 0)

/-- Distinct places give distinct concrete coordinate classes. -/
theorem placeSpike_injective :
    Function.Injective (placeSpike (Place := Place) (kappa := kappa)) := by
  classical
  intro v w hvw
  by_contra hvne
  have hcomponent := congrArg (fun x : PresentedWitt Place kappa ↦ x.2.1 v) hvw
  have hwv : v ≠ w := hvne
  rw [show (placeSpike (Place := Place) (kappa := kappa) v).2.1 v =
      simplePole (kappa v) by simp [placeSpike]] at hcomponent
  rw [show (placeSpike (Place := Place) (kappa := kappa) w).2.1 v = 0 by
      change (DFinsupp.single (β := fun u ↦ OddPrincipalPart (kappa u))
        w (simplePole (kappa w))) v = 0
      exact DFinsupp.single_eq_of_ne hwv] at hcomponent
  exact simplePole_ne_zero (kappa v) hcomponent

/-- Concrete fixed-finite-family obstruction on the presented Witt space. -/
theorem not_injective_fixed_finite_outcomes [Infinite Place]
    {Query : Type*} [Fintype Query]
    (observe : PresentedWitt Place kappa → Query → Bool) :
    ¬Function.Injective observe := by
  letI : Infinite (PresentedWitt Place kappa) :=
    Infinite.of_injective placeSpike placeSpike_injective
  exact WittRamification.not_injective_finitePNOutcomeVector observe

end PlaceSpikes

end

end Ogdoad.WittRealization
