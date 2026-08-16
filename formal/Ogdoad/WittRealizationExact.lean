import Mathlib

/-!
# The exact-sequence core of characteristic-two Witt realization

For `K = F₂(t)`, the cited Milnor--Scharlau sequence has the shape

```text
0 → C → W → R → C → 0,
```

where `C = W_q(F₂)`, `W = W_q(F₂(t))`, and `R` is the direct sum of
the placewise residue groups.  All these groups are naturally `F₂`-vector
spaces.  This file isolates what follows from exactness alone.

The main theorem `coordinatesEquivOfProjection` proves that an explicit linear
constant detector `p : W → C` satisfying `p ∘ constant = id` gives faithful
additive coordinates

```text
W ≃ C × ker(transfer).
```

For `F₂(t)`, the intended detector is the unramified `phi0` coordinate in the
Aravire--Jacob decomposition at infinity with canonical uniformizer `1/t`.
Once its additivity and identity on constant forms are proved,
`coordinatesEquivOfProjection` supplies the canonical algebraic coordinates
without a basis choice.  The later `splitCoordinatesEquiv` is only a fallback:
Mathlib can extend a basis to manufacture some retraction, but that construction
is deliberately noncomputable and noncanonical and therefore does not settle
functoriality under scalar extension or Scharlau transfer.

The second main ingredient is `traceBitPresentation`.  For every finite
extension `E/F₂`, it embeds a wild coefficient `z : E` into the basis-free
family of bits `lambda ↦ Tr(lambda*z)`.  Nondegeneracy of the finite-field
trace pairing proves that these observations distinguish coefficients.

Finally, `additiveEncoding_eq_of_absorption` records the cancellation
obstruction to extending this nonsingular program faithfully to arbitrary
singular forms.  The characteristic-two quasilinear relation
`<c> ⊥ <c> ≅ <c> ⊥ <0>` forces every additive encoding into a
cancellative game-value group to identify `<c>` with `<0>`.

No declaration below assumes or proves the Milnor--Scharlau sequence for
quadratic Witt groups.  A future formalization of that cited theorem should
instantiate `ResidueSequence`; the results here then apply without change.
-/

namespace Ogdoad.WittRealizationExact

abbrev F2 := ZMod 2

section FiniteFieldTraceBits

/-- The basis-free family of `F₂` observations of a coefficient in a finite
residue field: `z` is sent to the linear functional
`lambda ↦ Tr_{E/F₂}(lambda*z)`.  Packaging this as a linear map proves
linearity in `z` by construction. -/
noncomputable def traceBitPresentation
    (E : Type*) [Field E] [Finite E] [Algebra F2 E] :
    E →ₗ[F2] Module.Dual F2 E :=
  Algebra.traceForm F2 E

@[simp]
theorem traceBitPresentation_apply
    {E : Type*} [Field E] [Finite E] [Algebra F2 E]
    (z lambda : E) :
    traceBitPresentation E z lambda =
      Algebra.trace F2 E (lambda * z) := by
  rw [traceBitPresentation, Algebra.traceForm_apply, mul_comm]

@[simp]
theorem traceBitPresentation_add
    {E : Type*} [Field E] [Finite E] [Algebra F2 E]
    (z w : E) :
    traceBitPresentation E (z + w) =
      traceBitPresentation E z + traceBitPresentation E w :=
  map_add (traceBitPresentation E) z w

@[simp]
theorem traceBitPresentation_smul
    {E : Type*} [Field E] [Finite E] [Algebra F2 E]
    (a : F2) (z : E) :
    traceBitPresentation E (a • z) =
      a • traceBitPresentation E z :=
  map_smul (traceBitPresentation E) a z

/-- The finite-field trace observations distinguish coefficients. -/
theorem traceBitPresentation_injective
    (E : Type*) [Field E] [Finite E] [Algebra F2 E] :
    Function.Injective (traceBitPresentation E) := by
  rw [← LinearMap.ker_eq_bot]
  exact (traceForm_nondegenerate F2 E).ker_eq_bot

/-- Point-separating form of trace nondegeneracy: every nonzero coefficient is
detected by at least one trace bit. -/
theorem exists_traceBitPresentation_ne_zero
    {E : Type*} [Field E] [Finite E] [Algebra F2 E]
    {z : E} (hz : z ≠ 0) :
    ∃ lambda : E, traceBitPresentation E z lambda ≠ 0 := by
  by_contra h
  apply hz
  apply (traceForm_nondegenerate F2 E).1 z
  intro lambda
  by_contra hne
  exact h ⟨lambda, hne⟩

end FiniteFieldTraceBits

section SingularCancellationBoundary

variable {Form Value : Type*}
  [AddCommMonoid Form] [AddCancelCommMonoid Value]

/-- Any additive encoding into a cancellative value monoid identifies `a` and
`z` as soon as the source has the absorption relation `a+a=a+z`.

For quasilinear one-dimensional forms in characteristic two, the change of
variables `(u,v)=(x+y,y)` gives
`<c> ⊥ <c> ≅ <c> ⊥ <0>`.  Thus an additive impartial-game-value
encoding cannot distinguish the nonzero radical coefficient `<c>` from the
zero form while retaining this isometry relation. -/
theorem additiveEncoding_eq_of_absorption
    (encode : Form →+ Value) {a z : Form}
    (habsorb : a + a = a + z) : encode a = encode z := by
  have h := congrArg encode habsorb
  have h' : encode a + encode a = encode a + encode z := by
    simpa only [map_add] using h
  exact add_left_cancel h'

/-- Consequently, a genuine absorption pair obstructs injectivity of every
additive encoding into a cancellative value monoid. -/
theorem not_injective_additiveEncoding_of_absorption
    (encode : Form →+ Value) {a z : Form}
    (hane : a ≠ z) (habsorb : a + a = a + z) :
    ¬Function.Injective encode := by
  intro hinjective
  exact hane (hinjective (additiveEncoding_eq_of_absorption encode habsorb))

end SingularCancellationBoundary

variable {C W R : Type*}
  [AddCommGroup C] [AddCommGroup W] [AddCommGroup R]
  [Module F2 C] [Module F2 W] [Module F2 R]

/-- The linear-algebra data and exactness hypotheses in the
Milnor--Scharlau sequence.  The endpoint hypotheses record the leading
injection and trailing surjection. -/
structure ResidueSequence (C W R : Type*)
    [AddCommGroup C] [AddCommGroup W] [AddCommGroup R]
    [Module F2 C] [Module F2 W] [Module F2 R] where
  constant : C →ₗ[F2] W
  residue : W →ₗ[F2] R
  transfer : R →ₗ[F2] C
  constant_injective : Function.Injective constant
  exact_at_witt : Function.Exact constant residue
  exact_at_residue : Function.Exact residue transfer
  transfer_surjective : Function.Surjective transfer

namespace ResidueSequence

variable (S : ResidueSequence C W R)

/-- Constants have zero second residue. -/
@[simp]
theorem residue_constant (c : C) : S.residue (S.constant c) = 0 := by
  have hcomp := S.exact_at_witt.linearMap_comp_eq_zero
  exact LinearMap.ext_iff.mp hcomp c

/-- Every Witt residue tuple satisfies the transfer/reciprocity relation. -/
@[simp]
theorem transfer_residue (w : W) : S.transfer (S.residue w) = 0 := by
  have hcomp := S.exact_at_residue.linearMap_comp_eq_zero
  exact LinearMap.ext_iff.mp hcomp w

/-- The residue map with codomain restricted to the transfer kernel. -/
def kernelResidue : W →ₗ[F2] LinearMap.ker S.transfer :=
  S.residue.codRestrict (LinearMap.ker S.transfer) fun w ↦ by
    exact LinearMap.mem_ker.mpr (S.transfer_residue w)

@[simp]
theorem kernelResidue_coe (w : W) :
    (S.kernelResidue w : R) = S.residue w :=
  rfl

/-- The transfer relation is the only relation on residue tuples. -/
theorem transfer_eq_zero_iff_exists_residue (r : R) :
    S.transfer r = 0 ↔ ∃ w : W, S.residue w = r := by
  rw [← LinearMap.mem_ker, S.exact_at_residue.linearMap_ker_eq,
    LinearMap.mem_range]

/-- Two classes have the same residues exactly when their difference is a
constant-field class.  Injectivity makes that constant unique. -/
theorem residue_eq_iff_existsUnique_constant (x y : W) :
    S.residue x = S.residue y ↔
      ∃! c : C, x - y = S.constant c := by
  constructor
  · intro hxy
    have hker : x - y ∈ LinearMap.ker S.residue := by
      rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
    rw [S.exact_at_witt.linearMap_ker_eq, LinearMap.mem_range] at hker
    obtain ⟨c, hc⟩ := hker
    refine ⟨c, hc.symm, ?_⟩
    intro d hd
    apply S.constant_injective
    exact hd.symm.trans hc.symm
  · rintro ⟨c, hc, _⟩
    apply sub_eq_zero.mp
    calc
      S.residue x - S.residue y = S.residue (x - y) := by rw [map_sub]
      _ = S.residue (S.constant c) := congrArg S.residue hc
      _ = 0 := S.residue_constant c

/-- Coordinates built from an explicitly supplied constant detector.  For
`F₂(t)`, the intended detector is the unramified `phi0` coordinate in the
Aravire--Jacob decomposition at the canonical infinite uniformizer `1/t`. -/
def coordinatesOfProjection (projection : W →ₗ[F2] C) :
    W →ₗ[F2] C × LinearMap.ker S.transfer :=
  projection.prod S.kernelResidue

@[simp]
theorem coordinatesOfProjection_apply (projection : W →ₗ[F2] C) (w : W) :
    S.coordinatesOfProjection projection w =
      (projection w, S.kernelResidue w) :=
  rfl

theorem projection_constant_of_comp_eq_id
    (projection : W →ₗ[F2] C)
    (hprojection : projection ∘ₗ S.constant = LinearMap.id)
    (c : C) : projection (S.constant c) = c := by
  exact LinearMap.ext_iff.mp hprojection c

theorem coordinatesOfProjection_injective
    (projection : W →ₗ[F2] C)
    (hprojection : projection ∘ₗ S.constant = LinearMap.id) :
    Function.Injective (S.coordinatesOfProjection projection) := by
  intro x y hxy
  have hproj : projection x = projection y := congrArg Prod.fst hxy
  have hkres : S.kernelResidue x = S.kernelResidue y :=
    congrArg Prod.snd hxy
  have hres : S.residue x = S.residue y :=
    congrArg Subtype.val hkres
  have hker : x - y ∈ LinearMap.ker S.residue := by
    rw [LinearMap.mem_ker, map_sub, hres, sub_self]
  rw [S.exact_at_witt.linearMap_ker_eq, LinearMap.mem_range] at hker
  obtain ⟨c, hc⟩ := hker
  have hprojzero : projection (x - y) = 0 := by
    rw [map_sub, hproj, sub_self]
  have hc0 : c = 0 := by
    calc
      c = projection (S.constant c) :=
        (S.projection_constant_of_comp_eq_id projection hprojection c).symm
      _ = projection (x - y) := by rw [hc]
      _ = 0 := hprojzero
  apply sub_eq_zero.mp
  calc
    x - y = S.constant c := hc.symm
    _ = 0 := by rw [hc0, map_zero]

theorem coordinatesOfProjection_surjective
    (projection : W →ₗ[F2] C)
    (hprojection : projection ∘ₗ S.constant = LinearMap.id) :
    Function.Surjective (S.coordinatesOfProjection projection) := by
  rintro ⟨c, r, hr⟩
  have hrange : (r : R) ∈ LinearMap.range S.residue := by
    rw [← S.exact_at_residue.linearMap_ker_eq]
    exact hr
  rw [LinearMap.mem_range] at hrange
  obtain ⟨w, hw⟩ := hrange
  let correction : C := c - projection w
  let x : W := w + S.constant correction
  refine ⟨x, ?_⟩
  apply Prod.ext
  · change projection x = c
    simp only [x, map_add, correction,
      S.projection_constant_of_comp_eq_id projection hprojection]
    abel
  · apply Subtype.ext
    change S.residue x = r
    simp only [x, map_add, S.residue_constant, add_zero, hw]

/-- An explicit constant detector splitting the constant inclusion turns the
Milnor--Scharlau residue sequence into faithful additive coordinates.  Once
the canonical-infinity `phi0` detector is constructed and shown to be a
retraction, this theorem gives the desired basis-independent algebraic
isomorphism without any choice of vector-space basis. -/
noncomputable def coordinatesEquivOfProjection
    (projection : W →ₗ[F2] C)
    (hprojection : projection ∘ₗ S.constant = LinearMap.id) :
    W ≃ₗ[F2] C × LinearMap.ker S.transfer :=
  LinearEquiv.ofBijective (S.coordinatesOfProjection projection)
    ⟨S.coordinatesOfProjection_injective projection hprojection,
      S.coordinatesOfProjection_surjective projection hprojection⟩

/-- A linear retraction of the constant-field inclusion.  Its construction
extends a basis and is consequently a choice, not canonical arithmetic data. -/
noncomputable def constantProjection : W →ₗ[F2] C :=
  S.constant.leftInverse

@[simp]
theorem constantProjection_constant (c : C) :
    S.constantProjection (S.constant c) = c := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot_of_injective S.constant_injective) c

/-- Constant coordinate together with the transfer-zero residue tuple. -/
noncomputable def splitCoordinates :
    W →ₗ[F2] C × LinearMap.ker S.transfer :=
  S.coordinatesOfProjection S.constantProjection

@[simp]
theorem splitCoordinates_apply (w : W) :
    S.splitCoordinates w =
      (S.constantProjection w, S.kernelResidue w) :=
  rfl

theorem splitCoordinates_injective :
    Function.Injective S.splitCoordinates := by
  exact S.coordinatesOfProjection_injective S.constantProjection
    (LinearMap.leftInverse_comp_of_inj
      (LinearMap.ker_eq_bot_of_injective S.constant_injective))

theorem splitCoordinates_surjective :
    Function.Surjective S.splitCoordinates := by
  exact S.coordinatesOfProjection_surjective S.constantProjection
    (LinearMap.leftInverse_comp_of_inj
      (LinearMap.ker_eq_bot_of_injective S.constant_injective))

/-- Exactness over `F₂` gives a faithful additive coordinate system after a
choice of constant projection.  This theorem proves the algebraic splitting;
it makes no claim that the choice is natural in field maps or is realized by
impartial arenas. -/
noncomputable def splitCoordinatesEquiv :
    W ≃ₗ[F2] C × LinearMap.ker S.transfer :=
  LinearEquiv.ofBijective S.splitCoordinates
    ⟨S.splitCoordinates_injective, S.splitCoordinates_surjective⟩

/-- Modulo constants, the residue map is canonically an equivalence onto the
transfer kernel.  Unlike `splitCoordinatesEquiv`, this quotient statement uses
no splitting choice. -/
noncomputable def quotientConstantsEquivTransferKernel :
    (W ⧸ LinearMap.range S.constant) ≃ₗ[F2] LinearMap.ker S.transfer :=
  (Submodule.quotEquivOfEq (LinearMap.range S.constant)
      (LinearMap.ker S.residue) S.exact_at_witt.linearMap_ker_eq.symm).trans
    (S.residue.quotKerEquivRange.trans
      (LinearEquiv.ofEq (LinearMap.range S.residue)
        (LinearMap.ker S.transfer)
        S.exact_at_residue.linearMap_ker_eq.symm))

section FiniteSupport

variable {Place : Type*} (T : ResidueSequence C W (Place →₀ F2))

/-- The nonzero place set of an individual Witt class is finite by
construction of the direct sum. -/
noncomputable def relevantPlaces (w : W) : Finset Place :=
  (T.residue w).support

theorem residue_eq_zero_of_not_mem_relevantPlaces
    [DecidableEq Place] (w : W) {v : Place}
    (hv : v ∉ T.relevantPlaces w) : T.residue w v = 0 := by
  by_contra hne
  exact hv (Finsupp.mem_support_iff.mpr hne)

/-- The finite-support tuple still obeys the single global transfer relation. -/
theorem residue_transfer_relation (w : W) :
    T.transfer (T.residue w) = 0 :=
  T.transfer_residue w

end FiniteSupport

end ResidueSequence

end Ogdoad.WittRealizationExact
