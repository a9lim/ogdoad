import Ogdoad.SymplecticBasis
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Deterministic public Witt frames

This module flattens `SymplecticBasis.Decomposition` into an actual basis.
The basis carries a public partial matching: matched basis vectors pair to
one, and every other basis pairing is zero.  Classical choice fixes a single
frame as a function of the alternating form, which is the deterministic
frame consumed by the Gold arena.
-/

noncomputable section

namespace Ogdoad.WittFrame

open scoped CharTwo
open Module
set_option linter.unusedSimpArgs false

variable {K V : Type*} [Field K] [CharP K 2]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- An adapted basis and its public matching. -/
structure Frame (B : LinearMap.BilinForm K V) (S : Submodule K V) where
  Index : Type*
  fintypeIndex : Fintype Index
  decEqIndex : DecidableEq Index
  basis : Basis Index K S
  mate : Index → Option Index
  mate_ne_self : ∀ i, mate i ≠ some i
  mate_symm : ∀ {i j}, mate i = some j → mate j = some i
  pairing : ∀ i j, B (basis i : V) (basis j : V) =
    if mate i = some j then 1 else 0

attribute [instance] Frame.fintypeIndex Frame.decEqIndex

private def pairFamily (e f : V) : Fin 2 → V := ![e, f]

/-- The normalized pair is a basis of its plane. -/
private def planeBasis (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt)
    {e f : V} (hef : B e f = 1) :
    Basis (Fin 2) K (SymplecticBasis.plane (K := K) e f) := by
  let P := SymplecticBasis.plane (K := K) e f
  let v : Fin 2 → P := fun i ↦ ⟨pairFamily e f i, by
    fin_cases i
    · change e ∈ Submodule.span K ({e, f} : Set V)
      rw [Submodule.mem_span_pair]
      exact ⟨1, 0, by simp [pairFamily]⟩
    · change f ∈ Submodule.span K ({e, f} : Set V)
      rw [Submodule.mem_span_pair]
      exact ⟨0, 1, by simp [pairFamily]⟩⟩
  have hli : LinearIndependent K v := by
    apply LinearIndependent.of_comp (Submodule.subtype P)
    simpa [Function.comp_def, v, pairFamily] using
      SymplecticBasis.pair_linearIndependent B hAlt hef
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    intro x _
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp x.property
    have hv0 : v 0 ∈ Submodule.span K (Set.range v) :=
      Submodule.subset_span (Set.mem_range_self 0)
    have hv1 : v 1 ∈ Submodule.span K (Set.range v) :=
      Submodule.subset_span (Set.mem_range_self 1)
    have := (Submodule.span K (Set.range v)).add_mem
      ((Submodule.span K (Set.range v)).smul_mem a hv0)
      ((Submodule.span K (Set.range v)).smul_mem b hv1)
    convert this using 1
    apply Subtype.ext
    simpa [v, pairFamily] using hab.symm
  exact Basis.mk hli hspan

/-- Turn a certified internal direct sum `P ⊕ W = S` into the corresponding
linear equivalence. -/
def addEquiv {P W S : Submodule K V}
    (hdisjoint : Disjoint P W) (hspans : P ⊔ W = S) :
    (P × W) ≃ₗ[K] S := by
  let addMap : (P × W) →ₗ[K] S :=
    { toFun := fun x ↦ ⟨(x.1 : V) + (x.2 : V), by
        rw [← hspans]
        exact Submodule.mem_sup.mpr ⟨x.1, x.1.property, x.2, x.2.property, rfl⟩⟩
      map_add' := by intro x y; apply Subtype.ext; simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by intro a x; apply Subtype.ext; simp [smul_add] }
  apply LinearEquiv.ofBijective addMap
  constructor
  · intro x y hxy
    have hv : (x.1 : V) - (y.1 : V) = -((x.2 : V) - (y.2 : V)) := by
      have := congrArg Subtype.val hxy
      change (x.1 : V) + (x.2 : V) = (y.1 : V) + (y.2 : V) at this
      apply eq_neg_of_add_eq_zero_left
      calc
        (x.1 : V) - (y.1 : V) + ((x.2 : V) - (y.2 : V)) =
            ((x.1 : V) + (x.2 : V)) - ((y.1 : V) + (y.2 : V)) := by abel
        _ = 0 := sub_eq_zero.mpr this
    have hp : (x.1 : V) - (y.1 : V) ∈ P := P.sub_mem x.1.property y.1.property
    have hw : -((x.2 : V) - (y.2 : V)) ∈ W :=
      W.neg_mem (W.sub_mem x.2.property y.2.property)
    have hz : (x.1 : V) - (y.1 : V) = 0 :=
      Submodule.disjoint_def.mp hdisjoint _ hp (hv.symm ▸ hw)
    apply Prod.ext
    · apply Subtype.ext
      exact sub_eq_zero.mp hz
    · apply Subtype.ext
      have hneg := congrArg (fun z : V ↦ -z) hv
      have : (x.2 : V) - (y.2 : V) = 0 := by simpa [hz] using hneg.symm
      exact sub_eq_zero.mp this
  · intro s
    have hs : (s : V) ∈ P ⊔ W := by rw [hspans]; exact s.property
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hs
    exact ⟨(⟨p, hp⟩, ⟨w, hw⟩), by
      apply Subtype.ext
      exact hpw⟩

private theorem planeBasis_zero (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt)
    {e f : V} (hef : B e f = 1) :
    ((planeBasis B hAlt hef 0 : SymplecticBasis.plane (K := K) e f) : V) = e := by
  simp [planeBasis, pairFamily, Basis.mk_apply]

private theorem planeBasis_one (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt)
    {e f : V} (hef : B e f = 1) :
    ((planeBasis B hAlt hef 1 : SymplecticBasis.plane (K := K) e f) : V) = f := by
  simp [planeBasis, pairFamily, Basis.mk_apply]

/-- Flatten a recursive decomposition into an actual adapted basis. -/
def ofDecomposition (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt)
    {S : Submodule K V} (d : SymplecticBasis.Decomposition B S) : Frame B S :=
  d.rec (motive := fun S _ ↦ Frame B S)
    (fun S hzero ↦ by
      let b := Module.Free.chooseBasis K S
      exact
        { Index := Module.Free.ChooseBasisIndex K S
          fintypeIndex := Fintype.ofFinite _
          decEqIndex := Classical.decEq _
          basis := b
          mate := fun _ ↦ none
          mate_ne_self := by simp
          mate_symm := by simp
          pairing := by
            intro i j
            simpa using hzero (b i : V) (b i).property (b j : V) (b j).property })
    (fun {S} e f heS hfS hef hdisjoint hspans tail tailFrame ↦ by
      let P := SymplecticBasis.plane (K := K) e f
      let W := S ⊓ B.orthogonal P
      let bP := planeBasis B hAlt hef
      let equiv := addEquiv hdisjoint hspans
      let b := (bP.prod tailFrame.basis).map equiv
      let mate : (Fin 2 ⊕ tailFrame.Index) → Option (Fin 2 ⊕ tailFrame.Index)
        | .inl 0 => some (.inl 1)
        | .inl 1 => some (.inl 0)
        | .inr i => (tailFrame.mate i).map Sum.inr
      letI : Fintype tailFrame.Index := tailFrame.fintypeIndex
      letI : DecidableEq tailFrame.Index := tailFrame.decEqIndex
      exact
        { Index := Fin 2 ⊕ tailFrame.Index
          fintypeIndex := inferInstance
          decEqIndex := inferInstance
          basis := b
          mate := mate
          mate_ne_self := by
            intro i
            rcases i with i | i
            · fin_cases i <;> simp [mate]
            · intro h
              apply tailFrame.mate_ne_self i
              simpa [mate] using h
          mate_symm := by
            intro i j hij
            rcases i with i | i
            · fin_cases i
              · change some (Sum.inl 1) = some j at hij
                have hj : Sum.inl 1 = j := Option.some.inj hij
                subst j
                simp [mate]
              · change some (Sum.inl 0) = some j at hij
                have hj : Sum.inl 0 = j := Option.some.inj hij
                subst j
                simp [mate]
            · cases hmi : tailFrame.mate i with
              | none => simp [mate, hmi] at hij
              | some k =>
                  have hs : some (Sum.inr k) = some j := by
                    simpa [mate, hmi] using hij
                  have hj : Sum.inr k = j := Option.some.inj hs
                  subst j
                  simpa [mate] using tailFrame.mate_symm hmi
          pairing := by
            intro i j
            rcases i with i | i <;> rcases j with j | j
            · fin_cases i <;> fin_cases j
              · simp [b, bP, equiv, mate, Basis.prod_apply_inl_fst,
                  Basis.prod_apply_inl_snd, addEquiv, hAlt.self_eq_zero]
              · simp [b, bP, equiv, mate, Basis.prod_apply_inl_fst,
                  Basis.prod_apply_inl_snd, addEquiv, planeBasis_zero,
                  planeBasis_one, hef]
              · have hfe : B f e = 1 := by
                  calc
                    B f e = -B e f := (hAlt.neg_eq e f).symm
                    _ = 1 := by simp [hef]
                simp [b, bP, equiv, mate, Basis.prod_apply_inl_fst,
                  Basis.prod_apply_inl_snd, addEquiv, planeBasis_zero,
                  planeBasis_one, hfe]
              · simp [b, bP, equiv, mate, Basis.prod_apply_inl_fst,
                  Basis.prod_apply_inl_snd, addEquiv, hAlt.self_eq_zero]
            · have hjW : ((tailFrame.basis j : W) : V) ∈ B.orthogonal P :=
                  (tailFrame.basis j).property.2
              have hzero : B (pairFamily e f i) (tailFrame.basis j : V) = 0 := by
                apply hjW
                fin_cases i
                · change e ∈ Submodule.span K ({e, f} : Set V)
                  rw [Submodule.mem_span_pair]
                  exact ⟨1, 0, by simp [pairFamily]⟩
                · change f ∈ Submodule.span K ({e, f} : Set V)
                  rw [Submodule.mem_span_pair]
                  exact ⟨0, 1, by simp [pairFamily]⟩
              fin_cases i <;> simpa [b, bP, equiv, mate, Basis.prod_apply_inl_fst,
                Basis.prod_apply_inl_snd, Basis.prod_apply_inr_fst,
                Basis.prod_apply_inr_snd, addEquiv, planeBasis_zero,
                planeBasis_one, pairFamily] using hzero
            · have hiW : ((tailFrame.basis i : W) : V) ∈ B.orthogonal P :=
                  (tailFrame.basis i).property.2
              have hzero : B (tailFrame.basis i : V) (pairFamily e f j) = 0 := by
                have hright : B (pairFamily e f j) (tailFrame.basis i : V) = 0 := by
                  apply hiW
                  fin_cases j
                  · change e ∈ Submodule.span K ({e, f} : Set V)
                    rw [Submodule.mem_span_pair]
                    exact ⟨1, 0, by simp [pairFamily]⟩
                  · change f ∈ Submodule.span K ({e, f} : Set V)
                    rw [Submodule.mem_span_pair]
                    exact ⟨0, 1, by simp [pairFamily]⟩
                calc
                  B (tailFrame.basis i : V) (pairFamily e f j) =
                      -B (pairFamily e f j) (tailFrame.basis i : V) :=
                    (hAlt.neg_eq (pairFamily e f j) (tailFrame.basis i : V)).symm
                  _ = 0 := by rw [hright]; simp
              fin_cases j <;> simpa [b, bP, equiv, mate, Basis.prod_apply_inl_fst,
                Basis.prod_apply_inl_snd, Basis.prod_apply_inr_fst,
                Basis.prod_apply_inr_snd, addEquiv, planeBasis_zero,
                planeBasis_one, pairFamily] using hzero
            · simpa [b, equiv, mate, Basis.prod_apply_inr_fst,
                Basis.prod_apply_inr_snd, addEquiv] using tailFrame.pairing i j })

/-- The fixed public frame chosen from the form alone. -/
def frame (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt) : Frame B ⊤ :=
  ofDecomposition B hAlt (SymplecticBasis.decomposition B hAlt)

end Ogdoad.WittFrame
