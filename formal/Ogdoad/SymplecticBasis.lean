import Mathlib

/-!
# Symplectic decomposition of a finite alternating space

Mathlib v4.32 does not yet provide the characteristic-free symplectic-basis
existence theorem needed by the Ogdoad papers.  This file supplies it as a
finite recursive proof object.  Each node splits a normalized alternating
plane from its orthogonal complement; the leaf is exactly the polar radical.
The object is a basis decomposition rather than a mere list of locally paired
vectors: its `Disjoint` and `sup` fields certify a direct sum at every level.
-/

noncomputable section

namespace Ogdoad.SymplecticBasis

open scoped CharTwo
set_option linter.unusedSectionVars false

variable {K V : Type*} [Field K] [CharP K 2]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The plane spanned by a prospective symplectic pair. -/
def plane (e f : V) : Submodule K V :=
  Submodule.span K ({e, f} : Set V)

omit [CharP K 2] [FiniteDimensional K V] in
private theorem left_mem_plane (e f : V) : e ∈ plane (K := K) e f := by
  rw [plane, Submodule.mem_span_pair]
  exact ⟨1, 0, by simp⟩

omit [CharP K 2] [FiniteDimensional K V] in
private theorem right_mem_plane (e f : V) : f ∈ plane (K := K) e f := by
  rw [plane, Submodule.mem_span_pair]
  exact ⟨0, 1, by simp⟩

/-- A finite recursive symplectic basis of a subspace `S`.  A `pair` node
records `S = span(e,f) ⊕ W`, with `W` the part of `S` orthogonal to that
plane; recursion therefore makes distinct recorded planes mutually
orthogonal.  A `radical` leaf records that the remaining restriction is zero. -/
inductive Decomposition (B : LinearMap.BilinForm K V) :
    Submodule K V → Type _
  | radical (S : Submodule K V)
      (zero_on : ∀ x ∈ S, ∀ y ∈ S, B x y = 0) : Decomposition B S
  | pair {S : Submodule K V} (e f : V)
      (left_mem : e ∈ S) (right_mem : f ∈ S)
      (pairing : B e f = 1)
      (disjoint : Disjoint (plane (K := K) e f)
        (S ⊓ B.orthogonal (plane (K := K) e f)))
      (spans : plane (K := K) e f ⊔
        (S ⊓ B.orthogonal (plane (K := K) e f)) = S)
      (tail : Decomposition B
        (S ⊓ B.orthogonal (plane (K := K) e f))) : Decomposition B S

/-- A normalized alternating pair spans a nondegenerate plane. -/
private theorem restrict_plane_nondegenerate
    (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt)
    {e f : V} (hef : B e f = 1) :
    (B.restrict (plane (K := K) e f)).Nondegenerate := by
  have hfe : B f e = 1 := by
    calc
      B f e = -B e f := (hAlt.neg_eq e f).symm
      _ = 1 := by simp [hef]
  constructor
  · intro x hx
    apply Subtype.ext
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp x.property
    have he := hx ⟨e, left_mem_plane (K := K) e f⟩
    have hf := hx ⟨f, right_mem_plane (K := K) e f⟩
    change B (x : V) e = 0 at he
    change B (x : V) f = 0 at hf
    rw [← hab] at he hf
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      hAlt.self_eq_zero, hef, hfe, smul_eq_mul, mul_zero, mul_one,
      add_zero, zero_add] at he hf
    rw [← hab]
    rw [he, hf]
    simp
  · intro x hx
    apply Subtype.ext
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp x.property
    have he := hx ⟨e, left_mem_plane (K := K) e f⟩
    have hf := hx ⟨f, right_mem_plane (K := K) e f⟩
    change B e (x : V) = 0 at he
    change B f (x : V) = 0 at hf
    rw [← hab] at he hf
    simp only [map_add, map_smul, hAlt.self_eq_zero, hef, hfe,
      smul_eq_mul, mul_zero, mul_one, add_zero, zero_add] at he hf
    rw [← hab]
    rw [hf, he]
    simp

/-- A normalized pair is linearly independent; in particular its plane is
genuinely two-dimensional. -/
theorem pair_linearIndependent (B : LinearMap.BilinForm K V)
    (hAlt : B.IsAlt) {e f : V} (hef : B e f = 1) :
    LinearIndependent K ![e, f] := by
  rw [linearIndependent_fin2]
  change f ≠ 0 ∧ ∀ a : K, a • f ≠ e
  constructor
  · intro hf
    rw [hf, map_zero] at hef
    exact one_ne_zero hef.symm
  · intro a h
    have := congrArg (fun z => B z f) h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
      hAlt.self_eq_zero, mul_zero, hef] at this
    exact zero_ne_one this

/-- Every finite-dimensional alternating space has a complete symplectic
decomposition, including its radical.  Classical choice makes this a fixed
function of `B` and the current subspace; no extra symplectic-family premise
is accepted. -/
theorem exists_decomposition (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt)
    (S : Submodule K V) : Nonempty (Decomposition B S) := by
  classical
  let rec build (S : Submodule K V) : Decomposition B S := by
    by_cases hzero : ∀ x ∈ S, ∀ y ∈ S, B x y = 0
    · exact .radical S hzero
    · push Not at hzero
      have hwitness : Nonempty { p : V × V //
          p.1 ∈ S ∧ p.2 ∈ S ∧ B p.1 p.2 ≠ 0 } := by
        rcases hzero with ⟨e, heS, f₀, hf₀S, hef₀⟩
        exact ⟨⟨(e, f₀), heS, hf₀S, hef₀⟩⟩
      let witness := Classical.choice hwitness
      let e : V := witness.1.1
      let f₀ : V := witness.1.2
      have heS : e ∈ S := witness.2.1
      have hf₀S : f₀ ∈ S := witness.2.2.1
      have hef₀ : B e f₀ ≠ 0 := witness.2.2.2
      let c : K := B e f₀
      let f : V := c⁻¹ • f₀
      have hc : c ≠ 0 := hef₀
      have hfS : f ∈ S := S.smul_mem c⁻¹ hf₀S
      have hef : B e f = 1 := by
        simp only [f, map_smul, smul_eq_mul, c]
        exact inv_mul_cancel₀ hc
      let P : Submodule K V := plane (K := K) e f
      let W : Submodule K V := S ⊓ B.orthogonal P
      have hPnondeg : (B.restrict P).Nondegenerate := by
        simpa [P] using restrict_plane_nondegenerate B hAlt hef
      have hcompl : IsCompl P (B.orthogonal P) :=
        B.isCompl_orthogonal_of_restrict_nondegenerate hAlt.isRefl hPnondeg
      have hPleS : P ≤ S := by
        change plane (K := K) e f ≤ S
        rw [plane, Submodule.span_le]
        intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hx
        · exact heS
        · simpa only [Set.mem_singleton_iff] using hx ▸ hfS
      have hdisjoint : Disjoint P W := by
        exact hcompl.disjoint.mono le_rfl inf_le_right
      have hspans : P ⊔ W = S := by
        apply le_antisymm
        · exact sup_le hPleS inf_le_left
        · intro s hs
          have hsTop : s ∈ P ⊔ B.orthogonal P := by
            rw [hcompl.sup_eq_top]
            exact Submodule.mem_top
          obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hsTop
          have hpS : p ∈ S := hPleS hp
          have hwS : w ∈ S := by
            have : s - p ∈ S := S.sub_mem hs hpS
            rw [← hpw] at this
            simpa using this
          exact Submodule.mem_sup.mpr ⟨p, hp, w, ⟨hwS, hw⟩, hpw⟩
      have hWlt : Module.finrank K W < Module.finrank K S := by
        apply Submodule.finrank_lt_finrank_of_lt
        refine lt_of_le_of_ne inf_le_left ?_
        intro hWS
        have heW : e ∈ W := by rw [hWS]; exact heS
        have heP : e ∈ P := by simpa [P] using left_mem_plane (K := K) e f
        have he0 : e = 0 := by
          exact (Submodule.disjoint_def.mp hdisjoint) e heP heW
        rw [he0, map_zero] at hef
        exact one_ne_zero hef.symm
      exact .pair e f heS hfS hef
        (by simpa [P, W] using hdisjoint)
        (by simpa [P, W] using hspans)
        (build W)
  termination_by Module.finrank K S
  decreasing_by exact hWlt
  exact ⟨build S⟩

/-- Root form: a reusable full symplectic basis theorem for every finite
alternating form. -/
noncomputable def decomposition (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt) :
    Decomposition B ⊤ :=
  Classical.choice (exists_decomposition B hAlt ⊤)

end Ogdoad.SymplecticBasis
