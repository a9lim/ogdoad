import Ogdoad.Off
import Ogdoad.SymplecticBasis
import Ogdoad.WittFrame
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Complete finite-dimensional classification in characteristic two

This file closes the structural theorem used in `transfinite_arf.tex` under
the exact hypotheses needed by the proof: Frobenius and Artin--Schreier are
surjective.  It combines the recursive symplectic decomposition with a
hyperbolic change of basis on every nondegenerate plane and the complete
rank-zero/rank-one description of the polar radical.

The result is packaged as data, not merely a proposition: `normalForm`
returns a fixed recursive orthogonal decomposition and the transformed
hyperbolic pair at every node.
-/

noncomputable section

namespace Ogdoad.CharTwoClassification

open scoped BigOperators CharTwo
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

variable {K V : Type*} [Field K] [CharP K 2]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

abbrev Decomposition (Q : QuadraticForm K V) :=
  SymplecticBasis.Decomposition Q.polarBilin

/-- The complete normal-form certificate for a zero-polar restriction.
The functional is either zero, or has a displayed unit vector and a
codimension-one kernel. -/
structure RadicalCertificate (Q : QuadraticForm K V)
    (S : Submodule K V) where
  linear : S →ₗ[K] K
  quadratic_eq_square : ∀ x : S, Q x = linear x ^ 2
  shape : linear = 0 ∨ ∃ e : S, linear e = 1 ∧
    Module.finrank K (LinearMap.ker linear) + 1 = Module.finrank K S

/-- A node certificate records the actual hyperbolic replacement inside the
same symplectic plane. -/
structure PlaneCertificate (Q : QuadraticForm K V) (e f : V) where
  left : V
  right : V
  hyperbolic : Off.IsHyperbolicPair Q left right
  same_span : Off.pairSpan (K := K) left right = Off.pairSpan (K := K) e f

/-- A complete recursive normal form attached to a symplectic decomposition.
The recursion preserves the certified orthogonal direct sums stored in `d`;
at a leaf it supplies the full radical normal form. -/
def NormalForm (Q : QuadraticForm K V) :
    {S : Submodule K V} → Decomposition Q S → Type _
  | _, .radical S _ => RadicalCertificate Q S
  | _, @SymplecticBasis.Decomposition.pair _ _ _ _ _ _ S e f _ _ _ _ _ tail =>
      PlaneCertificate Q e f × NormalForm Q tail

/-- Frobenius surjectivity for a perfect characteristic-two field, stated in
the elementary square form consumed by the quadratic-form proof. -/
theorem frobenius_surjective_of_perfect [PerfectField K] :
    Function.Surjective (fun x : K => x ^ 2) := by
  intro y
  obtain ⟨x, hx⟩ := surjective_frobenius K 2 y
  exact ⟨x, by simpa only [frobenius_def] using hx⟩

omit [FiniteDimensional K V] in
/-- The polar form of a quadratic form is alternating in characteristic two. -/
private theorem polarBilin_isAlt (Q : QuadraticForm K V) :
    Q.polarBilin.IsAlt := by
  intro x
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
  simp

/-- Assemble the complete normal form along any supplied decomposition. -/
def normalFormAlong
    (hFrob : Function.Surjective (fun x : K => x ^ 2))
    (hAS : Function.Surjective (fun x : K => x ^ 2 + x))
    (Q : QuadraticForm K V) :
    {S : Submodule K V} → (d : Decomposition Q S) → NormalForm Q d
  | _, .radical S hzero => by
      let QR : QuadraticForm K S := Q.restrict S
      have hpolar : ∀ x y : S, QR.polarBilin x y = 0 := by
        intro x y
        change Q.polarBilin (x : V) (y : V) = 0
        exact hzero x x.property y y.property
      let witness : RadicalCertificate Q S := by
        let h := Off.zero_polar_normal_form_of_frobenius hFrob QR hpolar
        let ell := Classical.choose h
        have hell := Classical.choose_spec h
        exact ⟨ell, hell.1, hell.2⟩
      exact witness
  | _, @SymplecticBasis.Decomposition.pair _ _ _ _ _ _ S e f he hf hef
      hdisjoint hspans tail => by
      let witness : PlaneCertificate Q e f := by
        let h := Off.hyperbolic_pair_of_polar_eq_one_of_artinSchreier hAS Q hef
        let e' := Classical.choose h
        let he' := Classical.choose_spec h
        let f' := Classical.choose he'
        have hf' := Classical.choose_spec he'
        exact ⟨e', f', hf'.1, hf'.2⟩
      exact ⟨witness, normalFormAlong hFrob hAS Q tail⟩

/-- Root theorem: every finite-dimensional quadratic form over a perfect
characteristic-two field with surjective Artin--Schreier map is an orthogonal
sum of hyperbolic planes and exactly one of the two radical forms `Z^s` or
`A ⊥ Z^(s-1)`.  The returned object contains all basis changes and all
direct-sum witnesses. -/
def normalForm [PerfectField K]
    (hAS : Function.Surjective (fun x : K => x ^ 2 + x))
    (Q : QuadraticForm K V) :
    NormalForm Q (SymplecticBasis.decomposition Q.polarBilin (polarBilin_isAlt Q)) :=
  normalFormAlong (frobenius_surjective_of_perfect (K := K)) hAS Q
    (SymplecticBasis.decomposition Q.polarBilin (polarBilin_isAlt Q))

/-- Algebraically closed specialization used as the set-sized proxy for the
finite-dimensional `On₂` argument. -/
def algebraicallyClosedNormalForm [IsAlgClosed K] (Q : QuadraticForm K V) :
    NormalForm Q (SymplecticBasis.decomposition Q.polarBilin (polarBilin_isAlt Q)) :=
  normalForm (Off.artinSchreier_surjective (K := K)) Q

abbrev NormalSpace (K : Type*) (r s : Nat) :=
  (Fin r → K × K) × (Fin s → K)

def hyperbolicHalf : LinearMap.BilinForm K (K × K) where
  toFun x :=
    { toFun := fun y => x.1 * y.2
      map_add' := by intro y z; simp [mul_add]
      map_smul' := by intro a y; simp; ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    simp [add_mul]
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    simp
    ring

def hyperbolic : QuadraticForm K (K × K) := hyperbolicHalf.toQuadraticMap

@[simp] theorem hyperbolic_apply (x : K × K) : hyperbolic x = x.1 * x.2 := rfl

def radicalForm (s : Nat) (anis : Bool) : QuadraticForm K (Fin s → K) :=
  QuadraticMap.pi fun i => if anis ∧ i.val = 0 then QuadraticMap.sq else 0

def canonicalForm (r s : Nat) (anis : Bool) : QuadraticForm K (NormalSpace K r s) :=
  (QuadraticMap.pi fun _ : Fin r => hyperbolic).prod (radicalForm s anis)

@[simp] theorem radicalForm_apply (x : Fin s → K) :
    radicalForm s anis x = ∑ i, if anis ∧ i.val = 0 then x i ^ 2 else 0 := by
  simp only [radicalForm, QuadraticMap.pi_apply]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all [QuadraticMap.sq_apply, pow_two]

@[simp] theorem radicalForm_true_apply_of_pos (hs : 0 < s) (x : Fin s → K) :
    radicalForm s true x = x ⟨0, hs⟩ ^ 2 := by
  rw [radicalForm_apply]
  simp only [true_and]
  rw [Finset.sum_eq_single ⟨0, hs⟩]
  · simp
  · intro b _ hne
    split_ifs with hb
    · exact (hne (Fin.ext hb)).elim
    · rfl
  · simp

@[simp] theorem canonicalForm_apply (x : NormalSpace K r s) :
    canonicalForm r s anis x =
      (∑ i, (x.1 i).1 * (x.1 i).2) +
        ∑ i, if anis ∧ i.val = 0 then x.2 i ^ 2 else 0 := by
  rw [canonicalForm, QuadraticMap.prod_apply, QuadraticMap.pi_apply,
    radicalForm_apply]
  apply congrArg₂ (· + ·) ?_ rfl
  apply Finset.sum_congr rfl
  intro i _
  exact hyperbolic_apply (x.1 i)

def finSuccPiEquiv (A : Type*) [AddCommGroup A] [Module K A] (r : Nat) :
    (Fin (r + 1) → A) ≃ₗ[K] A × (Fin r → A) :=
  LinearEquiv.piCongrLeft K (fun _ ↦ A) (finSuccEquiv r) ≪≫ₗ
    LinearEquiv.piOptionEquivProd K

def consEquiv (r : Nat) : (K × (Fin r → K)) ≃ₗ[K] (Fin (r + 1) → K) :=
  { toFun := fun x ↦ Fin.cons x.1 x.2
    invFun := fun x ↦ (x 0, Fin.tail x)
    left_inv := by intro x; ext <;> simp
    right_inv := by intro x; ext <;> simp
    map_add' := by
      intro x y
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
    map_smul' := by
      intro a x
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp }

@[simp] theorem consEquiv_zero (x : K × (Fin r → K)) :
    consEquiv (K := K) r x 0 = x.1 := by
  rfl

def prependEquiv (r s : Nat) :
    ((K × K) × NormalSpace K r s) ≃ₗ[K] NormalSpace K (r + 1) s :=
  { toFun := fun x ↦ (Fin.cons x.1 x.2.1, x.2.2)
    invFun := fun x ↦ (x.1 0, (Fin.tail x.1, x.2))
    left_inv := by intro x; ext <;> simp
    right_inv := by intro x; ext <;> simp
    map_add' := by
      intro x y
      apply Prod.ext
      · funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
      · rfl
    map_smul' := by
      intro a x
      apply Prod.ext
      · funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
      · rfl }

@[simp] theorem prependEquiv_plane (p : K × K) (tail : NormalSpace K r s) :
    ((prependEquiv (K := K) r s) (p, tail)).1 0 = p := by
  simp [prependEquiv, finSuccPiEquiv]

@[simp] theorem prependEquiv_tail_plane (p : K × K) (tail : NormalSpace K r s)
    (i : Fin r) :
    ((prependEquiv (K := K) r s) (p, tail)).1 i.succ = tail.1 i := by
  simp [prependEquiv, finSuccPiEquiv]

@[simp] theorem prependEquiv_radical (p : K × K) (tail : NormalSpace K r s) :
    ((prependEquiv (K := K) r s) (p, tail)).2 = tail.2 := by
  rfl

def planeEquiv (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt)
    {e f : V} (hef : B e f = 1) :
    Ogdoad.SymplecticBasis.plane (K := K) e f ≃ₗ[K] K × K :=
  { toFun := fun x ↦ (B (x : V) f, B e (x : V))
    invFun := fun p ↦ ⟨p.1 • e + p.2 • f, by
      rw [Ogdoad.SymplecticBasis.plane, Submodule.mem_span_pair]
      exact ⟨p.1, p.2, rfl⟩⟩
    left_inv := by
      intro x
      apply Subtype.ext
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp x.property
      have hfe : B f e = 1 := by
        calc
          B f e = -B e f := (hAlt.neg_eq e f).symm
          _ = 1 := by simp [hef]
      have hxf : B (x : V) f = a := by
        rw [← hab]
        simp [hAlt.self_eq_zero, hef]
      have hex : B e (x : V) = b := by
        rw [← hab]
        simp [hAlt.self_eq_zero, hef]
      change B (x : V) f • e + B e (x : V) • f = (x : V)
      rw [hxf, hex]
      exact hab
    right_inv := by
      intro p
      have hfe : B f e = 1 := by
        calc
          B f e = -B e f := (hAlt.neg_eq e f).symm
          _ = 1 := by simp [hef]
      simp [hAlt.self_eq_zero, hef, hfe]
    map_add' := by intro x y; simp
    map_smul' := by intro a x; simp }

def hyperbolicPairIsometry (Q : QuadraticForm K V)
    {e f : V} (hp : Ogdoad.Off.IsHyperbolicPair Q e f) :
    (Q.restrict (Ogdoad.SymplecticBasis.plane (K := K) e f)).IsometryEquiv hyperbolic where
  toLinearEquiv := planeEquiv Q.polarBilin
    (polarBilin_isAlt Q) hp.polar_eq_one
  map_app' := by
    intro x
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp x.property
    change hyperbolic (Q.polarBilin (x : V) f, Q.polarBilin e (x : V)) = Q (x : V)
    rw [show (x : V) = a • e + b • f from hab.symm, hyperbolic_apply]
    have hfe : Q.polarBilin f e = 1 := by
      calc
        Q.polarBilin f e = Q.polarBilin e f := by
          simpa only [QuadraticMap.polarBilin_apply_apply] using
            QuadraticMap.polar_comm Q f e
        _ = 1 := hp.polar_eq_one
    have hxf : Q.polarBilin (a • e + b • f) f = a := by
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, (polarBilin_isAlt Q).self_eq_zero,
        hp.polar_eq_one, mul_one, mul_zero, add_zero]
    have hex : Q.polarBilin e (a • e + b • f) = b := by
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, (polarBilin_isAlt Q).self_eq_zero,
        hp.polar_eq_one, mul_zero, mul_one, zero_add]
    rw [hxf, hex, QuadraticMap.map_add Q (a • e) (b • f),
      QuadraticMap.map_smul Q a e, QuadraticMap.map_smul Q b f]
    have hpolar : QuadraticMap.polar Q e f = 1 := by
      simpa only [QuadraticMap.polarBilin_apply_apply] using hp.polar_eq_one
    rw [QuadraticMap.polar_smul_left Q a e (b • f),
      QuadraticMap.polar_smul_right Q b e f]
    rw [hpolar]
    simp [hp.left_isotropic, hp.right_isotropic]

def orthogonalSumIsometry (Q : QuadraticForm K V)
    {P W S : Submodule K V}
    (hdisjoint : Disjoint P W) (hspans : P ⊔ W = S)
    (horth : ∀ p : P, ∀ w : W, Q.polarBilin (p : V) (w : V) = 0) :
    (Q.restrict S).IsometryEquiv ((Q.restrict P).prod (Q.restrict W)) where
  toLinearEquiv := (Ogdoad.WittFrame.addEquiv hdisjoint hspans).symm
  map_app' := by
    intro x
    let y := (Ogdoad.WittFrame.addEquiv hdisjoint hspans).symm x
    have hy : Ogdoad.WittFrame.addEquiv hdisjoint hspans y = x :=
      (Ogdoad.WittFrame.addEquiv hdisjoint hspans).apply_symm_apply x
    have hx : (x : V) = (y.1 : V) + (y.2 : V) := by
      exact (congrArg Subtype.val hy).symm
    change Q (y.1 : V) + Q (y.2 : V) = Q (x : V)
    rw [hx, QuadraticMap.map_add Q (y.1 : V) (y.2 : V)]
    have hp : QuadraticMap.polar Q (y.1 : V) (y.2 : V) = 0 := by
      simpa only [QuadraticMap.polarBilin_apply_apply] using horth y.1 y.2
    rw [hp, add_zero]

def splitFunctionalEquiv (ell : V →ₗ[K] K) (e : V) (he : ell e = 1) :
    V ≃ₗ[K] K × LinearMap.ker ell :=
  { toFun := fun x ↦ (ell x, ⟨x - ell x • e, by simp [he]⟩)
    invFun := fun p ↦ p.1 • e + (p.2 : V)
    left_inv := by intro x; simp
    right_inv := by
      intro p
      apply Prod.ext
      · simp [he]
      · apply Subtype.ext
        simp [he]
    map_add' := by
      intro x y
      apply Prod.ext
      · simp
      · apply Subtype.ext
        simp [add_smul]
        abel
    map_smul' := by
      intro a x
      apply Prod.ext
      · simp
      · apply Subtype.ext
        simp [smul_sub, smul_smul] }

def emptyPlanesEquiv (A : Type*) [AddCommGroup A] [Module K A] :
    A ≃ₗ[K] (Fin 0 → K × K) × A :=
  (LinearEquiv.uniqueProd (R := K) (M := A) (M₂ := Fin 0 → K × K)).symm

def zeroRadicalIsometry (Q : QuadraticForm K V) {S : Submodule K V}
    (c : RadicalCertificate Q S)
    (hell : c.linear = 0) :
    (Q.restrict S).IsometryEquiv (canonicalForm 0 (Module.finrank K S) false) := by
  let coord : S ≃ₗ[K] (Fin (Module.finrank K S) → K) :=
    LinearEquiv.ofFinrankEq S (Fin (Module.finrank K S) → K) (by simp)
  let full := coord.trans (emptyPlanesEquiv (K := K) (Fin (Module.finrank K S) → K))
  exact
    { toLinearEquiv := full
      map_app' := by
        intro x
        rw [canonicalForm_apply]
        simp only [Finset.univ_eq_empty, Finset.sum_empty, Bool.false_eq_true,
          false_and, ↓reduceIte, add_zero]
        have hQ := c.quadratic_eq_square x
        rw [hell] at hQ
        simpa using hQ.symm }

def anisotropicRadicalIsometry (Q : QuadraticForm K V) {S : Submodule K V}
    (c : RadicalCertificate Q S)
    (e : S) (he : c.linear e = 1) :
    (Q.restrict S).IsometryEquiv
      (canonicalForm 0 (Module.finrank K (LinearMap.ker c.linear) + 1) true) := by
  let k := Module.finrank K (LinearMap.ker c.linear)
  let tail : LinearMap.ker c.linear ≃ₗ[K] (Fin k → K) :=
    LinearEquiv.ofFinrankEq (LinearMap.ker c.linear) (Fin k → K) (by simp [k])
  let coord : S ≃ₗ[K] (Fin (k + 1) → K) :=
    (splitFunctionalEquiv c.linear e he).trans
      ((LinearEquiv.prodCongr (LinearEquiv.refl K K) tail).trans
        (consEquiv (K := K) k))
  let full := coord.trans (emptyPlanesEquiv (K := K) (Fin (k + 1) → K))
  exact
    { toLinearEquiv := full
      map_app' := by
        intro x
        rw [canonicalForm, QuadraticMap.prod_apply, QuadraticMap.pi_apply]
        simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
        rw [radicalForm_true_apply_of_pos (Nat.zero_lt_succ k)]
        change coord x 0 ^ 2 = Q x
        have hcoord : coord x 0 = c.linear x := by
          simp [coord, tail, splitFunctionalEquiv]
        rw [hcoord]
        exact (c.quadratic_eq_square x).symm }

def prependIsometry (r s : Nat) (anis : Bool) :
    ((hyperbolic (K := K)).prod (canonicalForm (K := K) r s anis)).IsometryEquiv
      (canonicalForm (K := K) (r + 1) s anis) where
  toLinearEquiv := prependEquiv r s
  map_app' := by
    intro x
    rw [canonicalForm_apply, QuadraticMap.prod_apply, hyperbolic_apply,
      canonicalForm_apply]
    simp [Fin.sum_univ_succ, prependEquiv]
    abel

structure Classification (Q : QuadraticForm K V) (S : Submodule K V) where
  planes : Nat
  radicalDim : Nat
  anisotropic : Bool
  anisotropic_pos : anisotropic = true → 0 < radicalDim
  isometry : (Q.restrict S).IsometryEquiv
    (canonicalForm planes radicalDim anisotropic)

def classificationOfNormalForm (Q : QuadraticForm K V) :
    {S : Submodule K V} →
      (d : Decomposition Q S) →
      NormalForm Q d → Classification Q S
  | _, .radical S _, c => by
      classical
      by_cases hell : c.linear = 0
      · exact
          { planes := 0
            radicalDim := Module.finrank K S
            anisotropic := false
            anisotropic_pos := by simp
            isometry := zeroRadicalIsometry Q c hell }
      · have hex : ∃ e : S, c.linear e = 1 ∧
            Module.finrank K (LinearMap.ker c.linear) + 1 = Module.finrank K S :=
          c.shape.resolve_left hell
        let e := Classical.choose hex
        have he := (Classical.choose_spec hex).1
        let k := Module.finrank K (LinearMap.ker c.linear)
        exact
          { planes := 0
            radicalDim := k + 1
            anisotropic := true
            anisotropic_pos := by simp [k]
            isometry := anisotropicRadicalIsometry Q c e he }
  | _, @Ogdoad.SymplecticBasis.Decomposition.pair _ _ _ _ _ _ S e f _ _ _
      hdisjoint hspans tail, nf => by
      change PlaneCertificate Q e f ×
        NormalForm Q tail at nf
      rcases nf with ⟨pc, ntail⟩
      let tailClass := classificationOfNormalForm Q tail ntail
      let P := Ogdoad.SymplecticBasis.plane (K := K) e f
      let W := S ⊓ LinearMap.BilinForm.orthogonal Q.polarBilin P
      have hspan : Ogdoad.SymplecticBasis.plane (K := K) pc.left pc.right = P := by
        simpa [P, Ogdoad.SymplecticBasis.plane, Ogdoad.Off.pairSpan] using pc.same_span
      let planeIso : (Q.restrict P).IsometryEquiv hyperbolic := by
        rw [← hspan]
        exact hyperbolicPairIsometry Q pc.hyperbolic
      let splitIso : (Q.restrict S).IsometryEquiv
          ((Q.restrict P).prod (Q.restrict W)) :=
        orthogonalSumIsometry Q hdisjoint hspans (by
          intro p w
          exact w.property.2 p p.property)
      let combined := splitIso.trans (planeIso.prod tailClass.isometry)
      exact
        { planes := tailClass.planes + 1
          radicalDim := tailClass.radicalDim
          anisotropic := tailClass.anisotropic
          anisotropic_pos := tailClass.anisotropic_pos
          isometry := combined.trans
            (prependIsometry tailClass.planes tailClass.radicalDim
              tailClass.anisotropic) }

def topRestrictionIsometry (Q : QuadraticForm K V) :
    Q.IsometryEquiv (Q.restrict (⊤ : Submodule K V)) where
  toLinearEquiv := Submodule.topEquiv.symm
  map_app' := by intro x; rfl

def classificationAlong
    (hFrob : Function.Surjective (fun x : K => x ^ 2))
    (hAS : Function.Surjective (fun x : K => x ^ 2 + x))
    (Q : QuadraticForm K V)
    (d : Decomposition Q ⊤) : Classification Q ⊤ :=
  classificationOfNormalForm Q d
    (normalFormAlong hFrob hAS Q d)

def classification [PerfectField K]
    (hAS : Function.Surjective (fun x : K => x ^ 2 + x))
    (Q : QuadraticForm K V) : Classification Q ⊤ :=
  let d := Ogdoad.SymplecticBasis.decomposition Q.polarBilin (polarBilin_isAlt Q)
  classificationAlong (frobenius_surjective_of_perfect (K := K))
    hAS Q d

theorem exists_isometry_normalForm [PerfectField K]
    (hAS : Function.Surjective (fun x : K => x ^ 2 + x))
    (Q : QuadraticForm K V) :
    ∃ r s anis, (anis = true → 0 < s) ∧
      Nonempty (Q.IsometryEquiv (canonicalForm r s anis)) := by
  let c := classification hAS Q
  exact ⟨c.planes, c.radicalDim, c.anisotropic, c.anisotropic_pos,
    ⟨(topRestrictionIsometry Q).trans c.isometry⟩⟩

@[simp] theorem finrank_normalSpace (r s : Nat) :
    Module.finrank K (NormalSpace K r s) = 2 * r + s := by
  simp [NormalSpace, Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm]

@[simp] theorem hyperbolic_polar (x y : K × K) :
    QuadraticMap.polar hyperbolic x y = x.1 * y.2 + x.2 * y.1 := by
  rw [QuadraticMap.polar]
  simp only [hyperbolic_apply, Prod.fst_add, Prod.snd_add]
  ring

theorem radicalForm_polar_zero (s : Nat) (anis : Bool) (x y : Fin s → K) :
    QuadraticMap.polar (radicalForm s anis) x y = 0 := by
  rw [QuadraticMap.polar]
  simp only [radicalForm_apply, Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs
  · rw [CharTwo.add_sq]
    ring
  · simp

@[simp] theorem canonicalForm_polar (x y : NormalSpace K r s) :
    QuadraticMap.polar (canonicalForm r s anis) x y =
      ∑ i, ((x.1 i).1 * (y.1 i).2 + (x.1 i).2 * (y.1 i).1) := by
  rw [canonicalForm, QuadraticMap.polar_prod, QuadraticMap.Ring.polar_pi,
    radicalForm_polar_zero]
  simp only [hyperbolic_polar, add_zero]

theorem mem_canonical_polar_ker_iff (x : NormalSpace K r s) :
    x ∈ (canonicalForm r s anis).polarBilin.ker ↔ x.1 = 0 := by
  classical
  simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    QuadraticMap.polarBilin_apply_apply]
  constructor
  · intro h
    funext i
    apply Prod.ext
    · let y : NormalSpace K r s := (Pi.single i (0, 1), 0)
      have hy := h y
      rw [canonicalForm_polar, Finset.sum_eq_single i] at hy
      · simpa [y, Pi.single_apply] using hy
      · intro b _ hne
        simp [y, Pi.single_apply, hne]
      · simp
    · let y : NormalSpace K r s := (Pi.single i (1, 0), 0)
      have hy := h y
      rw [canonicalForm_polar, Finset.sum_eq_single i] at hy
      · simpa [y, Pi.single_apply] using hy
      · intro b _ hne
        simp [y, Pi.single_apply, hne]
      · simp
  · intro hx y
    rw [canonicalForm_polar]
    simp [hx]

def polarKernelEquiv (r s : Nat) (anis : Bool) :
    (Fin s → K) ≃ₗ[K] (canonicalForm (K := K) r s anis).polarBilin.ker :=
  { toFun := fun z ↦ ⟨(0, z), (mem_canonical_polar_ker_iff (0, z)).2 rfl⟩
    invFun := fun x ↦ x.1.2
    left_inv := by intro z; rfl
    right_inv := by
      intro x
      apply Subtype.ext
      apply Prod.ext
      · exact (mem_canonical_polar_ker_iff x.1).1 x.property |>.symm
      · rfl
    map_add' := by intro x y; apply Subtype.ext; apply Prod.ext <;> simp
    map_smul' := by intro a x; apply Subtype.ext; apply Prod.ext <;> simp }

@[simp] theorem finrank_canonical_polar_ker (r s : Nat) (anis : Bool) :
    Module.finrank K (canonicalForm (K := K) r s anis).polarBilin.ker = s := by
  rw [← (polarKernelEquiv (K := K) r s anis).finrank_eq]
  simp

theorem mem_canonical_radical_iff (x : NormalSpace K r s) :
    x ∈ (canonicalForm r s anis).radical ↔
      x.1 = 0 ∧ radicalForm s anis x.2 = 0 := by
  change canonicalForm r s anis x = 0 ∧
      x ∈ (canonicalForm r s anis).polarBilin.ker ↔ _
  rw [mem_canonical_polar_ker_iff]
  constructor
  · rintro ⟨hQ, hx⟩
    refine ⟨hx, ?_⟩
    simpa [canonicalForm_apply, hx] using hQ
  · rintro ⟨hx, hQ⟩
    exact ⟨by simpa [canonicalForm_apply, hx] using hQ, hx⟩

def zeroCanonicalRadicalEquiv (r s : Nat) :
    (Fin s → K) ≃ₗ[K] (canonicalForm (K := K) r s false).radical :=
  { toFun := fun z ↦ ⟨(0, z), by
      rw [mem_canonical_radical_iff]
      simp [radicalForm_apply]⟩
    invFun := fun x ↦ x.1.2
    left_inv := by intro z; rfl
    right_inv := by
      intro x
      apply Subtype.ext
      apply Prod.ext
      · exact ((mem_canonical_radical_iff x.1).1 x.property).1.symm
      · rfl
    map_add' := by intro x y; apply Subtype.ext; apply Prod.ext <;> simp
    map_smul' := by intro a x; apply Subtype.ext; apply Prod.ext <;> simp }

@[simp] theorem finrank_canonical_radical_false (r s : Nat) :
    Module.finrank K (canonicalForm (K := K) r s false).radical = s := by
  rw [← (zeroCanonicalRadicalEquiv (K := K) r s).finrank_eq]
  simp

def headLinear (s : Nat) (hs : 0 < s) : (Fin s → K) →ₗ[K] K :=
  LinearMap.proj ⟨0, hs⟩

def anisotropicCanonicalRadicalEquiv (r s : Nat) (hs : 0 < s) :
    LinearMap.ker (headLinear (K := K) s hs) ≃ₗ[K]
      (canonicalForm (K := K) r s true).radical :=
  { toFun := fun z ↦ ⟨(0, (z : Fin s → K)), by
      rw [mem_canonical_radical_iff]
      refine ⟨rfl, ?_⟩
      rw [radicalForm_true_apply_of_pos hs]
      have hz : (z : Fin s → K) ⟨0, hs⟩ = 0 := by
        exact z.property
      simp [hz]⟩
    invFun := fun x ↦ ⟨x.1.2, by
      change x.1.2 ⟨0, hs⟩ = 0
      have hrad := ((mem_canonical_radical_iff x.1).1 x.property).2
      rw [radicalForm_true_apply_of_pos hs] at hrad
      exact sq_eq_zero_iff.mp hrad⟩
    left_inv := by intro z; apply Subtype.ext; rfl
    right_inv := by
      intro x
      apply Subtype.ext
      apply Prod.ext
      · exact ((mem_canonical_radical_iff x.1).1 x.property).1.symm
      · rfl
    map_add' := by intro x y; apply Subtype.ext; apply Prod.ext <;> simp
    map_smul' := by intro a x; apply Subtype.ext; apply Prod.ext <;> simp }

theorem headLinear_ne_zero (s : Nat) (hs : 0 < s) :
    headLinear (K := K) s hs ≠ 0 := by
  intro h
  have hx := LinearMap.congr_fun h (Pi.single (⟨0, hs⟩ : Fin s) 1)
  simpa [headLinear] using hx

theorem finrank_canonical_radical_true_add_one (r s : Nat) (hs : 0 < s) :
    Module.finrank K (canonicalForm (K := K) r s true).radical + 1 = s := by
  rw [← (anisotropicCanonicalRadicalEquiv (K := K) r s hs).finrank_eq]
  calc
    Module.finrank K (LinearMap.ker (headLinear (K := K) s hs)) + 1 =
        Module.finrank K (Fin s → K) :=
      Module.Dual.finrank_ker_add_one_of_ne_zero (headLinear_ne_zero s hs)
    _ = s := by simp

theorem finrank_canonical_radical_add_indicator (r s : Nat) (anis : Bool)
    (hpos : anis = true → 0 < s) :
    Module.finrank K (canonicalForm (K := K) r s anis).radical +
      (if anis then 1 else 0) = s := by
  cases anis with
  | false => simpa using finrank_canonical_radical_false (K := K) r s
  | true => simpa using finrank_canonical_radical_true_add_one (K := K) r s (hpos rfl)

theorem _root_.QuadraticMap.IsometryEquiv.map_polarBilin
    {W : Type*} [AddCommGroup W] [Module K W]
    {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    (e : Q.IsometryEquiv Q') (x y : V) :
    Q'.polarBilin (e x) (e y) = Q.polarBilin x y := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
  change Q' (e x + e y) - Q' (e x) - Q' (e y) = Q (x + y) - Q x - Q y
  rw [← map_add e x y, e.map_app, e.map_app, e.map_app]

theorem _root_.QuadraticMap.IsometryEquiv.map_polarBilin_ker
    {W : Type*} [AddCommGroup W] [Module K W]
    {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    (e : Q.IsometryEquiv Q') :
    Q.polarBilin.ker.map e.toLinearMap = Q'.polarBilin.ker := by
  apply le_antisymm
  · rintro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change Q.polarBilin y = 0 at hy
    change Q'.polarBilin (e y) = 0
    apply LinearMap.ext
    intro z
    rw [show z = e (e.symm z) by simp, e.map_polarBilin]
    simpa [hy]
  · intro x hx
    change Q'.polarBilin x = 0 at hx
    refine ⟨e.symm x, ?_, by simp⟩
    change Q.polarBilin (e.symm x) = 0
    apply LinearMap.ext
    intro z
    have h := LinearMap.congr_fun hx (e z)
    simp only [LinearMap.zero_apply] at h
    have hp := e.map_polarBilin (e.symm x) z
    rw [e.apply_symm_apply] at hp
    exact hp.symm.trans h

theorem _root_.QuadraticMap.Equivalent.finrank_polarBilin_ker_eq
    {W : Type*} [AddCommGroup W] [Module K W]
    {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    (h : Q.Equivalent Q') :
    Module.finrank K Q.polarBilin.ker = Module.finrank K Q'.polarBilin.ker := by
  obtain ⟨e⟩ := h
  rw [← e.map_polarBilin_ker, LinearEquiv.finrank_map_eq]

def Classification.rootIsometry (Q : QuadraticForm K V)
    (c : Classification Q ⊤) :
    Q.IsometryEquiv (canonicalForm c.planes c.radicalDim c.anisotropic) :=
  (topRestrictionIsometry Q).trans c.isometry

theorem Classification.dimension_eq (Q : QuadraticForm K V)
    (c : Classification Q ⊤) :
    Module.finrank K V = 2 * c.planes + c.radicalDim := by
  rw [(c.rootIsometry Q).toLinearEquiv.finrank_eq, finrank_normalSpace]

theorem Classification.polarRadical_dimension_eq (Q : QuadraticForm K V)
    (c : Classification Q ⊤) :
    Module.finrank K Q.polarBilin.ker = c.radicalDim := by
  exact (show Q.Equivalent
      (canonicalForm c.planes c.radicalDim c.anisotropic) from ⟨c.rootIsometry Q⟩)
    |>.finrank_polarBilin_ker_eq.trans
      (finrank_canonical_polar_ker c.planes c.radicalDim c.anisotropic)

theorem Classification.quadraticRadical_dimension_eq (Q : QuadraticForm K V)
    (c : Classification Q ⊤) :
    Module.finrank K Q.radical + (if c.anisotropic then 1 else 0) = c.radicalDim := by
  rw [(show Q.Equivalent
      (canonicalForm c.planes c.radicalDim c.anisotropic) from ⟨c.rootIsometry Q⟩)
        |>.rank_radical_eq]
  exact finrank_canonical_radical_add_indicator c.planes c.radicalDim
    c.anisotropic c.anisotropic_pos

/-- Complete classification: over a perfect characteristic-two field with
surjective Artin--Schreier map, two finite-dimensional quadratic forms are
isometric exactly when the dimensions of the ambient space, polar radical,
and quadratic radical agree. -/
theorem equivalent_iff_dimension_radicals_eq
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [PerfectField K]
    (hAS : Function.Surjective (fun x : K => x ^ 2 + x))
    (Q₁ : QuadraticForm K V) (Q₂ : QuadraticForm K W) :
    Q₁.Equivalent Q₂ ↔
      Module.finrank K V = Module.finrank K W ∧
      Module.finrank K Q₁.polarBilin.ker = Module.finrank K Q₂.polarBilin.ker ∧
      Module.finrank K Q₁.radical = Module.finrank K Q₂.radical := by
  constructor
  · intro h
    obtain ⟨e⟩ := h
    exact ⟨e.toLinearEquiv.finrank_eq,
      (show Q₁.Equivalent Q₂ from ⟨e⟩).finrank_polarBilin_ker_eq,
      (show Q₁.Equivalent Q₂ from ⟨e⟩).rank_radical_eq⟩
  · rintro ⟨hdim, hpolar, hradical⟩
    let c₁ := classification hAS Q₁
    let c₂ := classification hAS Q₂
    have hs : c₁.radicalDim = c₂.radicalDim := by
      calc
        c₁.radicalDim = Module.finrank K Q₁.polarBilin.ker :=
          (c₁.polarRadical_dimension_eq Q₁).symm
        _ = Module.finrank K Q₂.polarBilin.ker := hpolar
        _ = c₂.radicalDim := c₂.polarRadical_dimension_eq Q₂
    have hq₁ := c₁.quadraticRadical_dimension_eq Q₁
    have hq₂ := c₂.quadraticRadical_dimension_eq Q₂
    have hindicator : (if c₁.anisotropic then 1 else 0) =
        (if c₂.anisotropic then 1 else 0) := by
      omega
    have hanis : c₁.anisotropic = c₂.anisotropic := by
      cases h₁ : c₁.anisotropic <;> cases h₂ : c₂.anisotropic <;>
        simp [h₁, h₂] at hindicator ⊢
    have hd₁ := c₁.dimension_eq Q₁
    have hd₂ := c₂.dimension_eq Q₂
    have hr : c₁.planes = c₂.planes := by
      omega
    let e₁ := c₁.rootIsometry Q₁
    let e₂ := c₂.rootIsometry Q₂
    rw [hr, hs, hanis] at e₁
    exact ⟨e₁.trans e₂.symm⟩

/-- Algebraically closed specialization used for the set-sized `On₂` proxy
in the flagship paper. -/
theorem algebraicallyClosed_equivalent_iff_dimension_radicals_eq
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [IsAlgClosed K]
    (Q₁ : QuadraticForm K V) (Q₂ : QuadraticForm K W) :
    Q₁.Equivalent Q₂ ↔
      Module.finrank K V = Module.finrank K W ∧
      Module.finrank K Q₁.polarBilin.ker = Module.finrank K Q₂.polarBilin.ker ∧
      Module.finrank K Q₁.radical = Module.finrank K Q₂.radical :=
  equivalent_iff_dimension_radicals_eq
    (Ogdoad.Off.artinSchreier_surjective (K := K)) Q₁ Q₂


end Ogdoad.CharTwoClassification
