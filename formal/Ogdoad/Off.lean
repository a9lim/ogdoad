import Mathlib

/-!
# The `off` classification over full `On₂`

This file formalizes the field-theoretic and quadratic-form core of
`writeups/transfinite_arf.tex`.  A set-sized algebraically closed field of
characteristic two is the formal proxy for the finite-dimensional argument over
Conway's proper-class nimber field: any one form and its finitely many chosen
roots live in such a subfield.
-/

namespace Ogdoad.Off

variable {K : Type*} [Field K] [CharP K 2] [IsAlgClosed K]

open scoped CharTwo

omit [CharP K 2] in
/-- Frobenius is surjective over an algebraically closed field. -/
theorem frobenius_surjective : Function.Surjective (fun x : K => x ^ 2) := by
  intro a
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq a (by decide : 0 < 2)
  exact ⟨x, hx⟩

omit [CharP K 2] in
/-- The Artin–Schreier map `x ↦ x² + x` is surjective. -/
theorem artinSchreier_surjective :
    Function.Surjective (fun x : K => x ^ 2 + x) := by
  intro a
  let p : Polynomial K := Polynomial.X ^ 2 + Polynomial.X - Polynomial.C a
  have hp : p.degree ≠ 0 := by
    rw [show p = Polynomial.C 1 * Polynomial.X ^ 2 +
        Polynomial.C 1 * Polynomial.X + Polynomial.C (-a) by
          simp only [p, Polynomial.C_1, one_mul, map_neg, sub_eq_add_neg]]
    rw [Polynomial.degree_quadratic one_ne_zero]
    norm_num
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p hp
  refine ⟨x, ?_⟩
  rw [Polynomial.IsRoot.def] at hx
  simp only [p, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C] at hx
  exact sub_eq_zero.mp hx

section Quadratic

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The span of two vectors, used to state that a basis change stays inside
one symplectic plane. -/
def pairSpan (e f : V) : Submodule K V :=
  Submodule.span K ({e, f} : Set V)

omit [CharP K 2] [IsAlgClosed K] in
private lemma left_mem_pairSpan (e f : V) : e ∈ pairSpan (K := K) e f := by
  rw [pairSpan, Submodule.mem_span_pair]
  exact ⟨1, 0, by simp⟩

omit [CharP K 2] [IsAlgClosed K] in
private lemma right_mem_pairSpan (e f : V) : f ∈ pairSpan (K := K) e f := by
  rw [pairSpan, Submodule.mem_span_pair]
  exact ⟨0, 1, by simp⟩

omit [CharP K 2] [IsAlgClosed K] in
private lemma pairSpan_eq_of_mem {e f v w : V}
    (hv : v ∈ pairSpan (K := K) e f) (hw : w ∈ pairSpan (K := K) e f)
    (he : e ∈ pairSpan (K := K) v w) (hf : f ∈ pairSpan (K := K) v w) :
    pairSpan (K := K) v w = pairSpan (K := K) e f := by
  apply le_antisymm
  · rw [pairSpan, Submodule.span_le]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hv
    · have : x = w := Set.mem_singleton_iff.mp hx
      simpa [this] using hw
  · rw [pairSpan, Submodule.span_le]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact he
    · have : x = f := Set.mem_singleton_iff.mp hx
      simpa [this] using hf

omit [CharP K 2] [IsAlgClosed K] in
private lemma polarBilin_comm (Q : QuadraticForm K V) (x y : V) :
    Q.polarBilin x y = Q.polarBilin y x := by
  simpa only [QuadraticMap.polarBilin_apply_apply] using QuadraticMap.polar_comm Q x y

/-- A hyperbolic pair for `Q`: two isotropic vectors pairing to one. -/
structure IsHyperbolicPair (Q : QuadraticForm K V) (e f : V) : Prop where
  left_isotropic : Q e = 0
  right_isotropic : Q f = 0
  polar_eq_one : Q.polarBilin e f = 1

/-- The load-bearing `off` lemma.  Over an algebraically closed field of
characteristic two, every normalized symplectic pair can be changed, inside
its own plane, into a hyperbolic pair. -/
theorem hyperbolic_pair_of_polar_eq_one (Q : QuadraticForm K V) {e f : V}
    (hef : Q.polarBilin e f = 1) :
    ∃ e' f', IsHyperbolicPair Q e' f' ∧
      pairSpan (K := K) e' f' = pairSpan (K := K) e f := by
  classical
  let a := Q e
  let b := Q f
  have hfe : Q.polarBilin f e = 1 := by
    rw [polarBilin_comm Q f e]
    exact hef
  have hpef : QuadraticMap.polar Q e f = 1 := by
    simpa only [QuadraticMap.polarBilin_apply_apply] using hef
  have hpfe : QuadraticMap.polar Q f e = 1 := by
    simpa only [QuadraticMap.polarBilin_apply_apply] using hfe
  by_cases ha : a = 0
  · let e' := e
    let f' := f + b • e
    have hQe' : Q e' = 0 := by simpa [e', a] using ha
    have hQf' : Q f' = 0 := by
      rw [show f' = f + b • e from rfl, QuadraticMap.map_add (⇑Q) f (b • e),
        QuadraticMap.map_smul Q b e,
        QuadraticMap.polar_smul_right]
      simp only [smul_eq_mul]
      rw [show Q e = a from rfl, show Q f = b from rfl, ha, hpfe]
      simp
    have he'f' : Q.polarBilin e' f' = 1 := by
      rw [QuadraticMap.polarBilin_apply_apply, show e' = e from rfl,
        show f' = f + b • e from rfl, QuadraticMap.polar_add_right,
        QuadraticMap.polar_smul_right, hpef, QuadraticMap.polar_self]
      simp
    have he'mem : e' ∈ pairSpan (K := K) e f := by
      simpa [e'] using left_mem_pairSpan (K := K) e f
    have hf'mem : f' ∈ pairSpan (K := K) e f := by
      exact (pairSpan (K := K) e f).add_mem (right_mem_pairSpan (K := K) e f)
        ((pairSpan (K := K) e f).smul_mem b (left_mem_pairSpan (K := K) e f))
    have hemem : e ∈ pairSpan (K := K) e' f' := by
      simpa [e'] using left_mem_pairSpan (K := K) e' f'
    have hfmem : f ∈ pairSpan (K := K) e' f' := by
      have := (pairSpan (K := K) e' f').sub_mem
        (right_mem_pairSpan (K := K) e' f')
        ((pairSpan (K := K) e' f').smul_mem b hemem)
      simpa [f', e'] using this
    exact ⟨e', f', ⟨hQe', hQf', he'f'⟩,
      pairSpan_eq_of_mem he'mem hf'mem hemem hfmem⟩
  · obtain ⟨t, ht⟩ := artinSchreier_surjective (K := K) (a * b)
    change t ^ 2 + t = a * b at ht
    let e' := (t / a) • e + f
    have hQe' : Q e' = 0 := by
      rw [show e' = (t / a) • e + f from rfl,
        QuadraticMap.map_add (⇑Q) ((t / a) • e) f,
        QuadraticMap.map_smul Q (t / a) e, QuadraticMap.polar_smul_left]
      simp only [smul_eq_mul]
      rw [show Q e = a from rfl, show Q f = b from rfl, hpef]
      calc
        t / a * (t / a) * a + b + t / a * 1 = (t ^ 2 + t) / a + b := by
          field_simp [ha]
          ring
        _ = a * b / a + b := by rw [ht]
        _ = b + b := by field_simp [ha]
        _ = 0 := by simp
    have he'e : Q.polarBilin e' e = 1 := by
      rw [QuadraticMap.polarBilin_apply_apply,
        show e' = (t / a) • e + f from rfl, QuadraticMap.polar_add_left,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_self, hpfe]
      simp
    let f' := e + a • e'
    have hQf' : Q f' = 0 := by
      rw [show f' = e + a • e' from rfl, QuadraticMap.map_add (⇑Q) e (a • e'),
        QuadraticMap.map_smul Q a e', QuadraticMap.polar_smul_right]
      simp only [smul_eq_mul, hQe', mul_zero, add_zero]
      rw [show Q e = a from rfl]
      have hpee' : QuadraticMap.polar Q e e' = 1 := by
        rw [QuadraticMap.polar_comm]
        simpa only [QuadraticMap.polarBilin_apply_apply] using he'e
      rw [hpee']
      simp
    have he'f' : Q.polarBilin e' f' = 1 := by
      rw [QuadraticMap.polarBilin_apply_apply, show f' = e + a • e' from rfl,
        QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_self]
      simp only [hQe', smul_zero, add_zero]
      simpa only [QuadraticMap.polarBilin_apply_apply] using he'e
    have he'mem : e' ∈ pairSpan (K := K) e f := by
      exact (pairSpan (K := K) e f).add_mem
        ((pairSpan (K := K) e f).smul_mem (t / a) (left_mem_pairSpan (K := K) e f))
        (right_mem_pairSpan (K := K) e f)
    have hf'mem : f' ∈ pairSpan (K := K) e f := by
      exact (pairSpan (K := K) e f).add_mem (left_mem_pairSpan (K := K) e f)
        ((pairSpan (K := K) e f).smul_mem a he'mem)
    have hemem : e ∈ pairSpan (K := K) e' f' := by
      have := (pairSpan (K := K) e' f').sub_mem
        (right_mem_pairSpan (K := K) e' f')
        ((pairSpan (K := K) e' f').smul_mem a (left_mem_pairSpan (K := K) e' f'))
      simpa [f'] using this
    have hfmem : f ∈ pairSpan (K := K) e' f' := by
      have := (pairSpan (K := K) e' f').sub_mem
        (left_mem_pairSpan (K := K) e' f')
        ((pairSpan (K := K) e' f').smul_mem (t / a) hemem)
      simpa [e'] using this
    exact ⟨e', f', ⟨hQe', hQf', he'f'⟩,
      pairSpan_eq_of_mem he'mem hf'mem hemem hfmem⟩

/-- Pointwise conversion of each supplied symplectic pair into a hyperbolic
pair, preserving that pair's span.  No relationship between different indices
is assumed or proved here: cross-plane orthogonality, direct-sum assembly, and
the classification theorem itself remain paper-level. -/
theorem hyperbolic_family_of_symplectic_family {I : Type*} (Q : QuadraticForm K V)
    (e f : I → V) (hef : ∀ i, Q.polarBilin (e i) (f i) = 1) :
    ∃ e' f' : I → V, ∀ i,
      IsHyperbolicPair Q (e' i) (f' i) ∧
        pairSpan (K := K) (e' i) (f' i) = pairSpan (K := K) (e i) (f i) := by
  classical
  choose e' f' hp hspan using fun i ↦
    hyperbolic_pair_of_polar_eq_one Q (hef i)
  exact ⟨e', f', fun i ↦ ⟨hp i, hspan i⟩⟩

/-- The canonical square root selected from algebraic closure. -/
noncomputable def squareRoot (x : K) : K :=
  Classical.choose (frobenius_surjective (K := K) x)

omit [CharP K 2] in
@[simp] theorem squareRoot_sq (x : K) : squareRoot x ^ 2 = x :=
  Classical.choose_spec (frobenius_surjective (K := K) x)

/-- If the polar form vanishes, the unique square root of `Q` is a linear
functional.  This is the structural content behind the two radical normal
forms `Z^s` and `A ⊥ Z^(s-1)`. -/
noncomputable def zeroPolarLinear (Q : QuadraticForm K V)
    (hpolar : ∀ x y, Q.polarBilin x y = 0) : V →ₗ[K] K where
  toFun x := squareRoot (Q x)
  map_add' x y := by
    apply CharTwo.sq_injective
    change squareRoot (Q (x + y)) ^ 2 =
      (squareRoot (Q x) + squareRoot (Q y)) ^ 2
    rw [CharTwo.add_sq, squareRoot_sq, squareRoot_sq, squareRoot_sq]
    have hp : QuadraticMap.polar Q x y = 0 := by
      simpa only [QuadraticMap.polarBilin_apply_apply] using hpolar x y
    rw [QuadraticMap.map_add (⇑Q) x y, hp, add_zero]
  map_smul' a x := by
    apply CharTwo.sq_injective
    change squareRoot (Q (a • x)) ^ 2 = (a * squareRoot (Q x)) ^ 2
    rw [squareRoot_sq, mul_pow, squareRoot_sq]
    rw [QuadraticMap.map_smul Q a x]
    simp only [smul_eq_mul]
    ring

@[simp] theorem zeroPolarLinear_sq (Q : QuadraticForm K V)
    (hpolar : ∀ x y, Q.polarBilin x y = 0) (x : V) :
    zeroPolarLinear Q hpolar x ^ 2 = Q x :=
  squareRoot_sq (Q x)

/-- Complete structural normal form for the polar radical.  The first branch
is `Z^s`; in the second branch the displayed vector is the `A` coordinate and
the kernel has codimension one, hence is `Z^(s-1)`. -/
theorem zero_polar_normal_form [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hpolar : ∀ x y, Q.polarBilin x y = 0) :
    ∃ ℓ : V →ₗ[K] K,
      (∀ x, Q x = (ℓ x) ^ 2) ∧
      (ℓ = 0 ∨ ∃ e, ℓ e = 1 ∧
        Module.finrank K (LinearMap.ker ℓ) + 1 = Module.finrank K V) := by
  let ℓ := zeroPolarLinear Q hpolar
  refine ⟨ℓ, fun x ↦ (zeroPolarLinear_sq Q hpolar x).symm, ?_⟩
  by_cases hℓ : ℓ = 0
  · exact Or.inl hℓ
  · right
    have hsurj : Function.Surjective ℓ :=
      LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hℓ)
    obtain ⟨e, he⟩ := hsurj 1
    exact ⟨e, he, Module.Dual.finrank_ker_add_one_of_ne_zero hℓ⟩

end Quadratic

end Ogdoad.Off
