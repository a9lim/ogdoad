import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Observation lower bounds for quadratic-refinement realizers

At fixed polar form, quadratic refinements form a torsor under the dual vector
space. Exactness therefore forces every transcript certificate for the rooted
outcome at `x` to span `x`. The Boolean-coordinate specialization shows that
weight-`w` observations need total count at least `weight(x) / w`.
-/

namespace Ogdoad.GoldNoEvaluator

section Span

variable {K V Oracle : Type} [Field K] [AddCommGroup V] [Module K V]

/-- Agreement on the observations selected at `(q,x)` fixes the rooted result.
The finite observation set may depend adaptively on the original oracle. -/
def TranscriptStable
    (eval : Oracle → V → K)
    (observe : Oracle → V → Finset V)
    (result : Oracle → V → K) : Prop :=
  ∀ q q' x,
    (∀ z ∈ observe q x, eval q z = eval q' z) →
    result q x = result q' x

/-- If adding every linear functional gives another refinement with the same
polar form, an exact result at `x` has no transcript certificate whose queried
points fail to span `x`. -/
theorem exact_forces_mem_span
    (eval : Oracle → V → K)
    (twist : Oracle → (V →ₗ[K] K) → Oracle)
    (observe : Oracle → V → Finset V)
    (result : Oracle → V → K)
    (htwist : ∀ q ell z, eval (twist q ell) z = eval q z + ell z)
    (hstable : TranscriptStable eval observe result)
    (q : Oracle) (x : V)
    (hexact : ∀ r, result r x = eval r x) :
    x ∈ Submodule.span K (observe q x : Set V) := by
  by_contra hx
  obtain ⟨ell, hellx, hker⟩ := Submodule.exists_le_ker_of_notMem hx
  let q' := twist q ell
  have hagree : ∀ z ∈ observe q x, eval q z = eval q' z := by
    intro z hz
    have hzspan : z ∈ Submodule.span K (observe q x : Set V) :=
      Submodule.subset_span hz
    have hzker : z ∈ LinearMap.ker ell := hker hzspan
    rw [htwist]
    simp [LinearMap.mem_ker.mp hzker]
  have hout : result q x = result q' x := hstable q q' x hagree
  rw [hexact q, hexact q', htwist] at hout
  have hzero : ell x = 0 := by
    apply add_left_cancel (a := eval q x)
    simpa using hout.symm
  exact hellx hzero

end Span

section Coordinates

variable {n Oracle : Type} [Fintype n] [DecidableEq n]

abbrev Cube (n : Type) := n → Bool

def support (z : Cube n) : Finset n :=
  Finset.univ.filter fun i ↦ z i = true

def covered (queries : Finset (Cube n)) : Finset n :=
  queries.biUnion support

theorem covered_card_le {queries : Finset (Cube n)} {w : Nat}
    (hweight : ∀ z ∈ queries, (support z).card ≤ w) :
    (covered queries).card ≤ queries.card * w := by
  simpa [covered] using Finset.card_biUnion_le_card_mul queries support w hweight

theorem exists_fresh_coordinate
    {queries : Finset (Cube n)} {x : Cube n} {C w : Nat}
    (hcard : queries.card ≤ C)
    (hweight : ∀ z ∈ queries, (support z).card ≤ w)
    (hx : C * w < (support x).card) :
    ∃ j, x j = true ∧ ∀ z ∈ queries, z j = false := by
  have hcover : (covered queries).card < (support x).card := by
    calc
      (covered queries).card ≤ queries.card * w := covered_card_le hweight
      _ ≤ C * w := Nat.mul_le_mul_right w hcard
      _ < (support x).card := hx
  obtain ⟨j, hjx, hjcover⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcover
  refine ⟨j, ?_, ?_⟩
  · simpa [support] using hjx
  · intro z hz
    have hjz : j ∉ support z := by
      intro hj
      exact hjcover (Finset.mem_biUnion.mpr ⟨z, hz, hj⟩)
    simpa [support] using hjz

/-- Coordinate form of transcript stability for Boolean refinements. -/
def CubeTranscriptStable
    (eval : Oracle → Cube n → Bool)
    (observe : Oracle → Cube n → Finset (Cube n))
    (outcome : Oracle → Cube n → Bool) : Prop :=
  ∀ q q' x,
    (∀ z ∈ observe q x, eval q z = eval q' z) →
    outcome q x = outcome q' x

/-- Exactness forces the observations at `x` to cover every active coordinate
of `x`. Otherwise a twist at an uncovered coordinate is transcript-invisible
but flips the target. -/
theorem exact_forces_support_covered
    (eval : Oracle → Cube n → Bool)
    (twist : Oracle → n → Oracle)
    (observe : Oracle → Cube n → Finset (Cube n))
    (outcome : Oracle → Cube n → Bool)
    (htwist : ∀ q j z, eval (twist q j) z = (eval q z != z j))
    (hstable : CubeTranscriptStable eval observe outcome)
    (q : Oracle) (x : Cube n)
    (hexact : ∀ r, outcome r x = eval r x) :
    support x ⊆ covered (observe q x) := by
  intro j hxj
  by_contra hjcover
  let q' := twist q j
  have hxj' : x j = true := by simpa [support] using hxj
  have hj : ∀ z ∈ observe q x, z j = false := by
    intro z hz
    have hjz : j ∉ support z := by
      intro hjz
      exact hjcover (Finset.mem_biUnion.mpr ⟨z, hz, hjz⟩)
    simpa [support] using hjz
  have hagree : ∀ z ∈ observe q x, eval q z = eval q' z := by
    intro z hz
    rw [htwist]
    simp [hj z hz]
  have hout : outcome q x = outcome q' x := hstable q q' x hagree
  have htarget : eval q' x = !eval q x := by
    rw [htwist]
    simp [hxj']
  rw [hexact q, hexact q', htarget] at hout
  cases eval q x <;> simp at hout

/-- Weight-`w` transcript observations need total count at least
`weight(x) / w`, stated without division. -/
theorem exact_query_weight_lower_bound
    (eval : Oracle → Cube n → Bool)
    (twist : Oracle → n → Oracle)
    (observe : Oracle → Cube n → Finset (Cube n))
    (outcome : Oracle → Cube n → Bool)
    {w : Nat}
    (htwist : ∀ q j z, eval (twist q j) z = (eval q z != z j))
    (hstable : CubeTranscriptStable eval observe outcome)
    (hweight : ∀ q x z, z ∈ observe q x → (support z).card ≤ w)
    (q : Oracle) (x : Cube n)
    (hexact : ∀ r, outcome r x = eval r x) :
    (support x).card ≤ (observe q x).card * w := by
  calc
    (support x).card ≤ (covered (observe q x)).card :=
      Finset.card_le_card (exact_forces_support_covered
        eval twist observe outcome htwist hstable q x hexact)
    _ ≤ (observe q x).card * w := covered_card_le (hweight q x)

/-- A uniform bounded-total observation budget is incompatible with exactness
at any input whose weight exceeds the budgeted support. -/
theorem no_dense_exact
    (eval : Oracle → Cube n → Bool)
    (twist : Oracle → n → Oracle)
    (observe : Oracle → Cube n → Finset (Cube n))
    (outcome : Oracle → Cube n → Bool)
    {C w : Nat}
    (htwist : ∀ q j z, eval (twist q j) z = (eval q z != z j))
    (hstable : CubeTranscriptStable eval observe outcome)
    (hcard : ∀ q x, (observe q x).card ≤ C)
    (hweight : ∀ q x z, z ∈ observe q x → (support z).card ≤ w)
    (q : Oracle) (x : Cube n)
    (hx : C * w < (support x).card) :
    ¬(∀ r, outcome r x = eval r x) := by
  intro hexact
  exact Nat.not_le_of_gt hx (exact_query_weight_lower_bound
    eval twist observe outcome htwist hstable (hweight := hweight)
    q x hexact |>.trans (Nat.mul_le_mul_right w (hcard q x)))

end Coordinates

end Ogdoad.GoldNoEvaluator
