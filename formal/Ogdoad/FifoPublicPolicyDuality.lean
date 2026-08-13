import Ogdoad.FifoPublicPolicyAffine
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Affine duality for graph-free FIFO policies

The universal public-policy affine statement is not merely sufficient for
FIFO linking.  Its negation has a finite-dimensional affine separator, and
every linear functional on the real-edge quotient is the evaluation
functional of an isolated-dummy simple graph.  This module packages those
two exact duality steps.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem realEdgeQuotient_add_self (d : V) (q : RealEdgeQuotient V d) :
    q + q = 0 := by
  calc
    q + q = (1 : ZMod 2) • q + (1 : ZMod 2) • q := by simp
    _ = ((1 : ZMod 2) + 1) • q := (add_smul 1 1 q).symm
    _ = 0 := by
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [h11, zero_smul]

omit [Fintype V] in
theorem realEdgeQuotient_neg_eq_self (d : V) (q : RealEdgeQuotient V d) :
    -q = q := by
  rw [neg_eq_iff_add_eq_zero]
  exact realEdgeQuotient_add_self d q

/-- The projected response relation of one public policy, viewed as an
honest affine subspace over `F₂`.  Ternary closure is precisely the affine
closure operation because the only scalars are zero and one. -/
def PublicPolicy.projectedAffineSubspace (d : V) (seat : Bool)
    {s : PublicState V} (policy : PublicPolicy seat s) :
    AffineSubspace (ZMod 2) (RealEdgeQuotient V d) where
  carrier := {q | ProjectedPublicPolicyAffineMoment d seat policy q}
  smul_vsub_vadd_mem' c q₁ q₂ q₃ h₁ h₂ h₃ := by
    by_cases hc : c = 0
    · subst c
      simpa using h₃
    · have hc1 : c = 1 := zmod2_eq_one_of_ne_zero c hc
      subst c
      obtain ⟨z₁, hz₁, hq₁⟩ := h₁
      obtain ⟨z₂, hz₂, hq₂⟩ := h₂
      obtain ⟨z₃, hz₃, hq₃⟩ := h₃
      refine ⟨z₁ + z₂ + z₃, .ternary hz₁ hz₂ hz₃, ?_⟩
      simp only [map_add, hq₁, hq₂, hq₃, vsub_eq_sub,
        sub_eq_add_neg, realEdgeQuotient_neg_eq_self]
      change q₁ + q₂ + q₃ = (1 : ZMod 2) • (q₁ + q₂) + q₃
      simp

omit [Fintype V] in
/-- Every finite public policy has at least one affine response moment. -/
theorem PublicPolicy.exists_affineMoment
    {seat : Bool} {s : PublicState V} (policy : PublicPolicy seat s) :
    ∃ z, PublicPolicyAffineMoment seat policy z := by
  induction policy with
  | terminal => exact ⟨0, .terminal _ _⟩
  | choose s hseat m t hstep child ih =>
      obtain ⟨z, hz⟩ := ih
      exact ⟨moveLiveStar s.toZeroState m + z, .choose hz⟩
  | answer s hseat hasMove children ih =>
      obtain ⟨m, t, hstep⟩ := hasMove
      obtain ⟨z, hz⟩ := ih m t hstep
      exact ⟨moveLiveStar s.toZeroState m + z, .answerChild hz⟩

instance PublicPolicy.projectedAffineSubspace_nonempty (d : V) (seat : Bool)
    {s : PublicState V} (policy : PublicPolicy seat s) :
    Nonempty (policy.projectedAffineSubspace d seat) := by
  obtain ⟨z, hz⟩ := policy.exists_affineMoment
  exact ⟨⟨realEdgeProjection d z, z, hz, rfl⟩⟩

/-- A point outside a nonempty affine subspace over `F₂` is separated by a
linear functional which is constantly one on that subspace. -/
theorem exists_linearSeparator_of_zero_not_mem
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W]
    (A : AffineSubspace (ZMod 2) W) [Nonempty A]
    (hzero : (0 : W) ∉ A) :
    ∃ ell : W →ₗ[ZMod 2] ZMod 2,
      ∀ q : W, q ∈ A → ell q = 1 := by
  let a : A := Classical.choice inferInstance
  have ha : (a : W) ∉ A.direction := by
    intro hadir
    have haa : (a : W) + (a : W) ∈ A :=
      A.vadd_mem_of_mem_direction hadir a.property
    have hself : (a : W) + (a : W) = 0 := by
      calc
        (a : W) + a = (1 : ZMod 2) • (a : W) +
            (1 : ZMod 2) • (a : W) := by simp
        _ = ((1 : ZMod 2) + 1) • (a : W) := (add_smul 1 1 _).symm
        _ = 0 := by
          have h11 : (1 : ZMod 2) + 1 = 0 := by decide
          rw [h11, zero_smul]
    exact hzero (hself ▸ haa)
  have haQ : A.direction.mkQ (a : W) ≠ 0 := by
    intro h
    apply ha
    rw [← Submodule.Quotient.mk_eq_zero]
    simpa [Submodule.mkQ_apply] using h
  let Q := W ⧸ A.direction
  let aq : Q := A.direction.mkQ (a : W)
  have haq : aq ≠ 0 := haQ
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) haq
  let ell : W →ₗ[ZMod 2] ZMod 2 := f.comp A.direction.mkQ
  refine ⟨ell, ?_⟩
  intro q hq
  have hdiff : q - (a : W) ∈ A.direction :=
    A.vsub_mem_direction hq a.property
  have hquot : A.direction.mkQ q = A.direction.mkQ (a : W) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    change Submodule.Quotient.mk (q - (a : W)) = 0
    exact (Submodule.Quotient.mk_eq_zero A.direction).2 hdiff
  change f (A.direction.mkQ q) = 1
  rw [hquot]
  exact hf

/-- The isolated-dummy graph represented by a linear functional on the exact
real-edge quotient. -/
def graphOfRealEdgeFunctional (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦
    ell (realEdgeProjection d (Finsupp.single s(x, y) 1)) = 1

omit [Fintype V] in
theorem graphOfRealEdgeFunctional_dummy (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2) :
    IsDummy (graphOfRealEdgeFunctional d ell) d := by
  intro v
  rw [graphOfRealEdgeFunctional, SimpleGraph.fromRel_adj]
  intro h
  rcases h with ⟨hne, h | h⟩
  · rw [realEdgeProjection_dummy_single, map_zero] at h
    exact zero_ne_one h
  · have hswap :
        realEdgeProjection d (Finsupp.single s(v, d) (1 : ZMod 2)) = 0 := by
      rw [Sym2.eq_swap]
      exact realEdgeProjection_dummy_single d v 1
    rw [hswap, map_zero] at h
    exact zero_ne_one h

omit [Fintype V] in
/-- Graph evaluation of the represented graph is exactly the supplied
quotient functional. -/
theorem graphEvaluation_graphOfRealEdgeFunctional (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (z : EdgeVector V) :
    graphEvaluation (graphOfRealEdgeFunctional d ell) z =
      ell (realEdgeProjection d z) := by
  have hhom : graphEvaluation (graphOfRealEdgeFunctional d ell) =
      (ell.comp (realEdgeProjection d)).toAddMonoidHom := by
    apply Finsupp.addHom_ext
    intro e a
    induction e using Sym2.inductionOn with
    | _ x y =>
        by_cases hxy : x = y
        · subst y
          simp [graphEvaluation_single, adjacencyBit,
            graphOfRealEdgeFunctional]
        · by_cases hone :
              ell (realEdgeProjection d
                (Finsupp.single s(x, y) 1)) = 1
          · simp [graphEvaluation_single, adjacencyBit,
              graphOfRealEdgeFunctional, SimpleGraph.fromRel_adj,
              hxy, hone]
            have hsingle :
                Finsupp.single s(x, y) a =
                  a • Finsupp.single s(x, y) (1 : ZMod 2) := by
              ext e
              simp [smul_eq_mul]
            rw [hsingle, map_smul, map_smul, hone]
            simp
          · have hzero := zmod2_eq_zero_of_ne_one _ hone
            simp [graphEvaluation_single, adjacencyBit,
              graphOfRealEdgeFunctional, SimpleGraph.fromRel_adj,
              hxy, hzero, Sym2.eq_swap]
            have hsingle :
                Finsupp.single s(x, y) a =
                  a • Finsupp.single s(x, y) (1 : ZMod 2) := by
              ext e
              simp [smul_eq_mul]
            rw [hsingle, map_smul, map_smul, hzero]
            simp
  exact DFunLike.congr_fun hhom z

omit [Fintype V] in
/-- Peel one public live-star prefix from an affine evaluation identity. -/
theorem graphEvaluation_tail_eq_of_step
    {G : SimpleGraph V} {s t : State V} {m : Move V}
    {z : EdgeVector V} (hs : WellFormed s)
    (hstep : step G s m = some t)
    (hwhole : graphEvaluation G (moveLiveStar s m + z) =
      1 + potential G s) :
    graphEvaluation G z = 1 + potential G t := by
  have hstar := graphEvaluation_moveLiveStar G s m hs
  have hpotential := step_potential_eq_add_liveDegree hstep
  rw [map_add, hstar] at hwhole
  rw [hpotential]
  cases m with
  | «open» v =>
      simp only at hwhole ⊢
      calc
        graphEvaluation G z =
            (liveDegree G s v + liveDegree G s v) +
              graphEvaluation G z := by
                rw [CharTwo.add_self_eq_zero, zero_add]
        _ = liveDegree G s v +
            (liveDegree G s v + graphEvaluation G z) := by abel
        _ = liveDegree G s v + (1 + potential G s) := by rw [hwhole]
        _ = 1 + (potential G s + liveDegree G s v) := by abel
  | close => simpa using hwhole
  | pass => simpa using hwhole

omit [Fintype V] in
/-- A public policy whose entire affine response space evaluates to the odd
defect at a concrete state lifts to an exact odd strategy on the graph. -/
noncomputable def PublicPolicy.toOddStrategy_of_graphEvaluation
    {G : SimpleGraph V} {seat : Bool} {u : PublicState V}
    (policy : PublicPolicy seat u) :
    ∀ {s : State V}, s.public = u → WellFormed s →
      (∀ z, PublicPolicyAffineMoment seat policy z →
        graphEvaluation G z = 1 + potential G s) →
      OddStrategy G seat s := by
  induction policy with
  | terminal u ht =>
      intro s hsu hs heval
      have htConcrete : Terminal s := by
        constructor
        · change s.public.untouched = ∅
          rw [hsu]
          exact ht.1
        · change s.public.queue = []
          rw [hsu]
          exact ht.2
      have hscore : s.score ≠ 0 := by
        intro hzero
        have h := heval 0 (.terminal u ht)
        rw [map_zero, terminal_potential htConcrete, hzero] at h
        exact zero_ne_one h
      exact .terminal s htConcrete hscore
  | choose u hseat m v hpublic child ih =>
      intro s hsu hs heval
      cases hsu
      let t := concreteStepOfPublic G s m v hpublic
      have hstep : step G s m = some t :=
        concreteStepOfPublic_step G s m v hpublic
      have htpublic : t.public = v :=
        concreteStepOfPublic_public G s m v hpublic
      have htWF : WellFormed t := wellFormed_step hs hstep
      have hchildEval : ∀ z, PublicPolicyAffineMoment seat child z →
          graphEvaluation G z = 1 + potential G t := by
        intro z hz
        apply graphEvaluation_tail_eq_of_step hs hstep
        have hroot := heval (moveLiveStar s.public.toZeroState m + z)
          (.choose hz)
        simpa using hroot
      exact .choose s hseat m t hstep
        (ih htpublic htWF hchildEval)
  | answer u hseat hasMove children ih =>
      intro s hsu hs heval
      cases hsu
      have concreteHasMove : ∃ m t, step G s m = some t := by
        obtain ⟨m, v, hpublic⟩ := hasMove
        exact ⟨m, concreteStepOfPublic G s m v hpublic,
          concreteStepOfPublic_step G s m v hpublic⟩
      refine .answer s hseat concreteHasMove ?_
      intro m t hstep
      have hpublic : publicStep s.public m = some t.public := by
        rw [← step_public G s m, hstep]
        rfl
      have htWF : WellFormed t := wellFormed_step hs hstep
      apply ih m t.public hpublic rfl htWF
      intro z hz
      apply graphEvaluation_tail_eq_of_step hs hstep
      have hroot := heval (moveLiveStar s.public.toZeroState m + z)
        (.answerChild hz)
      simpa using hroot

/-- FIFO linking implies the universal graph-free affine statement.  If a
public affine space omitted zero, affine separation and graph representation
would turn the same public policy into an exact odd counterstrategy on an
isolated-dummy graph, contradicting FIFO. -/
theorem FifoLinkingTheorem.implies_universalPublicPolicyAffine
    (h : FifoLinkingTheorem.{u}) : UniversalPublicPolicyAffine.{u} := by
  intro V instF instD d seat policy
  by_contra hzero
  let A := policy.projectedAffineSubspace d seat
  have hzeroA : (0 : RealEdgeQuotient V d) ∉ A := hzero
  obtain ⟨ell, hell⟩ := exists_linearSeparator_of_zero_not_mem A hzeroA
  let G := graphOfRealEdgeFunctional d ell
  have hpolicyEval : ∀ z, PublicPolicyAffineMoment seat policy z →
      graphEvaluation G z = 1 + potential G (initial (V := V)) := by
    intro z hz
    have hmem : realEdgeProjection d z ∈ A :=
      ⟨z, hz, rfl⟩
    rw [graphEvaluation_graphOfRealEdgeFunctional]
    rw [hell _ hmem]
    simp [potential, initial, queueCut]
  let odd : OddStrategy G seat (initial (V := V)) :=
    policy.toOddStrategy_of_graphEvaluation rfl wellFormed_initial hpolicyEval
  have heven := h V instF instD G d
    (graphOfRealEdgeFunctional_dummy d ell) seat
  exact heven.not_oddWins odd.toOddWins

/-- Exact logical status of the graph-free affine formulation: it is
equivalent to the original FIFO linking conjecture, not a weaker sufficient
condition. -/
theorem universalPublicPolicyAffine_iff_fifoLinking :
    UniversalPublicPolicyAffine.{u} ↔ FifoLinkingTheorem.{u} :=
  ⟨UniversalPublicPolicyAffine.implies_fifoLinking,
    FifoLinkingTheorem.implies_universalPublicPolicyAffine⟩

end

end Ogdoad.Fifo
