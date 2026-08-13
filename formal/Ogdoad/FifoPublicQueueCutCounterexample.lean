import Ogdoad.FifoPublicPolicyAffine
import Ogdoad.FifoCommonDummyEventBoundary

/-!
# Untouched-dummy boundary for the public queue-cut target

The natural projected queue-cut target is not a state-local invariant, even
at a complete-fan node where the distinguished isolated label is still
untouched.  The exact seven-label `commonDummyParent` countermodel already
supplies such a node: the physical mover has an odd strategy from score zero.
Forgetting that strategy gives a public policy.  Every affine response moment
of this policy evaluates to `1 + potential`, whereas the queue-cut vector
evaluates to the queue cut itself.  Since the current score is zero, equality
after deleting the isolated label would force `1 = 0`.

Thus a successful initial-root proof cannot induct on only the current public
state, dummy liveness, and ownership.  It must retain initial-root ancestry or
an additional order-sensitive correction.
-/

namespace Ogdoad.Fifo

noncomputable section

/-- The natural universal cut vector proposed as a state-local affine
target.  It is named locally here because the counterexample, unlike the
failed invariant module, remains useful. -/
def candidateQueueCutVector {V : Type*} [DecidableEq V]
    (s : PublicState V) : EdgeVector V :=
  (s.queue.map (liveStarVector s.untouched)).sum

@[simp] theorem graphEvaluation_candidateQueueCutVector
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (s : PublicState V) :
    graphEvaluation G (candidateQueueCutVector s) =
      queueCut G s.untouched s.queue := by
  rw [candidateQueueCutVector, map_list_sum, queueCut]
  apply congrArg List.sum
  rw [List.map_map]
  apply List.map_congr_left
  intro v hv
  exact graphEvaluation_liveStarVector G s.untouched v

/-- The checked losing-mover result provides an exact odd strategy tree for
the full-fan seat at `commonDummyParent`. -/
def commonDummyParentMoverOddStrategy :
    OddStrategy commonDummyGraph true commonDummyParent := by
  have hspec := commonDummyWinner_spec true commonDummyParent
  rw [commonDummyParent_true_loses] at hspec
  exact Classical.choice hspec.nonempty_oddStrategy

/-- Forget the score labels of the exact losing-mover strategy. -/
def commonDummyParentBadPublicPolicy :
    PublicPolicy true commonDummyParent.public :=
  commonDummyParentMoverOddStrategy.toPublicPolicy

/-- Equality after deleting an isolated dummy implies equality under graph
evaluation. -/
theorem graphEvaluation_eq_of_realEdgeProjection_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {d : V}
    (hd : IsDummy G d) {x y : EdgeVector V}
    (hxy : realEdgeProjection d x = realEdgeProjection d y) :
    graphEvaluation G x = graphEvaluation G y := by
  have hprojection : realEdgeProjection d (x + y) = 0 := by
    rw [map_add, hxy]
    calc
      (realEdgeProjection d y) + (realEdgeProjection d y) =
          (1 : ZMod 2) • realEdgeProjection d y +
            (1 : ZMod 2) • realEdgeProjection d y := by simp
      _ = ((1 : ZMod 2) + 1) • realEdgeProjection d y :=
        (add_smul 1 1 _).symm
      _ = 0 := by
        have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        rw [h11, zero_smul]
  have hevaluation :=
    graphEvaluation_eq_zero_of_realEdgeProjection_eq_zero hd hprojection
  rw [map_add] at hevaluation
  calc
    graphEvaluation G x = graphEvaluation G x +
        (graphEvaluation G y + graphEvaluation G y) := by
          rw [CharTwo.add_self_eq_zero, add_zero]
    _ = (graphEvaluation G x + graphEvaluation G y) +
        graphEvaluation G y := by abel
    _ = graphEvaluation G y := by rw [hevaluation, zero_add]

/-- The exact full-fan public policy at `commonDummyParent` omits the natural
projected queue-cut target even though label `5` is isolated and untouched. -/
theorem commonDummyParentBadPublicPolicy_no_queueCut :
    ¬ProjectedPublicPolicyAffineMoment 5 true
      commonDummyParentBadPublicPolicy
      (realEdgeProjection 5 (candidateQueueCutVector commonDummyParent.public)) := by
  rintro ⟨z, hzPublic, hzProjection⟩
  have hz : AffineResponseMoment commonDummyGraph true
      commonDummyParentMoverOddStrategy z :=
    hzPublic.toAffineResponseMoment commonDummyParentMoverOddStrategy
  have heval := hz.graphEvaluation_eq
    (show WellFormed commonDummyParent by
      simp [WellFormed, commonDummyParent])
  have heq := graphEvaluation_eq_of_realEdgeProjection_eq
    commonDummyGraph_dummyFive hzProjection
  rw [heq] at heval
  change graphEvaluation commonDummyGraph
      (candidateQueueCutVector commonDummyParent.public) = _ at heval
  rw [graphEvaluation_candidateQueueCutVector] at heval
  have heval' :
      queueCut commonDummyGraph {0, 1, 5, 6} [2, 4, 3] =
        1 + queueCut commonDummyGraph {0, 1, 5, 6} [2, 4, 3] := by
    simp [potential, commonDummyParent, State.public] at heval
  have := congrArg (fun a : ZMod 2 ↦
    a + queueCut commonDummyGraph {0, 1, 5, 6} [2, 4, 3]) heval'
  simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero] at this
  exact one_ne_zero this.symm

/-- The bad policy satisfies exactly the hypotheses of the proposed
untouched-dummy full-fan queue-cut invariant. -/
theorem commonDummyParent_refutes_untouched_queueCut_invariant :
    (5 : Fin 7) ∈ commonDummyParent.public.untouched ∧
      commonDummyParent.public.toMove = true ∧
      ¬ProjectedPublicPolicyAffineMoment 5 true
        commonDummyParentBadPublicPolicy
        (realEdgeProjection 5
          (candidateQueueCutVector commonDummyParent.public)) := by
  exact ⟨by simp [commonDummyParent, State.public], rfl,
    commonDummyParentBadPublicPolicy_no_queueCut⟩

end

end Ogdoad.Fifo
