import Ogdoad.FifoCrossExitIncidence

/-!
# Dual conservation across a complete FIFO fan

At an isolated-dummy root carrying an explicit odd strategy, the game graph
is already a separating functional: it evaluates every root affine response
point to one and every root response direction to zero.

This module records the consequence for a strategy-relative defender fan.
If an odd family of lifted child branches has aggregate ancestry/move prefix
zero, its aggregate continuation residue still evaluates to one.  Adding any
homogeneous root correction does not change that value.  In particular the
residue cannot vanish in the real-edge quotient.

Thus complete earlier fans and cross-exit ladder corrections do not by
themselves contradict separation.  They can only move the surviving affine
unit between continuation cosets.  A proof of FIFO linking must additionally
construct an incidence identity which kills that odd residue; this is exactly
the causal factor-extension obligation.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem list_sum_map_add {I : Type*} (is : List I)
    (f g : I → EdgeVector V) :
    (is.map fun i ↦ f i + g i).sum =
      (is.map f).sum + (is.map g).sum := by
  induction is with
  | nil => simp
  | cons i rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      abel

/-- Dual conservation law for an odd defender fan in one fixed root
strategy.  Once the ancestry-plus-move prefixes cancel under the game graph,
the child continuation sum, even after an arbitrary homogeneous root
correction, has graph value exactly one.

This is the sharp obstruction to the tempting extension from complete prefix
cancellation to complete response cancellation. -/
theorem StrategyPrefix.graphEvaluation_oddFan_residue_add_direction_eq_one
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {hroot : OddStrategy G seat (initial (V := V))}
    {hseat : s.toMove = seat}
    {hasMove : ∃ move next, step G s move = some next}
    {children : ∀ move next, step G s move = some next →
      OddStrategy G seat next}
    {p : EdgeVector V}
    (hp : StrategyPrefix G seat hroot
      (OddStrategy.answer s hseat hasMove children) p)
    {I : Type*} (is : List I) (move : I → Move V)
    (next : I → State V)
    (hstep : ∀ i ∈ is, step G s (move i) = some (next i))
    (continuation : I → EdgeVector V)
    (hcontinuation : ∀ i (hi : i ∈ is),
      AffineResponseMoment G seat
        (children (move i) (next i) (hstep i hi)) (continuation i))
    (hodd : is.length % 2 = 1)
    (hprefix : graphEvaluation G
      (is.map fun i ↦ p + moveLiveStar s (move i)).sum = 0)
    (direction : EdgeVector V)
    (hdirection : ResponseDirection G seat hroot direction) :
    graphEvaluation G ((is.map continuation).sum + direction) = 1 := by
  let points := is.map fun i ↦
    p + (moveLiveStar s (move i) + continuation i)
  have hpoints : ∀ z ∈ points,
      AffineResponseMoment G seat hroot z := by
    intro z hz
    simp only [points, List.mem_map] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    have hlocal : AffineResponseMoment G seat
        (OddStrategy.answer s hseat hasMove children)
        (moveLiveStar s (move i) + continuation i) :=
      AffineResponseMoment.answerChild (hstep := hstep i hi)
        (hcontinuation i hi)
    exact hp.lift hlocal
  have hresponse : AffineResponseMoment G seat hroot points.sum := by
    apply AffineResponseMoment.odd_list_sum points
    · simpa [points] using hodd
    · exact hpoints
  have hcorrected : AffineResponseMoment G seat hroot
      (points.sum + direction) := hresponse.add_direction hdirection
  have heval := hcorrected.graphEvaluation_eq wellFormed_initial
  have hdecomp : points.sum =
      (is.map fun i ↦ p + moveLiveStar s (move i)).sum +
        (is.map continuation).sum := by
    simpa only [points, add_assoc] using
      list_sum_map_add is
        (fun i ↦ p + moveLiveStar s (move i)) continuation
  rw [hdecomp, add_assoc, map_add, hprefix, zero_add] at heval
  simpa [potential, initial, queueCut] using heval

/-- Real-edge quotient form of the dual conservation law.  On an
isolated-dummy graph, an odd zero-prefix fan leaves a nonzero continuation
residue modulo dummy and diagonal coordinates, even after every supplied
root response direction is added. -/
theorem StrategyPrefix.oddFan_residue_add_direction_projection_ne_zero
    {G : SimpleGraph V} {d : V} {seat : Bool} {s : State V}
    {hroot : OddStrategy G seat (initial (V := V))}
    (hdummy : IsDummy G d)
    {hseat : s.toMove = seat}
    {hasMove : ∃ move next, step G s move = some next}
    {children : ∀ move next, step G s move = some next →
      OddStrategy G seat next}
    {p : EdgeVector V}
    (hp : StrategyPrefix G seat hroot
      (OddStrategy.answer s hseat hasMove children) p)
    {I : Type*} (is : List I) (move : I → Move V)
    (next : I → State V)
    (hstep : ∀ i ∈ is, step G s (move i) = some (next i))
    (continuation : I → EdgeVector V)
    (hcontinuation : ∀ i (hi : i ∈ is),
      AffineResponseMoment G seat
        (children (move i) (next i) (hstep i hi)) (continuation i))
    (hodd : is.length % 2 = 1)
    (hprefix : realEdgeProjection d
      (is.map fun i ↦ p + moveLiveStar s (move i)).sum = 0)
    (direction : EdgeVector V)
    (hdirection : ResponseDirection G seat hroot direction) :
    realEdgeProjection d
      ((is.map continuation).sum + direction) ≠ 0 := by
  intro hzero
  have hprefixEval : graphEvaluation G
      (is.map fun i ↦ p + moveLiveStar s (move i)).sum = 0 :=
    graphEvaluation_eq_zero_of_realEdgeProjection_eq_zero hdummy hprefix
  have hresidueEval :=
    hp.graphEvaluation_oddFan_residue_add_direction_eq_one
      is move next hstep continuation hcontinuation hodd hprefixEval
        direction hdirection
  have hresidueZero : graphEvaluation G
      ((is.map continuation).sum + direction) = 0 :=
    graphEvaluation_eq_zero_of_realEdgeProjection_eq_zero hdummy hzero
  rw [hresidueZero] at hresidueEval
  exact zero_ne_one hresidueEval

end

end Ogdoad.Fifo
