import Ogdoad.FifoHub

/-!
# A complete-leaf FIFO trace obstruction

This file records a small graph-independent obstruction to using the sum of
*all* leaves of a fixed attacker policy as the missing affine contraction.
On two real vertices and one dummy, a positional attacker policy has six
compatible terminal schedules.  Their augmentation is zero, but their real
edge moment is the nonzero edge `s(0,1)`.

The example does not contradict isolated-dummy FIFO linking: its six terminal
moments are not all on one odd graph-evaluation sheet.  It only rules out the
stronger proposed identity saying that the unweighted complete-leaf sum is
always augmentation times the complete real graph.
-/

namespace Ogdoad.Fifo

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- All graph-independent legal children on `Fin 3`, in label order. -/
def legalPublicChildrenThree (s : PublicState (Fin 3)) :
    List (Move (Fin 3) × PublicState (Fin 3)) :=
  ([Move.open 0, Move.open 1, Move.open 2, Move.close, Move.pass]).filterMap fun m ↦
    (publicStep s m).map fun t ↦ (m, t)

/-- One off-diagonal coordinate of a move's complete-graph live star.  For
distinct `x,y`, this is exactly the `s(x,y)` coordinate of `moveLiveStar`:
an OPEN of one endpoint contributes precisely when the other endpoint is
still live. -/
def moveEdgeBit (s : PublicState V) (m : Move V) (x y : V) : Bool :=
  match m with
  | .open v =>
      let live := s.untouched ∪ s.queue.toFinset
      decide ((v = x ∧ y ∈ live) ∨ (v = y ∧ x ∈ live))
  | .close => false
  | .pass => false

/-- One terminal live-star coordinate for every leaf compatible with a
positional policy for the player outside `seat`.  At a `seat` node every
legal child is retained; at an outside-seat node only the policy-selected
child is retained.  Fuel is merely a transparent evaluator bound; `rank`
proves that `rank s + 1` is always sufficient. -/
def policyLeafEdgeBits (seat : Bool)
    (policy : PublicState (Fin 3) → Move (Fin 3)) (x y : Fin 3) :
    Nat → PublicState (Fin 3) → List Bool
  | 0, _ => []
  | fuel + 1, s =>
      if s.untouched = ∅ ∧ s.queue = [] then
        [false]
      else if s.toMove = seat then
        (legalPublicChildrenThree s).flatMap fun child ↦
          (policyLeafEdgeBits seat policy x y fuel child.2).map fun z ↦
            (moveEdgeBit s child.1 x y).xor z
      else
        match publicStep s (policy s) with
        | none => []
        | some t =>
            (policyLeafEdgeBits seat policy x y fuel t).map fun z ↦
              (moveEdgeBit s (policy s) x y).xor z

/-- A positional policy witnessing failure of the raw complete-leaf formula
on `Fin 3`.  Vertex `2` is the prospective dummy. -/
def completeLeafCounterPolicy (s : PublicState (Fin 3)) : Move (Fin 3) :=
  if s.untouched = ∅ then .close
  else if s.untouched = {1, 2} then .open 2
  else if s.untouched = {0, 2} then .open 0
  else if s.untouched = {0, 1} then .open 0
  else if s.untouched = {0} then .open 0
  else if s.untouched = {1} then .open 1
  else if s.untouched = {2} then .open 2
  else .open 0

/-- The complete compatible leaf family has exactly six leaves, hence even
augmentation. -/
theorem completeLeafCounterPolicy_card :
    (policyLeafEdgeBits false completeLeafCounterPolicy
      0 1 20 (initial (V := Fin 3)).public).length = 6 := by
  native_decide

theorem completeLeafCounterPolicy_even_augmentation :
    (policyLeafEdgeBits false completeLeafCounterPolicy
      0 1 20 (initial (V := Fin 3)).public).length % 2 = 0 := by
  rw [completeLeafCounterPolicy_card]

/-- The same complete family has nonzero real moment `s(0,1)`.  Concretely
the six schedules have moments
`0, 01, 0, 12, 0, 12`, whose sum is `01`. -/
theorem completeLeafCounterPolicy_moment :
    (policyLeafEdgeBits false completeLeafCounterPolicy
      0 1 20 (initial (V := Fin 3)).public).foldl Bool.xor false = true := by
  native_decide

/-- Hence the raw identity `moment = augmentation * K_real` is false even
for a graph-independent positional policy at an initial root: here the
augmentation is zero while the real moment is nonzero. -/
theorem completeLeafCounterPolicy_not_zero :
    (policyLeafEdgeBits false completeLeafCounterPolicy
      0 1 20 (initial (V := Fin 3)).public).foldl Bool.xor false ≠ false := by
  rw [completeLeafCounterPolicy_moment]
  decide

end Ogdoad.Fifo
