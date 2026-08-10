import Mathlib.Data.Bool.Basic

/-!
# Compiling a forced charge to normal play

The Gold FIFO construction first produces a finite perfect-information tree
whose leaves carry a Boolean charge. This file proves that a uniform local
claim move turns any such tree into an ordinary normal-play game without
changing who can force the designated charge. It also records exact boundaries
for the naturality criterion.
-/


namespace Ogdoad.GoldSemantics

mutual
  inductive PayTree where
    | leaf (sigma : Bool)
    | node (moves : PayForest)

  inductive PayForest where
    | nil
    | cons (head : PayTree) (tail : PayForest)
end

def want (stance mover : Bool) : Bool :=
  if mover then !stance else stance

mutual
  def forced (stance : Bool) : PayTree -> Bool -> Bool
    | .leaf sigma, _mover => sigma
    | .node moves, mover =>
        if forcedAny stance moves (!mover) (want stance mover)
        then want stance mover else !(want stance mover)

  def forcedAny (stance : Bool) : PayForest -> Bool -> Bool -> Bool
    | .nil, _mover, _target => false
    | .cons head tail, mover, target =>
        (forced stance head mover == target) || forcedAny stance tail mover target
end

mutual
  /-- Winning status in the normal-play compiler.  A payoff leaf carries one
  claim move exactly when the player to move is the seat designated by sigma. -/
  def compiledWin (stance : Bool) : PayTree -> Bool -> Bool
    | .leaf sigma, mover => sigma == want stance mover
    | .node moves, mover => compiledSome stance moves (!mover)

  def compiledSome (stance : Bool) : PayForest -> Bool -> Bool
    | .nil, _nextMover => false
    | .cons head tail, nextMover =>
        !(compiledWin stance head nextMover) || compiledSome stance tail nextMover
end

theorem want_not_mover (stance mover : Bool) :
    want stance (!mover) = !(want stance mover) := by
  cases stance <;> cases mover <;> decide

mutual
  theorem compiledWin_eq (stance : Bool) (tree : PayTree) (mover : Bool) :
      compiledWin stance tree mover = (forced stance tree mover == want stance mover) := by
    cases tree with
    | leaf sigma => simp [compiledWin, forced]
    | node moves =>
        simp only [compiledWin, forced]
        rw [compiledSome_eq]
        rw [want_not_mover]
        cases hw : want stance mover <;>
          cases h : forcedAny stance moves (!mover) (want stance mover) <;>
          simp [hw] at h ⊢

  theorem compiledSome_eq (stance : Bool) (moves : PayForest) (nextMover : Bool) :
      compiledSome stance moves nextMover =
        forcedAny stance moves nextMover (!(want stance nextMover)) := by
    cases moves with
    | nil => simp [compiledSome, forcedAny]
    | cons head tail =>
        simp only [compiledSome, forcedAny]
        rw [compiledWin_eq, compiledSome_eq]
        cases forced stance head nextMover <;> cases want stance nextMover <;> simp
end

theorem root_isP_iff_forced_zero (tree : PayTree) :
    compiledWin true tree false = false ↔ forced true tree false = false := by
  rw [compiledWin_eq]
  simp [want]

section Dominance

variable {State : Type} (move : State -> State -> Prop) (outcome : State -> Bool)

/-- Delete losing options at N-positions, retaining every forced option at
P-positions. -/
def Pruned (s t : State) : Prop :=
  move s t /\ (outcome s = false \/ outcome t = false)

theorem pruned_successors_same
    (pRule : forall s t, outcome s = false -> move s t -> outcome t = true)
    {s t u : State} (ht : Pruned move outcome s t) (hu : Pruned move outcome s u) :
    outcome t = outcome u := by
  rcases ht with ⟨ht, hkeepT⟩
  rcases hu with ⟨hu, hkeepU⟩
  cases hs : outcome s with
  | false => rw [pRule s t hs ht, pRule s u hs hu]
  | true =>
      have ht0 : outcome t = false := hkeepT.resolve_left (by simp [hs])
      have hu0 : outcome u = false := hkeepU.resolve_left (by simp [hs])
      rw [ht0, hu0]

end Dominance

def edgeCloseValue (qa qb : Bool) : Bool := qa != qb
def edgeOpenValue (qa qb : Bool) : Bool := !(edgeCloseValue qa qb)

theorem edge_fork_always_winning (qa qb : Bool) :
    edgeOpenValue qa qb || edgeCloseValue qa qb = true := by
  cases qa <;> cases qb <;> decide

theorem edge_fork_optimum_swaps (qa qb : Bool) :
    edgeOpenValue (!qa) qb = edgeCloseValue qa qb /\
    edgeCloseValue (!qa) qb = edgeOpenValue qa qb := by
  cases qa <;> cases qb <;> decide

/-- A phase-free leaf cannot name the same initial-seat winner after both an
even and an odd number of preceding moves. -/
theorem phase_free_leaf_obstruction (leafCurrentWins : Bool) :
    leafCurrentWins != !leafCurrentWins := by
  cases leafCurrentWins <;> decide

end Ogdoad.GoldSemantics
