import Ogdoad.FifoPositionalSelectedEdgeBoundary

/-!
# The positional state quotient has labelled cycles

Identifying equal full FIFO states changes the topology of the pruned policy:
commuting histories can create genuine one-cycles in the quotient DAG.  This
does not by itself supply the zero moment needed for FIFO linking.  The
smallest relevant square already carries a nonzero real-edge label.

The example is an exact positional odd strategy on the empty graph at score
one.  Its defender root retains both `OPEN 2` and `CLOSE`.  A state-dependent
Bellman tie-break selects the complementary edge at each attacker child, and
the two paths reach the same full state.  The four retained edges form an
`F₂` cycle, but their live-star sum projects to the nonzero real coordinate
`s(0,2)`.  Hence state-DAG incidence and positional reconvergence alone do not
force a zero projected moment.

This is a local noninitial obstruction, not a counterexample to FIFO linking.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

namespace StatePreferredOdd

/-- Bellman choice with a preferred move depending on the full state. -/
noncomputable def winningChoice
    (G : SimpleGraph V) (seat : Bool) (preferred : State V → Move V)
    (s : State V) (hwin : OddWins G seat s) (ht : ¬Terminal s)
    (hturn : s.toMove ≠ seat) : PositionalOdd.OddWinningChoice G seat s := by
  by_cases hp : ∃ t, step G s (preferred s) = some t ∧ OddWins G seat t
  · let t := Classical.choose hp
    exact {
      move := preferred s
      next := t
      step := (Classical.choose_spec hp).1
      wins := (Classical.choose_spec hp).2 }
  · exact PositionalOdd.canonicalOddWinningChoice G seat s hwin ht hturn

omit [Fintype V] in
theorem winningChoice_move_eq
    (G : SimpleGraph V) (seat : Bool) (preferred : State V → Move V)
    (s : State V) (hwin : OddWins G seat s) (ht : ¬Terminal s)
    (hturn : s.toMove ≠ seat)
    (hp : ∃ t, step G s (preferred s) = some t ∧ OddWins G seat t) :
    (winningChoice G seat preferred s hwin ht hturn).move = preferred s := by
  simp only [winningChoice, dif_pos hp]

/-- Rank-recursive full-state strategy with a state-dependent Bellman
tie-break. -/
noncomputable def strategy
    (G : SimpleGraph V) (seat : Bool) (preferred : State V → Move V)
    (s : State V) (hwin : OddWins G seat s) : OddStrategy G seat s := by
  by_cases ht : Terminal s
  · exact .terminal s ht
      (PositionalOdd.oddWins_terminal_score_ne_zero hwin ht)
  · by_cases hturn : s.toMove = seat
    · exact .answer s hturn (not_terminal_has_step ht)
        (fun m t hstep ↦ strategy G seat preferred t
          (hwin.answer_child hturn hstep))
    · let choice := winningChoice G seat preferred s hwin ht hturn
      exact .choose s hturn choice.move choice.next choice.step
        (strategy G seat preferred choice.next choice.wins)
termination_by rank s
decreasing_by
  · exact rank_step_lt hstep
  · exact rank_step_lt choice.step

omit [Fintype V] in
/-- The state strategy is independent of the displayed proof of membership
in the odd-winning region. -/
theorem strategy_proof_irrelevant
    (G : SimpleGraph V) (seat : Bool) (preferred : State V → Move V)
    (s : State V) (h₁ h₂ : OddWins G seat s) :
    strategy G seat preferred s h₁ = strategy G seat preferred s h₂ := by
  have : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

omit [Fintype V] in
/-- Equal full states have equal state-preferred continuations. -/
theorem strategy_eq_of_state_eq
    (G : SimpleGraph V) (seat : Bool) (preferred : State V → Move V)
    {s t : State V} (hst : s = t)
    (hs : OddWins G seat s) (ht : OddWins G seat t) :
    HEq (strategy G seat preferred s hs)
      (strategy G seat preferred t ht) := by
  subst t
  exact heq_of_eq (strategy_proof_irrelevant G seat preferred s hs ht)

omit [Fintype V] in
theorem strategy_selectedMove_eq
    (G : SimpleGraph V) (seat : Bool) (preferred : State V → Move V)
    (s : State V) (hwin : OddWins G seat s) (ht : ¬Terminal s)
    (hturn : s.toMove ≠ seat)
    (hp : ∃ t, step G s (preferred s) = some t ∧ OddWins G seat t) :
    (strategy G seat preferred s hwin).selectedMove =
      some (preferred s) := by
  rw [strategy.eq_def]
  simp only [dif_neg ht, dif_neg hturn, OddStrategy.selectedMove]
  rw [winningChoice_move_eq G seat preferred s hwin ht hturn hp]

end StatePreferredOdd

/-! ## Exact FIFO commuting square -/

def positionalDAGRoot : State (Fin 4) where
  untouched := {2, 3}
  queue := [0, 1]
  ko := false
  toMove := false
  score := 1

def positionalDAGOpen : State (Fin 4) where
  untouched := {3}
  queue := [0, 1, 2]
  ko := false
  toMove := true
  score := 1

def positionalDAGClose : State (Fin 4) where
  untouched := {2, 3}
  queue := [1]
  ko := false
  toMove := true
  score := 1

def positionalDAGJoin : State (Fin 4) where
  untouched := {3}
  queue := [1, 2]
  ko := false
  toMove := false
  score := 1

theorem positionalDAG_open :
    step (⊥ : SimpleGraph (Fin 4)) positionalDAGRoot (.open 2) =
      some positionalDAGOpen := by
  simp [step, positionalDAGRoot, positionalDAGOpen]

theorem positionalDAG_open_close :
    step (⊥ : SimpleGraph (Fin 4)) positionalDAGOpen .close =
      some positionalDAGJoin := by
  simp [step, positionalDAGOpen, positionalDAGJoin, flip]

theorem positionalDAG_close :
    step (⊥ : SimpleGraph (Fin 4)) positionalDAGRoot .close =
      some positionalDAGClose := by
  simp [step, positionalDAGRoot, positionalDAGClose, flip]

theorem positionalDAG_close_open :
    step (⊥ : SimpleGraph (Fin 4)) positionalDAGClose (.open 2) =
      some positionalDAGJoin := by
  simp [step, positionalDAGClose, positionalDAGJoin]

theorem positionalDAG_root_noLiveCut :
    NoLiveCut (⊥ : SimpleGraph (Fin 4)) positionalDAGRoot := by
  simp [NoLiveCut]

theorem positionalDAG_open_noLiveCut :
    NoLiveCut (⊥ : SimpleGraph (Fin 4)) positionalDAGOpen := by
  simp [NoLiveCut]

theorem positionalDAG_close_noLiveCut :
    NoLiveCut (⊥ : SimpleGraph (Fin 4)) positionalDAGClose := by
  simp [NoLiveCut]

theorem positionalDAG_join_noLiveCut :
    NoLiveCut (⊥ : SimpleGraph (Fin 4)) positionalDAGJoin := by
  simp [NoLiveCut]

theorem positionalDAG_root_odd :
    OddWins (⊥ : SimpleGraph (Fin 4)) false positionalDAGRoot :=
  oddWins_of_noLiveCut false positionalDAGRoot
    positionalDAG_root_noLiveCut (by decide)

theorem positionalDAG_open_odd :
    OddWins (⊥ : SimpleGraph (Fin 4)) false positionalDAGOpen :=
  oddWins_of_noLiveCut false positionalDAGOpen
    positionalDAG_open_noLiveCut (by decide)

theorem positionalDAG_close_odd :
    OddWins (⊥ : SimpleGraph (Fin 4)) false positionalDAGClose :=
  oddWins_of_noLiveCut false positionalDAGClose
    positionalDAG_close_noLiveCut (by decide)

theorem positionalDAG_join_odd :
    OddWins (⊥ : SimpleGraph (Fin 4)) false positionalDAGJoin :=
  oddWins_of_noLiveCut false positionalDAGJoin
    positionalDAG_join_noLiveCut (by decide)

/-- State-dependent tie-break traversing the two complementary sides of the
square. -/
def positionalDAGPreferred (s : State (Fin 4)) : Move (Fin 4) :=
  if s = positionalDAGOpen then .close else .open 2

def positionalDAGStrategy :
    OddStrategy (⊥ : SimpleGraph (Fin 4)) false positionalDAGRoot :=
  StatePreferredOdd.strategy ⊥ false positionalDAGPreferred
    positionalDAGRoot positionalDAG_root_odd

theorem positionalDAGPreferred_open :
    positionalDAGPreferred positionalDAGOpen = .close := by
  simp [positionalDAGPreferred]

theorem positionalDAGPreferred_close :
    positionalDAGPreferred positionalDAGClose = .open 2 := by
  simp [positionalDAGPreferred, positionalDAGClose, positionalDAGOpen]

theorem positionalDAG_open_selected_close :
    (StatePreferredOdd.strategy ⊥ false positionalDAGPreferred
      positionalDAGOpen positionalDAG_open_odd).selectedMove =
        some .close := by
  rw [← positionalDAGPreferred_open]
  apply StatePreferredOdd.strategy_selectedMove_eq
    (⊥ : SimpleGraph (Fin 4)) false positionalDAGPreferred
      positionalDAGOpen positionalDAG_open_odd
      (by simp [Terminal, positionalDAGOpen]) (by decide)
  exact ⟨positionalDAGJoin, positionalDAG_open_close,
    positionalDAG_join_odd⟩

theorem positionalDAG_close_selected_open :
    (StatePreferredOdd.strategy ⊥ false positionalDAGPreferred
      positionalDAGClose positionalDAG_close_odd).selectedMove =
        some (.open 2) := by
  rw [← positionalDAGPreferred_close]
  apply StatePreferredOdd.strategy_selectedMove_eq
    (⊥ : SimpleGraph (Fin 4)) false positionalDAGPreferred
      positionalDAGClose positionalDAG_close_odd
      (by simp [Terminal, positionalDAGClose]) (by decide)
  exact ⟨positionalDAGJoin, positionalDAG_close_open,
    positionalDAG_join_odd⟩

/-! ## The quotient-chain calculation -/

/-- Source and target of the four square edges.  Vertices are ordered as
root, OPEN child, CLOSE child, and common join. -/
def positionalSquareSource : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 2

def positionalSquareTarget : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 3
  | 2 => 2
  | 3 => 3

/-- Degree-one boundary on the finite state quotient. -/
def positionalSquareBoundary (c : Fin 4 → ZMod 2) (v : Fin 4) : ZMod 2 :=
  ∑ e : Fin 4, c e *
    ((if positionalSquareSource e = v then 1 else 0) +
      if positionalSquareTarget e = v then 1 else 0)

/-- All four retained edges form a nonzero cycle after the two histories are
identified at the common full state. -/
theorem positionalSquare_allEdges_cycle :
    positionalSquareBoundary (fun _ ↦ 1) = 0 := by
  funext v
  fin_cases v <;> decide

def positionalSquareLabel : Fin 4 → EdgeVector (Fin 4)
  | 0 => moveLiveStar positionalDAGRoot (.open 2)
  | 1 => moveLiveStar positionalDAGOpen .close
  | 2 => moveLiveStar positionalDAGRoot .close
  | 3 => moveLiveStar positionalDAGClose (.open 2)

def positionalSquareLabelSum : EdgeVector (Fin 4) :=
  ∑ e : Fin 4, positionalSquareLabel e

def positionalDAGProbeRel (x y : Fin 4) : Bool :=
  decide (x = 0 ∧ y = 2)

def positionalDAGProbeGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun x y ↦ positionalDAGProbeRel x y = true

theorem positionalDAGProbe_dummyThree :
    IsDummy positionalDAGProbeGraph 3 := by
  intro v
  fin_cases v <;>
    simp [positionalDAGProbeGraph, positionalDAGProbeRel,
      SimpleGraph.fromRel_adj]

/-- The quotient cycle has unit evaluation on the real probe edge `0--2`. -/
theorem graphEvaluation_positionalSquareLabelSum :
    graphEvaluation positionalDAGProbeGraph positionalSquareLabelSum = 1 := by
  rw [positionalSquareLabelSum, map_sum]
  rw [Fin.sum_univ_four]
  simp only [positionalSquareLabel, moveLiveStar, map_zero, add_zero]
  rw [graphEvaluation_liveStarVector, graphEvaluation_liveStarVector]
  simp [positionalDAGRoot, positionalDAGClose, liveSet, flip,
    positionalDAGProbeGraph, positionalDAGProbeRel]
  decide

/-- Therefore the nonzero state-DAG cycle has nonzero real-edge label after
deleting the untouched isolated dummy.  Incidence cancellation alone cannot
produce the required zero moment. -/
theorem realEdgeProjection_positionalSquareLabelSum_ne_zero :
    realEdgeProjection 3 positionalSquareLabelSum ≠ 0 := by
  intro hzero
  have heval := graphEvaluation_eq_zero_of_realEdgeProjection_eq_zero
    positionalDAGProbe_dummyThree hzero
  rw [graphEvaluation_positionalSquareLabelSum] at heval
  exact one_ne_zero heval

end

end Ogdoad.Fifo
