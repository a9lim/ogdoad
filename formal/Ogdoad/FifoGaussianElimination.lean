import Ogdoad.FifoCellSwapOutcomeBoundary
import Ogdoad.FifoRootCongruence

/-!
# Causal debt laws for Gaussian graph elimination

An elementary alternating-matrix congruence adds one source row and column
`i` to one target row and column `j`.  Algebraically these moves reduce every
alternating graph to hyperbolic matching blocks and isolates.  FIFO play does
not automatically respect that reduction: the target row is visible before
`j` opens and its whole residual degree is visible when `j` eventually
closes.

This file makes that obstruction exact.  Before the target opens, the charge
of a queued front `f != j` changes by the single source-row coordinate
`G(i,f)`.  After the target opens, every other front charge is unchanged, and
closing `j` changes by the source-row degree into the remaining untouched
set.  These identities are the causal ledger an adaptive Gaussian strategy
would have to cancel.  They do not assert root-value invariance under graph
congruence.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- On the modified target row, the elementary-congruence defect is exactly
the source-row coordinate. -/
theorem adjacencyBit_elementaryCongruenceGraph_target_add
    (G : SimpleGraph V) (i j k : V) (hkj : k ≠ j) :
    adjacencyBit (elementaryCongruenceGraph G i j) j k +
      adjacencyBit G j k = adjacencyBit G i k := by
  classical
  have h := adjacencyBit_elementaryCongruenceGraph_add G i j j k
  simpa [elementaryCongruenceRowWeight, hkj] using h

omit [Fintype V] in
/-- Once the target label is absent from the untouched set, every other
front has exactly the same close charge before and after the row operation. -/
theorem flip_elementaryCongruenceGraph_eq_of_target_not_mem
    (G : SimpleGraph V) (i j f : V) (U : Finset V)
    (hfj : f ≠ j) (hjU : j ∉ U) :
    flip (elementaryCongruenceGraph G i j) U f = flip G U f := by
  classical
  rw [flip_eq_sum_adjacencyBit, flip_eq_sum_adjacencyBit]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≠ j := fun h ↦ hjU (h ▸ hk)
  have hadj := elementaryCongruenceGraph_adj_away_iff G i j f k hfj hkj
  simp only [adjacencyBit]
  rw [if_congr hadj rfl rfl]

omit [Fintype V] in
/-- After the target has opened, its eventual close carries the whole
source-row residual degree as the congruence defect. -/
theorem flip_elementaryCongruenceGraph_target_add
    (G : SimpleGraph V) (i j : V) (U : Finset V) (hjU : j ∉ U) :
    flip (elementaryCongruenceGraph G i j) U j + flip G U j =
      flip G U i := by
  classical
  rw [flip_eq_sum_adjacencyBit, flip_eq_sum_adjacencyBit,
    flip_eq_sum_adjacencyBit, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact adjacencyBit_elementaryCongruenceGraph_target_add G i j k
    (fun h ↦ hjU (h ▸ hk))

omit [Fintype V] in
/-- Before the target opens, a queued non-target front sees exactly one bit
of congruence debt: its adjacency to the source row. -/
theorem flip_elementaryCongruenceGraph_add_of_target_mem
    (G : SimpleGraph V) (i j f : V) (U : Finset V)
    (hfj : f ≠ j) (hjU : j ∈ U) :
    flip (elementaryCongruenceGraph G i j) U f + flip G U f =
      adjacencyBit G i f := by
  classical
  have hInv := flip_elementaryCongruenceGraph_eq_of_target_not_mem
    G i j f (U.erase j) hfj (by simp)
  rw [flip_eq_flip_erase_add hjU, flip_eq_flip_erase_add hjU, hInv]
  have hrow := adjacencyBit_elementaryCongruenceGraph_target_add
    G i j f hfj
  rw [adjacencyBit_comm (elementaryCongruenceGraph G i j) f j,
    adjacencyBit_comm G f j]
  have hself : flip G (U.erase j) f + flip G (U.erase j) f = 0 :=
    CharTwo.add_self_eq_zero _
  calc
    flip G (U.erase j) f + adjacencyBit (elementaryCongruenceGraph G i j) j f +
        (flip G (U.erase j) f + adjacencyBit G j f) =
        (flip G (U.erase j) f + flip G (U.erase j) f) +
          (adjacencyBit (elementaryCongruenceGraph G i j) j f +
            adjacencyBit G j f) := by abel
    _ = adjacencyBit (elementaryCongruenceGraph G i j) j f +
          adjacencyBit G j f := by rw [hself, zero_add]
    _ = adjacencyBit G i f := hrow

omit [Fintype V] [DecidableEq V] in
/-- A Gaussian shear away from an existing pivot leaves that pivot edge
unchanged. -/
theorem elementaryCongruenceGraph_pivot_preserved
    (G : SimpleGraph V) (i j k : V) (hik : i ≠ k) (hjk : j ≠ k) :
    (elementaryCongruenceGraph G i k).Adj i j ↔ G.Adj i j :=
  elementaryCongruenceGraph_adj_away_iff G i k i j hik hjk

omit [Fintype V] [DecidableEq V] in
/-- If `i-j` and `k-j` are both edges, adding the `i` row and column to the
`k` row and column clears the latter edge.  This is the elementary pivot step
in symplectic Gaussian elimination. -/
theorem elementaryCongruenceGraph_clears_pivot_neighbor
    (G : SimpleGraph V) (i j k : V) (hjk : j ≠ k)
    (hij : G.Adj i j) (hkj : G.Adj k j) :
    ¬(elementaryCongruenceGraph G i k).Adj k j := by
  rw [elementaryCongruenceGraph_adj_j_iff G i k j hjk]
  simp [hij, hkj, Xor]

omit [Fintype V] [DecidableEq V] in
/-- The elementary pivot step can be performed without destroying a
distinguished isolated dummy, provided the dummy is not its target. -/
theorem IsDummy.elementaryPivot
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    (i k : V) (hdk : d ≠ k) :
    IsDummy (Ogdoad.Fifo.elementaryCongruenceGraph G i k) d :=
  Ogdoad.Fifo.IsDummy.elementaryCongruenceGraph hd i k hdk

/-! ## Multi-copy root interaction parity -/

/-- Every complete interaction between a score-zero source strategy and a
score-one strategy on its elementary shear has unit row debt.  This is the
play-level core of the root congruence obstruction, separated from the
strategy interaction which constructs the play. -/
theorem CrossGraphStrategyPlay.elementaryCongruenceRowEvaluation_eq_one
    (G : SimpleGraph V) (i j : V)
    (play : CrossGraphStrategyPlay G (elementaryCongruenceGraph G i j)
      (initial (V := V)) (initial (V := V))) :
    elementaryCongruenceRowEvaluation G i j play.moment = 1 := by
  have hGscore := play.traceG.terminal_score_eq_graphEvaluation
    play.isTerminalG
  have hHscore := play.traceH.terminal_score_eq_graphEvaluation
    play.isTerminalH
  have hHeval : graphEvaluation (elementaryCongruenceGraph G i j)
      play.moment = 1 := by
    rw [← hHscore]
    exact zmod2_eq_one_of_ne_zero _ play.scoreH
  have hGeval : graphEvaluation G play.moment = 0 := by
    rw [← hGscore]
    exact play.scoreG
  have hdefect := graphEvaluation_elementaryCongruenceGraph_add
    G i j play.moment
  rw [hHeval, hGeval, add_zero] at hdefect
  exact hdefect.symm

/-- Sum of the universal edge moments carried by several complete root
interactions. -/
def crossGraphPlayMomentSum (G : SimpleGraph V) (i j : V)
    (plays : List (CrossGraphStrategyPlay G
      (elementaryCongruenceGraph G i j)
      (initial (V := V)) (initial (V := V)))) : EdgeVector V :=
  (plays.map CrossGraphStrategyPlay.moment).sum

/-- Exact multi-copy parity law: the shear-row evaluation of a sum of common
interaction moments is the number of copies modulo two. -/
theorem elementaryCongruenceRowEvaluation_crossGraphPlayMomentSum
    (G : SimpleGraph V) (i j : V)
    (plays : List (CrossGraphStrategyPlay G
      (elementaryCongruenceGraph G i j)
      (initial (V := V)) (initial (V := V)))) :
    elementaryCongruenceRowEvaluation G i j
        (crossGraphPlayMomentSum G i j plays) =
      (plays.length : ZMod 2) := by
  induction plays with
  | nil => simp [crossGraphPlayMomentSum]
  | cons play plays ih =>
      rw [crossGraphPlayMomentSum, List.map_cons, List.sum_cons, map_add,
        CrossGraphStrategyPlay.elementaryCongruenceRowEvaluation_eq_one
          G i j play]
      change 1 + elementaryCongruenceRowEvaluation G i j
          ((plays.map CrossGraphStrategyPlay.moment).sum) =
        ((plays.length + 1 : Nat) : ZMod 2)
      rw [← crossGraphPlayMomentSum, ih]
      simp [Nat.cast_add, add_comm]

/-- An odd affine combination of complete source/target interactions can
never be row-neutral.  Two copies do cancel the row debt, but their
augmentation is even; adding any third copy restores unit debt.  Therefore
plain multi-copy interaction cannot by itself manufacture the odd neutral
certificate required for root shear transport. -/
theorem crossGraphPlayMomentSum_ne_zero_of_odd
    (G : SimpleGraph V) (i j : V)
    (plays : List (CrossGraphStrategyPlay G
      (elementaryCongruenceGraph G i j)
      (initial (V := V)) (initial (V := V))))
    (hodd : Odd plays.length) :
    elementaryCongruenceRowEvaluation G i j
      (crossGraphPlayMomentSum G i j plays) = 1 := by
  rw [elementaryCongruenceRowEvaluation_crossGraphPlayMomentSum]
  rw [← ZMod.natCast_mod plays.length 2, Nat.odd_iff.mp hodd]
  rfl

/-! ## A smallest conditioned obstruction to phase-only transport -/

/-- An orientation of the matching edge `0--2`. -/
def shearDebtSourceRel (x y : Fin 4) : Bool := decide (x = 0 ∧ y = 2)

/-- A matching edge `0--2` on four labels; `3` is the distinguished dummy
and `1` is an additional isolated real label. -/
def shearDebtSourceGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun x y ↦ shearDebtSourceRel x y = true

/-- An orientation of the path edges `0--2` and `1--2`. -/
def shearDebtTargetRel (x y : Fin 4) : Bool := decide
  ((x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 2))

/-- The target after adding row and column `0` to the real isolated row and
column `1`.  It is the path `0--2--1` together with the untouched dummy `3`. -/
def shearDebtTargetGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun x y ↦ shearDebtTargetRel x y = true

theorem shearDebtTargetGraph_eq_elementaryCongruence :
    shearDebtTargetGraph =
      elementaryCongruenceGraph shearDebtSourceGraph 0 1 := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [shearDebtTargetGraph, shearDebtTargetRel, shearDebtSourceGraph,
      shearDebtSourceRel, SimpleGraph.fromRel_adj,
      elementaryCongruenceGraph, Xor]

theorem shearDebtSourceGraph_dummy : IsDummy shearDebtSourceGraph 3 := by
  intro v
  fin_cases v <;>
    simp [shearDebtSourceGraph, shearDebtSourceRel, SimpleGraph.fromRel_adj]

theorem shearDebtTargetGraph_dummy : IsDummy shearDebtTargetGraph 3 := by
  rw [shearDebtTargetGraph_eq_elementaryCongruence]
  exact IsDummy.elementaryCongruenceGraph shearDebtSourceGraph_dummy 0 1 (by decide)

/-- The clear checkpoint reached by the common prefix `OPEN 2; OPEN 0`.
The shear target `1` and dummy `3` are both still untouched. -/
def shearDebtCheckpoint : State (Fin 4) where
  untouched := {1, 3}
  queue := [2, 0]
  ko := false
  toMove := false
  score := 0

theorem shearDebtCheckpoint_target_unopened :
    1 ∈ shearDebtCheckpoint.untouched := by decide

theorem shearDebtCheckpoint_dummy_unopened :
    3 ∈ shearDebtCheckpoint.untouched := by decide

theorem shearDebtCheckpoint_reachable (G : SimpleGraph (Fin 4)) :
    ∃ s,
      step G (initial (V := Fin 4)) (.open 2) = some s ∧
      step G s (.open 0) = some shearDebtCheckpoint := by
  let s : State (Fin 4) := {
    untouched := {0, 1, 3}
    queue := [2]
    ko := true
    toMove := true
    score := 0 }
  refine ⟨s, ?_, ?_⟩
  · have hU : (Finset.univ.erase 2 : Finset (Fin 4)) = {0, 1, 3} := by
      ext x
      fin_cases x <;> simp
    simp [step, initial, s, hU]
  · simp [step, s, shearDebtCheckpoint]

/-- Symmetrize an oriented Boolean edge relation. -/
def shearDebtAdj (rel : Fin 4 → Fin 4 → Bool) (x y : Fin 4) : Bool :=
  rel x y || rel y x

/-- Executable close charge for one of the two small graphs. -/
def shearDebtFlip (rel : Fin 4 → Fin 4 → Bool)
    (U : Finset (Fin 4)) (v : Fin 4) : ZMod 2 :=
  ((U.filter fun w ↦ shearDebtAdj rel v w = true).card : ZMod 2)

def shearDebtStep (rel : Fin 4 → Fin 4 → Bool) (s : State (Fin 4)) :
    Move (Fin 4) → Option (State (Fin 4))
  | .open v =>
      if v ∈ s.untouched then
        some {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove
          score := s.score }
      else none
  | .close =>
      match s.queue with
      | [] => none
      | f :: q =>
          if s.ko then none else
            some {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove
              score := s.score + shearDebtFlip rel s.untouched f }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

theorem shearDebtSourceFlip_eq_flip (U : Finset (Fin 4)) (v : Fin 4) :
    shearDebtFlip shearDebtSourceRel U v = flip shearDebtSourceGraph U v := by
  classical
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [shearDebtAdj, shearDebtSourceGraph,
      shearDebtSourceRel, SimpleGraph.fromRel_adj]

theorem shearDebtTargetFlip_eq_flip (U : Finset (Fin 4)) (v : Fin 4) :
    shearDebtFlip shearDebtTargetRel U v = flip shearDebtTargetGraph U v := by
  classical
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [shearDebtAdj, shearDebtTargetGraph,
      shearDebtTargetRel, SimpleGraph.fromRel_adj]

theorem shearDebtSourceStep_eq_step (s : State (Fin 4)) (m : Move (Fin 4)) :
    shearDebtStep shearDebtSourceRel s m = step shearDebtSourceGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [shearDebtStep, step]
  | close =>
      cases q <;> cases ko <;> simp [shearDebtStep, step,
        shearDebtSourceFlip_eq_flip]
  | pass => simp [shearDebtStep, step]

theorem shearDebtTargetStep_eq_step (s : State (Fin 4)) (m : Move (Fin 4)) :
    shearDebtStep shearDebtTargetRel s m = step shearDebtTargetGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [shearDebtStep, step]
  | close =>
      cases q <;> cases ko <;> simp [shearDebtStep, step,
        shearDebtTargetFlip_eq_flip]
  | pass => simp [shearDebtStep, step]

def shearDebtMoves : List (Move (Fin 4)) :=
  [.open 0, .open 1, .open 2, .open 3, .close, .pass]

theorem mem_shearDebtMoves (m : Move (Fin 4)) : m ∈ shearDebtMoves := by
  cases m with
  | «open» v => fin_cases v <;> simp [shearDebtMoves]
  | close => simp [shearDebtMoves]
  | pass => simp [shearDebtMoves]

def shearDebtSourceWinner (seat : Bool) : Bool :=
  finiteEvenWinner shearDebtMoves
    (shearDebtStep shearDebtSourceRel) seat
    (rank shearDebtCheckpoint + 1) shearDebtCheckpoint

def shearDebtTargetWinner (seat : Bool) : Bool :=
  finiteEvenWinner shearDebtMoves
    (shearDebtStep shearDebtTargetRel) seat
    (rank shearDebtCheckpoint + 1) shearDebtCheckpoint

theorem shearDebtSourceWinner_spec (seat : Bool) :
    if shearDebtSourceWinner seat then
      EvenWins shearDebtSourceGraph seat shearDebtCheckpoint
    else OddWins shearDebtSourceGraph seat shearDebtCheckpoint := by
  apply finiteEvenWinner_spec shearDebtSourceGraph shearDebtMoves
    mem_shearDebtMoves (shearDebtStep shearDebtSourceRel)
    shearDebtSourceStep_eq_step seat
    (rank shearDebtCheckpoint + 1) shearDebtCheckpoint
  omega

theorem shearDebtTargetWinner_spec (seat : Bool) :
    if shearDebtTargetWinner seat then
      EvenWins shearDebtTargetGraph seat shearDebtCheckpoint
    else OddWins shearDebtTargetGraph seat shearDebtCheckpoint := by
  apply finiteEvenWinner_spec shearDebtTargetGraph shearDebtMoves
    mem_shearDebtMoves (shearDebtStep shearDebtTargetRel)
    shearDebtTargetStep_eq_step seat
    (rank shearDebtCheckpoint + 1) shearDebtCheckpoint
  omega

theorem shearDebtSource_false_wins :
    shearDebtSourceWinner false = true := by decide

theorem shearDebtSource_true_wins :
    shearDebtSourceWinner true = true := by decide

theorem shearDebtTarget_false_wins :
    shearDebtTargetWinner false = true := by decide

theorem shearDebtTarget_true_loses :
    shearDebtTargetWinner true = false := by decide

/-- At debt zero with the target still unopened, a dummy-preserving shear can
change a reachable checkpoint from both-even to mover-controlled.  Hence a
mutual induction indexed only by target phase and one score-debt bit cannot
transport conditioned outcome sheets pointwise; a successful Gaussian proof
must also exploit root ancestry or a richer strategy-correlated invariant. -/
theorem shearDebt_unopened_zero_conditioned_outcome_boundary :
    BothEven shearDebtSourceGraph shearDebtCheckpoint ∧
      MoverControlled shearDebtTargetGraph shearDebtCheckpoint := by
  constructor
  · constructor
    · have h := shearDebtSourceWinner_spec false
      rw [shearDebtSource_false_wins] at h
      simpa [MoverEvenWins, shearDebtCheckpoint] using h
    · have h := shearDebtSourceWinner_spec true
      rw [shearDebtSource_true_wins] at h
      simpa [NonmoverEvenWins, shearDebtCheckpoint] using h
  · constructor
    · have h := shearDebtTargetWinner_spec false
      rw [shearDebtTarget_false_wins] at h
      simpa [MoverEvenWins, shearDebtCheckpoint] using h
    · have h := shearDebtTargetWinner_spec true
      rw [shearDebtTarget_true_loses] at h
      have hnot := (oddWins_iff_not_evenWins shearDebtTargetGraph true
        shearDebtCheckpoint).mp h
      simpa [NonmoverEvenWins, shearDebtCheckpoint] using hnot

end

end Ogdoad.Fifo
