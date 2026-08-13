import Ogdoad.FifoCellSwapOutcomeBoundary
import Ogdoad.FifoBlockInduction
import Ogdoad.FifoGaussianElimination
import Ogdoad.FifoMatching
import Ogdoad.FifoRootCongruence

/-!
# FIFO root outcome is not an alternating-form invariant

The smallest singular alternating matrix already separates the FIFO schedule
game from ordinary congruence classification.  Start with one edge on three
labels, so the third label is an isolated coordinate.  An elementary shear
which adds one endpoint row to the isolated row turns this graph into a
three-vertex path.  The source root is `BothEven`, while the path root is
`MoverControlled`.

Thus the empty-root FIFO outcome is neither invariant under alternating-matrix
congruence nor determined by rank and radical dimension.  In particular, a
nonzero radical vector cannot replace an actual isolated label in a proof of
the FIFO linking conjecture.
-/

namespace Ogdoad.Fifo

noncomputable section

/-- One orientation of the edges `0--2` and `1--2`. -/
def congruencePathRel (x y : Fin 3) : Bool := decide (
  (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 2))

/-- The three-vertex path `0--2--1`. -/
def congruencePathGraph : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun x y ↦ congruencePathRel x y = true

theorem congruencePathGraph_adj_iff (x y : Fin 3) :
    congruencePathGraph.Adj x y ↔
      (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) ∨
      (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) := by
  fin_cases x <;> fin_cases y <;>
    simp [congruencePathGraph, congruencePathRel,
      SimpleGraph.fromRel_adj]

/-- Adding the row of vertex `0` to the isolated row `1` of the one-edge
graph `0--2` gives exactly the path `0--2--1`. -/
theorem congruencePathGraph_eq_elementaryCongruence :
    congruencePathGraph =
      elementaryCongruenceGraph activeNeutralIntervalGraph 0 1 := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [congruencePathGraph, congruencePathRel,
      elementaryCongruenceGraph, activeNeutralIntervalGraph,
      SimpleGraph.fromRel_adj, Xor]

def congruencePathAdj (x y : Fin 3) : Bool :=
  congruencePathRel x y || congruencePathRel y x

def congruencePathFlip (U : Finset (Fin 3)) (v : Fin 3) : ZMod 2 :=
  ((U.filter fun w ↦ congruencePathAdj v w = true).card : ZMod 2)

theorem congruencePathFlip_eq_flip (U : Finset (Fin 3)) (v : Fin 3) :
    congruencePathFlip U v = flip congruencePathGraph U v := by
  classical
  simp only [congruencePathFlip, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [congruencePathAdj, congruencePathRel, congruencePathGraph,
      SimpleGraph.fromRel_adj]

def congruencePathStep (s : State (Fin 3)) :
    Move (Fin 3) → Option (State (Fin 3))
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
              score := s.score + congruencePathFlip s.untouched f }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

theorem congruencePathStep_eq_step (s : State (Fin 3)) (m : Move (Fin 3)) :
    congruencePathStep s m = step congruencePathGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [congruencePathStep, step]
  | close =>
      cases q <;> cases ko <;> simp [congruencePathStep, step,
        congruencePathFlip_eq_flip]
  | pass => simp [congruencePathStep, step]

def congruencePathMoves : List (Move (Fin 3)) :=
  [.open 0, .open 1, .open 2, .close, .pass]

theorem mem_congruencePathMoves (m : Move (Fin 3)) :
    m ∈ congruencePathMoves := by
  cases m with
  | «open» v => fin_cases v <;> simp [congruencePathMoves]
  | close => simp [congruencePathMoves]
  | pass => simp [congruencePathMoves]

def congruencePathWinner (seat : Bool) : Bool :=
  finiteEvenWinner congruencePathMoves
    congruencePathStep seat
    (rank (initial (V := Fin 3)) + 1) (initial (V := Fin 3))

theorem congruencePathWinner_spec (seat : Bool) :
    if congruencePathWinner seat then
      EvenWins congruencePathGraph seat (initial (V := Fin 3))
    else OddWins congruencePathGraph seat (initial (V := Fin 3)) := by
  apply finiteEvenWinner_spec congruencePathGraph congruencePathMoves
    mem_congruencePathMoves congruencePathStep congruencePathStep_eq_step seat
    (rank (initial (V := Fin 3)) + 1) (initial (V := Fin 3))
  omega

theorem congruencePathWinner_false_wins :
    congruencePathWinner false = true := by
  decide

theorem congruencePathWinner_true_loses :
    congruencePathWinner true = false := by
  decide

theorem congruencePath_moverControlled :
    MoverControlled congruencePathGraph (initial (V := Fin 3)) := by
  constructor
  · have h := congruencePathWinner_spec false
    rw [congruencePathWinner_false_wins] at h
    simpa [MoverEvenWins, initial] using h
  · have h := congruencePathWinner_spec true
    rw [congruencePathWinner_true_loses] at h
    have hnot := (oddWins_iff_not_evenWins congruencePathGraph true
      (initial (V := Fin 3))).mp h
    simpa [NonmoverEvenWins, initial] using hnot

/-- The source of the shear is a matching plus an isolated label, hence its
root is both-even. -/
theorem activeNeutralIntervalGraph_root_bothEven :
    BothEven activeNeutralIntervalGraph (initial (V := Fin 3)) := by
  have hmatching : IsMatchingGraph activeNeutralIntervalGraph := by
    intro v x y hvx hvy
    fin_cases v <;> fin_cases x <;> fin_cases y <;>
      simp [activeNeutralIntervalGraph, SimpleGraph.fromRel_adj] at hvx hvy ⊢
  exact ⟨by simpa [MoverEvenWins, initial] using
      evenWins_initial_of_matching hmatching false,
    by simpa [NonmoverEvenWins, initial] using
      evenWins_initial_of_matching hmatching true⟩

/-- One elementary alternating congruence changes the exact FIFO root
outcome, from both-even to mover-controlled. -/
theorem root_outcome_not_elementaryCongruence_invariant :
    BothEven activeNeutralIntervalGraph (initial (V := Fin 3)) ∧
      MoverControlled
        (elementaryCongruenceGraph activeNeutralIntervalGraph 0 1)
        (initial (V := Fin 3)) := by
  rw [← congruencePathGraph_eq_elementaryCongruence]
  exact ⟨activeNeutralIntervalGraph_root_bothEven,
    congruencePath_moverControlled⟩

/-! ## A dummy-preserving shear still has nonneutral common traces -/

def shearTraceSourceRel (x y : Fin 4) : Bool := decide (x = 0 ∧ y = 2)

def shearTraceSourceGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun x y ↦ shearTraceSourceRel x y = true

def shearTraceTargetRel (x y : Fin 4) : Bool := decide (
  (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 2))

def shearTraceTargetGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun x y ↦ shearTraceTargetRel x y = true

def shearTraceSourceAdj (x y : Fin 4) : Bool :=
  shearTraceSourceRel x y || shearTraceSourceRel y x

def shearTraceTargetAdj (x y : Fin 4) : Bool :=
  shearTraceTargetRel x y || shearTraceTargetRel y x

def explicitFlip4 (adj : Fin 4 → Fin 4 → Bool)
    (U : Finset (Fin 4)) (v : Fin 4) : ZMod 2 :=
  ((U.filter fun w ↦ adj v w = true).card : ZMod 2)

def explicitStep4 (adj : Fin 4 → Fin 4 → Bool)
    (s : State (Fin 4)) : Move (Fin 4) → Option (State (Fin 4))
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
              score := s.score + explicitFlip4 adj s.untouched f }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

theorem explicitFlip4_source_eq_flip (U : Finset (Fin 4)) (v : Fin 4) :
    explicitFlip4 shearTraceSourceAdj U v =
      flip shearTraceSourceGraph U v := by
  classical
  simp only [explicitFlip4, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [shearTraceSourceAdj, shearTraceSourceRel,
      shearTraceSourceGraph, SimpleGraph.fromRel_adj]

theorem explicitFlip4_target_eq_flip (U : Finset (Fin 4)) (v : Fin 4) :
    explicitFlip4 shearTraceTargetAdj U v =
      flip shearTraceTargetGraph U v := by
  classical
  simp only [explicitFlip4, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [shearTraceTargetAdj, shearTraceTargetRel,
      shearTraceTargetGraph, SimpleGraph.fromRel_adj]

theorem explicitStep4_source_eq_step (s : State (Fin 4)) (m : Move (Fin 4)) :
    explicitStep4 shearTraceSourceAdj s m = step shearTraceSourceGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [explicitStep4, step]
  | close =>
      cases q <;> cases ko <;> simp [explicitStep4, step,
        explicitFlip4_source_eq_flip]
  | pass => simp [explicitStep4, step]

theorem explicitStep4_target_eq_step (s : State (Fin 4)) (m : Move (Fin 4)) :
    explicitStep4 shearTraceTargetAdj s m = step shearTraceTargetGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [explicitStep4, step]
  | close =>
      cases q <;> cases ko <;> simp [explicitStep4, step,
        explicitFlip4_target_eq_flip]
  | pass => simp [explicitStep4, step]

theorem shearTraceTarget_eq_elementaryCongruence :
    shearTraceTargetGraph =
      elementaryCongruenceGraph shearTraceSourceGraph 0 1 := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [shearTraceTargetGraph, shearTraceTargetRel,
      shearTraceSourceGraph, shearTraceSourceRel,
      elementaryCongruenceGraph, SimpleGraph.fromRel_adj, Xor]

theorem shearTraceSource_dummy : IsDummy shearTraceSourceGraph 3 := by
  intro v
  fin_cases v <;>
    simp [shearTraceSourceGraph, shearTraceSourceRel,
      SimpleGraph.fromRel_adj]

def runMoves {V : Type*} (next : State V → Move V → Option (State V)) :
    State V → List (Move V) → Option (State V)
  | s, [] => some s
  | s, m :: ms => (next s m).bind fun t ↦ runMoves next t ms

theorem legalTrace_of_runMoves {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (next : State V → Move V → Option (State V))
    (hnext : ∀ s m, next s m = step G s m)
    {s t : State V} {ms : List (Move V)}
    (h : runMoves next s ms = some t) : LegalTrace G s ms t := by
  induction ms generalizing s with
  | nil =>
      simp [runMoves] at h
      subst t
      exact .nil s
  | cons m ms ih =>
      simp only [runMoves] at h
      cases hstep : next s m with
      | none => simp [hstep] at h
      | some u =>
          simp only [hstep, Option.bind_some] at h
          exact .cons (by rw [← hnext]; exact hstep) (ih h)

def nonneutralShearWord : List (Move (Fin 4)) :=
  [.open 1, .open 0, .close, .open 2, .close, .close,
    .open 3, .pass, .close]

def nonneutralShearSourceTerminal : State (Fin 4) where
  untouched := ∅
  queue := []
  ko := false
  toMove := true
  score := 0

def nonneutralShearTargetTerminal : State (Fin 4) where
  untouched := ∅
  queue := []
  ko := false
  toMove := true
  score := 1

theorem nonneutralShearWord_source_run :
    runMoves (explicitStep4 shearTraceSourceAdj) (initial (V := Fin 4))
      nonneutralShearWord = some nonneutralShearSourceTerminal := by
  decide

theorem nonneutralShearWord_target_run :
    runMoves (explicitStep4 shearTraceTargetAdj) (initial (V := Fin 4))
      nonneutralShearWord = some nonneutralShearTargetTerminal := by
  decide

/-- A shear which preserves the isolated dummy still admits a common legal
terminal schedule with source score zero and target score one.  Therefore
neutrality cannot quantify over all common traces; it must select an
interaction using the opposing strategy trees. -/
theorem exists_nonneutral_dummyPreservingShear_commonTrace :
    ∃ tG tH,
      LegalTrace shearTraceSourceGraph (initial (V := Fin 4))
        nonneutralShearWord tG ∧
      LegalTrace shearTraceTargetGraph (initial (V := Fin 4))
        nonneutralShearWord tH ∧
      Terminal tG ∧ Terminal tH ∧
      tG.score = 0 ∧ tH.score = 1 := by
  refine ⟨nonneutralShearSourceTerminal, nonneutralShearTargetTerminal,
    legalTrace_of_runMoves shearTraceSourceGraph
      (explicitStep4 shearTraceSourceAdj) explicitStep4_source_eq_step
      nonneutralShearWord_source_run,
    legalTrace_of_runMoves shearTraceTargetGraph
      (explicitStep4 shearTraceTargetAdj) explicitStep4_target_eq_step
      nonneutralShearWord_target_run, ?_⟩
  simp [Terminal, nonneutralShearSourceTerminal,
    nonneutralShearTargetTerminal]

/-- Fully packaged boundary: the shear target is a real label, the dummy is
isolated before and after the shear, yet the displayed common terminal word
has unit score defect. -/
theorem dummyPreservingShear_universalTraceNeutrality_false :
    IsDummy shearTraceSourceGraph 3 ∧
      shearTraceTargetGraph =
        elementaryCongruenceGraph shearTraceSourceGraph 0 1 ∧
      (3 : Fin 4) ≠ 1 ∧
      ∃ tG tH,
        LegalTrace shearTraceSourceGraph (initial (V := Fin 4))
          nonneutralShearWord tG ∧
        LegalTrace shearTraceTargetGraph (initial (V := Fin 4))
          nonneutralShearWord tH ∧
        Terminal tG ∧ Terminal tH ∧
        tG.score = 0 ∧ tH.score = 1 := by
  exact ⟨shearTraceSource_dummy,
    shearTraceTarget_eq_elementaryCongruence, by decide,
    exists_nonneutral_dummyPreservingShear_commonTrace⟩

def shearCheckpoint : State (Fin 4) where
  untouched := {2, 3}
  queue := [1]
  ko := false
  toMove := true
  score := 0

def shearTraceMoves : List (Move (Fin 4)) :=
  [.open 0, .open 1, .open 2, .open 3, .close, .pass]

theorem mem_shearTraceMoves (m : Move (Fin 4)) : m ∈ shearTraceMoves := by
  cases m with
  | «open» v => fin_cases v <;> simp [shearTraceMoves]
  | close => simp [shearTraceMoves]
  | pass => simp [shearTraceMoves]

def shearCheckpointSourceWinner (seat : Bool) : Bool :=
  finiteEvenWinner shearTraceMoves
    (explicitStep4 shearTraceSourceAdj) seat
    (rank shearCheckpoint + 1) shearCheckpoint

def shearCheckpointTargetWinner (seat : Bool) : Bool :=
  finiteEvenWinner shearTraceMoves
    (explicitStep4 shearTraceTargetAdj) seat
    (rank shearCheckpoint + 1) shearCheckpoint

theorem shearCheckpointSourceWinner_spec (seat : Bool) :
    if shearCheckpointSourceWinner seat then
      EvenWins shearTraceSourceGraph seat shearCheckpoint
    else OddWins shearTraceSourceGraph seat shearCheckpoint := by
  apply finiteEvenWinner_spec shearTraceSourceGraph shearTraceMoves
    mem_shearTraceMoves (explicitStep4 shearTraceSourceAdj)
    explicitStep4_source_eq_step seat (rank shearCheckpoint + 1)
    shearCheckpoint
  omega

theorem shearCheckpointTargetWinner_spec (seat : Bool) :
    if shearCheckpointTargetWinner seat then
      EvenWins shearTraceTargetGraph seat shearCheckpoint
    else OddWins shearTraceTargetGraph seat shearCheckpoint := by
  apply finiteEvenWinner_spec shearTraceTargetGraph shearTraceMoves
    mem_shearTraceMoves (explicitStep4 shearTraceTargetAdj)
    explicitStep4_target_eq_step seat (rank shearCheckpoint + 1)
    shearCheckpoint
  omega

theorem shearCheckpoint_source_false_wins :
    shearCheckpointSourceWinner false = true := by decide

theorem shearCheckpoint_source_true_wins :
    shearCheckpointSourceWinner true = true := by decide

theorem shearCheckpoint_target_false_loses :
    shearCheckpointTargetWinner false = false := by decide

theorem shearCheckpoint_target_true_wins :
    shearCheckpointTargetWinner true = true := by decide

/-- Even while the dummy remains untouched, a real-target elementary shear
can change an intermediate public state's outcome from both-even to
mover-controlled.  Therefore root shear invariance cannot be proved by a
pointwise four-sheet transport induction over all descendant states. -/
theorem dummyPreservingShear_checkpoint_sheet_not_invariant :
    3 ∈ shearCheckpoint.untouched ∧
      BothEven shearTraceSourceGraph shearCheckpoint ∧
      MoverControlled shearTraceTargetGraph shearCheckpoint := by
  have hs0 := shearCheckpointSourceWinner_spec false
  rw [shearCheckpoint_source_false_wins] at hs0
  have hs1 := shearCheckpointSourceWinner_spec true
  rw [shearCheckpoint_source_true_wins] at hs1
  have ht1 := shearCheckpointTargetWinner_spec true
  rw [shearCheckpoint_target_true_wins] at ht1
  have ht0 := shearCheckpointTargetWinner_spec false
  rw [shearCheckpoint_target_false_loses] at ht0
  refine ⟨by decide, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa [MoverEvenWins, shearCheckpoint] using hs1
  · simpa [NonmoverEvenWins, shearCheckpoint] using hs0
  · simpa [MoverEvenWins, shearCheckpoint] using ht1
  · have hnot := (oddWins_iff_not_evenWins shearTraceTargetGraph false
      shearCheckpoint).mp ht0
    simpa [NonmoverEvenWins, shearCheckpoint] using hnot

/-! ## A minimal ternary first-step obstruction -/

/-- Two-edge source path `1--0--2`, with label `3` isolated. -/
def ternaryForkSourceRel (x y : Fin 4) : Bool := decide (
  (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2))

def ternaryForkSourceGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun x y ↦ ternaryForkSourceRel x y = true

/-- The target matching edge `0--1`, obtained by shearing row `1` into the
real target row `2`. -/
def ternaryForkTargetRel (x y : Fin 4) : Bool := decide (x = 0 ∧ y = 1)

def ternaryForkTargetGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun x y ↦ ternaryForkTargetRel x y = true

def ternaryForkSourceAdj (x y : Fin 4) : Bool :=
  ternaryForkSourceRel x y || ternaryForkSourceRel y x

def ternaryForkTargetAdj (x y : Fin 4) : Bool :=
  ternaryForkTargetRel x y || ternaryForkTargetRel y x

theorem explicitFlip4_ternaryForkSource_eq_flip
    (U : Finset (Fin 4)) (v : Fin 4) :
    explicitFlip4 ternaryForkSourceAdj U v =
      flip ternaryForkSourceGraph U v := by
  classical
  simp only [explicitFlip4, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [ternaryForkSourceAdj, ternaryForkSourceRel,
      ternaryForkSourceGraph, SimpleGraph.fromRel_adj]

theorem explicitFlip4_ternaryForkTarget_eq_flip
    (U : Finset (Fin 4)) (v : Fin 4) :
    explicitFlip4 ternaryForkTargetAdj U v =
      flip ternaryForkTargetGraph U v := by
  classical
  simp only [explicitFlip4, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [ternaryForkTargetAdj, ternaryForkTargetRel,
      ternaryForkTargetGraph, SimpleGraph.fromRel_adj]

theorem explicitStep4_ternaryForkSource_eq_step
    (s : State (Fin 4)) (m : Move (Fin 4)) :
    explicitStep4 ternaryForkSourceAdj s m =
      step ternaryForkSourceGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [explicitStep4, step]
  | close =>
      cases q <;> cases ko <;> simp [explicitStep4, step,
        explicitFlip4_ternaryForkSource_eq_flip]
  | pass => simp [explicitStep4, step]

theorem explicitStep4_ternaryForkTarget_eq_step
    (s : State (Fin 4)) (m : Move (Fin 4)) :
    explicitStep4 ternaryForkTargetAdj s m =
      step ternaryForkTargetGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [explicitStep4, step]
  | close =>
      cases q <;> cases ko <;> simp [explicitStep4, step,
        explicitFlip4_ternaryForkTarget_eq_flip]
  | pass => simp [explicitStep4, step]

theorem ternaryForkTarget_eq_elementaryCongruence :
    ternaryForkTargetGraph =
      elementaryCongruenceGraph ternaryForkSourceGraph 1 2 := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [ternaryForkTargetGraph, ternaryForkTargetRel,
      ternaryForkSourceGraph, ternaryForkSourceRel,
      elementaryCongruenceGraph, SimpleGraph.fromRel_adj, Xor]

theorem ternaryForkSource_dummy : IsDummy ternaryForkSourceGraph 3 := by
  intro v
  fin_cases v <;>
    simp [ternaryForkSourceGraph, ternaryForkSourceRel,
      SimpleGraph.fromRel_adj]

def ternaryForkCheckpoint : State (Fin 4) where
  untouched := {0, 3}
  queue := [1, 2]
  ko := false
  toMove := false
  score := 0

def ternaryForkAfterOpen1 : State (Fin 4) where
  untouched := {0, 2, 3}
  queue := [1]
  ko := true
  toMove := true
  score := 0

theorem ternaryForkCheckpoint_common_reachable :
    StepPath ternaryForkSourceGraph (initial (V := Fin 4))
        [.open 1, .open 2] ternaryForkCheckpoint ∧
      StepPath ternaryForkTargetGraph (initial (V := Fin 4))
        [.open 1, .open 2] ternaryForkCheckpoint := by
  have hs1 : step ternaryForkSourceGraph (initial (V := Fin 4)) (.open 1) =
      some ternaryForkAfterOpen1 := by
    rw [← explicitStep4_ternaryForkSource_eq_step]
    decide
  have hs2 : step ternaryForkSourceGraph ternaryForkAfterOpen1 (.open 2) =
      some ternaryForkCheckpoint := by
    rw [← explicitStep4_ternaryForkSource_eq_step]
    decide
  have ht1 : step ternaryForkTargetGraph (initial (V := Fin 4)) (.open 1) =
      some ternaryForkAfterOpen1 := by
    rw [← explicitStep4_ternaryForkTarget_eq_step]
    decide
  have ht2 : step ternaryForkTargetGraph ternaryForkAfterOpen1 (.open 2) =
      some ternaryForkCheckpoint := by
    rw [← explicitStep4_ternaryForkTarget_eq_step]
    decide
  constructor
  · exact StepPath.cons hs1 (StepPath.cons hs2 (StepPath.nil _))
  · exact StepPath.cons ht1 (StepPath.cons ht2 (StepPath.nil _))

def ternaryForkSourceWinner (seat : Bool) (s : State (Fin 4)) : Bool :=
  finiteEvenWinner shearTraceMoves
    (explicitStep4 ternaryForkSourceAdj) seat (rank s + 1) s

def ternaryForkTargetWinner (seat : Bool) (s : State (Fin 4)) : Bool :=
  finiteEvenWinner shearTraceMoves
    (explicitStep4 ternaryForkTargetAdj) seat (rank s + 1) s

theorem ternaryForkSourceWinner_spec (seat : Bool) (s : State (Fin 4)) :
    if ternaryForkSourceWinner seat s then
      EvenWins ternaryForkSourceGraph seat s
    else OddWins ternaryForkSourceGraph seat s := by
  apply finiteEvenWinner_spec ternaryForkSourceGraph shearTraceMoves
    mem_shearTraceMoves (explicitStep4 ternaryForkSourceAdj)
    explicitStep4_ternaryForkSource_eq_step seat (rank s + 1) s
  omega

theorem ternaryForkTargetWinner_spec (seat : Bool) (s : State (Fin 4)) :
    if ternaryForkTargetWinner seat s then
      EvenWins ternaryForkTargetGraph seat s
    else OddWins ternaryForkTargetGraph seat s := by
  apply finiteEvenWinner_spec ternaryForkTargetGraph shearTraceMoves
    mem_shearTraceMoves (explicitStep4 ternaryForkTargetAdj)
    explicitStep4_ternaryForkTarget_eq_step seat (rank s + 1) s
  omega

/-- A simultaneous first step retaining both source even strategies and the
target odd strategy.  This is the local compatibility required by the
proposed ternary first-return coupling. -/
def TernaryBothEvenOddStep {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (seat : Bool) (s : State V) : Prop :=
  ∃ (m : Move V) (tG tH : State V),
    step G s m = some tG ∧ step H s m = some tH ∧
      BothEven G tG ∧ Nonempty (OddStrategy H seat tH)

def ternaryForkAfterOpen0 : State (Fin 4) where
  untouched := {3}
  queue := [1, 2, 0]
  ko := false
  toMove := true
  score := 0

def ternaryForkAfterOpen3 : State (Fin 4) where
  untouched := (Finset.erase ({0, 3} : Finset (Fin 4)) 3)
  queue := [1, 2, 3]
  ko := false
  toMove := true
  score := 0

def ternaryForkAfterClose : State (Fin 4) where
  untouched := {0, 3}
  queue := [2]
  ko := false
  toMove := true
  score := 1

theorem ternaryForkCheckpoint_source_false_wins :
    ternaryForkSourceWinner false ternaryForkCheckpoint = true := by decide

theorem ternaryForkCheckpoint_source_true_wins :
    ternaryForkSourceWinner true ternaryForkCheckpoint = true := by decide

theorem ternaryForkCheckpoint_target_false_wins :
    ternaryForkTargetWinner false ternaryForkCheckpoint = true := by decide

theorem ternaryForkCheckpoint_target_true_loses :
    ternaryForkTargetWinner true ternaryForkCheckpoint = false := by decide

theorem ternaryForkAfterOpen0_target_true_wins :
    ternaryForkTargetWinner true ternaryForkAfterOpen0 = true := by decide

theorem ternaryForkAfterOpen3_target_true_wins :
    ternaryForkTargetWinner true ternaryForkAfterOpen3 = true := by decide

theorem ternaryForkAfterClose_source_false_loses :
    ternaryForkSourceWinner false ternaryForkAfterClose = false := by decide

theorem ternaryForkCheckpoint_source_bothEven :
    BothEven ternaryForkSourceGraph ternaryForkCheckpoint := by
  have hfalse := ternaryForkSourceWinner_spec false ternaryForkCheckpoint
  rw [ternaryForkCheckpoint_source_false_wins] at hfalse
  have htrue := ternaryForkSourceWinner_spec true ternaryForkCheckpoint
  rw [ternaryForkCheckpoint_source_true_wins] at htrue
  exact ⟨by simpa [MoverEvenWins, ternaryForkCheckpoint] using hfalse,
    by simpa [NonmoverEvenWins, ternaryForkCheckpoint] using htrue⟩

theorem ternaryForkCheckpoint_target_moverControlled :
    MoverControlled ternaryForkTargetGraph ternaryForkCheckpoint := by
  have hfalse := ternaryForkTargetWinner_spec false ternaryForkCheckpoint
  rw [ternaryForkCheckpoint_target_false_wins] at hfalse
  have htrue := ternaryForkTargetWinner_spec true ternaryForkCheckpoint
  rw [ternaryForkCheckpoint_target_true_loses] at htrue
  refine ⟨by simpa [MoverEvenWins, ternaryForkCheckpoint] using hfalse, ?_⟩
  have hnot := (oddWins_iff_not_evenWins ternaryForkTargetGraph true
    ternaryForkCheckpoint).mp htrue
  simpa [NonmoverEvenWins, ternaryForkCheckpoint] using hnot

/-- At the minimal fork checkpoint no common first move can retain both
source even strategies and the target odd strategy.  The target odd policy
is forced toward `CLOSE`, while that child is odd for the complementary
source seat; both target-compatible OPEN children are even for the target
seat and therefore leave its odd strategy. -/
theorem ternaryForkCheckpoint_no_ternaryBothEvenOddStep :
    ¬TernaryBothEvenOddStep ternaryForkSourceGraph
      ternaryForkTargetGraph true ternaryForkCheckpoint := by
  rintro ⟨m, tG, tH, hstepG, hstepH, hboth, ⟨hodd⟩⟩
  cases m with
  | «open» v =>
      fin_cases v
      · have htH : tH = ternaryForkAfterOpen0 := by
          simpa [step, ternaryForkCheckpoint, ternaryForkAfterOpen0] using
            hstepH.symm
        subst tH
        have heven := ternaryForkTargetWinner_spec true ternaryForkAfterOpen0
        rw [ternaryForkAfterOpen0_target_true_wins] at heven
        exact heven.not_oddWins hodd.toOddWins
      · simp [step, ternaryForkCheckpoint] at hstepG
      · simp [step, ternaryForkCheckpoint] at hstepG
      · have htH : tH = ternaryForkAfterOpen3 := by
          simpa [step, ternaryForkCheckpoint, ternaryForkAfterOpen3] using
            hstepH.symm
        subst tH
        have heven := ternaryForkTargetWinner_spec true ternaryForkAfterOpen3
        rw [ternaryForkAfterOpen3_target_true_wins] at heven
        exact heven.not_oddWins hodd.toOddWins
  | close =>
      have htG : tG = ternaryForkAfterClose := by
        rw [← explicitStep4_ternaryForkSource_eq_step] at hstepG
        have hcalc : explicitStep4 ternaryForkSourceAdj
            ternaryForkCheckpoint .close = some ternaryForkAfterClose := by
          decide
        rw [hcalc] at hstepG
        exact (Option.some.inj hstepG).symm
      subst tG
      have hsourceOdd :=
        ternaryForkSourceWinner_spec false ternaryForkAfterClose
      rw [ternaryForkAfterClose_source_false_loses] at hsourceOdd
      have hsourceEven :
          EvenWins ternaryForkSourceGraph false ternaryForkAfterClose := by
        simpa [NonmoverEvenWins, ternaryForkAfterClose] using hboth.2
      exact hsourceEven.not_oddWins hsourceOdd
  | pass => simp [step, ternaryForkCheckpoint] at hstepG

/-- Fully packaged four-vertex no-go for pointwise three-strategy coupling.
The dummy is still live, the target is a genuine dummy-preserving shear, and
the checkpoint is reached by one common two-OPEN prefix.  Nevertheless the
full source `BothEven` sheet and the target's losing-seat odd strategy have no
common child retaining all three policies. -/
theorem dummyPreservingShear_ternaryFirstStepCoupling_false :
    IsDummy ternaryForkSourceGraph 3 ∧
      ternaryForkTargetGraph =
        elementaryCongruenceGraph ternaryForkSourceGraph 1 2 ∧
      (3 : Fin 4) ≠ 2 ∧ 3 ∈ ternaryForkCheckpoint.untouched ∧
      StepPath ternaryForkSourceGraph (initial (V := Fin 4))
        [.open 1, .open 2] ternaryForkCheckpoint ∧
      StepPath ternaryForkTargetGraph (initial (V := Fin 4))
        [.open 1, .open 2] ternaryForkCheckpoint ∧
      BothEven ternaryForkSourceGraph ternaryForkCheckpoint ∧
      MoverControlled ternaryForkTargetGraph ternaryForkCheckpoint ∧
      ¬TernaryBothEvenOddStep ternaryForkSourceGraph
        ternaryForkTargetGraph true ternaryForkCheckpoint := by
  exact ⟨ternaryForkSource_dummy,
    ternaryForkTarget_eq_elementaryCongruence, by decide, by decide,
    ternaryForkCheckpoint_common_reachable.1,
    ternaryForkCheckpoint_common_reachable.2,
    ternaryForkCheckpoint_source_bothEven,
    ternaryForkCheckpoint_target_moverControlled,
    ternaryForkCheckpoint_no_ternaryBothEvenOddStep⟩

/-- Root-level formulation suggested by the exact checkpoint boundary: a
dummy-preserving shear should transport either physical target at score-zero
empty-queue checkpoints while the isolated dummy remains untouched.  The
pointwise analogue with a nonempty queue is false above. -/
def DummyEmptyQueueShearForward : Prop :=
  ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (d : V), IsDummy G d →
      ∀ (i j : V), i ≠ j → d ≠ j →
        ∀ (U : Finset V), d ∈ U → ∀ (turn seat : Bool),
          EvenWins G seat (emptyRoot U turn) →
            EvenWins (elementaryCongruenceGraph G i j) seat
              (emptyRoot U turn)

/-- Strictly weaker empty-queue target sufficient for FIFO: preserve the cold
`BothEven` sheet, without transporting either seat on arbitrary controlled
source sheets. -/
def DummyEmptyQueueShearBothEvenForward : Prop :=
  ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (d : V), IsDummy G d →
      ∀ (i j : V), i ≠ j → d ≠ j →
        ∀ (U : Finset V), d ∈ U → ∀ turn : Bool,
          BothEven G (emptyRoot U turn) →
            BothEven (elementaryCongruenceGraph G i j)
              (emptyRoot U turn)

/-- Exact first-return block defect, stated via the universal OPEN moment.
For a path between score-zero empty queues on `G`, its shear-row evaluation
is exactly the terminal score obtained by replaying the same public word on
the sheared graph.  Thus empty-queue root invariance reduces to selecting or
pairing first-return words with zero controller defect. -/
theorem emptyQueueBlock_shear_terminalScore_eq_rowEvaluation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (i j : V)
    {s tG tH : State V} {z : EdgeVector V}
    (hsWF : WellFormed s)
    (hsQueue : s.queue = []) (hsScore : s.score = 0)
    (htraceG : LiveStarTrace G s tG z)
    (htraceH : LiveStarTrace (elementaryCongruenceGraph G i j) s tH z)
    (htGQueue : tG.queue = []) (htHQueue : tH.queue = [])
    (htGScore : tG.score = 0) :
    tH.score = elementaryCongruenceRowEvaluation G i j z := by
  have hpotG := htraceG.potential_eq_add_evaluation hsWF
  have hpotH := htraceH.potential_eq_add_evaluation hsWF
  -- The source need not literally be `initial`, so discharge its potential
  -- from the stated empty queue and zero score.
  have hsPotG : potential G s = 0 := by
    simp [potential, queueCut, hsQueue, hsScore]
  have hsPotH : potential (elementaryCongruenceGraph G i j) s = 0 := by
    simp [potential, queueCut, hsQueue, hsScore]
  have htGPot : potential G tG = tG.score := by
    simp [potential, queueCut, htGQueue]
  have htHPot : potential (elementaryCongruenceGraph G i j) tH = tH.score := by
    simp [potential, queueCut, htHQueue]
  rw [hsPotG, zero_add, htGPot, htGScore] at hpotG
  rw [hsPotH, zero_add, htHPot] at hpotH
  have hGeval : graphEvaluation G z = 0 := hpotG.symm
  have hdefect := graphEvaluation_elementaryCongruenceGraph_add G i j z
  rw [← hpotH, hGeval, add_zero] at hdefect
  exact hdefect

/-- Zero-score replay across a first-return block is equivalent to vanishing
of its shear controller moment. -/
theorem emptyQueueBlock_shear_terminalScore_zero_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (i j : V)
    {s tG tH : State V} {z : EdgeVector V}
    (hsWF : WellFormed s) (hsQueue : s.queue = []) (hsScore : s.score = 0)
    (htraceG : LiveStarTrace G s tG z)
    (htraceH : LiveStarTrace (elementaryCongruenceGraph G i j) s tH z)
    (htGQueue : tG.queue = []) (htHQueue : tH.queue = [])
    (htGScore : tG.score = 0) :
    tH.score = 0 ↔ elementaryCongruenceRowEvaluation G i j z = 0 := by
  rw [emptyQueueBlock_shear_terminalScore_eq_rowEvaluation G i j hsWF
    hsQueue hsScore htraceG htraceH htGQueue htHQueue htGScore]

/-- Without assuming that either replay is neutral, the endpoint score debt of
an empty-queue block is exactly its elementary-shear row evaluation.  Thus a
unit controller moment swaps the score sheet at the first return, whereas a
zero moment preserves it. -/
theorem emptyQueueBlock_shear_terminalScores_add_eq_rowEvaluation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (i j : V)
    {s tG tH : State V} {z : EdgeVector V}
    (hsWF : WellFormed s) (hsQueue : s.queue = []) (hsScore : s.score = 0)
    (htraceG : LiveStarTrace G s tG z)
    (htraceH : LiveStarTrace (elementaryCongruenceGraph G i j) s tH z)
    (htGQueue : tG.queue = []) (htHQueue : tH.queue = []) :
    tH.score + tG.score = elementaryCongruenceRowEvaluation G i j z := by
  have hpotG := htraceG.potential_eq_add_evaluation hsWF
  have hpotH := htraceH.potential_eq_add_evaluation hsWF
  have hsPotG : potential G s = 0 := by
    simp [potential, queueCut, hsQueue, hsScore]
  have hsPotH : potential (elementaryCongruenceGraph G i j) s = 0 := by
    simp [potential, queueCut, hsQueue, hsScore]
  have htGPot : potential G tG = tG.score := by
    simp [potential, queueCut, htGQueue]
  have htHPot : potential (elementaryCongruenceGraph G i j) tH = tH.score := by
    simp [potential, queueCut, htHQueue]
  rw [hsPotG, zero_add, htGPot] at hpotG
  rw [hsPotH, zero_add, htHPot] at hpotH
  have hdefect := graphEvaluation_elementaryCongruenceGraph_add G i j z
  rwa [← hpotH, ← hpotG] at hdefect

/-! ## Stopped interaction at the next empty queue -/

/-- One interaction of an even source strategy and an odd target strategy,
stopped as soon as the common public queue is empty.  Unlike a complete
`CrossGraphStrategyPlay`, this retains both descendant strategy trees. -/
structure CrossGraphStrategyBlockExit {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (seat : Bool) (sG sH : State V) where
  terminalG : State V
  terminalH : State V
  moves : List (Move V)
  moment : EdgeVector V
  evenTail : EvenWins G seat terminalG
  oddTail : OddStrategy H seat terminalH
  pathG : StepPath G sG moves terminalG
  pathH : StepPath H sH moves terminalH
  traceG : LiveStarTrace G sG terminalG moment
  traceH : LiveStarTrace H sH terminalH moment
  public_eq : terminalG.public = terminalH.public
  queue_empty : terminalG.queue = []

def CrossGraphStrategyBlockExit.prepend
    {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} {seat : Bool} {sG sH tG tH : State V}
    {m : Move V} (hpublic : sG.public = sH.public)
    (hstepG : step G sG m = some tG) (hstepH : step H sH m = some tH)
    (tail : CrossGraphStrategyBlockExit G H seat tG tH) :
    CrossGraphStrategyBlockExit G H seat sG sH := by
  have hstar : moveLiveStar sG m = moveLiveStar sH m :=
    moveLiveStar_eq_of_public_eq hpublic m
  exact {
    terminalG := tail.terminalG
    terminalH := tail.terminalH
    moves := m :: tail.moves
    moment := moveLiveStar sG m + tail.moment
    evenTail := tail.evenTail
    oddTail := tail.oddTail
    pathG := StepPath.cons hstepG tail.pathG
    pathH := StepPath.cons hstepH tail.pathH
    traceG := LiveStarTrace.cons hstepG tail.traceG
    traceH := by
      rw [hstar]
      exact LiveStarTrace.cons hstepH tail.traceH
    public_eq := tail.public_eq
    queue_empty := tail.queue_empty }

theorem queue_ne_empty_of_emptyQueue_step
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {s t : State V} {m : Move V}
    (hqueue : s.queue = []) (hstep : step G s m = some t) :
    t.queue ≠ [] := by
  cases m with
  | «open» v =>
      simp only [step] at hstep
      split at hstep
      · cases hstep
        simp [hqueue]
      · contradiction
  | close => simp [step, hqueue] at hstep
  | pass => simp [step, hqueue] at hstep

theorem EvenWins.exists_crossGraphStrategyBlockExit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (seat : Bool) :
    ∀ {sG : State V}, EvenWins G seat sG →
      ∀ {sH : State V}, sG.public = sH.public →
        OddStrategy H seat sH → sG.queue ≠ [] →
        Nonempty (CrossGraphStrategyBlockExit G H seat sG sH) := by
  intro sG heven
  induction heven with
  | terminal sG hterminalG _ =>
      intro sH hpublic hodd hqueue
      exact False.elim (hqueue hterminalG.2)
  | choose sG hseat m tG hstepG hevenTail ih =>
      intro sH hpublic hodd hqueue
      have hturn : sG.toMove = sH.toMove :=
        congrArg PublicState.toMove hpublic
      cases hodd with
      | terminal _ hterminalH _ =>
          obtain ⟨tH, hstepH, _⟩ :=
            exists_step_of_public_eq G H hpublic hstepG
          exact False.elim (terminal_no_step hterminalH ⟨m, tH, hstepH⟩)
      | choose _ hoddSeat _ _ _ _ =>
          exact False.elim (hoddSeat (hturn ▸ hseat))
      | answer _ _ _ childrenH =>
          obtain ⟨tH, hstepH, hpublic'⟩ :=
            exists_step_of_public_eq G H hpublic hstepG
          let oddTail := childrenH m tH hstepH
          have hstar : moveLiveStar sG m = moveLiveStar sH m :=
            moveLiveStar_eq_of_public_eq hpublic m
          by_cases hempty : tG.queue = []
          · exact ⟨{
              terminalG := tG
              terminalH := tH
              moves := [m]
              moment := moveLiveStar sG m
              evenTail := hevenTail
              oddTail := oddTail
              pathG := StepPath.cons hstepG (StepPath.nil _)
              pathH := StepPath.cons hstepH (StepPath.nil _)
              traceG := by
                simpa using LiveStarTrace.cons hstepG (LiveStarTrace.refl tG)
              traceH := by
                rw [hstar]
                simpa using LiveStarTrace.cons hstepH (LiveStarTrace.refl tH)
              public_eq := hpublic'
              queue_empty := hempty }⟩
          · obtain ⟨tail⟩ := ih hpublic' oddTail hempty
            exact ⟨{
              terminalG := tail.terminalG
              terminalH := tail.terminalH
              moves := m :: tail.moves
              moment := moveLiveStar sG m + tail.moment
              evenTail := tail.evenTail
              oddTail := tail.oddTail
              pathG := StepPath.cons hstepG tail.pathG
              pathH := StepPath.cons hstepH tail.pathH
              traceG := LiveStarTrace.cons hstepG tail.traceG
              traceH := by
                rw [hstar]
                exact LiveStarTrace.cons hstepH tail.traceH
              public_eq := tail.public_eq
              queue_empty := tail.queue_empty }⟩
  | answer sG hseat hasMoveG childrenG ih =>
      intro sH hpublic hodd hqueue
      have hturn : sG.toMove = sH.toMove :=
        congrArg PublicState.toMove hpublic
      cases hodd with
      | terminal _ hterminalH _ =>
          obtain ⟨m, tG, hstepG⟩ := hasMoveG
          obtain ⟨tH, hstepH, _⟩ :=
            exists_step_of_public_eq G H hpublic hstepG
          exact False.elim (terminal_no_step hterminalH ⟨m, tH, hstepH⟩)
      | choose _ _ m tH hstepH oddTail =>
          obtain ⟨tG, hstepG, hpublic'⟩ :=
            exists_step_of_public_eq H G hpublic.symm hstepH
          let evenTail := childrenG m tG hstepG
          have hstar : moveLiveStar sG m = moveLiveStar sH m :=
            moveLiveStar_eq_of_public_eq hpublic m
          by_cases hempty : tG.queue = []
          · exact ⟨{
              terminalG := tG
              terminalH := tH
              moves := [m]
              moment := moveLiveStar sG m
              evenTail := evenTail
              oddTail := oddTail
              pathG := StepPath.cons hstepG (StepPath.nil _)
              pathH := StepPath.cons hstepH (StepPath.nil _)
              traceG := by
                simpa using LiveStarTrace.cons hstepG (LiveStarTrace.refl tG)
              traceH := by
                rw [hstar]
                simpa using LiveStarTrace.cons hstepH (LiveStarTrace.refl tH)
              public_eq := hpublic'.symm
              queue_empty := hempty }⟩
          · obtain ⟨tail⟩ := ih m tG hstepG hpublic'.symm oddTail hempty
            exact ⟨{
              terminalG := tail.terminalG
              terminalH := tail.terminalH
              moves := m :: tail.moves
              moment := moveLiveStar sG m + tail.moment
              evenTail := tail.evenTail
              oddTail := tail.oddTail
              pathG := StepPath.cons hstepG tail.pathG
              pathH := StepPath.cons hstepH tail.pathH
              traceG := LiveStarTrace.cons hstepG tail.traceG
              traceH := by
                rw [hstar]
                exact LiveStarTrace.cons hstepH tail.traceH
              public_eq := tail.public_eq
              queue_empty := tail.queue_empty }⟩
      | answer _ hoddSeat _ _ =>
          exact False.elim (hseat (hturn.trans hoddSeat))

/-- Starting from a nonterminal empty queue, opposite strategies determine a
nonempty common first block and retain opposite descendant strategies at its
next empty-queue endpoint. -/
theorem EvenWins.exists_crossGraphStrategyFirstBlockExit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (seat : Bool)
    {sG sH : State V} (heven : EvenWins G seat sG)
    (hpublic : sG.public = sH.public) (hodd : OddStrategy H seat sH)
    (hqueue : sG.queue = []) (hU : sG.untouched.Nonempty) :
    ∃ exit : CrossGraphStrategyBlockExit G H seat sG sH,
      exit.moves ≠ [] := by
  cases heven with
  | terminal _ hterminal _ => exact False.elim (hU.ne_empty hterminal.1)
  | choose _ hseat m tG hstepG evenTail =>
      have hturn : sG.toMove = sH.toMove :=
        congrArg PublicState.toMove hpublic
      cases hodd with
      | terminal _ hterminalH _ =>
          obtain ⟨tH, hstepH, _⟩ :=
            exists_step_of_public_eq G H hpublic hstepG
          exact False.elim (terminal_no_step hterminalH ⟨m, tH, hstepH⟩)
      | choose _ hoddSeat _ _ _ _ =>
          exact False.elim (hoddSeat (hturn ▸ hseat))
      | answer _ _ _ childrenH =>
          obtain ⟨tH, hstepH, hpublic'⟩ :=
            exists_step_of_public_eq G H hpublic hstepG
          let oddTail := childrenH m tH hstepH
          have hqueueT : tG.queue ≠ [] :=
            queue_ne_empty_of_emptyQueue_step hqueue hstepG
          obtain ⟨tail⟩ := evenTail.exists_crossGraphStrategyBlockExit
            G H seat hpublic' oddTail hqueueT
          refine ⟨tail.prepend hpublic hstepG hstepH, ?_⟩
          simp [CrossGraphStrategyBlockExit.prepend]
  | answer _ hseat hasMoveG childrenG =>
      have hturn : sG.toMove = sH.toMove :=
        congrArg PublicState.toMove hpublic
      cases hodd with
      | terminal _ hterminalH _ =>
          obtain ⟨m, tG, hstepG⟩ := hasMoveG
          obtain ⟨tH, hstepH, _⟩ :=
            exists_step_of_public_eq G H hpublic hstepG
          exact False.elim (terminal_no_step hterminalH ⟨m, tH, hstepH⟩)
      | choose _ _ m tH hstepH oddTail =>
          obtain ⟨tG, hstepG, hpublic'⟩ :=
            exists_step_of_public_eq H G hpublic.symm hstepH
          let evenTail := childrenG m tG hstepG
          have hqueueT : tG.queue ≠ [] :=
            queue_ne_empty_of_emptyQueue_step hqueue hstepG
          obtain ⟨tail⟩ := evenTail.exists_crossGraphStrategyBlockExit
            G H seat hpublic'.symm oddTail hqueueT
          refine ⟨tail.prepend hpublic hstepG hstepH, ?_⟩
          simp [CrossGraphStrategyBlockExit.prepend]
      | answer _ hoddSeat _ _ =>
          exact False.elim (hseat (hturn.trans hoddSeat))

/-- A genuine first-return interaction strictly descends the well-founded
game rank.  This is the induction parameter retained by the stopped strategy
trees at the block endpoint. -/
theorem CrossGraphStrategyBlockExit.rank_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} {seat : Bool} {sG sH : State V}
    (exit : CrossGraphStrategyBlockExit G H seat sG sH)
    (hne : exit.moves ≠ []) :
    rank exit.terminalG < rank sG :=
  exit.pathG.rank_lt_of_nonempty hne

/-- If a first-return endpoint is not terminal, its next choice belongs to
the same physical controller as at the start of the block. -/
theorem CrossGraphStrategyBlockExit.toMove_eq_of_terminal_untouched_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} {seat : Bool} {sG sH : State V}
    (exit : CrossGraphStrategyBlockExit G H seat sG sH)
    (hsQueue : sG.queue = []) (hne : exit.moves ≠ [])
    (htU : exit.terminalG.untouched.Nonempty) :
    exit.terminalG.toMove = sG.toMove := by
  obtain ⟨_, _, _, _, _, _, hturn⟩ :=
    exit.pathG.consecutive_empty_queue_choices hsQueue exit.queue_empty hne htU
  exact hturn

/-- The score sheets carried by a stopped source/shear interaction differ by
exactly the block controller debt.  This is the Bellman datum that survives at
the first empty-queue descendant. -/
theorem CrossGraphStrategyBlockExit.shear_terminalScores_add_eq_rowEvaluation
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {i j : V} {seat : Bool} {s : State V}
    (exit : CrossGraphStrategyBlockExit G
      (elementaryCongruenceGraph G i j) seat s s)
    (hsWF : WellFormed s) (hsQueue : s.queue = []) (hsScore : s.score = 0) :
    exit.terminalH.score + exit.terminalG.score =
      elementaryCongruenceRowEvaluation G i j exit.moment := by
  have htHQueue : exit.terminalH.queue = [] := by
    have hqueues := congrArg PublicState.queue exit.public_eq
    exact hqueues.symm.trans exit.queue_empty
  exact emptyQueueBlock_shear_terminalScores_add_eq_rowEvaluation
    G i j hsWF hsQueue hsScore exit.traceG exit.traceH
      exit.queue_empty htHQueue

/-- A public-state equality plus the missing score coordinate reconstructs
the full private state. -/
theorem state_eq_of_public_eq_of_score_eq
    {V : Type*} [DecidableEq V] {s t : State V}
    (hpublic : s.public = t.public) (hscore : s.score = t.score) : s = t := by
  cases s
  cases t
  simp only [State.public, PublicState.mk.injEq, State.mk.injEq] at hpublic hscore ⊢
  aesop

/-- The controller debt is not merely a scalar endpoint identity: after a
common first block, the sheared endpoint is exactly the corresponding score
translation of the source endpoint. -/
theorem CrossGraphStrategyBlockExit.terminalH_eq_scoreTranslate_rowEvaluation
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {i j : V} {seat : Bool} {s : State V}
    (exit : CrossGraphStrategyBlockExit G
      (elementaryCongruenceGraph G i j) seat s s)
    (hsWF : WellFormed s) (hsQueue : s.queue = []) (hsScore : s.score = 0) :
    exit.terminalH = scoreTranslate
      (elementaryCongruenceRowEvaluation G i j exit.moment) exit.terminalG := by
  have hdebt := exit.shear_terminalScores_add_eq_rowEvaluation
    hsWF hsQueue hsScore
  apply state_eq_of_public_eq_of_score_eq
  · simpa [scoreTranslate, State.public] using exit.public_eq.symm
  · calc
      exit.terminalH.score =
          (exit.terminalH.score + exit.terminalG.score) +
            exit.terminalG.score := by
              simp [add_assoc, CharTwo.add_self_eq_zero]
      _ = elementaryCongruenceRowEvaluation G i j exit.moment +
            exit.terminalG.score := by rw [hdebt]
      _ = (scoreTranslate
          (elementaryCongruenceRowEvaluation G i j exit.moment)
            exit.terminalG).score := by rfl

/-- On a unit-debt first return, the target odd tail becomes an even tail for
the complementary physical seat after normalizing both endpoints to the
source score sheet.  This is the exact sheet rotation that prevents a direct
minimal-counterexample descent. -/
theorem CrossGraphStrategyBlockExit.target_complementaryEven_of_shearRow_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {i j : V} {seat : Bool} {s : State V}
    (exit : CrossGraphStrategyBlockExit G
      (elementaryCongruenceGraph G i j) seat s s)
    (hsWF : WellFormed s) (hsQueue : s.queue = []) (hsScore : s.score = 0)
    (hrho : elementaryCongruenceRowEvaluation G i j exit.moment = 1) :
    EvenWins (elementaryCongruenceGraph G i j) (!seat) exit.terminalG := by
  have heq := exit.terminalH_eq_scoreTranslate_rowEvaluation
    hsWF hsQueue hsScore
  rw [hrho] at heq
  have hodd : OddWins (elementaryCongruenceGraph G i j) seat
      (scoreTranslate 1 exit.terminalG) := by
    rw [← heq]
    exact exit.oddTail.toOddWins
  exact (oddWins_scoreTranslate_one_iff_evenWins
    (elementaryCongruenceGraph G i j) seat exit.terminalG).mp hodd

/-- On a zero-debt first return the two endpoints literally coincide, so the
retained tails are a genuine smaller same-seat forward counterexample. -/
theorem CrossGraphStrategyBlockExit.terminal_eq_of_shearRow_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {i j : V} {seat : Bool} {s : State V}
    (exit : CrossGraphStrategyBlockExit G
      (elementaryCongruenceGraph G i j) seat s s)
    (hsWF : WellFormed s) (hsQueue : s.queue = []) (hsScore : s.score = 0)
    (hrho : elementaryCongruenceRowEvaluation G i j exit.moment = 0) :
    exit.terminalH = exit.terminalG := by
  have heq := exit.terminalH_eq_scoreTranslate_rowEvaluation
    hsWF hsQueue hsScore
  simpa [hrho, scoreTranslate] using heq

/-- Once the shear target is absent from both the untouched carrier and the
queue, source and sheared games have identical next-state functions. -/
theorem step_elementaryCongruenceGraph_eq_of_target_absent
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (i j : V)
    (s : State V) (m : Move V) (hjU : j ∉ s.untouched)
    (hjq : j ∉ s.queue) :
    step (elementaryCongruenceGraph G i j) s m = step G s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  simp only at hjU hjq
  cases m with
  | «open» v => simp [step]
  | close =>
      cases q with
      | nil => simp [step]
      | cons f q =>
          have hfj : f ≠ j := by
            intro h
            subst f
            exact hjq (by simp)
          have hflip := flip_elementaryCongruenceGraph_eq_of_target_not_mem
            G i j f U hfj hjU
          cases ko <;> simp [step, hflip]
  | pass => simp [step]

/-- Absence of a consumed target label is forward invariant. -/
theorem target_absent_of_step
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {j : V}
    {s t : State V} {m : Move V} (hjU : j ∉ s.untouched)
    (hjq : j ∉ s.queue) (hstep : step G s m = some t) :
    j ∉ t.untouched ∧ j ∉ t.queue := by
  cases m with
  | «open» v =>
      simp only [step] at hstep
      split at hstep
      · rename_i hv
        cases hstep
        have hvj : v ≠ j := fun h ↦ hjU (h ▸ hv)
        constructor
        · exact fun hmem ↦ hjU (Finset.mem_of_mem_erase hmem)
        · simp [List.mem_append, hjq, Ne.symm hvj]
      · contradiction
  | close =>
      simp only [step] at hstep
      split at hstep
      · contradiction
      · split at hstep
        · contradiction
        · cases hstep
          exact ⟨hjU, by
            rename_i f q hqueue _
            rw [hqueue] at hjq
            exact (by simpa using hjq : j ≠ f ∧ j ∉ q).2⟩
  | pass =>
      simp only [step] at hstep
      split at hstep
      · cases hstep
        exact ⟨hjU, hjq⟩
      · contradiction

/-- After the shear target has been completely consumed, every source even
strategy transports verbatim to the sheared graph. -/
theorem EvenWins.elementaryCongruenceGraph_of_target_absent
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (i j : V)
    {seat : Bool} {s : State V} (h : EvenWins G seat s)
    (hjU : j ∉ s.untouched) (hjq : j ∉ s.queue) :
    EvenWins (elementaryCongruenceGraph G i j) seat s := by
  induction h with
  | terminal s hterminal hscore =>
      exact EvenWins.terminal s hterminal hscore
  | choose s hseat m t hstep _ ih =>
      have hstep' : step (elementaryCongruenceGraph G i j) s m = some t := by
        rw [step_elementaryCongruenceGraph_eq_of_target_absent
          G i j s m hjU hjq]
        exact hstep
      obtain ⟨hjUt, hjqt⟩ := target_absent_of_step hjU hjq hstep
      exact EvenWins.choose s hseat m t hstep' (ih hjUt hjqt)
  | answer s hseat hasMove children ih =>
      have hasMove' : ∃ m t,
          step (elementaryCongruenceGraph G i j) s m = some t := by
        obtain ⟨m, t, hstep⟩ := hasMove
        exact ⟨m, t, by
          rw [step_elementaryCongruenceGraph_eq_of_target_absent
            G i j s m hjU hjq]
          exact hstep⟩
      refine EvenWins.answer s hseat hasMove' ?_
      intro m t hstep'
      have hstep : step G s m = some t := by
        rw [← step_elementaryCongruenceGraph_eq_of_target_absent
          G i j s m hjU hjq]
        exact hstep'
      obtain ⟨hjUt, hjqt⟩ := target_absent_of_step hjU hjq hstep
      exact ih m t hstep hjUt hjqt

/-- The same consumed-target transport in the reverse direction. -/
theorem EvenWins.of_elementaryCongruenceGraph_target_absent
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (i j : V)
    {seat : Bool} {s : State V}
    (h : EvenWins (elementaryCongruenceGraph G i j) seat s)
    (hjU : j ∉ s.untouched) (hjq : j ∉ s.queue) :
    EvenWins G seat s := by
  induction h with
  | terminal s hterminal hscore =>
      exact EvenWins.terminal s hterminal hscore
  | choose s hseat m t hstep _ ih =>
      have hstep' : step G s m = some t := by
        rw [← step_elementaryCongruenceGraph_eq_of_target_absent
          G i j s m hjU hjq]
        exact hstep
      obtain ⟨hjUt, hjqt⟩ := target_absent_of_step hjU hjq hstep'
      exact EvenWins.choose s hseat m t hstep' (ih hjUt hjqt)
  | answer s hseat hasMove children ih =>
      have hasMove' : ∃ m t, step G s m = some t := by
        obtain ⟨m, t, hstep⟩ := hasMove
        exact ⟨m, t, by
          rw [← step_elementaryCongruenceGraph_eq_of_target_absent
            G i j s m hjU hjq]
          exact hstep⟩
      refine EvenWins.answer s hseat hasMove' ?_
      intro m t hstep'
      have hstep : step (elementaryCongruenceGraph G i j) s m = some t := by
        rw [step_elementaryCongruenceGraph_eq_of_target_absent
          G i j s m hjU hjq]
        exact hstep'
      obtain ⟨hjUt, hjqt⟩ := target_absent_of_step hjU hjq hstep'
      exact ih m t hstep hjUt hjqt

/-- A stopped opposite-strategy interaction whose first empty return has
already consumed the shear target must carry unit debt.  Zero debt would
identify the endpoints, after which the source even tail transports to the
target graph and contradicts the retained target odd tail. -/
theorem CrossGraphStrategyBlockExit.shear_rowEvaluation_eq_one_of_target_consumed
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {i j : V} {seat : Bool} {s : State V}
    (exit : CrossGraphStrategyBlockExit G
      (elementaryCongruenceGraph G i j) seat s s)
    (hsWF : WellFormed s) (hsQueue : s.queue = []) (hsScore : s.score = 0)
    (hj : j ∉ exit.terminalG.untouched) :
    elementaryCongruenceRowEvaluation G i j exit.moment = 1 := by
  apply zmod2_eq_one_of_ne_zero
  intro hrho
  have heq := exit.terminal_eq_of_shearRow_eq_zero
    hsWF hsQueue hsScore hrho
  have hevenH : EvenWins (elementaryCongruenceGraph G i j) seat
      exit.terminalG :=
    exit.evenTail.elementaryCongruenceGraph_of_target_absent
      G i j hj (by simp [exit.queue_empty])
  rw [← heq] at hevenH
  exact hevenH.not_oddWins exit.oddTail.toOddWins

/-- The unit-debt consumed-target branch is cold on the source-normalized
sheet: the retained source strategy supplies one seat, while score-normalizing
the target odd tail supplies the complementary seat; target absence transports
both strategies across the shear. -/
theorem CrossGraphStrategyBlockExit.bothEven_normalized_of_target_consumed
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {i j : V} {seat : Bool} {s : State V}
    (exit : CrossGraphStrategyBlockExit G
      (elementaryCongruenceGraph G i j) seat s s)
    (hsWF : WellFormed s) (hsQueue : s.queue = []) (hsScore : s.score = 0)
    (hj : j ∉ exit.terminalG.untouched) :
    BothEven G exit.terminalG ∧
      BothEven (elementaryCongruenceGraph G i j) exit.terminalG := by
  have hrho := exit.shear_rowEvaluation_eq_one_of_target_consumed
    hsWF hsQueue hsScore hj
  have hotherH := exit.target_complementaryEven_of_shearRow_eq_one
    hsWF hsQueue hsScore hrho
  have hjq : j ∉ exit.terminalG.queue := by simp [exit.queue_empty]
  have hseatH := exit.evenTail.elementaryCongruenceGraph_of_target_absent
    G i j hj hjq
  have hotherG := hotherH.of_elementaryCongruenceGraph_target_absent
    G i j hj hjq
  have hseatG := exit.evenTail
  constructor
  · cases seat <;> cases hturn : exit.terminalG.toMove <;>
      simp [BothEven, MoverEvenWins, NonmoverEvenWins, hturn]
        at hseatG hotherG ⊢ <;> aesop
  · cases seat <;> cases hturn : exit.terminalG.toMove <;>
      simp [BothEven, MoverEvenWins, NonmoverEvenWins, hturn]
        at hseatH hotherH ⊢ <;> aesop

/-- Exact survival trichotomy at a stopped first return.  Consuming the shear
target forces unit debt.  Otherwise either both the target and dummy remain
available for smaller-carrier induction, or the dummy alone has already been
consumed while the shear target remains live. -/
theorem CrossGraphStrategyBlockExit.target_dummy_survival_trichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {i j d : V} {seat : Bool} {s : State V}
    (exit : CrossGraphStrategyBlockExit G
      (elementaryCongruenceGraph G i j) seat s s)
    (hsWF : WellFormed s) (hsQueue : s.queue = []) (hsScore : s.score = 0) :
    (j ∉ exit.terminalG.untouched ∧
        elementaryCongruenceRowEvaluation G i j exit.moment = 1) ∨
      (j ∈ exit.terminalG.untouched ∧ d ∈ exit.terminalG.untouched) ∨
      (j ∈ exit.terminalG.untouched ∧ d ∉ exit.terminalG.untouched) := by
  by_cases hj : j ∈ exit.terminalG.untouched
  · by_cases hd : d ∈ exit.terminalG.untouched
    · exact Or.inr (Or.inl ⟨hj, hd⟩)
    · exact Or.inr (Or.inr ⟨hj, hd⟩)
  · exact Or.inl ⟨hj,
      exit.shear_rowEvaluation_eq_one_of_target_consumed
        hsWF hsQueue hsScore hj⟩

/-- Winning strategies for complementary named seats are exactly enough to
form the mover/nonmover `BothEven` sheet, regardless of the current turn. -/
theorem bothEven_of_complementary_evenWins
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s : State V}
    (seat : Bool) (hseat : EvenWins G seat s)
    (hother : EvenWins G (!seat) s) : BothEven G s := by
  cases seat <;> cases hturn : s.toMove <;>
    simp [BothEven, MoverEvenWins, NonmoverEvenWins, hturn] at hseat hother ⊢ <;>
      aesop

/-- An explicit odd strategy for either named seat excludes the full
`BothEven` sheet. -/
theorem OddStrategy.not_bothEven
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s : State V}
    {seat : Bool} (hodd : OddStrategy G seat s) : ¬BothEven G s := by
  intro hboth
  have heven : EvenWins G seat s := by
    cases seat <;> cases hturn : s.toMove <;>
      simp [BothEven, MoverEvenWins, NonmoverEvenWins, hturn] at hboth ⊢ <;>
        aesop
  exact heven.not_oddWins hodd.toOddWins

/-- Consequently, a zero-debt return would be a genuine smaller
`BothEven`-preservation counterexample if the common word also stayed inside
the source strategy for the complementary seat.  This extra ancestry witness
is precisely what ordinary two-strategy interaction does not retain. -/
theorem CrossGraphStrategyBlockExit.smaller_bothEven_counterexample_of_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {i j : V} {seat : Bool} {s : State V}
    (exit : CrossGraphStrategyBlockExit G
      (elementaryCongruenceGraph G i j) seat s s)
    (hsWF : WellFormed s) (hsQueue : s.queue = []) (hsScore : s.score = 0)
    (hrho : elementaryCongruenceRowEvaluation G i j exit.moment = 0)
    (hother : EvenWins G (!seat) exit.terminalG) :
    BothEven G exit.terminalG ∧
      ¬BothEven (elementaryCongruenceGraph G i j) exit.terminalG := by
  have heq := exit.terminal_eq_of_shearRow_eq_zero
    hsWF hsQueue hsScore hrho
  refine ⟨bothEven_of_complementary_evenWins seat exit.evenTail hother, ?_⟩
  rw [← heq]
  exact exit.oddTail.not_bothEven

/-- If the first queue return is already terminal, opposite retained strategy
tails force opposite endpoint scores, hence the block debt is necessarily one.
Neutral debt can occur only at a proper smaller Bellman descendant. -/
theorem CrossGraphStrategyBlockExit.shear_rowEvaluation_eq_one_of_terminal
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {i j : V} {seat : Bool} {s : State V}
    (exit : CrossGraphStrategyBlockExit G
      (elementaryCongruenceGraph G i j) seat s s)
    (hsWF : WellFormed s) (hsQueue : s.queue = []) (hsScore : s.score = 0)
    (htU : exit.terminalG.untouched = ∅) :
    elementaryCongruenceRowEvaluation G i j exit.moment = 1 := by
  have htG : Terminal exit.terminalG := ⟨htU, exit.queue_empty⟩
  have hscoreG : exit.terminalG.score = 0 := by
    cases exit.evenTail with
    | terminal _ _ hscore => exact hscore
    | choose _ _ m t hstep _ =>
        exact False.elim (terminal_no_step htG ⟨m, t, hstep⟩)
    | answer _ _ hasMove _ =>
        exact False.elim (terminal_no_step htG hasMove)
  have htHQueue : exit.terminalH.queue = [] := by
    have hqueues := congrArg PublicState.queue exit.public_eq
    exact hqueues.symm.trans exit.queue_empty
  have htHU : exit.terminalH.untouched = ∅ := by
    have hUs := congrArg PublicState.untouched exit.public_eq
    exact hUs.symm.trans htU
  have htH : Terminal exit.terminalH := ⟨htHU, htHQueue⟩
  have hscoreH : exit.terminalH.score = 1 := by
    have hne : exit.terminalH.score ≠ 0 := by
      cases exit.oddTail with
      | terminal _ _ hscore => exact hscore
      | choose _ _ m t hstep _ =>
          exact False.elim (terminal_no_step htH ⟨m, t, hstep⟩)
      | answer _ _ hasMove _ =>
          exact False.elim (terminal_no_step htH hasMove)
    exact zmod2_eq_one_of_ne_zero _ hne
  have hdebt := exit.shear_terminalScores_add_eq_rowEvaluation
    hsWF hsQueue hsScore
  rw [hscoreH, hscoreG, add_zero] at hdebt
  exact hdebt.symm

/-- Exact first-return Bellman descent for opposite source/shear strategies.
The interaction stops after a nonempty block, keeps both strategy tails, has
strictly smaller rank, and records the full endpoint score discrepancy in one
row-evaluation bit. -/
theorem EvenWins.exists_shearFirstBlockDescent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (i j : V) (seat : Bool) {s : State V}
    (hsWF : WellFormed s) (hsQueue : s.queue = []) (hsScore : s.score = 0)
    (hsU : s.untouched.Nonempty) (heven : EvenWins G seat s)
    (hodd : OddStrategy (elementaryCongruenceGraph G i j) seat s) :
    ∃ exit : CrossGraphStrategyBlockExit G
        (elementaryCongruenceGraph G i j) seat s s,
      exit.moves ≠ [] ∧ rank exit.terminalG < rank s ∧
        exit.terminalH.score + exit.terminalG.score =
          elementaryCongruenceRowEvaluation G i j exit.moment := by
  obtain ⟨exit, hne⟩ := heven.exists_crossGraphStrategyFirstBlockExit
    G (elementaryCongruenceGraph G i j) seat rfl hodd hsQueue hsU
  exact ⟨exit, hne, exit.rank_lt hne,
    exit.shear_terminalScores_add_eq_rowEvaluation hsWF hsQueue hsScore⟩

/-- The shear-row charge of one OPEN live star has only two controller terms:
opening the modified label `j` reads the `i`-row on the remaining live set;
opening any other label reads the single `i-v` bit exactly while `j` is live. -/
theorem elementaryCongruenceRowEvaluation_liveStarVector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (i j : V) (L : Finset V) (v : V) :
    elementaryCongruenceRowEvaluation G i j (liveStarVector L v) =
      (if v = j then flip G (L.erase j) i else 0) +
        if j ∈ L.erase v then adjacencyBit G i v else 0 := by
  classical
  rw [liveStarVector, map_sum]
  simp only [elementaryCongruenceRowEvaluation_single, mul_one,
    elementaryCongruenceRowWeight]
  by_cases hvj : v = j
  · subst v
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false,
      false_and, ↓reduceIte, add_zero]
    rw [flip_eq_sum_adjacencyBit]
    apply Finset.sum_congr rfl
    intro w hw
    have hwj : w ≠ j := (Finset.mem_erase.mp hw).1
    simp [hwj]
  · simp only [if_neg hvj]
    by_cases hj : j ∈ L.erase v
    · rw [if_pos hj]
      rw [Finset.sum_eq_single j]
      · simp [hvj]
      · intro w hw hwj
        simp [hvj, hwj]
      · exact fun h ↦ (h hj).elim
    · rw [if_neg hj]
      apply Finset.sum_eq_zero
      intro w hw
      have hwj : w ≠ j := by
        intro h
        subst w
        exact hj hw
      simp [hvj, hwj]

/-- Opening an isolated dummy has zero shear-row controller charge whenever
the shear modifies a real row. -/
theorem elementaryCongruenceRowEvaluation_dummy_liveStar_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    (i j : V) (hdj : d ≠ j) (L : Finset V) :
    elementaryCongruenceRowEvaluation G i j (liveStarVector L d) = 0 := by
  rw [elementaryCongruenceRowEvaluation_liveStarVector]
  have hid : ¬G.Adj i d := by simpa [G.adj_comm] using hd i
  simp [hdj, adjacencyBit, hid]

/-- Adding the isolated dummy to the live set does not change the controller
charge of any real OPEN.  Hence commuting the dummy past a fixed OPEN cannot
toggle the shear defect directly; it must change which real OPEN a policy
selects. -/
theorem elementaryCongruenceRowEvaluation_liveStar_insert_dummy
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    (i j : V) (hdj : d ≠ j) (L : Finset V) (v : V) (hdv : d ≠ v) :
    elementaryCongruenceRowEvaluation G i j
        (liveStarVector (insert d L) v) =
      elementaryCongruenceRowEvaluation G i j (liveStarVector L v) := by
  rw [elementaryCongruenceRowEvaluation_liveStarVector,
    elementaryCongruenceRowEvaluation_liveStarVector]
  have hjd : j ≠ d := Ne.symm hdj
  by_cases hvj : v = j
  · subst v
    have herase : (insert d L).erase j = insert d (L.erase j) := by
      ext w
      simp only [Finset.mem_erase, Finset.mem_insert]
      aesop
    rw [herase, flip_insert_dummy hd]
    simp [hjd]
  · have hjv : j ≠ v := Ne.symm hvj
    simp [hvj, hjv, hjd]

/-- A unit shear defect on a complete trace is witnessed by at least one
individual transition with unit controller charge. -/
theorem LiveStarTrace.exists_unit_shearController
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (i j : V) :
    ∀ {s t : State V} {z : EdgeVector V}, LiveStarTrace G s t z →
      elementaryCongruenceRowEvaluation G i j z = 1 →
      ∃ (a b : State V) (m : Move V),
        step G a m = some b ∧
          elementaryCongruenceRowEvaluation G i j
            (moveLiveStar a m) = 1 := by
  intro s t z htrace hone
  induction htrace with
  | refl s =>
      simp [elementaryCongruenceRowEvaluation] at hone
  | @cons a b t m tailMoment hstep tail ih =>
      rw [map_add] at hone
      by_cases hhead : elementaryCongruenceRowEvaluation G i j
          (moveLiveStar a m) = 0
      · rw [hhead, zero_add] at hone
        exact ih hone
      · have hheadOne : elementaryCongruenceRowEvaluation G i j
            (moveLiveStar a m) = 1 :=
          zmod2_eq_one_of_ne_zero _ hhead
        exact ⟨a, b, m, hstep, hheadOne⟩

/-- Exact local shape of a unit controller event.  CLOSE and PASS contribute
nothing.  An OPEN contributes one only by opening `j` across an odd surviving
`i`-row, or by opening an `i`-neighbour while `j` is still live. -/
theorem unit_shearController_open_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (i j : V) (s : State V) (m : Move V)
    (hone : elementaryCongruenceRowEvaluation G i j
      (moveLiveStar s m) = 1) :
    ∃ v : V, m = .open v ∧
      ((v = j ∧ flip G ((liveSet s).erase j) i = 1) ∨
        (v ≠ j ∧ j ∈ (liveSet s).erase v ∧
          adjacencyBit G i v = 1)) := by
  cases m with
  | close => simp [moveLiveStar, elementaryCongruenceRowEvaluation] at hone
  | pass => simp [moveLiveStar, elementaryCongruenceRowEvaluation] at hone
  | «open» v =>
      refine ⟨v, rfl, ?_⟩
      change elementaryCongruenceRowEvaluation G i j
        (liveStarVector (liveSet s) v) = 1 at hone
      rw [elementaryCongruenceRowEvaluation_liveStarVector] at hone
      by_cases hvj : v = j
      · left
        refine ⟨hvj, ?_⟩
        subst v
        simpa using hone
      · right
        refine ⟨hvj, ?_⟩
        simp only [if_neg hvj, zero_add] at hone
        by_cases hjlive : j ∈ (liveSet s).erase v
        · exact ⟨hjlive, by simpa [hjlive] using hone⟩
        · simp [hjlive] at hone

/-- Every unit shear-defect trace contains one of the two explicit OPEN
controller events.  This is the first point at which a dummy commutation must
remain compatible with both opposing root policies. -/
theorem LiveStarTrace.exists_unit_shearController_open
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (i j : V)
    {s t : State V} {z : EdgeVector V} (htrace : LiveStarTrace G s t z)
    (hone : elementaryCongruenceRowEvaluation G i j z = 1) :
    ∃ (a b : State V) (v : V),
      step G a (.open v) = some b ∧
      ((v = j ∧ flip G ((liveSet a).erase j) i = 1) ∨
        (v ≠ j ∧ j ∈ (liveSet a).erase v ∧
          adjacencyBit G i v = 1)) := by
  obtain ⟨a, b, m, hstep, hunit⟩ :=
    htrace.exists_unit_shearController G i j hone
  obtain ⟨v, rfl, hcases⟩ :=
    unit_shearController_open_cases G i j a m hunit
  exact ⟨a, b, v, hstep, hcases⟩

/-- Every opposite-score common play across an elementary shear has unit row
defect.  This depends only on its endpoint score contract, not on how the
interaction was selected.  Consequently there is no neutral alternative
common play while the same even/odd endpoint targets are retained. -/
theorem CrossGraphStrategyPlay.rowEvaluation_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (i j : V)
    (play : CrossGraphStrategyPlay G
      (elementaryCongruenceGraph G i j)
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
  have hone := graphEvaluation_elementaryCongruenceGraph_add
    G i j play.moment
  rw [hHeval, hGeval, add_zero] at hone
  exact hone.symm

/-- Every opposite-score common play across an elementary shear contains a
unit OPEN controller event on its source trace.  A proof by dummy commutation
must therefore alter one of these events while staying inside both strategy
trees; commuting arbitrary legal schedules is insufficient. -/
theorem CrossGraphStrategyPlay.exists_unit_shearController_open
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (i j : V)
    (play : CrossGraphStrategyPlay G
      (elementaryCongruenceGraph G i j)
      (initial (V := V)) (initial (V := V))) :
    ∃ (a b : State V) (v : V),
      step G a (.open v) = some b ∧
      ((v = j ∧ flip G ((liveSet a).erase j) i = 1) ∨
        (v ≠ j ∧ j ∈ (liveSet a).erase v ∧
          adjacencyBit G i v = 1)) := by
  exact play.traceG.exists_unit_shearController_open G i j
    (play.rowEvaluation_eq_one G i j)

/-! ## Exact dummy-preserving congruence reduction

The false unrestricted invariance above uses the dummy as the modified row.
The useful restricted statement forbids precisely that operation.  The next
definitions and theorems isolate the two independent obligations: ordinary
symplectic elimination on the real coordinates, and root-value transport.
The unit-defect results above show that ordinary complete-play interaction
cannot prove the latter by selecting a neutral common terminal trace.
-/

universe u

/-- An elementary alternating shear is an involution when its source and
target labels are distinct. -/
theorem elementaryCongruenceGraph_involutive
    {V : Type*} (G : SimpleGraph V) (i j : V) (hij : i ≠ j) :
    elementaryCongruenceGraph
        (elementaryCongruenceGraph G i j) i j = G := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp
  · by_cases hxj : x = j
    · subst x
      have hyj : y ≠ j := by exact fun h ↦ hxy h.symm
      by_cases hgjy : G.Adj j y <;> by_cases hgiy : G.Adj i y
      · have hiy : i ≠ y := G.ne_of_adj hgiy
        simp [elementaryCongruenceGraph, hxy, hyj, hij, hgjy, hgiy,
          hiy, Xor]
      · simp [elementaryCongruenceGraph, hxy, hyj, hij, hgjy, hgiy, Xor]
      · have hiy : i ≠ y := G.ne_of_adj hgiy
        simp [elementaryCongruenceGraph, hxy, hyj, hij, hgjy, hgiy,
          hiy, Xor]
      · simp [elementaryCongruenceGraph, hxy, hyj, hij, hgjy, hgiy, Xor]
    · by_cases hyj : y = j
      · subst y
        have hxj' : x ≠ j := hxj
        by_cases hgxj : G.Adj x j <;> by_cases hgix : G.Adj i x
        · have hix : i ≠ x := G.ne_of_adj hgix
          simp [elementaryCongruenceGraph, hxy, hij, hgxj, hgix,
            hix, Xor]
        · simp [elementaryCongruenceGraph, hxy, hij, hgxj, hgix,
            Xor]
        · have hix : i ≠ x := G.ne_of_adj hgix
          simp [elementaryCongruenceGraph, hxy, hij, hgxj, hgix,
            hix, Xor]
        · simp [elementaryCongruenceGraph, hxy, hij, hgxj, hgix,
            Xor]
      · simp [elementaryCongruenceGraph, hxy, hxj, hyj, Xor]

/-- A genuine shear preserves the adjacency between its own source and target
labels: the toggling entry would be the loop at the source, which is zero. -/
theorem elementaryCongruenceGraph_adj_source_target_iff
    {V : Type*} (G : SimpleGraph V) (i j : V) (hij : i ≠ j) :
    (elementaryCongruenceGraph G i j).Adj i j ↔ G.Adj i j := by
  have h := elementaryCongruenceGraph_adj_j_iff G i j i hij
  rw [(elementaryCongruenceGraph G i j).adj_comm]
  simpa [G.adj_comm, Xor] using h

/-- One exact cell of alternating Gaussian elimination.  If `j` is the
chosen mate of pivot `i` and `k` is another neighbour of `i`, shearing the
`j`-row into target row `k` clears `i-k`, preserves `i-j`, and preserves an
isolated dummy. -/
theorem dummyShear_clears_pivot_neighbor
    {V : Type*} {G : SimpleGraph V} {d i j k : V}
    (hd : IsDummy G d) (hij : G.Adj i j) (hik : G.Adj i k)
    (hjk : j ≠ k) :
    let H := elementaryCongruenceGraph G j k
    ¬H.Adj i k ∧ H.Adj i j ∧ IsDummy H d := by
  have hikNe : i ≠ k := G.ne_of_adj hik
  have hjiNe : j ≠ i := (G.ne_of_adj hij).symm
  have hdk : d ≠ k := by
    intro h
    subst k
    exact hd i hik.symm
  have hclear :
      ¬(elementaryCongruenceGraph G j k).Adj i k := by
    have htarget := elementaryCongruenceGraph_adj_j_iff G j k i hikNe
    rw [(elementaryCongruenceGraph G j k).adj_comm]
    rw [htarget]
    simp [G.adj_comm, hik, hij, Xor]
  have hpair : (elementaryCongruenceGraph G j k).Adj i j :=
    (elementaryCongruenceGraph_adj_away_iff G j k i j hikNe hjk).2 hij
  exact ⟨hclear, hpair, hd.elementaryCongruenceGraph j k hdk⟩

/-- A chain of elementary alternating congruences in which the modified row
is never the distinguished dummy row.  The source row may be arbitrary. -/
inductive DummyShearReachable {V : Type u} [DecidableEq V] (d : V) :
    SimpleGraph V → SimpleGraph V → Prop
  | refl (G : SimpleGraph V) : DummyShearReachable d G G
  | shear {G H : SimpleGraph V} (chain : DummyShearReachable d G H)
      (i j : V) (hij : i ≠ j) (hdj : d ≠ j) :
      DummyShearReachable d G (elementaryCongruenceGraph H i j)

/-- Every graph along a dummy-preserving shear chain retains its isolated
dummy. -/
theorem DummyShearReachable.isDummy {V : Type u} [DecidableEq V] {d : V}
    {G H : SimpleGraph V} (h : DummyShearReachable d G H)
    (hd : IsDummy G d) : IsDummy H d := by
  induction h with
  | refl => exact hd
  | shear chain i j hij hdj ih =>
      exact ih.elementaryCongruenceGraph i j hdj

theorem DummyShearReachable.trans {V : Type u} [DecidableEq V] {d : V}
    {G H K : SimpleGraph V} (hGH : DummyShearReachable d G H)
    (hHK : DummyShearReachable d H K) : DummyShearReachable d G K := by
  induction hHK with
  | refl => exact hGH
  | shear chain i j hij hdj ih =>
      exact .shear ih i j hij hdj

/-- Because every genuine shear is involutive, dummy-preserving shear
reachability is symmetric. -/
theorem DummyShearReachable.symm {V : Type u} [DecidableEq V] {d : V}
    {G H : SimpleGraph V} (h : DummyShearReachable d G H) :
    DummyShearReachable d H G := by
  induction h with
  | refl => exact .refl _
  | @shear L chain i j hij hdj ih =>
      have hback : DummyShearReachable d
          (elementaryCongruenceGraph L i j) L := by
        have hone : DummyShearReachable d
            (elementaryCongruenceGraph L i j)
            (elementaryCongruenceGraph
              (elementaryCongruenceGraph L i j) i j) :=
          .shear (.refl _) i j hij hdj
        simpa [elementaryCongruenceGraph_involutive L i j hij] using hone
      exact hback.trans ih

/-- Standard alternating-matrix elimination, stated in exactly the
coordinate-preserving form needed here: every graph with an isolated basis
coordinate is obtainable from a matching graph by shears which never modify
that coordinate. -/
def DummyShearNormalForm : Prop :=
  ∀ (V : Type u) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (d : V), IsDummy G d →
      ∃ M : SimpleGraph V,
        IsDummy M d ∧ IsMatchingGraph M ∧ DummyShearReachable d M G

/-- Root-level forward invariance under exactly one dummy-preserving
elementary congruence.  Full equivalence is unnecessary for the reduction:
the normal-form chain is oriented from a matching graph toward the target. -/
def DummyRootShearForward : Prop :=
  ∀ (V : Type u) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (d : V), IsDummy G d →
      ∀ (i j : V), i ≠ j → d ≠ j → ∀ seat : Bool,
        EvenWins G seat (initial (V := V)) →
          EvenWins (elementaryCongruenceGraph G i j) seat
            (initial (V := V))

/-- The genuinely sufficient root theorem only transports the `BothEven`
cold sheet.  It makes no claim about shears at controlled roots. -/
def DummyRootShearBothEvenForward : Prop :=
  ∀ (V : Type u) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (d : V), IsDummy G d →
      ∀ (i j : V), i ≠ j → d ≠ j →
        BothEven G (initial (V := V)) →
          BothEven (elementaryCongruenceGraph G i j)
            (initial (V := V))

/-- The empty-queue formulation specializes to root shear transport. -/
theorem dummyRootShearForward_of_emptyQueue
    (hempty : DummyEmptyQueueShearForward) :
    DummyRootShearForward.{0} := by
  intro V instF instD G d hd i j hij hdj seat heven
  have h := hempty V instF instD G d hd i j hij hdj
    (Finset.univ : Finset V) (by simp) false seat
  simpa [initial, emptyRoot] using h (by simpa [initial, emptyRoot] using heven)

/-- The cold-sheet empty-queue formulation specializes to the root. -/
theorem dummyRootShearBothEvenForward_of_emptyQueue
    (hempty : DummyEmptyQueueShearBothEvenForward) :
    DummyRootShearBothEvenForward.{0} := by
  intro V instF instD G d hd i j hij hdj hboth
  have h := hempty V instF instD G d hd i j hij hdj
    (Finset.univ : Finset V) (by simp) false
  simpa [initial, emptyRoot] using h (by simpa [initial, emptyRoot] using hboth)

/-- A forward root-shear theorem propagates an even strategy through any
finite dummy-preserving shear chain. -/
theorem evenWins_of_dummyShearReachable
    (hforward : DummyRootShearForward.{u})
    {V : Type u} [Fintype V] [DecidableEq V] {d : V}
    {G H : SimpleGraph V} (hd : IsDummy G d)
    (hreach : DummyShearReachable d G H) (seat : Bool)
    (heven : EvenWins G seat (initial (V := V))) :
    EvenWins H seat (initial (V := V)) := by
  induction hreach with
  | refl => exact heven
  | @shear L chain i j hij hdj ih =>
      have hdL : IsDummy L d := chain.isDummy hd
      exact hforward V inferInstance inferInstance L d hdL i j hij hdj seat ih

/-- Cold-sheet shear transport propagates through an arbitrary finite
dummy-preserving shear chain. -/
theorem bothEven_of_dummyShearReachable
    (hforward : DummyRootShearBothEvenForward.{u})
    {V : Type u} [Fintype V] [DecidableEq V] {d : V}
    {G H : SimpleGraph V} (hd : IsDummy G d)
    (hreach : DummyShearReachable d G H)
    (heven : BothEven G (initial (V := V))) :
    BothEven H (initial (V := V)) := by
  induction hreach with
  | refl => exact heven
  | @shear L chain i j hij hdj ih =>
      have hdL : IsDummy L d := chain.isDummy hd
      exact hforward V inferInstance inferInstance L d hdL i j hij hdj ih

/-- Alternating normal form plus preservation of only the `BothEven` root
sheet already implies FIFO in full; arbitrary one-seat shear transport is
stronger than necessary. -/
theorem fifoLinking_of_dummyShearNormalForm_and_rootShearBothEvenForward
    (hnormal : DummyShearNormalForm.{u})
    (hforward : DummyRootShearBothEvenForward.{u}) :
    FifoLinkingTheorem.{u} := by
  intro V instF instD G d hd seat
  obtain ⟨M, hdM, hmatching, hreach⟩ :=
    hnormal V instF instD G d hd
  have hbase : BothEven M (initial (V := V)) := ⟨
    evenWins_initial_of_matching hmatching (initial (V := V)).toMove,
    evenWins_initial_of_matching hmatching (!(initial (V := V)).toMove)⟩
  have hboth := bothEven_of_dummyShearReachable hforward hdM hreach hbase
  cases seat with
  | false => exact hboth.1
  | true => exact hboth.2

/-- Complete honest conditional reduction: real-coordinate symplectic
elimination plus root invariance under dummy-preserving shears implies the
arbitrary-graph isolated-dummy FIFO linking conjecture in its entirety. -/
theorem fifoLinking_of_dummyShearNormalForm_and_rootShearForward
    (hnormal : DummyShearNormalForm.{u})
    (hforward : DummyRootShearForward.{u}) :
    FifoLinkingTheorem.{u} := by
  intro V instF instD G d hd seat
  obtain ⟨M, hdM, hmatching, hreach⟩ :=
    hnormal V instF instD G d hd
  have hbase : EvenWins M seat (initial (V := V)) :=
    evenWins_initial_of_matching hmatching seat
  exact evenWins_of_dummyShearReachable hforward hdM hreach seat hbase

end

end Ogdoad.Fifo
