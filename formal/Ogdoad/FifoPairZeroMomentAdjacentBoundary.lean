import Ogdoad.FifoPairZeroMomentNormal

/-!
# A zero-moment pair whose odd strategy loses every queued pair

The same-degree, zero-second-moment pair condition is not universally safe
without the isolated-dummy root hypothesis.  On the five-vertex star, queue
two leaves.  They have the same full degree and zero second moment, but the
odd player closes the first leaf with unit charge.  The defender's legal
second CLOSE returns to score zero with an empty queue, inside the same exact
odd strategy.

Thus the strict zero descendant extracted in `FifoPairZeroMomentNormal`
cannot in general be required to retain some adjacent queued pair satisfying
the same two scalar conditions.  In this counterexample there is no queued
pair at all.  The result is an exact Bellman certificate, not a graph census.
-/

namespace Ogdoad.Fifo

noncomputable section

/-! ## The five-vertex star and a computable Bellman model -/

def zeroPairStarRel (x y : Fin 5) : Bool := decide (
  (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨
  (x = 0 ∧ y = 3) ∨ (x = 0 ∧ y = 4))

def zeroPairStarGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun x y ↦ zeroPairStarRel x y = true

def zeroPairStarAdj (x y : Fin 5) : Bool :=
  zeroPairStarRel x y || zeroPairStarRel y x

def zeroPairStarFlip (U : Finset (Fin 5)) (v : Fin 5) : ZMod 2 :=
  ((U.filter fun w ↦ zeroPairStarAdj v w = true).card : ZMod 2)

theorem zeroPairStarFlip_eq_flip (U : Finset (Fin 5)) (v : Fin 5) :
    zeroPairStarFlip U v = flip zeroPairStarGraph U v := by
  classical
  simp only [zeroPairStarFlip, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [zeroPairStarAdj, zeroPairStarRel, zeroPairStarGraph,
      SimpleGraph.fromRel_adj]

def zeroPairStarStep (s : State (Fin 5)) :
    Move (Fin 5) → Option (State (Fin 5))
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
              score := s.score + zeroPairStarFlip s.untouched f }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

theorem zeroPairStarStep_eq_step
    (s : State (Fin 5)) (m : Move (Fin 5)) :
    zeroPairStarStep s m = step zeroPairStarGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [zeroPairStarStep, step]
  | close =>
      cases q <;> cases ko <;> simp [zeroPairStarStep, step,
        zeroPairStarFlip_eq_flip]
  | pass => simp [zeroPairStarStep, step]

def zeroPairStarMoves : List (Move (Fin 5)) :=
  [.open 0, .open 1, .open 2, .open 3, .open 4, .close, .pass]

theorem mem_zeroPairStarMoves (m : Move (Fin 5)) :
    m ∈ zeroPairStarMoves := by
  cases m with
  | «open» v => fin_cases v <;> simp [zeroPairStarMoves]
  | close => simp [zeroPairStarMoves]
  | pass => simp [zeroPairStarMoves]

/-! ## The charged two-CLOSE branch -/

def zeroPairStarAfterFirstClose : State (Fin 5) where
  untouched := {0, 3, 4}
  queue := [2]
  ko := false
  toMove := true
  score := 1

def zeroPairStarAfterTwoCloses : State (Fin 5) where
  untouched := {0, 3, 4}
  queue := []
  ko := false
  toMove := false
  score := 0

theorem zeroPairStar_root_close :
    step zeroPairStarGraph
        (afterInitialTwoOpens (1 : Fin 5) 2) .close =
      some zeroPairStarAfterFirstClose := by
  norm_num [step, afterInitialTwoOpens, zeroPairStarAfterFirstClose,
    flip, zeroPairStarGraph, zeroPairStarRel, SimpleGraph.fromRel_adj]
  all_goals decide

theorem zeroPairStar_second_close :
    step zeroPairStarGraph zeroPairStarAfterFirstClose .close =
      some zeroPairStarAfterTwoCloses := by
  norm_num [step, zeroPairStarAfterFirstClose,
    zeroPairStarAfterTwoCloses, flip, zeroPairStarGraph,
    zeroPairStarRel, SimpleGraph.fromRel_adj]
  all_goals decide

def zeroPairStarAfterFirstWinner : Bool :=
  finiteEvenWinner zeroPairStarMoves zeroPairStarStep true
    (rank zeroPairStarAfterFirstClose + 1) zeroPairStarAfterFirstClose

theorem zeroPairStarAfterFirstWinner_value :
    zeroPairStarAfterFirstWinner = false := by
  decide

theorem zeroPairStar_afterFirst_oddWins :
    OddWins zeroPairStarGraph true zeroPairStarAfterFirstClose := by
  have hspec := finiteEvenWinner_spec zeroPairStarGraph
    zeroPairStarMoves mem_zeroPairStarMoves zeroPairStarStep
    zeroPairStarStep_eq_step true
    (rank zeroPairStarAfterFirstClose + 1) zeroPairStarAfterFirstClose
    (by omega)
  change if zeroPairStarAfterFirstWinner then
      EvenWins zeroPairStarGraph true zeroPairStarAfterFirstClose
    else OddWins zeroPairStarGraph true zeroPairStarAfterFirstClose at hspec
  rw [zeroPairStarAfterFirstWinner_value] at hspec
  exact hspec

/-- State after one of the three legal root OPEN alternatives. -/
def zeroPairStarAfterRootOpen (v : Fin 5) : State (Fin 5) where
  untouched := ((Finset.univ.erase 1).erase 2).erase v
  queue := [1, 2, v]
  ko := false
  toMove := true
  score := 0

theorem zeroPairStar_root_open (v : Fin 5)
    (hv : v ∈ ((Finset.univ.erase 1).erase 2 : Finset (Fin 5))) :
    step zeroPairStarGraph (afterInitialTwoOpens (1 : Fin 5) 2) (.open v) =
      some (zeroPairStarAfterRootOpen v) := by
  simp [step, afterInitialTwoOpens, zeroPairStarAfterRootOpen, hv]

def zeroPairStarAfterRootOpenWinner (v : Fin 5) : Bool :=
  finiteEvenWinner zeroPairStarMoves zeroPairStarStep true
    (rank (zeroPairStarAfterRootOpen v) + 1)
    (zeroPairStarAfterRootOpen v)

theorem zeroPairStarAfterRootOpenWinner_value (v : Fin 5)
    (hv : v ∈ ((Finset.univ.erase 1).erase 2 : Finset (Fin 5))) :
    zeroPairStarAfterRootOpenWinner v = true := by
  fin_cases v <;> simp at hv ⊢ <;> decide

theorem zeroPairStar_afterRootOpen_evenWins (v : Fin 5)
    (hv : v ∈ ((Finset.univ.erase 1).erase 2 : Finset (Fin 5))) :
    EvenWins zeroPairStarGraph true (zeroPairStarAfterRootOpen v) := by
  have hspec := finiteEvenWinner_spec zeroPairStarGraph
    zeroPairStarMoves mem_zeroPairStarMoves zeroPairStarStep
    zeroPairStarStep_eq_step true
    (rank (zeroPairStarAfterRootOpen v) + 1)
    (zeroPairStarAfterRootOpen v) (by omega)
  change if zeroPairStarAfterRootOpenWinner v then
      EvenWins zeroPairStarGraph true (zeroPairStarAfterRootOpen v)
    else OddWins zeroPairStarGraph true
      (zeroPairStarAfterRootOpen v) at hspec
  rw [zeroPairStarAfterRootOpenWinner_value v hv] at hspec
  exact hspec

theorem zeroPairStar_root_oddWins :
    OddWins zeroPairStarGraph true
      (afterInitialTwoOpens (1 : Fin 5) 2) := by
  exact OddWins.choose (afterInitialTwoOpens (1 : Fin 5) 2) (by decide)
    .close zeroPairStarAfterFirstClose zeroPairStar_root_close
    zeroPairStar_afterFirst_oddWins

/-- CLOSE is not merely one successful odd move.  Every exact odd strategy
at the q=0 root must select it: each of the three legal OPEN alternatives is
even-winning. -/
theorem zeroPairStarStrategy_selectedClose
    (strategy : OddStrategy zeroPairStarGraph true
      (afterInitialTwoOpens (1 : Fin 5) 2)) :
    strategy.selectedMove = some .close := by
  cases strategy with
  | terminal _ hterminal _ =>
      exact False.elim
        (terminal_no_step hterminal
          ⟨.close, zeroPairStarAfterFirstClose, zeroPairStar_root_close⟩)
  | answer _ hseat _ _ =>
      simp [afterInitialTwoOpens] at hseat
  | choose _ _ m t hstep child =>
      change some m = some (.close : Move (Fin 5))
      apply congrArg some
      cases m with
      | «open» v =>
          have hv : v ∈
              ((Finset.univ.erase 1).erase 2 : Finset (Fin 5)) := by
            simp only [step, afterInitialTwoOpens] at hstep
            split at hstep
            · assumption
            · contradiction
          have hcanonical := zeroPairStar_root_open v hv
          rw [hcanonical] at hstep
          have ht : t = zeroPairStarAfterRootOpen v :=
            Option.some.inj hstep.symm
          subst t
          exact False.elim
            ((zeroPairStar_afterRootOpen_evenWins v hv).not_oddWins
              child.toOddWins)
      | close => rfl
      | pass => simp [step, afterInitialTwoOpens] at hstep

/-! ## Failure of universal q=0 pair safety -/

theorem zeroPairStar_root_data :
    (2 : Fin 5) ∈
        sameDegreeMates zeroPairStarGraph Finset.univ 1 ∧
      pairSecondMoment zeroPairStarGraph Finset.univ 1 2 = 0 := by
  constructor
  · norm_num [sameDegreeMates, flip, zeroPairStarGraph,
      zeroPairStarRel, SimpleGraph.fromRel_adj]
    all_goals decide
  · norm_num [pairSecondMoment, neighborDegreeBit, flip, adjacencyBit,
      zeroPairStarGraph, zeroPairStarRel, SimpleGraph.fromRel_adj]
    all_goals decide

theorem zeroPairStar_not_evenWins :
    ¬EvenWins zeroPairStarGraph true
      (afterInitialTwoOpens (1 : Fin 5) 2) :=
  (oddWins_iff_not_evenWins zeroPairStarGraph true _).mp
    zeroPairStar_root_oddWins

theorem zeroPairStar_not_zeroMomentPairSafe :
    ¬ZeroMomentPairSafeAt zeroPairStarGraph := by
  intro hsafe
  exact zeroPairStar_not_evenWins
    (hsafe true 1 2 zeroPairStar_root_data.1 zeroPairStar_root_data.2)

/-- The still-relevant restricted assertion: q=0 pair safety only on graphs
which actually carry an isolated dummy.  The five-vertex star below refutes
`ZeroMomentPairSafeAt`, but cannot refute this implication. -/
def IsolatedZeroMomentPairSafeAt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∀ d, IsDummy G d → ZeroMomentPairSafeAt G

theorem zeroPairStar_no_isolatedDummy (d : Fin 5) :
    ¬IsDummy zeroPairStarGraph d := by
  intro hd
  fin_cases d
  · have h := hd 1
    simp [zeroPairStarGraph, zeroPairStarRel,
      SimpleGraph.fromRel_adj] at h
  · have h := hd 0
    simp [zeroPairStarGraph, zeroPairStarRel,
      SimpleGraph.fromRel_adj] at h
  · have h := hd 0
    simp [zeroPairStarGraph, zeroPairStarRel,
      SimpleGraph.fromRel_adj] at h
  · have h := hd 0
    simp [zeroPairStarGraph, zeroPairStarRel,
      SimpleGraph.fromRel_adj] at h
  · have h := hd 0
    simp [zeroPairStarGraph, zeroPairStarRel,
      SimpleGraph.fromRel_adj] at h

theorem zeroPairStar_isolatedZeroMomentPairSafe :
    IsolatedZeroMomentPairSafeAt zeroPairStarGraph := by
  intro d hd
  exact False.elim (zeroPairStar_no_isolatedDummy d hd)

/-! ## Exact loss of every adjacent queue pair -/

/-- A pair of consecutive queue cells which, after adjoining just those two
cells to the current untouched residual carrier, is same-degree and has zero
second moment. -/
def HasAdjacentCurrentZeroMomentPair
    (G : SimpleGraph (Fin 5)) (s : State (Fin 5)) : Prop :=
  ∃ pre x y post,
    s.queue = pre ++ x :: y :: post ∧
      y ∈ sameDegreeMates G (insert x (insert y s.untouched)) x ∧
      pairSecondMoment G (insert x (insert y s.untouched)) x y = 0

theorem zeroPairStarAfterTwoCloses_no_adjacent_zeroMomentPair :
    ¬HasAdjacentCurrentZeroMomentPair zeroPairStarGraph
      zeroPairStarAfterTwoCloses := by
  rintro ⟨pre, x, y, post, hqueue, _hpair⟩
  simp [zeroPairStarAfterTwoCloses] at hqueue

/-- Choose one exact data-valued strategy whose first move is the charged
CLOSE certified above. -/
noncomputable def zeroPairStarAfterFirstStrategy :
    OddStrategy zeroPairStarGraph true zeroPairStarAfterFirstClose :=
  Classical.choice zeroPairStar_afterFirst_oddWins.nonempty_oddStrategy

noncomputable def zeroPairStarRootStrategy :
    OddStrategy zeroPairStarGraph true
      (afterInitialTwoOpens (1 : Fin 5) 2) :=
  OddStrategy.choose (afterInitialTwoOpens (1 : Fin 5) 2) (by decide)
    .close zeroPairStarAfterFirstClose zeroPairStar_root_close
    zeroPairStarAfterFirstStrategy

/-- The defender-controlled first-CLOSE child contains its legal second
CLOSE, independently of which exact odd continuation was chosen. -/
theorem zeroPairStarAfterFirstStrategy_has_secondClose :
    ∃ desc : OddStrategy zeroPairStarGraph true
        zeroPairStarAfterTwoCloses,
      StrategyNode zeroPairStarGraph true
        zeroPairStarAfterFirstStrategy desc := by
  let strategy := zeroPairStarAfterFirstStrategy
  change ∃ desc : OddStrategy zeroPairStarGraph true
      zeroPairStarAfterTwoCloses,
    StrategyNode zeroPairStarGraph true strategy desc
  cases strategy with
  | terminal _ hterminal _ =>
      exact False.elim
        (terminal_no_step hterminal
          ⟨.close, zeroPairStarAfterTwoCloses,
            zeroPairStar_second_close⟩)
  | choose _ hseat _ _ _ _ =>
      exact False.elim (hseat rfl)
  | answer _ _ _ children =>
      let desc := children .close zeroPairStarAfterTwoCloses
        zeroPairStar_second_close
      exact ⟨desc, StrategyNode.answer (StrategyNode.root desc)⟩

/-- The actual q=0 odd strategy has a strict score-zero descendant with empty
queue, hence with no adjacent pair on which an infinite descent could recur.
-/
theorem zeroPairStar_strategy_loses_adjacent_pair :
    ∃ desc : OddStrategy zeroPairStarGraph true
        zeroPairStarAfterTwoCloses,
      StrategyNode zeroPairStarGraph true zeroPairStarRootStrategy desc ∧
        rank zeroPairStarAfterTwoCloses <
          rank (afterInitialTwoOpens (1 : Fin 5) 2) ∧
        zeroPairStarAfterTwoCloses.score = 0 ∧
        ¬HasAdjacentCurrentZeroMomentPair zeroPairStarGraph
          zeroPairStarAfterTwoCloses := by
  obtain ⟨desc, hchild⟩ :=
    zeroPairStarAfterFirstStrategy_has_secondClose
  refine ⟨desc, ?_, ?_, rfl,
    zeroPairStarAfterTwoCloses_no_adjacent_zeroMomentPair⟩
  · exact StrategyNode.choose hchild
  · exact lt_trans (rank_step_lt zeroPairStar_second_close)
      (rank_step_lt zeroPairStar_root_close)

/-- Complete exact obstruction: the five-vertex star has a same-degree q=0
initial pair and an odd strategy whose strict zero descendant has no current
FIFO pair at all. -/
theorem zeroPairStar_adjacent_descent_counterexample :
    (2 : Fin 5) ∈
        sameDegreeMates zeroPairStarGraph Finset.univ 1 ∧
      pairSecondMoment zeroPairStarGraph Finset.univ 1 2 = 0 ∧
      ∃ desc : OddStrategy zeroPairStarGraph true
          zeroPairStarAfterTwoCloses,
        StrategyNode zeroPairStarGraph true zeroPairStarRootStrategy desc ∧
          rank zeroPairStarAfterTwoCloses <
            rank (afterInitialTwoOpens (1 : Fin 5) 2) ∧
          zeroPairStarAfterTwoCloses.score = 0 ∧
          ¬HasAdjacentCurrentZeroMomentPair zeroPairStarGraph
            zeroPairStarAfterTwoCloses := by
  exact ⟨zeroPairStar_root_data.1, zeroPairStar_root_data.2,
    zeroPairStar_strategy_loses_adjacent_pair⟩

/-! ## The same star after adjoining one isolated dummy -/

/-- `K₁,₄` on labels `0,…,4`, with label `5` isolated. -/
def zeroPairDummyStarRel (x y : Fin 6) : Bool := decide (
  (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨
  (x = 0 ∧ y = 3) ∨ (x = 0 ∧ y = 4))

def zeroPairDummyStarGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun x y ↦ zeroPairDummyStarRel x y = true

def zeroPairDummyStarAdj (x y : Fin 6) : Bool :=
  zeroPairDummyStarRel x y || zeroPairDummyStarRel y x

def zeroPairDummyStarFlip (U : Finset (Fin 6)) (v : Fin 6) : ZMod 2 :=
  ((U.filter fun w ↦ zeroPairDummyStarAdj v w = true).card : ZMod 2)

theorem zeroPairDummyStarFlip_eq_flip (U : Finset (Fin 6)) (v : Fin 6) :
    zeroPairDummyStarFlip U v = flip zeroPairDummyStarGraph U v := by
  classical
  simp only [zeroPairDummyStarFlip, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [zeroPairDummyStarAdj, zeroPairDummyStarRel,
      zeroPairDummyStarGraph, SimpleGraph.fromRel_adj]

def zeroPairDummyStarStep (s : State (Fin 6)) :
    Move (Fin 6) → Option (State (Fin 6))
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
              score := s.score + zeroPairDummyStarFlip s.untouched f }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

theorem zeroPairDummyStarStep_eq_step
    (s : State (Fin 6)) (m : Move (Fin 6)) :
    zeroPairDummyStarStep s m = step zeroPairDummyStarGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [zeroPairDummyStarStep, step]
  | close =>
      cases q <;> cases ko <;> simp [zeroPairDummyStarStep, step,
        zeroPairDummyStarFlip_eq_flip]
  | pass => simp [zeroPairDummyStarStep, step]

def zeroPairDummyStarMoves : List (Move (Fin 6)) :=
  [.open 0, .open 1, .open 2, .open 3, .open 4, .open 5, .close, .pass]

theorem mem_zeroPairDummyStarMoves (m : Move (Fin 6)) :
    m ∈ zeroPairDummyStarMoves := by
  cases m with
  | «open» v => fin_cases v <;> simp [zeroPairDummyStarMoves]
  | close => simp [zeroPairDummyStarMoves]
  | pass => simp [zeroPairDummyStarMoves]

theorem zeroPairDummyStar_dummy :
    IsDummy zeroPairDummyStarGraph 5 := by
  intro v
  fin_cases v <;>
    simp [zeroPairDummyStarGraph, zeroPairDummyStarRel,
      SimpleGraph.fromRel_adj]

theorem zeroPairDummyStar_root_data :
    (2 : Fin 6) ∈
        sameDegreeMates zeroPairDummyStarGraph Finset.univ 1 ∧
      pairSecondMoment zeroPairDummyStarGraph Finset.univ 1 2 = 0 := by
  constructor
  · norm_num [sameDegreeMates, flip, zeroPairDummyStarGraph,
      zeroPairDummyStarRel, SimpleGraph.fromRel_adj]
    all_goals decide
  · norm_num [pairSecondMoment, neighborDegreeBit, flip, adjacencyBit,
      zeroPairDummyStarGraph, zeroPairDummyStarRel,
      SimpleGraph.fromRel_adj]
    all_goals decide

def zeroPairDummyStarPairWinner : Bool :=
  finiteEvenWinner zeroPairDummyStarMoves zeroPairDummyStarStep true
    (rank (afterInitialTwoOpens (1 : Fin 6) 2) + 1)
    (afterInitialTwoOpens (1 : Fin 6) 2)

set_option maxHeartbeats 2000000 in
theorem zeroPairDummyStarPairWinner_value :
    zeroPairDummyStarPairWinner = true := by
  decide

set_option maxHeartbeats 2000000 in
/-- The exact unrestricted Bellman result reverses after adjoining the
isolated dummy: the same displayed leaf pair is now even-winning. -/
theorem zeroPairDummyStar_pair_evenWins :
    EvenWins zeroPairDummyStarGraph true
      (afterInitialTwoOpens (1 : Fin 6) 2) := by
  have hspec := finiteEvenWinner_spec zeroPairDummyStarGraph
    zeroPairDummyStarMoves mem_zeroPairDummyStarMoves
    zeroPairDummyStarStep zeroPairDummyStarStep_eq_step true
    (rank (afterInitialTwoOpens (1 : Fin 6) 2) + 1)
    (afterInitialTwoOpens (1 : Fin 6) 2) (by omega)
  change if zeroPairDummyStarPairWinner then
      EvenWins zeroPairDummyStarGraph true
        (afterInitialTwoOpens (1 : Fin 6) 2)
    else OddWins zeroPairDummyStarGraph true
      (afterInitialTwoOpens (1 : Fin 6) 2) at hspec
  rw [zeroPairDummyStarPairWinner_value] at hspec
  exact hspec

/-- This one-edge-family test supports, but does not prove, the isolated
variant: the unrestricted counterexample disappears when a dummy is added.
-/
theorem zeroPairDummyStar_selected_pair_safe :
    IsDummy zeroPairDummyStarGraph 5 ∧
      (2 : Fin 6) ∈
        sameDegreeMates zeroPairDummyStarGraph Finset.univ 1 ∧
      pairSecondMoment zeroPairDummyStarGraph Finset.univ 1 2 = 0 ∧
      EvenWins zeroPairDummyStarGraph true
        (afterInitialTwoOpens (1 : Fin 6) 2) := by
  exact ⟨zeroPairDummyStar_dummy, zeroPairDummyStar_root_data.1,
    zeroPairDummyStar_root_data.2, zeroPairDummyStar_pair_evenWins⟩

/-! ## Symbolic first-response policy -/

def zeroPairDummyStarAfterOpenZeroClose : State (Fin 6) where
  untouched := {3, 4, 5}
  queue := [2, 0]
  ko := false
  toMove := false
  score := 0

def zeroPairDummyStarAfterOpenThreeZero : State (Fin 6) where
  untouched := {4, 5}
  queue := [1, 2, 3, 0]
  ko := false
  toMove := false
  score := 0

def zeroPairDummyStarAfterOpenFourZero : State (Fin 6) where
  untouched := {3, 5}
  queue := [1, 2, 4, 0]
  ko := false
  toMove := false
  score := 0

def zeroPairDummyStarAfterOpenDummyZero : State (Fin 6) where
  untouched := {3, 4}
  queue := [1, 2, 5, 0]
  ko := false
  toMove := false
  score := 0

def zeroPairDummyStarAfterTwoCloses : State (Fin 6) where
  untouched := {0, 3, 4, 5}
  queue := []
  ko := false
  toMove := false
  score := 0

/-- The local pair-mode predicate suggested by the exact response table: the
queue begins with a same-degree q=0 pair on the current residual carrier. -/
def HasFrontCurrentZeroMomentPair {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : State V) : Prop :=
  ∃ x y tail,
    s.queue = x :: y :: tail ∧
      y ∈ sameDegreeMates G (insert x (insert y s.untouched)) x ∧
      pairSecondMoment G (insert x (insert y s.untouched)) x y = 0

def zeroPairDummyStarRunMoves :
    State (Fin 6) → List (Move (Fin 6)) → Option (State (Fin 6))
  | s, [] => some s
  | s, m :: ms =>
      (zeroPairDummyStarStep s m).bind fun t ↦
        zeroPairDummyStarRunMoves t ms

/-- One explicit winning reply word for each possible attacker move from
`[1,2]`: after `OPEN 0`, close `1`; after `OPEN 3`, `OPEN 4`, or dummy
`OPEN 5`, open `0`; after `CLOSE 1`, close `2`. -/
theorem zeroPairDummyStar_symbolic_response_runs :
    zeroPairDummyStarRunMoves
        (afterInitialTwoOpens (1 : Fin 6) 2) [.open 0, .close] =
        some zeroPairDummyStarAfterOpenZeroClose ∧
      zeroPairDummyStarRunMoves
        (afterInitialTwoOpens (1 : Fin 6) 2) [.open 3, .open 0] =
        some zeroPairDummyStarAfterOpenThreeZero ∧
      zeroPairDummyStarRunMoves
        (afterInitialTwoOpens (1 : Fin 6) 2) [.open 4, .open 0] =
        some zeroPairDummyStarAfterOpenFourZero ∧
      zeroPairDummyStarRunMoves
        (afterInitialTwoOpens (1 : Fin 6) 2) [.open 5, .open 0] =
        some zeroPairDummyStarAfterOpenDummyZero ∧
      zeroPairDummyStarRunMoves
        (afterInitialTwoOpens (1 : Fin 6) 2) [.close, .close] =
        some zeroPairDummyStarAfterTwoCloses := by
  decide

private theorem zeroPairDummyStar_evenWins_of_finiteWinner
    (s : State (Fin 6))
    (h : finiteEvenWinner zeroPairDummyStarMoves zeroPairDummyStarStep true
        (rank s + 1) s = true) :
    EvenWins zeroPairDummyStarGraph true s := by
  have hspec := finiteEvenWinner_spec zeroPairDummyStarGraph
    zeroPairDummyStarMoves mem_zeroPairDummyStarMoves
    zeroPairDummyStarStep zeroPairDummyStarStep_eq_step true
    (rank s + 1) s (by omega)
  rw [h] at hspec
  exact hspec

set_option maxHeartbeats 2000000 in
/-- Every displayed two-ply endpoint is even-winning.  This theorem checks
that the response table is a genuine first layer of a full Bellman policy,
not merely a list of legal neutral moves. -/
theorem zeroPairDummyStar_symbolic_response_endpoints_evenWins :
    EvenWins zeroPairDummyStarGraph true
        zeroPairDummyStarAfterOpenZeroClose ∧
      EvenWins zeroPairDummyStarGraph true
        zeroPairDummyStarAfterOpenThreeZero ∧
      EvenWins zeroPairDummyStarGraph true
        zeroPairDummyStarAfterOpenFourZero ∧
      EvenWins zeroPairDummyStarGraph true
        zeroPairDummyStarAfterOpenDummyZero ∧
      EvenWins zeroPairDummyStarGraph true
        zeroPairDummyStarAfterTwoCloses := by
  constructor
  · apply zeroPairDummyStar_evenWins_of_finiteWinner
    decide
  constructor
  · apply zeroPairDummyStar_evenWins_of_finiteWinner
    decide
  constructor
  · apply zeroPairDummyStar_evenWins_of_finiteWinner
    decide
  constructor
  · apply zeroPairDummyStar_evenWins_of_finiteWinner
    decide
  · apply zeroPairDummyStar_evenWins_of_finiteWinner
    decide

/-- Each OPEN response returns to pair mode, whereas the two-CLOSE response
enters empty-root mode.  This is the exact finite shape behind the possible
two-state induction; no closure theorem for arbitrary graphs is asserted. -/
theorem zeroPairDummyStar_response_modes :
    HasFrontCurrentZeroMomentPair zeroPairDummyStarGraph
        zeroPairDummyStarAfterOpenZeroClose ∧
      HasFrontCurrentZeroMomentPair zeroPairDummyStarGraph
        zeroPairDummyStarAfterOpenThreeZero ∧
      HasFrontCurrentZeroMomentPair zeroPairDummyStarGraph
        zeroPairDummyStarAfterOpenFourZero ∧
      HasFrontCurrentZeroMomentPair zeroPairDummyStarGraph
        zeroPairDummyStarAfterOpenDummyZero ∧
      zeroPairDummyStarAfterTwoCloses.queue = [] := by
  constructor
  · refine ⟨2, 0, [], rfl, ?_, ?_⟩
    · norm_num [sameDegreeMates, zeroPairDummyStarAfterOpenZeroClose,
        flip, zeroPairDummyStarGraph, zeroPairDummyStarRel,
        SimpleGraph.fromRel_adj]
      all_goals decide
    · norm_num [pairSecondMoment, neighborDegreeBit,
        zeroPairDummyStarAfterOpenZeroClose, flip, adjacencyBit,
        zeroPairDummyStarGraph, zeroPairDummyStarRel,
        SimpleGraph.fromRel_adj]
      all_goals decide
  constructor
  · refine ⟨1, 2, [3, 0], rfl, ?_, ?_⟩
    · norm_num [sameDegreeMates, zeroPairDummyStarAfterOpenThreeZero,
        flip, zeroPairDummyStarGraph, zeroPairDummyStarRel,
        SimpleGraph.fromRel_adj]
      all_goals decide
    · norm_num [pairSecondMoment, neighborDegreeBit,
        zeroPairDummyStarAfterOpenThreeZero, flip, adjacencyBit,
        zeroPairDummyStarGraph, zeroPairDummyStarRel,
        SimpleGraph.fromRel_adj]
      all_goals decide
  constructor
  · refine ⟨1, 2, [4, 0], rfl, ?_, ?_⟩
    · norm_num [sameDegreeMates, zeroPairDummyStarAfterOpenFourZero,
        flip, zeroPairDummyStarGraph, zeroPairDummyStarRel,
        SimpleGraph.fromRel_adj]
      all_goals decide
    · norm_num [pairSecondMoment, neighborDegreeBit,
        zeroPairDummyStarAfterOpenFourZero, flip, adjacencyBit,
        zeroPairDummyStarGraph, zeroPairDummyStarRel,
        SimpleGraph.fromRel_adj]
      all_goals decide
  constructor
  · refine ⟨1, 2, [5, 0], rfl, ?_, ?_⟩
    · norm_num [sameDegreeMates, zeroPairDummyStarAfterOpenDummyZero,
        flip, zeroPairDummyStarGraph, zeroPairDummyStarRel,
        SimpleGraph.fromRel_adj]
      all_goals decide
    · norm_num [pairSecondMoment, neighborDegreeBit,
        zeroPairDummyStarAfterOpenDummyZero, flip, adjacencyBit,
        zeroPairDummyStarGraph, zeroPairDummyStarRel,
        SimpleGraph.fromRel_adj]
      all_goals decide
  · rfl

/-- The dummy makes the two-CLOSE branch even-winning by leaving an even
four-vertex residual root containing the dummy.  On the star without the
dummy, the same word leaves an odd three-vertex residual root and is
odd-winning. -/
theorem zeroPairStar_dummy_repairs_close_branch :
    zeroPairStarAfterTwoCloses.untouched.card = 3 ∧
      zeroPairDummyStarAfterTwoCloses.untouched.card = 4 ∧
      zeroPairStarAfterTwoCloses.queue = [] ∧
      zeroPairDummyStarAfterTwoCloses.queue = [] ∧
      OddWins zeroPairStarGraph true zeroPairStarAfterTwoCloses ∧
      EvenWins zeroPairDummyStarGraph true
        zeroPairDummyStarAfterTwoCloses := by
  have hsmall : OddWins zeroPairStarGraph true
      zeroPairStarAfterTwoCloses := by
    exact zeroPairStar_afterFirst_oddWins.answer_child rfl
      zeroPairStar_second_close
  exact ⟨by decide, by decide, rfl, rfl, hsmall,
    zeroPairDummyStar_symbolic_response_endpoints_evenWins.2.2.2.2⟩

end

end Ogdoad.Fifo
