import Ogdoad.FifoCellSwapOutcomeBoundary
import Ogdoad.FifoParityCounterNormal

/-!
# The common-dummy policy-event boundary

A common attacker choice `OPEN d` in two score-coupled policies is a genuine
controlled descent, but it is not locally contradictory.  This file pins the
smallest one-step ancestry pattern found by exact search.  On a seven-label
graph with two isolated vertices, a nonmover-controlled defender state has
two mover-controlled isolated-OPEN children.  At either child, exact
score-coupled odd policies can select the other isolate in common and descend
to a nonmover-controlled state.

Thus even retaining the immediate universal sibling does not exclude common
dummy consumption.  The missing datum is policy selection at that sibling:
outcome classes and public ancestry alone say only that the sibling is
mover-controlled, not which move either exact attacker policy selects there.
This is a route countermodel, not a counterexample to the initial FIFO
linking conjecture; its displayed parent is reached from a both-even root.
-/

namespace Ogdoad.Fifo

noncomputable section

def commonDummyRel (x y : Fin 7) : Bool := decide (
    (x = 0 ∧ y = 2) ∨ (x = 0 ∧ y = 3) ∨ (x = 0 ∧ y = 4) ∨
    (x = 1 ∧ y = 2) ∨ (x = 1 ∧ y = 3))

def commonDummyGraph : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel fun x y ↦ commonDummyRel x y = true

def commonDummyAdj (x y : Fin 7) : Bool :=
  commonDummyRel x y || commonDummyRel y x

def commonDummyFlip (U : Finset (Fin 7)) (v : Fin 7) : ZMod 2 :=
  ((U.filter fun w ↦ commonDummyAdj v w = true).card : ZMod 2)

theorem commonDummyFlip_eq_flip (U : Finset (Fin 7)) (v : Fin 7) :
    commonDummyFlip U v = flip commonDummyGraph U v := by
  classical
  simp only [commonDummyFlip, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [commonDummyAdj, commonDummyRel, commonDummyGraph,
      SimpleGraph.fromRel_adj]

def commonDummyStep (s : State (Fin 7)) :
    Move (Fin 7) → Option (State (Fin 7))
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
              score := s.score + commonDummyFlip s.untouched f }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

theorem commonDummyStep_eq_step (s : State (Fin 7)) (m : Move (Fin 7)) :
    commonDummyStep s m = step commonDummyGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [commonDummyStep, step]
  | close =>
      cases q <;> cases ko <;> simp [commonDummyStep, step,
        commonDummyFlip_eq_flip]
  | pass => simp [commonDummyStep, step]

def commonDummyParent : State (Fin 7) where
  untouched := {0, 1, 5, 6}
  queue := [2, 4, 3]
  ko := false
  toMove := true
  score := 0

def commonDummyLeft : State (Fin 7) where
  untouched := {0, 1, 6}
  queue := [2, 4, 3, 5]
  ko := false
  toMove := false
  score := 0

def commonDummySibling : State (Fin 7) where
  untouched := {0, 1, 5}
  queue := [2, 4, 3, 6]
  ko := false
  toMove := false
  score := 0

def commonDummyLeftChild : State (Fin 7) where
  untouched := {0, 1}
  queue := [2, 4, 3, 5, 6]
  ko := false
  toMove := true
  score := 0

def commonDummySiblingChild : State (Fin 7) where
  untouched := {0, 1}
  queue := [2, 4, 3, 6, 5]
  ko := false
  toMove := true
  score := 0

def commonDummyMoves : List (Move (Fin 7)) :=
  [.open 0, .open 1, .open 2, .open 3, .open 4, .open 5, .open 6,
    .close, .pass]

theorem mem_commonDummyMoves (m : Move (Fin 7)) :
    m ∈ commonDummyMoves := by
  cases m with
  | «open» v => fin_cases v <;> simp [commonDummyMoves]
  | close => simp [commonDummyMoves]
  | pass => simp [commonDummyMoves]

def commonDummyWinner (seat : Bool) (s : State (Fin 7)) : Bool :=
  finiteEvenWinner commonDummyMoves commonDummyStep seat (rank s + 1) s

theorem commonDummyWinner_spec (seat : Bool) (s : State (Fin 7)) :
    if commonDummyWinner seat s then EvenWins commonDummyGraph seat s
    else OddWins commonDummyGraph seat s := by
  apply finiteEvenWinner_spec commonDummyGraph commonDummyMoves
    mem_commonDummyMoves commonDummyStep commonDummyStep_eq_step seat
    (rank s + 1) s
  omega

theorem commonDummyParent_true_loses :
    commonDummyWinner true commonDummyParent = false := by decide

theorem commonDummyParent_false_wins :
    commonDummyWinner false commonDummyParent = true := by decide

theorem commonDummyLeft_false_wins :
    commonDummyWinner false commonDummyLeft = true := by decide

theorem commonDummyLeft_true_loses :
    commonDummyWinner true commonDummyLeft = false := by decide

theorem commonDummySibling_false_wins :
    commonDummyWinner false commonDummySibling = true := by decide

theorem commonDummySibling_true_loses :
    commonDummyWinner true commonDummySibling = false := by decide

theorem commonDummyLeftChild_true_loses :
    commonDummyWinner true commonDummyLeftChild = false := by decide

theorem commonDummyLeftChild_false_wins :
    commonDummyWinner false commonDummyLeftChild = true := by decide

theorem commonDummySiblingChild_true_loses :
    commonDummyWinner true commonDummySiblingChild = false := by decide

theorem commonDummySiblingChild_false_wins :
    commonDummyWinner false commonDummySiblingChild = true := by decide

private theorem even_of_winner_true (seat : Bool) (s : State (Fin 7))
    (h : commonDummyWinner seat s = true) :
    EvenWins commonDummyGraph seat s := by
  have hs := commonDummyWinner_spec seat s
  rw [h] at hs
  exact hs

private theorem odd_of_winner_false (seat : Bool) (s : State (Fin 7))
    (h : commonDummyWinner seat s = false) :
    OddWins commonDummyGraph seat s := by
  have hs := commonDummyWinner_spec seat s
  rw [h] at hs
  exact hs

theorem commonDummyParent_nonmoverControlled :
    NonmoverControlled commonDummyGraph commonDummyParent := by
  have hodd := odd_of_winner_false true commonDummyParent
    commonDummyParent_true_loses
  have hnot := (oddWins_iff_not_evenWins commonDummyGraph true
    commonDummyParent).mp hodd
  have heven := even_of_winner_true false commonDummyParent
    commonDummyParent_false_wins
  exact ⟨by simpa [MoverEvenWins, commonDummyParent] using hnot,
    by simpa [NonmoverEvenWins, commonDummyParent] using heven⟩

theorem commonDummyLeft_moverControlled :
    MoverControlled commonDummyGraph commonDummyLeft := by
  have heven := even_of_winner_true false commonDummyLeft
    commonDummyLeft_false_wins
  have hodd := odd_of_winner_false true commonDummyLeft
    commonDummyLeft_true_loses
  have hnot := (oddWins_iff_not_evenWins commonDummyGraph true
    commonDummyLeft).mp hodd
  exact ⟨by simpa [MoverEvenWins, commonDummyLeft] using heven,
    by simpa [NonmoverEvenWins, commonDummyLeft] using hnot⟩

theorem commonDummySibling_moverControlled :
    MoverControlled commonDummyGraph commonDummySibling := by
  have heven := even_of_winner_true false commonDummySibling
    commonDummySibling_false_wins
  have hodd := odd_of_winner_false true commonDummySibling
    commonDummySibling_true_loses
  have hnot := (oddWins_iff_not_evenWins commonDummyGraph true
    commonDummySibling).mp hodd
  exact ⟨by simpa [MoverEvenWins, commonDummySibling] using heven,
    by simpa [NonmoverEvenWins, commonDummySibling] using hnot⟩

theorem commonDummyLeftChild_nonmoverControlled :
    NonmoverControlled commonDummyGraph commonDummyLeftChild := by
  have hodd := odd_of_winner_false true commonDummyLeftChild
    commonDummyLeftChild_true_loses
  have hnot := (oddWins_iff_not_evenWins commonDummyGraph true
    commonDummyLeftChild).mp hodd
  have heven := even_of_winner_true false commonDummyLeftChild
    commonDummyLeftChild_false_wins
  exact ⟨by simpa [MoverEvenWins, commonDummyLeftChild] using hnot,
    by simpa [NonmoverEvenWins, commonDummyLeftChild] using heven⟩

theorem commonDummySiblingChild_nonmoverControlled :
    NonmoverControlled commonDummyGraph commonDummySiblingChild := by
  have hodd := odd_of_winner_false true commonDummySiblingChild
    commonDummySiblingChild_true_loses
  have hnot := (oddWins_iff_not_evenWins commonDummyGraph true
    commonDummySiblingChild).mp hodd
  have heven := even_of_winner_true false commonDummySiblingChild
    commonDummySiblingChild_false_wins
  exact ⟨by simpa [MoverEvenWins, commonDummySiblingChild] using hnot,
    by simpa [NonmoverEvenWins, commonDummySiblingChild] using heven⟩

theorem commonDummyGraph_dummyFive : IsDummy commonDummyGraph 5 := by
  intro v
  fin_cases v <;>
    simp [commonDummyGraph, commonDummyRel, SimpleGraph.fromRel_adj]

theorem commonDummyGraph_dummySix : IsDummy commonDummyGraph 6 := by
  intro v
  fin_cases v <;>
    simp [commonDummyGraph, commonDummyRel, SimpleGraph.fromRel_adj]

theorem commonDummyParent_openFive :
    step commonDummyGraph commonDummyParent (.open 5) =
      some commonDummyLeft := by
  simp [step, commonDummyParent, commonDummyLeft]
  ext x
  fin_cases x <;> simp

theorem commonDummyParent_openSix :
    step commonDummyGraph commonDummyParent (.open 6) =
      some commonDummySibling := by
  simp [step, commonDummyParent, commonDummySibling]
  ext x
  fin_cases x <;> simp

theorem commonDummyParent_queueTurnParity : QueueTurnParity commonDummyParent := by
  norm_num [QueueTurnParity, commonDummyParent]

theorem commonDummyLeft_queueTurnParity : QueueTurnParity commonDummyLeft := by
  norm_num [QueueTurnParity, commonDummyLeft]

theorem commonDummyLeftChild_queueTurnParity :
    QueueTurnParity commonDummyLeftChild := by
  norm_num [QueueTurnParity, commonDummyLeftChild]

theorem commonDummyParent_liveSet_card_odd :
    Odd (liveSet commonDummyParent).card := by
  change Odd ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)).card
  native_decide

theorem commonDummyLeft_liveSet_card_odd :
    Odd (liveSet commonDummyLeft).card := by
  change Odd ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)).card
  native_decide

theorem commonDummyLeftChild_liveSet_card_odd :
    Odd (liveSet commonDummyLeftChild).card := by
  change Odd ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)).card
  native_decide

theorem commonDummyLeft_openSix :
    step commonDummyGraph commonDummyLeft (.open 6) =
      some commonDummyLeftChild := by
  simp [step, commonDummyLeft, commonDummyLeftChild]
  ext x
  fin_cases x <;> simp

theorem commonDummySibling_openFive :
    step commonDummyGraph commonDummySibling (.open 5) =
      some commonDummySiblingChild := by
  simp [step, commonDummySibling, commonDummySiblingChild]
  ext x
  fin_cases x <;> simp

/-- Exact score-coupled policies at the left child select the isolated label
`6` in common. -/
theorem commonDummyLeft_has_commonOpenPolicies :
    ∃ (left : OddStrategy commonDummyGraph true commonDummyLeft)
      (right : OddStrategy commonDummyGraph true
        (scoreTranslate 1 commonDummyLeft)),
      left.selectedMove = some (.open 6) ∧
      right.selectedMove = some (.open 6) := by
  have hleftTail : OddWins commonDummyGraph true commonDummyLeftChild :=
    odd_of_winner_false true commonDummyLeftChild
      commonDummyLeftChild_true_loses
  have hrightTail : OddWins commonDummyGraph true
      (scoreTranslate 1 commonDummyLeftChild) :=
    (oddWins_scoreTranslate_one_iff_evenWins commonDummyGraph true
      commonDummyLeftChild).2
      (even_of_winner_true false commonDummyLeftChild
        commonDummyLeftChild_false_wins)
  obtain ⟨leftTail⟩ := hleftTail.nonempty_oddStrategy
  obtain ⟨rightTail⟩ := hrightTail.nonempty_oddStrategy
  let left : OddStrategy commonDummyGraph true commonDummyLeft :=
    .choose commonDummyLeft (by decide) (.open 6) commonDummyLeftChild
      commonDummyLeft_openSix leftTail
  have htranslated : step commonDummyGraph
      (scoreTranslate 1 commonDummyLeft) (.open 6) =
        some (scoreTranslate 1 commonDummyLeftChild) := by
    rw [step_scoreTranslate, commonDummyLeft_openSix]
    rfl
  let right : OddStrategy commonDummyGraph true
      (scoreTranslate 1 commonDummyLeft) :=
    .choose (scoreTranslate 1 commonDummyLeft) (by decide) (.open 6)
      (scoreTranslate 1 commonDummyLeftChild) htranslated rightTail
  exact ⟨left, right, rfl, rfl⟩

/-- The immediate universal sibling has the symmetric exact pair-policy
event: both policies may select isolated label `5`. -/
theorem commonDummySibling_has_commonOpenPolicies :
    ∃ (left : OddStrategy commonDummyGraph true commonDummySibling)
      (right : OddStrategy commonDummyGraph true
        (scoreTranslate 1 commonDummySibling)),
      left.selectedMove = some (.open 5) ∧
      right.selectedMove = some (.open 5) := by
  have hleftTail : OddWins commonDummyGraph true
      commonDummySiblingChild :=
    odd_of_winner_false true commonDummySiblingChild
      commonDummySiblingChild_true_loses
  have hrightTail : OddWins commonDummyGraph true
      (scoreTranslate 1 commonDummySiblingChild) :=
    (oddWins_scoreTranslate_one_iff_evenWins commonDummyGraph true
      commonDummySiblingChild).2
      (even_of_winner_true false commonDummySiblingChild
        commonDummySiblingChild_false_wins)
  obtain ⟨leftTail⟩ := hleftTail.nonempty_oddStrategy
  obtain ⟨rightTail⟩ := hrightTail.nonempty_oddStrategy
  let left : OddStrategy commonDummyGraph true commonDummySibling :=
    .choose commonDummySibling (by decide) (.open 5)
      commonDummySiblingChild commonDummySibling_openFive leftTail
  have htranslated : step commonDummyGraph
      (scoreTranslate 1 commonDummySibling) (.open 5) =
        some (scoreTranslate 1 commonDummySiblingChild) := by
    rw [step_scoreTranslate, commonDummySibling_openFive]
    rfl
  let right : OddStrategy commonDummyGraph true
      (scoreTranslate 1 commonDummySibling) :=
    .choose (scoreTranslate 1 commonDummySibling) (by decide) (.open 5)
      (scoreTranslate 1 commonDummySiblingChild) htranslated rightTail
  exact ⟨left, right, rfl, rfl⟩

/-- One-step policy-ancestry no-go: a nonmover-controlled defender state can
have two mover-controlled isolated-OPEN children, and each child admits exact
score-coupled policies selecting the other isolate in common.  Therefore
neither controlled classes nor the existence of the immediate universal
sibling determines the selector needed to rule out common dummy consumption. -/
theorem commonDummyEvent_with_universalSibling_is_consistent :
    IsDummy commonDummyGraph 5 ∧ IsDummy commonDummyGraph 6 ∧
      NonmoverControlled commonDummyGraph commonDummyParent ∧
      step commonDummyGraph commonDummyParent (.open 5) =
        some commonDummyLeft ∧
      step commonDummyGraph commonDummyParent (.open 6) =
        some commonDummySibling ∧
      MoverControlled commonDummyGraph commonDummyLeft ∧
      MoverControlled commonDummyGraph commonDummySibling ∧
      NonmoverControlled commonDummyGraph commonDummyLeftChild ∧
      NonmoverControlled commonDummyGraph commonDummySiblingChild ∧
      QueueTurnParity commonDummyParent ∧
      QueueTurnParity commonDummyLeft ∧
      QueueTurnParity commonDummyLeftChild ∧
      Odd (liveSet commonDummyParent).card ∧
      Odd (liveSet commonDummyLeft).card ∧
      Odd (liveSet commonDummyLeftChild).card ∧
      (∃ (left : OddStrategy commonDummyGraph true commonDummyLeft)
        (right : OddStrategy commonDummyGraph true
          (scoreTranslate 1 commonDummyLeft)),
        left.selectedMove = some (.open 6) ∧
        right.selectedMove = some (.open 6)) ∧
      (∃ (left : OddStrategy commonDummyGraph true commonDummySibling)
        (right : OddStrategy commonDummyGraph true
          (scoreTranslate 1 commonDummySibling)),
        left.selectedMove = some (.open 5) ∧
        right.selectedMove = some (.open 5)) := by
  exact ⟨commonDummyGraph_dummyFive, commonDummyGraph_dummySix,
    commonDummyParent_nonmoverControlled, commonDummyParent_openFive,
    commonDummyParent_openSix, commonDummyLeft_moverControlled,
    commonDummySibling_moverControlled,
    commonDummyLeftChild_nonmoverControlled,
    commonDummySiblingChild_nonmoverControlled,
    commonDummyParent_queueTurnParity,
    commonDummyLeft_queueTurnParity,
    commonDummyLeftChild_queueTurnParity,
    commonDummyParent_liveSet_card_odd,
    commonDummyLeft_liveSet_card_odd,
    commonDummyLeftChild_liveSet_card_odd,
    commonDummyLeft_has_commonOpenPolicies,
    commonDummySibling_has_commonOpenPolicies⟩

end

end Ogdoad.Fifo
