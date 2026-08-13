import Ogdoad.FifoCongruenceOutcomeBoundary

/-!
# The consumed-dummy shear branch contains the no-dummy obstruction

The first-return shear descent has one branch not covered by the exact
target-consumed cold theorem: the isolated dummy has been consumed while the
shear target remains untouched.  This file shows that the omission is sharp.

On five labels, start with the single edge `0--2`, use `3` as the isolated
dummy, `4` as an auxiliary isolate, and shear row `0` into target row `1`.
The common neutral block

`OPEN 3; OPEN 4; CLOSE; CLOSE`

consumes the dummy and the auxiliary isolate and returns to an empty queue,
leaving the shear target `1` untouched.  Its residual source state is the
cold matching-plus-isolate root, whereas its residual target state is the
mover-controlled three-vertex path root.

Thus the branch in which the dummy is consumed but the shear target survives
cannot be discharged by an endpoint-only `BothEven` transport statement.
Any successful whole-block proof must retain genuinely strategy-correlated
ancestry across the dummy-consuming block.
-/

namespace Ogdoad.Fifo

noncomputable section

/-- Exact reduction of a dummy-consumed first-return branch.  If the shear
target was consumed in the same block, the existing unit-debt theorem makes
the normalized endpoint cold on both graphs.  Otherwise the target survives,
which is the sole branch requiring additional ancestry information. -/
theorem CrossGraphStrategyBlockExit.cold_or_target_survives_of_dummy_consumed
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {i j d : V} {seat : Bool} {s : State V}
    (exit : CrossGraphStrategyBlockExit G
      (elementaryCongruenceGraph G i j) seat s s)
    (hsWF : WellFormed s) (hsQueue : s.queue = []) (hsScore : s.score = 0)
    (hd : d ∉ exit.terminalG.untouched) :
    (j ∉ exit.terminalG.untouched ∧ BothEven G exit.terminalG ∧
        BothEven (elementaryCongruenceGraph G i j) exit.terminalG) ∨
      (j ∈ exit.terminalG.untouched ∧ d ∉ exit.terminalG.untouched) := by
  by_cases hj : j ∈ exit.terminalG.untouched
  · exact Or.inr ⟨hj, hd⟩
  · have hcold := exit.bothEven_normalized_of_target_consumed
      hsWF hsQueue hsScore hj
    exact Or.inl ⟨hj, hcold.1, hcold.2⟩

/-- The strongest endpoint-only statement one might try on the surviving
branch: a common neutral root trace from a cold source root, consuming the
dummy but not the shear target, should preserve the cold endpoint sheet.
The finite witness below refutes this statement. -/
def DummyConsumedSurvivingTargetEndpointBothEvenForward : Prop :=
  ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (d : V), IsDummy G d →
      ∀ (i j : V), i ≠ j → d ≠ j →
        BothEven G (initial (V := V)) →
          ∀ (s : State V),
            (∃ ms,
              LegalTrace G (initial (V := V)) ms s ∧
              LegalTrace (elementaryCongruenceGraph G i j)
                (initial (V := V)) ms s) →
            d ∉ s.untouched → j ∈ s.untouched → s.queue = [] →
              s.score = 0 → BothEven G s →
                BothEven (elementaryCongruenceGraph G i j) s

/-- The source has the single real edge `0--2`; labels `1`, `3`, and `4` are
isolated. -/
def consumedDummyShearSourceRel (x y : Fin 5) : Bool :=
  decide (x = 0 ∧ y = 2)

def consumedDummyShearSourceGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun x y ↦ consumedDummyShearSourceRel x y = true

/-- Shearing row `0` into target row `1` produces the path `0--2--1`; labels
`3` and `4` remain isolated. -/
def consumedDummyShearTargetRel (x y : Fin 5) : Bool :=
  decide ((x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 2))

def consumedDummyShearTargetGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun x y ↦ consumedDummyShearTargetRel x y = true

def consumedDummyShearSourceAdj (x y : Fin 5) : Bool :=
  consumedDummyShearSourceRel x y || consumedDummyShearSourceRel y x

def consumedDummyShearTargetAdj (x y : Fin 5) : Bool :=
  consumedDummyShearTargetRel x y || consumedDummyShearTargetRel y x

def consumedDummyShearFlip (adj : Fin 5 → Fin 5 → Bool)
    (U : Finset (Fin 5)) (v : Fin 5) : ZMod 2 :=
  ((U.filter fun w ↦ adj v w = true).card : ZMod 2)

def consumedDummyShearStep (adj : Fin 5 → Fin 5 → Bool)
    (s : State (Fin 5)) : Move (Fin 5) → Option (State (Fin 5))
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
          if s.ko then none
          else
            some {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove
              score := s.score + consumedDummyShearFlip adj s.untouched f }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

theorem consumedDummyShearFlip_source_eq_flip
    (U : Finset (Fin 5)) (v : Fin 5) :
    consumedDummyShearFlip consumedDummyShearSourceAdj U v =
      flip consumedDummyShearSourceGraph U v := by
  classical
  simp only [consumedDummyShearFlip, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [consumedDummyShearSourceAdj, consumedDummyShearSourceRel,
      consumedDummyShearSourceGraph, SimpleGraph.fromRel_adj]

theorem consumedDummyShearFlip_target_eq_flip
    (U : Finset (Fin 5)) (v : Fin 5) :
    consumedDummyShearFlip consumedDummyShearTargetAdj U v =
      flip consumedDummyShearTargetGraph U v := by
  classical
  simp only [consumedDummyShearFlip, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [consumedDummyShearTargetAdj, consumedDummyShearTargetRel,
      consumedDummyShearTargetGraph, SimpleGraph.fromRel_adj]

theorem consumedDummyShearStep_source_eq_step
    (s : State (Fin 5)) (m : Move (Fin 5)) :
    consumedDummyShearStep consumedDummyShearSourceAdj s m =
      step consumedDummyShearSourceGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [consumedDummyShearStep, step]
  | close =>
      cases q <;> cases ko <;>
        simp [consumedDummyShearStep, step,
          consumedDummyShearFlip_source_eq_flip]
  | pass => simp [consumedDummyShearStep, step]

theorem consumedDummyShearStep_target_eq_step
    (s : State (Fin 5)) (m : Move (Fin 5)) :
    consumedDummyShearStep consumedDummyShearTargetAdj s m =
      step consumedDummyShearTargetGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [consumedDummyShearStep, step]
  | close =>
      cases q <;> cases ko <;>
        simp [consumedDummyShearStep, step,
          consumedDummyShearFlip_target_eq_flip]
  | pass => simp [consumedDummyShearStep, step]

theorem consumedDummyShearTarget_eq_elementaryCongruence :
    consumedDummyShearTargetGraph =
      elementaryCongruenceGraph consumedDummyShearSourceGraph 0 1 := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [consumedDummyShearTargetGraph, consumedDummyShearTargetRel,
      consumedDummyShearSourceGraph, consumedDummyShearSourceRel,
      elementaryCongruenceGraph, SimpleGraph.fromRel_adj, Xor]

theorem consumedDummyShearSource_dummy :
    IsDummy consumedDummyShearSourceGraph 3 := by
  intro v
  fin_cases v <;>
    simp [consumedDummyShearSourceGraph, consumedDummyShearSourceRel,
      SimpleGraph.fromRel_adj]

theorem consumedDummyShearSource_matching :
    IsMatchingGraph consumedDummyShearSourceGraph := by
  intro v x y hvx hvy
  fin_cases v <;> fin_cases x <;> fin_cases y <;>
    simp [consumedDummyShearSourceGraph, consumedDummyShearSourceRel,
      SimpleGraph.fromRel_adj] at hvx hvy ⊢

theorem consumedDummyShearSource_root_bothEven :
    BothEven consumedDummyShearSourceGraph (initial (V := Fin 5)) := by
  exact ⟨by simpa [MoverEvenWins, initial] using
      evenWins_initial_of_matching consumedDummyShearSource_matching false,
    by simpa [NonmoverEvenWins, initial] using
      evenWins_initial_of_matching consumedDummyShearSource_matching true⟩

theorem consumedDummyShearTarget_dummy :
    IsDummy consumedDummyShearTargetGraph 3 := by
  rw [consumedDummyShearTarget_eq_elementaryCongruence]
  exact consumedDummyShearSource_dummy.elementaryCongruenceGraph 0 1
    (by decide)

/-- Empty-queue checkpoint after consuming labels `3` and `4`.  The dummy is
gone, but the shear target `1` survives. -/
def consumedDummyShearEndpoint : State (Fin 5) where
  untouched := {0, 1, 2}
  queue := []
  ko := false
  toMove := false
  score := 0

def consumedDummyShearWord : List (Move (Fin 5)) :=
  [.open 3, .open 4, .close, .close]

def consumedDummyShearMoves : List (Move (Fin 5)) :=
  [.open 0, .open 1, .open 2, .open 3, .open 4, .close, .pass]

theorem mem_consumedDummyShearMoves (m : Move (Fin 5)) :
    m ∈ consumedDummyShearMoves := by
  cases m with
  | «open» v => fin_cases v <;> simp [consumedDummyShearMoves]
  | close => simp [consumedDummyShearMoves]
  | pass => simp [consumedDummyShearMoves]

theorem consumedDummyShearWord_source_run :
    runMoves (consumedDummyShearStep consumedDummyShearSourceAdj)
      (initial (V := Fin 5)) consumedDummyShearWord =
        some consumedDummyShearEndpoint := by
  decide

theorem consumedDummyShearWord_target_run :
    runMoves (consumedDummyShearStep consumedDummyShearTargetAdj)
      (initial (V := Fin 5)) consumedDummyShearWord =
        some consumedDummyShearEndpoint := by
  decide

theorem consumedDummyShearWord_source_trace :
    LegalTrace consumedDummyShearSourceGraph (initial (V := Fin 5))
      consumedDummyShearWord consumedDummyShearEndpoint := by
  exact legalTrace_of_runMoves consumedDummyShearSourceGraph
    (consumedDummyShearStep consumedDummyShearSourceAdj)
    consumedDummyShearStep_source_eq_step consumedDummyShearWord_source_run

theorem consumedDummyShearWord_target_trace :
    LegalTrace consumedDummyShearTargetGraph (initial (V := Fin 5))
      consumedDummyShearWord consumedDummyShearEndpoint := by
  exact legalTrace_of_runMoves consumedDummyShearTargetGraph
    (consumedDummyShearStep consumedDummyShearTargetAdj)
    consumedDummyShearStep_target_eq_step consumedDummyShearWord_target_run

theorem consumedDummyShearEndpoint_survival :
    (3 : Fin 5) ∉ consumedDummyShearEndpoint.untouched ∧
      (1 : Fin 5) ∈ consumedDummyShearEndpoint.untouched ∧
      consumedDummyShearEndpoint.queue = [] ∧
      consumedDummyShearEndpoint.score = 0 := by
  decide

def consumedDummyShearSourceWinner (seat : Bool) : Bool :=
  finiteEvenWinner consumedDummyShearMoves
    (consumedDummyShearStep consumedDummyShearSourceAdj) seat
    (rank consumedDummyShearEndpoint + 1) consumedDummyShearEndpoint

def consumedDummyShearTargetWinner (seat : Bool) : Bool :=
  finiteEvenWinner consumedDummyShearMoves
    (consumedDummyShearStep consumedDummyShearTargetAdj) seat
    (rank consumedDummyShearEndpoint + 1) consumedDummyShearEndpoint

theorem consumedDummyShearSourceWinner_spec (seat : Bool) :
    if consumedDummyShearSourceWinner seat then
      EvenWins consumedDummyShearSourceGraph seat consumedDummyShearEndpoint
    else
      OddWins consumedDummyShearSourceGraph seat consumedDummyShearEndpoint := by
  apply finiteEvenWinner_spec consumedDummyShearSourceGraph
    consumedDummyShearMoves mem_consumedDummyShearMoves
    (consumedDummyShearStep consumedDummyShearSourceAdj)
    consumedDummyShearStep_source_eq_step seat
    (rank consumedDummyShearEndpoint + 1) consumedDummyShearEndpoint
  omega

theorem consumedDummyShearTargetWinner_spec (seat : Bool) :
    if consumedDummyShearTargetWinner seat then
      EvenWins consumedDummyShearTargetGraph seat consumedDummyShearEndpoint
    else
      OddWins consumedDummyShearTargetGraph seat consumedDummyShearEndpoint := by
  apply finiteEvenWinner_spec consumedDummyShearTargetGraph
    consumedDummyShearMoves mem_consumedDummyShearMoves
    (consumedDummyShearStep consumedDummyShearTargetAdj)
    consumedDummyShearStep_target_eq_step seat
    (rank consumedDummyShearEndpoint + 1) consumedDummyShearEndpoint
  omega

theorem consumedDummyShear_source_false_wins :
    consumedDummyShearSourceWinner false = true := by decide

theorem consumedDummyShear_source_true_wins :
    consumedDummyShearSourceWinner true = true := by decide

theorem consumedDummyShear_target_false_wins :
    consumedDummyShearTargetWinner false = true := by decide

theorem consumedDummyShear_target_true_loses :
    consumedDummyShearTargetWinner true = false := by decide

theorem consumedDummyShearEndpoint_source_bothEven :
    BothEven consumedDummyShearSourceGraph consumedDummyShearEndpoint := by
  have hfalse := consumedDummyShearSourceWinner_spec false
  rw [consumedDummyShear_source_false_wins] at hfalse
  have htrue := consumedDummyShearSourceWinner_spec true
  rw [consumedDummyShear_source_true_wins] at htrue
  exact ⟨by simpa [MoverEvenWins, consumedDummyShearEndpoint] using hfalse,
    by simpa [NonmoverEvenWins, consumedDummyShearEndpoint] using htrue⟩

theorem consumedDummyShearEndpoint_target_moverControlled :
    MoverControlled consumedDummyShearTargetGraph
      consumedDummyShearEndpoint := by
  have hfalse := consumedDummyShearTargetWinner_spec false
  rw [consumedDummyShear_target_false_wins] at hfalse
  have htrue := consumedDummyShearTargetWinner_spec true
  rw [consumedDummyShear_target_true_loses] at htrue
  have hnot := (oddWins_iff_not_evenWins consumedDummyShearTargetGraph true
    consumedDummyShearEndpoint).mp htrue
  exact ⟨by simpa [MoverEvenWins, consumedDummyShearEndpoint] using hfalse,
    by simpa [NonmoverEvenWins, consumedDummyShearEndpoint] using hnot⟩

/-- Sharp remaining-branch boundary.  A common score-zero first block can
consume the isolated dummy while leaving the shear target live, and land on a
source-cold / target-controlled endpoint.  Hence the target-consumed cold
theorem cannot be extended by replacing “target consumed” with “dummy
consumed”; the missing input is strategy ancestry, not endpoint outcome. -/
theorem consumedDummy_survivingTarget_endpoint_transport_false :
    IsDummy consumedDummyShearSourceGraph 3 ∧
      BothEven consumedDummyShearSourceGraph (initial (V := Fin 5)) ∧
      consumedDummyShearTargetGraph =
        elementaryCongruenceGraph consumedDummyShearSourceGraph 0 1 ∧
      LegalTrace consumedDummyShearSourceGraph (initial (V := Fin 5))
        consumedDummyShearWord consumedDummyShearEndpoint ∧
      LegalTrace consumedDummyShearTargetGraph (initial (V := Fin 5))
        consumedDummyShearWord consumedDummyShearEndpoint ∧
      (3 : Fin 5) ∉ consumedDummyShearEndpoint.untouched ∧
      (1 : Fin 5) ∈ consumedDummyShearEndpoint.untouched ∧
      consumedDummyShearEndpoint.queue = [] ∧
      consumedDummyShearEndpoint.score = 0 ∧
      BothEven consumedDummyShearSourceGraph consumedDummyShearEndpoint ∧
      MoverControlled consumedDummyShearTargetGraph
        consumedDummyShearEndpoint := by
  exact ⟨consumedDummyShearSource_dummy,
    consumedDummyShearSource_root_bothEven,
    consumedDummyShearTarget_eq_elementaryCongruence,
    consumedDummyShearWord_source_trace,
    consumedDummyShearWord_target_trace,
    consumedDummyShearEndpoint_survival.1,
    consumedDummyShearEndpoint_survival.2.1,
    consumedDummyShearEndpoint_survival.2.2.1,
    consumedDummyShearEndpoint_survival.2.2.2,
    consumedDummyShearEndpoint_source_bothEven,
    consumedDummyShearEndpoint_target_moverControlled⟩

theorem dummyConsumedSurvivingTargetEndpointBothEvenForward_false :
    ¬DummyConsumedSurvivingTargetEndpointBothEvenForward := by
  intro hforward
  have htarget := hforward (Fin 5) inferInstance inferInstance
    consumedDummyShearSourceGraph 3 consumedDummyShearSource_dummy
    0 1 (by decide) (by decide) consumedDummyShearSource_root_bothEven
    consumedDummyShearEndpoint
    ⟨consumedDummyShearWord, consumedDummyShearWord_source_trace, by
      rw [← consumedDummyShearTarget_eq_elementaryCongruence]
      exact consumedDummyShearWord_target_trace⟩
    consumedDummyShearEndpoint_survival.1
    consumedDummyShearEndpoint_survival.2.1
    consumedDummyShearEndpoint_survival.2.2.1
    consumedDummyShearEndpoint_survival.2.2.2
    consumedDummyShearEndpoint_source_bothEven
  rw [← consumedDummyShearTarget_eq_elementaryCongruence] at htarget
  exact consumedDummyShearEndpoint_target_moverControlled.2 htarget.2

end

end Ogdoad.Fifo
