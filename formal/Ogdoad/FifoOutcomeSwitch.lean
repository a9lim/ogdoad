import Ogdoad.FifoOutcome
import Ogdoad.FifoNeutralPair

/-!
# Root outcome sheets do not classify active dummy intervals

The four-valued mover/nonmover outcome sheet of a dummy-free public state
does not retain enough information to transport a strategy through an active
isolated-dummy interval.  On the three-label graph already used by
`FifoNeutralPair`, the reversed two-OPEN prefixes

`OPEN d; OPEN 0` and `OPEN 0; OPEN d`

have the same remaining real vertex, the same real queue after erasing `d`,
the same turn, and the same score.  Nevertheless their FIFO orders have
opposite outcomes for seat `true`: the dummy-front state is even-winning,
whereas `oddWins_activeNeutralInterval` proves that the dummy-rear state is
odd-winning.

This is a conditioned-state obstruction, not a counterexample to linking at
the initial root.  It says exactly that a case split on the dummy-free root
outcome sheet cannot by itself supply the missing ancestry-sensitive splice.
-/

namespace Ogdoad.Fifo

noncomputable section

/-- The reversed companion of `activeNeutralIntervalState`, reached by
opening the isolated dummy before the real vertex `0`. -/
def activeDummyFrontState : State (Fin 3) where
  untouched := {2}
  queue := [1, 0]
  ko := false
  toMove := false
  score := 0

/-- Both reversed prefixes delete to this same real public data.  Its `ko`
bit is the singleton delay at the dummy-free one-OPEN state. -/
def activeDummyShadowState : State (Fin 3) where
  untouched := {2}
  queue := [0]
  ko := true
  toMove := true
  score := 0

/-- The dummy-front state is reached by the reversed two-OPEN prefix. -/
theorem activeDummyFrontState_reachable :
    ∃ s0,
      step activeNeutralIntervalGraph (initial (V := Fin 3)) (.open 1) =
        some s0 ∧
      step activeNeutralIntervalGraph s0 (.open 0) =
        some activeDummyFrontState := by
  let s0 : State (Fin 3) := {
    untouched := {0, 2}
    queue := [1]
    ko := true
    toMove := true
    score := 0 }
  refine ⟨s0, ?_, ?_⟩
  · have hU : (Finset.univ.erase 1 : Finset (Fin 3)) = {0, 2} := by
      ext x
      fin_cases x <;> simp
    simp [step, initial, s0, hU]
  · simp [step, s0, activeDummyFrontState]

/-- Erasing the isolated label from either reversed queue gives the same real
queue.  The remaining real public coordinates already agree. -/
theorem reversed_prefixes_have_same_real_shadow :
    activeDummyFrontState.untouched = activeNeutralIntervalState.untouched ∧
    activeDummyFrontState.queue.erase 1 =
      activeNeutralIntervalState.queue.erase 1 ∧
    activeDummyFrontState.toMove = activeNeutralIntervalState.toMove ∧
    activeDummyFrontState.score = activeNeutralIntervalState.score := by
  decide

/-- In this two-OPEN checkpoint, deleting the one past dummy OPEN toggles the
controller and restores the singleton ko delay.  Both interval orders then
give exactly `activeDummyShadowState`. -/
theorem reversed_prefixes_delete_to_activeDummyShadow :
    ({ activeDummyFrontState with
        queue := activeDummyFrontState.queue.erase 1
        ko := true
        toMove := !activeDummyFrontState.toMove } : State (Fin 3)) =
      activeDummyShadowState ∧
    ({ activeNeutralIntervalState with
        queue := activeNeutralIntervalState.queue.erase 1
        ko := true
        toMove := !activeNeutralIntervalState.toMove } : State (Fin 3)) =
      activeDummyShadowState := by
  decide

/-- The explicit common dummy-free state is the ordinary `OPEN 0` child of
the root on the carrier with `1` removed. -/
theorem activeDummyShadowState_is_direct_open :
    step activeNeutralIntervalGraph (initialWithout 1) (.open 0) =
      some activeDummyShadowState := by
  have hU : ((Finset.univ.erase 1).erase 0 : Finset (Fin 3)) = {2} := by
    ext x
    fin_cases x <;> simp
  simp [step, initialWithout, activeDummyShadowState, hU]

/-- On the dummy-deleted two-real-vertex root, the current mover can force
even by opening either endpoint; the ko delay then forces the other OPEN
before any charged CLOSE. -/
theorem moverEvenWins_activeDummyShadowRoot :
    EvenWins activeNeutralIntervalGraph false (initialWithout 1) := by
  have hopen :
      step activeNeutralIntervalGraph (initialWithout 1) (.open 0) =
        some activeDummyShadowState :=
    activeDummyShadowState_is_direct_open
  refine EvenWins.choose (initialWithout 1) (by rfl) (.open 0)
    activeDummyShadowState hopen ?_
  have hasMove : ∃ m s',
      step activeNeutralIntervalGraph activeDummyShadowState m = some s' := by
    let so : State (Fin 3) := {
      untouched := ∅
      queue := [0, 2]
      ko := false
      toMove := false
      score := 0 }
    exact ⟨.open 2, so, by simp [step, activeDummyShadowState, so]⟩
  refine EvenWins.answer activeDummyShadowState (by decide) hasMove ?_
  intro m t hstep
  cases m with
  | «open» v =>
      simp only [step, activeDummyShadowState] at hstep
      split at hstep
      · rename_i hv
        have hv2 : v = 2 := by simpa using hv
        subst v
        cases hstep
        exact evenWins_of_untouched_empty false _ (by simp) (by simp)
      · contradiction
  | close =>
      simp [step, activeDummyShadowState] at hstep
  | pass =>
      simp [step, activeDummyShadowState] at hstep

/-- The physical nonmover can also force even at the same dummy-free root:
after either possible first OPEN, it opens the other real endpoint. -/
theorem nonmoverEvenWins_activeDummyShadowRoot :
    EvenWins activeNeutralIntervalGraph true (initialWithout 1) := by
  have hasMove : ∃ m s',
      step activeNeutralIntervalGraph (initialWithout 1) m = some s' :=
    ⟨.open 0, activeDummyShadowState,
      activeDummyShadowState_is_direct_open⟩
  refine EvenWins.answer (initialWithout 1) (by decide) hasMove ?_
  intro m t hstep
  cases m with
  | «open» v =>
      have hv : v ∈ (initialWithout (V := Fin 3) 1).untouched := by
        by_contra hnot
        simp [step, hnot] at hstep
      have hv02 : v = 0 ∨ v = 2 := by
        fin_cases v <;> simp [initialWithout] at hv ⊢
      rcases hv02 with rfl | rfl
      · have ht : t = activeDummyShadowState := by
          rw [activeDummyShadowState_is_direct_open] at hstep
          exact Option.some.inj hstep.symm
        subst t
        let so : State (Fin 3) := {
          untouched := ∅
          queue := [0, 2]
          ko := false
          toMove := false
          score := 0 }
        have hopen :
            step activeNeutralIntervalGraph activeDummyShadowState
              (.open 2) = some so := by
          simp [step, activeDummyShadowState, so]
        refine EvenWins.choose activeDummyShadowState (by rfl)
          (.open 2) so hopen ?_
        exact evenWins_of_untouched_empty true so (by simp [so])
          (by simp [so])
      · let s2 : State (Fin 3) := {
          untouched := {0}
          queue := [2]
          ko := true
          toMove := true
          score := 0 }
        have hopen2 :
            step activeNeutralIntervalGraph (initialWithout 1) (.open 2) =
              some s2 := by
          have hU :
              ((Finset.univ.erase 1).erase 2 : Finset (Fin 3)) = {0} := by
            ext x
            fin_cases x <;> simp
          simp [step, initialWithout, s2, hU]
        have ht : t = s2 := by
          rw [hopen2] at hstep
          exact Option.some.inj hstep.symm
        subst t
        let so : State (Fin 3) := {
          untouched := ∅
          queue := [2, 0]
          ko := false
          toMove := false
          score := 0 }
        have hopen : step activeNeutralIntervalGraph s2 (.open 0) = some so := by
          simp [step, s2, so]
        refine EvenWins.choose s2 (by rfl) (.open 0) so hopen ?_
        exact evenWins_of_untouched_empty true so (by simp [so])
          (by simp [so])
  | close =>
      simp [step, initialWithout] at hstep
  | pass =>
      simp [step, initialWithout] at hstep

/-- The common dummy-free root is in the strongest cold class `BothEven`.
Thus even that complete root sheet does not classify the two active interval
orders. -/
theorem bothEven_activeDummyShadowRoot :
    BothEven activeNeutralIntervalGraph (initialWithout 1) :=
  ⟨moverEvenWins_activeDummyShadowRoot,
    nonmoverEvenWins_activeDummyShadowRoot⟩

/-- With the dummy at the front, seat `true` can keep score zero.  If the
opponent opens `2`, the score-zero untouched-empty tail is immediate.  If the
opponent closes the neutral dummy, seat `true` opens `2` before real front
`0` can be charged. -/
theorem evenWins_activeDummyFront :
    EvenWins activeNeutralIntervalGraph true activeDummyFrontState := by
  have hasMove : ∃ m s',
      step activeNeutralIntervalGraph activeDummyFrontState m = some s' := by
    let so : State (Fin 3) := {
      untouched := ∅
      queue := [1, 0, 2]
      ko := false
      toMove := true
      score := 0 }
    exact ⟨.open 2, so, by simp [step, activeDummyFrontState, so]⟩
  refine EvenWins.answer activeDummyFrontState (by decide) hasMove ?_
  intro m t hstep
  cases m with
  | «open» v =>
      simp only [step, activeDummyFrontState] at hstep
      split at hstep
      · rename_i hv
        have hv2 : v = 2 := by simpa using hv
        subst v
        cases hstep
        exact evenWins_of_untouched_empty true _ (by simp) (by simp)
      · contradiction
  | close =>
      let sc : State (Fin 3) := {
        untouched := {2}
        queue := [0]
        ko := false
        toMove := true
        score := 0 }
      have hclose :
          step activeNeutralIntervalGraph activeDummyFrontState .close =
            some sc := by
        simp [step, activeDummyFrontState, sc,
          flip_dummy activeNeutralIntervalGraph_dummy]
      rw [hclose] at hstep
      have ht : t = sc := Option.some.inj hstep.symm
      subst t
      let so : State (Fin 3) := {
        untouched := ∅
        queue := [0, 2]
        ko := false
        toMove := false
        score := 0 }
      have hopen : step activeNeutralIntervalGraph sc (.open 2) = some so := by
        simp [step, sc, so]
      refine EvenWins.choose sc (by rfl) (.open 2) so hopen ?_
      exact evenWins_of_untouched_empty true so (by simp [so]) (by simp [so])
  | pass =>
      simp [step, activeDummyFrontState] at hstep

/-- The two active dummy placements have incompatible outcomes for the same
physical seat, despite having identical dummy-deleted real public data. -/
theorem active_dummy_order_changes_outcome :
    EvenWins activeNeutralIntervalGraph true activeDummyFrontState ∧
      OddWins activeNeutralIntervalGraph true activeNeutralIntervalState :=
  ⟨evenWins_activeDummyFront, oddWins_activeNeutralInterval⟩

/-- Consequently there is no outcome-preserving identification between the
two reversed active intervals. -/
theorem not_evenWins_activeDummyRear :
    ¬EvenWins activeNeutralIntervalGraph true activeNeutralIntervalState :=
  fun h ↦ h.not_oddWins oddWins_activeNeutralInterval

end

end Ogdoad.Fifo
