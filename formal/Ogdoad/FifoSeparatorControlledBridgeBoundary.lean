import Ogdoad.FifoPositionalSelectedEdgeBoundary
import Ogdoad.FifoSingletonForkBoundary

/-!
# A separator-zero fan need not create a controlled descent

The rank-minimal separator-one normal form leaves a selected real `OPEN`
whose child is a complete separator-zero fan.  Score translation does not
turn that zero-sheet policy into the second odd policy required by the
controlled-outcome machinery: translating the score exchanges the cold
`BothOdd` and `BothEven` classes.

The four-label positional missed-crossing model is already an exact local
counterexample to the proposed bridge.  Its outer selected policy lies on
sheet one and every proper concrete descendant lies on sheet zero.  Yet both
the complete-fan child and its forced `CLOSE` sibling are `BothOdd`, while the
isolated dummy remains untouched.  Hence neither state is controlled, and no
score-coupled odd companion exists there.

This refutes only the inference from a rank-minimal separator occurrence to a
lower controlled state.  The model starts at a noninitial score-one state and
is not a counterexample to FIFO linking.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- With no live cut, a unit score is cold odd for both physical seats. -/
theorem bothOdd_of_noLiveCut_score_one
    {G : SimpleGraph V} {s : State V}
    (hcut : NoLiveCut G s) (hscore : s.score = 1) : BothOdd G s := by
  have hnonzero : s.score ≠ 0 := by rw [hscore]; exact one_ne_zero
  constructor
  · exact (oddWins_iff_not_evenWins G s.toMove s).mp
      (oddWins_of_noLiveCut s.toMove s hcut hnonzero)
  · exact (oddWins_iff_not_evenWins G (!s.toMove) s).mp
      (oddWins_of_noLiveCut (!s.toMove) s hcut hnonzero)

omit [Fintype V] in
/-- A cold-odd state lies in neither controlled outcome class. -/
theorem BothOdd.not_controlled
    {G : SimpleGraph V} {s : State V} (h : BothOdd G s) :
    ¬(MoverControlled G s ∨ NonmoverControlled G s) := by
  rintro (hm | hn)
  · exact h.1 hm.1
  · exact h.2 hn.2

theorem positionalMissedCross_fan_bothOdd :
    BothOdd positionalMissedCrossGraph positionalMissedCrossFan :=
  bothOdd_of_noLiveCut_score_one positionalMissedCross_fan_noLiveCut rfl

theorem positionalMissedCross_close_bothOdd :
    BothOdd positionalMissedCrossGraph positionalMissedCrossClose :=
  bothOdd_of_noLiveCut_score_one positionalMissedCross_close_noLiveCut rfl

/-- The exact separator-minimum local model has a live dummy but neither its
complete-fan child nor the forced `CLOSE` child is controlled.  Together with
`positionalMissedCross_properDescendants_sheet_zero`, this is the smallest
checked obstruction to feeding the separator minimum directly into the
reachable-minimal controlled-state eliminator. -/
theorem positionalMissedCross_separator_child_close_not_controlled :
    PublicPolicySeparatorSheet 2
        (isolatedGraphSeparatorFunctional positionalMissedCrossGraph 2
          positionalMissedCross_dummyTwo) false
        positionalMissedCross_selectedOpenStrategy.toPublicPolicy 1 ∧
      (∀ {t : State (Fin 4)}
          (desc : OddStrategy positionalMissedCrossGraph false t),
        StrategyNode positionalMissedCrossGraph false
            positionalMissedCross_selectedOpenStrategy desc →
          rank t < rank positionalMissedCrossParent →
            PublicPolicySeparatorSheet 2
              (isolatedGraphSeparatorFunctional positionalMissedCrossGraph 2
                positionalMissedCross_dummyTwo) false
              desc.toPublicPolicy 0) ∧
      ((2 : Fin 4) ∈ positionalMissedCrossFan.untouched) ∧
      step positionalMissedCrossGraph positionalMissedCrossFan .close =
        some positionalMissedCrossClose ∧
      ¬(MoverControlled positionalMissedCrossGraph positionalMissedCrossFan ∨
        NonmoverControlled positionalMissedCrossGraph positionalMissedCrossFan) ∧
      ¬(MoverControlled positionalMissedCrossGraph positionalMissedCrossClose ∨
        NonmoverControlled positionalMissedCrossGraph positionalMissedCrossClose) := by
  exact ⟨positionalMissedCross_selectedOpenStrategy_sheet_one,
    fun desc hnode hlt ↦
      positionalMissedCross_properDescendants_sheet_zero desc hnode hlt,
    by simp [positionalMissedCrossFan],
    positionalMissedCross_fan_close,
    positionalMissedCross_fan_bothOdd.not_controlled,
    positionalMissedCross_close_bothOdd.not_controlled⟩

/-- Score translation makes the complete-fan child `BothEven`, so an odd
strategy for the same distinguished seat cannot provide the missing coupled
policy. -/
theorem positionalMissedCross_fan_no_scoreCoupled_right :
    ¬Nonempty (OddStrategy positionalMissedCrossGraph false
      (scoreTranslate 1 positionalMissedCrossFan)) := by
  intro hright
  have heven : BothEven positionalMissedCrossGraph
      (scoreTranslate 1 positionalMissedCrossFan) :=
    (bothEven_scoreTranslate_one_iff_bothOdd
      positionalMissedCrossGraph positionalMissedCrossFan).2
        positionalMissedCross_fan_bothOdd
  have hevenSeat : EvenWins positionalMissedCrossGraph false
      (scoreTranslate 1 positionalMissedCrossFan) := by
    simpa [BothEven, MoverEvenWins, positionalMissedCrossFan,
      scoreTranslate] using heven.1
  exact hevenSeat.not_oddWins (Classical.choice hright).toOddWins

end

end Ogdoad.Fifo
