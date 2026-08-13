import Ogdoad.FifoCanonicalPositionalOdd
import Ogdoad.FifoOddSpikeFactor
import Ogdoad.FifoSeparatorBadSynchronizationBoundary

/-!
# Positional Bellman policies do not force a commuting-square edge

Canonicalization quotients an odd strategy by full concrete state, but the
Bellman condition at an attacker node asks only for one odd-winning child.
It does not make that child unique.  This module makes the resulting boundary
exact in two stages.

First, `preferredOddStrategy` is a rank-recursive, genuinely state-positional
odd strategy which chooses a prescribed move whenever that move remains in
the odd-winning region.  Thus changing the harmless tie-break is still a
canonical positionalization of the same proposition-valued winning region.

Second, a four-label one-edge state realizes the separator-minimum local
shape.  Opening `1` has separator increment one because the old queued vertex
`0` is its only neighbour.  Below that opening every legal increment is zero,
the isolated dummy is `2`, and both the forced-CLOSE child and the dummy-OPEN
child are odd-winning.  The preferred positional policy chooses `OPEN 3` at
both children: neither complementary crossing edge (`OPEN 2` after CLOSE, or
CLOSE after `OPEN 2`) is selected.

This refutes the proposed *selected-edge forcing inference*, not FIFO linking.
The local root starts with score one and is not an initial root.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

namespace PreferredOdd

/-- A Bellman-winning choice which prefers `preferred` whenever that move has
an odd-winning legal successor. -/
noncomputable def preferredOddWinningChoice
    (G : SimpleGraph V) (seat : Bool) (preferred : Move V) (s : State V)
    (hwin : OddWins G seat s) (ht : ¬Terminal s)
    (hturn : s.toMove ≠ seat) : PositionalOdd.OddWinningChoice G seat s := by
  by_cases hp : ∃ t, step G s preferred = some t ∧ OddWins G seat t
  · let t := Classical.choose hp
    exact {
      move := preferred
      next := t
      step := (Classical.choose_spec hp).1
      wins := (Classical.choose_spec hp).2 }
  · exact PositionalOdd.canonicalOddWinningChoice G seat s hwin ht hturn

omit [Fintype V] in
/-- The preferred choice really takes the prescribed edge whenever it is a
legal transition inside the odd-winning region. -/
theorem preferredOddWinningChoice_move_eq
    (G : SimpleGraph V) (seat : Bool) (preferred : Move V) (s : State V)
    (hwin : OddWins G seat s) (ht : ¬Terminal s)
    (hturn : s.toMove ≠ seat)
    (hp : ∃ t, step G s preferred = some t ∧ OddWins G seat t) :
    (preferredOddWinningChoice G seat preferred s hwin ht hturn).move =
      preferred := by
  simp only [preferredOddWinningChoice, dif_pos hp]

/-- A full-state positional odd strategy with an explicit harmless
tie-break. -/
noncomputable def preferredOddStrategy
    (G : SimpleGraph V) (seat : Bool) (preferred : Move V) (s : State V)
    (hwin : OddWins G seat s) : OddStrategy G seat s := by
  by_cases ht : Terminal s
  · exact .terminal s ht
      (PositionalOdd.oddWins_terminal_score_ne_zero hwin ht)
  · by_cases hturn : s.toMove = seat
    · exact .answer s hturn (not_terminal_has_step ht)
        (fun m t hstep ↦ preferredOddStrategy G seat preferred t
          (hwin.answer_child hturn hstep))
    · let choice := preferredOddWinningChoice
        G seat preferred s hwin ht hturn
      exact .choose s hturn choice.move choice.next choice.step
        (preferredOddStrategy G seat preferred choice.next choice.wins)
termination_by rank s
decreasing_by
  · exact rank_step_lt hstep
  · exact rank_step_lt choice.step

omit [Fintype V] in
/-- Proof irrelevance makes the preferred construction a function of the
full state, not of a displayed `OddWins` derivation. -/
theorem preferredOddStrategy_proof_irrelevant
    (G : SimpleGraph V) (seat : Bool) (preferred : Move V) (s : State V)
    (h₁ h₂ : OddWins G seat s) :
    preferredOddStrategy G seat preferred s h₁ =
      preferredOddStrategy G seat preferred s h₂ := by
  have : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

/-- Recursive memoization predicate for the preferred positional tree. -/
def PreferredMemoized
    {G : SimpleGraph V} {seat : Bool} (preferred : Move V) :
    {s : State V} → OddStrategy G seat s → Prop
  | _, .terminal _ _ _ => True
  | _, .choose _ _ _ t _ child =>
      child = preferredOddStrategy G seat preferred t child.toOddWins ∧
        PreferredMemoized preferred child
  | _, .answer _ _ _ children =>
      ∀ m t (hstep : step G _ m = some t),
        children m t hstep =
            preferredOddStrategy G seat preferred t
              (children m t hstep).toOddWins ∧
          PreferredMemoized preferred (children m t hstep)

omit [Fintype V] in
theorem preferredOddStrategy_memoized
    (G : SimpleGraph V) (seat : Bool) (preferred : Move V) :
    ∀ (s : State V) (hodd : OddWins G seat s),
      PreferredMemoized preferred
        (preferredOddStrategy G seat preferred s hodd) := by
  intro s
  induction s using (measure rank).wf.induction with
  | h s ih =>
      intro hodd
      rw [preferredOddStrategy.eq_def]
      split
      · trivial
      · rename_i ht
        split
        · rename_i hturn
          intro m t hstep
          constructor
          · exact preferredOddStrategy_proof_irrelevant
              G seat preferred t (hodd.answer_child hturn hstep)
                (preferredOddStrategy G seat preferred t
                  (hodd.answer_child hturn hstep)).toOddWins
          · exact ih t (rank_step_lt hstep)
              (hodd.answer_child hturn hstep)
        · rename_i hturn
          let choice := preferredOddWinningChoice
            G seat preferred s hodd ht hturn
          constructor
          · exact preferredOddStrategy_proof_irrelevant
              G seat preferred choice.next choice.wins
                (preferredOddStrategy G seat preferred choice.next
                  choice.wins).toOddWins
          · exact ih choice.next (rank_step_lt choice.step) choice.wins

omit [Fintype V] in
theorem PreferredMemoized.node_eq_preferred
    {G : SimpleGraph V} {seat : Bool} {preferred : Move V}
    {r s : State V} {root : OddStrategy G seat r}
    {desc : OddStrategy G seat s}
    (hroot : root =
      preferredOddStrategy G seat preferred r root.toOddWins)
    (hmemo : PreferredMemoized preferred root)
    (hnode : StrategyNode G seat root desc) :
    desc = preferredOddStrategy G seat preferred s desc.toOddWins := by
  induction hnode with
  | root => exact hroot
  | @choose a b c hseat m hstep child desc hdesc ih =>
      exact ih hmemo.1 hmemo.2
  | @answer a b c hseat hasMove children m hstep desc hdesc ih =>
      exact ih (hmemo m b hstep).1 (hmemo m b hstep).2

omit [Fintype V] in
/-- Strong positionality: two occurrences of the same full state in one
preferred tree carry literally the same continuation. -/
theorem preferredOddStrategy_subtree_unique
    (G : SimpleGraph V) (seat : Bool) (preferred : Move V)
    (r : State V) (hodd : OddWins G seat r) {s : State V}
    (left right : OddStrategy G seat s)
    (hleft : StrategyNode G seat
      (preferredOddStrategy G seat preferred r hodd) left)
    (hright : StrategyNode G seat
      (preferredOddStrategy G seat preferred r hodd) right) :
    left = right := by
  have hmemo := preferredOddStrategy_memoized G seat preferred r hodd
  have hroot : preferredOddStrategy G seat preferred r hodd =
      preferredOddStrategy G seat preferred r
        (preferredOddStrategy G seat preferred r hodd).toOddWins :=
    preferredOddStrategy_proof_irrelevant G seat preferred r _ _
  have hl := hmemo.node_eq_preferred hroot hleft
  have hr := hmemo.node_eq_preferred hroot hright
  calc
    left = preferredOddStrategy G seat preferred s left.toOddWins := hl
    _ = preferredOddStrategy G seat preferred s right.toOddWins :=
      preferredOddStrategy_proof_irrelevant G seat preferred s _ _
    _ = right := hr.symm

omit [Fintype V] in
/-- At an attacker node the preferred positional strategy selects the
preferred move whenever it has an odd-winning child. -/
theorem preferredOddStrategy_selectedMove_eq
    (G : SimpleGraph V) (seat : Bool) (preferred : Move V) (s : State V)
    (hwin : OddWins G seat s) (ht : ¬Terminal s)
    (hturn : s.toMove ≠ seat)
    (hp : ∃ t, step G s preferred = some t ∧ OddWins G seat t) :
    (preferredOddStrategy G seat preferred s hwin).selectedMove =
      some preferred := by
  rw [preferredOddStrategy.eq_def]
  simp only [dif_neg ht, dif_neg hturn, OddStrategy.selectedMove]
  rw [preferredOddWinningChoice_move_eq G seat preferred s hwin ht hturn hp]

end PreferredOdd

/-! ## A four-label missed diamond -/

def positionalMissedCrossRel (x y : Fin 4) : Bool :=
  decide (x = 0 ∧ y = 1)

def positionalMissedCrossGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun x y ↦ positionalMissedCrossRel x y = true

def positionalMissedCrossParent : State (Fin 4) where
  untouched := {1, 2, 3}
  queue := [0]
  ko := false
  toMove := true
  score := 1

def positionalMissedCrossFan : State (Fin 4) where
  untouched := {2, 3}
  queue := [0, 1]
  ko := false
  toMove := false
  score := 1

def positionalMissedCrossClose : State (Fin 4) where
  untouched := {2, 3}
  queue := [1]
  ko := false
  toMove := true
  score := 1

def positionalMissedCrossDummy : State (Fin 4) where
  untouched := {3}
  queue := [0, 1, 2]
  ko := false
  toMove := true
  score := 1

def positionalMissedCrossCloseOpenThree : State (Fin 4) where
  untouched := {2}
  queue := [1, 3]
  ko := false
  toMove := false
  score := 1

def positionalMissedCrossDummyOpenThree : State (Fin 4) where
  untouched := ∅
  queue := [0, 1, 2, 3]
  ko := false
  toMove := false
  score := 1

theorem positionalMissedCross_dummyTwo :
    IsDummy positionalMissedCrossGraph 2 := by
  intro v
  fin_cases v <;>
    simp [positionalMissedCrossGraph, positionalMissedCrossRel,
      SimpleGraph.fromRel_adj]

theorem positionalMissedCross_parent_openOne :
    step positionalMissedCrossGraph positionalMissedCrossParent (.open 1) =
      some positionalMissedCrossFan := by
  simp [step, positionalMissedCrossParent, positionalMissedCrossFan]

theorem positionalMissedCross_fan_close :
    step positionalMissedCrossGraph positionalMissedCrossFan .close =
      some positionalMissedCrossClose := by
  simp [step, positionalMissedCrossFan, positionalMissedCrossClose,
    flip, positionalMissedCrossGraph, positionalMissedCrossRel,
    SimpleGraph.fromRel_adj]
  decide

theorem positionalMissedCross_fan_openDummy :
    step positionalMissedCrossGraph positionalMissedCrossFan (.open 2) =
      some positionalMissedCrossDummy := by
  simp [step, positionalMissedCrossFan, positionalMissedCrossDummy]

theorem positionalMissedCross_close_openThree :
    step positionalMissedCrossGraph positionalMissedCrossClose (.open 3) =
      some positionalMissedCrossCloseOpenThree := by
  simp [step, positionalMissedCrossClose,
    positionalMissedCrossCloseOpenThree]
  ext x
  fin_cases x <;> simp

theorem positionalMissedCross_dummy_openThree :
    step positionalMissedCrossGraph positionalMissedCrossDummy (.open 3) =
      some positionalMissedCrossDummyOpenThree := by
  simp [step, positionalMissedCrossDummy,
    positionalMissedCrossDummyOpenThree]

theorem positionalMissedCross_close_noLiveCut :
    NoLiveCut positionalMissedCrossGraph positionalMissedCrossClose := by
  intro u hu v hv
  fin_cases u <;> fin_cases v <;>
    simp [positionalMissedCrossClose, liveSet,
      positionalMissedCrossGraph, positionalMissedCrossRel,
      SimpleGraph.fromRel_adj] at hu hv ⊢

theorem positionalMissedCross_dummy_noLiveCut :
    NoLiveCut positionalMissedCrossGraph positionalMissedCrossDummy := by
  intro u hu v hv
  fin_cases u <;> fin_cases v <;>
    simp [positionalMissedCrossDummy, liveSet,
      positionalMissedCrossGraph, positionalMissedCrossRel,
      SimpleGraph.fromRel_adj] at hu hv ⊢

theorem positionalMissedCross_fan_noLiveCut :
    NoLiveCut positionalMissedCrossGraph positionalMissedCrossFan := by
  intro u hu v hv
  fin_cases u <;> fin_cases v <;>
    simp [positionalMissedCrossFan, liveSet,
      positionalMissedCrossGraph, positionalMissedCrossRel,
      SimpleGraph.fromRel_adj] at hu hv ⊢

theorem positionalMissedCross_parent_wellFormed :
    WellFormed positionalMissedCrossParent := by
  simp [WellFormed, positionalMissedCrossParent]

/-- The opener `1` has separator increment one: its unique graph neighbour is
the already queued debt vertex `0`. -/
theorem positionalMissedCross_parent_openOne_increment_one :
    publicSeparatorEvaluation 2
        (isolatedGraphSeparatorFunctional positionalMissedCrossGraph 2
          positionalMissedCross_dummyTwo)
        (moveLiveStar positionalMissedCrossParent (.open 1)) = 1 := by
  rw [publicSeparatorEvaluation_isolatedGraph]
  rw [graphEvaluation_moveLiveStar _ _ _
    positionalMissedCross_parent_wellFormed]
  simp [liveDegree, flip, queueCut, positionalMissedCrossParent,
    positionalMissedCrossGraph, positionalMissedCrossRel,
    SimpleGraph.fromRel_adj]
  decide

/-- Once `1` joins the queue, every legal child edge of the complete fan has
separator increment zero.  The unit bit has become pure queued debt. -/
theorem positionalMissedCross_fan_all_increments_zero
    (m : Move (Fin 4)) (u : PublicState (Fin 4))
    (hstep : publicStep positionalMissedCrossFan.public m = some u) :
    publicSeparatorEvaluation 2
        (isolatedGraphSeparatorFunctional positionalMissedCrossGraph 2
          positionalMissedCross_dummyTwo)
        (moveLiveStar positionalMissedCrossFan m) = 0 := by
  rw [publicSeparatorEvaluation_isolatedGraph]
  cases m with
  | close => simp [moveLiveStar]
  | pass => simp [moveLiveStar]
  | «open» v =>
      fin_cases v <;>
        simp [publicStep, State.public, positionalMissedCrossFan,
          moveLiveStar, graphEvaluation_liveStarVector, liveSet, flip,
          positionalMissedCrossGraph, positionalMissedCrossRel,
          SimpleGraph.fromRel_adj] at hstep ⊢

theorem positionalMissedCross_close_odd :
    OddWins positionalMissedCrossGraph false positionalMissedCrossClose :=
  oddWins_of_noLiveCut false positionalMissedCrossClose
    positionalMissedCross_close_noLiveCut (by decide)

theorem positionalMissedCross_dummy_odd :
    OddWins positionalMissedCrossGraph false positionalMissedCrossDummy :=
  oddWins_of_noLiveCut false positionalMissedCrossDummy
    positionalMissedCross_dummy_noLiveCut (by decide)

theorem positionalMissedCross_fan_odd :
    OddWins positionalMissedCrossGraph false positionalMissedCrossFan :=
  oddWins_of_noLiveCut false positionalMissedCrossFan
    positionalMissedCross_fan_noLiveCut (by decide)

def positionalMissedCrossFanPolicy :
    OddStrategy positionalMissedCrossGraph false positionalMissedCrossFan :=
  PreferredOdd.preferredOddStrategy positionalMissedCrossGraph false
    (.open 3) positionalMissedCrossFan positionalMissedCross_fan_odd

/-- The preceding unit opener is itself an exact odd-winning Bellman choice
whose child is the complete defender fan used below. -/
def positionalMissedCross_selectedOpenStrategy :
    OddStrategy positionalMissedCrossGraph false
      positionalMissedCrossParent :=
  .choose positionalMissedCrossParent (by decide) (.open 1)
    positionalMissedCrossFan positionalMissedCross_parent_openOne
    positionalMissedCrossFanPolicy

theorem positionalMissedCross_selectedOpenStrategy_move :
    positionalMissedCross_selectedOpenStrategy.selectedMove =
      some (.open 1) := rfl

/-- The entire selected-OPEN tree, including its complete fan, is positional
on full concrete states.  The outer root cannot recur because its unique
edge strictly decreases rank; every lower occurrence lies in the memoized
preferred fan. -/
theorem positionalMissedCross_selectedOpenStrategy_subtree_unique
    {s : State (Fin 4)}
    (left right : OddStrategy positionalMissedCrossGraph false s)
    (hleft : StrategyNode positionalMissedCrossGraph false
      positionalMissedCross_selectedOpenStrategy left)
    (hright : StrategyNode positionalMissedCrossGraph false
      positionalMissedCross_selectedOpenStrategy right) :
    left = right := by
  cases hleft with
  | root =>
      cases hright with
      | root => rfl
      | @choose _ _ _ _ _ hstep _ _ hdesc =>
          have hlt := lt_of_le_of_lt hdesc.rank_le (rank_step_lt hstep)
          exact False.elim (Nat.lt_irrefl _ hlt)
  | @choose _ _ _ _ _ hstep _ _ hleftDesc =>
      cases hright with
      | root =>
          have hlt := lt_of_le_of_lt hleftDesc.rank_le (rank_step_lt hstep)
          exact False.elim (Nat.lt_irrefl _ hlt)
      | @choose _ _ _ _ _ _ _ _ hrightDesc =>
          exact PreferredOdd.preferredOddStrategy_subtree_unique
            positionalMissedCrossGraph false (.open 3)
              positionalMissedCrossFan positionalMissedCross_fan_odd
              left right hleftDesc hrightDesc

theorem positionalMissedCross_parent_potential_zero :
    potential positionalMissedCrossGraph positionalMissedCrossParent = 0 := by
  simp [potential, queueCut, flip, positionalMissedCrossParent,
    positionalMissedCrossGraph, positionalMissedCrossRel,
    SimpleGraph.fromRel_adj]
  decide

theorem positionalMissedCross_fan_potential_one :
    potential positionalMissedCrossGraph positionalMissedCrossFan = 1 := by
  simp [potential, queueCut, flip, positionalMissedCrossFan,
    positionalMissedCrossGraph, positionalMissedCrossRel,
    SimpleGraph.fromRel_adj]
  decide

theorem positionalMissedCross_fan_wellFormed :
    WellFormed positionalMissedCrossFan := by
  simp [WellFormed, positionalMissedCrossFan]

/-- The exact selected-OPEN strategy is on separator sheet one. -/
theorem positionalMissedCross_selectedOpenStrategy_sheet_one :
    PublicPolicySeparatorSheet 2
      (isolatedGraphSeparatorFunctional positionalMissedCrossGraph 2
        positionalMissedCross_dummyTwo) false
      positionalMissedCross_selectedOpenStrategy.toPublicPolicy 1 := by
  exact (positionalMissedCross_selectedOpenStrategy.toPublicPolicy_separatorOne_iff_potential_zero
    positionalMissedCross_dummyTwo positionalMissedCross_parent_wellFormed).2
      positionalMissedCross_parent_potential_zero

/-- Its complete-fan child is uniformly on sheet zero. -/
theorem positionalMissedCross_fanPolicy_sheet_zero :
    PublicPolicySeparatorSheet 2
      (isolatedGraphSeparatorFunctional positionalMissedCrossGraph 2
        positionalMissedCross_dummyTwo) false
      positionalMissedCrossFanPolicy.toPublicPolicy 0 := by
  have hcanonical := positionalMissedCrossFanPolicy.toPublicPolicy_canonicalSeparatorSheet
    positionalMissedCross_dummyTwo positionalMissedCross_fan_wellFormed
  simpa [positionalMissedCross_fan_potential_one,
    CharTwo.add_self_eq_zero] using hcanonical

/-- The displayed selected OPEN is already an immediate separator-one
minimum, and it has the stronger rank-minimum local consequence that every
legal edge of its complete child fan has increment zero. -/
theorem positionalMissedCross_selectedOpenStrategy_immediateMinimal :
    PublicPolicySeparatorOneImmediateMinimal 2
      (isolatedGraphSeparatorFunctional positionalMissedCrossGraph 2
        positionalMissedCross_dummyTwo) false
      positionalMissedCross_selectedOpenStrategy.toPublicPolicy := by
  refine ⟨positionalMissedCross_selectedOpenStrategy_sheet_one, ?_⟩
  intro hchildOne
  obtain ⟨z, hz⟩ := positionalMissedCrossFanPolicy.toPublicPolicy.exists_affineMoment
  have hzero := positionalMissedCross_fanPolicy_sheet_zero z hz
  have hone := hchildOne z hz
  exact zero_ne_one (hzero.symm.trans hone)

omit [Fintype V] in
/-- No-live-cut, score, and well-formedness invariants propagate to every
exact descendant occurrence of one strategy. -/
theorem StrategyNode.noLiveCut_score_wellFormed
    {G : SimpleGraph V} {seat : Bool} {s t : State V}
    {root : OddStrategy G seat s} {desc : OddStrategy G seat t}
    (hnode : StrategyNode G seat root desc)
    (hcut : NoLiveCut G s) (hscore : s.score = 1)
    (hWF : WellFormed s) :
    NoLiveCut G t ∧ t.score = 1 ∧ WellFormed t := by
  induction hnode with
  | root => exact ⟨hcut, hscore, hWF⟩
  | @choose s s' t hseat m hstep child desc hdesc ih =>
      exact ih (noLiveCut_step hcut hstep)
        ((noLiveCut_step_score_eq hcut hstep).trans hscore)
        (wellFormed_step hWF hstep)
  | @answer s s' t hseat hasMove children m hstep desc hdesc ih =>
      exact ih (noLiveCut_step hcut hstep)
        ((noLiveCut_step_score_eq hcut hstep).trans hscore)
        (wellFormed_step hWF hstep)

omit [Fintype V] in
/-- A well-formed no-live-cut state has zero queue cut. -/
theorem queueCut_eq_zero_of_noLiveCut
    {G : SimpleGraph V} {s : State V}
    (hcut : NoLiveCut G s) (hWF : WellFormed s) :
    queueCut G s.untouched s.queue = 0 := by
  classical
  have hflip : ∀ z ∈ s.untouched, flip G (liveSet s) z = 0 := by
    intro z hz
    rw [flip]
    have hempty : (liveSet s).filter (G.Adj z) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro w hw
      exact hcut z hz w hw
    rw [hempty]
    simp
  have hsum := sum_flip_union_queue_eq_queueCut G hWF.1 hWF.2.symm
  have hsumZero :
      (∑ z ∈ s.untouched, flip G
        (s.untouched ∪ s.queue.toFinset) z) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    exact hflip z hz
  rw [hsumZero] at hsum
  exact hsum.symm

/-- Every proper concrete descendant below the displayed selected OPEN is
on separator sheet zero.  This is the strategy-level rank-minimal statement:
the countermodel does not hide a lower sheet-one occurrence in its exact odd
tree. -/
theorem positionalMissedCross_properDescendants_sheet_zero
    {t : State (Fin 4)}
    (desc : OddStrategy positionalMissedCrossGraph false t)
    (hnode : StrategyNode positionalMissedCrossGraph false
      positionalMissedCross_selectedOpenStrategy desc)
    (hlt : rank t < rank positionalMissedCrossParent) :
    PublicPolicySeparatorSheet 2
      (isolatedGraphSeparatorFunctional positionalMissedCrossGraph 2
        positionalMissedCross_dummyTwo) false desc.toPublicPolicy 0 := by
  cases hnode with
  | root => exact False.elim (Nat.lt_irrefl _ hlt)
  | @choose _ _ _ _ _ _ _ _ hdesc =>
      have hinv := hdesc.noLiveCut_score_wellFormed
        positionalMissedCross_fan_noLiveCut rfl
        positionalMissedCross_fan_wellFormed
      have hcutZero := queueCut_eq_zero_of_noLiveCut hinv.1 hinv.2.2
      have hpotential : potential positionalMissedCrossGraph t = 1 := by
        simp [potential, hinv.2.1, hcutZero]
      have hsheet := desc.toPublicPolicy_canonicalSeparatorSheet
        positionalMissedCross_dummyTwo hinv.2.2
      simpa [hpotential, CharTwo.add_self_eq_zero] using hsheet

/-- The two missed crossing choices occur inside the same complete fan of the
same positional strategy, rather than in separately selected local trees. -/
theorem positionalMissedCross_sameFan_misses_both_crossings :
    ∃ (hturn : positionalMissedCrossFan.toMove = false)
      (hasMove : ∃ m t,
        step positionalMissedCrossGraph positionalMissedCrossFan m = some t)
      (children : ∀ m t,
        step positionalMissedCrossGraph positionalMissedCrossFan m = some t →
          OddStrategy positionalMissedCrossGraph false t),
      positionalMissedCrossFanPolicy =
          .answer positionalMissedCrossFan hturn hasMove children ∧
        (children .close positionalMissedCrossClose
            positionalMissedCross_fan_close).selectedMove =
          some (.open 3) ∧
        (children (.open 2) positionalMissedCrossDummy
            positionalMissedCross_fan_openDummy).selectedMove =
          some (.open 3) := by
  have ht : ¬Terminal positionalMissedCrossFan := by
    simp [Terminal, positionalMissedCrossFan]
  have hturn : positionalMissedCrossFan.toMove = false := rfl
  rw [positionalMissedCrossFanPolicy,
    PreferredOdd.preferredOddStrategy.eq_def]
  simp only [dif_neg ht, dif_pos hturn]
  let hasMove : ∃ m t,
      step positionalMissedCrossGraph positionalMissedCrossFan m = some t :=
    not_terminal_has_step ht
  let children : ∀ m t,
      step positionalMissedCrossGraph positionalMissedCrossFan m = some t →
        OddStrategy positionalMissedCrossGraph false t :=
    fun m t hstep ↦ PreferredOdd.preferredOddStrategy
      positionalMissedCrossGraph false (.open 3) t
        (positionalMissedCross_fan_odd.answer_child hturn hstep)
  refine ⟨hturn, hasMove, children, rfl, ?_, ?_⟩
  · apply PreferredOdd.preferredOddStrategy_selectedMove_eq
      positionalMissedCrossGraph false (.open 3) positionalMissedCrossClose
        (positionalMissedCross_fan_odd.answer_child hturn
          positionalMissedCross_fan_close)
        (by simp [Terminal, positionalMissedCrossClose]) (by decide)
    exact ⟨positionalMissedCrossCloseOpenThree,
      positionalMissedCross_close_openThree,
      oddWins_of_noLiveCut false positionalMissedCrossCloseOpenThree
        (noLiveCut_step positionalMissedCross_close_noLiveCut
          positionalMissedCross_close_openThree) (by decide)⟩
  · apply PreferredOdd.preferredOddStrategy_selectedMove_eq
      positionalMissedCrossGraph false (.open 3) positionalMissedCrossDummy
        (positionalMissedCross_fan_odd.answer_child hturn
          positionalMissedCross_fan_openDummy)
        (by simp [Terminal, positionalMissedCrossDummy]) (by decide)
    exact ⟨positionalMissedCrossDummyOpenThree,
      positionalMissedCross_dummy_openThree,
      oddWins_of_noLiveCut false positionalMissedCrossDummyOpenThree
        (noLiveCut_step positionalMissedCross_dummy_noLiveCut
          positionalMissedCross_dummy_openThree) (by decide)⟩

/-- Both attacker children of the local defender fan are odd-winning, but a
single full-state positional Bellman rule selects `OPEN 3` at both.  Hence it
selects neither crossing edge of the isolated-dummy OPEN/CLOSE diamond. -/
theorem positionalOddWins_can_miss_both_crossing_edges :
    let closePolicy := PreferredOdd.preferredOddStrategy
      positionalMissedCrossGraph false (.open 3)
      positionalMissedCrossClose positionalMissedCross_close_odd
    let dummyPolicy := PreferredOdd.preferredOddStrategy
      positionalMissedCrossGraph false (.open 3)
      positionalMissedCrossDummy positionalMissedCross_dummy_odd
    closePolicy.selectedMove = some (.open 3) ∧
      dummyPolicy.selectedMove = some (.open 3) ∧
      closePolicy.selectedMove ≠ some (.open 2) ∧
      dummyPolicy.selectedMove ≠ some .close := by
  dsimp only
  have hcloseWin : OddWins positionalMissedCrossGraph false
      positionalMissedCrossCloseOpenThree :=
    oddWins_of_noLiveCut false positionalMissedCrossCloseOpenThree
      (noLiveCut_step positionalMissedCross_close_noLiveCut
        positionalMissedCross_close_openThree) (by decide)
  have hdummyWin : OddWins positionalMissedCrossGraph false
      positionalMissedCrossDummyOpenThree :=
    oddWins_of_noLiveCut false positionalMissedCrossDummyOpenThree
      (noLiveCut_step positionalMissedCross_dummy_noLiveCut
        positionalMissedCross_dummy_openThree) (by decide)
  have hclose := PreferredOdd.preferredOddStrategy_selectedMove_eq
    positionalMissedCrossGraph false (.open 3) positionalMissedCrossClose
      positionalMissedCross_close_odd
      (by simp [Terminal, positionalMissedCrossClose]) (by decide)
      ⟨positionalMissedCrossCloseOpenThree,
        positionalMissedCross_close_openThree, hcloseWin⟩
  have hdummy := PreferredOdd.preferredOddStrategy_selectedMove_eq
    positionalMissedCrossGraph false (.open 3) positionalMissedCrossDummy
      positionalMissedCross_dummy_odd
      (by simp [Terminal, positionalMissedCrossDummy]) (by decide)
      ⟨positionalMissedCrossDummyOpenThree,
        positionalMissedCross_dummy_openThree, hdummyWin⟩
  exact ⟨hclose, hdummy, by simp [hclose], by simp [hdummy]⟩

end

end Ogdoad.Fifo
