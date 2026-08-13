import Ogdoad.FifoCrossExitIncidence

/-!
# The third-sibling selection boundary

The one-front-offset square compares a canonical front `CLOSE` child with an
earlier universal `OPEN` sibling.  Removing the remaining queue cell would
require the odd strategy at that earlier sibling to select `CLOSE`.  A
complete universal fan does not force this selected reply.

The countermodel below is entirely semantic: on the empty graph with score
one, every continuation is odd-winning.  One fixed defender node therefore
has a legal odd strategy whose canonical `CLOSE` child selects `OPEN 1`, while
both earlier `OPEN` siblings select the other `OPEN` rather than `CLOSE`.
All three subtrees occur in the same Type-valued strategy.  Thus the third
sibling needed by a cross-exit contraction cannot be obtained from fan
completeness alone; an additional causal selection principle is essential.

This is not a counterexample to isolated-dummy FIFO linking: the local root
starts on score one and is not an initial game state.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- On the empty graph every legal move preserves the accumulated score. -/
theorem bot_step_score_eq
    {s t : State V} {m : Move V}
    (hstep : step (⊥ : SimpleGraph V) s m = some t) :
    t.score = s.score := by
  cases m with
  | «open» v =>
      simp only [step] at hstep
      split at hstep
      · cases hstep
        rfl
      · contradiction
  | close =>
      simp only [step] at hstep
      split at hstep
      · contradiction
      · rename_i f q hqueue
        split at hstep
        · contradiction
        · cases hstep
          simp [flip]
  | pass =>
      simp only [step] at hstep
      split at hstep
      · cases hstep
        rfl
      · contradiction

omit [Fintype V] in
/-- Since the empty graph never changes the score, a nonzero score is an
odd terminal invariant and either physical player can force it. -/
theorem oddWins_bot_of_score_ne_zero
    (seat : Bool) (s : State V) (hscore : s.score ≠ 0) :
    OddWins (⊥ : SimpleGraph V) seat s := by
  induction s using (measure rank).wf.induction with
  | h s ih =>
      by_cases hterminal : Terminal s
      · exact OddWins.terminal s hterminal hscore
      · have hasMove : ∃ m t, step (⊥ : SimpleGraph V) s m = some t :=
          not_terminal_has_step hterminal
        by_cases hseat : s.toMove = seat
        · refine OddWins.answer s hseat hasMove ?_
          intro m t hstep
          have htScore : t.score ≠ 0 := by
            rw [bot_step_score_eq hstep]
            exact hscore
          exact ih t (rank_step_lt hstep) htScore
        · obtain ⟨m, t, hstep⟩ := hasMove
          have htScore : t.score ≠ 0 := by
            rw [bot_step_score_eq hstep]
            exact hscore
          exact OddWins.choose s hseat m t hstep
            (ih t (rank_step_lt hstep) htScore)

/-! ## A three-child countermodel inside one exact strategy -/

/-- Exact immediate-child membership at a defender (`answer`) node, retaining
the labelled move rather than only descendant-tree membership. -/
def ImmediateAnswerChild
    {G : SimpleGraph V} {seat : Bool} {s t : State V}
    (root : OddStrategy G seat s) (m : Move V)
    (child : OddStrategy G seat t) : Prop :=
  ∃ (hseat : s.toMove = seat)
    (hasMove : ∃ move next, step G s move = some next)
    (children : ∀ move next, step G s move = some next →
      OddStrategy G seat next)
    (hstep : step G s m = some t),
    root = OddStrategy.answer s hseat hasMove children ∧
      child = children m t hstep

private def threeSiblingParent : State (Fin 3) where
  untouched := {1, 2}
  queue := [0]
  ko := false
  toMove := false
  score := 1

private def threeSiblingClose : State (Fin 3) where
  untouched := {1, 2}
  queue := []
  ko := false
  toMove := true
  score := 1

private def threeSiblingCloseOpen : State (Fin 3) where
  untouched := {2}
  queue := [1]
  ko := true
  toMove := false
  score := 1

private def threeSiblingOpenOne : State (Fin 3) where
  untouched := {2}
  queue := [0, 1]
  ko := false
  toMove := true
  score := 1

private def threeSiblingOpenOneOpenTwo : State (Fin 3) where
  untouched := ∅
  queue := [0, 1, 2]
  ko := false
  toMove := false
  score := 1

private def threeSiblingOpenTwo : State (Fin 3) where
  untouched := {1}
  queue := [0, 2]
  ko := false
  toMove := true
  score := 1

private def threeSiblingOpenTwoOpenOne : State (Fin 3) where
  untouched := ∅
  queue := [0, 2, 1]
  ko := false
  toMove := false
  score := 1

/-- One exact odd strategy can contain the canonical exit child and both
earlier universal `OPEN` siblings while neither earlier sibling selects the
front `CLOSE`. -/
theorem exists_sameTree_crossExit_without_closeSelecting_openSibling :
    ∃ (root : OddStrategy (⊥ : SimpleGraph (Fin 3)) false
        threeSiblingParent)
      (closeChild : OddStrategy (⊥ : SimpleGraph (Fin 3)) false
        threeSiblingClose)
      (openOneChild : OddStrategy (⊥ : SimpleGraph (Fin 3)) false
        threeSiblingOpenOne)
      (openTwoChild : OddStrategy (⊥ : SimpleGraph (Fin 3)) false
        threeSiblingOpenTwo),
      StrategyNode (⊥ : SimpleGraph (Fin 3)) false root closeChild ∧
      StrategyNode (⊥ : SimpleGraph (Fin 3)) false root openOneChild ∧
      StrategyNode (⊥ : SimpleGraph (Fin 3)) false root openTwoChild ∧
      ImmediateAnswerChild root .close closeChild ∧
      ImmediateAnswerChild root (.open 1) openOneChild ∧
      ImmediateAnswerChild root (.open 2) openTwoChild ∧
      closeChild.selectedMove = some (.open 1) ∧
      openOneChild.selectedMove = some (.open 2) ∧
      openTwoChild.selectedMove = some (.open 1) := by
  let G : SimpleGraph (Fin 3) := ⊥
  have hclose : step G threeSiblingParent .close =
      some threeSiblingClose := by
    simp [G, step, threeSiblingParent, threeSiblingClose, flip]
  have hcloseOpen : step G threeSiblingClose (.open 1) =
      some threeSiblingCloseOpen := by
    simp [step, threeSiblingClose, threeSiblingCloseOpen]
  have hopenOne : step G threeSiblingParent (.open 1) =
      some threeSiblingOpenOne := by
    simp [step, threeSiblingParent, threeSiblingOpenOne]
  have hopenOneOpenTwo : step G threeSiblingOpenOne (.open 2) =
      some threeSiblingOpenOneOpenTwo := by
    simp [step, threeSiblingOpenOne, threeSiblingOpenOneOpenTwo]
  have hopenTwo : step G threeSiblingParent (.open 2) =
      some threeSiblingOpenTwo := by
    simp [step, threeSiblingParent, threeSiblingOpenTwo]
    decide
  have hopenTwoOpenOne : step G threeSiblingOpenTwo (.open 1) =
      some threeSiblingOpenTwoOpenOne := by
    simp [step, threeSiblingOpenTwo, threeSiblingOpenTwoOpenOne]
  let closeTail : OddStrategy G false threeSiblingCloseOpen :=
    Classical.choice
      ((oddWins_bot_of_score_ne_zero false threeSiblingCloseOpen (by decide)).nonempty_oddStrategy)
  let closeChild : OddStrategy G false threeSiblingClose :=
    OddStrategy.choose threeSiblingClose (by decide) (.open 1)
      threeSiblingCloseOpen hcloseOpen closeTail
  let openOneTail : OddStrategy G false threeSiblingOpenOneOpenTwo :=
    Classical.choice
      ((oddWins_bot_of_score_ne_zero false threeSiblingOpenOneOpenTwo (by decide)).nonempty_oddStrategy)
  let openOneChild : OddStrategy G false threeSiblingOpenOne :=
    OddStrategy.choose threeSiblingOpenOne (by decide) (.open 2)
      threeSiblingOpenOneOpenTwo hopenOneOpenTwo openOneTail
  let openTwoTail : OddStrategy G false threeSiblingOpenTwoOpenOne :=
    Classical.choice
      ((oddWins_bot_of_score_ne_zero false threeSiblingOpenTwoOpenOne (by decide)).nonempty_oddStrategy)
  let openTwoChild : OddStrategy G false threeSiblingOpenTwo :=
    OddStrategy.choose threeSiblingOpenTwo (by decide) (.open 1)
      threeSiblingOpenTwoOpenOne hopenTwoOpenOne openTwoTail
  let children : ∀ m t, step G threeSiblingParent m = some t →
      OddStrategy G false t := fun m t hstep ↦ by
    classical
    by_cases hmClose : m = .close
    · subst m
      have ht : t = threeSiblingClose := by
        rw [hclose] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact closeChild
    by_cases hmOne : m = .open 1
    · subst m
      have ht : t = threeSiblingOpenOne := by
        rw [hopenOne] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact openOneChild
    by_cases hmTwo : m = .open 2
    · subst m
      have ht : t = threeSiblingOpenTwo := by
        rw [hopenTwo] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact openTwoChild
    have htScore : t.score ≠ 0 := by
      rw [bot_step_score_eq hstep]
      decide
    exact Classical.choice
      ((oddWins_bot_of_score_ne_zero false t htScore).nonempty_oddStrategy)
  let hasMove : ∃ m t, step G threeSiblingParent m = some t :=
    ⟨.close, threeSiblingClose, hclose⟩
  let root : OddStrategy G false threeSiblingParent :=
    OddStrategy.answer threeSiblingParent rfl hasMove children
  have hcloseNode : StrategyNode G false root closeChild := by
    apply StrategyNode.answer (hstep := hclose)
    simpa [children] using (StrategyNode.root closeChild)
  have hopenOneNode : StrategyNode G false root openOneChild := by
    apply StrategyNode.answer (hstep := hopenOne)
    simpa [children] using (StrategyNode.root openOneChild)
  have hopenTwoNode : StrategyNode G false root openTwoChild := by
    apply StrategyNode.answer (hstep := hopenTwo)
    simpa [children] using (StrategyNode.root openTwoChild)
  have hcloseImmediate : ImmediateAnswerChild root .close closeChild := by
    refine ⟨rfl, hasMove, children, hclose, rfl, ?_⟩
    simp [children]
  have hopenOneImmediate :
      ImmediateAnswerChild root (.open 1) openOneChild := by
    refine ⟨rfl, hasMove, children, hopenOne, rfl, ?_⟩
    simp [children]
  have hopenTwoImmediate :
      ImmediateAnswerChild root (.open 2) openTwoChild := by
    refine ⟨rfl, hasMove, children, hopenTwo, rfl, ?_⟩
    simp [children]
  refine ⟨root, closeChild, openOneChild, openTwoChild,
    hcloseNode, hopenOneNode, hopenTwoNode,
    hcloseImmediate, hopenOneImmediate, hopenTwoImmediate, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

/-- Fan completeness alone does not imply that an earlier `OPEN` sibling
selects the front `CLOSE`, even when the canonical `CLOSE` child selects the
matching `OPEN`. -/
theorem not_every_sameTree_crossExit_has_closeSelecting_openSibling :
    ¬(∀ (root : OddStrategy (⊥ : SimpleGraph (Fin 3)) false
          threeSiblingParent)
        (closeChild : OddStrategy (⊥ : SimpleGraph (Fin 3)) false
          threeSiblingClose)
        (openOneChild : OddStrategy (⊥ : SimpleGraph (Fin 3)) false
          threeSiblingOpenOne)
        (openTwoChild : OddStrategy (⊥ : SimpleGraph (Fin 3)) false
          threeSiblingOpenTwo),
      ImmediateAnswerChild root .close closeChild →
      ImmediateAnswerChild root (.open 1) openOneChild →
      ImmediateAnswerChild root (.open 2) openTwoChild →
      closeChild.selectedMove = some (.open 1) →
      openOneChild.selectedMove = some .close ∨
        openTwoChild.selectedMove = some .close) := by
  intro hall
  obtain ⟨root, closeChild, openOneChild, openTwoChild,
      hcloseNode, hopenOneNode, hopenTwoNode,
      hcloseImmediate, hopenOneImmediate, hopenTwoImmediate,
      hcloseSelect, hopenOneSelect, hopenTwoSelect⟩ :=
    exists_sameTree_crossExit_without_closeSelecting_openSibling
  have h := hall root closeChild openOneChild openTwoChild
    hcloseImmediate hopenOneImmediate hopenTwoImmediate hcloseSelect
  rcases h with h | h
  · rw [hopenOneSelect] at h
    cases h
  · rw [hopenTwoSelect] at h
    cases h

end

end Ogdoad.Fifo
