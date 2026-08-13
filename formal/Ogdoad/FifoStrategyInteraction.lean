import Ogdoad.FifoNeutralPair

/-!
# Interaction of complementary-seat odd strategies

Two odd strategies for complementary designated seats are not contradictory.
At every nonterminal state, exactly one of them supplies the selected move and
the other supplies the matching universal child.  Following that common edge
recursively reaches one terminal node belonging to both exact strategy trees,
and both trees require the same odd terminal score.

This is a symmetry/diagonal no-go theorem, not a FIFO linking theorem.  To
obtain a contradiction one needs opposite terminal targets at the same score
sheet; merely complementing the designated seat preserves the odd target.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Exact common terminal descendant of two odd strategies controlled by the
two complementary physical players. -/
theorem OddStrategy.exists_common_terminal
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (left : OddStrategy G seat s)
    (right : OddStrategy G (!seat) s) :
    ∃ (t : State V)
      (leftTail : OddStrategy G seat t)
      (rightTail : OddStrategy G (!seat) t),
      StrategyNode G seat left leftTail ∧
      StrategyNode G (!seat) right rightTail ∧
      Terminal t ∧ t.score ≠ 0 := by
  induction s using (measure rank).wf.induction with
  | h s ih =>
      cases left with
      | terminal _ hterminal hscore =>
          exact ⟨s, .terminal s hterminal hscore, right,
            StrategyNode.root _, StrategyNode.root _, hterminal, hscore⟩
      | choose _ hleftSeat m t hstep leftTail =>
          cases right with
          | terminal _ hterminal _ =>
              exact False.elim
                (terminal_no_step hterminal ⟨m, t, hstep⟩)
          | choose _ hrightSeat _ _ _ _ =>
              have hturn : s.toMove = !seat := Bool.eq_not_iff.mpr hleftSeat
              exact False.elim (hrightSeat (by simp [hturn]))
          | answer _ hrightSeat _ children =>
              let rightTail := children m t hstep
              obtain ⟨u, leftEnd, rightEnd,
                  hleftNode, hrightNode, hterminal, hscore⟩ :=
                ih t (rank_step_lt hstep) leftTail rightTail
              exact ⟨u, leftEnd, rightEnd,
                StrategyNode.choose hleftNode,
                StrategyNode.answer hrightNode,
                hterminal, hscore⟩
      | answer _ hleftSeat hasMove children =>
          cases right with
          | terminal _ hterminal _ =>
              obtain ⟨m, t, hstep⟩ := hasMove
              exact False.elim
                (terminal_no_step hterminal ⟨m, t, hstep⟩)
          | choose _ hrightSeat m t hstep rightTail =>
              let leftTail := children m t hstep
              obtain ⟨u, leftEnd, rightEnd,
                  hleftNode, hrightNode, hterminal, hscore⟩ :=
                ih t (rank_step_lt hstep) leftTail rightTail
              exact ⟨u, leftEnd, rightEnd,
                StrategyNode.answer hleftNode,
                StrategyNode.choose hrightNode,
                hterminal, hscore⟩
          | answer _ hrightSeat _ _ =>
              have hturn : s.toMove = seat := hleftSeat
              exact False.elim (by
                have : s.toMove ≠ seat := by
                  simpa using Bool.eq_not_iff.mp hrightSeat
                exact this hturn)

end

end Ogdoad.Fifo
