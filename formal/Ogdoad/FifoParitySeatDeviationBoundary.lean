import Ogdoad.FifoParitySeatCloseFirst

/-!
# The leafmost clear-deviation boundary

The dummy-free parity-seat normalization forces every alleged odd strategy
to deviate from CLOSE-first play at some clear attacker node.  Descending to
the last such deviation makes its selected child CLOSE-first.  This file
records the exact Bellman obstruction at that point.

The deviation cannot be PASS because the queue is clear and nonempty, and it
is not CLOSE by definition, so it is an OPEN.  Its child is therefore a
coherent clear defender state.  The conditioned CLOSE-first theorem then
forces both ends of the OPEN onto score sheet one.  Consequently the natural
leafmost-deviation descent does not produce a smaller score-zero
counterstrategy; eliminating it still requires information from the earlier
defender ancestry fan.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A last clear deviation: the displayed non-CLOSE attacker move has a
CLOSE-first selected child. -/
def LeafmostClearDeviation
    (G : SimpleGraph V) (seat : Bool) (root : State V)
    (hroot : OddWins G seat root) : Prop :=
  ∃ (s t : State V) (m : Move V) (hchild : OddWins G seat t),
    InOddStrategy G seat hroot s ∧
      s.toMove ≠ seat ∧ step G s m = some t ∧
      Clear s ∧ m ≠ .close ∧ OddStrategyCloseFirst hchild

omit [Fintype V] in
/-- Every displayed clear deviation has a last one: recursively descend when
its selected child still contains a deviation, and otherwise retain the
current node.  The witness stays inside the original strategy tree. -/
theorem OddStrategyHasClearDeviation.exists_leafmost
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddWins G seat root}
    (hdev : OddStrategyHasClearDeviation hroot) :
    LeafmostClearDeviation G seat root hroot := by
  induction root using (measure rank).wf.induction with
  | h root ih =>
      cases hdev with
      | here s hseat m t hstep hchild hclear hm =>
          rcases oddStrategy_deviation_or_closeFirst hchild with
            hchildDev | hchildClose
          · rcases ih t (rank_step_lt hstep) hchildDev with
              ⟨u, w, move, tail, hmem, huturn, hustep, huclear,
                humove, hutail⟩
            exact ⟨u, w, move, tail,
              InOddStrategy.choose (hseat := hseat) (m := m)
                (hstep := hstep) hmem,
              huturn, hustep, huclear, humove, hutail⟩
          · exact ⟨root, t, m, hchild, InOddStrategy.root _, hseat, hstep,
              hclear, hm, hchildClose⟩
      | @choose s t hseat m hstep hchild tail =>
          rcases ih t (rank_step_lt hstep) tail with
            ⟨u, w, move, htail, hmem, huturn, hustep, huclear,
              humove, huclose⟩
          exact ⟨u, w, move, htail,
            InOddStrategy.choose (hseat := hseat) (m := m)
              (hstep := hstep) hmem,
            huturn, hustep, huclear, humove, huclose⟩
      | @answer s t hseat hasMove hchildren m hstep tail =>
          rcases ih t (rank_step_lt hstep) tail with
            ⟨u, w, move, htail, hmem, huturn, hustep, huclear,
              humove, huclose⟩
          exact ⟨u, w, move, htail,
            InOddStrategy.answer (hseat := hseat) (hasMove := hasMove)
              (hchildren := hchildren) (m := m) (hstep := hstep) hmem,
            huturn, hustep, huclear, humove, huclose⟩

omit [Fintype V] in
/-- Coherence propagates to every public state occurring in a displayed odd
strategy tree. -/
theorem InOddStrategy.coherent
    {G : SimpleGraph V} {seat : Bool} {root t : State V}
    {hroot : OddWins G seat root}
    (ht : InOddStrategy G seat hroot t) (hrootCoherent : Coherent root) :
    Coherent t := by
  induction ht with
  | root => exact hrootCoherent
  | @choose s s' t hseat m hstep hchild ht ih =>
      exact ih (coherent_step hrootCoherent hstep)
  | @answer s s' t hseat hasMove hchildren m hstep ht ih =>
      exact ih (coherent_step hrootCoherent hstep)

/-- The Bellman obstruction at a last clear deviation.  The selected move is
an OPEN, and both its source and its CLOSE-first child have score one. -/
theorem leafmostClearDeviation_open_score_one
    {G : SimpleGraph V} {seat : Bool} {s t : State V} {m : Move V}
    (hseat : s.toMove ≠ seat) (hstep : step G s m = some t)
    (hclear : Clear s) (hm : m ≠ .close)
    {hchild : OddWins G seat t} (hclose : OddStrategyCloseFirst hchild)
    (hcoherent : Coherent s) :
    ∃ v, m = .open v ∧ s.score = 1 ∧ t.score = 1 := by
  cases m with
  | close => exact False.elim (hm rfl)
  | pass =>
      simp only [step] at hstep
      split at hstep
      · rename_i hpass
        exact False.elim (Bool.false_ne_true (hclear.2.symm.trans hpass.2.2))
      · contradiction
  | «open» v =>
      have htCoherent : Coherent t := coherent_step hcoherent hstep
      have htTurn : t.toMove = seat := by
        rw [step_toMove hstep, Bool.eq_not_iff.mpr hseat]
        simp
      have htQueue : t.queue ≠ [] := by
        simp only [step] at hstep
        split at hstep
        · cases hstep
          exact List.append_ne_nil_of_right_ne_nil s.queue (by simp)
        · contradiction
      have htKo : t.ko = false := by
        simp only [step] at hstep
        split at hstep
        · cases hstep
          exact List.isEmpty_eq_false_iff.mpr hclear.1
        · contradiction
      have htNonzero : t.score ≠ 0 := by
        intro htZero
        have hnot := ConditionedCloseFirstTheorem
          V inferInstance inferInstance G (!seat) t htCoherent
            (by simp [htTurn]) htQueue htKo
        apply hnot
        simpa [htZero] using hclose.toCloseFirstWins
      have htOne : t.score = 1 := zmod2_eq_one_of_ne_zero _ htNonzero
      exact ⟨v, rfl, (open_score hstep).symm.trans htOne, htOne⟩

/-- A leafmost deviation below a coherent root is therefore an OPEN between
two score-one states, with a CLOSE-first tail. -/
theorem LeafmostClearDeviation.exists_open_score_one
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddWins G seat root}
    (hleaf : LeafmostClearDeviation G seat root hroot)
    (hrootCoherent : Coherent root) :
    ∃ (s t : State V) (v : V) (hchild : OddWins G seat t),
      InOddStrategy G seat hroot s ∧ s.toMove ≠ seat ∧
        step G s (.open v) = some t ∧ Clear s ∧
        s.score = 1 ∧ t.score = 1 ∧ OddStrategyCloseFirst hchild := by
  rcases hleaf with
    ⟨s, t, m, hchild, hmem, hturn, hstep, hclear, hm, hclose⟩
  obtain ⟨v, rfl, hsOne, htOne⟩ :=
    leafmostClearDeviation_open_score_one hturn hstep hclear hm hclose
      (hmem.coherent hrootCoherent)
  exact ⟨s, t, v, hchild, hmem, hturn, hstep, hclear, hsOne, htOne,
    hclose⟩

/-- Exact parity-seat consequence.  Every hypothetical counterstrategy has a
leafmost selected OPEN on score sheet one.  Hence the obvious recursive plan
cannot restart the original score-zero parity problem at that smaller child. -/
theorem paritySeatCounterstrategy_has_leafmost_open_score_one
    (G : SimpleGraph V) (seat : Bool)
    (hseat : (Odd (Fintype.card V) ∧ seat = false) ∨
      (Even (Fintype.card V) ∧ seat = true))
    (h : OddWins G seat (initial (V := V))) :
    ∃ (s t : State V) (v : V) (hchild : OddWins G seat t),
      InOddStrategy G seat h s ∧ s.toMove ≠ seat ∧
        step G s (.open v) = some t ∧ Clear s ∧
        s.score = 1 ∧ t.score = 1 ∧ OddStrategyCloseFirst hchild := by
  exact
    (paritySeatCounterstrategy_has_clearDeviation G seat hseat h).exists_leafmost
      |>.exists_open_score_one coherent_initial

end

end Ogdoad.Fifo
