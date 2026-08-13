import Ogdoad.FifoOddSpikeFactor

/-!
# The dummy sibling of a charged-CLOSE spike

At the remaining charged-CLOSE predecessor, the complete same-root fan
contains the sibling which OPENs an untouched isolated dummy.  The exact
first-response classification forces the selected reply in that sibling to
be a real OPEN adjacent to the old queue front.  It cannot be CLOSE, because
the close case would make the dummy adjacent to both spike fronts.

This is a structural restriction on the separator-dual strategy, not yet a
contraction of its branch-dependent continuation spaces.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A row-zero source cannot select CLOSE and must OPEN a row-one target. -/
theorem OddSpikeOpenReplyCase.of_row_zero
    {G : SimpleGraph V} {U : Finset V} {y f z : V} {m : Move V}
    (hcase : OddSpikeOpenReplyCase G U y f z m)
    (hyz : adjacencyBit G y z = 0) :
    ∃ w, m = .open w ∧ w ∈ U.erase z ∧
      adjacencyBit G y w = 1 := by
  cases hcase with
  | close hyzOne hfz =>
      exact False.elim (by rw [hyz] at hyzOne; exact zero_ne_one hyzOne)
  | «open» w hw hrow =>
      have hyw : adjacencyBit G y w = 1 := by simpa [hyz] using hrow
      exact ⟨w, rfl, hw, hyw⟩

omit [Fintype V] in
/-- At a row-one source, the charged-spike reply either exits by CLOSE
through the second spike row, or OPENs a row-zero target. -/
theorem OddSpikeOpenReplyCase.of_row_one
    {G : SimpleGraph V} {U : Finset V} {y f z : V} {m : Move V}
    (hcase : OddSpikeOpenReplyCase G U y f z m)
    (hyz : adjacencyBit G y z = 1) :
    (m = .close ∧ adjacencyBit G f z = 1) ∨
      ∃ w, m = .open w ∧ w ∈ U.erase z ∧
        adjacencyBit G y w = 0 := by
  cases hcase with
  | close _ hfz => exact Or.inl ⟨rfl, hfz⟩
  | «open» w hw hrow =>
      have hyw : adjacencyBit G y w = 0 := by
        rw [hyz] at hrow
        have := congrArg (fun a : ZMod 2 ↦ (1 : ZMod 2) + a) hrow
        simpa [add_assoc] using this
      exact Or.inr ⟨w, rfl, hw, hyw⟩

/-- In the isolated-dummy sibling of a charged-CLOSE spike, the counterpolicy
must select a real neighbour of the old queue front. -/
theorem MinimalBadPredecessorCase.chargedClose_dummySibling_selects_neighbor
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d) {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    {s parent : State V} {pp : EdgeVector V} {f : V} {q : List V}
    (hparentTurn : parent.toMove = seat)
    (hfan : ∀ m t, step G parent m = some t →
      ∃ childTree : OddStrategy G seat t,
        StrategyPrefix G seat root childTree
          (pp + moveLiveStar parent m))
    (hincoming : step G parent .close = some s)
    (hminimal : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat root desc →
      rank t < rank s → t.score ≠ 0)
    (hcase : MinimalBadPredecessorCase G parent s f q .close)
    (hfcharge : flip G s.untouched f = 1)
    (hdU : d ∈ parent.untouched) :
    ∃ (y w : V) (sd : State V)
        (sdTree : OddStrategy G seat sd),
      parent.queue = y :: f :: q ∧
      step G parent (.open d) = some sd ∧
      StrategyPrefix G seat root sdTree
        (pp + moveLiveStar parent (.open d)) ∧
      (∀ {t : State V} {desc : OddStrategy G seat t},
        StrategyNode G seat sdTree desc → t.score = 1) ∧
      sdTree.selectedMove = some (.open w) ∧
      w ∈ parent.untouched.erase d ∧
      adjacencyBit G y w = 1 := by
  obtain ⟨y, sd, sdTree, hqueue, hopen, hprefix, hone,
      m, hselected, hreply⟩ :=
    hcase.chargedClose_openSibling_replyCase hparentTurn hfan hincoming
      hminimal hfcharge hdU
  cases hreply with
  | close hyd hfd =>
      have hyd0 : adjacencyBit G y d = 0 := by
        simp [adjacencyBit, G.adj_comm, hd y]
      exact False.elim (by rw [hyd0] at hyd; exact zero_ne_one hyd)
  | «open» w hw hrow =>
      have hyd0 : adjacencyBit G y d = 0 := by
        simp [adjacencyBit, G.adj_comm, hd y]
      have hyw : adjacencyBit G y w = 1 := by
        simpa [hyd0] using hrow
      exact ⟨y, w, sd, sdTree, hqueue, hopen, hprefix, hone,
        hselected, hw, hyw⟩

end

end Ogdoad.Fifo
