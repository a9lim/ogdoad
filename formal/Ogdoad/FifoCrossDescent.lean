import Ogdoad.FifoAffine

/-!
# Same-tree crossed response descent

This file isolates one genuinely causal induction step for the open FIFO
linking problem.  Two holes must belong to the same explicit Type-valued
`OddStrategy` tree.  If their selected attacker moves are OPENs and the two
universal defender nodes contain the crossed OPEN replies, those replies give
two smaller holes in that same tree.

The theorem is deliberately conditional.  It does not say that the two holes
exist, that their selected moves are OPENs, or that a mixed OPEN/CLOSE boundary
can be absorbed.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Two queues differ by reversing every consecutive response cell. -/
inductive CellSwap : List V → List V → Prop
  | nil : CellSwap [] []
  | cell (a b : V) {q q' : List V} (tail : CellSwap q q') :
      CellSwap (a :: b :: q) (b :: a :: q')

omit [Fintype V] [DecidableEq V] in
/-- Crossed OPEN replies append one new reversed cell. -/
theorem CellSwap.append_cross {q q' : List V} (h : CellSwap q q')
    (z w : V) : CellSwap (q ++ [z, w]) (q' ++ [w, z]) := by
  induction h with
  | nil => exact CellSwap.cell z w CellSwap.nil
  | cell a b tail ih =>
      simpa only [List.cons_append] using CellSwap.cell a b ih

omit [Fintype V] [DecidableEq V] in
/-- Crossed CLOSE replies delete the first reversed cell. -/
theorem CellSwap.tail_of_cell {a b : V} {q q' : List V}
    (h : CellSwap (a :: b :: q) (b :: a :: q')) : CellSwap q q' := by
  cases h with
  | cell _ _ tail => exact tail

/-- The public relation transported by crossed response descent. -/
structure PublicCellSwap (s t : State V) : Prop where
  untouched : s.untouched = t.untouched
  queue : CellSwap s.queue t.queue
  ko : s.ko = t.ko
  toMove : s.toMove = t.toMove
  score : s.score = t.score

/-- The explicit state produced by opening `v`, without its legality premise. -/
private def openSuccessor (s : State V) (v : V) : State V where
  untouched := s.untouched.erase v
  queue := s.queue ++ [v]
  ko := s.queue.isEmpty
  toMove := !s.toMove
  score := s.score

omit [Fintype V] in
private theorem eq_openSuccessor_of_step {G : SimpleGraph V}
    {s t : State V} {v : V} (h : step G s (.open v) = some t) :
    t = openSuccessor s v := by
  simp only [step] at h
  split at h
  · cases h
    rfl
  · contradiction

omit [Fintype V] in
/-- Two crossed OPEN pairs preserve the public cell-swap relation. -/
theorem PublicCellSwap.open_cross {G : SimpleGraph V}
    {sA sB aA aB tA tB : State V} {z w : V}
    (hpublic : PublicCellSwap sA sB)
    (haz : step G sA (.open z) = some aA)
    (haw : step G aA (.open w) = some tA)
    (hbw : step G sB (.open w) = some aB)
    (hbz : step G aB (.open z) = some tB) :
    PublicCellSwap tA tB := by
  have haA := eq_openSuccessor_of_step haz
  have htA := eq_openSuccessor_of_step haw
  have haB := eq_openSuccessor_of_step hbw
  have htB := eq_openSuccessor_of_step hbz
  subst aA
  subst tA
  subst aB
  subst tB
  refine {
    untouched := ?_
    queue := ?_
    ko := ?_
    toMove := ?_
    score := ?_ }
  · simp only [openSuccessor]
    ext v
    simp [hpublic.untouched, and_left_comm]
  · simpa [openSuccessor, List.append_assoc] using
      hpublic.queue.append_cross z w
  · simp only [openSuccessor]
    have hA : (sA.queue ++ [z]).isEmpty = false := by
      cases sA.queue <;> rfl
    have hB : (sB.queue ++ [w]).isEmpty = false := by
      cases sB.queue <;> rfl
    rw [hA, hB]
  · simp [openSuccessor, hpublic.toMove]
  · simpa only [openSuccessor] using hpublic.score

omit [Fintype V] in
/--
Constructor-level crossed OPEN descent inside one fixed Type-valued odd
strategy.  The hypotheses spell out both selected OPEN constructors and the
crossed legal replies at their universal answer nodes.  The conclusion keeps
the exact same root strategy, records the public endpoint relation, and gives
strict rank descent on both sides.

This lemma has no conclusion at a mixed OPEN/CLOSE boundary.
-/
theorem StrategyPrefix.crossOpen
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    {sA sB aA aB tA tB : State V} {z w : V}
    {pA pB : EdgeVector V}
    {hattA : sA.toMove ≠ seat} {hattB : sB.toMove ≠ seat}
    {haz : step G sA (.open z) = some aA}
    {hbw : step G sB (.open w) = some aB}
    {hdefA : aA.toMove = seat} {hdefB : aB.toMove = seat}
    {hasMoveA : ∃ m u, step G aA m = some u}
    {hasMoveB : ∃ m u, step G aB m = some u}
    {childrenA : ∀ m u, step G aA m = some u → OddStrategy G seat u}
    {childrenB : ∀ m u, step G aB m = some u → OddStrategy G seat u}
    (prefixA : StrategyPrefix G seat hroot
      (OddStrategy.choose sA hattA (.open z) aA haz
        (OddStrategy.answer aA hdefA hasMoveA childrenA)) pA)
    (prefixB : StrategyPrefix G seat hroot
      (OddStrategy.choose sB hattB (.open w) aB hbw
        (OddStrategy.answer aB hdefB hasMoveB childrenB)) pB)
    (haw : step G aA (.open w) = some tA)
    (hbz : step G aB (.open z) = some tB)
    (hpublic : PublicCellSwap sA sB) :
    StrategyPrefix G seat hroot (childrenA (.open w) tA haw)
        ((pA + moveLiveStar sA (.open z)) +
          moveLiveStar aA (.open w)) ∧
      StrategyPrefix G seat hroot (childrenB (.open z) tB hbz)
        ((pB + moveLiveStar sB (.open w)) +
          moveLiveStar aB (.open z)) ∧
      PublicCellSwap tA tB ∧
      rank tA < rank sA ∧ rank tB < rank sB := by
  have prefixA' : StrategyPrefix G seat hroot
      (OddStrategy.answer aA hdefA hasMoveA childrenA)
      (pA + moveLiveStar sA (.open z)) :=
    StrategyPrefix.choose prefixA
  have prefixB' : StrategyPrefix G seat hroot
      (OddStrategy.answer aB hdefB hasMoveB childrenB)
      (pB + moveLiveStar sB (.open w)) :=
    StrategyPrefix.choose prefixB
  refine ⟨StrategyPrefix.answer (hstep := haw) prefixA',
    StrategyPrefix.answer (hstep := hbz) prefixB',
    hpublic.open_cross haz haw hbw hbz, ?_, ?_⟩
  · exact lt_trans (rank_step_lt haw) (rank_step_lt haz)
  · exact lt_trans (rank_step_lt hbz) (rank_step_lt hbw)

end

end Ogdoad.Fifo
