import Ogdoad.FifoCrossDescent
import Ogdoad.FifoMinHotCurvature

/-!
# The same-OPEN two-phase braid

This module enlarges the pure `CellSwap` relation just enough to survive a
same selected OPEN followed by the two universal front-CLOSE replies.  An
even phase consists of a cell-swapped queue core with an identical suffix in
both copies.  Closing the first member of the leading reversed cell gives a
half phase; a common OPEN there, followed by closing the second member,
returns to an even phase at strict lower rank.

The common half-phase OPEN contributes the exact universal curvature
`aw + bw`, where `(a,b)` is the active reversed cell.  Its graph evaluation is
also the XOR difference of the two paired CLOSE scores.  Thus the braid is a
finite causal carrier for reducing the same-OPEN escape to a smaller braid or
to the already separate distinct-OPEN/mixed boundaries.

It is deliberately **not** an odd contraction theorem.  Every transition
compares two histories and therefore has augmentation zero.  Closing the
carrier under these squares supplies neither the third ancestry hole nor the
continuation direction needed for an odd affine factor certificate.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Queue phases -/

omit [Fintype V] in
/-- Cell swapping preserves the underlying queue vertex set. -/
theorem CellSwap.toFinset_eq {q q' : List V} (h : CellSwap q q') :
    q.toFinset = q'.toFinset := by
  induction h with
  | nil => rfl
  | cell a b tail ih =>
      simp only [List.toFinset_cons]
      rw [ih]
      ext x
      simp [or_left_comm]

/-- Even phase: a cell-swapped core followed by one identical suffix.  The
suffix may have either parity; it records common OPENs which occurred after
the still-active swapped cells were created. -/
def EvenBraidQueues (qA qB : List V) : Prop :=
  ∃ coreA coreB suffix, CellSwap coreA coreB ∧
    qA = coreA ++ suffix ∧ qB = coreB ++ suffix

omit [Fintype V] in
/-- An even braid has the same underlying live queue set in both copies. -/
theorem EvenBraidQueues.toFinset_eq {qA qB : List V}
    (h : EvenBraidQueues qA qB) : qA.toFinset = qB.toFinset := by
  rcases h with ⟨coreA, coreB, suffix, cells, rfl, rfl⟩
  rw [List.toFinset_append, List.toFinset_append, cells.toFinset_eq]

/-- Half phase after closing the first member of a leading reversed cell.
The active endpoints `a,b` remain exchanged at the two queue fronts. -/
def HalfBraidQueues (a b : V) (qA qB : List V) : Prop :=
  ∃ coreA coreB suffix, CellSwap coreA coreB ∧
    qA = b :: (coreA ++ suffix) ∧
    qB = a :: (coreB ++ suffix)

omit [Fintype V] [DecidableEq V] in
/-- Appending one common OPEN preserves the even phase. -/
theorem EvenBraidQueues.append_common {qA qB : List V}
    (h : EvenBraidQueues qA qB) (z : V) :
    EvenBraidQueues (qA ++ [z]) (qB ++ [z]) := by
  rcases h with ⟨coreA, coreB, suffix, cells, rfl, rfl⟩
  exact ⟨coreA, coreB, suffix ++ [z], cells,
    by simp [List.append_assoc], by simp [List.append_assoc]⟩

omit [Fintype V] [DecidableEq V] in
/-- Closing the first fronts of a leading reversed cell moves from the even
phase to the half phase. -/
theorem EvenBraidQueues.close_first_cell {a b : V} {qA qB r : List V}
    (h : CellSwap qA qB) :
    HalfBraidQueues a b (b :: (qA ++ r)) (a :: (qB ++ r)) := by
  exact ⟨qA, qB, r, h, rfl, rfl⟩

omit [Fintype V] [DecidableEq V] in
/-- Closing the second active fronts returns a half phase to an even phase. -/
theorem HalfBraidQueues.close_second_cell
    {a b : V} {qA qB : List V} (h : HalfBraidQueues a b qA qB) :
    EvenBraidQueues qA.tail qB.tail := by
  rcases h with ⟨coreA, coreB, suffix, cells, rfl, rfl⟩
  exact ⟨coreA, coreB, suffix, cells, by simp, by simp⟩

/-! ## Vector and scalar curvature -/

omit [Fintype V] in
/-- At a half phase the two live sets differ only by the exchanged active
fronts `a,b`.  A common OPEN `w` therefore changes the paired prefix moment
by exactly the two incident edge coordinates `aw + bw`. -/
theorem liveStarVector_halfCell_commonOpen
    (L : Finset V) (a b w : V)
    (ha : a ∉ L) (hb : b ∉ L) (haw : a ≠ w) (hbw : b ≠ w) :
    liveStarVector (insert b L) w + liveStarVector (insert a L) w =
      Finsupp.single s(a, w) 1 + Finsupp.single s(b, w) 1 := by
  have hA := liveStarVector_insert_cancel L a w ha haw
  have hB := liveStarVector_insert_cancel L b w hb hbw
  calc
    liveStarVector (insert b L) w + liveStarVector (insert a L) w =
        (liveStarVector L w + liveStarVector (insert b L) w) +
          (liveStarVector L w + liveStarVector (insert a L) w) := by
            ext e
            simp only [Finsupp.add_apply]
            symm
            calc
              (liveStarVector L w) e +
                    (liveStarVector (insert b L) w) e +
                  ((liveStarVector L w) e +
                    (liveStarVector (insert a L) w) e) =
                ((liveStarVector L w) e + (liveStarVector L w) e) +
                  ((liveStarVector (insert b L) w) e +
                    (liveStarVector (insert a L) w) e) := by abel
              _ = (liveStarVector (insert b L) w) e +
                    (liveStarVector (insert a L) w) e := by
                rw [CharTwo.add_self_eq_zero, zero_add]
    _ = Finsupp.single s(b, w) 1 + Finsupp.single s(a, w) 1 := by
      rw [hB, hA]
    _ = Finsupp.single s(a, w) 1 + Finsupp.single s(b, w) 1 := add_comm _ _

omit [Fintype V] in
/-- The scalar score difference of the two first-CLOSE/common-OPEN/
second-CLOSE schedules is the evaluation of the same two-edge curvature. -/
theorem pairedClose_commonOpen_scoreDefect
    (G : SimpleGraph V) (U : Finset V) (a b w : V) (hw : w ∈ U) :
    (flip G U a + flip G U b) +
        (flip G (U.erase w) b + flip G (U.erase w) a) =
      adjacencyBit G a w + adjacencyBit G b w := by
  have hA := flip_eq_flip_erase_add (G := G) (f := a) hw
  have hB := flip_eq_flip_erase_add (G := G) (f := b) hw
  rw [hA, hB]
  calc
    (flip G (U.erase w) a + adjacencyBit G a w +
          (flip G (U.erase w) b + adjacencyBit G b w)) +
        (flip G (U.erase w) b + flip G (U.erase w) a) =
      (flip G (U.erase w) a + flip G (U.erase w) a) +
        (flip G (U.erase w) b + flip G (U.erase w) b) +
          (adjacencyBit G a w + adjacencyBit G b w) := by abel
    _ = adjacencyBit G a w + adjacencyBit G b w := by
      rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
        zero_add, zero_add]

omit [Fintype V] [DecidableEq V] in
/-- Graph evaluation of the half-phase vector update. -/
theorem graphEvaluation_halfCellCurvature
    (G : SimpleGraph V) (a b w : V) :
    graphEvaluation G
        (Finsupp.single s(a, w) 1 + Finsupp.single s(b, w) 1) =
      adjacencyBit G a w + adjacencyBit G b w := by
  simp [graphEvaluation_single]

/-! ## One full operational `E → H → E` path -/

private def braidOpenSuccessor (s : State V) (v : V) : State V where
  untouched := s.untouched.erase v
  queue := s.queue ++ [v]
  ko := s.queue.isEmpty
  toMove := !s.toMove
  score := s.score

omit [Fintype V] in
private theorem eq_braidOpenSuccessor_of_step {G : SimpleGraph V}
    {s t : State V} {v : V} (h : step G s (.open v) = some t) :
    t = braidOpenSuccessor s v := by
  simp only [step] at h
  split at h
  · cases h
    rfl
  · contradiction

private def braidCloseSuccessor (G : SimpleGraph V) (s : State V)
    (f : V) (q : List V) : State V where
  untouched := s.untouched
  queue := q
  ko := false
  toMove := !s.toMove
  score := s.score + flip G s.untouched f

omit [Fintype V] in
private theorem eq_braidCloseSuccessor_of_step {G : SimpleGraph V}
    {s t : State V} {f : V} {q : List V}
    (hqueue : s.queue = f :: q) (h : step G s .close = some t) :
    t = braidCloseSuccessor G s f q := by
  simp only [step, hqueue] at h
  split at h
  · contradiction
  · cases h
    rfl

omit [Fintype V] in
/-- One complete same-OPEN braid cell.

Both copies start in an even phase with leading reversed cell `(a,b)`.  They
OPEN the same `z`, close their respective first fronts, OPEN the same `w` in
the resulting half phase, and close their respective second fronts.  The
endpoints form a smaller even braid with common suffix extended by `[z,w]`.
Their score XOR changes by the graph evaluation of `aw + bw`, and both ranks
drop strictly.

The theorem is operational rather than strategic: a fixed `OddStrategy`
supplies the four step hypotheses only when the selected and universal moves
actually occur in that tree. -/
theorem sameOpenBraid_even_half_even
    {G : SimpleGraph V}
    {sA sB oA oB hA hB uA uB tA tB : State V}
    {a b z w : V} {qA qB r : List V}
    (hcells : CellSwap qA qB)
    (hUA : sA.untouched = sB.untouched)
    (hqueueA : sA.queue = (a :: b :: qA) ++ r)
    (hqueueB : sB.queue = (b :: a :: qB) ++ r)
    (hturn : sA.toMove = sB.toMove)
    (hAz : step G sA (.open z) = some oA)
    (hBz : step G sB (.open z) = some oB)
    (hAc : step G oA .close = some hA)
    (hBc : step G oB .close = some hB)
    (hAw : step G hA (.open w) = some uA)
    (hBw : step G hB (.open w) = some uB)
    (hAcc : step G uA .close = some tA)
    (hBcc : step G uB .close = some tB) :
    tA.untouched = tB.untouched ∧
      EvenBraidQueues tA.queue tB.queue ∧
      tA.ko = false ∧ tB.ko = false ∧
      tA.toMove = tB.toMove ∧
      tA.score + tB.score =
        (sA.score + sB.score) +
          (adjacencyBit G a w + adjacencyBit G b w) ∧
      rank tA < rank sA ∧ rank tB < rank sB := by
  have hoA := eq_braidOpenSuccessor_of_step hAz
  have hoB := eq_braidOpenSuccessor_of_step hBz
  subst oA
  subst oB
  have hcloseQueueA :
      (braidOpenSuccessor sA z).queue =
        a :: (b :: (qA ++ r ++ [z])) := by
    simp [braidOpenSuccessor, hqueueA, List.append_assoc]
  have hcloseQueueB :
      (braidOpenSuccessor sB z).queue =
        b :: (a :: (qB ++ r ++ [z])) := by
    simp [braidOpenSuccessor, hqueueB, List.append_assoc]
  have hhA := eq_braidCloseSuccessor_of_step hcloseQueueA hAc
  have hhB := eq_braidCloseSuccessor_of_step hcloseQueueB hBc
  subst hA
  subst hB
  have huA := eq_braidOpenSuccessor_of_step hAw
  have huB := eq_braidOpenSuccessor_of_step hBw
  subst uA
  subst uB
  have hsecondQueueA :
      (braidOpenSuccessor
          (braidCloseSuccessor G (braidOpenSuccessor sA z) a
            (b :: (qA ++ r ++ [z]))) w).queue =
        b :: (qA ++ (r ++ [z, w])) := by
    simp [braidOpenSuccessor, braidCloseSuccessor, List.append_assoc]
  have hsecondQueueB :
      (braidOpenSuccessor
          (braidCloseSuccessor G (braidOpenSuccessor sB z) b
            (a :: (qB ++ r ++ [z]))) w).queue =
        a :: (qB ++ (r ++ [z, w])) := by
    simp [braidOpenSuccessor, braidCloseSuccessor, List.append_assoc]
  have htA := eq_braidCloseSuccessor_of_step hsecondQueueA hAcc
  have htB := eq_braidCloseSuccessor_of_step hsecondQueueB hBcc
  subst tA
  subst tB
  have hwU : w ∈ sA.untouched.erase z := by
    simp only [step, braidCloseSuccessor, braidOpenSuccessor] at hAw
    split at hAw
    · assumption
    · contradiction
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [braidOpenSuccessor, braidCloseSuccessor, hUA]
  · refine ⟨qA, qB, r ++ [z, w], hcells, ?_, ?_⟩
    · simp [braidOpenSuccessor, braidCloseSuccessor]
    · simp [braidOpenSuccessor, braidCloseSuccessor]
  · simp [braidOpenSuccessor, braidCloseSuccessor, hturn]
  · simp only [braidOpenSuccessor, braidCloseSuccessor]
    rw [hUA]
    have hdefect := pairedClose_commonOpen_scoreDefect
      G (sB.untouched.erase z) a b w (by simpa [hUA] using hwU)
    calc
      sA.score + flip G (sB.untouched.erase z) a +
            flip G ((sB.untouched.erase z).erase w) b +
          (sB.score + flip G (sB.untouched.erase z) b +
            flip G ((sB.untouched.erase z).erase w) a) =
        (sA.score + sB.score) +
          ((flip G (sB.untouched.erase z) a +
              flip G (sB.untouched.erase z) b) +
            (flip G ((sB.untouched.erase z).erase w) b +
              flip G ((sB.untouched.erase z).erase w) a)) := by abel
      _ = (sA.score + sB.score) +
          (adjacencyBit G a w + adjacencyBit G b w) := by rw [hdefect]
  · exact lt_trans (rank_step_lt hAcc)
      (lt_trans (rank_step_lt hAw)
        (lt_trans (rank_step_lt hAc) (rank_step_lt hAz)))
  · exact lt_trans (rank_step_lt hBcc)
      (lt_trans (rank_step_lt hBw)
        (lt_trans (rank_step_lt hBc) (rank_step_lt hBz)))

end

end Ogdoad.Fifo
