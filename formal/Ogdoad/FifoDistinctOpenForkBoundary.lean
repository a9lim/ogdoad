import Ogdoad.FifoParityCounterNormal
import Ogdoad.FifoSameOpenBraid
import Ogdoad.FifoCrossExitIncidence

/-!
# The distinct-OPEN first-fork boundary

At a score-coupled policy fork which selects two distinct OPENs, the crossed
defender replies append the reversed pairs `[x, y]` and `[y, x]` after one
identical FIFO prefix.  This looks like the `CellSwap` carrier used by the
crossed-response braid, but the direction of the queue matters: a reachable
nonempty common prefix cannot swap with itself because its entries are
distinct.

This file proves the exact boundary.  For a well-formed common state, the two
crossed queues form an `EvenBraidQueues` pair if and only if the old queue was
empty.  At every false-seat attacker fork, queue/turn parity forces the old
queue to have odd length.  Thus the distinct-OPEN first fork of the
even-order nonmover-controlled obstruction lies outside the existing
CellSwap braid.  At a true-seat attacker fork the queue is even, but parity
alone does not decide whether it is empty; this is the odd-order
mover-controlled side.

This is a route no-go, not a disproof of the FIFO parity-seat conjecture.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u}

/-- A legal OPEN certifies membership in the source untouched carrier. -/
theorem mem_untouched_of_open_step [DecidableEq V]
    {G : SimpleGraph V} {s t : State V} {x : V}
    (hstep : step G s (.open x) = some t) : x ∈ s.untouched := by
  simp only [step] at hstep
  split at hstep
  · assumption
  · contradiction

/-- Appending two distinct untouched labels preserves queue nodupness at a
well-formed state. -/
theorem WellFormed.queue_append_two_nodup [DecidableEq V]
    {s : State V} {x y : V} (hWF : WellFormed s)
    (hx : x ∈ s.untouched) (hy : y ∈ s.untouched) (hxy : x ≠ y) :
    (s.queue ++ [x, y]).Nodup := by
  have hxq : x ∉ s.queue := by
    intro hxmem
    exact Finset.disjoint_left.mp hWF.2 hx (by simpa using hxmem)
  have hyq : y ∉ s.queue := by
    intro hymem
    exact Finset.disjoint_left.mp hWF.2 hy (by simpa using hymem)
  rw [List.nodup_append]
  refine ⟨hWF.1, by simp [hxy], ?_⟩
  intro a ha b hb
  simp at hb
  rcases hb with rfl | rfl
  · exact fun h => hxq (h ▸ ha)
  · exact fun h => hyq (h ▸ ha)

/-- If a cell-swap pair begins with the same two entries, those entries are
equal.  Hence a nodup nonempty queue cannot be a nontrivial self-swap. -/
theorem CellSwap.same_two_head_eq {a b : V} {q q' : List V}
    (h : CellSwap (a :: b :: q) (a :: b :: q')) : a = b := by
  cases h
  rfl

/-- Every queue on the left side of `CellSwap` has even length. -/
theorem CellSwap.left_length_even {q q' : List V} (h : CellSwap q q') :
    q.length % 2 = 0 := by
  induction h with
  | nil => rfl
  | cell a b tail ih =>
      simp only [List.length_cons]
      omega

/-- Crossed OPENs appended after the same nonempty nodup prefix do not form a
`CellSwap` pair.  The one-entry prefix fails by odd length; a longer prefix
would force its first two distinct entries to be equal. -/
theorem CellSwap.same_nonempty_nodup_prefix_append_cross_impossible
    {q : List V} {x y : V} (hq : q ≠ [])
    (hn : (q ++ [x, y]).Nodup) :
    ¬CellSwap (q ++ [x, y]) (q ++ [y, x]) := by
  intro hcells
  cases q with
  | nil => exact hq rfl
  | cons a tail =>
      cases tail with
      | nil =>
          have heven := hcells.left_length_even
          norm_num at heven
      | cons b r =>
          have hab : a ≠ b := by
            have ha : a ∉ b :: (r ++ [x, y]) := (List.nodup_cons.mp hn).1
            have hab' : a ≠ b ∧ a ∉ r ++ [x, y] := by
              simpa only [List.mem_cons, not_or] using ha
            exact hab'.1
          exact hab (by
            simpa only [List.cons_append] using hcells.same_two_head_eq)

/-- Exact list-level boundary for the larger same-OPEN braid relation.  A
common nonempty suffix would force the distinct final labels `x,y` to agree;
with empty suffix the pure `CellSwap` obstruction applies. -/
theorem EvenBraidQueues.same_nodup_prefix_append_cross_iff_empty
    {q : List V} {x y : V} (hxy : x ≠ y)
    (hn : (q ++ [x, y]).Nodup) :
    EvenBraidQueues (q ++ [x, y]) (q ++ [y, x]) ↔ q = [] := by
  constructor
  · rintro ⟨coreA, coreB, suffix, hcells, hA, hB⟩
    by_contra hq
    have hsuffix : suffix = [] := by
      by_contra hs
      have hlastA : some y = suffix.getLast? := by
        calc
          some y = (q ++ [x, y]).getLast? := by simp
          _ = (coreA ++ suffix).getLast? := congrArg List.getLast? hA
          _ = suffix.getLast? :=
            List.getLast?_append_of_ne_nil coreA hs
      have hlastB : some x = suffix.getLast? := by
        calc
          some x = (q ++ [y, x]).getLast? := by simp
          _ = (coreB ++ suffix).getLast? := congrArg List.getLast? hB
          _ = suffix.getLast? :=
            List.getLast?_append_of_ne_nil coreB hs
      exact hxy (Option.some.inj (hlastB.trans hlastA.symm))
    subst suffix
    simp only [List.append_nil] at hA hB
    subst coreA
    subst coreB
    exact CellSwap.same_nonempty_nodup_prefix_append_cross_impossible
      hq hn hcells
  · rintro rfl
    exact ⟨[x, y], [y, x], [], CellSwap.cell x y CellSwap.nil, by simp,
      by simp⟩

/-! ## The wider common-prefix / swapped-core / common-suffix braid -/

/-- An indexed sandwich braid retains a common FIFO prefix before the
cell-swapped core and a common suffix after it.  The index is load-bearing:
it records how many common fronts must be consumed before the existing
`EvenBraidQueues` phase begins. -/
def SandwichBraidQueues (pre qA qB : List V) : Prop :=
  ∃ coreA coreB suffix, CellSwap coreA coreB ∧
    qA = pre ++ coreA ++ suffix ∧
    qB = pre ++ coreB ++ suffix

/-- Every distinct-OPEN crossed pair belongs to the sandwich braid indexed
by its old common queue, including the false-seat nonempty-prefix case. -/
theorem SandwichBraidQueues.append_cross_after_prefix
    (q : List V) (x y : V) :
    SandwichBraidQueues q (q ++ [x, y]) (q ++ [y, x]) := by
  exact ⟨[x, y], [y, x], [], CellSwap.cell x y CellSwap.nil, by simp,
    by simp⟩

/-- A common OPEN is stored in the sandwich suffix. -/
theorem SandwichBraidQueues.append_common {pre qA qB : List V}
    (h : SandwichBraidQueues pre qA qB) (z : V) :
    SandwichBraidQueues pre (qA ++ [z]) (qB ++ [z]) := by
  rcases h with ⟨coreA, coreB, suffix, hcells, rfl, rfl⟩
  exact ⟨coreA, coreB, suffix ++ [z], hcells,
    by simp [List.append_assoc], by simp [List.append_assoc]⟩

/-- A common FIFO CLOSE consumes one indexed prefix front and exposes a
strictly shorter sandwich phase. -/
theorem SandwichBraidQueues.tail_of_common_prefix
    {a : V} {pre qA qB : List V}
    (h : SandwichBraidQueues (a :: pre) qA qB) :
    SandwichBraidQueues pre qA.tail qB.tail := by
  rcases h with ⟨coreA, coreB, suffix, hcells, rfl, rfl⟩
  exact ⟨coreA, coreB, suffix, hcells, by simp, by simp⟩

/-- Once the indexed common prefix is empty, the sandwich is exactly an
ordinary even braid. -/
theorem SandwichBraidQueues.toEvenBraid
    {qA qB : List V} (h : SandwichBraidQueues [] qA qB) :
    EvenBraidQueues qA qB := by
  rcases h with ⟨coreA, coreB, suffix, hcells, hA, hB⟩
  exact ⟨coreA, coreB, suffix, hcells, by simpa using hA,
    by simpa using hB⟩

/-- Operational form: two distinct legal OPENs at one well-formed state enter
the existing even braid after crossed replies exactly when their common old
queue is empty. -/
theorem distinctOpen_cross_evenBraid_iff_queue_empty [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} {s sx sy : State V} {x y : V}
    (hWF : WellFormed s) (hx : step G s (.open x) = some sx)
    (hy : step G s (.open y) = some sy) (hxy : x ≠ y) :
    EvenBraidQueues (s.queue ++ [x, y]) (s.queue ++ [y, x]) ↔
      s.queue = [] := by
  apply EvenBraidQueues.same_nodup_prefix_append_cross_iff_empty hxy
  exact hWF.queue_append_two_nodup
    (mem_untouched_of_open_step hx) (mem_untouched_of_open_step hy) hxy

/-- Positive side of the exact boundary.  If the common old queue is empty,
crossed OPEN replies from score-coupled roots become a genuine
`PublicCellSwap` after translating the right endpoint back by one score unit.
The translation is essential: the two original strategy endpoints still
differ by one accumulated score. -/
theorem distinctOpen_emptyQueue_cross_publicCellSwap_after_untranslate
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {s sx sxy sy₁ syx₁ : State V} {x y : V}
    (hqueue : s.queue = [])
    (hx : step G s (.open x) = some sx)
    (hxy : step G sx (.open y) = some sxy)
    (hy₁ : step G (scoreTranslate 1 s) (.open y) = some sy₁)
    (hyx₁ : step G sy₁ (.open x) = some syx₁) :
    PublicCellSwap sxy (scoreTranslate 1 syx₁) := by
  have hpublic : PublicCellSwap s s := {
    untouched := rfl
    queue := by simpa [hqueue] using (CellSwap.nil : CellSwap ([] : List V) [])
    ko := rfl
    toMove := rfl
    score := rfl }
  have hy : step G s (.open y) = some (scoreTranslate 1 sy₁) := by
    have h := step_scoreTranslate G 1 (scoreTranslate 1 s) (.open y)
    rw [scoreTranslate_one_involutive, hy₁] at h
    simpa using h
  have hyx : step G (scoreTranslate 1 sy₁) (.open x) =
      some (scoreTranslate 1 syx₁) := by
    rw [step_scoreTranslate, hyx₁]
    rfl
  exact hpublic.open_cross hx hxy hy hyx

/-- At every false-seat attacker fork, the common old queue has odd length
and is therefore nonempty.  Consequently crossed distinct-OPEN queues cannot
enter `EvenBraidQueues`.  In particular this closes the braid route for the
even-order nonmover-controlled first-fork case. -/
theorem StrategyPrefix.falseSeat_attacker_distinctOpen_cross_not_evenBraid
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {root : OddStrategy G false (initial (V := V))}
    {s : State V} {tree : OddStrategy G false s} {p : EdgeVector V}
    {sx sy : State V} {x y : V}
    (hp : StrategyPrefix G false root tree p) (hattacker : s.toMove ≠ false)
    (hx : step G s (.open x) = some sx)
    (hy : step G s (.open y) = some sy) (hxy : x ≠ y) :
    ¬EvenBraidQueues (s.queue ++ [x, y]) (s.queue ++ [y, x]) := by
  have hxU : x ∈ s.untouched := mem_untouched_of_open_step hx
  have hqueueTurn := hp.queueTurnParity_of_untouched_nonempty ⟨x, hxU⟩
  have hmover : s.toMove = true := by
    cases hs : s.toMove
    · exact False.elim (hattacker hs)
    · rfl
  have hqueueOdd : s.queue.length % 2 = 1 := by
    simpa [QueueTurnParity, hmover] using hqueueTurn
  have hqueue : s.queue ≠ [] := by
    intro h
    rw [h] at hqueueOdd
    norm_num at hqueueOdd
  have hWF : WellFormed s := hp.wellFormed wellFormed_initial
  exact fun hbraid => hqueue
    ((distinctOpen_cross_evenBraid_iff_queue_empty hWF hx hy hxy).mp hbraid)

/-- At a true-seat attacker fork the old queue is even.  Unlike the
false-seat case, this leaves the empty-queue braid entry possible, and the
exact criterion remains `s.queue = []`. -/
theorem StrategyPrefix.trueSeat_attacker_distinctOpen_cross_evenBraid_iff_empty
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {root : OddStrategy G true (initial (V := V))}
    {s : State V} {tree : OddStrategy G true s} {p : EdgeVector V}
    {sx sy : State V} {x y : V}
    (hp : StrategyPrefix G true root tree p) (hattacker : s.toMove ≠ true)
    (hx : step G s (.open x) = some sx)
    (hy : step G s (.open y) = some sy) (hxy : x ≠ y) :
    s.queue.length % 2 = 0 ∧
      (EvenBraidQueues (s.queue ++ [x, y]) (s.queue ++ [y, x]) ↔
        s.queue = []) := by
  have hxU : x ∈ s.untouched := mem_untouched_of_open_step hx
  have hqueueTurn := hp.queueTurnParity_of_untouched_nonempty ⟨x, hxU⟩
  have hnonmover : s.toMove = false := by
    cases hs : s.toMove
    · rfl
    · exact False.elim (hattacker hs)
  have hqueueEven : s.queue.length % 2 = 0 := by
    simpa [QueueTurnParity, hnonmover] using hqueueTurn
  have hWF : WellFormed s := hp.wellFormed wellFormed_initial
  exact ⟨hqueueEven,
    distinctOpen_cross_evenBraid_iff_queue_empty hWF hx hy hxy⟩

end

end Ogdoad.Fifo
