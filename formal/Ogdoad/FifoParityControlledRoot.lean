import Ogdoad.FifoParitySeat
import Ogdoad.FifoSingletonForkBoundary

/-!
# From the parity-seat target to a controlled isolated-dummy root

The proposed dummy-free parity-seat theorem would immediately force every
remaining isolated-dummy counterstrategy into one of the two controlled
outcome classes.  Odd carrier order leaves only a mover-controlled root;
even order leaves only a nonmover-controlled root.  Combining this observation
with the live-dummy minimum theorem shows exactly where that route stops: its
least reachable controlled checkpoint has already consumed the dummy.

The parity-seat statement remains a hypothesis here.  The final theorem is a
conditional reduction, not a proof of FIFO linking.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Under the parity-seat target, an odd counterstrategy for the other seat
forces the initial outcome to be controlled, with its orientation determined
by carrier parity. -/
theorem OddStrategy.controlled_initial_of_paritySeat
    {G : SimpleGraph V} {seat : Bool}
    (hparity : FifoParitySeatAt G)
    (root : OddStrategy G seat (initial (V := V))) :
    (Odd (Fintype.card V) ∧ seat = true ∧
        MoverControlled G (initial (V := V))) ∨
      (Even (Fintype.card V) ∧ seat = false ∧
        NonmoverControlled G (initial (V := V))) := by
  rcases Nat.even_or_odd (Fintype.card V) with hEven | hOdd
  · have hMover : EvenWins G true (initial (V := V)) :=
      hparity.2 hEven
    have hseat : seat = false := by
      cases hseat : seat
      · rfl
      · exact False.elim (hMover.not_oddWins (by simpa [hseat] using
          root.toOddWins))
    subst seat
    refine Or.inr ⟨hEven, rfl, ?_⟩
    refine ⟨?_, ?_⟩
    · intro hMoverFalse
      have hEvenFalse : EvenWins G false (initial (V := V)) := by
        simpa [MoverEvenWins, initial] using hMoverFalse
      exact hEvenFalse.not_oddWins root.toOddWins
    · simpa [NonmoverEvenWins, initial] using hMover
  · have hNonmover : EvenWins G false (initial (V := V)) :=
      hparity.1 hOdd
    have hseat : seat = true := by
      cases hseat : seat
      · exact False.elim (hNonmover.not_oddWins (by simpa [hseat] using
          root.toOddWins))
      · rfl
    subst seat
    refine Or.inl ⟨hOdd, rfl, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [MoverEvenWins, initial] using hNonmover
    · intro hNonmoverTrue
      have hEvenTrue : EvenWins G true (initial (V := V)) := by
        simpa [NonmoverEvenWins, initial] using hNonmoverTrue
      exact hEvenTrue.not_oddWins root.toOddWins

/-- The parity-seat hypothesis and the strategy-relative bad-ancestry normal
form meet asymmetrically.  On odd carrier order, any remaining odd root has
seat `true`; its minimal bad queue is even, so both normal cases remain
possible.  On even carrier order, the odd root has seat `false`; its minimal
bad queue is odd, which eliminates the protected-OPEN case and forces a
charged-CLOSE predecessor with an even tail.

This is the strongest direct combination of the two current reductions.  In
particular, the odd-order branch deliberately retains the protected case. -/
theorem OddStrategy.paritySeat_controlled_badNormalForm
    {G : SimpleGraph V} {d : V} {seat : Bool}
    (hd : IsDummy G d) (hparity : FifoParitySeatAt G)
    (root : OddStrategy G seat (initial (V := V))) :
    (Odd (Fintype.card V) ∧ seat = true ∧
        MoverControlled G (initial (V := V)) ∧
        ∃ w : ControlledBadNormalWitness G d seat root,
          w.state.queue.length % 2 = 0) ∨
      (Even (Fintype.card V) ∧ seat = false ∧
        NonmoverControlled G (initial (V := V)) ∧
        ∃ (w : ControlledBadNormalWitness G d seat root) (y : V),
          w.incoming = .close ∧
          w.parent.queue = y :: w.front :: w.tail ∧
          w.parent.ko = false ∧
          w.parent.untouched = w.state.untouched ∧
          w.parent.score = 1 ∧
          flip G w.parent.untouched y = 1 ∧
          w.tail.length % 2 = 0) := by
  rcases root.controlled_initial_of_paritySeat hparity with
    ⟨hOdd, hseat, hcontrolled⟩ | ⟨hEven, hseat, hcontrolled⟩
  · subst seat
    obtain ⟨w⟩ := root.nonempty_controlledBadNormalWitness hd
    exact Or.inl ⟨hOdd, rfl, hcontrolled, w,
      w.trueSeat_queue_even⟩
  · subst seat
    obtain ⟨w⟩ := root.nonempty_controlledBadNormalWitness hd
    have hqueueOdd := w.falseSeat_queue_odd
    obtain ⟨y, hincoming, hqueue, hko, hU, hscore, hcharge⟩ :=
      w.normalCase.chargedClose_of_queue_odd w.queue hqueueOdd
    have htailEven : w.tail.length % 2 = 0 := by
      rw [w.queue, List.length_cons] at hqueueOdd
      omega
    exact Or.inr ⟨hEven, rfl, hcontrolled, w, y, hincoming,
      hqueue, hko, hU, hscore, hcharge, htailEven⟩

/-- Conditional endpoint of the parity-seat route.  Any alleged odd root
strategy yields a least reachable controlled checkpoint, and the complete
live-dummy fork elimination forces that checkpoint to have spent `d`. -/
theorem OddStrategy.paritySeat_rankMinimum_consumes_dummy
    {G : SimpleGraph V} {d : V} {seat : Bool}
    (hd : IsDummy G d) (hparity : FifoParitySeatAt G)
    (root : OddStrategy G seat (initial (V := V))) :
    ∃ s, ReachableFrom G (initial (V := V)) s ∧
      (MoverControlled G s ∨ NonmoverControlled G s) ∧
      d ∉ s.untouched ∧
      ∀ t, ReachableFrom G (initial (V := V)) t → rank t < rank s →
        ¬MoverControlled G t ∧ ¬NonmoverControlled G t := by
  have hcontrolled : MoverControlled G (initial (V := V)) ∨
      NonmoverControlled G (initial (V := V)) := by
    rcases root.controlled_initial_of_paritySeat hparity with
      ⟨_, _, hMover⟩ | ⟨_, _, hNonmover⟩
    · exact Or.inl hMover
    · exact Or.inr hNonmover
  exact controlled_isolated_root_rankMinimum_consumes_dummy
    G (initial (V := V)) d hd hcontrolled

end

end Ogdoad.Fifo
