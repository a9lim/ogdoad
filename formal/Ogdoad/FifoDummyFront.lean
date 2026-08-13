import Ogdoad.FifoFirstSeatRoot

/-!
# The isolated dummy-front selector obstruction

Consider the initial pair state with queue `[d, y]`, where `d` is isolated
and the physical first player is the even seeker.  Closing `d` and then
opening `z` reaches exactly the same public state as opening `z` and then
closing `d`.

This diamond does not by itself give the even seeker a strategy steal.  If
every dummy-consumed two-real-OPEN child is odd-winning, the odd seeker pairs
the two sides of the diamond: after `C_d` it selects `O_z`, while after
`O_z` it selects `C_d`.  Thus an even win at the dummy-front state already
forces a winning dummy-consumed pair child.  The theorem is a necessary
selector, not a proof that such a child exists.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Untouched carrier after the distinct initial pair `OPEN d; OPEN y`. -/
def dummyFrontCarrier (d y : V) : Finset V :=
  (Finset.univ.erase d).erase y

/-- State after closing the isolated front `d` from the initial pair
`[d, y]`. -/
def dummyFrontClearedState (d y : V) : State V where
  untouched := dummyFrontCarrier d y
  queue := [y]
  ko := false
  toMove := true
  score := 0

/-- State after opening `z` while the initial isolated front is still live. -/
def dummyFrontOpenedState (d y z : V) : State V where
  untouched := (dummyFrontCarrier d y).erase z
  queue := [d, y, z]
  ko := false
  toMove := true
  score := 0

/-- Common endpoint of `C_d; O_z` and `O_z; C_d`.  The dummy has been
consumed, and the remaining queue is the real pair `[y, z]`. -/
def dummyConsumedPairState (d y z : V) : State V where
  untouched := (dummyFrontCarrier d y).erase z
  queue := [y, z]
  ko := false
  toMove := false
  score := 0

/-- The immediate isolated-front CLOSE is neutral. -/
theorem afterInitialDummyReal_step_close
    {G : SimpleGraph V} {d y : V} (hd : IsDummy G d) :
    step G (afterInitialTwoOpens d y) .close =
      some (dummyFrontClearedState d y) := by
  simp [step, afterInitialTwoOpens, dummyFrontClearedState,
    dummyFrontCarrier, flip_dummy hd]

/-- Opening a remaining vertex after clearing the dummy reaches the common
dummy-consumed pair endpoint. -/
theorem dummyFrontCleared_step_open
    (G : SimpleGraph V) (d y z : V)
    (hz : z ∈ dummyFrontCarrier d y) :
    step G (dummyFrontClearedState d y) (.open z) =
      some (dummyConsumedPairState d y z) := by
  simp [step, dummyFrontClearedState, dummyConsumedPairState, hz]

/-- Opening first while retaining the dummy front gives the other corner of
the commuting diamond. -/
theorem afterInitialDummyReal_step_open
    (G : SimpleGraph V) (d y z : V)
    (hz : z ∈ dummyFrontCarrier d y) :
    step G (afterInitialTwoOpens d y) (.open z) =
      some (dummyFrontOpenedState d y z) := by
  have hzy : z ≠ y := by
    exact (Finset.mem_erase.mp hz).1
  have hzd : z ≠ d := by
    exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hz)).1
  simp [step, afterInitialTwoOpens, dummyFrontOpenedState,
    dummyFrontCarrier, hzy, hzd]

/-- Closing the isolated dummy after that OPEN reaches the same endpoint. -/
theorem dummyFrontOpened_step_close
    {G : SimpleGraph V} {d y z : V} (hd : IsDummy G d) :
    step G (dummyFrontOpenedState d y z) .close =
      some (dummyConsumedPairState d y z) := by
  simp [step, dummyFrontOpenedState, dummyConsumedPairState, flip_dummy hd]

/-- Exact Tweedledum--Tweedledee no-go.  If every real continuation obtained
by spending the dummy is odd-winning, then the initial dummy-front pair is
odd-winning as well.  The odd player answers the even player's two possible
move shapes by traversing the opposite side of the commuting diamond. -/
theorem oddWins_dummyFront_of_all_consumedPairs
    (G : SimpleGraph V) (d y : V) (hd : IsDummy G d)
    (hcarrier : (dummyFrontCarrier d y).Nonempty)
    (hall : ∀ z ∈ dummyFrontCarrier d y,
      OddWins G false (dummyConsumedPairState d y z)) :
    OddWins G false (afterInitialTwoOpens d y) := by
  have hclose := afterInitialDummyReal_step_close (G := G) (d := d) (y := y) hd
  refine OddWins.answer (afterInitialTwoOpens d y) rfl
    ⟨.close, dummyFrontClearedState d y, hclose⟩ ?_
  intro m t hstep
  cases m with
  | close =>
      rw [hclose] at hstep
      have ht : t = dummyFrontClearedState d y :=
        Option.some.inj hstep.symm
      subst t
      obtain ⟨z, hz⟩ := hcarrier
      exact OddWins.choose (dummyFrontClearedState d y)
        (by simp [dummyFrontClearedState])
        (.open z) (dummyConsumedPairState d y z)
        (dummyFrontCleared_step_open G d y z hz) (hall z hz)
  | «open» z =>
      have hz : z ∈ dummyFrontCarrier d y := by
        simp only [step, afterInitialTwoOpens] at hstep
        split at hstep
        · simpa [dummyFrontCarrier] using ‹z ∈
            (Finset.univ.erase d).erase y›
        · contradiction
      have hopen := afterInitialDummyReal_step_open G d y z hz
      rw [hopen] at hstep
      have ht : t = dummyFrontOpenedState d y z :=
        Option.some.inj hstep.symm
      subst t
      exact OddWins.choose (dummyFrontOpenedState d y z)
        (by simp [dummyFrontOpenedState])
        .close (dummyConsumedPairState d y z)
        (dummyFrontOpened_step_close (G := G) (d := d) (y := y) (z := z) hd)
        (hall z hz)
  | pass =>
      simp [step, afterInitialTwoOpens] at hstep

/-- Necessary selector for any successful dummy-front strategy.  An even win
at `[d, y]` implies that at least one remaining `z` gives an even-winning
dummy-consumed pair `[y, z]`.  This is the exact obstruction to a proof using
only neutrality of `C_d`: existence of the good real child is still required.
-/
theorem evenWins_dummyFront_has_consumedPair
    (G : SimpleGraph V) (d y : V) (hd : IsDummy G d)
    (hcarrier : (dummyFrontCarrier d y).Nonempty)
    (heven : EvenWins G false (afterInitialTwoOpens d y)) :
    ∃ z ∈ dummyFrontCarrier d y,
      EvenWins G false (dummyConsumedPairState d y z) := by
  by_contra hnone
  push Not at hnone
  have hall : ∀ z ∈ dummyFrontCarrier d y,
      OddWins G false (dummyConsumedPairState d y z) := by
    intro z hz
    exact oddWins_of_not_evenWins G false _ (hnone z hz)
  exact heven.not_oddWins
    (oddWins_dummyFront_of_all_consumedPairs G d y hd hcarrier hall)

end

end Ogdoad.Fifo
