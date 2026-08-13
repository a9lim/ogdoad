import Ogdoad.FifoMinHotCurvature
import Ogdoad.FifoOutcome

/-!
# Pair-state reduction for FIFO linking

This module records what a failure at a score-zero state with the mover
designated Even forces below it.  If the mover cannot force score zero while
an OPEN is available, then some lower-rank state is hot: one physical player
can force either terminal score.  Taking a minimum-rank hot state and applying
the checked minimum-hot classification gives a singleton charged wall.

On a graph with an isolated dummy, neither endpoint of that charged wall can
be the dummy.  Thus a counterexample at the initial two-OPEN checkpoint would
have to descend to a wall after the dummy has left the untouched carrier (and
cannot have the dummy as its queue front).  This is a genuine narrowing, not
a proof of the pair-state assertion: the missing step is still the causal
transport from the two-OPEN strategy fan to that later dummy-spending wall.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Hotness is invariant under a unit score debt: the two target strategies
are exchanged. -/
theorem hot_scoreTranslate_one_iff (G : SimpleGraph V)
    (player : Bool) (s : State V) :
    Hot G player (scoreTranslate 1 s) ↔ Hot G player s := by
  simp only [Hot, evenWins_scoreTranslate_one_iff_oddWins,
    oddWins_scoreTranslate_one_iff_evenWins, Bool.not_not, and_comm]

omit [Fintype V] in
/-- If the current mover cannot force score zero from a zero-score state at
which an OPEN is available, a hot state exists at strictly lower rank.

Otherwise every lower state would be cold at its current score.  The mover
could make any OPEN, which preserves score zero, and use coldness of the child
to win, contradicting the assumed failure. -/
theorem exists_hot_below_of_not_moverEvenWins
    (G : SimpleGraph V) (s : State V) (hs0 : s.score = 0)
    (hU : s.untouched.Nonempty) (hbad : ¬MoverEvenWins G s) :
    ∃ player t, rank t < rank s ∧ Hot G player t := by
  by_contra hnone
  push Not at hnone
  have hnohot : ∀ (player : Bool) (t : State V), rank t < rank s →
      ¬Hot G player t := by
    intro player t ht
    exact hnone player t ht
  obtain ⟨v, hv⟩ := hU
  let t : State V := {
    untouched := s.untouched.erase v
    queue := s.queue ++ [v]
    ko := s.queue.isEmpty
    toMove := !s.toMove
    score := s.score }
  have hopen : step G s (.open v) = some t := by
    simp [step, t, hv]
  have hcold : ColdAtOwnScore G t :=
    coldAtOwnScore_below_minHot G (rank s) hnohot t
      (rank_step_lt hopen)
  have heven : EvenWins G s.toMove t :=
    hcold.evenWins (by simp [t, hs0]) s.toMove
  exact hbad (EvenWins.choose s rfl (.open v) t hopen heven)

omit [Fintype V] [DecidableEq V] in
/-- A unit adjacency at a singleton wall cannot use an isolated dummy at
either endpoint. -/
theorem adjacencyBit_one_avoids_dummy
    {G : SimpleGraph V} {d f z : V} (hd : IsDummy G d)
    (hbit : adjacencyBit G f z = 1) : f ≠ d ∧ z ≠ d := by
  constructor
  · intro hfd
    subst f
    have hnot : ¬G.Adj d z := hd z
    simp [adjacencyBit, hnot] at hbit
  · intro hzd
    subst z
    have hnot : ¬G.Adj f d := by
      simpa [G.adj_comm] using hd f
    simp [adjacencyBit, hnot] at hbit

omit [Fintype V] in
/-- Exact minimum-hot obstruction forced by any score-zero mover failure with
an available OPEN.  The witness is normalized to score zero without changing
its rank or hotness.  Its singleton untouched vertex and queue front are real,
so the isolated dummy has already been consumed and is not the front.

The witness is minimum among all hot states of lower rank, not asserted to be
a descendant of the original strategy.  Recovering strategy ancestry is the
remaining causal factor-extension problem. -/
theorem moverFailure_yields_minHot_realWall
    (G : SimpleGraph V) (d : V) (hd : IsDummy G d)
    (s : State V) (hs0 : s.score = 0) (hU : s.untouched.Nonempty)
    (hbad : ¬MoverEvenWins G s) :
    ∃ player t f q z,
      rank t < rank s ∧ t.score = 0 ∧ t.toMove = player ∧
      t.queue = f :: q ∧ t.ko = false ∧ t.untouched = {z} ∧
      adjacencyBit G f z = 1 ∧
      (∀ a ∈ q, adjacencyBit G a z = 0) ∧
      d ∉ t.untouched ∧ f ≠ d := by
  classical
  obtain ⟨player, t, htRank, htHot⟩ :=
    exists_hot_below_of_not_moverEvenWins G s hs0 hU hbad
  let P : Nat → Prop := fun n ↦ ∃ (p : Bool) (u : State V),
    rank u < rank s ∧ Hot G p u ∧ rank u = n
  have hP : ∃ n, P n := ⟨rank t, player, t, htRank, htHot, rfl⟩
  let n := Nat.find hP
  obtain ⟨p, u, huRoot, huHot, huRank⟩ := Nat.find_spec hP
  let u0 := if u.score = 0 then u else scoreTranslate 1 u
  have hu0Rank : rank u0 = rank u := by
    simp only [u0]
    split
    · rfl
    · rfl
  have hu0Score : u0.score = 0 := by
    simp only [u0]
    split
    · assumption
    · rename_i hne
      have hone : u.score = 1 := zmod2_eq_one_of_ne_zero _ hne
      simp only [scoreTranslate, hone]
      exact CharTwo.add_self_eq_zero 1
  have hu0Hot : Hot G p u0 := by
    simp only [u0]
    split
    · exact huHot
    · exact (hot_scoreTranslate_one_iff G p u).2 huHot
  have hu0Root : rank u0 < rank s := by simpa [hu0Rank] using huRoot
  have hminimal : ∀ (other : Bool) (w : State V), rank w < rank u0 →
      ¬Hot G other w := by
    intro other w hw hwhot
    have hwRoot : rank w < rank s := lt_trans hw hu0Root
    have hPw : P (rank w) := ⟨other, w, hwRoot, hwhot, rfl⟩
    have hnle : n ≤ rank w := Nat.find_min' hP hPw
    have hule : rank u0 ≤ rank w := by
      rw [hu0Rank, huRank]
      exact hnle
    exact (Nat.not_lt_of_ge hule) hw
  obtain ⟨hturn, f, q, z, hqueue, hko, hcarrier, hbit, htail⟩ :=
    minHotState_is_singletonWall G p u0 hu0Score hu0Hot hminimal
  obtain ⟨hfd, hzd⟩ := adjacencyBit_one_avoids_dummy hd hbit
  refine ⟨p, u0, f, q, z, hu0Root, hu0Score, hturn, hqueue, hko,
    hcarrier, hbit, htail, ?_, hfd⟩
  rw [hcarrier]
  simpa using hzd.symm

/-- A zero-score odd counterstrategy at a coherent clear defender state must
contain a genuine attacker OPEN deviation.  The CLOSE-first alternative is
excluded by the conditioned theorem.  In particular this applies to every
well-formed two-OPEN checkpoint with the original mover designated Even. -/
theorem OddWins.hasClearDeviation_of_coherent_clear_defender
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (hodd : OddWins G seat s) (hs0 : s.score = 0)
    (hcoherent : Coherent s) (hturn : s.toMove = seat)
    (hqueue : s.queue ≠ []) (hko : s.ko = false) :
    OddStrategyHasClearDeviation hodd := by
  rcases oddStrategy_deviation_or_closeFirst hodd with hdev | hcf
  · exact hdev
  · exfalso
    have hnot := ConditionedCloseFirstTheorem
      V inferInstance inferInstance G (!seat) s hcoherent
        (by simp [hturn]) hqueue hko
    apply hnot
    simpa [hs0] using hcf.toCloseFirstWins

end

end Ogdoad.Fifo
