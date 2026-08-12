import Ogdoad.Fifo

/-!
# Turn and score conjugacies for the FIFO game

The operational game is equivariant under complementing the player to move.
Consequently, complementing both the distinguished seat and the mover leaves
either target-forcing strategy predicate unchanged.  Composing this turn
symmetry with the existing score-sheet translation exchanges the odd and even
targets while restoring the original distinguished seat.

This is an exact symmetry boundary, not a proof of the isolated-dummy linking
theorem.  At the initial state the conjugate root has both the opposite mover
and score one.  No nonempty legal move macro can connect a state to its own
turn/score conjugate, since every move strictly lowers `rank` while both
translations preserve it.
-/

namespace Ogdoad.Fifo

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Complement the player to move without changing the public FIFO state or
the accumulated score. -/
def turnTranslate (s : State V) : State V :=
  { s with toMove := !s.toMove }

omit [Fintype V] [DecidableEq V] in
/-- Complementing the mover twice recovers the original state. -/
@[simp] theorem turnTranslate_involutive (s : State V) :
    turnTranslate (turnTranslate s) = s := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  simp [turnTranslate]

omit [Fintype V] in
/-- Every legal FIFO transition commutes with mover complementation. -/
theorem step_turnTranslate (G : SimpleGraph V) (s : State V) (m : Move V) :
    step G (turnTranslate s) m =
      (step G s m).map turnTranslate := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m
  · simp [step, turnTranslate]
  · cases q <;> cases ko <;> simp [step, turnTranslate]
  · simp [step, turnTranslate]

omit [Fintype V] in
/-- Complementing both the distinguished seat and the mover transports an
even-forcing strategy without changing its terminal target. -/
theorem EvenWins.turnTranslated
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (h : EvenWins G seat s) :
    EvenWins G (!seat) (turnTranslate s) := by
  induction h with
  | terminal s hterminal hscore =>
      refine EvenWins.terminal (turnTranslate s) ?_ ?_
      · simpa [Terminal, turnTranslate] using hterminal
      · simpa [turnTranslate] using hscore
  | choose s hseat m s' hstep _ ih =>
      refine EvenWins.choose (turnTranslate s) ?_ m
        (turnTranslate s') ?_ ih
      · simpa [turnTranslate] using congrArg Bool.not hseat
      · rw [step_turnTranslate, hstep]
        rfl
  | answer s hseat hasMove hchildren ih =>
      refine EvenWins.answer (turnTranslate s) ?_ ?_ ?_
      · intro hnot
        apply hseat
        simpa [turnTranslate] using hnot
      · obtain ⟨m, s', hstep⟩ := hasMove
        exact ⟨m, turnTranslate s', by
          rw [step_turnTranslate, hstep]
          rfl⟩
      · intro m t htranslated
        rw [step_turnTranslate] at htranslated
        obtain ⟨s', hstep, rfl⟩ := Option.map_eq_some_iff.mp htranslated
        exact ih m s' hstep

omit [Fintype V] in
/-- Complementing both the distinguished seat and the mover transports an
odd-forcing strategy without changing its terminal target. -/
theorem OddWins.turnTranslated
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (h : OddWins G seat s) :
    OddWins G (!seat) (turnTranslate s) := by
  induction h with
  | terminal s hterminal hscore =>
      refine OddWins.terminal (turnTranslate s) ?_ ?_
      · simpa [Terminal, turnTranslate] using hterminal
      · simpa [turnTranslate] using hscore
  | choose s hseat m s' hstep _ ih =>
      refine OddWins.choose (turnTranslate s) ?_ m
        (turnTranslate s') ?_ ih
      · intro hnot
        apply hseat
        simpa [turnTranslate] using hnot
      · rw [step_turnTranslate, hstep]
        rfl
  | answer s hseat hasMove hchildren ih =>
      refine OddWins.answer (turnTranslate s) ?_ ?_ ?_
      · simpa [turnTranslate] using congrArg Bool.not hseat
      · obtain ⟨m, s', hstep⟩ := hasMove
        exact ⟨m, turnTranslate s', by
          rw [step_turnTranslate, hstep]
          rfl⟩
      · intro m t htranslated
        rw [step_turnTranslate] at htranslated
        obtain ⟨s', hstep, rfl⟩ := Option.map_eq_some_iff.mp htranslated
        exact ih m s' hstep

omit [Fintype V] in
/-- Exact even-strategy turn conjugacy. -/
theorem evenWins_turnTranslate_iff (G : SimpleGraph V)
    (seat : Bool) (s : State V) :
    EvenWins G (!seat) (turnTranslate s) ↔ EvenWins G seat s := by
  constructor
  · intro h
    have ht := h.turnTranslated
    simpa using ht
  · exact EvenWins.turnTranslated

omit [Fintype V] in
/-- Exact odd-strategy turn conjugacy. -/
theorem oddWins_turnTranslate_iff (G : SimpleGraph V)
    (seat : Bool) (s : State V) :
    OddWins G (!seat) (turnTranslate s) ↔ OddWins G seat s := by
  constructor
  · intro h
    have ht := h.turnTranslated
    simpa using ht
  · exact OddWins.turnTranslated

omit [Fintype V] in
/-- Composing mover complementation with score-sheet translation exchanges
the target while restoring the original distinguished seat. -/
theorem oddWins_iff_evenWins_scoreTurnTranslate (G : SimpleGraph V)
    (seat : Bool) (s : State V) :
    OddWins G seat s ↔
      EvenWins G seat (scoreTranslate 1 (turnTranslate s)) := by
  constructor
  · intro h
    simpa using h.turnTranslated.scoreTranslate_one
  · intro h
    have hodd : OddWins G (!seat) (turnTranslate s) :=
      (evenWins_scoreTranslate_one_iff_oddWins
        G seat (turnTranslate s)).mp h
    exact (oddWins_turnTranslate_iff G seat s).mp hodd

/-- The state conjugate to the initial root: the same untouched board and
empty queue, but with the opposite mover and score sheet. -/
def scoreTurnInitial : State V where
  untouched := Finset.univ
  queue := []
  ko := false
  toMove := true
  score := 1

omit [DecidableEq V] in
@[simp] theorem scoreTranslate_turnTranslate_initial :
    scoreTranslate 1 (turnTranslate (initial (V := V))) =
      scoreTurnInitial (V := V) := by
  rfl

/-- Initial-root spelling of the exact target/turn conjugacy.  The right-hand
root is deliberately not identified with the actual initial state. -/
theorem oddWins_initial_iff_evenWins_scoreTurnInitial
    (G : SimpleGraph V) (seat : Bool) :
    OddWins G seat (initial (V := V)) ↔
      EvenWins G seat (scoreTurnInitial (V := V)) := by
  simpa using oddWins_iff_evenWins_scoreTurnTranslate
    G seat (initial (V := V))

omit [Fintype V] [DecidableEq V] in
@[simp] theorem rank_turnTranslate (s : State V) :
    rank (turnTranslate s) = rank s := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  simp [rank, turnTranslate]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem rank_scoreTranslate (c : ZMod 2) (s : State V) :
    rank (scoreTranslate c s) = rank s := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  rfl

/-- A finite, explicitly labelled legal move path. -/
inductive StepPath (G : SimpleGraph V) :
    State V → List (Move V) → State V → Prop
  | nil (s : State V) : StepPath G s [] s
  | cons {s s' t : State V} {m : Move V} {ms : List (Move V)}
      (head : step G s m = some s') (tail : StepPath G s' ms t) :
      StepPath G s (m :: ms) t

omit [Fintype V] in
/-- Every nonempty legal path strictly lowers the game rank. -/
theorem StepPath.rank_lt_of_nonempty
    {G : SimpleGraph V} {s t : State V} {ms : List (Move V)}
    (h : StepPath G s ms t) (hne : ms ≠ []) : rank t < rank s := by
  induction h with
  | nil => exact False.elim (hne rfl)
  | @cons s s' t m ms hstep htail ih =>
      by_cases hnil : ms = []
      · subst ms
        cases htail
        exact rank_step_lt hstep
      · exact lt_trans (ih hnil) (rank_step_lt hstep)

omit [Fintype V] in
/-- No nonempty legal macro can connect a state to its own score-and-turn
conjugate.  In particular an isolated dummy, whose OPEN and CLOSE have zero
charge, cannot realize the missing root conjugacy by a fixed legal macro. -/
theorem no_nonempty_path_to_scoreTurnTranslate
    {G : SimpleGraph V} (s : State V) :
    ¬∃ ms, ms ≠ [] ∧
      StepPath G s ms (scoreTranslate 1 (turnTranslate s)) := by
  rintro ⟨ms, hne, hpath⟩
  have hlt := hpath.rank_lt_of_nonempty hne
  rw [rank_scoreTranslate, rank_turnTranslate] at hlt
  exact (Nat.lt_irrefl _) hlt

end

end Ogdoad.Fifo
