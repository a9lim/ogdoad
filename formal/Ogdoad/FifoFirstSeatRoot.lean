import Ogdoad.FifoNeutralPair

/-!
# Exact first-seat root Bellman form

At the initial root player `false` controls the first move. After its first
OPEN, player `true` controls a singleton-ko state; on a nontrivial carrier
the untouched set is nonempty, so the only legal replies are second OPENs.
Consequently first-seat FIFO linking is exactly an existential first opener
followed by a universal two-OPEN fan.

This is a root normal form, not a proof that any selector exists. In
particular, the stronger statement that every ordered pair is winning would
imply the first-seat half of FIFO linking, but is not asserted here.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The graph-independent state after the first initial OPEN. -/
def afterInitialOpen (x : V) : State V where
  untouched := Finset.univ.erase x
  queue := [x]
  ko := true
  toMove := true
  score := 0

/-- The graph-independent state after two distinct initial OPENs. -/
def afterInitialTwoOpens (x y : V) : State V where
  untouched := (Finset.univ.erase x).erase y
  queue := [x, y]
  ko := false
  toMove := false
  score := 0

/-- Every label is a legal first OPEN from the initial root. -/
theorem initial_step_open (G : SimpleGraph V) (x : V) :
    step G (initial (V := V)) (.open x) = some (afterInitialOpen x) := by
  simp [step, initial, afterInitialOpen]

/-- Membership in the punctured carrier is exactly legality of a second
OPEN, with the displayed two-OPEN state as successor. -/
theorem afterInitialOpen_step_open_iff
    (G : SimpleGraph V) (x y : V) :
    step G (afterInitialOpen x) (.open y) =
        some (afterInitialTwoOpens x y) ↔
      y ∈ (Finset.univ.erase x : Finset V) := by
  constructor
  · intro h
    simp only [step, afterInitialOpen] at h
    split at h
    · assumption
    · contradiction
  · intro hy
    simp [step, afterInitialOpen, afterInitialTwoOpens, hy]

/-- A nontrivial carrier always leaves a legal second opener after the first
OPEN. -/
theorem afterInitialOpen_hasMove [Nontrivial V]
    (G : SimpleGraph V) (x : V) :
    ∃ m s', step G (afterInitialOpen x) m = some s' := by
  obtain ⟨y, hyx⟩ := exists_ne x
  have hy : y ∈ (Finset.univ.erase x : Finset V) := by simp [hyx]
  exact ⟨.open y, afterInitialTwoOpens x y,
    (afterInitialOpen_step_open_iff G x y).2 hy⟩

/-- At the singleton-ko state with a nonempty untouched set, every legal move
is a second OPEN. -/
theorem afterInitialOpen_step_cases [Nontrivial V]
    (G : SimpleGraph V) (x : V) (m : Move V) (t : State V)
    (hstep : step G (afterInitialOpen x) m = some t) :
    ∃ y, y ∈ (Finset.univ.erase x : Finset V) ∧
      m = .open y ∧ t = afterInitialTwoOpens x y := by
  cases m with
  | «open» y =>
      have hy : y ∈ (Finset.univ.erase x : Finset V) := by
        simp only [step, afterInitialOpen] at hstep
        split at hstep
        · assumption
        · contradiction
      have hcanonical := (afterInitialOpen_step_open_iff G x y).2 hy
      rw [hcanonical] at hstep
      exact ⟨y, hy, rfl, Option.some.inj hstep.symm⟩
  | close => simp [step, afterInitialOpen] at hstep
  | pass =>
      have hne : (Finset.univ.erase x : Finset V) ≠ ∅ := by
        obtain ⟨y, hyx⟩ := exists_ne x
        exact Finset.nonempty_iff_ne_empty.mp ⟨y, by simp [hyx]⟩
      simp [step, afterInitialOpen, hne] at hstep

/-- Exact first-seat Bellman normal form. The outer existential is the first
player's initial OPEN; the inner universal family is the opponent's complete
second-OPEN reply fan. -/
theorem evenWins_initial_firstSeat_iff_twoOpenSelector [Nontrivial V]
    (G : SimpleGraph V) :
    EvenWins G false (initial (V := V)) ↔
      ∃ x : V, ∀ y ∈ (Finset.univ.erase x : Finset V),
        EvenWins G false (afterInitialTwoOpens x y) := by
  have hUniv : (Finset.univ : Finset V) ≠ ∅ := by
    exact Finset.nonempty_iff_ne_empty.mp
      (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty)
  constructor
  · intro hwin
    cases hwin with
    | terminal _ hterminal _ =>
        exact False.elim (hUniv (by simpa [Terminal, initial] using hterminal))
    | answer _ hseat _ _ =>
        exact False.elim (hseat rfl)
    | choose _ _ m t hstep hchild =>
        cases m with
        | close => simp [step, initial] at hstep
        | pass => simp [step, initial] at hstep
        | «open» x =>
            have hfirst := initial_step_open G x
            rw [hfirst] at hstep
            have ht : t = afterInitialOpen x := Option.some.inj hstep.symm
            subst t
            refine ⟨x, ?_⟩
            intro y hy
            have hsecond := (afterInitialOpen_step_open_iff G x y).2 hy
            cases hchild with
            | terminal _ hterminal _ =>
                exact False.elim
                  (terminal_no_step hterminal
                    ⟨.open y, afterInitialTwoOpens x y, hsecond⟩)
            | choose _ hseat _ _ _ _ =>
                simp [afterInitialOpen] at hseat
            | answer _ _ _ children =>
                exact children (.open y) (afterInitialTwoOpens x y) hsecond
  · rintro ⟨x, hfan⟩
    have hfirst := initial_step_open G x
    refine EvenWins.choose (initial (V := V)) rfl (.open x)
      (afterInitialOpen x) hfirst ?_
    refine EvenWins.answer (afterInitialOpen x) (by simp [afterInitialOpen])
      (afterInitialOpen_hasMove G x) ?_
    intro m t hstep
    obtain ⟨y, hy, rfl, rfl⟩ :=
      afterInitialOpen_step_cases G x m t hstep
    exact hfan y hy

/-- If every ordered distinct pair of initial OPENs is winning, first-seat
linking follows. This deliberately proves only the implication. -/
theorem evenWins_initial_firstSeat_of_all_twoOpens [Nontrivial V]
    (G : SimpleGraph V)
    (hall : ∀ x y : V, x ≠ y →
      EvenWins G false (afterInitialTwoOpens x y)) :
    EvenWins G false (initial (V := V)) := by
  rw [evenWins_initial_firstSeat_iff_twoOpenSelector]
  let x : V := Classical.choice (inferInstance : Nonempty V)
  refine ⟨x, ?_⟩
  intro y hy
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  exact hall x y hyx.symm

end

end Ogdoad.Fifo
