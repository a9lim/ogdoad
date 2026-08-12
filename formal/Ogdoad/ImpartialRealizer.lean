import Ogdoad.FifoMatching

/-!
# A pass-free impartial compiler for the matching FIFO arena

This file removes the only variable-tempo move from the weighted-source
FIFO mechanism.  The ko delay protects a front only while some unopened
coin remains; after the last OPEN, CLOSE is legal even when ko is set.
Thus PASS disappears, every play has exactly one OPEN and one CLOSE per
coin, and the initial-to-terminal tempo is even.

The matching safe-front proof survives unchanged at its only new branch:
a ko-set CLOSE is possible only after the untouched set is empty, when its
charge is necessarily zero.  The final Boolean charge is compiled by one
impartial tail move, present exactly at charge one.
-/

namespace Ogdoad.ImpartialRealizer

open Ogdoad.Fifo

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The pass-free move alphabet. -/
inductive Move (V : Type*) where
  | open (v : V)
  | close
deriving DecidableEq

/-- Pass-free FIFO transition.  A ko-set front may be closed exactly after
all coins have been opened. -/
def step (G : SimpleGraph V) (s : State V) : Move V → Option (State V)
  | .open v =>
      if v ∈ s.untouched then
        some {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove
          score := s.score }
      else none
  | .close =>
      match s.queue with
      | [] => none
      | f :: q =>
          if s.ko = false ∨ s.untouched = ∅ then
            some {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove
              score := s.score + flip G s.untouched f }
          else none

/-- A pass-free root with a supplied initial charge. -/
def initial (sigma : ZMod 2 := 0) : State V where
  untouched := Finset.univ
  queue := []
  ko := false
  toMove := false
  score := sigma

/-- Exactly the number of core FIFO moves still to be played. -/
def remaining (s : State V) : Nat :=
  2 * s.untouched.card + s.queue.length

omit [Fintype V] in
theorem step_toMove {G : SimpleGraph V} {s s' : State V} {m : Move V}
    (h : step G s m = some s') : s'.toMove = !s.toMove := by
  cases m
  · simp only [step] at h
    split at h
    · cases h
      rfl
    · contradiction
  · simp only [step] at h
    split at h
    · contradiction
    · split at h
      · cases h
        rfl
      · contradiction

omit [Fintype V] in
theorem open_score {G : SimpleGraph V} {s s' : State V} {v : V}
    (h : step G s (.open v) = some s') : s'.score = s.score := by
  simp only [step] at h
  split at h
  · cases h
    rfl
  · contradiction

omit [Fintype V] in
theorem close_score {G : SimpleGraph V} {s s' : State V}
    (h : step G s .close = some s') :
    ∃ f q, s.queue = f :: q ∧
      s'.score = s.score + flip G s.untouched f := by
  simp only [step] at h
  split at h
  · contradiction
  · rename_i f q hq
    split at h
    · cases h
      exact ⟨f, q, hq, rfl⟩
    · contradiction

omit [Fintype V] in
theorem untouched_empty_of_close_of_ko {G : SimpleGraph V}
    {s s' : State V} (h : step G s .close = some s')
    (hko : s.ko = true) : s.untouched = ∅ := by
  simp only [step] at h
  split at h
  · contradiction
  · split at h
    · rename_i hlegal
      exact hlegal.resolve_left (by simp [hko])
    · contradiction

omit [Fintype V] in
/-- Every core move consumes exactly one unit of the exact clock. -/
theorem remaining_step {G : SimpleGraph V} {s s' : State V} {m : Move V}
    (h : step G s m = some s') : remaining s = remaining s' + 1 := by
  cases m
  · rename_i v
    simp only [step] at h
    split at h
    · rename_i hv
      cases h
      rw [remaining, remaining, Finset.card_erase_of_mem hv,
        List.length_append]
      simp
      have hpos : 0 < s.untouched.card := Finset.card_pos.mpr ⟨v, hv⟩
      omega
    · contradiction
  · simp only [step] at h
    split at h
    · contradiction
    · rename_i f q hq
      split at h
      · cases h
        simp only [remaining, hq, List.length_cons]
        omega
      · contradiction

/-- Terminal means that every coin has been opened and the FIFO has drained. -/
def Terminal (s : State V) : Prop :=
  s.untouched = ∅ ∧ s.queue = []

omit [Fintype V] in
theorem terminal_no_step {G : SimpleGraph V} {s : State V}
    (hs : Terminal s) : ¬∃ m s', step G s m = some s' := by
  rcases hs with ⟨hU, hq⟩
  rintro ⟨m, s', hm⟩
  cases m <;> simp [step, hU, hq] at hm

omit [Fintype V] in
/-- The exhausted-board ko relaxation removes the only pass-only state. -/
theorem not_terminal_has_step {G : SimpleGraph V} {s : State V}
    (hs : ¬Terminal s) : ∃ m s', step G s m = some s' := by
  by_cases hU : s.untouched = ∅
  · cases hq : s.queue with
    | nil => exact False.elim (hs ⟨hU, hq⟩)
    | cons f q =>
        refine ⟨.close, {
          untouched := s.untouched
          queue := q
          ko := false
          toMove := !s.toMove
          score := s.score + flip G s.untouched f }, ?_⟩
        simp [step, hq, hU]
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hU
    refine ⟨.open v, {
      untouched := s.untouched.erase v
      queue := s.queue ++ [v]
      ko := s.queue.isEmpty
      toMove := !s.toMove
      score := s.score }, ?_⟩
    simp [step, hv]

omit [Fintype V] in
theorem step_score_eq_of_untouched_empty {G : SimpleGraph V}
    {s s' : State V} {m : Move V} (hU : s.untouched = ∅)
    (h : step G s m = some s') : s'.score = s.score := by
  cases m
  · simp [step, hU] at h
  · obtain ⟨f, q, _hq, hs⟩ := close_score h
    rw [hs, hU, flip_empty, add_zero]

omit [Fintype V] in
theorem step_untouched_eq_empty {G : SimpleGraph V}
    {s s' : State V} {m : Move V} (hU : s.untouched = ∅)
    (h : step G s m = some s') : s'.untouched = ∅ := by
  cases m
  · simp [step, hU] at h
  · simp only [step] at h
    split at h
    · contradiction
    · split at h
      · cases h
        exact hU
      · contradiction

/-- Boolean parity, presented recursively so that exact clock descent directly
controls the mover bit. -/
def clockParity : Nat → Bool
  | 0 => false
  | n + 1 => !(clockParity n)

@[simp] theorem clockParity_two_mul (n : Nat) :
    clockParity (2 * n) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      simp only [clockParity, Bool.not_not, ih]

/-- The mover is completely determined by the remaining core tempo. -/
def TempoAligned (s : State V) : Prop :=
  s.toMove = clockParity (remaining s)

omit [DecidableEq V] in
theorem tempoAligned_initial (sigma : ZMod 2) :
    TempoAligned (initial (V := V) sigma) := by
  simp [TempoAligned, initial, remaining]

omit [Fintype V] in
theorem TempoAligned.step {G : SimpleGraph V} {s s' : State V}
    {m : Move V} (hs : TempoAligned s) (h : step G s m = some s') :
    TempoAligned s' := by
  rw [TempoAligned, step_toMove h, hs, remaining_step h]
  simp [clockParity]

omit [Fintype V] [DecidableEq V] in
theorem TempoAligned.terminal_toMove {s : State V}
    (hs : TempoAligned s) (ht : Terminal s) : s.toMove = false := by
  rcases ht with ⟨hU, hq⟩
  simpa [TempoAligned, remaining, hU, hq, clockParity] using hs

/-- A finite strategy tree for forcing one absolute terminal charge. -/
inductive ForcesScore (G : SimpleGraph V) (seat : Bool) (target : ZMod 2) :
    State V → Prop
  | terminal (s : State V) (hterminal : Terminal s)
      (hscore : s.score = target) : ForcesScore G seat target s
  | choose (s : State V) (hseat : s.toMove = seat)
      (m : Move V) (s' : State V) (hstep : step G s m = some s')
      (hwin : ForcesScore G seat target s') : ForcesScore G seat target s
  | answer (s : State V) (hseat : s.toMove ≠ seat)
      (hasMove : ∃ m s', step G s m = some s')
      (hwin : ∀ m s', step G s m = some s' →
        ForcesScore G seat target s') : ForcesScore G seat target s

omit [Fintype V] in
theorem forcesScore_of_untouched_empty (G : SimpleGraph V)
    (seat : Bool) (target : ZMod 2) (s : State V)
    (hU : s.untouched = ∅) (hscore : s.score = target) :
    ForcesScore G seat target s := by
  induction s using (measure remaining).wf.induction with
  | h s ih =>
      by_cases ht : Terminal s
      · exact ForcesScore.terminal s ht hscore
      · have hasMove : ∃ m s', step G s m = some s' :=
          not_terminal_has_step ht
        by_cases hseat : s.toMove = seat
        · obtain ⟨m, s', hstep⟩ := hasMove
          refine ForcesScore.choose s hseat m s' hstep
            (ih s' ?_ ?_ ?_)
          · change remaining s' < remaining s
            rw [remaining_step hstep]
            omega
          · exact step_untouched_eq_empty hU hstep
          · rw [step_score_eq_of_untouched_empty hU hstep, hscore]
        · refine ForcesScore.answer s hseat hasMove ?_
          intro m s' hstep
          refine ih s' ?_ ?_ ?_
          · change remaining s' < remaining s
            rw [remaining_step hstep]
            omega
          · exact step_untouched_eq_empty hU hstep
          · rw [step_score_eq_of_untouched_empty hU hstep, hscore]

omit [Fintype V] in
/-- Safe-front matching induction for the pass-free transition, uniform over
every scoring submatching of one public matching. -/
theorem forcesScore_of_public_matching
    {G0 H : SimpleGraph V} (hG0 : IsMatchingGraph G0) (hHG0 : H ≤ G0)
    (seat : Bool) (target : ZMod 2) :
    ∀ s : State V, s.score = target →
      (s.toMove = seat ∨ MatchingFrontSafe H s) →
      ForcesScore H seat target s := by
  intro s
  induction s using (measure remaining).wf.induction with
  | h s ih =>
      intro hscore hmode
      by_cases ht : Terminal s
      · exact ForcesScore.terminal s ht hscore
      by_cases hseat : s.toMove = seat
      · by_cases hU : s.untouched = ∅
        · exact forcesScore_of_untouched_empty H seat target s hU hscore
        · obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hU
          cases hq : s.queue with
          | nil =>
              let s' : State V := {
                untouched := s.untouched.erase z
                queue := s.queue ++ [z]
                ko := s.queue.isEmpty
                toMove := !s.toMove
                score := s.score }
              have hstep : step H s (.open z) = some s' := by
                simp [step, s', hz]
              refine ForcesScore.choose s hseat (.open z) s' hstep
                (ih s' ?_ ?_ (Or.inr ?_))
              · change remaining s' < remaining s
                rw [remaining_step hstep]
                omega
              · exact hscore
              · exact matchingFrontSafe_of_open_empty s z hq
          | cons f q =>
              by_cases hmate : ∃ u ∈ s.untouched, G0.Adj f u
              · obtain ⟨u, hu, hfu⟩ := hmate
                let s' : State V := {
                  untouched := s.untouched.erase u
                  queue := s.queue ++ [u]
                  ko := s.queue.isEmpty
                  toMove := !s.toMove
                  score := s.score }
                have hstep : step H s (.open u) = some s' := by
                  simp [step, s', hu]
                refine ForcesScore.choose s hseat (.open u) s' hstep
                  (ih s' ?_ ?_ (Or.inr ?_))
                · change remaining s' < remaining s
                  rw [remaining_step hstep]
                  omega
                · exact hscore
                · exact matchingFrontSafe_of_open_public_mate
                    hG0 hHG0 s f u q hq hfu
              · have hnone : ∀ u ∈ s.untouched, ¬G0.Adj f u := by
                  intro u hu hfu
                  exact hmate ⟨u, hu, hfu⟩
                let s' : State V := {
                  untouched := s.untouched.erase z
                  queue := s.queue ++ [z]
                  ko := s.queue.isEmpty
                  toMove := !s.toMove
                  score := s.score }
                have hstep : step H s (.open z) = some s' := by
                  simp [step, s', hz]
                refine ForcesScore.choose s hseat (.open z) s' hstep
                  (ih s' ?_ ?_ (Or.inr ?_))
                · change remaining s' < remaining s
                  rw [remaining_step hstep]
                  omega
                · exact hscore
                · exact matchingFrontSafe_of_open_no_public_neighbor
                    hHG0 s f z q hq hnone
      · have hasMove : ∃ m s', step H s m = some s' :=
          not_terminal_has_step ht
        refine ForcesScore.answer s hseat hasMove ?_
        intro m s' hstep
        have hchildturn : s'.toMove = seat := by
          rw [step_toMove hstep]
          cases hs : s.toMove <;> cases hseat' : seat <;> simp_all
        apply ih s'
        · change remaining s' < remaining s
          rw [remaining_step hstep]
          omega
        · cases m with
          | «open» v => rw [open_score hstep, hscore]
          | close =>
              obtain ⟨f, q, hq, hs'⟩ := close_score hstep
              rcases hmode with hturn | hsafe
              · exact False.elim (hseat hturn)
              · rcases hsafe with hko | hfront
                · have hUempty := untouched_empty_of_close_of_ko hstep hko
                  rw [hs', hUempty, flip_empty, add_zero, hscore]
                · rw [hs', hfront f q hq, add_zero, hscore]
        · exact Or.inl hchildturn

/-- One public matching supports both-seat charge-preservation strategies for
every edge-deleted scoring submatching. -/
theorem forcesScore_initial_of_every_submatching
    {G0 : SimpleGraph V} (hG0 : IsMatchingGraph G0)
    (seat : Bool) (sigma : ZMod 2) :
    ∀ H : SimpleGraph V, H ≤ G0 →
      ForcesScore H seat sigma (initial (V := V) sigma) := by
  intro H hHG0
  apply forcesScore_of_public_matching hG0 hHG0 seat sigma
  · rfl
  · by_cases hs : seat = false
    · exact Or.inl (by simpa [initial] using hs.symm)
    · right
      right
      intro f q hq
      simp [initial] at hq

/-- At a drained state, one impartial tail move is present exactly at charge
one.  This predicate says which physical seat wins that local normal-play
tail. -/
def TailWinner (seat : Bool) (s : State V) : Prop :=
  if s.score = 1 then s.toMove = seat else s.toMove ≠ seat

/-- Ordinary normal-play strategy semantics for the pass-free core followed
by the impartial one-move charge tail.  All nonterminal move sets are `step`;
the terminal constructor is exactly the local tail evaluation. -/
inductive TailWins (G : SimpleGraph V) (seat : Bool) : State V → Prop
  | terminal (s : State V) (hterminal : Terminal s)
      (hwinner : TailWinner seat s) : TailWins G seat s
  | choose (s : State V) (hseat : s.toMove = seat)
      (m : Move V) (s' : State V) (hstep : step G s m = some s')
      (hwin : TailWins G seat s') : TailWins G seat s
  | answer (s : State V) (hseat : s.toMove ≠ seat)
      (hasMove : ∃ m s', step G s m = some s')
      (hwin : ∀ m s', step G s m = some s' → TailWins G seat s') :
      TailWins G seat s

omit [Fintype V] in
/-- The two physical seats cannot both possess normal-play winning strategy
trees from the same impartial position. -/
theorem TailWins.not_complement {G : SimpleGraph V} {seat : Bool}
    {s : State V} (h : TailWins G seat s) : ¬TailWins G (!seat) s := by
  induction h with
  | terminal s hterminal hwinner =>
      intro hother
      cases hother with
      | terminal _ _ hotherWinner =>
          unfold TailWinner at hwinner hotherWinner
          by_cases hs : s.score = 1
          · simp only [hs, if_true] at hwinner hotherWinner
            cases seat <;> cases s.toMove <;> simp_all
          · simp only [hs, if_false] at hwinner hotherWinner
            cases seat <;> cases s.toMove <;> simp_all
      | choose _ _ m s' hstep _ =>
          exact terminal_no_step hterminal ⟨m, s', hstep⟩
      | answer _ _ hasMove _ =>
          exact terminal_no_step hterminal hasMove
  | choose s hseat m s' hstep _ ih =>
      intro hother
      cases hother with
      | terminal _ hterminal _ =>
          exact terminal_no_step hterminal ⟨m, s', hstep⟩
      | choose _ hotherSeat _ _ _ _ =>
          cases seat <;> cases s.toMove <;> simp_all
      | answer _ _ _ hanswer =>
          exact ih (hanswer m s' hstep)
  | answer s hseat hasMove hwin ih =>
      intro hother
      cases hother with
      | terminal _ hterminal _ =>
          exact terminal_no_step hterminal hasMove
      | choose _ _ m s' hstep hchild =>
          exact ih m s' hstep hchild
      | answer _ hotherSeat _ _ =>
          cases seat <;> cases s.toMove <;> simp_all

omit [Fintype V] in
/-- A first-seat strategy forcing charge one compiles to a normal-play win. -/
theorem ForcesScore.one_to_tailWins_first {G : SimpleGraph V} {s : State V}
    (h : ForcesScore G false 1 s) (htempo : TempoAligned s) :
    TailWins G false s := by
  induction h with
  | terminal s hterminal hscore =>
      apply TailWins.terminal s hterminal
      have hturn := htempo.terminal_toMove hterminal
      simp [TailWinner, hscore, hturn]
  | choose s hseat m s' hstep _ ih =>
      exact TailWins.choose s hseat m s' hstep
        (ih (htempo.step hstep))
  | answer s hseat hasMove hwin ih =>
      refine TailWins.answer s hseat hasMove ?_
      intro m s' hstep
      exact ih m s' hstep (htempo.step hstep)

omit [Fintype V] in
/-- A second-seat strategy forcing charge zero compiles to a normal-play win. -/
theorem ForcesScore.zero_to_tailWins_second {G : SimpleGraph V} {s : State V}
    (h : ForcesScore G true 0 s) (htempo : TempoAligned s) :
    TailWins G true s := by
  induction h with
  | terminal s hterminal hscore =>
      apply TailWins.terminal s hterminal
      have hturn := htempo.terminal_toMove hterminal
      simp [TailWinner, hscore, hturn]
  | choose s hseat m s' hstep _ ih =>
      exact TailWins.choose s hseat m s' hstep
        (ih (htempo.step hstep))
  | answer s hseat hasMove hwin ih =>
      refine TailWins.answer s hseat hasMove ?_
      intro m s' hstep
      exact ih m s' hstep (htempo.step hstep)

/-- Charge one gives the first player a winning impartial strategy. -/
theorem first_wins_initial_one_of_every_submatching
    {G0 : SimpleGraph V} (hG0 : IsMatchingGraph G0) :
    ∀ H : SimpleGraph V, H ≤ G0 →
      TailWins H false (initial (V := V) 1) := by
  intro H hHG0
  exact (forcesScore_initial_of_every_submatching hG0 false 1 H hHG0)
    |>.one_to_tailWins_first (tempoAligned_initial 1)

/-- Charge zero gives the second player a winning impartial strategy, hence a
normal-play P-root. -/
theorem second_wins_initial_zero_of_every_submatching
    {G0 : SimpleGraph V} (hG0 : IsMatchingGraph G0) :
    ∀ H : SimpleGraph V, H ≤ G0 →
      TailWins H true (initial (V := V) 0) := by
  intro H hHG0
  exact (forcesScore_initial_of_every_submatching hG0 true 0 H hHG0)
    |>.zero_to_tailWins_second (tempoAligned_initial 0)

/-- Boolean charge embedded in the binary score sheet. -/
def scoreBit (sigma : Bool) : ZMod 2 :=
  if sigma then 1 else 0

/-- The normal-play root is a P-position exactly when its supplied charge is
zero.  This is the phase-free impartial replacement for the partizan terminal
claim compiler. -/
theorem root_isP_iff_charge_zero
    {G0 H : SimpleGraph V} (hG0 : IsMatchingGraph G0) (hHG0 : H ≤ G0)
    (sigma : Bool) :
    TailWins H true (initial (V := V) (scoreBit sigma)) ↔ sigma = false := by
  constructor
  · intro hsecond
    cases hsigma : sigma with
    | false => rfl
    | true =>
        have hfirst : TailWins H false (initial (V := V) 1) :=
          first_wins_initial_one_of_every_submatching hG0 H hHG0
        have hnotSecond : ¬TailWins H true (initial (V := V) 1) := by
          simpa using hfirst.not_complement
        exact False.elim (hnotSecond (by simpa [scoreBit, hsigma] using hsecond))
  · intro hsigma
    subst sigma
    simpa [scoreBit] using
      (second_wins_initial_zero_of_every_submatching hG0 H hHG0)

end

end Ogdoad.ImpartialRealizer
