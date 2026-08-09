import Mathlib

/-!
# The FIFO linking theorem

This file gives a formal semantics for the reduced odd-close parity game in
`experiments/linking_game.py` and `writeups/linking_affine.tex`.

The target theorem is deliberately stated but not postulated.  Results below
its statement are proved from the transition system; the one theorem carrying
the open mathematical content is exposed as the proposition
`FifoLinkingTheorem`.
-/

namespace Ogdoad.Fifo

open scoped BigOperators

noncomputable section

/-- A position of the reduced FIFO game.  `ko` is true exactly during the
one-move delay created by opening onto an empty queue. -/
structure State (V : Type*) where
  untouched : Finset V
  queue : List V
  ko : Bool
  toMove : Bool
  score : ZMod 2
deriving DecidableEq

/-- The three move forms.  A close always acts on the queue front, so it needs
no vertex payload. -/
inductive Move (V : Type*) where
  | open (v : V)
  | close
  | pass
deriving DecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The parity charged by closing `v`: its degree into the untouched set. -/
def flip (G : SimpleGraph V) (U : Finset V) (v : V) : ZMod 2 :=
  by
    classical
    exact ((U.filter (G.Adj v)).card : ZMod 2)

/-- One authoritative transition function, matching `legal_moves` in the
Python research oracle.

* OPEN removes an untouched vertex, appends it to the queue, and sets ko iff
  the old queue was empty.
* CLOSE removes the front when ko is clear and adds its untouched degree.
* PASS is forced exactly when no open or close is legal; it only clears ko.
-/
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
          if s.ko then none else
            some {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove
              score := s.score + flip G s.untouched f }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

/-- The game is over after every vertex has been opened and the FIFO queue has
been drained. -/
def Terminal (s : State V) : Prop :=
  s.untouched = ∅ ∧ s.queue = []

/-- Reachable positions have no repeated open vertex and no untouched vertex
already in the queue. -/
def WellFormed (s : State V) : Prop :=
  s.queue.Nodup ∧ Disjoint s.untouched s.queue.toFinset

/-- The initial position on the whole board. -/
def initial : State V where
  untouched := Finset.univ
  queue := []
  ko := false
  toMove := false
  score := 0

/-- A rank strictly decreased by every move, including the unique forced
pass.  The coefficient four is what pays simultaneously for appending to an
empty queue and setting ko. -/
def rank (s : State V) : Nat :=
  4 * s.untouched.card + 2 * s.queue.length + if s.ko then 1 else 0

omit [Fintype V] in
/-- Every legal transition strictly decreases `rank`; in particular the game
tree is finite and the forced pass cannot create a cycle. -/
theorem rank_step_lt {G : SimpleGraph V} {s s' : State V} {m : Move V}
    (h : step G s m = some s') : rank s' < rank s := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m
  · rename_i v
    simp only [step] at h
    split at h
    · rename_i hv
      cases h
      rw [rank, rank, Finset.card_erase_of_mem hv, List.length_append]
      simp only [List.length_cons, List.length_nil]
      have hcard : 0 < U.card := Finset.card_pos.mpr ⟨v, hv⟩
      have hpred : U.card - 1 + 1 = U.card := by omega
      cases q <;> cases ko <;> simp <;> omega
    · contradiction
  · simp only [step] at h
    split at h
    · contradiction
    · rename_i f q' hq
      split at h
      · contradiction
      · cases h
        simp [rank]
        omega
  · simp only [step] at h
    split at h
    · rename_i hp
      cases h
      rcases hp with ⟨rfl, hq, rfl⟩
      simp [rank]
    · contradiction

omit [Fintype V] in
/-- A legal move always hands the turn to the other seat. -/
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
      · contradiction
      · cases h
        rfl
  · simp only [step] at h
    split at h
    · cases h
      rfl
    · contradiction

/-- The initial state satisfies the representation invariant. -/
theorem wellFormed_initial : WellFormed (initial (V := V)) := by
  simp [WellFormed, initial]

omit [Fintype V] in
/-- The transition function preserves the queue/untouched representation
invariant. -/
theorem wellFormed_step {G : SimpleGraph V} {s s' : State V} {m : Move V}
    (hs : WellFormed s) (hstep : step G s m = some s') : WellFormed s' := by
  rcases hs with ⟨hnodup, hdisjoint⟩
  cases m
  · rename_i v
    simp only [step] at hstep
    split at hstep
    · rename_i hv
      cases hstep
      constructor
      · have hvq : v ∉ s.queue := by
          intro hvq
          exact (Finset.disjoint_left.mp hdisjoint hv) (by simpa using hvq)
        exact hnodup.append (by simp) (List.disjoint_singleton.mpr hvq)
      · rw [Finset.disjoint_left]
        intro x hxU hxq
        have hxU' : x ∈ s.untouched := Finset.mem_of_mem_erase hxU
        simp only [List.mem_toFinset, List.mem_append, List.mem_singleton] at hxq
        rcases hxq with hxq | hxv
        · exact (Finset.disjoint_left.mp hdisjoint hxU') (by simpa using hxq)
        · exact (Finset.ne_of_mem_erase hxU) hxv
    · contradiction
  · simp only [step] at hstep
    split at hstep
    · contradiction
    · rename_i f q hq
      split at hstep
      · contradiction
      · rw [hq] at hnodup hdisjoint
        cases hstep
        constructor
        · exact hnodup.tail
        · rw [Finset.disjoint_left]
          intro x hxU hxq
          exact (Finset.disjoint_left.mp hdisjoint hxU) (by simp [hxq])
  · simp only [step] at hstep
    split at hstep
    · cases hstep
      exact ⟨hnodup, hdisjoint⟩
    · contradiction

omit [Fintype V] in
/-- A close is FIFO by construction: the next queue is the old queue's tail. -/
theorem close_removes_front {G : SimpleGraph V} {s s' : State V}
    (h : step G s .close = some s') :
    ∃ f q, s.queue = f :: q ∧ s'.queue = q := by
  simp only [step] at h
  split at h
  · contradiction
  · rename_i f q hq
    split at h
    · contradiction
    · cases h
      exact ⟨f, q, hq, rfl⟩

omit [Fintype V] in
/-- A pass never changes the accumulated flip score. -/
theorem pass_score {G : SimpleGraph V} {s s' : State V}
    (h : step G s .pass = some s') : s'.score = s.score := by
  simp only [step] at h
  split at h
  · cases h
    rfl
  · contradiction

omit [Fintype V] in
/-- An open never changes the accumulated flip score. -/
theorem open_score {G : SimpleGraph V} {s s' : State V} {v : V}
    (h : step G s (.open v) = some s') : s'.score = s.score := by
  simp only [step] at h
  split at h
  · cases h
    rfl
  · contradiction

omit [Fintype V] in
/-- A close changes the score by exactly the untouched-degree parity of the
front it removes. -/
theorem close_score {G : SimpleGraph V} {s s' : State V}
    (h : step G s .close = some s') :
    ∃ f q, s.queue = f :: q ∧
      s'.score = s.score + flip G s.untouched f := by
  simp only [step] at h
  split at h
  · contradiction
  · rename_i f q hq
    split at h
    · contradiction
    · cases h
      exact ⟨f, q, hq, rfl⟩

/-- The current queue-to-untouched cut, counted modulo two.  The list form is
intentional: it makes the FIFO close identity independent of a separate
no-duplicates premise. -/
def queueCut (G : SimpleGraph V) (U : Finset V) (q : List V) : ZMod 2 :=
  (q.map (flip G U)).sum

/-- Score plus the live queue cut.  CLOSE conserves this quantity; OPEN is
the only move that can change it. -/
def potential (G : SimpleGraph V) (s : State V) : ZMod 2 :=
  s.score + queueCut G s.untouched s.queue

omit [Fintype V] [DecidableEq V] in
@[simp] theorem flip_empty (G : SimpleGraph V) (v : V) :
    flip G ∅ v = 0 := by
  simp [flip]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem queueCut_empty (G : SimpleGraph V) (q : List V) :
    queueCut G ∅ q = 0 := by
  induction q with
  | nil => rfl
  | cons v q ih =>
      unfold queueCut at ih ⊢
      simp [ih]

omit [Fintype V] in
/-- Closing the FIFO front transfers precisely its cut contribution into the
score, so `score + queueCut` is conserved. -/
theorem close_conserves_potential {G : SimpleGraph V} {s s' : State V}
    (h : step G s .close = some s') : potential G s' = potential G s := by
  simp only [step] at h
  split at h
  · contradiction
  · rename_i f q hq
    split at h
    · contradiction
    · cases h
      simp [potential, queueCut, hq, add_assoc]

omit [Fintype V] in
/-- PASS only clears the delay bit, so it also conserves the cut potential. -/
theorem pass_conserves_potential {G : SimpleGraph V} {s s' : State V}
    (h : step G s .pass = some s') : potential G s' = potential G s := by
  simp only [step] at h
  split at h
  · cases h
    rfl
  · contradiction

omit [Fintype V] [DecidableEq V] in
/-- At a terminal state the queue cut has vanished, so the potential is the
actual final score. -/
theorem terminal_potential {G : SimpleGraph V} {s : State V}
    (h : Terminal s) : potential G s = s.score := by
  rcases h with ⟨_, hq⟩
  simp [potential, queueCut, hq]

omit [Fintype V] in
/-- Once every vertex has been opened, no later CLOSE can add a flip; OPEN is
impossible and PASS is score-neutral. -/
theorem step_score_eq_of_untouched_empty {G : SimpleGraph V} {s s' : State V}
    {m : Move V} (hU : s.untouched = ∅) (h : step G s m = some s') :
    s'.score = s.score := by
  cases m
  · simp [step, hU] at h
  · obtain ⟨f, q, hq, hs⟩ := close_score h
    rw [hs, hU, flip_empty, add_zero]
  · exact pass_score h

omit [Fintype V] in
/-- Terminal states have no legal transition. -/
theorem terminal_no_step {G : SimpleGraph V} {s : State V}
    (hs : Terminal s) : ¬∃ m s', step G s m = some s' := by
  rcases hs with ⟨hU, hq⟩
  intro h
  rcases h with ⟨m, s', hm⟩
  cases m <;> simp [step, hU, hq] at hm

omit [Fintype V] in
/-- Every nonterminal state has an OPEN, CLOSE, or the forced PASS.  Thus the
pass rule removes the only apparent stuck state. -/
theorem not_terminal_has_step {G : SimpleGraph V} {s : State V}
    (hs : ¬Terminal s) : ∃ m s', step G s m = some s' := by
  by_cases hU : s.untouched = ∅
  · cases hq : s.queue with
    | nil => exact False.elim (hs ⟨hU, hq⟩)
    | cons f q =>
        cases hk : s.ko with
        | false =>
            refine ⟨Move.close, {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove
              score := s.score + flip G s.untouched f }, ?_⟩
            simp [step, hq, hk]
        | true =>
            refine ⟨Move.pass, { s with ko := false, toMove := !s.toMove }, ?_⟩
            simp [step, hU, hq, hk]
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hU
    refine ⟨Move.open v, {
      untouched := s.untouched.erase v
      queue := s.queue ++ [v]
      ko := s.queue.isEmpty
      toMove := !s.toMove
      score := s.score }, ?_⟩
    simp [step, hv]

omit [Fintype V] in
theorem exists_step_iff_not_terminal {G : SimpleGraph V} {s : State V} :
    (∃ m s', step G s m = some s') ↔ ¬Terminal s := by
  exact ⟨fun h ht ↦ terminal_no_step ht h, not_terminal_has_step⟩

/-- `EvenWins G seat s` is the finite strategy tree asserting that the seat
`seat` can force terminal score zero from `s`.  The existential/universal
constructors make the strategy quantifier order explicit. -/
inductive EvenWins (G : SimpleGraph V) (seat : Bool) : State V → Prop
  | terminal (s : State V) (hterminal : Terminal s) (hscore : s.score = 0) :
      EvenWins G seat s
  | choose (s : State V) (hseat : s.toMove = seat) (m : Move V) (s' : State V)
      (hstep : step G s m = some s') (hwin : EvenWins G seat s') :
      EvenWins G seat s
  | answer (s : State V) (hseat : s.toMove ≠ seat)
      (hasMove : ∃ m s', step G s m = some s')
      (hwin : ∀ m s', step G s m = some s' → EvenWins G seat s') :
      EvenWins G seat s

/-- `d` is an isolated dummy coin. -/
def IsDummy (G : SimpleGraph V) (d : V) : Prop :=
  ∀ v, ¬G.Adj d v

omit [Fintype V] [DecidableEq V] in
/-- Closing the isolated dummy can never add a flip, for any untouched set. -/
theorem flip_dummy {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    (U : Finset V) : flip G U d = 0 := by
  classical
  have hfilter : U.filter (G.Adj d) = ∅ := by
    ext x
    simp [hd x]
  simp [flip, hfilter]

/-- Exact formal statement of the still-open general FIFO linking theorem:
on every finite graph with an isolated dummy, either seat can force even flip
parity. -/
def FifoLinkingTheorem : Prop :=
  ∀ (V : Type*) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (d : V), IsDummy G d →
      ∀ seat : Bool, EvenWins G seat (initial (V := V))

/-- An edgeless graph is the fully proved base class: every close has charge
zero, so either seat forces even parity regardless of its choices. -/
def NoEdges (G : SimpleGraph V) : Prop :=
  ∀ u v, ¬G.Adj u v

omit [Fintype V] [DecidableEq V] in
theorem flip_eq_zero_of_noEdges {G : SimpleGraph V} (hG : NoEdges G)
    (U : Finset V) (v : V) : flip G U v = 0 := by
  classical
  have hfilter : U.filter (G.Adj v) = ∅ := by
    ext x
    simp [hG v x]
  simp [flip, hfilter]

omit [Fintype V] in
theorem step_score_eq_of_noEdges {G : SimpleGraph V} (hG : NoEdges G)
    {s s' : State V} {m : Move V} (hstep : step G s m = some s') :
    s'.score = s.score := by
  cases m
  · exact open_score hstep
  · obtain ⟨f, q, hq, hs⟩ := close_score hstep
    rw [hs, flip_eq_zero_of_noEdges hG, add_zero]
  · exact pass_score hstep

omit [Fintype V] in
/-- The strategy semantics is inhabited on the edgeless base class.  This
proof uses `rank_step_lt`, so it also checks that the existential/universal
strategy tree agrees with the terminating operational game. -/
theorem evenWins_of_noEdges {G : SimpleGraph V} (hG : NoEdges G)
    (seat : Bool) (s : State V) (hscore : s.score = 0) : EvenWins G seat s := by
  induction s using (measure rank).wf.induction with
  | h s ih =>
      by_cases ht : Terminal s
      · exact EvenWins.terminal s ht hscore
      · have hasMove : ∃ m s', step G s m = some s' := not_terminal_has_step ht
        by_cases hseat : s.toMove = seat
        · obtain ⟨m, s', hstep⟩ := hasMove
          refine EvenWins.choose s hseat m s' hstep (ih s' (rank_step_lt hstep) ?_)
          rw [step_score_eq_of_noEdges hG hstep, hscore]
        · refine EvenWins.answer s hseat hasMove ?_
          intro m s' hstep
          exact ih s' (rank_step_lt hstep) (by
            rw [step_score_eq_of_noEdges hG hstep, hscore])

theorem evenWins_initial_of_noEdges {G : SimpleGraph V} (hG : NoEdges G)
    (seat : Bool) : EvenWins G seat (initial (V := V)) := by
  apply evenWins_of_noEdges hG
  rfl

end

end Ogdoad.Fifo
