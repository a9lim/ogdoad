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

/-- The adjacency indicator as a scalar parity bit. -/
def adjacencyBit (G : SimpleGraph V) (u v : V) : ZMod 2 := by
  classical
  exact if G.Adj u v then 1 else 0

omit [Fintype V] in
/-- Removing `z` from the untouched set removes exactly the adjacency bit
between the closing front `f` and `z`.  The equation is oriented so the
cardinality decomposition occurs before reduction modulo two. -/
theorem flip_eq_flip_erase_add {G : SimpleGraph V} {U : Finset V} {f z : V}
    (hz : z ∈ U) :
    flip G U f = flip G (U.erase z) f + adjacencyBit G f z := by
  classical
  rw [flip, flip, adjacencyBit, Finset.filter_erase]
  by_cases hadj : G.Adj f z
  · have hzfilter : z ∈ U.filter (G.Adj f) := by simp [hz, hadj]
    have hcard := Finset.card_erase_add_one hzfilter
    simp only [hadj, if_true]
    have hcast :
        ((((U.filter (G.Adj f)).erase z).card + 1 : Nat) : ZMod 2) =
          ((U.filter (G.Adj f)).card : ZMod 2) :=
      congrArg (fun n : Nat ↦ (n : ZMod 2)) hcard
    simpa only [Nat.cast_add, Nat.cast_one] using hcast.symm
  · have hzfilter : z ∉ U.filter (G.Adj f) := by simp [hadj]
    simp [hadj, hzfilter]

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

/-- The full representation invariant of a reachable position.  Besides
queue/untouched disjointness, the ko delay can only occur immediately after
opening onto an empty queue, so a ko-set queue is necessarily a singleton. -/
def Coherent (s : State V) : Prop :=
  WellFormed s ∧ (s.ko = true → ∃ v, s.queue = [v])

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

/-- The initial state satisfies the complete reachable-state invariant. -/
theorem coherent_initial : Coherent (initial (V := V)) := by
  exact ⟨wellFormed_initial, by simp [initial]⟩

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
/-- Every legal transition preserves the fact that ko can only protect a
singleton queue. -/
theorem coherent_step {G : SimpleGraph V} {s s' : State V} {m : Move V}
    (hs : Coherent s) (hstep : step G s m = some s') : Coherent s' := by
  constructor
  · exact wellFormed_step hs.1 hstep
  · intro hko
    cases m
    · rename_i v
      simp only [step] at hstep
      split at hstep
      · cases hstep
        cases hq : s.queue with
        | nil => exact ⟨v, by simp⟩
        | cons f q => simp [hq] at hko
      · contradiction
    · simp only [step] at hstep
      split at hstep
      · contradiction
      · split at hstep
        · contradiction
        · cases hstep
          simp at hko
    · simp only [step] at hstep
      split at hstep
      · cases hstep
        simp at hko
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

omit [Fintype V] in
/-- Away from the singleton-queue ko wall, OPEN `z` then CLOSE `f` and CLOSE
`f` then OPEN `z` lead to the same public state.  Their scores differ by the
single adjacency bit `fz`; this is the local curvature of the two commuting
schedule paths. -/
theorem open_close_square_away_singleton (G : SimpleGraph V) (s : State V)
    (f z : V) (q : List V) (hqueue : s.queue = f :: q) (hq : q ≠ [])
    (hko : s.ko = false) (hz : z ∈ s.untouched) :
    ∃ so soc sc sco,
      step G s (.open z) = some so ∧
      step G so .close = some soc ∧
      step G s .close = some sc ∧
      step G sc (.open z) = some sco ∧
      soc.untouched = sco.untouched ∧
      soc.queue = sco.queue ∧
      soc.ko = sco.ko ∧
      soc.toMove = sco.toMove ∧
      sco.score = soc.score + adjacencyBit G f z := by
  have hqEmpty : q.isEmpty = false := by
    cases q with
    | nil => contradiction
    | cons _ _ => rfl
  let so : State V := {
    untouched := s.untouched.erase z
    queue := f :: (q ++ [z])
    ko := false
    toMove := !s.toMove
    score := s.score }
  let soc : State V := {
    untouched := s.untouched.erase z
    queue := q ++ [z]
    ko := false
    toMove := s.toMove
    score := s.score + flip G (s.untouched.erase z) f }
  let sc : State V := {
    untouched := s.untouched
    queue := q
    ko := false
    toMove := !s.toMove
    score := s.score + flip G s.untouched f }
  let sco : State V := {
    untouched := s.untouched.erase z
    queue := q ++ [z]
    ko := false
    toMove := s.toMove
    score := s.score + flip G s.untouched f }
  refine ⟨so, soc, sc, sco, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp [step, so, hqueue, hz]
  · simp [step, so, soc]
  · simp [step, sc, hqueue, hko]
  · simp [step, sc, sco, hz, hqEmpty]
  · simp only [soc, sco]
    rw [flip_eq_flip_erase_add hz]
    simp [add_assoc]

/-- Every adjacency coordinate occurs on a reachable OPEN/CLOSE square.  The
prefix `OPEN f; OPEN d` leaves the dummy behind `f`, so a distinct untouched
`z` supplies the square whose curvature is the bit `fz`. -/
theorem initial_reaches_open_close_square (G : SimpleGraph V) (f d z : V)
    (hfd : f ≠ d) (hfz : f ≠ z) (hdz : d ≠ z) :
    ∃ sf sfd so soc sc sco,
      step G (initial (V := V)) (.open f) = some sf ∧
      step G sf (.open d) = some sfd ∧
      step G sfd (.open z) = some so ∧
      step G so .close = some soc ∧
      step G sfd .close = some sc ∧
      step G sc (.open z) = some sco ∧
      soc.untouched = sco.untouched ∧
      soc.queue = sco.queue ∧
      soc.ko = sco.ko ∧
      soc.toMove = sco.toMove ∧
      sco.score = soc.score + adjacencyBit G f z := by
  let sf : State V := {
    untouched := Finset.univ.erase f
    queue := [f]
    ko := true
    toMove := true
    score := 0 }
  let sfd : State V := {
    untouched := (Finset.univ.erase f).erase d
    queue := [f, d]
    ko := false
    toMove := false
    score := 0 }
  have hsf : step G (initial (V := V)) (.open f) = some sf := by
    simp [step, initial, sf]
  have hdmem : d ∈ Finset.univ.erase f := by simp [hfd.symm]
  have hsfd : step G sf (.open d) = some sfd := by
    simp [step, sf, sfd, hdmem]
  have hzmem : z ∈ sfd.untouched := by
    simp [sfd, hfz.symm, hdz.symm]
  obtain ⟨so, soc, sc, sco, hso, hsoc, hsc, hsco, hU, hq, hko, hturn,
      hscore⟩ :=
    open_close_square_away_singleton G sfd f z [d] rfl (by simp) rfl hzmem
  exact ⟨sf, sfd, so, soc, sc, sco, hsf, hsfd, hso, hsoc, hsc, hsco,
    hU, hq, hko, hturn, hscore⟩

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
/-- Once the untouched set is empty, every legal transition keeps it empty. -/
theorem step_untouched_eq_empty {G : SimpleGraph V} {s s' : State V}
    {m : Move V} (hU : s.untouched = ∅) (h : step G s m = some s') :
    s'.untouched = ∅ := by
  cases m
  · simp [step, hU] at h
  · simp only [step] at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · cases h
        exact hU
  · simp only [step] at h
    split at h
    · cases h
      exact hU
    · contradiction

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

omit [Fintype V] in
/-- After the last OPEN, either seat can force an already-even score to remain
even while the queue drains.  This is the terminal-tail interface used by
finite repair arguments. -/
theorem evenWins_of_untouched_empty {G : SimpleGraph V} (seat : Bool)
    (s : State V) (hU : s.untouched = ∅) (hscore : s.score = 0) :
    EvenWins G seat s := by
  induction s using (measure rank).wf.induction with
  | h s ih =>
      by_cases hterminal : Terminal s
      · exact EvenWins.terminal s hterminal hscore
      · have hasMove : ∃ m s', step G s m = some s' :=
          not_terminal_has_step hterminal
        by_cases hseat : s.toMove = seat
        · obtain ⟨m, s', hstep⟩ := hasMove
          refine EvenWins.choose s hseat m s' hstep
            (ih s' (rank_step_lt hstep) ?_ ?_)
          · exact step_untouched_eq_empty hU hstep
          · rw [step_score_eq_of_untouched_empty hU hstep, hscore]
        · refine EvenWins.answer s hseat hasMove ?_
          intro m s' hstep
          exact ih s' (rank_step_lt hstep)
            (step_untouched_eq_empty hU hstep)
            (by rw [step_score_eq_of_untouched_empty hU hstep, hscore])

/-- The dual finite strategy tree: the player outside `seat` can force a
terminal odd score.  This is not the negation of `EvenWins` by definition;
`strategy_determined` below proves that one of the two explicit strategy
objects exists from every state. -/
inductive OddWins (G : SimpleGraph V) (seat : Bool) : State V → Prop
  | terminal (s : State V) (hterminal : Terminal s) (hscore : s.score ≠ 0) :
      OddWins G seat s
  | choose (s : State V) (hseat : s.toMove ≠ seat) (m : Move V) (s' : State V)
      (hstep : step G s m = some s') (hwin : OddWins G seat s') :
      OddWins G seat s
  | answer (s : State V) (hseat : s.toMove = seat)
      (hasMove : ∃ m s', step G s m = some s')
      (hwin : ∀ m s', step G s m = some s' → OddWins G seat s') :
      OddWins G seat s

omit [Fintype V] in
/-- Backward induction is internal to the formal model: from every state,
either the designated seat has an explicit even-forcing strategy tree or the
other seat has an explicit odd-forcing strategy tree.  Thus a counterexample
to the linking theorem may be taken to be a concrete `OddWins` object, with
no appeal to an external determinacy theorem. -/
theorem strategy_determined (G : SimpleGraph V) (seat : Bool) (s : State V) :
    EvenWins G seat s ∨ OddWins G seat s := by
  induction s using (measure rank).wf.induction with
  | h s ih =>
      by_cases hterminal : Terminal s
      · by_cases hscore : s.score = 0
        · exact Or.inl (EvenWins.terminal s hterminal hscore)
        · exact Or.inr (OddWins.terminal s hterminal hscore)
      · have hasMove : ∃ m s', step G s m = some s' :=
          not_terminal_has_step hterminal
        by_cases hseat : s.toMove = seat
        · by_cases hchild : ∃ m s',
              step G s m = some s' ∧ EvenWins G seat s'
          · obtain ⟨m, s', hstep, hwin⟩ := hchild
            exact Or.inl (EvenWins.choose s hseat m s' hstep hwin)
          · refine Or.inr (OddWins.answer s hseat hasMove ?_)
            intro m s' hstep
            rcases ih s' (rank_step_lt hstep) with hwin | hwin
            · exact False.elim (hchild ⟨m, s', hstep, hwin⟩)
            · exact hwin
        · by_cases hchild : ∃ m s',
              step G s m = some s' ∧ OddWins G seat s'
          · obtain ⟨m, s', hstep, hwin⟩ := hchild
            exact Or.inr (OddWins.choose s hseat m s' hstep hwin)
          · refine Or.inl (EvenWins.answer s hseat hasMove ?_)
            intro m s' hstep
            rcases ih s' (rank_step_lt hstep) with hwin | hwin
            · exact hwin
            · exact False.elim (hchild ⟨m, s', hstep, hwin⟩)

omit [Fintype V] in
/-- Negating an even-forcing strategy produces an explicit odd-forcing
counterstrategy, rather than only a classical double negation. -/
theorem oddWins_of_not_evenWins (G : SimpleGraph V) (seat : Bool) (s : State V)
    (h : ¬EvenWins G seat s) : OddWins G seat s := by
  exact (strategy_determined G seat s).resolve_left h

omit [Fintype V] in
/-- The two explicit strategy trees are incompatible.  The proof follows the
chosen branch at a `choose` node and the corresponding universally supplied
branch at an `answer` node. -/
theorem EvenWins.not_oddWins {G : SimpleGraph V} {seat : Bool} {s : State V}
    (h : EvenWins G seat s) : ¬OddWins G seat s := by
  induction h with
  | terminal s hterminal hscore =>
      intro hodd
      cases hodd with
      | terminal _ _ hoddscore => exact hoddscore hscore
      | choose _ _ m s' hstep _ =>
          exact terminal_no_step hterminal ⟨m, s', hstep⟩
      | answer _ _ hasMove _ =>
          exact terminal_no_step hterminal hasMove
  | choose s hseat m s' hstep _ ih =>
      intro hodd
      cases hodd with
      | terminal _ hterminal _ =>
          exact terminal_no_step hterminal ⟨m, s', hstep⟩
      | choose _ hoddseat _ _ _ _ => exact hoddseat hseat
      | answer _ _ _ hanswer => exact ih (hanswer m s' hstep)
  | answer s hseat hasMove _ ih =>
      intro hodd
      cases hodd with
      | terminal _ hterminal _ =>
          exact terminal_no_step hterminal hasMove
      | choose _ _ m s' hstep hchild => exact ih m s' hstep hchild
      | answer _ hoddseat _ _ => exact hseat hoddseat

omit [Fintype V] in
/-- Exact logical form used by a proof by counterstrategy exclusion. -/
theorem evenWins_iff_not_oddWins (G : SimpleGraph V) (seat : Bool) (s : State V) :
    EvenWins G seat s ↔ ¬OddWins G seat s := by
  exact ⟨EvenWins.not_oddWins, fun hodd ↦
    (strategy_determined G seat s).resolve_right hodd⟩

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

/-- Pointwise form of the open theorem as counterstrategy exclusion.  This is
the formal interface for a minimal-counterexample or affine-separation proof;
the dummy hypothesis is recorded even though determinacy itself is general. -/
theorem linking_at_iff_noOddCounterstrategy {G : SimpleGraph V} {d : V}
    (_hd : IsDummy G d) (seat : Bool) :
    EvenWins G seat (initial (V := V)) ↔
      ¬OddWins G seat (initial (V := V)) := by
  exact evenWins_iff_not_oddWins G seat initial

/-- Canonical attacker checkpoint with one untouched vertex and no ko delay. -/
def singletonState (b : V) (q : List V) (turn : Bool) : State V where
  untouched := {b}
  queue := q
  ko := false
  toMove := turn
  score := 0

/-- Exact queue-word criterion at a singleton untouched tail.  Reading the
queue in consecutive cells, a front bit zero is immediately absorbable; a
front bit one must be followed by another one before the scan continues. -/
def SingletonTail (G : SimpleGraph V) (b : V) : List V → Prop
  | [] => True
  | [_] => False
  | v :: w :: q => ¬G.Adj v b ∨ (G.Adj w b ∧ SingletonTail G b q)

omit [Fintype V] [DecidableEq V] in
theorem flip_singleton_of_adj {G : SimpleGraph V} {v b : V}
    (h : G.Adj v b) : flip G {b} v = 1 := by
  classical
  have hfilter : ({b} : Finset V).filter (G.Adj v) = {b} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun hx ↦ hx.1
    · intro hx
      subst x
      exact ⟨rfl, h⟩
  simp [flip, hfilter]

omit [Fintype V] [DecidableEq V] in
theorem flip_singleton_of_not_adj {G : SimpleGraph V} {v b : V}
    (h : ¬G.Adj v b) : flip G {b} v = 0 := by
  classical
  have hfilter : ({b} : Finset V).filter (G.Adj v) = ∅ := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxb, hadj⟩
      have hxb' : x = b := Finset.mem_singleton.mp hxb
      subst x
      exact False.elim (h hadj)
    · simp
  simp [flip, hfilter]

omit [Fintype V] in
/-- The singleton-tail criterion is sufficient, against every attacker move.
This is the exact terminating corridor used after all but one untouched vertex
has been opened. -/
theorem evenWins_singletonTail (G : SimpleGraph V) (seat : Bool) (b : V) :
    ∀ q, SingletonTail G b q →
      EvenWins G seat (singletonState b q (!seat)) := by
  intro q
  induction q using List.twoStepInduction with
  | nil =>
      intro _
      let s := singletonState b [] (!seat)
      have hnotseat : s.toMove ≠ seat := by
        simp [s, singletonState]
      have hasMove : ∃ m s', step G s m = some s' := by
        apply not_terminal_has_step
        simp [Terminal, s, singletonState]
      refine EvenWins.answer s hnotseat hasMove ?_
      intro m s' hstep
      cases m
      · rename_i v
        simp only [step, s, singletonState] at hstep
        split at hstep
        · rename_i hv
          cases hstep
          apply evenWins_of_untouched_empty seat
          · have hv' : v = b := Finset.mem_singleton.mp hv
            subst v
            simp
          · rfl
        · contradiction
      · simp [step, s, singletonState] at hstep
      · simp [step, s, singletonState] at hstep
  | singleton v => simp [SingletonTail]
  | cons_cons v w q ih _ =>
      intro htail
      let s := singletonState b (v :: w :: q) (!seat)
      have hnotseat : s.toMove ≠ seat := by
        simp [s, singletonState]
      have hasMove : ∃ m s', step G s m = some s' := by
        apply not_terminal_has_step
        simp [Terminal, s, singletonState]
      refine EvenWins.answer s hnotseat hasMove ?_
      intro m s' hstep
      cases m
      · rename_i x
        simp only [step, s, singletonState] at hstep
        split at hstep
        · rename_i hx
          cases hstep
          apply evenWins_of_untouched_empty seat
          · have hx' : x = b := Finset.mem_singleton.mp hx
            subst x
            simp
          · rfl
        · contradiction
      · simp only [step, s, singletonState] at hstep
        by_cases hvb : G.Adj v b
        · have hwb : G.Adj w b := by
            rcases htail with hnv | ⟨hw, _⟩
            · exact False.elim (hnv hvb)
            · exact hw
          have htail' : SingletonTail G b q := by
            rcases htail with hnv | ⟨_, ht⟩
            · exact False.elim (hnv hvb)
            · exact ht
          cases hstep
          let s2 := singletonState b q (!seat)
          have hclose : step G {
              untouched := {b}
              queue := w :: q
              ko := false
              toMove := seat
              score := 1 } .close = some s2 := by
            simp [step, s2, singletonState, flip_singleton_of_adj hwb,
              CharTwo.add_self_eq_zero]
          have heven : EvenWins G seat {
              untouched := {b}
              queue := w :: q
              ko := false
              toMove := seat
              score := 1 } :=
            EvenWins.choose _ (by rfl) .close s2 hclose (ih htail')
          simpa [flip_singleton_of_adj hvb] using heven
        · cases hstep
          let s2 : State V := {
            untouched := ∅
            queue := w :: q ++ [b]
            ko := false
            toMove := !seat
            score := 0 }
          have hopen : step G {
              untouched := {b}
              queue := w :: q
              ko := false
              toMove := seat
              score := 0 } (.open b) = some s2 := by
            simp [step, s2]
          have heven : EvenWins G seat {
              untouched := {b}
              queue := w :: q
              ko := false
              toMove := seat
              score := 0 } := by
            refine EvenWins.choose _ (by rfl) (.open b) s2 hopen ?_
            apply evenWins_of_untouched_empty seat
            · rfl
            · rfl
          simpa [flip_singleton_of_not_adj hvb] using heven
      · simp [step, s, singletonState] at hstep

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
