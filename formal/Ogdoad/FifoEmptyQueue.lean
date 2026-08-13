import Ogdoad.FifoSymmetry

/-!
# Empty-queue FIFO blocks

This file isolates graph-independent bookkeeping for legal FIFO paths.  A
path between empty queues has one CLOSE for every OPEN.  PASS moves are counted
separately, so a block opening `b` vertices has `2 * b` endpoint moves and
total length `2 * b + p`, where `p` is its number of PASSes.

If the destination still has an untouched vertex, no PASS can have occurred:
a legal PASS requires the untouched set to be empty, and it remains empty
thereafter.  Hence consecutive nonterminal empty-queue choices belong to the
same physical player.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Number of OPEN endpoint moves in a move word. -/
def openedCount : List (Move V) → Nat
  | [] => 0
  | .open _ :: ms => openedCount ms + 1
  | .close :: ms => openedCount ms
  | .pass :: ms => openedCount ms

/-- Number of CLOSE endpoint moves in a move word. -/
def closedCount : List (Move V) → Nat
  | [] => 0
  | .open _ :: ms => closedCount ms
  | .close :: ms => closedCount ms + 1
  | .pass :: ms => closedCount ms

/-- Number of forced PASS moves in a move word. -/
def passedCount : List (Move V) → Nat
  | [] => 0
  | .open _ :: ms => passedCount ms
  | .close :: ms => passedCount ms
  | .pass :: ms => passedCount ms + 1

omit [Fintype V] [DecidableEq V] in
/-- OPEN, CLOSE, and PASS partition every move word. -/
theorem length_eq_openedCount_add_closedCount_add_passedCount
    (ms : List (Move V)) :
    ms.length = openedCount ms + closedCount ms + passedCount ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      cases m <;> simp [openedCount, closedCount, passedCount, ih] <;> omega

omit [Fintype V] in
/-- One transition changes queue length by `+1` for OPEN, `-1` for CLOSE,
and zero for PASS. -/
theorem step_queue_length_balance {G : SimpleGraph V} {s t : State V}
    {m : Move V} (hstep : step G s m = some t) :
    t.queue.length + closedCount [m] =
      s.queue.length + openedCount [m] := by
  cases m with
  | «open» v =>
      simp only [step] at hstep
      split at hstep
      · cases hstep
        simp [openedCount, closedCount, List.length_append]
      · contradiction
  | close =>
      simp only [step] at hstep
      split at hstep
      · contradiction
      · split at hstep
        · contradiction
        · cases hstep
          simp [openedCount, closedCount, *]
  | pass =>
      simp only [step] at hstep
      split at hstep
      · cases hstep
        simp [openedCount, closedCount]
      · contradiction

omit [Fintype V] in
/-- Queue conservation along an arbitrary legal path. -/
theorem StepPath.queue_length_balance
    {G : SimpleGraph V} {s t : State V} {ms : List (Move V)}
    (hpath : StepPath G s ms t) :
    t.queue.length + closedCount ms =
      s.queue.length + openedCount ms := by
  induction hpath with
  | nil => simp [openedCount, closedCount]
  | @cons s s' t m ms hstep htail ih =>
      have hhead := step_queue_length_balance hstep
      cases m <;> simp [openedCount, closedCount] at hhead ⊢ <;> omega

omit [Fintype V] in
/-- Once a legal path starts with no untouched vertices, its endpoint also
has no untouched vertices. -/
theorem StepPath.untouched_eq_empty
    {G : SimpleGraph V} {s t : State V} {ms : List (Move V)}
    (hpath : StepPath G s ms t) (hs : s.untouched = ∅) :
    t.untouched = ∅ := by
  induction hpath with
  | nil => exact hs
  | cons hstep htail ih =>
      exact ih (step_untouched_eq_empty hs hstep)

omit [Fintype V] in
/-- A legal path ending while an untouched vertex remains contains no PASS.
A PASS would empty the untouched set permanently. -/
theorem StepPath.pass_not_mem_of_target_untouched_nonempty
    {G : SimpleGraph V} {s t : State V} {ms : List (Move V)}
    (hpath : StepPath G s ms t) (ht : t.untouched.Nonempty) :
    (Move.pass : Move V) ∉ ms := by
  induction hpath with
  | nil => simp
  | @cons s s' t m ms hstep htail ih =>
      cases m with
      | «open» v => simpa using ih ht
      | close => simpa using ih ht
      | pass =>
          intro _
          have hs : s.untouched = ∅ := by
            simp only [step] at hstep
            split at hstep
            · rename_i hp
              exact hp.1
            · contradiction
          have hs' : s'.untouched = ∅ :=
            step_untouched_eq_empty hs hstep
          have ht' : t.untouched = ∅ := htail.untouched_eq_empty hs'
          exact ht.ne_empty ht'

omit [Fintype V] [DecidableEq V] in
/-- The PASS count vanishes exactly when PASS is absent from the word. -/
theorem passedCount_eq_zero_iff (ms : List (Move V)) :
    passedCount ms = 0 ↔ (Move.pass : Move V) ∉ ms := by
  induction ms with
  | nil => simp [passedCount]
  | cons m ms ih =>
      cases m <;> simp [passedCount, ih]

/-- Iterated mover toggle for a move word. -/
def turnAfter : List (Move V) → Bool → Bool
  | [], turn => turn
  | _ :: ms, turn => turnAfter ms (!turn)

omit [Fintype V] in
/-- The mover at the endpoint of a legal path depends only on its length. -/
theorem StepPath.toMove_eq_turnAfter
    {G : SimpleGraph V} {s t : State V} {ms : List (Move V)}
    (hpath : StepPath G s ms t) :
    t.toMove = turnAfter ms s.toMove := by
  induction hpath with
  | nil => rfl
  | cons hstep htail ih =>
      rw [ih, step_toMove hstep]
      rfl

omit [Fintype V] [DecidableEq V] in
/-- An even word toggles the mover an even number of times. -/
theorem turnAfter_eq_of_length_eq_two_mul (ms : List (Move V))
    (turn : Bool) (b : Nat) (hlen : ms.length = 2 * b) :
    turnAfter ms turn = turn := by
  induction b generalizing ms turn with
  | zero =>
      cases ms with
      | nil => rfl
      | cons m ms => simp at hlen
  | succ b ih =>
      cases ms with
      | nil => simp at hlen
      | cons m ms =>
          cases ms with
          | nil => simp at hlen; omega
          | cons m' ms =>
              simp only [List.length_cons] at hlen
              simp only [turnAfter, Bool.not_not]
              exact ih ms turn (by omega)

omit [Fintype V] in
/-- Exact empty-queue block accounting.  The number of endpoint moves is
`2 * b`, and PASSes contribute separately to total path length. -/
theorem StepPath.empty_queue_block_counts
    {G : SimpleGraph V} {s t : State V} {ms : List (Move V)}
    (hpath : StepPath G s ms t) (hs : s.queue = []) (ht : t.queue = []) :
    closedCount ms = openedCount ms ∧
      openedCount ms + closedCount ms = 2 * openedCount ms ∧
      ms.length = 2 * openedCount ms + passedCount ms := by
  have hbalance := hpath.queue_length_balance
  rw [hs, ht] at hbalance
  simp only [List.length_nil, zero_add] at hbalance
  have hlength := length_eq_openedCount_add_closedCount_add_passedCount ms
  omega

omit [Fintype V] in
/-- A nonempty legal path starting at an empty queue must begin with OPEN, so
its opened-vertex count is positive. -/
theorem StepPath.openedCount_pos_of_nonempty_empty_start
    {G : SimpleGraph V} {s t : State V} {ms : List (Move V)}
    (hpath : StepPath G s ms t) (hs : s.queue = []) (hne : ms ≠ []) :
    0 < openedCount ms := by
  cases hpath with
  | nil => exact False.elim (hne rfl)
  | @cons s s' t m ms hstep htail =>
      cases m with
      | «open» v => simp [openedCount]
      | close => simp [step, hs] at hstep
      | pass => simp [step, hs] at hstep

omit [Fintype V] in
/-- Consecutive nonterminal empty-queue choices are controlled by the same
physical player.  More precisely, a nonempty block opens `b > 0` vertices,
uses exactly `2 * b` moves, contains no PASS, and preserves `toMove`. -/
theorem StepPath.consecutive_empty_queue_choices
    {G : SimpleGraph V} {s t : State V} {ms : List (Move V)}
    (hpath : StepPath G s ms t) (hs : s.queue = []) (ht : t.queue = [])
    (hne : ms ≠ []) (htU : t.untouched.Nonempty) :
    ∃ b, 0 < b ∧ openedCount ms = b ∧ closedCount ms = b ∧
      passedCount ms = 0 ∧ ms.length = 2 * b ∧ t.toMove = s.toMove := by
  let b := openedCount ms
  have hb : 0 < b := hpath.openedCount_pos_of_nonempty_empty_start hs hne
  obtain ⟨hclose, _, hlength⟩ := hpath.empty_queue_block_counts hs ht
  have hnopass : (Move.pass : Move V) ∉ ms :=
    hpath.pass_not_mem_of_target_untouched_nonempty htU
  have hpass : passedCount ms = 0 := (passedCount_eq_zero_iff ms).2 hnopass
  have hlen : ms.length = 2 * b := by simpa [b, hpass] using hlength
  have hturn : t.toMove = s.toMove := by
    rw [hpath.toMove_eq_turnAfter]
    exact turnAfter_eq_of_length_eq_two_mul ms s.toMove b hlen
  exact ⟨b, hb, rfl, by simpa [b] using hclose, hpass, hlen, hturn⟩

end

end Ogdoad.Fifo
