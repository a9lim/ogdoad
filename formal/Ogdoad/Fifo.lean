import Mathlib

/-!
# The FIFO linking theorem

This file gives a formal semantics for the reduced odd-close parity game in
`experiments/linking_game.py` and `writeups/linking_affine.tex`.

The target theorem is deliberately stated but not postulated.  Results below
its statement are proved from the transition system; the one theorem carrying
the open mathematical content is exposed as the proposition
`FifoLinkingTheorem`.

The stopped CLOSE-first empty-root theorem from the companion writeup has a
separate semantics below.  Its operational absorbers, bad-pair moment and rank
reduction, finite zero-fan mutual induction, and final rank contradiction are
kernel-checked.  This theorem remains separate from the open
`FifoLinkingTheorem`.

The local ancestry layer also records score-translation equivariance and the
exact singleton-queue OPEN/CLOSE reconvergence after one further OPEN.  These
transport a chosen ko-wall square through a shared continuation; they do not
assert the still-open global selection of compatible squares across a full
strategy fan.  An abstract fixed-front closure game separately kernel-checks
the affine no-separation recurrence and its sharp distinguished-leaf failure;
it deliberately omits the descendant continuation cosets which remain open.
Inside an explicit odd strategy tree, a separate minimum theorem extracts a
selected unit CLOSE followed, on the opposite score sheet, by a completely
score-neutral continuation.  Neutral opponent-controlled singleton tails
force the corresponding punctured vertex degrees to vanish; composing enough
such tails across the singleton wall remains part of the open global step.
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

/-- A nonzero parity bit is the unit bit. -/
theorem zmod2_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  apply ZMod.val_injective
  have hxval : x.val ≠ 0 := by
    intro h
    exact hx ((ZMod.val_eq_zero x).mp h)
  have hxlt : x.val < 2 := x.val_lt
  change x.val = 1
  omega

/-- A parity bit different from the unit bit is zero. -/
theorem zmod2_eq_zero_of_ne_one (x : ZMod 2) (hx : x ≠ 1) : x = 0 := by
  by_contra hx0
  exact hx (zmod2_eq_one_of_ne_zero x hx0)

omit [Fintype V] [DecidableEq V] in
/-- The adjacency bit inherits symmetry from a simple graph. -/
theorem adjacencyBit_comm (G : SimpleGraph V) (x y : V) :
    adjacencyBit G x y = adjacencyBit G y x := by
  classical
  simp only [adjacencyBit]
  rw [G.adj_comm]

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

omit [Fintype V] [DecidableEq V] in
/-- If a vertex is adjacent to every member of `U`, its flip is exactly the
cardinality parity of `U`. -/
theorem flip_eq_card_of_forall_adj {G : SimpleGraph V} {U : Finset V} {f : V}
    (h : ∀ x ∈ U, G.Adj f x) : flip G U f = (U.card : ZMod 2) := by
  classical
  have hfilter : U.filter (G.Adj f) = U := by
    exact Finset.filter_eq_self.mpr h
  simp [flip, hfilter]

omit [Fintype V] in
/-- The local obstruction exposed by a minimal CLOSE-first counterexample:
if deleting any one untouched vertex leaves odd front charge, then the front
dominates the untouched set and its undeleted charge is zero. -/
theorem flip_zero_and_adj_of_all_erase_flip_one
    {G : SimpleGraph V} {U : Finset V} {f : V}
    (hU : U.Nonempty)
    (herase : ∀ x ∈ U, flip G (U.erase x) f = 1) :
    flip G U f = 0 ∧ ∀ x ∈ U, G.Adj f x := by
  classical
  obtain ⟨x, hx⟩ := hU
  have hall : ∀ y ∈ U, G.Adj f y := by
    intro y hy
    by_contra hfy
    have hflipOne : flip G U f = 1 := by
      rw [flip_eq_flip_erase_add hy, herase y hy]
      simp [adjacencyBit, hfy]
    have hnot : ∀ z ∈ U, ¬G.Adj f z := by
      intro z hz hfz
      have hflipZero : flip G U f = 0 := by
        rw [flip_eq_flip_erase_add hz, herase z hz]
        simpa [adjacencyBit, hfz] using
          (CharTwo.add_self_eq_zero (1 : ZMod 2))
      rw [hflipOne] at hflipZero
      exact one_ne_zero hflipZero
    have hfilter : U.filter (G.Adj f) = ∅ := by
      exact Finset.filter_eq_empty_iff.mpr (fun z hz ↦ hnot z hz)
    have hflipZero : flip G U f = 0 := by simp [flip, hfilter]
    rw [hflipOne] at hflipZero
    exact one_ne_zero hflipZero
  constructor
  · rw [flip_eq_flip_erase_add hx, herase x hx]
    simpa [adjacencyBit, hall x hx] using
      (CharTwo.add_self_eq_zero (1 : ZMod 2))
  · exact hall

omit [Fintype V] in
/-- Three two-point erasure equations already force the undeleted charge to
vanish.  This is the algebraic core of the second-front step in the
conditioned CLOSE-first proof. -/
theorem flip_zero_of_three_double_erases
    {G : SimpleGraph V} {U : Finset V} {f x y z : V}
    (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (herase : ∀ a ∈ U, ∀ b ∈ U, a ≠ b →
      flip G ((U.erase a).erase b) f = 0) :
    flip G U f = 0 := by
  classical
  have pair (a b : V) (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) :
      flip G U f = adjacencyBit G f a + adjacencyBit G f b := by
    have hb' : b ∈ U.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
    calc
      flip G U f = flip G (U.erase a) f + adjacencyBit G f a :=
        flip_eq_flip_erase_add ha
      _ = (flip G ((U.erase a).erase b) f + adjacencyBit G f b) +
          adjacencyBit G f a := congrArg (fun t ↦ t + adjacencyBit G f a)
            (flip_eq_flip_erase_add hb')
      _ = adjacencyBit G f a + adjacencyBit G f b := by
        rw [herase a ha b hb hab]
        abel
  have h₁ := pair x y hx hy hxy
  have h₂ := pair x z hx hz hxz
  have h₃ := pair y z hy hz hyz
  calc
    flip G U f = adjacencyBit G f y + adjacencyBit G f z := h₃
    _ = (adjacencyBit G f x + adjacencyBit G f y) +
        (adjacencyBit G f x + adjacencyBit G f z) := by
      calc
        adjacencyBit G f y + adjacencyBit G f z =
            (adjacencyBit G f x + adjacencyBit G f x) +
              (adjacencyBit G f y + adjacencyBit G f z) := by
                rw [CharTwo.add_self_eq_zero, zero_add]
        _ = (adjacencyBit G f x + adjacencyBit G f y) +
            (adjacencyBit G f x + adjacencyBit G f z) := by abel
    _ = flip G U f + flip G U f := by rw [← h₁, ← h₂]
    _ = 0 := CharTwo.add_self_eq_zero _

omit [Fintype V] in
/-- The singleton-queue ko branch cannot repeat the one-point obstruction on
the punctured untouched set: the two all-adjacent conclusions would make a
finite set and its one-point erasure have the same cardinality parity. -/
theorem not_all_nested_erase_flips_one
    {G : SimpleGraph V} {U : Finset V} {f z : V}
    (hz : z ∈ U) (hpunctured : (U.erase z).Nonempty)
    (hfront : ∀ x ∈ U, flip G (U.erase x) f = 1)
    (hnested : ∀ y ∈ U.erase z,
      flip G ((U.erase z).erase y) z = 1) : False := by
  classical
  obtain ⟨hflipU, hadjU⟩ :=
    flip_zero_and_adj_of_all_erase_flip_one ⟨z, hz⟩ hfront
  obtain ⟨hflipErase, hadjErase⟩ :=
    flip_zero_and_adj_of_all_erase_flip_one hpunctured hnested
  have hcardU : ((U.card : Nat) : ZMod 2) = 0 := by
    rw [← flip_eq_card_of_forall_adj hadjU]
    exact hflipU
  have hcardErase : (((U.erase z).card : Nat) : ZMod 2) = 0 := by
    rw [← flip_eq_card_of_forall_adj hadjErase]
    exact hflipErase
  have hcardNat := Finset.card_erase_add_one hz
  have hcardCast : (((U.erase z).card : ZMod 2) + 1) = (U.card : ZMod 2) := by
    have hcast := congrArg (fun n : Nat ↦ (n : ZMod 2)) hcardNat
    simpa only [Nat.cast_add, Nat.cast_one] using hcast
  rw [hcardErase, hcardU, zero_add] at hcardCast
  exact one_ne_zero hcardCast

omit [Fintype V] [DecidableEq V] in
/-- The flip into a singleton untouched set is its adjacency coordinate. -/
theorem flip_singleton_eq_adjacencyBit {G : SimpleGraph V} {v x : V} :
    flip G {x} v = adjacencyBit G v x := by
  classical
  by_cases hvx : G.Adj v x
  · have hfilter : ({x} : Finset V).filter (G.Adj v) = {x} := by
      apply Finset.filter_eq_self.mpr
      intro z hz
      have hzx : z = x := Finset.mem_singleton.mp hz
      subst z
      exact hvx
    simp [flip, adjacencyBit, hvx, hfilter]
  · have hfilter : ({x} : Finset V).filter (G.Adj v) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro z hz
      have hzx : z = x := Finset.mem_singleton.mp hz
      subst z
      exact hvx
    simp [flip, adjacencyBit, hvx, hfilter]

omit [Fintype V] in
/-- On a two-point untouched set, the close charge is the sum of the two
adjacency coordinates. -/
theorem flip_pair {G : SimpleGraph V} {v x y : V} (hxy : x ≠ y) :
    flip G {x, y} v = adjacencyBit G v x + adjacencyBit G v y := by
  classical
  have hx : x ∈ ({x, y} : Finset V) := by simp
  have herase : ({x, y} : Finset V).erase x = {y} := by
    ext z
    simp [hxy]
  rw [flip_eq_flip_erase_add hx, herase, flip_singleton_eq_adjacencyBit,
    add_comm]

omit [Fintype V] in
/-- Summing two-point charges is the sum of the two coordinate totals. -/
theorem sum_flip_pair {G : SimpleGraph V} {x y : V} (hxy : x ≠ y) :
    ∀ q : List V, (q.map (flip G {x, y})).sum =
      (q.map (flip G {x})).sum + (q.map (flip G {y})).sum := by
  intro q
  induction q with
  | nil => simp
  | cons v q ih =>
      rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons,
        List.sum_cons, List.sum_cons, flip_pair hxy,
        flip_singleton_eq_adjacencyBit, flip_singleton_eq_adjacencyBit, ih]
      abel

/-- Consecutive queue cells have matching adjacency coordinates to the two
untouched vertices.  This is exactly the relation extracted by comparing the
"open now" response with the response that first consumes one more CLOSE
pair in the two-untouched base case. -/
inductive MatchedQueuePairs (G : SimpleGraph V) (x y : V) : List V → Prop
  | nil : MatchedQueuePairs G x y []
  | cons (a b : V) (q : List V)
      (hx : adjacencyBit G a x = adjacencyBit G b x)
      (hy : adjacencyBit G a y = adjacencyBit G b y)
      (tail : MatchedQueuePairs G x y q) :
      MatchedQueuePairs G x y (a :: b :: q)

omit [Fintype V] in
/-- Every matched queue-pair block has zero aggregate charge into a
two-point untouched set. -/
theorem MatchedQueuePairs.sum_flip_eq_zero
    {G : SimpleGraph V} {x y : V} (hxy : x ≠ y) :
    ∀ {q}, MatchedQueuePairs G x y q →
      (q.map (flip G {x, y})).sum = 0 := by
  intro q h
  induction h with
  | nil => simp
  | cons a b q hx hy _ ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
        flip_pair hxy, flip_pair hxy, hx, hy, ih]
      rw [add_zero]
      calc
        (adjacencyBit G b x + adjacencyBit G b y) +
            (adjacencyBit G b x + adjacencyBit G b y) = 0 :=
          CharTwo.add_self_eq_zero _

omit [Fintype V] in
/-- A single final queue cell whose two adjacency coordinates agree also has
zero charge into the two-point set.  This is the even-length endpoint of the
queue-pair argument. -/
theorem flip_pair_eq_zero_of_coordinates_eq
    {G : SimpleGraph V} {v x y : V} (hxy : x ≠ y)
    (h : adjacencyBit G v x = adjacencyBit G v y) :
    flip G {x, y} v = 0 := by
  rw [flip_pair hxy, h]
  exact CharTwo.add_self_eq_zero _

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

/-- Translate the accumulated score without changing the public game state. -/
def scoreTranslate (c : ZMod 2) (s : State V) : State V :=
  { s with score := c + s.score }

omit [Fintype V] in
/-- Every FIFO transition is equivariant under a uniform score translation.
Thus a locally reconvergent schedule square may be transported through any
common continuation without reopening its already-accounted score defect. -/
theorem step_scoreTranslate (G : SimpleGraph V) (c : ZMod 2) (s : State V)
    (m : Move V) :
    step G (scoreTranslate c s) m =
      (step G s m).map (scoreTranslate c) := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m
  · simp [step, scoreTranslate]
  · cases q <;> cases ko <;> simp [step, scoreTranslate, add_assoc]
  · simp [step, scoreTranslate]

omit [Fintype V] in
/-- Successors of a translated state are exactly translations of successors
of the original state. -/
theorem step_scoreTranslate_eq_some_iff (G : SimpleGraph V) (c : ZMod 2)
    (s t : State V) (m : Move V) :
    step G (scoreTranslate c s) m = some t ↔
      ∃ s', step G s m = some s' ∧ scoreTranslate c s' = t := by
  rw [step_scoreTranslate, Option.map_eq_some_iff]

omit [Fintype V] [DecidableEq V] in
/-- Translating a binary score sheet twice by one recovers the original
state. -/
theorem scoreTranslate_one_involutive (s : State V) :
    scoreTranslate 1 (scoreTranslate 1 s) = s := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  simp only [scoreTranslate]
  congr 1
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

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

omit [Fintype V] in
/-- At the singleton-queue ko wall the immediate OPEN/CLOSE square fails to
reconverge only because closing first makes the subsequent OPEN set `ko`.
Opening one further distinct untouched vertex clears that wall on both paths.
The resulting public states agree, and their scores differ by exactly the
adjacency bit between the original front and the first opened vertex.

This is the local transport square needed at a type-B/B' predecessor: the ko
discrepancy does not survive the next real OPEN. -/
theorem singleton_wall_reconverges_after_open (G : SimpleGraph V) (s : State V)
    (f z w : V) (hqueue : s.queue = [f]) (hko : s.ko = false)
    (hz : z ∈ s.untouched) (hw : w ∈ s.untouched) (hzw : z ≠ w) :
    ∃ sc scz sczw so soc socw,
      step G s .close = some sc ∧
      step G sc (.open z) = some scz ∧
      step G scz (.open w) = some sczw ∧
      step G s (.open z) = some so ∧
      step G so .close = some soc ∧
      step G soc (.open w) = some socw ∧
      sczw.untouched = socw.untouched ∧
      sczw.queue = socw.queue ∧
      sczw.ko = socw.ko ∧
      sczw.toMove = socw.toMove ∧
      sczw.score = socw.score + adjacencyBit G f z ∧
      sczw = scoreTranslate (adjacencyBit G f z) socw := by
  have hwErase : w ∈ s.untouched.erase z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzw, hw⟩
  let sc : State V := {
    untouched := s.untouched
    queue := []
    ko := false
    toMove := !s.toMove
    score := s.score + flip G s.untouched f }
  let scz : State V := {
    untouched := s.untouched.erase z
    queue := [z]
    ko := true
    toMove := s.toMove
    score := s.score + flip G s.untouched f }
  let sczw : State V := {
    untouched := (s.untouched.erase z).erase w
    queue := [z, w]
    ko := false
    toMove := !s.toMove
    score := s.score + flip G s.untouched f }
  let so : State V := {
    untouched := s.untouched.erase z
    queue := [f, z]
    ko := false
    toMove := !s.toMove
    score := s.score }
  let soc : State V := {
    untouched := s.untouched.erase z
    queue := [z]
    ko := false
    toMove := s.toMove
    score := s.score + flip G (s.untouched.erase z) f }
  let socw : State V := {
    untouched := (s.untouched.erase z).erase w
    queue := [z, w]
    ko := false
    toMove := !s.toMove
    score := s.score + flip G (s.untouched.erase z) f }
  refine ⟨sc, scz, sczw, so, soc, socw, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [step, sc, hqueue, hko]
  · simp [step, sc, scz, hz]
  · simp [step, scz, sczw, hwErase]
  · simp [step, so, hqueue, hz]
  · simp [step, so, soc]
  · simp [step, soc, socw, hwErase]
  · simp only [sczw, socw]
    rw [flip_eq_flip_erase_add hz]
    simp [add_assoc]
  · simp only [sczw, socw, scoreTranslate]
    congr 1
    rw [flip_eq_flip_erase_add hz]
    abel

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
/-- Translating the score sheet by one turns a strategy for `seat` to force
even score into a strategy for the same player, expressed as an odd strategy
outside the complementary distinguished seat. -/
theorem EvenWins.scoreTranslate_one {G : SimpleGraph V} {seat : Bool}
    {s : State V} (h : EvenWins G seat s) :
    OddWins G (!seat) (scoreTranslate 1 s) := by
  induction h with
  | terminal s hterminal hscore =>
      refine OddWins.terminal (scoreTranslate 1 s) ?_ ?_
      · simpa [Terminal, scoreTranslate] using hterminal
      · simp [scoreTranslate, hscore]
  | choose s hseat m s' hstep _ ih =>
      refine OddWins.choose (scoreTranslate 1 s) ?_ m
        (scoreTranslate 1 s') ?_ ih
      · simp [scoreTranslate, hseat]
      · rw [step_scoreTranslate, hstep]
        simp
  | answer s hseat hasMove hwin ih =>
      refine OddWins.answer (scoreTranslate 1 s) ?_ ?_ ?_
      · simpa [scoreTranslate] using Bool.eq_not_iff.mpr hseat
      · obtain ⟨m, s', hstep⟩ := hasMove
        exact ⟨m, scoreTranslate 1 s', by
          rw [step_scoreTranslate, hstep]
          simp⟩
      · intro m t hstep
        obtain ⟨s', hbase, rfl⟩ :=
          (step_scoreTranslate_eq_some_iff G 1 s t m).mp hstep
        exact ih m s' hbase

omit [Fintype V] in
/-- Dually, translating by one turns an odd-forcing strategy into an
even-forcing strategy for the same player, now named as the complementary
seat. -/
theorem OddWins.scoreTranslate_one {G : SimpleGraph V} {seat : Bool}
    {s : State V} (h : OddWins G seat s) :
    EvenWins G (!seat) (scoreTranslate 1 s) := by
  induction h with
  | terminal s hterminal hscore =>
      refine EvenWins.terminal (scoreTranslate 1 s) ?_ ?_
      · simpa [Terminal, scoreTranslate] using hterminal
      · have hscoreOne : s.score = 1 :=
          zmod2_eq_one_of_ne_zero s.score hscore
        simp only [scoreTranslate, hscoreOne]
        exact CharTwo.add_self_eq_zero 1
  | choose s hseat m s' hstep _ ih =>
      refine EvenWins.choose (scoreTranslate 1 s) ?_ m
        (scoreTranslate 1 s') ?_ ih
      · simpa [scoreTranslate] using Bool.eq_not_iff.mpr hseat
      · rw [step_scoreTranslate, hstep]
        simp
  | answer s hseat hasMove hwin ih =>
      refine EvenWins.answer (scoreTranslate 1 s) ?_ ?_ ?_
      · simpa [scoreTranslate] using Bool.ne_not.mpr hseat
      · obtain ⟨m, s', hstep⟩ := hasMove
        exact ⟨m, scoreTranslate 1 s', by
          rw [step_scoreTranslate, hstep]
          simp⟩
      · intro m t hstep
        obtain ⟨s', hbase, rfl⟩ :=
          (step_scoreTranslate_eq_some_iff G 1 s t m).mp hstep
        exact ih m s' hbase

omit [Fintype V] in
/-- Exact win-sheet transport in the orientation used by a locally
reconvergent schedule square.  The complemented seat is essential because
`OddWins G seat` is controlled by the player outside `seat`. -/
theorem evenWins_scoreTranslate_one_iff_oddWins (G : SimpleGraph V)
    (seat : Bool) (s : State V) :
    EvenWins G seat (scoreTranslate 1 s) ↔ OddWins G (!seat) s := by
  constructor
  · intro h
    have ht := h.scoreTranslate_one
    rw [scoreTranslate_one_involutive] at ht
    exact ht
  · intro h
    simpa using h.scoreTranslate_one

omit [Fintype V] in
/-- Rewriting form of `evenWins_scoreTranslate_one_iff_oddWins`, intended for
the endpoint equality produced by a local schedule square. -/
theorem evenWins_iff_oddWins_of_eq_scoreTranslate_one
    {G : SimpleGraph V} {seat : Bool} {s t : State V}
    (h : s = scoreTranslate 1 t) :
    EvenWins G seat s ↔ OddWins G (!seat) t := by
  rw [h]
  exact evenWins_scoreTranslate_one_iff_oddWins G seat t

omit [Fintype V] in
/-- The dual orientation of `evenWins_scoreTranslate_one_iff_oddWins`. -/
theorem oddWins_scoreTranslate_one_iff_evenWins (G : SimpleGraph V)
    (seat : Bool) (s : State V) :
    OddWins G seat (scoreTranslate 1 s) ↔ EvenWins G (!seat) s := by
  constructor
  · intro h
    have ht := h.scoreTranslate_one
    rw [scoreTranslate_one_involutive] at ht
    exact ht
  · intro h
    simpa using h.scoreTranslate_one

/-! ## Fixed-front prefix affine recurrence

The following deletion game isolates only the closure prefix at one frozen
front.  A remainder is a finite coordinate set and `closureValue weight S` is
the value of a linear functional on its characteristic vector.  There is no
FIFO queue, graph, descendant strategy, or continuation coset in these
definitions: the result is exactly the scalar no-separation recurrence. -/

/-- Evaluation of a linear functional on the characteristic vector of a
finite remainder. -/
def closureValue (weight : V → ZMod 2) (S : Finset V) : ZMod 2 :=
  ∑ v ∈ S, weight v

omit [Fintype V] in
/-- Erasing one coordinate changes the functional by that coordinate's
weight. -/
theorem closureValue_erase_eq_add (weight : V → ZMod 2)
    {S : Finset V} {v : V} (hv : v ∈ S) :
    closureValue weight (S.erase v) =
      closureValue weight S + weight v := by
  have hsum := Finset.sum_erase_add S weight hv
  calc
    closureValue weight (S.erase v) =
        (closureValue weight (S.erase v) + weight v) + weight v := by
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = closureValue weight S + weight v := by
      simpa only [closureValue] using congrArg (fun x ↦ x + weight v) hsum

omit [Fintype V] [DecidableEq V] in
/-- A unit value of a binary linear functional has a coordinate of unit
weight. -/
theorem exists_weight_one_of_closureValue_eq_one (weight : V → ZMod 2)
    {S : Finset V} (hvalue : closureValue weight S = 1) :
    ∃ v ∈ S, weight v = 1 := by
  by_contra h
  push Not at h
  have hzero : ∀ v ∈ S, weight v = 0 := by
    intro v hv
    exact zmod2_eq_zero_of_ne_one (weight v) (h v hv)
  have hsumZero : closureValue weight S = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact hzero v hv
  rw [hvalue] at hsumZero
  exact one_ne_zero hsumZero

mutual
  /-- At an attacker node, the attacker may stop at the present remainder or
  choose one coordinate to erase and hand the resulting state to the
  defender. -/
  inductive ClosureAttackerForces (weight : V → ZMod 2) (target : ZMod 2) :
      Finset V → Prop where
    | stop (S : Finset V) (hvalue : closureValue weight S = target) :
        ClosureAttackerForces weight target S
    | erase (S : Finset V) (v : V) (hv : v ∈ S)
        (next : ClosureDefenderForces weight target (S.erase v)) :
        ClosureAttackerForces weight target S

  /-- At a defender node, both the immediate stop and every possible
  one-coordinate erasure must stay on the target sheet. -/
  inductive ClosureDefenderForces (weight : V → ZMod 2) (target : ZMod 2) :
      Finset V → Prop where
    | all (S : Finset V) (stop : closureValue weight S = target)
        (erase : ∀ v ∈ S,
          ClosureAttackerForces weight target (S.erase v)) :
        ClosureDefenderForces weight target S
end

omit [Fintype V] in
/-- No attacker policy can put every leaf of a defender-rooted closure prefix
on affine sheet one.  Equivalently, the characteristic vectors of the leaf
remainders cannot all be separated from zero by one binary linear
functional. -/
theorem not_closureDefenderForces_one (weight : V → ZMod 2) :
    ∀ S : Finset V, ¬ClosureDefenderForces weight 1 S := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
      intro hforce
      cases hforce with
      | all _ hvalue erase =>
          obtain ⟨v, hv, hweight⟩ :=
            exists_weight_one_of_closureValue_eq_one weight hvalue
          have hchild := erase v hv
          have hchildValue : closureValue weight (S.erase v) = 0 := by
            rw [closureValue_erase_eq_add weight hv, hvalue, hweight]
            exact CharTwo.add_self_eq_zero 1
          cases hchild with
          | stop _ hstop =>
              rw [hchildValue] at hstop
              exact zero_ne_one hstop
          | erase _ w hw hnext =>
              exact ih ((S.erase v).erase w)
                (lt_of_le_of_lt (Finset.erase_subset w (S.erase v))
                  (Finset.erase_ssubset hv)) hnext

omit [Fintype V] in
/-- The sharp opposite-sheet policy.  At an attacker node of value zero,
stop.  At one of value one, erase a unit-weight coordinate; the new defender
node has value zero. -/
theorem closure_zero_policy (weight : V → ZMod 2) :
    ∀ S : Finset V,
      ClosureAttackerForces weight 0 S ∧
        (closureValue weight S = 0 →
          ClosureDefenderForces weight 0 S) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
      constructor
      · by_cases hzero : closureValue weight S = 0
        · exact ClosureAttackerForces.stop S hzero
        · have hone : closureValue weight S = 1 :=
            zmod2_eq_one_of_ne_zero (closureValue weight S) hzero
          obtain ⟨v, hv, hweight⟩ :=
            exists_weight_one_of_closureValue_eq_one weight hone
          refine ClosureAttackerForces.erase S v hv ?_
          apply (ih (S.erase v) (Finset.erase_ssubset hv)).2
          rw [closureValue_erase_eq_add weight hv, hone, hweight]
          exact CharTwo.add_self_eq_zero 1
      · intro hzero
        refine ClosureDefenderForces.all S hzero ?_
        intro v hv
        exact (ih (S.erase v) (Finset.erase_ssubset hv)).1

omit [Fintype V] in
/-- Sharp relative failure of prefix separation.  If the defender's immediate
stop at the root has value one, every branch after a defender erasure admits
an attacker policy whose leaves all have value zero.  Thus a prefix affine
flow cannot in general be required to carry that designated immediate-close
(B') branch together with the rest of the fan. -/
theorem fixedFrontPrefix_sharp_relative_failure (weight : V → ZMod 2)
    (S : Finset V) (hroot : closureValue weight S = 1) :
    closureValue weight S = 1 ∧
      (¬ClosureDefenderForces weight 1 S) ∧
        (∀ v ∈ S, ClosureAttackerForces weight 0 (S.erase v)) := by
  exact ⟨hroot, not_closureDefenderForces_one weight S,
    fun v _hv ↦ (closure_zero_policy weight (S.erase v)).1⟩

/-- A target-forcing strategy tree for a distinguished attacker who must
CLOSE whenever CLOSE is legal.  The target is an absolute terminal score;
using an explicit target, rather than only the predicate "odd", lets a
well-founded proof compare a subtree with the score at its new root.

At an attacker node the selected move is existential, with `priority`
enforcing CLOSE-first play.  At every other node all legal replies remain
universal. -/
inductive CloseFirstWins (G : SimpleGraph V) (attacker : Bool)
    (target : ZMod 2) : State V → Prop
  | terminal (s : State V) (hterminal : Terminal s) (hscore : s.score = target) :
      CloseFirstWins G attacker target s
  | choose (s : State V) (hattacker : s.toMove = attacker)
      (m : Move V) (s' : State V) (hstep : step G s m = some s')
      (priority : (∃ sc, step G s .close = some sc) → m = .close)
      (hwin : CloseFirstWins G attacker target s') :
      CloseFirstWins G attacker target s
  | answer (s : State V) (hdefender : s.toMove ≠ attacker)
      (hasMove : ∃ m s', step G s m = some s')
      (hwin : ∀ m s', step G s m = some s' →
        CloseFirstWins G attacker target s') :
      CloseFirstWins G attacker target s

omit [Fintype V] in
/-- At a defender node, a target-forcing tree contains the subtree after each
legal reply. -/
theorem CloseFirstWins.answer_child {G : SimpleGraph V} {attacker : Bool}
    {target : ZMod 2} {s s' : State V} {m : Move V}
    (h : CloseFirstWins G attacker target s)
    (hdefender : s.toMove ≠ attacker) (hstep : step G s m = some s') :
    CloseFirstWins G attacker target s' := by
  cases h with
  | terminal _ hterminal _ =>
      exact False.elim (terminal_no_step hterminal ⟨m, s', hstep⟩)
  | choose _ hattacker _ _ _ _ _ => exact False.elim (hdefender hattacker)
  | answer _ _ _ hanswer => exact hanswer m s' hstep

omit [Fintype V] in
/-- At an attacker node where CLOSE is legal, CLOSE-first play selects that
unique move and exposes its target-forcing subtree. -/
theorem CloseFirstWins.close_child {G : SimpleGraph V} {attacker : Bool}
    {target : ZMod 2} {s s' : State V}
    (h : CloseFirstWins G attacker target s)
    (hattacker : s.toMove = attacker)
    (hclose : step G s .close = some s') :
    CloseFirstWins G attacker target s' := by
  cases h with
  | terminal _ hterminal _ =>
      exact False.elim (terminal_no_step hterminal ⟨Move.close, s', hclose⟩)
  | choose _ _ m child hstep priority hchild =>
      have hm : m = .close := priority ⟨s', hclose⟩
      subst m
      rw [hclose] at hstep
      cases hstep
      exact hchild
  | answer _ hdefender _ _ => exact False.elim (hdefender hattacker)

/-- A public state at which FIFO CLOSE is legal.  This is also exactly the
checkpoint at which the stopped extension permits its artificial STOP. -/
def Clear (s : State V) : Prop :=
  s.queue ≠ [] ∧ s.ko = false

/-- The exact stopped CLOSE-first attacker used by the normalization argument.

At a clear attacker node it may STOP only when the accumulated score is odd.
If it continues, its selected ordinary move must be CLOSE, at either score.
At a ko-protected or empty-queue attacker node it may select any legal ordinary
move.  Defender nodes retain the full universal legal-move fan.  Thus this
predicate is deliberately distinct from `CloseFirstWins`: a STOP is a genuine
winning leaf rather than a claim about the eventual terminal score. -/
inductive StoppedCloseFirstWins (G : SimpleGraph V) (attacker : Bool) :
    State V → Prop
  | terminal (s : State V) (hterminal : Terminal s) (hscore : s.score ≠ 0) :
      StoppedCloseFirstWins G attacker s
  | stop (s : State V) (hattacker : s.toMove = attacker)
      (hclear : Clear s) (hscore : s.score ≠ 0) :
      StoppedCloseFirstWins G attacker s
  | choose (s : State V) (hattacker : s.toMove = attacker)
      (m : Move V) (s' : State V) (hstep : step G s m = some s')
      (priority : Clear s → m = .close)
      (hwin : StoppedCloseFirstWins G attacker s') :
      StoppedCloseFirstWins G attacker s
  | answer (s : State V) (hdefender : s.toMove ≠ attacker)
      (hasMove : ∃ m s', step G s m = some s')
      (hwin : ∀ m s', step G s m = some s' →
        StoppedCloseFirstWins G attacker s') :
      StoppedCloseFirstWins G attacker s

omit [Fintype V] in
/-- Every legal defender reply occurs in a stopped CLOSE-first winning tree. -/
theorem StoppedCloseFirstWins.answer_child
    {G : SimpleGraph V} {attacker : Bool} {s s' : State V} {m : Move V}
    (h : StoppedCloseFirstWins G attacker s)
    (hdefender : s.toMove ≠ attacker) (hstep : step G s m = some s') :
    StoppedCloseFirstWins G attacker s' := by
  cases h with
  | terminal _ hterminal _ =>
      exact False.elim (terminal_no_step hterminal ⟨m, s', hstep⟩)
  | stop _ hattacker _ _ => exact False.elim (hdefender hattacker)
  | choose _ hattacker _ _ _ _ _ => exact False.elim (hdefender hattacker)
  | answer _ _ _ hanswer => exact hanswer m s' hstep

omit [Fintype V] in
/-- At a clear attacker node, continuing a stopped strategy exposes the
unique CLOSE child.  A score-one STOP leaf is the only alternative. -/
theorem StoppedCloseFirstWins.close_child_of_score_zero
    {G : SimpleGraph V} {attacker : Bool} {s s' : State V}
    (h : StoppedCloseFirstWins G attacker s)
    (hattacker : s.toMove = attacker) (hscore : s.score = 0)
    (hclose : step G s .close = some s') :
    StoppedCloseFirstWins G attacker s' := by
  cases h with
  | terminal _ hterminal _ =>
      exact False.elim (terminal_no_step hterminal ⟨Move.close, s', hclose⟩)
  | stop _ _ _ hodd => exact False.elim (hodd hscore)
  | choose _ _ m child hstep priority hchild =>
      have hclear : Clear s := by
        simp only [Clear]
        simp only [step] at hclose
        split at hclose
        · contradiction
        · split at hclose
          · contradiction
          · rename_i f q hq _
            exact ⟨by simp [hq], by cases hk : s.ko <;> simp_all⟩
      have hm : m = .close := priority hclear
      subst m
      rw [hclose] at hstep
      cases hstep
      exact hchild
  | answer _ hdefender _ _ => exact False.elim (hdefender hattacker)

/-- Empty no-dummy root used only for the stopped theorem.  The distinguished
attacker moves second; its opponent therefore owns the root move. -/
def stoppedEmptyRoot (U : Finset V) (attacker : Bool) : State V where
  untouched := U
  queue := []
  ko := false
  toMove := !attacker
  score := 0

/-- Kernel-level notation for the stopped empty-root assertion.  This is not
the universal-full-fan predicate `P(H)` from the paper. -/
def StoppedEmptyRootSafe (G : SimpleGraph V) (U : Finset V)
    (attacker : Bool) : Prop :=
  ¬StoppedCloseFirstWins G attacker (stoppedEmptyRoot U attacker)

/-- Ordered two-front checkpoint used by the stopped bad-pair induction.  The
board parameter includes the two queued vertices; all other board vertices
remain untouched. -/
def stoppedPairState (S : Finset V) (x y : V) (attacker : Bool) : State V where
  untouched := (S.erase x).erase y
  queue := [x, y]
  ko := false
  toMove := !attacker
  score := 0

/-- An ordered pair is bad when the stopped attacker wins from its canonical
defender checkpoint.  Membership and distinctness are recorded in the
predicate so later fan arguments can delete either front without side
conditions escaping. -/
def StoppedBadPair (G : SimpleGraph V) (S : Finset V) (attacker : Bool)
    (x y : V) : Prop :=
  x ∈ S ∧ y ∈ S ∧ x ≠ y ∧
    StoppedCloseFirstWins G attacker (stoppedPairState S x y attacker)

omit [Fintype V] in
/-- The elementary two-CLOSE absorber: at a bad pair, a zero source charge
forces the second-front charge to be one whenever the smaller empty root is
safe. -/
theorem StoppedBadPair.beta_eq_one_of_alpha_eq_zero
    {G : SimpleGraph V} {S : Finset V} {attacker : Bool} {x y : V}
    (hbad : StoppedBadPair G S attacker x y)
    (hroot : StoppedEmptyRootSafe G ((S.erase x).erase y) attacker)
    (halpha : flip G ((S.erase x).erase y) x = 0) :
    flip G ((S.erase x).erase y) y = 1 := by
  rcases hbad with ⟨hx, hy, hxy, hwin⟩
  let sx : State V := {
    untouched := (S.erase x).erase y
    queue := [y]
    ko := false
    toMove := attacker
    score := 0 }
  let sxy := stoppedEmptyRoot ((S.erase x).erase y) attacker
  have hclosex : step G (stoppedPairState S x y attacker) .close = some sx := by
    simp [step, stoppedPairState, sx, halpha]
  have hdefender : (!attacker : Bool) ≠ attacker := by
    cases attacker <;> simp
  have hwinx : StoppedCloseFirstWins G attacker sx :=
    hwin.answer_child hdefender hclosex
  by_contra hbeta
  have hbeta0 := zmod2_eq_zero_of_ne_one _ hbeta
  have hclosey : step G sx .close = some sxy := by
    simp [step, sx, sxy, stoppedEmptyRoot, hbeta0]
  have hwiny : StoppedCloseFirstWins G attacker sxy :=
    hwinx.close_child_of_score_zero rfl rfl hclosey
  exact hroot hwiny

omit [Fintype V] in
/-- The operational three-block absorber.  Equality of the first two close
charges cancels the temporary score, and a zero last charge returns to the
smaller stopped empty root. -/
theorem not_stoppedBadPair_of_threeBlock
    {G : SimpleGraph V} {S : Finset V} {attacker : Bool} {x y z : V}
    (hz : z ∈ (S.erase x).erase y)
    (hpair : flip G (((S.erase x).erase y).erase z) x =
      flip G (((S.erase x).erase y).erase z) y)
    (hlast : flip G (((S.erase x).erase y).erase z) z = 0)
    (hroot : StoppedEmptyRootSafe G
      (((S.erase x).erase y).erase z) attacker) :
    ¬StoppedBadPair G S attacker x y := by
  intro hbad
  rcases hbad with ⟨hx, hy, hxy, hwin⟩
  let U := (S.erase x).erase y
  let so : State V := {
    untouched := U.erase z
    queue := [x, y, z]
    ko := false
    toMove := attacker
    score := 0 }
  let sox : State V := {
    untouched := U.erase z
    queue := [y, z]
    ko := false
    toMove := !attacker
    score := flip G (U.erase z) x }
  let soxy : State V := {
    untouched := U.erase z
    queue := [z]
    ko := false
    toMove := attacker
    score := 0 }
  let soxyz := stoppedEmptyRoot (U.erase z) attacker
  have hopen : step G (stoppedPairState S x y attacker) (.open z) = some so := by
    simp [step, stoppedPairState, so, U, hz]
  have hdefender : (!attacker : Bool) ≠ attacker := by
    cases attacker <;> simp
  have hwino : StoppedCloseFirstWins G attacker so :=
    hwin.answer_child hdefender hopen
  have hclosex : step G so .close = some sox := by
    simp [step, so, sox]
  have hwinox : StoppedCloseFirstWins G attacker sox :=
    hwino.close_child_of_score_zero rfl rfl hclosex
  have hclosey : step G sox .close = some soxy := by
    simp [step, sox, soxy, U, ← hpair, CharTwo.add_self_eq_zero]
  have hwinoxy : StoppedCloseFirstWins G attacker soxy :=
    hwinox.answer_child hdefender hclosey
  have hclosez : step G soxy .close = some soxyz := by
    simpa [step, soxy, soxyz, stoppedEmptyRoot, U] using hlast
  have hwinxyz : StoppedCloseFirstWins G attacker soxyz :=
    hwinoxy.close_child_of_score_zero rfl rfl hclosez
  exact hroot hwinxyz

omit [Fintype V] [DecidableEq V] in
@[simp] theorem adjacencyBit_self (G : SimpleGraph V) (v : V) :
    adjacencyBit G v v = 0 := by
  simp [adjacencyBit]

omit [Fintype V] in
/-- Adjoining one untouched vertex adds precisely its adjacency coordinate to
every close charge. -/
theorem flip_insert_of_not_mem {G : SimpleGraph V} {U : Finset V} {f z : V}
    (hz : z ∉ U) :
    flip G (insert z U) f = flip G U f + adjacencyBit G f z := by
  have hzmem : z ∈ insert z U := Finset.mem_insert_self z U
  rw [flip_eq_flip_erase_add hzmem, Finset.erase_insert hz]

omit [Fintype V] in
/-- `flip` is the sum of adjacency coordinates over the untouched board. -/
theorem flip_eq_sum_adjacencyBit (G : SimpleGraph V) (U : Finset V) (f : V) :
    flip G U f = ∑ z ∈ U, adjacencyBit G f z := by
  induction U using Finset.induction with
  | empty => simp
  | @insert z U hz ih =>
      rw [flip_insert_of_not_mem hz, ih]
      simp [hz, add_comm]

omit [Fintype V] in
/-- Handshaking over an arbitrary finite induced board, stated directly in
the parity language used by the game. -/
theorem sum_flip_self_eq_zero (G : SimpleGraph V) (U : Finset V) :
    (∑ v ∈ U, flip G U v) = 0 := by
  induction U using Finset.induction with
  | empty => simp
  | @insert x U hx ih =>
      rw [Finset.sum_insert hx]
      simp_rw [flip_insert_of_not_mem hx]
      rw [Finset.sum_add_distrib, ih]
      rw [flip_eq_sum_adjacencyBit]
      have hsymm :
          (∑ v ∈ U, adjacencyBit G v x) =
            ∑ v ∈ U, adjacencyBit G x v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact adjacencyBit_comm G v x
      rw [hsymm]
      simp
      simpa [two_nsmul] using
        (CharTwo.add_self_eq_zero (∑ z ∈ U, adjacencyBit G x z))

/-- The parity of the degrees of the neighbours of `v` in the induced board
`U`.  This is the two-step walk bit denoted `b_v` in the stopped bad-pair
proof. -/
def neighborDegreeBit (G : SimpleGraph V) (U : Finset V) (v : V) : ZMod 2 :=
  ∑ w ∈ U, adjacencyBit G v w * flip G U w

omit [Fintype V] in
/-- Deleting a board vertex toggles every remaining degree by its adjacency
coordinate to the deleted vertex. -/
theorem flip_erase_eq_add {G : SimpleGraph V} {U : Finset V} {x w : V}
    (hx : x ∈ U) :
    flip G (U.erase x) w = flip G U w + adjacencyBit G w x := by
  have h := flip_eq_flip_erase_add (G := G) (f := w) hx
  calc
    flip G (U.erase x) w =
        (flip G (U.erase x) w + adjacencyBit G w x) +
          adjacencyBit G w x := by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = flip G U w + adjacencyBit G w x := by rw [← h]

omit [Fintype V] in
/-- The source two-step bit after deleting `x`.  The correction consists of
the removed neighbour-degree term and the common-neighbour moment. -/
theorem neighborDegreeBit_erase
    {G : SimpleGraph V} {U : Finset V} {x y : V} (hx : x ∈ U) :
    neighborDegreeBit G (U.erase x) y =
      neighborDegreeBit G U y +
        adjacencyBit G y x * flip G U x +
        ∑ w ∈ U.erase x,
          adjacencyBit G y w * adjacencyBit G x w := by
  classical
  rw [neighborDegreeBit, neighborDegreeBit]
  have hsplit :
      (∑ w ∈ U.erase x, adjacencyBit G y w * flip G U w) +
          adjacencyBit G y x * flip G U x =
        ∑ w ∈ U, adjacencyBit G y w * flip G U w :=
    Finset.sum_erase_add U
      (fun w ↦ adjacencyBit G y w * flip G U w) hx
  have hsplit' :
      (∑ w ∈ U.erase x, adjacencyBit G y w * flip G U w) =
        (∑ w ∈ U, adjacencyBit G y w * flip G U w) -
          adjacencyBit G y x * flip G U x := by
    apply eq_sub_of_add_eq
    simpa [add_comm] using hsplit
  simp_rw [flip_erase_eq_add (G := G) hx, mul_add]
  rw [Finset.sum_add_distrib, hsplit']
  have hcommon :
      (∑ w ∈ U.erase x,
          adjacencyBit G y w * adjacencyBit G w x) =
        ∑ w ∈ U.erase x,
          adjacencyBit G y w * adjacencyBit G x w := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [adjacencyBit_comm G w x]
  rw [hcommon]
  rw [sub_eq_add_neg]
  have hneg (t : ZMod 2) : -t = t := by
    exact CharTwo.neg_eq t
  rw [hneg]

omit [Fintype V] in
/-- Splitting a finite sum after erasing two distinct members. -/
theorem sum_erase_erase_add
    {S : Finset V} {x y : V} (f : V → ZMod 2)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    (∑ z ∈ (S.erase x).erase y, f z) + f y + f x =
      ∑ z ∈ S, f z := by
  have hyErase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
  have hySplit := Finset.sum_erase_add (S.erase x) f hyErase
  have hxSplit := Finset.sum_erase_add S f hx
  calc
    (∑ z ∈ (S.erase x).erase y, f z) + f y + f x =
        (∑ z ∈ S.erase x, f z) + f x := by rw [hySplit]
    _ = ∑ z ∈ S, f z := hxSplit

omit [Fintype V] in
/-- Erasing two board vertices toggles a charge by the two corresponding
adjacency coordinates. -/
theorem flip_erase_erase_eq_add
    {G : SimpleGraph V} {S : Finset V} {x y w : V}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    flip G ((S.erase x).erase y) w =
      flip G S w + adjacencyBit G w x + adjacencyBit G w y := by
  have hyErase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
  rw [flip_erase_eq_add (G := G) hyErase,
    flip_erase_eq_add (G := G) hx]

omit [Fintype V] in
/-- Reverse orientation of `flip_erase_erase_eq_add`, valid because every
adjacency coordinate has additive order two. -/
theorem flip_eq_erase_erase_add
    {G : SimpleGraph V} {S : Finset V} {x y w : V}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    flip G S w = flip G ((S.erase x).erase y) w +
      adjacencyBit G w x + adjacencyBit G w y := by
  have h := flip_erase_erase_eq_add (G := G) (w := w) hx hy hxy
  calc
    flip G S w = flip G S w +
        ((adjacencyBit G w x + adjacencyBit G w x) +
          (adjacencyBit G w y + adjacencyBit G w y)) := by
            rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
              zero_add, add_zero]
    _ = flip G ((S.erase x).erase y) w +
        adjacencyBit G w x + adjacencyBit G w y := by rw [h]; abel

omit [Fintype V] in
/-- The sum of full-board degree bits over the untouched complement of an
ordered pair is the sum of the two front charges. -/
theorem sum_flip_pairUntouched
    {G : SimpleGraph V} {S : Finset V} {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    (∑ z ∈ (S.erase x).erase y, flip G S z) =
      flip G ((S.erase x).erase y) x +
        flip G ((S.erase x).erase y) y := by
  let U := (S.erase x).erase y
  let alpha := flip G U x
  let beta := flip G U y
  let a := adjacencyBit G x y
  have hpx : flip G S x = alpha + a := by
    simpa [U, alpha, a, adjacencyBit_self, add_comm, add_left_comm,
      add_assoc] using
        (flip_eq_erase_erase_add (G := G) (w := x) hx hy hxy)
  have hpy : flip G S y = beta + a := by
    simpa [U, beta, a, adjacencyBit_self, adjacencyBit_comm,
      add_comm, add_left_comm, add_assoc] using
        (flip_eq_erase_erase_add (G := G) (w := y) hx hy hxy)
  have hsplit := sum_erase_erase_add (f := fun z ↦ flip G S z) hx hy hxy
  have hhandshake := sum_flip_self_eq_zero G S
  rw [hhandshake, hpx, hpy] at hsplit
  have hzero : (∑ z ∈ U, flip G S z) + (alpha + beta) = 0 := by
    calc
      (∑ z ∈ U, flip G S z) + (alpha + beta) =
          ((∑ z ∈ U, flip G S z) + (alpha + beta)) + (a + a) := by
            rw [CharTwo.add_self_eq_zero, add_zero]
      _ = (∑ z ∈ U, flip G S z) + (beta + a) + (alpha + a) := by abel
      _ = 0 := hsplit
  change (∑ z ∈ U, flip G S z) = alpha + beta
  calc
    (∑ z ∈ U, flip G S z) =
        ((∑ z ∈ U, flip G S z) + (alpha + beta)) +
          (alpha + beta) := by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = alpha + beta := by rw [hzero, zero_add]

omit [Fintype V] in
/-- Splitting the source two-step bit into the opposite-front endpoint and
the untouched contribution. -/
theorem neighborDegreeBit_split_pair
    {G : SimpleGraph V} {S : Finset V} {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    neighborDegreeBit G S x =
      adjacencyBit G x y * flip G S y +
        ∑ z ∈ (S.erase x).erase y,
          adjacencyBit G x z * flip G S z := by
  have hsplit := sum_erase_erase_add
    (f := fun z ↦ adjacencyBit G x z * flip G S z) hx hy hxy
  rw [adjacencyBit_self, zero_mul, add_zero] at hsplit
  rw [neighborDegreeBit]
  rw [← hsplit]
  abel

omit [Fintype V] in
/-- The common-neighbour correction in the deletion formula may be summed on
the pair-untouched board; the omitted second front contributes zero. -/
theorem commonNeighbor_sum_erase_eq_pairUntouched
    {G : SimpleGraph V} {S : Finset V} {x y : V}
    (_hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    (∑ w ∈ S.erase x,
      adjacencyBit G y w * adjacencyBit G x w) =
        ∑ w ∈ (S.erase x).erase y,
          adjacencyBit G x w * adjacencyBit G y w := by
  have hyErase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
  have hsplit := Finset.sum_erase_add (S.erase x)
    (fun w ↦ adjacencyBit G y w * adjacencyBit G x w) hyErase
  rw [adjacencyBit_self, zero_mul, add_zero] at hsplit
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro w hw
  ring

omit [Fintype V] [DecidableEq V] in
/-- Multiplication by a parity bit restricts a sum to its one-fibre. -/
theorem sum_bit_mul_eq_filter_one
    (U : Finset V) (bit f : V → ZMod 2) :
    (∑ z ∈ U, bit z * f z) =
      ∑ z ∈ U.filter (fun z ↦ bit z = 1), f z := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hbit0 : bit z = 0
  · simp [hbit0]
  · have hbit1 := zmod2_eq_one_of_ne_zero (bit z) hbit0
    simp [hbit1]

omit [Fintype V] [DecidableEq V] in
/-- The zero-fibre indicator of a parity bit is `1 + bit`. -/
theorem sum_one_add_bit_mul_eq_filter_zero
    (U : Finset V) (bit f : V → ZMod 2) :
    (∑ z ∈ U, (1 + bit z) * f z) =
      ∑ z ∈ U.filter (fun z ↦ bit z = 0), f z := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hbit0 : bit z = 0
  · simp [hbit0]
  · have hbit1 := zmod2_eq_one_of_ne_zero (bit z) hbit0
    simp [hbit1, CharTwo.add_self_eq_zero]

omit [Fintype V] in
/-- Erasing one member changes cardinality parity by one. -/
theorem card_erase_cast_add_one {S : Finset V} {x : V} (hx : x ∈ S) :
    (((S.erase x).card : Nat) : ZMod 2) + 1 = (S.card : ZMod 2) := by
  have hcard := Finset.card_erase_add_one hx
  have hcast := congrArg (fun n : Nat ↦ (n : ZMod 2)) hcard
  simpa only [Nat.cast_add, Nat.cast_one] using hcast

omit [Fintype V] in
/-- Erasing two distinct members preserves cardinality parity. -/
theorem card_erase_erase_cast_eq
    {S : Finset V} {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ((((S.erase x).erase y).card : Nat) : ZMod 2) =
      (S.card : ZMod 2) := by
  have hyErase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
  have hyCard := card_erase_cast_add_one hyErase
  have hxCard := card_erase_cast_add_one hx
  calc
    ((((S.erase x).erase y).card : Nat) : ZMod 2) =
        ((((S.erase x).erase y).card : Nat) : ZMod 2) + (1 + 1) := by
          rw [CharTwo.add_self_eq_zero, add_zero]
    _ = (((((S.erase x).erase y).card : Nat) : ZMod 2) + 1) + 1 := by abel
    _ = (((S.erase x).card : Nat) : ZMod 2) + 1 := by rw [hyCard]
    _ = (S.card : ZMod 2) := hxCard

omit [Fintype V] in
/-- Graph-parity form of the three-block absorber.  A bad pair has no vertex
whose full-board degree and two front-adjacency sum both equal
`alpha + beta`. -/
theorem StoppedBadPair.no_threeBlock_fibre
    {G : SimpleGraph V} {S : Finset V} {attacker : Bool} {x y z : V}
    (hbad : StoppedBadPair G S attacker x y)
    (hz : z ∈ (S.erase x).erase y)
    (hroot : StoppedEmptyRootSafe G
      (((S.erase x).erase y).erase z) attacker) :
    ¬(flip G S z =
          flip G ((S.erase x).erase y) x +
            flip G ((S.erase x).erase y) y ∧
       adjacencyBit G x z + adjacencyBit G y z =
          flip G ((S.erase x).erase y) x +
            flip G ((S.erase x).erase y) y) := by
  rintro ⟨hp, hadj⟩
  let U := (S.erase x).erase y
  have hpair : flip G (U.erase z) x = flip G (U.erase z) y := by
    have hxerase := flip_erase_eq_add (G := G) (w := x) hz
    have hyerase := flip_erase_eq_add (G := G) (w := y) hz
    rw [hxerase, hyerase]
    have hadj' : adjacencyBit G x z + adjacencyBit G y z =
        flip G U x + flip G U y := by simpa [U] using hadj
    apply eq_of_sub_eq_zero
    rw [sub_eq_add_neg, CharTwo.neg_eq]
    calc
      (flip G U x + adjacencyBit G x z) +
          (flip G U y + adjacencyBit G y z) =
          (adjacencyBit G x z + adjacencyBit G y z) +
            (flip G U x + flip G U y) := by abel
      _ = 0 := by rw [hadj', CharTwo.add_self_eq_zero]
  have hxS : x ∈ S := hbad.1
  have hyS : y ∈ S := hbad.2.1
  have hxy : x ≠ y := hbad.2.2.1
  have hyErase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hyS⟩
  have hzU : z ∈ U := by simpa [U] using hz
  have hlastU : flip G U z = 0 := by
    have hxdel := flip_erase_eq_add (G := G) (w := z) hxS
    have hydel := flip_erase_eq_add (G := G) (w := z) hyErase
    have hp' : flip G S z = flip G U x + flip G U y := by
      simpa [U] using hp
    have hadj' : adjacencyBit G z x + adjacencyBit G z y =
        flip G U x + flip G U y := by
      rw [adjacencyBit_comm G z x, adjacencyBit_comm G z y]
      exact hadj
    rw [hydel, hxdel, hp']
    calc
      flip G U x + flip G U y + adjacencyBit G z x +
          adjacencyBit G z y =
          (flip G U x + flip G U y) +
            (adjacencyBit G z x + adjacencyBit G z y) := by abel
      _ = 0 := by rw [hadj', CharTwo.add_self_eq_zero]
  have hlast : flip G (U.erase z) z = 0 := by
    rw [flip_erase_eq_add (G := G) hzU, hlastU, adjacencyBit_self]
    rfl
  exact not_stoppedBadPair_of_threeBlock hz hpair hlast hroot hbad

omit [Fintype V] in
/-- A zero-charge OPEN/CLOSE rotation exports a bad pair to the one-front
deleted board.  This is the semantic child used by the `Z`-fan induction. -/
theorem StoppedBadPair.child_of_zero_open
    {G : SimpleGraph V} {S : Finset V} {attacker : Bool} {x y z : V}
    (hbad : StoppedBadPair G S attacker x y)
    (hz : z ∈ (S.erase x).erase y)
    (hzero : flip G (((S.erase x).erase y).erase z) x = 0) :
    StoppedBadPair G (S.erase x) attacker y z := by
  rcases hbad with ⟨hx, hy, hxy, hwin⟩
  let U := (S.erase x).erase y
  let so : State V := {
    untouched := U.erase z
    queue := [x, y, z]
    ko := false
    toMove := attacker
    score := 0 }
  let child := stoppedPairState (S.erase x) y z attacker
  have hopen : step G (stoppedPairState S x y attacker) (.open z) = some so := by
    simp [step, stoppedPairState, so, U, hz]
  have hdefender : (!attacker : Bool) ≠ attacker := by
    cases attacker <;> simp
  have hwino : StoppedCloseFirstWins G attacker so :=
    hwin.answer_child hdefender hopen
  have hclose : step G so .close = some child := by
    simp [step, so, child, stoppedPairState, U, hzero]
  have hwinchild : StoppedCloseFirstWins G attacker child :=
    hwino.close_child_of_score_zero rfl rfl hclose
  have hyErase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
  have hzErase : z ∈ S.erase x :=
    Finset.mem_of_mem_erase hz
  have hyz : y ≠ z := by
    intro heq
    subst z
    exact (Finset.notMem_erase y (S.erase x)) hz
  exact ⟨hyErase, hzErase, hyz, hwinchild⟩

/-- Every scalar in `ZMod 2` is idempotent. -/
theorem zmod2_sq_eq_self (t : ZMod 2) : t * t = t := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [zmod2_eq_one_of_ne_zero t ht]
    simp

/-- Distinct parity bits differ by the unit bit, so the affine equality
indicator `x + 1 + y` vanishes. -/
theorem zmod2_add_one_add_eq_zero_of_ne (x y : ZMod 2) (hxy : x ≠ y) :
    x + 1 + y = 0 := by
  have hsum0 : x + y ≠ 0 := by
    intro h
    have : x = y := by
      calc
        x = x + (y + y) := by rw [CharTwo.add_self_eq_zero, add_zero]
        _ = (x + y) + y := by abel
        _ = y := by rw [h, zero_add]
    exact hxy this
  have hsum1 : x + y = 1 := zmod2_eq_one_of_ne_zero _ hsum0
  calc
    x + 1 + y = (x + y) + 1 := by abel
    _ = 0 := by rw [hsum1, CharTwo.add_self_eq_zero]

omit [Fintype V] [DecidableEq V] in
/-- Parity of an empty equality fibre.  This is the abstract algebra behind
the stopped bad-pair moment identity. -/
theorem no_common_value_moment
    (U : Finset V) (p q : V → ZMod 2) (r : ZMod 2)
    (hp : (∑ z ∈ U, p z) = r) (hq : (∑ z ∈ U, q z) = r)
    (hfibre : ∀ z ∈ U, ¬(p z = r ∧ q z = r)) :
    (∑ z ∈ U, p z * q z) = (1 + r) * (U.card : ZMod 2) := by
  have hindicator :
      (∑ z ∈ U, (p z + 1 + r) * (q z + 1 + r)) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hpzr : p z = r
    · have hqzr : q z ≠ r := by
        intro h
        exact hfibre z hz ⟨hpzr, h⟩
      rw [zmod2_add_one_add_eq_zero_of_ne (q z) r hqzr]
      simp
    · rw [zmod2_add_one_add_eq_zero_of_ne (p z) r hpzr]
      simp
  have hexpand :
      (∑ z ∈ U, (p z + 1 + r) * (q z + 1 + r)) =
        (∑ z ∈ U, p z * q z) +
          (1 + r) * (∑ z ∈ U, p z) +
          (1 + r) * (∑ z ∈ U, q z) +
          (U.card : ZMod 2) * ((1 + r) * (1 + r)) := by
    have hpoint (z : V) :
        (p z + 1 + r) * (q z + 1 + r) =
          p z * q z + (1 + r) * p z +
            (1 + r) * q z + (1 + r) * (1 + r) := by ring
    simp_rw [hpoint, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hexpand, hp, hq] at hindicator
  rw [zmod2_sq_eq_self (1 + r)] at hindicator
  have hcross : (1 + r) * r + (1 + r) * r = 0 :=
    CharTwo.add_self_eq_zero _
  have hsummed :
      (∑ z ∈ U, p z * q z) +
          (U.card : ZMod 2) * (1 + r) = 0 := by
    calc
      (∑ z ∈ U, p z * q z) + (U.card : ZMod 2) * (1 + r) =
          ((∑ z ∈ U, p z * q z) +
            ((1 + r) * r + (1 + r) * r)) +
              (U.card : ZMod 2) * (1 + r) := by rw [hcross, add_zero]
      _ = 0 := by simpa [add_assoc] using hindicator
  calc
    (∑ z ∈ U, p z * q z) =
        (∑ z ∈ U, p z * q z) +
          ((U.card : ZMod 2) * (1 + r) +
            (U.card : ZMod 2) * (1 + r)) := by
              rw [CharTwo.add_self_eq_zero, add_zero]
    _ = (U.card : ZMod 2) * (1 + r) := by
      rw [← add_assoc, hsummed, zero_add]
    _ = (1 + r) * (U.card : ZMod 2) := mul_comm _ _

omit [Fintype V] in
/-- The empty three-block fibre gives the exact stopped bad-pair moment
identity in graph notation. -/
theorem StoppedBadPair.moment
    {G : SimpleGraph V} {S : Finset V} {attacker : Bool} {x y : V}
    (hbad : StoppedBadPair G S attacker x y)
    (hsafe : ∀ T : Finset V, T ⊂ S → StoppedEmptyRootSafe G T attacker) :
    neighborDegreeBit G S x + neighborDegreeBit G S y =
      (1 + (flip G ((S.erase x).erase y) x +
        flip G ((S.erase x).erase y) y)) * (S.card : ZMod 2) +
      adjacencyBit G x y *
        (flip G ((S.erase x).erase y) x +
          flip G ((S.erase x).erase y) y) := by
  let U := (S.erase x).erase y
  let alpha := flip G U x
  let beta := flip G U y
  let a := adjacencyBit G x y
  let r := alpha + beta
  have hx : x ∈ S := hbad.1
  have hy : y ∈ S := hbad.2.1
  have hxy : x ≠ y := hbad.2.2.1
  have hyErase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
  have hproper (T : Finset V) (hTS : T ⊆ S) (hxT : x ∉ T) : T ⊂ S := by
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨hTS, fun hEq ↦ hxT (hEq ▸ hx)⟩
  have hUSub : U ⊆ S := by
    intro z hz
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
  have hxU : x ∉ U := by simp [U]
  have hproperU : U ⊂ S := hproper U hUSub hxU
  have hpx : flip G S x = alpha + a := by
    simpa [U, alpha, a, adjacencyBit_self, add_comm, add_left_comm,
      add_assoc] using
        (flip_eq_erase_erase_add (G := G) (w := x) hx hy hxy)
  have hpy : flip G S y = beta + a := by
    simpa [U, beta, a, adjacencyBit_self, adjacencyBit_comm,
      add_comm, add_left_comm, add_assoc] using
        (flip_eq_erase_erase_add (G := G) (w := y) hx hy hxy)
  have hpSum : (∑ z ∈ U, flip G S z) = r := by
    have hsplit := sum_erase_erase_add (f := fun z ↦ flip G S z) hx hy hxy
    have hhandshake := sum_flip_self_eq_zero G S
    rw [hhandshake, hpx, hpy] at hsplit
    have hzero : (∑ z ∈ U, flip G S z) + r = 0 := by
      calc
        (∑ z ∈ U, flip G S z) + r =
            ((∑ z ∈ U, flip G S z) + r) + (a + a) := by
              rw [CharTwo.add_self_eq_zero, add_zero]
        _ = (∑ z ∈ U, flip G S z) + (beta + a) + (alpha + a) := by
              simp only [r]
              abel
        _ = 0 := hsplit
    calc
      (∑ z ∈ U, flip G S z) =
          ((∑ z ∈ U, flip G S z) + r) + r := by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = r := by rw [hzero, zero_add]
  have hqSum :
      (∑ z ∈ U, (adjacencyBit G x z + adjacencyBit G y z)) = r := by
    rw [Finset.sum_add_distrib]
    rw [← flip_eq_sum_adjacencyBit G U x,
      ← flip_eq_sum_adjacencyBit G U y]
  have hfibre : ∀ z ∈ U,
      ¬(flip G S z = r ∧
        adjacencyBit G x z + adjacencyBit G y z = r) := by
    intro z hz
    have hsub : U.erase z ⊆ S :=
      Finset.Subset.trans (Finset.erase_subset z U) hUSub
    have hxErase : x ∉ U.erase z := fun hxmem ↦ hxU (Finset.mem_of_mem_erase hxmem)
    have hroot := hsafe (U.erase z) (hproper (U.erase z) hsub hxErase)
    simpa [U, alpha, beta, r] using hbad.no_threeBlock_fibre hz hroot
  have hprod := no_common_value_moment U
    (fun z ↦ flip G S z)
    (fun z ↦ adjacencyBit G x z + adjacencyBit G y z)
    r hpSum hqSum hfibre
  have hcardNat : U.card + 2 = S.card := by
    have hyCard := Finset.card_erase_add_one hyErase
    have hxCard := Finset.card_erase_add_one hx
    dsimp [U]
    omega
  have hcard : (U.card : ZMod 2) = (S.card : ZMod 2) := by
    have hcast := congrArg (fun n : Nat ↦ (n : ZMod 2)) hcardNat
    simpa [Nat.cast_add, CharTwo.two_eq_zero] using hcast
  rw [hcard] at hprod
  have hwalk : neighborDegreeBit G S x + neighborDegreeBit G S y =
      ∑ z ∈ S, flip G S z *
        (adjacencyBit G x z + adjacencyBit G y z) := by
    rw [neighborDegreeBit, neighborDegreeBit, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  have hsplit := sum_erase_erase_add
    (f := fun z ↦ flip G S z *
      (adjacencyBit G x z + adjacencyBit G y z)) hx hy hxy
  have hends :
      flip G S y * (adjacencyBit G x y + adjacencyBit G y y) +
        flip G S x * (adjacencyBit G x x + adjacencyBit G y x) = a * r := by
    rw [adjacencyBit_self, adjacencyBit_self, zero_add, add_zero,
      adjacencyBit_comm G y x, hpx, hpy]
    simp only [r]
    calc
      (beta + a) * a + (alpha + a) * a =
          a * (alpha + beta) + (a * a + a * a) := by ring
      _ = a * (alpha + beta) := by
        rw [CharTwo.add_self_eq_zero, add_zero]
  have hsplit' :
      (∑ z ∈ U, flip G S z *
        (adjacencyBit G x z + adjacencyBit G y z)) + a * r =
          ∑ z ∈ S, flip G S z *
            (adjacencyBit G x z + adjacencyBit G y z) := by
    calc
      (∑ z ∈ U, flip G S z *
          (adjacencyBit G x z + adjacencyBit G y z)) + a * r =
          (∑ z ∈ U, flip G S z *
            (adjacencyBit G x z + adjacencyBit G y z)) +
              (flip G S y *
                (adjacencyBit G x y + adjacencyBit G y y) +
               flip G S x *
                (adjacencyBit G x x + adjacencyBit G y x)) := by rw [hends]
      _ = _ := by simpa [U, add_assoc] using hsplit
  rw [hwalk, ← hsplit', hprod]

/-- Three-level rank used to orient stopped bad arcs. -/
def stoppedBadRank (p b : ZMod 2) : Nat :=
  if b = 0 then 0 else if p = 0 then 2 else 1

/-- The exact bad-pair bits and moment equation force strict rank descent.
This is the algebraic terminal step of the stopped empty-root proof. -/
theorem stoppedBadArc_rank_lt
    (a alpha beta epsilon px py bX bY r : ZMod 2)
    (hpx : px = a + alpha) (hpy : py = a + beta)
    (hr : r = alpha + beta) (hbeta : beta = 1) (hbx : bX = 1)
    (halpha : alpha = 1 → epsilon = 1)
    (hmoment : bX + bY = (1 + r) * epsilon + a * r) :
    stoppedBadRank py bY < stoppedBadRank px bX := by
  have h11 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
  by_cases halpha0 : alpha = 0
  · simp [halpha0, hbeta] at hr hpx hpy hmoment
    have hr1 : r = 1 := by simpa using hr
    rw [hr1, hbx] at hmoment
    have hby : bY = 1 + a := by
      have := hmoment
      simp only [CharTwo.add_self_eq_zero, zero_mul, mul_one] at this
      calc
        bY = bY + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
        _ = 1 + (1 + bY) := by abel
        _ = 1 + a := by simp [this]
    have hpxa : px = a := by simpa using hpx
    have hpya : py = a + 1 := by simpa using hpy
    by_cases ha0 : a = 0
    · simp [stoppedBadRank, hpxa, hpya, hby, hbx, ha0]
    · have ha1 : a = 1 := zmod2_eq_one_of_ne_zero a ha0
      simp [stoppedBadRank, hpxa, hby, hbx, ha1, h11]
  · have halpha1 : alpha = 1 := zmod2_eq_one_of_ne_zero alpha halpha0
    have hepsilon1 : epsilon = 1 := halpha halpha1
    simp [halpha1, hbeta, hepsilon1, hbx] at hr hmoment hpx hpy
    have hr0 : r = 0 := by simpa [h11] using hr
    rw [hr0] at hmoment
    have hby0 : bY = 0 := by
      have := hmoment
      simpa using this
    unfold stoppedBadRank
    simp only [hby0, hbx, ↓reduceIte, one_ne_zero]
    by_cases hpx0 : px = 0 <;> simp [hpx0]

omit [Fintype V] [DecidableEq V] in
/-- A finite nonempty set cannot support an everywhere-outgoing relation that
strictly decreases a natural-valued rank.  This packages the directed-cycle
argument without choosing an actual cycle. -/
theorem no_total_strict_rank_relation
    (S : Finset V) (hS : S.Nonempty) (R : V → V → Prop) (rho : V → Nat)
    (hout : ∀ x ∈ S, ∃ y ∈ S, R x y)
    (hdesc : ∀ {x y}, x ∈ S → y ∈ S → R x y → rho y < rho x) : False := by
  obtain ⟨x, hxS, hxmin⟩ := Finset.exists_min_image S rho hS
  obtain ⟨y, hyS, hxy⟩ := hout x hxS
  exact (not_lt_of_ge (hxmin y hyS)) (hdesc hxS hyS hxy)

omit [Fintype V] in
/-- A stopped winning tree at an empty defender root exports a bad outgoing
ordered pair from every possible first OPEN.  This is the exact root fan used
by the final rank contradiction. -/
theorem StoppedCloseFirstWins.outgoing_stoppedBadPair
    {G : SimpleGraph V} {S : Finset V} {attacker : Bool}
    (hwin : StoppedCloseFirstWins G attacker (stoppedEmptyRoot S attacker))
    (hcard : 2 ≤ S.card) :
    ∀ x ∈ S, ∃ y ∈ S, StoppedBadPair G S attacker x y := by
  intro x hx
  let sx : State V := {
    untouched := S.erase x
    queue := [x]
    ko := true
    toMove := attacker
    score := 0 }
  have hopenx : step G (stoppedEmptyRoot S attacker) (.open x) = some sx := by
    simp [step, stoppedEmptyRoot, sx, hx]
  have hdefender : (!attacker : Bool) ≠ attacker := by
    cases attacker <;> simp
  have hwinx : StoppedCloseFirstWins G attacker sx :=
    hwin.answer_child hdefender hopenx
  have hremain : S.erase x ≠ ∅ := by
    intro hempty
    have hcardErase := Finset.card_erase_add_one hx
    rw [hempty] at hcardErase
    simp at hcardErase
    omega
  cases hwinx with
  | terminal _ hterminal _ => exact False.elim (List.cons_ne_nil x [] hterminal.2)
  | stop _ _ hclear _ => exact False.elim (by simp [Clear, sx] at hclear)
  | answer _ hnotattacker _ _ => exact False.elim (hnotattacker rfl)
  | choose _ _ m child hstep _ hchild =>
      cases m with
      | close => simp [step, sx] at hstep
      | pass => simp [step, sx, hremain] at hstep
      | «open» y =>
          have hyErase : y ∈ S.erase x := by
            simp only [step] at hstep
            split at hstep
            · assumption
            · contradiction
          have hyS : y ∈ S := Finset.mem_of_mem_erase hyErase
          have hyx : y ≠ x := (Finset.ne_of_mem_erase hyErase)
          have hchildState : child = stoppedPairState S x y attacker := by
            simp only [step] at hstep
            split at hstep
            · cases hstep
              simp [sx, stoppedPairState]
            · contradiction
          subst child
          exact ⟨y, hyS, hx, hyS, Ne.symm hyx, hchild⟩

omit [Fintype V] in
/-- With no untouched vertex and even current score, neither terminal play nor
a stopped leaf can witness an attacker win. -/
theorem not_stoppedCloseFirstWins_of_untouched_empty
    {G : SimpleGraph V} {attacker : Bool} {s : State V}
    (hU : s.untouched = ∅) (hscore : s.score = 0) :
    ¬StoppedCloseFirstWins G attacker s := by
  intro hwin
  induction hwin with
  | terminal _ _ hodd => exact hodd hscore
  | stop _ _ _ hodd => exact hodd hscore
  | choose _ _ _ _ hstep _ _ ih =>
      exact ih (step_untouched_eq_empty hU hstep)
        (by rw [step_score_eq_of_untouched_empty hU hstep, hscore])
  | answer _ _ hasMove _ ih =>
      obtain ⟨m, s', hstep⟩ := hasMove
      exact ih m s' hstep (step_untouched_eq_empty hU hstep)
        (by rw [step_score_eq_of_untouched_empty hU hstep, hscore])

omit [Fintype V] in
/-- Empty-board base of the stopped empty-root induction. -/
theorem stoppedEmptyRootSafe_empty (G : SimpleGraph V) (attacker : Bool) :
    StoppedEmptyRootSafe G ∅ attacker := by
  apply not_stoppedCloseFirstWins_of_untouched_empty
  · rfl
  · rfl

omit [Fintype V] in
/-- One-vertex base of the stopped empty-root induction.  The defender opens
the sole vertex, after which every continuation has empty untouched set and
even score. -/
theorem stoppedEmptyRootSafe_singleton (G : SimpleGraph V) (attacker : Bool)
    (x : V) : StoppedEmptyRootSafe G {x} attacker := by
  intro hwin
  let sx : State V := {
    untouched := ∅
    queue := [x]
    ko := true
    toMove := attacker
    score := 0 }
  have hopen : step G (stoppedEmptyRoot {x} attacker) (.open x) = some sx := by
    simp [step, stoppedEmptyRoot, sx]
  have hdefender : (!attacker : Bool) ≠ attacker := by
    cases attacker <;> simp
  have hwinx : StoppedCloseFirstWins G attacker sx :=
    hwin.answer_child hdefender hopen
  exact not_stoppedCloseFirstWins_of_untouched_empty rfl rfl hwinx

/-- The exact local obligation left by the formalized absorber algebra: every
stopped bad pair must strictly descend the two-bit rank. -/
def StoppedBadPairRankDescent (G : SimpleGraph V) (S : Finset V)
    (attacker : Bool) : Prop :=
  ∀ ⦃x y⦄, StoppedBadPair G S attacker x y →
    stoppedBadRank (flip G S y) (neighborDegreeBit G S y) <
      stoppedBadRank (flip G S x) (neighborDegreeBit G S x)

/-- The three inductive bits of the stopped bad-pair fan lemma: the second
front charge and source two-step bit are one, and a one source charge forces
odd board order. -/
def StoppedBadPairBits (G : SimpleGraph V) (S : Finset V)
    (attacker : Bool) : Prop :=
  ∀ ⦃x y⦄, StoppedBadPair G S attacker x y →
    flip G ((S.erase x).erase y) y = 1 ∧
      neighborDegreeBit G S x = 1 ∧
      (flip G ((S.erase x).erase y) x = 1 →
        (S.card : ZMod 2) = 1)

omit [Fintype V] in
/-- Terminal domination wall of the stopped bad-pair fan: if the complete
zero-charge OPEN fibre is empty, the source charge is zero and the remaining
two required bits follow from the two-CLOSE absorber and handshaking. -/
theorem StoppedBadPair.bits_of_zeroFan_empty
    {G : SimpleGraph V} {S : Finset V} {attacker : Bool} {x y : V}
    (hbad : StoppedBadPair G S attacker x y)
    (hroot : StoppedEmptyRootSafe G ((S.erase x).erase y) attacker)
    (hZ : ((S.erase x).erase y).filter (fun z ↦
      adjacencyBit G x z = flip G ((S.erase x).erase y) x) = ∅) :
    flip G ((S.erase x).erase y) y = 1 ∧
      neighborDegreeBit G S x = 1 ∧
      (flip G ((S.erase x).erase y) x = 1 →
        (S.card : ZMod 2) = 1) := by
  let U := (S.erase x).erase y
  let alpha := flip G U x
  let beta := flip G U y
  have hx : x ∈ S := hbad.1
  have hy : y ∈ S := hbad.2.1
  have hxy : x ≠ y := hbad.2.2.1
  have halpha0 : alpha = 0 := by
    by_contra hne
    have halpha1 := zmod2_eq_one_of_ne_zero alpha hne
    have hallZero : ∀ z ∈ U, adjacencyBit G x z = 0 := by
      intro z hz
      by_contra hbit0
      have hbit1 := zmod2_eq_one_of_ne_zero (adjacencyBit G x z) hbit0
      have hzZ : z ∈ U.filter (fun w ↦ adjacencyBit G x w = alpha) := by
        simp [hz, hbit1, halpha1]
      rw [show U.filter (fun w ↦ adjacencyBit G x w = alpha) = ∅ by
        simpa [U, alpha] using hZ] at hzZ
      simp at hzZ
    have : alpha = 0 := by
      change flip G U x = 0
      rw [flip_eq_sum_adjacencyBit]
      exact Finset.sum_eq_zero (fun z hz ↦ hallZero z hz)
    exact hne this
  have hallOne : ∀ z ∈ U, adjacencyBit G x z = 1 := by
    intro z hz
    by_contra hbit0
    have hzZ : z ∈ U.filter (fun w ↦ adjacencyBit G x w = alpha) := by
      have hbit1 := zmod2_eq_zero_of_ne_one (adjacencyBit G x z) hbit0
      simp [hz, hbit1, halpha0]
    rw [show U.filter (fun w ↦ adjacencyBit G x w = alpha) = ∅ by
      simpa [U, alpha] using hZ] at hzZ
    simp at hzZ
  have hbeta : beta = 1 := by
    apply hbad.beta_eq_one_of_alpha_eq_zero hroot
    simpa [U, alpha] using halpha0
  have hsum :
      (∑ z ∈ U, adjacencyBit G x z * flip G S z) =
        ∑ z ∈ U, flip G S z := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [hallOne z hz, one_mul]
  have hpSum := sum_flip_pairUntouched (G := G) hx hy hxy
  have hsplit := neighborDegreeBit_split_pair (G := G) hx hy hxy
  have hpy : flip G S y = beta + adjacencyBit G x y := by
    simpa [U, beta, adjacencyBit_self, adjacencyBit_comm,
      add_comm, add_left_comm, add_assoc] using
        (flip_eq_erase_erase_add (G := G) (w := y) hx hy hxy)
  have hbX : neighborDegreeBit G S x = 1 := by
    rw [hsplit, hsum, hpSum, hpy]
    simp only [U, alpha, beta] at halpha0 hbeta ⊢
    rw [halpha0, hbeta]
    let t := adjacencyBit G x y
    change t * (1 + t) + 1 = 1
    calc
      t * (1 + t) + 1 = (t + t * t) + 1 := by rw [mul_add, mul_one]
      _ = (t + t) + 1 := by rw [zmod2_sq_eq_self]
      _ = 1 := by rw [CharTwo.add_self_eq_zero, zero_add]
  refine ⟨?_, hbX, ?_⟩
  · simpa [U, beta] using hbeta
  · intro halpha1
    have : (0 : ZMod 2) = 1 := by
      simpa only [U, alpha, halpha0] using halpha1
    exact False.elim (zero_ne_one this)

omit [Fintype V] in
/-- Inductive handoff for every member of the complete zero-charge OPEN fan.
The three conclusions are exactly the child versions of equations (E1)--(E3)
before rewriting them into full-board degree notation. -/
theorem StoppedBadPair.zeroFan_child_bits
    {G : SimpleGraph V} {S : Finset V} {attacker : Bool} {x y z : V}
    (hbad : StoppedBadPair G S attacker x y)
    (hz : z ∈ (S.erase x).erase y)
    (hcoordinate : adjacencyBit G x z =
      flip G ((S.erase x).erase y) x)
    (hsmall : StoppedBadPairBits G (S.erase x) attacker) :
    flip G (((S.erase x).erase y).erase z) z = 1 ∧
      neighborDegreeBit G (S.erase x) y = 1 ∧
      (flip G (((S.erase x).erase y).erase z) y = 1 →
        ((S.erase x).card : ZMod 2) = 1) := by
  have hzero : flip G (((S.erase x).erase y).erase z) x = 0 := by
    rw [flip_erase_eq_add (G := G) hz, hcoordinate,
      CharTwo.add_self_eq_zero]
  have hchild := hbad.child_of_zero_open hz hzero
  simpa [Finset.erase_right_comm] using hsmall hchild

omit [Fintype V] in
/-- The complete nonempty zero-charge OPEN fan exports the three equations
used in the two algebraic case splits. -/
theorem StoppedBadPair.zeroFan_equations
    {G : SimpleGraph V} {S : Finset V} {attacker : Bool} {x y : V}
    (hbad : StoppedBadPair G S attacker x y)
    (hsmall : StoppedBadPairBits G (S.erase x) attacker)
    (hZ : (((S.erase x).erase y).filter (fun z ↦
      adjacencyBit G x z = flip G ((S.erase x).erase y) x)).Nonempty) :
    (∀ z ∈ ((S.erase x).erase y).filter (fun w ↦
        adjacencyBit G x w = flip G ((S.erase x).erase y) x),
      flip G S z + flip G ((S.erase x).erase y) x +
        adjacencyBit G y z = 1) ∧
    (neighborDegreeBit G S y +
      adjacencyBit G x y * flip G S x +
      (∑ w ∈ (S.erase x).erase y,
        adjacencyBit G x w * adjacencyBit G y w) = 1) ∧
    ((S.card : ZMod 2) = 1 →
      ∀ z ∈ ((S.erase x).erase y).filter (fun w ↦
          adjacencyBit G x w = flip G ((S.erase x).erase y) x),
        adjacencyBit G y z = flip G ((S.erase x).erase y) y) := by
  let U := (S.erase x).erase y
  let alpha := flip G U x
  let beta := flip G U y
  let Z := U.filter (fun z ↦ adjacencyBit G x z = alpha)
  have hx : x ∈ S := hbad.1
  have hy : y ∈ S := hbad.2.1
  have hxy : x ≠ y := hbad.2.2.1
  have hE1 : ∀ z ∈ Z,
      flip G S z + alpha + adjacencyBit G y z = 1 := by
    intro z hzZ
    have hzU : z ∈ U := (Finset.mem_filter.mp hzZ).1
    have hcoord : adjacencyBit G x z = alpha := (Finset.mem_filter.mp hzZ).2
    have hchild := hbad.zeroFan_child_bits hzU hcoord hsmall
    have hthree := flip_erase_erase_eq_add (G := G) (w := z) hx hy hxy
    have hself := flip_erase_eq_add (G := G) (w := z) hzU
    rw [hself, adjacencyBit_self, add_zero, hthree,
      adjacencyBit_comm G z x, adjacencyBit_comm G z y, hcoord] at hchild
    exact hchild.1
  have hE2 : neighborDegreeBit G S y +
      adjacencyBit G x y * flip G S x +
      (∑ w ∈ U, adjacencyBit G x w * adjacencyBit G y w) = 1 := by
    obtain ⟨z, hzZ⟩ := hZ
    have hzU : z ∈ U := by
      simpa [U, alpha, Z] using (Finset.mem_filter.mp hzZ).1
    have hcoord : adjacencyBit G x z = alpha := by
      simpa [U, alpha, Z] using (Finset.mem_filter.mp hzZ).2
    have hchild := hbad.zeroFan_child_bits hzU hcoord hsmall
    have hdelete := neighborDegreeBit_erase (G := G) (x := x) (y := y) hx
    have hcommon := commonNeighbor_sum_erase_eq_pairUntouched
      (G := G) hx hy hxy
    rw [hcommon] at hdelete
    rw [hdelete] at hchild
    simpa [U, adjacencyBit_comm G y x] using hchild.2.1
  have hE3 : (S.card : ZMod 2) = 1 →
      ∀ z ∈ Z, adjacencyBit G y z = beta := by
    intro hepsilon z hzZ
    have hzU : z ∈ U := (Finset.mem_filter.mp hzZ).1
    have hcoord : adjacencyBit G x z = alpha := (Finset.mem_filter.mp hzZ).2
    have hchild := hbad.zeroFan_child_bits hzU hcoord hsmall
    have hcard := card_erase_cast_add_one hx
    rw [hepsilon] at hcard
    have hcard0 : (((S.erase x).card : Nat) : ZMod 2) = 0 := by
      exact add_right_cancel (hcard.trans rfl)
    by_contra hY
    have hsumNe : beta + adjacencyBit G y z ≠ 0 := by
      intro hsum
      have heq : adjacencyBit G y z = beta := by
        calc
          adjacencyBit G y z = (beta + beta) + adjacencyBit G y z := by
            rw [CharTwo.add_self_eq_zero, zero_add]
          _ = beta + (beta + adjacencyBit G y z) := by abel
          _ = beta := by rw [hsum, add_zero]
      exact hY heq
    have hsum1 := zmod2_eq_one_of_ne_zero _ hsumNe
    have hcharge1 : flip G (U.erase z) y = 1 := by
      rw [flip_erase_eq_add (G := G) hzU, adjacencyBit_comm G y z]
      simpa [beta, adjacencyBit_comm G z y] using hsum1
    have hcard1 := hchild.2.2 hcharge1
    rw [hcard0] at hcard1
    exact zero_ne_one hcard1
  refine ⟨?_, ?_, ?_⟩
  · intro z hzZ
    exact hE1 z (by simpa [U, alpha, Z] using hzZ)
  · simpa [U] using hE2
  · intro hepsilon z hzZ
    have := hE3 hepsilon z (by simpa [U, alpha, Z] using hzZ)
    simpa [U, beta] using this

omit [Fintype V] in
/-- Nonempty zero-fan, source-charge-one branch of the stopped bad-pair
lemma. -/
theorem StoppedBadPair.bits_of_zeroFan_alpha_one
    {G : SimpleGraph V} {S : Finset V} {attacker : Bool} {x y : V}
    (hbad : StoppedBadPair G S attacker x y)
    (hsafe : ∀ T : Finset V, T ⊂ S → StoppedEmptyRootSafe G T attacker)
    (hsmall : StoppedBadPairBits G (S.erase x) attacker)
    (hZ : (((S.erase x).erase y).filter (fun z ↦
      adjacencyBit G x z = flip G ((S.erase x).erase y) x)).Nonempty)
    (halpha : flip G ((S.erase x).erase y) x = 1) :
    flip G ((S.erase x).erase y) y = 1 ∧
      neighborDegreeBit G S x = 1 ∧
      (flip G ((S.erase x).erase y) x = 1 →
        (S.card : ZMod 2) = 1) := by
  let U := (S.erase x).erase y
  let alpha := flip G U x
  let beta := flip G U y
  let a := adjacencyBit G x y
  let epsilon : ZMod 2 := S.card
  let r := alpha + beta
  let c := ∑ w ∈ U, adjacencyBit G x w * adjacencyBit G y w
  have hx : x ∈ S := hbad.1
  have hy : y ∈ S := hbad.2.1
  have hxy : x ≠ y := hbad.2.2.1
  have hfan := hbad.zeroFan_equations hsmall hZ
  have hE1 := hfan.1
  have hE2 := hfan.2.1
  have hE3 := hfan.2.2
  have hpEqY : ∀ z ∈ U.filter (fun w ↦ adjacencyBit G x w = alpha),
      flip G S z = adjacencyBit G y z := by
    intro z hzZ
    have h := hE1 z (by simpa [U, alpha] using hzZ)
    have ha1 : alpha = 1 := by simpa [U, alpha] using halpha
    rw [show flip G ((S.erase x).erase y) x = 1 from halpha] at h
    calc
      flip G S z = flip G S z +
          ((1 + 1) + (adjacencyBit G y z + adjacencyBit G y z)) := by
            rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
              zero_add, add_zero]
      _ = (flip G S z + 1 + adjacencyBit G y z) +
          (1 + adjacencyBit G y z) := by abel
      _ = adjacencyBit G y z := by
        rw [h]
        calc
          1 + (1 + adjacencyBit G y z) =
              (1 + 1) + adjacencyBit G y z := by abel
          _ = adjacencyBit G y z := by
            rw [CharTwo.add_self_eq_zero, zero_add]
  have hsumEq :
      (∑ z ∈ U, adjacencyBit G x z * flip G S z) = c := by
    simp only [c]
    apply Finset.sum_congr rfl
    intro z hzU
    by_cases hX0 : adjacencyBit G x z = 0
    · simp [hX0]
    · have hX1 := zmod2_eq_one_of_ne_zero (adjacencyBit G x z) hX0
      have hzZ : z ∈ U.filter (fun w ↦ adjacencyBit G x w = alpha) := by
        simp [hzU, hX1, show alpha = 1 by simpa [U, alpha] using halpha]
      rw [hpEqY z hzZ]
  have hpy : flip G S y = beta + a := by
    simpa [U, beta, a, adjacencyBit_self, adjacencyBit_comm,
      add_comm, add_left_comm, add_assoc] using
        (flip_eq_erase_erase_add (G := G) (w := y) hx hy hxy)
  have hpx : flip G S x = a + 1 := by
    simpa [U, a, adjacencyBit_self, add_comm, add_left_comm,
      add_assoc, halpha] using
        (flip_eq_erase_erase_add (G := G) (w := x) hx hy hxy)
  have hbXformula : neighborDegreeBit G S x = a * r + c := by
    have hsplit := neighborDegreeBit_split_pair (G := G) hx hy hxy
    rw [hsplit, hsumEq, hpy]
    simp only [r, alpha]
    rw [show flip G U x = 1 by simpa [U] using halpha]
    calc
      a * (beta + a) + c = a * (1 + beta) + c := by
        rw [mul_add, mul_add, zmod2_sq_eq_self, mul_one]
        abel
      _ = a * (1 + beta) + c := rfl
  have hbYformula : neighborDegreeBit G S y = 1 + c := by
    have hE2' : neighborDegreeBit G S y + a * flip G S x + c = 1 := by
      simpa [U, a, c] using hE2
    rw [hpx] at hE2'
    have hzero : a * (a + 1) = 0 := by
      rw [mul_add, mul_one, zmod2_sq_eq_self, CharTwo.add_self_eq_zero]
    rw [hzero, add_zero] at hE2'
    calc
      neighborDegreeBit G S y =
          (neighborDegreeBit G S y + c) + c := by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = 1 + c := by rw [hE2']
  have hmoment := hbad.moment hsafe
  have hmoment' : (a * r + c) + (1 + c) =
      (1 + r) * epsilon + a * r := by
    rw [hbXformula, hbYformula] at hmoment
    simpa [U, alpha, beta, a, epsilon, r] using hmoment
  have hleft : (a * r + c) + (1 + c) = 1 + a * r := by
    calc
      (a * r + c) + (1 + c) = 1 + a * r + (c + c) := by abel
      _ = 1 + a * r := by rw [CharTwo.add_self_eq_zero, add_zero]
  rw [hleft] at hmoment'
  have hprod : beta * epsilon = 1 := by
    have hcancel : (1 + r) * epsilon = 1 := by
      calc
        (1 + r) * epsilon = ((1 + r) * epsilon + a * r) + a * r := by
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        _ = (1 + a * r) + a * r := by rw [← hmoment']
        _ = 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have honeR : 1 + r = beta := by
      simp only [r, alpha]
      rw [show flip G U x = 1 by simpa [U] using halpha]
      calc
        1 + (1 + beta) = (1 + 1) + beta := by abel
        _ = beta := by rw [CharTwo.add_self_eq_zero, zero_add]
    rw [honeR] at hcancel
    exact hcancel
  have hbeta : beta = 1 := by
    by_contra hb0
    have hbzero := zmod2_eq_zero_of_ne_one beta hb0
    rw [hbzero, zero_mul] at hprod
    exact zero_ne_one hprod
  have hepsilon : epsilon = 1 := by
    by_contra he0
    have hezero := zmod2_eq_zero_of_ne_one epsilon he0
    rw [hezero, mul_zero] at hprod
    exact zero_ne_one hprod
  have hc : c = 1 := by
    have hall : ∀ z ∈ U,
        adjacencyBit G x z * adjacencyBit G y z = adjacencyBit G x z := by
      intro z hzU
      by_cases hX0 : adjacencyBit G x z = 0
      · simp [hX0]
      · have hX1 := zmod2_eq_one_of_ne_zero (adjacencyBit G x z) hX0
        have hzZ : z ∈ U.filter (fun w ↦ adjacencyBit G x w = alpha) := by
          simp [hzU, hX1, show alpha = 1 by simpa [U, alpha] using halpha]
        have hY := hE3 (by simpa [epsilon] using hepsilon) z
          (by simpa [U, alpha] using hzZ)
        rw [show adjacencyBit G y z = 1 by
          simpa [U, beta, hbeta] using hY, hX1]
        simp
    calc
      c = ∑ z ∈ U, adjacencyBit G x z := by
        simp only [c]
        apply Finset.sum_congr rfl
        exact hall
      _ = alpha := by rw [← flip_eq_sum_adjacencyBit G U x]
      _ = 1 := by simpa [U, alpha] using halpha
  have hbX : neighborDegreeBit G S x = 1 := by
    rw [hbXformula, hc]
    have hr0 : r = 0 := by
      simp only [r, alpha]
      rw [show flip G U x = 1 by simpa [U] using halpha, hbeta,
        CharTwo.add_self_eq_zero]
    rw [hr0, mul_zero, zero_add]
  refine ⟨?_, hbX, ?_⟩
  · simpa [U, beta] using hbeta
  · intro _
    simpa [epsilon] using hepsilon

omit [Fintype V] in
/-- Nonempty zero-fan, source-charge-zero branch of the stopped bad-pair
lemma. -/
theorem StoppedBadPair.bits_of_zeroFan_alpha_zero
    {G : SimpleGraph V} {S : Finset V} {attacker : Bool} {x y : V}
    (hbad : StoppedBadPair G S attacker x y)
    (hsafe : ∀ T : Finset V, T ⊂ S → StoppedEmptyRootSafe G T attacker)
    (hsmall : StoppedBadPairBits G (S.erase x) attacker)
    (hZ : (((S.erase x).erase y).filter (fun z ↦
      adjacencyBit G x z = flip G ((S.erase x).erase y) x)).Nonempty)
    (halpha : flip G ((S.erase x).erase y) x = 0) :
    flip G ((S.erase x).erase y) y = 1 ∧
      neighborDegreeBit G S x = 1 ∧
      (flip G ((S.erase x).erase y) x = 1 →
        (S.card : ZMod 2) = 1) := by
  let U := (S.erase x).erase y
  let X := fun z ↦ adjacencyBit G x z
  let Y := fun z ↦ adjacencyBit G y z
  let alpha := flip G U x
  let beta := flip G U y
  let a := adjacencyBit G x y
  let epsilon : ZMod 2 := S.card
  let r := alpha + beta
  let c := ∑ w ∈ U, X w * Y w
  let Z := U.filter (fun z ↦ X z = alpha)
  have hx : x ∈ S := hbad.1
  have hy : y ∈ S := hbad.2.1
  have hxy : x ≠ y := hbad.2.2.1
  have hyErase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
  have hUSub : U ⊂ S := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun z hz ↦ Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz), ?_⟩
    intro hEq
    have hxU : x ∈ U := hEq ▸ hx
    exact (by simp [U] at hxU)
  have hroot := hsafe U hUSub
  have hbeta : beta = 1 := by
    apply hbad.beta_eq_one_of_alpha_eq_zero hroot
    simpa [U, alpha] using halpha
  have hfan := hbad.zeroFan_equations hsmall hZ
  have hE1 := hfan.1
  have hE2 := hfan.2.1
  have hE3 := hfan.2.2
  have hpx : flip G S x = a := by
    simpa [U, a, adjacencyBit_self, add_comm, add_left_comm,
      add_assoc, halpha] using
        (flip_eq_erase_erase_add (G := G) (w := x) hx hy hxy)
  have hpy : flip G S y = 1 + a := by
    have h := flip_eq_erase_erase_add (G := G) (w := y) hx hy hxy
    simpa [U, beta, a, adjacencyBit_self, adjacencyBit_comm,
      add_comm, add_left_comm, add_assoc, hbeta] using h
  have hpSum := sum_flip_pairUntouched (G := G) hx hy hxy
  have hpSum' : (∑ z ∈ U, flip G S z) = 1 := by
    simpa [U, alpha, beta, halpha, hbeta] using hpSum
  have hsumXp : (∑ z ∈ U, X z * flip G S z) =
      neighborDegreeBit G S x := by
    have hsplit := neighborDegreeBit_split_pair (G := G) hx hy hxy
    have ha0 : a * (1 + a) = 0 := by
      rw [mul_add, mul_one, zmod2_sq_eq_self, CharTwo.add_self_eq_zero]
    rw [hpy, ha0, zero_add] at hsplit
    simpa [U, X] using hsplit.symm
  have hsumZY : (∑ z ∈ Z, Y z) = 1 + c := by
    have hfilter := sum_one_add_bit_mul_eq_filter_zero U X Y
    have hsumY : (∑ z ∈ U, Y z) = 1 := by
      rw [show (∑ z ∈ U, Y z) = flip G U y by
        simpa [Y] using (flip_eq_sum_adjacencyBit G U y).symm]
      exact hbeta
    calc
      (∑ z ∈ Z, Y z) = ∑ z ∈ U, (1 + X z) * Y z := by
        simpa [Z, halpha, U, X, alpha] using hfilter.symm
      _ = (∑ z ∈ U, Y z) + ∑ z ∈ U, X z * Y z := by
        simp_rw [add_mul, one_mul]
        rw [Finset.sum_add_distrib]
      _ = 1 + c := by rw [hsumY]
  have hsumZp : (∑ z ∈ Z, flip G S z) =
      1 + neighborDegreeBit G S x := by
    have hfilter := sum_one_add_bit_mul_eq_filter_zero U X
      (fun z ↦ flip G S z)
    calc
      (∑ z ∈ Z, flip G S z) =
          ∑ z ∈ U, (1 + X z) * flip G S z := by
            simpa [Z, halpha, U, X, alpha] using hfilter.symm
      _ = (∑ z ∈ U, flip G S z) +
          ∑ z ∈ U, X z * flip G S z := by
            simp_rw [add_mul, one_mul]
            rw [Finset.sum_add_distrib]
      _ = 1 + neighborDegreeBit G S x := by rw [hpSum', hsumXp]
  have hcardZ : ((Z.card : Nat) : ZMod 2) = epsilon := by
    have hfilter := sum_one_add_bit_mul_eq_filter_zero U X (fun _ ↦ (1 : ZMod 2))
    have hsumX : (∑ z ∈ U, X z) = 0 := by
      rw [show (∑ z ∈ U, X z) = flip G U x by
        simpa [X] using (flip_eq_sum_adjacencyBit G U x).symm]
      simpa [U, alpha] using halpha
    have hcardU := card_erase_erase_cast_eq hx hy hxy
    calc
      ((Z.card : Nat) : ZMod 2) = ∑ z ∈ Z, (1 : ZMod 2) := by simp
      _ = ∑ z ∈ U, (1 + X z) * 1 := by
        simpa [Z, halpha, U, X, alpha] using hfilter.symm
      _ = (∑ z ∈ U, (1 : ZMod 2)) + ∑ z ∈ U, X z := by
        simp_rw [mul_one]
        rw [Finset.sum_add_distrib]
      _ = (U.card : ZMod 2) := by rw [hsumX]; simp
      _ = epsilon := by simpa [U, epsilon] using hcardU
  have hsumE1 : (∑ z ∈ Z, flip G S z) + (∑ z ∈ Z, Y z) =
      (Z.card : ZMod 2) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ z ∈ Z, (flip G S z + Y z)) = ∑ z ∈ Z, (1 : ZMod 2) := by
        apply Finset.sum_congr rfl
        intro z hzZ
        have h := hE1 z (by simpa [U, X, alpha, Z] using hzZ)
        simpa [U, Y, alpha, halpha] using h
      _ = (Z.card : ZMod 2) := by simp
  have hbXcEpsilon : neighborDegreeBit G S x + c = epsilon := by
    rw [hsumZp, hsumZY, hcardZ] at hsumE1
    have heq : (1 + neighborDegreeBit G S x) + (1 + c) =
        neighborDegreeBit G S x + c := by
      calc
        (1 + neighborDegreeBit G S x) + (1 + c) =
            (neighborDegreeBit G S x + c) + (1 + 1) := by abel
        _ = neighborDegreeBit G S x + c := by
          rw [CharTwo.add_self_eq_zero, add_zero]
    calc
      neighborDegreeBit G S x + c =
          (1 + neighborDegreeBit G S x) + (1 + c) := heq.symm
      _ = epsilon := hsumE1
  have hbYformula : neighborDegreeBit G S y = 1 + a + c := by
    have hE2' : neighborDegreeBit G S y + a * flip G S x + c = 1 := by
      simpa [U, X, Y, a, c] using hE2
    rw [hpx, zmod2_sq_eq_self] at hE2'
    calc
      neighborDegreeBit G S y =
          (neighborDegreeBit G S y + a + c) + (a + c) := by
            calc
              neighborDegreeBit G S y = neighborDegreeBit G S y +
                  ((a + c) + (a + c)) := by
                    rw [CharTwo.add_self_eq_zero, add_zero]
              _ = _ := by abel
      _ = 1 + a + c := by rw [hE2']; abel
  have hmoment := hbad.moment hsafe
  have hbXcOne : neighborDegreeBit G S x + c = 1 := by
    have hmoment' : neighborDegreeBit G S x + (1 + a + c) = a := by
      rw [hbYformula] at hmoment
      simpa [U, alpha, beta, a, epsilon, r, halpha, hbeta,
        CharTwo.add_self_eq_zero] using hmoment
    calc
      neighborDegreeBit G S x + c =
          (neighborDegreeBit G S x + (1 + a + c)) + (1 + a) := by
            calc
              neighborDegreeBit G S x + c =
                  (neighborDegreeBit G S x + c) +
                    ((1 + 1) + (a + a)) := by
                      rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
                        zero_add, add_zero]
              _ = _ := by abel
      _ = a + (1 + a) := by rw [hmoment']
      _ = 1 := by
        calc
          a + (1 + a) = 1 + (a + a) := by abel
          _ = 1 := by rw [CharTwo.add_self_eq_zero, add_zero]
  have hepsilon : epsilon = 1 := by rw [← hbXcEpsilon, hbXcOne]
  have hallY : ∀ z ∈ Z, Y z = 1 := by
    intro z hzZ
    have h := hE3 (by simpa [epsilon] using hepsilon) z
      (by simpa [U, X, alpha, Z] using hzZ)
    simpa [U, Y, beta, hbeta] using h
  have hc : c = 0 := by
    have hsumZY' : (∑ z ∈ Z, Y z) = (Z.card : ZMod 2) := by
      calc
        (∑ z ∈ Z, Y z) = ∑ z ∈ Z, (1 : ZMod 2) := by
          apply Finset.sum_congr rfl
          intro z hzZ
          rw [hallY z hzZ]
        _ = (Z.card : ZMod 2) := by simp
    have honec : 1 + c = 1 := by
      calc
        1 + c = ∑ z ∈ Z, Y z := hsumZY.symm
        _ = (Z.card : ZMod 2) := hsumZY'
        _ = epsilon := hcardZ
        _ = 1 := hepsilon
    apply add_left_cancel (a := (1 : ZMod 2))
    simpa using honec
  have hbX : neighborDegreeBit G S x = 1 := by
    rw [hc, add_zero] at hbXcOne
    exact hbXcOne
  refine ⟨?_, hbX, ?_⟩
  · simpa [U, beta] using hbeta
  · intro hcontra
    have : (0 : ZMod 2) = 1 := by
      simpa only [U, alpha, halpha] using hcontra
    exact False.elim (zero_ne_one this)

omit [Fintype V] in
/-- The bad-pair bits plus the already-proved moment identity imply strict
rank descent on the current board. -/
theorem stoppedBadPairRankDescent_of_bits
    {G : SimpleGraph V} {S : Finset V} {attacker : Bool}
    (hbits : StoppedBadPairBits G S attacker)
    (hsafe : ∀ T : Finset V, T ⊂ S → StoppedEmptyRootSafe G T attacker) :
    StoppedBadPairRankDescent G S attacker := by
  intro x y hbad
  have hx : x ∈ S := hbad.1
  have hy : y ∈ S := hbad.2.1
  have hxy : x ≠ y := hbad.2.2.1
  let U := (S.erase x).erase y
  let a := adjacencyBit G x y
  let alpha := flip G U x
  let beta := flip G U y
  let epsilon : ZMod 2 := S.card
  let px := flip G S x
  let py := flip G S y
  let bX := neighborDegreeBit G S x
  let bY := neighborDegreeBit G S y
  let r := alpha + beta
  have hpx : px = a + alpha := by
    simpa [U, px, a, alpha, adjacencyBit_self, add_comm, add_left_comm,
      add_assoc] using
        (flip_eq_erase_erase_add (G := G) (w := x) hx hy hxy)
  have hpy : py = a + beta := by
    simpa [U, py, a, beta, adjacencyBit_self, adjacencyBit_comm,
      add_comm, add_left_comm, add_assoc] using
        (flip_eq_erase_erase_add (G := G) (w := y) hx hy hxy)
  obtain ⟨hbeta, hbX, halpha⟩ := hbits hbad
  have hmoment := hbad.moment hsafe
  exact stoppedBadArc_rank_lt a alpha beta epsilon px py bX bY r
    hpx hpy rfl (by simpa [U, beta] using hbeta)
    (by simpa [bX] using hbX)
    (by simpa [U, alpha, epsilon] using halpha)
    (by simpa [U, alpha, beta, epsilon, a, bX, bY, r] using hmoment)

omit [Fintype V] in
/-- Once bad-pair rank descent is available on a board of order at least two,
the complete root fan contradicts finiteness. -/
theorem stoppedEmptyRootSafe_of_rankDescent
    {G : SimpleGraph V} {S : Finset V} {attacker : Bool}
    (hcard : 2 ≤ S.card) (hdesc : StoppedBadPairRankDescent G S attacker) :
    StoppedEmptyRootSafe G S attacker := by
  intro hwin
  have hout := hwin.outgoing_stoppedBadPair hcard
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  exact no_total_strict_rank_relation S hS
    (StoppedBadPair G S attacker)
    (fun v ↦ stoppedBadRank (flip G S v) (neighborDegreeBit G S v))
    hout (fun hx hy hbad ↦ hdesc hbad)

/-- Strategy-level form of the mutual fan step.  Its induction
hypothesis supplies both stopped empty-root safety and the three bad-pair bits
on every proper subboard; all defender siblings stay inside `StoppedBadPair`. -/
def StoppedBadPairFanLift (G : SimpleGraph V) (attacker : Bool) : Prop :=
  ∀ S : Finset V,
    (∀ T : Finset V, T ⊂ S →
      StoppedEmptyRootSafe G T attacker ∧
        StoppedBadPairBits G T attacker) →
      StoppedBadPairBits G S attacker

omit [Fintype V] in
/-- The audited three-way zero-fan proof: empty fibre, nonempty source-charge
one, and nonempty source-charge zero. -/
theorem stoppedBadPairFanLift (G : SimpleGraph V) (attacker : Bool) :
    StoppedBadPairFanLift G attacker := by
  intro S ih x y hbad
  let U := (S.erase x).erase y
  let alpha := flip G U x
  let Z := U.filter (fun z ↦ adjacencyBit G x z = alpha)
  have hx : x ∈ S := hbad.1
  have hy : y ∈ S := hbad.2.1
  have hxy : x ≠ y := hbad.2.2.1
  have hproperU : U ⊂ S := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun z hz ↦ Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz), ?_⟩
    intro hEq
    have hxU : x ∈ U := hEq ▸ hx
    exact (by simp [U] at hxU)
  have hroot : StoppedEmptyRootSafe G U attacker := (ih U hproperU).1
  by_cases hZ0 : Z = ∅
  · apply hbad.bits_of_zeroFan_empty hroot
    simpa [U, alpha, Z] using hZ0
  · have hZne : Z.Nonempty := Finset.nonempty_iff_ne_empty.mpr hZ0
    have hsmall : StoppedBadPairBits G (S.erase x) attacker :=
      (ih (S.erase x) (Finset.erase_ssubset hx)).2
    have hsafe : ∀ T : Finset V, T ⊂ S →
        StoppedEmptyRootSafe G T attacker := fun T hT ↦ (ih T hT).1
    by_cases halpha0 : alpha = 0
    · apply hbad.bits_of_zeroFan_alpha_zero hsafe hsmall
        (by simpa [U, alpha, Z] using hZne)
      simpa [U, alpha] using halpha0
    · have halpha1 : alpha = 1 := zmod2_eq_one_of_ne_zero alpha halpha0
      apply hbad.bits_of_zeroFan_alpha_one hsafe hsmall
        (by simpa [U, alpha, Z] using hZne)
      simpa [U, alpha] using halpha1

omit [Fintype V] in
/-- The mutual-induction shell is complete: the local fan lift alone implies
the stopped close-first empty-root theorem on every finite board. -/
theorem stoppedEmptyRootSafe_of_badPairFanLift
    (G : SimpleGraph V) (attacker : Bool)
    (hfan : StoppedBadPairFanLift G attacker) :
    ∀ S : Finset V, StoppedEmptyRootSafe G S attacker := by
  have hall : ∀ S : Finset V,
      StoppedEmptyRootSafe G S attacker ∧
        StoppedBadPairBits G S attacker := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
        have hbits := hfan S ih
        have hsafe : ∀ T : Finset V, T ⊂ S →
            StoppedEmptyRootSafe G T attacker := fun T hT ↦ (ih T hT).1
        have hdesc := stoppedBadPairRankDescent_of_bits hbits hsafe
        refine ⟨?_, hbits⟩
        by_cases h0 : S = ∅
        · subst S
          exact stoppedEmptyRootSafe_empty G attacker
        by_cases h1 : S.card = 1
        · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
          exact stoppedEmptyRootSafe_singleton G attacker x
        have hcard0 : S.card ≠ 0 :=
          Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
        have hcard : 2 ≤ S.card := by omega
        exact stoppedEmptyRootSafe_of_rankDescent hcard hdesc
  exact fun S ↦ (hall S).1

/-- Exact formal statement of the stopped CLOSE-first empty-root theorem. -/
def StoppedCloseFirstEmptyRootTheorem : Prop :=
  ∀ (V : Type*) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (attacker : Bool) (S : Finset V),
      StoppedEmptyRootSafe G S attacker

/-- The stopped CLOSE-first empty-root theorem, fully kernel-checked. -/
theorem stoppedCloseFirstEmptyRootTheorem :
    StoppedCloseFirstEmptyRootTheorem := by
  intro V _ _ G attacker S
  exact stoppedEmptyRootSafe_of_badPairFanLift G attacker
    (stoppedBadPairFanLift G attacker) S

omit [Fintype V] in
/-- Once the untouched set is empty, a CLOSE-first strategy can force only
the score already present at the root.  PASS and every remaining CLOSE are
score-neutral there. -/
theorem CloseFirstWins.target_eq_of_untouched_empty
    {G : SimpleGraph V} {attacker : Bool} {target : ZMod 2} {s : State V}
    (h : CloseFirstWins G attacker target s) (hU : s.untouched = ∅) :
    target = s.score := by
  induction h with
  | terminal _ _ hscore => exact hscore.symm
  | choose _ _ _ _ hstep _ _ ih =>
      have hU' := step_untouched_eq_empty hU hstep
      have hscore := step_score_eq_of_untouched_empty hU hstep
      rw [ih hU', hscore]
  | answer _ _ hasMove _ ih =>
      obtain ⟨m, s', hstep⟩ := hasMove
      have hU' := step_untouched_eq_empty hU hstep
      have hscore := step_score_eq_of_untouched_empty hU hstep
      rw [ih m s' hstep hU', hscore]

omit [Fintype V] in
/-- With no untouched vertex, no CLOSE-first strategy can force the score to
change.  This is the rank-zero base of the conditioned theorem. -/
theorem not_closeFirstWins_next_of_untouched_empty
    {G : SimpleGraph V} {attacker : Bool} {s : State V}
    (hU : s.untouched = ∅) :
    ¬CloseFirstWins G attacker (s.score + 1) s := by
  intro hwin
  have htarget := hwin.target_eq_of_untouched_empty hU
  have htarget' : s.score + 1 = s.score := htarget
  have h10 : (1 : ZMod 2) = 0 := by
    calc
      1 = -s.score + (s.score + 1) := by abel
      _ = -s.score + s.score := by rw [htarget']
      _ = 0 := by abel
  exact one_ne_zero h10

omit [Fintype V] in
/-- The first base case of the conditioned CLOSE-first theorem.  If the
defender moves with one untouched vertex and a clear nonempty queue, opening
that vertex removes every possible future charge.  Thus a CLOSE-first
attacker cannot change the score parity from this checkpoint. -/
theorem not_closeFirstWins_next_of_singleton_untouched
    {G : SimpleGraph V} {attacker : Bool} {s : State V} {x : V}
    (hdefender : s.toMove ≠ attacker) (hU : s.untouched = {x})
    (hqueue : s.queue ≠ []) :
    ¬CloseFirstWins G attacker (s.score + 1) s := by
  intro hwin
  cases hwin with
  | terminal _ hterminal _ => exact hqueue hterminal.2
  | choose _ hattacker _ _ _ _ _ => exact hdefender hattacker
  | answer _ _ _ hanswer =>
      cases hq : s.queue with
      | nil => exact False.elim (hqueue hq)
      | cons f q =>
          let s' : State V := {
            untouched := ∅
            queue := f :: q ++ [x]
            ko := false
            toMove := !s.toMove
            score := s.score }
          have hopen : step G s (.open x) = some s' := by
            simp [step, s', hq, hU]
          have hchild := hanswer (.open x) s' hopen
          have htarget := hchild.target_eq_of_untouched_empty (by rfl)
          have htarget' : s.score + 1 = s.score := by
            simp only [s'] at htarget
            exact htarget
          have h10 : (1 : ZMod 2) = 0 := by
            calc
              1 = -s.score + (s.score + 1) := by abel
              _ = -s.score + s.score := by rw [htarget']
              _ = 0 := by abel
          exact one_ne_zero h10

omit [Fintype V] in
/-- If exactly one untouched vertex remains and CLOSE is illegal, the only
possible score-changing phase is over: either player must OPEN that vertex,
after which every charge is zero. -/
theorem CloseFirstWins.target_eq_score_of_singleton_no_close
    {G : SimpleGraph V} {attacker : Bool} {target : ZMod 2}
    {s : State V} {u : V} (hwin : CloseFirstWins G attacker target s)
    (hU : s.untouched = {u}) (hnoClose : ¬∃ sc, step G s .close = some sc) :
    target = s.score := by
  classical
  by_cases hattacker : s.toMove = attacker
  · cases hwin with
    | terminal _ hterminal _ =>
        simp [Terminal, hU] at hterminal
    | answer _ hdefender _ _ => exact False.elim (hdefender hattacker)
    | choose _ _ m s' hstep _ hchild =>
        cases m with
        | close => exact False.elim (hnoClose ⟨s', hstep⟩)
        | pass => simp [step, hU] at hstep
        | «open» v =>
            have hv : v ∈ s.untouched := by
              simp only [step] at hstep
              split at hstep
              · assumption
              · contradiction
            have hvu : v = u := by simpa [hU] using hv
            have hU' : s'.untouched = ∅ := by
              simp only [step] at hstep
              split at hstep
              · cases hstep
                simp [hU, hvu]
              · contradiction
            have htarget := hchild.target_eq_of_untouched_empty hU'
            rw [open_score hstep] at htarget
            exact htarget
  · let s' : State V := {
      untouched := ∅
      queue := s.queue ++ [u]
      ko := s.queue.isEmpty
      toMove := !s.toMove
      score := s.score }
    have hopen : step G s (.open u) = some s' := by
      simp [step, s', hU]
    have hchild := hwin.answer_child hattacker hopen
    exact hchild.target_eq_of_untouched_empty rfl

/-- A state used while deliberately draining a fixed FIFO queue. -/
def drainState (U : Finset V) (q : List V) (turn : Bool)
    (score : ZMod 2) : State V where
  untouched := U
  queue := q
  ko := false
  toMove := turn
  score := score

omit [Fintype V] in
/-- Once the empty-queue endpoint is known to preserve the score, alternating
defender CLOSE choices and mandatory attacker CLOSEs compute the target as
the initial score plus the whole live queue cut. -/
theorem CloseFirstWins.target_eq_score_add_sum_flip_of_drain
    {G : SimpleGraph V} {attacker turn : Bool} {target score : ZMod 2}
    {U : Finset V} {q : List V}
    (hfinish : ∀ (turn' : Bool) (score' : ZMod 2),
      CloseFirstWins G attacker target (drainState U [] turn' score') →
        target = score')
    (hwin : CloseFirstWins G attacker target (drainState U q turn score)) :
    target = score + (q.map (flip G U)).sum := by
  induction q generalizing turn score with
  | nil => simpa [drainState] using hfinish turn score hwin
  | cons f q ih =>
      let s' := drainState U q (!turn) (score + flip G U f)
      have hclose : step G (drainState U (f :: q) turn score) .close =
          some s' := by
        simp [step, drainState, s']
      have hchild : CloseFirstWins G attacker target s' := by
        by_cases hattacker : turn = attacker
        · exact hwin.close_child (by simpa [drainState] using hattacker) hclose
        · exact hwin.answer_child (by simpa [drainState] using hattacker) hclose
      have htarget := ih hchild
      simpa [s', List.sum_cons, add_assoc] using htarget

omit [Fintype V] in
/-- With exactly two untouched vertices and an empty clear queue, ko forces
both OPENs before either new queue cell can close, so the score cannot change. -/
theorem CloseFirstWins.target_eq_score_of_pair_empty
    {G : SimpleGraph V} {attacker turn : Bool} {target score : ZMod 2}
    {x y : V} (hxy : x ≠ y)
    (hwin : CloseFirstWins G attacker target
      (drainState {x, y} [] turn score)) : target = score := by
  classical
  let s := drainState ({x, y} : Finset V) [] turn score
  by_cases hattacker : turn = attacker
  · cases hwin with
    | terminal _ hterminal _ => simp [Terminal, drainState] at hterminal
    | answer _ hdefender _ _ =>
        exact False.elim (hdefender (by simpa [drainState] using hattacker))
    | choose _ _ m s' hstep _ hchild =>
        cases m with
        | close => simp [step, drainState] at hstep
        | pass => simp [step, drainState] at hstep
        | «open» v =>
            have hv : v ∈ ({x, y} : Finset V) := by
              simp only [step] at hstep
              split at hstep
              · assumption
              · contradiction
            let sv : State V := {
              untouched := ({x, y} : Finset V).erase v
              queue := [v]
              ko := true
              toMove := !turn
              score := score }
            have hs' : s' = sv := by
              simp only [step] at hstep
              split at hstep
              · cases hstep
                simp [drainState, sv]
              · contradiction
            rw [hs'] at hchild
            have hcard : (({x, y} : Finset V).erase v).card = 1 := by
              rw [Finset.card_erase_of_mem hv]
              simp [hxy]
            obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard
            have hU' : sv.untouched = {u} := by exact hu
            have hnoClose : ¬∃ sc, step G sv .close = some sc := by
              simp [step, sv]
            have ht := hchild.target_eq_score_of_singleton_no_close hU' hnoClose
            simpa [sv] using ht
  · let sx : State V := {
      untouched := {y}
      queue := [x]
      ko := true
      toMove := !turn
      score := score }
    have hopen : step G (drainState ({x, y} : Finset V) [] turn score)
        (.open x) = some sx := by
      simp [step, drainState, sx, hxy]
    have hchild := hwin.answer_child (by simpa [drainState] using hattacker) hopen
    have hnoClose : ¬∃ sc, step G sx .close = some sc := by
      intro hc
      obtain ⟨sc, hc⟩ := hc
      simp [step, sx] at hc
    exact hchild.target_eq_score_of_singleton_no_close rfl hnoClose

/-- Exact dummy-free target of the conditioned CLOSE-first argument.
`Coherent` records precisely the reachability invariants used by the proof:
queue nodupness, queue/untouched disjointness, and the singleton shape of a
ko-protected queue. -/
theorem ConditionedCloseFirstTheorem :
    ∀ (V : Type*) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (attacker : Bool) (s : State V),
        Coherent s → s.toMove ≠ attacker → s.queue ≠ [] → s.ko = false →
          ¬CloseFirstWins G attacker (s.score + 1) s := by
  intro V _ _ G attacker s
  induction s using (measure rank).wf.induction with
  | h s ih =>
      intro hcoherent hdefender hqueue hko hwin
      classical
      by_cases hU0 : s.untouched = ∅
      · exact not_closeFirstWins_next_of_untouched_empty hU0 hwin
      by_cases hU1 : s.untouched.card = 1
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hU1
        exact not_closeFirstWins_next_of_singleton_untouched
          hdefender hx hqueue hwin
      by_cases hU2 : s.untouched.card = 2
      · obtain ⟨x, y, hxy, hU⟩ := Finset.card_eq_two.mp hU2
        cases hq : s.queue with
        | nil => exact False.elim (hqueue hq)
        | cons f q =>
          have hEraseX : s.untouched.erase x = {y} := by
            rw [hU]
            simp [hxy]
          have hEraseY : s.untouched.erase y = {x} := by
            rw [hU]
            ext z
            simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨_, rfl | rfl⟩
              · rfl
              · contradiction
            · intro hz
              subst z
              exact ⟨hxy, Or.inl rfl⟩
          have hxmem : x ∈ s.untouched := by simp [hU]
          have hymem : y ∈ s.untouched := by simp [hU]
          have hturn : (!s.toMove : Bool) = attacker := by
            cases hs : s.toMove <;> cases ha : attacker <;> simp_all
          let sox : State V := {
            untouched := {y}
            queue := f :: (q ++ [x])
            ko := false
            toMove := !s.toMove
            score := s.score }
          have hopenx : step G s (.open x) = some sox := by
            simp [step, sox, hq, hxmem, hEraseX]
          have hwinox := hwin.answer_child hdefender hopenx
          have hfrontY : adjacencyBit G f y = 1 := by
            have hne : adjacencyBit G f y ≠ 0 := by
              intro hzero
              let sy : State V := {
                untouched := {y}
                queue := q ++ [x]
                ko := false
                toMove := s.toMove
                score := s.score }
              have hclose : step G sox .close = some sy := by
                simp [step, sox, sy, flip_singleton_eq_adjacencyBit, hzero]
              have hwiny := hwinox.close_child (by
                change (!s.toMove : Bool) = attacker
                exact hturn) hclose
              exact not_closeFirstWins_next_of_singleton_untouched
                (s := sy) hdefender rfl (by simp [sy]) hwiny
            exact zmod2_eq_one_of_ne_zero _ hne
          let sy : State V := {
            untouched := {y}
            queue := q ++ [x]
            ko := false
            toMove := s.toMove
            score := s.score + 1 }
          have hcloseY : step G sox .close = some sy := by
            simp [step, sox, sy, flip_singleton_eq_adjacencyBit, hfrontY]
          have hwinY : CloseFirstWins G attacker (s.score + 1) sy :=
            hwinox.close_child (by
              change (!s.toMove : Bool) = attacker
              exact hturn) hcloseY
          let soy : State V := {
            untouched := {x}
            queue := f :: (q ++ [y])
            ko := false
            toMove := !s.toMove
            score := s.score }
          have hopeny : step G s (.open y) = some soy := by
            simp [step, soy, hq, hymem, hEraseY]
          have hwinoy := hwin.answer_child hdefender hopeny
          have hfrontX : adjacencyBit G f x = 1 := by
            have hne : adjacencyBit G f x ≠ 0 := by
              intro hzero
              let sx : State V := {
                untouched := {x}
                queue := q ++ [y]
                ko := false
                toMove := s.toMove
                score := s.score }
              have hclose : step G soy .close = some sx := by
                simp [step, soy, sx, flip_singleton_eq_adjacencyBit, hzero]
              have hwinx := hwinoy.close_child (by
                change (!s.toMove : Bool) = attacker
                exact hturn) hclose
              exact not_closeFirstWins_next_of_singleton_untouched
                (s := sx) hdefender rfl (by simp [sx]) hwinx
            exact zmod2_eq_one_of_ne_zero _ hne
          let sx : State V := {
            untouched := {x}
            queue := q ++ [y]
            ko := false
            toMove := s.toMove
            score := s.score + 1 }
          have hcloseX : step G soy .close = some sx := by
            simp [step, soy, sx, flip_singleton_eq_adjacencyBit, hfrontX]
          have hwinX : CloseFirstWins G attacker (s.score + 1) sx :=
            hwinoy.close_child (by
              change (!s.toMove : Bool) = attacker
              exact hturn) hcloseX
          have hfinishY : ∀ (turn' : Bool) (score' : ZMod 2),
              CloseFirstWins G attacker (s.score + 1)
                (drainState {y} [] turn' score') → s.score + 1 = score' := by
            intro turn' score' hw
            exact hw.target_eq_score_of_singleton_no_close rfl (by
              simp [step, drainState])
          have hwinY' : CloseFirstWins G attacker (s.score + 1)
              (drainState {y} (q ++ [x]) s.toMove (s.score + 1)) := by
            simpa [sy, drainState] using hwinY
          have hsumY :=
            hwinY'.target_eq_score_add_sum_flip_of_drain hfinishY
          have hzeroY : ((q ++ [x]).map (flip G {y})).sum = 0 := by
            have h := congrArg (fun z ↦ z - (s.score + 1)) hsumY
            simpa using h.symm
          have hfinishX : ∀ (turn' : Bool) (score' : ZMod 2),
              CloseFirstWins G attacker (s.score + 1)
                (drainState {x} [] turn' score') → s.score + 1 = score' := by
            intro turn' score' hw
            exact hw.target_eq_score_of_singleton_no_close rfl (by
              simp [step, drainState])
          have hwinX' : CloseFirstWins G attacker (s.score + 1)
              (drainState {x} (q ++ [y]) s.toMove (s.score + 1)) := by
            simpa [sx, drainState] using hwinX
          have hsumX :=
            hwinX'.target_eq_score_add_sum_flip_of_drain hfinishX
          have hzeroX : ((q ++ [y]).map (flip G {x})).sum = 0 := by
            have h := congrArg (fun z ↦ z - (s.score + 1)) hsumX
            simpa using h.symm
          have haddZeroEq (a b : ZMod 2) (hab : a + b = 0) : a = b := by
            calc
              a = a + (b + b) := by rw [CharTwo.add_self_eq_zero, add_zero]
              _ = (a + b) + b := by abel
              _ = b := by rw [hab, zero_add]
          have hqx : (q.map (flip G {x})).sum = adjacencyBit G x y := by
            have h : (q.map (flip G {x})).sum + adjacencyBit G y x = 0 := by
              simpa [List.map_append, flip_singleton_eq_adjacencyBit,
                List.sum_append] using hzeroX
            rw [adjacencyBit_comm G y x] at h
            exact haddZeroEq _ _ h
          have hqy : (q.map (flip G {y})).sum = adjacencyBit G x y := by
            have h : (q.map (flip G {y})).sum + adjacencyBit G x y = 0 := by
              simpa [List.map_append, flip_singleton_eq_adjacencyBit,
                List.sum_append] using hzeroY
            exact haddZeroEq _ _ h
          have hqsplit : (q.map (flip G {x, y})).sum =
              (q.map (flip G {x})).sum + (q.map (flip G {y})).sum :=
            sum_flip_pair hxy q
          have hqzero : (q.map (flip G {x, y})).sum = 0 := by
            rw [hqsplit, hqx, hqy]
            exact CharTwo.add_self_eq_zero _
          have hfrontzero : flip G {x, y} f = 0 := by
            rw [flip_pair hxy, hfrontX, hfrontY]
            exact CharTwo.add_self_eq_zero _
          have hwinDrain : CloseFirstWins G attacker (s.score + 1)
              (drainState {x, y} (f :: q) s.toMove s.score) := by
            have hsDrain : s =
                drainState ({x, y} : Finset V) (f :: q) s.toMove s.score := by
              cases s with
              | mk U Q ko turn score =>
                  change U = {x, y} at hU
                  change Q = f :: q at hq
                  change ko = false at hko
                  subst U
                  subst Q
                  subst ko
                  rfl
            rw [← hsDrain]
            exact hwin
          have hfinishPair : ∀ (turn' : Bool) (score' : ZMod 2),
              CloseFirstWins G attacker (s.score + 1)
                (drainState {x, y} [] turn' score') → s.score + 1 = score' := by
            intro turn' score' hw
            exact hw.target_eq_score_of_pair_empty hxy
          have htotal :=
            hwinDrain.target_eq_score_add_sum_flip_of_drain hfinishPair
          have htarget : s.score + 1 = s.score := by
            simp [hfrontzero, hqzero] at htotal
          have h10 : (1 : ZMod 2) = 0 := by
            calc
              1 = -s.score + (s.score + 1) := by abel
              _ = -s.score + s.score := by rw [htarget]
              _ = 0 := by abel
          exact one_ne_zero h10
      have hU3 : 3 ≤ s.untouched.card := by
        have hpos : 0 < s.untouched.card := Finset.card_pos.mpr
          (Finset.nonempty_iff_ne_empty.mpr hU0)
        omega
      cases hq : s.queue with
      | nil => exact False.elim (hqueue hq)
      | cons f q =>
        have hturn : (!s.toMove : Bool) = attacker := by
          cases hs : s.toMove <;> cases ha : attacker <;> simp_all
        have herase : ∀ x ∈ s.untouched,
            flip G (s.untouched.erase x) f = 1 := by
          intro x hx
          let so : State V := {
            untouched := s.untouched.erase x
            queue := f :: (q ++ [x])
            ko := false
            toMove := !s.toMove
            score := s.score }
          let soc : State V := {
            untouched := s.untouched.erase x
            queue := q ++ [x]
            ko := false
            toMove := s.toMove
            score := s.score + flip G (s.untouched.erase x) f }
          have hopen : step G s (.open x) = some so := by
            simp [step, so, hq, hx]
          have hclose : step G so .close = some soc := by
            simp [step, so, soc]
          have hwino : CloseFirstWins G attacker (s.score + 1) so :=
            hwin.answer_child hdefender hopen
          have hwinc : CloseFirstWins G attacker (s.score + 1) soc :=
            hwino.close_child (by change (!s.toMove : Bool) = attacker; exact hturn) hclose
          have hne : flip G (s.untouched.erase x) f ≠ 0 := by
            intro hzero
            have htarget : s.score + 1 = soc.score + 1 := by
              simp [soc, hzero]
            rw [htarget] at hwinc
            exact ih soc (lt_trans (rank_step_lt hclose) (rank_step_lt hopen))
              (coherent_step (coherent_step hcoherent hopen) hclose)
              (by change s.toMove ≠ attacker; exact hdefender)
              (by simp [soc]) (by rfl) hwinc
          exact zmod2_eq_one_of_ne_zero _ hne
        obtain ⟨hflipf, hfuniv⟩ :=
          flip_zero_and_adj_of_all_erase_flip_one
            (Finset.nonempty_iff_ne_empty.mpr hU0) herase
        cases q with
        | nil =>
          let sc : State V := {
            untouched := s.untouched
            queue := []
            ko := false
            toMove := !s.toMove
            score := s.score }
          have hclosef : step G s .close = some sc := by
            simp [step, sc, hq, hko, hflipf]
          have hwinc : CloseFirstWins G attacker (s.score + 1) sc :=
            hwin.answer_child hdefender hclosef
          have hattacker : sc.toMove = attacker := by
            change (!s.toMove : Bool) = attacker
            exact hturn
          cases hwinc with
          | terminal _ hterminal _ =>
              exact hU0 hterminal.1
          | answer _ hnotattacker _ _ =>
              exact False.elim (hnotattacker hattacker)
          | choose _ _ m sz hstep _ hwinsz =>
              cases m with
              | close => simp [step, sc] at hstep
              | pass => simp [step, sc, hU0] at hstep
              | «open» z =>
                have hz : z ∈ s.untouched := by
                  simp only [step] at hstep
                  split at hstep
                  · assumption
                  · contradiction
                let sz' : State V := {
                  untouched := s.untouched.erase z
                  queue := [z]
                  ko := true
                  toMove := s.toMove
                  score := s.score }
                have hsz : sz = sz' := by
                  simp only [step] at hstep
                  split at hstep
                  · cases hstep
                    simp [sc, sz']
                  · contradiction
                rw [hsz] at hwinsz
                have hopenz : step G sc (.open z) = some sz' := by
                  simp [step, sc, sz', hz]
                have hpunctured : (s.untouched.erase z).Nonempty := by
                  rw [Finset.nonempty_iff_ne_empty]
                  intro hempty
                  have hcard : s.untouched.card = 1 := by
                    have := Finset.card_erase_add_one hz
                    simp [hempty] at this
                    omega
                  exact hU1 hcard
                have hnested : ∀ y ∈ s.untouched.erase z,
                    flip G ((s.untouched.erase z).erase y) z = 1 := by
                  intro y hy
                  let szy : State V := {
                    untouched := (s.untouched.erase z).erase y
                    queue := [z, y]
                    ko := false
                    toMove := !s.toMove
                    score := s.score }
                  let szyc : State V := {
                    untouched := (s.untouched.erase z).erase y
                    queue := [y]
                    ko := false
                    toMove := s.toMove
                    score := s.score +
                      flip G ((s.untouched.erase z).erase y) z }
                  have hopeny : step G sz' (.open y) = some szy := by
                    simp [step, sz', szy, hy]
                  have hwinszy : CloseFirstWins G attacker (s.score + 1) szy :=
                    hwinsz.answer_child (by
                      change s.toMove ≠ attacker
                      exact hdefender) hopeny
                  have hclosez : step G szy .close = some szyc := by
                    simp [step, szy, szyc]
                  have hwinszyc : CloseFirstWins G attacker (s.score + 1) szyc :=
                    hwinszy.close_child (by
                      change (!s.toMove : Bool) = attacker
                      exact hturn) hclosez
                  have hne : flip G ((s.untouched.erase z).erase y) z ≠ 0 := by
                    intro hzero
                    have htarget : s.score + 1 = szyc.score + 1 := by
                      simp [szyc, hzero]
                    rw [htarget] at hwinszyc
                    exact ih szyc
                      (lt_trans (rank_step_lt hclosez)
                        (lt_trans (rank_step_lt hopeny)
                          (lt_trans (rank_step_lt hopenz)
                            (rank_step_lt hclosef))))
                      (coherent_step
                        (coherent_step
                          (coherent_step
                            (coherent_step hcoherent hclosef) hopenz) hopeny)
                        hclosez)
                      (by change s.toMove ≠ attacker; exact hdefender)
                      (by simp [szyc]) (by rfl) hwinszyc
                  exact zmod2_eq_one_of_ne_zero _ hne
                exact not_all_nested_erase_flips_one hz hpunctured herase hnested
        | cons g qtail =>
          have hdouble : ∀ x ∈ s.untouched, ∀ y ∈ s.untouched, x ≠ y →
              flip G ((s.untouched.erase x).erase y) g = 0 := by
            intro x hx y hy hxy
            let so : State V := {
              untouched := s.untouched.erase x
              queue := f :: g :: (qtail ++ [x])
              ko := false
              toMove := !s.toMove
              score := s.score }
            let sof : State V := {
              untouched := s.untouched.erase x
              queue := g :: (qtail ++ [x])
              ko := false
              toMove := s.toMove
              score := s.score + 1 }
            let sofy : State V := {
              untouched := (s.untouched.erase x).erase y
              queue := g :: (qtail ++ [x, y])
              ko := false
              toMove := !s.toMove
              score := s.score + 1 }
            let sofyc : State V := {
              untouched := (s.untouched.erase x).erase y
              queue := qtail ++ [x, y]
              ko := false
              toMove := s.toMove
              score := s.score + 1 +
                flip G ((s.untouched.erase x).erase y) g }
            have hopenx : step G s (.open x) = some so := by
              simp [step, so, hq, hx]
            have hclosef' : step G so .close = some sof := by
              simp [step, so, sof, herase x hx]
            have hyerase : y ∈ s.untouched.erase x :=
              Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
            have hopeny : step G sof (.open y) = some sofy := by
              simp [step, sof, sofy, hyerase, List.append_assoc]
            have hcloseg : step G sofy .close = some sofyc := by
              simp [step, sofy, sofyc]
            have hwino := hwin.answer_child hdefender hopenx
            have hwinof := hwino.close_child (by
              change (!s.toMove : Bool) = attacker
              exact hturn) hclosef'
            have hwinofy := hwinof.answer_child hdefender hopeny
            have hwinofyc := hwinofy.close_child (by
              change (!s.toMove : Bool) = attacker
              exact hturn) hcloseg
            have hneone : flip G ((s.untouched.erase x).erase y) g ≠ 1 := by
              intro hone
              have htarget : s.score + 1 = sofyc.score + 1 := by
                simp only [sofyc, hone]
                abel
              rw [htarget] at hwinofyc
              exact ih sofyc
                (lt_trans (rank_step_lt hcloseg)
                  (lt_trans (rank_step_lt hopeny)
                    (lt_trans (rank_step_lt hclosef')
                      (rank_step_lt hopenx))))
                (coherent_step
                  (coherent_step
                    (coherent_step
                      (coherent_step hcoherent hopenx) hclosef') hopeny)
                  hcloseg)
                hdefender (by simp [sofyc]) (by rfl) hwinofyc
            exact zmod2_eq_zero_of_ne_one _ hneone
          obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < s.untouched.card)
          obtain ⟨y, hy, hxy⟩ : ∃ y ∈ s.untouched, y ≠ x := by
            by_contra hnone
            push Not at hnone
            have hsub : s.untouched ⊆ {x} := by
              intro z hz
              simp only [Finset.mem_singleton]
              exact hnone z hz
            have := Finset.card_le_card hsub
            simp at this
            omega
          obtain ⟨z, hz, hzx, hzy⟩ :
              ∃ z ∈ s.untouched, z ≠ x ∧ z ≠ y := by
            by_contra hnone
            push Not at hnone
            have hsub : s.untouched ⊆ {x, y} := by
              intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton]
              by_cases hwx : w = x
              · exact Or.inl hwx
              · exact Or.inr (hnone w hw hwx)
            have := Finset.card_le_card hsub
            have hcardpair : ({x, y} : Finset V).card = 2 :=
              Finset.card_eq_two.mpr ⟨x, y, Ne.symm hxy, rfl⟩
            rw [hcardpair] at this
            omega
          have hflipg : flip G s.untouched g = 0 :=
            flip_zero_of_three_double_erases hx hy hz
              (Ne.symm hxy) (Ne.symm hzx) (Ne.symm hzy)
              hdouble
          let sf : State V := {
            untouched := s.untouched
            queue := g :: qtail
            ko := false
            toMove := !s.toMove
            score := s.score }
          let sfg : State V := {
            untouched := s.untouched
            queue := qtail
            ko := false
            toMove := s.toMove
            score := s.score }
          have hclosef : step G s .close = some sf := by
            simp [step, sf, hq, hko, hflipf]
          have hcloseg : step G sf .close = some sfg := by
            simp [step, sf, sfg, hflipg]
          have hwinf := hwin.answer_child hdefender hclosef
          have hwinfg := hwinf.close_child (by
            change (!s.toMove : Bool) = attacker
            exact hturn) hcloseg
          cases qtail with
          | cons a rest =>
              exact ih sfg
                (lt_trans (rank_step_lt hcloseg) (rank_step_lt hclosef))
                (coherent_step (coherent_step hcoherent hclosef) hcloseg)
                hdefender (by simp [sfg]) (by rfl) (by
                  simpa [sfg] using hwinfg)
          | nil =>
              let sx : State V := {
                untouched := s.untouched.erase x
                queue := [x]
                ko := true
                toMove := !s.toMove
                score := s.score }
              have hopenx : step G sfg (.open x) = some sx := by
                simp [step, sfg, sx, hx]
              have hwinx : CloseFirstWins G attacker (s.score + 1) sx :=
                hwinfg.answer_child hdefender hopenx
              have hremain : s.untouched.erase x ≠ ∅ := by
                intro hempty
                have hcard := Finset.card_erase_add_one hx
                simp [hempty] at hcard
                omega
              have hattackerx : sx.toMove = attacker := by
                change (!s.toMove : Bool) = attacker
                exact hturn
              cases hwinx with
              | terminal _ hterminal _ =>
                  exact List.cons_ne_nil x [] hterminal.2
              | answer _ hnotattacker _ _ =>
                  exact False.elim (hnotattacker hattackerx)
              | choose _ _ m sxy0 hstep _ hwinsxy =>
                  cases m with
                  | close => simp [step, sx] at hstep
                  | pass => simp [step, sx, hremain] at hstep
                  | «open» y =>
                    have hyerase : y ∈ s.untouched.erase x := by
                      simp only [step] at hstep
                      split at hstep
                      · assumption
                      · contradiction
                    let sxy : State V := {
                      untouched := (s.untouched.erase x).erase y
                      queue := [x, y]
                      ko := false
                      toMove := s.toMove
                      score := s.score }
                    have hsxy : sxy0 = sxy := by
                      simp only [step] at hstep
                      split at hstep
                      · cases hstep
                        simp [sx, sxy]
                      · contradiction
                    rw [hsxy] at hwinsxy
                    have hopeny : step G sx (.open y) = some sxy := by
                      simp [step, sx, sxy, hyerase]
                    exact ih sxy
                      (lt_trans (rank_step_lt hopeny)
                        (lt_trans (rank_step_lt hopenx)
                          (lt_trans (rank_step_lt hcloseg)
                            (rank_step_lt hclosef))))
                      (coherent_step
                        (coherent_step
                          (coherent_step
                            (coherent_step hcoherent hclosef) hcloseg) hopenx)
                        hopeny)
                      hdefender (by simp [sxy]) (by rfl) hwinsxy

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

/-! ### Strategy-tree-relative charged-close extraction

The local score-sheet transport lemmas above do not by themselves contradict
determinacy: the same physical player can sometimes force either target from
one public state.  The constructor-sensitive object below follows a displayed
odd proof.  A rank-minimal zero-sheet node in that relation has a
rigid operational form: the odd-seeking player selects an odd CLOSE, and the
opposite score sheet of its child admits a strategy all of whose moves are
score-neutral. -/

/-- Constructor-sensitive membership under the displayed `OddWins` proof.
At a `choose` constructor only its displayed child belongs; at an `answer`
constructor every legal child belongs.  Since `OddWins` lives in `Prop`, proof
irrelevance can identify different displayed trees at one state; use the
Type-valued `OddStrategy` interface when fixed-policy identity is essential. -/
inductive InOddStrategy {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (seat : Bool) :
    {s : State V} → OddWins G seat s → State V → Prop
  | root {s : State V} (h : OddWins G seat s) :
      InOddStrategy G seat h s
  | choose {s s' t : State V} {hseat : s.toMove ≠ seat}
      {m : Move V} {hstep : step G s m = some s'}
      {hchild : OddWins G seat s'}
      (ht : InOddStrategy G seat hchild t) :
      InOddStrategy G seat
        (OddWins.choose s hseat m s' hstep hchild) t
  | answer {s s' t : State V} {hseat : s.toMove = seat}
      {hasMove : ∃ m u, step G s m = some u}
      {hchildren : ∀ m u, step G s m = some u → OddWins G seat u}
      {m : Move V} {hstep : step G s m = some s'}
      (ht : InOddStrategy G seat (hchildren m s' hstep) t) :
      InOddStrategy G seat
        (OddWins.answer s hseat hasMove hchildren) t

/-- Strategy-tree membership composes down nested odd subtrees. -/
theorem InOddStrategy.trans
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {seat : Bool} {r s t : State V}
    {hr : OddWins G seat r} {hs : OddWins G seat s}
    (hrs : InOddStrategy G seat hr s)
    (hst : InOddStrategy G seat hs t) :
    InOddStrategy G seat hr t := by
  induction hrs with
  | root => simpa using hst
  | @choose s0 s1 t0 hseat m hstep hchild ht ih =>
      exact InOddStrategy.choose (hseat := hseat) (m := m)
        (hstep := hstep) (ih hst)
  | @answer s0 s1 t0 hseat hasMove hchildren m hstep ht ih =>
      exact InOddStrategy.answer (hseat := hseat) (hasMove := hasMove)
        (hchildren := hchildren) (m := m) (hstep := hstep) (ih hst)

/-- Every node in an odd strategy tree carries the corresponding odd
sub-strategy. -/
theorem InOddStrategy.oddWins
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {seat : Bool} {s t : State V}
    {h : OddWins G seat s} (ht : InOddStrategy G seat h t) :
    OddWins G seat t := by
  induction ht with
  | root => assumption
  | choose _ ih => exact ih
  | answer _ ih => exact ih

/-- A strategy which forces terminal score zero without changing the score
on any move in its explicit strategy tree. -/
inductive TreeNeutralWins {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (player : Bool) : State V → Prop
  | terminal (s : State V) (hterminal : Terminal s) (hscore : s.score = 0) :
      TreeNeutralWins G player s
  | choose (s : State V) (hplayer : s.toMove = player)
      (m : Move V) (s' : State V) (hstep : step G s m = some s')
      (hneutral : s'.score = s.score) (hwin : TreeNeutralWins G player s') :
      TreeNeutralWins G player s
  | answer (s : State V) (hplayer : s.toMove ≠ player)
      (hasMove : ∃ m s', step G s m = some s')
      (hneutral : ∀ m s', step G s m = some s' → s'.score = s.score)
      (hwin : ∀ m s', step G s m = some s' →
        TreeNeutralWins G player s') :
      TreeNeutralWins G player s

/-- Forgetting the transition-by-transition neutrality certificate leaves an
ordinary strategy forcing terminal score zero. -/
theorem TreeNeutralWins.toEvenWins
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {player : Bool} {s : State V}
    (h : TreeNeutralWins G player s) : EvenWins G player s := by
  induction h with
  | terminal s hterminal hscore =>
      exact EvenWins.terminal s hterminal hscore
  | choose s hplayer m s' hstep _ _ ih =>
      exact EvenWins.choose s hplayer m s' hstep ih
  | answer s hplayer hasMove _ _ ih =>
      exact EvenWins.answer s hplayer hasMove ih

/-- At an opponent-controlled node of a neutral tree, every legal move both
preserves the score and leads to another neutral subtree. -/
theorem TreeNeutralWins.answer_child
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {player : Bool} {s s' : State V}
    (h : TreeNeutralWins G player s) (hturn : s.toMove ≠ player)
    {m : Move V} (hstep : step G s m = some s') :
    s'.score = s.score ∧ TreeNeutralWins G player s' := by
  cases h with
  | terminal _ hterminal _ =>
      exact False.elim (terminal_no_step hterminal ⟨m, s', hstep⟩)
  | choose _ hplayer _ _ _ _ _ => exact False.elim (hturn hplayer)
  | answer _ _ _ hneutral hwin => exact ⟨hneutral m s' hstep, hwin m s' hstep⟩

/-- If every node of one explicit odd strategy subtree is already on score
sheet one, translating the subtree by one produces a completely score-neutral
strategy for the same physical player.  This is the direct interface used
when a separate monotone measure (for example the number of live real
vertices) proves that no score-zero descendant can occur. -/
theorem oddStrategy_one_subtree_translates_neutral
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (h : OddWins G seat s)
    (hone : ∀ {t : State V}, InOddStrategy G seat h t → t.score = 1) :
    TreeNeutralWins G (!seat) (scoreTranslate 1 s) := by
  induction h with
  | terminal s hterminal _ =>
      have hs1 : s.score = 1 := hone (InOddStrategy.root _)
      refine TreeNeutralWins.terminal (scoreTranslate 1 s) ?_ ?_
      · simpa [Terminal, scoreTranslate] using hterminal
      · simp [scoreTranslate, hs1, CharTwo.add_self_eq_zero]
  | choose s hseat m s' hstep hchild ih =>
      have hs1 : s.score = 1 := hone (InOddStrategy.root _)
      have hlocal : InOddStrategy G seat
          (OddWins.choose s hseat m s' hstep hchild) s' :=
        InOddStrategy.choose (hseat := hseat) (m := m) (hstep := hstep)
          (InOddStrategy.root hchild)
      have hs'1 : s'.score = 1 := hone hlocal
      have hone' : ∀ {t : State V}, InOddStrategy G seat hchild t →
          t.score = 1 := by
        intro t ht
        exact hone (hlocal.trans ht)
      refine TreeNeutralWins.choose (scoreTranslate 1 s) ?_ m
        (scoreTranslate 1 s') ?_ ?_ (ih hone')
      · simpa [scoreTranslate] using Bool.eq_not_iff.mpr hseat
      · rw [step_scoreTranslate, hstep]
        simp
      · simp [scoreTranslate, hs1, hs'1, CharTwo.add_self_eq_zero]
  | answer s hseat hasMove hchildren ih =>
      have hs1 : s.score = 1 := hone (InOddStrategy.root _)
      refine TreeNeutralWins.answer (scoreTranslate 1 s) ?_ ?_ ?_ ?_
      · simpa [scoreTranslate] using Bool.ne_not.mpr hseat
      · obtain ⟨m, s', hstep⟩ := hasMove
        exact ⟨m, scoreTranslate 1 s', by
          rw [step_scoreTranslate, hstep]
          simp⟩
      · intro m t htranslated
        obtain ⟨s', hstep, rfl⟩ :=
          (step_scoreTranslate_eq_some_iff G 1 s t m).mp htranslated
        have hlocal : InOddStrategy G seat
            (OddWins.answer s hseat hasMove hchildren) s' :=
          InOddStrategy.answer (hseat := hseat) (hasMove := hasMove)
            (hchildren := hchildren) (m := m) (hstep := hstep)
            (InOddStrategy.root (hchildren m s' hstep))
        have hs'1 : s'.score = 1 := hone hlocal
        simp [scoreTranslate, hs1, hs'1, CharTwo.add_self_eq_zero]
      · intro m t htranslated
        obtain ⟨s', hstep, rfl⟩ :=
          (step_scoreTranslate_eq_some_iff G 1 s t m).mp htranslated
        have hlocal : InOddStrategy G seat
            (OddWins.answer s hseat hasMove hchildren) s' :=
          InOddStrategy.answer (hseat := hseat) (hasMove := hasMove)
            (hchildren := hchildren) (m := m) (hstep := hstep)
            (InOddStrategy.root (hchildren m s' hstep))
        have hone' : ∀ {u : State V},
            InOddStrategy G seat (hchildren m s' hstep) u → u.score = 1 := by
          intro u hu
          exact hone (hlocal.trans hu)
        exact ih m s' hstep hone'

/-- If every proper node of an odd strategy subtree stays on score sheet one,
then translating its root by one produces a score-neutral strategy for the
same physical player.  The hypothesis is relative to the original strategy
tree, not to arbitrary game states. -/
theorem oddStrategy_subtree_one_translates_neutral
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {seat : Bool} {root s : State V}
    {hroot : OddWins G seat root} (h : OddWins G seat s)
    (hmem : InOddStrategy G seat hroot s)
    (hrank : rank s < rank root)
    (hnozero : ∀ {t : State V}, InOddStrategy G seat hroot t →
      rank t < rank root → t.score ≠ 0) :
    TreeNeutralWins G (!seat) (scoreTranslate 1 s) := by
  induction h with
  | terminal s hterminal hscore =>
      have hs1 : s.score = 1 :=
        zmod2_eq_one_of_ne_zero _ (hnozero hmem hrank)
      refine TreeNeutralWins.terminal (scoreTranslate 1 s) ?_ ?_
      · simpa [Terminal, scoreTranslate] using hterminal
      · simp [scoreTranslate, hs1, CharTwo.add_self_eq_zero]
  | choose s hseat m s' hstep hchild ih =>
      have hlocal : InOddStrategy G seat
          (OddWins.choose s hseat m s' hstep hchild) s' :=
        InOddStrategy.choose (hseat := hseat) (m := m) (hstep := hstep)
          (InOddStrategy.root hchild)
      have hmem' : InOddStrategy G seat hroot s' := hmem.trans hlocal
      have hrank' : rank s' < rank root :=
        lt_trans (rank_step_lt hstep) hrank
      have hs1 : s.score = 1 :=
        zmod2_eq_one_of_ne_zero _ (hnozero hmem hrank)
      have hs'1 : s'.score = 1 :=
        zmod2_eq_one_of_ne_zero _ (hnozero hmem' hrank')
      refine TreeNeutralWins.choose (scoreTranslate 1 s) ?_ m
        (scoreTranslate 1 s') ?_ ?_ (ih hmem' hrank')
      · simpa [scoreTranslate] using Bool.eq_not_iff.mpr hseat
      · rw [step_scoreTranslate, hstep]
        simp
      · simp [scoreTranslate, hs1, hs'1, CharTwo.add_self_eq_zero]
  | answer s hseat hasMove hchildren ih =>
      have hs1 : s.score = 1 :=
        zmod2_eq_one_of_ne_zero _ (hnozero hmem hrank)
      refine TreeNeutralWins.answer (scoreTranslate 1 s) ?_ ?_ ?_ ?_
      · simpa [scoreTranslate] using Bool.ne_not.mpr hseat
      · obtain ⟨m, s', hstep⟩ := hasMove
        exact ⟨m, scoreTranslate 1 s', by
          rw [step_scoreTranslate, hstep]
          simp⟩
      · intro m t htranslated
        obtain ⟨s', hstep, rfl⟩ :=
          (step_scoreTranslate_eq_some_iff G 1 s t m).mp htranslated
        have hlocal : InOddStrategy G seat
            (OddWins.answer s hseat hasMove hchildren) s' :=
          InOddStrategy.answer (hseat := hseat) (hasMove := hasMove)
            (hchildren := hchildren) (m := m) (hstep := hstep)
            (InOddStrategy.root (hchildren m s' hstep))
        have hmem' : InOddStrategy G seat hroot s' := hmem.trans hlocal
        have hrank' : rank s' < rank root :=
          lt_trans (rank_step_lt hstep) hrank
        have hs'1 : s'.score = 1 :=
          zmod2_eq_one_of_ne_zero _ (hnozero hmem' hrank')
        simp [scoreTranslate, hs1, hs'1, CharTwo.add_self_eq_zero]
      · intro m t htranslated
        obtain ⟨s', hstep, rfl⟩ :=
          (step_scoreTranslate_eq_some_iff G 1 s t m).mp htranslated
        have hlocal : InOddStrategy G seat
            (OddWins.answer s hseat hasMove hchildren) s' :=
          InOddStrategy.answer (hseat := hseat) (hasMove := hasMove)
            (hchildren := hchildren) (m := m) (hstep := hstep)
            (InOddStrategy.root (hchildren m s' hstep))
        have hmem' : InOddStrategy G seat hroot s' := hmem.trans hlocal
        have hrank' : rank s' < rank root :=
          lt_trans (rank_step_lt hstep) hrank
        exact ih m s' hstep hmem' hrank'

/-- A rank-minimal zero-sheet node inside one explicit odd strategy tree is
controlled by the odd-seeking player, whose selected move is an odd FIFO
CLOSE.  The selected child's opposite sheet has a fully neutral continuation.
This is the strategy-tree-relative replacement for global-state minimality. -/
theorem minimalOddStrategy_zeroNode_close_neutral
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (h : OddWins G seat s) (hs0 : s.score = 0)
    (hminimal : ∀ {t : State V}, InOddStrategy G seat h t →
      rank t < rank s → t.score ≠ 0) :
    s.toMove = !seat ∧
      ∃ f q s', s.queue = f :: q ∧ s.ko = false ∧
        step G s .close = some s' ∧ flip G s.untouched f = 1 ∧
          TreeNeutralWins G (!seat) (scoreTranslate 1 s') := by
  cases h with
  | terminal _ _ hscore => exact False.elim (hscore hs0)
  | choose _ hseat m s' hstep hchild =>
      have hplayer : s.toMove = !seat := Bool.eq_not_iff.mpr hseat
      have hmem : InOddStrategy G seat
          (OddWins.choose s hseat m s' hstep hchild) s' :=
        InOddStrategy.choose (hseat := hseat) (m := m) (hstep := hstep)
          (InOddStrategy.root hchild)
      have hrank : rank s' < rank s := rank_step_lt hstep
      have hs'1 : s'.score = 1 :=
        zmod2_eq_one_of_ne_zero _ (hminimal hmem hrank)
      have hneutral : TreeNeutralWins G (!seat) (scoreTranslate 1 s') :=
        oddStrategy_subtree_one_translates_neutral hchild hmem hrank hminimal
      have hm : m = .close := by
        cases m with
        | «open» v =>
            have hscore := open_score hstep
            rw [hs0] at hscore
            exact False.elim (one_ne_zero (hs'1.symm.trans hscore))
        | close => rfl
        | pass =>
            have hscore := pass_score hstep
            rw [hs0] at hscore
            exact False.elim (one_ne_zero (hs'1.symm.trans hscore))
      subst m
      obtain ⟨f, q, hqueue, hscore⟩ := close_score hstep
      have hko : s.ko = false := by
        cases hk : s.ko with
        | false => rfl
        | true => simp [step, hqueue, hk] at hstep
      have hflip : flip G s.untouched f = 1 := by
        rw [hs0, zero_add] at hscore
        exact hscore.symm.trans hs'1
      exact ⟨hplayer, f, q, s', hqueue, hko, hstep, hflip, hneutral⟩
  | answer _ hseat hasMove hchildren =>
      exfalso
      by_cases hU : s.untouched = ∅
      · obtain ⟨m, s', hstep⟩ := hasMove
        have hsome : ∃ m t, step G s m = some t := ⟨m, s', hstep⟩
        have hmem : InOddStrategy G seat
            (OddWins.answer s hseat hsome hchildren) s' :=
          InOddStrategy.answer (hseat := hseat) (hasMove := hsome)
            (hchildren := hchildren) (m := m) (hstep := hstep)
            (InOddStrategy.root (hchildren m s' hstep))
        have hrank : rank s' < rank s := rank_step_lt hstep
        have hs'0 : s'.score = 0 := by
          rw [step_score_eq_of_untouched_empty hU hstep, hs0]
        exact hminimal hmem hrank hs'0
      · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hU
        let s' : State V := {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove
          score := s.score }
        have hstep : step G s (.open v) = some s' := by
          simp [step, s', hv]
        have hmem : InOddStrategy G seat
            (OddWins.answer s hseat hasMove hchildren) s' :=
          InOddStrategy.answer (hseat := hseat) (hasMove := hasMove)
            (hchildren := hchildren) (m := .open v) (hstep := hstep)
            (InOddStrategy.root (hchildren (.open v) s' hstep))
        have hrank : rank s' < rank s := rank_step_lt hstep
        have hs'0 : s'.score = 0 := by simp [s', hs0]
        exact hminimal hmem hrank hs'0

/-- Every zero-sheet odd strategy contains a rank-minimal zero-sheet node.
At that node the preceding theorem gives the selected charged CLOSE followed
by a neutral translated tail.  Minimality is taken only over nodes of the
given strategy tree. -/
theorem oddStrategy_extract_minimalCloseNeutral
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    (hroot : OddWins G seat root) (hroot0 : root.score = 0) :
    ∃ s, InOddStrategy G seat hroot s ∧ s.score = 0 ∧
      s.toMove = !seat ∧
      ∃ f q s', s.queue = f :: q ∧ s.ko = false ∧
        step G s .close = some s' ∧ flip G s.untouched f = 1 ∧
          TreeNeutralWins G (!seat) (scoreTranslate 1 s') := by
  classical
  let P : Nat → Prop := fun n ↦ ∃ s,
    InOddStrategy G seat hroot s ∧ s.score = 0 ∧ rank s = n
  have hP : ∃ n, P n := by
    exact ⟨rank root, root, InOddStrategy.root hroot, hroot0, rfl⟩
  let n := Nat.find hP
  obtain ⟨s, hmem, hs0, hrank⟩ := Nat.find_spec hP
  have h : OddWins G seat s := hmem.oddWins
  have hminimal : ∀ {t : State V}, InOddStrategy G seat h t →
      rank t < rank s → t.score ≠ 0 := by
    intro t hinner hlt ht0
    have hglobal : InOddStrategy G seat hroot t := hmem.trans hinner
    have hPt : P (rank t) := ⟨t, hglobal, ht0, rfl⟩
    have hnle : n ≤ rank t := Nat.find_min' hP hPt
    have hsle : rank s ≤ rank t := by simpa [n, hrank] using hnle
    exact (Nat.not_lt_of_ge hsle) hlt
  obtain ⟨hturn, f, q, s', hqueue, hko, hstep, hflip, hneutral⟩ :=
    minimalOddStrategy_zeroNode_close_neutral h hs0 hminimal
  exact ⟨s, hmem, hs0, hturn, f, q, s', hqueue, hko, hstep,
    hflip, hneutral⟩

/-- At an opponent-controlled node of a neutral strategy, every legal CLOSE
has zero charge.  This is the local bridge from neutral tails to Eulerian
degree parity. -/
theorem TreeNeutralWins.opponent_close_flip_zero
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {player : Bool} {s : State V} {f : V} {q : List V}
    (h : TreeNeutralWins G player s) (hturn : s.toMove ≠ player)
    (hqueue : s.queue = f :: q) (hko : s.ko = false) :
    flip G s.untouched f = 0 := by
  let sc : State V := {
    untouched := s.untouched
    queue := q
    ko := false
    toMove := !s.toMove
    score := s.score + flip G s.untouched f }
  have hstep : step G s .close = some sc := by
    simp [step, hqueue, hko, sc]
  cases h with
  | terminal _ hterminal _ =>
      exact False.elim (terminal_no_step hterminal ⟨.close, sc, hstep⟩)
  | choose _ hplayer _ _ _ _ _ => exact False.elim (hturn hplayer)
  | answer _ _ _ hneutral _ =>
      have heq := hneutral .close sc hstep
      have hadd : s.score + flip G s.untouched f = s.score + 0 := by
        simpa [sc] using heq
      exact add_left_cancel hadd

/-- A neutral tail after every puncture of `U`, with the puncturing vertex as
the next opponent-controlled singleton front, forces even degree at every
vertex of the induced graph on `U`. -/
theorem treeNeutral_singletonTails_eulerian
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (player : Bool) (U : Finset V)
    (htails : ∀ w ∈ U,
      TreeNeutralWins G player {
        untouched := U.erase w
        queue := [w]
        ko := false
        toMove := !player
        score := 0 }) :
    ∀ w ∈ U, flip G (U.erase w) w = 0 := by
  intro w hw
  exact (htails w hw).opponent_close_flip_zero (by simp) rfl rfl

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
