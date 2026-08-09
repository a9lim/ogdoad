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
