import Ogdoad.FifoNormalization

/-!
# The queue-cut potential does not stay zero under a root strategy

The scalar potential

`potential G s = s.score + queueCut G s.untouched s.queue`

is conserved by CLOSE and PASS and changes by the live degree of an OPEN.
It is therefore natural to try to keep it zero after every defender move.
This file records a smallest causal obstruction to that stronger invariant.

On the real path `3--0--1--2` with isolated dummy `4`, the attacker opens
`0`.  The only zero-potential replies are `OPEN 1` and `OPEN 4`.  Whichever
one is chosen, the attacker opens the other; the only next zero-potential
reply is `CLOSE 0`.  The resulting state has score and queue cut both one,
and `2` is the unique odd-live-degree untouched vertex.  After `OPEN 2`,
every legal reply still has potential one.

This is an obstruction only to the pointwise potential-zero strategy, not to
the FIFO linking conjecture: a winning strategy may carry controlled
potential debt and cancel it later.
-/

namespace Ogdoad.Fifo

noncomputable section

/-- The real path `3--0--1--2` together with isolated label `4`. -/
def qPotentialWallGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun x y ↦
    (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 0 ∧ y = 3)

theorem qPotentialWallGraph_dummy : IsDummy qPotentialWallGraph 4 := by
  intro v
  simp [qPotentialWallGraph, SimpleGraph.fromRel_adj]

@[simp] theorem qPotentialWallGraph_adj (x y : Fin 5) :
    qPotentialWallGraph.Adj x y ↔
      ((x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 0 ∧ y = 3)) ∨
      ((y = 0 ∧ x = 1) ∨ (y = 1 ∧ x = 2) ∨ (y = 0 ∧ x = 3)) := by
  simp [qPotentialWallGraph, SimpleGraph.fromRel_adj]
  omega

@[simp] theorem qWall_flip_pair_zero :
    flip qPotentialWallGraph {2, 3} 0 = 1 := by
  rw [flip_pair (by decide)]
  simp [adjacencyBit]

@[simp] theorem qWall_flip_pair_one :
    flip qPotentialWallGraph {2, 3} 1 = 1 := by
  rw [flip_pair (by decide)]
  simp [adjacencyBit]

@[simp] theorem qWall_flip_pair_four :
    flip qPotentialWallGraph {2, 3} 4 = 0 := by
  rw [flip_pair (by decide)]
  simp [adjacencyBit]

/-- State after the first attacker move `OPEN 0`. -/
def qWallAfterOpenZero : State (Fin 5) where
  untouched := {1, 2, 3, 4}
  queue := [0]
  ko := true
  toMove := true
  score := 0

/-- The branch `OPEN 0; OPEN 1; OPEN 4`. -/
def qWallBeforeCloseA : State (Fin 5) where
  untouched := {2, 3}
  queue := [0, 1, 4]
  ko := false
  toMove := true
  score := 0

/-- The branch `OPEN 0; OPEN 4; OPEN 1`. -/
def qWallBeforeCloseB : State (Fin 5) where
  untouched := {2, 3}
  queue := [0, 4, 1]
  ko := false
  toMove := true
  score := 0

/-- The common public wall after closing front `0`, in the first order. -/
def qWallParentA : State (Fin 5) where
  untouched := {2, 3}
  queue := [1, 4]
  ko := false
  toMove := false
  score := 1

/-- The same wall with the two neutral tail entries exchanged. -/
def qWallParentB : State (Fin 5) where
  untouched := {2, 3}
  queue := [4, 1]
  ko := false
  toMove := false
  score := 1

/-- The first wall after the attacker opens its unique odd-degree vertex. -/
def qWallAfterOddOpenA : State (Fin 5) where
  untouched := {3}
  queue := [1, 4, 2]
  ko := false
  toMove := true
  score := 1

/-- The exchanged-tail version of the post-OPEN wall. -/
def qWallAfterOddOpenB : State (Fin 5) where
  untouched := {3}
  queue := [4, 1, 2]
  ko := false
  toMove := true
  score := 1

theorem qWall_first_open :
    step qPotentialWallGraph (initial (V := Fin 5)) (.open 0) =
      some qWallAfterOpenZero := by
  have hU : (Finset.univ.erase 0 : Finset (Fin 5)) = {1, 2, 3, 4} := by
    ext x
    fin_cases x <;> simp
  simp [step, initial, qWallAfterOpenZero, hU]

@[simp] theorem qWall_afterOpenZero_potential :
    potential qPotentialWallGraph qWallAfterOpenZero = 0 := by
  simp [potential, queueCut, qWallAfterOpenZero, flip]

theorem qWall_afterOpenZero_liveDegree_two :
    liveDegree qPotentialWallGraph qWallAfterOpenZero 2 = 1 := by
  classical
  rw [liveDegree_eq_flip_liveSet (by
    simp [WellFormed, qWallAfterOpenZero])]
  have hL : liveSet qWallAfterOpenZero = Finset.univ := by
    ext x
    fin_cases x <;> simp [liveSet, qWallAfterOpenZero]
  rw [hL]
  have hfilter :
      (Finset.univ : Finset (Fin 5)).filter
          (qPotentialWallGraph.Adj 2) = {1} := by
    ext x
    fin_cases x <;> simp
  rw [flip, hfilter]
  norm_num

theorem qWall_afterOpenZero_liveDegree_three :
    liveDegree qPotentialWallGraph qWallAfterOpenZero 3 = 1 := by
  classical
  rw [liveDegree_eq_flip_liveSet (by
    simp [WellFormed, qWallAfterOpenZero])]
  have hL : liveSet qWallAfterOpenZero = Finset.univ := by
    ext x
    fin_cases x <;> simp [liveSet, qWallAfterOpenZero]
  rw [hL]
  have hfilter :
      (Finset.univ : Finset (Fin 5)).filter
          (qPotentialWallGraph.Adj 3) = {0} := by
    ext x
    fin_cases x <;> simp
  rw [flip, hfilter]
  norm_num

/-- After `OPEN 0`, the only legal replies which leave the potential zero are
`OPEN 1` and `OPEN 4`. -/
theorem qWall_first_zero_reply
    (m : Move (Fin 5)) (t : State (Fin 5))
    (hstep : step qPotentialWallGraph qWallAfterOpenZero m = some t)
    (hzero : potential qPotentialWallGraph t = 0) :
    m = .open 1 ∨ m = .open 4 := by
  cases m with
  | «open» v =>
      have hpot := open_adds_liveDegree_to_potential hstep
      rw [hzero, qWall_afterOpenZero_potential, zero_add] at hpot
      fin_cases v
      · simp [step, qWallAfterOpenZero] at hstep
      · exact Or.inl (by simp)
      · have hpot' : 0 =
            liveDegree qPotentialWallGraph qWallAfterOpenZero 2 := by
          simpa using hpot
        rw [qWall_afterOpenZero_liveDegree_two] at hpot'
        exact False.elim (one_ne_zero hpot'.symm)
      · have hpot' : 0 =
            liveDegree qPotentialWallGraph qWallAfterOpenZero 3 := by
          simpa using hpot
        rw [qWall_afterOpenZero_liveDegree_three] at hpot'
        exact False.elim (one_ne_zero hpot'.symm)
      · exact Or.inr (by simp)
  | close => simp [step, qWallAfterOpenZero] at hstep
  | pass => simp [step, qWallAfterOpenZero] at hstep

theorem qWall_branchA_prefix :
    ∃ s,
      step qPotentialWallGraph qWallAfterOpenZero (.open 1) = some s ∧
      step qPotentialWallGraph s (.open 4) = some qWallBeforeCloseA := by
  let s : State (Fin 5) := {
    untouched := {2, 3, 4}
    queue := [0, 1]
    ko := false
    toMove := false
    score := 0 }
  refine ⟨s, ?_, ?_⟩
  · simp [step, qWallAfterOpenZero, s]
  · have hU : ({2, 3, 4} : Finset (Fin 5)).erase 4 = {2, 3} := by
      ext x
      fin_cases x <;> simp
    simp [step, qWallBeforeCloseA, s, hU]

theorem qWall_branchB_prefix :
    ∃ s,
      step qPotentialWallGraph qWallAfterOpenZero (.open 4) = some s ∧
      step qPotentialWallGraph s (.open 1) = some qWallBeforeCloseB := by
  let s : State (Fin 5) := {
    untouched := {1, 2, 3}
    queue := [0, 4]
    ko := false
    toMove := false
    score := 0 }
  refine ⟨s, ?_, ?_⟩
  · have hU : ({1, 2, 3, 4} : Finset (Fin 5)).erase 4 = {1, 2, 3} := by
      ext x
      fin_cases x <;> simp
    simp [step, qWallAfterOpenZero, s, hU]
  · simp [step, qWallBeforeCloseB, s]

@[simp] theorem qWall_beforeCloseA_potential :
    potential qPotentialWallGraph qWallBeforeCloseA = 0 := by
  simp [potential, queueCut, qWallBeforeCloseA]
  exact CharTwo.add_self_eq_zero 1

@[simp] theorem qWall_beforeCloseB_potential :
    potential qPotentialWallGraph qWallBeforeCloseB = 0 := by
  simp [potential, queueCut, qWallBeforeCloseB]
  exact CharTwo.add_self_eq_zero 1

theorem qWall_beforeCloseA_liveDegree (v : Fin 5) :
    liveDegree qPotentialWallGraph qWallBeforeCloseA v =
      liveDegree qPotentialWallGraph qWallAfterOpenZero v := by
  have hA : WellFormed qWallBeforeCloseA := by
    simp [WellFormed, qWallBeforeCloseA]
  have h0 : WellFormed qWallAfterOpenZero := by
    simp [WellFormed, qWallAfterOpenZero]
  rw [liveDegree_eq_flip_liveSet hA, liveDegree_eq_flip_liveSet h0]
  congr 1
  ext x
  fin_cases x <;> simp [liveSet, qWallBeforeCloseA, qWallAfterOpenZero]

theorem qWall_beforeCloseB_liveDegree (v : Fin 5) :
    liveDegree qPotentialWallGraph qWallBeforeCloseB v =
      liveDegree qPotentialWallGraph qWallAfterOpenZero v := by
  have hB : WellFormed qWallBeforeCloseB := by
    simp [WellFormed, qWallBeforeCloseB]
  have h0 : WellFormed qWallAfterOpenZero := by
    simp [WellFormed, qWallAfterOpenZero]
  rw [liveDegree_eq_flip_liveSet hB, liveDegree_eq_flip_liveSet h0]
  congr 1
  ext x
  fin_cases x <;> simp [liveSet, qWallBeforeCloseB, qWallAfterOpenZero]

/-- Once the first branch has opened the dummy, CLOSE is the only
potential-zero defender reply. -/
theorem qWall_beforeCloseA_only_zero
    (m : Move (Fin 5)) (t : State (Fin 5))
    (hstep : step qPotentialWallGraph qWallBeforeCloseA m = some t)
    (hzero : potential qPotentialWallGraph t = 0) :
    m = .close := by
  cases m with
  | «open» v =>
      have hpot := open_adds_liveDegree_to_potential hstep
      rw [hzero, qWall_beforeCloseA_potential, zero_add,
        qWall_beforeCloseA_liveDegree] at hpot
      fin_cases v
      · simp [step, qWallBeforeCloseA] at hstep
      · simp [step, qWallBeforeCloseA] at hstep
      · have hpot' : 0 =
            liveDegree qPotentialWallGraph qWallAfterOpenZero 2 := by
          simpa using hpot
        rw [qWall_afterOpenZero_liveDegree_two] at hpot'
        exact False.elim (one_ne_zero hpot'.symm)
      · have hpot' : 0 =
            liveDegree qPotentialWallGraph qWallAfterOpenZero 3 := by
          simpa using hpot
        rw [qWall_afterOpenZero_liveDegree_three] at hpot'
        exact False.elim (one_ne_zero hpot'.symm)
      · simp [step, qWallBeforeCloseA] at hstep
  | close => rfl
  | pass => simp [step, qWallBeforeCloseA] at hstep

/-- The exchanged opening order has the same forced zero-potential CLOSE. -/
theorem qWall_beforeCloseB_only_zero
    (m : Move (Fin 5)) (t : State (Fin 5))
    (hstep : step qPotentialWallGraph qWallBeforeCloseB m = some t)
    (hzero : potential qPotentialWallGraph t = 0) :
    m = .close := by
  cases m with
  | «open» v =>
      have hpot := open_adds_liveDegree_to_potential hstep
      rw [hzero, qWall_beforeCloseB_potential, zero_add,
        qWall_beforeCloseB_liveDegree] at hpot
      fin_cases v
      · simp [step, qWallBeforeCloseB] at hstep
      · simp [step, qWallBeforeCloseB] at hstep
      · have hpot' : 0 =
            liveDegree qPotentialWallGraph qWallAfterOpenZero 2 := by
          simpa using hpot
        rw [qWall_afterOpenZero_liveDegree_two] at hpot'
        exact False.elim (one_ne_zero hpot'.symm)
      · have hpot' : 0 =
            liveDegree qPotentialWallGraph qWallAfterOpenZero 3 := by
          simpa using hpot
        rw [qWall_afterOpenZero_liveDegree_three] at hpot'
        exact False.elim (one_ne_zero hpot'.symm)
      · simp [step, qWallBeforeCloseB] at hstep
  | close => rfl
  | pass => simp [step, qWallBeforeCloseB] at hstep

theorem qWall_closeA :
    step qPotentialWallGraph qWallBeforeCloseA .close =
      some qWallParentA := by
  simp [step, qWallBeforeCloseA, qWallParentA]

theorem qWall_closeB :
    step qPotentialWallGraph qWallBeforeCloseB .close =
      some qWallParentB := by
  simp [step, qWallBeforeCloseB, qWallParentB]

theorem qWall_parentA_potential :
    potential qPotentialWallGraph qWallParentA = 0 := by
  simp [potential, queueCut, qWallParentA]
  exact CharTwo.add_self_eq_zero 1

theorem qWall_parentB_potential :
    potential qPotentialWallGraph qWallParentB = 0 := by
  simp [potential, queueCut, qWallParentB]
  exact CharTwo.add_self_eq_zero 1

theorem qWall_parentA_unique_odd :
    liveDegree qPotentialWallGraph qWallParentA 2 = 1 ∧
      liveDegree qPotentialWallGraph qWallParentA 3 = 0 := by
  simp [liveDegree, queueCut, qWallParentA, flip_pair,
    flip_singleton_eq_adjacencyBit, adjacencyBit]

theorem qWall_parentB_unique_odd :
    liveDegree qPotentialWallGraph qWallParentB 2 = 1 ∧
      liveDegree qPotentialWallGraph qWallParentB 3 = 0 := by
  simp [liveDegree, queueCut, qWallParentB, flip_pair,
    flip_singleton_eq_adjacencyBit, adjacencyBit]

theorem qWall_odd_openA :
    step qPotentialWallGraph qWallParentA (.open 2) =
      some qWallAfterOddOpenA := by
  simp [step, qWallParentA, qWallAfterOddOpenA]

theorem qWall_odd_openB :
    step qPotentialWallGraph qWallParentB (.open 2) =
      some qWallAfterOddOpenB := by
  simp [step, qWallParentB, qWallAfterOddOpenB]

theorem qWall_afterOddOpenA_potential :
    potential qPotentialWallGraph qWallAfterOddOpenA = 1 := by
  simp [potential, queueCut, qWallAfterOddOpenA,
    flip_singleton_eq_adjacencyBit, adjacencyBit]

theorem qWall_afterOddOpenB_potential :
    potential qPotentialWallGraph qWallAfterOddOpenB = 1 := by
  simp [potential, queueCut, qWallAfterOddOpenB,
    flip_singleton_eq_adjacencyBit, adjacencyBit]

/-- At the first post-OPEN wall, neither legal move (`OPEN 3` or `CLOSE 1`)
repairs the potential. -/
theorem qWall_afterOddOpenA_no_zero_reply
    (m : Move (Fin 5)) (t : State (Fin 5))
    (hstep : step qPotentialWallGraph qWallAfterOddOpenA m = some t) :
    potential qPotentialWallGraph t = 1 := by
  cases m with
  | «open» v =>
      fin_cases v <;> simp [step, qWallAfterOddOpenA] at hstep
      subst t
      simp [potential, queueCut]
  | close =>
      simp [step, qWallAfterOddOpenA] at hstep
      subst t
      simp [potential, queueCut, flip_singleton_eq_adjacencyBit,
        adjacencyBit]
  | pass => simp [step, qWallAfterOddOpenA] at hstep

/-- The exchanged-tail wall has the same no-repair property. -/
theorem qWall_afterOddOpenB_no_zero_reply
    (m : Move (Fin 5)) (t : State (Fin 5))
    (hstep : step qPotentialWallGraph qWallAfterOddOpenB m = some t) :
    potential qPotentialWallGraph t = 1 := by
  cases m with
  | «open» v =>
      fin_cases v <;> simp [step, qWallAfterOddOpenB] at hstep
      subst t
      simp [potential, queueCut]
  | close =>
      simp [step, qWallAfterOddOpenB] at hstep
      subst t
      simp [potential, queueCut, flip_singleton_eq_adjacencyBit,
        adjacencyBit]
  | pass => simp [step, qWallAfterOddOpenB] at hstep

end

end Ogdoad.Fifo
