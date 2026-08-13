import Ogdoad.FifoPairGaussian

/-!
# Zero-second-moment pair safety boundary

This module tests the proposed universal Bellman safety of a same-degree
initial pair with vanishing second moment.  The search is restricted to an
already formalized exact candidate graph; no graph census is used.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Structural relation to the parity-selected initial seat -/

/-- The existing exact losing equal-degree pair does not satisfy the new
hypothesis: its second moment is one.  Thus it is not a q=0 counterexample. -/
theorem pairGaussianCounter_secondMoment_eq_one :
    pairSecondMoment pairGaussianCounterGraph Finset.univ 0 4 = 1 := by
  norm_num [pairSecondMoment, neighborDegreeBit, flip, adjacencyBit,
    pairGaussianCounterGraph, pairGaussianCounterRel,
    SimpleGraph.fromRel_adj]
  all_goals decide

/-- Universal safety assertion for same-degree, zero-second-moment initial
pairs on one graph. -/
def ZeroMomentPairSafeAt (G : SimpleGraph V) : Prop :=
  ∀ (seat : Bool) (x y : V),
    y ∈ sameDegreeMates G Finset.univ x →
      pairSecondMoment G Finset.univ x y = 0 →
        EvenWins G seat (afterInitialTwoOpens x y)

/-- The q=0 pair theorem would prove the even-carrier/nonmover half of
`FifoParitySeatAt`.  After every first OPEN, seat `true` chooses the two-bit
handshake mate and invokes pair safety. -/
theorem even_nonmover_of_zeroMomentPairSafe
    (G : SimpleGraph V) [Nontrivial V]
    (hsafe : ZeroMomentPairSafeAt G)
    (hcard : Even (Fintype.card V)) :
    EvenWins G true (initial (V := V)) := by
  have hcardZ : (((Finset.univ : Finset V).card : Nat) : ZMod 2) = 0 := by
    rw [Finset.card_univ, ← ZMod.natCast_mod (Fintype.card V) 2,
      Nat.even_iff.mp hcard]
    rfl
  have hU : (Finset.univ : Finset V) ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp Finset.univ_nonempty
  refine EvenWins.answer (initial (V := V)) (by simp [initial])
    ⟨.open (Classical.choice (inferInstance : Nonempty V)),
      afterInitialOpen (Classical.choice (inferInstance : Nonempty V)),
      initial_step_open G _⟩ ?_
  intro m t hstep
  cases m with
  | close => simp [step, initial] at hstep
  | pass => simp [step, initial, hU] at hstep
  | «open» x =>
      have hxstep := initial_step_open G x
      rw [hxstep] at hstep
      have ht : t = afterInitialOpen x := Option.some.inj hstep.symm
      subst t
      obtain ⟨y, hyMate, hmoment⟩ :=
        exists_sameDegreeMate_pairSecondMoment_eq_zero
          G Finset.univ x (Finset.mem_univ x) hcardZ
      have hy := (Finset.mem_filter.mp hyMate).1
      have hyStep := (afterInitialOpen_step_open_iff G x y).2 hy
      refine EvenWins.choose (afterInitialOpen x) (by simp [afterInitialOpen])
        (.open y) (afterInitialTwoOpens x y) hyStep ?_
      exact hsafe true x y hyMate hmoment

/-- Exact odd-order quantifier obstruction: pair safety can prove the
mover-seat root only if one can find a first opener for which every legal
second reply is already a safe q=0 mate.  The two-bit handshake supplies only
one such mate for each opener and therefore does not establish this premise. -/
theorem odd_mover_of_all_secondReplies_zeroMoment
    (G : SimpleGraph V) [Nontrivial V]
    (hsafe : ZeroMomentPairSafeAt G) (x : V)
    (hall : ∀ y ∈ (Finset.univ.erase x : Finset V),
      y ∈ sameDegreeMates G Finset.univ x ∧
        pairSecondMoment G Finset.univ x y = 0) :
    EvenWins G false (initial (V := V)) := by
  rw [evenWins_initial_firstSeat_iff_twoOpenSelector]
  exact ⟨x, fun y hy ↦ hsafe false x y (hall y hy).1 (hall y hy).2⟩

/-- Smallest exact failure of the odd-order premise: on the three-vertex path
`0—1—2`, after first opener `0`, reply `1` is legal but has the opposite
full-degree parity and hence is outside the same-degree (therefore q=0)
selector class. -/
def oddQuantifierCounterGraph : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun x y ↦ x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 2

theorem oddQuantifierCounter_reply_legal :
    (1 : Fin 3) ∈ (Finset.univ.erase 0 : Finset (Fin 3)) := by decide

theorem oddQuantifierCounter_reply_not_sameDegree :
    (1 : Fin 3) ∉
      sameDegreeMates oddQuantifierCounterGraph Finset.univ 0 := by
  norm_num [sameDegreeMates, flip, oddQuantifierCounterGraph,
    SimpleGraph.fromRel_adj]
  all_goals decide

/-- Therefore even perfect universal q=0 pair safety cannot by itself close
the odd-card/mover Bellman fan via the handshake selector. -/
theorem oddQuantifierCounter_not_all_secondReplies_zeroMoment :
    ¬∀ y ∈ (Finset.univ.erase (0 : Fin 3) : Finset (Fin 3)),
      y ∈ sameDegreeMates oddQuantifierCounterGraph Finset.univ 0 ∧
        pairSecondMoment oddQuantifierCounterGraph Finset.univ 0 y = 0 := by
  intro hall
  exact oddQuantifierCounter_reply_not_sameDegree
    (hall 1 oddQuantifierCounter_reply_legal).1

/-- Exact outcome bit of the existing fixed-front phase-pivot graph at its
zero-second-moment initial pair. -/
def phasePivotPairWinner : Bool :=
  finiteEvenWinner phasePivotCounterMoves phasePivotCounterStep true
    (rank (afterInitialTwoOpens (1 : Fin 7) 2) + 1)
    (afterInitialTwoOpens (1 : Fin 7) 2)

theorem phasePivotPairWinner_value : phasePivotPairWinner = true := by
  native_decide

set_option maxHeartbeats 2000000 in
/-- Full Bellman certificate for the positive phase-pivot test.  This includes
all legal CLOSE and OPEN continuations, not only the restricted two-action
menu considered in `FifoPairGaussian`. -/
theorem phasePivot_zeroMomentPair_evenWins :
    EvenWins phasePivotCounterGraph true
      (afterInitialTwoOpens (1 : Fin 7) 2) := by
  have hspec := finiteEvenWinner_spec phasePivotCounterGraph
    phasePivotCounterMoves mem_phasePivotCounterMoves phasePivotCounterStep
    phasePivotCounterStep_eq_step true
    (rank (afterInitialTwoOpens (1 : Fin 7) 2) + 1)
    (afterInitialTwoOpens (1 : Fin 7) 2) (by omega)
  have hvalue :
      finiteEvenWinner phasePivotCounterMoves phasePivotCounterStep true
        (rank (afterInitialTwoOpens (1 : Fin 7) 2) + 1)
        (afterInitialTwoOpens (1 : Fin 7) 2) = true :=
    phasePivotPairWinner_value
  rw [hvalue] at hspec
  exact hspec

/-! ## The third-moment boundary as an exact pair-safety test -/

/-- The eight-real part of `thirdMomentCounterGraph`: a six-vertex path,
with `6` adjacent to `3,4` and `7` isolated.  The pair `6,7` has zero
second moment, while its forced two-bit response to `OPEN 1` is `OPEN 2`
and creates unit next-pair debt. -/
def zeroMomentCounterRel (x y : Fin 8) : Bool := decide (
  (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 3) ∨
  (x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 5) ∨
  (x = 3 ∧ y = 6) ∨ (x = 4 ∧ y = 6))

def zeroMomentCounterGraph : SimpleGraph (Fin 8) :=
  SimpleGraph.fromRel fun x y ↦ zeroMomentCounterRel x y = true

def zeroMomentCounterAdj (x y : Fin 8) : Bool :=
  zeroMomentCounterRel x y || zeroMomentCounterRel y x

def zeroMomentCounterFlip (U : Finset (Fin 8)) (v : Fin 8) : ZMod 2 :=
  ((U.filter fun w ↦ zeroMomentCounterAdj v w = true).card : ZMod 2)

theorem zeroMomentCounterFlip_eq_flip
    (U : Finset (Fin 8)) (v : Fin 8) :
    zeroMomentCounterFlip U v = flip zeroMomentCounterGraph U v := by
  classical
  simp only [zeroMomentCounterFlip, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [zeroMomentCounterAdj, zeroMomentCounterRel,
      zeroMomentCounterGraph, SimpleGraph.fromRel_adj]

def zeroMomentCounterStep (s : State (Fin 8)) :
    Move (Fin 8) → Option (State (Fin 8))
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
              score := s.score + zeroMomentCounterFlip s.untouched f }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

theorem zeroMomentCounterStep_eq_step
    (s : State (Fin 8)) (m : Move (Fin 8)) :
    zeroMomentCounterStep s m = step zeroMomentCounterGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [zeroMomentCounterStep, step]
  | close =>
      cases q <;> cases ko <;> simp [zeroMomentCounterStep, step,
        zeroMomentCounterFlip_eq_flip]
  | pass => simp [zeroMomentCounterStep, step]

def zeroMomentCounterMoves : List (Move (Fin 8)) :=
  [.open 0, .open 1, .open 2, .open 3, .open 4, .open 5, .open 6, .open 7,
    .close, .pass]

theorem mem_zeroMomentCounterMoves (m : Move (Fin 8)) :
    m ∈ zeroMomentCounterMoves := by
  cases m with
  | «open» v => fin_cases v <;> simp [zeroMomentCounterMoves]
  | close => simp [zeroMomentCounterMoves]
  | pass => simp [zeroMomentCounterMoves]

def zeroMomentCounterWinner : Bool :=
  finiteEvenWinner zeroMomentCounterMoves zeroMomentCounterStep true
    (rank (afterInitialTwoOpens (6 : Fin 8) 7) + 1)
    (afterInitialTwoOpens (6 : Fin 8) 7)

theorem zeroMomentCounterWinner_value : zeroMomentCounterWinner = true := by
  native_decide

theorem zeroMomentCounter_root_data :
    (7 : Fin 8) ∈
        sameDegreeMates zeroMomentCounterGraph Finset.univ 6 ∧
      pairSecondMoment zeroMomentCounterGraph Finset.univ 6 7 = 0 := by
  constructor
  · norm_num [sameDegreeMates, flip, zeroMomentCounterGraph,
      zeroMomentCounterRel, SimpleGraph.fromRel_adj]
    all_goals decide
  · norm_num [pairSecondMoment, neighborDegreeBit, flip, adjacencyBit,
      zeroMomentCounterGraph, zeroMomentCounterRel,
      SimpleGraph.fromRel_adj]
    all_goals decide

/-! ## A one-edge repair of the existing losing pair -/

/-- Add edge `1—3` to `pairGaussianCounterGraph`.  This toggles the
second moment of pair `0,4` while preserving their common degree parity. -/
def repairedPairCounterRel (x y : Fin 7) : Bool := decide (
  (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 0 ∧ y = 5) ∨
  (x = 1 ∧ y = 3) ∨ (x = 1 ∧ y = 5) ∨
  (x = 2 ∧ y = 4) ∨ (x = 2 ∧ y = 5))

def repairedPairCounterGraph : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel fun x y ↦ repairedPairCounterRel x y = true

def repairedPairCounterAdj (x y : Fin 7) : Bool :=
  repairedPairCounterRel x y || repairedPairCounterRel y x

def repairedPairCounterFlip (U : Finset (Fin 7)) (v : Fin 7) : ZMod 2 :=
  ((U.filter fun w ↦ repairedPairCounterAdj v w = true).card : ZMod 2)

theorem repairedPairCounterFlip_eq_flip
    (U : Finset (Fin 7)) (v : Fin 7) :
    repairedPairCounterFlip U v = flip repairedPairCounterGraph U v := by
  classical
  simp only [repairedPairCounterFlip, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [repairedPairCounterAdj, repairedPairCounterRel,
      repairedPairCounterGraph, SimpleGraph.fromRel_adj]

def repairedPairCounterStep (s : State (Fin 7)) :
    Move (Fin 7) → Option (State (Fin 7))
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
              score := s.score + repairedPairCounterFlip s.untouched f }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

theorem repairedPairCounterStep_eq_step
    (s : State (Fin 7)) (m : Move (Fin 7)) :
    repairedPairCounterStep s m = step repairedPairCounterGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [repairedPairCounterStep, step]
  | close =>
      cases q <;> cases ko <;> simp [repairedPairCounterStep, step,
        repairedPairCounterFlip_eq_flip]
  | pass => simp [repairedPairCounterStep, step]

def repairedPairCounterWinner : Bool :=
  finiteEvenWinner pairGaussianCounterMoves repairedPairCounterStep true
    (rank (afterInitialTwoOpens (0 : Fin 7) 4) + 1)
    (afterInitialTwoOpens (0 : Fin 7) 4)

theorem repairedPairCounterWinner_value :
    repairedPairCounterWinner = true := by
  native_decide

set_option maxHeartbeats 500000 in
theorem repairedPairCounter_root_data :
    (4 : Fin 7) ∈
        sameDegreeMates repairedPairCounterGraph Finset.univ 0 ∧
      pairSecondMoment repairedPairCounterGraph Finset.univ 0 4 = 0 := by
  constructor
  · norm_num [sameDegreeMates, flip, repairedPairCounterGraph,
      repairedPairCounterRel, SimpleGraph.fromRel_adj]
    all_goals decide
  · norm_num [pairSecondMoment, neighborDegreeBit, flip, adjacencyBit,
      repairedPairCounterGraph, repairedPairCounterRel,
      SimpleGraph.fromRel_adj]
    all_goals decide

set_option maxHeartbeats 2000000 in
theorem repaired_zeroMomentPair_evenWins :
    EvenWins repairedPairCounterGraph true
      (afterInitialTwoOpens (0 : Fin 7) 4) := by
  have hspec := finiteEvenWinner_spec repairedPairCounterGraph
    pairGaussianCounterMoves mem_pairGaussianCounterMoves
    repairedPairCounterStep repairedPairCounterStep_eq_step true
    (rank (afterInitialTwoOpens (0 : Fin 7) 4) + 1)
    (afterInitialTwoOpens (0 : Fin 7) 4) (by omega)
  have hvalue :
      finiteEvenWinner pairGaussianCounterMoves repairedPairCounterStep true
        (rank (afterInitialTwoOpens (0 : Fin 7) 4) + 1)
        (afterInitialTwoOpens (0 : Fin 7) 4) = true :=
    repairedPairCounterWinner_value
  rw [hvalue] at hspec
  exact hspec

end

end Ogdoad.Fifo
