import Ogdoad.FifoDistinctOpenForkBoundary

/-!
# Cell-swap outcome and polarity boundary

The empty-queue distinct-OPEN fork creates two crossed endpoints whose queues
are one reversed FIFO cell.  Score-untranslating the right endpoint gives a
genuine `PublicCellSwap`, but a controlled-state induction would additionally
need the two queue orders to carry compatible outcome sheets.

They need not.  This file gives a reflected finite Bellman evaluator and a
coherent isolated-dummy countermodel in which one cell order is `BothOdd` and
the reversed order is `BothEven`.  Thus neither endpoint is controlled.  The
positive CellSwap braid is real structural information, but it does not by
itself yield a lower controlled state or repair the score-policy polarity.

The countermodel is a no-go for that induction step, not a counterexample to
the initial-root FIFO linking conjecture.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u


def finiteMoves (V : Type u) [Fintype V] : List (Move V) :=
  (Finset.univ.toList.map Move.open) ++ [.close, .pass]

theorem mem_finiteMoves {V : Type u} [Fintype V] [DecidableEq V]
    (m : Move V) : m ∈ finiteMoves V := by
  cases m with
  | «open» v => simp [finiteMoves]
  | close => simp [finiteMoves]
  | pass => simp [finiteMoves]

def finiteChildren {V : Type u}
    (moves : List (Move V))
    (next : State V → Move V → Option (State V)) (s : State V) :
    List (Move V × State V) :=
  moves.filterMap fun m ↦ (next s m).map fun t ↦ (m, t)

theorem mem_finiteChildren_of_next {V : Type u} [DecidableEq V]
    {moves : List (Move V)}
    {next : State V → Move V → Option (State V)} {s t : State V}
    {m : Move V} (hm : m ∈ moves) (h : next s m = some t) :
    (m, t) ∈ finiteChildren moves next s := by
  rw [finiteChildren, List.mem_filterMap]
  exact ⟨m, hm, by simp [h]⟩

theorem next_of_mem_finiteChildren {V : Type u} [DecidableEq V]
    {moves : List (Move V)}
    {next : State V → Move V → Option (State V)} {s : State V}
    {child : Move V × State V} (h : child ∈ finiteChildren moves next s) :
    next s child.1 = some child.2 := by
  rw [finiteChildren, List.mem_filterMap] at h
  obtain ⟨m, _hm, hmap⟩ := h
  cases hn : next s m with
  | none => simp [hn] at hmap
  | some t =>
      simp [hn] at hmap
      cases hmap
      exact hn

def finiteEvenWinner {V : Type u} [Fintype V] [DecidableEq V]
    (moves : List (Move V))
    (next : State V → Move V → Option (State V)) (seat : Bool) :
    Nat → State V → Bool
  | 0, s => decide (s.score = 0)
  | fuel + 1, s =>
      if s.untouched = ∅ ∧ s.queue = [] then decide (s.score = 0)
      else if s.toMove = seat then
        (finiteChildren moves next s).any fun child ↦
          finiteEvenWinner moves next seat fuel child.2
      else
        (finiteChildren moves next s).all fun child ↦
          finiteEvenWinner moves next seat fuel child.2

theorem finiteEvenWinner_spec {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (moves : List (Move V)) (hcomplete : ∀ m, m ∈ moves)
    (next : State V → Move V → Option (State V))
    (hnext : ∀ s m, next s m = step G s m) (seat : Bool) :
    ∀ (fuel : Nat) (s : State V), rank s < fuel →
      if finiteEvenWinner moves next seat fuel s then EvenWins G seat s
      else OddWins G seat s := by
  intro fuel
  induction fuel with
  | zero =>
      intro s hrank
      omega
  | succ fuel ih =>
      intro s hrank
      rw [finiteEvenWinner]
      split
      · rename_i hterminal
        split
        · rename_i hscore
          exact EvenWins.terminal s hterminal (of_decide_eq_true hscore)
        · rename_i hscore
          have hscore' : decide (s.score = 0) = false := by
            cases h : decide (s.score = 0)
            · rfl
            · exact False.elim (hscore h)
          exact OddWins.terminal s hterminal (of_decide_eq_false hscore')
      · rename_i hterminal
        split
        · rename_i hseat
          split
          · rename_i hany
            obtain ⟨child, hmem, hwin⟩ := List.any_eq_true.mp hany
            have hstep : step G s child.1 = some child.2 := by
              rw [← hnext]
              exact next_of_mem_finiteChildren hmem
            have hrankChild : rank child.2 < fuel := by
              have := rank_step_lt hstep
              omega
            have hchild := ih child.2 hrankChild
            rw [hwin] at hchild
            exact EvenWins.choose s hseat child.1 child.2 hstep hchild
          · rename_i hany
            have hany' :
                (finiteChildren moves next s).any (fun child ↦
                  finiteEvenWinner moves next seat fuel child.2) = false := by
              cases h : (finiteChildren moves next s).any (fun child ↦
                finiteEvenWinner moves next seat fuel child.2)
              · rfl
              · exact False.elim (hany h)
            refine OddWins.answer s hseat (not_terminal_has_step hterminal) ?_
            intro m t hstep
            have hmem : (m, t) ∈ finiteChildren moves next s := by
              apply mem_finiteChildren_of_next
              · exact hcomplete m
              · rw [hnext, hstep]
            have hnot := List.any_eq_false.mp hany' (m, t) hmem
            have hwin : finiteEvenWinner moves next seat fuel t = false := by
              cases h : finiteEvenWinner moves next seat fuel t
              · rfl
              · exact False.elim (hnot h)
            have hrankChild : rank t < fuel := by
              have := rank_step_lt hstep
              omega
            have hchild := ih t hrankChild
            rw [hwin] at hchild
            exact hchild
        · rename_i hseat
          split
          · rename_i hall
            refine EvenWins.answer s hseat (not_terminal_has_step hterminal) ?_
            intro m t hstep
            have hmem : (m, t) ∈ finiteChildren moves next s := by
              apply mem_finiteChildren_of_next
              · exact hcomplete m
              · rw [hnext, hstep]
            have hwin := List.all_eq_true.mp hall (m, t) hmem
            have hrankChild : rank t < fuel := by
              have := rank_step_lt hstep
              omega
            have hchild := ih t hrankChild
            rw [hwin] at hchild
            exact hchild
          · rename_i hall
            have hall' :
                (finiteChildren moves next s).all (fun child ↦
                  finiteEvenWinner moves next seat fuel child.2) = false := by
              cases h : (finiteChildren moves next s).all (fun child ↦
                finiteEvenWinner moves next seat fuel child.2)
              · rfl
              · exact False.elim (hall h)
            obtain ⟨child, hmem, hnot⟩ := List.all_eq_false.mp hall'
            have hwin : finiteEvenWinner moves next seat fuel child.2 = false := by
              cases h : finiteEvenWinner moves next seat fuel child.2
              · rfl
              · exact False.elim (hnot h)
            have hstep : step G s child.1 = some child.2 := by
              rw [← hnext]
              exact next_of_mem_finiteChildren hmem
            have hrankChild : rank child.2 < fuel := by
              have := rank_step_lt hstep
              omega
            have hchild := ih child.2 hrankChild
            rw [hwin] at hchild
            exact OddWins.choose s hseat child.1 child.2 hstep hchild

def polarityBoundaryRel (x y : Fin 7) : Bool := decide (
    (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 3) ∨
    (x = 0 ∧ y = 5) ∨ (x = 1 ∧ y = 2) ∨
    (x = 1 ∧ y = 3) ∨ (x = 1 ∧ y = 5) ∨
    (x = 2 ∧ y = 4) ∨ (x = 3 ∧ y = 4) ∨
    (x = 3 ∧ y = 5))

def polarityBoundaryGraph : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel fun x y ↦ polarityBoundaryRel x y = true

def polarityBoundaryAdj (x y : Fin 7) : Bool :=
  polarityBoundaryRel x y || polarityBoundaryRel y x

def polarityBoundaryFlip (U : Finset (Fin 7)) (v : Fin 7) : ZMod 2 :=
  ((U.filter fun w ↦ polarityBoundaryAdj v w = true).card : ZMod 2)

theorem polarityBoundaryFlip_eq_flip (U : Finset (Fin 7)) (v : Fin 7) :
    polarityBoundaryFlip U v = flip polarityBoundaryGraph U v := by
  classical
  simp only [polarityBoundaryFlip, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [polarityBoundaryAdj, polarityBoundaryRel, polarityBoundaryGraph,
      SimpleGraph.fromRel_adj]

def polarityBoundaryStep (s : State (Fin 7)) :
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
              score := s.score + polarityBoundaryFlip s.untouched f }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

theorem polarityBoundaryStep_eq_step (s : State (Fin 7)) (m : Move (Fin 7)) :
    polarityBoundaryStep s m = step polarityBoundaryGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [polarityBoundaryStep, step]
  | close =>
      cases q <;> cases ko <;> simp [polarityBoundaryStep, step,
        polarityBoundaryFlip_eq_flip]
  | pass => simp [polarityBoundaryStep, step]

def polarityBoundaryA : State (Fin 7) where
  untouched := {1, 2, 3, 5}
  queue := [0, 4]
  ko := false
  toMove := false
  score := 0

def polarityBoundaryB : State (Fin 7) where
  untouched := {1, 2, 3, 5}
  queue := [4, 0]
  ko := false
  toMove := false
  score := 0

def polarityBoundaryMoves : List (Move (Fin 7)) :=
  [.open 0, .open 1, .open 2, .open 3, .open 4, .open 5, .open 6,
    .close, .pass]

theorem mem_polarityBoundaryMoves (m : Move (Fin 7)) :
    m ∈ polarityBoundaryMoves := by
  cases m with
  | «open» v => fin_cases v <;> simp [polarityBoundaryMoves]
  | close => simp [polarityBoundaryMoves]
  | pass => simp [polarityBoundaryMoves]

def polarityBoundaryWinner (seat : Bool) (s : State (Fin 7)) : Bool :=
  finiteEvenWinner polarityBoundaryMoves polarityBoundaryStep seat
    (rank s + 1) s

theorem polarityBoundaryWinner_spec (seat : Bool) (s : State (Fin 7)) :
    if polarityBoundaryWinner seat s then
      EvenWins polarityBoundaryGraph seat s
    else OddWins polarityBoundaryGraph seat s := by
  apply finiteEvenWinner_spec polarityBoundaryGraph polarityBoundaryMoves
    mem_polarityBoundaryMoves polarityBoundaryStep
    polarityBoundaryStep_eq_step seat (rank s + 1) s
  omega

theorem polarityBoundaryA_false_loses :
    polarityBoundaryWinner false polarityBoundaryA = false := by
  decide

theorem polarityBoundaryA_true_loses :
    polarityBoundaryWinner true polarityBoundaryA = false := by
  decide

theorem polarityBoundaryB_false_wins :
    polarityBoundaryWinner false polarityBoundaryB = true := by
  decide

theorem polarityBoundaryB_true_wins :
    polarityBoundaryWinner true polarityBoundaryB = true := by
  decide

theorem polarityBoundaryA_oddWins_false :
    OddWins polarityBoundaryGraph false polarityBoundaryA := by
  have h := polarityBoundaryWinner_spec false polarityBoundaryA
  rw [polarityBoundaryA_false_loses] at h
  exact h

theorem polarityBoundaryA_oddWins_true :
    OddWins polarityBoundaryGraph true polarityBoundaryA := by
  have h := polarityBoundaryWinner_spec true polarityBoundaryA
  rw [polarityBoundaryA_true_loses] at h
  exact h

theorem polarityBoundaryB_evenWins_false :
    EvenWins polarityBoundaryGraph false polarityBoundaryB := by
  have h := polarityBoundaryWinner_spec false polarityBoundaryB
  rw [polarityBoundaryB_false_wins] at h
  exact h

theorem polarityBoundaryB_evenWins_true :
    EvenWins polarityBoundaryGraph true polarityBoundaryB := by
  have h := polarityBoundaryWinner_spec true polarityBoundaryB
  rw [polarityBoundaryB_true_wins] at h
  exact h

theorem polarityBoundaryA_bothOdd :
    BothOdd polarityBoundaryGraph polarityBoundaryA := by
  constructor
  · have hnot := (oddWins_iff_not_evenWins polarityBoundaryGraph false
        polarityBoundaryA).mp polarityBoundaryA_oddWins_false
    simpa [MoverEvenWins, polarityBoundaryA] using hnot
  · have hnot := (oddWins_iff_not_evenWins polarityBoundaryGraph true
        polarityBoundaryA).mp polarityBoundaryA_oddWins_true
    simpa [NonmoverEvenWins, polarityBoundaryA] using hnot

theorem polarityBoundaryB_bothEven :
    BothEven polarityBoundaryGraph polarityBoundaryB := by
  exact ⟨by simpa [MoverEvenWins, polarityBoundaryB] using
      polarityBoundaryB_evenWins_false,
    by simpa [NonmoverEvenWins, polarityBoundaryB] using
      polarityBoundaryB_evenWins_true⟩

theorem polarityBoundary_publicCellSwap :
    PublicCellSwap polarityBoundaryA polarityBoundaryB := {
  untouched := rfl
  queue := CellSwap.cell 0 4 CellSwap.nil
  ko := rfl
  toMove := rfl
  score := rfl }

theorem polarityBoundaryGraph_dummy :
    IsDummy polarityBoundaryGraph 6 := by
  intro v
  fin_cases v <;>
    simp [polarityBoundaryGraph, polarityBoundaryRel,
      SimpleGraph.fromRel_adj]

theorem polarityBoundaryA_coherent : Coherent polarityBoundaryA := by
  simp [Coherent, WellFormed, polarityBoundaryA]

theorem polarityBoundaryB_coherent : Coherent polarityBoundaryB := by
  simp [Coherent, WellFormed, polarityBoundaryB]

/-- `PublicCellSwap` does not transport the cold outcome class, even in a
graph with an isolated dummy: these coherent endpoints have opposite cold
sheets.  Therefore the empty-queue crossed-OPEN braid cannot by itself turn
the two endpoint policies into a lower controlled state. -/
theorem publicCellSwap_does_not_preserve_cold_outcome :
    ∃ (G : SimpleGraph (Fin 7)) (d : Fin 7) (s t : State (Fin 7)),
      IsDummy G d ∧ Coherent s ∧ Coherent t ∧ PublicCellSwap s t ∧
      BothOdd G s ∧ BothEven G t := by
  exact ⟨polarityBoundaryGraph, 6, polarityBoundaryA, polarityBoundaryB,
    polarityBoundaryGraph_dummy, polarityBoundaryA_coherent,
    polarityBoundaryB_coherent, polarityBoundary_publicCellSwap,
    polarityBoundaryA_bothOdd, polarityBoundaryB_bothEven⟩

end

end Ogdoad.Fifo
