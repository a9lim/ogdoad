import Ogdoad.Fifo

/-!
# Four-valued FIFO outcome transport

At a fixed public FIFO state there are two distinguished even-score targets:
the current mover may be the even player, or the other physical player may be
the even player.  These two propositions form the mover/nonmover outcome
sheet.

Adding one to the accumulated score does not merely negate both entries.  It
also exchanges the two physical targets.  Consequently the exact debt action
on a sheet `(M, N)` is

`(M, N) |-> (not N, not M)`.

The mover-controlled and nonmover-controlled outcome classes are fixed by
this involution; the both-even and both-odd classes are exchanged.  This is a
universal strategy-tree theorem.  It does not assert that the outcome sheet
is compositional under graph union or under a first-block decomposition.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The current physical mover can force terminal score zero. -/
def MoverEvenWins (G : SimpleGraph V) (s : State V) : Prop :=
  EvenWins G s.toMove s

/-- The physical player not currently moving can force terminal score zero. -/
def NonmoverEvenWins (G : SimpleGraph V) (s : State V) : Prop :=
  EvenWins G (!s.toMove) s

/-- Both physical players can force terminal score zero when designated Even. -/
def BothEven (G : SimpleGraph V) (s : State V) : Prop :=
  MoverEvenWins G s ∧ NonmoverEvenWins G s

/-- Exactly the current mover can force terminal score zero. -/
def MoverControlled (G : SimpleGraph V) (s : State V) : Prop :=
  MoverEvenWins G s ∧ ¬NonmoverEvenWins G s

/-- Exactly the current nonmover can force terminal score zero. -/
def NonmoverControlled (G : SimpleGraph V) (s : State V) : Prop :=
  ¬MoverEvenWins G s ∧ NonmoverEvenWins G s

/-- Neither physical player can force terminal score zero when designated
Even.  By determinacy, each can instead force terminal score one when it is
the player outside the distinguished Even seat. -/
def BothOdd (G : SimpleGraph V) (s : State V) : Prop :=
  ¬MoverEvenWins G s ∧ ¬NonmoverEvenWins G s

omit [Fintype V] in
/-- The mover/nonmover sheet lies in exactly one of the four Boolean outcome
regions.  The disjunction is stated in the order both-even, mover-controlled,
nonmover-controlled, both-odd. -/
theorem four_outcome_cases (G : SimpleGraph V) (s : State V) :
    BothEven G s ∨ MoverControlled G s ∨
      NonmoverControlled G s ∨ BothOdd G s := by
  by_cases hM : MoverEvenWins G s
  · by_cases hN : NonmoverEvenWins G s
    · exact Or.inl ⟨hM, hN⟩
    · exact Or.inr (Or.inl ⟨hM, hN⟩)
  · by_cases hN : NonmoverEvenWins G s
    · exact Or.inr (Or.inr (Or.inl ⟨hM, hN⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hM, hN⟩))

omit [Fintype V] in
/-- Determinacy in the dual orientation: an odd strategy exists exactly when
the corresponding even strategy does not. -/
theorem oddWins_iff_not_evenWins (G : SimpleGraph V) (seat : Bool) (s : State V) :
    OddWins G seat s ↔ ¬EvenWins G seat s := by
  constructor
  · intro hodd heven
    exact heven.not_oddWins hodd
  · exact oddWins_of_not_evenWins G seat s

omit [Fintype V] in
/-- A unit score debt complements the opposite-seat entry of the win sheet. -/
theorem evenWins_scoreTranslate_one_iff_not_complementary_evenWins
    (G : SimpleGraph V) (seat : Bool) (s : State V) :
    EvenWins G seat (scoreTranslate 1 s) ↔ ¬EvenWins G (!seat) s := by
  rw [evenWins_scoreTranslate_one_iff_oddWins]
  exact oddWins_iff_not_evenWins G (!seat) s

omit [Fintype V] in
/-- First coordinate of the exact debt action `(M,N) |-> (not N,not M)`. -/
theorem moverEvenWins_scoreTranslate_one_iff
    (G : SimpleGraph V) (s : State V) :
    MoverEvenWins G (scoreTranslate 1 s) ↔ ¬NonmoverEvenWins G s := by
  simpa [MoverEvenWins, NonmoverEvenWins, scoreTranslate] using
    evenWins_scoreTranslate_one_iff_not_complementary_evenWins
      G s.toMove s

omit [Fintype V] in
/-- Second coordinate of the exact debt action `(M,N) |-> (not N,not M)`. -/
theorem nonmoverEvenWins_scoreTranslate_one_iff
    (G : SimpleGraph V) (s : State V) :
    NonmoverEvenWins G (scoreTranslate 1 s) ↔ ¬MoverEvenWins G s := by
  simpa [MoverEvenWins, NonmoverEvenWins, scoreTranslate] using
    evenWins_scoreTranslate_one_iff_not_complementary_evenWins
      G (!s.toMove) s

omit [Fintype V] in
/-- A unit debt exchanges the both-even and both-odd outcome classes. -/
theorem bothEven_scoreTranslate_one_iff_bothOdd
    (G : SimpleGraph V) (s : State V) :
    BothEven G (scoreTranslate 1 s) ↔ BothOdd G s := by
  simp only [BothEven, BothOdd, moverEvenWins_scoreTranslate_one_iff,
    nonmoverEvenWins_scoreTranslate_one_iff, and_comm]

omit [Fintype V] in
/-- Mover control is fixed by the unit-debt involution. -/
theorem moverControlled_scoreTranslate_one_iff
    (G : SimpleGraph V) (s : State V) :
    MoverControlled G (scoreTranslate 1 s) ↔ MoverControlled G s := by
  simp only [MoverControlled, moverEvenWins_scoreTranslate_one_iff,
    nonmoverEvenWins_scoreTranslate_one_iff, not_not, and_comm]

omit [Fintype V] in
/-- Nonmover control is fixed by the unit-debt involution. -/
theorem nonmoverControlled_scoreTranslate_one_iff
    (G : SimpleGraph V) (s : State V) :
    NonmoverControlled G (scoreTranslate 1 s) ↔ NonmoverControlled G s := by
  simp only [NonmoverControlled, moverEvenWins_scoreTranslate_one_iff,
    nonmoverEvenWins_scoreTranslate_one_iff, not_not, and_comm]

omit [Fintype V] in
/-- The reverse cold-class exchange under the same involution. -/
theorem bothOdd_scoreTranslate_one_iff_bothEven
    (G : SimpleGraph V) (s : State V) :
    BothOdd G (scoreTranslate 1 s) ↔ BothEven G s := by
  simp only [BothOdd, BothEven, moverEvenWins_scoreTranslate_one_iff,
    nonmoverEvenWins_scoreTranslate_one_iff, not_not, and_comm]

end

end Ogdoad.Fifo
