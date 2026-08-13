import Ogdoad.BrownGame

/-!
# The intrinsic Brown selector as a finite partizan game

This module closes the operational gap left by the starter-profile decoder in
`BrownGame.lean`.  `FinitePGame` is a finite partizan game tree;
Left and Right have separate option lists, and the two starter predicates are
computed by ordinary normal-play recursion.  The Brown selector is the single
game `{A_(Q+ell) | A_Q}` and its four outcomes are derived from that recursion.
-/

namespace Ogdoad.BrownSelectorPGame

open Ogdoad.BrownGame

/- A finite partizan game and its finite option lists.  The mutual inductive
definition is the ordinary finite-tree analogue of Conway's recursive game tree; it keeps
Left and Right options distinct. -/
mutual
  inductive FinitePGame : Type
    | node (left right : FinitePGameList) : FinitePGame

  inductive FinitePGameList : Type
    | nil : FinitePGameList
    | cons (head : FinitePGame) (tail : FinitePGameList) : FinitePGameList
end

/- The two starter predicates and their option-list folds, computed by
ordinary normal-play recursion on the actual tree. -/
mutual
  def leftToMoveWins : FinitePGame → Bool
    | .node left _ => existsLeftWinningMove left

  def rightToMoveWins : FinitePGame → Bool
    | .node _ right => existsRightWinningMove right

  def existsLeftWinningMove : FinitePGameList → Bool
    | .nil => false
    | .cons g rest => !(rightToMoveWins g) || existsLeftWinningMove rest

  def existsRightWinningMove : FinitePGameList → Bool
    | .nil => false
    | .cons g rest => !(leftToMoveWins g) || existsRightWinningMove rest
end

/-- The four normal-play outcome classes computed from the actual game tree. -/
def outcome (g : FinitePGame) : PartizanOutcome :=
  outcomeOfStarterProfile (leftToMoveWins g) (!(rightToMoveWins g))

/-- The optionless game. -/
def zero : FinitePGame := .node .nil .nil

/-- The impartial star game, with one move for either player to zero. -/
def star : FinitePGame := .node (.cons zero .nil) (.cons zero .nil)

@[simp] theorem leftToMoveWins_zero : leftToMoveWins zero = false := rfl
@[simp] theorem rightToMoveWins_zero : rightToMoveWins zero = false := rfl
@[simp] theorem leftToMoveWins_star : leftToMoveWins star = true := rfl
@[simp] theorem rightToMoveWins_star : rightToMoveWins star = true := rfl

/-- The exact ordinary quadratic follower: it is `P` on bit zero and `N` on
bit one. -/
def quadraticArena (r : ZMod 2) : FinitePGame :=
  if r = 0 then zero else star

@[simp] theorem quadraticArena_zero : quadraticArena 0 = zero := by
  simp [quadraticArena]

@[simp] theorem quadraticArena_one : quadraticArena 1 = star := by
  norm_num [quadraticArena]

theorem quadraticArena_leftToMoveWins (r : ZMod 2) :
    leftToMoveWins (quadraticArena r) = (r == 1) := by
  fin_cases r <;> decide

theorem quadraticArena_rightToMoveWins (r : ZMod 2) :
    rightToMoveWins (quadraticArena r) = (r == 1) := by
  fin_cases r <;> decide

/-- The intrinsic Brown selector is one partizan root, with the `Q+ell`
arena as its unique Left option and the `Q` arena as its unique Right option. -/
def brownSelector (ell Q : ZMod 2) : FinitePGame :=
  .node (.cons (quadraticArena (Q + ell)) .nil)
    (.cons (quadraticArena Q) .nil)

theorem brownSelector_leftToMoveWins (ell Q : ZMod 2) :
    leftToMoveWins (brownSelector ell Q) = !((Q + ell) == 1) := by
  fin_cases ell <;> fin_cases Q <;> decide

theorem brownSelector_rightToMoveWins (ell Q : ZMod 2) :
    rightToMoveWins (brownSelector ell Q) = !(Q == 1) := by
  fin_cases ell <;> fin_cases Q <;> decide

/-- The operational tree semantics agrees with the earlier truth-table
specification. -/
theorem outcome_brownSelector (ell Q : ZMod 2) :
    outcome (brownSelector ell Q) = brownSelectorOutcome ell Q := by
  fin_cases ell <;> fin_cases Q <;> decide

/-- The four actual games realize `0 -> N`, `1 -> R`, `2 -> P`, `3 -> L`. -/
theorem brownSelector_outcome_table :
    outcome (brownSelector 0 0) = .next ∧
    outcome (brownSelector 1 0) = .right ∧
    outcome (brownSelector 0 1) = .previous ∧
    outcome (brownSelector 1 1) = .left := by
  decide

/-- The fixed outcome decoder recovers the Brown residue from the actual
partizan game. -/
theorem brownSelector_decodes (ell Q : ZMod 2) :
    brownResidueOfOutcome (outcome (brownSelector ell Q)) =
      liftBit ell + doubleBit Q := by
  rw [outcome_brownSelector, brownSelectorOutcome_decodes]

/- Apply the actual selector game to the canonical bits of a Brown
refinement. -/
def partizanGame {V : Type*} [AddCommGroup V]
    (q : BrownRefinement V) (x : V) : FinitePGame :=
  brownSelector (q.linearPart x) (q.classicalPart x)

/-- End-to-end four-outcome realization of a Brown refinement by one finite
partizan game. -/
theorem partizanGame_decodes
    {V : Type*} [AddCommGroup V] (q : BrownRefinement V) (x : V) :
    brownResidueOfOutcome (outcome (partizanGame q x)) = q.quadratic x := by
  rw [partizanGame, brownSelector_decodes]
  exact (q.decomposition x).symm

end Ogdoad.BrownSelectorPGame
