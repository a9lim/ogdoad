import Mathlib.Data.Bool.Basic

/-!
# Outcome-preserving unavoidable fork padding

This records why strengthening a counterfactual-fork axiom from raw
reachability to optimal or even unavoidable reachability does not by itself
exclude decorative gadgets.
-/

namespace Ogdoad.GoldForkPadding

mutual
  inductive Tree where
    | node (moves : Forest)

  inductive Forest where
    | nil
    | cons (head : Tree) (tail : Forest)
end

mutual
  def win : Tree → Bool
    | .node moves => hasLosing moves

  def hasLosing : Forest → Bool
    | .nil => false
    | .cons head tail => !win head || hasLosing tail
end

def pLeaf : Tree := .node .nil
def nStar : Tree := .node (.cons pLeaf .nil)

def leftChild (q : Bool) : Tree := if q then nStar else pLeaf
def rightChild (q : Bool) : Tree := if q then pLeaf else nStar

/-- Both actions are always legal; exactly one goes to a P-position, and the
choice swaps when the queried bit swaps. -/
def fork (q : Bool) : Tree :=
  .node (.cons (leftChild q) (.cons (rightChild q) .nil))

/-- A single forced move into the always-N fork makes a P-position. Hence this
wrapper can replace any terminal P-node without changing its outcome. -/
def wrapper (q : Bool) : Tree :=
  .node (.cons (fork q) .nil)

theorem pLeaf_isP : win pLeaf = false := by rfl
theorem nStar_isN : win nStar = true := by rfl

theorem fork_isN (q : Bool) : win (fork q) = true := by
  cases q <;> decide

theorem fork_optimum_swaps (q : Bool) :
    (!win (leftChild (!q)) = !win (rightChild q)) ∧
    (!win (rightChild (!q)) = !win (leftChild q)) := by
  cases q <;> decide

theorem fork_has_unique_winning_action (q : Bool) :
    (!win (leftChild q) != !win (rightChild q)) := by
  cases q <;> decide

theorem wrapper_isP (q : Bool) : win (wrapper q) = false := by
  cases q <;> decide

mutual
  def padTerminals (q : Bool) : Tree → Tree
    | .node .nil => wrapper q
    | .node (.cons head tail) =>
        .node (.cons (padTerminals q head) (padForest q tail))

  def padForest (q : Bool) : Forest → Forest
    | .nil => .nil
    | .cons head tail => .cons (padTerminals q head) (padForest q tail)
end

/-- Every original terminal is replaced by an unavoidable q-sensitive fork,
yet the normal-play outcome of every finite tree is unchanged. -/
theorem win_padTerminals (q : Bool) (tree : Tree) :
    win (padTerminals q tree) = win tree := by
  apply Tree.rec
    (motive_1 := fun t => win (padTerminals q t) = win t)
    (motive_2 := fun f => hasLosing (padForest q f) = hasLosing f)
  · intro moves ih
    cases moves with
    | nil => simp [padTerminals, wrapper_isP, win, hasLosing]
    | cons head tail => simpa [padTerminals, padForest, win] using ih
  · rfl
  · intro head tail ihHead ihTail
    simp [padForest, hasLosing, ihHead, ihTail]

end Ogdoad.GoldForkPadding
