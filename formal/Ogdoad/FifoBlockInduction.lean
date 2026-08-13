import Ogdoad.FifoEmptyQueue

/-!
# First-block induction for FIFO linking

This module separates the global empty-root induction from the unresolved
combinatorics inside one positive FIFO block.  `EvenBlockWins` is a finite
strategy tree which may stop at a certified, strictly smaller state.  The
splicing theorem replaces every such exit by an ordinary `EvenWins` tree.

Three first-block hypotheses then suffice:

* the mover can end a zero-score block on every carrier;
* the nonmover can do so on an even carrier while leaving even residual
  order;
* the nonmover can do so on an odd carrier with an isolated dummy, leaving
  either even residual order or the dummy still untouched.

The corresponding full empty-root theorems follow by well-founded induction
on the number of untouched vertices.  The last theorem specializes these
abstract block hypotheses to both seats of an isolated-dummy initial board.
No declaration below proves any of the three first-block hypotheses.  In
fact, the mover property is a deliberately strong sufficient hypothesis and
is false for arbitrary graphs (an eight-vertex counterexample is known); the
point of the module is the exact splicing implication, not a claim that this
particular block package settles FIFO linking.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A score-zero empty-queue checkpoint on a specified untouched carrier and
with a specified physical player to move. -/
def emptyRoot (U : Finset V) (turn : Bool) : State V where
  untouched := U
  queue := []
  ko := false
  toMove := turn
  score := 0

/-- A target-zero strategy which is allowed to stop at a state satisfying
`Exit`, provided its untouched carrier is strictly smaller than `bound`.
The choice/answer constructors have exactly the same quantifier order as
`EvenWins`; only the additional `exit` constructor differs. -/
inductive EvenBlockWins (G : SimpleGraph V) (seat : Bool) (bound : Nat)
    (Exit : State V → Prop) : State V → Prop
  | terminal (s : State V) (hterminal : Terminal s) (hscore : s.score = 0) :
      EvenBlockWins G seat bound Exit s
  | exit (s : State V) (hscore : s.score = 0)
      (hsmaller : s.untouched.card < bound) (hexit : Exit s) :
      EvenBlockWins G seat bound Exit s
  | choose (s : State V) (hseat : s.toMove = seat)
      (m : Move V) (s' : State V) (hstep : step G s m = some s')
      (hwin : EvenBlockWins G seat bound Exit s') :
      EvenBlockWins G seat bound Exit s
  | answer (s : State V) (hseat : s.toMove ≠ seat)
      (hasMove : ∃ m s', step G s m = some s')
      (hwin : ∀ m s', step G s m = some s' →
        EvenBlockWins G seat bound Exit s') :
      EvenBlockWins G seat bound Exit s

omit [Fintype V] in
/-- Splice an ordinary even-winning continuation into every certified block
exit. -/
theorem EvenBlockWins.toEvenWins
    {G : SimpleGraph V} {seat : Bool} {bound : Nat}
    {Exit : State V → Prop} {s : State V}
    (h : EvenBlockWins G seat bound Exit s)
    (hcont : ∀ t, t.untouched.card < bound → Exit t → EvenWins G seat t) :
    EvenWins G seat s := by
  induction h with
  | terminal s ht hs => exact EvenWins.terminal s ht hs
  | exit s _ hsmall hexit => exact hcont s hsmall hexit
  | choose s hseat m s' hstep _ ih =>
      exact EvenWins.choose s hseat m s' hstep ih
  | answer s hseat hasMove _ ih =>
      exact EvenWins.answer s hseat hasMove ih

/-- First-block obligation for the physical player who owns the empty-root
move.  The next empty root has the same mover and strictly fewer untouched
vertices (the strict inequality is carried by `EvenBlockWins.exit`). -/
def MoverFirstBlockProperty (G : SimpleGraph V) : Prop :=
  ∀ (U : Finset V) (turn : Bool), U.Nonempty →
    EvenBlockWins G turn U.card
      (fun t ↦ t = emptyRoot t.untouched turn) (emptyRoot U turn)

/-- First-block obligation for the physical player who does not own the
empty-root move on an even carrier.  A nonterminal exit must again have even
residual order. -/
def EvenNonmoverFirstBlockProperty (G : SimpleGraph V) : Prop :=
  ∀ (U : Finset V) (turn : Bool), U.Nonempty → Even U.card →
    EvenBlockWins G (!turn) U.card
      (fun t ↦ t = emptyRoot t.untouched turn ∧ Even t.untouched.card)
      (emptyRoot U turn)

/-- First-block obligation for the physical player who does not own the
empty-root move on an odd carrier containing the isolated dummy.  At an exit,
either the residual order is even (so the even-carrier induction takes over)
or the dummy remains untouched (so the odd-isolated induction repeats). -/
def OddDummyNonmoverFirstBlockProperty (G : SimpleGraph V) (d : V) : Prop :=
  ∀ (U : Finset V) (turn : Bool), d ∈ U → Odd U.card →
    EvenBlockWins G (!turn) U.card
      (fun t ↦ t = emptyRoot t.untouched turn ∧
        (Even t.untouched.card ∨ d ∈ t.untouched))
      (emptyRoot U turn)

omit [Fintype V] in
/-- The mover first-block property iterates over successive empty-queue
blocks and gives a full even strategy on every empty root. -/
theorem mover_evenWins_emptyRoot
    {G : SimpleGraph V} (hblock : MoverFirstBlockProperty G) :
    ∀ (U : Finset V) (turn : Bool), EvenWins G turn (emptyRoot U turn) := by
  intro U turn
  induction hcard : U.card using Nat.strong_induction_on generalizing U turn with
  | h n ih =>
      by_cases hU : U = ∅
      · subst U
        exact EvenWins.terminal (emptyRoot ∅ turn)
          (by simp [Terminal, emptyRoot]) (by simp [emptyRoot])
      · have hne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
        apply (hblock U turn hne).toEvenWins
        intro t hsmall ht
        rw [ht]
        exact ih t.untouched.card (by simpa [hcard] using hsmall)
          t.untouched turn rfl

omit [Fintype V] in
/-- The even-carrier nonmover first-block property iterates without needing
a dummy: its exit parity is precisely the induction invariant. -/
theorem even_nonmover_evenWins_emptyRoot
    {G : SimpleGraph V} (hblock : EvenNonmoverFirstBlockProperty G) :
    ∀ (U : Finset V) (turn : Bool), Even U.card →
      EvenWins G (!turn) (emptyRoot U turn) := by
  intro U turn hEven
  induction hcard : U.card using Nat.strong_induction_on generalizing U turn with
  | h n ih =>
      by_cases hU : U = ∅
      · subst U
        exact EvenWins.terminal (emptyRoot ∅ turn)
          (by simp [Terminal, emptyRoot]) (by simp [emptyRoot])
      · have hne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
        apply (hblock U turn hne hEven).toEvenWins
        intro t hsmall ht
        rcases ht with ⟨ht, hResidualEven⟩
        rw [ht]
        exact ih t.untouched.card (by simpa [hcard] using hsmall)
          t.untouched turn hResidualEven rfl

omit [Fintype V] in
/-- Mutual parity handoff for the nonmover.  Odd isolated-dummy exits recurse
when the dummy remains, and hand off to the independent even-carrier theorem
when the residual order is even. -/
theorem oddDummy_nonmover_evenWins_emptyRoot
    {G : SimpleGraph V} {d : V}
    (hEvenBlock : EvenNonmoverFirstBlockProperty G)
    (hOddBlock : OddDummyNonmoverFirstBlockProperty G d) :
    ∀ (U : Finset V) (turn : Bool), d ∈ U → Odd U.card →
      EvenWins G (!turn) (emptyRoot U turn) := by
  have hEvenRoot := even_nonmover_evenWins_emptyRoot hEvenBlock
  intro U turn hdU hOdd
  induction hcard : U.card using Nat.strong_induction_on generalizing U turn with
  | h n ih =>
      apply (hOddBlock U turn hdU hOdd).toEvenWins
      intro t hsmall ht
      rcases ht with ⟨ht, hEven | hdResidual⟩
      · rw [ht]
        exact hEvenRoot _ turn hEven
      · rcases Nat.even_or_odd t.untouched.card with hEven | hOddResidual
        · rw [ht]
          exact hEvenRoot _ turn hEven
        · rw [ht]
          exact ih t.untouched.card (by simpa [hcard] using hsmall)
            t.untouched turn hdResidual hOddResidual rfl

/-- Abstract conditional first-block reduction of isolated-dummy FIFO
linking.  The global both-seat theorem is a formal consequence of the three
stated local block obligations.  This implication remains useful as a
bookkeeping boundary even though `MoverFirstBlockProperty` is too strong in
general. -/
theorem fifoLinking_of_firstBlockProperties
    {G : SimpleGraph V} {d : V} (_hd : IsDummy G d)
    (hMover : MoverFirstBlockProperty G)
    (hEvenBlock : EvenNonmoverFirstBlockProperty G)
    (hOddBlock : OddDummyNonmoverFirstBlockProperty G d) :
    ∀ seat, EvenWins G seat (initial (V := V)) := by
  intro seat
  cases seat with
  | false =>
      simpa [initial, emptyRoot] using
        mover_evenWins_emptyRoot hMover (Finset.univ : Finset V) false
  | true =>
      rcases Nat.even_or_odd (Fintype.card V) with hEven | hOdd
      · simpa [initial, emptyRoot, Finset.card_univ] using
          even_nonmover_evenWins_emptyRoot hEvenBlock
            (Finset.univ : Finset V) false hEven
      · simpa [initial, emptyRoot, Finset.card_univ] using
          oddDummy_nonmover_evenWins_emptyRoot hEvenBlock hOddBlock
            (Finset.univ : Finset V) false (by simp) hOdd

end

end Ogdoad.Fifo
