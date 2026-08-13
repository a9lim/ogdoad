import Mathlib

/-!
# The four FIFO outcome classes are not a contextual algebra

This file isolates an abstract obstruction to treating the four-valued FIFO
outcome sheet as a compositional game value.

Write `M` for the proposition that the current mover can force score zero
when designated Even, and `N` for the corresponding proposition for the
current nonmover.  At a finite alternating choice node the exact Bellman
recurrence is

`M = exists child, N child`,  `N = forall child, M child`.

A forced score-neutral move exchanges `M` and `N`, so two adjacent forced
neutral moves are harmless.  A FIFO ko wall is different: dummy OPEN, one
real choice, dummy CLOSE.  The real choice has the opposite controller, so
the resulting sheet uses the missing aggregates

`M = forall child, N child`,  `N = exists child, M child`.

The explicit option families below have the same mover-controlled sheet
before this locked neutral pair and different sheets afterward.  Thus the
four outcome classes alone cannot justify dummy deletion or a general
strategy-composition theorem; one must retain option-family and
legality/ancestry data.  This is an abstract no-go result, not a counterexample
to the FIFO linking conjecture.
-/

namespace Ogdoad.FifoOutcomeAlgebra

/-- The mover/nonmover even-winning sheet `(M,N)`. -/
abbrev Sheet := Bool × Bool

/-- Exact Bellman sheet of a node with the given child sheets. -/
def choiceSheet (children : List Sheet) : Sheet :=
  (children.any Prod.snd, children.all Prod.fst)

/-- A forced score-neutral move exchanges the physical mover and nonmover. -/
def forcedNeutral (child : Sheet) : Sheet := (child.2, child.1)

@[simp] theorem forcedNeutral_fst (child : Sheet) :
    (forcedNeutral child).1 = child.2 := rfl

@[simp] theorem forcedNeutral_snd (child : Sheet) :
    (forcedNeutral child).2 = child.1 := rfl

/-- Two adjacent forced neutral moves are exactly sheet-neutral. -/
theorem forcedNeutral_twice (child : Sheet) :
    forcedNeutral (forcedNeutral child) = child := by
  rcases child with ⟨m, n⟩
  rfl

/-- Dummy OPEN, one real choice, and dummy CLOSE.  Applying the two forced
coordinate exchanges around the ordinary choice reverses the controller of
the sandwiched option family. -/
def lockedNeutralPair (children : List Sheet) : Sheet :=
  (children.all Prod.snd, children.any Prod.fst)

/-- The locked pair uses `forall N` and `exists M`, aggregates absent from the
ordinary four-valued sheet of the original choice node. -/
theorem lockedNeutralPair_eq (children : List Sheet) :
    lockedNeutralPair children =
      (children.all Prod.snd, children.any Prod.fst) := by
  rfl

/-- The four regions of a mover/nonmover sheet. -/
inductive OutcomeClass where
  | bothEven
  | moverControlled
  | nonmoverControlled
  | bothOdd
deriving DecidableEq, Repr

/-- Classify a Boolean winning sheet. -/
def outcomeClass : Sheet → OutcomeClass
  | (true, true) => .bothEven
  | (true, false) => .moverControlled
  | (false, true) => .nonmoverControlled
  | (false, false) => .bothOdd

private def evenLeaf : Sheet := (true, true)
private def oddLeaf : Sheet := (false, false)

/-- The direct two-option node is mover-controlled. -/
private def directChoice : Sheet := choiceSheet [evenLeaf, oddLeaf]

/-- One forced tempo turns it into a nonmover-controlled sheet. -/
private def delayedChoice : Sheet := choiceSheet [directChoice]

/-- Two forced tempi return to the mover-controlled class. -/
private def twiceDelayedChoice : Sheet := choiceSheet [delayedChoice]

theorem directChoice_is_moverControlled :
    outcomeClass directChoice = .moverControlled := by
  rfl

theorem twiceDelayedChoice_is_moverControlled :
    outcomeClass twiceDelayedChoice = .moverControlled := by
  rfl

/-- A ko-like locked neutral pair distinguishes two option families having
exactly the same four-valued outcome class before insertion. -/
theorem outcomeClass_not_contextual :
    outcomeClass directChoice = outcomeClass twiceDelayedChoice ∧
    outcomeClass (lockedNeutralPair [evenLeaf, oddLeaf]) =
      .nonmoverControlled ∧
    outcomeClass (lockedNeutralPair [delayedChoice]) =
      .moverControlled := by
  decide

/-- No unary operation on the four outcome classes computes the locked-pair
effect for every finite option family. -/
theorem no_lockedPair_operation_on_outcomeClass :
    ¬∃ op : OutcomeClass → OutcomeClass,
      ∀ children : List Sheet,
        op (outcomeClass (choiceSheet children)) =
          outcomeClass (lockedNeutralPair children) := by
  rintro ⟨op, hop⟩
  have hdirect := hop [evenLeaf, oddLeaf]
  have hdelayed := hop [delayedChoice]
  change op .moverControlled = .nonmoverControlled at hdirect
  change op .moverControlled = .moverControlled at hdelayed
  rw [hdirect] at hdelayed
  exact OutcomeClass.noConfusion hdelayed

end Ogdoad.FifoOutcomeAlgebra
