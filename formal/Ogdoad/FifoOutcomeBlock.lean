import Ogdoad.FifoBlockInduction
import Ogdoad.FifoOutcome

/-!
# Outcome-valued first-return blocks

A scalar first-block interface may stop only at score zero.  That loses the
relevant information after the isolated dummy has been spent: a score-one
exit can still be winning, depending on the two-seat outcome sheet of the
residual no-dummy game.

`EvenContinuationBlockWins` is the exact stopped strategy tree in which an
exit carries an arbitrary continuation predicate and no scalar restriction.
Splicing is sound.  Specializing the exit predicate to the actual winning
region after the dummy has been consumed gives an exact equivalence with the
original full winning strategy.  Thus carrying the complete outcome sheet is
sound, but by itself is not an induction theorem: the resulting stopped
obligation is precisely as strong as the original game unless one proves an
independent local description of the favorable exits.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A stopped even strategy whose exits may carry arbitrary score debt.
Unlike `EvenBlockWins`, the exit constructor does not require score zero;
the continuation predicate owns the complete residual obligation. -/
inductive EvenContinuationBlockWins (G : SimpleGraph V) (seat : Bool)
    (bound : Nat) (Exit : State V → Prop) : State V → Prop
  | terminal (s : State V) (hterminal : Terminal s) (hscore : s.score = 0) :
      EvenContinuationBlockWins G seat bound Exit s
  | exit (s : State V) (hsmaller : s.untouched.card < bound)
      (hexit : Exit s) :
      EvenContinuationBlockWins G seat bound Exit s
  | choose (s : State V) (hseat : s.toMove = seat)
      (m : Move V) (s' : State V) (hstep : step G s m = some s')
      (hwin : EvenContinuationBlockWins G seat bound Exit s') :
      EvenContinuationBlockWins G seat bound Exit s
  | answer (s : State V) (hseat : s.toMove ≠ seat)
      (hasMove : ∃ m s', step G s m = some s')
      (hwin : ∀ m s', step G s m = some s' →
        EvenContinuationBlockWins G seat bound Exit s') :
      EvenContinuationBlockWins G seat bound Exit s

omit [Fintype V] in
/-- Splice a full winning strategy into every outcome-valued block exit. -/
theorem EvenContinuationBlockWins.toEvenWins
    {G : SimpleGraph V} {seat : Bool} {bound : Nat}
    {Exit : State V → Prop} {s : State V}
    (h : EvenContinuationBlockWins G seat bound Exit s)
    (hcont : ∀ t, t.untouched.card < bound → Exit t →
      EvenWins G seat t) :
    EvenWins G seat s := by
  induction h with
  | terminal s ht hs => exact EvenWins.terminal s ht hs
  | exit s hsmall hexit => exact hcont s hsmall hexit
  | choose s hseat m s' hstep _ ih =>
      exact EvenWins.choose s hseat m s' hstep ih
  | answer s hseat hasMove _ ih =>
      exact EvenWins.answer s hseat hasMove ih

omit [Fintype V] in
/-- A legal move never adds an untouched vertex. -/
theorem step_untouched_subset {G : SimpleGraph V} {s t : State V}
    {m : Move V} (hstep : step G s m = some t) :
    t.untouched ⊆ s.untouched := by
  cases m with
  | «open» v =>
      simp only [step] at hstep
      split at hstep
      · cases hstep
        exact Finset.erase_subset v s.untouched
      · contradiction
  | close =>
      simp only [step] at hstep
      split at hstep
      · contradiction
      · split at hstep
        · contradiction
        · cases hstep
          exact Finset.Subset.rfl
  | pass =>
      simp only [step] at hstep
      split at hstep
      · cases hstep
        exact Finset.Subset.rfl
      · contradiction

/-- A first-return exit after the distinguished dummy has been consumed,
carrying the actual full winning continuation rather than only a scalar or
carrier-parity summary. -/
def ConsumedWinningExit (G : SimpleGraph V) (seat : Bool) (d : V)
    (s : State V) : Prop :=
  s.queue = [] ∧ d ∉ s.untouched ∧ EvenWins G seat s

omit [Fintype V] in
/-- Any full winning strategy may be truncated when it first reaches an
empty queue after consuming `d`.  The strict-cardinality certificate follows
from monotonicity of the untouched carrier and the loss of `d`.

This direction is the reason the complete residual outcome sheet cannot by
itself simplify the conjecture: the favorable-exit block strategy is already
available whenever, and only because, the full strategy is available. -/
theorem EvenWins.toConsumedWinningBlock
    {G : SimpleGraph V} {seat turn : Bool} {d : V} {U : Finset V}
    (hdU : d ∈ U) :
    EvenWins G seat (emptyRoot U turn) →
      EvenContinuationBlockWins G seat U.card
        (ConsumedWinningExit G seat d) (emptyRoot U turn) := by
  intro hroot
  have build : ∀ {s : State V}, EvenWins G seat s → s.untouched ⊆ U →
      EvenContinuationBlockWins G seat U.card
        (ConsumedWinningExit G seat d) s := by
    intro s hwin
    induction hwin with
    | terminal s hterminal hscore =>
        intro _
        exact EvenContinuationBlockWins.terminal s hterminal hscore
    | choose s hseat m s' hstep hchild ih =>
        intro hsub
        by_cases hexit : s.queue = [] ∧ d ∉ s.untouched
        · have hproper : s.untouched ⊂ U := by
            rw [Finset.ssubset_iff_subset_ne]
            exact ⟨hsub, fun hEq ↦ hexit.2 (hEq ▸ hdU)⟩
          exact EvenContinuationBlockWins.exit s
            (Finset.card_lt_card hproper)
            ⟨hexit.1, hexit.2,
              EvenWins.choose s hseat m s' hstep hchild⟩
        · exact EvenContinuationBlockWins.choose s hseat m s' hstep
            (ih (Finset.Subset.trans (step_untouched_subset hstep) hsub))
    | answer s hseat hasMove hchildren ih =>
        intro hsub
        by_cases hexit : s.queue = [] ∧ d ∉ s.untouched
        · have hproper : s.untouched ⊂ U := by
            rw [Finset.ssubset_iff_subset_ne]
            exact ⟨hsub, fun hEq ↦ hexit.2 (hEq ▸ hdU)⟩
          exact EvenContinuationBlockWins.exit s
            (Finset.card_lt_card hproper)
            ⟨hexit.1, hexit.2,
              EvenWins.answer s hseat hasMove hchildren⟩
        · exact EvenContinuationBlockWins.answer s hseat hasMove
            (fun m t hstep ↦
              ih m t hstep
                (Finset.Subset.trans (step_untouched_subset hstep) hsub))
  exact build hroot Finset.Subset.rfl

omit [Fintype V] in
/-- Exact boundary of the outcome-valued first-block reformulation: stopping
after consuming the dummy at a favorable complete-outcome exit is equivalent
to the original full winning assertion. -/
theorem consumedWinningBlock_iff_evenWins
    {G : SimpleGraph V} {seat turn : Bool} {d : V} {U : Finset V}
    (hdU : d ∈ U) :
    EvenContinuationBlockWins G seat U.card
        (ConsumedWinningExit G seat d) (emptyRoot U turn) ↔
      EvenWins G seat (emptyRoot U turn) := by
  constructor
  · intro hblock
    exact hblock.toEvenWins (fun _ _ hexit ↦ hexit.2.2)
  · exact EvenWins.toConsumedWinningBlock hdU

end

end Ogdoad.Fifo
