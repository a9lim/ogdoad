import Ogdoad.FifoNormalization

/-!
# Type-valued FIFO strategy trees

`EvenWins` and `OddWins` deliberately live in `Prop`: they state that a
winning strategy exists.  Proof irrelevance therefore makes two proofs of
`OddWins G seat s` indistinguishable, so such a proof cannot safely index an
object intended to retain one particular policy.

`OddStrategy` is the corresponding data-carrying tree in `Type`.  Its
constructors have the same existential/universal shape as `OddWins`, but two
different selected moves remain different data.  The erasure theorem and its
converse up to `Nonempty` show that no game-semantic strength is changed.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- One explicit strategy tree for the player outside `seat` to force an odd
terminal score.  Unlike `OddWins`, this lives in `Type`, so it can be used as
an observable index for a fixed-policy response space. -/
inductive OddStrategy (G : SimpleGraph V) (seat : Bool) : State V → Type u
  | terminal (s : State V) (hterminal : Terminal s) (hscore : s.score ≠ 0) :
      OddStrategy G seat s
  | choose (s : State V) (hseat : s.toMove ≠ seat)
      (m : Move V) (s' : State V) (hstep : step G s m = some s')
      (tail : OddStrategy G seat s') : OddStrategy G seat s
  | answer (s : State V) (hseat : s.toMove = seat)
      (hasMove : ∃ m s', step G s m = some s')
      (children : ∀ m s', step G s m = some s' → OddStrategy G seat s') :
      OddStrategy G seat s

omit [Fintype V] in
/-- Forget the identity of an explicit strategy, retaining only the
proposition that an odd-forcing strategy exists. -/
theorem OddStrategy.toOddWins {G : SimpleGraph V} {seat : Bool} {s : State V} :
    OddStrategy G seat s → OddWins G seat s
  | .terminal s ht hs => OddWins.terminal s ht hs
  | .choose s hseat m s' hstep tail =>
      OddWins.choose s hseat m s' hstep tail.toOddWins
  | .answer s hseat hasMove children =>
      OddWins.answer s hseat hasMove fun m s' hstep =>
        (children m s' hstep).toOddWins

omit [Fintype V] in
/-- Every propositional odd win has an explicit Type-valued representative.
The result is stated in `Prop` as `Nonempty`, allowing elimination of the
proof-irrelevant `OddWins` witness while preserving a data-carrying tree. -/
theorem OddWins.nonempty_oddStrategy
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (h : OddWins G seat s) : Nonempty (OddStrategy G seat s) := by
  induction h with
  | terminal s ht hs =>
      exact ⟨OddStrategy.terminal s ht hs⟩
  | choose s hseat m s' hstep _ ih =>
      obtain ⟨tail⟩ := ih
      exact ⟨OddStrategy.choose s hseat m s' hstep tail⟩
  | answer s hseat hasMove children ih =>
      let children' : ∀ m s', step G s m = some s' → OddStrategy G seat s' :=
        fun m s' hstep => Classical.choice (ih m s' hstep)
      exact ⟨OddStrategy.answer s hseat hasMove children'⟩

omit [Fintype V] in
/-- The Type-valued and proposition-valued odd-strategy semantics agree after
forgetting the identity of the chosen policy. -/
theorem nonempty_oddStrategy_iff_oddWins
    {G : SimpleGraph V} {seat : Bool} {s : State V} :
    Nonempty (OddStrategy G seat s) ↔ OddWins G seat s := by
  constructor
  · rintro ⟨h⟩
    exact h.toOddWins
  · exact OddWins.nonempty_oddStrategy

end

end Ogdoad.Fifo
