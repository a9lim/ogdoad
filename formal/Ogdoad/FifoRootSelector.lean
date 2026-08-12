import Ogdoad.FifoNormalization

/-!
# The universal half of the FIFO root selector

On an even real carrier, handshaking makes the same-degree reply class of
every real opener odd, hence nonempty.  When the even player has the first
seat, the position after the first `OPEN` belongs to the opponent.  Therefore
an even-winning strategy contains every legal second `OPEN`, in particular a
same-degree real reply.

This is the universal (first-seat) half only.  For the second seat the
post-`OPEN` position is controlled by the even player, and proving that one
of its existential winning replies lies in the same-degree class is the
still-open root-selector problem.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Public state immediately after a real first `OPEN x` from the board with
real carrier `R` and one additional vertex `d`.  The graph is irrelevant to
this state constructor. -/
def afterFirstRealOpen (R : Finset V) (d x : V) : State V where
  untouched := insert d (R.erase x)
  queue := [x]
  ko := true
  toMove := true
  score := 0

/-- Public state after the initial `OPEN x; OPEN y` pair. -/
def afterTwoRealOpens (R : Finset V) (d x y : V) : State V where
  untouched := (insert d (R.erase x)).erase y
  queue := [x, y]
  ko := false
  toMove := false
  score := 0

omit [Fintype V] in
/-- Every same-degree real mate is a legal second `OPEN` at the root
checkpoint. -/
theorem afterFirstRealOpen_step_sameDegreeMate
    (G : SimpleGraph V) (R : Finset V) (d x y : V)
    (hy : y ∈ sameDegreeMates G R x) :
    step G (afterFirstRealOpen R d x) (.open y) =
      some (afterTwoRealOpens R d x y) := by
  have hyErase : y ∈ R.erase x := (Finset.mem_filter.mp hy).1
  simp [step, afterFirstRealOpen, afterTwoRealOpens, hyErase]

omit [Fintype V] in
/-- First-seat root selector.  If the even player is player `false`, then
after the initial real `OPEN x` the opponent controls the node.  Hence every
legal same-degree reply is even-winning; even cardinality of `R` supplies at
least one such reply. -/
theorem firstSeat_evenWins_has_sameDegree_open
    (G : SimpleGraph V) (R : Finset V) (d x : V)
    (hx : x ∈ R) (hR : (R.card : ZMod 2) = 0)
    (hwin : EvenWins G false (afterFirstRealOpen R d x)) :
    ∃ y t, y ∈ sameDegreeMates G R x ∧
      step G (afterFirstRealOpen R d x) (.open y) = some t ∧
      EvenWins G false t := by
  have hodd := sameDegreeMates_card_eq_one G R x hx hR
  have hnonempty : (sameDegreeMates G R x).Nonempty := by
    by_contra hempty
    have hzero : sameDegreeMates G R x = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hzero] at hodd
    norm_num at hodd
  obtain ⟨y, hy⟩ := hnonempty
  let t := afterTwoRealOpens R d x y
  have hstep : step G (afterFirstRealOpen R d x) (.open y) = some t :=
    afterFirstRealOpen_step_sameDegreeMate G R d x y hy
  refine ⟨y, t, hy, hstep, ?_⟩
  exact hwin.answer_child (by simp [afterFirstRealOpen]) hstep

omit [Fintype V] in
/-- Determinacy isolates the nontrivial second-seat selector exactly.  Its
failure is not a numerical condition: it is a simultaneous family of
odd-forcing strategy trees at every same-degree child. -/
theorem exists_secondSeat_even_sameDegree_iff_not_all_odd
    (G : SimpleGraph V) (R : Finset V) (d x : V) :
    (∃ y, y ∈ sameDegreeMates G R x ∧
        EvenWins G true (afterTwoRealOpens R d x y)) ↔
      ¬(∀ y, y ∈ sameDegreeMates G R x →
        OddWins G true (afterTwoRealOpens R d x y)) := by
  constructor
  · rintro ⟨y, hy, heven⟩ hall
    exact heven.not_oddWins (hall y hy)
  · intro hnot
    by_contra hex
    push Not at hex
    apply hnot
    intro y hy
    exact oddWins_of_not_evenWins G true _ (hex y hy)

omit [Fintype V] in
/-- Normal form for a failure of the existential second-seat selector.  A
winning move still exists at the post-`OPEN x` node, but it must be a second
`OPEN` outside the same-degree real class; ko excludes `CLOSE`, and the
nonempty untouched set excludes `PASS`. -/
theorem secondSeat_selector_failure_chooses_outside
    (G : SimpleGraph V) (R : Finset V) (d x : V)
    (hwin : EvenWins G true (afterFirstRealOpen R d x))
    (hbad : ∀ y, y ∈ sameDegreeMates G R x →
      ¬EvenWins G true (afterTwoRealOpens R d x y)) :
    ∃ z, z ∈ insert d (R.erase x) ∧
      z ∉ sameDegreeMates G R x ∧
      EvenWins G true (afterTwoRealOpens R d x z) := by
  cases hwin with
  | terminal _ hterminal _ =>
      simp [Terminal, afterFirstRealOpen] at hterminal
  | answer _ hseat _ _ =>
      exact False.elim (hseat rfl)
  | choose _ _ m t hstep hchild =>
      cases m with
      | close => simp [step, afterFirstRealOpen] at hstep
      | pass => simp [step, afterFirstRealOpen] at hstep
      | «open» z =>
          have hz : z ∈ insert d (R.erase x) := by
            simp only [step, afterFirstRealOpen] at hstep
            split at hstep
            · assumption
            · contradiction
          have ht : t = afterTwoRealOpens R d x z := by
            simp [step, afterFirstRealOpen, hz] at hstep
            exact hstep.symm
          subst t
          refine ⟨z, hz, ?_, hchild⟩
          intro hzMate
          exact hbad z hzMate hchild

end

end Ogdoad.Fifo
