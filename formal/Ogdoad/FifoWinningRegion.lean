import Ogdoad.FifoAffine

/-!
# Choice-saturated affine response spaces

`AffineResponseMoment` retains one explicit Type-valued `OddStrategy`.  This
module formalizes the complementary Bellman relaxation: at every state, range
over every odd-winning attacker choice and take their joint affine hull.

The relaxation is exact but does not solve FIFO linking.  It is precisely the
affine hull of the union of all fixed-strategy response spaces.  Every one of
its moments still evaluates to the odd terminal defect for the graph defining
the winning region.  Consequently, asking it to contain zero at the initial
root is equivalent to the original even-win statement (vacuously on an
even-winning root and impossibly on an odd-winning root).

Thus choice saturation can remove fixed-policy incompatibility at one state,
but any useful contraction theorem must add genuinely causal information; the
Bellman relaxation alone is a semantic reformulation.
-/

namespace Ogdoad.Fifo

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Affine response moments saturated across every odd-winning choice at the
same state.  The `OddWins` index records membership in the scalar Bellman
winning region; proof irrelevance deliberately identifies different choices.
-/
inductive WinningRegionAffineMoment (G : SimpleGraph V) (seat : Bool) :
    {s : State V} → OddWins G seat s → EdgeVector V → Prop
  | terminal (s : State V) (ht : Terminal s) (hs : s.score ≠ 0) :
      WinningRegionAffineMoment G seat (OddWins.terminal s ht hs) 0
  | choose {s s' : State V} {hseat : s.toMove ≠ seat}
      {m : Move V} {hstep : step G s m = some s'}
      {hchild : OddWins G seat s'} {z : EdgeVector V}
      (tail : WinningRegionAffineMoment G seat hchild z) :
      WinningRegionAffineMoment G seat
        (OddWins.choose s hseat m s' hstep hchild) (moveLiveStar s m + z)
  | answerChild {s s' : State V} {hseat : s.toMove = seat}
      {hasMove : ∃ m u, step G s m = some u}
      {hchildren : ∀ m u, step G s m = some u → OddWins G seat u}
      {m : Move V} {hstep : step G s m = some s'} {z : EdgeVector V}
      (tail : WinningRegionAffineMoment G seat (hchildren m s' hstep) z) :
      WinningRegionAffineMoment G seat
        (OddWins.answer s hseat hasMove hchildren) (moveLiveStar s m + z)
  | ternary {s : State V} {h : OddWins G seat s}
      {x y z : EdgeVector V}
      (hx : WinningRegionAffineMoment G seat h x)
      (hy : WinningRegionAffineMoment G seat h y)
      (hz : WinningRegionAffineMoment G seat h z) :
      WinningRegionAffineMoment G seat h (x + y + z)

omit [Fintype V] in
/-- All odd-winning witnesses at one state induce the same saturated response
relation. -/
theorem winningRegionAffineMoment_proof_irrelevant
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (h₁ h₂ : OddWins G seat s) (z : EdgeVector V) :
    WinningRegionAffineMoment G seat h₁ z ↔
      WinningRegionAffineMoment G seat h₂ z := by
  have heq : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

omit [Fintype V] in
/-- Every moment from one fixed Type-valued strategy belongs to the
choice-saturated winning-region affine space. -/
theorem AffineResponseMoment.toWinningRegion
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {strategy : OddStrategy G seat s} {z : EdgeVector V}
    (h : AffineResponseMoment G seat strategy z) :
    WinningRegionAffineMoment G seat strategy.toOddWins z := by
  induction h with
  | terminal s ht hs => exact WinningRegionAffineMoment.terminal s ht hs
  | @choose s s' hseat m hstep hchild z tail ih =>
      have hraw := WinningRegionAffineMoment.choose
        (hseat := hseat) (hstep := hstep) ih
      exact (winningRegionAffineMoment_proof_irrelevant _ _ _).mp hraw
  | @answerChild s s' hseat hasMove hchildren m hstep z tail ih =>
      have hraw := WinningRegionAffineMoment.answerChild
        (hseat := hseat) (hasMove := hasMove) (hchildren := fun m u hstep ↦
          (hchildren m u hstep).toOddWins) (hstep := hstep) ih
      exact (winningRegionAffineMoment_proof_irrelevant _ _ _).mp hraw
  | ternary hx hy hz ihx ihy ihz =>
      exact WinningRegionAffineMoment.ternary ihx ihy ihz

/-- The affine hull of the union of all fixed-strategy response spaces at a
state. -/
inductive FixedStrategyAffineHull (G : SimpleGraph V) (seat : Bool)
    (s : State V) : EdgeVector V → Prop
  | generator {strategy : OddStrategy G seat s} {z : EdgeVector V}
      (hz : AffineResponseMoment G seat strategy z) :
      FixedStrategyAffineHull G seat s z
  | ternary {x y z : EdgeVector V}
      (hx : FixedStrategyAffineHull G seat s x)
      (hy : FixedStrategyAffineHull G seat s y)
      (hz : FixedStrategyAffineHull G seat s z) :
      FixedStrategyAffineHull G seat s (x + y + z)

omit [Fintype V] in
theorem FixedStrategyAffineHull.toWinningRegion
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {z : EdgeVector V} (hroot : OddWins G seat s)
    (hz : FixedStrategyAffineHull G seat s z) :
    WinningRegionAffineMoment G seat hroot z := by
  induction hz with
  | generator hz =>
      exact (winningRegionAffineMoment_proof_irrelevant _ _ _).mp
        hz.toWinningRegion
  | ternary hx hy hz ihx ihy ihz =>
      exact WinningRegionAffineMoment.ternary ihx ihy ihz

omit [Fintype V] in
private theorem FixedStrategyAffineHull.lift_choose
    {G : SimpleGraph V} {seat : Bool} {s s' : State V}
    (hseat : s.toMove ≠ seat) (m : Move V)
    (hstep : step G s m = some s') {z : EdgeVector V}
    (hz : FixedStrategyAffineHull G seat s' z) :
    FixedStrategyAffineHull G seat s (moveLiveStar s m + z) := by
  induction hz with
  | @generator strategy z hz =>
      exact FixedStrategyAffineHull.generator
        (AffineResponseMoment.choose (hseat := hseat) (hstep := hstep) hz)
  | @ternary x y z hx hy hz ihx ihy ihz =>
      have hsum := FixedStrategyAffineHull.ternary ihx ihy ihz
      convert hsum using 1
      ext e
      simp only [Finsupp.add_apply]
      have hself : moveLiveStar s m e + moveLiveStar s m e = 0 :=
        CharTwo.add_self_eq_zero _
      have htriple :
          moveLiveStar s m e + moveLiveStar s m e + moveLiveStar s m e =
            moveLiveStar s m e := by rw [hself, zero_add]
      symm
      calc
        (moveLiveStar s m e + x e) +
              (moveLiveStar s m e + y e) +
                (moveLiveStar s m e + z e) =
            (moveLiveStar s m e + moveLiveStar s m e +
              moveLiveStar s m e) + (x e + y e + z e) := by abel
        _ = moveLiveStar s m e + (x e + y e + z e) := by rw [htriple]
        _ = moveLiveStar s m e + (x e + y e + z e) := by abel

omit [Fintype V] in
private theorem FixedStrategyAffineHull.lift_answer
    {G : SimpleGraph V} {seat : Bool} {s s' : State V}
    (hseat : s.toMove = seat)
    (hasMove : ∃ m u, step G s m = some u)
    (hchildren : ∀ m u, step G s m = some u → OddWins G seat u)
    (m : Move V) (hstep : step G s m = some s')
    {z : EdgeVector V}
    (hz : FixedStrategyAffineHull G seat s' z) :
    FixedStrategyAffineHull G seat s (moveLiveStar s m + z) := by
  classical
  induction hz with
  | @generator strategy z hz =>
      let children : ∀ m₀ u, step G s m₀ = some u →
          OddStrategy G seat u := fun m₀ u hu ↦
        if hm : m₀ = m then
          if hs' : u = s' then
            hs' ▸ strategy
          else
            Classical.choice ((hchildren m₀ u hu).nonempty_oddStrategy)
        else
          Classical.choice ((hchildren m₀ u hu).nonempty_oddStrategy)
      have hselected : children m s' hstep = strategy := by
        simp [children]
      have htail : AffineResponseMoment G seat (children m s' hstep) z := by
        simpa [hselected] using hz
      exact FixedStrategyAffineHull.generator
        (AffineResponseMoment.answerChild
          (hseat := hseat) (hasMove := hasMove)
          (hchildren := children) (hstep := hstep) htail)
  | @ternary x y z hx hy hz ihx ihy ihz =>
      have hsum := FixedStrategyAffineHull.ternary ihx ihy ihz
      convert hsum using 1
      ext e
      simp only [Finsupp.add_apply]
      have hself : moveLiveStar s m e + moveLiveStar s m e = 0 :=
        CharTwo.add_self_eq_zero _
      have htriple :
          moveLiveStar s m e + moveLiveStar s m e + moveLiveStar s m e =
            moveLiveStar s m e := by rw [hself, zero_add]
      symm
      calc
        (moveLiveStar s m e + x e) +
              (moveLiveStar s m e + y e) +
                (moveLiveStar s m e + z e) =
            (moveLiveStar s m e + moveLiveStar s m e +
              moveLiveStar s m e) + (x e + y e + z e) := by abel
        _ = moveLiveStar s m e + (x e + y e + z e) := by rw [htriple]
        _ = moveLiveStar s m e + (x e + y e + z e) := by abel

omit [Fintype V] in
/-- The choice-saturated relation is exactly the affine hull of the union of
all fixed Type-valued odd-strategy response spaces at the state. -/
theorem winningRegionAffineMoment_iff_fixedStrategyAffineHull
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (hroot : OddWins G seat s) (z : EdgeVector V) :
    WinningRegionAffineMoment G seat hroot z ↔
      FixedStrategyAffineHull G seat s z := by
  constructor
  · intro hz
    induction hz with
    | terminal s ht hs =>
        exact FixedStrategyAffineHull.generator
          (AffineResponseMoment.terminal s ht hs)
    | @choose s s' hseat m hstep hchild z tail ih =>
        exact ih.lift_choose hseat m hstep
    | @answerChild s s' hseat hasMove hchildren m hstep z tail ih =>
        exact ih.lift_answer hseat hasMove hchildren m hstep
    | ternary hx hy hz ihx ihy ihz =>
        exact FixedStrategyAffineHull.ternary ihx ihy ihz
  · exact FixedStrategyAffineHull.toWinningRegion hroot

omit [Fintype V] in
/-- Choice saturation preserves scalar soundness: the chosen graph evaluates
every resulting moment to the same odd terminal defect. -/
theorem WinningRegionAffineMoment.graphEvaluation_eq
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {h : OddWins G seat s} {z : EdgeVector V}
    (hr : WinningRegionAffineMoment G seat h z) (hs : WellFormed s) :
    graphEvaluation G z = 1 + potential G s := by
  induction hr with
  | terminal s ht hscore =>
      have hs1 : s.score = 1 := zmod2_eq_one_of_ne_zero _ hscore
      rw [terminal_potential ht, hs1]
      simp [CharTwo.add_self_eq_zero]
  | @choose s s' hseat m hstep hchild z tail ih =>
      have hs' : WellFormed s' := wellFormed_step hs hstep
      have hpot := step_potential_eq_add_liveDegree hstep
      have heval := graphEvaluation_moveLiveStar G s m hs
      rw [map_add, heval, ih hs', hpot]
      cases m with
      | «open» v =>
          simp only
          calc
            liveDegree G s v + (1 + (potential G s + liveDegree G s v)) =
                (liveDegree G s v + liveDegree G s v) +
                  (1 + potential G s) := by abel
            _ = 1 + potential G s := by
              rw [CharTwo.add_self_eq_zero, zero_add]
      | close => simp
      | pass => simp
  | @answerChild s s' hseat hasMove hchildren m hstep z tail ih =>
      have hs' : WellFormed s' := wellFormed_step hs hstep
      have hpot := step_potential_eq_add_liveDegree hstep
      have heval := graphEvaluation_moveLiveStar G s m hs
      rw [map_add, heval, ih hs', hpot]
      cases m with
      | «open» v =>
          simp only
          calc
            liveDegree G s v + (1 + (potential G s + liveDegree G s v)) =
                (liveDegree G s v + liveDegree G s v) +
                  (1 + potential G s) := by abel
            _ = 1 + potential G s := by
              rw [CharTwo.add_self_eq_zero, zero_add]
      | close => simp
      | pass => simp
  | @ternary s h x y z hx hy hz ihx ihy ihz =>
      rw [map_add, map_add, ihx hs, ihy hs, ihz hs]
      rw [CharTwo.add_self_eq_zero, zero_add]

/-- At an odd-winning initial root even the choice-saturated affine space
excludes zero. -/
theorem no_zero_winningRegionAffineMoment_initial
    {G : SimpleGraph V} {seat : Bool}
    {h : OddWins G seat (initial (V := V))} :
    ¬WinningRegionAffineMoment G seat h 0 := by
  intro hz
  have heval := hz.graphEvaluation_eq wellFormed_initial
  simp [potential, initial, queueCut] at heval

/-- Root zero in the choice-saturated space is exactly the original winner
statement.  Hence this saturation is a reformulation, not a contraction
theorem. -/
theorem evenWins_initial_iff_all_winningRegion_zero
    (G : SimpleGraph V) (seat : Bool) :
    EvenWins G seat (initial (V := V)) ↔
      ∀ h : OddWins G seat (initial (V := V)),
        WinningRegionAffineMoment G seat h 0 := by
  rw [evenWins_iff_not_oddWins]
  constructor
  · intro hno hodd
    exact False.elim (hno hodd)
  · intro hall hodd
    exact no_zero_winningRegionAffineMoment_initial (hall hodd)

end

end Ogdoad.Fifo
