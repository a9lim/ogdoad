import Ogdoad.FifoCrossDescent

/-!
# Crossed CLOSE descent and its phase obstruction

`FifoCrossDescent` handles two crossed OPEN choices inside one fixed
Type-valued odd strategy.  This module classifies the complementary case in
which both selected attacker moves and both crossed defender replies are
CLOSEs.

Closing a reversed queue cell restores `PublicCellSwap` at strict lower rank
and adds the two front charges to both score sheets.  Equal charges therefore
give the expected score-preserving descent.  Unequal charges instead take a
common score-zero pair to a common score-one pair while CLOSE contributes no
live-star prefix moment.  This is the exact phase escape from an induction
restricted to score-zero pairs.

The removed cell has a universal cut vector whose graph evaluation is one in
the unequal-charge case and whose real-edge projection is nonzero on an
isolated-dummy board.  The two endpoint continuation spaces have equal graph
evaluation, so they cannot absorb that vector by themselves.  A third,
earlier ancestry representative is a sufficient affine repair when its full
prefix-plus-continuation moment equals the endpoint pair.  No theorem below
constructs that earlier hole or proves the required equality; this module
exposes the remaining causal selection obligation rather than solving it.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Closing both entries of the first reversed cell restores `PublicCellSwap`.
The common score changes by the sum of the two front charges. -/
theorem PublicCellSwap.close_cross
    {G : SimpleGraph V} {sA sB aA aB tA tB : State V}
    {x y : V} {q q' : List V}
    (hpublic : PublicCellSwap sA sB)
    (hqA : sA.queue = x :: y :: q)
    (hqB : sB.queue = y :: x :: q')
    (hkoA : sA.ko = false)
    (hAx : step G sA .close = some aA)
    (hAy : step G aA .close = some tA)
    (hBy : step G sB .close = some aB)
    (hBx : step G aB .close = some tB) :
    PublicCellSwap tA tB ∧
      tA.score = sA.score + flip G sA.untouched x +
        flip G sA.untouched y ∧
      tB.score = sB.score + flip G sB.untouched y +
        flip G sB.untouched x := by
  have hkoB : sB.ko = false := by rw [← hpublic.ko, hkoA]
  have haA : aA = {
      untouched := sA.untouched
      queue := y :: q
      ko := false
      toMove := !sA.toMove
      score := sA.score + flip G sA.untouched x } := by
    simp [step, hqA, hkoA] at hAx
    exact hAx.symm
  have haB : aB = {
      untouched := sB.untouched
      queue := x :: q'
      ko := false
      toMove := !sB.toMove
      score := sB.score + flip G sB.untouched y } := by
    simp [step, hqB, hkoB] at hBy
    exact hBy.symm
  subst aA
  subst aB
  simp only [step] at hAy hBx
  simp at hAy hBx
  cases hAy
  cases hBx
  refine ⟨?_, rfl, rfl⟩
  refine {
    untouched := hpublic.untouched
    queue := ?_
    ko := rfl
    toMove := ?_
    score := ?_ }
  · exact CellSwap.tail_of_cell (hqA ▸ hqB ▸ hpublic.queue)
  · simp [hpublic.toMove]
  · rw [hpublic.score, hpublic.untouched]
    abel_nf

omit [Fintype V] in
/-- Unequal first-cell charges toggle the common score sheet after the two
crossed closes. -/
theorem PublicCellSwap.close_cross_score_one_of_unequal
    {G : SimpleGraph V} {sA sB aA aB tA tB : State V}
    {x y : V} {q q' : List V}
    (hpublic : PublicCellSwap sA sB)
    (hqA : sA.queue = x :: y :: q)
    (hqB : sB.queue = y :: x :: q')
    (hkoA : sA.ko = false)
    (hs0 : sA.score = 0)
    (hneq : flip G sA.untouched x ≠ flip G sA.untouched y)
    (hAx : step G sA .close = some aA)
    (hAy : step G aA .close = some tA)
    (hBy : step G sB .close = some aB)
    (hBx : step G aB .close = some tB) :
    PublicCellSwap tA tB ∧ tA.score = 1 ∧ tB.score = 1 := by
  obtain ⟨hcross, hscoreA, hscoreB⟩ :=
    hpublic.close_cross hqA hqB hkoA hAx hAy hBy hBx
  have hsum : flip G sA.untouched x + flip G sA.untouched y = 1 := by
    by_cases hx : flip G sA.untouched x = 0
    · have hy : flip G sA.untouched y = 1 := by
        apply zmod2_eq_one_of_ne_zero
        intro hy0
        exact hneq (hx.trans hy0.symm)
      rw [hx, hy, zero_add]
    · have hx1 := zmod2_eq_one_of_ne_zero _ hx
      have hy0 : flip G sA.untouched y = 0 := by
        by_contra hy
        exact hneq (hx1.trans (zmod2_eq_one_of_ne_zero _ hy).symm)
      rw [hx1, hy0, add_zero]
  refine ⟨hcross, ?_, ?_⟩
  · rw [hscoreA, hs0, zero_add, hsum]
  · rw [hscoreB, hpublic.score.symm, hs0, hpublic.untouched.symm]
    calc
      0 + flip G sA.untouched y + flip G sA.untouched x =
          flip G sA.untouched x + flip G sA.untouched y := by abel
      _ = 1 := hsum

omit [Fintype V] in
/-- Constructor-level crossed CLOSE descent inside one fixed odd strategy.
Both universal replies are CLOSE, both descendant ranks are strict, and the
two CLOSE moves leave the stored live-star prefixes unchanged. -/
theorem StrategyPrefix.crossClose
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    {sA sB aA aB tA tB : State V} {x y : V} {q q' : List V}
    {pA pB : EdgeVector V}
    {hattA : sA.toMove ≠ seat} {hattB : sB.toMove ≠ seat}
    {hAx : step G sA .close = some aA}
    {hBy : step G sB .close = some aB}
    {hdefA : aA.toMove = seat} {hdefB : aB.toMove = seat}
    {hasMoveA : ∃ m u, step G aA m = some u}
    {hasMoveB : ∃ m u, step G aB m = some u}
    {childrenA : ∀ m u, step G aA m = some u → OddStrategy G seat u}
    {childrenB : ∀ m u, step G aB m = some u → OddStrategy G seat u}
    (prefixA : StrategyPrefix G seat hroot
      (OddStrategy.choose sA hattA .close aA hAx
        (OddStrategy.answer aA hdefA hasMoveA childrenA)) pA)
    (prefixB : StrategyPrefix G seat hroot
      (OddStrategy.choose sB hattB .close aB hBy
        (OddStrategy.answer aB hdefB hasMoveB childrenB)) pB)
    (hAy : step G aA .close = some tA)
    (hBx : step G aB .close = some tB)
    (hpublic : PublicCellSwap sA sB)
    (hqA : sA.queue = x :: y :: q)
    (hqB : sB.queue = y :: x :: q')
    (hkoA : sA.ko = false) :
    StrategyPrefix G seat hroot (childrenA .close tA hAy) pA ∧
      StrategyPrefix G seat hroot (childrenB .close tB hBx) pB ∧
      PublicCellSwap tA tB ∧
      rank tA < rank sA ∧ rank tB < rank sB := by
  have prefixA' : StrategyPrefix G seat hroot
      (OddStrategy.answer aA hdefA hasMoveA childrenA)
      (pA + moveLiveStar sA .close) := StrategyPrefix.choose prefixA
  have prefixB' : StrategyPrefix G seat hroot
      (OddStrategy.answer aB hdefB hasMoveB childrenB)
      (pB + moveLiveStar sB .close) := StrategyPrefix.choose prefixB
  have prefixA'' := StrategyPrefix.answer (hstep := hAy) prefixA'
  have prefixB'' := StrategyPrefix.answer (hstep := hBx) prefixB'
  have hcross := hpublic.close_cross hqA hqB hkoA hAx hAy hBy hBx
  refine ⟨?_, ?_, hcross.1, ?_, ?_⟩
  · simpa [moveLiveStar] using prefixA''
  · simpa [moveLiveStar] using prefixB''
  · exact lt_trans (rank_step_lt hAy) (rank_step_lt hAx)
  · exact lt_trans (rank_step_lt hBx) (rank_step_lt hBy)

/-! ## Phase curvature and the necessary earlier affine branch -/

/-- Universal edge vector whose graph evaluation is the sum of the two
charges removed by a crossed CLOSE/CLOSE cell. -/
def closeCellCutVector (U : Finset V) (x y : V) : EdgeVector V :=
  liveStarVector U x + liveStarVector U y

omit [Fintype V] in
theorem graphEvaluation_closeCellCutVector
    (G : SimpleGraph V) (U : Finset V) (x y : V) :
    graphEvaluation G (closeCellCutVector U x y) =
      flip G U x + flip G U y := by
  rw [closeCellCutVector, map_add,
    graphEvaluation_liveStarVector, graphEvaluation_liveStarVector]

omit [Fintype V] in
/-- On an isolated-dummy graph, an unequal-charge crossed cell has a nonzero
real-edge phase defect. -/
theorem closeCellCutVector_projection_ne_zero
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    (U : Finset V) (x y : V)
    (hphase : flip G U x + flip G U y = 1) :
    realEdgeProjection d (closeCellCutVector U x y) ≠ 0 := by
  intro hzero
  have heval := graphEvaluation_eq_zero_of_realEdgeProjection_eq_zero hd hzero
  rw [graphEvaluation_closeCellCutVector, hphase] at heval
  exact one_ne_zero heval

omit [Fintype V] [DecidableEq V] in
/-- Cell swapping preserves the scalar queue cut. -/
theorem CellSwap.queueCut_eq (G : SimpleGraph V) (U : Finset V) :
    ∀ {q q' : List V}, CellSwap q q' →
      queueCut G U q = queueCut G U q' := by
  intro q q' h
  induction h with
  | nil => rfl
  | cell a b tail ih =>
      simp only [queueCut, List.map_cons, List.sum_cons]
      change flip G U a + (flip G U b + queueCut G U _) =
        flip G U b + (flip G U a + queueCut G U _)
      rw [ih]
      abel

omit [Fintype V] [DecidableEq V] in
/-- Public cell-swapped endpoints have equal cut potential. -/
theorem PublicCellSwap.potential_eq
    {G : SimpleGraph V} {s t : State V}
    (h : PublicCellSwap s t) : potential G s = potential G t := by
  rw [potential, potential, h.score, h.untouched,
    h.queue.queueCut_eq]

omit [Fintype V] in
/-- The two endpoint continuation spaces cannot by themselves absorb the
unequal-charge phase defect.  Their difference evaluates to zero because the
cell-swapped endpoints have equal potential, whereas the removed-cell vector
evaluates to one.

This rules out the endpoint-only cross-target equation
`zA + zB = closeCellCutVector U x y` without finite search. -/
theorem closeCross_endpoint_pair_ne_phaseDefect
    {G : SimpleGraph V} {seat : Bool} {sA sB : State V}
    {strategyA : OddStrategy G seat sA}
    {strategyB : OddStrategy G seat sB}
    {zA zB : EdgeVector V} {U : Finset V} {x y : V}
    (hpublic : PublicCellSwap sA sB)
    (hwellA : WellFormed sA) (hwellB : WellFormed sB)
    (hzA : AffineResponseMoment G seat strategyA zA)
    (hzB : AffineResponseMoment G seat strategyB zB)
    (hphase : flip G U x + flip G U y = 1) :
    zA + zB ≠ closeCellCutVector U x y := by
  intro heq
  have hevalA := hzA.graphEvaluation_eq hwellA
  have hevalB := hzB.graphEvaluation_eq hwellB
  have hpot := hpublic.potential_eq (G := G)
  have hleft : graphEvaluation G (zA + zB) = 0 := by
    rw [map_add, hevalA, hevalB, hpot]
    exact CharTwo.add_self_eq_zero _
  have hright : graphEvaluation G (closeCellCutVector U x y) = 1 := by
    rw [graphEvaluation_closeCellCutVector, hphase]
  rw [heq, hright] at hleft
  exact one_ne_zero hleft

omit [Fintype V] in
/-- Exact three-hole sufficient balance for escaping the unequal-charge
CLOSE/CLOSE sheet.  Two descended endpoints contribute an even homogeneous
pair.  An earlier ancestry representative is the minimum possible affine
repair: if it equals that pair, ternary closure gives root zero.

This is conditional: it does not construct the earlier hole or prove the
displayed equality.  The preceding no-go proves that the removed-cell phase
vector cannot replace the earlier affine representative. -/
theorem StrategyPrefix.crossClose_earlier_balance
    {G : SimpleGraph V} {seat : Bool} {root sA sB sE : State V}
    {hroot : OddStrategy G seat root}
    {strategyA : OddStrategy G seat sA}
    {strategyB : OddStrategy G seat sB}
    {strategyE : OddStrategy G seat sE}
    {pA pB pE zA zB zE : EdgeVector V}
    (hpA : StrategyPrefix G seat hroot strategyA pA)
    (hpB : StrategyPrefix G seat hroot strategyB pB)
    (hpE : StrategyPrefix G seat hroot strategyE pE)
    (hzA : AffineResponseMoment G seat strategyA zA)
    (hzB : AffineResponseMoment G seat strategyB zB)
    (hzE : AffineResponseMoment G seat strategyE zE)
    (hbalance : (pA + zA) + (pB + zB) = pE + zE) :
    AffineResponseMoment G seat hroot 0 := by
  have hA := hpA.lift hzA
  have hB := hpB.lift hzB
  have hE := hpE.lift hzE
  have hsum := AffineResponseMoment.ternary hA hB hE
  rw [hbalance] at hsum
  convert hsum using 1
  ext e
  exact (CharTwo.add_self_eq_zero ((pE + zE) e)).symm

end

end Ogdoad.Fifo
