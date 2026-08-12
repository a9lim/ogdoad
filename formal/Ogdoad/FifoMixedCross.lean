import Ogdoad.FifoCrossDescent

/-!
# The mixed OPEN/CLOSE cross boundary

This module records the exact result of crossing a selected OPEN on one
cell-swapped hole with a selected CLOSE on the other.  Both holes and both
crossed replies are required to occur in one explicit Type-valued
`OddStrategy` tree.

Unlike the OPEN/OPEN square, the endpoints need not be cell-swapped and need
not have equal score.  They retain the same root ancestry and have strictly
smaller rank, but their score difference is a genuine mixed curvature.  Thus
the theorem exposes, rather than absorbs, the mixed boundary.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The universal edge vector whose graph evaluation is the mixed cross
curvature. -/
def mixedCrossCurvature (U : Finset V) (f g z : V) : EdgeVector V :=
  liveStarVector (U.erase z) f + liveStarVector U g

omit [Fintype V] in
/-- Scalar CLOSE charge is evaluation of the universal mixed curvature. -/
theorem graphEvaluation_mixedCrossCurvature (G : SimpleGraph V)
    (U : Finset V) (f g z : V) :
    graphEvaluation G (mixedCrossCurvature U f g z) =
      flip G (U.erase z) f + flip G U g := by
  simp [mixedCrossCurvature, graphEvaluation_liveStarVector]

omit [Fintype V] in
/-- Unit mixed curvature cannot vanish after forgetting dummy-incident and
diagonal coordinates on an isolated-dummy graph. -/
theorem realEdgeProjection_mixedCrossCurvature_ne_zero
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    {U : Finset V} {f g z : V}
    (hcurvature : flip G (U.erase z) f + flip G U g = 1) :
    realEdgeProjection d (mixedCrossCurvature U f g z) ≠ 0 := by
  intro hzero
  have heval :=
    graphEvaluation_eq_zero_of_realEdgeProjection_eq_zero hd hzero
  rw [graphEvaluation_mixedCrossCurvature, hcurvature] at heval
  exact one_ne_zero heval

/-- The explicit state produced by opening `v`, without its legality premise. -/
private def openSuccessorMixed (s : State V) (v : V) : State V where
  untouched := s.untouched.erase v
  queue := s.queue ++ [v]
  ko := s.queue.isEmpty
  toMove := !s.toMove
  score := s.score

omit [Fintype V] in
private theorem eq_openSuccessorMixed_of_step {G : SimpleGraph V}
    {s t : State V} {v : V} (h : step G s (.open v) = some t) :
    t = openSuccessorMixed s v := by
  simp only [step] at h
  split at h
  · cases h
    rfl
  · contradiction

/-- The explicit state produced by closing the displayed queue front. -/
private def closeSuccessorMixed (G : SimpleGraph V) (s : State V)
    (f : V) (q : List V) : State V where
  untouched := s.untouched
  queue := q
  ko := false
  toMove := !s.toMove
  score := s.score + flip G s.untouched f

omit [Fintype V] in
private theorem eq_closeSuccessorMixed_of_step {G : SimpleGraph V}
    {s t : State V} {f : V} {q : List V}
    (hqueue : s.queue = f :: q) (h : step G s .close = some t) :
    t = closeSuccessorMixed G s f q := by
  simp only [step, hqueue] at h
  split at h
  · contradiction
  · cases h
    rfl

omit [Fintype V] in
/--
The exact constructor-level mixed cross inside one fixed odd-strategy tree.

The two starting holes have reversed leading cells and equal public data.
The first strategy choice is OPEN `z`, the second is CLOSE; the universal
answer nodes contain the crossed CLOSE and OPEN replies.  Both descendants
remain holes in the same root tree and have smaller rank.  Their queues are
the displayed phase-offset queues, while their score difference is the local
mixed curvature

`flip G (U.erase z) f + flip G U g`.

The final two score equalities show exactly what the common score-zero premise
buys: it identifies each endpoint sheet with its local CLOSE charge.  It does
not force the curvature to vanish.  In particular, the conclusion deliberately
contains neither `PublicCellSwap tA tB` nor `tA.score = tB.score`.
-/
theorem StrategyPrefix.crossOpenClose
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    {sA sB aA aB tA tB : State V} {f g z : V} {qA qB : List V}
    {pA pB : EdgeVector V}
    {hattA : sA.toMove ≠ seat} {hattB : sB.toMove ≠ seat}
    {haz : step G sA (.open z) = some aA}
    {hbg : step G sB .close = some aB}
    {hdefA : aA.toMove = seat} {hdefB : aB.toMove = seat}
    {hasMoveA : ∃ m u, step G aA m = some u}
    {hasMoveB : ∃ m u, step G aB m = some u}
    {childrenA : ∀ m u, step G aA m = some u → OddStrategy G seat u}
    {childrenB : ∀ m u, step G aB m = some u → OddStrategy G seat u}
    (prefixA : StrategyPrefix G seat hroot
      (OddStrategy.choose sA hattA (.open z) aA haz
        (OddStrategy.answer aA hdefA hasMoveA childrenA)) pA)
    (prefixB : StrategyPrefix G seat hroot
      (OddStrategy.choose sB hattB .close aB hbg
        (OddStrategy.answer aB hdefB hasMoveB childrenB)) pB)
    (hac : step G aA .close = some tA)
    (hbo : step G aB (.open z) = some tB)
    (hpublic : PublicCellSwap sA sB)
    (hqueueA : sA.queue = f :: g :: qA)
    (hqueueB : sB.queue = g :: f :: qB)
    (hscore0 : sA.score = 0) :
    StrategyPrefix G seat hroot (childrenA .close tA hac)
        ((pA + moveLiveStar sA (.open z)) + moveLiveStar aA .close) ∧
      StrategyPrefix G seat hroot (childrenB (.open z) tB hbo)
        ((pB + moveLiveStar sB .close) + moveLiveStar aB (.open z)) ∧
      tA.untouched = tB.untouched ∧
      tA.queue = g :: (qA ++ [z]) ∧
      tB.queue = f :: (qB ++ [z]) ∧
      tA.ko = false ∧ tB.ko = false ∧
      tA.toMove = tB.toMove ∧
      tA.score + tB.score =
        flip G (sA.untouched.erase z) f + flip G sA.untouched g ∧
      tA.score = flip G (sA.untouched.erase z) f ∧
      tB.score = flip G sA.untouched g ∧
      rank tA < rank sA ∧ rank tB < rank sB := by
  have prefixA' : StrategyPrefix G seat hroot
      (OddStrategy.answer aA hdefA hasMoveA childrenA)
      (pA + moveLiveStar sA (.open z)) :=
    StrategyPrefix.choose prefixA
  have prefixB' : StrategyPrefix G seat hroot
      (OddStrategy.answer aB hdefB hasMoveB childrenB)
      (pB + moveLiveStar sB .close) :=
    StrategyPrefix.choose prefixB
  have hpa : StrategyPrefix G seat hroot (childrenA .close tA hac)
      ((pA + moveLiveStar sA (.open z)) + moveLiveStar aA .close) :=
    StrategyPrefix.answer (hstep := hac) prefixA'
  have hpb : StrategyPrefix G seat hroot (childrenB (.open z) tB hbo)
      ((pB + moveLiveStar sB .close) + moveLiveStar aB (.open z)) :=
    StrategyPrefix.answer (hstep := hbo) prefixB'
  have haA := eq_openSuccessorMixed_of_step haz
  have haB := eq_closeSuccessorMixed_of_step hqueueB hbg
  subst aA
  subst aB
  have hqueueA' : (openSuccessorMixed sA z).queue =
      f :: (g :: qA ++ [z]) := by
    simp [openSuccessorMixed, hqueueA]
  have htA := eq_closeSuccessorMixed_of_step hqueueA' hac
  have htB := eq_openSuccessorMixed_of_step hbo
  subst tA
  subst tB
  have hscoreB : sB.score = 0 := hpublic.score.symm.trans hscore0
  refine ⟨hpa, hpb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [openSuccessorMixed, closeSuccessorMixed, hpublic.untouched]
  · simp [openSuccessorMixed, closeSuccessorMixed, hqueueA]
  · simp [openSuccessorMixed, closeSuccessorMixed]
  · simp [openSuccessorMixed, closeSuccessorMixed]
  · simp [openSuccessorMixed, closeSuccessorMixed]
  · simp [openSuccessorMixed, closeSuccessorMixed, hpublic.toMove]
  · simp [openSuccessorMixed, closeSuccessorMixed, hscore0, hscoreB,
      hpublic.untouched]
  · simp [openSuccessorMixed, closeSuccessorMixed, hscore0]
  · simp [openSuccessorMixed, closeSuccessorMixed, hscoreB,
      hpublic.untouched]
  · exact lt_trans (rank_step_lt hac) (rank_step_lt haz)
  · exact lt_trans (rank_step_lt hbo) (rank_step_lt hbg)

end

end Ogdoad.Fifo
