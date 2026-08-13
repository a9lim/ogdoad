import Ogdoad.FifoHub

/-!
# Root-strategy interaction across a graph shear

FIFO legality is independent of the graph: only the score coordinate depends
on adjacency.  This file makes the resulting cross-graph interaction exact.
An even strategy on one graph and an explicit odd strategy on another graph,
started from the same public state, determine a common public play and hence a
common universal live-star moment.

For an elementary alternating-matrix congruence, opposite terminal targets
therefore force the congruence-row functional to take value one on that
strategy-correlated moment.  This is an obstruction theorem, not a proof that
the functional vanishes.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A legal move on one graph has a unique public counterpart on any other
graph, provided the source public states agree. -/
theorem exists_step_of_public_eq
    (G H : SimpleGraph V) {sG sH tG : State V} {m : Move V}
    (hpublic : sG.public = sH.public)
    (hstep : step G sG m = some tG) :
    ∃ tH, step H sH m = some tH ∧ tG.public = tH.public := by
  have hGpublic : publicStep sG.public m = some tG.public := by
    calc
      publicStep sG.public m = (step G sG m).map State.public :=
        (step_public G sG m).symm
      _ = some tG.public := by simp [hstep]
  have hHpublic : publicStep sH.public m = some tG.public := by
    rw [← hpublic]
    exact hGpublic
  have hmapped : (step H sH m).map State.public = some tG.public := by
    rw [step_public]
    exact hHpublic
  obtain ⟨tH, hstepH, hpubH⟩ := Option.map_eq_some_iff.mp hmapped
  exact ⟨tH, hstepH, hpubH.symm⟩

omit [Fintype V] [DecidableEq V] in
/-- Erasing the score also erases every part of terminality. -/
theorem terminal_iff_of_public_eq {s t : State V}
    (hpublic : s.public = t.public) : Terminal s ↔ Terminal t := by
  simp only [State.public, PublicState.mk.injEq] at hpublic
  rcases hpublic with ⟨hU, hq, _, _⟩
  simp only [Terminal]
  constructor
  · rintro ⟨hsU, hsq⟩
    exact ⟨hU ▸ hsU, hq ▸ hsq⟩
  · rintro ⟨htU, htq⟩
    exact ⟨hU.symm ▸ htU, hq.symm ▸ htq⟩

omit [Fintype V] in
/-- The live-star payload of a move depends only on the public state. -/
theorem moveLiveStar_eq_of_public_eq {s t : State V}
    (hpublic : s.public = t.public) (m : Move V) :
    moveLiveStar s m = moveLiveStar t m := by
  simp only [State.public, PublicState.mk.injEq] at hpublic
  rcases hpublic with ⟨hU, hq, _, _⟩
  cases m with
  | «open» v => simp [moveLiveStar, liveSet, hU, hq]
  | close => simp [moveLiveStar]
  | pass => simp [moveLiveStar]

omit [Fintype V] [DecidableEq V] in
/-- An elementary congruence away from an isolated dummy preserves the dummy.
The side condition `d ≠ j` is essential: modifying the dummy row itself can
copy the `i`-row into it. -/
theorem IsDummy.elementaryCongruenceGraph {G : SimpleGraph V} {d : V}
    (hd : IsDummy G d) (i j : V) (hdj : d ≠ j) :
    IsDummy (elementaryCongruenceGraph G i j) d := by
  intro v hadj
  have hdi : ¬G.Adj i d := by
    intro hid
    exact hd i hid.symm
  have hdv : ¬G.Adj d v := hd v
  have hxor : Xor (G.Adj d v)
      ((d = j ∧ G.Adj i v) ∨ (v = j ∧ G.Adj i d)) := hadj.2
  simp [hdv, hdj, hdi] at hxor

/-- The data extracted from interacting an even strategy on `G` with an odd
strategy on `H`.  The endpoints can have different scores, but have identical
public data and are reached with the same universal edge moment. -/
structure CrossGraphStrategyPlay (G H : SimpleGraph V)
    (sG sH : State V) where
  terminalG : State V
  terminalH : State V
  moment : EdgeVector V
  traceG : LiveStarTrace G sG terminalG moment
  traceH : LiveStarTrace H sH terminalH moment
  public_eq : terminalG.public = terminalH.public
  isTerminalG : Terminal terminalG
  isTerminalH : Terminal terminalH
  scoreG : terminalG.score = 0
  scoreH : terminalH.score ≠ 0

omit [Fintype V] in
/-- Cross-graph strategy interaction.  Whenever the public source states
agree, an even strategy on `G` and an explicit odd strategy on `H` can be
played against each other.  At each node one strategy selects a move and the
other supplies its universal child, so the resulting public move word and
live-star moment are shared. -/
theorem EvenWins.exists_crossGraphStrategyPlay
    (G H : SimpleGraph V) (seat : Bool) :
    ∀ {sG : State V}, EvenWins G seat sG →
      ∀ {sH : State V}, sG.public = sH.public → OddStrategy H seat sH →
        Nonempty (CrossGraphStrategyPlay G H sG sH) := by
  intro sG heven
  induction heven with
  | terminal sG hterminalG hscoreG =>
      intro sH hpublic hodd
      have hterminalH : Terminal sH :=
        (terminal_iff_of_public_eq hpublic).mp hterminalG
      cases hodd with
      | terminal _ _ hscoreH =>
          exact ⟨{
            terminalG := sG
            terminalH := sH
            moment := 0
            traceG := LiveStarTrace.refl sG
            traceH := LiveStarTrace.refl sH
            public_eq := hpublic
            isTerminalG := hterminalG
            isTerminalH := hterminalH
            scoreG := hscoreG
            scoreH := hscoreH }⟩
      | choose _ _ m tH hstepH _ =>
          exact False.elim (terminal_no_step hterminalH ⟨m, tH, hstepH⟩)
      | answer _ _ hasMoveH _ =>
          exact False.elim (terminal_no_step hterminalH hasMoveH)
  | choose sG hseat m tG hstepG _ ih =>
      intro sH hpublic hodd
      have hturn : sG.toMove = sH.toMove :=
        congrArg PublicState.toMove hpublic
      cases hodd with
      | terminal _ hterminalH _ =>
          obtain ⟨tH, hstepH, _⟩ :=
            exists_step_of_public_eq G H hpublic hstepG
          exact False.elim (terminal_no_step hterminalH ⟨m, tH, hstepH⟩)
      | choose _ hoddSeat _ _ _ _ =>
          exact False.elim (hoddSeat (hturn ▸ hseat))
      | answer _ _ _ childrenH =>
          obtain ⟨tH, hstepH, hpublic'⟩ :=
            exists_step_of_public_eq G H hpublic hstepG
          let tailH := childrenH m tH hstepH
          obtain ⟨tail⟩ := ih hpublic' tailH
          have hstar : moveLiveStar sG m = moveLiveStar sH m :=
            moveLiveStar_eq_of_public_eq hpublic m
          exact ⟨{
            terminalG := tail.terminalG
            terminalH := tail.terminalH
            moment := moveLiveStar sG m + tail.moment
            traceG := LiveStarTrace.cons hstepG tail.traceG
            traceH := by
              rw [hstar]
              exact LiveStarTrace.cons hstepH tail.traceH
            public_eq := tail.public_eq
            isTerminalG := tail.isTerminalG
            isTerminalH := tail.isTerminalH
            scoreG := tail.scoreG
            scoreH := tail.scoreH }⟩
  | answer sG hseat hasMoveG _ ih =>
      intro sH hpublic hodd
      have hturn : sG.toMove = sH.toMove :=
        congrArg PublicState.toMove hpublic
      cases hodd with
      | terminal _ hterminalH _ =>
          obtain ⟨m, tG, hstepG⟩ := hasMoveG
          obtain ⟨tH, hstepH, _⟩ :=
            exists_step_of_public_eq G H hpublic hstepG
          exact False.elim (terminal_no_step hterminalH ⟨m, tH, hstepH⟩)
      | choose _ _ m tH hstepH tailH =>
          obtain ⟨tG, hstepG, hpublic'⟩ :=
            exists_step_of_public_eq H G hpublic.symm hstepH
          obtain ⟨tail⟩ := ih m tG hstepG hpublic'.symm tailH
          have hstar : moveLiveStar sG m = moveLiveStar sH m :=
            moveLiveStar_eq_of_public_eq hpublic m
          exact ⟨{
            terminalG := tail.terminalG
            terminalH := tail.terminalH
            moment := moveLiveStar sG m + tail.moment
            traceG := LiveStarTrace.cons hstepG tail.traceG
            traceH := by
              rw [hstar]
              exact LiveStarTrace.cons hstepH tail.traceH
            public_eq := tail.public_eq
            isTerminalG := tail.isTerminalG
            isTerminalH := tail.isTerminalH
            scoreG := tail.scoreG
            scoreH := tail.scoreH }⟩
      | answer _ hoddSeat _ _ =>
          exact False.elim (hseat (hturn.trans hoddSeat))

/-- If an elementary congruence changes the root winner, interacting the two
opposite strategies produces a shared terminal edge moment on which the
congruence-row functional is exactly one. -/
theorem elementaryCongruence_counterstrategy_rowEvaluation_eq_one
    (G : SimpleGraph V) (i j : V) (seat : Bool)
    (heven : EvenWins G seat (initial (V := V)))
    (hodd : OddStrategy (elementaryCongruenceGraph G i j) seat
      (initial (V := V))) :
    ∃ play : CrossGraphStrategyPlay G (elementaryCongruenceGraph G i j)
        (initial (V := V)) (initial (V := V)),
      elementaryCongruenceRowEvaluation G i j play.moment = 1 := by
  obtain ⟨play⟩ := heven.exists_crossGraphStrategyPlay G
    (elementaryCongruenceGraph G i j) seat rfl hodd
  refine ⟨play, ?_⟩
  have hGscore := play.traceG.terminal_score_eq_graphEvaluation
    play.isTerminalG
  have hHscore := play.traceH.terminal_score_eq_graphEvaluation
    play.isTerminalH
  have hHeval : graphEvaluation (elementaryCongruenceGraph G i j)
      play.moment = 1 := by
    rw [← hHscore]
    exact zmod2_eq_one_of_ne_zero _ play.scoreH
  have hGeval : graphEvaluation G play.moment = 0 := by
    rw [← hGscore]
    exact play.scoreG
  have hdefect := graphEvaluation_elementaryCongruenceGraph_add
    G i j play.moment
  rw [hHeval, hGeval, add_zero] at hdefect
  exact hdefect.symm

end

end Ogdoad.Fifo
