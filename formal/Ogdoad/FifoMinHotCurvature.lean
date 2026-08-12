import Ogdoad.FifoNeutralPair

/-!
# Minimum-hot cross-target curvature

This module records a sharp boundary for paired-strategy and strategy-prism
attacks on the isolated-dummy FIFO linking theorem.  At a rank-minimal state
where one physical player can force both terminal score sheets, the two sheets
select opposite sides of a singleton CLOSE--OPEN wall.  Commuting those two
moves either reconverges modulo score translation or reaches forced terminal
drains, but in both cases leaves one unit universal edge coordinate.

On an isolated-dummy board that coordinate survives the real-edge quotient.
Thus diagonal policy switching does not by itself contract a paired response
to zero.  These are no-go/boundary lemmas, not a proof of the linking theorem:
the missing cancellation must still use earlier strategy-indexed defender
siblings and their continuation spaces.
-/

namespace Ogdoad.Fifo

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Adding one new live vertex to the star center's live set changes its
universal star by exactly the corresponding edge coordinate.  Over
characteristic two, summing the old and new stars isolates that coordinate. -/
theorem liveStarVector_insert_cancel
    (L : Finset V) (f z : V) (hf : f ∉ L) (hfz : f ≠ z) :
    liveStarVector L z + liveStarVector (insert f L) z =
      Finsupp.single s(f, z) 1 := by
  classical
  have herase : (insert f L).erase z = insert f (L.erase z) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hxz, hxf | hxL⟩
      · exact Or.inl hxf
      · exact Or.inr ⟨hxz, hxL⟩
    · rintro (hxf | ⟨hxz, hxL⟩)
      · subst x
        exact ⟨hfz, Or.inl rfl⟩
      · exact ⟨hxz, Or.inr hxL⟩
  have hfErase : f ∉ L.erase z := by simp [hf]
  rw [liveStarVector, liveStarVector, herase,
    Finset.sum_insert hfErase]
  have hsym : s(z, f) = s(f, z) := Sym2.eq_swap
  rw [hsym]
  let A := ∑ w ∈ L.erase z, Finsupp.single s(z, w) (1 : ZMod 2)
  calc
    A + (Finsupp.single s(f, z) 1 + A) =
        (A + A) + Finsupp.single s(f, z) 1 := by abel
    _ = Finsupp.single s(f, z) 1 := by
      ext e
      simp only [Finsupp.add_apply]
      rw [CharTwo.add_self_eq_zero, zero_add]

/-- Exact two-step cross-target diamond at a well-formed singleton wall.

The CLOSE--OPEN and OPEN--CLOSE orders have total universal live-star
difference `single {f,z}`.  If an old queue tail remains, they reach the same
public state with scores translated by one. -/
theorem singletonWall_cross_target_unit_curvature
    (G : SimpleGraph V) (s : State V) (f z : V) (q : List V)
    (hs : WellFormed s) (hs0 : s.score = 0)
    (hqueue : s.queue = f :: q) (hko : s.ko = false)
    (hU : s.untouched = {z})
    (hbit : adjacencyBit G f z = 1) :
    ∃ sC sCO sO sOC,
      step G s .close = some sC ∧
      step G sC (.open z) = some sCO ∧
      step G s (.open z) = some sO ∧
      step G sO .close = some sOC ∧
      (q ≠ [] → sCO = scoreTranslate 1 sOC) ∧
      (moveLiveStar s .close + moveLiveStar sC (.open z)) +
          (moveLiveStar s (.open z) + moveLiveStar sO .close) =
        Finsupp.single s(f, z) 1 := by
  classical
  rcases hs with ⟨hnodup, hdisjoint⟩
  rw [hqueue] at hnodup
  rw [hqueue, hU] at hdisjoint
  have hfq : f ∉ q := (List.nodup_cons.mp hnodup).1
  have hzf : z ≠ f := by
    intro h
    subst z
    have : f ∉ (f :: q).toFinset :=
      Finset.disjoint_left.mp hdisjoint (by simp)
    exact this (by simp)
  have hfz : f ≠ z := Ne.symm hzf
  let sC : State V := {
    untouched := {z}
    queue := q
    ko := false
    toMove := !s.toMove
    score := 1 }
  let sCO : State V := {
    untouched := ∅
    queue := q ++ [z]
    ko := q.isEmpty
    toMove := s.toMove
    score := 1 }
  let sO : State V := {
    untouched := ∅
    queue := f :: (q ++ [z])
    ko := false
    toMove := !s.toMove
    score := 0 }
  let sOC : State V := {
    untouched := ∅
    queue := q ++ [z]
    ko := false
    toMove := s.toMove
    score := 0 }
  refine ⟨sC, sCO, sO, sOC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [step, sC, hqueue, hko, hU, hs0,
      flip_singleton_eq_adjacencyBit, hbit]
  · simp [step, sC, sCO]
  · simp [step, sO, hqueue, hU, hs0]
  · simp [step, sO, sOC]
  · intro hq
    simp [sCO, sOC, scoreTranslate, hq]
  · simp only [moveLiveStar, zero_add, add_zero]
    have hL : liveSet sC = {z} ∪ q.toFinset := by
      simp [liveSet, sC]
    have hsL : liveSet s = insert f (liveSet sC) := by
      rw [hL]
      simp [liveSet, hU, hqueue, Finset.union_comm]
    have hfL : f ∉ liveSet sC := by
      rw [hL]
      simp [hfz, hfq]
    rw [hsL]
    exact liveStarVector_insert_cancel (liveSet sC) f z hfL hfz

/-- On an isolated-dummy board the unit singleton-wall curvature is a genuine
real-edge coordinate.  No separate hypotheses `f ≠ d`, `z ≠ d`, or
`f ≠ z` are needed: they follow already from isolation and `hbit`. -/
theorem singletonWall_curvature_projection_ne_zero
    (G : SimpleGraph V) (d f z : V) (hd : IsDummy G d)
    (hbit : adjacencyBit G f z = 1) :
    realEdgeProjection d (Finsupp.single s(f, z) 1 : EdgeVector V) ≠ 0 := by
  intro hzero
  have heval := graphEvaluation_eq_zero_of_realEdgeProjection_eq_zero hd hzero
  rw [graphEvaluation_single, hbit, one_mul] at heval
  exact one_ne_zero heval

/-- Exact empty-tail side of the singleton-wall split.

After two plies the CLOSE--OPEN order has `ko = true`, whereas the
OPEN--CLOSE order has `ko = false`.  The former is forced to PASS and CLOSE;
the latter closes immediately.  Both tails add zero live-star, and they end
at opposite terminal scores with opposite mover bits. -/
theorem singletonWall_empty_tail_forced_drain
    (G : SimpleGraph V) (s : State V) (f z : V)
    (hs0 : s.score = 0) (hqueue : s.queue = [f])
    (hko : s.ko = false) (hU : s.untouched = {z})
    (hbit : adjacencyBit G f z = 1) :
    ∃ sC sCO sO sOC sCOP sCOT sOCT,
      step G s .close = some sC ∧
      step G sC (.open z) = some sCO ∧
      step G s (.open z) = some sO ∧
      step G sO .close = some sOC ∧
      sCO.ko = true ∧ sOC.ko = false ∧
      step G sCO .pass = some sCOP ∧
      step G sCOP .close = some sCOT ∧
      step G sOC .close = some sOCT ∧
      Terminal sCOT ∧ Terminal sOCT ∧
      sCOT.score = 1 ∧ sOCT.score = 0 ∧
      sCOT.toMove = !sOCT.toMove ∧
      moveLiveStar sCO .pass + moveLiveStar sCOP .close = 0 ∧
      moveLiveStar sOC .close = 0 := by
  classical
  let sC : State V := {
    untouched := {z}
    queue := []
    ko := false
    toMove := !s.toMove
    score := 1 }
  let sCO : State V := {
    untouched := ∅
    queue := [z]
    ko := true
    toMove := s.toMove
    score := 1 }
  let sO : State V := {
    untouched := ∅
    queue := [f, z]
    ko := false
    toMove := !s.toMove
    score := 0 }
  let sOC : State V := {
    untouched := ∅
    queue := [z]
    ko := false
    toMove := s.toMove
    score := 0 }
  let sCOP : State V := {
    untouched := ∅
    queue := [z]
    ko := false
    toMove := !s.toMove
    score := 1 }
  let sCOT : State V := {
    untouched := ∅
    queue := []
    ko := false
    toMove := s.toMove
    score := 1 }
  let sOCT : State V := {
    untouched := ∅
    queue := []
    ko := false
    toMove := !s.toMove
    score := 0 }
  refine ⟨sC, sCO, sO, sOC, sCOP, sCOT, sOCT,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [step, sC, hqueue, hko, hU, hs0,
      flip_singleton_eq_adjacencyBit, hbit]
  · simp [step, sC, sCO]
  · simp [step, sO, hqueue, hU, hs0]
  · simp [step, sO, sOC]
  · rfl
  · rfl
  · simp [step, sCO, sCOP]
  · simp [step, sCOP, sCOT]
  · simp [step, sOC, sOCT]
  · simp [Terminal, sCOT]
  · simp [Terminal, sOCT]
  · rfl
  · rfl
  · simp [sCOT, sOCT]
  · simp [moveLiveStar]
  · simp [moveLiveStar]

/-- Kernel-checked minimum-hot form of the cross-target unit-curvature wall. -/
theorem minHot_cross_target_unit_curvature
    (G : SimpleGraph V) (d : V) (hd : IsDummy G d)
    (player : Bool) (s : State V) (hs : WellFormed s)
    (hs0 : s.score = 0) (hhot : Hot G player s)
    (hminimal : ∀ (other : Bool) (t : State V), rank t < rank s →
      ¬Hot G other t) :
    ∃ f q z sC sCO sO sOC,
      s.toMove = player ∧
      s.queue = f :: q ∧ s.ko = false ∧ s.untouched = {z} ∧
      adjacencyBit G f z = 1 ∧
      (∀ a ∈ q, adjacencyBit G a z = 0) ∧
      step G s .close = some sC ∧
      step G sC (.open z) = some sCO ∧
      step G s (.open z) = some sO ∧
      step G sO .close = some sOC ∧
      (q ≠ [] → sCO = scoreTranslate 1 sOC) ∧
      (moveLiveStar s .close + moveLiveStar sC (.open z)) +
          (moveLiveStar s (.open z) + moveLiveStar sO .close) =
        Finsupp.single s(f, z) 1 ∧
      realEdgeProjection d
          (Finsupp.single s(f, z) 1 : EdgeVector V) ≠ 0 := by
  obtain ⟨hturn, f, q, z, hqueue, hko, hU, hbit, htail⟩ :=
    minHotState_is_singletonWall G player s hs0 hhot hminimal
  obtain ⟨sC, sCO, sO, sOC, hC, hCO, hO, hOC, hdiag, hcurve⟩ :=
    singletonWall_cross_target_unit_curvature
      G s f z q hs hs0 hqueue hko hU hbit
  exact ⟨f, q, z, sC, sCO, sO, sOC, hturn, hqueue, hko, hU,
    hbit, htail, hC, hCO, hO, hOC, hdiag, hcurve,
    singletonWall_curvature_projection_ne_zero G d f z hd hbit⟩

/-- At a rank-minimal score-zero hot wall, every actual target-one policy
selects the charged CLOSE.  This is a statement about Type-valued strategy
data, not merely about proof-irrelevant force sets. -/
theorem minHot_oddStrategy_selectedClose
    (G : SimpleGraph V) (player : Bool) (s : State V)
    (hs0 : s.score = 0) (hhot : Hot G player s)
    (hminimal : ∀ (other : Bool) (t : State V), rank t < rank s →
      ¬Hot G other t)
    (strategy : OddStrategy G (!player) s) :
    strategy.selectedMove = some .close := by
  obtain ⟨hturn, f, q, z, hqueue, hko, hU, hbit, htail⟩ :=
    minHotState_is_singletonWall G player s hs0 hhot hminimal
  cases strategy with
  | terminal _ hterminal _ =>
      exact False.elim (by
        have hnot : ¬Terminal s := by simp [Terminal, hU]
        exact hnot hterminal)
  | choose _ hseat m t hstep child =>
      change some m = some (.close : Move V)
      apply congrArg some
      cases m with
      | «open» v =>
          have ht0 : t.score = 0 := by
            have hscore := open_score hstep
            exact hscore.trans hs0
          have hcold := coldAtOwnScore_below_minHot G (rank s) hminimal
            t (rank_step_lt hstep)
          have heven : EvenWins G player t := hcold.evenWins ht0 player
          exact False.elim
            (hminimal player t (rank_step_lt hstep)
              ⟨heven, child.toOddWins⟩)
      | close => rfl
      | pass => simp [step, hqueue, hko] at hstep
  | answer _ hseat _ _ =>
      exact False.elim ((Bool.eq_not_iff.mp hseat) hturn)

/-- The same physical player's score-translated target-zero policy selects
the unique OPEN at a rank-minimal hot wall.  Hence choice saturation across
actual policies cannot align the two score sheets at the wall. -/
theorem minHot_translatedOddStrategy_selectedOpen
    (G : SimpleGraph V) (player : Bool) (s : State V)
    (hs0 : s.score = 0) (hhot : Hot G player s)
    (hminimal : ∀ (other : Bool) (t : State V), rank t < rank s →
      ¬Hot G other t)
    (strategy : OddStrategy G (!player) (scoreTranslate 1 s)) :
    ∃ z, s.untouched = {z} ∧
      strategy.selectedMove = some (.open z) := by
  classical
  obtain ⟨hturn, f, q, z, hqueue, hko, hU, hbit, htail⟩ :=
    minHotState_is_singletonWall G player s hs0 hhot hminimal
  refine ⟨z, hU, ?_⟩
  cases strategy with
  | terminal _ hterminal _ =>
      exact False.elim (by
        have hnot : ¬Terminal (scoreTranslate 1 s) := by
          simp [Terminal, scoreTranslate, hU]
        exact hnot hterminal)
  | choose _ hseat m t hstep child =>
      change some m = some (.open z : Move V)
      apply congrArg some
      cases m with
      | «open» v =>
          have hv : v ∈ s.untouched := by
            simp only [step, scoreTranslate] at hstep
            split at hstep
            · assumption
            · contradiction
          exact congrArg Move.open
            (Finset.mem_singleton.mp (hU ▸ hv))
      | close =>
          have ht0 : t.score = 0 := by
            simp [step, scoreTranslate, hqueue, hko, hU, hs0,
              flip_singleton_eq_adjacencyBit, hbit] at hstep
            subst t
            exact CharTwo.add_self_eq_zero 1
          have hrank : rank t < rank s := by
            have hrank' := rank_step_lt hstep
            change rank t < rank s at hrank'
            exact hrank'
          have hcold := coldAtOwnScore_below_minHot G (rank s) hminimal
            t hrank
          have heven : EvenWins G player t := hcold.evenWins ht0 player
          exact False.elim
            (hminimal player t hrank ⟨heven, child.toOddWins⟩)
      | pass => simp [step, scoreTranslate, hqueue, hko] at hstep
  | answer _ hseat _ _ =>
      have hsEq : s.toMove = !player := by
        simpa [scoreTranslate] using hseat
      exact False.elim ((Bool.eq_not_iff.mp hsEq) hturn)

end

end Ogdoad.Fifo
