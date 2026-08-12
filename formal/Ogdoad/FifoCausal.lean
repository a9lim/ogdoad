import Ogdoad.Fifo

/-!
# Direct causal transport for the FIFO linking theorem

This module isolates a strategy-tree consequence of the operational
OPEN/CLOSE squares in `Ogdoad.Fifo`.  At a charged selected CLOSE, the
opposite score sheet can carry a completely neutral strategy.  Opening a
neighbour of that front first removes the charge; away from the singleton
queue wall, the commuting square transports the neutral strategy to that
alternative branch.

The theorem below is local.  The still-open global step is to prove that the
defender ancestry of an arbitrary odd counterstrategy supplies enough such
neighbour-OPEN alternatives simultaneously.
-/

namespace Ogdoad.Fifo

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- A unit close charge has an actual untouched neighbour. -/
theorem exists_mem_adj_of_flip_eq_one
    {G : SimpleGraph V} {U : Finset V} {f : V}
    (hflip : flip G U f = 1) : ∃ z ∈ U, G.Adj f z := by
  classical
  by_contra h
  have hno : ∀ z ∈ U, ¬G.Adj f z := by
    intro z hz hadj
    exact h ⟨z, hz, hadj⟩
  have hfilter : U.filter (G.Adj f) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro z hz
    exact hno z hz
  rw [flip, hfilter] at hflip
  simp at hflip

omit [Fintype V] in
/-- Away from the singleton-queue ko wall, opening a neighbour of a charged
front before closing it transports the neutral continuation on the opposite
score sheet to the OPEN-then-CLOSE branch.

Concretely, the selected `C_f` has charge one.  Since `fz` is an edge,
opening `z` first removes exactly that charge.  The paths `C_f; O_z` and
`O_z; C_f` reconverge publicly, while their scores differ by one.  Translating
the first path's score sheet by one therefore makes the endpoints identical.
-/
theorem exists_treeNeutral_open_close_of_adj_away_singleton
    {G : SimpleGraph V} {player : Bool} {s sc : State V}
    {f z : V} {q : List V}
    (hturn : s.toMove = player)
    (hqueue : s.queue = f :: q) (hq : q ≠ []) (hko : s.ko = false)
    (hz : z ∈ s.untouched) (hadj : G.Adj f z)
    (hclose : step G s .close = some sc)
    (hneutral : TreeNeutralWins G player (scoreTranslate 1 sc)) :
    ∃ so soc,
      step G s (.open z) = some so ∧
      step G so .close = some soc ∧
      TreeNeutralWins G player soc := by
  obtain ⟨so, soc, sc', sco, hopen, hopenClose, hclose', hcloseOpen,
      hU, hq', hko', hmove, hscores⟩ :=
    open_close_square_away_singleton G s f z q hqueue hq hko hz
  have hsc : sc' = sc := by
    rw [hclose] at hclose'
    exact Option.some.inj hclose'.symm
  subst sc'
  have htranslated :
      step G (scoreTranslate 1 sc) (.open z) =
        some (scoreTranslate 1 sco) := by
    rw [step_scoreTranslate, hcloseOpen]
    rfl
  have hopponent : (scoreTranslate 1 sc).toMove ≠ player := by
    have hmoveClose := step_toMove hclose
    simp only [scoreTranslate]
    rw [hmoveClose, hturn]
    cases player <;> simp
  have hchild : TreeNeutralWins G player (scoreTranslate 1 sco) :=
    (hneutral.answer_child hopponent htranslated).2
  have hsheet : scoreTranslate 1 sco = soc := by
    obtain ⟨scoU, scoq, scoko, scoMove, scoScore⟩ := sco
    obtain ⟨socU, socq, socko, socMove, socScore⟩ := soc
    simp only [scoreTranslate] at hU hq' hko' hmove hscores ⊢
    simp_all only [adjacencyBit, ↓reduceIte]
    congr 1
    calc
      1 + (socScore + 1) = (1 + 1) + socScore := by abel
      _ = socScore := by rw [CharTwo.add_self_eq_zero, zero_add]
  exact ⟨so, soc, hopen, hopenClose, hsheet ▸ hchild⟩

omit [Fintype V] in
/-- At the singleton-queue ko wall, one further distinct OPEN repairs the
public-state discrepancy.  A neutral continuation already transported along
`C_f; O_z; O_w` therefore transfers to the alternative
`O_z; C_f; O_w` branch.

This is the exact causal wall transport.  A global FIFO proof must still
select compatible repair OPENs `w` across the relevant strategy fan.
-/
theorem exists_treeNeutral_open_close_open_of_adj_singleton
    {G : SimpleGraph V} {player : Bool}
    {s sc scz sczw : State V} {f z w : V}
    (hqueue : s.queue = [f]) (hko : s.ko = false)
    (hz : z ∈ s.untouched) (hw : w ∈ s.untouched) (hzw : z ≠ w)
    (hadj : G.Adj f z)
    (hclose : step G s .close = some sc)
    (hcloseOpen : step G sc (.open z) = some scz)
    (hcloseOpenOpen : step G scz (.open w) = some sczw)
    (hneutral : TreeNeutralWins G player (scoreTranslate 1 sczw)) :
    ∃ so soc socw,
      step G s (.open z) = some so ∧
      step G so .close = some soc ∧
      step G soc (.open w) = some socw ∧
      TreeNeutralWins G player socw := by
  obtain ⟨sc', scz', sczw', so, soc, socw, hclose', hcloseOpen',
      hcloseOpenOpen', hopen, hopenClose, hopenCloseOpen, _, _, _, _, _,
      hsheet⟩ :=
    singleton_wall_reconverges_after_open G s f z w hqueue hko hz hw hzw
  have hbit : adjacencyBit G f z = 1 := by simp [adjacencyBit, hadj]
  have hsheet0 : sczw' = scoreTranslate 1 socw := by
    rw [hbit] at hsheet
    exact hsheet
  have hsc : sc' = sc := by
    rw [hclose] at hclose'
    exact Option.some.inj hclose'.symm
  subst sc'
  have hscz : scz' = scz := by
    rw [hcloseOpen] at hcloseOpen'
    exact Option.some.inj hcloseOpen'.symm
  subst scz'
  have hsczw : sczw' = sczw := by
    rw [hcloseOpenOpen] at hcloseOpenOpen'
    exact Option.some.inj hcloseOpenOpen'.symm
  have hdouble : scoreTranslate 1 sczw = socw := by
    calc
      scoreTranslate 1 sczw = scoreTranslate 1 sczw' :=
        congrArg (scoreTranslate 1) hsczw.symm
      _ =
          scoreTranslate 1 (scoreTranslate 1 socw) :=
        congrArg (scoreTranslate 1) hsheet0
      _ = socw := scoreTranslate_one_involutive socw
  exact ⟨so, soc, socw, hopen, hopenClose, hopenCloseOpen,
    hdouble ▸ hneutral⟩

omit [Fintype V] in
/-- Every zero-sheet odd counterstrategy contains either a singleton-wall
charged CLOSE or a charged CLOSE with a concrete neighbour whose
OPEN-then-CLOSE alternative already carries a neutral strategy.  Thus the
singleton queue is the only local operational exception; the remaining
difficulty is to make the earlier defender ancestry select these alternatives
coherently. -/
theorem oddStrategy_extract_causal_neighbor_or_singleton
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    (hroot : OddWins G seat root) (hroot0 : root.score = 0) :
    ∃ s, InOddStrategy G seat hroot s ∧ s.score = 0 ∧
      s.toMove = !seat ∧
      ∃ f q sc, s.queue = f :: q ∧ s.ko = false ∧
        step G s .close = some sc ∧ flip G s.untouched f = 1 ∧
        TreeNeutralWins G (!seat) (scoreTranslate 1 sc) ∧
        (q = [] ∨ ∃ z so soc,
          z ∈ s.untouched ∧ G.Adj f z ∧
          step G s (.open z) = some so ∧
          step G so .close = some soc ∧
          TreeNeutralWins G (!seat) soc) := by
  obtain ⟨s, hmem, hs0, hturn, f, q, sc, hqueue, hko, hclose, hflip,
      hneutral⟩ := oddStrategy_extract_minimalCloseNeutral hroot hroot0
  refine ⟨s, hmem, hs0, hturn, f, q, sc, hqueue, hko, hclose, hflip,
    hneutral, ?_⟩
  by_cases hq : q = []
  · exact Or.inl hq
  · obtain ⟨z, hz, hadj⟩ := exists_mem_adj_of_flip_eq_one hflip
    obtain ⟨so, soc, hopen, hopenClose, hneutral'⟩ :=
      exists_treeNeutral_open_close_of_adj_away_singleton
        hturn hqueue hq hko hz hadj hclose hneutral
    exact Or.inr ⟨z, so, soc, hz, hadj, hopen, hopenClose, hneutral'⟩

end

end Ogdoad.Fifo
