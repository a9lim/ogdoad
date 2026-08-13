import Ogdoad.FifoFirstSeatRoot
import Ogdoad.FifoOuterFan

/-!
# The isolated-dummy front fan

Consider the first-seat pair state after `OPEN d; OPEN y`, where `d` is the
isolated dummy.  Its defender fan consists of `CLOSE d` together with every
remaining `OPEN z`.  On an odd total carrier (equivalently, an even real
carrier plus the dummy), this complete fan is even, so its affine sum is a
response direction rather than a response point.

The universal OPEN-prefix sum also does not vanish after dummy projection.
It is exactly the surviving star of `y`, i.e. the non-dummy part of the
two-OPEN ancestry prefix.  Finally, graph evaluation proves that no response
point at the pair state can equal that star after projection.  Thus the
complete local fan and the elementary dummy-close/OPEN commuting diamonds do
not by themselves contract the pair state: a successful argument must import
an additional affine point from earlier common ancestry.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- With odd total order, the complete legal fan at the dummy-front pair
state has even size: one `CLOSE d` plus one `OPEN` for every remaining label. -/
theorem dummyFront_complete_fan_card_even (d y : V) (hdy : d ≠ y)
    (hV : ((Finset.univ : Finset V).card % 2) = 1) :
    (1 + ((Finset.univ.erase d).erase y).card) % 2 = 0 := by
  have hy : y ∈ (Finset.univ.erase d : Finset V) := by
    simp [hdy.symm]
  have hdCard := Finset.card_erase_add_one (Finset.mem_univ d)
  have hyCard := Finset.card_erase_add_one hy
  omega

/-- The complete real OPEN fan at `queue = [d,y]` leaves exactly the
non-dummy part of the two-OPEN ancestry prefix.  In particular the prefix
does not cancel locally; after quotienting dummy coordinates it is the
full-live star of `y`. -/
theorem dummyFront_open_fan_prefix_projection
    (d y : V) (hdy : d ≠ y) :
    realEdgeProjection d
        (∑ z ∈ (Finset.univ.erase d).erase y,
          liveStarVector Finset.univ z) =
      realEdgeProjection d (liveStarVector Finset.univ y) := by
  have hy : y ∈ (Finset.univ.erase d : Finset V) := by
    simp [hdy.symm]
  have htotal := sum_liveStarVector_eq_zero (Finset.univ : Finset V)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ d)] at htotal
  rw [← Finset.sum_erase_add _ _ hy] at htotal
  have hsource :
      (∑ z ∈ (Finset.univ.erase d).erase y,
          liveStarVector Finset.univ z) =
        liveStarVector Finset.univ y + liveStarVector Finset.univ d := by
    let S := ∑ z ∈ (Finset.univ.erase d).erase y,
      liveStarVector Finset.univ z
    let P := liveStarVector Finset.univ y + liveStarVector Finset.univ d
    have hself : P + P = 0 := by
      ext e
      exact CharTwo.add_self_eq_zero (P e)
    have htotal' : S + P = 0 := by
      simpa only [S, P, add_assoc] using htotal
    calc
      S = S + (P + P) := by rw [hself, add_zero]
      _ = (S + P) + P := by abel
      _ = P := by rw [htotal', zero_add]
  rw [hsource, map_add, realEdgeProjection_liveStarVector_dummy, add_zero]

/-- The residual `y`-star cannot itself be a response point of an odd
strategy at the dummy-front pair state.  Its graph evaluation is the pair
state's potential, while every odd response point evaluates to one plus that
potential.  The statement is made in the exact isolated-dummy quotient. -/
theorem dummyFront_response_ne_ancestryStar
    (G : SimpleGraph V) (d y : V) (hd : IsDummy G d) (hdy : d ≠ y)
    (h : OddStrategy G false (afterInitialTwoOpens d y))
    {z : EdgeVector V}
    (hz : AffineResponseMoment G false h z) :
    realEdgeProjection d z ≠
      realEdgeProjection d (liveStarVector Finset.univ y) := by
  have hstepD := initial_step_open G d
  have hy : y ∈ (Finset.univ.erase d : Finset V) := by
    simp [hdy.symm]
  have hstepY := (afterInitialOpen_step_open_iff G d y).2 hy
  have hWFD : WellFormed (afterInitialOpen d) :=
    wellFormed_step wellFormed_initial hstepD
  have hWF : WellFormed (afterInitialTwoOpens d y) :=
    wellFormed_step hWFD hstepY
  have hpotentialD : potential G (afterInitialOpen d) = 0 := by
    simp [potential, queueCut, afterInitialOpen, flip_dummy hd]
  have hliveD : liveSet (afterInitialOpen d) = Finset.univ := by
    ext v
    simp [liveSet, afterInitialOpen]
  have hpotential :
      potential G (afterInitialTwoOpens d y) =
        graphEvaluation G (liveStarVector Finset.univ y) := by
    calc
      potential G (afterInitialTwoOpens d y) =
          liveDegree G (afterInitialOpen d) y := by
            simpa [hpotentialD] using open_adds_liveDegree_to_potential hstepY
      _ = graphEvaluation G (liveStarVector Finset.univ y) := by
            simpa [hliveD] using
              (graphEvaluation_liveStar_eq_liveDegree G
                (afterInitialOpen d) y hWFD).symm
  intro hproj
  have hprojZero : realEdgeProjection d
      (z + liveStarVector Finset.univ y) = 0 := by
    rw [map_add, hproj]
    have hself : realEdgeProjection d (liveStarVector Finset.univ y) +
        realEdgeProjection d (liveStarVector Finset.univ y) = 0 := by
      rw [← map_add]
      have hsource : liveStarVector Finset.univ y +
          liveStarVector Finset.univ y = 0 := by
        ext e
        exact CharTwo.add_self_eq_zero _
      rw [hsource, map_zero]
    exact hself
  have hevalZero :=
    graphEvaluation_eq_zero_of_realEdgeProjection_eq_zero hd hprojZero
  rw [map_add, hz.graphEvaluation_eq hWF, hpotential] at hevalZero
  have hone : (1 : ZMod 2) = 0 := by
    calc
      (1 : ZMod 2) =
          (1 + graphEvaluation G (liveStarVector Finset.univ y)) +
            graphEvaluation G (liveStarVector Finset.univ y) := by
              symm
              rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = 0 := hevalZero
  exact one_ne_zero hone

end

end Ogdoad.Fifo
