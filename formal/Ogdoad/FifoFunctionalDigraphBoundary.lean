import Ogdoad.FifoFirstSeatStrategy

/-!
# A whole-functional-digraph prefix boundary

Summing selected first-seat arcs over a directed cycle cancels their
two-`OPEN` prefixes.  Adding every in-tree feeding the cycles does not make
an odd zero-prefix family automatic.  The explicit fixed-point-free map below
has two even cycles and genuine in-trees.  One isolated-dummy graph functional
evaluates the prefix of every selected arc to one.  Consequently every odd
subfamily of arcs has nonzero image in the real-edge quotient.

This is a countermodel to a graph-independent arborescence/Laplacian prefix
contraction, not to FIFO linking.  It leaves open an identity using correlated
continuation representatives from the fixed strategy tree.
-/

namespace Ogdoad.Fifo

noncomputable section

/-- A fixed-point-free functional digraph with cycles `0 <-> 1`, `4 <-> 5`
and in-tree edges `3 -> 2 -> 1`, `6 -> 4`. -/
def arborescenceReply : Fin 7 → Fin 7 := ![1, 0, 1, 2, 5, 4, 4]

theorem arborescenceReply_ne (x : Fin 7) : arborescenceReply x ≠ x := by
  fin_cases x <;> decide

/-- A real-edge separator with edges `1--3` and `5--6`; label `0` is an
isolated dummy.  Its degree-parity colouring alternates on every selected
arc of `arborescenceReply`. -/
def arborescenceSeparatorGraph : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel fun x y ↦
    (x = 1 ∧ y = 3) ∨ (x = 5 ∧ y = 6)

theorem arborescenceSeparatorGraph_dummy :
    IsDummy arborescenceSeparatorGraph 0 := by
  intro v
  fin_cases v <;>
    simp [arborescenceSeparatorGraph, SimpleGraph.fromRel_adj]

/-- The separator evaluates every selected two-OPEN arc prefix to one,
including every edge in both in-trees. -/
theorem graphEvaluation_arborescenceArcPrefix (x : Fin 7) :
    graphEvaluation arborescenceSeparatorGraph
        (twoOpenArcPrefix Finset.univ (x, arborescenceReply x)) = 1 := by
  rw [twoOpenArcPrefix, map_add,
    graphEvaluation_liveStarVector, graphEvaluation_liveStarVector]
  fin_cases x <;>
    norm_num [flip, arborescenceReply, arborescenceSeparatorGraph,
      SimpleGraph.fromRel_adj] <;>
    decide

/-- The aggregate separator value of a list of selected arcs is exactly the
list length modulo two. -/
theorem graphEvaluation_sum_arborescenceArcPrefixes (xs : List (Fin 7)) :
    graphEvaluation arborescenceSeparatorGraph
        (xs.map fun x ↦
          twoOpenArcPrefix Finset.univ (x, arborescenceReply x)).sum =
      (xs.length : ZMod 2) := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      rw [List.map_cons, List.sum_cons, map_add,
        graphEvaluation_arborescenceArcPrefix, ih]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      exact add_comm _ _

/-- Even after the full functional digraph and all its fibers are available,
no odd list of selected arc prefixes contracts in the isolated-dummy
real-edge quotient.  Thus an arborescence sum must use continuation-coset
data, not only the incidence of `x -> reply x`. -/
theorem odd_arborescenceArcPrefixes_projection_ne_zero
    (xs : List (Fin 7)) (hodd : xs.length % 2 = 1) :
    realEdgeProjection 0
        (xs.map fun x ↦
          twoOpenArcPrefix Finset.univ (x, arborescenceReply x)).sum ≠ 0 := by
  intro hzero
  have hevalZero :
      graphEvaluation arborescenceSeparatorGraph
          (xs.map fun x ↦
            twoOpenArcPrefix Finset.univ (x, arborescenceReply x)).sum = 0 :=
    graphEvaluation_eq_zero_of_realEdgeProjection_eq_zero
      arborescenceSeparatorGraph_dummy hzero
  rw [graphEvaluation_sum_arborescenceArcPrefixes] at hevalZero
  have hcast : (xs.length : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod xs.length 2, hodd]
    rfl
  rw [hcast] at hevalZero
  exact one_ne_zero hevalZero

end

end Ogdoad.Fifo
