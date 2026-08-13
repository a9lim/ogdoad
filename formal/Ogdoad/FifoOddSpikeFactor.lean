import Ogdoad.FifoStrategyBadAncestry
import Ogdoad.FifoOuterFan

/-!
# Strategy-relative odd-spike punctured fans

The charged-`CLOSE` branch of the minimal bad-ancestry trichotomy has more
same-root structure than the bare two-close spike records.  Every alternative
defender `OPEN z` at the spike parent has the same rank as the minimal
score-zero child, starts on score sheet one, and remains on that sheet
throughout its exact strategy subtree.  Translating by one therefore turns
each such punctured sibling into a completely score-neutral strategy.

The first selected move in a punctured sibling is consequently restricted.
If it closes the old front `y`, then `z` is adjacent to both spike fronts.
If it opens another vertex `w`, the `y`-row changes colour across the selected
arc `z -> w`.  Thus a no-close punctured fan is a row-alternating functional
digraph; its directed cycles are necessarily even.  This is genuine
same-root causal information, but it does not itself choose the odd affine
incidence required by the factor-extension conjecture.

The final construction makes that limit exact.  A five-vertex legal history
reaches a score-one charged spike with a real OPEN sink and a dummy feeder.
One exact local odd strategy contains all three relevant siblings, yet after
recursively expanding their selected continuations every projected response
direction vanishes and the two basin contributions cancel, leaving the
nonzero history prefix.  Hence basin expansion alone cannot prove the needed
factor equation.  Its exact upward-extension failure is also identified:
at the earlier defender node after two OPENs, opening the real centre enters
an explicitly constructed even-winning sibling.  Thus no odd strategy exists
at that ancestor, so the local obstruction is not a counterexample to FIFO
linking.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A proper descendant in an exact strategy tree has strictly smaller game
rank.  The only rank-preserving subtree membership is the root itself. -/
theorem StrategyNode.state_eq_or_rank_lt
    {G : SimpleGraph V} {seat : Bool} {s t : State V}
    {root : OddStrategy G seat s} {desc : OddStrategy G seat t}
    (h : StrategyNode G seat root desc) : t = s ∨ rank t < rank s := by
  cases h with
  | root => exact Or.inl rfl
  | @choose s s' t hseat m hstep child desc hdesc =>
      exact Or.inr (lt_of_le_of_lt hdesc.rank_le (rank_step_lt hstep))
  | @answer s s' t hseat hasMove children m hstep desc hdesc =>
      exact Or.inr (lt_of_le_of_lt hdesc.rank_le (rank_step_lt hstep))

/-- The canonical state after an alternative `OPEN z` at an odd-spike
defender parent. -/
private def oddSpikeOpenState (parent : State V) (z : V) : State V where
  untouched := parent.untouched.erase z
  queue := parent.queue ++ [z]
  ko := parent.queue.isEmpty
  toMove := !parent.toMove
  score := parent.score

/-- Every punctured sibling of a strategy-relative charged-CLOSE spike is an
exact same-root subtree which stays entirely on score sheet one.  Translating
that subtree by one gives a transition-by-transition neutral strategy. -/
theorem MinimalBadPredecessorCase.chargedClose_openSibling_neutral
    {G : SimpleGraph V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    {s parent : State V} {pp : EdgeVector V} {f : V} {q : List V}
    (hfan : ∀ m t, step G parent m = some t →
      ∃ childTree : OddStrategy G seat t,
        StrategyPrefix G seat root childTree
          (pp + moveLiveStar parent m))
    (hincoming : step G parent .close = some s)
    (hminimal : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat root desc →
      rank t < rank s → t.score ≠ 0)
    (hcase : MinimalBadPredecessorCase G parent s f q .close)
    {z : V} (hz : z ∈ parent.untouched) :
    ∃ (sz : State V) (szTree : OddStrategy G seat sz),
      step G parent (.open z) = some sz ∧
      StrategyPrefix G seat root szTree
        (pp + moveLiveStar parent (.open z)) ∧
      sz.untouched = parent.untouched.erase z ∧
      sz.queue = parent.queue ++ [z] ∧
      sz.ko = false ∧ sz.toMove = !parent.toMove ∧
      sz.score = 1 ∧ rank sz = rank s ∧
      (∀ {t : State V} {desc : OddStrategy G seat t},
        StrategyNode G seat szTree desc → t.score = 1) ∧
      TreeNeutralWins G (!seat) (scoreTranslate 1 sz) := by
  classical
  cases hcase with
  | chargedClose y hqueue hko hU hscore hcharge =>
      let sz := oddSpikeOpenState parent z
      have hopen : step G parent (.open z) = some sz := by
        simp [step, sz, oddSpikeOpenState, hz]
      obtain ⟨szTree, hprefix⟩ := hfan (.open z) sz hopen
      have hnode : StrategyNode G seat root szTree :=
        hprefix.toStrategyNode
      have hszU : sz.untouched = parent.untouched.erase z := rfl
      have hszQueue : sz.queue = parent.queue ++ [z] := rfl
      have hszKo : sz.ko = false := by
        simp [sz, oddSpikeOpenState, hqueue]
      have hszTurn : sz.toMove = !parent.toMove := rfl
      have hszScore : sz.score = 1 := by
        simp [sz, oddSpikeOpenState, hscore]
      let cs : State V := {
        untouched := parent.untouched
        queue := f :: q
        ko := false
        toMove := !parent.toMove
        score := parent.score + flip G parent.untouched y }
      have hclose : step G parent .close = some cs := by
        simp [step, cs, hqueue, hko]
      have hsEq : s = cs := by
        rw [hincoming] at hclose
        exact Option.some.inj hclose
      have hszRank : rank sz = rank s := by
        have hcardPos : 0 < parent.untouched.card :=
          Finset.card_pos.mpr ⟨z, hz⟩
        rw [hsEq]
        simp [rank, sz, oddSpikeOpenState, cs, hqueue,
          Finset.card_erase_of_mem hz]
        omega
      have hone : ∀ {t : State V} {desc : OddStrategy G seat t},
          StrategyNode G seat szTree desc → t.score = 1 := by
        intro t desc hdesc
        rcases hdesc.state_eq_or_rank_lt with hroot | hlt
        · subst t
          exact hszScore
        · have hlt' : rank t < rank s := by
            rw [← hszRank]
            exact hlt
          exact zmod2_eq_one_of_ne_zero _
            (hminimal (hnode.trans hdesc) hlt')
      exact ⟨sz, szTree, hopen, hprefix, hszU, hszQueue, hszKo,
        hszTurn, hszScore, hszRank, hone,
        szTree.one_subtree_translates_neutral hone⟩

/-- The first selected response in a charged-spike punctured sibling.  A
selected old-front close places the puncture in the joint `11` fibre of the
two spike fronts.  A selected open crosses the old-front adjacency row. -/
inductive OddSpikeOpenReplyCase (G : SimpleGraph V)
    (U : Finset V) (y f z : V) : Move V → Prop
  | close
      (hyz : adjacencyBit G y z = 1)
      (hfz : adjacencyBit G f z = 1) :
      OddSpikeOpenReplyCase G U y f z .close
  | open (w : V) (hw : w ∈ U.erase z)
      (hrow : adjacencyBit G y z + adjacencyBit G y w = 1) :
      OddSpikeOpenReplyCase G U y f z (.open w)

omit [Fintype V] [DecidableEq V] in
private theorem list_sum_map_add {I : Type*} (is : List I)
    (a b : I → ZMod 2) :
    (is.map fun i ↦ a i + b i).sum =
      (is.map a).sum + (is.map b).sum := by
  induction is with
  | nil => simp
  | cons i rest ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      abel

omit [Fintype V] [DecidableEq V] in
private theorem list_perm_sum_eq {xs ys : List (ZMod 2)}
    (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons x h ih => simp [ih]
  | swap x y rest => exact add_left_comm y x rest.sum
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [Fintype V] [DecidableEq V] in
/-- A balanced directed family whose every arc crosses one binary row has
even cardinality.  In particular every directed cycle in a no-close
odd-spike reply graph is even. -/
theorem even_of_balanced_row_alternating
    (row : V → ZMod 2) (arcs : List (V × V))
    (hbalanced : (arcs.map Prod.fst).Perm (arcs.map Prod.snd))
    (halternating : ∀ e ∈ arcs, row e.1 + row e.2 = 1) :
    arcs.length % 2 = 0 := by
  have hsumOne :
      (arcs.map fun e ↦ row e.1 + row e.2).sum =
        (arcs.length : ZMod 2) := by
    clear hbalanced
    induction arcs with
    | nil => simp
    | cons e rest ih =>
        have he : row e.1 + row e.2 = 1 :=
          halternating e (by simp)
        have hrest : ∀ a ∈ rest, row a.1 + row a.2 = 1 := by
          intro a ha
          exact halternating a (by simp [ha])
        rw [List.map_cons, List.sum_cons, he, ih hrest]
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        exact add_comm _ _
  have hperm :
      (arcs.map fun e ↦ row e.1).Perm
        (arcs.map fun e ↦ row e.2) := by
    simpa only [List.map_map, Function.comp_def] using
      hbalanced.map row
  have hsumEq :
      (arcs.map fun e ↦ row e.1).sum =
        (arcs.map fun e ↦ row e.2).sum :=
    list_perm_sum_eq hperm
  have hsumZero :
      (arcs.map fun e ↦ row e.1 + row e.2).sum = 0 := by
    rw [list_sum_map_add arcs (fun e ↦ row e.1) (fun e ↦ row e.2),
      hsumEq]
    exact CharTwo.add_self_eq_zero _
  have hcastZero : (arcs.length : ZMod 2) = 0 :=
    hsumOne.symm.trans hsumZero
  by_contra hne
  have hodd : arcs.length % 2 = 1 := by omega
  have hcastOdd : (arcs.length : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod arcs.length 2, hodd]
    rfl
  rw [hcastOdd] at hcastZero
  exact one_ne_zero hcastZero

omit [Fintype V] in
/-- Exact indegree-weight identity for the partial functional digraph exposed
by an odd spike.  Vertices in `C` are CLOSE sinks and therefore have row
value one; every other vertex points across the row.  If the charged front
row has total value one on `U`, then the successor multiset has row weight
`|U| + 1`, independently of the number of sinks.

Equivalently, the number (with indegree multiplicity) of OPEN arcs landing in
the row-one fibre is odd exactly when `U` is even.  This is the complete
first-response parity identity; it does not force a CLOSE sink. -/
theorem partialReply_successor_row_sum
    (U C : Finset V) (row : V → ZMod 2) (next : V → V)
    (hCU : C ⊆ U)
    (hrow : ∑ z ∈ U, row z = 1)
    (hsink : ∀ z ∈ C, row z = 1)
    (hopen : ∀ z ∈ U \ C, row z + row (next z) = 1) :
    ∑ z ∈ U \ C, row (next z) = (U.card : ZMod 2) + 1 := by
  classical
  have hsinkSum :
      (∑ z ∈ C, row z) = (C.card : ZMod 2) := by
    calc
      (∑ z ∈ C, row z) = ∑ _z ∈ C, (1 : ZMod 2) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact hsink z hz
      _ = (C.card : ZMod 2) := by simp
  have hsplit := Finset.sum_sdiff hCU (f := row)
  rw [hrow, hsinkSum] at hsplit
  have hopenDomainSum :
      (∑ z ∈ U \ C, row z) = 1 + (C.card : ZMod 2) := by
    calc
      (∑ z ∈ U \ C, row z) =
          ((∑ z ∈ U \ C, row z) + (C.card : ZMod 2)) +
            (C.card : ZMod 2) := by
              rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = 1 + (C.card : ZMod 2) := by rw [hsplit]
  have hpoint : ∀ z ∈ U \ C, row (next z) = 1 + row z := by
    intro z hz
    calc
      row (next z) = (row z + row z) + row (next z) := by
        rw [CharTwo.add_self_eq_zero, zero_add]
      _ = row z + (row z + row (next z)) := by abel
      _ = row z + 1 := by rw [hopen z hz]
      _ = 1 + row z := add_comm _ _
  have hcardNat := Finset.card_sdiff_add_card_eq_card hCU
  have hcard := congrArg (fun n : Nat ↦ (n : ZMod 2)) hcardNat
  simp only [Nat.cast_add] at hcard
  calc
    (∑ z ∈ U \ C, row (next z)) =
        ∑ z ∈ U \ C, (1 + row z) := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hpoint z hz
    _ = (U \ C).card • (1 : ZMod 2) +
        ∑ z ∈ U \ C, row z := by
          rw [Finset.sum_add_distrib]
          simp
    _ = ((U \ C).card : ZMod 2) + 1 + (C.card : ZMod 2) := by
          rw [hopenDomainSum]
          simp
          abel
    _ = (U.card : ZMod 2) + 1 := by
          rw [← hcard]
          abel

omit [Fintype V] [DecidableEq V] in
/-- Row weight decomposes exactly over any finite basin labelling.  Applied to
the functional components of the partial reply graph, the aggregate basin
weight remains the charged value one. -/
theorem sum_basin_rowWeight
    {K : Type*} [Fintype K] [DecidableEq K]
    (U : Finset V) (row : V → ZMod 2) (basin : V → K)
    (hrow : ∑ z ∈ U, row z = 1) :
    ∑ k : K, ∑ z ∈ U.filter (fun z ↦ basin z = k), row z = 1 := by
  classical
  calc
    (∑ k : K, ∑ z ∈ U.filter (fun z ↦ basin z = k), row z) =
        ∑ k : K, ∑ z ∈ U, if basin z = k then row z else 0 := by
          apply Finset.sum_congr rfl
          intro k _hk
          exact Finset.sum_filter (fun z ↦ basin z = k) row
    _ = ∑ z ∈ U, ∑ k : K, if basin z = k then row z else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ z ∈ U, row z := by
          apply Finset.sum_congr rfl
          intro z _hz
          rw [Finset.sum_eq_single (basin z)]
          · simp
          · intro k _hk hne
            simp [hne.symm]
          · simp
    _ = 1 := hrow

omit [Fintype V] [DecidableEq V] in
/-- The number of functional basins carrying row weight one is odd.  This is
the sharp basin conclusion of the charged row parity.  It does not say that
the odd-weight basin terminates at a CLOSE sink; it may be an even-cycle
component with a feeding in-tree. -/
theorem basin_rowWeight_one_count_odd
    {K : Type*} [Fintype K] [DecidableEq K]
    (U : Finset V) (row : V → ZMod 2) (basin : V → K)
    (hrow : ∑ z ∈ U, row z = 1) :
    (Finset.univ.filter (fun k ↦
      (∑ z ∈ U.filter (fun z ↦ basin z = k), row z) = 1)).card % 2 = 1 := by
  classical
  let weight : K → ZMod 2 := fun k ↦
    ∑ z ∈ U.filter (fun z ↦ basin z = k), row z
  change (Finset.univ.filter (fun k ↦ weight k = 1)).card % 2 = 1
  have hweight : ∑ k : K, weight k = 1 := by
    simpa only [weight] using sum_basin_rowWeight U row basin hrow
  have hpoint : ∀ k : K,
      (if weight k = 1 then (1 : ZMod 2) else 0) = weight k := by
    intro k
    by_cases hk : weight k = 1
    · simp [hk]
    · simp [zmod2_eq_zero_of_ne_one (weight k) hk]
  have hcardCast :
      ((Finset.univ.filter (fun k ↦ weight k = 1)).card : ZMod 2) = 1 := by
    calc
      ((Finset.univ.filter (fun k ↦ weight k = 1)).card : ZMod 2) =
          ∑ k : K, if weight k = 1 then (1 : ZMod 2) else 0 := by
            simp
      _ = ∑ k : K, weight k := by
            apply Finset.sum_congr rfl
            intro k _hk
            exact hpoint k
      _ = 1 := hweight
  have hcastMod :
      (((Finset.univ.filter (fun k ↦ weight k = 1)).card % 2 : Nat) :
          ZMod 2) = 1 := by
    calc
      (((Finset.univ.filter (fun k ↦ weight k = 1)).card % 2 : Nat) :
          ZMod 2) =
          ((Finset.univ.filter (fun k ↦ weight k = 1)).card :
            ZMod 2) := ZMod.natCast_mod _ 2
      _ = 1 := hcardCast
  by_contra hne
  have hlt :
      (Finset.univ.filter (fun k ↦ weight k = 1)).card % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  have heven :
      (Finset.univ.filter (fun k ↦ weight k = 1)).card % 2 = 0 := by
    omega
  rw [heven] at hcastMod
  exact zero_ne_one hcastMod

/-! ### Sharpness: the charged row need not produce any CLOSE sink -/

/-- A three-vertex row of total weight one. -/
def noSinkSpikeRow : Fin 3 → ZMod 2 := ![0, 0, 1]

/-- A fixed-point-free reply map with one even two-cycle and one feeding
vertex: `0 -> 2 -> 0` and `1 -> 2`. -/
def noSinkSpikeNext : Fin 3 → Fin 3 := ![2, 2, 0]

theorem noSinkSpikeNext_ne_and_alternating (z : Fin 3) :
    noSinkSpikeNext z ≠ z ∧
      noSinkSpikeRow z + noSinkSpikeRow (noSinkSpikeNext z) = 1 := by
  fin_cases z <;> decide

theorem sum_noSinkSpikeRow :
    ∑ z : Fin 3, noSinkSpikeRow z = 1 := by decide

/-- The exact successor-row identity is compatible with no CLOSE sinks at
all.  Hence neither the charged row nor cycle evenness forces an odd number
of CLOSE-selected punctures. -/
theorem noSink_partialReply_successor_row_sum :
    ∑ z ∈ (Finset.univ : Finset (Fin 3)) \ ∅,
        noSinkSpikeRow (noSinkSpikeNext z) =
      ((Finset.univ : Finset (Fin 3)).card : ZMod 2) + 1 := by
  apply partialReply_successor_row_sum
  · simp
  · simpa using sum_noSinkSpikeRow
  · simp
  · intro z _hz
    exact (noSinkSpikeNext_ne_and_alternating z).2

/-! ## Exact affine carrier left by the smallest sink basin -/

omit [Fintype V] in
/-- If one descendant affine space has constant projected value, every one
of its continuation directions projects to zero. -/
theorem ResponseDirection.projection_eq_zero_of_affine_constant
    {G : SimpleGraph V} {d : V} {seat : Bool} {s : State V}
    {tree : OddStrategy G seat s} {b q : EdgeVector V}
    (hconstant : ∀ z, AffineResponseMoment G seat tree z →
      realEdgeProjection d z = realEdgeProjection d b)
    (hq : ResponseDirection G seat tree q) :
    realEdgeProjection d q = 0 := by
  obtain ⟨x, y, hx, hy, rfl⟩ := hq
  rw [map_add, hconstant x hx, hconstant y hy]
  rw [← map_add]
  have hself : b + b = 0 := by
    ext e
    exact CharTwo.add_self_eq_zero _
  rw [hself, map_zero]

omit [Fintype V] in
/-- The smallest charged-spike basin has three causal holes: the selected
spike, its CLOSE-sink sibling, and one feeder sibling.  If the selected
decorated coset is the unit carrier `e`, both off-spine decorated cosets are
zero, and all three continuation direction spaces are silent, then expanding
the entire basin cannot satisfy the projected ancestry-factor equation.

This is the exact algebra of the three-real legal response tree in the paper:
the sink and feeder cancel only each other, leaving the selected two-edge
curvature.  The result quantifies over arbitrary representatives and
directions in all three continuation cosets. -/
theorem oddSpike_twoVertexBasin_factor_impossible
    {G : SimpleGraph V} {d : V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    (selected sink feeder : StrategyHole G seat hroot)
    (e : EdgeVector V)
    (hene : realEdgeProjection d e ≠ 0)
    (hselected : ∀ a, AffineResponseMoment G seat selected.tree a →
      realEdgeProjection d (selected.moment + a) =
        realEdgeProjection d e)
    (hsink : ∀ a, AffineResponseMoment G seat sink.tree a →
      realEdgeProjection d (sink.moment + a) = 0)
    (hfeeder : ∀ a, AffineResponseMoment G seat feeder.tree a →
      realEdgeProjection d (feeder.moment + a) = 0) :
    ∀ (aS aC aF dS dC dF : EdgeVector V),
      AffineResponseMoment G seat selected.tree aS →
      AffineResponseMoment G seat sink.tree aC →
      AffineResponseMoment G seat feeder.tree aF →
      ResponseDirection G seat selected.tree dS →
      ResponseDirection G seat sink.tree dC →
      ResponseDirection G seat feeder.tree dF →
      realEdgeProjection d
          ((selected.moment + aS) +
            (sink.moment + aC) + (feeder.moment + aF)) ≠
        realEdgeProjection d (dS + dC + dF) := by
  intro aS aC aF dS dC dF haS haC haF hdS hdC hdF heq
  have hdS0 : realEdgeProjection d dS = 0 := by
    apply hdS.projection_eq_zero_of_affine_constant (b := aS)
    intro z hz
    have hSa := hselected aS haS
    have hSz := hselected z hz
    have hpref : realEdgeProjection d selected.moment +
        realEdgeProjection d aS =
      realEdgeProjection d selected.moment +
        realEdgeProjection d z := by
      simpa only [map_add] using hSa.trans hSz.symm
    exact (add_left_cancel hpref).symm
  have hdC0 : realEdgeProjection d dC = 0 := by
    apply hdC.projection_eq_zero_of_affine_constant (b := aC)
    intro z hz
    have hCa := hsink aC haC
    have hCz := hsink z hz
    have hpref : realEdgeProjection d sink.moment +
        realEdgeProjection d aC =
      realEdgeProjection d sink.moment +
        realEdgeProjection d z := by
      simpa only [map_add] using hCa.trans hCz.symm
    exact (add_left_cancel hpref).symm
  have hdF0 : realEdgeProjection d dF = 0 := by
    apply hdF.projection_eq_zero_of_affine_constant (b := aF)
    intro z hz
    have hFa := hfeeder aF haF
    have hFz := hfeeder z hz
    have hpref : realEdgeProjection d feeder.moment +
        realEdgeProjection d aF =
      realEdgeProjection d feeder.moment +
        realEdgeProjection d z := by
      simpa only [map_add] using hFa.trans hFz.symm
    exact (add_left_cancel hpref).symm
  have hleft :
      realEdgeProjection d
          ((selected.moment + aS) +
            (sink.moment + aC) + (feeder.moment + aF)) =
        realEdgeProjection d e := by
    rw [map_add, map_add, hselected aS haS, hsink aC haC,
      hfeeder aF haF, add_zero, add_zero]
  have hright : realEdgeProjection d (dS + dC + dF) = 0 := by
    rw [map_add, map_add, hdS0, hdC0, hdF0, add_zero, add_zero]
  rw [hleft, hright] at heq
  exact hene heq

/-! ## Semantic realization of the two-vertex basin -/

/-- No graph edge crosses from an untouched vertex to any still-live vertex.
This is the exact condition under which every future FIFO close is neutral. -/
def NoLiveCut (G : SimpleGraph V) (s : State V) : Prop :=
  ∀ u ∈ s.untouched, ∀ v ∈ liveSet s, ¬G.Adj u v

omit [Fintype V] in
private theorem untouched_subset_of_step
    {G : SimpleGraph V} {s t : State V} {m : Move V}
    (hstep : step G s m = some t) : t.untouched ⊆ s.untouched := by
  intro v hv
  cases m with
  | «open» z =>
      simp only [step] at hstep
      split at hstep
      · cases hstep
        exact Finset.mem_of_mem_erase hv
      · contradiction
  | close =>
      simp only [step] at hstep
      split at hstep
      · contradiction
      · split at hstep
        · contradiction
        · cases hstep
          exact hv
  | pass =>
      simp only [step] at hstep
      split at hstep
      · cases hstep
        exact hv
      · contradiction

omit [Fintype V] in
private theorem liveSet_subset_of_step
    {G : SimpleGraph V} {s t : State V} {m : Move V}
    (hstep : step G s m = some t) : liveSet t ⊆ liveSet s := by
  intro v hv
  cases m with
  | «open» z =>
      simp only [step] at hstep
      split at hstep
      · rename_i hz
        cases hstep
        simp only [liveSet, List.toFinset_append, Finset.mem_union] at hv ⊢
        simp only [List.toFinset_cons, List.toFinset_nil,
          Finset.mem_insert] at hv
        rcases hv with hvU | hvq | hvz
        · exact Or.inl (Finset.mem_of_mem_erase hvU)
        · exact Or.inr hvq
        · rcases hvz with rfl | hfalse
          · exact Or.inl hz
          · simp at hfalse
      · contradiction
  | close =>
      simp only [step] at hstep
      split at hstep
      · contradiction
      · rename_i f q hqueue
        split at hstep
        · contradiction
        · cases hstep
          simp only [liveSet, Finset.mem_union] at hv ⊢
          rcases hv with hvU | hvq
          · exact Or.inl hvU
          · exact Or.inr (by
              rw [hqueue]
              simp only [List.toFinset_cons, Finset.mem_insert]
              exact Or.inr hvq)
  | pass =>
      simp only [step] at hstep
      split at hstep
      · cases hstep
        exact hv
      · contradiction

omit [Fintype V] in
theorem noLiveCut_step
    {G : SimpleGraph V} {s t : State V} {m : Move V}
    (h : NoLiveCut G s) (hstep : step G s m = some t) :
    NoLiveCut G t := by
  intro u hu v hv
  exact h u (untouched_subset_of_step hstep hu)
    v (liveSet_subset_of_step hstep hv)

omit [Fintype V] in
theorem noLiveCut_step_score_eq
    {G : SimpleGraph V} {s t : State V} {m : Move V}
    (h : NoLiveCut G s) (hstep : step G s m = some t) :
    t.score = s.score := by
  classical
  cases m with
  | «open» z => exact open_score hstep
  | pass => exact pass_score hstep
  | close =>
      obtain ⟨f, q, hqueue, hscore⟩ := close_score hstep
      have hfilter : s.untouched.filter (G.Adj f) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro v hv
        have hfLive : f ∈ liveSet s := by
          simp [liveSet, hqueue]
        exact fun hadj ↦ h v hv f hfLive (G.adj_symm hadj)
      have hflip : flip G s.untouched f = 0 := by
        simp [flip, hfilter]
      rw [hscore, hflip, add_zero]

omit [Fintype V] in
/-- A no-live-cut state on score one admits an exact odd strategy for either
distinguished seat.  The proof retains the terminating strategy tree. -/
theorem oddWins_of_noLiveCut
    {G : SimpleGraph V} (seat : Bool) (s : State V)
    (hcut : NoLiveCut G s) (hscore : s.score ≠ 0) :
    OddWins G seat s := by
  induction s using (measure rank).wf.induction with
  | h s ih =>
      by_cases hterminal : Terminal s
      · exact OddWins.terminal s hterminal hscore
      · have hasMove : ∃ m t, step G s m = some t :=
          not_terminal_has_step hterminal
        by_cases hseat : s.toMove = seat
        · refine OddWins.answer s hseat hasMove ?_
          intro m t hstep
          have htScore : t.score ≠ 0 := by
            rw [noLiveCut_step_score_eq hcut hstep]
            exact hscore
          exact ih t (rank_step_lt hstep)
            (noLiveCut_step hcut hstep) htScore
        · obtain ⟨m, t, hstep⟩ := hasMove
          have htScore : t.score ≠ 0 := by
            rw [noLiveCut_step_score_eq hcut hstep]
            exact hscore
          exact OddWins.choose s hseat m t hstep
            (ih t (rank_step_lt hstep)
              (noLiveCut_step hcut hstep) htScore)

/-- Every legal future OPEN either opens the dummy or is the sole live real
vertex.  This is exactly the carrier condition making all future universal
live-star moments vanish in the real-edge quotient. -/
def ProjectionSilentCarrier (d : V) (s : State V) : Prop :=
  ∀ v ∈ s.untouched,
    v = d ∨ ∀ w ∈ liveSet s, w = d ∨ w = v

omit [Fintype V] in
theorem projectionSilentCarrier_step
    {G : SimpleGraph V} {d : V} {s t : State V} {m : Move V}
    (h : ProjectionSilentCarrier d s)
    (hstep : step G s m = some t) : ProjectionSilentCarrier d t := by
  intro v hv
  rcases h v (untouched_subset_of_step hstep hv) with rfl | hvOnly
  · exact Or.inl rfl
  · exact Or.inr fun w hw ↦
      hvOnly w (liveSet_subset_of_step hstep hw)

omit [Fintype V] in
theorem realEdgeProjection_moveLiveStar_eq_zero_of_silentCarrier
    {G : SimpleGraph V} {d : V} {s t : State V} {m : Move V}
    (h : ProjectionSilentCarrier d s)
    (hstep : step G s m = some t) :
    realEdgeProjection d (moveLiveStar s m) = 0 := by
  classical
  cases m with
  | close => simp [moveLiveStar]
  | pass => simp [moveLiveStar]
  | «open» v =>
      have hv : v ∈ s.untouched := by
        simp only [step] at hstep
        split at hstep
        · assumption
        · contradiction
      rcases h v hv with hvd | hvOnly
      · rw [hvd]
        exact realEdgeProjection_liveStarVector_dummy d (liveSet s)
      · rw [moveLiveStar, liveStarVector, map_sum]
        apply Finset.sum_eq_zero
        intro w hw
        have hwLive : w ∈ liveSet s := Finset.mem_of_mem_erase hw
        have hwne : w ≠ v := Finset.ne_of_mem_erase hw
        rcases hvOnly w hwLive with hwd | hwv
        · rw [hwd]
          have hsym : s(v, d) = s(d, v) := Sym2.eq_swap
          rw [hsym, realEdgeProjection_dummy_single]
        · exact False.elim (hwne hwv)

omit [Fintype V] in
/-- Under `ProjectionSilentCarrier`, every affine response representative of
every exact strategy has zero real-edge projection. -/
theorem AffineResponseMoment.projection_eq_zero_of_silentCarrier
    {G : SimpleGraph V} {d : V} {seat : Bool} {s : State V}
    {tree : OddStrategy G seat s} {z : EdgeVector V}
    (hz : AffineResponseMoment G seat tree z)
    (hcarrier : ProjectionSilentCarrier d s) :
    realEdgeProjection d z = 0 := by
  induction hz with
  | terminal => simp
  | @choose s t hseat m hstep child z tail ih =>
      rw [map_add,
        realEdgeProjection_moveLiveStar_eq_zero_of_silentCarrier
          hcarrier hstep,
        ih (projectionSilentCarrier_step hcarrier hstep), zero_add]
  | @answerChild s t hseat hasMove children m hstep z tail ih =>
      rw [map_add,
        realEdgeProjection_moveLiveStar_eq_zero_of_silentCarrier
          hcarrier hstep,
        ih (projectionSilentCarrier_step hcarrier hstep), zero_add]
  | ternary hx hy hz ihx ihy ihz =>
      rw [map_add, map_add, ihx hcarrier, ihy hcarrier, ihz hcarrier,
        add_zero, add_zero]

omit [Fintype V] in
/-- If one selected move enters a projection-silent carrier, the entire
affine response space at the selected node is the single projected move
star.  Ternary affine closure does not enlarge that singleton because three
copies of one vector sum to the same vector in characteristic two. -/
theorem AffineResponseMoment.projection_eq_move_of_choose_silentCarrier
    {G : SimpleGraph V} {d : V} {seat : Bool} {s t : State V}
    {hseat : s.toMove ≠ seat} {m : Move V}
    {hstep : step G s m = some t} {tail : OddStrategy G seat t}
    {z : EdgeVector V}
    (hz : AffineResponseMoment G seat
      (OddStrategy.choose s hseat m t hstep tail) z)
    (hcarrier : ProjectionSilentCarrier d t) :
    realEdgeProjection d z =
      realEdgeProjection d (moveLiveStar s m) := by
  generalize htree :
    OddStrategy.choose s hseat m t hstep tail = tree at hz
  induction hz with
  | terminal => cases htree
  | choose htail ih =>
      cases htree
      rw [map_add,
        htail.projection_eq_zero_of_silentCarrier hcarrier, add_zero]
  | answerChild => cases htree
  | @ternary s' h x y z hx hy hz ihx ihy ihz =>
      rw [map_add, map_add, ihx htree, ihy htree, ihz htree]
      let c := realEdgeProjection d (moveLiveStar s' m)
      change c + c + c = c
      have hself : c + c = 0 := by
        calc
          c + c = (1 : ZMod 2) • c + (1 : ZMod 2) • c := by simp
          _ = ((1 : ZMod 2) + 1) • c := (add_smul 1 1 c).symm
          _ = 0 := by
            have h11 : (1 : ZMod 2) + 1 = 0 := by decide
            rw [h11, zero_smul]
      calc
        c + c + c = 0 + c := by rw [hself]
        _ = c := zero_add c

/-! ## Exact two-vertex feeder basin -/

/-- The smallest charged-spike board carrying both a real OPEN sink and a
dummy feeder.  Vertices `0,1` are the two charged queue fronts, `2` is their
common real neighbour, and `3` is isolated. -/
def twoVertexBasinGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun x y ↦
    (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 2)

theorem twoVertexBasinGraph_dummy :
    IsDummy twoVertexBasinGraph 3 := by
  intro v
  fin_cases v <;>
    simp [twoVertexBasinGraph, SimpleGraph.fromRel_adj]

/-- Local score-one charged-CLOSE parent.  It is a semantic same-tree
checkpoint, not asserted to be reachable from the initial board. -/
def twoVertexBasinParent : State (Fin 4) where
  untouched := {2, 3}
  queue := [0, 1]
  ko := false
  toMove := false
  score := 1

private def twoVertexBasinSelected : State (Fin 4) where
  untouched := {2, 3}
  queue := [1]
  ko := false
  toMove := true
  score := 0

private def twoVertexBasinSelectedTail : State (Fin 4) where
  untouched := {2, 3}
  queue := []
  ko := false
  toMove := false
  score := 1

private def twoVertexBasinSink : State (Fin 4) where
  untouched := {3}
  queue := [0, 1, 2]
  ko := false
  toMove := true
  score := 1

private def twoVertexBasinSinkTail : State (Fin 4) where
  untouched := {3}
  queue := [1, 2]
  ko := false
  toMove := false
  score := 1

private def twoVertexBasinFeeder : State (Fin 4) where
  untouched := {2}
  queue := [0, 1, 3]
  ko := false
  toMove := true
  score := 1

private def twoVertexBasinFeederTail : State (Fin 4) where
  untouched := ∅
  queue := [0, 1, 3, 2]
  ko := false
  toMove := false
  score := 1

private theorem twoVertexBasin_step_selected :
    step twoVertexBasinGraph twoVertexBasinParent .close =
      some twoVertexBasinSelected := by
  simp [step, twoVertexBasinGraph, SimpleGraph.fromRel_adj,
    twoVertexBasinParent, twoVertexBasinSelected, flip]
  decide

private theorem twoVertexBasin_step_selectedTail :
    step twoVertexBasinGraph twoVertexBasinSelected .close =
      some twoVertexBasinSelectedTail := by
  simp [step, twoVertexBasinGraph, SimpleGraph.fromRel_adj,
    twoVertexBasinSelected, twoVertexBasinSelectedTail, flip]
  decide

private theorem twoVertexBasin_step_sink :
    step twoVertexBasinGraph twoVertexBasinParent (.open 2) =
      some twoVertexBasinSink := by
  simp [step, twoVertexBasinParent, twoVertexBasinSink]

private theorem twoVertexBasin_step_sinkTail :
    step twoVertexBasinGraph twoVertexBasinSink .close =
      some twoVertexBasinSinkTail := by
  simp [step, twoVertexBasinGraph, SimpleGraph.fromRel_adj,
    twoVertexBasinSink, twoVertexBasinSinkTail, flip]
  decide

private theorem twoVertexBasin_step_feeder :
    step twoVertexBasinGraph twoVertexBasinParent (.open 3) =
      some twoVertexBasinFeeder := by
  simp [step, twoVertexBasinParent, twoVertexBasinFeeder]
  decide

private theorem twoVertexBasin_step_feederTail :
    step twoVertexBasinGraph twoVertexBasinFeeder (.open 2) =
      some twoVertexBasinFeederTail := by
  simp [step, twoVertexBasinFeeder, twoVertexBasinFeederTail]

private theorem twoVertexBasin_selectedTail_noLiveCut :
    NoLiveCut twoVertexBasinGraph twoVertexBasinSelectedTail := by
  intro u hu v hv
  fin_cases u <;> fin_cases v <;>
    simp [twoVertexBasinSelectedTail, liveSet,
      twoVertexBasinGraph, SimpleGraph.fromRel_adj] at hu hv ⊢

private theorem twoVertexBasin_sinkTail_noLiveCut :
    NoLiveCut twoVertexBasinGraph twoVertexBasinSinkTail := by
  intro u hu v hv
  fin_cases u <;> fin_cases v <;>
    simp [twoVertexBasinSinkTail, liveSet,
      twoVertexBasinGraph, SimpleGraph.fromRel_adj] at hu hv ⊢

private theorem twoVertexBasin_feederTail_noLiveCut :
    NoLiveCut twoVertexBasinGraph twoVertexBasinFeederTail := by
  intro u hu
  fin_cases u <;> simp [twoVertexBasinFeederTail] at hu

private theorem twoVertexBasin_selectedTail_silent :
    ProjectionSilentCarrier 3 twoVertexBasinSelectedTail := by
  intro v hv
  fin_cases v <;>
    simp [twoVertexBasinSelectedTail, liveSet] at hv ⊢

private theorem twoVertexBasin_sink_silent :
    ProjectionSilentCarrier 3 twoVertexBasinSink := by
  intro v hv
  fin_cases v <;> simp [twoVertexBasinSink] at hv ⊢

private theorem twoVertexBasin_feederTail_silent :
    ProjectionSilentCarrier 3 twoVertexBasinFeederTail := by
  intro v hv
  fin_cases v <;> simp [twoVertexBasinFeederTail] at hv

/-- The CLOSE sink and dummy feeder occur as siblings in one exact local
odd strategy.  Their continuation affine spaces are projection singletons:
the selected charged-CLOSE continuation and the real OPEN sink contribute
zero, while the dummy feeder contributes exactly the later `OPEN 2` star. -/
theorem exists_sameTree_twoVertexBasin_continuationConstants :
    ∃ (parentTree : OddStrategy twoVertexBasinGraph false
          twoVertexBasinParent)
      (selectedTree : OddStrategy twoVertexBasinGraph false
          twoVertexBasinSelected)
      (sinkTree : OddStrategy twoVertexBasinGraph false
          twoVertexBasinSink)
      (feederTree : OddStrategy twoVertexBasinGraph false
          twoVertexBasinFeeder),
      StrategyPrefix twoVertexBasinGraph false parentTree selectedTree 0 ∧
      StrategyPrefix twoVertexBasinGraph false parentTree sinkTree
        (moveLiveStar twoVertexBasinParent (.open 2)) ∧
      StrategyPrefix twoVertexBasinGraph false parentTree feederTree
        (moveLiveStar twoVertexBasinParent (.open 3)) ∧
      selectedTree.selectedMove = some .close ∧
      sinkTree.selectedMove = some .close ∧
      feederTree.selectedMove = some (.open 2) ∧
      (∀ z, AffineResponseMoment twoVertexBasinGraph false selectedTree z →
        realEdgeProjection 3 z = 0) ∧
      (∀ z, AffineResponseMoment twoVertexBasinGraph false sinkTree z →
        realEdgeProjection 3 z = 0) ∧
      (∀ z, AffineResponseMoment twoVertexBasinGraph false feederTree z →
        realEdgeProjection 3 z =
          realEdgeProjection 3
            (moveLiveStar twoVertexBasinParent (.open 2))) := by
  let selectedTail : OddStrategy twoVertexBasinGraph false
      twoVertexBasinSelectedTail :=
    Classical.choice
      ((oddWins_of_noLiveCut false twoVertexBasinSelectedTail
        twoVertexBasin_selectedTail_noLiveCut (by decide)).nonempty_oddStrategy)
  let selectedTree : OddStrategy twoVertexBasinGraph false
      twoVertexBasinSelected :=
    OddStrategy.choose twoVertexBasinSelected (by decide) .close
      twoVertexBasinSelectedTail twoVertexBasin_step_selectedTail selectedTail
  let sinkTail : OddStrategy twoVertexBasinGraph false
      twoVertexBasinSinkTail :=
    Classical.choice
      ((oddWins_of_noLiveCut false twoVertexBasinSinkTail
        twoVertexBasin_sinkTail_noLiveCut (by decide)).nonempty_oddStrategy)
  let sinkTree : OddStrategy twoVertexBasinGraph false twoVertexBasinSink :=
    OddStrategy.choose twoVertexBasinSink (by decide) .close
      twoVertexBasinSinkTail twoVertexBasin_step_sinkTail sinkTail
  let feederTail : OddStrategy twoVertexBasinGraph false
      twoVertexBasinFeederTail :=
    Classical.choice
      ((oddWins_of_noLiveCut false twoVertexBasinFeederTail
        twoVertexBasin_feederTail_noLiveCut (by decide)).nonempty_oddStrategy)
  let feederTree : OddStrategy twoVertexBasinGraph false
      twoVertexBasinFeeder :=
    OddStrategy.choose twoVertexBasinFeeder (by decide) (.open 2)
      twoVertexBasinFeederTail twoVertexBasin_step_feederTail feederTail
  let children : ∀ m t,
      step twoVertexBasinGraph twoVertexBasinParent m = some t →
        OddStrategy twoVertexBasinGraph false t := fun m t hstep ↦ by
    classical
    by_cases hmClose : m = .close
    · subst m
      have ht : t = twoVertexBasinSelected := by
        rw [twoVertexBasin_step_selected] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact selectedTree
    by_cases hmTwo : m = .open 2
    · subst m
      have ht : t = twoVertexBasinSink := by
        rw [twoVertexBasin_step_sink] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact sinkTree
    by_cases hmThree : m = .open 3
    · subst m
      have ht : t = twoVertexBasinFeeder := by
        rw [twoVertexBasin_step_feeder] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact feederTree
    exfalso
    cases m with
    | close => exact hmClose rfl
    | pass => simp [step, twoVertexBasinParent] at hstep
    | «open» v =>
        fin_cases v <;>
          simp [step, twoVertexBasinParent] at hstep hmTwo hmThree
  let hasMove : ∃ m t,
      step twoVertexBasinGraph twoVertexBasinParent m = some t :=
    ⟨.close, twoVertexBasinSelected, twoVertexBasin_step_selected⟩
  let parentTree : OddStrategy twoVertexBasinGraph false
      twoVertexBasinParent :=
    OddStrategy.answer twoVertexBasinParent rfl hasMove children
  have hselectedPrefix : StrategyPrefix twoVertexBasinGraph false
      parentTree selectedTree 0 := by
    have h := StrategyPrefix.answer (hstep := twoVertexBasin_step_selected)
      (StrategyPrefix.root : StrategyPrefix twoVertexBasinGraph false
        parentTree parentTree 0)
    simpa [parentTree, children, moveLiveStar] using h
  have hsinkPrefix : StrategyPrefix twoVertexBasinGraph false
      parentTree sinkTree
        (moveLiveStar twoVertexBasinParent (.open 2)) := by
    have h := StrategyPrefix.answer (hstep := twoVertexBasin_step_sink)
      (StrategyPrefix.root : StrategyPrefix twoVertexBasinGraph false
        parentTree parentTree 0)
    simpa [parentTree, children] using h
  have hfeederPrefix : StrategyPrefix twoVertexBasinGraph false
      parentTree feederTree
        (moveLiveStar twoVertexBasinParent (.open 3)) := by
    have h := StrategyPrefix.answer (hstep := twoVertexBasin_step_feeder)
      (StrategyPrefix.root : StrategyPrefix twoVertexBasinGraph false
        parentTree parentTree 0)
    simpa [parentTree, children] using h
  have hselectedConstant : ∀ z,
      AffineResponseMoment twoVertexBasinGraph false selectedTree z →
        realEdgeProjection 3 z = 0 := by
    intro z hz
    have h := hz.projection_eq_move_of_choose_silentCarrier
      twoVertexBasin_selectedTail_silent
    simpa [selectedTree, moveLiveStar] using h
  have hsinkConstant : ∀ z,
      AffineResponseMoment twoVertexBasinGraph false sinkTree z →
        realEdgeProjection 3 z = 0 := by
    intro z hz
    exact hz.projection_eq_zero_of_silentCarrier
      twoVertexBasin_sink_silent
  have hparentLive : liveSet twoVertexBasinParent = Finset.univ := by
    ext v
    fin_cases v <;> simp [twoVertexBasinParent, liveSet]
  have hfeederLive : liveSet twoVertexBasinFeeder = Finset.univ := by
    ext v
    fin_cases v <;> simp [twoVertexBasinFeeder, liveSet]
  have hfeederConstant : ∀ z,
      AffineResponseMoment twoVertexBasinGraph false feederTree z →
        realEdgeProjection 3 z =
          realEdgeProjection 3
            (moveLiveStar twoVertexBasinParent (.open 2)) := by
    intro z hz
    have h := hz.projection_eq_move_of_choose_silentCarrier
      twoVertexBasin_feederTail_silent
    simpa [feederTree, moveLiveStar, hparentLive, hfeederLive] using h
  refine ⟨parentTree, selectedTree, sinkTree, feederTree,
    hselectedPrefix, hsinkPrefix, hfeederPrefix, ?_, ?_, ?_,
    hselectedConstant, hsinkConstant, hfeederConstant⟩
  · rfl
  · rfl
  · rfl

omit [Fintype V] in
private theorem realEdgeQuotient_add_self (d : V)
    (x : RealEdgeQuotient V d) : x + x = 0 := by
  calc
    x + x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := by simp
    _ = ((1 : ZMod 2) + 1) • x := (add_smul 1 1 x).symm
    _ = 0 := by
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [h11, zero_smul]

omit [Fintype V] in
/-- Exact obstruction left by a two-vertex feeder basin after all three
continuation affine spaces are expanded.  The sink prefix and feeder
continuation contribute the same vector `e`, hence cancel.  Three copies of
the common ancestry prefix leave exactly one copy.  Since constant projected
affine spaces have only zero projected response directions, no choice of
continuation representatives or directions can repair a nonzero prefix. -/
theorem oddSpike_twoVertexBasin_commonPrefix_factor_impossible
    {G : SimpleGraph V} {d : V} {seat : Bool}
    {sS sC sF : State V}
    {selectedTree : OddStrategy G seat sS}
    {sinkTree : OddStrategy G seat sC}
    {feederTree : OddStrategy G seat sF}
    (p sinkPrefix feederPrefix e : EdgeVector V)
    (hpne : realEdgeProjection d p ≠ 0)
    (hsinkPrefix : realEdgeProjection d sinkPrefix =
      realEdgeProjection d e)
    (hfeederPrefix : realEdgeProjection d feederPrefix = 0)
    (hselected : ∀ a, AffineResponseMoment G seat selectedTree a →
      realEdgeProjection d a = 0)
    (hsink : ∀ a, AffineResponseMoment G seat sinkTree a →
      realEdgeProjection d a = 0)
    (hfeeder : ∀ a, AffineResponseMoment G seat feederTree a →
      realEdgeProjection d a = realEdgeProjection d e) :
    ∀ (aS aC aF dS dC dF : EdgeVector V),
      AffineResponseMoment G seat selectedTree aS →
      AffineResponseMoment G seat sinkTree aC →
      AffineResponseMoment G seat feederTree aF →
      ResponseDirection G seat selectedTree dS →
      ResponseDirection G seat sinkTree dC →
      ResponseDirection G seat feederTree dF →
      realEdgeProjection d
          ((p + aS) +
            (p + sinkPrefix + aC) +
            (p + feederPrefix + aF)) ≠
        realEdgeProjection d (dS + dC + dF) := by
  intro aS aC aF dS dC dF haS haC haF hdS hdC hdF heq
  have hdS0 : realEdgeProjection d dS = 0 := by
    apply hdS.projection_eq_zero_of_affine_constant (b := aS)
    intro z hz
    rw [hselected z hz, hselected aS haS]
  have hdC0 : realEdgeProjection d dC = 0 := by
    apply hdC.projection_eq_zero_of_affine_constant (b := aC)
    intro z hz
    rw [hsink z hz, hsink aC haC]
  have hdF0 : realEdgeProjection d dF = 0 := by
    apply hdF.projection_eq_zero_of_affine_constant (b := aF)
    intro z hz
    rw [hfeeder z hz, hfeeder aF haF]
  have hleft :
      realEdgeProjection d
          ((p + aS) +
            (p + sinkPrefix + aC) +
            (p + feederPrefix + aF)) =
        realEdgeProjection d p := by
    simp only [map_add]
    rw [hselected aS haS, hsinkPrefix, hsink aC haC,
      hfeederPrefix, hfeeder aF haF]
    let P := realEdgeProjection d p
    let E := realEdgeProjection d e
    change (P + 0) + (P + E + 0) + (P + 0 + E) = P
    have hPP : P + P = 0 := realEdgeQuotient_add_self d P
    have hEE : E + E = 0 := realEdgeQuotient_add_self d E
    calc
      (P + 0) + (P + E + 0) + (P + 0 + E) =
          (P + P + P) + (E + E) := by abel
      _ = P := by rw [hPP, zero_add, hEE, add_zero]
  have hright : realEdgeProjection d (dS + dC + dF) = 0 := by
    rw [map_add, map_add, hdS0, hdC0, hdF0, add_zero, add_zero]
  rw [hleft, hright] at heq
  exact hpne heq

/-- Any occurrence of the local score-one basin as a subtree of an exact
strategy rooted at the initial board has nonzero common ancestry prefix in
the real-edge quotient.  This is forced by the potential invariant, not by a
chosen continuation representative. -/
theorem twoVertexBasin_initialPrefix_projection_ne_zero
    {root : OddStrategy twoVertexBasinGraph false
      (initial (V := Fin 4))}
    {parentTree : OddStrategy twoVertexBasinGraph false
      twoVertexBasinParent}
    {p : EdgeVector (Fin 4)}
    (hp : StrategyPrefix twoVertexBasinGraph false root parentTree p) :
    realEdgeProjection 3 p ≠ 0 := by
  intro hzero
  have hevalZero : graphEvaluation twoVertexBasinGraph p = 0 :=
    graphEvaluation_eq_zero_of_realEdgeProjection_eq_zero
      twoVertexBasinGraph_dummy hzero
  have heval := hp.graphEvaluation_eq_potential_add wellFormed_initial
  have hpot :
      potential twoVertexBasinGraph (initial (V := Fin 4)) +
          potential twoVertexBasinGraph twoVertexBasinParent = 1 := by
    simp [potential, initial, queueCut, twoVertexBasinParent,
      twoVertexBasinGraph, SimpleGraph.fromRel_adj, flip]
    decide
  have hone : graphEvaluation twoVertexBasinGraph p = 1 := by
    exact heval.trans hpot
  rw [hone] at hevalZero
  exact one_ne_zero hevalZero

/-- A single theorem packaging the exact same-tree obstruction.  The local
strategy has the charged selected CLOSE, the real OPEN sink, and the dummy
OPEN feeder as immediate siblings.  After recursively expanding their
selected continuations, every attempted three-hole factor equation still
fails for every nonzero common ancestry prefix. -/
theorem exists_sameTree_twoVertexBasin_factor_obstruction :
    ∃ (parentTree : OddStrategy twoVertexBasinGraph false
          twoVertexBasinParent)
      (selectedTree : OddStrategy twoVertexBasinGraph false
          twoVertexBasinSelected)
      (sinkTree : OddStrategy twoVertexBasinGraph false
          twoVertexBasinSink)
      (feederTree : OddStrategy twoVertexBasinGraph false
          twoVertexBasinFeeder),
      StrategyPrefix twoVertexBasinGraph false parentTree selectedTree 0 ∧
      StrategyPrefix twoVertexBasinGraph false parentTree sinkTree
        (moveLiveStar twoVertexBasinParent (.open 2)) ∧
      StrategyPrefix twoVertexBasinGraph false parentTree feederTree
        (moveLiveStar twoVertexBasinParent (.open 3)) ∧
      selectedTree.selectedMove = some .close ∧
      sinkTree.selectedMove = some .close ∧
      feederTree.selectedMove = some (.open 2) ∧
      ∀ (p aS aC aF dS dC dF : EdgeVector (Fin 4)),
        realEdgeProjection 3 p ≠ 0 →
        AffineResponseMoment twoVertexBasinGraph false selectedTree aS →
        AffineResponseMoment twoVertexBasinGraph false sinkTree aC →
        AffineResponseMoment twoVertexBasinGraph false feederTree aF →
        ResponseDirection twoVertexBasinGraph false selectedTree dS →
        ResponseDirection twoVertexBasinGraph false sinkTree dC →
        ResponseDirection twoVertexBasinGraph false feederTree dF →
        realEdgeProjection 3
            ((p + aS) +
              (p + moveLiveStar twoVertexBasinParent (.open 2) + aC) +
              (p + moveLiveStar twoVertexBasinParent (.open 3) + aF)) ≠
          realEdgeProjection 3 (dS + dC + dF) := by
  obtain ⟨parentTree, selectedTree, sinkTree, feederTree,
      hselectedPrefix, hsinkPrefix, hfeederPrefix,
      hselectedMove, hsinkMove, hfeederMove,
      hselected, hsink, hfeeder⟩ :=
    exists_sameTree_twoVertexBasin_continuationConstants
  refine ⟨parentTree, selectedTree, sinkTree, feederTree,
    hselectedPrefix, hsinkPrefix, hfeederPrefix,
    hselectedMove, hsinkMove, hfeederMove, ?_⟩
  intro p aS aC aF dS dC dF hpne haS haC haF hdS hdC hdF
  have hfeederPrefixZero :
      realEdgeProjection 3
          (moveLiveStar twoVertexBasinParent (.open 3)) = 0 := by
    simpa [moveLiveStar] using
      (realEdgeProjection_liveStarVector_dummy 3
        (liveSet twoVertexBasinParent))
  exact oddSpike_twoVertexBasin_commonPrefix_factor_impossible
    p (moveLiveStar twoVertexBasinParent (.open 2))
      (moveLiveStar twoVertexBasinParent (.open 3))
      (moveLiveStar twoVertexBasinParent (.open 2))
      hpne rfl hfeederPrefixZero hselected hsink hfeeder
      aS aC aF dS dC dF haS haC haF hdS hdC hdF

/-! ## A reachable charged two-queue realization -/

/-- Adding one already-closed scoring vertex makes the score-one two-queue
charged spike genuinely reachable.  Edges are `0--3`, `1--3`, and `2--3`;
vertex `4` is isolated. -/
def reachableTwoVertexBasinGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun x y ↦
    (x = 0 ∧ y = 3) ∨ (x = 1 ∧ y = 3) ∨ (x = 2 ∧ y = 3)

theorem reachableTwoVertexBasinGraph_dummy :
    IsDummy reachableTwoVertexBasinGraph 4 := by
  intro v
  fin_cases v <;>
    simp [reachableTwoVertexBasinGraph, SimpleGraph.fromRel_adj]

private def reachableBasinAfterOpenZero : State (Fin 5) where
  untouched := {1, 2, 3, 4}
  queue := [0]
  ko := true
  toMove := true
  score := 0

private def reachableBasinAfterOpenOne : State (Fin 5) where
  untouched := {2, 3, 4}
  queue := [0, 1]
  ko := false
  toMove := false
  score := 0

private def reachableBasinAfterCloseZero : State (Fin 5) where
  untouched := {2, 3, 4}
  queue := [1]
  ko := false
  toMove := true
  score := 1

def reachableTwoVertexBasinParent : State (Fin 5) where
  untouched := {3, 4}
  queue := [1, 2]
  ko := false
  toMove := false
  score := 1

private theorem reachableBasin_step_openZero :
    step reachableTwoVertexBasinGraph (initial (V := Fin 5)) (.open 0) =
      some reachableBasinAfterOpenZero := by
  have hU : (Finset.univ.erase 0 : Finset (Fin 5)) = {1, 2, 3, 4} := by
    ext v
    fin_cases v <;> simp
  simp [step, initial, reachableBasinAfterOpenZero, hU]

private theorem reachableBasin_step_openOne :
    step reachableTwoVertexBasinGraph reachableBasinAfterOpenZero (.open 1) =
      some reachableBasinAfterOpenOne := by
  simp [step, reachableBasinAfterOpenZero, reachableBasinAfterOpenOne]

private theorem reachableBasin_step_closeZero :
    step reachableTwoVertexBasinGraph reachableBasinAfterOpenOne .close =
      some reachableBasinAfterCloseZero := by
  simp [step, reachableTwoVertexBasinGraph, SimpleGraph.fromRel_adj,
    reachableBasinAfterOpenOne, reachableBasinAfterCloseZero, flip]
  decide

private theorem reachableBasin_step_openTwo :
    step reachableTwoVertexBasinGraph reachableBasinAfterCloseZero (.open 2) =
      some reachableTwoVertexBasinParent := by
  simp [step, reachableBasinAfterCloseZero, reachableTwoVertexBasinParent]

/-- The exact universal live-star moment of the four-move history
`OPEN 0; OPEN 1; CLOSE; OPEN 2`. -/
def reachableTwoVertexBasinPrefix : EdgeVector (Fin 5) :=
  moveLiveStar (initial (V := Fin 5)) (.open 0) +
    (moveLiveStar reachableBasinAfterOpenZero (.open 1) +
      (moveLiveStar reachableBasinAfterOpenOne .close +
        (moveLiveStar reachableBasinAfterCloseZero (.open 2) + 0)))

/-- The smallest game-state-level realization of the two-queue odd--odd
spike is reachable from the actual initial board, and its trace prefix is a
genuine nonzero real-edge class.  This does not assert that the local odd
strategy extends upward to an initial odd counterstrategy. -/
theorem reachable_twoVertexBasin_trace_and_nonzero_prefix :
    LiveStarTrace reachableTwoVertexBasinGraph (initial (V := Fin 5))
        reachableTwoVertexBasinParent reachableTwoVertexBasinPrefix ∧
      flip reachableTwoVertexBasinGraph
          reachableTwoVertexBasinParent.untouched 1 = 1 ∧
      flip reachableTwoVertexBasinGraph
          reachableTwoVertexBasinParent.untouched 2 = 1 ∧
      realEdgeProjection 4 reachableTwoVertexBasinPrefix ≠ 0 := by
  have htrace : LiveStarTrace reachableTwoVertexBasinGraph
      (initial (V := Fin 5)) reachableTwoVertexBasinParent
      reachableTwoVertexBasinPrefix := by
    unfold reachableTwoVertexBasinPrefix
    exact LiveStarTrace.cons reachableBasin_step_openZero
      (LiveStarTrace.cons reachableBasin_step_openOne
        (LiveStarTrace.cons reachableBasin_step_closeZero
          (LiveStarTrace.cons reachableBasin_step_openTwo
            (LiveStarTrace.refl reachableTwoVertexBasinParent))))
  have hyCharge : flip reachableTwoVertexBasinGraph
      reachableTwoVertexBasinParent.untouched 1 = 1 := by
    simp [reachableTwoVertexBasinParent, flip,
      reachableTwoVertexBasinGraph, SimpleGraph.fromRel_adj]
    decide
  have hfCharge : flip reachableTwoVertexBasinGraph
      reachableTwoVertexBasinParent.untouched 2 = 1 := by
    simp [reachableTwoVertexBasinParent, flip,
      reachableTwoVertexBasinGraph, SimpleGraph.fromRel_adj]
    decide
  have hpne : realEdgeProjection 4 reachableTwoVertexBasinPrefix ≠ 0 := by
    intro hzero
    have hevalZero :
        graphEvaluation reachableTwoVertexBasinGraph
            reachableTwoVertexBasinPrefix = 0 :=
      graphEvaluation_eq_zero_of_realEdgeProjection_eq_zero
        reachableTwoVertexBasinGraph_dummy hzero
    have hpot := htrace.potential_eq_add_evaluation wellFormed_initial
    have hpotValue :
        potential reachableTwoVertexBasinGraph (initial (V := Fin 5)) +
            graphEvaluation reachableTwoVertexBasinGraph
              reachableTwoVertexBasinPrefix = 1 := by
      calc
        potential reachableTwoVertexBasinGraph (initial (V := Fin 5)) +
              graphEvaluation reachableTwoVertexBasinGraph
                reachableTwoVertexBasinPrefix =
            potential reachableTwoVertexBasinGraph
              reachableTwoVertexBasinParent := hpot.symm
        _ = 1 := by
          simp [potential, queueCut, reachableTwoVertexBasinParent,
            reachableTwoVertexBasinGraph, SimpleGraph.fromRel_adj, flip]
          decide
    have hevalOne :
        graphEvaluation reachableTwoVertexBasinGraph
            reachableTwoVertexBasinPrefix = 1 := by
      simpa [potential, initial, queueCut] using hpotValue
    rw [hevalOne] at hevalZero
    exact one_ne_zero hevalZero
  exact ⟨htrace, hyCharge, hfCharge, hpne⟩

private def reachableBasinSelected : State (Fin 5) where
  untouched := {3, 4}
  queue := [2]
  ko := false
  toMove := true
  score := 0

private def reachableBasinSelectedTail : State (Fin 5) where
  untouched := {3, 4}
  queue := []
  ko := false
  toMove := false
  score := 1

private def reachableBasinSink : State (Fin 5) where
  untouched := {4}
  queue := [1, 2, 3]
  ko := false
  toMove := true
  score := 1

private def reachableBasinSinkTail : State (Fin 5) where
  untouched := {4}
  queue := [2, 3]
  ko := false
  toMove := false
  score := 1

private def reachableBasinFeeder : State (Fin 5) where
  untouched := {3}
  queue := [1, 2, 4]
  ko := false
  toMove := true
  score := 1

private def reachableBasinFeederTail : State (Fin 5) where
  untouched := ∅
  queue := [1, 2, 4, 3]
  ko := false
  toMove := false
  score := 1

private theorem reachableBasin_step_selected :
    step reachableTwoVertexBasinGraph reachableTwoVertexBasinParent .close =
      some reachableBasinSelected := by
  simp [step, reachableTwoVertexBasinGraph, SimpleGraph.fromRel_adj,
    reachableTwoVertexBasinParent, reachableBasinSelected, flip]
  decide

private theorem reachableBasin_step_selectedTail :
    step reachableTwoVertexBasinGraph reachableBasinSelected .close =
      some reachableBasinSelectedTail := by
  simp [step, reachableTwoVertexBasinGraph, SimpleGraph.fromRel_adj,
    reachableBasinSelected, reachableBasinSelectedTail, flip]
  decide

private theorem reachableBasin_step_sink :
    step reachableTwoVertexBasinGraph reachableTwoVertexBasinParent (.open 3) =
      some reachableBasinSink := by
  simp [step, reachableTwoVertexBasinParent, reachableBasinSink]

private theorem reachableBasin_step_sinkTail :
    step reachableTwoVertexBasinGraph reachableBasinSink .close =
      some reachableBasinSinkTail := by
  simp [step, reachableTwoVertexBasinGraph, SimpleGraph.fromRel_adj,
    reachableBasinSink, reachableBasinSinkTail, flip]
  decide

private theorem reachableBasin_step_feeder :
    step reachableTwoVertexBasinGraph reachableTwoVertexBasinParent (.open 4) =
      some reachableBasinFeeder := by
  simp [step, reachableTwoVertexBasinParent, reachableBasinFeeder]
  decide

private theorem reachableBasin_step_feederTail :
    step reachableTwoVertexBasinGraph reachableBasinFeeder (.open 3) =
      some reachableBasinFeederTail := by
  simp [step, reachableBasinFeeder, reachableBasinFeederTail]

private theorem reachableBasin_selectedTail_noLiveCut :
    NoLiveCut reachableTwoVertexBasinGraph reachableBasinSelectedTail := by
  intro u hu v hv
  fin_cases u <;> fin_cases v <;>
    simp [reachableBasinSelectedTail, liveSet,
      reachableTwoVertexBasinGraph, SimpleGraph.fromRel_adj] at hu hv ⊢

private theorem reachableBasin_sinkTail_noLiveCut :
    NoLiveCut reachableTwoVertexBasinGraph reachableBasinSinkTail := by
  intro u hu v hv
  fin_cases u <;> fin_cases v <;>
    simp [reachableBasinSinkTail, liveSet,
      reachableTwoVertexBasinGraph, SimpleGraph.fromRel_adj] at hu hv ⊢

private theorem reachableBasin_feederTail_noLiveCut :
    NoLiveCut reachableTwoVertexBasinGraph reachableBasinFeederTail := by
  intro u hu
  fin_cases u <;> simp [reachableBasinFeederTail] at hu

private theorem reachableBasin_selectedTail_silent :
    ProjectionSilentCarrier 4 reachableBasinSelectedTail := by
  intro v hv
  fin_cases v <;> simp [reachableBasinSelectedTail, liveSet] at hv ⊢

private theorem reachableBasin_sink_silent :
    ProjectionSilentCarrier 4 reachableBasinSink := by
  intro v hv
  fin_cases v <;> simp [reachableBasinSink] at hv ⊢

private theorem reachableBasin_feederTail_silent :
    ProjectionSilentCarrier 4 reachableBasinFeederTail := by
  intro v hv
  fin_cases v <;> simp [reachableBasinFeederTail] at hv

/-- The reachable five-vertex history and the exact local strategy can be
joined at their common state.  The theorem makes the basin-expansion no-go
non-vacuous at game-state level: for every choice of three continuation
representatives and homogeneous corrections, the projected factor equation
fails.  It deliberately does not assert that this local odd strategy extends
backward to an odd strategy at the initial node. -/
theorem reachable_sameTree_twoVertexBasin_factor_obstruction :
    ∃ (parentTree : OddStrategy reachableTwoVertexBasinGraph false
          reachableTwoVertexBasinParent)
      (selectedTree : OddStrategy reachableTwoVertexBasinGraph false
          reachableBasinSelected)
      (sinkTree : OddStrategy reachableTwoVertexBasinGraph false
          reachableBasinSink)
      (feederTree : OddStrategy reachableTwoVertexBasinGraph false
          reachableBasinFeeder),
      LiveStarTrace reachableTwoVertexBasinGraph (initial (V := Fin 5))
        reachableTwoVertexBasinParent reachableTwoVertexBasinPrefix ∧
      StrategyPrefix reachableTwoVertexBasinGraph false parentTree
        selectedTree 0 ∧
      StrategyPrefix reachableTwoVertexBasinGraph false parentTree sinkTree
        (moveLiveStar reachableTwoVertexBasinParent (.open 3)) ∧
      StrategyPrefix reachableTwoVertexBasinGraph false parentTree feederTree
        (moveLiveStar reachableTwoVertexBasinParent (.open 4)) ∧
      selectedTree.selectedMove = some .close ∧
      sinkTree.selectedMove = some .close ∧
      feederTree.selectedMove = some (.open 3) ∧
      ∀ (aS aC aF dS dC dF : EdgeVector (Fin 5)),
        AffineResponseMoment reachableTwoVertexBasinGraph false
            selectedTree aS →
        AffineResponseMoment reachableTwoVertexBasinGraph false sinkTree aC →
        AffineResponseMoment reachableTwoVertexBasinGraph false feederTree aF →
        ResponseDirection reachableTwoVertexBasinGraph false selectedTree dS →
        ResponseDirection reachableTwoVertexBasinGraph false sinkTree dC →
        ResponseDirection reachableTwoVertexBasinGraph false feederTree dF →
        realEdgeProjection 4
            ((reachableTwoVertexBasinPrefix + aS) +
              (reachableTwoVertexBasinPrefix +
                moveLiveStar reachableTwoVertexBasinParent (.open 3) + aC) +
              (reachableTwoVertexBasinPrefix +
                moveLiveStar reachableTwoVertexBasinParent (.open 4) + aF)) ≠
          realEdgeProjection 4 (dS + dC + dF) := by
  let selectedTail : OddStrategy reachableTwoVertexBasinGraph false
      reachableBasinSelectedTail :=
    Classical.choice
      ((oddWins_of_noLiveCut false reachableBasinSelectedTail
        reachableBasin_selectedTail_noLiveCut (by decide)).nonempty_oddStrategy)
  let selectedTree : OddStrategy reachableTwoVertexBasinGraph false
      reachableBasinSelected :=
    OddStrategy.choose reachableBasinSelected (by decide) .close
      reachableBasinSelectedTail reachableBasin_step_selectedTail selectedTail
  let sinkTail : OddStrategy reachableTwoVertexBasinGraph false
      reachableBasinSinkTail :=
    Classical.choice
      ((oddWins_of_noLiveCut false reachableBasinSinkTail
        reachableBasin_sinkTail_noLiveCut (by decide)).nonempty_oddStrategy)
  let sinkTree : OddStrategy reachableTwoVertexBasinGraph false
      reachableBasinSink :=
    OddStrategy.choose reachableBasinSink (by decide) .close
      reachableBasinSinkTail reachableBasin_step_sinkTail sinkTail
  let feederTail : OddStrategy reachableTwoVertexBasinGraph false
      reachableBasinFeederTail :=
    Classical.choice
      ((oddWins_of_noLiveCut false reachableBasinFeederTail
        reachableBasin_feederTail_noLiveCut (by decide)).nonempty_oddStrategy)
  let feederTree : OddStrategy reachableTwoVertexBasinGraph false
      reachableBasinFeeder :=
    OddStrategy.choose reachableBasinFeeder (by decide) (.open 3)
      reachableBasinFeederTail reachableBasin_step_feederTail feederTail
  let children : ∀ m t,
      step reachableTwoVertexBasinGraph reachableTwoVertexBasinParent m =
          some t →
        OddStrategy reachableTwoVertexBasinGraph false t := fun m t hstep ↦ by
    classical
    by_cases hmClose : m = .close
    · subst m
      have ht : t = reachableBasinSelected := by
        rw [reachableBasin_step_selected] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact selectedTree
    by_cases hmThree : m = .open 3
    · subst m
      have ht : t = reachableBasinSink := by
        rw [reachableBasin_step_sink] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact sinkTree
    by_cases hmFour : m = .open 4
    · subst m
      have ht : t = reachableBasinFeeder := by
        rw [reachableBasin_step_feeder] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact feederTree
    exfalso
    cases m with
    | close => exact hmClose rfl
    | pass => simp [step, reachableTwoVertexBasinParent] at hstep
    | «open» v =>
        fin_cases v <;>
          simp [step, reachableTwoVertexBasinParent] at hstep hmThree hmFour
  let hasMove : ∃ m t,
      step reachableTwoVertexBasinGraph reachableTwoVertexBasinParent m =
        some t := ⟨.close, reachableBasinSelected, reachableBasin_step_selected⟩
  let parentTree : OddStrategy reachableTwoVertexBasinGraph false
      reachableTwoVertexBasinParent :=
    OddStrategy.answer reachableTwoVertexBasinParent rfl hasMove children
  have hselectedPrefix : StrategyPrefix reachableTwoVertexBasinGraph false
      parentTree selectedTree 0 := by
    have h := StrategyPrefix.answer (hstep := reachableBasin_step_selected)
      (StrategyPrefix.root : StrategyPrefix reachableTwoVertexBasinGraph false
        parentTree parentTree 0)
    simpa [parentTree, children, moveLiveStar] using h
  have hsinkPrefix : StrategyPrefix reachableTwoVertexBasinGraph false
      parentTree sinkTree
        (moveLiveStar reachableTwoVertexBasinParent (.open 3)) := by
    have h := StrategyPrefix.answer (hstep := reachableBasin_step_sink)
      (StrategyPrefix.root : StrategyPrefix reachableTwoVertexBasinGraph false
        parentTree parentTree 0)
    simpa [parentTree, children] using h
  have hfeederPrefix : StrategyPrefix reachableTwoVertexBasinGraph false
      parentTree feederTree
        (moveLiveStar reachableTwoVertexBasinParent (.open 4)) := by
    have h := StrategyPrefix.answer (hstep := reachableBasin_step_feeder)
      (StrategyPrefix.root : StrategyPrefix reachableTwoVertexBasinGraph false
        parentTree parentTree 0)
    simpa [parentTree, children] using h
  have hselected : ∀ z,
      AffineResponseMoment reachableTwoVertexBasinGraph false selectedTree z →
        realEdgeProjection 4 z = 0 := by
    intro z hz
    have h := hz.projection_eq_move_of_choose_silentCarrier
      reachableBasin_selectedTail_silent
    simpa [selectedTree, moveLiveStar] using h
  have hsink : ∀ z,
      AffineResponseMoment reachableTwoVertexBasinGraph false sinkTree z →
        realEdgeProjection 4 z = 0 := by
    intro z hz
    exact hz.projection_eq_zero_of_silentCarrier
      reachableBasin_sink_silent
  have hparentLive :
      liveSet reachableTwoVertexBasinParent = {1, 2, 3, 4} := by
    ext v
    fin_cases v <;> simp [reachableTwoVertexBasinParent, liveSet]
  have hfeederLive : liveSet reachableBasinFeeder = {1, 2, 3, 4} := by
    ext v
    fin_cases v <;> simp [reachableBasinFeeder, liveSet]
  have hfeeder : ∀ z,
      AffineResponseMoment reachableTwoVertexBasinGraph false feederTree z →
        realEdgeProjection 4 z =
          realEdgeProjection 4
            (moveLiveStar reachableTwoVertexBasinParent (.open 3)) := by
    intro z hz
    have h := hz.projection_eq_move_of_choose_silentCarrier
      reachableBasin_feederTail_silent
    simpa [feederTree, moveLiveStar, hparentLive, hfeederLive] using h
  have hfeederPrefixZero : realEdgeProjection 4
      (moveLiveStar reachableTwoVertexBasinParent (.open 4)) = 0 := by
    simpa [moveLiveStar] using
      (realEdgeProjection_liveStarVector_dummy 4
        (liveSet reachableTwoVertexBasinParent))
  have htrace := reachable_twoVertexBasin_trace_and_nonzero_prefix.1
  have hpne := reachable_twoVertexBasin_trace_and_nonzero_prefix.2.2.2
  refine ⟨parentTree, selectedTree, sinkTree, feederTree,
    htrace, hselectedPrefix, hsinkPrefix, hfeederPrefix, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · intro aS aC aF dS dC dF haS haC haF hdS hdC hdF
    exact oddSpike_twoVertexBasin_commonPrefix_factor_impossible
      reachableTwoVertexBasinPrefix
        (moveLiveStar reachableTwoVertexBasinParent (.open 3))
        (moveLiveStar reachableTwoVertexBasinParent (.open 4))
        (moveLiveStar reachableTwoVertexBasinParent (.open 3))
        hpne rfl hfeederPrefixZero hselected hsink hfeeder
        aS aC aF dS dC dF haS haC haF hdS hdC hdF

/-! ## Exact upward-extension failure -/

/-- The defender sibling which opens the real centre `3` before taking the
charged CLOSE.  Once `3` is open, the defender can always open the sole
remaining real neighbour `2` before `3` reaches the queue front. -/
private def reachableBasinDefusingSibling : State (Fin 5) where
  untouched := {2, 4}
  queue := [0, 1, 3]
  ko := false
  toMove := true
  score := 0

private def defusingAfterOpenTwo : State (Fin 5) where
  untouched := {4}
  queue := [0, 1, 3, 2]
  ko := false
  toMove := false
  score := 0

private def defusingAfterOpenTwoDummy : State (Fin 5) where
  untouched := ∅
  queue := [0, 1, 3, 2, 4]
  ko := false
  toMove := true
  score := 0

private def defusingAfterOpenDummy : State (Fin 5) where
  untouched := {2}
  queue := [0, 1, 3, 4]
  ko := false
  toMove := false
  score := 0

private def defusingAfterOpenDummyTwo : State (Fin 5) where
  untouched := ∅
  queue := [0, 1, 3, 4, 2]
  ko := false
  toMove := true
  score := 0

private def defusingAfterCloseZero : State (Fin 5) where
  untouched := {2, 4}
  queue := [1, 3]
  ko := false
  toMove := false
  score := 0

private def defusingAfterCloseZeroOpenTwo : State (Fin 5) where
  untouched := {4}
  queue := [1, 3, 2]
  ko := false
  toMove := true
  score := 0

private def defusingAfterCloseZeroOpenTwoDummy : State (Fin 5) where
  untouched := ∅
  queue := [1, 3, 2, 4]
  ko := false
  toMove := false
  score := 0

private def defusingAfterCloseOne : State (Fin 5) where
  untouched := {4}
  queue := [3, 2]
  ko := false
  toMove := false
  score := 0

private def defusingAfterCloseOneDummy : State (Fin 5) where
  untouched := ∅
  queue := [3, 2, 4]
  ko := false
  toMove := true
  score := 0

private theorem reachableBasin_step_defusingSibling :
    step reachableTwoVertexBasinGraph reachableBasinAfterOpenOne (.open 3) =
      some reachableBasinDefusingSibling := by
  simp [step, reachableBasinAfterOpenOne, reachableBasinDefusingSibling]
  decide

private theorem defusing_step_openTwo :
    step reachableTwoVertexBasinGraph reachableBasinDefusingSibling (.open 2) =
      some defusingAfterOpenTwo := by
  simp [step, reachableBasinDefusingSibling, defusingAfterOpenTwo]

private theorem defusing_step_openTwoDummy :
    step reachableTwoVertexBasinGraph defusingAfterOpenTwo (.open 4) =
      some defusingAfterOpenTwoDummy := by
  simp [step, defusingAfterOpenTwo, defusingAfterOpenTwoDummy]

private theorem defusing_step_openDummy :
    step reachableTwoVertexBasinGraph reachableBasinDefusingSibling (.open 4) =
      some defusingAfterOpenDummy := by
  simp [step, reachableBasinDefusingSibling, defusingAfterOpenDummy]
  decide

private theorem defusing_step_openDummyTwo :
    step reachableTwoVertexBasinGraph defusingAfterOpenDummy (.open 2) =
      some defusingAfterOpenDummyTwo := by
  simp [step, defusingAfterOpenDummy, defusingAfterOpenDummyTwo]

private theorem defusing_step_closeZero :
    step reachableTwoVertexBasinGraph reachableBasinDefusingSibling .close =
      some defusingAfterCloseZero := by
  simp [step, reachableTwoVertexBasinGraph, SimpleGraph.fromRel_adj,
    reachableBasinDefusingSibling, defusingAfterCloseZero, flip]
  decide

private theorem defusing_step_closeZeroOpenTwo :
    step reachableTwoVertexBasinGraph defusingAfterCloseZero (.open 2) =
      some defusingAfterCloseZeroOpenTwo := by
  simp [step, defusingAfterCloseZero, defusingAfterCloseZeroOpenTwo]

private theorem defusing_step_closeZeroOpenTwoDummy :
    step reachableTwoVertexBasinGraph defusingAfterCloseZeroOpenTwo (.open 4) =
      some defusingAfterCloseZeroOpenTwoDummy := by
  simp [step, defusingAfterCloseZeroOpenTwo,
    defusingAfterCloseZeroOpenTwoDummy]

private theorem defusing_step_closeOne :
    step reachableTwoVertexBasinGraph defusingAfterCloseZeroOpenTwo .close =
      some defusingAfterCloseOne := by
  simp [step, reachableTwoVertexBasinGraph, SimpleGraph.fromRel_adj,
    defusingAfterCloseZeroOpenTwo, defusingAfterCloseOne, flip]
  decide

private theorem defusing_step_closeOneDummy :
    step reachableTwoVertexBasinGraph defusingAfterCloseOne (.open 4) =
      some defusingAfterCloseOneDummy := by
  simp [step, defusingAfterCloseOne, defusingAfterCloseOneDummy]

/-- Opening the real centre at the earlier defender node is an exact
even-winning defusing response.  The proof is a small symbolic minimax tree:
whenever the opponent opens one remaining vertex, open the other; after
`CLOSE 0`, first open real neighbour `2`, then open dummy `4` before centre
`3` can be closed with odd charge. -/
theorem evenWins_reachableBasinDefusingSibling :
    EvenWins reachableTwoVertexBasinGraph false
      reachableBasinDefusingSibling := by
  have hevenOpenTwoDummy :
      EvenWins reachableTwoVertexBasinGraph false
        defusingAfterOpenTwoDummy :=
    evenWins_of_untouched_empty false defusingAfterOpenTwoDummy rfl rfl
  have hevenOpenTwo :
      EvenWins reachableTwoVertexBasinGraph false defusingAfterOpenTwo :=
    EvenWins.choose defusingAfterOpenTwo rfl (.open 4)
      defusingAfterOpenTwoDummy defusing_step_openTwoDummy
      hevenOpenTwoDummy
  have hevenOpenDummyTwo :
      EvenWins reachableTwoVertexBasinGraph false
        defusingAfterOpenDummyTwo :=
    evenWins_of_untouched_empty false defusingAfterOpenDummyTwo rfl rfl
  have hevenOpenDummy :
      EvenWins reachableTwoVertexBasinGraph false defusingAfterOpenDummy :=
    EvenWins.choose defusingAfterOpenDummy rfl (.open 2)
      defusingAfterOpenDummyTwo defusing_step_openDummyTwo
      hevenOpenDummyTwo
  have hevenCloseOneDummy :
      EvenWins reachableTwoVertexBasinGraph false
        defusingAfterCloseOneDummy :=
    evenWins_of_untouched_empty false defusingAfterCloseOneDummy rfl rfl
  have hevenCloseOne :
      EvenWins reachableTwoVertexBasinGraph false defusingAfterCloseOne :=
    EvenWins.choose defusingAfterCloseOne rfl (.open 4)
      defusingAfterCloseOneDummy defusing_step_closeOneDummy
      hevenCloseOneDummy
  let closeZeroOpenTwoChildren : ∀ m t,
      step reachableTwoVertexBasinGraph defusingAfterCloseZeroOpenTwo m =
          some t →
        EvenWins reachableTwoVertexBasinGraph false t := fun m t hstep ↦ by
    classical
    by_cases hmDummy : m = .open 4
    · subst m
      have ht : t = defusingAfterCloseZeroOpenTwoDummy := by
        rw [defusing_step_closeZeroOpenTwoDummy] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact evenWins_of_untouched_empty false
        defusingAfterCloseZeroOpenTwoDummy rfl rfl
    by_cases hmClose : m = .close
    · subst m
      have ht : t = defusingAfterCloseOne := by
        rw [defusing_step_closeOne] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact hevenCloseOne
    exfalso
    cases m with
    | close => exact hmClose rfl
    | pass => simp [step, defusingAfterCloseZeroOpenTwo] at hstep
    | «open» v =>
        fin_cases v <;>
          simp [step, defusingAfterCloseZeroOpenTwo] at hstep hmDummy
  let closeZeroOpenTwoHasMove : ∃ m t,
      step reachableTwoVertexBasinGraph defusingAfterCloseZeroOpenTwo m =
        some t :=
    ⟨.open 4, defusingAfterCloseZeroOpenTwoDummy,
      defusing_step_closeZeroOpenTwoDummy⟩
  have hevenCloseZeroOpenTwo :
      EvenWins reachableTwoVertexBasinGraph false
        defusingAfterCloseZeroOpenTwo :=
    EvenWins.answer defusingAfterCloseZeroOpenTwo (by decide)
      closeZeroOpenTwoHasMove closeZeroOpenTwoChildren
  have hevenCloseZero :
      EvenWins reachableTwoVertexBasinGraph false defusingAfterCloseZero :=
    EvenWins.choose defusingAfterCloseZero rfl (.open 2)
      defusingAfterCloseZeroOpenTwo defusing_step_closeZeroOpenTwo
      hevenCloseZeroOpenTwo
  let children : ∀ m t,
      step reachableTwoVertexBasinGraph reachableBasinDefusingSibling m =
          some t →
        EvenWins reachableTwoVertexBasinGraph false t := fun m t hstep ↦ by
    classical
    by_cases hmTwo : m = .open 2
    · subst m
      have ht : t = defusingAfterOpenTwo := by
        rw [defusing_step_openTwo] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact hevenOpenTwo
    by_cases hmDummy : m = .open 4
    · subst m
      have ht : t = defusingAfterOpenDummy := by
        rw [defusing_step_openDummy] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact hevenOpenDummy
    by_cases hmClose : m = .close
    · subst m
      have ht : t = defusingAfterCloseZero := by
        rw [defusing_step_closeZero] at hstep
        exact Option.some.inj hstep.symm
      subst t
      exact hevenCloseZero
    exfalso
    cases m with
    | close => exact hmClose rfl
    | pass => simp [step, reachableBasinDefusingSibling] at hstep
    | «open» v =>
        fin_cases v <;>
          simp [step, reachableBasinDefusingSibling] at hstep hmTwo hmDummy
  let hasMove : ∃ m t,
      step reachableTwoVertexBasinGraph reachableBasinDefusingSibling m =
        some t :=
    ⟨.open 2, defusingAfterOpenTwo, defusing_step_openTwo⟩
  exact EvenWins.answer reachableBasinDefusingSibling (by decide)
    hasMove children

/-- The first upward extension already fails at the defender node after
`OPEN 0; OPEN 1`: defender `OPEN 3` enters the exact even-winning sibling
above.  Consequently no odd strategy exists at this ancestor, so the
reachable local odd basin strategy cannot be a subtree of any initial odd
strategy along the displayed trace. -/
theorem no_oddStrategy_reachableBasinAfterOpenOne :
    IsEmpty (OddStrategy reachableTwoVertexBasinGraph false
      reachableBasinAfterOpenOne) := by
  refine ⟨fun oddTree ↦ ?_⟩
  have heven : EvenWins reachableTwoVertexBasinGraph false
      reachableBasinAfterOpenOne :=
    EvenWins.choose reachableBasinAfterOpenOne rfl (.open 3)
      reachableBasinDefusingSibling reachableBasin_step_defusingSibling
      evenWins_reachableBasinDefusingSibling
  exact heven.not_oddWins oddTree.toOddWins

omit [Fintype V] in
private theorem adjacencyBit_eq_one_of_flip_erase_zero
    {G : SimpleGraph V} {U : Finset V} {a z : V}
    (hz : z ∈ U) (hfull : flip G U a = 1)
    (herase : flip G (U.erase z) a = 0) :
    adjacencyBit G a z = 1 := by
  have hsplit := flip_eq_flip_erase_add (G := G) (f := a) hz
  rw [hfull, herase, zero_add] at hsplit
  exact hsplit.symm

private theorem zmod2_eq_zero_of_one_add_eq_one (x : ZMod 2)
    (h : 1 + x = 1) : x = 0 := by
  apply add_left_cancel (a := (1 : ZMod 2))
  simpa using h

/-- Exact first-response classification in every same-root punctured sibling
of a charged-CLOSE spike.  The theorem packages the neutral punctured-tree
argument without replacing continuation representatives by scalar bits. -/
theorem MinimalBadPredecessorCase.chargedClose_openSibling_replyCase
    {G : SimpleGraph V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    {s parent : State V} {pp : EdgeVector V} {f : V} {q : List V}
    (hparentTurn : parent.toMove = seat)
    (hfan : ∀ m t, step G parent m = some t →
      ∃ childTree : OddStrategy G seat t,
        StrategyPrefix G seat root childTree
          (pp + moveLiveStar parent m))
    (hincoming : step G parent .close = some s)
    (hminimal : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat root desc →
      rank t < rank s → t.score ≠ 0)
    (hcase : MinimalBadPredecessorCase G parent s f q .close)
    (hfcharge : flip G s.untouched f = 1)
    {z : V} (hz : z ∈ parent.untouched) :
    ∃ (y : V) (sz : State V) (szTree : OddStrategy G seat sz),
      parent.queue = y :: f :: q ∧
      step G parent (.open z) = some sz ∧
      StrategyPrefix G seat root szTree
        (pp + moveLiveStar parent (.open z)) ∧
      (∀ {t : State V} {desc : OddStrategy G seat t},
        StrategyNode G seat szTree desc → t.score = 1) ∧
      ∃ m, szTree.selectedMove = some m ∧
        OddSpikeOpenReplyCase G parent.untouched
          y f z m := by
  classical
  cases hcase with
  | chargedClose y hqueue hko hU hscore hyCharge =>
      obtain ⟨sz, szTree, hopen, hprefix, hszU, hszQueue, hszKo,
          hszTurn, hszScore, hszRank, hone, hneutral⟩ :=
        (MinimalBadPredecessorCase.chargedClose y hqueue hko hU hscore
          hyCharge).chargedClose_openSibling_neutral
            hfan hincoming hminimal hz
      cases szTree with
      | terminal _ hterminal hodd =>
          let c : State V := {
            untouched := sz.untouched
            queue := f :: (q ++ [z])
            ko := false
            toMove := !sz.toMove
            score := sz.score + flip G sz.untouched y }
          have hclose : step G sz .close = some c := by
            simp [step, c, hszQueue, hqueue, hszKo]
          exact False.elim
            (terminal_no_step hterminal ⟨.close, c, hclose⟩)
      | answer _ hseat hasMove children =>
          have hnot : sz.toMove ≠ seat := by
            rw [hszTurn, hparentTurn]
            simp
          exact False.elim (hnot hseat)
      | choose _ hseat m t hstep tail =>
          cases m with
          | pass =>
              simp [step, hszQueue, hqueue, hszKo] at hstep
          | close =>
              let c : State V := {
                untouched := sz.untouched
                queue := f :: (q ++ [z])
                ko := false
                toMove := !sz.toMove
                score := sz.score + flip G sz.untouched y }
              have hclose : step G sz .close = some c := by
                simp [step, c, hszQueue, hqueue, hszKo]
              have htEq : t = c := by
                rw [hclose] at hstep
                exact Option.some.inj hstep.symm
              subst t
              have hcNode : StrategyNode G seat
                  (OddStrategy.choose sz hseat .close c hclose tail) tail :=
                StrategyNode.choose (StrategyNode.root tail)
              have hcOne : c.score = 1 := hone hcNode
              have hyErase : flip G (parent.untouched.erase z) y = 0 := by
                have hcOne' := hcOne
                simp only [c, hszScore] at hcOne'
                have hzero : flip G sz.untouched y = 0 := by
                  exact zmod2_eq_zero_of_one_add_eq_one _ hcOne'
                simpa [hszU] using hzero
              have hyz : adjacencyBit G y z = 1 :=
                adjacencyBit_eq_one_of_flip_erase_zero hz hyCharge hyErase
              let cf : State V := {
                untouched := c.untouched
                queue := q ++ [z]
                ko := false
                toMove := !c.toMove
                score := c.score + flip G c.untouched f }
              have hcloseF : step G c .close = some cf := by
                simp [step, cf, c]
              have hcTurn : c.toMove = seat := by
                rw [show c.toMove = !sz.toMove by rfl, hszTurn,
                  hparentTurn]
                simp
              have hfErase : flip G (parent.untouched.erase z) f = 0 := by
                cases tail with
                | terminal _ hterminal _ =>
                    exact False.elim
                      (terminal_no_step hterminal ⟨.close, cf, hcloseF⟩)
                | choose _ htailSeat _ _ _ _ =>
                    exact False.elim (htailSeat hcTurn)
                | answer _ htailSeat hasMove children =>
                    let cfTree := children .close cf hcloseF
                    have hcfNode : StrategyNode G seat
                        (OddStrategy.choose sz hseat .close c hclose
                          (OddStrategy.answer c htailSeat hasMove children))
                        cfTree :=
                      StrategyNode.choose
                        (StrategyNode.answer (StrategyNode.root cfTree))
                    have hcfOne : cf.score = 1 := hone hcfNode
                    have hcfOne' := hcfOne
                    simp only [cf, hcOne] at hcfOne'
                    have hzero : flip G c.untouched f = 0 := by
                      exact zmod2_eq_zero_of_one_add_eq_one _ hcfOne'
                    simpa [c, hszU] using hzero
              have hfFull : flip G parent.untouched f = 1 := by
                simpa [hU] using hfcharge
              have hfz : adjacencyBit G f z = 1 :=
                adjacencyBit_eq_one_of_flip_erase_zero hz hfFull hfErase
              exact ⟨y, sz,
                OddStrategy.choose sz hseat .close c hclose tail,
                hqueue, hopen, hprefix, hone, .close, rfl,
                OddSpikeOpenReplyCase.close hyz hfz⟩
          | «open» w =>
              simp only [step] at hstep
              split at hstep
              · rename_i hw
                let so : State V := {
                  untouched := sz.untouched.erase w
                  queue := sz.queue ++ [w]
                  ko := sz.queue.isEmpty
                  toMove := !sz.toMove
                  score := sz.score }
                have htEq : t = so := by
                  cases hstep
                  rfl
                subst t
                have hw' : w ∈ parent.untouched.erase z := by
                  simpa [hszU] using hw
                let cy : State V := {
                  untouched := so.untouched
                  queue := f :: (q ++ [z, w])
                  ko := false
                  toMove := !so.toMove
                  score := so.score + flip G so.untouched y }
                have hcloseY : step G so .close = some cy := by
                  simp [step, cy, so, hszQueue, hqueue]
                have hsoTurn : so.toMove = seat := by
                  simp [so, hszTurn, hparentTurn]
                have hyDoubleErase :
                    flip G ((parent.untouched.erase z).erase w) y = 0 := by
                  cases tail with
                  | terminal _ hterminal _ =>
                      exact False.elim
                        (terminal_no_step hterminal ⟨.close, cy, hcloseY⟩)
                  | choose _ htailSeat _ _ _ _ =>
                      exact False.elim (htailSeat hsoTurn)
                  | answer _ htailSeat hasMove children =>
                      let cyTree := children .close cy hcloseY
                      have hcyNode : StrategyNode G seat
                          (OddStrategy.choose sz hseat (.open w) so
                            (by simp [step, so, hw])
                            (OddStrategy.answer so htailSeat hasMove children))
                          cyTree :=
                        StrategyNode.choose
                          (StrategyNode.answer (StrategyNode.root cyTree))
                      have hcyOne : cy.score = 1 := hone hcyNode
                      have hsoOne : so.score = 1 := by simp [so, hszScore]
                      have hcyOne' := hcyOne
                      simp only [cy, hsoOne] at hcyOne'
                      have hzero : flip G so.untouched y = 0 := by
                        exact zmod2_eq_zero_of_one_add_eq_one _ hcyOne'
                      simpa [so, hszU] using hzero
                have hsplitZ :=
                  flip_eq_flip_erase_add (G := G) (f := y) hz
                have hsplitW := flip_eq_flip_erase_add (G := G)
                  (f := y) hw'
                have hrow :
                    adjacencyBit G y z + adjacencyBit G y w = 1 := by
                  rw [hyCharge] at hsplitZ
                  rw [hsplitW, hyDoubleErase, zero_add] at hsplitZ
                  simpa [add_comm] using hsplitZ.symm
                exact ⟨y, sz,
                  OddStrategy.choose sz hseat (.open w) so
                    (by simp [step, so, hw]) tail,
                  hqueue, hopen, hprefix, hone, .open w, rfl,
                  OddSpikeOpenReplyCase.open w hw' hrow⟩
              · contradiction

end

end Ogdoad.Fifo
