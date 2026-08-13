import Ogdoad.FifoProtectedBlockBoundary
import Ogdoad.FifoOddSpikeFactor

/-!
# The protected / charged-spike splice boundary

The protected empty-block rule terminates by odd lexicographic replacement,
but its immediate leaves are attacker-controlled two-queue states with even
untouched carrier.  Such a leaf can genuinely be a charged-CLOSE spike.

This module packages the smallest reachable same-tree charged basin as an
exact obstruction to completing the splice using only its three local
siblings.  The history prefix is a nonzero real-edge class.  For every choice
of continuation representatives and homogeneous corrections in the three
actual sibling subtrees, the projected factor equation fails.  Thus a proof
must import a further cross-coset incidence from outside this local basin.

The construction is deliberately state-reachable rather than an odd strategy
at the initial root.  In fact its first upward extension has an explicit
even-winning defender sibling, so this particular local basin cannot occur
inside an initial odd counterstrategy.  It proves incompleteness of the
current local rewrite rule, not a counterexample to FIFO or to the global
factor interface.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A reachable local odd strategy with three same-tree ancestry holes whose
globally trace-decorated projected factor equation fails for every possible
choice of affine bases and homogeneous continuation corrections. -/
structure ReachableSameRootThreeHoleObstruction
    (G : SimpleGraph V) (d : V) (seat : Bool)
    (parent : State V) (tracePrefix : EdgeVector V) where
  parentTree : OddStrategy G seat parent
  selectedState : State V
  sideState₁ : State V
  sideState₂ : State V
  selectedTree : OddStrategy G seat selectedState
  sideTree₁ : OddStrategy G seat sideState₁
  sideTree₂ : OddStrategy G seat sideState₂
  sidePrefix₁ : EdgeVector V
  sidePrefix₂ : EdgeVector V
  trace : LiveStarTrace G (initial (V := V)) parent tracePrefix
  traceProjection_ne_zero : realEdgeProjection d tracePrefix ≠ 0
  selectedPrefix : StrategyPrefix G seat parentTree selectedTree 0
  sideAncestry₁ : StrategyPrefix G seat parentTree sideTree₁ sidePrefix₁
  sideAncestry₂ : StrategyPrefix G seat parentTree sideTree₂ sidePrefix₂
  noThreeHoleFactor :
    ∀ (a₀ a₁ a₂ c₀ c₁ c₂ : EdgeVector V),
      AffineResponseMoment G seat selectedTree a₀ →
      AffineResponseMoment G seat sideTree₁ a₁ →
      AffineResponseMoment G seat sideTree₂ a₂ →
      ResponseDirection G seat selectedTree c₀ →
      ResponseDirection G seat sideTree₁ c₁ →
      ResponseDirection G seat sideTree₂ c₂ →
      realEdgeProjection d
          ((tracePrefix + a₀) +
            (tracePrefix + sidePrefix₁ + a₁) +
            (tracePrefix + sidePrefix₂ + a₂)) ≠
        realEdgeProjection d (c₀ + c₁ + c₂)

/-- The obstruction is a genuine odd three-hole family, yet no assignments
of its continuation bases and corrections form the projected balance needed
by factor extension. -/
theorem ReachableSameRootThreeHoleObstruction.no_projected_threeHole_balance
    {G : SimpleGraph V} {d : V} {seat : Bool}
    {parent : State V} {tracePrefix : EdgeVector V}
    (h : ReachableSameRootThreeHoleObstruction
      G d seat parent tracePrefix) :
    ∀ (a₀ a₁ a₂ c₀ c₁ c₂ : EdgeVector V),
      AffineResponseMoment G seat h.selectedTree a₀ →
      AffineResponseMoment G seat h.sideTree₁ a₁ →
      AffineResponseMoment G seat h.sideTree₂ a₂ →
      ResponseDirection G seat h.selectedTree c₀ →
      ResponseDirection G seat h.sideTree₁ c₁ →
      ResponseDirection G seat h.sideTree₂ c₂ →
      ¬ realEdgeProjection d
          ((tracePrefix + a₀) +
            (tracePrefix + h.sidePrefix₁ + a₁) +
            (tracePrefix + h.sidePrefix₂ + a₂)) =
        realEdgeProjection d (c₀ + c₁ + c₂) := by
  exact h.noThreeHoleFactor

/-- Exact splice obstruction on the reachable five-vertex charged basin.

The parent is attacker-controlled, has queue length two, score one, even
carrier, and both displayed fronts charged.  It is reached by the real history
`OPEN 0; OPEN 1; CLOSE; OPEN 2`.  At that same state one exact local odd
strategy supplies the selected CLOSE and the two universal OPEN siblings,
but every three-hole projected factor equation fails. -/
theorem reachable_chargedTwoQueue_sameRoot_splice_obstruction :
    reachableTwoVertexBasinParent.toMove = false ∧
    reachableTwoVertexBasinParent.queue = [1, 2] ∧
    reachableTwoVertexBasinParent.score = 1 ∧
    reachableTwoVertexBasinParent.untouched.card % 2 = 0 ∧
    flip reachableTwoVertexBasinGraph
        reachableTwoVertexBasinParent.untouched 1 = 1 ∧
    flip reachableTwoVertexBasinGraph
        reachableTwoVertexBasinParent.untouched 2 = 1 ∧
    Nonempty (ReachableSameRootThreeHoleObstruction
      reachableTwoVertexBasinGraph 4 false
      reachableTwoVertexBasinParent reachableTwoVertexBasinPrefix) := by
  obtain ⟨parentTree, selectedTree, sideTree₁, sideTree₂,
      htrace, hselectedPrefix, hsidePrefix₁, hsidePrefix₂,
      hselectedMove, hsideMove₁, hsideMove₂, hobstruction⟩ :=
    reachable_sameTree_twoVertexBasin_factor_obstruction
  have htraceData := reachable_twoVertexBasin_trace_and_nonzero_prefix
  refine ⟨by rfl, by rfl, by rfl, by decide,
    htraceData.2.1, htraceData.2.2.1, ?_⟩
  exact ⟨{
    parentTree := parentTree
    selectedState := _
    sideState₁ := _
    sideState₂ := _
    selectedTree := selectedTree
    sideTree₁ := sideTree₁
    sideTree₂ := sideTree₂
    sidePrefix₁ := moveLiveStar reachableTwoVertexBasinParent (.open 3)
    sidePrefix₂ := moveLiveStar reachableTwoVertexBasinParent (.open 4)
    trace := htrace
    traceProjection_ne_zero := htraceData.2.2.2
    selectedPrefix := hselectedPrefix
    sideAncestry₁ := hsidePrefix₁
    sideAncestry₂ := hsidePrefix₂
    noThreeHoleFactor := hobstruction }⟩

/-- The local basin cannot be installed as a terminal contraction rule in the
protected odd expansion calculus: its universally quantified no-factor
statement supplies an explicit failed assignment for any proposed bases and
corrections.  Therefore the only possible repair is a new point or incidence
from outside the three-hole basin. -/
theorem reachable_chargedTwoQueue_requires_external_incidence :
    ∃ h : ReachableSameRootThreeHoleObstruction
        reachableTwoVertexBasinGraph 4 false
        reachableTwoVertexBasinParent reachableTwoVertexBasinPrefix,
      realEdgeProjection 4 reachableTwoVertexBasinPrefix ≠ 0 ∧
      ∀ (a₀ a₁ a₂ c₀ c₁ c₂ : EdgeVector (Fin 5)),
        AffineResponseMoment reachableTwoVertexBasinGraph false
            h.selectedTree a₀ →
        AffineResponseMoment reachableTwoVertexBasinGraph false
            h.sideTree₁ a₁ →
        AffineResponseMoment reachableTwoVertexBasinGraph false
            h.sideTree₂ a₂ →
        ResponseDirection reachableTwoVertexBasinGraph false
            h.selectedTree c₀ →
        ResponseDirection reachableTwoVertexBasinGraph false
            h.sideTree₁ c₁ →
        ResponseDirection reachableTwoVertexBasinGraph false
            h.sideTree₂ c₂ →
        ¬ realEdgeProjection 4
            ((reachableTwoVertexBasinPrefix + a₀) +
              (reachableTwoVertexBasinPrefix + h.sidePrefix₁ + a₁) +
              (reachableTwoVertexBasinPrefix + h.sidePrefix₂ + a₂)) =
          realEdgeProjection 4 (c₀ + c₁ + c₂) := by
  obtain ⟨h⟩ := reachable_chargedTwoQueue_sameRoot_splice_obstruction.2.2.2.2.2.2
  exact ⟨h, h.traceProjection_ne_zero,
    h.no_projected_threeHole_balance⟩

/-- The precise proposed terminal splice using only the three local basin
holes.  It asks for affine bases and homogeneous corrections whose globally
trace-decorated points satisfy the projected factor equation. -/
def ReachableChargedBasinLocalFactorSplice : Prop :=
  ∃ h : ReachableSameRootThreeHoleObstruction
      reachableTwoVertexBasinGraph 4 false
      reachableTwoVertexBasinParent reachableTwoVertexBasinPrefix,
    ∃ (a₀ a₁ a₂ c₀ c₁ c₂ : EdgeVector (Fin 5)),
      AffineResponseMoment reachableTwoVertexBasinGraph false
          h.selectedTree a₀ ∧
      AffineResponseMoment reachableTwoVertexBasinGraph false
          h.sideTree₁ a₁ ∧
      AffineResponseMoment reachableTwoVertexBasinGraph false
          h.sideTree₂ a₂ ∧
      ResponseDirection reachableTwoVertexBasinGraph false
          h.selectedTree c₀ ∧
      ResponseDirection reachableTwoVertexBasinGraph false
          h.sideTree₁ c₁ ∧
      ResponseDirection reachableTwoVertexBasinGraph false
          h.sideTree₂ c₂ ∧
      realEdgeProjection 4
          ((reachableTwoVertexBasinPrefix + a₀) +
            (reachableTwoVertexBasinPrefix + h.sidePrefix₁ + a₁) +
            (reachableTwoVertexBasinPrefix + h.sidePrefix₂ + a₂)) =
        realEdgeProjection 4 (c₀ + c₁ + c₂)

/-- The current local three-hole splice is false in a reachable same-tree
charged basin.  This is the exact theorem that prevents appending the basin as
a terminal rule to the otherwise terminating protected odd rewrite system. -/
theorem not_reachableChargedBasinLocalFactorSplice :
    ¬ ReachableChargedBasinLocalFactorSplice := by
  rintro ⟨h, a₀, a₁, a₂, c₀, c₁, c₂,
    ha₀, ha₁, ha₂, hc₀, hc₁, hc₂, hbalance⟩
  exact h.noThreeHoleFactor a₀ a₁ a₂ c₀ c₁ c₂
    ha₀ ha₁ ha₂ hc₀ hc₁ hc₂ hbalance

/-- Public spelling of the ancestor after the first two moves of the basin
history. -/
def reachableChargedBasinAfterTwoOpens : State (Fin 5) where
  untouched := {2, 3, 4}
  queue := [0, 1]
  ko := false
  toMove := false
  score := 0

/-- Sharp global qualification of the reachable local obstruction.  The
ancestor after `OPEN 0; OPEN 1` admits no odd strategy: its defender can open
the basin centre and enter an explicit even-winning defusing sibling.  Hence
the local three-hole obstruction above is not an initial-root counterstrategy
and cannot by itself disprove FIFO. -/
theorem reachable_chargedBasin_local_obstruction_not_upward_extendable :
    IsEmpty (OddStrategy reachableTwoVertexBasinGraph false
      reachableChargedBasinAfterTwoOpens) := by
  have h := no_oddStrategy_reachableBasinAfterOpenOne
  change IsEmpty (OddStrategy reachableTwoVertexBasinGraph false
    reachableChargedBasinAfterTwoOpens) at h
  exact h

end

end Ogdoad.Fifo
