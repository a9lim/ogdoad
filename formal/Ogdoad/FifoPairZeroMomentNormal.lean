import Ogdoad.FifoPairZeroMomentSafety
import Ogdoad.FifoParityCounterNormal
import Ogdoad.FifoPublicPrefixQueueCutBoundary

/-!
# Minimal counterstrategy reduction below a q=0 initial pair

At a same-degree two-OPEN root the queued fronts have equal residual close
charge.  If an alleged odd strategy had no smaller score-zero descendant,
the exact minimal-node theorem would force its selected first CLOSE to have
unit charge, while the universal second CLOSE would force the second front
to have zero charge.  Balance makes those conclusions incompatible.

Thus every alleged q=0 pair counterstrategy has a strictly smaller score-zero
descendant in its own exact strategy tree.  The second-moment hypothesis does
not strengthen this first descent: it identifies the root residual Gram debt,
but the descendant need not be another two-cell q=0 state.  The already
formalized third-moment example shows why direct recursive iteration fails.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A q=0 same-degree initial pair is balanced on its twice-punctured
residual carrier. -/
theorem zeroMomentPair_residual_front_balanced
    (G : SimpleGraph V) (x y : V)
    (hy : y ∈ sameDegreeMates G Finset.univ x)
    (_hmoment : pairSecondMoment G Finset.univ x y = 0) :
    flip G ((Finset.univ.erase x).erase y) x =
      flip G ((Finset.univ.erase x).erase y) y := by
  exact sameDegreeMate_balances_residual G Finset.univ x y
    (Finset.mem_univ x) hy

/-- The second scalar condition is exactly zero residual Gram debt. -/
theorem zeroMomentPair_residualGram_zero
    (G : SimpleGraph V) (x y : V)
    (hy : y ∈ sameDegreeMates G Finset.univ x)
    (hmoment : pairSecondMoment G Finset.univ x y = 0) :
    pairResidualGram G Finset.univ x y = 0 := by
  exact (pairResidualGram_eq_pairSecondMoment_of_sameDegreeMate
    G Finset.univ x y (Finset.mem_univ x) hy).trans hmoment

/-- The public Bellman root is also on the zero potential sheet.  This uses
front balance; q=0 supplies the additional, independent Gram constraint. -/
theorem zeroMomentPair_potential_zero
    (G : SimpleGraph V) (x y : V)
    (hy : y ∈ sameDegreeMates G Finset.univ x)
    (hmoment : pairSecondMoment G Finset.univ x y = 0) :
    potential G (afterInitialTwoOpens x y) = 0 := by
  have hbalanced := zeroMomentPair_residual_front_balanced
    G x y hy hmoment
  rw [potential]
  simp only [afterInitialTwoOpens, queueCut, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, zero_add]
  rw [hbalanced]
  exact CharTwo.add_self_eq_zero _

/-- The two-OPEN root is well formed whenever the displayed pair is
distinct, as certified by same-degree-mate membership. -/
theorem wellFormed_afterInitialTwoOpens_of_sameDegreeMate
    (G : SimpleGraph V) (x y : V)
    (hy : y ∈ sameDegreeMates G Finset.univ x) :
    WellFormed (afterInitialTwoOpens x y) := by
  have hfirst := initial_step_open G x
  have hyErase : y ∈ (Finset.univ.erase x : Finset V) :=
    (Finset.mem_filter.mp hy).1
  have hsecond := (afterInitialOpen_step_open_iff G x y).2 hyErase
  exact wellFormed_step (wellFormed_step wellFormed_initial hfirst) hsecond

/-- Exact ancestry scalar at a q=0 pair root.  The bare prefix evaluates to
the descendant potential; after adding the descendant queue-cut vector, the
decorated residual evaluates to the descendant score. -/
theorem StrategyPrefix.graphEvaluation_decoratedQueueCut_of_zeroMomentPair
    {G : SimpleGraph V} {seat : Bool} {x y : V} {s : State V}
    {root : OddStrategy G seat (afterInitialTwoOpens x y)}
    {tree : OddStrategy G seat s} {p : EdgeVector V}
    (hp : StrategyPrefix G seat root tree p)
    (hy : y ∈ sameDegreeMates G Finset.univ x)
    (hmoment : pairSecondMoment G Finset.univ x y = 0) :
    graphEvaluation G (p + rootQueueCutVector s.public) = s.score := by
  have hrootWF := wellFormed_afterInitialTwoOpens_of_sameDegreeMate G x y hy
  have hprefix := hp.graphEvaluation_eq_potential_add hrootWF
  rw [map_add, hprefix, graphEvaluation_rootQueueCutVector,
    zeroMomentPair_potential_zero G x y hy hmoment, zero_add]
  simp only [potential, State.public]
  let q := queueCut G s.untouched s.queue
  change s.score + q + q = s.score
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- At the smaller score-zero descendant, the tempting prefix-plus-queue-cut
target is on the homogeneous scalar sheet and therefore cannot itself be a
continuation point of the root odd strategy. -/
theorem StrategyPrefix.decoratedQueueCut_not_affine_of_zeroMomentPair
    {G : SimpleGraph V} {seat : Bool} {x y : V} {s : State V}
    {root : OddStrategy G seat (afterInitialTwoOpens x y)}
    {tree : OddStrategy G seat s} {p : EdgeVector V}
    (hp : StrategyPrefix G seat root tree p)
    (hy : y ∈ sameDegreeMates G Finset.univ x)
    (hmoment : pairSecondMoment G Finset.univ x y = 0)
    (hs0 : s.score = 0) :
    ¬AffineResponseMoment G seat root
      (p + rootQueueCutVector s.public) := by
  intro hresponse
  have hrootWF := wellFormed_afterInitialTwoOpens_of_sameDegreeMate G x y hy
  have hone := hresponse.graphEvaluation_eq hrootWF
  have hzero := hp.graphEvaluation_decoratedQueueCut_of_zeroMomentPair
    hy hmoment
  rw [hs0] at hzero
  rw [hzero, zeroMomentPair_potential_zero G x y hy hmoment] at hone
  exact zero_ne_one hone

/-! ## Exact factor-extension boundary -/

omit [Fintype V] in
/-- With unrestricted ancestry holes, the full-edge factor equation is
equivalent to the root affine-zero target.  The reverse implication uses the
root itself as a one-term hole, so this certificate language is not a smaller
inductive invariant until its allowed causal frontier is restricted. -/
theorem nonempty_strategyFactorCertificate_iff_affine_zero
    {G : SimpleGraph V} {seat : Bool} {rootState : State V}
    {root : OddStrategy G seat rootState} :
    Nonempty (StrategyFactorCertificate G seat root) ↔
      AffineResponseMoment G seat root 0 := by
  constructor
  · rintro ⟨certificate⟩
    exact certificate.zero
  · intro hzero
    let hole : StrategyHole G seat root := {
      state := rootState
      tree := root
      moment := 0
      ancestry := StrategyPrefix.root }
    let term : StrategyFactorTerm G seat root := {
      hole := hole
      base := 0
      correction := 0
      base_mem := hzero
      correction_mem := ResponseDirection.zero root }
    exact ⟨{
      terms := [term]
      odd := by simp
      factor := by simp [term, hole] }⟩

/-- Consequently an actual odd strategy at a q=0 pair root admits no
unrestricted factor certificate: such a certificate would already be the
desired contradiction.  Root potential zero makes the scalar obstruction
explicit (`0 = 1`). -/
theorem zeroMomentPair_no_strategyFactorCertificate
    {G : SimpleGraph V} {seat : Bool} {x y : V}
    (hy : y ∈ sameDegreeMates G Finset.univ x)
    (hmoment : pairSecondMoment G Finset.univ x y = 0)
    (root : OddStrategy G seat (afterInitialTwoOpens x y)) :
    ¬Nonempty (StrategyFactorCertificate G seat root) := by
  intro hcertificate
  have hzero : AffineResponseMoment G seat root 0 :=
    nonempty_strategyFactorCertificate_iff_affine_zero.mp hcertificate
  have heval := hzero.graphEvaluation_eq
    (wellFormed_afterInitialTwoOpens_of_sameDegreeMate G x y hy)
  rw [map_zero, zeroMomentPair_potential_zero G x y hy hmoment] at heval
  exact zero_ne_one heval

/-- First exact Bellman descent for q=0 pair safety.  Every odd strategy at
the pair root contains a strictly smaller score-zero descendant. -/
theorem OddStrategy.zeroMomentPair_exists_smaller_zero
    {G : SimpleGraph V} {seat : Bool} {x y : V}
    (hy : y ∈ sameDegreeMates G Finset.univ x)
    (hmoment : pairSecondMoment G Finset.univ x y = 0)
    (root : OddStrategy G seat (afterInitialTwoOpens x y)) :
    ∃ (t : State V) (desc : OddStrategy G seat t),
      StrategyNode G seat root desc ∧
        rank t < rank (afterInitialTwoOpens x y) ∧ t.score = 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hminimal : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat root desc →
      rank t < rank (afterInitialTwoOpens x y) → t.score ≠ 0 := by
    intro t desc hnode hrank ht0
    exact hnone t desc hnode hrank ht0
  have hbalanced := zeroMomentPair_residual_front_balanced
    G x y hy hmoment
  obtain ⟨_hturn, f, q, sc, hqueue, _hko, _hclose, hflip, _hneutral⟩ :=
    root.minimal_zeroNode_close_neutral rfl hminimal
  have hshape : f :: q = [x, y] := by
    exact hqueue.symm
  have hfx : f = x := (List.cons.inj hshape).1
  subst f
  have hq : q = [y] := (List.cons.inj hshape).2
  have hyZero := root.minimal_zeroNode_secondFront_flip_zero
    rfl hminimal (f := x) (y := y) (q := []) (by rfl)
  have hxOne :
      flip G ((Finset.univ.erase x).erase y) x = 1 := by
    simpa [afterInitialTwoOpens] using hflip
  have hyZero' :
      flip G ((Finset.univ.erase x).erase y) y = 0 := by
    simpa [afterInitialTwoOpens] using hyZero
  rw [hbalanced, hyZero'] at hxOne
  exact zero_ne_one hxOne

/-- The strict descendant comes with an exact original-root ancestry prefix.
Its prefix-plus-current-queue-cut residual evaluates to zero, but is not an
affine continuation point of the root strategy.  This is the precise point
where scalar infinite descent stops and ancestry factor extension begins. -/
theorem OddStrategy.zeroMomentPair_extract_decorated_boundary
    {G : SimpleGraph V} {seat : Bool} {x y : V}
    (hy : y ∈ sameDegreeMates G Finset.univ x)
    (hmoment : pairSecondMoment G Finset.univ x y = 0)
    (root : OddStrategy G seat (afterInitialTwoOpens x y)) :
    ∃ (t : State V) (desc : OddStrategy G seat t) (p : EdgeVector V),
      StrategyPrefix G seat root desc p ∧
        rank t < rank (afterInitialTwoOpens x y) ∧ t.score = 0 ∧
        graphEvaluation G (p + rootQueueCutVector t.public) = 0 ∧
        ¬AffineResponseMoment G seat root
          (p + rootQueueCutVector t.public) := by
  obtain ⟨t, desc, hnode, hrank, ht0⟩ :=
    root.zeroMomentPair_exists_smaller_zero hy hmoment
  obtain ⟨p, hp⟩ := hnode.exists_strategyPrefix
  have heval := hp.graphEvaluation_decoratedQueueCut_of_zeroMomentPair
    hy hmoment
  rw [ht0] at heval
  exact ⟨t, desc, p, hp, hrank, ht0, heval,
    hp.decoratedQueueCut_not_affine_of_zeroMomentPair hy hmoment ht0⟩

/-- Refine the proper zero descendant to the existing causal minimal form.
Its selected charged CLOSE has a neutral translated tail; away from a
singleton queue there is an actual adjacent OPEN/CLOSE pivot carrying the
transported neutral strategy.  This is the strongest graph-independent local
normal form supplied by the q=0 root data alone. -/
theorem OddStrategy.zeroMomentPair_extract_causal_minimum
    {G : SimpleGraph V} {seat : Bool} {x y : V}
    (hy : y ∈ sameDegreeMates G Finset.univ x)
    (hmoment : pairSecondMoment G Finset.univ x y = 0)
    (root : OddStrategy G seat (afterInitialTwoOpens x y)) :
    ∃ (t : State V) (desc : OddStrategy G seat t),
      StrategyNode G seat root desc ∧
      rank t < rank (afterInitialTwoOpens x y) ∧ t.score = 0 ∧
      ∃ (s : State V) (strategy : OddStrategy G seat s),
        StrategyNode G seat desc strategy ∧ s.score = 0 ∧
        s.toMove = !seat ∧
        ∃ f q sc, s.queue = f :: q ∧ s.ko = false ∧
          step G s .close = some sc ∧ flip G s.untouched f = 1 ∧
          TreeNeutralWins G (!seat) (scoreTranslate 1 sc) ∧
          (q = [] ∨ ∃ z so soc,
            z ∈ s.untouched ∧ G.Adj f z ∧
            step G s (.open z) = some so ∧
            step G so .close = some soc ∧
            TreeNeutralWins G (!seat) soc) := by
  obtain ⟨t, desc, hnode, hrank, ht0⟩ :=
    root.zeroMomentPair_exists_smaller_zero hy hmoment
  obtain ⟨s, strategy, hinner, hs0, hturn, f, q, sc, hqueue, hko,
      hclose, hflip, hneutral, hcausal⟩ :=
    desc.extract_causal_neighbor_or_singleton ht0
  exact ⟨t, desc, hnode, hrank, ht0, s, strategy, hinner, hs0, hturn,
    f, q, sc, hqueue, hko, hclose, hflip, hneutral, hcausal⟩

/-- The descent cannot simply recurse on the two scalar hypotheses.  The
existing exact third-moment witness starts from a same-degree q=0 pair, yet
its forced two-bit OPEN mate creates unit second moment on the next cell. -/
theorem zeroMomentPair_recursive_invariant_obstruction :
    (7 : Fin 9) ∈
        sameDegreeMates thirdMomentCounterGraph thirdMomentCounterR 6 ∧
      pairSecondMoment thirdMomentCounterGraph thirdMomentCounterR 6 7 = 0 ∧
      pairSecondMoment thirdMomentCounterGraph thirdMomentCounterS 1 2 = 1 := by
  exact ⟨thirdMomentCounter_root_data.2.1,
    thirdMomentCounter_root_data.2.2, thirdMomentCounter_new_pair_debt⟩

end

end Ogdoad.Fifo
