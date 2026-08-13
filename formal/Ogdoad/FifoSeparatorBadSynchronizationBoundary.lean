import Ogdoad.FifoStrategyBadAncestryClear
import Ogdoad.FifoPublicSeparatorAutomaton

/-!
# Separator minima do not synchronize with minimal bad FIFO nodes

For an actual odd strategy on a graph with isolated dummy, graph evaluation
factors through the real-edge quotient and supplies the canonical separator
functional.  The forgotten public policy at any well-formed strategy node is
then uniformly on sheet `1 + potential`.

This identifies the exact mismatch between the two natural minimizations.
The concrete bad-ancestry theorem minimizes nodes of **score** zero.  The
separator automaton minimizes nodes of **potential** zero, where potential is
score plus the current queue cut.  At the concrete minimum, the displayed
strategy move is a charged front `CLOSE`; its forgotten policy therefore
cannot be a separator-one minimum.  If it is on sheet one at all, the silent
selected CLOSE leaves its child on sheet one at lower rank.

More precisely, the charged front contributes one, so the separator sheet of
the concrete minimum is exactly the queue cut of the tail behind that front.
The charged-CLOSE/protected-OPEN predecessor dichotomy does not remove this
mismatch: both cases feed the same selected-CLOSE bad node.  Thus combining
the two independent minima does not exclude the selected real unit-OPEN with
inherited queue debt.  A proof still needs an ancestry comparison transporting
one minimum to the other.

This is an exact no-go boundary, not a proof or disproof of FIFO linking.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The linear functional on real-edge coordinates represented by an actual
simple graph with isolated dummy. -/
def isolatedGraphSeparatorFunctional (G : SimpleGraph V) (d : V)
    (hd : IsDummy G d) : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2 :=
  (realEdgeNullSpace d).liftQ
    ((graphEvaluation G).toZModLinearMap 2)
    (realEdgeNullSpace_le_graphEvaluation_ker hd)

omit [Fintype V] in
/-- The canonical quotient functional evaluates exactly as the source graph. -/
@[simp] theorem isolatedGraphSeparatorFunctional_projection
    (G : SimpleGraph V) (d : V) (hd : IsDummy G d)
    (z : EdgeVector V) :
    isolatedGraphSeparatorFunctional G d hd (realEdgeProjection d z) =
      graphEvaluation G z := by
  rfl

omit [Fintype V] in
/-- Public separator evaluation for the canonical functional is ordinary
graph evaluation. -/
@[simp] theorem publicSeparatorEvaluation_isolatedGraph
    (G : SimpleGraph V) (d : V) (hd : IsDummy G d)
    (z : EdgeVector V) :
    publicSeparatorEvaluation d (isolatedGraphSeparatorFunctional G d hd) z =
      graphEvaluation G z := by
  rfl

omit [Fintype V] in
/-- At every well-formed node of an actual odd strategy, forgetting scores
places the entire public affine response space on the canonical sheet
`1 + potential`. -/
theorem OddStrategy.toPublicPolicy_canonicalSeparatorSheet
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    {seat : Bool} {s : State V} (strategy : OddStrategy G seat s)
    (hs : WellFormed s) :
    PublicPolicySeparatorSheet d
      (isolatedGraphSeparatorFunctional G d hd) seat
      strategy.toPublicPolicy (1 + potential G s) := by
  intro z hz
  rw [publicSeparatorEvaluation_isolatedGraph]
  exact (hz.toAffineResponseMoment strategy).graphEvaluation_eq hs

omit [Fintype V] in
/-- The canonical separator sheet is unique because every finite policy has
at least one affine response moment. -/
theorem OddStrategy.toPublicPolicy_separatorSheet_eq
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    {seat : Bool} {s : State V} (strategy : OddStrategy G seat s)
    (hs : WellFormed s) {b : ZMod 2}
    (h : PublicPolicySeparatorSheet d
      (isolatedGraphSeparatorFunctional G d hd) seat
      strategy.toPublicPolicy b) :
    b = 1 + potential G s := by
  obtain ⟨z, hz⟩ := strategy.toPublicPolicy.exists_affineMoment
  have hb := h z hz
  have hcanonical :=
    strategy.toPublicPolicy_canonicalSeparatorSheet hd hs z hz
  exact hb.symm.trans hcanonical

omit [Fintype V] in
/-- Canonical sheet one is exactly potential zero. -/
theorem OddStrategy.toPublicPolicy_separatorOne_iff_potential_zero
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    {seat : Bool} {s : State V} (strategy : OddStrategy G seat s)
    (hs : WellFormed s) :
    PublicPolicySeparatorSheet d
        (isolatedGraphSeparatorFunctional G d hd) seat
        strategy.toPublicPolicy 1 ↔
      potential G s = 0 := by
  constructor
  · intro h
    have heq := strategy.toPublicPolicy_separatorSheet_eq hd hs h
    calc
      potential G s = (1 + 1) + potential G s := by
        rw [CharTwo.add_self_eq_zero, zero_add]
      _ = 1 + (1 + potential G s) := by abel
      _ = 1 + 1 := by rw [← heq]
      _ = 0 := CharTwo.add_self_eq_zero 1
  · intro hzero
    have hcanonical := strategy.toPublicPolicy_canonicalSeparatorSheet hd hs
    simpa [hzero] using hcanonical

omit [Fintype V] in
/-- A selected CLOSE in an actual odd strategy forbids immediate separator
minimality for every separator functional, independently of graph scores.
If the parent policy lies on sheet one, the silent CLOSE child lies on sheet
one as well. -/
theorem OddStrategy.selectedClose_not_separatorOneImmediateMinimal
    {G : SimpleGraph V} {d : V}
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    {seat : Bool} {s : State V} (strategy : OddStrategy G seat s)
    (hselected : strategy.selectedMove = some .close) :
    ¬PublicPolicySeparatorOneImmediateMinimal d ell seat
      strategy.toPublicPolicy := by
  intro hminimal
  cases strategy with
  | terminal s ht hs =>
      simp [OddStrategy.selectedMove] at hselected
  | answer s hseat hasMove children =>
      simp [OddStrategy.selectedMove] at hselected
  | choose s hseat m t hstep child =>
      have hm : m = .close := by
        simpa [OddStrategy.selectedMove] using Option.some.inj hselected
      subst m
      have hchild :=
        (publicPolicySeparatorSheet_choose_iff d ell seat hseat .close
          (by rw [← step_public G s .close, hstep]; rfl)
          child.toPublicPolicy 1).1 hminimal.1
      apply hminimal.2
      simpa [publicSeparatorEvaluation, moveLiveStar] using hchild

omit [Fintype V] in
/-- At a concrete score-zero charged-front bad node, the canonical separator
sheet is exactly the graph queue cut of the tail behind the front. -/
theorem minimalBad_selectedClose_canonical_sheet_eq_tailQueueCut
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    {seat : Bool} {s : State V} (strategy : OddStrategy G seat s)
    (hs : WellFormed s) {f : V} {q : List V}
    (hscore : s.score = 0) (hqueue : s.queue = f :: q)
    (hcharge : flip G s.untouched f = 1) :
    PublicPolicySeparatorSheet d
      (isolatedGraphSeparatorFunctional G d hd) seat
      strategy.toPublicPolicy (queueCut G s.untouched q) := by
  have hcanonical := strategy.toPublicPolicy_canonicalSeparatorSheet hd hs
  have hpotential : 1 + potential G s = queueCut G s.untouched q := by
    simp only [potential, hscore, zero_add, hqueue, queueCut,
      List.map_cons, List.sum_cons, hcharge]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  simpa [hpotential] using hcanonical

/-- The concrete minimal bad node extracted by the strategy-relative normal
form can never itself be the separator-one immediate minimum.  This conclusion
is independent of which predecessor case survives. -/
theorem extractedMinimalBadPolicy_not_separatorOneImmediateMinimal
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    {seat : Bool} (root : OddStrategy G seat (initial (V := V))) :
    ∃ (s : State V) (strategy : OddStrategy G seat s)
      (parent : State V) (incoming : Move V) (f : V) (q : List V),
      s.score = 0 ∧ s.queue = f :: q ∧
      flip G s.untouched f = 1 ∧
      MinimalBadPredecessorNormalCase G parent s f q incoming ∧
      strategy.selectedMove = some .close ∧
      ¬PublicPolicySeparatorOneImmediateMinimal d
        (isolatedGraphSeparatorFunctional G d hd) seat
        strategy.toPublicPolicy := by
  obtain ⟨s, strategy, _p, parent, _parentTree, _pp, incoming, f, q,
      _sc, _hprefix, _hparentPrefix, _hparentTurn, _hincoming, _hp, _hfan,
      hscore, _hturn, hqueue, _hko, _hclose, hcharge, _hfreal,
      hselected, _hneutral, hnormal⟩ :=
    root.extract_minimalBad_predecessor_normalCases hd
  exact ⟨s, strategy, parent, incoming, f, q,
    hscore, hqueue, hcharge, hnormal, hselected,
    strategy.selectedClose_not_separatorOneImmediateMinimal
      (isolatedGraphSeparatorFunctional G d hd) hselected⟩

/-! ## The score sheet of a selected separator minimum -/

omit [Fintype V] in
/-- Concrete score consequence of the same-root separator recurrence.  The
hypothesis `hpotential` is exactly what the preceding canonical-sheet theorem
supplies when this displayed public policy is the forgetting of the actual
odd subtree.

At a globally minimal sheet-one selected OPEN, every untouched OPEN in the
complete child fan has zero live degree.  Handshaking identifies their sum
with the child's queue cut, so that cut is zero.  The selected OPEN has live
degree one and toggles potential from zero to one while preserving score.
Consequently both concrete states have score one; the parent queue carries cut
one and the child queue carries cut zero. -/
theorem separatorRankMinimal_selectedOpen_scoreOne
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    {seat : Bool} {s t : State V}
    (hseat : s.toMove ≠ seat) (v : V)
    (hstep : step G s (.open v) = some t)
    (hturn : t.toMove = seat)
    (hasMove : ∃ m u, publicStep t.public m = some u)
    (children : ∀ m u, publicStep t.public m = some u →
      PublicPolicy seat u)
    (hpstep : publicStep s.public (.open v) = some t.public)
    (hminimal : PublicPolicySeparatorOneRankMinimal d
      (isolatedGraphSeparatorFunctional G d hd) seat
      (.choose s.public hseat (.open v) t.public hpstep
        (.answer t.public hturn hasMove children)))
    (hs : WellFormed s) (hpotential : potential G s = 0) :
    s.score = 1 ∧ queueCut G s.untouched s.queue = 1 ∧
      t.score = 1 ∧ queueCut G t.untouched t.queue = 0 ∧
        potential G s = 0 ∧ potential G t = 1 := by
  have htWF : WellFormed t := wellFormed_step hs hstep
  have himmediate := hminimal.immediate d
    (isolatedGraphSeparatorFunctional G d hd) seat
  have hopenEval := separatorOneImmediateMinimal_choose_increment_eq_one
    d (isolatedGraphSeparatorFunctional G d hd) seat hseat (.open v)
      hpstep (.answer t.public hturn hasMove children) himmediate
  have hopenDegree : liveDegree G s v = 1 := by
    rw [publicSeparatorEvaluation_isolatedGraph,
      moveLiveStar_public_toZeroState,
      graphEvaluation_moveLiveStar G s (.open v) hs] at hopenEval
    exact hopenEval
  have hchildIncrementZero : ∀ z ∈ t.untouched,
      liveDegree G t z = 0 := by
    intro z hz
    let u : PublicState V := {
      untouched := t.untouched.erase z
      queue := t.queue ++ [z]
      ko := t.queue.isEmpty
      toMove := !t.toMove }
    have hzstep : publicStep t.public (.open z) = some u := by
      simp [publicStep, State.public, u, hz]
    have hzero := separatorRankMinimal_choose_answer_child_increment_zero
      d (isolatedGraphSeparatorFunctional G d hd) seat hseat v hpstep
        hturn hasMove children hminimal (.open z) u hzstep
    rw [publicSeparatorEvaluation_isolatedGraph,
      moveLiveStar_public_toZeroState,
      graphEvaluation_moveLiveStar G t (.open z) htWF] at hzero
    exact hzero
  have hchildFlipZero : ∀ z ∈ t.untouched,
      flip G (liveSet t) z = 0 := by
    intro z hz
    rw [← liveDegree_eq_flip_liveSet htWF]
    exact hchildIncrementZero z hz
  have hqueueChild : queueCut G t.untouched t.queue = 0 := by
    have hsum := sum_flip_union_queue_eq_queueCut G
      htWF.1 htWF.2.symm
    have hsumZero :
        (∑ z ∈ t.untouched, flip G
          (t.untouched ∪ t.queue.toFinset) z) = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      exact hchildFlipZero z hz
    rw [hsumZero] at hsum
    exact hsum.symm
  have hpotentialChild : potential G t = 1 := by
    rw [open_adds_liveDegree_to_potential hstep, hpotential, hopenDegree,
      zero_add]
  have hscoreChild : t.score = 1 := by
    simpa [potential, hqueueChild] using hpotentialChild
  have hscoreEq : t.score = s.score := by
    simp only [step] at hstep
    split at hstep
    · cases hstep
      rfl
    · contradiction
  have hscoreParent : s.score = 1 := hscoreEq.symm.trans hscoreChild
  have hqueueParent : queueCut G s.untouched s.queue = 1 := by
    have hp : s.score + queueCut G s.untouched s.queue = 0 := by
      simpa [potential] using hpotential
    rw [hscoreParent] at hp
    have hadd := congrArg (fun z : ZMod 2 ↦ 1 + z) hp
    simpa [← add_assoc, CharTwo.add_self_eq_zero] using hadd
  exact ⟨hscoreParent, hqueueParent, hscoreChild, hqueueChild,
    hpotential, hpotentialChild⟩

/-- Exact synchronization boundary exported as one structure.  The concrete
bad node has score zero and charged front, but is not a separator minimum;
its canonical separator bit is the tail queue cut. -/
structure SeparatorBadSynchronizationBoundary
    (G : SimpleGraph V) (d : V) (seat : Bool) where
  state : State V
  strategy : OddStrategy G seat state
  parent : State V
  incoming : Move V
  front : V
  tail : List V
  score_zero : state.score = 0
  queue_eq : state.queue = front :: tail
  front_charge_one : flip G state.untouched front = 1
  normalCase : MinimalBadPredecessorNormalCase G parent state front tail incoming
  selected_close : strategy.selectedMove = some .close

/-- Every alleged isolated-dummy initial odd strategy contains the exact
synchronization boundary. -/
theorem OddStrategy.exists_separatorBadSynchronizationBoundary
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    {seat : Bool} (root : OddStrategy G seat (initial (V := V))) :
    Nonempty (SeparatorBadSynchronizationBoundary G d seat) := by
  obtain ⟨s, strategy, parent, incoming, f, q, hscore, hqueue, hcharge,
      hnormal, hselected, _hnot⟩ :=
    extractedMinimalBadPolicy_not_separatorOneImmediateMinimal hd root
  exact ⟨{
    state := s
    strategy := strategy
    parent := parent
    incoming := incoming
    front := f
    tail := q
    score_zero := hscore
    queue_eq := hqueue
    front_charge_one := hcharge
    normalCase := hnormal
    selected_close := hselected }⟩

/-! ## What state-positionality can and cannot identify -/

/-- Extensional state-positionality for one displayed Type-valued strategy:
every two attacker-owned occurrences with identical full concrete state have
the same selected move. -/
def OddStrategy.StatePositional
    {G : SimpleGraph V} {seat : Bool} {rootState : State V}
    (root : OddStrategy G seat rootState) : Prop :=
  ∀ {s : State V} (left right : OddStrategy G seat s),
    StrategyNode G seat root left → StrategyNode G seat root right →
      s.toMove ≠ seat → left.selectedMove = right.selectedMove

omit [Fintype V] in
/-- A state-positional strategy really does identify the selected moves at a
reconvergent concrete-state diamond. -/
theorem OddStrategy.StatePositional.selectedMove_eq_of_reconvergence
    {G : SimpleGraph V} {seat : Bool} {rootState s : State V}
    {root : OddStrategy G seat rootState} (hpos : root.StatePositional)
    (left right : OddStrategy G seat s)
    (hleft : StrategyNode G seat root left)
    (hright : StrategyNode G seat root right)
    (hattacker : s.toMove ≠ seat) :
    left.selectedMove = right.selectedMove :=
  hpos left right hleft hright hattacker

omit [Fintype V] in
/-- Selected-move equality is not continuation equality.  If two
reconvergent attacker occurrences select the same move and therefore reach
the same successor, the Type-valued child policies can still be distinct;
state-positionality supplies no theorem equating them.  This exact interface
is the remaining requirement for transporting affine continuation cosets
around a commuting square. -/
def OddStrategy.StateContinuationCoherent
    {G : SimpleGraph V} {seat : Bool} {rootState : State V}
    (root : OddStrategy G seat rootState) : Prop :=
  ∀ {s t : State V}
    (left right : OddStrategy G seat s)
    (_hleft : StrategyNode G seat root left)
    (_hright : StrategyNode G seat root right)
    (m : Move V) (_hstep : step G s m = some t)
    (leftChild rightChild : OddStrategy G seat t),
      left.selectedMove = some m → right.selectedMove = some m →
        StrategyNode G seat left leftChild →
          StrategyNode G seat right rightChild →
            leftChild = rightChild

/-- Logical boundary: continuation coherence implies state-positionality only
after one additionally supplies matching child occurrences for the selected
move.  The bare state-positional hypothesis contains only an equality in
`Option (Move V)` and cannot rewrite either dependent child tree or its affine
response space. -/
def OddStrategy.PositionalDiamondSynchronizationTarget
    {G : SimpleGraph V} {seat : Bool} {rootState : State V}
    (root : OddStrategy G seat rootState) : Prop :=
  root.StatePositional ∧ root.StateContinuationCoherent

/-! ## A canonical memoized odd strategy -/

omit [Fintype V] in
private theorem OddWins.terminal_score_ne
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (hodd : OddWins G seat s) (ht : Terminal s) : s.score ≠ 0 := by
  cases hodd with
  | terminal _ _ hs => exact hs
  | choose _ _ m t hstep _ =>
      exact False.elim (terminal_no_step ht ⟨m, t, hstep⟩)
  | answer _ _ hasMove _ => exact False.elim (terminal_no_step ht hasMove)

omit [Fintype V] in
private theorem OddWins.exists_odd_child_of_attacker
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (hodd : OddWins G seat s) (hseat : s.toMove ≠ seat)
    (ht : ¬Terminal s) :
    ∃ m t, step G s m = some t ∧ OddWins G seat t := by
  cases hodd with
  | terminal _ hterminal _ => exact False.elim (ht hterminal)
  | choose _ _ m t hstep hchild => exact ⟨m, t, hstep, hchild⟩
  | answer _ hdefender _ _ => exact False.elim (hseat hdefender)

omit [Fintype V] in
private theorem OddWins.all_odd_children_of_defender
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (hodd : OddWins G seat s) (hseat : s.toMove = seat)
    (ht : ¬Terminal s) :
    (∃ m t, step G s m = some t) ∧
      ∀ m t, step G s m = some t → OddWins G seat t := by
  cases hodd with
  | terminal _ hterminal _ => exact False.elim (ht hterminal)
  | choose _ hattacker _ _ _ _ => exact False.elim (hattacker hseat)
  | answer _ _ hasMove children => exact ⟨hasMove, children⟩

/-- One certified odd-winning move and successor. -/
structure OddChildWitness (G : SimpleGraph V) (seat : Bool) (s : State V) where
  move : Move V
  next : State V
  step_eq : step G s move = some next
  odd : OddWins G seat next

/-- One canonical odd-winning move and successor at an attacker-owned
odd-winning nonterminal state. -/
noncomputable def canonicalOddChoice
    (G : SimpleGraph V) (seat : Bool) (s : State V)
    (hodd : OddWins G seat s) (hseat : s.toMove ≠ seat)
    (ht : ¬Terminal s) : OddChildWitness G seat s :=
  Classical.choice (show Nonempty (OddChildWitness G seat s) by
    obtain ⟨m, t, hstep, hchild⟩ :=
      hodd.exists_odd_child_of_attacker hseat ht
    exact ⟨⟨m, t, hstep, hchild⟩⟩)

omit [Fintype V] in
theorem canonicalOddChoice_spec
    (G : SimpleGraph V) (seat : Bool) (s : State V)
    (hodd : OddWins G seat s) (hseat : s.toMove ≠ seat)
    (ht : ¬Terminal s) :
    step G s (canonicalOddChoice G seat s hodd hseat ht).move =
        some (canonicalOddChoice G seat s hodd hseat ht).next ∧
      OddWins G seat (canonicalOddChoice G seat s hodd hseat ht).next :=
  ⟨(canonicalOddChoice G seat s hodd hseat ht).step_eq,
    (canonicalOddChoice G seat s hodd hseat ht).odd⟩

noncomputable def canonicalOddStrategy
    (G : SimpleGraph V) (seat : Bool) (s : State V)
    (hodd : OddWins G seat s) : OddStrategy G seat s := by
  by_cases ht : Terminal s
  · exact .terminal s ht (hodd.terminal_score_ne ht)
  · by_cases hseat : s.toMove = seat
    · obtain ⟨hasMove, hall⟩ :=
        hodd.all_odd_children_of_defender hseat ht
      exact .answer s hseat hasMove fun m t hstep ↦
        canonicalOddStrategy G seat t (hall m t hstep)
    · let choice := canonicalOddChoice G seat s hodd hseat ht
      have hchoice := canonicalOddChoice_spec G seat s hodd hseat ht
      exact .choose s hseat choice.move choice.next hchoice.1
        (canonicalOddStrategy G seat choice.next hchoice.2)
termination_by rank s
decreasing_by
  all_goals first
    | exact rank_step_lt hstep
    | exact rank_step_lt hchoice.1

omit [Fintype V] in
/-- The canonical tree is independent of the proof of `OddWins`, by proof
irrelevance at its state-indexed input. -/
theorem canonicalOddStrategy_proof_irrelevant
    (G : SimpleGraph V) (seat : Bool) (s : State V)
    (h₁ h₂ : OddWins G seat s) :
    canonicalOddStrategy G seat s h₁ =
      canonicalOddStrategy G seat s h₂ := by
  have : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

/-- Every immediate child stored in a memoized tree is the canonical tree of
its concrete successor state, and is recursively memoized itself. -/
def OddStrategy.CanonicallyMemoized
    {G : SimpleGraph V} {seat : Bool} :
    {s : State V} → OddStrategy G seat s → Prop
  | _, .terminal _ _ _ => True
  | _, .choose _ _ _ t _ child =>
      child = canonicalOddStrategy G seat t child.toOddWins ∧
        child.CanonicallyMemoized
  | _, .answer _ _ _ children =>
      ∀ m t (hstep : step G _ m = some t),
        children m t hstep =
            canonicalOddStrategy G seat t (children m t hstep).toOddWins ∧
          (children m t hstep).CanonicallyMemoized

omit [Fintype V] in
/-- The well-founded construction is genuinely memoized at every child. -/
theorem canonicalOddStrategy_memoized
    (G : SimpleGraph V) (seat : Bool) :
    ∀ (s : State V) (hodd : OddWins G seat s),
      (canonicalOddStrategy G seat s hodd).CanonicallyMemoized := by
  intro s
  induction s using (measure rank).wf.induction with
  | h s ih =>
      intro hodd
      rw [canonicalOddStrategy.eq_def]
      split
      · trivial
      · rename_i ht
        split
        · rename_i hseat
          obtain ⟨hasMove, hall⟩ :=
            hodd.all_odd_children_of_defender hseat ht
          intro m t hstep
          constructor
          · exact canonicalOddStrategy_proof_irrelevant G seat t
              (hall m t hstep)
              (canonicalOddStrategy G seat t
                (hall m t hstep)).toOddWins
          · exact ih t (rank_step_lt hstep) (hall m t hstep)
        · rename_i hseat
          let choice := canonicalOddChoice G seat s hodd hseat ht
          have hchoice := canonicalOddChoice_spec G seat s hodd hseat ht
          constructor
          · exact canonicalOddStrategy_proof_irrelevant G seat choice.next
              hchoice.2
              (canonicalOddStrategy G seat choice.next hchoice.2).toOddWins
          · exact ih choice.next (rank_step_lt hchoice.1) hchoice.2

omit [Fintype V] in
/-- In a memoized tree whose root is canonical, every descendant occurrence
is the canonical tree of its concrete state. -/
theorem OddStrategy.CanonicallyMemoized.node_eq_canonical
    {G : SimpleGraph V} {seat : Bool} {r s : State V}
    {root : OddStrategy G seat r} {desc : OddStrategy G seat s}
    (hroot : root = canonicalOddStrategy G seat r root.toOddWins)
    (hmemo : root.CanonicallyMemoized)
    (hnode : StrategyNode G seat root desc) :
    desc = canonicalOddStrategy G seat s desc.toOddWins := by
  induction hnode with
  | root => exact hroot
  | @choose a b c hseat m hstep child desc hdesc ih =>
      exact ih hmemo.1 hmemo.2
  | @answer a b c hseat hasMove children m hstep desc hdesc ih =>
      exact ih (hmemo m b hstep).1 (hmemo m b hstep).2

omit [Fintype V] in
/-- Strong positional quotient: any two occurrences of the same full
concrete state inside the canonical tree are equal as Type-valued strategies,
not merely equal in their selected move. -/
theorem canonicalOddStrategy_subtree_unique
    (G : SimpleGraph V) (seat : Bool) (r : State V)
    (hodd : OddWins G seat r) {s : State V}
    (left right : OddStrategy G seat s)
    (hleft : StrategyNode G seat
      (canonicalOddStrategy G seat r hodd) left)
    (hright : StrategyNode G seat
      (canonicalOddStrategy G seat r hodd) right) :
    left = right := by
  have hmemo := canonicalOddStrategy_memoized G seat r hodd
  have hroot : canonicalOddStrategy G seat r hodd =
      canonicalOddStrategy G seat r
        (canonicalOddStrategy G seat r hodd).toOddWins :=
    canonicalOddStrategy_proof_irrelevant G seat r _ _
  have hl := hmemo.node_eq_canonical hroot hleft
  have hr := hmemo.node_eq_canonical hroot hright
  calc
    left = canonicalOddStrategy G seat s left.toOddWins := hl
    _ = canonicalOddStrategy G seat s right.toOddWins :=
      canonicalOddStrategy_proof_irrelevant G seat s _ _
    _ = right := hr.symm

omit [Fintype V] in
/-- Every odd-winning state therefore admits a canonical Type-valued strategy
satisfying both selected-move positionality and the stronger continuation
coherence required by a reconvergent commuting square. -/
theorem canonicalOddStrategy_positionalDiamondSynchronization
    (G : SimpleGraph V) (seat : Bool) (s : State V)
    (hodd : OddWins G seat s) :
    (canonicalOddStrategy G seat s hodd).PositionalDiamondSynchronizationTarget := by
  let root := canonicalOddStrategy G seat s hodd
  constructor
  · intro u left right hleft hright _hattacker
    rw [canonicalOddStrategy_subtree_unique G seat s hodd left right
      hleft hright]
  · intro u t left right hleft hright m hstep leftChild rightChild
      _hleftMove _hrightMove hleftChild hrightChild
    apply canonicalOddStrategy_subtree_unique G seat s hodd
    · exact hleft.trans hleftChild
    · exact hright.trans hrightChild

omit [Fintype V] in
/-- Exact existence form of the positional quotient: every odd-winning state
has a Type-valued odd strategy whose repeated concrete states share both their
selected move and their entire continuation tree. -/
theorem OddWins.nonempty_positionalDiamondSynchronization
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (hodd : OddWins G seat s) :
    Nonempty { strategy : OddStrategy G seat s //
      strategy.PositionalDiamondSynchronizationTarget } :=
  ⟨⟨canonicalOddStrategy G seat s hodd,
    canonicalOddStrategy_positionalDiamondSynchronization G seat s hodd⟩⟩

omit [Fintype V] in
/-- Affine payoff of a reconvergence in the canonical positional tree.  If
two root-to-node prefixes reach the same full concrete state, then the XOR of
their live-star prefix moments is a homogeneous response direction at the
root.  The shared continuation point cancels in characteristic two. -/
theorem canonicalOddStrategy_reconvergent_prefix_direction
    (G : SimpleGraph V) (seat : Bool) (r : State V)
    (hodd : OddWins G seat r) {s : State V}
    {left right : OddStrategy G seat s} {p q a : EdgeVector V}
    (hp : StrategyPrefix G seat
      (canonicalOddStrategy G seat r hodd) left p)
    (hq : StrategyPrefix G seat
      (canonicalOddStrategy G seat r hodd) right q)
    (ha : AffineResponseMoment G seat left a) :
    ResponseDirection G seat (canonicalOddStrategy G seat r hodd) (p + q) := by
  have heq : left = right :=
    canonicalOddStrategy_subtree_unique G seat r hodd left right
      hp.toStrategyNode hq.toStrategyNode
  subst right
  refine ⟨p + a, q + a, hp.lift ha, hq.lift ha, ?_⟩
  ext e
  simp only [Finsupp.add_apply]
  calc
    p e + q e = (p e + q e) + (a e + a e) := by
      rw [CharTwo.add_self_eq_zero, add_zero]
    _ = (p e + a e) + (q e + a e) := by abel

/-! ## Exact obstruction at the two minimal-bad predecessors -/

/-- The local square which would be needed to invoke continuation coherence
directly at a minimal-bad predecessor.  Its first edge is the extracted
incoming edge, while the distinct crossed edge is the bad subtree's selected
move.  Both orders are required to reach one full concrete state. -/
def MinimalBadSelectedImmediateSquare
    (G : SimpleGraph V) {seat : Bool}
    {parent state : State V} {incoming : Move V}
    (strategy : OddStrategy G seat state) : Prop :=
  ∃ (cross : Move V) (crossState common : State V),
    cross ≠ incoming ∧ strategy.selectedMove = some cross ∧
      step G parent cross = some crossState ∧
      step G crossState incoming = some common ∧
      step G state cross = some common

omit [Fintype V] in
/-- Neither exact minimal-bad normal case contains the immediate selected
commuting square.

In the charged-CLOSE case the incoming edge and the selected bad edge are
both `CLOSE`, contradicting distinctness.  In the protected-OPEN case the
selected bad edge is `CLOSE`, but the reverse-order CLOSE at the protected
singleton parent is illegal because `ko = true`. -/
theorem no_minimalBad_selectedImmediateSquare
    {G : SimpleGraph V} {seat : Bool}
    {parent state : State V} {incoming : Move V}
    {strategy : OddStrategy G seat state} {f : V} {q : List V}
    (hselected : strategy.selectedMove = some .close)
    (hcase : MinimalBadPredecessorNormalCase
      G parent state f q incoming) :
    ¬MinimalBadSelectedImmediateSquare
      (parent := parent) (incoming := incoming) G strategy := by
  rintro ⟨cross, crossState, common, hne, hcrossSelected,
    hparentCross, _hcrossIncoming, _hstateCross⟩
  have hcross : cross = .close := by
    exact Option.some.inj (hcrossSelected.symm.trans hselected)
  subst cross
  cases hcase with
  | chargedClose => exact hne rfl
  | protectedOpen x hx hqueue hko hscore hU hchildQueue hq =>
      simp [step, hqueue, hko] at hparentCross

omit [Fintype V] in
/-- The synchronization-boundary witness therefore has no immediate local
square to which state-positional continuation coherence could be applied. -/
theorem SeparatorBadSynchronizationBoundary.no_selectedImmediateSquare
    {G : SimpleGraph V} {d : V} {seat : Bool}
    (w : SeparatorBadSynchronizationBoundary G d seat) :
    ¬MinimalBadSelectedImmediateSquare
      (parent := w.parent) (incoming := w.incoming) G w.strategy :=
  no_minimalBad_selectedImmediateSquare w.selected_close w.normalCase

/-- Exact canonical form of the local obstruction: even after replacing an
alleged odd counterstrategy by the positional canonical strategy, its
extracted minimal-bad predecessor supplies no selected immediate commuting
square.  Any usable reconvergence must therefore pass through additional
siblings or a longer drain/repair history. -/
theorem canonicalOddStrategy_exists_minimalBad_without_immediateSquare
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    {seat : Bool} (hodd : OddWins G seat (initial (V := V))) :
    ∃ w : SeparatorBadSynchronizationBoundary G d seat,
      ¬MinimalBadSelectedImmediateSquare
        (parent := w.parent) (incoming := w.incoming) G w.strategy := by
  let root := canonicalOddStrategy G seat (initial (V := V)) hodd
  obtain ⟨w⟩ := root.exists_separatorBadSynchronizationBoundary hd
  exact ⟨w, w.no_selectedImmediateSquare⟩

/-! ## The remaining finite-dimensional span obligation -/

/-- One exact same-state reconvergence in the canonical strategy, retaining
the two root prefixes whose XOR becomes a homogeneous direction. -/
structure CanonicalReconvergence
    (G : SimpleGraph V) (seat : Bool) (r : State V)
    (hodd : OddWins G seat r) where
  state : State V
  left : OddStrategy G seat state
  right : OddStrategy G seat state
  leftPrefix : EdgeVector V
  rightPrefix : EdgeVector V
  leftOccurs : StrategyPrefix G seat
    (canonicalOddStrategy G seat r hodd) left leftPrefix
  rightOccurs : StrategyPrefix G seat
    (canonicalOddStrategy G seat r hodd) right rightPrefix

/-- Prefix XOR contributed by one exact canonical reconvergence. -/
def CanonicalReconvergence.direction
    {G : SimpleGraph V} {seat : Bool} {r : State V}
    {hodd : OddWins G seat r}
    (join : CanonicalReconvergence G seat r hodd) : EdgeVector V :=
  join.leftPrefix + join.rightPrefix

omit [Fintype V] in
/-- Every exact reconvergence contributes its prefix XOR to the root response
direction space. -/
theorem CanonicalReconvergence.responseDirection
    {G : SimpleGraph V} {seat : Bool} {r : State V}
    {hodd : OddWins G seat r}
    (join : CanonicalReconvergence G seat r hodd) :
    ResponseDirection G seat (canonicalOddStrategy G seat r hodd)
      join.direction := by
  obtain ⟨a, ha⟩ := exists_affineResponseMoment join.left
  exact canonicalOddStrategy_reconvergent_prefix_direction
    G seat r hodd join.leftOccurs join.rightOccurs ha

omit [Fintype V] in
private theorem ResponseDirection.add'
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {strategy : OddStrategy G seat s} {x y : EdgeVector V}
    (hx : ResponseDirection G seat strategy x)
    (hy : ResponseDirection G seat strategy y) :
    ResponseDirection G seat strategy (x + y) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  refine ⟨a + y, b, ha.add_direction hy, hb, ?_⟩
  abel

omit [Fintype V] in
/-- A finite span of exact reconvergence prefix XORs is still a homogeneous
root response direction. -/
theorem canonicalReconvergence_list_sum_responseDirection
    {G : SimpleGraph V} {seat : Bool} {r : State V}
    {hodd : OddWins G seat r}
    (joins : List (CanonicalReconvergence G seat r hodd)) :
    ResponseDirection G seat (canonicalOddStrategy G seat r hodd)
      (joins.map CanonicalReconvergence.direction).sum := by
  induction joins with
  | nil =>
      change ResponseDirection G seat
        (canonicalOddStrategy G seat r hodd) (0 : EdgeVector V)
      exact ResponseDirection.zero (canonicalOddStrategy G seat r hodd)
  | cons join rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact join.responseDirection.add' ih

/-- Exact remaining linear obstruction at an isolated-dummy initial root.
No finite span of already-occurring exact reconvergences can cancel a
prefix-decorated affine continuation point in the real-edge quotient.  Thus
a factor proof must construct an operational incidence equation asserting
such cancellation; positionality supplies every homogeneous summand once
the requisite longer histories are shown to occur, but supplies no such
history or equation by itself. -/
theorem canonicalReconvergence_span_ne_decorated_residual
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    {seat : Bool} (hodd : OddWins G seat (initial (V := V)))
    {s : State V} {tree : OddStrategy G seat s} {p a : EdgeVector V}
    (hp : StrategyPrefix G seat
      (canonicalOddStrategy G seat (initial (V := V)) hodd) tree p)
    (ha : AffineResponseMoment G seat tree a)
    (joins : List (CanonicalReconvergence G seat
      (initial (V := V)) hodd)) :
    realEdgeProjection d
      ((p + a) + (joins.map CanonicalReconvergence.direction).sum) ≠ 0 := by
  have hpoint : AffineResponseMoment G seat
      (canonicalOddStrategy G seat (initial (V := V)) hodd) (p + a) :=
    hp.lift ha
  have hdirection := canonicalReconvergence_list_sum_responseDirection joins
  intro hzero
  exact no_zero_projectedAffineResponseMoment_initial hd
    ⟨_, hpoint.add_direction hdirection, hzero⟩

/-- Combined minimal-bad/positional-span boundary.  The canonical strategy's
exact extractor produces one of the charged-CLOSE or protected-OPEN normal
cases.  At that same occurrence the immediate selected square is absent, and
no finite family of other already-occurring exact joins can cancel its
decorated continuation residual in the real-edge quotient.

This is the sharp common endpoint of both branches: a successful extension
must prove that additional repaired or drained histories actually occur and
that their prefix XORs satisfy the required incidence equation. -/
theorem canonicalOddStrategy_minimalBad_reconvergenceSpan_obstruction
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    {seat : Bool} (hodd : OddWins G seat (initial (V := V))) :
    ∃ (s : State V) (tree : OddStrategy G seat s) (p : EdgeVector V)
      (parent : State V) (incoming : Move V) (f : V) (q : List V),
      StrategyPrefix G seat
          (canonicalOddStrategy G seat (initial (V := V)) hodd) tree p ∧
      MinimalBadPredecessorNormalCase G parent s f q incoming ∧
      tree.selectedMove = some .close ∧
      ¬MinimalBadSelectedImmediateSquare
        (parent := parent) (incoming := incoming) G tree ∧
      ∀ (a : EdgeVector V), AffineResponseMoment G seat tree a →
        ∀ joins : List (CanonicalReconvergence G seat
          (initial (V := V)) hodd),
          realEdgeProjection d
            ((p + a) +
              (joins.map CanonicalReconvergence.direction).sum) ≠ 0 := by
  let root := canonicalOddStrategy G seat (initial (V := V)) hodd
  obtain ⟨s, tree, p, parent, _parentTree, _pp, incoming, f, q,
      _closeChild, hp, _hpp, _hparentTurn, _hincoming, _hmoment,
      _hfan, _hscore, _hturn, _hqueue, _hko, _hclose, _hcharge,
      _hfreal, hselected, _hneutral, hcase⟩ :=
    root.extract_minimalBad_predecessor_normalCases hd
  refine ⟨s, tree, p, parent, incoming, f, q, hp, hcase, hselected,
    no_minimalBad_selectedImmediateSquare hselected hcase, ?_⟩
  intro a ha joins
  exact canonicalReconvergence_span_ne_decorated_residual
    hd hodd hp ha joins

end

end Ogdoad.Fifo
