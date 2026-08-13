import Ogdoad.FifoStrategyBadAncestryClear
import Ogdoad.FifoProtectedFan

/-!
# The protected-singleton factor boundary

The surviving protected predecessor is a defender state with queue `[f]`,
active ko, score zero, and an even untouched carrier.  Rank minimality forces
every legal `OPEN z` sibling to select the charged `CLOSE f`.  Consequently
the undeleted front has zero charge and is adjacent to the whole untouched
carrier.

The complete protected OPEN fan has even cardinality.  In one exact strategy
tree its lifted response points therefore sum to a response *direction*, not
an affine point.  Its universal prefix is the front live star, leaving the
exact residue

`front live star + sum of child continuation representatives`.

This file also proves the sharp local obstruction: the front live star is not
itself an affine response point of the protected parent, even after quotienting
by an isolated dummy.  Hence the selected OPEN prefix cannot be cancelled
inside the protected subtree alone.  A successful factor extension must mix
this even-fan direction with genuinely earlier same-root affine data.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A non-root defender node in one exact initial strategy has an immediate
attacker parent.  Hence the incoming edge is the attacker's stored move, and
the exact prefix before that edge is retained. -/
theorem StrategyPrefix.immediate_attacker_parent
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {hroot : OddStrategy G seat (initial (V := V))}
    {strategy : OddStrategy G seat s} {p : EdgeVector V}
    (hprefix : StrategyPrefix G seat hroot strategy p)
    (hturn : s.toMove = seat) (hnotRoot : s ≠ initial) :
    ∃ (parent : State V) (parentTree : OddStrategy G seat parent)
      (pp : EdgeVector V) (m : Move V),
      StrategyPrefix G seat hroot parentTree pp ∧
      parent.toMove = !seat ∧ step G parent m = some s ∧
      parentTree.selectedMove = some m ∧
      p = pp + moveLiveStar parent m := by
  cases hprefix with
  | root => exact False.elim (hnotRoot rfl)
  | @choose parent child hseat m hstep childTree pp parentPrefix =>
      have hparentTurn : parent.toMove = !seat :=
        Bool.eq_not_iff.mpr hseat
      exact ⟨parent, _, pp, m,
        parentPrefix, hparentTurn, hstep, rfl, rfl⟩
  | @answer parent child hseat hasMove children m hstep pp parentPrefix =>
      have hchildTurn := step_toMove hstep
      have : s.toMove = !seat := by rw [hchildTurn, hseat]
      exact False.elim ((by simp : (seat : Bool) ≠ !seat) (hturn.symm.trans this))

/-- The protected singleton parent cannot be the initial root, so it always
has the immediate attacker predecessor supplied by
`StrategyPrefix.immediate_attacker_parent`. -/
theorem StrategyPrefix.protected_immediate_attacker_parent
    {G : SimpleGraph V} {seat : Bool} {parent : State V}
    {hroot : OddStrategy G seat (initial (V := V))}
    {parentTree : OddStrategy G seat parent} {p : EdgeVector V}
    (hprefix : StrategyPrefix G seat hroot parentTree p)
    (hturn : parent.toMove = seat) {f : V}
    (hqueue : parent.queue = [f]) :
    ∃ (earlier : State V) (earlierTree : OddStrategy G seat earlier)
      (pe : EdgeVector V) (m : Move V),
      StrategyPrefix G seat hroot earlierTree pe ∧
      earlier.toMove = !seat ∧ step G earlier m = some parent ∧
      earlierTree.selectedMove = some m ∧
      p = pe + moveLiveStar earlier m := by
  apply hprefix.immediate_attacker_parent hturn
  intro hrootEq
  subst parent
  simp [initial] at hqueue

/-- Exact selected edge immediately before a protected singleton parent.  The
parent's active ko bit forces its attacker predecessor to have empty queue and
to select precisely `OPEN f`; coherence then forces that predecessor clear. -/
theorem StrategyPrefix.protected_immediate_attacker_shape
    {G : SimpleGraph V} {seat : Bool} {parent : State V}
    {hroot : OddStrategy G seat (initial (V := V))}
    {parentTree : OddStrategy G seat parent} {p : EdgeVector V}
    (hprefix : StrategyPrefix G seat hroot parentTree p)
    (hturn : parent.toMove = seat) {f : V}
    (hqueue : parent.queue = [f]) (hko : parent.ko = true)
    (hscore : parent.score = 0) :
    ∃ (empty : State V) (emptyTree : OddStrategy G seat empty)
      (pe : EdgeVector V),
      StrategyPrefix G seat hroot emptyTree pe ∧
      empty.toMove = !seat ∧
      step G empty (.open f) = some parent ∧
      emptyTree.selectedMove = some (.open f) ∧
      p = pe + moveLiveStar empty (.open f) ∧
      empty.queue = [] ∧ empty.ko = false ∧
      f ∈ empty.untouched ∧
      parent.untouched = empty.untouched.erase f ∧
      empty.score = 0 := by
  obtain ⟨empty, emptyTree, pe, m, hemptyPrefix, hemptyTurn,
      hincoming, hselected, hp⟩ :=
    hprefix.protected_immediate_attacker_parent hturn hqueue
  have hemptyCoherent := hemptyPrefix.coherent_of_initial
  cases m with
  | «open» z =>
      have hincomingStep := hincoming
      simp only [step] at hincoming
      split at hincoming
      · rename_i hz
        let openState : State V := {
          untouched := empty.untouched.erase z
          queue := empty.queue ++ [z]
          ko := empty.queue.isEmpty
          toMove := !empty.toMove
          score := empty.score }
        have heq : openState = parent := Option.some.inj hincoming
        have hemptyQueue : empty.queue = [] := by
          have hkoEq : openState.ko = parent.ko :=
            congrArg State.ko heq
          cases hq : empty.queue with
          | nil => rfl
          | cons a q => simp [openState, hq, hko] at hkoEq
        have hzEq : z = f := by
          have hqueueEq : openState.queue = parent.queue :=
            congrArg State.queue heq
          simp [openState, hemptyQueue, hqueue] at hqueueEq
          exact hqueueEq
        subst z
        have hemptyKo : empty.ko = false := by
          cases hk : empty.ko with
          | false => rfl
          | true =>
              obtain ⟨y, hy⟩ := hemptyCoherent.2 hk
              rw [hemptyQueue] at hy
              cases hy
        have hU : parent.untouched = empty.untouched.erase f := by
          exact (congrArg State.untouched heq).symm
        have hemptyScore : empty.score = 0 := by
          calc
            empty.score = openState.score := rfl
            _ = parent.score := congrArg State.score heq
            _ = 0 := hscore
        exact ⟨empty, emptyTree, pe, hemptyPrefix, hemptyTurn,
          hincomingStep, hselected, hp, hemptyQueue, hemptyKo, hz, hU,
          hemptyScore⟩
      · contradiction
  | close =>
      simp only [step] at hincoming
      split at hincoming
      · contradiction
      · split at hincoming
        · contradiction
        · have hkoEq := congrArg State.ko (Option.some.inj hincoming)
          simp [hko] at hkoEq
  | pass =>
      simp only [step] at hincoming
      split at hincoming
      · have hkoEq := congrArg State.ko (Option.some.inj hincoming)
        simp [hko] at hkoEq
      · contradiction

/-- If the empty-queue attacker predecessor of a protected wall is not the
initial root, its own immediate defender predecessor necessarily enters by a
front CLOSE.  OPEN cannot create an empty queue, while PASS would require an
empty untouched carrier, contradicting the selected `OPEN f`. -/
theorem StrategyPrefix.empty_attacker_prior_defender_close
    {G : SimpleGraph V} {seat : Bool} {empty : State V}
    {hroot : OddStrategy G seat (initial (V := V))}
    {emptyTree : OddStrategy G seat empty} {pe : EdgeVector V}
    (hprefix : StrategyPrefix G seat hroot emptyTree pe)
    (hturn : empty.toMove = !seat) (hnotRoot : empty ≠ initial)
    {f : V} (hqueue : empty.queue = []) (hf : f ∈ empty.untouched)
    (hscore : empty.score = 0) :
    ∃ (defender : State V) (defenderTree : OddStrategy G seat defender)
      (pd : EdgeVector V) (y : V),
      StrategyPrefix G seat hroot defenderTree pd ∧
      defender.toMove = seat ∧ step G defender .close = some empty ∧
      pe = pd ∧
      (∀ m t, step G defender m = some t →
        ∃ childTree : OddStrategy G seat t,
          StrategyPrefix G seat hroot childTree
            (pd + moveLiveStar defender m)) ∧
      defender.queue = [y] ∧ defender.ko = false ∧
      defender.untouched = empty.untouched ∧
      defender.score + flip G defender.untouched y = 0 := by
  obtain ⟨defender, defenderTree, pd, incoming, hdefenderPrefix,
      hdefenderTurn, hincoming, hp, hfan⟩ :=
    hprefix.immediate_defender_parent hturn hnotRoot
  cases incoming with
  | «open» z =>
      simp only [step] at hincoming
      split at hincoming
      · have hqueueEq := congrArg State.queue (Option.some.inj hincoming)
        simp [hqueue] at hqueueEq
      · contradiction
  | close =>
      have hincomingStep := hincoming
      simp only [step] at hincoming
      split at hincoming
      · contradiction
      · rename_i y tail hdefenderQueue
        split at hincoming
        · contradiction
        · rename_i hdefenderKoRaw
          let closeState : State V := {
            untouched := defender.untouched
            queue := tail
            ko := false
            toMove := !defender.toMove
            score := defender.score + flip G defender.untouched y }
          have heq : closeState = empty := Option.some.inj hincoming
          have htail : tail = [] := by
            calc
              tail = closeState.queue := rfl
              _ = empty.queue := congrArg State.queue heq
              _ = [] := hqueue
          have hdefenderQueue' : defender.queue = [y] := by
            rw [hdefenderQueue, htail]
          have hdefenderKo : defender.ko = false := by
            cases hk : defender.ko with
            | false => rfl
            | true => simp [hk] at hdefenderKoRaw
          have hU : defender.untouched = empty.untouched := by
            calc
              defender.untouched = closeState.untouched := rfl
              _ = empty.untouched := congrArg State.untouched heq
          have hscoreEq : defender.score + flip G defender.untouched y = 0 := by
            calc
              defender.score + flip G defender.untouched y =
                  closeState.score := rfl
              _ = empty.score := congrArg State.score heq
              _ = 0 := hscore
          simp [moveLiveStar] at hp
          exact ⟨defender, defenderTree, pd, y, hdefenderPrefix,
            hdefenderTurn, hincomingStep, hp, hfan, hdefenderQueue',
            hdefenderKo, hU, hscoreEq⟩
  | pass =>
      simp only [step] at hincoming
      split at hincoming
      · rename_i hpass
        have hUeq := congrArg State.untouched (Option.some.inj hincoming)
        have : empty.untouched = ∅ := by
          simpa using hUeq.symm.trans hpass.1
        rw [this] at hf
        simp at hf
      · contradiction

/-- Sharp ancestry-depth classification for a protected singleton parent.

Its immediate predecessor is always the selected empty-queue `OPEN f`.  That
predecessor is either the initial root itself (so no earlier defender sibling
exists), or it came from a universal defender by `CLOSE y`.  In the latter
case the defender's untouched carrier is exactly `insert f` of the protected
carrier and its complete same-root fan is retained. -/
theorem StrategyPrefix.protected_prior_defender_or_initial
    {G : SimpleGraph V} {seat : Bool} {parent : State V}
    {hroot : OddStrategy G seat (initial (V := V))}
    {parentTree : OddStrategy G seat parent} {p : EdgeVector V}
    (hprefix : StrategyPrefix G seat hroot parentTree p)
    (hturn : parent.toMove = seat) {f : V}
    (hqueue : parent.queue = [f]) (hko : parent.ko = true)
    (hscore : parent.score = 0) :
    ∃ (empty : State V) (emptyTree : OddStrategy G seat empty)
      (pe : EdgeVector V),
      StrategyPrefix G seat hroot emptyTree pe ∧
      empty.toMove = !seat ∧
      step G empty (.open f) = some parent ∧
      emptyTree.selectedMove = some (.open f) ∧
      p = pe + moveLiveStar empty (.open f) ∧
      empty.queue = [] ∧ empty.ko = false ∧
      f ∈ empty.untouched ∧
      parent.untouched = empty.untouched.erase f ∧
      empty.score = 0 ∧
      (empty = initial ∨
        ∃ (defender : State V)
          (defenderTree : OddStrategy G seat defender)
          (pd : EdgeVector V) (y : V),
          StrategyPrefix G seat hroot defenderTree pd ∧
          defender.toMove = seat ∧
          step G defender .close = some empty ∧
          pe = pd ∧
          (∀ m t, step G defender m = some t →
            ∃ childTree : OddStrategy G seat t,
              StrategyPrefix G seat hroot childTree
                (pd + moveLiveStar defender m)) ∧
          defender.queue = [y] ∧ defender.ko = false ∧
          defender.untouched = insert f parent.untouched ∧
          defender.score + flip G defender.untouched y = 0) := by
  obtain ⟨empty, emptyTree, pe, hemptyPrefix, hemptyTurn, hopen,
      hselected, hp, hemptyQueue, hemptyKo, hf, hparentU,
      hemptyScore⟩ :=
    hprefix.protected_immediate_attacker_shape hturn hqueue hko hscore
  refine ⟨empty, emptyTree, pe, hemptyPrefix, hemptyTurn, hopen,
    hselected, hp, hemptyQueue, hemptyKo, hf, hparentU,
    hemptyScore, ?_⟩
  by_cases hrootEq : empty = initial
  · exact Or.inl hrootEq
  · obtain ⟨defender, defenderTree, pd, y, hdefenderPrefix,
        hdefenderTurn, hclose, hpe, hfan, hdefenderQueue,
        hdefenderKo, hdefenderU, hscoreEq⟩ :=
      hemptyPrefix.empty_attacker_prior_defender_close
        hemptyTurn hrootEq hemptyQueue hf hemptyScore
    have hcarrier : defender.untouched = insert f parent.untouched := by
      calc
        defender.untouched = empty.untouched := hdefenderU
        _ = insert f (empty.untouched.erase f) :=
          (Finset.insert_erase hf).symm
        _ = insert f parent.untouched := by rw [hparentU]
    exact Or.inr ⟨defender, defenderTree, pd, y, hdefenderPrefix,
      hdefenderTurn, hclose, hpe, hfan, hdefenderQueue,
      hdefenderKo, hcarrier, hscoreEq⟩

omit [Fintype V] in
/-- Exact one-level-earlier shape of a protected singleton parent.  If its
immediate attacker predecessor entered by `CLOSE y`, then the predecessor
had queue `[y,f]`, was clear, had the same untouched carrier, and the charge
of `y` equals the protected parent's score change.  In particular, a
score-zero protected parent can only have an uncharged incoming CLOSE from a
score-zero predecessor or a charged incoming CLOSE from a score-one
predecessor. -/
theorem protected_parent_of_incoming_close
    {G : SimpleGraph V} {earlier parent : State V} {f : V}
    (hparentQueue : parent.queue = [f])
    (hparentScore : parent.score = 0)
    (hincoming : step G earlier .close = some parent) :
    ∃ y,
      earlier.queue = [y, f] ∧ earlier.ko = false ∧
      earlier.untouched = parent.untouched ∧
      earlier.score + flip G earlier.untouched y = 0 ∧
      ((earlier.score = 0 ∧ flip G earlier.untouched y = 0) ∨
        (earlier.score = 1 ∧ flip G earlier.untouched y = 1)) := by
  simp only [step] at hincoming
  split at hincoming
  · contradiction
  · rename_i y tail hqueue
    split at hincoming
    · contradiction
    · rename_i hko
      let closeState : State V := {
        untouched := earlier.untouched
        queue := tail
        ko := false
        toMove := !earlier.toMove
        score := earlier.score + flip G earlier.untouched y }
      have heq : closeState = parent := Option.some.inj hincoming
      have htail : tail = [f] := by
        calc
          tail = closeState.queue := rfl
          _ = parent.queue := congrArg State.queue heq
          _ = [f] := hparentQueue
      have hqueue' : earlier.queue = [y, f] := by
        rw [hqueue, htail]
      have hko' : earlier.ko = false := by
        cases hk : earlier.ko with
        | false => rfl
        | true => simp [hk] at hko
      have hU : earlier.untouched = parent.untouched := by
        calc
          earlier.untouched = closeState.untouched := rfl
          _ = parent.untouched := congrArg State.untouched heq
      have hscore : earlier.score + flip G earlier.untouched y = 0 := by
        calc
          earlier.score + flip G earlier.untouched y = closeState.score := rfl
          _ = parent.score := congrArg State.score heq
          _ = 0 := hparentScore
      have hsame : earlier.score = flip G earlier.untouched y := by
        have := congrArg (fun z : ZMod 2 ↦
          z + flip G earlier.untouched y) hscore
        simpa [add_assoc, CharTwo.add_self_eq_zero] using this
      by_cases hs0 : earlier.score = 0
      · exact ⟨y, hqueue', hko', hU, hscore, Or.inl ⟨hs0, hsame ▸ hs0⟩⟩
      · have hs1 := zmod2_eq_one_of_ne_zero _ hs0
        exact ⟨y, hqueue', hko', hU, hscore,
          Or.inr ⟨hs1, hsame ▸ hs1⟩⟩

omit [Fintype V] in
/-- Minimality does not force the one-level-earlier incoming `CLOSE` to be
charged.  What it forces is the exact dichotomy already visible on score
sheets: neutral `C_y` from score zero, or charged `C_y` from score one.  The
neutral alternative is fully compatible with primary rank minimality because
the protected parent has the same score and strictly smaller rank. -/
theorem protected_incoming_close_score_dichotomy
    {G : SimpleGraph V} {seat : Bool}
    {rootState earlier parent : State V}
    {root : OddStrategy G seat rootState}
    {earlierTree : OddStrategy G seat earlier}
    {parentTree : OddStrategy G seat parent} {f : V}
    (hearlier : StrategyNode G seat root earlierTree)
    (hincomingNode : StrategyNode G seat earlierTree parentTree)
    (hparentQueue : parent.queue = [f])
    (hparentScore : parent.score = 0)
    (hincoming : step G earlier .close = some parent)
    (_hminimal : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat root desc →
      rank t < rank parent → t.score ≠ 0) :
    ∃ y,
      earlier.queue = [y, f] ∧ earlier.ko = false ∧
      earlier.untouched = parent.untouched ∧
      ((earlier.score = 0 ∧ flip G earlier.untouched y = 0) ∨
        (earlier.score = 1 ∧ flip G earlier.untouched y = 1)) := by
  obtain ⟨y, hqueue, hko, hU, hscore, hcases⟩ :=
    protected_parent_of_incoming_close hparentQueue hparentScore hincoming
  -- `_hminimal` cannot be applied to `parent`: it only excludes zero nodes
  -- of rank strictly below `parent`, whereas this is the comparison node.
  have _hparentGlobal : StrategyNode G seat root parentTree :=
    hearlier.trans hincomingNode
  exact ⟨y, hqueue, hko, hU, hcases⟩

omit [Fintype V] in
/-- In the exact causal shape proposed for the protected wall, the selected
`OPEN f` from an empty-queue attacker predecessor forces that predecessor's
score to remain zero.  Thus if that predecessor itself arrived by `CLOSE y`,
the incoming close is necessarily neutral, not charged. -/
theorem protected_selectedOpen_after_close_is_neutral
    {G : SimpleGraph V} {defender earlier parent : State V} {f : V}
    (hdefenderScore : defender.score = 0)
    (hclose : step G defender .close = some earlier)
    (hopen : step G earlier (.open f) = some parent)
    (hparentScore : parent.score = 0) :
    earlier.score = 0 ∧
      ∃ y q, defender.queue = y :: q ∧
        flip G defender.untouched y = 0 := by
  have hearlierScore : earlier.score = 0 := by
    have hopenScore := open_score hopen
    exact hopenScore.symm.trans hparentScore
  obtain ⟨y, q, hqueue, hscore⟩ := close_score hclose
  have hy : flip G defender.untouched y = 0 := by
    rw [hdefenderScore, zero_add] at hscore
    exact hscore.symm.trans hearlierScore
  exact ⟨hearlierScore, y, q, hqueue, hy⟩

omit [Fintype V] in
/-- The stars centred at every vertex other than `f` sum to the star centred
at `f`.  This is the exact prefix left by a complete even protected OPEN fan. -/
theorem sum_liveStarVector_insert_complement_eq_front
    (U : Finset V) (f : V) (hfU : f ∉ U) :
    (∑ z ∈ U, liveStarVector (insert f U) z) =
      liveStarVector (insert f U) f := by
  have htotal := sum_liveStarVector_eq_zero (insert f U)
  rw [Finset.sum_insert hfU] at htotal
  have hself :
      liveStarVector (insert f U) f +
          liveStarVector (insert f U) f = 0 := by
    ext e
    exact CharTwo.add_self_eq_zero _
  calc
    (∑ z ∈ U, liveStarVector (insert f U) z) =
        0 + ∑ z ∈ U, liveStarVector (insert f U) z := by
          rw [zero_add]
    _ = (liveStarVector (insert f U) f +
            liveStarVector (insert f U) f) +
          ∑ z ∈ U, liveStarVector (insert f U) z := by rw [hself]
    _ = liveStarVector (insert f U) f +
          (liveStarVector (insert f U) f +
            ∑ z ∈ U, liveStarVector (insert f U) z) := by abel
    _ = liveStarVector (insert f U) f := by rw [htotal, add_zero]

omit [Fintype V] in
/-- The carrier one level before a protected OPEN is odd: it restores the
selected vertex `f` to the even protected untouched carrier. -/
theorem insert_card_mod_two_eq_one_of_even
    (U : Finset V) (f : V) (hfU : f ∉ U)
    (heven : U.card % 2 = 0) :
    (insert f U).card % 2 = 1 := by
  rw [Finset.card_insert_of_notMem hfU]
  omega

omit [Fintype V] in
/-- `ZMod 2` parity form exported by the protected ancestry classifier. -/
theorem insert_card_mod_two_eq_one_of_zmod_even
    (U : Finset V) (f : V) (hfU : f ∉ U)
    (heven : (U.card : ZMod 2) = 0) :
    (insert f U).card % 2 = 1 := by
  have hEven : Even U.card :=
    ZMod.natCast_eq_zero_iff_even.mp heven
  obtain ⟨k, hk⟩ := hEven
  rw [Finset.card_insert_of_notMem hfU, hk]
  omega

omit [Fintype V] in
/-- Convert a nodup list sum to the corresponding finite-set sum. -/
theorem list_sum_map_eq_finset_sum_of_nodup
    (is : List V) (his : is.Nodup) (a : V → EdgeVector V) :
    (is.map a).sum = ∑ z ∈ is.toFinset, a z := by
  induction is with
  | nil => simp
  | cons z rest ih =>
      have hz : z ∉ rest := (List.nodup_cons.mp his).1
      have hrest : rest.Nodup := (List.nodup_cons.mp his).2
      simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
      rw [Finset.sum_insert (by simpa using hz), ih hrest]

omit [Fintype V] [DecidableEq V] in
/-- Pointwise distributivity of list sums in the universal edge space. -/
theorem list_sum_map_add_edgeVector {I : Type*} (is : List I)
    (a b : I → EdgeVector V) :
    (is.map fun i ↦ a i + b i).sum =
      (is.map a).sum + (is.map b).sum := by
  induction is with
  | nil => simp
  | cons i rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      abel

omit [Fintype V] in
/-- The first earlier defender fan which can change affine augmentation.

At a clear defender state with queued front `y`, suppose the legal OPEN
siblings enumerate an odd untouched carrier `W`, with the front outside it
and `liveSet = insert y W`.  Odd convolution of arbitrary child continuation
representatives gives an actual affine response point.  The complete OPEN
prefix sum is exactly the front star at `y`; this is the precise affine source
that is unavailable inside the even protected fan one level later. -/
theorem AffineResponseMoment.oneEarlier_complete_open_fan_point
    {G : SimpleGraph V} {seat : Bool} {defender : State V}
    {hseat : defender.toMove = seat}
    {hasMove : ∃ m t, step G defender m = some t}
    {children : ∀ m t, step G defender m = some t →
      OddStrategy G seat t}
    (W : Finset V) (y : V) (hyW : y ∉ W)
    (is : List V) (his : is.Nodup) (hset : is.toFinset = W)
    (t : V → State V)
    (hstep : ∀ z ∈ is, step G defender (.open z) = some (t z))
    (a : V → EdgeVector V)
    (ha : ∀ z (hz : z ∈ is),
      AffineResponseMoment G seat
        (children (.open z) (t z) (hstep z hz)) (a z))
    (hodd : W.card % 2 = 1)
    (hlive : liveSet defender = insert y W) :
    AffineResponseMoment G seat
      (OddStrategy.answer defender hseat hasMove children)
      (liveStarVector (insert y W) y + (is.map a).sum) := by
  let points := is.map fun z ↦ moveLiveStar defender (.open z) + a z
  have hpoints : ∀ w ∈ points,
      AffineResponseMoment G seat
        (OddStrategy.answer defender hseat hasMove children) w := by
    intro w hw
    simp only [points, List.mem_map] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact AffineResponseMoment.answerChild
      (hstep := hstep z hz) (ha z hz)
  have hlen : is.length = W.card := by
    rw [← List.toFinset_card_of_nodup his, hset]
  have hpointsOdd : points.length % 2 = 1 := by
    simpa [points, hlen] using hodd
  have hpoint : AffineResponseMoment G seat
      (OddStrategy.answer defender hseat hasMove children) points.sum := by
    exact AffineResponseMoment.odd_list_sum points hpointsOdd hpoints
  have hdecomp : points.sum =
      (is.map fun z ↦ moveLiveStar defender (.open z)).sum +
        (is.map a).sum := by
    exact list_sum_map_add_edgeVector is
      (fun z ↦ moveLiveStar defender (.open z)) a
  have hprefix :
      (is.map fun z ↦ moveLiveStar defender (.open z)).sum =
        liveStarVector (insert y W) y := by
    simp only [moveLiveStar, hlive]
    rw [list_sum_map_eq_finset_sum_of_nodup is his, hset]
    exact sum_liveStarVector_insert_complement_eq_front W y hyW
  rw [hdecomp, hprefix] at hpoint
  exact hpoint

omit [Fintype V] in
/-- The one-level-earlier odd OPEN-fan point lifts with its exact ancestry to
the original strategy root. -/
theorem StrategyPrefix.oneEarlier_complete_open_fan_point
    {G : SimpleGraph V} {seat : Bool} {root defender : State V}
    {hroot : OddStrategy G seat root}
    {hseat : defender.toMove = seat}
    {hasMove : ∃ m t, step G defender m = some t}
    {children : ∀ m t, step G defender m = some t →
      OddStrategy G seat t}
    {p : EdgeVector V}
    (hp : StrategyPrefix G seat hroot
      (OddStrategy.answer defender hseat hasMove children) p)
    (W : Finset V) (y : V) (hyW : y ∉ W)
    (is : List V) (his : is.Nodup) (hset : is.toFinset = W)
    (t : V → State V)
    (hstep : ∀ z ∈ is, step G defender (.open z) = some (t z))
    (a : V → EdgeVector V)
    (ha : ∀ z (hz : z ∈ is),
      AffineResponseMoment G seat
        (children (.open z) (t z) (hstep z hz)) (a z))
    (hodd : W.card % 2 = 1)
    (hlive : liveSet defender = insert y W) :
    AffineResponseMoment G seat hroot
      (p + (liveStarVector (insert y W) y + (is.map a).sum)) := by
  apply hp.lift
  exact AffineResponseMoment.oneEarlier_complete_open_fan_point
    W y hyW is his hset t hstep a ha hodd hlive

/-- Sharp one-level semantic boundary.  The earlier odd OPEN fan supplies an
affine root point, while the protected even fan supplies only a root response
direction.  Adding the latter to the former remains an affine point and hence
cannot vanish after isolated-dummy projection.  Thus these two complete fans,
without a further affine source or cross-coset incidence identity, do not yet
form a factor certificate. -/
theorem AffineResponseMoment.initial_add_direction_projection_ne_zero
    {G : SimpleGraph V} {d : V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    {a direction : EdgeVector V}
    (hd : IsDummy G d)
    (ha : AffineResponseMoment G seat root a)
    (hdirection : ResponseDirection G seat root direction) :
    realEdgeProjection d (a + direction) ≠ 0 := by
  intro hzero
  exact no_zero_projectedAffineResponseMoment_initial hd
    ⟨a + direction, ha.add_direction hdirection, hzero⟩

omit [Fintype V] in
/-- Exact same-tree direction supplied by the complete protected OPEN fan.

The family is even, so it cannot itself be convolved to an affine response
point.  Its sum is nevertheless a continuation direction, with the displayed
front-star residue. -/
theorem AffineResponseMoment.protected_complete_open_fan_direction
    {G : SimpleGraph V} {seat : Bool} {parent : State V}
    {hseat : parent.toMove = seat}
    {hasMove : ∃ m t, step G parent m = some t}
    {children : ∀ m t, step G parent m = some t →
      OddStrategy G seat t}
    (U : Finset V) (f : V) (hfU : f ∉ U)
    (is : List V) (his : is.Nodup) (hset : is.toFinset = U)
    (t : V → State V)
    (hstep : ∀ z ∈ is, step G parent (.open z) = some (t z))
    (a : V → EdgeVector V)
    (ha : ∀ z (hz : z ∈ is),
      AffineResponseMoment G seat
        (children (.open z) (t z) (hstep z hz)) (a z))
    (heven : U.card % 2 = 0)
    (hlive : liveSet parent = insert f U) :
    ResponseDirection G seat
      (OddStrategy.answer parent hseat hasMove children)
      (liveStarVector (insert f U) f + (is.map a).sum) := by
  let points := is.map fun z ↦ moveLiveStar parent (.open z) + a z
  have hpoints : ∀ w ∈ points,
      AffineResponseMoment G seat
        (OddStrategy.answer parent hseat hasMove children) w := by
    intro w hw
    simp only [points, List.mem_map] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact AffineResponseMoment.answerChild
      (hstep := hstep z hz) (ha z hz)
  have hlen : is.length = U.card := by
    rw [← List.toFinset_card_of_nodup his, hset]
  have hpointsEven : points.length % 2 = 0 := by
    simpa [points, hlen] using heven
  have hdirection : ResponseDirection G seat
      (OddStrategy.answer parent hseat hasMove children) points.sum :=
    AffineResponseMoment.even_list_sum_direction
      points hpointsEven hpoints
  have hdecomp : points.sum =
      (is.map fun z ↦ moveLiveStar parent (.open z)).sum +
        (is.map a).sum := by
    exact list_sum_map_add_edgeVector is
      (fun z ↦ moveLiveStar parent (.open z)) a
  have hprefix :
      (is.map fun z ↦ moveLiveStar parent (.open z)).sum =
        liveStarVector (insert f U) f := by
    simp only [moveLiveStar, hlive]
    rw [list_sum_map_eq_finset_sum_of_nodup is his, hset]
    exact sum_liveStarVector_insert_complement_eq_front U f hfU
  rw [hdecomp, hprefix] at hdirection
  exact hdirection

omit [Fintype V] in
/-- The complete protected-fan direction remains available at the original
strategy root; the common ancestry prefix cancels in a direction. -/
theorem StrategyPrefix.protected_complete_open_fan_direction
    {G : SimpleGraph V} {seat : Bool} {root parent : State V}
    {hroot : OddStrategy G seat root}
    {hseat : parent.toMove = seat}
    {hasMove : ∃ m t, step G parent m = some t}
    {children : ∀ m t, step G parent m = some t →
      OddStrategy G seat t}
    {p : EdgeVector V}
    (hp : StrategyPrefix G seat hroot
      (OddStrategy.answer parent hseat hasMove children) p)
    (U : Finset V) (f : V) (hfU : f ∉ U)
    (is : List V) (his : is.Nodup) (hset : is.toFinset = U)
    (t : V → State V)
    (hstep : ∀ z ∈ is, step G parent (.open z) = some (t z))
    (a : V → EdgeVector V)
    (ha : ∀ z (hz : z ∈ is),
      AffineResponseMoment G seat
        (children (.open z) (t z) (hstep z hz)) (a z))
    (heven : U.card % 2 = 0)
    (hlive : liveSet parent = insert f U) :
    ResponseDirection G seat hroot
      (liveStarVector (insert f U) f + (is.map a).sum) := by
  apply hp.lift_direction
  exact AffineResponseMoment.protected_complete_open_fan_direction
    U f hfU is his hset t hstep a ha heven hlive

/-- Rank minimality at one protected child forces every sibling obtained by
`OPEN z` to have charged front `f`.  Therefore the protected parent has a
zero-charge universal front and even untouched carrier. -/
theorem protectedOpen_sameRoot_front_data
    {G : SimpleGraph V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    {s parent : State V} {pp : EdgeVector V} {f x : V}
    (hfan : ∀ m t, step G parent m = some t →
      ∃ childTree : OddStrategy G seat t,
        StrategyPrefix G seat root childTree
          (pp + moveLiveStar parent m))
    (hincoming : step G parent (.open x) = some s)
    (hminimal : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat root desc →
      rank t < rank s → t.score ≠ 0)
    (hx : x ∈ parent.untouched)
    (hqueue : parent.queue = [f])
    (hscore : parent.score = 0) :
    flip G parent.untouched f = 0 ∧
      (∀ z ∈ parent.untouched, G.Adj f z) ∧
      (parent.untouched.card : ZMod 2) = 0 := by
  classical
  let sx : State V := {
    untouched := parent.untouched.erase x
    queue := parent.queue ++ [x]
    ko := parent.queue.isEmpty
    toMove := !parent.toMove
    score := parent.score }
  have hsEq : sx = s := by
    have hsx : step G parent (.open x) = some sx := by
      simp [step, sx, hx]
    rw [hincoming] at hsx
    exact Option.some.inj hsx.symm
  have herase : ∀ z ∈ parent.untouched,
      flip G (parent.untouched.erase z) f = 1 := by
    intro z hz
    let sz : State V := {
      untouched := parent.untouched.erase z
      queue := parent.queue ++ [z]
      ko := parent.queue.isEmpty
      toMove := !parent.toMove
      score := parent.score }
    have hzStep : step G parent (.open z) = some sz := by
      simp [step, sz, hz]
    obtain ⟨szTree, hszPrefix⟩ := hfan (.open z) sz hzStep
    have hszNode : StrategyNode G seat root szTree :=
      hszPrefix.toStrategyNode
    have hsz0 : sz.score = 0 := by simp [sz, hscore]
    have hszRank : rank sz = rank s := by
      rw [← hsEq]
      simp [rank, sz, sx, hqueue,
        Finset.card_erase_of_mem hz, Finset.card_erase_of_mem hx]
    have hminimalZ : ∀ {t : State V}
        {desc : OddStrategy G seat t},
        StrategyNode G seat szTree desc →
        rank t < rank sz → t.score ≠ 0 := by
      intro t desc hdesc hlt
      apply hminimal (hszNode.trans hdesc)
      rw [hszRank] at hlt
      exact hlt
    obtain ⟨_, fz, qz, scz, hqueueZ, _, _, hflipZ, _⟩ :=
      szTree.minimal_zeroNode_close_neutral hsz0 hminimalZ
    have hqueueCanonical : sz.queue = [f, z] := by
      simp [sz, hqueue]
    have hfz : fz = f := by
      have hcons : fz :: qz = f :: [z] :=
        hqueueZ.symm.trans hqueueCanonical
      exact (List.cons.inj hcons).1
    subst fz
    simpa [sz] using hflipZ
  obtain ⟨hfrontZero, hfrontUniversal⟩ :=
    flip_zero_and_adj_of_all_erase_flip_one ⟨x, hx⟩ herase
  have hcarrierEven : (parent.untouched.card : ZMod 2) = 0 := by
    rw [← flip_eq_card_of_forall_adj hfrontUniversal]
    exact hfrontZero
  exact ⟨hfrontZero, hfrontUniversal, hcarrierEven⟩

omit [Fintype V] in
/-- The front live star cannot be an affine response point of a protected
score-zero singleton parent.  Its graph evaluation is zero, whereas every
response point of the exact odd subtree evaluates to one. -/
theorem not_affineResponseMoment_protected_frontStar
    {G : SimpleGraph V} {seat : Bool} {parent : State V}
    (strategy : OddStrategy G seat parent) (hparent : WellFormed parent)
    {f : V} (hscore : parent.score = 0)
    (hqueue : parent.queue = [f])
    (hfrontZero : flip G parent.untouched f = 0) :
    ¬AffineResponseMoment G seat strategy
      (liveStarVector (liveSet parent) f) := by
  intro hmoment
  have heval := hmoment.graphEvaluation_eq hparent
  have hpot : potential G parent = 0 := by
    simp [potential, queueCut, hscore, hqueue, hfrontZero]
  have hstar :
      graphEvaluation G (liveStarVector (liveSet parent) f) = 0 := by
    rw [graphEvaluation_liveStar_eq_liveDegree G parent f hparent]
    simp [liveDegree, queueCut, hqueue, hfrontZero,
      flip_singleton_eq_adjacencyBit]
  rw [hstar, hpot] at heval
  exact zero_ne_one heval

omit [Fintype V] in
/-- The same obstruction survives the isolated-dummy quotient.  Therefore a
protected subtree cannot cancel the selected preceding `OPEN f` prefix even
after all dummy-incident coordinates are forgotten. -/
theorem not_projectedAffineResponseMoment_protected_frontStar
    {G : SimpleGraph V} {d : V} {seat : Bool} {parent : State V}
    (hd : IsDummy G d) (strategy : OddStrategy G seat parent)
    (hparent : WellFormed parent)
    {f : V} (hscore : parent.score = 0)
    (hqueue : parent.queue = [f])
    (hfrontZero : flip G parent.untouched f = 0) :
    ¬ProjectedAffineResponseMoment d G seat strategy
      (realEdgeProjection d (liveStarVector (liveSet parent) f)) := by
  rintro ⟨z, hz, hprojection⟩
  have hzEval := hz.graphEvaluation_eq hparent
  have hpot : potential G parent = 0 := by
    simp [potential, queueCut, hscore, hqueue, hfrontZero]
  have hstarEval :
      graphEvaluation G (liveStarVector (liveSet parent) f) = 0 := by
    rw [graphEvaluation_liveStar_eq_liveDegree G parent f hparent]
    simp [liveDegree, queueCut, hqueue, hfrontZero,
      flip_singleton_eq_adjacencyBit]
  have hprojectionZero :
      realEdgeProjection d
        (z + liveStarVector (liveSet parent) f) = 0 := by
    rw [map_add, hprojection, ← map_add]
    have hself :
        liveStarVector (liveSet parent) f +
            liveStarVector (liveSet parent) f = 0 := by
      ext e
      exact CharTwo.add_self_eq_zero _
    rw [hself, map_zero]
  have hdiffEval :=
    graphEvaluation_eq_zero_of_realEdgeProjection_eq_zero hd hprojectionZero
  rw [map_add, hzEval, hpot, hstarEval, add_zero] at hdiffEval
  exact one_ne_zero hdiffEval

omit [Fintype V] in
/-- Causal form of the projected obstruction.  No continuation point from
the protected parent can cancel the preceding selected `OPEN f` prefix by
itself. -/
theorem no_protected_local_selectedOpen_cancellation
    {G : SimpleGraph V} {d : V} {seat : Bool} {parent : State V}
    (hd : IsDummy G d) (strategy : OddStrategy G seat parent)
    (hparent : WellFormed parent)
    {f : V} (hscore : parent.score = 0)
    (hqueue : parent.queue = [f])
    (hfrontZero : flip G parent.untouched f = 0) :
    ¬∃ a, AffineResponseMoment G seat strategy a ∧
      realEdgeProjection d
        (liveStarVector (liveSet parent) f + a) = 0 := by
  rintro ⟨a, ha, hcancel⟩
  have haEval := ha.graphEvaluation_eq hparent
  have hpot : potential G parent = 0 := by
    simp [potential, queueCut, hscore, hqueue, hfrontZero]
  have hstarEval :
      graphEvaluation G (liveStarVector (liveSet parent) f) = 0 := by
    rw [graphEvaluation_liveStar_eq_liveDegree G parent f hparent]
    simp [liveDegree, queueCut, hqueue, hfrontZero,
      flip_singleton_eq_adjacencyBit]
  have hcancelEval :=
    graphEvaluation_eq_zero_of_realEdgeProjection_eq_zero hd hcancel
  rw [map_add, hstarEval, zero_add, haEval, hpot, add_zero] at hcancelEval
  exact one_ne_zero hcancelEval

end

end Ogdoad.Fifo
