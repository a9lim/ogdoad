import Ogdoad.FifoPairState

/-!
# Strategy-relative minimal bad ancestry

The global minimum-hot reduction may choose a state unrelated to a supplied
counterstrategy.  This file instead minimizes the residual target directly
inside one exact `OddStrategy` tree.  At its deepest score-zero node the
stored move is a unit CLOSE and the translated selected continuation is
neutral.  The node also has an exact live-star prefix from the original root.

At an initial root this node has an immediate defender parent.  Its incoming
move is either a CLOSE or an OPEN; PASS is impossible.  Splitting by the
incoming charge and by the parent's ko bit initially gives four cases:

* a charged CLOSE followed by the selected charged CLOSE;
* a neutral CLOSE followed by the selected charged CLOSE;
* an OPEN from a protected singleton queue;
* an OPEN from a clear nonempty queue.

A secondary minimum on untouched-carrier size excludes the neutral-CLOSE
case: the same defender parent has an OPEN sibling of equal rank and smaller
carrier.  The first two surviving cases are the proposed odd--odd and
protected-singleton ancestries.  Excluding the clear-OPEN case still requires
the missing fixed-front causal transport.  Thus the theorem repairs the
global-minimum-not-descendant defect and proves one of the two predecessor
exclusions without claiming the other.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Extend an existing root prefix through an exact subtree membership. -/
theorem StrategyNode.extend_strategyPrefix
    {G : SimpleGraph V} {seat : Bool} {root s t : State V}
    {hroot : OddStrategy G seat root}
    {middle : OddStrategy G seat s} {desc : OddStrategy G seat t}
    (hnode : StrategyNode G seat middle desc)
    {p : EdgeVector V} (hprefix : StrategyPrefix G seat hroot middle p) :
    ∃ q, StrategyPrefix G seat hroot desc q := by
  induction hnode generalizing p with
  | root => exact ⟨p, hprefix⟩
  | @choose s s' t hseat m hstep child desc hchild ih =>
      exact ih (StrategyPrefix.choose hprefix)
  | @answer s s' t hseat hasMove children m hstep desc hchild ih =>
      exact ih (StrategyPrefix.answer hprefix)

omit [Fintype V] in
/-- Every exact subtree node carries some live-star prefix from its root. -/
theorem StrategyNode.exists_strategyPrefix
    {G : SimpleGraph V} {seat : Bool} {root t : State V}
    {hroot : OddStrategy G seat root} {desc : OddStrategy G seat t}
    (hnode : StrategyNode G seat hroot desc) :
    ∃ p, StrategyPrefix G seat hroot desc p :=
  hnode.extend_strategyPrefix StrategyPrefix.root

omit [Fintype V] in
/-- Forgetting the prefix moment retains exact subtree membership. -/
theorem StrategyPrefix.toStrategyNode
    {G : SimpleGraph V} {seat : Bool} {root s : State V}
    {hroot : OddStrategy G seat root} {desc : OddStrategy G seat s}
    {p : EdgeVector V} (hprefix : StrategyPrefix G seat hroot desc p) :
    StrategyNode G seat hroot desc := by
  induction hprefix with
  | root => exact StrategyNode.root _
  | @choose s s' hseat m hstep child p parent ih =>
      exact ih.trans (StrategyNode.choose (StrategyNode.root child))
  | @answer s s' hseat hasMove children m hstep p parent ih =>
      exact ih.trans (StrategyNode.answer (StrategyNode.root _))

/-- A strategy prefix from the initial root stays in the coherent reachable
state space. -/
theorem StrategyPrefix.coherent_of_initial
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {hroot : OddStrategy G seat (initial (V := V))}
    {desc : OddStrategy G seat s} {p : EdgeVector V}
    (hprefix : StrategyPrefix G seat hroot desc p) : Coherent s := by
  induction hprefix with
  | root => exact coherent_initial
  | @choose s s' hseat m hstep child p parent ih =>
      exact coherent_step ih hstep
  | @answer s s' hseat hasMove children m hstep p parent ih =>
      exact coherent_step ih hstep

omit [Fintype V] in
/-- Constructor-level form of the selected CLOSE at a strategy-relative
minimum score-zero node. -/
theorem OddStrategy.minimal_zeroNode_selectedClose
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (strategy : OddStrategy G seat s) (hs0 : s.score = 0)
    (hminimal : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat strategy desc →
      rank t < rank s → t.score ≠ 0) :
    strategy.selectedMove = some .close := by
  cases strategy with
  | terminal _ _ hscore => exact False.elim (hscore hs0)
  | choose _ hseat m t hstep child =>
      change some m = some (.close : Move V)
      apply congrArg some
      have hmem : StrategyNode G seat
          (OddStrategy.choose s hseat m t hstep child) child :=
        StrategyNode.choose (StrategyNode.root child)
      have ht1 : t.score ≠ 0 := hminimal hmem (rank_step_lt hstep)
      cases m with
      | «open» v =>
          exact False.elim (ht1 ((open_score hstep).trans hs0))
      | close => rfl
      | pass =>
          exact False.elim (ht1 ((pass_score hstep).trans hs0))
  | answer _ hseat hasMove children =>
      have hasMove' := hasMove
      obtain ⟨m, t, hstep⟩ := hasMove'
      have hmem : StrategyNode G seat
          (OddStrategy.answer s hseat hasMove children)
          (children m t hstep) :=
        StrategyNode.answer (StrategyNode.root _)
      have ht0 : t.score = 0 := by
        by_cases hU : s.untouched = ∅
        · exact (step_score_eq_of_untouched_empty hU hstep).trans hs0
        · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hU
          let so : State V := {
            untouched := s.untouched.erase v
            queue := s.queue ++ [v]
            ko := s.queue.isEmpty
            toMove := !s.toMove
            score := s.score }
          have hopen : step G s (.open v) = some so := by
            simp [step, so, hv]
          have hopenMem : StrategyNode G seat
              (OddStrategy.answer s hseat hasMove children)
              (children (.open v) so hopen) :=
            StrategyNode.answer (StrategyNode.root _)
          exact False.elim
            (hminimal hopenMem (rank_step_lt hopen) (by simp [so, hs0]))
      exact False.elim (hminimal hmem (rank_step_lt hstep) ht0)

/-- The three surviving immediate defender ancestries of a lexicographically
minimal bad node.  The first two constructors are the candidate normal forms;
the clear OPEN is the remaining fixed-front exclusion obligation. -/
inductive MinimalBadPredecessorCase (G : SimpleGraph V)
    (parent child : State V) (f : V) (q : List V) : Move V → Prop
  | chargedClose (y : V)
      (hqueue : parent.queue = y :: f :: q)
      (hko : parent.ko = false)
      (hU : parent.untouched = child.untouched)
      (hscore : parent.score = 1)
      (hcharge : flip G parent.untouched y = 1) :
      MinimalBadPredecessorCase G parent child f q .close
  | protectedOpen (x : V)
      (hx : x ∈ parent.untouched)
      (hqueue : parent.queue = [f])
      (hko : parent.ko = true)
      (hscore : parent.score = 0)
      (hU : child.untouched = parent.untouched.erase x)
      (hchildQueue : child.queue = [f, x])
      (hq : q = [x]) :
      MinimalBadPredecessorCase G parent child f q (.open x)
  | clearOpen (x : V)
      (hx : x ∈ parent.untouched)
      (hqueue : parent.queue ≠ [])
      (hko : parent.ko = false)
      (hscore : parent.score = 0)
      (hU : child.untouched = parent.untouched.erase x)
      (hchildQueue : child.queue = parent.queue ++ [x])
      (hfrontQueue : ∃ r, parent.queue = f :: r ∧ q = r ++ [x])
      (hfrontZero : flip G parent.untouched f = 0)
      (hfrontUniversal : ∀ z ∈ parent.untouched, G.Adj f z)
      (hcarrierEven : (parent.untouched.card : ZMod 2) = 0) :
      MinimalBadPredecessorCase G parent child f q (.open x)

omit [Fintype V] in
/-- The clear-OPEN case is necessarily the charged side of the local square.
The neutral adjacency branch is empty: the front dominates the whole parent
carrier, while its undeleted charge is zero. -/
theorem MinimalBadPredecessorCase.clearOpen_data
    {G : SimpleGraph V} {parent child : State V}
    {f x : V} {q : List V}
    (hcase : MinimalBadPredecessorCase G parent child f q (.open x))
    (hko : parent.ko = false) :
    ∃ r, parent.queue = f :: r ∧ q = r ++ [x] ∧
      x ∈ parent.untouched ∧ adjacencyBit G f x = 1 ∧
      flip G parent.untouched f = 0 ∧
      flip G (parent.untouched.erase x) f = 1 ∧
      (∀ z ∈ parent.untouched, G.Adj f z) ∧
      (parent.untouched.card : ZMod 2) = 0 := by
  cases hcase with
  | protectedOpen x hx hqueue hko' hscore hU hchildQueue hq =>
      exact False.elim (by simp [hko] at hko')
  | clearOpen x hx hqueue hko' hscore hU hchildQueue hfrontQueue
      hfrontZero hfrontUniversal hcarrierEven =>
      obtain ⟨r, hqueue', hq'⟩ := hfrontQueue
      have hbit : adjacencyBit G f x = 1 := by
        simp [adjacencyBit, hfrontUniversal x hx]
      have heraseEq := flip_eq_flip_erase_add (G := G) (f := f) hx
      rw [hfrontZero, hbit] at heraseEq
      have herase : flip G (parent.untouched.erase x) f = 1 := by
        have := congrArg (fun z : ZMod 2 ↦ z + 1) heraseEq
        simpa [add_assoc, CharTwo.add_self_eq_zero] using this.symm
      exact ⟨r, hqueue', hq', hx, hbit, hfrontZero, herase,
        hfrontUniversal, hcarrierEven⟩

omit [Fintype V] in
/-- On an isolated-dummy board, the unit defect in the clear-OPEN square is a
genuine real-edge residue.  It cannot disappear in the dummy quotient. -/
theorem MinimalBadPredecessorCase.clearOpen_curvature_projection_ne_zero
    {G : SimpleGraph V} {parent child : State V}
    {d f x : V} {q : List V}
    (hd : IsDummy G d)
    (hcase : MinimalBadPredecessorCase G parent child f q (.open x))
    (hko : parent.ko = false) :
    realEdgeProjection d
        (Finsupp.single s(f, x) 1 : EdgeVector V) ≠ 0 := by
  obtain ⟨_, _, _, _, hbit, _, _, _, _⟩ := hcase.clearOpen_data hko
  exact singletonWall_curvature_projection_ne_zero G d f x hd hbit

omit [Fintype V] in
/-- With a nonempty old tail, the clear predecessor gives the ordinary
OPEN/CLOSE commuting square with a unit score defect. -/
theorem MinimalBadPredecessorCase.clearOpen_nonemptyTail_unitSquare
    {G : SimpleGraph V} {parent child : State V}
    {f x : V} {q r : List V}
    (hcase : MinimalBadPredecessorCase G parent child f q (.open x))
    (hko : parent.ko = false) (hqueue : parent.queue = f :: r)
    (hr : r ≠ []) :
    ∃ so soc sc sco,
      step G parent (.open x) = some so ∧
      step G so .close = some soc ∧
      step G parent .close = some sc ∧
      step G sc (.open x) = some sco ∧
      soc.untouched = sco.untouched ∧ soc.queue = sco.queue ∧
      soc.ko = sco.ko ∧ soc.toMove = sco.toMove ∧
      sco.score = soc.score + 1 := by
  obtain ⟨_, _, _, hx, hbit, _, _, _, _⟩ := hcase.clearOpen_data hko
  obtain ⟨so, soc, sc, sco, hopen, hopenClose, hclose, hcloseOpen,
      hU, hq, hkoEq, hturn, hscore⟩ :=
    open_close_square_away_singleton G parent f x r hqueue hr hko hx
  rw [hbit] at hscore
  exact ⟨so, soc, sc, sco, hopen, hopenClose, hclose, hcloseOpen,
    hU, hq, hkoEq, hturn, hscore⟩

omit [Fintype V] in
/-- With a singleton old queue, the even nonempty real carrier supplies a
second OPEN.  That extra OPEN clears the ko discrepancy, after which the two
orders reconverge with the same unit score defect. -/
theorem MinimalBadPredecessorCase.clearOpen_singleton_unitSquare
    {G : SimpleGraph V} {parent child : State V}
    {f x : V} {q : List V}
    (hcase : MinimalBadPredecessorCase G parent child f q (.open x))
    (hko : parent.ko = false) (hqueue : parent.queue = [f]) :
    ∃ w ∈ parent.untouched, w ≠ x ∧
      ∃ sc scx scxw so soc socw,
        step G parent .close = some sc ∧
        step G sc (.open x) = some scx ∧
        step G scx (.open w) = some scxw ∧
        step G parent (.open x) = some so ∧
        step G so .close = some soc ∧
        step G soc (.open w) = some socw ∧
        scxw.untouched = socw.untouched ∧
        scxw.queue = socw.queue ∧ scxw.ko = socw.ko ∧
        scxw.toMove = socw.toMove ∧
        scxw.score = socw.score + 1 ∧
        scxw = scoreTranslate 1 socw := by
  obtain ⟨_, _, _, hx, hbit, _, _, _, hcarrierEven⟩ :=
    hcase.clearOpen_data hko
  have hwitness : ∃ w ∈ parent.untouched, w ≠ x := by
    by_contra hnone
    push Not at hnone
    have hsingleton : parent.untouched = {x} := by
      ext z
      simp only [Finset.mem_singleton]
      constructor
      · exact fun hz ↦ hnone z hz
      · intro hzx
        subst z
        exact hx
    have hcardOne : (parent.untouched.card : ZMod 2) = 1 := by
      rw [hsingleton]
      simp
    have : (1 : ZMod 2) = 0 := hcardOne.symm.trans hcarrierEven
    exact one_ne_zero this
  obtain ⟨w, hw, hwx⟩ := hwitness
  obtain ⟨sc, scx, scxw, so, soc, socw,
      hclose, hopenX, hopenW, hopen, hopenClose, hopenW',
      hU, hq, hkoEq, hturn, hscore, htranslate⟩ :=
    singleton_wall_reconverges_after_open G parent f x w hqueue hko
      hx hw hwx.symm
  rw [hbit] at hscore htranslate
  exact ⟨w, hw, hwx, sc, scx, scxw, so, soc, socw,
    hclose, hopenX, hopenW, hopen, hopenClose, hopenW',
    hU, hq, hkoEq, hturn, hscore, htranslate⟩

/-- A non-root attacker node in an exact initial strategy has an immediate
defender parent and an exact prefix through that incoming edge. -/
theorem StrategyPrefix.immediate_defender_parent
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {hroot : OddStrategy G seat (initial (V := V))}
    {strategy : OddStrategy G seat s} {p : EdgeVector V}
    (hprefix : StrategyPrefix G seat hroot strategy p)
    (hturn : s.toMove = !seat) (hnotRoot : s ≠ initial) :
    ∃ (parent : State V) (parentTree : OddStrategy G seat parent)
      (pp : EdgeVector V) (m : Move V),
      StrategyPrefix G seat hroot parentTree pp ∧
      parent.toMove = seat ∧ step G parent m = some s ∧
      p = pp + moveLiveStar parent m ∧
      (∀ m' t', step G parent m' = some t' →
        ∃ childTree : OddStrategy G seat t',
          StrategyPrefix G seat hroot childTree
            (pp + moveLiveStar parent m')) := by
  cases hprefix with
  | root => exact False.elim (hnotRoot rfl)
  | @choose parent child hseat m hstep childTree pp parentPrefix =>
      have hparentTurn : parent.toMove = !seat :=
        Bool.eq_not_iff.mpr hseat
      have hchildTurn := step_toMove hstep
      have : s.toMove = seat := by
        rw [hchildTurn, hparentTurn]
        simp
      exact False.elim
        ((by simp : (!seat : Bool) ≠ seat) (hturn.symm.trans this))
  | @answer parent child hseat hasMove children m hstep pp parentPrefix =>
      exact ⟨parent, .answer parent hseat hasMove children, pp, m,
        parentPrefix, hseat, hstep, rfl, fun m' t' hstep' ↦
          ⟨children m' t' hstep',
            StrategyPrefix.answer (hstep := hstep') parentPrefix⟩⟩

/-- Exact strategy-relative ancestry trichotomy at an isolated-dummy
initial counterstrategy.  Isolation is used to certify that the selected
charged front is real. -/
theorem OddStrategy.extract_minimalBad_predecessor_cases
    {G : SimpleGraph V} {d : V} {seat : Bool}
    (hd : IsDummy G d)
    (root : OddStrategy G seat (initial (V := V))) :
    ∃ (s : State V) (strategy : OddStrategy G seat s)
      (p : EdgeVector V) (parent : State V)
      (parentTree : OddStrategy G seat parent) (pp : EdgeVector V)
      (incoming : Move V) (f : V) (q : List V) (sc : State V),
      StrategyPrefix G seat root strategy p ∧
      StrategyPrefix G seat root parentTree pp ∧
      parent.toMove = seat ∧ step G parent incoming = some s ∧
      p = pp + moveLiveStar parent incoming ∧
      (∀ m t, step G parent m = some t →
        ∃ childTree : OddStrategy G seat t,
          StrategyPrefix G seat root childTree
            (pp + moveLiveStar parent m)) ∧
      s.score = 0 ∧ s.toMove = !seat ∧
      s.queue = f :: q ∧ s.ko = false ∧
      step G s .close = some sc ∧ flip G s.untouched f = 1 ∧
      f ≠ d ∧ strategy.selectedMove = some .close ∧
      TreeNeutralWins G (!seat) (scoreTranslate 1 sc) ∧
      MinimalBadPredecessorCase G parent s f q incoming := by
  classical
  let P : Nat → Prop := fun n ↦
    ∃ (s : State V) (strategy : OddStrategy G seat s),
      StrategyNode G seat root strategy ∧ s.score = 0 ∧ rank s = n
  have hP : ∃ n, P n :=
    ⟨rank (initial (V := V)), initial, root,
      StrategyNode.root root, rfl, rfl⟩
  let n := Nat.find hP
  obtain ⟨s0, strategy0, hnode0, hs00, hrank0⟩ := Nat.find_spec hP
  let Q : Nat → Prop := fun k ↦
    ∃ (s : State V) (strategy : OddStrategy G seat s),
      StrategyNode G seat root strategy ∧ s.score = 0 ∧
        rank s = n ∧ s.untouched.card = k
  have hQ : ∃ k, Q k :=
    ⟨s0.untouched.card, s0, strategy0, hnode0, hs00,
      hrank0, rfl⟩
  let k := Nat.find hQ
  obtain ⟨s, strategy, hnode, hs0, hrank, hcard⟩ := Nat.find_spec hQ
  have hminimal : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat strategy desc →
      rank t < rank s → t.score ≠ 0 := by
    intro t desc hinner hlt ht0
    have hglobal : StrategyNode G seat root desc := hnode.trans hinner
    have hPt : P (rank t) := ⟨t, desc, hglobal, ht0, rfl⟩
    have hnle : n ≤ rank t := Nat.find_min' hP hPt
    have hsle : rank s ≤ rank t := by simpa [n, hrank] using hnle
    exact (Nat.not_lt_of_ge hsle) hlt
  have hcarrierMinimal : ∀ {t : State V}
      {desc : OddStrategy G seat t},
      StrategyNode G seat root desc → t.score = 0 →
      rank t = rank s → s.untouched.card ≤ t.untouched.card := by
    intro t desc hdesc ht0 htrank
    have hQt : Q t.untouched.card := by
      refine ⟨t, desc, hdesc, ht0, ?_, rfl⟩
      rw [htrank, hrank]
    have hkle : k ≤ t.untouched.card := Nat.find_min' hQ hQt
    simpa [k, hcard] using hkle
  obtain ⟨hturn, f, q, sc, hqueue, hko, hclose, hflip, hneutral⟩ :=
    strategy.minimal_zeroNode_close_neutral hs0 hminimal
  have hselected := strategy.minimal_zeroNode_selectedClose hs0 hminimal
  obtain ⟨p, hprefix⟩ := hnode.exists_strategyPrefix
  have hnotRoot : s ≠ initial := by
    intro hs
    subst s
    simp [initial] at hqueue
  obtain ⟨parent, parentTree, pp, incoming, hparentPrefix,
      hparentTurn, hincoming, hp, hfan⟩ :=
    hprefix.immediate_defender_parent hturn hnotRoot
  have hparentCoherent := hparentPrefix.coherent_of_initial
  have hfreal : f ≠ d := by
    intro hfd
    subst f
    have hzero := flip_dummy hd s.untouched
    exact one_ne_zero (hflip.symm.trans hzero)
  refine ⟨s, strategy, p, parent, parentTree, pp, incoming, f, q, sc,
    hprefix, hparentPrefix, hparentTurn, hincoming, hp, hfan, hs0, hturn,
    hqueue, hko, hclose, hflip, hfreal, hselected, hneutral, ?_⟩
  cases incoming with
  | close =>
      simp only [step] at hincoming
      split at hincoming
      · contradiction
      · rename_i y tail hparentQueue
        split at hincoming
        · contradiction
        · rename_i hparentKo
          let closeState : State V := {
            untouched := parent.untouched
            queue := tail
            ko := false
            toMove := !parent.toMove
            score := parent.score + flip G parent.untouched y }
          have hsEq : closeState = s := Option.some.inj hincoming
          have htail : tail = f :: q := by
            calc
              tail = closeState.queue := rfl
              _ = s.queue := congrArg State.queue hsEq
              _ = f :: q := hqueue
          have hqueue' : parent.queue = y :: f :: q := by
            rw [hparentQueue, htail]
          have hscoreEq : parent.score + flip G parent.untouched y = 0 := by
            calc
              parent.score + flip G parent.untouched y = closeState.score := rfl
              _ = s.score := congrArg State.score hsEq
              _ = 0 := hs0
          have hU : parent.untouched = s.untouched := by
            calc
              parent.untouched = closeState.untouched := rfl
              _ = s.untouched := congrArg State.untouched hsEq
          have hko' : parent.ko = false := by
            cases hk : parent.ko with
            | false => rfl
            | true => simp [hk] at hparentKo
          by_cases hy0 : flip G parent.untouched y = 0
          · have hp0 : parent.score = 0 := by
              rw [hy0, add_zero] at hscoreEq
              exact hscoreEq
            obtain ⟨z, hzS, _⟩ := exists_mem_adj_of_flip_eq_one hflip
            have hzParent : z ∈ parent.untouched := by
              rw [hU]
              exact hzS
            let so : State V := {
              untouched := parent.untouched.erase z
              queue := parent.queue ++ [z]
              ko := parent.queue.isEmpty
              toMove := !parent.toMove
              score := parent.score }
            have hopen : step G parent (.open z) = some so := by
              simp [step, so, hzParent]
            obtain ⟨soTree, hsoPrefix⟩ := hfan (.open z) so hopen
            have hsoNode : StrategyNode G seat root soTree :=
              hsoPrefix.toStrategyNode
            have hso0 : so.score = 0 := by simp [so, hp0]
            have hcardPos : 0 < parent.untouched.card :=
              Finset.card_pos.mpr ⟨z, hzParent⟩
            have hsoRank : rank so = rank s := by
              rw [← hsEq]
              simp [rank, so, closeState, hqueue', htail,
                Finset.card_erase_of_mem hzParent]
              omega
            have hle := hcarrierMinimal hsoNode hso0 hsoRank
            have hcardErase := Finset.card_erase_of_mem hzParent
            have hsCardPos : 0 < s.untouched.card := by
              rw [← hU]
              exact hcardPos
            simp only [so] at hle
            rw [hcardErase, hU] at hle
            omega
          · have hy1 : flip G parent.untouched y = 1 :=
              zmod2_eq_one_of_ne_zero _ hy0
            have hp1 : parent.score = 1 := by
              rw [hy1] at hscoreEq
              have := congrArg (fun z : ZMod 2 ↦ z + 1) hscoreEq
              simpa [add_assoc, CharTwo.add_self_eq_zero] using this
            exact MinimalBadPredecessorCase.chargedClose y hqueue' hko'
              hU hp1 hy1
  | «open» x =>
      simp only [step] at hincoming
      split at hincoming
      · rename_i hx
        let openState : State V := {
          untouched := parent.untouched.erase x
          queue := parent.queue ++ [x]
          ko := parent.queue.isEmpty
          toMove := !parent.toMove
          score := parent.score }
        have hsEq : openState = s := Option.some.inj hincoming
        have hscoreParent : parent.score = 0 := by
          calc
            parent.score = openState.score := rfl
            _ = s.score := congrArg State.score hsEq
            _ = 0 := hs0
        have hU : s.untouched = parent.untouched.erase x := by
          exact (congrArg State.untouched hsEq).symm
        have hchildQueue : s.queue = parent.queue ++ [x] := by
          exact (congrArg State.queue hsEq).symm
        have hparentQueue : parent.queue ≠ [] := by
          intro hnil
          have hkoEq : openState.ko = s.ko := congrArg State.ko hsEq
          simp [openState, hnil, hko] at hkoEq
        cases hk : parent.ko with
        | false =>
            cases hparentQueueEq : parent.queue with
            | nil => exact False.elim (hparentQueue hparentQueueEq)
            | cons a r =>
              have hshape : f :: q = a :: (r ++ [x]) := by
                calc
                  f :: q = s.queue := hqueue.symm
                  _ = parent.queue ++ [x] := hchildQueue
                  _ = a :: (r ++ [x]) := by simp [hparentQueueEq]
              have haf : a = f := (List.cons.inj hshape).1.symm
              subst a
              have hqShape : q = r ++ [x] := (List.cons.inj hshape).2
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
                have hsz0 : sz.score = 0 := by simp [sz, hscoreParent]
                have hszRank : rank sz = rank s := by
                  rw [← hsEq]
                  simp [rank, sz, openState, hparentQueueEq,
                    Finset.card_erase_of_mem hz,
                    Finset.card_erase_of_mem hx]
                have hminimalZ : ∀ {t : State V}
                    {desc : OddStrategy G seat t},
                    StrategyNode G seat szTree desc →
                    rank t < rank sz → t.score ≠ 0 := by
                  intro t desc hinner hlt ht0
                  have hglobal : StrategyNode G seat root desc :=
                    hszNode.trans hinner
                  have hPt : P (rank t) :=
                    ⟨t, desc, hglobal, ht0, rfl⟩
                  have hnle : n ≤ rank t := Nat.find_min' hP hPt
                  have hszN : rank sz = n := hszRank.trans hrank
                  rw [hszN] at hlt
                  exact (Nat.not_lt_of_ge hnle) hlt
                obtain ⟨_, fz, qz, scz, hqueueZ, hkoZ, hcloseZ,
                    hflipZ, hneutralZ⟩ :=
                  szTree.minimal_zeroNode_close_neutral hsz0 hminimalZ
                have hszQueue : sz.queue = f :: (r ++ [z]) := by
                  simp [sz, hparentQueueEq]
                have hfrontEq : fz = f := by
                  have hcons : fz :: qz = f :: (r ++ [z]) :=
                    hqueueZ.symm.trans hszQueue
                  exact (List.cons.inj hcons).1
                subst fz
                simpa [sz] using hflipZ
              obtain ⟨hfrontZero, hfrontUniversal⟩ :=
                flip_zero_and_adj_of_all_erase_flip_one ⟨x, hx⟩ herase
              have hcarrierEven : (parent.untouched.card : ZMod 2) = 0 := by
                rw [← flip_eq_card_of_forall_adj hfrontUniversal]
                exact hfrontZero
              exact MinimalBadPredecessorCase.clearOpen x hx hparentQueue hk
                hscoreParent hU hchildQueue ⟨r, hparentQueueEq, hqShape⟩
                hfrontZero hfrontUniversal hcarrierEven
        | true =>
            obtain ⟨y, hy⟩ := hparentCoherent.2 hk
            have hchildQueue' : s.queue = [y, x] := by
              rw [hchildQueue, hy]
              rfl
            have hyf : y = f := by
              rw [hqueue] at hchildQueue'
              exact (List.cons.inj hchildQueue'.symm).1
            subst y
            have hq : q = [x] := by
              rw [hqueue] at hchildQueue'
              exact (List.cons.inj hchildQueue'.symm).2.symm
            exact MinimalBadPredecessorCase.protectedOpen x hx hy hk
              hscoreParent hU hchildQueue' hq
      · contradiction
  | pass =>
      simp only [step] at hincoming
      split at hincoming
      · rename_i hpass
        let passState : State V := {
          parent with ko := false, toMove := !parent.toMove }
        have hsEq : passState = s := Option.some.inj hincoming
        have hU : s.untouched = ∅ := by
          calc
            s.untouched = passState.untouched :=
              (congrArg State.untouched hsEq).symm
            _ = parent.untouched := rfl
            _ = ∅ := hpass.1
        have hzero : flip G s.untouched f = 0 := by simp [hU, flip]
        exact False.elim (one_ne_zero (hflip.symm.trans hzero))
      · contradiction

end

end Ogdoad.Fifo
