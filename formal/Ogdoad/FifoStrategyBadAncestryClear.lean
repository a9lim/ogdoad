import Ogdoad.FifoStrategyBadAncestry

/-!
# Excluding the clear-OPEN minimal bad ancestry

The clear-OPEN predecessor has a clear queue `f :: r`, score zero, and even
untouched carrier.  Its complete defender fan contains both every `OPEN z`
and the front `CLOSE f`.  All these children have the same minimal rank.

The `CLOSE f` child forces the next front `y` to have unit charge on the full
carrier.  In every `OPEN z` sibling, fixed-front minimality first selects
`CLOSE f`; the following universal `CLOSE y` must retain odd score, so `y`
has zero charge after erasing every `z`.  Hence `y` is adjacent to every
untouched vertex.  Its full charge is therefore the carrier cardinality,
which is even, contradicting the unit charge from the `CLOSE f` child.

This is the missing same-root fixed-front crossing argument.  It uses the
actual universal siblings and exact strategy ancestry; no minimax census or
unrelated global minimum is involved.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- At a rank-minimal zero node whose queue has two displayed fronts, the
second front has charge zero.  The strategy selects the first `CLOSE`; its
child is a defender node, so the second `CLOSE` is universal.  A unit second
charge would return to score zero at strictly smaller rank. -/
theorem OddStrategy.minimal_zeroNode_secondFront_flip_zero
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (strategy : OddStrategy G seat s) (hs0 : s.score = 0)
    (hminimal : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat strategy desc →
      rank t < rank s → t.score ≠ 0)
    {f y : V} {q : List V} (hqueue : s.queue = f :: y :: q) :
    flip G s.untouched y = 0 := by
  have hselected := strategy.minimal_zeroNode_selectedClose hs0 hminimal
  cases strategy with
  | terminal _ _ hscore => exact False.elim (hscore hs0)
  | answer _ _ _ _ => simp [OddStrategy.selectedMove] at hselected
  | choose _ hseat m a hstep child =>
      have hm : m = .close := by
        simpa [OddStrategy.selectedMove] using Option.some.inj hselected
      subst m
      have hfirstNode : StrategyNode G seat
          (OddStrategy.choose s hseat .close a hstep child) child :=
        StrategyNode.choose (StrategyNode.root child)
      have ha1 : a.score = 1 :=
        zmod2_eq_one_of_ne_zero _
          (hminimal hfirstNode (rank_step_lt hstep))
      let a0 : State V := {
        untouched := s.untouched
        queue := y :: q
        ko := false
        toMove := !s.toMove
        score := s.score + flip G s.untouched f }
      have haEq : a = a0 := by
        have hstep' := hstep
        simp only [step, hqueue] at hstep'
        split at hstep'
        · contradiction
        · exact Option.some.inj hstep'.symm
      let b : State V := {
        untouched := a.untouched
        queue := q
        ko := false
        toMove := !a.toMove
        score := a.score + flip G a.untouched y }
      have hqueueA : a.queue = y :: q := by
        simp [haEq, a0]
      have hkoA : a.ko = false := by
        simp [haEq, a0]
      have hsecond : step G a .close = some b := by
        simp [step, b, hqueueA, hkoA]
      have haTurn : a.toMove = seat := by
        have hmove := step_toMove hstep
        have hsTurn : s.toMove = !seat := Bool.eq_not_iff.mpr hseat
        rw [hmove, hsTurn]
        simp
      cases child with
      | terminal _ hterminal _ =>
          exact False.elim (terminal_no_step hterminal ⟨.close, b, hsecond⟩)
      | choose _ hchildSeat _ _ _ _ =>
          exact False.elim (hchildSeat haTurn)
      | answer _ hchildSeat hasMove children =>
          let bTree := children .close b hsecond
          have hbNode : StrategyNode G seat
              (OddStrategy.choose s hseat .close a hstep
                (OddStrategy.answer a hchildSeat hasMove children)) bTree :=
            StrategyNode.choose
              (StrategyNode.answer (StrategyNode.root bTree))
          have hbNe : b.score ≠ 0 :=
            hminimal hbNode
              (lt_trans (rank_step_lt hsecond) (rank_step_lt hstep))
          by_contra hy0
          have hy1 := zmod2_eq_one_of_ne_zero _ hy0
          have haU : a.untouched = s.untouched := by
            simp [haEq, a0]
          have hb0 : b.score = 0 := by
            simp only [b]
            rw [ha1, haU, hy1]
            exact CharTwo.add_self_eq_zero 1
          exact hbNe hb0

/-- The clear-OPEN predecessor is incompatible with rank minimality in one
fixed initial odd strategy.  The hypotheses are exactly the same-root parent
fan and the rank-minimal zero-node data available at the extraction site in
`OddStrategy.extract_minimalBad_predecessor_cases`. -/
theorem no_clearOpen_of_sameRoot_rankMinimal
    {G : SimpleGraph V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    {s parent : State V} {pp : EdgeVector V} {f x : V} {r : List V}
    (hfan : ∀ m t, step G parent m = some t →
      ∃ childTree : OddStrategy G seat t,
        StrategyPrefix G seat root childTree
          (pp + moveLiveStar parent m))
    (hincoming : step G parent (.open x) = some s)
    (hminimal : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat root desc →
      rank t < rank s → t.score ≠ 0)
    (hx : x ∈ parent.untouched)
    (hqueue : parent.queue = f :: r)
    (hko : parent.ko = false)
    (hscore : parent.score = 0)
    (hfrontZero : flip G parent.untouched f = 0)
    (hcarrierEven : (parent.untouched.card : ZMod 2) = 0) : False := by
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
  let c : State V := {
    untouched := parent.untouched
    queue := r
    ko := false
    toMove := !parent.toMove
    score := parent.score }
  have hclose : step G parent .close = some c := by
    simp [step, c, hqueue, hko, hfrontZero]
  obtain ⟨cTree, hcPrefix⟩ := hfan .close c hclose
  have hcNode : StrategyNode G seat root cTree := hcPrefix.toStrategyNode
  have hc0 : c.score = 0 := by simp [c, hscore]
  have hcRank : rank c = rank s := by
    have hcardPos : 0 < parent.untouched.card :=
      Finset.card_pos.mpr ⟨x, hx⟩
    rw [← hsEq]
    simp [rank, c, sx, hqueue, Finset.card_erase_of_mem hx]
    omega
  have hminimalC : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat cTree desc →
      rank t < rank c → t.score ≠ 0 := by
    intro t desc hdesc hlt
    apply hminimal (hcNode.trans hdesc)
    rw [hcRank] at hlt
    exact hlt
  obtain ⟨_, y, tail, cy, hcQueue, _, _, hyOne, _⟩ :=
    cTree.minimal_zeroNode_close_neutral hc0 hminimalC
  have hrShape : r = y :: tail := by
    simpa [c] using hcQueue
  have hyFull : flip G parent.untouched y = 1 := by
    simpa [c] using hyOne
  have hyErase : ∀ z ∈ parent.untouched,
      flip G (parent.untouched.erase z) y = 0 := by
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
    have hqueueZ : sz.queue = f :: y :: (tail ++ [z]) := by
      simp [sz, hqueue, hrShape]
    exact szTree.minimal_zeroNode_secondFront_flip_zero
      hsz0 hminimalZ hqueueZ
  have hyUniversal : ∀ z ∈ parent.untouched, G.Adj y z := by
    intro z hz
    have hsplit := flip_eq_flip_erase_add (G := G) (f := y) hz
    have hbit : adjacencyBit G y z = 1 := by
      rw [hyFull, hyErase z hz] at hsplit
      simpa using hsplit.symm
    by_contra hnot
    simp [adjacencyBit, hnot] at hbit
  have hcard := flip_eq_card_of_forall_adj hyUniversal
  rw [hyFull, hcarrierEven] at hcard
  exact one_ne_zero hcard

/-! ## The exact two-case normal form -/

/-- The two surviving immediate ancestries after excluding `clearOpen`.
Unlike a disjunction of constructor names, this Type-valued normal form keeps
every field of the selected alternative available after case analysis. -/
inductive MinimalBadPredecessorNormalCase (G : SimpleGraph V)
    (parent child : State V) (f : V) (q : List V) : Move V → Prop
  | chargedClose (y : V)
      (hqueue : parent.queue = y :: f :: q)
      (hko : parent.ko = false)
      (hU : parent.untouched = child.untouched)
      (hscore : parent.score = 1)
      (hcharge : flip G parent.untouched y = 1) :
      MinimalBadPredecessorNormalCase G parent child f q .close
  | protectedOpen (x : V)
      (hx : x ∈ parent.untouched)
      (hqueue : parent.queue = [f])
      (hko : parent.ko = true)
      (hscore : parent.score = 0)
      (hU : child.untouched = parent.untouched.erase x)
      (hchildQueue : child.queue = [f, x])
      (hq : q = [x]) :
      MinimalBadPredecessorNormalCase G parent child f q (.open x)

/-- Paper-level strategy-relative bad-ancestry normal form.  Every isolated-
dummy initial odd counterstrategy contains a lexicographically minimal bad
node whose immediate predecessor is exactly either a charged `CLOSE` or a
protected singleton-queue `OPEN`.  All ancestry prefixes, the complete
same-root parent fan, the charged selected close, and its neutral translated
tail are retained verbatim from the three-case extractor.

The proof repeats the finite witness selection because the older existential
theorem deliberately did not export its internal rank-minimality certificate;
the clear branch is discharged by `no_clearOpen_of_sameRoot_rankMinimal`. -/
theorem OddStrategy.extract_minimalBad_predecessor_normalCases
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
      MinimalBadPredecessorNormalCase G parent s f q incoming := by
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
      StrategyNode G seat root desc →
      rank t < rank s → t.score ≠ 0 := by
    intro t desc hglobal hlt ht0
    have hPt : P (rank t) := ⟨t, desc, hglobal, ht0, rfl⟩
    have hnle : n ≤ rank t := Nat.find_min' hP hPt
    have hsle : rank s ≤ rank t := by simpa [n, hrank] using hnle
    exact (Nat.not_lt_of_ge hsle) hlt
  have hminimalLocal : ∀ {t : State V}
      {desc : OddStrategy G seat t},
      StrategyNode G seat strategy desc →
      rank t < rank s → t.score ≠ 0 := by
    intro t desc hdesc
    exact hminimal (hnode.trans hdesc)
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
    strategy.minimal_zeroNode_close_neutral hs0 hminimalLocal
  have hselected :=
    strategy.minimal_zeroNode_selectedClose hs0 hminimalLocal
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
              have hadd := congrArg (fun z : ZMod 2 ↦ z + 1) hscoreEq
              simpa [add_assoc, CharTwo.add_self_eq_zero] using hadd
            exact MinimalBadPredecessorNormalCase.chargedClose y
              hqueue' hko' hU hp1 hy1
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
        have hU : s.untouched = parent.untouched.erase x :=
          (congrArg State.untouched hsEq).symm
        have hchildQueue : s.queue = parent.queue ++ [x] :=
          (congrArg State.queue hsEq).symm
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
                  intro t desc hinner hlt
                  apply hminimal (hszNode.trans hinner)
                  rw [hszRank] at hlt
                  exact hlt
                obtain ⟨_, fz, qz, scz, hqueueZ, _, _, hflipZ, _⟩ :=
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
              have hcarrierEven :
                  (parent.untouched.card : ZMod 2) = 0 := by
                rw [← flip_eq_card_of_forall_adj hfrontUniversal]
                exact hfrontZero
              have hincomingOriginal :
                  step G parent (.open x) = some s := by
                rw [← hsEq]
                simp [step, openState, hx]
              exact False.elim
                (no_clearOpen_of_sameRoot_rankMinimal hfan
                  hincomingOriginal hminimal hx
                  hparentQueueEq hk hscoreParent hfrontZero hcarrierEven)
        | true =>
            obtain ⟨y, hy⟩ := hparentCoherent.2 hk
            have hchildQueue' : s.queue = [y, x] := by
              rw [hchildQueue, hy]
              rfl
            have hyf : y = f := by
              rw [hqueue] at hchildQueue'
              exact (List.cons.inj hchildQueue'.symm).1
            subst y
            have hq' : q = [x] := by
              rw [hqueue] at hchildQueue'
              exact (List.cons.inj hchildQueue'.symm).2.symm
            exact MinimalBadPredecessorNormalCase.protectedOpen x hx hy hk
              hscoreParent hU hchildQueue' hq'
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
