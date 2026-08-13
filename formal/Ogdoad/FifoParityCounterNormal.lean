import Ogdoad.FifoStrategyBadAncestryClear

/-!
# Parity-seat counterstrategy normal form

Before the unique forced PASS, the physical mover is determined by the
parity of the FIFO queue length: OPEN and CLOSE both toggle the turn and the
queue-length parity.  A strategy descendant with nonempty untouched carrier
cannot lie after the PASS.  Combining this reachability invariant with the
strategy-relative minimal-bad normal form gives a sharper obstruction for
the proposed parity-seat theorem.

On an odd-order board, a mover-seat odd counterstrategy cannot enter the
protected-singleton alternative: the extracted bad queue must have odd
length, whereas a protected bad queue has length two.  Thus any such
counterstrategy has the charged-CLOSE ancestry.  On even order the bad queue
has even length; both the charged-CLOSE and protected alternatives remain.

This is a universal proof reduction, not a proof of the parity-seat theorem.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Before a forced PASS, the mover bit equals the FIFO queue-length parity. -/
def QueueTurnParity (s : State V) : Prop :=
  s.queue.length % 2 = if s.toMove then 1 else 0

omit [DecidableEq V] in
/-- The empty initial queue has the initial mover bit. -/
theorem queueTurnParity_initial :
    QueueTurnParity (initial (V := V)) := by
  simp [QueueTurnParity, initial]

omit [Fintype V] in
/-- OPEN and CLOSE preserve queue/turn parity.  PASS is excluded by the
nonempty untouched carrier of the target. -/
theorem QueueTurnParity.step_of_target_nonempty
    {G : SimpleGraph V} {s t : State V} {m : Move V}
    (hs : QueueTurnParity s) (hstep : step G s m = some t)
    (htU : t.untouched.Nonempty) : QueueTurnParity t := by
  cases m with
  | «open» v =>
      simp only [step] at hstep
      split at hstep
      · cases hstep
        simp only [QueueTurnParity, List.length_append, List.length_cons,
          List.length_nil]
        cases hturn : s.toMove <;> simp [QueueTurnParity, hturn] at hs ⊢ <;>
          omega
      · contradiction
  | close =>
      simp only [step] at hstep
      split at hstep
      · contradiction
      · rename_i f q hqueue
        split at hstep
        · contradiction
        · cases hstep
          simp only [QueueTurnParity]
          cases hturn : s.toMove <;>
            simp [QueueTurnParity, hqueue, hturn] at hs ⊢ <;> omega
  | pass =>
      simp only [step] at hstep
      split at hstep
      · rename_i hpass
        cases hstep
        rw [hpass.1] at htU
        simp at htU
      · contradiction

omit [Fintype V] in
/-- A target with an untouched vertex can only be reached from a source with
an untouched vertex. -/
theorem source_untouched_nonempty_of_step
    {G : SimpleGraph V} {s t : State V} {m : Move V}
    (hstep : step G s m = some t) (htU : t.untouched.Nonempty) :
    s.untouched.Nonempty := by
  cases m with
  | «open» v =>
      simp only [step] at hstep
      split at hstep
      · rename_i hv
        exact ⟨v, hv⟩
      · contradiction
  | close =>
      simp only [step] at hstep
      split at hstep
      · contradiction
      · split at hstep
        · contradiction
        · cases hstep
          exact htU
  | pass =>
      simp only [step] at hstep
      split at hstep
      · rename_i hp
        cases hstep
        rw [hp.1] at htU
        simp at htU
      · contradiction

/-- Every exact initial-strategy descendant with an untouched vertex is
before the forced PASS, hence satisfies queue/turn parity. -/
theorem StrategyPrefix.queueTurnParity_of_untouched_nonempty
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {root : OddStrategy G seat (initial (V := V))}
    {tree : OddStrategy G seat s} {p : EdgeVector V}
    (hp : StrategyPrefix G seat root tree p)
    (hU : s.untouched.Nonempty) : QueueTurnParity s := by
  induction hp with
  | root => exact queueTurnParity_initial
  | @choose parent child hseat m hstep childTree p parentPrefix ih =>
      exact ih (source_untouched_nonempty_of_step hstep hU)
        |>.step_of_target_nonempty hstep hU
  | @answer parent child hseat hasMove children m hstep p parentPrefix ih =>
      exact ih (source_untouched_nonempty_of_step hstep hU)
        |>.step_of_target_nonempty hstep hU

/-- At an attacker node for the parity-selected seat, the queue length has
the same parity as the whole carrier.  This applies to every exact initial
strategy prefix before PASS, not only to the minimal-bad node. -/
theorem StrategyPrefix.queueCardParity_at_paritySeat_attacker
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {root : OddStrategy G seat (initial (V := V))}
    {tree : OddStrategy G seat s} {p : EdgeVector V}
    (hp : StrategyPrefix G seat root tree p)
    (hU : s.untouched.Nonempty) (hattacker : s.toMove ≠ seat)
    (hseat : (Odd (Fintype.card V) ∧ seat = false) ∨
      (Even (Fintype.card V) ∧ seat = true)) :
    s.queue.length % 2 = Fintype.card V % 2 := by
  have hqueueTurn := hp.queueTurnParity_of_untouched_nonempty hU
  rcases hseat with ⟨hodd, rfl⟩ | ⟨heven, rfl⟩
  · have hmover : s.toMove = true := by
      cases hs : s.toMove
      · exact False.elim (hattacker hs)
      · rfl
    simpa [QueueTurnParity, hmover, Nat.odd_iff.mp hodd] using hqueueTurn
  · have hnonmover : s.toMove = false := by
      cases hs : s.toMove
      · rfl
      · exact False.elim (hattacker hs)
    simpa [QueueTurnParity, hnonmover, Nat.even_iff.mp heven] using hqueueTurn

omit [Fintype V] [DecidableEq V] in
/-- A unit close charge certifies a nonempty untouched carrier. -/
theorem untouched_nonempty_of_flip_eq_one
    {G : SimpleGraph V} {s : State V} {f : V}
    (hflip : flip G s.untouched f = 1) : s.untouched.Nonempty := by
  by_contra hU
  rw [Finset.not_nonempty_iff_eq_empty.mp hU] at hflip
  simp [flip] at hflip

/-- Data retained at the parity-seat minimum.  The final field is the new
root-parity constraint on the extracted bad queue. -/
structure ParitySeatBadNormalWitness (G : SimpleGraph V) (d : V)
    (seat : Bool) (root : OddStrategy G seat (initial (V := V))) where
  state : State V
  tree : OddStrategy G seat state
  moment : EdgeVector V
  parent : State V
  parentTree : OddStrategy G seat parent
  parentMoment : EdgeVector V
  incoming : Move V
  front : V
  tail : List V
  closeChild : State V
  ancestry : StrategyPrefix G seat root tree moment
  parentAncestry : StrategyPrefix G seat root parentTree parentMoment
  parentTurn : parent.toMove = seat
  incomingStep : step G parent incoming = some state
  momentEq : moment = parentMoment + moveLiveStar parent incoming
  completeParentFan : ∀ m t, step G parent m = some t →
    ∃ childTree : OddStrategy G seat t,
      StrategyPrefix G seat root childTree
        (parentMoment + moveLiveStar parent m)
  score : state.score = 0
  turn : state.toMove = !seat
  queue : state.queue = front :: tail
  ko : state.ko = false
  closeStep : step G state .close = some closeChild
  charged : flip G state.untouched front = 1
  realFront : front ≠ d
  selectedClose : tree.selectedMove = some .close
  neutralTail : TreeNeutralWins G (!seat) (scoreTranslate 1 closeChild)
  normalCase : MinimalBadPredecessorNormalCase G parent state front tail incoming
  queueCardParity : state.queue.length % 2 = Fintype.card V % 2

/-- Every parity-selected initial odd counterstrategy has the usual exact
minimal-bad normal form, now with the bad queue constrained to have the same
parity as the whole board. -/
theorem OddStrategy.nonempty_paritySeatBadNormalWitness
    {G : SimpleGraph V} {d : V} {seat : Bool}
    (hd : IsDummy G d)
    (root : OddStrategy G seat (initial (V := V)))
    (hseat : (Odd (Fintype.card V) ∧ seat = false) ∨
      (Even (Fintype.card V) ∧ seat = true)) :
    Nonempty (ParitySeatBadNormalWitness G d seat root) := by
  classical
  obtain ⟨s, tree, p, parent, parentTree, pp, incoming, f, q, sc,
      hp, hpp, hparentTurn, hincoming, hmoment, hfan, hs0, hturn,
      hqueue, hko, hclose, hflip, hfreal, hselected, hneutral, hnormal⟩ :=
    root.extract_minimalBad_predecessor_normalCases hd
  have hU : s.untouched.Nonempty := untouched_nonempty_of_flip_eq_one hflip
  have hqueueTurn := hp.queueTurnParity_of_untouched_nonempty hU
  have hqueueParity : s.queue.length % 2 = Fintype.card V % 2 := by
    rcases hseat with ⟨hodd, rfl⟩ | ⟨heven, rfl⟩
    · have hmover : s.toMove = true := by simpa using hturn
      simpa [QueueTurnParity, hmover, Nat.odd_iff.mp hodd] using hqueueTurn
    · have hnonmover : s.toMove = false := by simpa using hturn
      simpa [QueueTurnParity, hnonmover, Nat.even_iff.mp heven] using hqueueTurn
  exact ⟨{
    state := s
    tree := tree
    moment := p
    parent := parent
    parentTree := parentTree
    parentMoment := pp
    incoming := incoming
    front := f
    tail := q
    closeChild := sc
    ancestry := hp
    parentAncestry := hpp
    parentTurn := hparentTurn
    incomingStep := hincoming
    momentEq := hmoment
    completeParentFan := hfan
    score := hs0
    turn := hturn
    queue := hqueue
    ko := hko
    closeStep := hclose
    charged := hflip
    realFront := hfreal
    selectedClose := hselected
    neutralTail := hneutral
    normalCase := hnormal
    queueCardParity := hqueueParity }⟩

/-- Odd-order mover-seat counterstrategies have no protected alternative.
Their exact minimum is a charged CLOSE following a charged CLOSE, with an
even queue tail after the selected front. -/
theorem OddStrategy.oddCard_mover_yields_chargedClose
    {G : SimpleGraph V} {d : V}
    (hd : IsDummy G d) (hcard : Odd (Fintype.card V))
    (root : OddStrategy G false (initial (V := V))) :
    ∃ (w : ParitySeatBadNormalWitness G d false root) (y : V),
      w.incoming = .close ∧
      w.parent.queue = y :: w.front :: w.tail ∧
      w.parent.ko = false ∧
      w.parent.untouched = w.state.untouched ∧
      w.parent.score = 1 ∧
      flip G w.parent.untouched y = 1 ∧
      w.tail.length % 2 = 0 := by
  obtain ⟨s, tree, p, parent, parentTree, pp, incoming, f, q, sc,
      hp, hpp, hparentTurn, hincoming, hmoment, hfan, hs0, hturn,
      hqueue, hko, hclose, hflip, hfreal, hselected, hneutral, hnormal⟩ :=
    root.extract_minimalBad_predecessor_normalCases hd
  have hU : s.untouched.Nonempty := untouched_nonempty_of_flip_eq_one hflip
  have hqueueTurn := hp.queueTurnParity_of_untouched_nonempty hU
  have hqueueParity : s.queue.length % 2 = Fintype.card V % 2 := by
    have hmover : s.toMove = true := by simpa using hturn
    simpa [QueueTurnParity, hmover, Nat.odd_iff.mp hcard] using hqueueTurn
  have hqueueOdd : s.queue.length % 2 = 1 := by
    rw [hqueueParity, Nat.odd_iff.mp hcard]
  cases hnormal with
  | chargedClose y hparentQueue hparentKo hparentU hparentScore hcharge =>
      let w : ParitySeatBadNormalWitness G d false root := {
        state := s
        tree := tree
        moment := p
        parent := parent
        parentTree := parentTree
        parentMoment := pp
        incoming := .close
        front := f
        tail := q
        closeChild := sc
        ancestry := hp
        parentAncestry := hpp
        parentTurn := hparentTurn
        incomingStep := hincoming
        momentEq := hmoment
        completeParentFan := hfan
        score := hs0
        turn := hturn
        queue := hqueue
        ko := hko
        closeStep := hclose
        charged := hflip
        realFront := hfreal
        selectedClose := hselected
        neutralTail := hneutral
        normalCase := .chargedClose y hparentQueue hparentKo hparentU
          hparentScore hcharge
        queueCardParity := hqueueParity }
      refine ⟨w, y, rfl, hparentQueue, hparentKo, hparentU,
        hparentScore, hcharge, ?_⟩
      change q.length % 2 = 0
      rw [hqueue] at hqueueOdd
      simp only [List.length_cons] at hqueueOdd
      have htailBound : q.length % 2 < 2 := Nat.mod_lt _ (by omega)
      rw [Nat.add_mod] at hqueueOdd
      norm_num at hqueueOdd
      omega
  | protectedOpen x hx hparentQueue hparentKo hparentScore hchildU
      hchildQueue htail =>
      have hlen : s.queue.length = 2 := by simp [hchildQueue]
      rw [hlen] at hqueueOdd
      norm_num at hqueueOdd

end

end Ogdoad.Fifo
