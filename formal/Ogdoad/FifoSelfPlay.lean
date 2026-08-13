import Ogdoad.FifoFirstSeatStrategy
import Ogdoad.FifoSymmetry

/-!
# A sharp two-selected-child obstruction for FIFO self-play

Deleting an active isolated-dummy interval reverses the controller of every
real event strictly inside the interval.  Consequently a self-play transport
which reuses an attacker-controlled node as a defender-controlled node must
turn selected children into a complete legal response fan.

Two attacker-selected children do not supply that fan on an arbitrary
carrier.  Each explicit odd strategy selects only one second OPEN below a
fixed first OPEN; even two independently selected strategies cover at most
two replies.  When the original carrier has at least four vertices, the
protected singleton-ko state has at least three legal second OPENs, so one
reply is necessarily absent from both selections.

This is a no-go theorem only for a static splice which replays two stored
attacker choices; it does not exclude a dynamic coupling in which the other
copy is currently at a defender node and supplies a full fan.  It is not a
counterexample to FIFO linking.  A successful static splice must import an
additional universal sibling from common root ancestry rather than replaying
only the two selected children.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Exact self-play contradiction criterion.  An odd strategy at a state and
an odd strategy for the same distinguished seat at its score-and-turn
conjugate cannot coexist: conjugating the first strategy makes it an even
strategy at the second root. -/
theorem OddStrategy.not_scoreTurnConjugate
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 (turnTranslate s))) :
    False := by
  have heven : EvenWins G seat (scoreTranslate 1 (turnTranslate s)) :=
    (oddWins_iff_evenWins_scoreTurnTranslate G seat s).mp left.toOddWins
  exact heven.not_oddWins right.toOddWins

omit [Fintype V] in
/-- Common-root spelling of the contradiction criterion.  Thus a successful
copycat proof from one alleged odd root may stop as soon as it constructs two
exact descendant subtrees at score-and-turn conjugate public states. -/
theorem StrategyNode.not_scoreTurnConjugatePair
    {G : SimpleGraph V} {seat : Bool} {rootState s : State V}
    {root : OddStrategy G seat rootState}
    {left : OddStrategy G seat s}
    (_hleft : StrategyNode G seat root left)
    {right : OddStrategy G seat (scoreTranslate 1 (turnTranslate s))}
    (_hright : StrategyNode G seat root right) : False := by
  exact left.not_scoreTurnConjugate right

omit [Fintype V] in
/-- A neutral isolated-dummy move cannot itself create the score component of
the conjugacy required by `OddStrategy.not_scoreTurnConjugate`: it preserves
the accumulated score exactly.  Dummy OPEN/CLOSE can therefore provide a
controller phase, but a successful self-play contradiction must obtain its
unit score defect from a charged real CLOSE or from an OPEN/CLOSE curvature
square. -/
theorem neutralDummyStep_not_scoreTranslate
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    {s t : State V} {m : Move V}
    (hdummyMove : m = .open d ∨
      (m = .close ∧ s.queue.head? = some d))
    (hstep : step G s m = some t) :
    t.score = s.score ∧ t ≠ scoreTranslate 1 s := by
  have hscore : t.score = s.score := by
    rcases hdummyMove with rfl | ⟨rfl, hfront⟩
    · exact open_score hstep
    · obtain ⟨f, q, hqueue, hcloseScore⟩ := close_score hstep
      have hfd : f = d := by
        rw [hqueue] at hfront
        simpa using hfront
      subst f
      rw [hcloseScore, flip_dummy hd, add_zero]
  refine ⟨hscore, ?_⟩
  intro heq
  have hscoreEq := congrArg State.score heq
  simp only [scoreTranslate] at hscoreEq
  rw [hscore] at hscoreEq
  have hone : (1 : ZMod 2) = 0 := by
    exact add_eq_right.mp hscoreEq.symm
  exact one_ne_zero hone

omit [Fintype V] [DecidableEq V] in
/-- The one-front lag produced by the dynamic CLOSE/earlier-OPEN coupling is
already incompatible with score-and-turn conjugacy, independently of its
score defect: conjugacy preserves the queue, whereas a finite list cannot be
equal to itself with one extra front cell.  Thus the unit score curvature of
a real-front exit still does not finish the self-play argument until an
ancestry repair removes this queue lag. -/
theorem oneFrontOffset_not_scoreTurnTranslate
    {sA sB : State V} {x : V}
    (hqueue : sB.queue = x :: sA.queue) :
    sB ≠ scoreTranslate 1 (turnTranslate sA) := by
  intro hconjugate
  have hqueueEq := congrArg State.queue hconjugate
  have hbad : x :: sA.queue = sA.queue := by
    rw [← hqueue]
    simpa [scoreTranslate, turnTranslate] using hqueueEq
  exact List.cons_ne_self x sA.queue hbad

omit [Fintype V] in
/-- A finite set with at least three elements has an element outside any two
specified labels. -/
theorem Finset.exists_ne_two_of_three_le_card
    (S : Finset V) (a b : V) (hcard : 3 ≤ S.card) :
    ∃ z ∈ S, z ≠ a ∧ z ≠ b := by
  by_contra hnone
  have hcover : ∀ z ∈ S, z = a ∨ z = b := by
    intro z hz
    by_contra hout
    have hza : z ≠ a := fun hza ↦ hout (Or.inl hza)
    have hzb : z ≠ b := fun hzb ↦ hout (Or.inr hzb)
    exact hnone ⟨z, hz, hza, hzb⟩
  have hsub : S ⊆ {a, b} := by
    intro z hz
    rcases hcover z hz with rfl | rfl <;> simp
  have hle : S.card ≤ ({a, b} : Finset V).card :=
    Finset.card_le_card hsub
  have hab : ({a, b} : Finset V).card ≤ 2 := by
    exact Finset.card_insert_le a {b}
  omega

/-- On a carrier of size at least four, after any first OPEN there is a legal
second OPEN different from both specified candidate replies. -/
theorem exists_uncovered_secondOpen_of_four_le_card
    (x a b : V) (hcard : 4 ≤ Fintype.card V) :
    ∃ z ∈ (Finset.univ.erase x : Finset V), z ≠ a ∧ z ≠ b := by
  have hpunctured : 3 ≤ (Finset.univ.erase x : Finset V).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
    omega
  exact Finset.exists_ne_two_of_three_le_card
    (Finset.univ.erase x) a b hpunctured

/-- Even two independent first-seat odd strategies leave a legal second OPEN
outside both stored replies below every fixed first opener.  In particular,
two shifted copies of one strategy cannot *merely by replaying those two
selected children* implement the universal node required after an
interval-induced controller reversal.  The theorem does not address an
alternating coupling where one copy contributes a genuine universal node. -/
theorem two_firstSeatOddStrategies_leave_uncovered_reply
    [Nontrivial V] {G : SimpleGraph V}
    (hcard : 4 ≤ Fintype.card V)
    (root₁ root₂ : OddStrategy G false (initial (V := V))) (x : V) :
    let fan₁ := root₁.firstSeatSelectedFan
    let fan₂ := root₂.firstSeatSelectedFan
    ∃ z ∈ (Finset.univ.erase x : Finset V),
      z ≠ fan₁.reply x ∧ z ≠ fan₂.reply x := by
  dsimp only
  exact exists_uncovered_secondOpen_of_four_le_card x
    (root₁.firstSeatSelectedFan.reply x)
    (root₂.firstSeatSelectedFan.reply x) hcard

end

end Ogdoad.Fifo
