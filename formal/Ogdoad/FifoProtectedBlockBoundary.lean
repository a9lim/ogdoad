import Ogdoad.FifoStrategyBadAncestryClear
import Ogdoad.FifoCrossExitIncidence
import Mathlib.Data.Multiset.DershowitzManna

/-!
# The protected branch starts at an empty-queue block

The protected-singleton alternative in the strategy-relative bad-ancestry
normal form has a defender parent with queue `[f]` and active ko.  Exact
strategy ancestry forces that parent to be the immediate child of the
attacker's selected `OPEN f` from an empty queue.  Thus the protected case is
not an arbitrary singleton wall: it is the first move of one selected
empty-queue block in the same root strategy.

Walking backward across that selected OPEN does not, by itself, supply the
extra affine point needed by the causal factor extension.  A continuation
representative at the protected parent lifts to the empty-queue attacker node
as `moveLiveStar empty (OPEN f) + a`; lifting that point to the original root
is definitionally the same decorated point `parentPrefix + a`.  Therefore a
successful protected-case contraction must use a different branch of the
preceding first-return block, not merely expose the selected predecessor.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem odd_constant_prefix_sum {I : Type*}
    (is : List I) (p : EdgeVector V) (hodd : is.length % 2 = 1) :
    (is.map fun _ ↦ p).sum = p := by
  cases is with
  | nil => simp at hodd
  | cons i rest =>
      cases rest with
      | nil => simp
      | cons j tail =>
          have htail : tail.length % 2 = 1 := by
            simp only [List.length_cons] at hodd
            omega
          have ih := odd_constant_prefix_sum tail p htail
          simp only [List.map_cons, List.sum_cons]
          rw [ih]
          ext e
          simp only [Finsupp.add_apply]
          calc
            p e + (p e + p e) = p e + 0 := by
              rw [CharTwo.add_self_eq_zero]
            _ = p e := add_zero _
termination_by is.length

omit [Fintype V] [DecidableEq V] in
private theorem protected_list_sum_map_add {I : Type*}
    (is : List I) (a b : I → EdgeVector V) :
    (is.map fun i ↦ a i + b i).sum =
      (is.map a).sum + (is.map b).sum := by
  induction is with
  | nil => simp
  | cons i rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      abel

omit [Fintype V] in
/-- Odd ordinary siblings and one distinguished sibling form a homogeneous
exchange at a defender node.  After lifting to a common strategy root, the
distinguished decorated point differs from the odd sum of ordinary decorated
points by an actual root response direction.

This is the parity orientation needed at the predecessor of a protected
block: its singleton CLOSE is distinguished and its odd untouched carrier
indexes the alternative OPEN siblings. -/
theorem StrategyPrefix.answer_oddFan_distinguished_exchange
    {G : SimpleGraph V} {seat : Bool} {root s t0 : State V}
    {hroot : OddStrategy G seat root}
    {hseat : s.toMove = seat}
    {hasMove : ∃ m u, step G s m = some u}
    {children : ∀ m u, step G s m = some u → OddStrategy G seat u}
    {p : EdgeVector V}
    (hp : StrategyPrefix G seat hroot
      (OddStrategy.answer s hseat hasMove children) p)
    {I : Type*} (is : List I) (m : I → Move V) (t : I → State V)
    (hstep : ∀ i ∈ is, step G s (m i) = some (t i))
    (z : I → EdgeVector V)
    (hz : ∀ i (hi : i ∈ is), AffineResponseMoment G seat
      (children (m i) (t i) (hstep i hi)) (z i))
    (m0 : Move V) (hstep0 : step G s m0 = some t0)
    (z0 : EdgeVector V)
    (hz0 : AffineResponseMoment G seat
      (children m0 t0 hstep0) z0)
    (hodd : is.length % 2 = 1) :
    ∃ ladder,
      ResponseDirection G seat hroot ladder ∧
      (p + (moveLiveStar s m0 + z0)) +
          (is.map fun i ↦
            p + (moveLiveStar s (m i) + z i)).sum = ladder := by
  let ordinary := is.map fun i ↦ moveLiveStar s (m i) + z i
  have hordinaryMem : ∀ w ∈ ordinary,
      AffineResponseMoment G seat
        (OddStrategy.answer s hseat hasMove children) w := by
    intro w hw
    simp only [ordinary, List.mem_map] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    exact AffineResponseMoment.answerChild
      (hstep := hstep i hi) (hz i hi)
  have hordinaryOdd : ordinary.length % 2 = 1 := by
    simpa [ordinary] using hodd
  have hordinary : AffineResponseMoment G seat
      (OddStrategy.answer s hseat hasMove children) ordinary.sum :=
    AffineResponseMoment.odd_list_sum ordinary hordinaryOdd hordinaryMem
  have hdistinguished : AffineResponseMoment G seat
      (OddStrategy.answer s hseat hasMove children)
      (moveLiveStar s m0 + z0) :=
    AffineResponseMoment.answerChild (hstep := hstep0) hz0
  let ladder := (moveLiveStar s m0 + z0) + ordinary.sum
  have hlocal : ResponseDirection G seat
      (OddStrategy.answer s hseat hasMove children) ladder :=
    ⟨moveLiveStar s m0 + z0, ordinary.sum,
      hdistinguished, hordinary, rfl⟩
  refine ⟨ladder, hp.lift_direction hlocal, ?_⟩
  have hdecomp :
      (is.map fun i ↦ p + (moveLiveStar s (m i) + z i)).sum =
        p + ordinary.sum := by
    rw [protected_list_sum_map_add]
    rw [odd_constant_prefix_sum is p hodd]
  rw [hdecomp]
  simp only [ladder]
  ext e
  simp only [Finsupp.add_apply]
  calc
    p e + (moveLiveStar s m0 e + z0 e) +
          (p e + ordinary.sum e) =
        (p e + p e) +
          ((moveLiveStar s m0 e + z0 e) + ordinary.sum e) := by abel
    _ = (moveLiveStar s m0 e + z0 e) + ordinary.sum e := by
      rw [CharTwo.add_self_eq_zero, zero_add]

omit [Fintype V] in
/-- Full-open-fan specialization at a clear singleton defender predecessor.
When its untouched carrier is odd, the distinguished CLOSE decorated point
is congruent, modulo a root response direction, to the odd family of every
OPEN-sibling decorated point.  This is the exact recursive replacement made
available one block before a non-root protected singleton. -/
theorem StrategyPrefix.singletonClear_oddCarrier_close_exchange
    {G : SimpleGraph V} {seat : Bool} {root before empty : State V}
    {hroot : OddStrategy G seat root}
    {hseat : before.toMove = seat}
    {hasMove : ∃ m u, step G before m = some u}
    {children : ∀ m u, step G before m = some u →
      OddStrategy G seat u}
    {p : EdgeVector V}
    (hp : StrategyPrefix G seat hroot
      (OddStrategy.answer before hseat hasMove children) p)
    (is : List V) (his : is.Nodup)
    (hset : is.toFinset = before.untouched)
    (t : V → State V)
    (hstep : ∀ z ∈ is, step G before (.open z) = some (t z))
    (a : V → EdgeVector V)
    (ha : ∀ z (hz : z ∈ is), AffineResponseMoment G seat
      (children (.open z) (t z) (hstep z hz)) (a z))
    (hclose : step G before .close = some empty)
    (a0 : EdgeVector V)
    (ha0 : AffineResponseMoment G seat
      (children .close empty hclose) a0)
    (hoddCarrier : before.untouched.card % 2 = 1) :
    ∃ ladder,
      ResponseDirection G seat hroot ladder ∧
      (p + a0) +
          (is.map fun z ↦
            p + (moveLiveStar before (.open z) + a z)).sum = ladder := by
  have hlen : is.length = before.untouched.card := by
    rw [← List.toFinset_card_of_nodup his, hset]
  have hodd : is.length % 2 = 1 := by omega
  obtain ⟨ladder, hdir, hbalance⟩ :=
    hp.answer_oddFan_distinguished_exchange is
      (fun z ↦ .open z) t hstep a ha .close hclose a0 ha0 hodd
  refine ⟨ladder, hdir, ?_⟩
  simpa [moveLiveStar] using hbalance

/-- Exact predecessor of a ko-protected singleton defender node in one fixed
strategy tree.  The predecessor is attacker-controlled, has empty queue, and
its stored move is precisely the displayed `OPEN f`. -/
theorem StrategyPrefix.protectedSingleton_selectedEmptyPredecessor
    {G : SimpleGraph V} {seat : Bool} {parent : State V}
    {hroot : OddStrategy G seat (initial (V := V))}
    {parentTree : OddStrategy G seat parent} {pp : EdgeVector V}
    (hp : StrategyPrefix G seat hroot parentTree pp)
    (hturn : parent.toMove = seat)
    {f : V} (hqueue : parent.queue = [f]) (hko : parent.ko = true) :
    ∃ (empty : State V) (hatt : empty.toMove ≠ seat)
      (hopen : step G empty (.open f) = some parent)
      (pe : EdgeVector V),
      empty.queue = [] ∧
      empty.score = parent.score ∧
      parent.untouched = empty.untouched.erase f ∧
      liveSet empty = liveSet parent ∧
      StrategyPrefix G seat hroot
        (OddStrategy.choose empty hatt (.open f) parent hopen parentTree) pe ∧
      pp = pe + moveLiveStar empty (.open f) := by
  induction hp with
  | root =>
      simp [initial] at hqueue
  | @choose empty child hatt m hstep childTree pe hp0 ih =>
      cases m with
      | close =>
          simp only [step] at hstep
          split at hstep
          · contradiction
          · split at hstep
            · contradiction
            · cases hstep
              simp at hko
      | pass =>
          simp only [step] at hstep
          split at hstep
          · cases hstep
            simp at hko
          · contradiction
      | «open» v =>
          simp only [step] at hstep
          split at hstep
          · rename_i hv
            cases hstep
            have hemptyQueue : empty.queue = [] := by
              simpa using hko
            have hvf : v = f := by
              simpa [hemptyQueue] using hqueue
            subst v
            exact ⟨empty, hatt,
              by simp [step, hv], pe, hemptyQueue, rfl, rfl,
              by simp [liveSet, hemptyQueue, Finset.insert_erase hv],
              hp0, rfl⟩
          · contradiction
  | @answer empty child hdef hasMove children m hstep pe hp0 ih =>
      have hchildTurn : child.toMove = !empty.toMove := step_toMove hstep
      have : child.toMove = !seat := by rw [hchildTurn, hdef]
      exact False.elim
        ((by simp : (!seat : Bool) ≠ seat) (this.symm.trans hturn))

omit [Fintype V] in
/-- Crossing backward over the selected `OPEN f` creates no new affine
degree of freedom: the parent continuation and the empty-queue predecessor
continuation are the same point after adding the forced OPEN prefix. -/
theorem StrategyPrefix.protectedSingleton_predecessor_lift_exact
    {G : SimpleGraph V} {seat : Bool} {root empty parent : State V}
    {hroot : OddStrategy G seat root}
    {parentTree : OddStrategy G seat parent}
    {hatt : empty.toMove ≠ seat}
    {hopen : step G empty (.open f) = some parent}
    {pe pp a : EdgeVector V}
    (he : StrategyPrefix G seat hroot
      (OddStrategy.choose empty hatt (.open f) parent hopen parentTree) pe)
    (hpp : pp = pe + moveLiveStar empty (.open f))
    (ha : AffineResponseMoment G seat parentTree a) :
    AffineResponseMoment G seat hroot (pp + a) ∧
      AffineResponseMoment G seat
        (OddStrategy.choose empty hatt (.open f) parent hopen parentTree)
        (moveLiveStar empty (.open f) + a) := by
  have hempty : AffineResponseMoment G seat
      (OddStrategy.choose empty hatt (.open f) parent hopen parentTree)
      (moveLiveStar empty (.open f) + a) :=
    AffineResponseMoment.choose (hseat := hatt) (hstep := hopen) ha
  constructor
  · rw [hpp, add_assoc]
    exact he.lift hempty
  · exact hempty

omit [Fintype V] in
/-- A universal protected real front forces the isolated dummy to have been
consumed before the selected empty-queue block began. -/
theorem protected_selectedEmpty_dummy_consumed
    {G : SimpleGraph V} {d f : V} {empty parent : State V}
    (hd : IsDummy G d) (hfd : f ≠ d)
    (hU : parent.untouched = empty.untouched.erase f)
    (huniversal : ∀ z ∈ parent.untouched, G.Adj f z) :
    d ∉ empty.untouched := by
  intro hdmem
  have hdmem : d ∈ parent.untouched := by
    rw [hU]
    simp [hdmem, hfd.symm]
  have hfrontDummy : G.Adj f d := huniversal d hdmem
  exact hd f (by simpa [G.adj_comm] using hfrontDummy)

/-- Consequently the empty-queue block predecessor cannot be the initial
root, whose untouched carrier is universal. -/
theorem protected_selectedEmpty_ne_initial_of_dummy_front
    {G : SimpleGraph V} {d f : V} {empty parent : State V}
    (hd : IsDummy G d) (hfd : f ≠ d)
    (hU : parent.untouched = empty.untouched.erase f)
    (huniversal : ∀ z ∈ parent.untouched, G.Adj f z) :
    empty ≠ initial := by
  intro hempty
  have hdGone := protected_selectedEmpty_dummy_consumed
    hd hfd hU huniversal
  apply hdGone
  rw [hempty]
  simp [initial]

omit [Fintype V] in
/-- Restoring the selected block opener to an even protected carrier makes
the preceding empty-queue carrier odd. -/
theorem protectedPredecessor_card_mod_two_eq_one
    (empty parent : State V) (f : V)
    (hf : f ∈ empty.untouched)
    (hU : parent.untouched = empty.untouched.erase f)
    (heven : (parent.untouched.card : ZMod 2) = 0) :
    empty.untouched.card % 2 = 1 := by
  have hEven : Even parent.untouched.card :=
    ZMod.natCast_eq_zero_iff_even.mp heven
  obtain ⟨k, hk⟩ := hEven
  have hcard := Finset.card_erase_add_one hf
  rw [← hU, hk] at hcard
  omega

/-- Constructor-specialized form used by the two-case minimal-bad normal
form.  In the protected branch, the displayed singleton defender parent is
the selected first child of an empty-queue attacker node. -/
theorem MinimalBadPredecessorNormalCase.protectedOpen_emptyBlockStart
    {G : SimpleGraph V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    {s parent : State V} {parentTree : OddStrategy G seat parent}
    {pp : EdgeVector V} {f x : V} {q : List V}
    (hprefix : StrategyPrefix G seat root parentTree pp)
    (hturn : parent.toMove = seat)
    (hcase : MinimalBadPredecessorNormalCase G parent s f q (.open x)) :
    ∃ (empty : State V) (hatt : empty.toMove ≠ seat)
      (hopen : step G empty (.open f) = some parent)
      (pe : EdgeVector V),
      empty.queue = [] ∧ empty.score = 0 ∧
      parent.untouched = empty.untouched.erase f ∧
      liveSet empty = liveSet parent ∧
      StrategyPrefix G seat root
        (OddStrategy.choose empty hatt (.open f) parent hopen parentTree) pe ∧
      pp = pe + moveLiveStar empty (.open f) := by
  cases hcase with
  | protectedOpen x hx hqueue hko hscore hU hchildQueue hq =>
      obtain ⟨empty, hatt, hopen, pe, hempty, hscoreEq, hUeq,
          hlive, he, hpp⟩ :=
        hprefix.protectedSingleton_selectedEmptyPredecessor hturn hqueue hko
      exact ⟨empty, hatt, hopen, pe, hempty, hscoreEq.trans hscore,
        hUeq, hlive, he, hpp⟩

/-- The selected empty-queue start of a protected block is either the initial
root itself or is entered by a universal singleton-front CLOSE.  In the
second case the CLOSE has zero live-star moment, so the defender parent and
the empty-queue attacker node have exactly the same root prefix.  The entire
legal fan at that earlier defender parent remains available in the same
strategy tree. -/
theorem StrategyPrefix.selectedEmptyBlock_root_or_closeFan
    {G : SimpleGraph V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    {empty parent : State V} {parentTree : OddStrategy G seat parent}
    {hatt : empty.toMove ≠ seat}
    {hopen : step G empty (.open f) = some parent}
    {pe : EdgeVector V}
    (he : StrategyPrefix G seat root
      (OddStrategy.choose empty hatt (.open f) parent hopen parentTree) pe)
    (hempty : empty.queue = []) :
    empty = initial ∨
      ∃ (before : State V) (beforeTree : OddStrategy G seat before)
        (pb : EdgeVector V) (y : V),
        StrategyPrefix G seat root beforeTree pb ∧
        before.toMove = seat ∧ before.queue = [y] ∧
        before.ko = false ∧ step G before .close = some empty ∧
        pe = pb ∧
        (∀ m t, step G before m = some t →
          ∃ childTree : OddStrategy G seat t,
            StrategyPrefix G seat root childTree
              (pb + moveLiveStar before m)) := by
  by_cases hroot : empty = initial
  · exact Or.inl hroot
  · right
    have hturn : empty.toMove = !seat := Bool.eq_not_iff.mpr hatt
    obtain ⟨before, beforeTree, pb, incoming, hbeforePrefix,
        hbeforeTurn, hincoming, hpe, hfan⟩ :=
      he.immediate_defender_parent hturn hroot
    have hf : f ∈ empty.untouched := by
      simp only [step] at hopen
      split at hopen
      · assumption
      · contradiction
    cases incoming with
    | «open» z =>
        simp only [step] at hincoming
        split at hincoming
        · cases hincoming
          simp at hempty
        · contradiction
    | pass =>
        simp only [step] at hincoming
        split at hincoming
        · rename_i hpass
          cases hincoming
          simp [hpass.1] at hf
        · contradiction
    | close =>
        simp only [step] at hincoming
        split at hincoming
        · contradiction
        · rename_i y tail hqueue
          split at hincoming
          · contradiction
          · cases hincoming
            have htail : tail = [] := by simpa using hempty
            subst tail
            have hko : before.ko = false := by
              cases hk : before.ko with
              | false => rfl
              | true => simp [hk] at *
            refine ⟨before, beforeTree, pb, y, hbeforePrefix,
              hbeforeTurn, hqueue, hko, ?_, ?_, hfan⟩
            · simp [step, hqueue, hko]
            · simpa [moveLiveStar] using hpe

/-- Exact-child refinement of the non-root empty-block predecessor.  Unlike
an existential complete-fan interface, this retains the actual dependent
child function of the defender strategy and identifies its CLOSE child with
the supplied selected empty-queue subtree.  This identity is necessary when
transporting a particular protected continuation representative backward. -/
theorem StrategyPrefix.selectedEmptyBlock_exactCloseFan
    {G : SimpleGraph V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    {empty : State V} {emptyTree : OddStrategy G seat empty}
    {pe : EdgeVector V}
    (he : StrategyPrefix G seat root emptyTree pe)
    (hturn : empty.toMove = !seat) (hnotRoot : empty ≠ initial)
    {f : V} (hempty : empty.queue = []) (hf : f ∈ empty.untouched) :
    ∃ (before : State V) (hdef : before.toMove = seat)
      (hasMove : ∃ m u, step G before m = some u)
      (children : ∀ m u, step G before m = some u →
        OddStrategy G seat u)
      (pb : EdgeVector V) (y : V)
      (hclose : step G before .close = some empty),
      StrategyPrefix G seat root
        (OddStrategy.answer before hdef hasMove children) pb ∧
      children .close empty hclose = emptyTree ∧
      before.queue = [y] ∧ before.ko = false ∧
      before.untouched = empty.untouched ∧ pe = pb := by
  induction he with
  | root => exact False.elim (hnotRoot rfl)
  | @choose before child hatt m hstep childTree pb hp ih =>
      have hchildTurn : child.toMove = !before.toMove := step_toMove hstep
      have hbeforeTurn : before.toMove = !seat := Bool.eq_not_iff.mpr hatt
      have : child.toMove = seat := by rw [hchildTurn, hbeforeTurn]; simp
      exact False.elim
        ((by simp : (seat : Bool) ≠ !seat) (this.symm.trans hturn))
  | @answer before child hdef hasMove children m hstep pb hp ih =>
      have hstepOriginal := hstep
      cases m with
      | «open» z =>
          simp only [step] at hstep
          split at hstep
          · cases hstep
            simp at hempty
          · contradiction
      | pass =>
          simp only [step] at hstep
          split at hstep
          · rename_i hpass
            cases hstep
            simp [hpass.1] at hf
          · contradiction
      | close =>
          simp only [step] at hstep
          split at hstep
          · contradiction
          · rename_i y tail hqueue
            split at hstep
            · contradiction
            · cases hstep
              have htail : tail = [] := by simpa using hempty
              subst tail
              have hko : before.ko = false := by
                cases hk : before.ko with
                | false => rfl
                | true => simp [hk] at *
              refine ⟨before, hdef, hasMove, children, pb, y,
                hstepOriginal, hp, ?_, hqueue, hko, rfl, ?_⟩
              · rfl
              · simp [moveLiveStar]

omit [Fintype V] in
/-- Replacing a singleton CLOSE child by any OPEN sibling preserves game
rank but strictly decreases untouched-carrier size.  Thus the protected
odd-fan replacement descends in the lexicographic measure
`(rank, untouched.card)`, even though rank alone does not decrease. -/
theorem singletonClose_openSibling_lex_decrease
    {G : SimpleGraph V} {before empty opened : State V} {y z : V}
    (hqueue : before.queue = [y]) (hko : before.ko = false)
    (hz : z ∈ before.untouched)
    (hclose : step G before .close = some empty)
    (hopen : step G before (.open z) = some opened) :
    rank opened = rank empty ∧
      opened.untouched.card < empty.untouched.card := by
  have hempty : empty = {
      untouched := before.untouched
      queue := []
      ko := false
      toMove := !before.toMove
      score := before.score + flip G before.untouched y } := by
    simp [step, hqueue, hko] at hclose
    exact hclose.symm
  have hopened : opened = {
      untouched := before.untouched.erase z
      queue := [y, z]
      ko := false
      toMove := !before.toMove
      score := before.score } := by
    simp [step, hqueue, hz] at hopen
    exact hopen.symm
  rw [hempty, hopened]
  constructor
  · have hpos : 0 < before.untouched.card :=
      Finset.card_pos.mpr ⟨z, hz⟩
    simp [rank, Finset.card_erase_of_mem hz]
    omega
  · exact Finset.card_erase_lt_of_mem hz

omit [Fintype V] in
/-- An exchange `old + new = ladder` with homogeneous ladder preserves the
homogeneous response coset exactly.  It is a normalization equality, not a
contraction step. -/
theorem ResponseDirection.exchange_iff
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {h : OddStrategy G seat s} {old new ladder : EdgeVector V}
    (hladder : ResponseDirection G seat h ladder)
    (hbalance : old + new = ladder) :
    ResponseDirection G seat h old ↔ ResponseDirection G seat h new := by
  have hrecoverOld : new + ladder = old := by
    rw [← hbalance]
    ext e
    simp only [Finsupp.add_apply]
    calc
      new e + (old e + new e) = old e + (new e + new e) := by abel
      _ = old e := by rw [CharTwo.add_self_eq_zero, add_zero]
  have hrecoverNew : old + ladder = new := by
    rw [← hbalance]
    ext e
    simp only [Finsupp.add_apply]
    calc
      old e + (old e + new e) = (old e + old e) + new e := by abel
      _ = new e := by rw [CharTwo.add_self_eq_zero, zero_add]
  constructor
  · intro hold
    rw [← hrecoverNew]
    exact hold.add hladder
  · intro hnew
    rw [← hrecoverOld]
    exact hnew.add hladder

/-- A root affine response point is not itself a homogeneous response
direction. -/
theorem AffineResponseMoment.initial_not_responseDirection
    {G : SimpleGraph V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    {x : EdgeVector V}
    (hx : AffineResponseMoment G seat root x) :
    ¬ResponseDirection G seat root x := by
  intro hdirection
  have hzeroAffine : AffineResponseMoment G seat root (x + x) :=
    hx.add_direction hdirection
  have hself : x + x = 0 := by
    ext e
    exact CharTwo.add_self_eq_zero _
  rw [hself] at hzeroAffine
  exact no_zero_affineResponseMoment_initial hzeroAffine

/-- Scalar realization of the lexicographic hole measure.  The coefficient
`|V|+1` makes any rank drop dominate every possible carrier size. -/
def StrategyFactorTerm.descentMeasure
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    (t : StrategyFactorTerm G seat hroot) : Nat :=
  (Fintype.card V + 1) * rank t.hole.state +
    t.hole.state.untouched.card

/-- The paper's lexicographic descent on strategy holes. -/
def StrategyFactorTerm.LexDesc
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    (child parent : StrategyFactorTerm G seat hroot) : Prop :=
  rank child.hole.state < rank parent.hole.state ∨
    (rank child.hole.state = rank parent.hole.state ∧
      child.hole.state.untouched.card <
        parent.hole.state.untouched.card)

/-- Lexicographic hole descent strictly decreases its scalar realization. -/
theorem StrategyFactorTerm.descentMeasure_lt
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    {child parent : StrategyFactorTerm G seat hroot}
    (h : child.LexDesc parent) :
    child.descentMeasure < parent.descentMeasure := by
  have hcard : child.hole.state.untouched.card < Fintype.card V + 1 := by
    have hle : child.hole.state.untouched.card ≤ Fintype.card V := by
      simpa using Finset.card_le_card
        (Finset.subset_univ child.hole.state.untouched)
    omega
  cases h with
  | inl hrank =>
      have hmul :
          (Fintype.card V + 1) * (rank child.hole.state + 1) ≤
            (Fintype.card V + 1) * rank parent.hole.state :=
        Nat.mul_le_mul_left _ (Nat.add_one_le_iff.mpr hrank)
      unfold descentMeasure
      calc
        (Fintype.card V + 1) * rank child.hole.state +
              child.hole.state.untouched.card <
            (Fintype.card V + 1) * rank child.hole.state +
              (Fintype.card V + 1) := Nat.add_lt_add_left hcard _
        _ = (Fintype.card V + 1) * (rank child.hole.state + 1) := by
          simp [Nat.mul_add]
        _ ≤ (Fintype.card V + 1) * rank parent.hole.state := hmul
        _ ≤ (Fintype.card V + 1) * rank parent.hole.state +
              parent.hole.state.untouched.card := Nat.le_add_right _ _
  | inr hsame =>
      unfold descentMeasure
      rw [hsame.1]
      exact Nat.add_lt_add_left hsame.2 _

/-- Hence the exact strategy-hole lexicographic descent is well founded. -/
theorem StrategyFactorTerm.lexDesc_wellFounded
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root} :
    WellFounded (fun child parent : StrategyFactorTerm G seat hroot ↦
      child.LexDesc parent) := by
  apply (InvImage.wf StrategyFactorTerm.descentMeasure Nat.lt_wfRel.wf).mono
  intro child parent h
  exact StrategyFactorTerm.descentMeasure_lt h

/-- Prefix-decorated affine point represented by a strategy factor term. -/
def StrategyFactorTerm.decorated
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    (t : StrategyFactorTerm G seat hroot) : EdgeVector V :=
  t.hole.moment + t.base

/-- Aggregate decorated frontier represented by a list of factor terms. -/
def strategyDecoratedSum
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    (frontier : List (StrategyFactorTerm G seat hroot)) : EdgeVector V :=
  (frontier.map StrategyFactorTerm.decorated).sum

/-- A finite recursive odd factor expansion.  One frontier term may be
replaced by an odd family of strictly lexicographically smaller terms when
their decorated sum differs from the old decorated point by a root response
direction.  `stop` leaves a term irreducible; the inductive derivation records
an arbitrary finite schedule of replacements. -/
inductive StrategyOddFactorExpansion
    (G : SimpleGraph V) (seat : Bool) {root : State V}
    (hroot : OddStrategy G seat root) :
    List (StrategyFactorTerm G seat hroot) →
      List (StrategyFactorTerm G seat hroot) → Prop
  | stop (frontier) :
      StrategyOddFactorExpansion G seat hroot frontier frontier
  | replace (before after : List (StrategyFactorTerm G seat hroot))
      (old : StrategyFactorTerm G seat hroot)
      (news : List (StrategyFactorTerm G seat hroot))
      (hodd : news.length % 2 = 1)
      (hdesc : ∀ child ∈ news, child.LexDesc old)
      (ladder : EdgeVector V)
      (hladder : ResponseDirection G seat hroot ladder)
      (hbalance : old.decorated + strategyDecoratedSum news = ladder)
      {terminal : List (StrategyFactorTerm G seat hroot)}
      (tail : StrategyOddFactorExpansion G seat hroot
        (before ++ news ++ after) terminal) :
      StrategyOddFactorExpansion G seat hroot
        (before ++ old :: after) terminal

/-- Multiset of scalar lexicographic measures carried by one frontier. -/
def strategyFrontierMeasure
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    (frontier : List (StrategyFactorTerm G seat hroot)) : Multiset Nat :=
  frontier.map StrategyFactorTerm.descentMeasure

/-- One valid odd factor rewrite of a frontier. -/
def StrategyOddFactorRewrite
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    (hroot : OddStrategy G seat root)
    (next current : List (StrategyFactorTerm G seat hroot)) : Prop :=
  ∃ (before after : List (StrategyFactorTerm G seat hroot))
      (old : StrategyFactorTerm G seat hroot)
      (news : List (StrategyFactorTerm G seat hroot))
      (ladder : EdgeVector V),
    current = before ++ old :: after ∧
    next = before ++ news ++ after ∧
    news.length % 2 = 1 ∧
    (∀ child ∈ news, child.LexDesc old) ∧
    ResponseDirection G seat hroot ladder ∧
    old.decorated + strategyDecoratedSum news = ladder

/-- A frontier rewrite strictly decreases the Dershowitz--Manna multiset
extension of the hole measure: the one removed measure is replaced only by
strictly smaller measures. -/
theorem strategyFrontierMeasure_rewrite_lt
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    {next current : List (StrategyFactorTerm G seat hroot)}
    (h : StrategyOddFactorRewrite hroot next current) :
    Multiset.IsDershowitzMannaLT
      (strategyFrontierMeasure next) (strategyFrontierMeasure current) := by
  classical
  obtain ⟨before, after, old, news, ladder, rfl, rfl,
      hodd, hdesc, hladder, hbalance⟩ := h
  let X : Multiset Nat :=
    strategyFrontierMeasure before + strategyFrontierMeasure after
  let Y : Multiset Nat := strategyFrontierMeasure news
  let Z : Multiset Nat := {old.descentMeasure}
  refine ⟨X, Y, Z, by simp [Z], ?_, ?_, ?_⟩
  · simp [X, Y, strategyFrontierMeasure]
    exact (@List.perm_append_comm Nat
      (news.map StrategyFactorTerm.descentMeasure)
      (after.map StrategyFactorTerm.descentMeasure)).append_left
        (before.map StrategyFactorTerm.descentMeasure)
  · simp only [X, Z, strategyFrontierMeasure, List.map_append,
      List.map_cons]
    change (↑(before.map StrategyFactorTerm.descentMeasure ++
        old.descentMeasure :: after.map StrategyFactorTerm.descentMeasure) :
          Multiset Nat) =
      ↑((before.map StrategyFactorTerm.descentMeasure ++
        after.map StrategyFactorTerm.descentMeasure) ++
          [old.descentMeasure])
    rw [Multiset.coe_eq_coe]
    simpa [List.append_assoc] using
      ((@List.perm_append_comm Nat
        [old.descentMeasure]
        (after.map StrategyFactorTerm.descentMeasure)).append_left
          (before.map StrategyFactorTerm.descentMeasure))
  · intro y hy
    simp only [Y, strategyFrontierMeasure, Multiset.mem_coe,
      List.mem_map] at hy
    obtain ⟨child, hchild, rfl⟩ := hy
    refine ⟨old.descentMeasure, by simp [Z], ?_⟩
    exact StrategyFactorTerm.descentMeasure_lt (hdesc child hchild)

/-- Therefore arbitrary scheduling of valid protected odd rewrites on a
finite frontier terminates; termination does not depend on choosing a
particular leaf first. -/
theorem StrategyOddFactorRewrite.wellFounded
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    (hroot : OddStrategy G seat root) :
    WellFounded (StrategyOddFactorRewrite hroot) := by
  apply (InvImage.wf strategyFrontierMeasure
    Multiset.wellFounded_isDershowitzMannaLT).mono
  intro next current h
  exact strategyFrontierMeasure_rewrite_lt h

/-- Each recorded expansion edge really follows the well-founded scalar
measure on every newly created child. -/
theorem StrategyOddFactorExpansion.child_measure_lt
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    {old child : StrategyFactorTerm G seat hroot}
    {news : List (StrategyFactorTerm G seat hroot)}
    (hdesc : ∀ child ∈ news, child.LexDesc old)
    (hchild : child ∈ news) :
    child.descentMeasure < old.descentMeasure := by
  exact StrategyFactorTerm.descentMeasure_lt (hdesc child hchild)

omit [Fintype V] in
/-- Replacing one term by an odd family preserves parity of the complete
frontier, independently of where the term occurs. -/
theorem StrategyOddFactorExpansion.odd_terminal
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    {start terminal : List (StrategyFactorTerm G seat hroot)}
    (h : StrategyOddFactorExpansion G seat hroot start terminal)
    (hodd : start.length % 2 = 1) :
    terminal.length % 2 = 1 := by
  induction h with
  | stop => exact hodd
  | replace before after old news hnews hdesc ladder hladder hbalance tail ih =>
      apply ih
      simp only [List.length_append, List.length_cons] at hodd ⊢
      omega

omit [Fintype V] in
/-- One contextual factor replacement differs from the old frontier by the
same homogeneous ladder as the replaced term. -/
theorem strategyDecoratedSum_replace_direction
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    (before after : List (StrategyFactorTerm G seat hroot))
    (old : StrategyFactorTerm G seat hroot)
    (news : List (StrategyFactorTerm G seat hroot))
    {ladder : EdgeVector V}
    (hladder : ResponseDirection G seat hroot ladder)
    (hbalance : old.decorated + strategyDecoratedSum news = ladder) :
    ResponseDirection G seat hroot
      (strategyDecoratedSum (before ++ old :: after) +
        strategyDecoratedSum (before ++ news ++ after)) := by
  have heq :
      strategyDecoratedSum (before ++ old :: after) +
          strategyDecoratedSum (before ++ news ++ after) = ladder := by
    rw [← hbalance]
    simp only [strategyDecoratedSum, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons]
    ext e
    simp only [Finsupp.add_apply]
    let b := (before.map StrategyFactorTerm.decorated).sum e
    let a := (after.map StrategyFactorTerm.decorated).sum e
    let n := (news.map StrategyFactorTerm.decorated).sum e
    let o := old.decorated e
    change (b + (o + a)) + ((b + n) + a) = o + n
    have hb : b + b = 0 := CharTwo.add_self_eq_zero b
    have ha : a + a = 0 := CharTwo.add_self_eq_zero a
    calc
      (b + (o + a)) + ((b + n) + a) =
          (b + b) + (a + a) + (o + n) := by abel
      _ = o + n := by rw [hb, ha]; simp
  rw [heq]
  exact hladder

omit [Fintype V] in
/-- Any finite sequence of odd lex-decreasing replacements preserves exactly
whether the aggregate frontier lies in the root response-direction space. -/
theorem StrategyOddFactorExpansion.direction_iff
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    {start terminal : List (StrategyFactorTerm G seat hroot)}
    (h : StrategyOddFactorExpansion G seat hroot start terminal) :
    ResponseDirection G seat hroot (strategyDecoratedSum start) ↔
      ResponseDirection G seat hroot (strategyDecoratedSum terminal) := by
  induction h with
  | stop => exact Iff.rfl
  | replace before after old news hodd hdesc ladder hladder hbalance tail ih =>
      have hstep := strategyDecoratedSum_replace_direction
        before after old news hladder hbalance
      exact (ResponseDirection.exchange_iff hstep rfl).trans ih

/-- In particular, starting from one genuine affine root point, no finite
odd replacement expansion can end in a homogeneous frontier.  This is the
precise algebraic obstruction to obtaining the FIFO factor certificate from
the protected replacement rule alone. -/
theorem StrategyOddFactorExpansion.terminal_not_direction_of_singleton
    {G : SimpleGraph V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    (start : StrategyFactorTerm G seat root)
    {terminal : List (StrategyFactorTerm G seat root)}
    (h : StrategyOddFactorExpansion G seat root [start] terminal) :
    ¬ResponseDirection G seat root (strategyDecoratedSum terminal) := by
  intro hterminal
  have hstart : ResponseDirection G seat root
      (strategyDecoratedSum [start]) := h.direction_iff.mpr hterminal
  have haffine : AffineResponseMoment G seat root start.decorated :=
    start.hole.ancestry.lift start.base_mem
  apply haffine.initial_not_responseDirection
  simpa [strategyDecoratedSum] using hstart

/-- A non-root selected empty block with odd carrier admits the exact causal
factor replacement needed by the ancestry interface.  Any chosen response
representative of the selected CLOSE child is congruent, modulo a genuine
root response direction, to an odd list of `StrategyFactorTerm`s coming from
*all* OPEN siblings of the preceding defender fan.

The terms retain their actual dependent subtrees and root prefixes; this is
strictly stronger than merely asserting that some root affine points have the
same sum. -/
theorem StrategyPrefix.selectedEmptyBlock_oddOpenFactorReplacement
    {G : SimpleGraph V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    {empty : State V} {emptyTree : OddStrategy G seat empty}
    {pe a0 : EdgeVector V}
    (he : StrategyPrefix G seat root emptyTree pe)
    (hturn : empty.toMove = !seat) (hnotRoot : empty ≠ initial)
    {f : V} (hempty : empty.queue = []) (hf : f ∈ empty.untouched)
    (hodd : empty.untouched.card % 2 = 1)
    (ha0 : AffineResponseMoment G seat emptyTree a0) :
    ∃ (terms : List (StrategyFactorTerm G seat root))
      (ladder : EdgeVector V),
      terms.length % 2 = 1 ∧
      (∀ term ∈ terms, term.correction = 0) ∧
      (∀ term ∈ terms,
        rank term.hole.state = rank empty ∧
          term.hole.state.untouched.card < empty.untouched.card ∧
          term.hole.state.queue.length = 2 ∧
          term.hole.state.untouched.card % 2 = 0 ∧
          term.hole.state.toMove = !seat) ∧
      ResponseDirection G seat root ladder ∧
      (pe + a0) +
        (terms.map fun term ↦ term.hole.moment + term.base).sum =
          ladder := by
  classical
  obtain ⟨before, hdef, hasMove, children, pb, y, hclose,
      hp, hcloseChild, hqueue, hko, hU, hpe⟩ :=
    he.selectedEmptyBlock_exactCloseFan hturn hnotRoot hempty hf
  let I := {z : V // z ∈ before.untouched}
  let indices : List I := before.untouched.attach.toList
  let target : I → State V := fun z ↦ {
    untouched := before.untouched.erase z.1
    queue := before.queue ++ [z.1]
    ko := before.queue.isEmpty
    toMove := !before.toMove
    score := before.score }
  have hopen : ∀ z : I,
      step G before (.open z.1) = some (target z) := by
    intro z
    simp [step, target, z.2]
  let child : (z : I) → OddStrategy G seat (target z) :=
    fun z ↦ children (.open z.1) (target z) (hopen z)
  let base : I → EdgeVector V := fun z ↦
    Classical.choose (exists_affineResponseMoment (child z))
  have hbase : ∀ z : I,
      AffineResponseMoment G seat (child z) (base z) := by
    intro z
    exact Classical.choose_spec (exists_affineResponseMoment (child z))
  let term : I → StrategyFactorTerm G seat root := fun z ↦ {
    hole := {
      state := target z
      tree := child z
      moment := pb + moveLiveStar before (.open z.1)
      ancestry := StrategyPrefix.answer (hstep := hopen z) hp }
    base := base z
    correction := 0
    base_mem := hbase z
    correction_mem := ResponseDirection.zero (child z) }
  have hindices : indices.length % 2 = 1 := by
    simp [indices, I, hU, hodd]
  have ha0' : AffineResponseMoment G seat
      (children .close empty hclose) a0 := by
    rw [hcloseChild]
    exact ha0
  obtain ⟨ladder, hladder, hbalance⟩ :=
    hp.answer_oddFan_distinguished_exchange indices
      (fun z ↦ .open z.1) target (fun z _ ↦ hopen z)
      base (fun z _ ↦ hbase z) .close hclose a0 ha0' hindices
  refine ⟨indices.map term, ladder, ?_, ?_, ?_, hladder, ?_⟩
  · simpa using hindices
  · intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    rfl
  · intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    simp only [term]
    obtain ⟨hrank, hcardLt⟩ :=
      singletonClose_openSibling_lex_decrease hqueue hko z.2
        hclose (hopen z)
    refine ⟨hrank, hcardLt, ?_, ?_, ?_⟩
    · simp [target, hqueue]
    · have hcardErase := Finset.card_erase_of_mem z.2
      simp only [target]
      rw [hcardErase, hU]
      omega
    · simp [target, hdef]
  · have htermSum :
        ((indices.map term).map fun t ↦ t.hole.moment + t.base).sum =
          (indices.map fun z ↦
            pb + (moveLiveStar before (.open z.1) + base z)).sum := by
      induction indices with
      | nil => rfl
      | cons z rest ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [ih]
          simp only [term]
          abel
    rw [hpe, htermSum]
    simpa [moveLiveStar] using hbalance

/-- The concrete protected-block exchange is one step of the abstract odd
expansion calculus.  Its immediate frontier consists entirely of even-carrier
two-queue holes, so the protected empty-block rule itself cannot immediately
reapply.  The frontier nevertheless remains non-homogeneous. -/
theorem StrategyPrefix.selectedEmptyBlock_oneStepOddExpansion
    {G : SimpleGraph V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    {empty : State V} {emptyTree : OddStrategy G seat empty}
    {pe a0 : EdgeVector V}
    (he : StrategyPrefix G seat root emptyTree pe)
    (hturn : empty.toMove = !seat) (hnotRoot : empty ≠ initial)
    {f : V} (hempty : empty.queue = []) (hf : f ∈ empty.untouched)
    (hodd : empty.untouched.card % 2 = 1)
    (ha0 : AffineResponseMoment G seat emptyTree a0) :
    ∃ (old : StrategyFactorTerm G seat root)
      (terms : List (StrategyFactorTerm G seat root)),
      old.hole.state = empty ∧
      StrategyOddFactorExpansion G seat root [old] terms ∧
      (∀ term ∈ terms,
        term.hole.state.queue.length = 2 ∧
          term.hole.state.untouched.card % 2 = 0 ∧
          term.hole.state.toMove = !seat) ∧
      ¬ResponseDirection G seat root (strategyDecoratedSum terms) := by
  let old : StrategyFactorTerm G seat root := {
    hole := {
      state := empty
      tree := emptyTree
      moment := pe
      ancestry := he }
    base := a0
    correction := 0
    base_mem := ha0
    correction_mem := ResponseDirection.zero emptyTree }
  obtain ⟨terms, ladder, htermsOdd, hzero, hdecrease,
      hladder, hbalance⟩ :=
    he.selectedEmptyBlock_oddOpenFactorReplacement hturn hnotRoot
      hempty hf hodd ha0
  have hdesc : ∀ term ∈ terms, term.LexDesc old := by
    intro term hterm
    right
    exact ⟨(hdecrease term hterm).1, (hdecrease term hterm).2.1⟩
  have hbalance' : old.decorated + strategyDecoratedSum terms = ladder := by
    change (pe + a0) +
      (terms.map fun term ↦ term.hole.moment + term.base).sum = ladder
    exact hbalance
  have hexpansion : StrategyOddFactorExpansion G seat root [old] terms := by
    have htail : StrategyOddFactorExpansion G seat root
        ([] ++ terms ++ []) terms := by
      simpa using StrategyOddFactorExpansion.stop terms
    simpa using StrategyOddFactorExpansion.replace
      (hroot := root) [] [] old terms htermsOdd hdesc ladder hladder
        hbalance' htail
  refine ⟨old, terms, rfl, hexpansion, ?_, ?_⟩
  · intro term hterm
    exact ⟨(hdecrease term hterm).2.2.1,
      (hdecrease term hterm).2.2.2.1,
      (hdecrease term hterm).2.2.2.2⟩
  · exact hexpansion.terminal_not_direction_of_singleton old

end

end Ogdoad.Fifo
