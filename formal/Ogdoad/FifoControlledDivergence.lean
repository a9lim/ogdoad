import Ogdoad.FifoParitySeat
import Ogdoad.FifoParityCounterNormal
import Ogdoad.FifoSymmetry

/-!
# Controlled FIFO outcomes force a genuine policy divergence

A mover- or nonmover-controlled outcome means that one physical player can
force either terminal parity, using two possibly different policies.  After
translating the even-forcing policy by one score unit, both policies become
exact odd strategies for the same distinguished seat, rooted at states which
differ only by that score unit.

This file proves that the two score-coupled policies must eventually choose
different moves.  If every selected move agreed, the common structural play
would end at score-coupled terminal states which were both odd, impossible in
`ZMod 2`.  Moreover the first disagreement necessarily involves an `OPEN`:
`CLOSE` and `PASS` are individually unique and cannot both be legal at one
state.

For the parity-seat approach this is the exact extra structure carried by the
controlled outcome that remains to be excluded using the isolated dummy.  The
result does not itself prove that exclusion.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A certificate that two exact odd strategies on score-coupled roots first
diverge after a (possibly empty) common policy prefix.  At an attacker node
both policies select a move.  Equal selections extend the common prefix;
unequal selections are the desired divergence.  At a defender node an
arbitrary common legal reply extends both universal fans. -/
inductive ScoreCoupledDivergence (G : SimpleGraph V) (seat : Bool) :
    {s : State V} → OddStrategy G seat s →
      OddStrategy G seat (scoreTranslate 1 s) → Prop
  | here {s u₀ u₁ : State V} {hseat₀ : s.toMove ≠ seat}
      {hseat₁ : (scoreTranslate 1 s).toMove ≠ seat}
      {m₀ m₁ : Move V} {hstep₀ : step G s m₀ = some u₀}
      {hstep₁ : step G (scoreTranslate 1 s) m₁ = some u₁}
      {left : OddStrategy G seat u₀} {right : OddStrategy G seat u₁}
      (hne : m₀ ≠ m₁) :
      ScoreCoupledDivergence G seat
        (.choose s hseat₀ m₀ u₀ hstep₀ left)
        (.choose (scoreTranslate 1 s) hseat₁ m₁ u₁ hstep₁ right)
  | choose {s u : State V} {hseat₀ : s.toMove ≠ seat}
      {hseat₁ : (scoreTranslate 1 s).toMove ≠ seat}
      {m : Move V} {hstep : step G s m = some u}
      {hstep₁ : step G (scoreTranslate 1 s) m =
        some (scoreTranslate 1 u)}
      {left : OddStrategy G seat u}
      {right : OddStrategy G seat (scoreTranslate 1 u)}
      (tail : ScoreCoupledDivergence G seat left right) :
      ScoreCoupledDivergence G seat
        (.choose s hseat₀ m u hstep left)
        (.choose (scoreTranslate 1 s) hseat₁ m
          (scoreTranslate 1 u) hstep₁ right)
  | answer {s u : State V} {hseat₀ : s.toMove = seat}
      {hseat₁ : (scoreTranslate 1 s).toMove = seat}
      {hasMove₀ : ∃ m t, step G s m = some t}
      {hasMove₁ : ∃ m t, step G (scoreTranslate 1 s) m = some t}
      {children₀ : ∀ m t, step G s m = some t → OddStrategy G seat t}
      {children₁ : ∀ m t, step G (scoreTranslate 1 s) m = some t →
        OddStrategy G seat t}
      {m : Move V} {hstep : step G s m = some u}
      {hstep₁ : step G (scoreTranslate 1 s) m =
        some (scoreTranslate 1 u)}
      (tail : ScoreCoupledDivergence G seat
        (children₀ m u hstep)
        (children₁ m (scoreTranslate 1 u) hstep₁)) :
      ScoreCoupledDivergence G seat
        (.answer s hseat₀ hasMove₀ children₀)
        (.answer (scoreTranslate 1 s) hseat₁ hasMove₁ children₁)

/-- The terminal fork of a score-coupled divergence, together with the exact
common ancestry moment from each of the two roots. -/
def ScoreCoupledFork (G : SimpleGraph V) (seat : Bool)
    {root : State V} (leftRoot : OddStrategy G seat root)
    (rightRoot : OddStrategy G seat (scoreTranslate 1 root)) : Prop :=
  ∃ (state : State V) (left : OddStrategy G seat state)
    (right : OddStrategy G seat (scoreTranslate 1 state))
    (moment : EdgeVector V) (leftMove rightMove : Move V),
    StrategyPrefix G seat leftRoot left moment ∧
    StrategyPrefix G seat rightRoot right moment ∧
    left.selectedMove = some leftMove ∧
    right.selectedMove = some rightMove ∧ leftMove ≠ rightMove

omit [Fintype V] in
/-- Two exact odd policies rooted one score unit apart cannot agree at every
attacker choice.  The proof follows equal choices and arbitrary common
defender replies until the binary terminal-score contradiction appears. -/
theorem OddStrategy.scoreCoupledDivergence
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s)) :
    ScoreCoupledDivergence G seat left right := by
  induction s using (measure rank).wf.induction with
  | h s ih =>
      cases left with
      | terminal _ hterminal hscore =>
          cases right with
          | terminal _ _ htranslatedScore =>
              have hs1 : s.score = 1 :=
                zmod2_eq_one_of_ne_zero _ hscore
              exact False.elim (htranslatedScore (by
                simp [scoreTranslate, hs1, CharTwo.add_self_eq_zero]))
          | choose _ _ m t hstep _ =>
              have hterminalTranslated : Terminal (scoreTranslate 1 s) := by
                simpa [Terminal, scoreTranslate] using hterminal
              exact False.elim
                (terminal_no_step hterminalTranslated ⟨m, t, hstep⟩)
          | answer _ _ hasMove _ =>
              have hterminalTranslated : Terminal (scoreTranslate 1 s) := by
                simpa [Terminal, scoreTranslate] using hterminal
              exact False.elim (terminal_no_step hterminalTranslated hasMove)
      | choose _ hseat₀ m₀ u₀ hstep₀ leftTail =>
          cases right with
          | terminal _ hterminal _ =>
              have hterminalBase : Terminal s := by
                simpa [Terminal, scoreTranslate] using hterminal
              exact False.elim
                (terminal_no_step hterminalBase ⟨m₀, u₀, hstep₀⟩)
          | choose _ hseat₁ m₁ u₁ hstep₁ rightTail =>
              by_cases hmove : m₀ = m₁
              · subst m₁
                have hu : u₁ = scoreTranslate 1 u₀ := by
                  rw [step_scoreTranslate, hstep₀] at hstep₁
                  exact Option.some.inj hstep₁.symm
                subst u₁
                exact ScoreCoupledDivergence.choose
                  (ih u₀ (rank_step_lt hstep₀) leftTail rightTail)
              · exact ScoreCoupledDivergence.here hmove
          | answer _ hseat₁ _ _ =>
              exact False.elim (hseat₀ (by
                simpa [scoreTranslate] using hseat₁))
      | answer _ hseat₀ hasMove₀ children₀ =>
          cases right with
          | terminal _ hterminal _ =>
              have hterminalBase : Terminal s := by
                simpa [Terminal, scoreTranslate] using hterminal
              exact False.elim (terminal_no_step hterminalBase hasMove₀)
          | choose _ hseat₁ _ _ _ _ =>
              exact False.elim (hseat₁ (by
                simpa [scoreTranslate] using hseat₀))
          | answer _ hseat₁ hasMove₁ children₁ =>
              obtain ⟨m, u, hstep⟩ := hasMove₀
              have hstep₁ : step G (scoreTranslate 1 s) m =
                  some (scoreTranslate 1 u) := by
                rw [step_scoreTranslate, hstep]
                rfl
              exact ScoreCoupledDivergence.answer
                (ih u (rank_step_lt hstep)
                  (children₀ m u hstep)
                  (children₁ m (scoreTranslate 1 u) hstep₁))

omit [Fintype V] in
/-- A divergence is not merely an abstract recursive certificate: its first
unequal choices occur at score-coupled strategy nodes carrying one identical
root ancestry moment. -/
theorem ScoreCoupledDivergence.toFork
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {leftRoot : OddStrategy G seat root}
    {rightRoot : OddStrategy G seat (scoreTranslate 1 root)}
    (hdiv : ScoreCoupledDivergence G seat leftRoot rightRoot) :
    ScoreCoupledFork G seat leftRoot rightRoot := by
  have descend : ∀ {s : State V}
      {left : OddStrategy G seat s}
      {right : OddStrategy G seat (scoreTranslate 1 s)},
      ScoreCoupledDivergence G seat left right →
      ∀ {p : EdgeVector V},
        StrategyPrefix G seat leftRoot left p →
        StrategyPrefix G seat rightRoot right p →
        ScoreCoupledFork G seat leftRoot rightRoot := by
    intro s left right h
    induction h with
    | @here t u₀ u₁ hseat₀ hseat₁ m₀ m₁ hstep₀ hstep₁
        leftTail rightTail hne =>
        intro p hp₀ hp₁
        exact ⟨t, .choose t hseat₀ m₀ u₀ hstep₀ leftTail,
          .choose (scoreTranslate 1 t) hseat₁ m₁ u₁ hstep₁ rightTail,
          p, m₀, m₁, hp₀, hp₁, rfl, rfl, hne⟩
    | @choose t u hseat₀ hseat₁ m hstep hstep₁ left right tail ih =>
        intro p hp₀ hp₁
        have hpLeft : StrategyPrefix G seat leftRoot left
            (p + moveLiveStar t m) := StrategyPrefix.choose hp₀
        have hpRight : StrategyPrefix G seat rightRoot right
            (p + moveLiveStar t m) := by
          simpa [moveLiveStar, liveSet, scoreTranslate] using
            (StrategyPrefix.choose hp₁)
        exact ih hpLeft hpRight
    | @answer t u hseat₀ hseat₁ hasMove₀ hasMove₁
        children₀ children₁ m hstep hstep₁ tail ih =>
        intro p hp₀ hp₁
        have hpLeft : StrategyPrefix G seat leftRoot
            (children₀ m u hstep) (p + moveLiveStar t m) :=
          StrategyPrefix.answer hp₀
        have hpRight : StrategyPrefix G seat rightRoot
            (children₁ m (scoreTranslate 1 u) hstep₁)
            (p + moveLiveStar t m) := by
          simpa [moveLiveStar, liveSet, scoreTranslate] using
            (StrategyPrefix.answer hp₁)
        exact ih hpLeft hpRight
  exact descend hdiv StrategyPrefix.root StrategyPrefix.root

omit [Fintype V] in
/-- Two distinct legal moves at one FIFO state cannot both be drawn from the
unique non-OPEN moves.  Hence a policy divergence always contains a genuine
choice of a vertex to open. -/
theorem distinct_legal_moves_include_open
    {G : SimpleGraph V} {s u₀ u₁ : State V} {m₀ m₁ : Move V}
    (hstep₀ : step G s m₀ = some u₀)
    (hstep₁ : step G s m₁ = some u₁) (hne : m₀ ≠ m₁) :
    (∃ x, m₀ = .open x) ∨ (∃ x, m₁ = .open x) := by
  cases m₀ with
  | «open» x => exact Or.inl ⟨x, rfl⟩
  | close =>
      cases m₁ with
      | «open» x => exact Or.inr ⟨x, rfl⟩
      | close => exact False.elim (hne rfl)
      | pass =>
          simp only [step] at hstep₀ hstep₁
          split at hstep₀
          · contradiction
          · rename_i f q hqueue
            split at hstep₀
            · contradiction
            · split at hstep₁
              · rename_i hpass
                exact False.elim (by
                  exact ‹¬s.ko = true› hpass.2.2)
              · contradiction
  | pass =>
      cases m₁ with
      | «open» x => exact Or.inr ⟨x, rfl⟩
      | close =>
          simp only [step] at hstep₀ hstep₁
          split at hstep₀
          · rename_i hpass
            split at hstep₁
            · contradiction
            · rename_i f q hqueue
              exact False.elim (by
                rw [hpass.2.2] at hstep₁
                simp at hstep₁)
          · contradiction
      | pass => exact False.elim (hne rfl)

omit [Fintype V] in
/-- If one branch of a divergence opens a still-untouched label and the other
branch is not an OPEN at all, then the other branch is necessarily `CLOSE`.
The forced PASS is unavailable while that label remains untouched. -/
theorem open_and_nonopen_legal_forces_close
    {G : SimpleGraph V} {s u₁ : State V} {d : V} {m : Move V}
    (hdmem : d ∈ s.untouched)
    (hstep : step G s m = some u₁)
    (hnopen : ¬∃ x, m = .open x) : m = .close := by
  cases m with
  | «open» x => exact False.elim (hnopen ⟨x, rfl⟩)
  | close => rfl
  | pass =>
      simp only [step] at hstep
      split at hstep
      · rename_i hpass
        exact False.elim (by
          rw [hpass.1] at hdmem
          simp at hdmem)
      · contradiction

omit [Fintype V] in
/-- Away from the singleton ko wall, opening an untouched isolated dummy
commutes exactly with closing the existing FIFO front.  This is the local
diamond available when a controlled-policy divergence is `OPEN d` versus
`CLOSE`; the nonempty tail hypothesis is sharp because it keeps the ko bit
clear on the close-first branch. -/
theorem isolatedUntouched_open_close_commute
    (G : SimpleGraph V) (s : State V) (d f : V) (q : List V)
    (hqueue : s.queue = f :: q) (hq : q ≠ []) (hko : s.ko = false)
    (hdmem : d ∈ s.untouched) (hd : IsDummy G d) :
    ∃ so soc sc sco,
      step G s (.open d) = some so ∧
      step G so .close = some soc ∧
      step G s .close = some sc ∧
      step G sc (.open d) = some sco ∧
      soc = sco := by
  have hqEmpty : q.isEmpty = false := by
    cases q with
    | nil => contradiction
    | cons _ _ => rfl
  have hbit : adjacencyBit G f d = 0 := by
    simp [adjacencyBit, G.adj_comm, hd f]
  have hflip : flip G (s.untouched.erase d) f =
      flip G s.untouched f := by
    have hsplit := flip_eq_flip_erase_add (G := G) (f := f) hdmem
    rw [hbit, add_zero] at hsplit
    exact hsplit.symm
  let so : State V := {
    untouched := s.untouched.erase d
    queue := f :: (q ++ [d])
    ko := false
    toMove := !s.toMove
    score := s.score }
  let soc : State V := {
    untouched := s.untouched.erase d
    queue := q ++ [d]
    ko := false
    toMove := s.toMove
    score := s.score + flip G s.untouched f }
  let sc : State V := {
    untouched := s.untouched
    queue := q
    ko := false
    toMove := !s.toMove
    score := s.score + flip G s.untouched f }
  let sco : State V := {
    untouched := s.untouched.erase d
    queue := q ++ [d]
    ko := false
    toMove := s.toMove
    score := s.score + flip G s.untouched f }
  refine ⟨so, soc, sc, sco, ?_, ?_, ?_, ?_, rfl⟩
  · simp [step, so, hqueue, hdmem]
  · simp [step, so, soc, hflip]
  · simp [step, sc, hqueue, hko]
  · simp [step, sc, sco, hdmem, hqEmpty]

omit [Fintype V] in
/-- Exact first-fork trichotomy in the presence of a distinguished isolated
label.  The two score-coupled policies have one common ancestry vector and
their first unequal selected moves are exactly one of:

1. two distinct OPENs;
2. a real OPEN versus CLOSE;
3. dummy OPEN versus CLOSE.

In the last case the closeable queue is either a singleton (the sharp ko
wall) or the two move orders form an exact commuting diamond.  No PASS case
survives. -/
theorem ScoreCoupledDivergence.isolated_firstFork_trichotomy
    {G : SimpleGraph V} {seat : Bool} {root : State V} {d : V}
    (hd : IsDummy G d)
    {leftRoot : OddStrategy G seat root}
    {rightRoot : OddStrategy G seat (scoreTranslate 1 root)}
    (hdiv : ScoreCoupledDivergence G seat leftRoot rightRoot) :
    ∃ (t : State V) (left : OddStrategy G seat t)
      (right : OddStrategy G seat (scoreTranslate 1 t))
      (p : EdgeVector V),
      StrategyPrefix G seat leftRoot left p ∧
      StrategyPrefix G seat rightRoot right p ∧
      ((∃ x y, x ≠ y ∧ left.selectedMove = some (.open x) ∧
          right.selectedMove = some (.open y)) ∨
       (∃ x, x ≠ d ∧
          ((left.selectedMove = some (.open x) ∧
              right.selectedMove = some .close) ∨
           (left.selectedMove = some .close ∧
              right.selectedMove = some (.open x)))) ∨
       (∃ f q, t.queue = f :: q ∧ t.ko = false ∧
          ((left.selectedMove = some (.open d) ∧
              right.selectedMove = some .close) ∨
           (left.selectedMove = some .close ∧
              right.selectedMove = some (.open d))) ∧
          (q = [] ∨ ∃ so soc sc sco,
            step G t (.open d) = some so ∧
            step G so .close = some soc ∧
            step G t .close = some sc ∧
            step G sc (.open d) = some sco ∧ soc = sco))) := by
  obtain ⟨t, left, right, p, m₀, m₁, hp₀, hp₁,
      hselected₀, hselected₁, hne⟩ := hdiv.toFork
  refine ⟨t, left, right, p, hp₀, hp₁, ?_⟩
  cases left with
  | terminal _ _ _ => simp [OddStrategy.selectedMove] at hselected₀
  | answer _ _ _ _ => simp [OddStrategy.selectedMove] at hselected₀
  | choose _ hseat₀ move₀ u₀ hstep₀ tail₀ =>
      have hm₀ : move₀ = m₀ := by
        simpa [OddStrategy.selectedMove] using Option.some.inj hselected₀
      subst m₀
      cases right with
      | terminal _ _ _ => simp [OddStrategy.selectedMove] at hselected₁
      | answer _ _ _ _ => simp [OddStrategy.selectedMove] at hselected₁
      | choose _ hseat₁ move₁ u₁ hstep₁ tail₁ =>
          have hm₁ : move₁ = m₁ := by
            simpa [OddStrategy.selectedMove] using Option.some.inj hselected₁
          subst m₁
          obtain ⟨u₁base, hstep₁base, _hu₁⟩ :=
            (step_scoreTranslate_eq_some_iff G 1 t u₁ move₁).mp hstep₁
          cases move₀ with
          | «open» x =>
              cases move₁ with
              | «open» y =>
                  exact Or.inl ⟨x, y, by simpa using hne,
                    by simp [OddStrategy.selectedMove],
                    by simp [OddStrategy.selectedMove]⟩
              | close =>
                  by_cases hxd : x = d
                  · subst x
                    have hdmem : d ∈ t.untouched := by
                      simp only [step] at hstep₀
                      split at hstep₀
                      · assumption
                      · contradiction
                    cases hqueue : t.queue with
                    | nil => simp [step, hqueue] at hstep₁base
                    | cons f q =>
                        have hko : t.ko = false := by
                          cases hk : t.ko with
                          | false => rfl
                          | true => simp [step, hqueue, hk] at hstep₁base
                        refine Or.inr (Or.inr ⟨f, q, rfl, hko,
                          Or.inl ⟨by simp [OddStrategy.selectedMove],
                            by simp [OddStrategy.selectedMove]⟩, ?_⟩)
                        by_cases hq : q = []
                        · exact Or.inl hq
                        · exact Or.inr (isolatedUntouched_open_close_commute
                            G t d f q hqueue hq hko hdmem hd)
                  · exact Or.inr (Or.inl ⟨x, hxd,
                      Or.inl ⟨by simp [OddStrategy.selectedMove],
                        by simp [OddStrategy.selectedMove]⟩⟩)
              | pass =>
                  simp only [step] at hstep₀ hstep₁base
                  split at hstep₀
                  · rename_i hx
                    split at hstep₁base
                    · rename_i hpass
                      exact False.elim (by
                        rw [hpass.1] at hx
                        simp at hx)
                    · contradiction
                  · contradiction
          | close =>
              cases move₁ with
              | «open» x =>
                  by_cases hxd : x = d
                  · subst x
                    have hdmem : d ∈ t.untouched := by
                      simp only [step] at hstep₁base
                      split at hstep₁base
                      · assumption
                      · contradiction
                    cases hqueue : t.queue with
                    | nil => simp [step, hqueue] at hstep₀
                    | cons f q =>
                        have hko : t.ko = false := by
                          cases hk : t.ko with
                          | false => rfl
                          | true => simp [step, hqueue, hk] at hstep₀
                        refine Or.inr (Or.inr ⟨f, q, rfl, hko,
                          Or.inr ⟨by simp [OddStrategy.selectedMove],
                            by simp [OddStrategy.selectedMove]⟩, ?_⟩)
                        by_cases hq : q = []
                        · exact Or.inl hq
                        · exact Or.inr (isolatedUntouched_open_close_commute
                            G t d f q hqueue hq hko hdmem hd)
                  · exact Or.inr (Or.inl ⟨x, hxd,
                      Or.inr ⟨by simp [OddStrategy.selectedMove],
                        by simp [OddStrategy.selectedMove]⟩⟩)
              | close => exact False.elim (hne rfl)
              | pass =>
                  simp only [step] at hstep₀ hstep₁base
                  split at hstep₀
                  · contradiction
                  · rename_i f q hqueue
                    split at hstep₀
                    · contradiction
                    · split at hstep₁base
                      · rename_i hpass
                        exact False.elim (by
                          exact ‹¬t.ko = true› hpass.2.2)
                      · contradiction
          | pass =>
              cases move₁ with
              | «open» x =>
                  simp only [step] at hstep₀
                  split at hstep₀
                  · rename_i hpass
                    have hx : x ∈ t.untouched := by
                      simp only [step] at hstep₁base
                      split at hstep₁base
                      · assumption
                      · contradiction
                    exact False.elim (by
                      rw [hpass.1] at hx
                      simp at hx)
                  · contradiction
              | close =>
                  simp only [step] at hstep₀ hstep₁base
                  split at hstep₀
                  · rename_i hpass
                    split at hstep₁base
                    · contradiction
                    · rename_i f q hqueue
                      rw [hpass.2.2] at hstep₁base
                      simp at hstep₁base
                  · contradiction
              | pass => exact False.elim (hne rfl)

/-! ## Join with the minimal-bad ancestry normal form -/

/-- The exact minimal-bad data needed to compare a controlled policy fork
with the strategy-relative charged/protected normal form. -/
structure ControlledBadNormalWitness (G : SimpleGraph V) (d : V)
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
  normalCase : MinimalBadPredecessorNormalCase
    G parent state front tail incoming

/-- Package the existing lexicographically minimal bad-ancestry theorem in a
reusable witness type.  No parity-seat assertion is added here. -/
theorem OddStrategy.nonempty_controlledBadNormalWitness
    {G : SimpleGraph V} {d : V} {seat : Bool}
    (hd : IsDummy G d)
    (root : OddStrategy G seat (initial (V := V))) :
    Nonempty (ControlledBadNormalWitness G d seat root) := by
  classical
  obtain ⟨s, tree, p, parent, parentTree, pp, incoming, f, q, sc,
      hp, hpp, hparentTurn, hincoming, hmoment, hfan, hs0, hturn,
      hqueue, hko, hclose, hflip, hfreal, hselected, hneutral, hnormal⟩ :=
    root.extract_minimalBad_predecessor_normalCases hd
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
    normalCase := hnormal }⟩

omit [Fintype V] in
/-- Defender-controlled exact odd-strategy nodes store no selected move.
This is the polarity reason a protected predecessor cannot itself be the
first fork of two score-coupled attacker policies. -/
theorem OddStrategy.selectedMove_eq_none_of_turn_eq_seat
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (strategy : OddStrategy G seat s) (hturn : s.toMove = seat) :
    strategy.selectedMove = none := by
  cases strategy with
  | terminal _ _ _ => rfl
  | choose _ hseat _ _ _ _ => exact False.elim (hseat hturn)
  | answer _ _ _ _ => rfl

/-- The predecessor exported by the minimal-bad normal form is universal,
not a selected-policy fork.  This holds in both the charged and protected
normal cases. -/
theorem ControlledBadNormalWitness.parent_selectedMove_eq_none
    {G : SimpleGraph V} {d : V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    (w : ControlledBadNormalWitness G d seat root) :
    w.parentTree.selectedMove = none :=
  w.parentTree.selectedMove_eq_none_of_turn_eq_seat w.parentTurn

omit [Fintype V] in
/-- An OPEN-indexed minimal-bad predecessor is necessarily protected, and its
bad-queue tail is the singleton containing that opened label. -/
theorem MinimalBadPredecessorNormalCase.tail_nonempty_of_incoming_open
    {G : SimpleGraph V} {parent child : State V} {f : V} {q : List V}
    {incoming : Move V}
    (h : MinimalBadPredecessorNormalCase G parent child f q incoming)
    {x : V} (hincoming : incoming = .open x) : q ≠ [] := by
  cases h with
  | chargedClose => simp at hincoming
  | protectedOpen y hy hqueue hko hscore hU hchildQueue hq =>
      rw [hq]
      simp

/-- The protected alternative always has a nonempty bad-queue tail: its bad
state is exactly `[front,x]`.  Hence protected ancestry is not the singleton
queue wall. -/
theorem ControlledBadNormalWitness.protected_tail_nonempty
    {G : SimpleGraph V} {d : V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    (w : ControlledBadNormalWitness G d seat root)
    {x : V} (hincoming : w.incoming = .open x) :
    w.tail ≠ [] :=
  w.normalCase.tail_nonempty_of_incoming_open hincoming

/-- The bad state still has an untouched neighbour of its charged real
front, so its root-to-node path is before the forced PASS and satisfies the
queue/turn invariant. -/
theorem ControlledBadNormalWitness.queueTurnParity
    {G : SimpleGraph V} {d : V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    (w : ControlledBadNormalWitness G d seat root) :
    QueueTurnParity w.state := by
  exact w.ancestry.queueTurnParity_of_untouched_nonempty
    (untouched_nonempty_of_flip_eq_one w.charged)

/-- For distinguished seat `false`, the minimal bad node belongs to physical
player `true`; its queue therefore has odd length. -/
theorem ControlledBadNormalWitness.falseSeat_queue_odd
    {G : SimpleGraph V} {d : V}
    {root : OddStrategy G false (initial (V := V))}
    (w : ControlledBadNormalWitness G d false root) :
    w.state.queue.length % 2 = 1 := by
  have h := w.queueTurnParity
  simpa [QueueTurnParity, w.turn] using h

/-- For distinguished seat `true`, the controlled minimum has even queue
length.  This is why the protected two-cell case survives on this side. -/
theorem ControlledBadNormalWitness.trueSeat_queue_even
    {G : SimpleGraph V} {d : V}
    {root : OddStrategy G true (initial (V := V))}
    (w : ControlledBadNormalWitness G d true root) :
    w.state.queue.length % 2 = 0 := by
  have h := w.queueTurnParity
  simpa [QueueTurnParity, w.turn] using h

omit [Fintype V] in
/-- An odd bad queue rules out the protected two-cell state and forces the
charged-CLOSE predecessor alternative. -/
theorem MinimalBadPredecessorNormalCase.chargedClose_of_queue_odd
    {G : SimpleGraph V} {parent child : State V} {f : V} {q : List V}
    {incoming : Move V}
    (h : MinimalBadPredecessorNormalCase G parent child f q incoming)
    (_hqueue : child.queue = f :: q)
    (hodd : child.queue.length % 2 = 1) :
    ∃ y, incoming = .close ∧ parent.queue = y :: f :: q ∧
      parent.ko = false ∧ parent.untouched = child.untouched ∧
      parent.score = 1 ∧ flip G parent.untouched y = 1 := by
  cases h with
  | chargedClose y hparentQueue hparentKo hparentU hparentScore hcharge =>
      exact ⟨y, rfl, hparentQueue, hparentKo, hparentU,
        hparentScore, hcharge⟩
  | protectedOpen x hx hparentQueue hparentKo hparentScore hchildU
      hchildQueue htail =>
      have hlen : child.queue.length = 2 := by simp [hchildQueue]
      rw [hlen] at hodd
      norm_num at hodd

omit [Fintype V] in
/-- A singleton bad queue cannot have protected ancestry, whose tail is a
singleton.  Thus the sharp singleton wall always lies in the charged-CLOSE
normal case. -/
theorem MinimalBadPredecessorNormalCase.chargedClose_of_tail_empty
    {G : SimpleGraph V} {parent child : State V} {f : V} {q : List V}
    {incoming : Move V}
    (h : MinimalBadPredecessorNormalCase G parent child f q incoming)
    (hq : q = []) :
    ∃ y, incoming = .close ∧ parent.queue = y :: f :: q ∧
      parent.ko = false ∧ parent.untouched = child.untouched ∧
      parent.score = 1 ∧ flip G parent.untouched y = 1 := by
  cases h with
  | chargedClose y hparentQueue hparentKo hparentU hparentScore hcharge =>
      exact ⟨y, rfl, hparentQueue, hparentKo, hparentU,
        hparentScore, hcharge⟩
  | protectedOpen x hx hparentQueue hparentKo hparentScore hchildU
      hchildQueue htail =>
      rw [htail] at hq
      simp at hq

/-- At the left policy's selected charged CLOSE, any unequal selected move of
the score-coupled right policy is necessarily an OPEN.  PASS is impossible
because the unit charge certifies a nonempty untouched carrier. -/
theorem ControlledBadNormalWitness.unequal_rightMove_is_open
    {G : SimpleGraph V} {d : V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    (w : ControlledBadNormalWitness G d seat root)
    (right : OddStrategy G seat (scoreTranslate 1 w.state))
    (m : Move V) (hselected : right.selectedMove = some m)
    (hne : m ≠ .close) :
    ∃ x t, right.selectedMove = some (.open x) ∧
      step G w.state (.open x) = some t := by
  cases right with
  | terminal _ _ _ => simp [OddStrategy.selectedMove] at hselected
  | answer _ _ _ _ => simp [OddStrategy.selectedMove] at hselected
  | choose _ hseat move u hstep tail =>
      have hm : move = m := by
        simpa [OddStrategy.selectedMove] using Option.some.inj hselected
      subst m
      obtain ⟨t, hstepBase, _hu⟩ :=
        (step_scoreTranslate_eq_some_iff G 1 w.state u move).mp hstep
      cases move with
      | «open» x =>
          exact ⟨x, t, by simp [OddStrategy.selectedMove], hstepBase⟩
      | close => exact False.elim (hne rfl)
      | pass =>
          have hU : w.state.untouched.Nonempty :=
            untouched_nonempty_of_flip_eq_one w.charged
          simp only [step] at hstepBase
          split at hstepBase
          · rename_i hpass
            exact False.elim (by
              rw [hpass.1] at hU
              simp at hU)
          · contradiction

omit [Fintype V] in
/-- A score-coupled pair is exactly a controlled outcome.  The odd policy
shows that `seat` cannot force even, while translating the right odd policy
back by one shows that `!seat` can force even.  Which controlled class this
is depends only on the public mover bit. -/
theorem scoreCoupledPair_controlled
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s)) :
    (s.toMove = seat → NonmoverControlled G s) ∧
    (s.toMove = !seat → MoverControlled G s) := by
  have hnot : ¬EvenWins G seat s :=
    (oddWins_iff_not_evenWins G seat s).mp left.toOddWins
  have heven : EvenWins G (!seat) s := by
    have htranslated := right.toOddWins.scoreTranslate_one
    simpa [scoreTranslate_one_involutive] using htranslated
  constructor
  · intro hturn
    exact ⟨by simpa [MoverEvenWins, hturn] using hnot,
      by simpa [NonmoverEvenWins, hturn] using heven⟩
  · intro hturn
    exact ⟨by simpa [MoverEvenWins, hturn] using heven,
      by simpa [NonmoverEvenWins, hturn] using hnot⟩

omit [Fintype V] in
/-- If the two coupled attacker policies select the same move, their child
policies remain score-coupled and therefore give a strictly lower-rank
controlled outcome.  Thus repeating the minimal bad CLOSE is descent, not a
local contradiction. -/
theorem scoreCoupledPair_same_selectedMove_descends_controlled
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (m : Move V) (hleft : left.selectedMove = some m)
    (hright : right.selectedMove = some m) :
    ∃ t, step G s m = some t ∧ rank t < rank s ∧
      NonmoverControlled G t := by
  cases left with
  | terminal _ _ _ => simp [OddStrategy.selectedMove] at hleft
  | answer _ _ _ _ => simp [OddStrategy.selectedMove] at hleft
  | choose _ hseat₀ move₀ t hstep₀ leftTail =>
      have hm₀ : move₀ = m := by
        simpa [OddStrategy.selectedMove] using Option.some.inj hleft
      subst move₀
      cases right with
      | terminal _ _ _ => simp [OddStrategy.selectedMove] at hright
      | answer _ _ _ _ => simp [OddStrategy.selectedMove] at hright
      | choose _ hseat₁ move₁ u hstep₁ rightTail =>
          have hm₁ : move₁ = m := by
            simpa [OddStrategy.selectedMove] using Option.some.inj hright
          subst move₁
          have htranslated : step G (scoreTranslate 1 s) m =
              some (scoreTranslate 1 t) := by
            rw [step_scoreTranslate, hstep₀]
            rfl
          have hu : u = scoreTranslate 1 t := by
            rw [htranslated] at hstep₁
            exact Option.some.inj hstep₁.symm
          subst u
          have hcontrolled := scoreCoupledPair_controlled leftTail rightTail
          have hsTurn : s.toMove = !seat := Bool.eq_not_iff.mpr hseat₀
          have htTurn : t.toMove = seat := by
            rw [step_toMove hstep₀, hsTurn]
            simp
          exact ⟨t, hstep₀, rank_step_lt hstep₀,
            hcontrolled.1 htTurn⟩

omit [Fintype V] in
/-- Dually, at a score-coupled defender node every legal child remains
score-coupled and is mover-controlled.  Thus controlled classes alternate
along every common transition. -/
theorem scoreCoupledPair_answerChild_moverControlled
    {G : SimpleGraph V} {seat : Bool} {s t : State V}
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = seat) {m : Move V}
    (hstep : step G s m = some t) :
    MoverControlled G t := by
  cases left with
  | terminal _ hterminal _ =>
      exact False.elim (terminal_no_step hterminal ⟨m, t, hstep⟩)
  | choose _ hseat _ _ _ _ => exact False.elim (hseat hturn)
  | answer _ hseat₀ hasMove₀ children₀ =>
      cases right with
      | terminal _ hterminal _ =>
          have hstepTranslated : step G (scoreTranslate 1 s) m =
              some (scoreTranslate 1 t) := by
            rw [step_scoreTranslate, hstep]
            rfl
          exact False.elim (terminal_no_step hterminal
            ⟨m, scoreTranslate 1 t, hstepTranslated⟩)
      | choose _ hseat _ _ _ _ =>
          exact False.elim (hseat (by simpa [scoreTranslate] using hturn))
      | answer _ hseat₁ hasMove₁ children₁ =>
          have hstepTranslated : step G (scoreTranslate 1 s) m =
              some (scoreTranslate 1 t) := by
            rw [step_scoreTranslate, hstep]
            rfl
          have hcontrolled := scoreCoupledPair_controlled
            (children₀ m t hstep)
            (children₁ m (scoreTranslate 1 t) hstepTranslated)
          have htTurn : t.toMove = !seat := by
            rw [step_toMove hstep, hturn]
          exact hcontrolled.2 htTurn

omit [Fintype V] in
/-- If two score-coupled attacker policies select different first moves and
the crossed defender replies reconverge, the common endpoint is again
controlled.  This is the abstract commuting-fork descent used to eliminate
dummy OPEN/CLOSE squares at a rank-minimal controlled state. -/
theorem scoreCoupledPair_commuting_selectedMoves_descend
    {G : SimpleGraph V} {seat : Bool} {s so sc soc sco : State V}
    {m₀ m₁ : Move V}
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hleft : left.selectedMove = some m₀)
    (hright : right.selectedMove = some m₁)
    (hstep₀ : step G s m₀ = some so)
    (hstep₁ : step G s m₁ = some sc)
    (hcross₀ : step G so m₁ = some soc)
    (hcross₁ : step G sc m₀ = some sco)
    (heq : soc = sco) :
    rank soc < rank s ∧
      (MoverControlled G soc ∨ NonmoverControlled G soc) := by
  cases left with
  | terminal _ hterminal _ =>
      exact False.elim (terminal_no_step hterminal ⟨m₀, so, hstep₀⟩)
  | answer _ hseat _ _ =>
      exact False.elim (by
        rw [hturn] at hseat
        simp at hseat)
  | choose _ hseat₀ move₀ u₀ hchosen₀ leftTail =>
      have hm₀ : move₀ = m₀ := by
        simpa [OddStrategy.selectedMove] using Option.some.inj hleft
      subst move₀
      have hu₀ : u₀ = so := by
        rw [hstep₀] at hchosen₀
        exact Option.some.inj hchosen₀.symm
      subst u₀
      cases right with
      | terminal _ _ _ => simp [OddStrategy.selectedMove] at hright
      | answer _ _ _ _ => simp [OddStrategy.selectedMove] at hright
      | choose _ hseat₁ move₁ u₁ hchosen₁ rightTail =>
          have hm₁ : move₁ = m₁ := by
            simpa [OddStrategy.selectedMove] using Option.some.inj hright
          subst move₁
          have htranslatedStep : step G (scoreTranslate 1 s) m₁ =
              some (scoreTranslate 1 sc) := by
            rw [step_scoreTranslate, hstep₁]
            rfl
          have hu₁ : u₁ = scoreTranslate 1 sc := by
            rw [htranslatedStep] at hchosen₁
            exact Option.some.inj hchosen₁.symm
          subst u₁
          have hsoTurn : so.toMove = seat := by
            rw [step_toMove hstep₀, hturn]
            simp
          have hscTurn : (scoreTranslate 1 sc).toMove = seat := by
            have : sc.toMove = seat := by
              rw [step_toMove hstep₁, hturn]
              simp
            simpa [scoreTranslate] using this
          have leftCross : OddStrategy G seat soc := by
            cases leftTail with
            | terminal _ hterminal _ =>
                exact False.elim
                  (terminal_no_step hterminal ⟨m₁, soc, hcross₀⟩)
            | choose _ hseat _ _ _ _ =>
                exact False.elim (hseat hsoTurn)
            | answer _ _ _ children => exact children m₁ soc hcross₀
          have hcross₁Translated :
              step G (scoreTranslate 1 sc) m₀ =
                some (scoreTranslate 1 sco) := by
            rw [step_scoreTranslate, hcross₁]
            rfl
          have rightCross :
              OddStrategy G seat (scoreTranslate 1 sco) := by
            cases rightTail with
            | terminal _ hterminal _ =>
                exact False.elim (terminal_no_step hterminal
                  ⟨m₀, scoreTranslate 1 sco, hcross₁Translated⟩)
            | choose _ hseat _ _ _ _ =>
                exact False.elim (hseat hscTurn)
            | answer _ _ _ children =>
                exact children m₀ (scoreTranslate 1 sco) hcross₁Translated
          subst sco
          have hcontrolled := scoreCoupledPair_controlled leftCross rightCross
          have hrank : rank soc < rank s :=
            lt_trans (rank_step_lt hcross₀) (rank_step_lt hstep₀)
          by_cases hsocTurn : soc.toMove = seat
          · exact ⟨hrank, Or.inr (hcontrolled.1 hsocTurn)⟩
          · have hsocTurn' : soc.toMove = !seat :=
              Bool.eq_not_iff.mpr hsocTurn
            exact ⟨hrank, Or.inl (hcontrolled.2 hsocTurn')⟩

omit [Fintype V] in
/-- A rank-minimal controlled state cannot contain a score-coupled selected
commuting fork, because the crossed endpoint would be a smaller controlled
state. -/
theorem minimalControlled_no_commuting_scoreCoupledFork
    {G : SimpleGraph V} {seat : Bool} {s so sc soc sco : State V}
    {m₀ m₁ : Move V}
    (hminimal : ∀ {t : State V}, rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hleft : left.selectedMove = some m₀)
    (hright : right.selectedMove = some m₁)
    (hstep₀ : step G s m₀ = some so)
    (hstep₁ : step G s m₁ = some sc)
    (hcross₀ : step G so m₁ = some soc)
    (hcross₁ : step G sc m₀ = some sco)
    (heq : soc = sco) : False := by
  obtain ⟨hrank, hcontrolled⟩ :=
    scoreCoupledPair_commuting_selectedMoves_descend
      left right hturn hleft hright hstep₀ hstep₁ hcross₀ hcross₁ heq
  rcases hcontrolled with hmover | hnonmover
  · exact (hminimal hrank).1 hmover
  · exact (hminimal hrank).2 hnonmover

omit [Fintype V] in
/-- In particular a rank-minimal controlled state cannot have its two
score-coupled policies select `OPEN d` and `CLOSE` in opposite orders when
`d` is isolated and the queue has a nonempty tail.  Only the singleton ko
wall can evade the commuting descent. -/
theorem minimalControlled_no_dummyOpenClose_awaySingleton
    {G : SimpleGraph V} {seat : Bool} {s : State V} {d f : V}
    {q : List V}
    (hminimal : ∀ {t : State V}, rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hqueue : s.queue = f :: q) (hq : q ≠ []) (hko : s.ko = false)
    (hdmem : d ∈ s.untouched) (hd : IsDummy G d) :
    ¬((left.selectedMove = some (.open d) ∧
          right.selectedMove = some .close) ∨
      (left.selectedMove = some .close ∧
          right.selectedMove = some (.open d))) := by
  obtain ⟨so, soc, sc, sco, hopen, hopenClose, hclose, hcloseOpen, heq⟩ :=
    isolatedUntouched_open_close_commute
      G s d f q hqueue hq hko hdmem hd
  rintro (hforward | hreverse)
  · exact minimalControlled_no_commuting_scoreCoupledFork
      hminimal left right hturn hforward.1 hforward.2
      hopen hclose hopenClose hcloseOpen heq
  · exact minimalControlled_no_commuting_scoreCoupledFork
      hminimal left right hturn hreverse.1 hreverse.2
      hclose hopen hcloseOpen hopenClose heq.symm

omit [Fintype V] in
/-- More generally, an away-singleton real OPEN/CLOSE fork at a rank-minimal
controlled state must open a neighbour of the current front.  If the
adjacency bit were zero, the ordinary OPEN/CLOSE square would reconverge
without score curvature and produce a smaller controlled endpoint. -/
theorem minimalControlled_openClose_awaySingleton_adjacent
    {G : SimpleGraph V} {seat : Bool} {s : State V} {f z : V}
    {q : List V}
    (hminimal : ∀ {t : State V}, rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hqueue : s.queue = f :: q) (hq : q ≠ []) (hko : s.ko = false)
    (hz : z ∈ s.untouched)
    (hfork :
      (left.selectedMove = some (.open z) ∧
          right.selectedMove = some .close) ∨
      (left.selectedMove = some .close ∧
          right.selectedMove = some (.open z))) :
    adjacencyBit G f z = 1 := by
  by_contra hne
  have hbit : adjacencyBit G f z = 0 := by
    exact zmod2_eq_zero_of_ne_one _ hne
  obtain ⟨so, soc, sc, sco, hopen, hopenClose, hclose, hcloseOpen,
      hU, hqueueEq, hkoEq, hturnEq, hscoreEq⟩ :=
    open_close_square_away_singleton G s f z q hqueue hq hko hz
  have heq : soc = sco := by
    obtain ⟨socU, socQ, socKo, socTurn, socScore⟩ := soc
    obtain ⟨scoU, scoQ, scoKo, scoTurn, scoScore⟩ := sco
    simp only at hU hqueueEq hkoEq hturnEq hscoreEq hbit ⊢
    subst scoU
    subst scoQ
    subst scoKo
    subst scoTurn
    rw [hbit, add_zero] at hscoreEq
    subst scoScore
    rfl
  rcases hfork with hforward | hreverse
  · exact minimalControlled_no_commuting_scoreCoupledFork
      hminimal left right hturn hforward.1 hforward.2
      hopen hclose hopenClose hcloseOpen heq
  · exact minimalControlled_no_commuting_scoreCoupledFork
      hminimal left right hturn hreverse.1 hreverse.2
      hclose hopen hcloseOpen hopenClose heq.symm

omit [Fintype V] in
/-- At a rank-minimal controlled state, any exact score-coupled attacker
policy pair must disagree immediately.  This retains the actual policies and
selected moves, unlike the policy-free outcome recursion, so local commuting
diamonds can be applied to the fork. -/
theorem minimalControlled_scoreCoupled_currentFork
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (hminimal : ∀ {t : State V}, rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat) :
    ∃ (u₀ u₁ : State V) (m₀ m₁ : Move V),
      left.selectedMove = some m₀ ∧ right.selectedMove = some m₁ ∧
      step G s m₀ = some u₀ ∧ step G s m₁ = some u₁ ∧ m₀ ≠ m₁ := by
  have hmover : MoverControlled G s :=
    (scoreCoupledPair_controlled left right).2 hturn
  cases left with
  | terminal _ hterminal hoddScore =>
      cases hmover.1 with
      | terminal _ _ hevenScore => exact False.elim (hoddScore hevenScore)
      | choose _ _ m t hstep _ =>
          exact False.elim (terminal_no_step hterminal ⟨m, t, hstep⟩)
      | answer _ _ hasMove _ =>
          exact False.elim (terminal_no_step hterminal hasMove)
  | answer _ hseat _ _ =>
      exact False.elim (by
        have hne : s.toMove ≠ seat := by rw [hturn]; simp
        exact hne hseat)
  | choose _ hseat₀ m₀ u₀ hstep₀ leftTail =>
      cases right with
      | terminal _ hterminal _ =>
          have hterminalBase : Terminal s := by
            simpa [Terminal, scoreTranslate] using hterminal
          exact False.elim
            (terminal_no_step hterminalBase ⟨m₀, u₀, hstep₀⟩)
      | answer _ hseat₁ _ _ =>
          exact False.elim (by
            have hbaseSeat : s.toMove = seat := by
              simpa [scoreTranslate] using hseat₁
            have hne : s.toMove ≠ seat := by rw [hturn]; simp
            exact hne hbaseSeat)
      | choose _ hseat₁ m₁ u₁ hstep₁ rightTail =>
          obtain ⟨u₁base, hstep₁base, _hu₁⟩ :=
            (step_scoreTranslate_eq_some_iff G 1 s u₁ m₁).mp hstep₁
          by_cases hmove : m₀ = m₁
          · subst m₁
            have hleftSelected :
                (OddStrategy.choose s hseat₀ m₀ u₀ hstep₀ leftTail).selectedMove =
                  some m₀ := rfl
            have hrightSelected :
                (OddStrategy.choose (scoreTranslate 1 s) hseat₁ m₀ u₁ hstep₁
                  rightTail).selectedMove = some m₀ := rfl
            obtain ⟨t, _hstep, hrank, hcontrolled⟩ :=
              scoreCoupledPair_same_selectedMove_descends_controlled
                (OddStrategy.choose s hseat₀ m₀ u₀ hstep₀ leftTail)
                (OddStrategy.choose (scoreTranslate 1 s) hseat₁ m₀ u₁ hstep₁
                  rightTail)
                m₀ hleftSelected hrightSelected
            exact False.elim ((hminimal hrank).2 hcontrolled)
          · exact ⟨u₀, u₁base, m₀, m₁, rfl, rfl,
              hstep₀, hstep₁base, hmove⟩

omit [Fintype V] in
/-- Exact away-singleton shape theorem for a rank-minimal controlled fork
with an untouched isolated dummy.  The two score-coupled policies either
select two distinct OPENs, or select CLOSE against a real OPEN which is
forced to be adjacent to the current front.  In particular neither a PASS
fork nor an OPEN-d/CLOSE fork survives. -/
theorem minimalControlled_isolated_awaySingleton_currentFork_shapes
    {G : SimpleGraph V} {seat : Bool} {s : State V} {d f : V}
    {q : List V}
    (hminimal : ∀ {t : State V}, rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hqueue : s.queue = f :: q) (hq : q ≠ []) (hko : s.ko = false)
    (hdmem : d ∈ s.untouched) (hd : IsDummy G d) :
    ∃ (u₀ u₁ : State V) (m₀ m₁ : Move V),
      left.selectedMove = some m₀ ∧ right.selectedMove = some m₁ ∧
      step G s m₀ = some u₀ ∧ step G s m₁ = some u₁ ∧
      ((∃ x y, x ≠ y ∧ m₀ = .open x ∧ m₁ = .open y) ∨
       (∃ z, z ≠ d ∧ adjacencyBit G f z = 1 ∧
          ((m₀ = .open z ∧ m₁ = .close) ∨
           (m₀ = .close ∧ m₁ = .open z)))) := by
  obtain ⟨u₀, u₁, m₀, m₁, hleft, hright, hstep₀, hstep₁, hne⟩ :=
    minimalControlled_scoreCoupled_currentFork hminimal left right hturn
  refine ⟨u₀, u₁, m₀, m₁, hleft, hright, hstep₀, hstep₁, ?_⟩
  obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ :=
    distinct_legal_moves_include_open hstep₀ hstep₁ hne
  · by_cases hopen₁ : ∃ y, m₁ = .open y
    · obtain ⟨y, rfl⟩ := hopen₁
      exact Or.inl ⟨x, y, by simpa using hne, rfl, rfl⟩
    · have hm₁ : m₁ = .close :=
        open_and_nonopen_legal_forces_close hdmem hstep₁ hopen₁
      subst m₁
      have hxd : x ≠ d := by
        intro hxd
        subst x
        exact minimalControlled_no_dummyOpenClose_awaySingleton
          hminimal left right hturn hqueue hq hko hdmem hd
          (Or.inl ⟨hleft, hright⟩)
      have hadj : adjacencyBit G f x = 1 :=
        minimalControlled_openClose_awaySingleton_adjacent
          hminimal left right hturn hqueue hq hko
          (by
            simp only [step] at hstep₀
            split at hstep₀
            · assumption
            · contradiction)
          (Or.inl ⟨hleft, hright⟩)
      exact Or.inr ⟨x, hxd, hadj, Or.inl ⟨rfl, rfl⟩⟩
  · by_cases hopen₀ : ∃ y, m₀ = .open y
    · obtain ⟨y, rfl⟩ := hopen₀
      exact Or.inl ⟨y, x, by simpa using hne, rfl, rfl⟩
    · have hm₀ : m₀ = .close :=
        open_and_nonopen_legal_forces_close hdmem hstep₀ hopen₀
      subst m₀
      have hxd : x ≠ d := by
        intro hxd
        subst x
        exact minimalControlled_no_dummyOpenClose_awaySingleton
          hminimal left right hturn hqueue hq hko hdmem hd
          (Or.inr ⟨hleft, hright⟩)
      have hadj : adjacencyBit G f x = 1 :=
        minimalControlled_openClose_awaySingleton_adjacent
          hminimal left right hturn hqueue hq hko
          (by
            simp only [step] at hstep₁
            split at hstep₁
            · assumption
            · contradiction)
          (Or.inr ⟨hleft, hright⟩)
      exact Or.inr ⟨x, hxd, hadj, Or.inr ⟨rfl, rfl⟩⟩

/-- At a minimal bad node, a coupled right policy which repeats the selected
CLOSE therefore exports a smaller controlled state at the close child. -/
theorem ControlledBadNormalWitness.rightClose_descends_controlled
    {G : SimpleGraph V} {d : V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    (w : ControlledBadNormalWitness G d seat root)
    (right : OddStrategy G seat (scoreTranslate 1 w.state))
    (hright : right.selectedMove = some .close) :
    rank w.closeChild < rank w.state ∧
      NonmoverControlled G w.closeChild := by
  obtain ⟨t, hstep, hrank, hcontrolled⟩ :=
    scoreCoupledPair_same_selectedMove_descends_controlled
      w.tree right .close w.selectedClose hright
  have ht : t = w.closeChild := by
    rw [w.closeStep] at hstep
    exact Option.some.inj hstep.symm
  subst t
  exact ⟨hrank, hcontrolled⟩

/-- Exact local join of the score-coupled first-fork analysis with the
minimal-bad normal form.  If the two policies first disagree at the bad node,
the right move is an OPEN.  It is either real, or it opens the dummy.  A
dummy fork is either the sharp singleton wall, which is necessarily
charged-CLOSE ancestry, or lies in an exact OPEN-d/CLOSE commuting diamond.
In particular protected ancestry can occur only in the commuting region. -/
theorem ControlledBadNormalWitness.immediateFork_trichotomy
    {G : SimpleGraph V} {d : V} {seat : Bool}
    {root : OddStrategy G seat (initial (V := V))}
    (hd : IsDummy G d)
    (w : ControlledBadNormalWitness G d seat root)
    (right : OddStrategy G seat (scoreTranslate 1 w.state))
    (m : Move V) (hselected : right.selectedMove = some m)
    (hne : m ≠ .close) :
    (∃ x t, x ≠ d ∧ right.selectedMove = some (.open x) ∧
      step G w.state (.open x) = some t) ∨
    (∃ t y, w.tail = [] ∧
      right.selectedMove = some (.open d) ∧
      step G w.state (.open d) = some t ∧
      w.incoming = .close ∧
      w.parent.queue = y :: w.front :: w.tail ∧
      w.parent.ko = false ∧
      w.parent.untouched = w.state.untouched ∧
      w.parent.score = 1 ∧ flip G w.parent.untouched y = 1) ∨
    (∃ t so soc sc sco, w.tail ≠ [] ∧
      right.selectedMove = some (.open d) ∧
      step G w.state (.open d) = some t ∧
      step G w.state (.open d) = some so ∧
      step G so .close = some soc ∧
      step G w.state .close = some sc ∧
      step G sc (.open d) = some sco ∧ soc = sco) := by
  obtain ⟨x, t, hrightOpen, hopen⟩ :=
    w.unequal_rightMove_is_open right m hselected hne
  by_cases hxd : x = d
  · subst x
    by_cases htail : w.tail = []
    · obtain ⟨y, hincoming, hparentQueue, hparentKo, hparentU,
          hparentScore, hcharge⟩ :=
        w.normalCase.chargedClose_of_tail_empty htail
      exact Or.inr (Or.inl ⟨t, y, htail, hrightOpen, hopen,
        hincoming, hparentQueue, hparentKo, hparentU, hparentScore, hcharge⟩)
    · have hdmem : d ∈ w.state.untouched := by
        simp only [step] at hopen
        split at hopen
        · assumption
        · contradiction
      obtain ⟨so, soc, sc, sco, hopen', hopenClose, hclose,
          hcloseOpen, heq⟩ :=
        isolatedUntouched_open_close_commute G w.state d w.front w.tail
          w.queue htail w.ko hdmem hd
      exact Or.inr (Or.inr ⟨t, so, soc, sc, sco, htail, hrightOpen,
        hopen, hopen', hopenClose, hclose, hcloseOpen, heq⟩)
  · exact Or.inl ⟨x, t, hxd, hrightOpen, hopen⟩

/-- Consequently every false-seat controlled minimum has charged-CLOSE
ancestry; protectedOpen is impossible independently of total board parity. -/
theorem ControlledBadNormalWitness.falseSeat_yields_chargedClose
    {G : SimpleGraph V} {d : V}
    {root : OddStrategy G false (initial (V := V))}
    (w : ControlledBadNormalWitness G d false root) :
    ∃ y, w.incoming = .close ∧
      w.parent.queue = y :: w.front :: w.tail ∧
      w.parent.ko = false ∧
      w.parent.untouched = w.state.untouched ∧
      w.parent.score = 1 ∧ flip G w.parent.untouched y = 1 := by
  exact w.normalCase.chargedClose_of_queue_odd w.queue
    w.falseSeat_queue_odd

/-- A mover-controlled initial root supplies the exact score-coupled policy
pair and an independently minimized true-seat bad-ancestry witness.  The bad
queue is even, so both charged and protected ancestry remain possible. -/
theorem MoverControlled.exists_scoreCoupled_badNormal
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    (h : MoverControlled G (initial (V := V))) :
    ∃ (left : OddStrategy G true (initial (V := V)))
      (right : OddStrategy G true
        (scoreTranslate 1 (initial (V := V)))),
      ScoreCoupledDivergence G true left right ∧
      Nonempty (ControlledBadNormalWitness G d true left) := by
  have hleftWins : OddWins G true (initial (V := V)) :=
    oddWins_of_not_evenWins G true (initial (V := V)) h.2
  have hrightWins : OddWins G true
      (scoreTranslate 1 (initial (V := V))) := by
    simpa [MoverEvenWins, initial] using h.1.scoreTranslate_one
  obtain ⟨left⟩ := hleftWins.nonempty_oddStrategy
  obtain ⟨right⟩ := hrightWins.nonempty_oddStrategy
  have hdiv := left.scoreCoupledDivergence right
  exact ⟨left, right, hdiv, left.nonempty_controlledBadNormalWitness hd⟩

/-- A nonmover-controlled initial root supplies the false-seat coupled pair;
on this side queue/turn parity eliminates protectedOpen altogether, leaving
only the charged-CLOSE spike. -/
theorem NonmoverControlled.exists_scoreCoupled_chargedNormal
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d)
    (h : NonmoverControlled G (initial (V := V))) :
    ∃ (left : OddStrategy G false (initial (V := V)))
      (right : OddStrategy G false
        (scoreTranslate 1 (initial (V := V))))
      (w : ControlledBadNormalWitness G d false left) (y : V),
      ScoreCoupledDivergence G false left right ∧
      w.incoming = .close ∧
      w.parent.queue = y :: w.front :: w.tail ∧
      w.parent.ko = false ∧
      w.parent.untouched = w.state.untouched ∧
      w.parent.score = 1 ∧ flip G w.parent.untouched y = 1 := by
  have hleftWins : OddWins G false (initial (V := V)) :=
    oddWins_of_not_evenWins G false (initial (V := V)) h.1
  have hrightWins : OddWins G false
      (scoreTranslate 1 (initial (V := V))) := by
    simpa [NonmoverEvenWins, initial] using h.2.scoreTranslate_one
  obtain ⟨left⟩ := hleftWins.nonempty_oddStrategy
  obtain ⟨right⟩ := hrightWins.nonempty_oddStrategy
  have hdiv := left.scoreCoupledDivergence right
  obtain ⟨w⟩ := left.nonempty_controlledBadNormalWitness hd
  obtain ⟨y, hincoming, hqueue, hko, hU, hscore, hcharge⟩ :=
    w.falseSeat_yields_chargedClose
  exact ⟨left, right, w, y, hdiv, hincoming, hqueue, hko, hU,
    hscore, hcharge⟩


omit [Fintype V] in
/-- Every score-coupled divergence exposes two distinct legal moves from one
common underlying state, at least one of which is an `OPEN`. -/
theorem ScoreCoupledDivergence.exists_open_divergence
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {left : OddStrategy G seat s}
    {right : OddStrategy G seat (scoreTranslate 1 s)}
    (h : ScoreCoupledDivergence G seat left right) :
    ∃ (t u₀ u₁ : State V) (m₀ m₁ : Move V),
      step G t m₀ = some u₀ ∧ step G t m₁ = some u₁ ∧ m₀ ≠ m₁ ∧
        ((∃ x, m₀ = .open x) ∨ (∃ x, m₁ = .open x)) := by
  induction h with
  | @here t u₀ u₁ _ _ m₀ m₁ hstep₀ hstep₁ _ _ hne =>
      have hstep₁Base : ∃ v, step G t m₁ = some v := by
        obtain ⟨v, hv, _⟩ :=
          (step_scoreTranslate_eq_some_iff G 1 t u₁ m₁).mp hstep₁
        exact ⟨v, hv⟩
      obtain ⟨v, hv⟩ := hstep₁Base
      exact ⟨t, u₀, v, m₀, m₁, hstep₀, hv, hne,
        distinct_legal_moves_include_open hstep₀ hv hne⟩
  | choose _ ih => exact ih
  | answer _ ih => exact ih

omit [Fintype V] in
/-- The exact score-coupled policy obstruction present in a mover-controlled
outcome.  Both policies are controlled by the current mover. -/
theorem MoverControlled.exists_scoreCoupledDivergence
    {G : SimpleGraph V} {s : State V} (h : MoverControlled G s) :
    ∃ (left : OddStrategy G (!s.toMove) s)
      (right : OddStrategy G (!s.toMove) (scoreTranslate 1 s)),
      ScoreCoupledDivergence G (!s.toMove) left right := by
  have hleftWins : OddWins G (!s.toMove) s :=
    oddWins_of_not_evenWins G (!s.toMove) s h.2
  have hrightWins : OddWins G (!s.toMove) (scoreTranslate 1 s) := by
    simpa [MoverEvenWins] using h.1.scoreTranslate_one
  obtain ⟨left⟩ := hleftWins.nonempty_oddStrategy
  obtain ⟨right⟩ := hrightWins.nonempty_oddStrategy
  exact ⟨left, right, left.scoreCoupledDivergence right⟩

omit [Fintype V] in
/-- The dual score-coupled policy obstruction in a nonmover-controlled
outcome.  Here both policies are controlled by the current nonmover. -/
theorem NonmoverControlled.exists_scoreCoupledDivergence
    {G : SimpleGraph V} {s : State V} (h : NonmoverControlled G s) :
    ∃ (left : OddStrategy G s.toMove s)
      (right : OddStrategy G s.toMove (scoreTranslate 1 s)),
      ScoreCoupledDivergence G s.toMove left right := by
  have hleftWins : OddWins G s.toMove s :=
    oddWins_of_not_evenWins G s.toMove s h.1
  have hrightWins : OddWins G s.toMove (scoreTranslate 1 s) := by
    simpa [NonmoverEvenWins] using h.2.scoreTranslate_one
  obtain ⟨left⟩ := hleftWins.nonempty_oddStrategy
  obtain ⟨right⟩ := hrightWins.nonempty_oddStrategy
  exact ⟨left, right, left.scoreCoupledDivergence right⟩

omit [Fintype V] in
/-- Outcome-level universal recursion: every legal child of a
nonmover-controlled node is mover-controlled.  The two controlling policies
belong to the nonmover and are therefore universal at the current node. -/
theorem NonmoverControlled.every_child_moverControlled
    {G : SimpleGraph V} {s t : State V}
    (h : NonmoverControlled G s) {m : Move V}
    (hstep : step G s m = some t) : MoverControlled G t := by
  obtain ⟨left, right, _hdiv⟩ := h.exists_scoreCoupledDivergence
  exact scoreCoupledPair_answerChild_moverControlled
    left right rfl hstep

omit [Fintype V] in
/-- Outcome-level attacker recursion.  At a mover-controlled node, the two
policies either select different legal moves immediately, necessarily
including an OPEN, or agree on one move and descend to a strictly lower-rank
nonmover-controlled child. -/
theorem MoverControlled.currentFork_or_descend
    {G : SimpleGraph V} {s : State V} (h : MoverControlled G s) :
    (∃ (u₀ u₁ : State V) (m₀ m₁ : Move V),
      step G s m₀ = some u₀ ∧ step G s m₁ = some u₁ ∧ m₀ ≠ m₁ ∧
        ((∃ x, m₀ = .open x) ∨ (∃ x, m₁ = .open x))) ∨
    (∃ (t : State V) (m : Move V), step G s m = some t ∧
      rank t < rank s ∧ NonmoverControlled G t) := by
  obtain ⟨left, right, _hdiv⟩ := h.exists_scoreCoupledDivergence
  cases left with
  | terminal _ hterminal hoddScore =>
      have heven : EvenWins G s.toMove s := h.1
      cases heven with
      | terminal _ _ hevenScore => exact False.elim (hoddScore hevenScore)
      | choose _ _ m t hstep _ =>
          exact False.elim (terminal_no_step hterminal ⟨m, t, hstep⟩)
      | answer _ _ hasMove _ =>
          exact False.elim (terminal_no_step hterminal hasMove)
  | answer _ hseat _ _ =>
      exact False.elim (by cases s.toMove <;> simp at hseat)
  | choose _ hseat₀ m₀ u₀ hstep₀ leftTail =>
      cases right with
      | terminal _ hterminal _ =>
          have htranslatedTerminal : Terminal s := by
            simpa [Terminal, scoreTranslate] using hterminal
          exact False.elim
            (terminal_no_step htranslatedTerminal ⟨m₀, u₀, hstep₀⟩)
      | answer _ hseat₁ _ _ =>
          exact False.elim (by
            cases s.toMove <;> simp [scoreTranslate] at hseat₁)
      | choose _ hseat₁ m₁ u₁ hstep₁ rightTail =>
          by_cases hmove : m₀ = m₁
          · subst m₁
            have hleftSelected :
                (OddStrategy.choose s hseat₀ m₀ u₀ hstep₀ leftTail).selectedMove =
                  some m₀ := rfl
            have hrightSelected :
                (OddStrategy.choose (scoreTranslate 1 s) hseat₁ m₀ u₁ hstep₁ rightTail).selectedMove =
                  some m₀ := rfl
            obtain ⟨t, hstep, hrank, hcontrolled⟩ :=
              scoreCoupledPair_same_selectedMove_descends_controlled
                (OddStrategy.choose s hseat₀ m₀ u₀ hstep₀ leftTail)
                (OddStrategy.choose (scoreTranslate 1 s) hseat₁ m₀ u₁ hstep₁ rightTail)
                m₀ hleftSelected hrightSelected
            exact Or.inr ⟨t, m₀, hstep, hrank, hcontrolled⟩
          · obtain ⟨u₁base, hstep₁base, _hu₁⟩ :=
              (step_scoreTranslate_eq_some_iff G 1 s u₁ m₁).mp hstep₁
            exact Or.inl ⟨u₀, u₁base, m₀, m₁, hstep₀, hstep₁base,
              hmove, distinct_legal_moves_include_open
                hstep₀ hstep₁base hmove⟩

omit [Fintype V] in
/-- At a rank-minimal controlled state, the controlled class cannot be
nonmover-controlled: every legal child would be a smaller mover-controlled
state. -/
theorem minimalControlled_not_nonmoverControlled
    {G : SimpleGraph V} {s : State V}
    (hminimal : ∀ {t : State V}, rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (h : NonmoverControlled G s) : False := by
  have hnotTerminal : ¬Terminal s := by
    intro hterminal
    rcases h with ⟨hnotMover, hnonmover⟩
    cases hnonmover with
    | terminal _ _ hscore =>
        exact hnotMover (EvenWins.terminal s hterminal hscore)
    | choose _ _ m t hstep _ =>
        exact terminal_no_step hterminal ⟨m, t, hstep⟩
    | answer _ _ hasMove _ => exact terminal_no_step hterminal hasMove
  obtain ⟨m, t, hstep⟩ := not_terminal_has_step hnotTerminal
  have hchild : MoverControlled G t := h.every_child_moverControlled hstep
  exact (hminimal (rank_step_lt hstep)).1 hchild

omit [Fintype V] in
/-- Therefore every rank-minimal controlled state is mover-controlled and
exposes an immediate distinct legal-move fork containing an OPEN. -/
theorem minimalControlled_moverFork
    {G : SimpleGraph V} {s : State V}
    (hminimal : ∀ {t : State V}, rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (hcontrolled : MoverControlled G s ∨ NonmoverControlled G s) :
    ∃ (u₀ u₁ : State V) (m₀ m₁ : Move V),
      MoverControlled G s ∧
      step G s m₀ = some u₀ ∧ step G s m₁ = some u₁ ∧ m₀ ≠ m₁ ∧
        ((∃ x, m₀ = .open x) ∨ (∃ x, m₁ = .open x)) := by
  have hmover : MoverControlled G s := by
    rcases hcontrolled with hmover | hnonmover
    · exact hmover
    · exact False.elim (minimalControlled_not_nonmoverControlled
        hminimal hnonmover)
  rcases hmover.currentFork_or_descend with hfork | hdesc
  · obtain ⟨u₀, u₁, m₀, m₁, hstep₀, hstep₁, hne, hopen⟩ := hfork
    exact ⟨u₀, u₁, m₀, m₁, hmover, hstep₀, hstep₁, hne, hopen⟩
  · obtain ⟨t, m, hstep, hrank, hnonmover⟩ := hdesc
    exact False.elim ((hminimal hrank).2 hnonmover)

omit [Fintype V] in
/-- Rank minimization over any nonempty family of controlled states.  This
is the policy-free well-founded kernel needed for a reachable-state argument;
the caller supplies closure/reachability information in the predicate `P`. -/
theorem exists_rankMinimal_controlled
    (G : SimpleGraph V) (P : State V → Prop)
    (hex : ∃ s, P s ∧
      (MoverControlled G s ∨ NonmoverControlled G s)) :
    ∃ s, P s ∧ (MoverControlled G s ∨ NonmoverControlled G s) ∧
      ∀ t, P t → rank t < rank s →
        ¬MoverControlled G t ∧ ¬NonmoverControlled G t := by
  classical
  let Q : Nat → Prop := fun n ↦ ∃ s, P s ∧
    (MoverControlled G s ∨ NonmoverControlled G s) ∧ rank s = n
  have hQ : ∃ n, Q n := by
    obtain ⟨s, hP, hcontrolled⟩ := hex
    exact ⟨rank s, s, hP, hcontrolled, rfl⟩
  let n := Nat.find hQ
  obtain ⟨s, hP, hcontrolled, hrank⟩ := Nat.find_spec hQ
  refine ⟨s, hP, hcontrolled, ?_⟩
  intro t htP hlt
  constructor <;> intro htcontrolled
  · have hQt : Q (rank t) :=
      ⟨t, htP, Or.inl htcontrolled, rfl⟩
    have hnle := Nat.find_min' hQ hQt
    have hsle : rank s ≤ rank t := by simpa [n, hrank] using hnle
    exact (Nat.not_lt_of_ge hsle) hlt
  · have hQt : Q (rank t) :=
      ⟨t, htP, Or.inr htcontrolled, rfl⟩
    have hnle := Nat.find_min' hQ hQt
    have hsle : rank s ≤ rank t := by simpa [n, hrank] using hnle
    exact (Nat.not_lt_of_ge hsle) hlt

omit [Fintype V] in
/-- Legal reachability from a fixed root. -/
def ReachableFrom (G : SimpleGraph V) (root t : State V) : Prop :=
  ∃ ms, StepPath G root ms t

omit [Fintype V] in
theorem reachableFrom_root (G : SimpleGraph V) (root : State V) :
    ReachableFrom G root root :=
  ⟨[], StepPath.nil root⟩

omit [Fintype V] in
/-- Reachability is closed under one further legal child. -/
theorem ReachableFrom.step
    {G : SimpleGraph V} {root s t : State V}
    (hreach : ReachableFrom G root s) {m : Move V}
    (hstep : step G s m = some t) : ReachableFrom G root t := by
  obtain ⟨ms, hpath⟩ := hreach
  induction hpath with
  | nil => exact ⟨[m], StepPath.cons hstep (StepPath.nil t)⟩
  | @cons a b s n ns hab htail ih =>
      obtain ⟨tail, htail'⟩ := ih hstep
      exact ⟨n :: tail, StepPath.cons hab htail'⟩

omit [Fintype V] in
/-- Relative version of the commuting-fork exclusion.  Rank minimization only
among states reachable from a fixed root is enough, because the crossed
endpoint is reached by the displayed two-step schedule. -/
theorem reachableMinimal_no_commuting_scoreCoupledFork
    {G : SimpleGraph V} {root : State V} {seat : Bool}
    {s so sc soc sco : State V} {m₀ m₁ : Move V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ t, ReachableFrom G root t → rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hleft : left.selectedMove = some m₀)
    (hright : right.selectedMove = some m₁)
    (hstep₀ : step G s m₀ = some so)
    (hstep₁ : step G s m₁ = some sc)
    (hcross₀ : step G so m₁ = some soc)
    (hcross₁ : step G sc m₀ = some sco)
    (heq : soc = sco) : False := by
  obtain ⟨hrank, hcontrolled⟩ :=
    scoreCoupledPair_commuting_selectedMoves_descend
      left right hturn hleft hright hstep₀ hstep₁ hcross₀ hcross₁ heq
  have hreachEnd : ReachableFrom G root soc :=
    (hreach.step hstep₀).step hcross₀
  rcases hcontrolled with hmover | hnonmover
  · exact (hminimal soc hreachEnd hrank).1 hmover
  · exact (hminimal soc hreachEnd hrank).2 hnonmover

omit [Fintype V] in
/-- At a reachable rank minimum, an isolated-dummy OPEN/CLOSE fork can occur
only at the singleton ko wall. -/
theorem reachableMinimal_no_dummyOpenClose_awaySingleton
    {G : SimpleGraph V} {root : State V} {seat : Bool}
    {s : State V} {d f : V} {q : List V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ t, ReachableFrom G root t → rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hqueue : s.queue = f :: q) (hq : q ≠ []) (hko : s.ko = false)
    (hdmem : d ∈ s.untouched) (hd : IsDummy G d) :
    ¬((left.selectedMove = some (.open d) ∧
          right.selectedMove = some .close) ∨
      (left.selectedMove = some .close ∧
          right.selectedMove = some (.open d))) := by
  obtain ⟨so, soc, sc, sco, hopen, hopenClose, hclose, hcloseOpen, heq⟩ :=
    isolatedUntouched_open_close_commute
      G s d f q hqueue hq hko hdmem hd
  rintro (hforward | hreverse)
  · exact reachableMinimal_no_commuting_scoreCoupledFork
      hreach hminimal left right hturn hforward.1 hforward.2
      hopen hclose hopenClose hcloseOpen heq
  · exact reachableMinimal_no_commuting_scoreCoupledFork
      hreach hminimal left right hturn hreverse.1 hreverse.2
      hclose hopen hcloseOpen hopenClose heq.symm

omit [Fintype V] in
/-- The real mixed fork surviving away from a singleton queue at a reachable
rank minimum has unit OPEN/CLOSE curvature. -/
theorem reachableMinimal_openClose_awaySingleton_adjacent
    {G : SimpleGraph V} {root : State V} {seat : Bool}
    {s : State V} {f z : V} {q : List V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ t, ReachableFrom G root t → rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hqueue : s.queue = f :: q) (hq : q ≠ []) (hko : s.ko = false)
    (hz : z ∈ s.untouched)
    (hfork :
      (left.selectedMove = some (.open z) ∧
          right.selectedMove = some .close) ∨
      (left.selectedMove = some .close ∧
          right.selectedMove = some (.open z))) :
    adjacencyBit G f z = 1 := by
  by_contra hne
  have hbit : adjacencyBit G f z = 0 :=
    zmod2_eq_zero_of_ne_one _ hne
  obtain ⟨so, soc, sc, sco, hopen, hopenClose, hclose, hcloseOpen,
      hU, hqueueEq, hkoEq, hturnEq, hscoreEq⟩ :=
    open_close_square_away_singleton G s f z q hqueue hq hko hz
  have heq : soc = sco := by
    obtain ⟨socU, socQ, socKo, socTurn, socScore⟩ := soc
    obtain ⟨scoU, scoQ, scoKo, scoTurn, scoScore⟩ := sco
    simp only at hU hqueueEq hkoEq hturnEq hscoreEq hbit ⊢
    subst scoU
    subst scoQ
    subst scoKo
    subst scoTurn
    rw [hbit, add_zero] at hscoreEq
    subst scoScore
    rfl
  rcases hfork with hforward | hreverse
  · exact reachableMinimal_no_commuting_scoreCoupledFork
      hreach hminimal left right hturn hforward.1 hforward.2
      hopen hclose hopenClose hcloseOpen heq
  · exact reachableMinimal_no_commuting_scoreCoupledFork
      hreach hminimal left right hturn hreverse.1 hreverse.2
      hclose hopen hcloseOpen hopenClose heq.symm

omit [Fintype V] in
/-- A score-coupled attacker pair at a reachable rank-minimal controlled
state must fork immediately. -/
theorem reachableMinimal_scoreCoupled_currentFork
    {G : SimpleGraph V} {root : State V} {seat : Bool} {s : State V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ t, ReachableFrom G root t → rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat) :
    ∃ (u₀ u₁ : State V) (m₀ m₁ : Move V),
      left.selectedMove = some m₀ ∧ right.selectedMove = some m₁ ∧
      step G s m₀ = some u₀ ∧ step G s m₁ = some u₁ ∧ m₀ ≠ m₁ := by
  have hmover : MoverControlled G s :=
    (scoreCoupledPair_controlled left right).2 hturn
  cases left with
  | terminal _ hterminal hoddScore =>
      cases hmover.1 with
      | terminal _ _ hevenScore => exact False.elim (hoddScore hevenScore)
      | choose _ _ m t hstep _ =>
          exact False.elim (terminal_no_step hterminal ⟨m, t, hstep⟩)
      | answer _ _ hasMove _ =>
          exact False.elim (terminal_no_step hterminal hasMove)
  | answer _ hseat _ _ =>
      exact False.elim (by
        have hne : s.toMove ≠ seat := by rw [hturn]; simp
        exact hne hseat)
  | choose _ hseat₀ m₀ u₀ hstep₀ leftTail =>
      cases right with
      | terminal _ hterminal _ =>
          have hterminalBase : Terminal s := by
            simpa [Terminal, scoreTranslate] using hterminal
          exact False.elim
            (terminal_no_step hterminalBase ⟨m₀, u₀, hstep₀⟩)
      | answer _ hseat₁ _ _ =>
          exact False.elim (by
            have hbaseSeat : s.toMove = seat := by
              simpa [scoreTranslate] using hseat₁
            have hne : s.toMove ≠ seat := by rw [hturn]; simp
            exact hne hbaseSeat)
      | choose _ hseat₁ m₁ u₁ hstep₁ rightTail =>
          obtain ⟨u₁base, hstep₁base, _hu₁⟩ :=
            (step_scoreTranslate_eq_some_iff G 1 s u₁ m₁).mp hstep₁
          by_cases hmove : m₀ = m₁
          · subst m₁
            have hleftSelected :
                (OddStrategy.choose s hseat₀ m₀ u₀ hstep₀ leftTail).selectedMove =
                  some m₀ := rfl
            have hrightSelected :
                (OddStrategy.choose (scoreTranslate 1 s) hseat₁ m₀ u₁ hstep₁
                  rightTail).selectedMove = some m₀ := rfl
            obtain ⟨t, hstep, hrank, hcontrolled⟩ :=
              scoreCoupledPair_same_selectedMove_descends_controlled
                (OddStrategy.choose s hseat₀ m₀ u₀ hstep₀ leftTail)
                (OddStrategy.choose (scoreTranslate 1 s) hseat₁ m₀ u₁ hstep₁
                  rightTail)
                m₀ hleftSelected hrightSelected
            exact False.elim
              ((hminimal t (hreach.step hstep) hrank).2 hcontrolled)
          · exact ⟨u₀, u₁base, m₀, m₁, rfl, rfl,
              hstep₀, hstep₁base, hmove⟩

omit [Fintype V] in
/-- Every controlled root has a reachable rank-minimal controlled descendant.
That descendant is mover-controlled and exposes an immediate distinct-move
fork containing an OPEN. -/
theorem controlled_root_has_reachable_minimal_moverFork
    (G : SimpleGraph V) (root : State V)
    (hroot : MoverControlled G root ∨ NonmoverControlled G root) :
    ∃ s, ReachableFrom G root s ∧ MoverControlled G s ∧
      ∃ (u₀ u₁ : State V) (m₀ m₁ : Move V),
        step G s m₀ = some u₀ ∧ step G s m₁ = some u₁ ∧ m₀ ≠ m₁ ∧
          ((∃ x, m₀ = .open x) ∨ (∃ x, m₁ = .open x)) := by
  obtain ⟨s, hreach, hcontrolled, hminimalReach⟩ :=
    exists_rankMinimal_controlled G (ReachableFrom G root)
      ⟨root, reachableFrom_root G root, hroot⟩
  -- Use the relative minimum directly: all recursive alternatives in
  -- `minimalControlled_moverFork` are actual children and hence reachable.
  have hmover : MoverControlled G s := by
    rcases hcontrolled with hm | hn
    · exact hm
    · exact False.elim (by
        have hnotTerminal : ¬Terminal s := by
          intro hterminal
          rcases hn with ⟨hnot, heven⟩
          cases heven with
          | terminal _ _ hs => exact hnot (.terminal s hterminal hs)
          | choose _ _ m t hs _ =>
              exact terminal_no_step hterminal ⟨m, t, hs⟩
          | answer _ _ hasMove _ => exact terminal_no_step hterminal hasMove
        obtain ⟨m, t, hs⟩ := not_terminal_has_step hnotTerminal
        exact (hminimalReach t (hreach.step hs) (rank_step_lt hs)).1
          (hn.every_child_moverControlled hs))
  rcases hmover.currentFork_or_descend with hfork | hdesc
  · obtain ⟨u₀, u₁, m₀, m₁, hs₀, hs₁, hne, hopen⟩ := hfork
    exact ⟨s, hreach, hmover, u₀, u₁, m₀, m₁,
      hs₀, hs₁, hne, hopen⟩
  · obtain ⟨t, m, hs, hrank, hn⟩ := hdesc
    exact False.elim
      ((hminimalReach t (hreach.step hs) hrank).2 hn)

/-- Sharp root-level controlled obstruction in the presence of an isolated
dummy.  A controlled root has a reachable rank-minimal mover-controlled
state carrying the two exact score-coupled attacker policies.  Either the
dummy has already been consumed, or the current fork is one of four explicit
shapes: two distinct OPENs; dummy OPEN versus CLOSE at the singleton ko wall;
real OPEN versus CLOSE at that same wall; or, away from the wall, real OPEN
versus CLOSE along an edge from the current front.

The separate real singleton-wall alternative is essential: the local wall
repair uses one further OPEN at an attacker node, so its availability is not
implied by the two policies formalized here. -/
theorem controlled_isolated_root_reachable_minimal_exact_shapes
    (G : SimpleGraph V) (root : State V) (d : V)
    (hd : IsDummy G d)
    (hroot : MoverControlled G root ∨ NonmoverControlled G root) :
    ∃ (s : State V), ReachableFrom G root s ∧ MoverControlled G s ∧
      ∃ (left : OddStrategy G (!s.toMove) s)
        (right : OddStrategy G (!s.toMove) (scoreTranslate 1 s))
        (u₀ u₁ : State V) (m₀ m₁ : Move V),
        left.selectedMove = some m₀ ∧ right.selectedMove = some m₁ ∧
        step G s m₀ = some u₀ ∧ step G s m₁ = some u₁ ∧
        m₀ ≠ m₁ ∧
        (d ∉ s.untouched ∨
          (d ∈ s.untouched ∧
            ((∃ x y, x ≠ y ∧ m₀ = .open x ∧ m₁ = .open y) ∨
             (∃ f, s.queue = [f] ∧
                ((m₀ = .open d ∧ m₁ = .close) ∨
                 (m₀ = .close ∧ m₁ = .open d))) ∨
             (∃ f z, z ≠ d ∧ z ∈ s.untouched ∧ s.queue = [f] ∧
                ((m₀ = .open z ∧ m₁ = .close) ∨
                 (m₀ = .close ∧ m₁ = .open z))) ∨
             (∃ f q z, q ≠ [] ∧ z ≠ d ∧ z ∈ s.untouched ∧
                s.queue = f :: q ∧ adjacencyBit G f z = 1 ∧
                ((m₀ = .open z ∧ m₁ = .close) ∨
                 (m₀ = .close ∧ m₁ = .open z)))))) := by
  obtain ⟨s, hreach, hcontrolled, hminimalReach⟩ :=
    exists_rankMinimal_controlled G (ReachableFrom G root)
      ⟨root, reachableFrom_root G root, hroot⟩
  have hmover : MoverControlled G s := by
    rcases hcontrolled with hm | hn
    · exact hm
    · exact False.elim (by
        have hnotTerminal : ¬Terminal s := by
          intro hterminal
          rcases hn with ⟨hnot, heven⟩
          cases heven with
          | terminal _ _ hs => exact hnot (.terminal s hterminal hs)
          | choose _ _ m t hs _ =>
              exact terminal_no_step hterminal ⟨m, t, hs⟩
          | answer _ _ hasMove _ => exact terminal_no_step hterminal hasMove
        obtain ⟨m, t, hs⟩ := not_terminal_has_step hnotTerminal
        exact (hminimalReach t (hreach.step hs) (rank_step_lt hs)).1
          (hn.every_child_moverControlled hs))
  obtain ⟨left, right, _hdiv⟩ := hmover.exists_scoreCoupledDivergence
  have hturn : s.toMove = !(!s.toMove) := by simp
  obtain ⟨u₀, u₁, m₀, m₁, hleft, hright, hstep₀, hstep₁, hne⟩ :=
    reachableMinimal_scoreCoupled_currentFork
      hreach hminimalReach left right hturn
  refine ⟨s, hreach, hmover, left, right, u₀, u₁, m₀, m₁,
    hleft, hright, hstep₀, hstep₁, hne, ?_⟩
  by_cases hdmem : d ∈ s.untouched
  · refine Or.inr ⟨hdmem, ?_⟩
    obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ :=
      distinct_legal_moves_include_open hstep₀ hstep₁ hne
    · by_cases hopen₁ : ∃ y, m₁ = .open y
      · obtain ⟨y, rfl⟩ := hopen₁
        exact Or.inl ⟨x, y, by simpa using hne, rfl, rfl⟩
      · have hm₁ : m₁ = .close :=
          open_and_nonopen_legal_forces_close hdmem hstep₁ hopen₁
        subst m₁
        obtain ⟨f, q, hqueue, _⟩ := close_removes_front hstep₁
        have hko : s.ko = false := by
          cases hk : s.ko with
          | false => rfl
          | true => simp [step, hqueue, hk] at hstep₁
        by_cases hq : q = []
        · have hqueueSingleton : s.queue = [f] := by
            simpa [hq] using hqueue
          by_cases hxd : x = d
          · subst x
            exact Or.inr (Or.inl ⟨f, hqueueSingleton, Or.inl ⟨rfl, rfl⟩⟩)
          · exact Or.inr (Or.inr (Or.inl
              ⟨f, x, hxd, by
                simp only [step] at hstep₀
                split at hstep₀
                · assumption
                · contradiction,
                hqueueSingleton, Or.inl ⟨rfl, rfl⟩⟩))
        · have hxd : x ≠ d := by
            intro hxd
            subst x
            exact reachableMinimal_no_dummyOpenClose_awaySingleton
              hreach hminimalReach left right hturn hqueue hq hko hdmem hd
              (Or.inl ⟨hleft, hright⟩)
          have hxmem : x ∈ s.untouched := by
            simp only [step] at hstep₀
            split at hstep₀
            · assumption
            · contradiction
          have hadj := reachableMinimal_openClose_awaySingleton_adjacent
            hreach hminimalReach left right hturn hqueue hq hko hxmem
              (Or.inl ⟨hleft, hright⟩)
          exact Or.inr (Or.inr (Or.inr
            ⟨f, q, x, hq, hxd, hxmem, hqueue, hadj,
              Or.inl ⟨rfl, rfl⟩⟩))
    · by_cases hopen₀ : ∃ y, m₀ = .open y
      · obtain ⟨y, rfl⟩ := hopen₀
        exact Or.inl ⟨y, x, by simpa using hne, rfl, rfl⟩
      · have hm₀ : m₀ = .close :=
          open_and_nonopen_legal_forces_close hdmem hstep₀ hopen₀
        subst m₀
        obtain ⟨f, q, hqueue, _⟩ := close_removes_front hstep₀
        have hko : s.ko = false := by
          cases hk : s.ko with
          | false => rfl
          | true => simp [step, hqueue, hk] at hstep₀
        by_cases hq : q = []
        · have hqueueSingleton : s.queue = [f] := by
            simpa [hq] using hqueue
          by_cases hxd : x = d
          · subst x
            exact Or.inr (Or.inl ⟨f, hqueueSingleton, Or.inr ⟨rfl, rfl⟩⟩)
          · exact Or.inr (Or.inr (Or.inl
              ⟨f, x, hxd, by
                simp only [step] at hstep₁
                split at hstep₁
                · assumption
                · contradiction,
                hqueueSingleton, Or.inr ⟨rfl, rfl⟩⟩))
        · have hxd : x ≠ d := by
            intro hxd
            subst x
            exact reachableMinimal_no_dummyOpenClose_awaySingleton
              hreach hminimalReach left right hturn hqueue hq hko hdmem hd
              (Or.inr ⟨hleft, hright⟩)
          have hxmem : x ∈ s.untouched := by
            simp only [step] at hstep₁
            split at hstep₁
            · assumption
            · contradiction
          have hadj := reachableMinimal_openClose_awaySingleton_adjacent
            hreach hminimalReach left right hturn hqueue hq hko hxmem
              (Or.inr ⟨hleft, hright⟩)
          exact Or.inr (Or.inr (Or.inr
            ⟨f, q, x, hq, hxd, hxmem, hqueue, hadj,
              Or.inr ⟨rfl, rfl⟩⟩))
  · exact Or.inl hdmem

omit [Fintype V] in
/-- Sharp isolated-root consequence of reachable controlled minimization.
The minimal mover fork either still has the isolated dummy available, or the
dummy has already been consumed on the common controlled history.  This is
the exact fork in the global argument: the first branch admits the local
isolated-dummy classifications above; the second has left their scope. -/
theorem controlled_isolated_root_minimalFork_dummy_status
    (G : SimpleGraph V) (root : State V) (d : V)
    (_hd : IsDummy G d) (_hdroot : d ∈ root.untouched)
    (hroot : MoverControlled G root ∨ NonmoverControlled G root) :
    ∃ s, ReachableFrom G root s ∧ MoverControlled G s ∧
      ((d ∉ s.untouched) ∨
       (d ∈ s.untouched ∧
        ∃ (u₀ u₁ : State V) (m₀ m₁ : Move V),
          step G s m₀ = some u₀ ∧ step G s m₁ = some u₁ ∧ m₀ ≠ m₁ ∧
            ((∃ x, m₀ = .open x) ∨ (∃ x, m₁ = .open x)))) := by
  obtain ⟨s, hreach, hmover, u₀, u₁, m₀, m₁,
      hstep₀, hstep₁, hne, hopen⟩ :=
    controlled_root_has_reachable_minimal_moverFork G root hroot
  refine ⟨s, hreach, hmover, ?_⟩
  by_cases hdmem : d ∈ s.untouched
  · exact Or.inr ⟨hdmem, u₀, u₁, m₀, m₁,
      hstep₀, hstep₁, hne, hopen⟩
  · exact Or.inl hdmem

/-- Targeted odd-order specialization of the preceding theorem.  Isolation
and parity identify this as the controlled class left open by the parity-seat
reduction; they do not yet eliminate the divergence. -/
theorem odd_isolated_moverControlled_has_open_divergence
    {G : SimpleGraph V} {d : V} (_hd : IsDummy G d)
    (_hcard : Odd (Fintype.card V))
    (h : MoverControlled G (initial (V := V))) :
    ∃ (t u₀ u₁ : State V) (m₀ m₁ : Move V),
      step G t m₀ = some u₀ ∧ step G t m₁ = some u₁ ∧ m₀ ≠ m₁ ∧
        ((∃ x, m₀ = .open x) ∨ (∃ x, m₁ = .open x)) := by
  obtain ⟨left, right, hdiv⟩ := h.exists_scoreCoupledDivergence
  exact hdiv.exists_open_divergence

/-- Targeted even-order specialization for the other controlled class. -/
theorem even_isolated_nonmoverControlled_has_open_divergence
    {G : SimpleGraph V} {d : V} (_hd : IsDummy G d)
    (_hcard : Even (Fintype.card V))
    (h : NonmoverControlled G (initial (V := V))) :
    ∃ (t u₀ u₁ : State V) (m₀ m₁ : Move V),
      step G t m₀ = some u₀ ∧ step G t m₁ = some u₁ ∧ m₀ ≠ m₁ ∧
        ((∃ x, m₀ = .open x) ∨ (∃ x, m₁ = .open x)) := by
  obtain ⟨left, right, hdiv⟩ := h.exists_scoreCoupledDivergence
  exact hdiv.exists_open_divergence

end

end Ogdoad.Fifo
