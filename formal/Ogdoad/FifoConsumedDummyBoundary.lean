import Ogdoad.FifoOutcomeSwitch
import Ogdoad.FifoPairState
import Ogdoad.FifoMatching
import Ogdoad.FifoControlledDivergence

/-!
# Consumed-dummy boundary for controlled-state minimization

Rank minimization over all root-reachable controlled states does not preserve
an isolated dummy in the untouched carrier.  The three-vertex edge-plus-
isolate board already has a root-reachable mover-controlled singleton wall at
the globally least possible controlled rank, after the dummy has been opened
and closed.

This is not a counterexample to FIFO linking: the initial root of the example
is both-even.  It shows that a successful controlled-state descent must retain
the common score-coupled root policies (or equivalent strategy-prefix data),
not merely legal reachability and the controlled outcome class.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Either controlled outcome class supplies a hot physical player. -/
theorem controlled_has_hot
    {G : SimpleGraph V} {s : State V}
    (h : MoverControlled G s ∨ NonmoverControlled G s) :
    ∃ player, Hot G player s := by
  rcases h with hmover | hnonmover
  · refine ⟨s.toMove, hmover.1, ?_⟩
    exact oddWins_of_not_evenWins G (!s.toMove) s hmover.2
  · refine ⟨!s.toMove, hnonmover.2, ?_⟩
    simpa using oddWins_of_not_evenWins G s.toMove s hnonmover.1

omit [Fintype V] in
/-- Six is the least possible rank of a controlled FIFO state.  A hypothetical
smaller hot state has a globally minimum hot score translate; the checked
minimum-hot classification makes it a singleton charged wall, whose rank is
already at least six. -/
theorem six_le_rank_of_hot
    {G : SimpleGraph V} {player : Bool} {s : State V}
    (hhot : Hot G player s) : 6 ≤ rank s := by
  classical
  let P : Nat → Prop := fun n ↦
    ∃ (p : Bool) (t : State V), Hot G p t ∧ rank t = n
  have hP : ∃ n, P n := ⟨rank s, player, s, hhot, rfl⟩
  let n := Nat.find hP
  obtain ⟨p, t, htHot, htRank⟩ := Nat.find_spec hP
  let t0 := if t.score = 0 then t else scoreTranslate 1 t
  have ht0Rank : rank t0 = rank t := by
    simp only [t0]
    split <;> rfl
  have ht0Score : t0.score = 0 := by
    simp only [t0]
    split
    · assumption
    · rename_i hne
      have hone : t.score = 1 := zmod2_eq_one_of_ne_zero _ hne
      simp [scoreTranslate, hone, CharTwo.add_self_eq_zero]
  have ht0Hot : Hot G p t0 := by
    simp only [t0]
    split
    · exact htHot
    · exact (hot_scoreTranslate_one_iff G p t).2 htHot
  have hminimal : ∀ (other : Bool) (w : State V), rank w < rank t0 →
      ¬Hot G other w := by
    intro other w hw hwhot
    have hPw : P (rank w) := ⟨other, w, hwhot, rfl⟩
    have hnle : n ≤ rank w := Nat.find_min' hP hPw
    have htle : rank t0 ≤ rank w := by
      rw [ht0Rank, htRank]
      exact hnle
    exact (Nat.not_lt_of_ge htle) hw
  obtain ⟨_turn, f, q, z, hqueue, hko, hU, _hbit, _htail⟩ :=
    minHotState_is_singletonWall G p t0 ht0Score ht0Hot hminimal
  have hsixMin : 6 ≤ rank t0 := by
    rw [rank, hqueue, hko, hU]
    simp
    omega
  have hminRoot : rank t0 ≤ rank s := by
    have hPs : P (rank s) := ⟨player, s, hhot, rfl⟩
    have hnle : n ≤ rank s := Nat.find_min' hP hPs
    rw [ht0Rank, htRank]
    exact hnle
  exact le_trans hsixMin hminRoot

omit [Fintype V] in
theorem six_le_rank_of_controlled
    {G : SimpleGraph V} {s : State V}
    (h : MoverControlled G s ∨ NonmoverControlled G s) :
    6 ≤ rank s := by
  obtain ⟨player, hhot⟩ := controlled_has_hot h
  exact six_le_rank_of_hot hhot

omit [Fintype V] in
/-- At the least possible controlled rank, an isolated dummy cannot remain
untouched.  Normalizing the score and applying the minimum-hot theorem gives
a singleton charged wall.  Isolation excludes the dummy from either endpoint
of that wall. -/
theorem rank_six_controlled_consumes_isolated
    {G : SimpleGraph V} {d : V} {s : State V}
    (hd : IsDummy G d) (hrank : rank s = 6)
    (hcontrolled : MoverControlled G s ∨ NonmoverControlled G s) :
    d ∉ s.untouched := by
  intro hdmem
  obtain ⟨player, hhot⟩ := controlled_has_hot hcontrolled
  let s0 := if s.score = 0 then s else scoreTranslate 1 s
  have hs0Rank : rank s0 = rank s := by
    simp only [s0]
    split <;> rfl
  have hs0Score : s0.score = 0 := by
    simp only [s0]
    split
    · assumption
    · rename_i hne
      have hone : s.score = 1 := zmod2_eq_one_of_ne_zero _ hne
      simp [scoreTranslate, hone, CharTwo.add_self_eq_zero]
  have hs0Hot : Hot G player s0 := by
    simp only [s0]
    split
    · exact hhot
    · exact (hot_scoreTranslate_one_iff G player s).2 hhot
  have hminimal : ∀ (other : Bool) (t : State V), rank t < rank s0 →
      ¬Hot G other t := by
    intro other t hlt hthot
    have hsix := six_le_rank_of_hot hthot
    have hs0Six : rank s0 = 6 := hs0Rank.trans hrank
    omega
  obtain ⟨_turn, f, q, z, _hqueue, _hko, hU, hbit, _htail⟩ :=
    minHotState_is_singletonWall G player s0 hs0Score hs0Hot hminimal
  have hdmem0 : d ∈ s0.untouched := by
    simp only [s0]
    split
    · exact hdmem
    · simpa [scoreTranslate] using hdmem
  have hdz : d = z := by
    rw [hU] at hdmem0
    simpa using hdmem0
  have hzNotDummy := (adjacencyBit_one_avoids_dummy hd hbit).2
  exact hzNotDummy hdz.symm

/-! ## Exact common-policy ancestry before dummy consumption -/

/-- Along two score-coupled root policies, either both attacker policies
select the dummy at one common ancestry node, or their first unequal selected
moves occur while the dummy is still untouched.  The two alternatives retain
the exact common root prefixes. -/
def ScoreCoupledDummyEvent (G : SimpleGraph V) (seat : Bool) (d : V)
    {root : State V} (leftRoot : OddStrategy G seat root)
    (rightRoot : OddStrategy G seat (scoreTranslate 1 root)) : Prop :=
  (∃ (state : State V) (left : OddStrategy G seat state)
      (right : OddStrategy G seat (scoreTranslate 1 state))
      (moment : EdgeVector V),
      StrategyPrefix G seat leftRoot left moment ∧
      StrategyPrefix G seat rightRoot right moment ∧
      d ∈ state.untouched ∧
      left.selectedMove = some (.open d) ∧
      right.selectedMove = some (.open d)) ∨
  (∃ (state : State V) (left : OddStrategy G seat state)
      (right : OddStrategy G seat (scoreTranslate 1 state))
      (moment : EdgeVector V) (leftMove rightMove : Move V),
      StrategyPrefix G seat leftRoot left moment ∧
      StrategyPrefix G seat rightRoot right moment ∧
      d ∈ state.untouched ∧
      left.selectedMove = some leftMove ∧
      right.selectedMove = some rightMove ∧ leftMove ≠ rightMove)

omit [Fintype V] in
/-- A legal move other than `OPEN d` preserves membership of `d` in the
untouched carrier. -/
theorem mem_untouched_of_step_ne_dummyOpen
    {G : SimpleGraph V} {d : V} {s t : State V} {m : Move V}
    (hdmem : d ∈ s.untouched) (hstep : step G s m = some t)
    (hne : m ≠ .open d) : d ∈ t.untouched := by
  cases m with
  | «open» x =>
      have hxd : x ≠ d := by
        intro hxd
        subst x
        exact hne rfl
      simp only [step] at hstep
      split at hstep
      · cases hstep
        exact Finset.mem_erase.mpr ⟨Ne.symm hxd, hdmem⟩
      · contradiction
  | close =>
      simp only [step] at hstep
      split at hstep
      · contradiction
      · split at hstep
        · contradiction
        · cases hstep
          exact hdmem
  | pass =>
      simp only [step] at hstep
      split at hstep
      · cases hstep
        exact hdmem
      · contradiction

omit [Fintype V] in
/-- Score-coupled exact odd policies cannot coexist once the untouched
carrier is empty: one of the two roots has score zero, and either physical
seat can preserve that score through the forced drain. -/
theorem scoreCoupledPair_untouched_nonempty
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s)) :
    s.untouched.Nonempty := by
  by_contra hne
  have hU : s.untouched = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  by_cases hs0 : s.score = 0
  · exact (evenWins_of_untouched_empty seat s hU hs0).not_oddWins
      left.toOddWins
  · have hs1 : s.score = 1 := zmod2_eq_one_of_ne_zero _ hs0
    have htU : (scoreTranslate 1 s).untouched = ∅ := by
      simpa [scoreTranslate] using hU
    have ht0 : (scoreTranslate 1 s).score = 0 := by
      simp [scoreTranslate, hs1, CharTwo.add_self_eq_zero]
    exact (evenWins_of_untouched_empty seat (scoreTranslate 1 s) htU ht0)
      |>.not_oddWins right.toOddWins

omit [Fintype V] in
/-- At a common defender node with the dummy untouched, some legal common
reply other than `OPEN d` exists.  Otherwise `d` would be the sole untouched
vertex; opening it would give score-coupled odd children with empty carrier,
contradicting `scoreCoupledPair_untouched_nonempty`. -/
theorem scoreCoupledPair_answer_exists_nonDummy_step
    {G : SimpleGraph V} {seat : Bool} {s : State V} {d : V}
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = seat) (hdmem : d ∈ s.untouched) :
    ∃ m t, step G s m = some t ∧ m ≠ .open d := by
  cases left with
  | terminal _ hterminal _ =>
      let td : State V := {
        untouched := s.untouched.erase d
        queue := s.queue ++ [d]
        ko := s.queue.isEmpty
        toMove := !s.toMove
        score := s.score }
      have hopen : step G s (.open d) = some td := by
        simp [step, td, hdmem]
      exact False.elim (terminal_no_step hterminal ⟨.open d, td, hopen⟩)
  | choose _ hseat _ _ _ _ => exact False.elim (hseat hturn)
  | answer _ hseat₀ hasMove₀ children₀ =>
      cases right with
      | terminal _ hterminal _ =>
          let td : State V := {
            untouched := s.untouched.erase d
            queue := s.queue ++ [d]
            ko := s.queue.isEmpty
            toMove := !s.toMove
            score := s.score }
          have hopen :
              step G (scoreTranslate 1 s) (.open d) =
                some (scoreTranslate 1 td) := by
            rw [step_scoreTranslate]
            simp [step, td, hdmem]
          exact False.elim
            (terminal_no_step hterminal ⟨.open d, scoreTranslate 1 td, hopen⟩)
      | choose _ hseat _ _ _ _ =>
          exact False.elim (hseat (by simpa [scoreTranslate] using hturn))
      | answer _ hseat₁ hasMove₁ children₁ =>
          by_contra hnone
          push Not at hnone
          have hUsub : s.untouched ⊆ {d} := by
            intro x hx
            by_contra hxd
            let tx : State V := {
              untouched := s.untouched.erase x
              queue := s.queue ++ [x]
              ko := s.queue.isEmpty
              toMove := !s.toMove
              score := s.score }
            have hxstep : step G s (.open x) = some tx := by
              simp [step, tx, hx]
            exact hxd (by
              have := hnone (.open x) tx hxstep
              simpa using this)
          have hUeq : s.untouched = {d} := by
            apply Finset.Subset.antisymm hUsub
            simpa using hdmem
          let td : State V := {
            untouched := ∅
            queue := s.queue ++ [d]
            ko := s.queue.isEmpty
            toMove := !s.toMove
            score := s.score }
          have hopen : step G s (.open d) = some td := by
            simp [step, td, hUeq]
          have hopen₁ :
              step G (scoreTranslate 1 s) (.open d) =
                some (scoreTranslate 1 td) := by
            rw [step_scoreTranslate, hopen]
            simp
          have hnonempty := scoreCoupledPair_untouched_nonempty
            (children₀ (.open d) td hopen)
            (children₁ (.open d) (scoreTranslate 1 td) hopen₁)
          have htdEmpty : td.untouched = ∅ := by rfl
          exact (Finset.not_nonempty_iff_eq_empty.mpr htdEmpty) hnonempty

omit [Fintype V] in
/-- The earlier universal fan does contain the dummy sibling, but that sibling
is itself mover-controlled.  Hence taking it transports the controlled
obstruction past dummy consumption rather than contradicting it. -/
theorem scoreCoupledPair_answer_dummySibling_moverControlled
    {G : SimpleGraph V} {seat : Bool} {s : State V} {d : V}
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = seat) (hdmem : d ∈ s.untouched) :
    ∃ td, step G s (.open d) = some td ∧
      MoverControlled G td ∧ d ∉ td.untouched := by
  let td : State V := {
    untouched := s.untouched.erase d
    queue := s.queue ++ [d]
    ko := s.queue.isEmpty
    toMove := !s.toMove
    score := s.score }
  have hstep : step G s (.open d) = some td := by
    simp [step, td, hdmem]
  have hmover := scoreCoupledPair_answerChild_moverControlled
    left right hturn hstep
  exact ⟨td, hstep, hmover, by simp [td]⟩

omit [Fintype V] in
/-- A common attacker selection of `OPEN d` is an exact controlled descent:
the current state is mover-controlled, its dummy-open child is
nonmover-controlled, and the dummy is absent from that child.  Thus this
surviving event is not a bookkeeping artifact of the ancestry theorem. -/
theorem scoreCoupledPair_commonDummyOpen_controlledDescent
    {G : SimpleGraph V} {seat : Bool} {s : State V} {d : V}
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hleft : left.selectedMove = some (.open d))
    (hright : right.selectedMove = some (.open d)) :
    ∃ t, step G s (.open d) = some t ∧ rank t < rank s ∧
      MoverControlled G s ∧ NonmoverControlled G t ∧
      d ∉ t.untouched := by
  have hturn : s.toMove = !seat := by
    cases left with
    | terminal _ _ _ => simp [OddStrategy.selectedMove] at hleft
    | answer _ _ _ _ => simp [OddStrategy.selectedMove] at hleft
    | choose _ hseat _ _ _ _ => exact Bool.eq_not_iff.mpr hseat
  obtain ⟨t, hstep, hrank, hnonmover⟩ :=
    scoreCoupledPair_same_selectedMove_descends_controlled
      left right (.open d) hleft hright
  have hdnot : d ∉ t.untouched := by
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp
    · contradiction
  exact ⟨t, hstep, hrank,
    (scoreCoupledPair_controlled left right).2 hturn,
    hnonmover, hdnot⟩

omit [Fintype V] in
/-- Conversely, every mover-controlled state whose isolated dummy is still
untouched admits a score-coupled pair which commonly selects that dummy
exactly when the dummy-open child is nonmover-controlled.  This identifies
the surviving policy event with an ordinary outcome transition, and shows
that an ancestry contradiction must use information from before the event. -/
theorem exists_scoreCoupled_commonDummyOpen_iff
    {G : SimpleGraph V} {s t : State V} {d : V}
    (_hdmem : d ∈ s.untouched)
    (hstep : step G s (.open d) = some t)
    (hmover : MoverControlled G s) :
    (∃ (left : OddStrategy G (!s.toMove) s)
      (right : OddStrategy G (!s.toMove) (scoreTranslate 1 s)),
      left.selectedMove = some (.open d) ∧
      right.selectedMove = some (.open d)) ↔
      NonmoverControlled G t := by
  constructor
  · rintro ⟨left, right, hleft, hright⟩
    obtain ⟨u, hu, _hrank, _hmover, hnonmover, _hdnot⟩ :=
      scoreCoupledPair_commonDummyOpen_controlledDescent
        left right hleft hright
    rw [hstep] at hu
    exact Option.some.inj hu.symm ▸ hnonmover
  · intro hnonmover
    have hleftRoot : OddWins G (!s.toMove) s :=
      oddWins_of_not_evenWins G (!s.toMove) s hmover.2
    have hrightRoot : OddWins G (!s.toMove) (scoreTranslate 1 s) := by
      simpa [MoverEvenWins] using hmover.1.scoreTranslate_one
    have htTurn : t.toMove = !s.toMove := step_toMove hstep
    have hleftChild : OddWins G (!s.toMove) t := by
      have hnot : ¬EvenWins G (!s.toMove) t := by
        simpa [MoverEvenWins, htTurn] using hnonmover.1
      exact oddWins_of_not_evenWins G (!s.toMove) t hnot
    have hstep₁ : step G (scoreTranslate 1 s) (.open d) =
        some (scoreTranslate 1 t) := by
      rw [step_scoreTranslate, hstep]
      simp
    have hrightChild :
        OddWins G (!s.toMove) (scoreTranslate 1 t) := by
      have hevenT : EvenWins G s.toMove t := by
        simpa [NonmoverEvenWins, htTurn] using hnonmover.2
      simpa using hevenT.scoreTranslate_one
    obtain ⟨leftTail⟩ := hleftChild.nonempty_oddStrategy
    obtain ⟨rightTail⟩ := hrightChild.nonempty_oddStrategy
    let left : OddStrategy G (!s.toMove) s :=
      .choose s (by simp) (.open d) t hstep leftTail
    let right : OddStrategy G (!s.toMove) (scoreTranslate 1 s) :=
      .choose (scoreTranslate 1 s) (by simp [scoreTranslate]) (.open d)
        (scoreTranslate 1 t) hstep₁ rightTail
    exact ⟨left, right, rfl, rfl⟩

/-- In the mover-controlled initial orientation there is literally no earlier
fan to exploit: common selection of the dummy at the root is equivalent to
nonmover control of the ordinary one-OPEN child. -/
theorem moverControlled_initial_commonDummyOpen_iff
    {G : SimpleGraph V} {d : V}
    (hmover : MoverControlled G (initial (V := V))) :
    (∃ (left : OddStrategy G (!((initial (V := V)).toMove))
        (initial (V := V)))
      (right : OddStrategy G (!((initial (V := V)).toMove))
        (scoreTranslate 1 (initial (V := V)))),
      left.selectedMove = some (.open d) ∧
      right.selectedMove = some (.open d)) ↔
      NonmoverControlled G (afterInitialOpen d) := by
  have hstep := initial_step_open G d
  exact exists_scoreCoupled_commonDummyOpen_iff
    (G := G) (s := initial (V := V)) (t := afterInitialOpen d)
    (d := d) (by simp [initial]) hstep hmover

omit [Fintype V] in
/-- Exact first-event theorem for the common policy ancestry.  At defender
nodes the proof deliberately follows a non-dummy reply, which always exists
by the preceding lemma.  Consequently the dummy can disappear before the
first unequal policy choices only when both attacker policies themselves
select `OPEN d` at a common ancestry node. -/
theorem OddStrategy.scoreCoupledDummyEvent
    {G : SimpleGraph V} {seat : Bool} {root : State V} {d : V}
    (leftRoot : OddStrategy G seat root)
    (rightRoot : OddStrategy G seat (scoreTranslate 1 root))
    (hdroot : d ∈ root.untouched) :
    ScoreCoupledDummyEvent G seat d leftRoot rightRoot := by
  have descend : ∀ {s : State V}
      {left : OddStrategy G seat s}
      {right : OddStrategy G seat (scoreTranslate 1 s)},
      d ∈ s.untouched →
      ∀ {p : EdgeVector V},
        StrategyPrefix G seat leftRoot left p →
        StrategyPrefix G seat rightRoot right p →
        ScoreCoupledDummyEvent G seat d leftRoot rightRoot := by
    intro s
    induction s using (measure rank).wf.induction with
    | h s ih =>
      intro left right hdmem p hpLeft hpRight
      cases left with
      | terminal _ hterminal hscore =>
          cases right with
          | terminal _ _ htranslatedScore =>
              have hs1 : s.score = 1 := zmod2_eq_one_of_ne_zero _ hscore
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
          | answer _ hseat₁ _ _ =>
              exact False.elim (hseat₀ (by
                simpa [scoreTranslate] using hseat₁))
          | choose _ hseat₁ m₁ u₁ hstep₁ rightTail =>
              by_cases hmove : m₀ = m₁
              · subst m₁
                by_cases hdmove : m₀ = .open d
                · subst m₀
                  exact Or.inl ⟨s,
                    .choose s hseat₀ (.open d) u₀ hstep₀ leftTail,
                    .choose (scoreTranslate 1 s) hseat₁ (.open d) u₁
                      hstep₁ rightTail,
                    p, hpLeft, hpRight, hdmem, rfl, rfl⟩
                · have hu : u₁ = scoreTranslate 1 u₀ := by
                    rw [step_scoreTranslate, hstep₀] at hstep₁
                    exact Option.some.inj hstep₁.symm
                  subst u₁
                  have hdchild : d ∈ u₀.untouched :=
                    mem_untouched_of_step_ne_dummyOpen hdmem hstep₀ hdmove
                  have hpLeft' : StrategyPrefix G seat leftRoot leftTail
                      (p + moveLiveStar s m₀) := StrategyPrefix.choose hpLeft
                  have hpRight' : StrategyPrefix G seat rightRoot rightTail
                      (p + moveLiveStar s m₀) := by
                    simpa [moveLiveStar, liveSet, scoreTranslate] using
                      (StrategyPrefix.choose hpRight)
                  exact ih u₀ (rank_step_lt hstep₀)
                    hdchild hpLeft' hpRight'
              · exact Or.inr ⟨s,
                  .choose s hseat₀ m₀ u₀ hstep₀ leftTail,
                  .choose (scoreTranslate 1 s) hseat₁ m₁ u₁ hstep₁
                    rightTail,
                  p, m₀, m₁, hpLeft, hpRight, hdmem, rfl, rfl, hmove⟩
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
              let leftNow := OddStrategy.answer s hseat₀ hasMove₀ children₀
              let rightNow := OddStrategy.answer (scoreTranslate 1 s) hseat₁
                hasMove₁ children₁
              obtain ⟨m, u, hstep, hm⟩ :=
                scoreCoupledPair_answer_exists_nonDummy_step
                  leftNow rightNow hseat₀ hdmem
              have hstep₁ : step G (scoreTranslate 1 s) m =
                  some (scoreTranslate 1 u) := by
                rw [step_scoreTranslate, hstep]
                simp
              have hdchild : d ∈ u.untouched :=
                mem_untouched_of_step_ne_dummyOpen hdmem hstep hm
              have hpLeft' : StrategyPrefix G seat leftRoot
                  (children₀ m u hstep) (p + moveLiveStar s m) :=
                StrategyPrefix.answer hpLeft
              have hpRight' : StrategyPrefix G seat rightRoot
                  (children₁ m (scoreTranslate 1 u) hstep₁)
                  (p + moveLiveStar s m) := by
                simpa [moveLiveStar, liveSet, scoreTranslate] using
                  (StrategyPrefix.answer hpRight)
              exact ih u (rank_step_lt hstep) hdchild hpLeft' hpRight'
  exact descend hdroot StrategyPrefix.root StrategyPrefix.root

/-- Root-level controlled specialization.  The former opaque
"dummy already consumed" branch is replaced by an exact ancestry event:
before any unequal choices, both score-coupled attacker policies selected the
dummy at one common root-prefix node.  Otherwise the unequal-choice fork
itself still has the isolated dummy available. -/
theorem controlled_isolated_initial_has_dummyEvent
    (G : SimpleGraph V) (d : V) (_hd : IsDummy G d)
    (hroot : MoverControlled G (initial (V := V)) ∨
      NonmoverControlled G (initial (V := V))) :
    ∃ (seat : Bool)
      (left : OddStrategy G seat (initial (V := V)))
      (right : OddStrategy G seat
        (scoreTranslate 1 (initial (V := V)))),
      ScoreCoupledDummyEvent G seat d left right := by
  rcases hroot with hmover | hnonmover
  · obtain ⟨left, right, _hdiv⟩ :=
      hmover.exists_scoreCoupledDivergence
    exact ⟨!((initial (V := V)).toMove), left, right,
      left.scoreCoupledDummyEvent right (by simp [initial])⟩
  · obtain ⟨left, right, _hdiv⟩ :=
      hnonmover.exists_scoreCoupledDivergence
    exact ⟨(initial (V := V)).toMove, left, right,
      left.scoreCoupledDummyEvent right (by simp [initial])⟩

/-- The least-rank controlled checkpoint on the three-label edge-plus-isolate
board.  It is reached after `OPEN 1; OPEN 2; CLOSE 1`: the isolated dummy `1`
has left both the untouched carrier and the queue, and the real edge `2--0`
is the surviving singleton wall. -/
def consumedDummyWallState : State (Fin 3) where
  untouched := {0}
  queue := [2]
  ko := false
  toMove := true
  score := 0

theorem consumedDummyWallState_reachable :
    ∃ s0 s1,
      step activeNeutralIntervalGraph (initial (V := Fin 3)) (.open 1) =
          some s0 ∧
      step activeNeutralIntervalGraph s0 (.open 2) = some s1 ∧
      step activeNeutralIntervalGraph s1 .close =
          some consumedDummyWallState := by
  let s0 : State (Fin 3) := {
    untouched := {0, 2}
    queue := [1]
    ko := true
    toMove := true
    score := 0 }
  let s1 : State (Fin 3) := {
    untouched := {0}
    queue := [1, 2]
    ko := false
    toMove := false
    score := 0 }
  refine ⟨s0, s1, ?_, ?_, ?_⟩
  · have hU : (Finset.univ.erase 1 : Finset (Fin 3)) = {0, 2} := by
      ext x
      fin_cases x <;> simp
    simp [step, initial, s0, hU]
  · have hErase : ({0, 2} : Finset (Fin 3)).erase 2 = {0} := by
      ext x
      fin_cases x <;> simp
    simp [step, s0, s1, hErase]
  · simp [step, s1, consumedDummyWallState,
      flip_dummy activeNeutralIntervalGraph_dummy]

theorem evenWins_consumedDummyWall_mover :
    EvenWins activeNeutralIntervalGraph true consumedDummyWallState := by
  let t : State (Fin 3) := {
    untouched := ∅
    queue := [2, 0]
    ko := false
    toMove := false
    score := 0 }
  have hopen :
      step activeNeutralIntervalGraph consumedDummyWallState (.open 0) =
        some t := by
    simp [step, consumedDummyWallState, t]
  refine EvenWins.choose consumedDummyWallState rfl (.open 0) t hopen ?_
  exact evenWins_of_untouched_empty true t (by simp [t]) (by simp [t])

theorem oddWins_consumedDummyWall_nonmover :
    OddWins activeNeutralIntervalGraph false consumedDummyWallState := by
  let sc : State (Fin 3) := {
    untouched := {0}
    queue := []
    ko := false
    toMove := false
    score := 1 }
  have hadj : activeNeutralIntervalGraph.Adj 2 0 := by
    simp [activeNeutralIntervalGraph, SimpleGraph.fromRel_adj]
  have hclose :
      step activeNeutralIntervalGraph consumedDummyWallState .close =
        some sc := by
    simp [step, consumedDummyWallState, sc, flip_singleton_of_adj hadj]
  refine OddWins.choose consumedDummyWallState (by decide) .close sc hclose ?_
  let so : State (Fin 3) := {
    untouched := ∅
    queue := [0]
    ko := true
    toMove := true
    score := 1 }
  have hopen : step activeNeutralIntervalGraph sc (.open 0) = some so := by
    simp [step, sc, so]
  refine OddWins.answer sc rfl ⟨.open 0, so, hopen⟩ ?_
  intro m t hstep
  cases m with
  | «open» v =>
      simp only [step, sc] at hstep
      split at hstep
      · rename_i hv
        have hv0 : v = 0 := by simpa using hv
        subst v
        cases hstep
        exact oddWins_of_untouched_empty activeNeutralIntervalGraph false so
          (by simp [so]) (by simp [so])
      · contradiction
  | close => simp [step, sc] at hstep
  | pass => simp [step, sc] at hstep

theorem consumedDummyWall_moverControlled :
    MoverControlled activeNeutralIntervalGraph consumedDummyWallState := by
  refine ⟨?_, ?_⟩
  · simpa [MoverEvenWins, consumedDummyWallState] using
      evenWins_consumedDummyWall_mover
  · intro hnonmover
    have heven :
        EvenWins activeNeutralIntervalGraph false consumedDummyWallState := by
      simpa [NonmoverEvenWins, consumedDummyWallState] using hnonmover
    exact heven.not_oddWins oddWins_consumedDummyWall_nonmover

/-- The same board is not a root counterexample: it is a matching plus one
isolate, so the proved matching theorem gives both physical seats an even
strategy at the initial root. -/
theorem bothEven_consumedDummyBoundary_root :
    BothEven activeNeutralIntervalGraph (initial (V := Fin 3)) := by
  have hmatching : IsMatchingGraph activeNeutralIntervalGraph := by
    intro v x y hvx hvy
    fin_cases v <;> fin_cases x <;> fin_cases y <;>
      simp [activeNeutralIntervalGraph, SimpleGraph.fromRel_adj] at hvx hvy ⊢
  exact ⟨by simpa [MoverEvenWins, initial] using
      evenWins_initial_of_matching hmatching false,
    by simpa [NonmoverEvenWins, initial] using
      evenWins_initial_of_matching hmatching true⟩

omit [Fintype V] in
/-- The countermodel is at the global least controlled rank and has already
spent the isolated dummy.  Thus legal root ancestry plus rank minimality does
not suffice to retain `d`; the missing invariant must remember how the
controlled state is embedded in the common root policies. -/
theorem consumedDummyWall_is_leastRank_rootReachable_controlled :
    rank consumedDummyWallState = 6 ∧
    1 ∉ consumedDummyWallState.untouched ∧
    MoverControlled activeNeutralIntervalGraph consumedDummyWallState ∧
    (∃ s0 s1,
      step activeNeutralIntervalGraph (initial (V := Fin 3)) (.open 1) =
          some s0 ∧
      step activeNeutralIntervalGraph s0 (.open 2) = some s1 ∧
      step activeNeutralIntervalGraph s1 .close =
          some consumedDummyWallState) ∧
    ∀ (G : SimpleGraph V) (s : State V),
      MoverControlled G s ∨ NonmoverControlled G s →
      rank consumedDummyWallState ≤ rank s := by
  refine ⟨by decide, by decide, consumedDummyWall_moverControlled,
    consumedDummyWallState_reachable, ?_⟩
  intro G s hcontrolled
  change 6 ≤ rank s
  exact six_le_rank_of_controlled hcontrolled

end

end Ogdoad.Fifo
