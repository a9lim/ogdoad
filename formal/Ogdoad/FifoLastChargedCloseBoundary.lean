import Ogdoad.FifoPositionalStateDAGBoundary

/-!
# The last charged CLOSE on a score-one root prefix

Every legal path from the score-zero initial root to a score-one state has a
last score-changing edge.  Since OPEN and PASS preserve score, that edge is a
unit-charged `CLOSE`; every later edge is score-neutral.  This module records
that exact causal decomposition and the FIFO order dichotomy for a vertex
still queued at the target: it either survived behind the charged front, or
its `OPEN` occurs in the neutral suffix.

Both order branches occur in exact initial-root public-policy histories with
a sheet-one selected descendant.  In the survivor example the earlier opener
is needed to clear the ko wall; in the neutral-suffix example, commuting the
debt opener earlier destroys the last CLOSE's charge.  Thus neither order
alone produces a same-score reconvergence.  The examples deliberately do not
put the entire initial policy on sheet one, which is the missing global
counterstrategy coupling.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A legal path on which every individual transition preserves score. -/
inductive ScoreNeutralPath (G : SimpleGraph V) :
    State V → List (Move V) → State V → Prop
  | nil (s : State V) : ScoreNeutralPath G s [] s
  | cons {s s' t : State V} {m : Move V} {ms : List (Move V)}
      (head : step G s m = some s') (score_eq : s'.score = s.score)
      (tail : ScoreNeutralPath G s' ms t) :
      ScoreNeutralPath G s (m :: ms) t

omit [Fintype V] in
theorem ScoreNeutralPath.toStepPath
    {G : SimpleGraph V} {s t : State V} {ms : List (Move V)}
    (h : ScoreNeutralPath G s ms t) : StepPath G s ms t := by
  induction h with
  | nil => exact .nil _
  | cons hstep _ _ ih => exact .cons hstep ih

omit [Fintype V] in
theorem ScoreNeutralPath.score_eq
    {G : SimpleGraph V} {s t : State V} {ms : List (Move V)}
    (h : ScoreNeutralPath G s ms t) : t.score = s.score := by
  induction h with
  | nil => rfl
  | cons _ hscore _ ih => exact ih.trans hscore

omit [Fintype V] in
/-- A score-changing FIFO edge is necessarily a CLOSE whose front has unit
charge. -/
theorem scoreChange_step_is_chargedClose
    {G : SimpleGraph V} {s t : State V} {m : Move V}
    (hstep : step G s m = some t) (hne : t.score ≠ s.score) :
    ∃ f q, m = .close ∧ s.queue = f :: q ∧
      flip G s.untouched f = 1 ∧
        t.score = s.score + 1 := by
  cases m with
  | «open» v => exact False.elim (hne (open_score hstep))
  | pass => exact False.elim (hne (pass_score hstep))
  | close =>
      obtain ⟨f, q, hqueue, hscore⟩ := close_score hstep
      have hflipNe : flip G s.untouched f ≠ 0 := by
        intro hzero
        apply hne
        rw [hscore, hzero, add_zero]
      have hflip : flip G s.untouched f = 1 :=
        zmod2_eq_one_of_ne_zero _ hflipNe
      exact ⟨f, q, rfl, hqueue, hflip, by rw [hscore, hflip]⟩

omit [Fintype V] in
/-- Every legal path either is pointwise score-neutral, or decomposes at its
last score-changing edge into an arbitrary prefix, that edge, and a neutral
suffix. -/
theorem StepPath.neutral_or_lastScoreChange
    {G : SimpleGraph V} {s t : State V} {ms : List (Move V)}
    (hpath : StepPath G s ms t) :
    ScoreNeutralPath G s ms t ∨
      ∃ (pre post : List (Move V)) (a b : State V) (m : Move V),
        ms = pre ++ m :: post ∧ StepPath G s pre a ∧
          step G a m = some b ∧ b.score ≠ a.score ∧
            ScoreNeutralPath G b post t := by
  induction hpath with
  | nil s => exact Or.inl (.nil s)
  | @cons s s' t m ms hstep tail ih =>
      rcases ih with hneutral | hlast
      · by_cases hscore : s'.score = s.score
        · exact Or.inl (.cons hstep hscore hneutral)
        · exact Or.inr ⟨[], ms, s, s', m, by simp,
            .nil s, hstep, hscore, hneutral⟩
      · obtain ⟨pre, post, a, b, n, hmoves, hpre, hn, hchange,
          hneutral⟩ := hlast
        exact Or.inr ⟨m :: pre, post, a, b, n, by simp [hmoves],
          .cons hstep hpre, hn, hchange, hneutral⟩

omit [Fintype V] in
/-- Score zero-to-one forces an exact last unit-charged CLOSE followed by a
pointwise neutral suffix. -/
theorem StepPath.exists_lastChargedClose
    {G : SimpleGraph V} {s t : State V} {ms : List (Move V)}
    (hpath : StepPath G s ms t) (hs : s.score = 0) (ht : t.score = 1) :
    ∃ (pre post : List (Move V)) (a b : State V) (f : V) (q : List V),
      ms = pre ++ .close :: post ∧ StepPath G s pre a ∧
        step G a .close = some b ∧ a.queue = f :: q ∧
          flip G a.untouched f = 1 ∧ b.score = a.score + 1 ∧
            ScoreNeutralPath G b post t := by
  rcases hpath.neutral_or_lastScoreChange with hneutral | hlast
  · have heq := hneutral.score_eq
    rw [hs, ht] at heq
    exact False.elim (one_ne_zero heq)
  · obtain ⟨pre, post, a, b, m, hmoves, hpre, hm, hchange,
      hneutral⟩ := hlast
    obtain ⟨f, q, rfl, hqueue, hflip, hscore⟩ :=
      scoreChange_step_is_chargedClose hm hchange
    exact ⟨pre, post, a, b, f, q, hmoves, hpre, hm, hqueue,
      hflip, hscore, hneutral⟩

omit [Fintype V] in
/-- A vertex queued at the end of a path was either already queued at the
start or was opened somewhere along the path. -/
theorem StepPath.mem_queue_source_or_open_mem
    {G : SimpleGraph V} {s t : State V} {ms : List (Move V)}
    (hpath : StepPath G s ms t) {r : V} (hr : r ∈ t.queue) :
    r ∈ s.queue ∨ Move.open r ∈ ms := by
  induction hpath with
  | nil => exact Or.inl hr
  | @cons s s' t m ms hstep tail ih =>
      rcases ih hr with hrs' | hopen
      · cases m with
        | «open» v =>
            simp only [step] at hstep
            split at hstep
            · cases hstep
              simp only [List.mem_append, List.mem_singleton] at hrs'
              rcases hrs' with hrs | rfl
              · exact Or.inl hrs
              · exact Or.inr (by simp)
            · contradiction
        | close =>
            simp only [step] at hstep
            split at hstep
            · contradiction
            · rename_i f q hqueue
              split at hstep
              · contradiction
              · cases hstep
                exact Or.inl (by rw [hqueue]; simp [hrs'])
        | pass =>
            simp only [step] at hstep
            split at hstep
            · cases hstep
              exact Or.inl hrs'
            · contradiction
      · exact Or.inr (by simp [hopen])

omit [Fintype V] in
/-- Applied after the last charged CLOSE, every vertex still queued at the
score-one target has exactly the two possible interval orders: it survived
behind the charged front, or its opener lies in the neutral suffix. -/
theorem queuedAtTarget_survivesLastClose_or_openedInNeutralSuffix
    {G : SimpleGraph V} {b t : State V} {post : List (Move V)}
    (hsuffix : ScoreNeutralPath G b post t) {r : V}
    (hr : r ∈ t.queue) :
    r ∈ b.queue ∨ Move.open r ∈ post :=
  hsuffix.toStepPath.mem_queue_source_or_open_mem hr

omit [Fintype V] in
theorem StepPath.append_last
    {G : SimpleGraph V} {s t u : State V}
    {ms : List (Move V)} {m : Move V}
    (hpath : StepPath G s ms t) (hstep : step G t m = some u) :
    StepPath G s (ms ++ [m]) u := by
  induction hpath with
  | nil => exact .cons hstep (.nil _)
  | cons hhead _ ih =>
      simpa using StepPath.cons hhead (ih hstep)

/-- An exact strategy prefix forgets to an ordinary legal move path while
retaining its endpoint. -/
theorem StrategyPrefix.exists_stepPath
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {root : OddStrategy G seat (initial (V := V))}
    {child : OddStrategy G seat s} {p : EdgeVector V}
    (hprefix : StrategyPrefix G seat root child p) :
    ∃ ms, StepPath G (initial (V := V)) ms s := by
  induction hprefix with
  | root => exact ⟨[], .nil _⟩
  | @choose s s' hseat m hstep child p parent ih =>
      obtain ⟨ms, hpath⟩ := ih
      exact ⟨ms ++ [m], hpath.append_last hstep⟩
  | @answer s s' hseat hasMove children m hstep p parent ih =>
      obtain ⟨ms, hpath⟩ := ih
      exact ⟨ms ++ [m], hpath.append_last hstep⟩

/-- Strategy-relative form: every score-one occurrence in an exact strategy
rooted at the score-zero initial state has a last unit-charged CLOSE and a
neutral suffix. -/
theorem StrategyPrefix.exists_lastChargedClose_of_score_one
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {root : OddStrategy G seat (initial (V := V))}
    {child : OddStrategy G seat s} {p : EdgeVector V}
    (hprefix : StrategyPrefix G seat root child p) (hscore : s.score = 1) :
    ∃ (ms pre post : List (Move V)) (a b : State V)
      (f : V) (q : List V),
      StepPath G (initial (V := V)) ms s ∧
        ms = pre ++ .close :: post ∧ StepPath G (initial (V := V)) pre a ∧
          step G a .close = some b ∧ a.queue = f :: q ∧
            flip G a.untouched f = 1 ∧ b.score = a.score + 1 ∧
              ScoreNeutralPath G b post s := by
  obtain ⟨ms, hpath⟩ := hprefix.exists_stepPath
  obtain ⟨pre, post, a, b, f, q, hmoves, hpre, hclose, hqueue,
      hflip, hchange, hneutral⟩ :=
    hpath.exists_lastChargedClose (by rfl) hscore
  exact ⟨ms, pre, post, a, b, f, q, hpath, hmoves, hpre, hclose,
    hqueue, hflip, hchange, hneutral⟩

/-! ## A reachable separated-debt history -/

def separatedDebtRel (x y : Fin 6) : Bool := decide (
  (x = 0 ∧ y = 1) ∨ (x = 4 ∧ y = 5))

def separatedDebtGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun x y ↦ separatedDebtRel x y = true

def separatedDebtAfterOpenFour : State (Fin 6) where
  untouched := {0, 1, 2, 3, 5}
  queue := [4]
  ko := true
  toMove := true
  score := 0

def separatedDebtBeforeChargedClose : State (Fin 6) where
  untouched := {1, 2, 3, 5}
  queue := [4, 0]
  ko := false
  toMove := false
  score := 0

def separatedDebtAfterChargedClose : State (Fin 6) where
  untouched := {1, 2, 3, 5}
  queue := [0]
  ko := false
  toMove := true
  score := 1

def separatedDebtSelectedState : State (Fin 6) where
  untouched := {1, 2, 3}
  queue := [0, 5]
  ko := false
  toMove := false
  score := 1

def separatedDebtFan : State (Fin 6) where
  untouched := {2, 3}
  queue := [0, 5, 1]
  ko := false
  toMove := true
  score := 1

theorem separatedDebt_dummyTwo : IsDummy separatedDebtGraph 2 := by
  intro v
  fin_cases v <;>
    simp [separatedDebtGraph, separatedDebtRel, SimpleGraph.fromRel_adj]

theorem separatedDebt_step_openFour :
    step separatedDebtGraph (initial (V := Fin 6)) (.open 4) =
      some separatedDebtAfterOpenFour := by
  simp [step, initial, separatedDebtAfterOpenFour]
  ext x
  fin_cases x <;> simp

theorem separatedDebt_step_openZero :
    step separatedDebtGraph separatedDebtAfterOpenFour (.open 0) =
      some separatedDebtBeforeChargedClose := by
  simp [step, separatedDebtAfterOpenFour, separatedDebtBeforeChargedClose]

theorem separatedDebt_step_chargedClose :
    step separatedDebtGraph separatedDebtBeforeChargedClose .close =
      some separatedDebtAfterChargedClose := by
  simp [step, separatedDebtBeforeChargedClose,
    separatedDebtAfterChargedClose, flip, separatedDebtGraph,
    separatedDebtRel, SimpleGraph.fromRel_adj]
  decide

theorem separatedDebt_step_openFive :
    step separatedDebtGraph separatedDebtAfterChargedClose (.open 5) =
      some separatedDebtSelectedState := by
  simp [step, separatedDebtAfterChargedClose, separatedDebtSelectedState]
  ext x
  fin_cases x <;> simp

theorem separatedDebt_step_selectedOpen :
    step separatedDebtGraph separatedDebtSelectedState (.open 1) =
      some separatedDebtFan := by
  simp [step, separatedDebtSelectedState, separatedDebtFan]

def separatedDebtPrefixMoves : List (Move (Fin 6)) :=
  [.open 4, .open 0, .close, .open 5]

theorem separatedDebt_initial_path :
    StepPath separatedDebtGraph (initial (V := Fin 6))
      separatedDebtPrefixMoves separatedDebtSelectedState := by
  exact .cons separatedDebt_step_openFour
    (.cons separatedDebt_step_openZero
      (.cons separatedDebt_step_chargedClose
        (.cons separatedDebt_step_openFive (.nil _))))

theorem separatedDebt_lastClose_charge_one :
    flip separatedDebtGraph separatedDebtBeforeChargedClose.untouched 4 = 1 := by
  simp [separatedDebtBeforeChargedClose, flip, separatedDebtGraph,
    separatedDebtRel, SimpleGraph.fromRel_adj]
  decide

/-- The post-charge suffix is pointwise neutral. -/
theorem separatedDebt_neutral_suffix :
    ScoreNeutralPath separatedDebtGraph separatedDebtAfterChargedClose
      [.open 5] separatedDebtSelectedState := by
  exact .cons separatedDebt_step_openFive rfl (.nil _)

/-- The queued separator-debt vertex `0` is a survivor behind the charged
front `4`, whereas the neighbour `5` which supplied that charge is opened
later in the neutral suffix.  The two causal roles are disjoint. -/
theorem separatedDebt_survivor_and_lateChargeNeighbor :
    (0 : Fin 6) ∈ separatedDebtAfterChargedClose.queue ∧
      (0 : Fin 6) ∈ separatedDebtSelectedState.queue ∧
      Move.open (5 : Fin 6) ∈ ([.open 5] : List (Move (Fin 6))) ∧
      (0 : Fin 6) ≠ 5 := by
  simp [separatedDebtAfterChargedClose, separatedDebtSelectedState]

theorem separatedDebt_selected_potential_zero :
    potential separatedDebtGraph separatedDebtSelectedState = 0 := by
  simp [potential, queueCut, separatedDebtSelectedState, flip,
    separatedDebtGraph, separatedDebtRel, SimpleGraph.fromRel_adj]
  decide

theorem separatedDebt_selectedOpen_increment_one :
    liveDegree separatedDebtGraph separatedDebtSelectedState 1 = 1 := by
  simp [liveDegree, flip, queueCut, separatedDebtSelectedState,
    separatedDebtGraph, separatedDebtRel, SimpleGraph.fromRel_adj]
  decide

theorem separatedDebt_fan_noLiveCut :
    NoLiveCut separatedDebtGraph separatedDebtFan := by
  intro u hu v hv
  fin_cases u <;> fin_cases v <;>
    simp [separatedDebtFan, liveSet, separatedDebtGraph, separatedDebtRel,
      SimpleGraph.fromRel_adj] at hu hv ⊢

/-- The initial-root legal history reaches precisely the separator-minimum
local scalar shape: score one, queue cut one, selected unit OPEN, followed by
a no-live-cut fan.  Legality alone therefore does not relate the last charged
front `4` to the surviving queued debt `0`. -/
theorem separatedDebt_reachable_selectedShape :
    ReachableFrom separatedDebtGraph (initial (V := Fin 6))
        separatedDebtSelectedState ∧
      separatedDebtSelectedState.score = 1 ∧
      queueCut separatedDebtGraph separatedDebtSelectedState.untouched
          separatedDebtSelectedState.queue = 1 ∧
      liveDegree separatedDebtGraph separatedDebtSelectedState 1 = 1 ∧
      NoLiveCut separatedDebtGraph separatedDebtFan := by
  refine ⟨⟨separatedDebtPrefixMoves, separatedDebt_initial_path⟩,
    rfl, ?_, separatedDebt_selectedOpen_increment_one,
    separatedDebt_fan_noLiveCut⟩
  have hp := separatedDebt_selected_potential_zero
  have hbase :
      1 + queueCut separatedDebtGraph {1, 2, 3} [0, 5] = 0 := by
    simpa [potential, separatedDebtSelectedState] using hp
  have hq : queueCut separatedDebtGraph {1, 2, 3} [0, 5] = 1 := by
    calc
      queueCut separatedDebtGraph {1, 2, 3} [0, 5] =
          0 + queueCut separatedDebtGraph {1, 2, 3} [0, 5] := by rw [zero_add]
      _ = (1 + 1) + queueCut separatedDebtGraph {1, 2, 3} [0, 5] := by
        rw [CharTwo.add_self_eq_zero]
      _ = 1 + (1 + queueCut separatedDebtGraph {1, 2, 3} [0, 5]) := by abel
      _ = 1 + 0 := by rw [hbase]
      _ = 1 := by rw [add_zero]
  simpa [separatedDebtSelectedState] using hq

/-! ## The same history as an exact initial-root public-policy occurrence -/

/-- An arbitrary total public policy, used only to fill universal siblings
outside the displayed occurrence. -/
noncomputable def arbitraryPublicPolicy
    (seat : Bool) (s : PublicState V) : PublicPolicy seat s := by
  by_cases ht : s.untouched = ∅ ∧ s.queue = []
  · exact .terminal s ht
  · have hnotTerminal : ¬Terminal s.toZeroState := by
      simpa [Terminal, PublicState.toZeroState] using ht
    have hasMove : ∃ m u, publicStep s m = some u := by
      have hc := not_terminal_has_step (G := (⊥ : SimpleGraph V))
        hnotTerminal
      simpa [PublicState.toZeroState, State.public] using
        publicHasMove_of_hasMove (⊥ : SimpleGraph V) s.toZeroState hc
    by_cases hturn : s.toMove = seat
    · exact .answer s hturn hasMove
        (fun m u hstep ↦ arbitraryPublicPolicy seat u)
    · let m := Classical.choose hasMove
      let hu := Classical.choose_spec hasMove
      let u := Classical.choose hu
      let hstep := Classical.choose_spec hu
      exact .choose s hturn m u hstep (arbitraryPublicPolicy seat u)
termination_by publicSeparatorRank s
decreasing_by
  · exact publicSeparatorRank_step_lt hstep
  · exact publicSeparatorRank_step_lt hstep

/-- A public policy recursively memoized by its full public state, preferring
the supplied state-dependent move whenever it is legal. -/
noncomputable def positionalPublicPolicy
    (seat : Bool) (preferred : PublicState V → Move V)
    (s : PublicState V) : PublicPolicy seat s := by
  by_cases ht : s.untouched = ∅ ∧ s.queue = []
  · exact .terminal s ht
  · have hnotTerminal : ¬Terminal s.toZeroState := by
      simpa [Terminal, PublicState.toZeroState] using ht
    have hasMove : ∃ m u, publicStep s m = some u := by
      have hc := not_terminal_has_step (G := (⊥ : SimpleGraph V))
        hnotTerminal
      simpa [PublicState.toZeroState, State.public] using
        publicHasMove_of_hasMove (⊥ : SimpleGraph V) s.toZeroState hc
    by_cases hturn : s.toMove = seat
    · exact .answer s hturn hasMove
        (fun m u hstep ↦ positionalPublicPolicy seat preferred u)
    · by_cases hp : ∃ u, publicStep s (preferred s) = some u
      · let u := Classical.choose hp
        let hstep := Classical.choose_spec hp
        exact .choose s hturn (preferred s) u hstep
          (positionalPublicPolicy seat preferred u)
      · let m := Classical.choose hasMove
        let hu := Classical.choose_spec hasMove
        let u := Classical.choose hu
        let hstep := Classical.choose_spec hu
        exact .choose s hturn m u hstep
          (positionalPublicPolicy seat preferred u)
termination_by publicSeparatorRank s
decreasing_by
  · exact publicSeparatorRank_step_lt hstep
  · exact publicSeparatorRank_step_lt hstep
  · exact publicSeparatorRank_step_lt hstep

omit [Fintype V] in
theorem positionalPublicPolicy_eq_choose_preferred
    (seat : Bool) (preferred : PublicState V → Move V)
    (s u : PublicState V)
    (ht : ¬(s.untouched = ∅ ∧ s.queue = []))
    (hturn : s.toMove ≠ seat)
    (hstep : publicStep s (preferred s) = some u) :
    ∃ (hturn' : s.toMove ≠ seat)
      (hstep' : publicStep s (preferred s) = some u),
      positionalPublicPolicy seat preferred s =
        .choose s hturn' (preferred s) u hstep'
          (positionalPublicPolicy seat preferred u) := by
  rw [positionalPublicPolicy.eq_def]
  simp only [dif_neg ht, dif_neg hturn]
  split
  · rename_i hp
    have hu : Classical.choose hp = u := by
      have hc := Classical.choose_spec hp
      exact Option.some.inj (hc.symm.trans hstep)
    subst u
    refine ⟨hturn, hstep, ?_⟩
    congr
  · rename_i hp
    exact False.elim (hp ⟨u, hstep⟩)

omit [Fintype V] in
theorem positionalPublicPolicy_eq_answer
    (seat : Bool) (preferred : PublicState V → Move V)
    (s : PublicState V)
    (ht : ¬(s.untouched = ∅ ∧ s.queue = []))
    (hturn : s.toMove = seat) :
    ∃ (hasMove : ∃ m u, publicStep s m = some u),
      positionalPublicPolicy seat preferred s =
        .answer s hturn hasMove
          (fun _ u _ ↦ positionalPublicPolicy seat preferred u) := by
  rw [positionalPublicPolicy.eq_def]
  simp only [dif_neg ht, dif_pos hturn]
  have hnotTerminal : ¬Terminal s.toZeroState := by
    simpa [Terminal, PublicState.toZeroState] using ht
  have hasMove : ∃ m u, publicStep s m = some u := by
    have hc := not_terminal_has_step (G := (⊥ : SimpleGraph V))
      hnotTerminal
    simpa [PublicState.toZeroState, State.public] using
      publicHasMove_of_hasMove (⊥ : SimpleGraph V) s.toZeroState hc
  refine ⟨hasMove, ?_⟩
  trivial

def separatedDebtRootSelector (s : PublicState (Fin 6)) : Move (Fin 6) :=
  if s = (initial (V := Fin 6)).public then .open 4
  else if s = separatedDebtBeforeChargedClose.public then .close
  else if s = separatedDebtSelectedState.public then .open 1
  else .open 3

noncomputable def separatedDebtPositionalInitialPolicy :
    PublicPolicy true (initial (V := Fin 6)).public :=
  positionalPublicPolicy true separatedDebtRootSelector
    (initial (V := Fin 6)).public

noncomputable def separatedDebtPositionalSelectedPolicy :
    PublicPolicy true separatedDebtSelectedState.public :=
  positionalPublicPolicy true separatedDebtRootSelector
    separatedDebtSelectedState.public

theorem separatedDebtRootSelector_initial :
    separatedDebtRootSelector (initial (V := Fin 6)).public = .open 4 := by
  simp [separatedDebtRootSelector]

theorem separatedDebtRootSelector_beforeClose :
    separatedDebtRootSelector separatedDebtBeforeChargedClose.public =
      .close := by
  have hne : separatedDebtBeforeChargedClose.public ≠
      (initial (V := Fin 6)).public := by
    intro h
    have hq := congrArg PublicState.queue h
    simp [separatedDebtBeforeChargedClose, initial, State.public] at hq
  simp [separatedDebtRootSelector, hne]

theorem separatedDebtRootSelector_selected :
    separatedDebtRootSelector separatedDebtSelectedState.public = .open 1 := by
  have hinit : separatedDebtSelectedState.public ≠
      (initial (V := Fin 6)).public := by
    intro h
    have hq := congrArg PublicState.queue h
    simp [separatedDebtSelectedState, initial, State.public] at hq
  have hclose : separatedDebtSelectedState.public ≠
      separatedDebtBeforeChargedClose.public := by
    intro h
    have hq := congrArg PublicState.queue h
    simp [separatedDebtSelectedState, separatedDebtBeforeChargedClose,
      State.public] at hq
  simp [separatedDebtRootSelector, hinit, hclose]

/-- A universal public node whose one distinguished legal child is fixed and
whose irrelevant siblings are filled arbitrarily. -/
noncomputable def publicAnswerWithChild
    (seat : Bool) (s : PublicState V) (hseat : s.toMove = seat)
    (m₀ : Move V) (u₀ : PublicState V)
    (h₀ : publicStep s m₀ = some u₀) (child₀ : PublicPolicy seat u₀) :
    PublicPolicy seat s :=
  .answer s hseat ⟨m₀, u₀, h₀⟩
    (fun m u hstep ↦ by
      classical
      by_cases hm : m = m₀
      · subst m
        have hu : u = u₀ := by
          rw [h₀] at hstep
          exact Option.some.inj hstep.symm
        subst u
        exact child₀
      · exact arbitraryPublicPolicy seat u)

theorem separatedDebt_public_openFour :
    publicStep (initial (V := Fin 6)).public (.open 4) =
      some separatedDebtAfterOpenFour.public := by
  rw [← step_public separatedDebtGraph _ _, separatedDebt_step_openFour]
  rfl

theorem separatedDebt_public_openZero :
    publicStep separatedDebtAfterOpenFour.public (.open 0) =
      some separatedDebtBeforeChargedClose.public := by
  rw [← step_public separatedDebtGraph _ _, separatedDebt_step_openZero]
  rfl

theorem separatedDebt_public_chargedClose :
    publicStep separatedDebtBeforeChargedClose.public .close =
      some separatedDebtAfterChargedClose.public := by
  rw [← step_public separatedDebtGraph _ _, separatedDebt_step_chargedClose]
  rfl

theorem separatedDebt_public_openFive :
    publicStep separatedDebtAfterChargedClose.public (.open 5) =
      some separatedDebtSelectedState.public := by
  rw [← step_public separatedDebtGraph _ _, separatedDebt_step_openFive]
  rfl

theorem separatedDebt_public_selectedOpen :
    publicStep separatedDebtSelectedState.public (.open 1) =
      some separatedDebtFan.public := by
  rw [← step_public separatedDebtGraph _ _, separatedDebt_step_selectedOpen]
  rfl

/-- The same causal history is an occurrence in a policy generated solely
from the current public state.  Thus history-dependent filler choices are not
responsible for the survivor branch. -/
theorem separatedDebt_positionalPolicy_initialOccurrence :
    PublicPolicyNode true separatedDebtPositionalInitialPolicy
      separatedDebtPositionalSelectedPolicy := by
  change PublicPolicyNode true
    (positionalPublicPolicy true separatedDebtRootSelector
      (initial (V := Fin 6)).public)
    (positionalPublicPolicy true separatedDebtRootSelector
      separatedDebtSelectedState.public)
  have hopenFour :
      publicStep (initial (V := Fin 6)).public
          (separatedDebtRootSelector (initial (V := Fin 6)).public) =
        some separatedDebtAfterOpenFour.public := by
    simpa [separatedDebtRootSelector_initial] using separatedDebt_public_openFour
  obtain ⟨_, _, hroot⟩ := positionalPublicPolicy_eq_choose_preferred
    true separatedDebtRootSelector (initial (V := Fin 6)).public
      separatedDebtAfterOpenFour.public
      (by
        intro h
        have hU := h.1
        change (Finset.univ : Finset (Fin 6)) = ∅ at hU
        have hfour : (4 : Fin 6) ∈ (Finset.univ : Finset (Fin 6)) :=
          Finset.mem_univ _
        rw [hU] at hfour
        simp at hfour)
      (by decide) hopenFour
  rw [hroot]
  apply PublicPolicyNode.choose
  obtain ⟨_, hopenAnswer⟩ := positionalPublicPolicy_eq_answer
    true separatedDebtRootSelector separatedDebtAfterOpenFour.public
      (by
        intro h
        have hq := h.2
        simp [separatedDebtAfterOpenFour, State.public] at hq)
      rfl
  rw [hopenAnswer]
  apply PublicPolicyNode.answer (m := .open 0)
    (hstep := separatedDebt_public_openZero)
  have hclose :
      publicStep separatedDebtBeforeChargedClose.public
          (separatedDebtRootSelector separatedDebtBeforeChargedClose.public) =
        some separatedDebtAfterChargedClose.public := by
    simpa [separatedDebtRootSelector_beforeClose] using
      separatedDebt_public_chargedClose
  obtain ⟨_, _, hbeforeClose⟩ := positionalPublicPolicy_eq_choose_preferred
    true separatedDebtRootSelector separatedDebtBeforeChargedClose.public
      separatedDebtAfterChargedClose.public
      (by
        intro h
        have hq := h.2
        simp [separatedDebtBeforeChargedClose, State.public] at hq)
      (by decide) hclose
  rw [hbeforeClose]
  apply PublicPolicyNode.choose
  obtain ⟨_, hafterClose⟩ := positionalPublicPolicy_eq_answer
    true separatedDebtRootSelector separatedDebtAfterChargedClose.public
      (by
        intro h
        have hq := h.2
        simp [separatedDebtAfterChargedClose, State.public] at hq)
      rfl
  rw [hafterClose]
  apply PublicPolicyNode.answer (m := .open 5)
    (hstep := separatedDebt_public_openFive)
  exact PublicPolicyNode.root _

theorem separatedDebt_fan_odd :
    OddWins separatedDebtGraph true separatedDebtFan :=
  oddWins_of_noLiveCut true separatedDebtFan separatedDebt_fan_noLiveCut
    (by decide)

def separatedDebtFanStrategy :
    OddStrategy separatedDebtGraph true separatedDebtFan :=
  PreferredOdd.preferredOddStrategy separatedDebtGraph true (.open 3)
    separatedDebtFan separatedDebt_fan_odd

def separatedDebtSelectedStrategy :
    OddStrategy separatedDebtGraph true separatedDebtSelectedState :=
  .choose separatedDebtSelectedState (by decide) (.open 1) separatedDebtFan
    separatedDebt_step_selectedOpen separatedDebtFanStrategy

def separatedDebtSelectedPolicy :
    PublicPolicy true separatedDebtSelectedState.public :=
  separatedDebtSelectedStrategy.toPublicPolicy

noncomputable def separatedDebtAfterClosePolicy :
    PublicPolicy true separatedDebtAfterChargedClose.public :=
  publicAnswerWithChild true separatedDebtAfterChargedClose.public rfl
    (.open 5) separatedDebtSelectedState.public
      separatedDebt_public_openFive separatedDebtSelectedPolicy

noncomputable def separatedDebtBeforeClosePolicy :
    PublicPolicy true separatedDebtBeforeChargedClose.public :=
  .choose separatedDebtBeforeChargedClose.public (by decide) .close
    separatedDebtAfterChargedClose.public separatedDebt_public_chargedClose
      separatedDebtAfterClosePolicy

noncomputable def separatedDebtAfterOpenFourPolicy :
    PublicPolicy true separatedDebtAfterOpenFour.public :=
  publicAnswerWithChild true separatedDebtAfterOpenFour.public rfl
    (.open 0) separatedDebtBeforeChargedClose.public
      separatedDebt_public_openZero separatedDebtBeforeClosePolicy

noncomputable def separatedDebtInitialPolicy :
    PublicPolicy true (initial (V := Fin 6)).public :=
  .choose (initial (V := Fin 6)).public (by decide) (.open 4)
    separatedDebtAfterOpenFour.public separatedDebt_public_openFour
      separatedDebtAfterOpenFourPolicy

/-- The selected separator state is an actual constructor-sensitive
descendant occurrence of one initial-root public policy. -/
theorem separatedDebt_selectedPolicy_initialOccurrence :
    PublicPolicyNode true separatedDebtInitialPolicy
      separatedDebtSelectedPolicy := by
  apply PublicPolicyNode.choose
  apply PublicPolicyNode.answer (m := .open 0)
    (hstep := separatedDebt_public_openZero)
  · apply PublicPolicyNode.choose
    apply PublicPolicyNode.answer (m := .open 5)
      (hstep := separatedDebt_public_openFive)
    simpa [separatedDebtAfterClosePolicy, publicAnswerWithChild] using
      (PublicPolicyNode.root separatedDebtSelectedPolicy)

theorem separatedDebt_selected_wellFormed :
    WellFormed separatedDebtSelectedState := by
  simp [WellFormed, separatedDebtSelectedState]

theorem separatedDebt_fan_potential_one :
    potential separatedDebtGraph separatedDebtFan = 1 := by
  simp [potential, queueCut, separatedDebtFan, flip, separatedDebtGraph,
    separatedDebtRel, SimpleGraph.fromRel_adj]
  decide

theorem separatedDebt_fan_wellFormed :
    WellFormed separatedDebtFan := by
  simp [WellFormed, separatedDebtFan]

/-- The exact occurrence is on separator sheet one. -/
theorem separatedDebt_selectedPolicy_sheet_one :
    PublicPolicySeparatorSheet 2
      (isolatedGraphSeparatorFunctional separatedDebtGraph 2
        separatedDebt_dummyTwo) true separatedDebtSelectedPolicy 1 := by
  exact (separatedDebtSelectedStrategy.toPublicPolicy_separatorOne_iff_potential_zero
    separatedDebt_dummyTwo separatedDebt_selected_wellFormed).2
      separatedDebt_selected_potential_zero

theorem separatedDebt_fanPolicy_sheet_zero :
    PublicPolicySeparatorSheet 2
      (isolatedGraphSeparatorFunctional separatedDebtGraph 2
        separatedDebt_dummyTwo) true
      separatedDebtFanStrategy.toPublicPolicy 0 := by
  have hcanonical := separatedDebtFanStrategy.toPublicPolicy_canonicalSeparatorSheet
    separatedDebt_dummyTwo separatedDebt_fan_wellFormed
  simpa [separatedDebt_fan_potential_one, CharTwo.add_self_eq_zero] using
    hcanonical

/-- The displayed selected occurrence is already an immediate sheet-one
minimum: its sole retained child is uniformly sheet zero. -/
theorem separatedDebt_selectedPolicy_immediateMinimal :
    PublicPolicySeparatorOneImmediateMinimal 2
      (isolatedGraphSeparatorFunctional separatedDebtGraph 2
        separatedDebt_dummyTwo) true separatedDebtSelectedPolicy := by
  refine ⟨separatedDebt_selectedPolicy_sheet_one, ?_⟩
  intro hchildOne
  obtain ⟨z, hz⟩ := separatedDebtFanStrategy.toPublicPolicy.exists_affineMoment
  have hzero := separatedDebt_fanPolicy_sheet_zero z hz
  have hone := hchildOne z hz
  exact zero_ne_one (hzero.symm.trans hone)

/-- The initial-root public-policy occurrence realizes the survivor branch:
the last charged front and its charging neighbour are `4,5`, while the
separator debt is the earlier queued vertex `0`.  What it intentionally does
not assert is that the whole initial public policy lies on sheet one; that
extra global hypothesis is equivalent to the missing odd-counterstrategy
coupling. -/
theorem separatedDebt_initialOccurrence_survivor_boundary :
    PublicPolicyNode true separatedDebtInitialPolicy
        separatedDebtSelectedPolicy ∧
      PublicPolicySeparatorSheet 2
        (isolatedGraphSeparatorFunctional separatedDebtGraph 2
          separatedDebt_dummyTwo) true separatedDebtSelectedPolicy 1 ∧
      (0 : Fin 6) ∈ separatedDebtAfterChargedClose.queue ∧
      (0 : Fin 6) ∈ separatedDebtSelectedState.queue ∧
      flip separatedDebtGraph separatedDebtBeforeChargedClose.untouched 4 = 1 := by
  exact ⟨separatedDebt_selectedPolicy_initialOccurrence,
    separatedDebt_selectedPolicy_sheet_one, by simp [separatedDebtAfterChargedClose],
    by simp [separatedDebtSelectedState], separatedDebt_lastClose_charge_one⟩

/-- The survivor opener `OPEN 0` cannot be commuted to after the charged
CLOSE by the ordinary square: before it is opened, the singleton queue is
still behind the ko wall and `CLOSE` is illegal. -/
theorem separatedDebt_survivorOpener_breaks_ko_wall :
    step separatedDebtGraph separatedDebtAfterOpenFour .close = none := by
  simp [step, separatedDebtAfterOpenFour]

def separatedDebtChargeNeighborOpenedEarly : State (Fin 6) where
  untouched := {0, 1, 2, 3}
  queue := [4, 5]
  ko := false
  toMove := false
  score := 0

def separatedDebtEarlyNeighborClose : State (Fin 6) where
  untouched := {0, 1, 2, 3}
  queue := [5]
  ko := false
  toMove := true
  score := 0

theorem separatedDebt_openChargeNeighborEarly :
    step separatedDebtGraph separatedDebtAfterOpenFour (.open 5) =
      some separatedDebtChargeNeighborOpenedEarly := by
  simp [step, separatedDebtAfterOpenFour,
    separatedDebtChargeNeighborOpenedEarly]
  ext x
  fin_cases x <;> simp

/-- Conversely, moving the charging neighbour `OPEN 5` to before the CLOSE
removes it from the untouched set and neutralizes that CLOSE.  The reordered
history is therefore on score sheet zero rather than the selected occurrence's
score-one sheet. -/
theorem separatedDebt_earlyChargeNeighbor_neutralizes_close :
    step separatedDebtGraph separatedDebtChargeNeighborOpenedEarly .close =
      some separatedDebtEarlyNeighborClose ∧
      separatedDebtEarlyNeighborClose.score = 0 := by
  constructor
  · simp [step, separatedDebtChargeNeighborOpenedEarly,
      separatedDebtEarlyNeighborClose, flip, separatedDebtGraph,
      separatedDebtRel, SimpleGraph.fromRel_adj]
    decide
  · rfl

/-! ## The complementary neutral-suffix debt order -/

/-- Replacing the old debt edge `0--1` by `5--1` makes the vertex opened in
the neutral suffix itself the queued separator debt. -/
def lateDebtRel (x y : Fin 6) : Bool := decide (
  (x = 4 ∧ y = 5) ∨ (x = 1 ∧ y = 5))

def lateDebtGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun x y ↦ lateDebtRel x y = true

theorem lateDebt_dummyTwo : IsDummy lateDebtGraph 2 := by
  intro v
  fin_cases v <;>
    simp [lateDebtGraph, lateDebtRel, SimpleGraph.fromRel_adj]

theorem lateDebt_step_openFour :
    step lateDebtGraph (initial (V := Fin 6)) (.open 4) =
      some separatedDebtAfterOpenFour := by
  simp [step, initial, separatedDebtAfterOpenFour]
  ext x
  fin_cases x <;> simp

theorem lateDebt_step_openZero :
    step lateDebtGraph separatedDebtAfterOpenFour (.open 0) =
      some separatedDebtBeforeChargedClose := by
  simp [step, separatedDebtAfterOpenFour, separatedDebtBeforeChargedClose]

theorem lateDebt_step_chargedClose :
    step lateDebtGraph separatedDebtBeforeChargedClose .close =
      some separatedDebtAfterChargedClose := by
  simp [step, separatedDebtBeforeChargedClose,
    separatedDebtAfterChargedClose, flip, lateDebtGraph,
    lateDebtRel, SimpleGraph.fromRel_adj]
  decide

theorem lateDebt_step_openFive :
    step lateDebtGraph separatedDebtAfterChargedClose (.open 5) =
      some separatedDebtSelectedState := by
  simp [step, separatedDebtAfterChargedClose, separatedDebtSelectedState]
  ext x
  fin_cases x <;> simp

theorem lateDebt_step_selectedOpen :
    step lateDebtGraph separatedDebtSelectedState (.open 1) =
      some separatedDebtFan := by
  simp [step, separatedDebtSelectedState, separatedDebtFan]

theorem lateDebt_initial_path :
    StepPath lateDebtGraph (initial (V := Fin 6))
      separatedDebtPrefixMoves separatedDebtSelectedState := by
  exact .cons lateDebt_step_openFour
    (.cons lateDebt_step_openZero
      (.cons lateDebt_step_chargedClose
        (.cons lateDebt_step_openFive (.nil _))))

theorem lateDebt_neutral_suffix :
    ScoreNeutralPath lateDebtGraph separatedDebtAfterChargedClose
      [.open 5] separatedDebtSelectedState := by
  exact .cons lateDebt_step_openFive rfl (.nil _)

theorem lateDebt_selected_potential_zero :
    potential lateDebtGraph separatedDebtSelectedState = 0 := by
  simp [potential, queueCut, separatedDebtSelectedState, flip,
    lateDebtGraph, lateDebtRel, SimpleGraph.fromRel_adj]
  decide

theorem lateDebt_fan_noLiveCut :
    NoLiveCut lateDebtGraph separatedDebtFan := by
  intro u hu v hv
  fin_cases u <;> fin_cases v <;>
    simp [separatedDebtFan, liveSet, lateDebtGraph, lateDebtRel,
      SimpleGraph.fromRel_adj] at hu hv ⊢

theorem lateDebt_fan_odd : OddWins lateDebtGraph true separatedDebtFan :=
  oddWins_of_noLiveCut true separatedDebtFan lateDebt_fan_noLiveCut (by decide)

def lateDebtFanStrategy : OddStrategy lateDebtGraph true separatedDebtFan :=
  PreferredOdd.preferredOddStrategy lateDebtGraph true (.open 3)
    separatedDebtFan lateDebt_fan_odd

def lateDebtSelectedStrategy :
    OddStrategy lateDebtGraph true separatedDebtSelectedState :=
  .choose separatedDebtSelectedState (by decide) (.open 1) separatedDebtFan
    lateDebt_step_selectedOpen lateDebtFanStrategy

def lateDebtSelectedPolicy : PublicPolicy true separatedDebtSelectedState.public :=
  lateDebtSelectedStrategy.toPublicPolicy

noncomputable def lateDebtAfterClosePolicy :
    PublicPolicy true separatedDebtAfterChargedClose.public :=
  publicAnswerWithChild true separatedDebtAfterChargedClose.public rfl
    (.open 5) separatedDebtSelectedState.public separatedDebt_public_openFive
      lateDebtSelectedPolicy

noncomputable def lateDebtBeforeClosePolicy :
    PublicPolicy true separatedDebtBeforeChargedClose.public :=
  .choose separatedDebtBeforeChargedClose.public (by decide) .close
    separatedDebtAfterChargedClose.public separatedDebt_public_chargedClose
      lateDebtAfterClosePolicy

noncomputable def lateDebtAfterOpenFourPolicy :
    PublicPolicy true separatedDebtAfterOpenFour.public :=
  publicAnswerWithChild true separatedDebtAfterOpenFour.public rfl
    (.open 0) separatedDebtBeforeChargedClose.public
      separatedDebt_public_openZero lateDebtBeforeClosePolicy

noncomputable def lateDebtInitialPolicy :
    PublicPolicy true (initial (V := Fin 6)).public :=
  .choose (initial (V := Fin 6)).public (by decide) (.open 4)
    separatedDebtAfterOpenFour.public separatedDebt_public_openFour
      lateDebtAfterOpenFourPolicy

theorem lateDebt_selectedPolicy_initialOccurrence :
    PublicPolicyNode true lateDebtInitialPolicy lateDebtSelectedPolicy := by
  apply PublicPolicyNode.choose
  apply PublicPolicyNode.answer (m := .open 0)
    (hstep := separatedDebt_public_openZero)
  · apply PublicPolicyNode.choose
    apply PublicPolicyNode.answer (m := .open 5)
      (hstep := separatedDebt_public_openFive)
    simpa [lateDebtAfterClosePolicy, publicAnswerWithChild] using
      (PublicPolicyNode.root lateDebtSelectedPolicy)

theorem lateDebt_selectedPolicy_sheet_one :
    PublicPolicySeparatorSheet 2
      (isolatedGraphSeparatorFunctional lateDebtGraph 2 lateDebt_dummyTwo)
      true lateDebtSelectedPolicy 1 := by
  exact (lateDebtSelectedStrategy.toPublicPolicy_separatorOne_iff_potential_zero
    lateDebt_dummyTwo separatedDebt_selected_wellFormed).2
      lateDebt_selected_potential_zero

/-- The complementary branch is also realized at an exact initial-root
occurrence: the queued separator partner `5` was opened only after the last
charged CLOSE, inside its neutral suffix. -/
theorem lateDebt_initialOccurrence_openedInNeutralSuffix_boundary :
    PublicPolicyNode true lateDebtInitialPolicy lateDebtSelectedPolicy ∧
      PublicPolicySeparatorSheet 2
        (isolatedGraphSeparatorFunctional lateDebtGraph 2 lateDebt_dummyTwo)
        true lateDebtSelectedPolicy 1 ∧
      Move.open (5 : Fin 6) ∈ ([.open 5] : List (Move (Fin 6))) ∧
      (5 : Fin 6) ∈ separatedDebtSelectedState.queue ∧
      (5 : Fin 6) ∉ separatedDebtAfterChargedClose.queue ∧
      liveDegree lateDebtGraph separatedDebtSelectedState 1 = 1 := by
  refine ⟨lateDebt_selectedPolicy_initialOccurrence,
    lateDebt_selectedPolicy_sheet_one, by simp,
    by simp [separatedDebtSelectedState],
    by simp [separatedDebtAfterChargedClose], ?_⟩
  simp [liveDegree, flip, queueCut, separatedDebtSelectedState,
    lateDebtGraph, lateDebtRel, SimpleGraph.fromRel_adj]
  decide

/-- Commuting the suffix debt opener before the charged CLOSE destroys the
charge, so this interval order also supplies no same-score square. -/
theorem lateDebt_earlyDebtOpener_neutralizes_close :
    step lateDebtGraph separatedDebtChargeNeighborOpenedEarly .close =
      some separatedDebtEarlyNeighborClose ∧
      separatedDebtEarlyNeighborClose.score = 0 := by
  constructor
  · simp [step, separatedDebtChargeNeighborOpenedEarly,
      separatedDebtEarlyNeighborClose, flip, lateDebtGraph,
      lateDebtRel, SimpleGraph.fromRel_adj]
    decide
  · rfl

end

end Ogdoad.Fifo
