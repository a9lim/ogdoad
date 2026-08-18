import Ogdoad.FifoAffine
import Ogdoad.FifoCausal

/-!
# The isolated FIFO dummy as a neutral two-event interval

Opening the isolated dummy at an empty root and later closing it deletes two
turns and contributes no score.  This file pins the exact operational content
of that observation.  After one intervening real OPEN, dummy deletion misses
the corresponding dummy-free state precisely in the singleton `ko` bit.
After two distinct intervening real OPENs, that wall is cleared and deletion
is an exact equality of states.

This is a local strategy-stealing interface, not the arbitrary-graph FIFO
linking theorem.  In particular, while the dummy interval is open, ownership
of the projected real events is reversed; the exact endpoint equality does
not by itself make an attacker strategy compatible with both histories.

The final section records two distinct obstructions.  First, commuting
schedule diamonds generate only augmentation-zero formal chains and hence
cannot by themselves generate the odd affine chain required by linking.
Second, an explicit reachable conditioned position with an active neutral
dummy interval is nevertheless winning for the odd seeker.  Neither result
is a counterexample at the initial root; both isolate work that a genuinely
causal ancestry argument must still do.
-/

namespace Ogdoad.Fifo

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Fixed-policy nodes and charged-close extraction -/

omit [Fintype V] in
/-- The `InOddStrategy` relation in `Fifo.lean` is indexed by an
`OddWins` proof and hence cannot distinguish two policies at the same state. -/
theorem inOddStrategy_proof_irrelevant
    {G : SimpleGraph V} {seat : Bool} {s t : State V}
    (h₁ h₂ : OddWins G seat s) :
    InOddStrategy G seat h₁ t ↔ InOddStrategy G seat h₂ t := by
  have heq : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

omit [Fintype V] in
/-- The same collapse applies to the CLOSE-first certificate: it can
state that such a witness exists at the public state, but not that a supplied
`OddWins` proof denotes that particular policy. -/
theorem oddStrategyCloseFirst_proof_irrelevant
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (h₁ h₂ : OddWins G seat s) :
    OddStrategyCloseFirst h₁ ↔ OddStrategyCloseFirst h₂ := by
  have heq : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

omit [Fintype V] in
/-- Likewise, clear-deviation membership is a public-state existence
claim rather than membership in a distinguishable fixed policy. -/
theorem oddStrategyHasClearDeviation_proof_irrelevant
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (h₁ h₂ : OddWins G seat s) :
    OddStrategyHasClearDeviation h₁ ↔
      OddStrategyHasClearDeviation h₂ := by
  have heq : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

/-- The unrestricted full-edge initial factor condition is also equivalent
to linking, although `FifoAffine` only needs its forward implication.  In the
reverse direction the quantified strategy type is empty, so this equivalence
is an audit of vacuity, not a causal construction theorem. -/
theorem initialAncestryFactorExtensionAt_iff_linking
    {G : SimpleGraph V} {d : V} {seat : Bool} (hd : IsDummy G d) :
    InitialAncestryFactorExtensionAt G d seat ↔
      EvenWins G seat (initial (V := V)) := by
  constructor
  · intro hfactor
    exact initialAncestryFactorExtensionAt_implies_linking hfactor hd
  · intro heven _ strategy
    have hno : ¬OddWins G seat (initial (V := V)) :=
      (linking_at_iff_noOddCounterstrategy hd seat).mp heven
    exact False.elim (hno strategy.toOddWins)

/-- Exact subtree membership for one data-carrying strategy.  At an attacker
node only its stored child is retained; at a defender node every legal child
is retained.  The descendant strategy itself is an index, so proof
irrelevance of this proposition does not identify different policies. -/
inductive StrategyNode (G : SimpleGraph V) (seat : Bool) :
    {s : State V} → OddStrategy G seat s →
      {t : State V} → OddStrategy G seat t → Prop
  | root {s : State V} (strategy : OddStrategy G seat s) :
      StrategyNode G seat strategy strategy
  | choose {s s' t : State V} {hseat : s.toMove ≠ seat}
      {m : Move V} {hstep : step G s m = some s'}
      {child : OddStrategy G seat s'} {desc : OddStrategy G seat t}
      (hdesc : StrategyNode G seat child desc) :
      StrategyNode G seat
        (OddStrategy.choose s hseat m s' hstep child) desc
  | answer {s s' t : State V} {hseat : s.toMove = seat}
      {hasMove : ∃ m u, step G s m = some u}
      {children : ∀ m u, step G s m = some u → OddStrategy G seat u}
      {m : Move V} {hstep : step G s m = some s'}
      {desc : OddStrategy G seat t}
      (hdesc : StrategyNode G seat (children m s' hstep) desc) :
      StrategyNode G seat
        (OddStrategy.answer s hseat hasMove children) desc

/-- The move stored at an attacker node of an exact strategy. -/
def OddStrategy.selectedMove
    {G : SimpleGraph V} {seat : Bool} {s : State V} :
    OddStrategy G seat s → Option (Move V)
  | .terminal .. => none
  | .choose _ _ m _ _ _ => some m
  | .answer .. => none

omit [Fintype V] in
/-- Exact subtree membership is transitive. -/
theorem StrategyNode.trans
    {G : SimpleGraph V} {seat : Bool} {r s t : State V}
    {root : OddStrategy G seat r} {middle : OddStrategy G seat s}
    {desc : OddStrategy G seat t}
    (hrs : StrategyNode G seat root middle)
    (hst : StrategyNode G seat middle desc) :
    StrategyNode G seat root desc := by
  induction hrs with
  | root => exact hst
  | choose hchild ih => exact StrategyNode.choose (ih hst)
  | answer hchild ih => exact StrategyNode.answer (ih hst)

omit [Fintype V] in
/-- Game rank is nonincreasing down an exact strategy tree. -/
theorem StrategyNode.rank_le
    {G : SimpleGraph V} {seat : Bool} {r t : State V}
    {root : OddStrategy G seat r} {desc : OddStrategy G seat t}
    (h : StrategyNode G seat root desc) : rank t ≤ rank r := by
  induction h with
  | root => exact le_rfl
  | @choose s s' t hseat m hstep child desc hchild ih =>
      exact le_trans ih (Nat.le_of_lt (rank_step_lt hstep))
  | @answer s s' t hseat hasMove children m hstep desc hchild ih =>
      exact le_trans ih (Nat.le_of_lt (rank_step_lt hstep))

omit [Fintype V] in
/-- If every node of one exact odd strategy stays on score sheet one,
translating its root by one yields a transition-by-transition neutral strategy
for the same physical player. -/
theorem OddStrategy.one_subtree_translates_neutral
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (strategy : OddStrategy G seat s)
    (hone : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat strategy desc → t.score = 1) :
    TreeNeutralWins G (!seat) (scoreTranslate 1 s) := by
  induction strategy with
  | terminal s hterminal _ =>
      have hs1 : s.score = 1 := hone (StrategyNode.root _)
      refine TreeNeutralWins.terminal (scoreTranslate 1 s) ?_ ?_
      · simpa [Terminal, scoreTranslate] using hterminal
      · simp [scoreTranslate, hs1, CharTwo.add_self_eq_zero]
  | choose s hseat m s' hstep child ih =>
      have hs1 : s.score = 1 := hone (StrategyNode.root _)
      have hlocal : StrategyNode G seat
          (OddStrategy.choose s hseat m s' hstep child) child :=
        StrategyNode.choose (StrategyNode.root child)
      have hs'1 : s'.score = 1 := hone hlocal
      have hone' : ∀ {t : State V} {desc : OddStrategy G seat t},
          StrategyNode G seat child desc → t.score = 1 := by
        intro t desc ht
        exact hone (hlocal.trans ht)
      refine TreeNeutralWins.choose (scoreTranslate 1 s) ?_ m
        (scoreTranslate 1 s') ?_ ?_ (ih hone')
      · simpa [scoreTranslate] using Bool.eq_not_iff.mpr hseat
      · rw [step_scoreTranslate, hstep]
        simp
      · simp [scoreTranslate, hs1, hs'1, CharTwo.add_self_eq_zero]
  | answer s hseat hasMove children ih =>
      have hs1 : s.score = 1 := hone (StrategyNode.root _)
      refine TreeNeutralWins.answer (scoreTranslate 1 s) ?_ ?_ ?_ ?_
      · simpa [scoreTranslate] using Bool.ne_not.mpr hseat
      · obtain ⟨m, s', hstep⟩ := hasMove
        exact ⟨m, scoreTranslate 1 s', by
          rw [step_scoreTranslate, hstep]
          simp⟩
      · intro m t htranslated
        obtain ⟨s', hstep, rfl⟩ :=
          (step_scoreTranslate_eq_some_iff G 1 s t m).mp htranslated
        have hlocal : StrategyNode G seat
            (OddStrategy.answer s hseat hasMove children)
            (children m s' hstep) :=
          StrategyNode.answer (StrategyNode.root _)
        have hs'1 : s'.score = 1 := hone hlocal
        simp [scoreTranslate, hs1, hs'1, CharTwo.add_self_eq_zero]
      · intro m t htranslated
        obtain ⟨s', hstep, rfl⟩ :=
          (step_scoreTranslate_eq_some_iff G 1 s t m).mp htranslated
        have hlocal : StrategyNode G seat
            (OddStrategy.answer s hseat hasMove children)
            (children m s' hstep) :=
          StrategyNode.answer (StrategyNode.root _)
        have hone' : ∀ {u : State V} {desc : OddStrategy G seat u},
            StrategyNode G seat (children m s' hstep) desc →
              u.score = 1 := by
          intro u desc hu
          exact hone (hlocal.trans hu)
        exact ih m s' hstep hone'

omit [Fintype V] in
/-- The same translation theorem relative to a larger exact strategy. -/
theorem OddStrategy.subtree_one_translates_neutral
    {G : SimpleGraph V} {seat : Bool} {rootState s : State V}
    {root : OddStrategy G seat rootState} (strategy : OddStrategy G seat s)
    (hmem : StrategyNode G seat root strategy)
    (hrank : rank s < rank rootState)
    (hnozero : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat root desc →
      rank t < rank rootState → t.score ≠ 0) :
    TreeNeutralWins G (!seat) (scoreTranslate 1 s) := by
  apply strategy.one_subtree_translates_neutral
  intro t desc hdesc
  have hglobal : StrategyNode G seat root desc := hmem.trans hdesc
  have hrank' : rank t < rank rootState :=
    lt_of_le_of_lt hdesc.rank_le hrank
  exact zmod2_eq_one_of_ne_zero _ (hnozero hglobal hrank')

omit [Fintype V] in
/-- At a rank-minimal zero-sheet node of one exact strategy, the stored move
is a charge-one CLOSE and its translated child is neutral. -/
theorem OddStrategy.minimal_zeroNode_close_neutral
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (strategy : OddStrategy G seat s) (hs0 : s.score = 0)
    (hminimal : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat strategy desc →
      rank t < rank s → t.score ≠ 0) :
    s.toMove = !seat ∧
      ∃ f q s', s.queue = f :: q ∧ s.ko = false ∧
        step G s .close = some s' ∧ flip G s.untouched f = 1 ∧
          TreeNeutralWins G (!seat) (scoreTranslate 1 s') := by
  cases strategy with
  | terminal _ _ hscore => exact False.elim (hscore hs0)
  | choose _ hseat m s' hstep child =>
      have hplayer : s.toMove = !seat := Bool.eq_not_iff.mpr hseat
      have hmem : StrategyNode G seat
          (OddStrategy.choose s hseat m s' hstep child) child :=
        StrategyNode.choose (StrategyNode.root child)
      have hrank : rank s' < rank s := rank_step_lt hstep
      have hs'1 : s'.score = 1 :=
        zmod2_eq_one_of_ne_zero _ (hminimal hmem hrank)
      have hneutral : TreeNeutralWins G (!seat) (scoreTranslate 1 s') :=
        OddStrategy.subtree_one_translates_neutral child hmem hrank hminimal
      have hm : m = .close := by
        cases m with
        | «open» v =>
            have hscore' := open_score hstep
            rw [hs0] at hscore'
            exact False.elim (one_ne_zero (hs'1.symm.trans hscore'))
        | close => rfl
        | pass =>
            have hscore' := pass_score hstep
            rw [hs0] at hscore'
            exact False.elim (one_ne_zero (hs'1.symm.trans hscore'))
      subst m
      obtain ⟨f, q, hqueue, hscore⟩ := close_score hstep
      have hko : s.ko = false := by
        cases hk : s.ko with
        | false => rfl
        | true => simp [step, hqueue, hk] at hstep
      have hflip : flip G s.untouched f = 1 := by
        rw [hs0, zero_add] at hscore
        exact hscore.symm.trans hs'1
      exact ⟨hplayer, f, q, s', hqueue, hko, hstep, hflip, hneutral⟩
  | answer _ hseat hasMove children =>
      exfalso
      by_cases hU : s.untouched = ∅
      · have hasMove' := hasMove
        obtain ⟨m, s', hstep⟩ := hasMove'
        have hmem : StrategyNode G seat
            (OddStrategy.answer s hseat hasMove children)
            (children m s' hstep) :=
          StrategyNode.answer (StrategyNode.root _)
        have hrank : rank s' < rank s := rank_step_lt hstep
        have hs'0 : s'.score = 0 := by
          rw [step_score_eq_of_untouched_empty hU hstep, hs0]
        exact hminimal hmem hrank hs'0
      · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hU
        let s' : State V := {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove
          score := s.score }
        have hstep : step G s (.open v) = some s' := by
          simp [step, s', hv]
        have hmem : StrategyNode G seat
            (OddStrategy.answer s hseat hasMove children)
            (children (.open v) s' hstep) :=
          StrategyNode.answer (StrategyNode.root _)
        have hrank : rank s' < rank s := rank_step_lt hstep
        have hs'0 : s'.score = 0 := by simp [s', hs0]
        exact hminimal hmem hrank hs'0

omit [Fintype V] in
/-- Every exact zero-sheet strategy has a rank-minimal zero node with a
charged selected CLOSE and a neutral translated continuation. -/
theorem OddStrategy.extract_minimalCloseNeutral
    {G : SimpleGraph V} {seat : Bool} {rootState : State V}
    (root : OddStrategy G seat rootState) (hroot0 : rootState.score = 0) :
    ∃ (s : State V) (strategy : OddStrategy G seat s),
      StrategyNode G seat root strategy ∧ s.score = 0 ∧
      s.toMove = !seat ∧
      ∃ f q s', s.queue = f :: q ∧ s.ko = false ∧
        step G s .close = some s' ∧ flip G s.untouched f = 1 ∧
          TreeNeutralWins G (!seat) (scoreTranslate 1 s') := by
  classical
  let P : Nat → Prop := fun n ↦
    ∃ (s : State V) (strategy : OddStrategy G seat s),
    StrategyNode G seat root strategy ∧
      s.score = 0 ∧ rank s = n
  have hP : ∃ n, P n := by
    exact ⟨rank rootState, rootState, root, StrategyNode.root root,
      hroot0, rfl⟩
  let n := Nat.find hP
  obtain ⟨s, strategy, hmem, hs0, hrank⟩ := Nat.find_spec hP
  have hminimal : ∀ {t : State V} {desc : OddStrategy G seat t},
      StrategyNode G seat strategy desc →
      rank t < rank s → t.score ≠ 0 := by
    intro t desc hinner hlt ht0
    have hglobal : StrategyNode G seat root desc := hmem.trans hinner
    have hPt : P (rank t) := ⟨t, desc, hglobal, ht0, rfl⟩
    have hnle : n ≤ rank t := Nat.find_min' hP hPt
    have hsle : rank s ≤ rank t := by simpa [n, hrank] using hnle
    exact (Nat.not_lt_of_ge hsle) hlt
  obtain ⟨hturn, f, q, s', hqueue, hko, hstep, hflip, hneutral⟩ :=
    strategy.minimal_zeroNode_close_neutral hs0 hminimal
  exact ⟨s, strategy, hmem, hs0, hturn, f, q, s', hqueue, hko,
    hstep, hflip, hneutral⟩

omit [Fintype V] in
/-- Fixed-policy causal extraction.  Off the singleton FIFO wall, an actual
untouched neighbour of the charged front yields an OPEN-then-CLOSE branch
whose endpoint already carries the transported neutral strategy. -/
theorem OddStrategy.extract_causal_neighbor_or_singleton
    {G : SimpleGraph V} {seat : Bool} {rootState : State V}
    (root : OddStrategy G seat rootState) (hroot0 : rootState.score = 0) :
    ∃ (s : State V) (strategy : OddStrategy G seat s),
      StrategyNode G seat root strategy ∧ s.score = 0 ∧
      s.toMove = !seat ∧
      ∃ f q sc, s.queue = f :: q ∧ s.ko = false ∧
        step G s .close = some sc ∧ flip G s.untouched f = 1 ∧
        TreeNeutralWins G (!seat) (scoreTranslate 1 sc) ∧
        (q = [] ∨ ∃ z so soc,
          z ∈ s.untouched ∧ G.Adj f z ∧
          step G s (.open z) = some so ∧
          step G so .close = some soc ∧
          TreeNeutralWins G (!seat) soc) := by
  obtain ⟨s, strategy, hmem, hs0, hturn, f, q, sc, hqueue, hko,
      hclose, hflip, hneutral⟩ := root.extract_minimalCloseNeutral hroot0
  refine ⟨s, strategy, hmem, hs0, hturn, f, q, sc, hqueue, hko,
    hclose, hflip, hneutral, ?_⟩
  by_cases hq : q = []
  · exact Or.inl hq
  · obtain ⟨z, hz, hadj⟩ := exists_mem_adj_of_flip_eq_one hflip
    obtain ⟨so, soc, hopen, hopenClose, hneutral'⟩ :=
      exists_treeNeutral_open_close_of_adj_away_singleton
        hturn hqueue hq hko hz hadj hclose hneutral
    exact Or.inr ⟨z, so, soc, hz, hadj, hopen, hopenClose, hneutral'⟩

/-! ## Augmentation obstruction for commute-generated flows -/

/-- A formal binary chain on a type of histories. -/
abbrev HistoryChain (H : Type*) := H →₀ ZMod 2

/-- Sum of the coefficients of a formal history chain. -/
def historyAugmentation {H : Type*} (c : HistoryChain H) : ZMod 2 :=
  c.sum fun _ a ↦ a

theorem historyAugmentation_add {H : Type*} [DecidableEq H]
    (c₁ c₂ : HistoryChain H) :
    historyAugmentation (c₁ + c₂) =
      historyAugmentation c₁ + historyAugmentation c₂ := by
  unfold historyAugmentation
  apply Finsupp.sum_add_index
  · intro _ _
    rfl
  · intro _ _ _ _
    rfl

@[simp] theorem historyAugmentation_single {H : Type*}
    (h : H) (a : ZMod 2) :
    historyAugmentation (Finsupp.single h a) = a := by
  simp [historyAugmentation]

/-- The homogeneous relation supplied by one commuting schedule diamond. -/
def commuteBoundary {H : Type*} (left right : H) : HistoryChain H :=
  Finsupp.single left 1 + Finsupp.single right 1

theorem historyAugmentation_commuteBoundary
    {H : Type*} [DecidableEq H] (left right : H) :
    historyAugmentation (commuteBoundary left right) = 0 := by
  rw [commuteBoundary, historyAugmentation_add,
    historyAugmentation_single, historyAugmentation_single]
  exact CharTwo.add_self_eq_zero 1

/-- Any finite sum of commuting-diamond relations has even augmentation.
Therefore bubbling the isolated CLOSE through OPENs can add only homogeneous
corrections; by itself it can never produce the odd affine response chain
required by FIFO linking. -/
theorem historyAugmentation_sum_commuteBoundaries
    {H : Type*} [DecidableEq H] (pairs : List (H × H)) :
    historyAugmentation
      ((pairs.map fun p ↦ commuteBoundary p.1 p.2).sum) = 0 := by
  induction pairs with
  | nil => simp [historyAugmentation]
  | cons p pairs ih =>
      rw [List.map_cons, List.sum_cons, historyAugmentation_add,
        historyAugmentation_commuteBoundary, ih, zero_add]

/-- Sharp algebraic no-go for a neutral-pair-only contraction. -/
theorem odd_chain_ne_sum_commuteBoundaries
    {H : Type*} [DecidableEq H] (c : HistoryChain H)
    (hodd : historyAugmentation c = 1) :
    ¬∃ pairs : List (H × H),
      c = (pairs.map fun p ↦ commuteBoundary p.1 p.2).sum := by
  rintro ⟨pairs, rfl⟩
  rw [historyAugmentation_sum_commuteBoundaries] at hodd
  exact zero_ne_one hodd

/-- The empty root after deleting the distinguished dummy label. -/
def initialWithout (d : V) : State V where
  untouched := Finset.univ.erase d
  queue := []
  ko := false
  toMove := false
  score := 0

/-- Clear only the one-step ko marker. -/
def clearKo (s : State V) : State V :=
  { s with ko := false }

/-- Delete one still-untouched label without changing the current public FIFO
phase.  This is the state map used when comparing a dummy interval with its
dummy-free shadow. -/
def dropUntouched (d : V) (s : State V) : State V :=
  { s with untouched := s.untouched.erase d }

omit [Fintype V] [DecidableEq V] in
@[simp] theorem clearKo_clearKo (s : State V) :
    clearKo (clearKo s) = clearKo s := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  rfl

omit [Fintype V] in
/-- Relative, state-level neutral-pair theorem.  From any clear empty-queue
state, opening an untouched isolated dummy, drafting two distinct real
vertices, and closing the dummy gives exactly the same state as deleting the
dummy first and opening those two vertices.  Four actual moves replace two
shadow moves, so turn ownership also agrees. -/
theorem neutralPair_two_open_switch
    (G : SimpleGraph V) (s : State V) (d x y : V)
    (hqueue : s.queue = []) (hko : s.ko = false)
    (hdmem : d ∈ s.untouched) (hxmem : x ∈ s.untouched)
    (hymem : y ∈ s.untouched)
    (hdx : d ≠ x) (hdy : d ≠ y) (hxy : x ≠ y)
    (hd : IsDummy G d) :
    ∃ sd sdx sdxy switched sx direct,
      step G s (.open d) = some sd ∧
      step G sd (.open x) = some sdx ∧
      step G sdx (.open y) = some sdxy ∧
      step G sdxy .close = some switched ∧
      step G (dropUntouched d s) (.open x) = some sx ∧
      step G sx (.open y) = some direct ∧
      switched = direct := by
  let sd : State V := {
    untouched := s.untouched.erase d
    queue := [d]
    ko := true
    toMove := !s.toMove
    score := s.score }
  let sdx : State V := {
    untouched := (s.untouched.erase d).erase x
    queue := [d, x]
    ko := false
    toMove := s.toMove
    score := s.score }
  let sdxy : State V := {
    untouched := ((s.untouched.erase d).erase x).erase y
    queue := [d, x, y]
    ko := false
    toMove := !s.toMove
    score := s.score }
  let switched : State V := {
    untouched := ((s.untouched.erase d).erase x).erase y
    queue := [x, y]
    ko := false
    toMove := s.toMove
    score := s.score }
  let sx : State V := {
    untouched := (s.untouched.erase d).erase x
    queue := [x]
    ko := true
    toMove := !s.toMove
    score := s.score }
  let direct : State V := {
    untouched := ((s.untouched.erase d).erase x).erase y
    queue := [x, y]
    ko := false
    toMove := s.toMove
    score := s.score }
  refine ⟨sd, sdx, sdxy, switched, sx, direct, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp [step, sd, hqueue, hdmem]
  · have hx : x ∈ s.untouched.erase d := by
      exact Finset.mem_erase.mpr ⟨hdx.symm, hxmem⟩
    simp [step, sd, sdx, hx]
  · have hy : y ∈ (s.untouched.erase d).erase x := by
      exact Finset.mem_erase.mpr ⟨hxy.symm,
        Finset.mem_erase.mpr ⟨hdy.symm, hymem⟩⟩
    simp [step, sdx, sdxy, hy]
  · simp [step, sdxy, switched, flip_dummy hd]
  · have hx : x ∈ s.untouched.erase d := by
      exact Finset.mem_erase.mpr ⟨hdx.symm, hxmem⟩
    simp [step, dropUntouched, sx, hqueue, hko, hx]
  · have hy : y ∈ (s.untouched.erase d).erase x := by
      exact Finset.mem_erase.mpr ⟨hxy.symm,
        Finset.mem_erase.mpr ⟨hdy.symm, hymem⟩⟩
    simp [step, sx, direct, hy]

omit [Fintype V] in
/-- Once at least one vertex sits behind an isolated front, its CLOSE commutes
exactly with any fresh OPEN.  This is the elementary diamond which lets the
dummy CLOSE bubble left through a drafted word until it reaches the unique
singleton ko wall. -/
theorem isolatedFront_open_close_commute
    (G : SimpleGraph V) (s : State V) (d z : V) (q : List V)
    (hqueue : s.queue = d :: q) (hq : q ≠ []) (hko : s.ko = false)
    (hz : z ∈ s.untouched) (hd : IsDummy G d) :
    ∃ so soc sc sco,
      step G s (.open z) = some so ∧
      step G so .close = some soc ∧
      step G s .close = some sc ∧
      step G sc (.open z) = some sco ∧
      soc = sco := by
  have hqEmpty : q.isEmpty = false := by
    cases q with
    | nil => contradiction
    | cons _ _ => rfl
  let so : State V := {
    untouched := s.untouched.erase z
    queue := d :: (q ++ [z])
    ko := false
    toMove := !s.toMove
    score := s.score }
  let soc : State V := {
    untouched := s.untouched.erase z
    queue := q ++ [z]
    ko := false
    toMove := s.toMove
    score := s.score }
  let sc : State V := {
    untouched := s.untouched
    queue := q
    ko := false
    toMove := !s.toMove
    score := s.score }
  let sco : State V := {
    untouched := s.untouched.erase z
    queue := q ++ [z]
    ko := false
    toMove := s.toMove
    score := s.score }
  refine ⟨so, soc, sc, sco, ?_, ?_, ?_, ?_, rfl⟩
  · simp [step, so, hqueue, hz]
  · simp [step, so, soc, flip_dummy hd]
  · simp [step, sc, hqueue, hko, flip_dummy hd]
  · simp [step, sc, sco, hz, hqEmpty]

/-- The exact one-real-OPEN dummy switch.  It agrees with opening that real
vertex at the dummy-deleted root except that closing the dummy has cleared
the singleton ko marker. -/
theorem dummy_first_one_open_switch
    (G : SimpleGraph V) (d v : V) (hdv : d ≠ v) (hd : IsDummy G d) :
    ∃ sd sdv switched direct,
      step G (initial (V := V)) (.open d) = some sd ∧
      step G sd (.open v) = some sdv ∧
      step G sdv .close = some switched ∧
      step G (initialWithout d) (.open v) = some direct ∧
      switched = clearKo direct ∧
      direct.ko = true ∧ switched.ko = false := by
  let sd : State V := {
    untouched := Finset.univ.erase d
    queue := [d]
    ko := true
    toMove := true
    score := 0 }
  let sdv : State V := {
    untouched := (Finset.univ.erase d).erase v
    queue := [d, v]
    ko := false
    toMove := false
    score := 0 }
  let switched : State V := {
    untouched := (Finset.univ.erase d).erase v
    queue := [v]
    ko := false
    toMove := true
    score := 0 }
  let direct : State V := {
    untouched := (Finset.univ.erase d).erase v
    queue := [v]
    ko := true
    toMove := true
    score := 0 }
  refine ⟨sd, sdv, switched, direct, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [step, initial, sd]
  · have hv : v ∈ Finset.univ.erase d := by simp [hdv.symm]
    simp [step, sd, sdv, hv]
  · simp [step, sdv, switched, flip_dummy hd]
  · have hv : v ∈ Finset.univ.erase d := by simp [hdv.symm]
    simp [step, initialWithout, direct, hv]

/-- Two distinct drafted real OPENs clear the only ko defect.  Consequently
`OPEN d; OPEN x; OPEN y; CLOSE d` is exactly the same state as
`OPEN x; OPEN y` from the dummy-deleted root.  The equality includes the
player to move and the accumulated score. -/
theorem dummy_first_two_open_switch
    (G : SimpleGraph V) (d x y : V)
    (hdx : d ≠ x) (hdy : d ≠ y) (hxy : x ≠ y)
    (hd : IsDummy G d) :
    ∃ sd sdx sdxy switched sx direct,
      step G (initial (V := V)) (.open d) = some sd ∧
      step G sd (.open x) = some sdx ∧
      step G sdx (.open y) = some sdxy ∧
      step G sdxy .close = some switched ∧
      step G (initialWithout d) (.open x) = some sx ∧
      step G sx (.open y) = some direct ∧
      switched = direct := by
  let sd : State V := {
    untouched := Finset.univ.erase d
    queue := [d]
    ko := true
    toMove := true
    score := 0 }
  let sdx : State V := {
    untouched := (Finset.univ.erase d).erase x
    queue := [d, x]
    ko := false
    toMove := false
    score := 0 }
  let sdxy : State V := {
    untouched := ((Finset.univ.erase d).erase x).erase y
    queue := [d, x, y]
    ko := false
    toMove := true
    score := 0 }
  let switched : State V := {
    untouched := ((Finset.univ.erase d).erase x).erase y
    queue := [x, y]
    ko := false
    toMove := false
    score := 0 }
  let sx : State V := {
    untouched := (Finset.univ.erase d).erase x
    queue := [x]
    ko := true
    toMove := true
    score := 0 }
  let direct : State V := {
    untouched := ((Finset.univ.erase d).erase x).erase y
    queue := [x, y]
    ko := false
    toMove := false
    score := 0 }
  refine ⟨sd, sdx, sdxy, switched, sx, direct, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp [step, initial, sd]
  · have hx : x ∈ Finset.univ.erase d := by simp [hdx.symm]
    simp [step, sd, sdx, hx]
  · have hy : y ∈ (Finset.univ.erase d).erase x := by
      simp [hdy.symm, hxy.symm]
    simp [step, sdx, sdxy, hy]
  · simp [step, sdxy, switched, flip_dummy hd]
  · have hx : x ∈ Finset.univ.erase d := by simp [hdx.symm]
    simp [step, initialWithout, sx, hx]
  · have hy : y ∈ (Finset.univ.erase d).erase x := by
      simp [hdy.symm, hxy.symm]
    simp [step, sx, direct, hy]

/-- The one-OPEN endpoint is genuinely not the dummy-deleted OPEN state:
their ko bits differ.  This is the exact obstruction to treating the dummy
interval as a neutral two-turn pass before a second real OPEN has occurred. -/
theorem dummy_first_one_open_switch_ne_direct
    (G : SimpleGraph V) (d v : V) (hdv : d ≠ v) (hd : IsDummy G d) :
    ∃ switched direct,
      (∃ sd sdv,
        step G (initial (V := V)) (.open d) = some sd ∧
        step G sd (.open v) = some sdv ∧
        step G sdv .close = some switched) ∧
      step G (initialWithout d) (.open v) = some direct ∧
      switched ≠ direct := by
  obtain ⟨sd, sdv, switched, direct, hsd, hsdv, hswitch, hdirect,
      _hclear, hdko, hsko⟩ :=
    dummy_first_one_open_switch G d v hdv hd
  refine ⟨switched, direct, ⟨⟨sd, sdv, hsd, hsdv, hswitch⟩,
    hdirect, ?_⟩⟩
  intro heq
  have := congrArg State.ko heq
  simp [hdko, hsko] at this

omit [Fintype V] in
/-- Once no untouched vertex remains, an already odd score is preserved to
the terminal state and therefore supports either odd-seeking seat. -/
theorem oddWins_of_untouched_empty (G : SimpleGraph V) (seat : Bool)
    (s : State V) (hU : s.untouched = ∅) (hscore : s.score ≠ 0) :
    OddWins G seat s := by
  have hscoreOne : s.score = 1 := zmod2_eq_one_of_ne_zero s.score hscore
  let t := scoreTranslate 1 s
  have htU : t.untouched = ∅ := by simpa [t, scoreTranslate] using hU
  have htScore : t.score = 0 := by
    simp [t, scoreTranslate, hscoreOne, CharTwo.add_self_eq_zero]
  have heven : EvenWins G (!seat) t :=
    evenWins_of_untouched_empty (!seat) t htU htScore
  have hodd := heven.scoreTranslate_one
  simpa [t, scoreTranslate_one_involutive] using hodd

/-! ## Sharp limit of the neutral-pair interpretation -/

/-- A three-label graph with one real edge `0--2` and isolated label `1`. -/
def activeNeutralIntervalGraph : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun x y ↦ x = 0 ∧ y = 2

theorem activeNeutralIntervalGraph_dummy :
    IsDummy activeNeutralIntervalGraph 1 := by
  intro v
  simp [activeNeutralIntervalGraph, SimpleGraph.fromRel_adj]

/-- A reachable checkpoint while the isolated interval for label `1`
is open immediately behind a real front. -/
def activeNeutralIntervalState : State (Fin 3) where
  untouched := {2}
  queue := [0, 1]
  ko := false
  toMove := false
  score := 0

theorem coherent_activeNeutralIntervalState :
    Coherent activeNeutralIntervalState := by
  simp [Coherent, WellFormed, activeNeutralIntervalState]

/-- The conditioned obstruction is not an arbitrary carrier: the ordinary
two-OPEN prefix `OPEN 0; OPEN 1` reaches it from the actual root. -/
theorem activeNeutralIntervalState_reachable :
    ∃ s0,
      step activeNeutralIntervalGraph (initial (V := Fin 3)) (.open 0) =
        some s0 ∧
      step activeNeutralIntervalGraph s0 (.open 1) =
        some activeNeutralIntervalState := by
  let s0 : State (Fin 3) := {
    untouched := {1, 2}
    queue := [0]
    ko := true
    toMove := true
    score := 0 }
  refine ⟨s0, ?_, ?_⟩
  · have hU : (Finset.univ.erase 0 : Finset (Fin 3)) = {1, 2} := by
      ext x
      fin_cases x <;> simp
    simp [step, initial, s0, hU]
  · simp [step, s0, activeNeutralIntervalState]

/-- An active isolated two-event interval does not make an arbitrary
conditioned state safe.  At this checkpoint the odd player closes real front
`0`, scoring on the sole untouched neighbour `2`.  Whether the defender then
opens `2` or closes dummy `1`, the attacker reaches an untouched-empty odd
tail.  Root ancestry, not the mere presence of a neutral interval, is thus an
essential hypothesis of any strategy-stealing proof. -/
theorem oddWins_activeNeutralInterval :
    OddWins activeNeutralIntervalGraph true activeNeutralIntervalState := by
  let s1 : State (Fin 3) := {
    untouched := {2}
    queue := [1]
    ko := false
    toMove := true
    score := 1 }
  have hclose :
      step activeNeutralIntervalGraph activeNeutralIntervalState .close =
        some s1 := by
    have hadj : activeNeutralIntervalGraph.Adj 0 2 := by
      simp [activeNeutralIntervalGraph, SimpleGraph.fromRel_adj]
    simp [step, activeNeutralIntervalState, s1,
      flip_singleton_of_adj hadj]
  refine OddWins.choose activeNeutralIntervalState (by decide) .close s1
    hclose ?_
  have hasMove : ∃ m s', step activeNeutralIntervalGraph s1 m = some s' := by
    let so : State (Fin 3) := {
      untouched := ∅
      queue := [1, 2]
      ko := false
      toMove := false
      score := 1 }
    exact ⟨.open 2, so, by simp [step, s1, so]⟩
  refine OddWins.answer s1 (by rfl) hasMove ?_
  intro m t hstep
  cases m
  · rename_i v
    simp only [step, s1] at hstep
    split at hstep
    · rename_i hv
      have hv2 : v = 2 := by simpa using hv
      subst v
      cases hstep
      apply oddWins_of_untouched_empty activeNeutralIntervalGraph true
      · simp
      · simp
    · contradiction
  · let s2 : State (Fin 3) := {
      untouched := {2}
      queue := []
      ko := false
      toMove := false
      score := 1 }
    let s3 : State (Fin 3) := {
      untouched := ∅
      queue := [2]
      ko := true
      toMove := true
      score := 1 }
    have hs1close : step activeNeutralIntervalGraph s1 .close = some s2 := by
      simp [step, s1, s2, flip_dummy activeNeutralIntervalGraph_dummy]
    rw [hs1close] at hstep
    have ht : t = s2 := Option.some.inj hstep.symm
    subst t
    have hopen :
        step activeNeutralIntervalGraph s2 (.open 2) = some s3 := by
      simp [step, s2, s3]
    refine OddWins.choose s2 (by decide) (.open 2) s3 hopen ?_
    exact oddWins_of_untouched_empty activeNeutralIntervalGraph true s3
      (by simp [s3]) (by simp [s3])
  · simp [step, s1] at hstep

/-- The conditioned obstruction is causal, not merely existential: every
exact odd strategy at this state must select the charged real CLOSE.  The
neutral alternative `OPEN 2` is legal but leads to an even untouched-empty
tail, so it cannot be the selected child of the fixed odd policy. -/
theorem activeNeutralIntervalStrategy_selectedClose
    (strategy : OddStrategy activeNeutralIntervalGraph true
      activeNeutralIntervalState) :
    strategy.selectedMove = some .close := by
  cases strategy with
  | terminal _ hterminal _ =>
      exact False.elim (by
        have hnot : ¬Terminal activeNeutralIntervalState := by
          simp [Terminal, activeNeutralIntervalState]
        exact hnot hterminal)
  | choose _ hseat m s' hstep child =>
      change some m = some (.close : Move (Fin 3))
      apply congrArg some
      cases m with
      | «open» v =>
          simp only [step, activeNeutralIntervalState] at hstep
          split at hstep
          · rename_i hv
            have hv2 : v = 2 := by simpa using hv
            subst v
            cases hstep
            have heven : EvenWins activeNeutralIntervalGraph true {
                untouched := ∅
                queue := [0, 1, 2]
                ko := false
                toMove := true
                score := 0 } :=
              evenWins_of_untouched_empty true _ (by rfl) (by rfl)
            exact False.elim (heven.not_oddWins child.toOddWins)
          · contradiction
      | close => rfl
      | pass => simp [step, activeNeutralIntervalState] at hstep
  | answer _ hseat _ _ => simp [activeNeutralIntervalState] at hseat

theorem not_evenWins_activeNeutralInterval :
    ¬EvenWins activeNeutralIntervalGraph true activeNeutralIntervalState :=
  fun h ↦ h.not_oddWins oddWins_activeNeutralInterval

end

end Ogdoad.Fifo
