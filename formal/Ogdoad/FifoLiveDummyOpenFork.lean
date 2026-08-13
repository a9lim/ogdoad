import Ogdoad.FifoSingletonForkBoundary
import Ogdoad.FifoEmptyQueue
import Ogdoad.FifoDistinctOpenForkBoundary

/-!
# A full FIFO drain kills the distinct-OPEN minimum

At a rank-minimal controlled state, the selected child of the base-score
policy is cold odd, while the selected child of the translated policy is cold
even.  Coldness then propagates down every further legal edge, because a
lower controlled state is excluded by minimality.

Suppose the two policies select distinct OPENs `x,y`.  From the cold-odd `x`
child, take the universal reply `OPEN y`; from the cold-even `y` child, take
`OPEN x`.  Now drain the whole FIFO queue on both sides.  The endpoints agree
exactly: the untouched sets agree, the number of moves agrees, and the drain
scores contain the same fixed-carrier front charges in opposite order.  One
state would therefore be both cold odd and cold even, a contradiction.

The argument is graph-independent and also covers a selected isolated dummy.
The longer three-OPEN rotation below records the initially discovered live-
dummy route, but the two-OPEN drain theorem is the decisive strengthening.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

def closeWord (q : List V) : List (Move V) :=
  q.map fun _ ↦ .close

omit [Fintype V] in
theorem StepPath.append {G : SimpleGraph V} {s t u : State V}
    {ms ns : List (Move V)} (hst : StepPath G s ms t)
    (htu : StepPath G t ns u) : StepPath G s (ms ++ ns) u := by
  induction hst with
  | nil => simpa using htu
  | cons hstep htail ih =>
      simpa using StepPath.cons hstep (ih htu)

omit [Fintype V] in
/-- A clear fixed queue can always be drained by repeated CLOSEs. -/
theorem stepPath_drainState (G : SimpleGraph V) (U : Finset V) :
    ∀ (q : List V) (turn : Bool) (score : ZMod 2),
      ∃ t, StepPath G (drainState U q turn score) (closeWord q) t ∧
        t.untouched = U ∧ t.queue = [] ∧ t.ko = false ∧
        t.score = score + (q.map (flip G U)).sum := by
  intro q
  induction q with
  | nil =>
      intro turn score
      exact ⟨drainState U [] turn score, StepPath.nil _, rfl, rfl, rfl,
        by simp [drainState]⟩
  | cons f q ih =>
      intro turn score
      let next := drainState U q (!turn) (score + flip G U f)
      have hclose : step G (drainState U (f :: q) turn score) .close =
          some next := by
        simp [step, drainState, next]
      obtain ⟨t, htail, hU, hqueue, hko, hscore⟩ :=
        ih (!turn) (score + flip G U f)
      refine ⟨t, ?_, hU, hqueue, hko, ?_⟩
      · simpa [closeWord, next] using StepPath.cons hclose htail
      · simpa [List.sum_cons, add_assoc] using hscore

private def openedState (s : State V) (v : V) : State V where
  untouched := s.untouched.erase v
  queue := s.queue ++ [v]
  ko := s.queue.isEmpty
  toMove := !s.toMove
  score := s.score

omit [Fintype V] in
private theorem step_openedState (G : SimpleGraph V) (s : State V) (v : V)
    (hv : v ∈ s.untouched) :
    step G s (.open v) = some (openedState s v) := by
  simp [step, openedState, hv]

omit [Fintype V] in
private theorem openedState_queue_nonempty (s : State V) (v : V) :
    (openedState s v).queue ≠ [] := by
  simp [openedState]

omit [Fintype V] in
private theorem openedState_mem_iff {s : State V} {a v : V} :
    a ∈ (openedState s v).untouched ↔ a ∈ s.untouched ∧ a ≠ v := by
  simp [openedState, and_comm]

omit [Fintype V] [DecidableEq V] in
private theorem turnAfter_closeWord_eq_of_length_eq
    {q r : List V} (h : q.length = r.length) (turn : Bool) :
    turnAfter (closeWord q) turn = turnAfter (closeWord r) turn := by
  induction q generalizing r turn with
  | nil =>
      cases r with
      | nil => rfl
      | cons _ _ => simp at h
  | cons a q ih =>
      cases r with
      | nil => simp at h
      | cons b r =>
          simp only [List.length_cons] at h
          simp only [closeWord, List.map_cons, turnAfter]
          exact ih (Nat.succ.inj h) (!turn)

omit [Fintype V] in
/-- Drafting two distinct OPENs in opposite orders and then draining the
entire queue reaches one exact common endpoint.  After both OPENs the
untouched carrier is identical; during the drain it is fixed, so the two new
front charges occur in opposite order and add to the same score. -/
theorem swapped_open_pair_drain_reconverges
    (G : SimpleGraph V) (s : State V) (x y : V)
    (hxmem : x ∈ s.untouched) (hymem : y ∈ s.untouched)
    (hxy : x ≠ y) :
    ∃ sx sy t,
      step G s (.open x) = some sx ∧
      step G s (.open y) = some sy ∧
      StepPath G sx
        ([.open y] ++ closeWord (s.queue ++ [x, y])) t ∧
      StepPath G sy
        ([.open x] ++ closeWord (s.queue ++ [y, x])) t := by
  let sx := openedState s x
  let sy := openedState s y
  let sxy := openedState sx y
  let syx := openedState sy x
  have hsx : step G s (.open x) = some sx :=
    step_openedState G s x hxmem
  have hsy : step G s (.open y) = some sy :=
    step_openedState G s y hymem
  have hyx : y ∈ sx.untouched := by
    simp [sx, openedState, hymem, hxy.symm]
  have hxy' : x ∈ sy.untouched := by
    simp [sy, openedState, hxmem, hxy]
  have hsxy : step G sx (.open y) = some sxy :=
    step_openedState G sx y hyx
  have hsyx : step G sy (.open x) = some syx :=
    step_openedState G sy x hxy'
  have hqueueA : sxy.queue = s.queue ++ [x, y] := by
    simp [sxy, sx, openedState, List.append_assoc]
  have hqueueB : syx.queue = s.queue ++ [y, x] := by
    simp [syx, sy, openedState, List.append_assoc]
  have hkoA : sxy.ko = false := by
    simp [sxy, sx, openedState]
  have hkoB : syx.ko = false := by
    simp [syx, sy, openedState]
  have hturn : sxy.toMove = syx.toMove := by
    simp [sxy, sx, syx, sy, openedState]
  have hscore : sxy.score = syx.score := by
    simp [sxy, sx, syx, sy, openedState]
  have hU : sxy.untouched = syx.untouched := by
    ext v
    simp [sxy, sx, syx, sy, openedState, and_left_comm]
  have hAasDrain : sxy = drainState sxy.untouched sxy.queue
      sxy.toMove sxy.score := by
    obtain ⟨U, q, ko, turn, score⟩ := sxy
    simp only at hkoA ⊢
    subst ko
    rfl
  have hBasDrain : syx = drainState syx.untouched syx.queue
      syx.toMove syx.score := by
    obtain ⟨U, q, ko, turn, score⟩ := syx
    simp only at hkoB ⊢
    subst ko
    rfl
  obtain ⟨tA, hpathA, htAU, htAq, htAko, htAscore⟩ :=
    stepPath_drainState G sxy.untouched sxy.queue sxy.toMove sxy.score
  obtain ⟨tB, hpathB, htBU, htBq, htBko, htBscore⟩ :=
    stepPath_drainState G syx.untouched syx.queue syx.toMove syx.score
  have hlen : sxy.queue.length = syx.queue.length := by
    rw [hqueueA, hqueueB]
    simp
  have htTurnEq : tA.toMove = tB.toMove := by
    have hpathATurn := hpathA.toMove_eq_turnAfter
    have hpathBTurn := hpathB.toMove_eq_turnAfter
    rw [hAasDrain] at hpathATurn
    rw [hBasDrain] at hpathBTurn
    simp only [drainState] at hpathATurn hpathBTurn
    rw [hpathATurn, hpathBTurn, hturn]
    exact turnAfter_closeWord_eq_of_length_eq hlen syx.toMove
  have hsum :
      (sxy.queue.map (flip G sxy.untouched)).sum =
        (syx.queue.map (flip G syx.untouched)).sum := by
    rw [hqueueA, hqueueB, hU]
    simp only [List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    abel
  have htScoreEq : tA.score = tB.score := by
    calc
      tA.score = sxy.score +
          (sxy.queue.map (flip G sxy.untouched)).sum := htAscore
      _ = syx.score +
          (syx.queue.map (flip G syx.untouched)).sum := by
            rw [hscore, hsum]
      _ = tB.score := htBscore.symm
  have htEq : tA = tB := by
    obtain ⟨UA, qA, koA, turnA, scoreA⟩ := tA
    obtain ⟨UB, qB, koB, turnB, scoreB⟩ := tB
    simp only at htAU htBU htAq htBq htAko htBko htTurnEq htScoreEq ⊢
    subst UB
    subst qA
    subst qB
    subst koA
    subst koB
    subst turnB
    subst scoreB
    congr 1
    exact htAU.trans hU
  subst tB
  refine ⟨sx, sy, tA, hsx, hsy, ?_, ?_⟩
  · have hopenPath : StepPath G sx [.open y] sxy :=
      StepPath.cons hsxy (StepPath.nil _)
    have hpathA' : StepPath G sxy (closeWord sxy.queue) tA :=
      hAasDrain ▸ hpathA
    simpa [hqueueA] using StepPath.append hopenPath hpathA'
  · have hopenPath : StepPath G sy [.open x] syx :=
      StepPath.cons hsyx (StepPath.nil _)
    have hpathB' : StepPath G syx (closeWord syx.queue) tA :=
      hBasDrain ▸ hpathB
    simpa [hqueueB] using StepPath.append hopenPath hpathB'

omit [Fintype V] in
/-- Drafting the cyclic orders `x,y,d` and `y,d,x`, then draining the entire
queue, reaches one exact common endpoint when `d` is isolated. -/
theorem rotated_real_real_dummy_drain_reconverges
    (G : SimpleGraph V) (s : State V) (d x y : V)
    (hd : IsDummy G d)
    (hdmem : d ∈ s.untouched) (hxmem : x ∈ s.untouched)
    (hymem : y ∈ s.untouched)
    (hxy : x ≠ y) (hxd : x ≠ d) (hyd : y ≠ d) :
    ∃ sx sy t,
      step G s (.open x) = some sx ∧
      step G s (.open y) = some sy ∧
      StepPath G sx
        ([.open y, .open d] ++ closeWord (s.queue ++ [x, y, d])) t ∧
      StepPath G sy
        ([.open d, .open x] ++ closeWord (s.queue ++ [y, d, x])) t := by
  let sx := openedState s x
  let sy := openedState s y
  let sxy := openedState sx y
  let syd := openedState sy d
  let sxyd := openedState sxy d
  let sydx := openedState syd x
  have hsx : step G s (.open x) = some sx :=
    step_openedState G s x hxmem
  have hsy : step G s (.open y) = some sy :=
    step_openedState G s y hymem
  have hyx : y ∈ sx.untouched := by
    simp [sx, openedState, hymem, hxy.symm]
  have hdx : d ∈ sx.untouched := by
    simp [sx, openedState, hdmem, hxd.symm]
  have hdy : d ∈ sy.untouched := by
    simp [sy, openedState, hdmem, hyd.symm]
  have hxy' : x ∈ sy.untouched := by
    simp [sy, openedState, hxmem, hxy]
  have hsxy : step G sx (.open y) = some sxy :=
    step_openedState G sx y hyx
  have hsyd : step G sy (.open d) = some syd :=
    step_openedState G sy d hdy
  have hdxy : d ∈ sxy.untouched := by
    simp [sxy, sx, openedState, hdmem, hxd.symm, hyd.symm]
  have hxyd : x ∈ syd.untouched := by
    simp [syd, sy, openedState, hxmem, hxy, hxd]
  have hsxyd : step G sxy (.open d) = some sxyd :=
    step_openedState G sxy d hdxy
  have hsydx : step G syd (.open x) = some sydx :=
    step_openedState G syd x hxyd
  have hqueueA : sxyd.queue = s.queue ++ [x, y, d] := by
    simp [sxyd, sxy, sx, openedState, List.append_assoc]
  have hqueueB : sydx.queue = s.queue ++ [y, d, x] := by
    simp [sydx, syd, sy, openedState, List.append_assoc]
  have hkoA : sxyd.ko = false := by
    simp [sxyd, sxy, sx, openedState]
  have hkoB : sydx.ko = false := by
    simp [sydx, syd, sy, openedState]
  have hturn : sxyd.toMove = sydx.toMove := by
    simp [sxyd, sxy, sx, sydx, syd, sy, openedState]
  have hscore : sxyd.score = sydx.score := by
    simp [sxyd, sxy, sx, sydx, syd, sy, openedState]
  have hU : sxyd.untouched = sydx.untouched := by
    ext v
    simp [sxyd, sxy, sx, sydx, syd, sy, openedState, and_left_comm]
  have hAasDrain : sxyd = drainState sxyd.untouched sxyd.queue
      sxyd.toMove sxyd.score := by
    obtain ⟨U, q, ko, turn, score⟩ := sxyd
    simp only at hkoA ⊢
    subst ko
    rfl
  have hBasDrain : sydx = drainState sydx.untouched sydx.queue
      sydx.toMove sydx.score := by
    obtain ⟨U, q, ko, turn, score⟩ := sydx
    simp only at hkoB ⊢
    subst ko
    rfl
  obtain ⟨tA, hpathA, htAU, htAq, htAko, htAscore⟩ :=
    stepPath_drainState G sxyd.untouched sxyd.queue sxyd.toMove sxyd.score
  obtain ⟨tB, hpathB, htBU, htBq, htBko, htBscore⟩ :=
    stepPath_drainState G sydx.untouched sydx.queue sydx.toMove sydx.score
  have hlen : sxyd.queue.length = sydx.queue.length := by
    rw [hqueueA, hqueueB]
    simp
  have htTurnEq : tA.toMove = tB.toMove := by
    have hpathATurn := hpathA.toMove_eq_turnAfter
    have hpathBTurn := hpathB.toMove_eq_turnAfter
    rw [hAasDrain] at hpathATurn
    rw [hBasDrain] at hpathBTurn
    simp only [drainState] at hpathATurn hpathBTurn
    rw [hpathATurn, hpathBTurn, hturn]
    exact turnAfter_closeWord_eq_of_length_eq hlen sydx.toMove
  have hsum :
      (sxyd.queue.map (flip G sxyd.untouched)).sum =
        (sydx.queue.map (flip G sydx.untouched)).sum := by
    rw [hqueueA, hqueueB, hU]
    simp only [List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [flip_dummy hd]
    abel
  have htScoreEq : tA.score = tB.score := by
    calc
      tA.score = sxyd.score +
          (sxyd.queue.map (flip G sxyd.untouched)).sum := htAscore
      _ = sydx.score +
          (sydx.queue.map (flip G sydx.untouched)).sum := by
            rw [hscore, hsum]
      _ = tB.score := htBscore.symm
  have htEq : tA = tB := by
    obtain ⟨UA, qA, koA, turnA, scoreA⟩ := tA
    obtain ⟨UB, qB, koB, turnB, scoreB⟩ := tB
    simp only at htAU htBU htAq htBq htAko htBko htTurnEq htScoreEq ⊢
    subst UB
    subst qA
    subst qB
    subst koA
    subst koB
    subst turnB
    subst scoreB
    congr 1
    exact htAU.trans hU
  subst tB
  refine ⟨sx, sy, tA, hsx, hsy, ?_, ?_⟩
  · have hopenPath : StepPath G sx [.open y, .open d] sxyd :=
      StepPath.cons hsxy (StepPath.cons hsxyd (StepPath.nil _))
    have hpathA' : StepPath G sxyd (closeWord sxyd.queue) tA :=
      hAasDrain ▸ hpathA
    simpa [hqueueA] using StepPath.append hopenPath hpathA'
  · have hopenPath : StepPath G sy [.open d, .open x] sydx :=
      StepPath.cons hsyd (StepPath.cons hsydx (StepPath.nil _))
    have hpathB' : StepPath G sydx (closeWord sydx.queue) tA :=
      hBasDrain ▸ hpathB
    simpa [hqueueB] using StepPath.append hopenPath hpathB'

omit [Fintype V] in
/-- Cold-odd heredity along a whole path below a reachable controlled
minimum. -/
theorem BothOdd.stepPath_of_reachableMinimal
    {G : SimpleGraph V} {root minimum start finish : State V}
    {ms : List (Move V)}
    (hminimal : ∀ t, ReachableFrom G root t → rank t < rank minimum →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (hreach : ReachableFrom G root start) (hrank : rank start < rank minimum)
    (hcold : BothOdd G start) (hpath : StepPath G start ms finish) :
    BothOdd G finish := by
  induction hpath with
  | nil => exact hcold
  | @cons s t u m ms hstep htail ih =>
      have hreachT := hreach.step hstep
      have hrankT : rank t < rank minimum :=
        lt_trans (rank_step_lt hstep) hrank
      have hcoldT := hcold.step_of_not_moverControlled hstep
        (hminimal t hreachT hrankT).1
      exact ih hreachT hrankT hcoldT

omit [Fintype V] in
/-- Cold-even heredity along a whole path below a reachable controlled
minimum. -/
theorem BothEven.stepPath_of_reachableMinimal
    {G : SimpleGraph V} {root minimum start finish : State V}
    {ms : List (Move V)}
    (hminimal : ∀ t, ReachableFrom G root t → rank t < rank minimum →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (hreach : ReachableFrom G root start) (hrank : rank start < rank minimum)
    (hcold : BothEven G start) (hpath : StepPath G start ms finish) :
    BothEven G finish := by
  induction hpath with
  | nil => exact hcold
  | @cons s t u m ms hstep htail ih =>
      have hreachT := hreach.step hstep
      have hrankT : rank t < rank minimum :=
        lt_trans (rank_step_lt hstep) hrank
      have hcoldT := hcold.step_of_not_moverControlled hstep
        (hminimal t hreachT hrankT).1
      exact ih hreachT hrankT hcoldT

omit [Fintype V] in
/-- No reachable rank-minimal controlled state can have its score-coupled
policies select two distinct OPENs.  The crossed replies followed by a full
FIFO drain reconverge exactly, so cold heredity assigns incompatible cold
classes to one lower endpoint.  This graph-independent theorem also covers
the case where either selected OPEN is the isolated dummy. -/
theorem reachableMinimal_no_distinctOpenFork
    {G : SimpleGraph V} {root : State V} {seat : Bool}
    {s sx sy : State V} {x y : V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ t, ReachableFrom G root t → rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hleft : left.selectedMove = some (.open x))
    (hright : right.selectedMove = some (.open y))
    (hstepX : step G s (.open x) = some sx)
    (hstepY : step G s (.open y) = some sy)
    (hxy : x ≠ y) : False := by
  have hxmem : x ∈ s.untouched := mem_untouched_of_open_step hstepX
  have hymem : y ∈ s.untouched := mem_untouched_of_open_step hstepY
  obtain ⟨sx', sy', t, hsx', hsy', hpathOdd, hpathEven⟩ :=
    swapped_open_pair_drain_reconverges G s x y hxmem hymem hxy
  have hsx : sx' = sx := by
    rw [hstepX] at hsx'
    exact Option.some.inj hsx'.symm
  have hsy : sy' = sy := by
    rw [hstepY] at hsy'
    exact Option.some.inj hsy'.symm
  subst sx'
  subst sy'
  have hcoldOdd : BothOdd G sx :=
    scoreCoupled_leftSelectedChild_bothOdd hreach hminimal left hturn
      (.open x) hleft hstepX
  have hcoldEven : BothEven G sy :=
    scoreCoupled_rightSelectedChild_bothEven hreach hminimal right hturn
      (.open y) hright hstepY
  have hoddEnd : BothOdd G t :=
    hcoldOdd.stepPath_of_reachableMinimal hminimal (hreach.step hstepX)
      (rank_step_lt hstepX) hpathOdd
  have hevenEnd : BothEven G t :=
    hcoldEven.stepPath_of_reachableMinimal hminimal (hreach.step hstepY)
      (rank_step_lt hstepY) hpathEven
  exact hoddEnd.1 hevenEnd.1

omit [Fintype V] in
/-- With any untouched label available, the immediate fork at a reachable
controlled minimum is therefore necessarily OPEN versus CLOSE.  PASS is
impossible while the carrier is nonempty, and the preceding theorem excludes
two distinct OPENs. -/
theorem reachableMinimal_liveCarrier_scoreCoupled_openCloseFork
    {G : SimpleGraph V} {root : State V} {seat : Bool}
    {s : State V} {d : V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ t, ReachableFrom G root t → rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat) (hdmem : d ∈ s.untouched) :
    ∃ (so sc : State V) (x : V),
      step G s (.open x) = some so ∧ step G s .close = some sc ∧
        ((left.selectedMove = some (.open x) ∧
            right.selectedMove = some .close) ∨
         (left.selectedMove = some .close ∧
            right.selectedMove = some (.open x))) := by
  obtain ⟨u₀, u₁, m₀, m₁, hleft, hright, hstep₀, hstep₁, hne⟩ :=
    reachableMinimal_scoreCoupled_currentFork
      hreach hminimal left right hturn
  obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ :=
    distinct_legal_moves_include_open hstep₀ hstep₁ hne
  · by_cases hopen₁ : ∃ y, m₁ = .open y
    · obtain ⟨y, rfl⟩ := hopen₁
      exact False.elim (reachableMinimal_no_distinctOpenFork
        hreach hminimal left right hturn hleft hright hstep₀ hstep₁
          (by simpa using hne))
    · have hm₁ : m₁ = .close :=
        open_and_nonopen_legal_forces_close hdmem hstep₁ hopen₁
      subst m₁
      exact ⟨u₀, u₁, x, hstep₀, hstep₁, Or.inl ⟨hleft, hright⟩⟩
  · by_cases hopen₀ : ∃ y, m₀ = .open y
    · obtain ⟨y, rfl⟩ := hopen₀
      exact False.elim (reachableMinimal_no_distinctOpenFork
        hreach hminimal left right hturn hleft hright hstep₀ hstep₁
          (by simpa using hne))
    · have hm₀ : m₀ = .close :=
        open_and_nonopen_legal_forces_close hdmem hstep₀ hopen₀
      subst m₀
      exact ⟨u₁, u₀, x, hstep₁, hstep₀, Or.inr ⟨hleft, hright⟩⟩

omit [Fintype V] in
/-- A reachable rank-minimal controlled state cannot have its score-coupled
policies select two distinct real OPENs while the isolated dummy stays live. -/
theorem reachableMinimal_no_twoRealOpenFork_liveDummy
    {G : SimpleGraph V} {root : State V} {seat : Bool}
    {s sx sy : State V} {d x y : V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ t, ReachableFrom G root t → rank t < rank s →
      ¬MoverControlled G t ∧ ¬NonmoverControlled G t)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hleft : left.selectedMove = some (.open x))
    (hright : right.selectedMove = some (.open y))
    (hstepX : step G s (.open x) = some sx)
    (hstepY : step G s (.open y) = some sy)
    (hxy : x ≠ y) (hdmem : d ∈ s.untouched)
    (hxd : x ≠ d) (hyd : y ≠ d) (hd : IsDummy G d) : False := by
  have hxmem : x ∈ s.untouched := mem_untouched_of_open_step hstepX
  have hymem : y ∈ s.untouched := mem_untouched_of_open_step hstepY
  obtain ⟨sx', sy', t, hsx', hsy', hpathOdd, hpathEven⟩ :=
    rotated_real_real_dummy_drain_reconverges G s d x y hd hdmem hxmem hymem
      hxy hxd hyd
  have hsx : sx' = sx := by
    rw [hstepX] at hsx'
    exact Option.some.inj hsx'.symm
  have hsy : sy' = sy := by
    rw [hstepY] at hsy'
    exact Option.some.inj hsy'.symm
  subst sx'
  subst sy'
  have hcoldOdd : BothOdd G sx :=
    scoreCoupled_leftSelectedChild_bothOdd hreach hminimal left hturn
      (.open x) hleft hstepX
  have hcoldEven : BothEven G sy :=
    scoreCoupled_rightSelectedChild_bothEven hreach hminimal right hturn
      (.open y) hright hstepY
  have hoddEnd : BothOdd G t :=
    hcoldOdd.stepPath_of_reachableMinimal hminimal (hreach.step hstepX)
      (rank_step_lt hstepX) hpathOdd
  have hevenEnd : BothEven G t :=
    hcoldEven.stepPath_of_reachableMinimal hminimal (hreach.step hstepY)
      (rank_step_lt hstepY) hpathEven
  exact hoddEnd.1 hevenEnd.1

end

end Ogdoad.Fifo
