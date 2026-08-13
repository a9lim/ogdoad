import Ogdoad.FifoControlledDivergence
import Ogdoad.FifoEmptyQueue

/-!
# The singleton isolated-dummy fork is not rank-minimal

At a rank-minimal controlled FIFO state every lower state is cold: its two
mover/nonmover outcome bits agree.  Cold classes are hereditary along every
legal move as long as controlled children are excluded.  Indeed the universal
coordinate transports one of the two bits, while exclusion of mover control
forces the other bit to agree.

The two selected children of a score-coupled attacker pair have opposite cold
classes.  The base-score policy produces a `BothOdd` child; the unit-translated
policy, read back on the base sheet, produces a `BothEven` child.  At a
singleton queue `[f]`, if the first policy opens an untouched isolated dummy
and the second closes `f` (or conversely), one further untouched OPEN clears
the ko discrepancy and makes the two schedules reconverge.  Heredity would
then assign both cold classes to one state, a contradiction.  If no further
untouched label exists, the carrier is exactly the dummy singleton and the
wall is directly cold.

Thus the sharp singleton dummy/CLOSE alternative in the general divergence
classification is eliminated at a reachable rank minimum.  This argument is
outcome-theoretic; it does not address a real OPEN/CLOSE wall or two distinct
OPENs.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A both-even state remains both-even across a legal edge once mover control
at the child is excluded.  The old nonmover is universal at the parent, so it
supplies the child's mover bit; absence of mover control supplies the other
bit. -/
theorem BothEven.step_of_not_moverControlled
    {G : SimpleGraph V} {s t : State V} (h : BothEven G s)
    {m : Move V} (hstep : step G s m = some t)
    (hnot : ¬MoverControlled G t) : BothEven G t := by
  have hturn : t.toMove = !s.toMove := step_toMove hstep
  have hparent : EvenWins G (!s.toMove) s := by
    simpa [NonmoverEvenWins] using h.2
  have hchild : EvenWins G (!s.toMove) t :=
    hparent.answer_child (by simp) hstep
  have hmover : MoverEvenWins G t := by
    simpa [MoverEvenWins, hturn] using hchild
  have hnonmover : NonmoverEvenWins G t := by
    by_contra hn
    exact hnot ⟨hmover, hn⟩
  exact ⟨hmover, hnonmover⟩

omit [Fintype V] in
/-- Dually, a both-odd state remains both-odd across a legal edge once mover
control at the child is excluded.  If the child's nonmover could force even,
the old mover could select this edge; absence of mover control then excludes
the remaining child bit. -/
theorem BothOdd.step_of_not_moverControlled
    {G : SimpleGraph V} {s t : State V} (h : BothOdd G s)
    {m : Move V} (hstep : step G s m = some t)
    (hnot : ¬MoverControlled G t) : BothOdd G t := by
  have hturn : t.toMove = !s.toMove := step_toMove hstep
  have hnonmover : ¬NonmoverEvenWins G t := by
    intro ht
    have hchild : EvenWins G s.toMove t := by
      simpa [NonmoverEvenWins, hturn] using ht
    have hparent : EvenWins G s.toMove s :=
      EvenWins.choose s rfl m t hstep hchild
    exact h.1 (by simpa [MoverEvenWins] using hparent)
  have hmover : ¬MoverEvenWins G t := by
    intro ht
    exact hnot ⟨ht, hnonmover⟩
  exact ⟨hmover, hnonmover⟩

omit [Fintype V] in
/-- The base-score selected child of a score-coupled attacker pair is cold
odd at a rank minimum. -/
theorem scoreCoupled_leftSelectedChild_bothOdd
    {G : SimpleGraph V} {root : State V} {seat : Bool}
    {s t : State V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ u, ReachableFrom G root u → rank u < rank s →
      ¬MoverControlled G u ∧ ¬NonmoverControlled G u)
    (left : OddStrategy G seat s) (hturn : s.toMove = !seat)
    (m : Move V) (hselected : left.selectedMove = some m)
    (hstep : step G s m = some t) : BothOdd G t := by
  have hrank : rank t < rank s := rank_step_lt hstep
  have hcold := hminimal t (hreach.step hstep) hrank
  cases left with
  | terminal _ _ _ => simp [OddStrategy.selectedMove] at hselected
  | answer _ hseat _ _ => exact False.elim (by
      have : s.toMove ≠ seat := by rw [hturn]; simp
      exact this hseat)
  | choose _ hseat move u hchosen tail =>
      have hm : move = m := by
        simpa [OddStrategy.selectedMove] using Option.some.inj hselected
      subst move
      have hu : u = t := by
        rw [hstep] at hchosen
        exact Option.some.inj hchosen.symm
      subst u
      have htturn : t.toMove = seat := by
        rw [step_toMove hstep, hturn]
        simp
      have hnotEven : ¬EvenWins G seat t :=
        (oddWins_iff_not_evenWins G seat t).mp tail.toOddWins
      have hmover : ¬MoverEvenWins G t := by
        simpa [MoverEvenWins, htturn] using hnotEven
      have hnonmover : ¬NonmoverEvenWins G t := by
        intro hn
        exact hcold.2 ⟨hmover, hn⟩
      exact ⟨hmover, hnonmover⟩

omit [Fintype V] in
/-- The selected child of the unit-translated policy, pulled back to the base
score sheet, is cold even at a rank minimum. -/
theorem scoreCoupled_rightSelectedChild_bothEven
    {G : SimpleGraph V} {root : State V} {seat : Bool}
    {s t : State V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ u, ReachableFrom G root u → rank u < rank s →
      ¬MoverControlled G u ∧ ¬NonmoverControlled G u)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (m : Move V) (hselected : right.selectedMove = some m)
    (hstep : step G s m = some t) : BothEven G t := by
  have hrank : rank t < rank s := rank_step_lt hstep
  have hcold := hminimal t (hreach.step hstep) hrank
  cases right with
  | terminal _ _ _ => simp [OddStrategy.selectedMove] at hselected
  | answer _ hseat _ _ => exact False.elim (by
      have : (scoreTranslate 1 s).toMove ≠ seat := by
        simp [scoreTranslate, hturn]
      exact this hseat)
  | choose _ hseat move u hchosen tail =>
      have hm : move = m := by
        simpa [OddStrategy.selectedMove] using Option.some.inj hselected
      subst move
      have htranslated : step G (scoreTranslate 1 s) m =
          some (scoreTranslate 1 t) := by
        rw [step_scoreTranslate, hstep]
        rfl
      have hu : u = scoreTranslate 1 t := by
        rw [htranslated] at hchosen
        exact Option.some.inj hchosen.symm
      subst u
      have htturn : t.toMove = seat := by
        rw [step_toMove hstep, hturn]
        simp
      have heven : EvenWins G (!seat) t :=
        (oddWins_scoreTranslate_one_iff_evenWins G seat t).mp tail.toOddWins
      have hnonmover : NonmoverEvenWins G t := by
        simpa [NonmoverEvenWins, htturn] using heven
      have hmover : MoverEvenWins G t := by
        by_contra hn
        exact hcold.2 ⟨hn, hnonmover⟩
      exact ⟨hmover, hnonmover⟩

omit [Fintype V] in
/-- At score zero, a singleton queue whose only untouched label is an
isolated dummy is both-even.  Either opening the dummy or closing the current
front enters an untouched-empty neutral drain. -/
theorem isolated_singletonWall_bothEven_of_score_zero
    {G : SimpleGraph V} {s : State V} {d f : V}
    (hd : IsDummy G d) (hU : s.untouched = {d})
    (hqueue : s.queue = [f]) (hko : s.ko = false)
    (hs0 : s.score = 0) : BothEven G s := by
  constructor
  · let so : State V := {
      untouched := ∅
      queue := [f, d]
      ko := false
      toMove := !s.toMove
      score := 0 }
    have hopen : step G s (.open d) = some so := by
      simp [step, so, hU, hqueue, hs0]
    have hchild : EvenWins G s.toMove so :=
      evenWins_of_untouched_empty s.toMove so (by simp [so]) (by simp [so])
    show EvenWins G s.toMove s
    exact EvenWins.choose s rfl (.open d) so hopen hchild
  · have hasMove : ∃ m t, step G s m = some t := by
      let so : State V := {
        untouched := ∅
        queue := [f, d]
        ko := false
        toMove := !s.toMove
        score := 0 }
      exact ⟨.open d, so, by simp [step, so, hU, hqueue, hs0]⟩
    show EvenWins G (!s.toMove) s
    refine EvenWins.answer s (by simp) hasMove ?_
    intro m t hstep
    cases m with
    | «open» x =>
        simp only [step] at hstep
        split at hstep
        · rename_i hx
          have hxd : x = d := by simpa [hU] using hx
          subst x
          cases hstep
          exact evenWins_of_untouched_empty (!s.toMove) _
            (by simp [hU]) (by simp [hs0])
        · contradiction
    | close =>
        let sc : State V := {
          untouched := {d}
          queue := []
          ko := false
          toMove := !s.toMove
          score := 0 }
        have hflip : flip G {d} f = 0 := by
          rw [flip_singleton_eq_adjacencyBit]
          simp [adjacencyBit, G.adj_comm, hd f]
        have hclose : step G s .close = some sc := by
          simp [step, sc, hU, hqueue, hko, hs0, hflip]
        have ht : t = sc := by
          rw [hclose] at hstep
          exact Option.some.inj hstep.symm
        subst t
        let so : State V := {
          untouched := ∅
          queue := [d]
          ko := true
          toMove := s.toMove
          score := 0 }
        have hopen : step G sc (.open d) = some so := by
          simp [step, sc, so]
        refine EvenWins.choose sc (by simp [sc]) (.open d) so hopen ?_
        exact evenWins_of_untouched_empty (!s.toMove) so
          (by simp [so]) (by simp [so])
    | pass => simp [step, hU] at hstep

omit [Fintype V] in
/-- A singleton queue whose only untouched label is an isolated dummy is
cold.  The unit score translation exchanges the score-zero both-even case
with the score-one both-odd case. -/
theorem isolated_singletonWall_cold
    {G : SimpleGraph V} {s : State V} {d f : V}
    (hd : IsDummy G d) (hU : s.untouched = {d})
    (hqueue : s.queue = [f]) (hko : s.ko = false) :
    BothEven G s ∨ BothOdd G s := by
  by_cases hs0 : s.score = 0
  · exact Or.inl
      (isolated_singletonWall_bothEven_of_score_zero hd hU hqueue hko hs0)
  · right
    have hs1 : s.score = 1 := zmod2_eq_one_of_ne_zero _ hs0
    let base := scoreTranslate 1 s
    have hbaseScore : base.score = 0 := by
      simp [base, scoreTranslate, hs1, CharTwo.add_self_eq_zero]
    have hbaseEven : BothEven G base :=
      isolated_singletonWall_bothEven_of_score_zero hd
        (by simpa [base, scoreTranslate] using hU)
        (by simpa [base, scoreTranslate] using hqueue)
        (by simpa [base, scoreTranslate] using hko) hbaseScore
    have htranslate : scoreTranslate 1 base = s := by
      exact scoreTranslate_one_involutive s
    rw [← htranslate]
    exact (bothOdd_scoreTranslate_one_iff_bothEven G base).2 hbaseEven

omit [Fintype V] in
/-- The isolated-dummy singleton fork cannot occur at a reachable
rank-minimal controlled state.  If another untouched label remains, one more
OPEN makes the two wall schedules equal while cold-class heredity keeps their
opposite classes.  If none remains, the state is directly cold. -/
theorem reachableMinimal_no_dummyOpenClose_singleton
    {G : SimpleGraph V} {root : State V} {seat : Bool}
    {s : State V} {d f : V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ u, ReachableFrom G root u → rank u < rank s →
      ¬MoverControlled G u ∧ ¬NonmoverControlled G u)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hqueue : s.queue = [f]) (hko : s.ko = false)
    (hdmem : d ∈ s.untouched) (hd : IsDummy G d) :
    ¬((left.selectedMove = some (.open d) ∧
          right.selectedMove = some .close) ∨
      (left.selectedMove = some .close ∧
          right.selectedMove = some (.open d))) := by
  intro hfork
  by_cases hmore : (s.untouched.erase d).Nonempty
  · obtain ⟨w, hwErase⟩ := hmore
    have hwd : w ≠ d := (Finset.mem_erase.mp hwErase).1
    have hw : w ∈ s.untouched := Finset.mem_of_mem_erase hwErase
    obtain ⟨sc, scd, scdw, so, sod, sodw,
        hclose, hcloseOpen, hcloseOpenOpen,
        hopen, hopenClose, hopenCloseOpen,
        _hU, _hqueue, _hko, _hturn, _hscore, hsheet⟩ :=
      singleton_wall_reconverges_after_open
        G s f d w hqueue hko hdmem hw hwd.symm
    have hbit : adjacencyBit G f d = 0 := by
      simp [adjacencyBit, G.adj_comm, hd f]
    have heq : scdw = sodw := by
      simpa [hbit, scoreTranslate] using hsheet
    have hreachSc : ReachableFrom G root sc := hreach.step hclose
    have hreachScd : ReachableFrom G root scd := hreachSc.step hcloseOpen
    have hreachScdw : ReachableFrom G root scdw :=
      hreachScd.step hcloseOpenOpen
    have hreachSo : ReachableFrom G root so := hreach.step hopen
    have hreachSod : ReachableFrom G root sod := hreachSo.step hopenClose
    have hreachSodw : ReachableFrom G root sodw :=
      hreachSod.step hopenCloseOpen
    have hnoScd : ¬MoverControlled G scd :=
      (hminimal scd hreachScd
        (lt_trans (rank_step_lt hcloseOpen) (rank_step_lt hclose))).1
    have hnoScdw : ¬MoverControlled G scdw :=
      (hminimal scdw hreachScdw
        (lt_trans (rank_step_lt hcloseOpenOpen)
          (lt_trans (rank_step_lt hcloseOpen) (rank_step_lt hclose)))).1
    have hnoSod : ¬MoverControlled G sod :=
      (hminimal sod hreachSod
        (lt_trans (rank_step_lt hopenClose) (rank_step_lt hopen))).1
    have hnoSodw : ¬MoverControlled G sodw :=
      (hminimal sodw hreachSodw
        (lt_trans (rank_step_lt hopenCloseOpen)
          (lt_trans (rank_step_lt hopenClose) (rank_step_lt hopen)))).1
    rcases hfork with hforward | hreverse
    · have hoddSo : BothOdd G so :=
        scoreCoupled_leftSelectedChild_bothOdd
          hreach hminimal left hturn (.open d) hforward.1 hopen
      have hevenSc : BothEven G sc :=
        scoreCoupled_rightSelectedChild_bothEven
          hreach hminimal right hturn .close hforward.2 hclose
      have hoddSod : BothOdd G sod :=
        hoddSo.step_of_not_moverControlled hopenClose hnoSod
      have hoddSodw : BothOdd G sodw :=
        hoddSod.step_of_not_moverControlled hopenCloseOpen hnoSodw
      have hevenScd : BothEven G scd :=
        hevenSc.step_of_not_moverControlled hcloseOpen hnoScd
      have hevenScdw : BothEven G scdw :=
        hevenScd.step_of_not_moverControlled hcloseOpenOpen hnoScdw
      exact hoddSodw.1 (heq ▸ hevenScdw.1)
    · have hoddSc : BothOdd G sc :=
        scoreCoupled_leftSelectedChild_bothOdd
          hreach hminimal left hturn .close hreverse.1 hclose
      have hevenSo : BothEven G so :=
        scoreCoupled_rightSelectedChild_bothEven
          hreach hminimal right hturn (.open d) hreverse.2 hopen
      have hoddScd : BothOdd G scd :=
        hoddSc.step_of_not_moverControlled hcloseOpen hnoScd
      have hoddScdw : BothOdd G scdw :=
        hoddScd.step_of_not_moverControlled hcloseOpenOpen hnoScdw
      have hevenSod : BothEven G sod :=
        hevenSo.step_of_not_moverControlled hopenClose hnoSod
      have hevenSodw : BothEven G sodw :=
        hevenSod.step_of_not_moverControlled hopenCloseOpen hnoSodw
      exact hoddScdw.1 (heq ▸ hevenSodw.1)
  · have hU : s.untouched = {d} := by
      ext x
      constructor
      · intro hx
        by_cases hxd : x = d
        · simp [hxd]
        · have hxErase : x ∈ s.untouched.erase d :=
            Finset.mem_erase.mpr ⟨hxd, hx⟩
          exact False.elim (hmore ⟨x, hxErase⟩)
      · intro hx
        have hxd : x = d := by simpa using hx
        simpa [hxd] using hdmem
    have hcold := isolated_singletonWall_cold hd hU hqueue hko
    have hmover : MoverControlled G s :=
      (scoreCoupledPair_controlled left right).2 hturn
    rcases hcold with heven | hodd
    · exact hmover.2 heven.2
    · exact hodd.1 hmover.1

omit [Fintype V] in
/-- Opening an isolated dummy behind a singleton real wall and then opening
the wall vertex gives a neutral four-move detour.  Fully draining `f,z,d` in
the two FIFO orders reaches one exact endpoint:

`OPEN z; CLOSE f; OPEN d; CLOSE z; CLOSE d`

equals

`OPEN d; OPEN z; CLOSE f; CLOSE d; CLOSE z`.

The only potentially different charge is the close of `f`; deleting the
isolated dummy does not change it. -/
theorem isolated_singleton_realFork_dummyDrain_bridge
    (G : SimpleGraph V) (s : State V) (d f z : V)
    (hqueue : s.queue = [f]) (_hko : s.ko = false)
    (hdmem : d ∈ s.untouched) (hzmem : z ∈ s.untouched)
    (hdz : d ≠ z) (hd : IsDummy G d) :
    ∃ so soc socd socdz leftEnd sd sdz sdzc sdzcd rightEnd,
      step G s (.open z) = some so ∧
      step G so .close = some soc ∧
      step G soc (.open d) = some socd ∧
      step G socd .close = some socdz ∧
      step G socdz .close = some leftEnd ∧
      step G s (.open d) = some sd ∧
      step G sd (.open z) = some sdz ∧
      step G sdz .close = some sdzc ∧
      step G sdzc .close = some sdzcd ∧
      step G sdzcd .close = some rightEnd ∧
      leftEnd = rightEnd := by
  have hdEraseZ : d ∈ s.untouched.erase z :=
    Finset.mem_erase.mpr ⟨hdz, hdmem⟩
  have hzEraseD : z ∈ s.untouched.erase d :=
    Finset.mem_erase.mpr ⟨hdz.symm, hzmem⟩
  have hfd : adjacencyBit G f d = 0 := by
    simp [adjacencyBit, G.adj_comm, hd f]
  have hErase : (s.untouched.erase z).erase d =
      (s.untouched.erase d).erase z := by
    ext x
    simp [and_left_comm]
  have hflip : flip G (s.untouched.erase z) f =
      flip G ((s.untouched.erase d).erase z) f := by
    have hsplit := flip_eq_flip_erase_add
      (G := G) (f := f) hdEraseZ
    rw [hfd, add_zero, hErase] at hsplit
    exact hsplit
  let so : State V := {
    untouched := s.untouched.erase z
    queue := [f, z]
    ko := false
    toMove := !s.toMove
    score := s.score }
  let soc : State V := {
    untouched := s.untouched.erase z
    queue := [z]
    ko := false
    toMove := s.toMove
    score := s.score + flip G (s.untouched.erase z) f }
  let socd : State V := {
    untouched := (s.untouched.erase z).erase d
    queue := [z, d]
    ko := false
    toMove := !s.toMove
    score := s.score + flip G (s.untouched.erase z) f }
  let socdz : State V := {
    untouched := (s.untouched.erase z).erase d
    queue := [d]
    ko := false
    toMove := s.toMove
    score := s.score + flip G (s.untouched.erase z) f +
      flip G ((s.untouched.erase z).erase d) z }
  let leftEnd : State V := {
    untouched := (s.untouched.erase z).erase d
    queue := []
    ko := false
    toMove := !s.toMove
    score := s.score + flip G (s.untouched.erase z) f +
      flip G ((s.untouched.erase z).erase d) z }
  let sd : State V := {
    untouched := s.untouched.erase d
    queue := [f, d]
    ko := false
    toMove := !s.toMove
    score := s.score }
  let sdz : State V := {
    untouched := (s.untouched.erase d).erase z
    queue := [f, d, z]
    ko := false
    toMove := s.toMove
    score := s.score }
  let sdzc : State V := {
    untouched := (s.untouched.erase d).erase z
    queue := [d, z]
    ko := false
    toMove := !s.toMove
    score := s.score + flip G ((s.untouched.erase d).erase z) f }
  let sdzcd : State V := {
    untouched := (s.untouched.erase d).erase z
    queue := [z]
    ko := false
    toMove := s.toMove
    score := s.score + flip G ((s.untouched.erase d).erase z) f }
  let rightEnd : State V := {
    untouched := (s.untouched.erase d).erase z
    queue := []
    ko := false
    toMove := !s.toMove
    score := s.score + flip G ((s.untouched.erase d).erase z) f +
      flip G ((s.untouched.erase d).erase z) z }
  refine ⟨so, soc, socd, socdz, leftEnd, sd, sdz, sdzc, sdzcd,
    rightEnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [step, so, hqueue, hzmem]
  · simp [step, so, soc]
  · simp [step, soc, socd, hdEraseZ]
  · simp [step, socd, socdz]
  · simp [step, socdz, leftEnd, flip_dummy hd]
  · simp [step, sd, hqueue, hdmem]
  · simp [step, sd, sdz, hzEraseD]
  · simp [step, sdz, sdzc]
  · simp [step, sdzc, sdzcd, flip_dummy hd]
  · simp [step, sdzcd, rightEnd]
  · simp [leftEnd, rightEnd, hErase, hflip]

private def singletonForkCloseWord (q : List V) : List (Move V) :=
  q.map fun _ ↦ .close

omit [Fintype V] in
private theorem StepPath.singletonForkAppend
    {G : SimpleGraph V} {s t u : State V}
    {ms ns : List (Move V)} (hst : StepPath G s ms t)
    (htu : StepPath G t ns u) : StepPath G s (ms ++ ns) u := by
  induction hst with
  | nil => simpa using htu
  | cons hstep htail ih =>
      simpa using StepPath.cons hstep (ih htu)

omit [Fintype V] in
private theorem stepPath_singletonForkDrainState
    (G : SimpleGraph V) (U : Finset V) :
    ∀ (q : List V) (turn : Bool) (score : ZMod 2),
      ∃ t, StepPath G (drainState U q turn score)
          (singletonForkCloseWord q) t ∧
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
      · simpa [singletonForkCloseWord, next] using
          StepPath.cons hclose htail
      · simpa [List.sum_cons, add_assoc] using hscore

omit [Fintype V] [DecidableEq V] in
private theorem turnAfter_singletonForkCloseWord_eq_of_length_eq
    {q r : List V} (h : q.length = r.length) (turn : Bool) :
    turnAfter (singletonForkCloseWord q) turn =
      turnAfter (singletonForkCloseWord r) turn := by
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
          simp only [singletonForkCloseWord, List.map_cons, turnAfter]
          exact ih (Nat.succ.inj h) (!turn)

omit [Fintype V] in
/-- Opening an isolated dummy and a distinct real label in either order, then
draining the complete fixed-carrier queue, reaches one exact endpoint.  The
queue orders differ only by the transposition of `d,z`; CLOSE charges are
summed in the same untouched set, and the dummy term is zero. -/
theorem isolated_dummy_real_open_orders_drain_reconverge
    (G : SimpleGraph V) (s : State V) (d z : V)
    (hdmem : d ∈ s.untouched) (hzmem : z ∈ s.untouched)
    (hdz : d ≠ z) (hd : IsDummy G d) :
    ∃ sd sz t,
      step G s (.open d) = some sd ∧
      step G s (.open z) = some sz ∧
      StepPath G sd
        ([.open z] ++ singletonForkCloseWord (s.queue ++ [d, z])) t ∧
      StepPath G sz
        ([.open d] ++ singletonForkCloseWord (s.queue ++ [z, d])) t := by
  let sd : State V := {
    untouched := s.untouched.erase d
    queue := s.queue ++ [d]
    ko := s.queue.isEmpty
    toMove := !s.toMove
    score := s.score }
  let sz : State V := {
    untouched := s.untouched.erase z
    queue := s.queue ++ [z]
    ko := s.queue.isEmpty
    toMove := !s.toMove
    score := s.score }
  let sdz : State V := {
    untouched := (s.untouched.erase d).erase z
    queue := s.queue ++ [d, z]
    ko := false
    toMove := s.toMove
    score := s.score }
  let szd : State V := {
    untouched := (s.untouched.erase z).erase d
    queue := s.queue ++ [z, d]
    ko := false
    toMove := s.toMove
    score := s.score }
  have hopenD : step G s (.open d) = some sd := by
    simp [step, sd, hdmem]
  have hopenZ : step G s (.open z) = some sz := by
    simp [step, sz, hzmem]
  have hzEraseD : z ∈ s.untouched.erase d :=
    Finset.mem_erase.mpr ⟨hdz.symm, hzmem⟩
  have hdEraseZ : d ∈ s.untouched.erase z :=
    Finset.mem_erase.mpr ⟨hdz, hdmem⟩
  have hopenDZ : step G sd (.open z) = some sdz := by
    simp [step, sd, sdz, hzEraseD, List.append_assoc]
  have hopenZD : step G sz (.open d) = some szd := by
    simp [step, sz, szd, hdEraseZ, List.append_assoc]
  have hU : sdz.untouched = szd.untouched := by
    ext x
    simp [sdz, szd, and_left_comm]
  have hturn : sdz.toMove = szd.toMove := by simp [sdz, szd]
  have hscore : sdz.score = szd.score := by simp [sdz, szd]
  have hAasDrain : sdz = drainState sdz.untouched sdz.queue
      sdz.toMove sdz.score := by
    simp [sdz, drainState]
  have hBasDrain : szd = drainState szd.untouched szd.queue
      szd.toMove szd.score := by
    simp [szd, drainState]
  obtain ⟨tA, hpathA, htAU, htAq, htAko, htAscore⟩ :=
    stepPath_singletonForkDrainState
      G sdz.untouched sdz.queue sdz.toMove sdz.score
  obtain ⟨tB, hpathB, htBU, htBq, htBko, htBscore⟩ :=
    stepPath_singletonForkDrainState
      G szd.untouched szd.queue szd.toMove szd.score
  have hlen : sdz.queue.length = szd.queue.length := by
    simp [sdz, szd]
  have htTurnEq : tA.toMove = tB.toMove := by
    have hpathATurn := hpathA.toMove_eq_turnAfter
    have hpathBTurn := hpathB.toMove_eq_turnAfter
    rw [hAasDrain] at hpathATurn
    rw [hBasDrain] at hpathBTurn
    simp only [drainState] at hpathATurn hpathBTurn
    rw [hpathATurn, hpathBTurn, hturn]
    exact turnAfter_singletonForkCloseWord_eq_of_length_eq hlen szd.toMove
  have hsum :
      (sdz.queue.map (flip G sdz.untouched)).sum =
        (szd.queue.map (flip G szd.untouched)).sum := by
    rw [hU]
    simp only [sdz, szd, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [flip_dummy hd]
    abel
  have htScoreEq : tA.score = tB.score := by
    calc
      tA.score = sdz.score +
          (sdz.queue.map (flip G sdz.untouched)).sum := htAscore
      _ = szd.score +
          (szd.queue.map (flip G szd.untouched)).sum := by
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
  refine ⟨sd, sz, tA, hopenD, hopenZ, ?_, ?_⟩
  · have hopenPath : StepPath G sd [.open z] sdz :=
      StepPath.cons hopenDZ (StepPath.nil _)
    have hdrain : StepPath G sdz
        (singletonForkCloseWord sdz.queue) tA := hAasDrain ▸ hpathA
    simpa [sdz] using hopenPath.singletonForkAppend hdrain
  · have hopenPath : StepPath G sz [.open d] szd :=
      StepPath.cons hopenZD (StepPath.nil _)
    have hdrain : StepPath G szd
        (singletonForkCloseWord szd.queue) tA := hBasDrain ▸ hpathB
    simpa [szd] using hopenPath.singletonForkAppend hdrain

omit [Fintype V] in
/-- Three cyclically rotated OPEN schedules `x,y,d` and `y,d,x`, followed by
complete fixed-carrier drains, have one exact endpoint when `d` is isolated.
This is the two-real-OPEN analogue of the preceding transposition bridge. -/
theorem isolated_twoRealOpen_orders_drain_reconverge
    (G : SimpleGraph V) (s : State V) (d x y : V)
    (hdmem : d ∈ s.untouched) (hxmem : x ∈ s.untouched)
    (hymem : y ∈ s.untouched)
    (hxy : x ≠ y) (hxd : x ≠ d) (hyd : y ≠ d)
    (hd : IsDummy G d) :
    ∃ sx sy t,
      step G s (.open x) = some sx ∧
      step G s (.open y) = some sy ∧
      StepPath G sx
        ([.open y, .open d] ++
          singletonForkCloseWord (s.queue ++ [x, y, d])) t ∧
      StepPath G sy
        ([.open d, .open x] ++
          singletonForkCloseWord (s.queue ++ [y, d, x])) t := by
  let sx : State V := {
    untouched := s.untouched.erase x
    queue := s.queue ++ [x]
    ko := s.queue.isEmpty
    toMove := !s.toMove
    score := s.score }
  let sy : State V := {
    untouched := s.untouched.erase y
    queue := s.queue ++ [y]
    ko := s.queue.isEmpty
    toMove := !s.toMove
    score := s.score }
  let sxy : State V := {
    untouched := (s.untouched.erase x).erase y
    queue := s.queue ++ [x, y]
    ko := false
    toMove := s.toMove
    score := s.score }
  let syd : State V := {
    untouched := (s.untouched.erase y).erase d
    queue := s.queue ++ [y, d]
    ko := false
    toMove := s.toMove
    score := s.score }
  let sxyd : State V := {
    untouched := ((s.untouched.erase x).erase y).erase d
    queue := s.queue ++ [x, y, d]
    ko := false
    toMove := !s.toMove
    score := s.score }
  let sydx : State V := {
    untouched := ((s.untouched.erase y).erase d).erase x
    queue := s.queue ++ [y, d, x]
    ko := false
    toMove := !s.toMove
    score := s.score }
  have hsx : step G s (.open x) = some sx := by
    simp [step, sx, hxmem]
  have hsy : step G s (.open y) = some sy := by
    simp [step, sy, hymem]
  have hyx : y ∈ s.untouched.erase x :=
    Finset.mem_erase.mpr ⟨hxy.symm, hymem⟩
  have hdy : d ∈ s.untouched.erase y :=
    Finset.mem_erase.mpr ⟨hyd.symm, hdmem⟩
  have hsxy : step G sx (.open y) = some sxy := by
    simp [step, sx, sxy, hyx, List.append_assoc]
  have hsyd : step G sy (.open d) = some syd := by
    simp [step, sy, syd, hdy, List.append_assoc]
  have hdxy : d ∈ (s.untouched.erase x).erase y := by
    simp [hdmem, hxd.symm, hyd.symm]
  have hxyd : x ∈ (s.untouched.erase y).erase d := by
    simp [hxmem, hxy, hxd]
  have hsxyd : step G sxy (.open d) = some sxyd := by
    simp [step, sxy, sxyd, hdxy, List.append_assoc]
  have hsydx : step G syd (.open x) = some sydx := by
    simp [step, syd, sydx, hxyd, List.append_assoc]
  have hU : sxyd.untouched = sydx.untouched := by
    ext v
    simp [sxyd, sydx, and_left_comm]
  have hAasDrain : sxyd = drainState sxyd.untouched sxyd.queue
      sxyd.toMove sxyd.score := by
    simp [sxyd, drainState]
  have hBasDrain : sydx = drainState sydx.untouched sydx.queue
      sydx.toMove sydx.score := by
    simp [sydx, drainState]
  obtain ⟨tA, hpathA, htAU, htAq, htAko, htAscore⟩ :=
    stepPath_singletonForkDrainState
      G sxyd.untouched sxyd.queue sxyd.toMove sxyd.score
  obtain ⟨tB, hpathB, htBU, htBq, htBko, htBscore⟩ :=
    stepPath_singletonForkDrainState
      G sydx.untouched sydx.queue sydx.toMove sydx.score
  have hlen : sxyd.queue.length = sydx.queue.length := by
    simp [sxyd, sydx]
  have htTurnEq : tA.toMove = tB.toMove := by
    have hpathATurn := hpathA.toMove_eq_turnAfter
    have hpathBTurn := hpathB.toMove_eq_turnAfter
    rw [hAasDrain] at hpathATurn
    rw [hBasDrain] at hpathBTurn
    simp only [drainState] at hpathATurn hpathBTurn
    rw [hpathATurn, hpathBTurn]
    exact turnAfter_singletonForkCloseWord_eq_of_length_eq hlen sydx.toMove
  have hsum :
      (sxyd.queue.map (flip G sxyd.untouched)).sum =
        (sydx.queue.map (flip G sydx.untouched)).sum := by
    rw [hU]
    simp only [sxyd, sydx, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [flip_dummy hd]
    abel
  have htScoreEq : tA.score = tB.score := by
    calc
      tA.score = sxyd.score +
          (sxyd.queue.map (flip G sxyd.untouched)).sum := htAscore
      _ = sydx.score +
          (sydx.queue.map (flip G sydx.untouched)).sum := by
            simp only [sxyd, sydx]
            rw [hsum]
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
    have hdrain : StepPath G sxyd
        (singletonForkCloseWord sxyd.queue) tA := hAasDrain ▸ hpathA
    simpa [sxyd] using hopenPath.singletonForkAppend hdrain
  · have hopenPath : StepPath G sy [.open d, .open x] sydx :=
      StepPath.cons hsyd (StepPath.cons hsydx (StepPath.nil _))
    have hdrain : StepPath G sydx
        (singletonForkCloseWord sydx.queue) tA := hBasDrain ▸ hpathB
    simpa [sydx] using hopenPath.singletonForkAppend hdrain

omit [Fintype V] in
private theorem BothOdd.stepPath_of_singletonReachableMinimum
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
private theorem BothEven.stepPath_of_singletonReachableMinimum
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
/-- A real OPEN/CLOSE singleton fork is also impossible at a reachable
controlled minimum while an isolated dummy remains untouched.  Opening the
dummy gives a third lower cold child.  Two neutral-interval schedules connect
that child separately to the CLOSE-selected and real-OPEN-selected children,
which have opposite cold classes. -/
theorem reachableMinimal_no_realOpenClose_singleton
    {G : SimpleGraph V} {root : State V} {seat : Bool}
    {s : State V} {d f z : V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ u, ReachableFrom G root u → rank u < rank s →
      ¬MoverControlled G u ∧ ¬NonmoverControlled G u)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hqueue : s.queue = [f]) (hko : s.ko = false)
    (hdmem : d ∈ s.untouched) (hzmem : z ∈ s.untouched)
    (hzd : z ≠ d) (hd : IsDummy G d) :
    ¬((left.selectedMove = some (.open z) ∧
          right.selectedMove = some .close) ∨
      (left.selectedMove = some .close ∧
          right.selectedMove = some (.open z))) := by
  intro hfork
  obtain ⟨sc, scd, scdz, sd, sdc, sdcz,
      hclose, hcloseOpen, hcloseOpenOpen,
      hopenD, hopenDClose, hopenDCloseOpen,
      _hU, _hqueue, _hko, _hturn, _hscore, hsheet⟩ :=
    singleton_wall_reconverges_after_open
      G s f d z hqueue hko hdmem hzmem hzd.symm
  have hbit : adjacencyBit G f d = 0 := by
    simp [adjacencyBit, G.adj_comm, hd f]
  have heqClose : scdz = sdcz := by
    simpa [hbit, scoreTranslate] using hsheet
  obtain ⟨so, soc, socd, socdz, leftEnd, sd', sdz, sdzc, sdzcd,
      rightEnd, hopenZ, hopenZClose, hopenZCloseOpenD,
      hopenZCloseOpenDClose, hopenZCloseOpenDCloseClose,
      hopenD', hopenDOpenZ, hopenDOpenZClose,
      hopenDOpenZCloseClose, hopenDOpenZCloseCloseClose, heqOpen⟩ :=
    isolated_singleton_realFork_dummyDrain_bridge
      G s d f z hqueue hko hdmem hzmem hzd.symm hd
  have hsd : sd' = sd := by
    rw [hopenD] at hopenD'
    exact Option.some.inj hopenD'.symm
  subst sd'
  have hreachSc : ReachableFrom G root sc := hreach.step hclose
  have hreachSo : ReachableFrom G root so := hreach.step hopenZ
  have hreachSd : ReachableFrom G root sd := hreach.step hopenD
  have hrankSc : rank sc < rank s := rank_step_lt hclose
  have hrankSo : rank so < rank s := rank_step_lt hopenZ
  have hrankSd : rank sd < rank s := rank_step_lt hopenD
  have hcoldSd : BothEven G sd ∨ BothOdd G sd := by
    rcases four_outcome_cases G sd with heven | hmover | hnonmover | hodd
    · exact Or.inl heven
    · exact False.elim ((hminimal sd hreachSd hrankSd).1 hmover)
    · exact False.elim ((hminimal sd hreachSd hrankSd).2 hnonmover)
    · exact Or.inr hodd
  have hpathSc : StepPath G sc [.open d, .open z] scdz :=
    StepPath.cons hcloseOpen
      (StepPath.cons hcloseOpenOpen (StepPath.nil _))
  have hpathSdClose : StepPath G sd [.close, .open z] sdcz :=
    StepPath.cons hopenDClose
      (StepPath.cons hopenDCloseOpen (StepPath.nil _))
  have hpathSo : StepPath G so
      [.close, .open d, .close, .close] leftEnd :=
    StepPath.cons hopenZClose
      (StepPath.cons hopenZCloseOpenD
        (StepPath.cons hopenZCloseOpenDClose
          (StepPath.cons hopenZCloseOpenDCloseClose (StepPath.nil _))))
  have hpathSdOpen : StepPath G sd
      [.open z, .close, .close, .close] rightEnd :=
    StepPath.cons hopenDOpenZ
      (StepPath.cons hopenDOpenZClose
        (StepPath.cons hopenDOpenZCloseClose
          (StepPath.cons hopenDOpenZCloseCloseClose (StepPath.nil _))))
  rcases hfork with hforward | hreverse
  · have hoddSo : BothOdd G so :=
      scoreCoupled_leftSelectedChild_bothOdd
        hreach hminimal left hturn (.open z) hforward.1 hopenZ
    have hevenSc : BothEven G sc :=
      scoreCoupled_rightSelectedChild_bothEven
        hreach hminimal right hturn .close hforward.2 hclose
    rcases hcoldSd with hevenSd | hoddSd
    · have hoddEnd : BothOdd G leftEnd :=
        hoddSo.stepPath_of_singletonReachableMinimum
          hminimal hreachSo hrankSo hpathSo
      have hevenEnd : BothEven G rightEnd :=
        hevenSd.stepPath_of_singletonReachableMinimum
          hminimal hreachSd hrankSd hpathSdOpen
      exact hoddEnd.1 (heqOpen ▸ hevenEnd.1)
    · have hevenEnd : BothEven G scdz :=
        hevenSc.stepPath_of_singletonReachableMinimum
          hminimal hreachSc hrankSc hpathSc
      have hoddEnd : BothOdd G sdcz :=
        hoddSd.stepPath_of_singletonReachableMinimum
          hminimal hreachSd hrankSd hpathSdClose
      exact hoddEnd.1 (heqClose ▸ hevenEnd.1)
  · have hoddSc : BothOdd G sc :=
      scoreCoupled_leftSelectedChild_bothOdd
        hreach hminimal left hturn .close hreverse.1 hclose
    have hevenSo : BothEven G so :=
      scoreCoupled_rightSelectedChild_bothEven
        hreach hminimal right hturn (.open z) hreverse.2 hopenZ
    rcases hcoldSd with hevenSd | hoddSd
    · have hoddEnd : BothOdd G scdz :=
        hoddSc.stepPath_of_singletonReachableMinimum
          hminimal hreachSc hrankSc hpathSc
      have hevenEnd : BothEven G sdcz :=
        hevenSd.stepPath_of_singletonReachableMinimum
          hminimal hreachSd hrankSd hpathSdClose
      exact hoddEnd.1 (heqClose.symm ▸ hevenEnd.1)
    · have hevenEnd : BothEven G leftEnd :=
        hevenSo.stepPath_of_singletonReachableMinimum
          hminimal hreachSo hrankSo hpathSo
      have hoddEnd : BothOdd G rightEnd :=
        hoddSd.stepPath_of_singletonReachableMinimum
          hminimal hreachSd hrankSd hpathSdOpen
      exact hoddEnd.1 (heqOpen.symm ▸ hevenEnd.1)

omit [Fintype V] in
/-- The away-singleton real OPEN/CLOSE survivor is impossible as well while
the isolated dummy remains untouched.  The dummy child meets the CLOSE child
through the ordinary neutral OPEN/CLOSE square, and meets the real-OPEN child
after the two OPEN orders are completely drained.  Hence it cannot be cold
while the selected children have opposite cold classes.  No assumption on
the front--opened-vertex adjacency is needed. -/
theorem reachableMinimal_no_realOpenClose_awaySingleton
    {G : SimpleGraph V} {root : State V} {seat : Bool}
    {s : State V} {d f z : V} {q : List V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ u, ReachableFrom G root u → rank u < rank s →
      ¬MoverControlled G u ∧ ¬NonmoverControlled G u)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hqueue : s.queue = f :: q) (hq : q ≠ []) (hko : s.ko = false)
    (hdmem : d ∈ s.untouched) (hzmem : z ∈ s.untouched)
    (hzd : z ≠ d) (hd : IsDummy G d) :
    ¬((left.selectedMove = some (.open z) ∧
          right.selectedMove = some .close) ∨
      (left.selectedMove = some .close ∧
          right.selectedMove = some (.open z))) := by
  intro hfork
  obtain ⟨sd, sdc, sc, scd, hopenD, hopenDClose, hclose,
      hcloseOpenD, heqClose⟩ :=
    isolatedUntouched_open_close_commute
      G s d f q hqueue hq hko hdmem hd
  obtain ⟨sd', so, openEnd, hopenD', hopenZ, hpathSdOpen, hpathSo⟩ :=
    isolated_dummy_real_open_orders_drain_reconverge
      G s d z hdmem hzmem hzd.symm hd
  have hsd : sd' = sd := by
    rw [hopenD] at hopenD'
    exact Option.some.inj hopenD'.symm
  subst sd'
  have hreachSd : ReachableFrom G root sd := hreach.step hopenD
  have hreachSc : ReachableFrom G root sc := hreach.step hclose
  have hreachSo : ReachableFrom G root so := hreach.step hopenZ
  have hrankSd : rank sd < rank s := rank_step_lt hopenD
  have hrankSc : rank sc < rank s := rank_step_lt hclose
  have hrankSo : rank so < rank s := rank_step_lt hopenZ
  have hcoldSd : BothEven G sd ∨ BothOdd G sd := by
    rcases four_outcome_cases G sd with heven | hmover | hnonmover | hodd
    · exact Or.inl heven
    · exact False.elim ((hminimal sd hreachSd hrankSd).1 hmover)
    · exact False.elim ((hminimal sd hreachSd hrankSd).2 hnonmover)
    · exact Or.inr hodd
  have hpathSdClose : StepPath G sd [.close] sdc :=
    StepPath.cons hopenDClose (StepPath.nil _)
  have hpathSc : StepPath G sc [.open d] scd :=
    StepPath.cons hcloseOpenD (StepPath.nil _)
  rcases hfork with hforward | hreverse
  · have hoddSo : BothOdd G so :=
      scoreCoupled_leftSelectedChild_bothOdd
        hreach hminimal left hturn (.open z) hforward.1 hopenZ
    have hevenSc : BothEven G sc :=
      scoreCoupled_rightSelectedChild_bothEven
        hreach hminimal right hturn .close hforward.2 hclose
    rcases hcoldSd with hevenSd | hoddSd
    · have hoddEnd : BothOdd G openEnd :=
        hoddSo.stepPath_of_singletonReachableMinimum
          hminimal hreachSo hrankSo hpathSo
      have hevenEnd : BothEven G openEnd :=
        hevenSd.stepPath_of_singletonReachableMinimum
          hminimal hreachSd hrankSd hpathSdOpen
      exact hoddEnd.1 hevenEnd.1
    · have hevenEnd : BothEven G scd :=
        hevenSc.stepPath_of_singletonReachableMinimum
          hminimal hreachSc hrankSc hpathSc
      have hoddEnd : BothOdd G sdc :=
        hoddSd.stepPath_of_singletonReachableMinimum
          hminimal hreachSd hrankSd hpathSdClose
      exact hoddEnd.1 (heqClose.symm ▸ hevenEnd.1)
  · have hoddSc : BothOdd G sc :=
      scoreCoupled_leftSelectedChild_bothOdd
        hreach hminimal left hturn .close hreverse.1 hclose
    have hevenSo : BothEven G so :=
      scoreCoupled_rightSelectedChild_bothEven
        hreach hminimal right hturn (.open z) hreverse.2 hopenZ
    rcases hcoldSd with hevenSd | hoddSd
    · have hoddEnd : BothOdd G scd :=
        hoddSc.stepPath_of_singletonReachableMinimum
          hminimal hreachSc hrankSc hpathSc
      have hevenEnd : BothEven G sdc :=
        hevenSd.stepPath_of_singletonReachableMinimum
          hminimal hreachSd hrankSd hpathSdClose
      exact hoddEnd.1 (heqClose ▸ hevenEnd.1)
    · have hevenEnd : BothEven G openEnd :=
        hevenSo.stepPath_of_singletonReachableMinimum
          hminimal hreachSo hrankSo hpathSo
      have hoddEnd : BothOdd G openEnd :=
        hoddSd.stepPath_of_singletonReachableMinimum
          hminimal hreachSd hrankSd hpathSdOpen
      exact hoddEnd.1 hevenEnd.1

omit [Fintype V] in
/-- The same complete-drain bridge eliminates a distinct-OPEN fork in which
one selected move spends the isolated dummy and the other opens a real label.
The selected children already have opposite cold classes, while the two OPEN
orders drain to one state. -/
theorem reachableMinimal_no_dummyRealOpenFork
    {G : SimpleGraph V} {root : State V} {seat : Bool}
    {s : State V} {d z : V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ u, ReachableFrom G root u → rank u < rank s →
      ¬MoverControlled G u ∧ ¬NonmoverControlled G u)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hdmem : d ∈ s.untouched) (hzmem : z ∈ s.untouched)
    (hzd : z ≠ d) (hd : IsDummy G d) :
    ¬((left.selectedMove = some (.open d) ∧
          right.selectedMove = some (.open z)) ∨
      (left.selectedMove = some (.open z) ∧
          right.selectedMove = some (.open d))) := by
  intro hfork
  obtain ⟨sd, sz, t, hopenD, hopenZ, hpathD, hpathZ⟩ :=
    isolated_dummy_real_open_orders_drain_reconverge
      G s d z hdmem hzmem hzd.symm hd
  have hreachSd : ReachableFrom G root sd := hreach.step hopenD
  have hreachSz : ReachableFrom G root sz := hreach.step hopenZ
  have hrankSd : rank sd < rank s := rank_step_lt hopenD
  have hrankSz : rank sz < rank s := rank_step_lt hopenZ
  rcases hfork with hforward | hreverse
  · have hoddSd : BothOdd G sd :=
      scoreCoupled_leftSelectedChild_bothOdd
        hreach hminimal left hturn (.open d) hforward.1 hopenD
    have hevenSz : BothEven G sz :=
      scoreCoupled_rightSelectedChild_bothEven
        hreach hminimal right hturn (.open z) hforward.2 hopenZ
    have hoddEnd : BothOdd G t :=
      hoddSd.stepPath_of_singletonReachableMinimum
        hminimal hreachSd hrankSd hpathD
    have hevenEnd : BothEven G t :=
      hevenSz.stepPath_of_singletonReachableMinimum
        hminimal hreachSz hrankSz hpathZ
    exact hoddEnd.1 hevenEnd.1
  · have hoddSz : BothOdd G sz :=
      scoreCoupled_leftSelectedChild_bothOdd
        hreach hminimal left hturn (.open z) hreverse.1 hopenZ
    have hevenSd : BothEven G sd :=
      scoreCoupled_rightSelectedChild_bothEven
        hreach hminimal right hturn (.open d) hreverse.2 hopenD
    have hoddEnd : BothOdd G t :=
      hoddSz.stepPath_of_singletonReachableMinimum
        hminimal hreachSz hrankSz hpathZ
    have hevenEnd : BothEven G t :=
      hevenSd.stepPath_of_singletonReachableMinimum
        hminimal hreachSd hrankSd hpathD
    exact hoddEnd.1 hevenEnd.1

omit [Fintype V] in
/-- Two distinct real selected OPENs are likewise impossible while the dummy
remains live: cyclically draft the other real label and the dummy, then drain
both fixed-carrier queues to the common endpoint above. -/
theorem reachableMinimal_no_twoRealOpenFork
    {G : SimpleGraph V} {root : State V} {seat : Bool}
    {s : State V} {d x y : V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ u, ReachableFrom G root u → rank u < rank s →
      ¬MoverControlled G u ∧ ¬NonmoverControlled G u)
    (left : OddStrategy G seat s)
    (right : OddStrategy G seat (scoreTranslate 1 s))
    (hturn : s.toMove = !seat)
    (hleft : left.selectedMove = some (.open x))
    (hright : right.selectedMove = some (.open y))
    (hxy : x ≠ y) (hdmem : d ∈ s.untouched)
    (hxd : x ≠ d) (hyd : y ≠ d) (hd : IsDummy G d) : False := by
  have hxmem : x ∈ s.untouched := by
    cases left with
    | terminal _ _ _ => simp [OddStrategy.selectedMove] at hleft
    | answer _ _ _ _ => simp [OddStrategy.selectedMove] at hleft
    | choose _ _ move u hstep tail =>
        have hm : move = .open x := by
          simpa [OddStrategy.selectedMove] using Option.some.inj hleft
        subst move
        simp only [step] at hstep
        split at hstep
        · assumption
        · contradiction
  have hymem : y ∈ s.untouched := by
    cases right with
    | terminal _ _ _ => simp [OddStrategy.selectedMove] at hright
    | answer _ _ _ _ => simp [OddStrategy.selectedMove] at hright
    | choose _ _ move u hstep tail =>
        have hm : move = .open y := by
          simpa [OddStrategy.selectedMove] using Option.some.inj hright
        subst move
        obtain ⟨t, hbase, _⟩ :=
          (step_scoreTranslate_eq_some_iff G 1 s u (.open y)).mp hstep
        simp only [step] at hbase
        split at hbase
        · assumption
        · contradiction
  obtain ⟨sx, sy, t, hstepX, hstepY, hpathX, hpathY⟩ :=
    isolated_twoRealOpen_orders_drain_reconverge
      G s d x y hdmem hxmem hymem hxy hxd hyd hd
  have hoddSx : BothOdd G sx :=
    scoreCoupled_leftSelectedChild_bothOdd
      hreach hminimal left hturn (.open x) hleft hstepX
  have hevenSy : BothEven G sy :=
    scoreCoupled_rightSelectedChild_bothEven
      hreach hminimal right hturn (.open y) hright hstepY
  have hoddEnd : BothOdd G t :=
    hoddSx.stepPath_of_singletonReachableMinimum
      hminimal (hreach.step hstepX) (rank_step_lt hstepX) hpathX
  have hevenEnd : BothEven G t :=
    hevenSy.stepPath_of_singletonReachableMinimum
      hminimal (hreach.step hstepY) (rank_step_lt hstepY) hpathY
  exact hoddEnd.1 hevenEnd.1

omit [Fintype V] in
/-- Complete live-dummy exclusion at a reachable rank-minimal controlled
state.  The score-coupled policies must fork immediately.  A distinct-OPEN
fork is eliminated by the complete-drain bridges, while every OPEN/CLOSE fork
is eliminated by the singleton or away-singleton neutral-dummy joins. -/
theorem reachableMinimal_controlled_dummy_not_untouched
    {G : SimpleGraph V} {root s : State V} {d : V}
    (hreach : ReachableFrom G root s)
    (hminimal : ∀ u, ReachableFrom G root u → rank u < rank s →
      ¬MoverControlled G u ∧ ¬NonmoverControlled G u)
    (hcontrolled : MoverControlled G s ∨ NonmoverControlled G s)
    (hd : IsDummy G d) : d ∉ s.untouched := by
  intro hdmem
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
        obtain ⟨m, t, hstep⟩ := not_terminal_has_step hnotTerminal
        exact (hminimal t (hreach.step hstep) (rank_step_lt hstep)).1
          (hn.every_child_moverControlled hstep))
  obtain ⟨left, right, _hdiv⟩ := hmover.exists_scoreCoupledDivergence
  have hturn : s.toMove = !(!s.toMove) := by simp
  obtain ⟨u₀, u₁, m₀, m₁, hleft, hright, hstep₀, hstep₁, hne⟩ :=
    reachableMinimal_scoreCoupled_currentFork
      hreach hminimal left right hturn
  obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ :=
    distinct_legal_moves_include_open hstep₀ hstep₁ hne
  · by_cases hopen₁ : ∃ y, m₁ = .open y
    · obtain ⟨y, rfl⟩ := hopen₁
      have hxmem : x ∈ s.untouched := by
        simp only [step] at hstep₀
        split at hstep₀
        · assumption
        · contradiction
      have hymem : y ∈ s.untouched := by
        simp only [step] at hstep₁
        split at hstep₁
        · assumption
        · contradiction
      by_cases hxd : x = d
      · subst x
        have hyd : y ≠ d := by
          intro hyd
          subst y
          exact hne rfl
        exact reachableMinimal_no_dummyRealOpenFork
          hreach hminimal left right hturn hdmem hymem hyd hd
          (Or.inl ⟨hleft, hright⟩)
      · by_cases hyd : y = d
        · subst y
          exact reachableMinimal_no_dummyRealOpenFork
            hreach hminimal left right hturn hdmem hxmem hxd hd
            (Or.inr ⟨hleft, hright⟩)
        · exact reachableMinimal_no_twoRealOpenFork
            hreach hminimal left right hturn hleft hright
            (by simpa using hne) hdmem hxd hyd hd
    · have hm₁ : m₁ = .close :=
        open_and_nonopen_legal_forces_close hdmem hstep₁ hopen₁
      subst m₁
      obtain ⟨f, q, hqueue, _⟩ := close_removes_front hstep₁
      have hko : s.ko = false := by
        cases hk : s.ko with
        | false => rfl
        | true => simp [step, hqueue, hk] at hstep₁
      by_cases hxd : x = d
      · subst x
        by_cases hq : q = []
        · exact reachableMinimal_no_dummyOpenClose_singleton
            hreach hminimal left right hturn (by simpa [hq] using hqueue)
            hko hdmem hd (Or.inl ⟨hleft, hright⟩)
        · exact reachableMinimal_no_dummyOpenClose_awaySingleton
            hreach hminimal left right hturn hqueue hq hko hdmem hd
            (Or.inl ⟨hleft, hright⟩)
      · have hxmem : x ∈ s.untouched := by
          simp only [step] at hstep₀
          split at hstep₀
          · assumption
          · contradiction
        by_cases hq : q = []
        · exact reachableMinimal_no_realOpenClose_singleton
            hreach hminimal left right hturn (by simpa [hq] using hqueue)
            hko hdmem hxmem hxd hd (Or.inl ⟨hleft, hright⟩)
        · exact reachableMinimal_no_realOpenClose_awaySingleton
            hreach hminimal left right hturn hqueue hq hko hdmem hxmem hxd hd
            (Or.inl ⟨hleft, hright⟩)
  · by_cases hopen₀ : ∃ y, m₀ = .open y
    · obtain ⟨y, rfl⟩ := hopen₀
      have hymem : y ∈ s.untouched := by
        simp only [step] at hstep₀
        split at hstep₀
        · assumption
        · contradiction
      have hxmem : x ∈ s.untouched := by
        simp only [step] at hstep₁
        split at hstep₁
        · assumption
        · contradiction
      by_cases hyd : y = d
      · subst y
        have hxd : x ≠ d := by
          intro hxd
          subst x
          exact hne rfl
        exact reachableMinimal_no_dummyRealOpenFork
          hreach hminimal left right hturn hdmem hxmem hxd hd
          (Or.inl ⟨hleft, hright⟩)
      · by_cases hxd : x = d
        · subst x
          exact reachableMinimal_no_dummyRealOpenFork
            hreach hminimal left right hturn hdmem hymem hyd hd
            (Or.inr ⟨hleft, hright⟩)
        · exact reachableMinimal_no_twoRealOpenFork
            hreach hminimal left right hturn hleft hright
            (by simpa using hne) hdmem hyd hxd hd
    · have hm₀ : m₀ = .close :=
        open_and_nonopen_legal_forces_close hdmem hstep₀ hopen₀
      subst m₀
      obtain ⟨f, q, hqueue, _⟩ := close_removes_front hstep₀
      have hko : s.ko = false := by
        cases hk : s.ko with
        | false => rfl
        | true => simp [step, hqueue, hk] at hstep₀
      by_cases hxd : x = d
      · subst x
        by_cases hq : q = []
        · exact reachableMinimal_no_dummyOpenClose_singleton
            hreach hminimal left right hturn (by simpa [hq] using hqueue)
            hko hdmem hd (Or.inr ⟨hleft, hright⟩)
        · exact reachableMinimal_no_dummyOpenClose_awaySingleton
            hreach hminimal left right hturn hqueue hq hko hdmem hd
            (Or.inr ⟨hleft, hright⟩)
      · have hxmem : x ∈ s.untouched := by
          simp only [step] at hstep₁
          split at hstep₁
          · assumption
          · contradiction
        by_cases hq : q = []
        · exact reachableMinimal_no_realOpenClose_singleton
            hreach hminimal left right hturn (by simpa [hq] using hqueue)
            hko hdmem hxmem hxd hd (Or.inr ⟨hleft, hright⟩)
        · exact reachableMinimal_no_realOpenClose_awaySingleton
            hreach hminimal left right hturn hqueue hq hko hdmem hxmem hxd hd
            (Or.inr ⟨hleft, hright⟩)

omit [Fintype V] in
/-- Root-level form: if a controlled isolated-dummy root exists, every
reachable controlled state of minimum rank has already consumed the dummy. -/
theorem controlled_isolated_root_rankMinimum_consumes_dummy
    (G : SimpleGraph V) (root : State V) (d : V)
    (hd : IsDummy G d)
    (hroot : MoverControlled G root ∨ NonmoverControlled G root) :
    ∃ s, ReachableFrom G root s ∧
      (MoverControlled G s ∨ NonmoverControlled G s) ∧
      d ∉ s.untouched ∧
      ∀ t, ReachableFrom G root t → rank t < rank s →
        ¬MoverControlled G t ∧ ¬NonmoverControlled G t := by
  obtain ⟨s, hreach, hcontrolled, hminimal⟩ :=
    exists_rankMinimal_controlled G (ReachableFrom G root)
      ⟨root, reachableFrom_root G root, hroot⟩
  exact ⟨s, hreach, hcontrolled,
    reachableMinimal_controlled_dummy_not_untouched
      hreach hminimal hcontrolled hd,
    hminimal⟩

end

end Ogdoad.Fifo
