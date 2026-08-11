import Ogdoad.Fifo

/-!
# Checked normalization lemmas toward the complete FIFO theorem

This file isolates formal bridges which are useful in any normalization proof
from an arbitrary odd strategy to a CLOSE-first one:

* a graph-independent live-star vector whose evaluation gives the scalar
  queue-cut potential increment of an OPEN;
* the already checked stopped empty-root theorem and conditioned tail theorem
  together rule out a CLOSE-first odd strategy from the initial root, for
  either attacker seat;
* every hypothetical odd strategy at that root therefore contains a genuine
  clear-node OPEN deviation; and
* an isolated dummy and the handshaking parity of same-degree mates give the
  checked first-spoiler step of the least-root odd corridor.

The CLOSE-first result is the scalar, kernel-checked form of the paper's
complete both-seat contraction.  The corridor stops at the even real fan
created when the selected OPEN touches the dummy.  It therefore does not
normalize an arbitrary attacker strategy; the global ancestry problem remains
explicit.
-/

namespace Ogdoad.Fifo

open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- If a finite current board contains an isolated dummy and has at least one
vertex besides `v`, one can remove a second vertex `w` so that `v` has even
degree in the twice-punctured board.

If the once-punctured degree of `v` is even, use the dummy.  If it is odd,
some actual neighbour occurs in the defining parity sum, and removing that
neighbour toggles the degree to zero. -/
theorem exists_second_open_making_front_even
    {G : SimpleGraph V} {S : Finset V} {d v : V}
    (hd : IsDummy G d) (hdS : d ∈ S) (hvS : v ∈ S)
    (hrest : (S.erase v).Nonempty) :
    ∃ w ∈ S.erase v, flip G ((S.erase v).erase w) v = 0 := by
  classical
  by_cases hvd : v = d
  · subst v
    obtain ⟨w, hw⟩ := hrest
    exact ⟨w, hw, flip_dummy hd _⟩
  by_cases heven : flip G (S.erase v) v = 0
  · have hdmem : d ∈ S.erase v := Finset.mem_erase.mpr ⟨Ne.symm hvd, hdS⟩
    refine ⟨d, hdmem, ?_⟩
    rw [flip_erase_eq_add hdmem, heven]
    have hnotadj : ¬G.Adj v d := by
      simpa [G.adj_comm] using hd v
    simp [adjacencyBit, hnotadj]
  · have hodd : flip G (S.erase v) v = 1 :=
      zmod2_eq_one_of_ne_zero _ heven
    have hvalue :
        closureValue (adjacencyBit G v) (S.erase v) = 1 := by
      simpa [closureValue] using
        (flip_eq_sum_adjacencyBit G (S.erase v) v).symm.trans hodd
    obtain ⟨w, hw, hbit⟩ :=
      exists_weight_one_of_closureValue_eq_one (adjacencyBit G v) hvalue
    refine ⟨w, hw, ?_⟩
    rw [flip_erase_eq_add hw, hodd, hbit]
    exact CharTwo.add_self_eq_zero 1

omit [Fintype V] in
/-- On an even finite board, after any first opening `x` there is a second
opening `y` which makes the first queued CLOSE have charge zero.  For odd
degree choose a neighbour; for even degree the odd once-punctured board
cannot consist entirely of neighbours. -/
theorem exists_second_open_making_front_even_of_even_card
    {G : SimpleGraph V} {S : Finset V} {x : V}
    (hx : x ∈ S) (hcard : (S.card : ZMod 2) = 0) :
    ∃ y ∈ S.erase x, flip G ((S.erase x).erase y) x = 0 := by
  classical
  have heraseCard : ((S.erase x).card : ZMod 2) = 1 := by
    have hnat := Finset.card_erase_add_one hx
    have hcast := congrArg (fun n : Nat ↦ (n : ZMod 2)) hnat
    simp only [Nat.cast_add, Nat.cast_one] at hcast
    rw [hcard] at hcast
    calc
      ((S.erase x).card : ZMod 2) =
          (((S.erase x).card : ZMod 2) + 1) + 1 := by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = 0 + 1 := by rw [hcast]
      _ = 1 := by simp
  by_cases hp : flip G (S.erase x) x = 0
  · have hzero : ∃ y ∈ S.erase x, adjacencyBit G x y = 0 := by
      by_contra hnone
      push Not at hnone
      have hall : ∀ y ∈ S.erase x, adjacencyBit G x y = 1 := by
        intro y hy
        exact zmod2_eq_one_of_ne_zero _ (hnone y hy)
      have hone : flip G (S.erase x) x = 1 := by
        rw [flip_eq_sum_adjacencyBit]
        calc
          (∑ y ∈ S.erase x, adjacencyBit G x y) =
              ∑ _y ∈ S.erase x, (1 : ZMod 2) := by
                apply Finset.sum_congr rfl
                intro y hy
                exact hall y hy
          _ = 1 := by simpa using heraseCard
      exact one_ne_zero (hone.symm.trans hp)
    obtain ⟨y, hy, hbit⟩ := hzero
    refine ⟨y, hy, ?_⟩
    rw [flip_erase_eq_add hy, hp, hbit, add_zero]
  · have hp1 : flip G (S.erase x) x = 1 :=
      zmod2_eq_one_of_ne_zero _ hp
    have hvalue :
        closureValue (adjacencyBit G x) (S.erase x) = 1 := by
      simpa [closureValue] using
        (flip_eq_sum_adjacencyBit G (S.erase x) x).symm.trans hp1
    obtain ⟨y, hy, hbit⟩ :=
      exists_weight_one_of_closureValue_eq_one (adjacencyBit G x) hvalue
    refine ⟨y, hy, ?_⟩
    rw [flip_erase_eq_add hy, hp1, hbit]
    exact CharTwo.add_self_eq_zero 1

/-! ## Scalar and vector live-star interface -/

/-- The public live vertex set: untouched vertices together with the queued
vertices which have opened but not yet closed. -/
def liveSet (s : State V) : Finset V :=
  s.untouched ∪ s.queue.toFinset

/-- Scalar value of the star of `v` in the current live graph.  The list form
of the queue term remains correct without a separate nodup hypothesis; on a
well-formed reachable state it is exactly the induced live degree. -/
def liveDegree (G : SimpleGraph V) (s : State V) (v : V) : ZMod 2 :=
  flip G s.untouched v + queueCut G {v} s.queue

omit [Fintype V] in
/-- Deleting one untouched vertex changes the whole queue cut by its queue
star. -/
theorem queueCut_erase_eq_add
    {G : SimpleGraph V} {U : Finset V} {q : List V} {v : V} (hv : v ∈ U) :
    queueCut G (U.erase v) q = queueCut G U q + queueCut G {v} q := by
  induction q with
  | nil => simp [queueCut]
  | cons f q ih =>
      simp only [queueCut, List.map_cons, List.sum_cons] at ih ⊢
      rw [flip_erase_eq_add hv, flip_singleton_eq_adjacencyBit, ih]
      abel

omit [Fintype V] [DecidableEq V] in
/-- Appending one vertex to the queue appends its current cut charge. -/
theorem queueCut_append_singleton
    (G : SimpleGraph V) (U : Finset V) (q : List V) (v : V) :
    queueCut G U (q ++ [v]) = queueCut G U q + flip G U v := by
  simp [queueCut]

omit [Fintype V] in
/-- OPEN is the unique transition which changes `score + queueCut`; it adds
the scalar star (live degree) of the opened vertex. -/
theorem open_adds_liveDegree_to_potential
    {G : SimpleGraph V} {s s' : State V} {v : V}
    (hstep : step G s (.open v) = some s') :
    potential G s' = potential G s + liveDegree G s v := by
  simp only [step] at hstep
  split at hstep
  · rename_i hv
    cases hstep
    rw [potential, potential, liveDegree, queueCut_append_singleton,
      queueCut_erase_eq_add hv, flip_erase_eq_add hv, adjacencyBit_self]
    abel
  · contradiction

omit [Fintype V] in
/-- Unified scalar potential transition law.  CLOSE and PASS conserve the
potential; OPEN adds the live vertex degree. -/
theorem step_potential_eq_add_liveDegree
    {G : SimpleGraph V} {s s' : State V} {m : Move V}
    (hstep : step G s m = some s') :
    potential G s' = potential G s +
      match m with
      | .open v => liveDegree G s v
      | .close => 0
      | .pass => 0 := by
  cases m with
  | «open» v => exact open_adds_liveDegree_to_potential hstep
  | close => simpa using close_conserves_potential hstep
  | pass => simpa using pass_conserves_potential hstep

omit [Fintype V] in
/-- On a nodup queue, its scalar singleton cut is the degree of `v` into the
queued vertex finset. -/
theorem queueCut_singleton_eq_flip_toFinset
    (G : SimpleGraph V) (v : V) :
    ∀ {q : List V}, q.Nodup → queueCut G {v} q = flip G q.toFinset v := by
  intro q hq
  induction q with
  | nil => simp [queueCut]
  | cons f q ih =>
      obtain ⟨hf, hq⟩ := List.nodup_cons.mp hq
      simp only [queueCut, List.map_cons, List.sum_cons, List.toFinset_cons]
      change flip G {v} f + queueCut G {v} q =
        flip G (insert f q.toFinset) v
      rw [ih hq, flip_insert_of_not_mem (by simpa using hf),
        flip_singleton_eq_adjacencyBit, adjacencyBit_comm]
      abel

omit [Fintype V] in
/-- Scalar stars really are induced live degrees on reachable states. -/
theorem liveDegree_eq_flip_liveSet
    {G : SimpleGraph V} {s : State V} {v : V} (hs : WellFormed s) :
    liveDegree G s v = flip G (liveSet s) v := by
  rcases hs with ⟨hnodup, hdisjoint⟩
  rw [liveDegree, queueCut_singleton_eq_flip_toFinset G v hnodup,
    liveSet, flip_eq_sum_adjacencyBit, flip_eq_sum_adjacencyBit,
    flip_eq_sum_adjacencyBit, Finset.sum_union hdisjoint]

/-- Universal binary edge space used by the vector live-star identity. -/
abbrev EdgeVector (V : Type*) := Sym2 V →₀ ZMod 2

/-- The complete-graph star of `v` on a finite live set, as a vector of
unordered edge coordinates.  The diagonal is explicitly excluded. -/
def liveStarVector (L : Finset V) (v : V) : EdgeVector V :=
  ∑ w ∈ L.erase v, Finsupp.single s(v, w) 1

/-- Evaluation of a universal edge vector on one simple graph. -/
noncomputable def graphEvaluation (G : SimpleGraph V) : EdgeVector V →+ ZMod 2 := by
  classical
  exact Finsupp.liftAddHom fun e =>
    if e ∈ G.edgeSet then AddMonoidHom.id (ZMod 2) else 0

omit [Fintype V] [DecidableEq V] in
@[simp] theorem graphEvaluation_single
    (G : SimpleGraph V) (x y : V) (c : ZMod 2) :
    graphEvaluation G (Finsupp.single s(x, y) c) =
      adjacencyBit G x y * c := by
  classical
  by_cases hxy : G.Adj x y
  · simp [graphEvaluation, SimpleGraph.mem_edgeSet, adjacencyBit, hxy]
  · simp [graphEvaluation, SimpleGraph.mem_edgeSet, adjacencyBit, hxy]

omit [Fintype V] in
/-- Every graph functional evaluates the universal live star to the
corresponding scalar degree. -/
theorem graphEvaluation_liveStarVector
    (G : SimpleGraph V) (L : Finset V) (v : V) :
    graphEvaluation G (liveStarVector L v) = flip G L v := by
  classical
  rw [liveStarVector, map_sum]
  simp only [graphEvaluation_single, mul_one]
  rw [flip_eq_sum_adjacencyBit]
  by_cases hv : v ∈ L
  · rw [← Finset.sum_erase_add _ _ hv]
    simp [adjacencyBit]
  · simp [Finset.erase_eq_self.mpr hv, adjacencyBit]

omit [Fintype V] in
/-- Vector-to-scalar bridge at a well-formed public state. -/
theorem graphEvaluation_liveStar_eq_liveDegree
    (G : SimpleGraph V) (s : State V) (v : V) (hs : WellFormed s) :
    graphEvaluation G (liveStarVector (liveSet s) v) = liveDegree G s v := by
  rw [graphEvaluation_liveStarVector, liveDegree_eq_flip_liveSet hs]

/-- Vector charge attached to one transition: an OPEN contributes its current
live star, while CLOSE and PASS contribute zero. -/
def moveLiveStar (s : State V) : Move V → EdgeVector V
  | .open v => liveStarVector (liveSet s) v
  | .close => 0
  | .pass => 0

omit [Fintype V] in
/-- Scalar evaluation of a move's universal star vector. -/
theorem graphEvaluation_moveLiveStar
    (G : SimpleGraph V) (s : State V) (m : Move V) (hs : WellFormed s) :
    graphEvaluation G (moveLiveStar s m) =
      match m with
      | .open v => liveDegree G s v
      | .close => 0
      | .pass => 0 := by
  cases m with
  | «open» v => exact graphEvaluation_liveStar_eq_liveDegree G s v hs
  | close => simp [moveLiveStar]
  | pass => simp [moveLiveStar]

/-- A finite legal trace carrying the sum of its OPEN live stars.  The vector
is graph-independent at the level of public live sets; `G` enters only through
legality of the score-carrying states. -/
inductive LiveStarTrace (G : SimpleGraph V) :
    State V → State V → EdgeVector V → Prop
  | refl (s : State V) : LiveStarTrace G s s 0
  | cons {s s' t : State V} {m : Move V} {z : EdgeVector V}
      (hstep : step G s m = some s') (tail : LiveStarTrace G s' t z) :
      LiveStarTrace G s t (moveLiveStar s m + z)

omit [Fintype V] in
/-- Telescoped potential law along an arbitrary finite trace. -/
theorem LiveStarTrace.potential_eq_add_evaluation
    {G : SimpleGraph V} {s t : State V} {z : EdgeVector V}
    (htrace : LiveStarTrace G s t z) (hs : WellFormed s) :
    potential G t = potential G s + graphEvaluation G z := by
  induction htrace with
  | refl s => simp
  | @cons s s' t m z hstep tail ih =>
      have hs' : WellFormed s' := wellFormed_step hs hstep
      have htail := ih hs'
      have hhead := step_potential_eq_add_liveDegree hstep
      have heval := graphEvaluation_moveLiveStar G s m hs
      calc
        potential G t = potential G s' + graphEvaluation G z := htail
        _ = potential G s + graphEvaluation G (moveLiveStar s m + z) := by
          rw [hhead, map_add, heval]
          cases m with
          | «open» v => simp; abel
          | close => simp
          | pass => simp

/-- Scalar live-degree identity for a complete history, packaged through its
universal vector star sum. -/
theorem LiveStarTrace.terminal_score_eq_graphEvaluation
    {G : SimpleGraph V} {t : State V} {z : EdgeVector V}
    (htrace : LiveStarTrace G (initial (V := V)) t z) (ht : Terminal t) :
    t.score = graphEvaluation G z := by
  have hpot := htrace.potential_eq_add_evaluation wellFormed_initial
  rw [terminal_potential ht] at hpot
  simpa [potential, initial, queueCut] using hpot

omit [Fintype V] in
/-- A terminal-score-one CLOSE-first strategy is also a stopped CLOSE-first
strategy: simply never use the extra STOP constructor. -/
theorem CloseFirstWins.toStoppedOne
    {G : SimpleGraph V} {attacker : Bool} {s : State V}
    (h : CloseFirstWins G attacker 1 s) :
    StoppedCloseFirstWins G attacker s := by
  induction h with
  | terminal s hterminal hscore =>
      exact StoppedCloseFirstWins.terminal s hterminal (by
        rw [hscore]
        exact one_ne_zero)
  | choose s hattacker m s' hstep priority _ ih =>
      refine StoppedCloseFirstWins.choose s hattacker m s' hstep ?_ ih
      intro hclear
      apply priority
      rcases hclear with ⟨hqueue, hko⟩
      cases hq : s.queue with
      | nil => exact False.elim (hqueue hq)
      | cons f q =>
          let sc : State V := {
            untouched := s.untouched
            queue := q
            ko := false
            toMove := !s.toMove
            score := s.score + flip G s.untouched f }
          exact ⟨sc, by simp [step, hq, hko, sc]⟩
  | answer s hdefender hasMove _ ih =>
      exact StoppedCloseFirstWins.answer s hdefender hasMove ih

/-- Complete scalar CLOSE-first contraction from the isolated-dummy initial
root, for either attacker seat.

When the attacker moves second, `stoppedCloseFirstEmptyRootTheorem` is already
strictly stronger.  When the attacker moves first and opens `v`, the defender
uses `exists_second_open_making_front_even`; CLOSE-first play then removes `v`
at charge zero and reaches a clear defender checkpoint excluded by
`ConditionedCloseFirstTheorem`. -/
theorem no_closeFirstOddStrategy_initial
    (G : SimpleGraph V) (d : V) (hd : IsDummy G d) (attacker : Bool) :
    ¬CloseFirstWins G attacker 1 (initial (V := V)) := by
  cases attacker with
  | true =>
      intro hwin
      have hsafe : StoppedEmptyRootSafe G Finset.univ true :=
        stoppedCloseFirstEmptyRootTheorem V inferInstance inferInstance
          G true Finset.univ
      apply hsafe
      simpa [StoppedEmptyRootSafe, stoppedEmptyRoot, initial] using
        hwin.toStoppedOne
  | false =>
      intro hwin
      cases hwin with
      | terminal _ hterminal _ =>
          have hduniv : d ∈ (Finset.univ : Finset V) := Finset.mem_univ d
          rw [Terminal, initial] at hterminal
          have : d ∈ (∅ : Finset V) := by
            rw [← hterminal.1]
            exact hduniv
          simp at this
      | answer _ hdefender _ _ =>
          exact hdefender rfl
      | choose _ _ m child hstep _ hchild =>
          cases m with
          | close => simp [step, initial] at hstep
          | pass => simp [step, initial] at hstep
          | «open» v =>
              let sv : State V := {
                untouched := Finset.univ.erase v
                queue := [v]
                ko := true
                toMove := true
                score := 0 }
              have hopenv : step G (initial (V := V)) (.open v) = some sv := by
                simp [step, initial, sv]
              have hchildEq : child = sv := by
                rw [hopenv] at hstep
                exact Option.some.inj hstep.symm
              subst child
              by_cases hrest : (Finset.univ.erase v).Nonempty
              · obtain ⟨w, hw, hfront⟩ :=
                  exists_second_open_making_front_even
                    hd (Finset.mem_univ d) (Finset.mem_univ v) hrest
                let svw : State V := {
                  untouched := (Finset.univ.erase v).erase w
                  queue := [v, w]
                  ko := false
                  toMove := false
                  score := 0 }
                have hopenw : step G sv (.open w) = some svw := by
                  simp [step, sv, svw, hw]
                have hpair : CloseFirstWins G false 1 svw :=
                  hchild.answer_child (by simp [sv]) hopenw
                let sc : State V := {
                  untouched := (Finset.univ.erase v).erase w
                  queue := [w]
                  ko := false
                  toMove := true
                  score := 0 }
                have hclose : step G svw .close = some sc := by
                  simp [step, svw, sc, hfront]
                have hsctree : CloseFirstWins G false 1 sc :=
                  hpair.close_child rfl hclose
                have hcoherent : Coherent sc := by
                  exact coherent_step
                    (coherent_step
                      (coherent_step coherent_initial hopenv) hopenw) hclose
                exact ConditionedCloseFirstTheorem V inferInstance inferInstance
                  G false sc hcoherent (by simp [sc]) (by simp [sc]) rfl (by
                    simpa [sc] using hsctree)
              · have hempty : Finset.univ.erase v = ∅ :=
                  Finset.not_nonempty_iff_eq_empty.mp hrest
                have hnext := not_closeFirstWins_next_of_untouched_empty
                  (G := G) (attacker := false) (s := sv) (by simpa [sv] using hempty)
                exact hnext (by simpa [sv] using hchild)

/-! ## Exact strategy-level normalization frontier

The following proof-indexed predicates distinguish a genuinely CLOSE-first
odd strategy from one which contains a clear-node deviation.  This keeps the
quantifiers inside one explicit `OddWins` tree; it does not replace the tree
by a positional state predicate.
-/

/-- Every attacker-controlled clear node in this particular odd strategy
selects FIFO CLOSE. -/
inductive OddStrategyCloseFirst {G : SimpleGraph V} {seat : Bool} :
    {s : State V} → OddWins G seat s → Prop
  | terminal (s : State V) (hterminal : Terminal s) (hscore : s.score ≠ 0) :
      OddStrategyCloseFirst (OddWins.terminal s hterminal hscore)
  | choose (s : State V) (hseat : s.toMove ≠ seat)
      (m : Move V) (s' : State V) (hstep : step G s m = some s')
      (hchild : OddWins G seat s')
      (priority : Clear s → m = .close)
      (tail : OddStrategyCloseFirst hchild) :
      OddStrategyCloseFirst (OddWins.choose s hseat m s' hstep hchild)
  | answer (s : State V) (hseat : s.toMove = seat)
      (hasMove : ∃ m s', step G s m = some s')
      (hchildren : ∀ m s', step G s m = some s' → OddWins G seat s')
      (tails : ∀ m s' (hstep : step G s m = some s'),
        OddStrategyCloseFirst (hchildren m s' hstep)) :
      OddStrategyCloseFirst (OddWins.answer s hseat hasMove hchildren)

/-- A witness that this particular odd strategy selects a non-CLOSE move at
some attacker-controlled clear node. -/
inductive OddStrategyHasClearDeviation {G : SimpleGraph V} {seat : Bool} :
    {s : State V} → OddWins G seat s → Prop
  | here (s : State V) (hseat : s.toMove ≠ seat)
      (m : Move V) (s' : State V) (hstep : step G s m = some s')
      (hchild : OddWins G seat s') (hclear : Clear s) (hm : m ≠ .close) :
      OddStrategyHasClearDeviation
        (OddWins.choose s hseat m s' hstep hchild)
  | choose {s s' : State V} {hseat : s.toMove ≠ seat}
      {m : Move V} {hstep : step G s m = some s'}
      {hchild : OddWins G seat s'}
      (tail : OddStrategyHasClearDeviation hchild) :
      OddStrategyHasClearDeviation
        (OddWins.choose s hseat m s' hstep hchild)
  | answer {s s' : State V} {hseat : s.toMove = seat}
      {hasMove : ∃ m u, step G s m = some u}
      {hchildren : ∀ m u, step G s m = some u → OddWins G seat u}
      {m : Move V} {hstep : step G s m = some s'}
      (tail : OddStrategyHasClearDeviation (hchildren m s' hstep)) :
      OddStrategyHasClearDeviation
        (OddWins.answer s hseat hasMove hchildren)

omit [Fintype V] in
/-- Forgetting the proof-indexed CLOSE-first certificate produces the existing
absolute-target CLOSE-first strategy tree for the physical odd player. -/
theorem OddStrategyCloseFirst.toCloseFirstWins
    {G : SimpleGraph V} {seat : Bool} {s : State V} {h : OddWins G seat s}
    (hcf : OddStrategyCloseFirst h) :
    CloseFirstWins G (!seat) 1 s := by
  induction hcf with
  | terminal s hterminal hscore =>
      exact CloseFirstWins.terminal s hterminal
        (zmod2_eq_one_of_ne_zero s.score hscore)
  | choose s hseat m s' hstep hchild priority _ ih =>
      refine CloseFirstWins.choose s (Bool.eq_not_iff.mpr hseat)
        m s' hstep ?_ ih
      rintro ⟨sc, hclose⟩
      apply priority
      simp only [Clear]
      simp only [step] at hclose
      split at hclose
      · contradiction
      · rename_i f q hq
        split at hclose
        · contradiction
        · exact ⟨by simp [hq], by cases hk : s.ko <;> simp_all⟩
  | answer s hseat hasMove hchildren _ ih =>
      refine CloseFirstWins.answer s ?_ hasMove ?_
      · simp [hseat]
      · intro m s' hstep
        exact ih m s' hstep

omit [Fintype V] in
/-- Structural dichotomy for one explicit odd strategy tree. -/
theorem oddStrategy_deviation_or_closeFirst
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (h : OddWins G seat s) :
    OddStrategyHasClearDeviation h ∨ OddStrategyCloseFirst h := by
  classical
  induction h with
  | terminal s hterminal hscore =>
      exact Or.inr (OddStrategyCloseFirst.terminal s hterminal hscore)
  | choose s hseat m s' hstep hchild ih =>
      by_cases hclear : Clear s
      · by_cases hm : m = .close
        · rcases ih with hdev | hcf
          · exact Or.inl (OddStrategyHasClearDeviation.choose
              (hseat := hseat) (m := m) (hstep := hstep) hdev)
          · exact Or.inr (OddStrategyCloseFirst.choose s hseat m s' hstep
              hchild (fun _ ↦ hm) hcf)
        · exact Or.inl (OddStrategyHasClearDeviation.here
            s hseat m s' hstep hchild hclear hm)
      · rcases ih with hdev | hcf
        · exact Or.inl (OddStrategyHasClearDeviation.choose
            (hseat := hseat) (m := m) (hstep := hstep) hdev)
        · exact Or.inr (OddStrategyCloseFirst.choose s hseat m s' hstep
            hchild (fun hc ↦ False.elim (hclear hc)) hcf)
  | answer s hseat hasMove hchildren ih =>
      by_cases hdev : ∃ (m : Move V) (s' : State V)
          (hstep : step G s m = some s'),
          OddStrategyHasClearDeviation (hchildren m s' hstep)
      · obtain ⟨m, s', hstep, htail⟩ := hdev
        exact Or.inl (OddStrategyHasClearDeviation.answer
          (hseat := hseat) (hasMove := hasMove) (hstep := hstep) htail)
      · refine Or.inr (OddStrategyCloseFirst.answer
          s hseat hasMove hchildren ?_)
        intro m s' hstep
        rcases ih m s' hstep with htail | htail
        · exact False.elim (hdev ⟨m, s', hstep, htail⟩)
        · exact htail

/-- Therefore every hypothetical odd counterstrategy on an isolated-dummy
initial board contains a genuine clear-node deviation.  The complete FIFO
theorem is reduced to eliminating a leafmost such deviation using its full
defender ancestry fan; local conditioned-state normalization is false. -/
theorem oddStrategy_initial_has_clearDeviation
    (G : SimpleGraph V) (d : V) (hd : IsDummy G d) (seat : Bool)
    (h : OddWins G seat (initial (V := V))) :
    OddStrategyHasClearDeviation h := by
  rcases oddStrategy_deviation_or_closeFirst h with hdev | hcf
  · exact hdev
  · exact False.elim
      (no_closeFirstOddStrategy_initial G d hd (!seat) hcf.toCloseFirstWins)

/-! ## Balanced-front contraction and the marked-dummy tail

This is the exact local implication used in the least-root odd corridor.  A
two-coin front whose two remaining degrees agree can be deleted by two FIFO
CLOSE moves without changing the score or the mover.  Consequently, if the
smaller empty-root state is already even-winning, an odd strategy at the pair
checkpoint cannot select CLOSE; PASS is illegal there, so its selected move
must be OPEN.  The final corollary records the precise dummy dichotomy: that
OPEN either consumes the marked dummy or leaves it untouched for the next
inductive checkpoint.

The smaller-root `EvenWins` hypothesis is intentionally explicit.  Removing
it would be exactly the still-open arbitrary-graph linking theorem, rather
than a local corridor lemma.
-/

/-- Clear checkpoint with ordered FIFO front `(x,y)`. -/
def balancedFrontState (U : Finset V) (x y : V) (attacker : Bool)
    (score : ZMod 2) : State V where
  untouched := U
  queue := [x, y]
  ko := false
  toMove := attacker
  score := score

/-- State after the first CLOSE at a balanced two-coin front. -/
def balancedFrontTailState (G : SimpleGraph V) (U : Finset V)
    (x y : V) (attacker : Bool) (score : ZMod 2) : State V where
  untouched := U
  queue := [y]
  ko := false
  toMove := !attacker
  score := score + flip G U x

/-- The smaller empty-root state reached after deleting the balanced front. -/
def balancedFrontResidualState (U : Finset V) (attacker : Bool)
    (score : ZMod 2) : State V where
  untouched := U
  queue := []
  ko := false
  toMove := attacker
  score := score

/-- Vertices of one induced-degree parity in a finite real board. -/
def degreeParityClass (G : SimpleGraph V) (R : Finset V) (a : ZMod 2) :
    Finset V :=
  R.filter fun v ↦ flip G R v = a

/-- The possible second fronts having the same real-board degree parity as
the fixed first front. -/
def sameDegreeMates (G : SimpleGraph V) (R : Finset V) (x : V) : Finset V :=
  (R.erase x).filter fun y ↦ flip G R y = flip G R x

omit [Fintype V] in
/-- Handshaking plus even total order makes both induced-degree parity
classes even.  The formulation is uniform in the requested bit `a`. -/
theorem degreeParityClass_card_eq_zero
    (G : SimpleGraph V) (R : Finset V) (a : ZMod 2)
    (hR : (R.card : ZMod 2) = 0) :
    ((degreeParityClass G R a).card : ZMod 2) = 0 := by
  classical
  rw [degreeParityClass, Finset.natCast_card_filter]
  by_cases ha : a = 0
  · subst a
    calc
      (∑ v ∈ R, if flip G R v = 0 then (1 : ZMod 2) else 0) =
          ∑ v ∈ R, (1 + flip G R v) := by
            apply Finset.sum_congr rfl
            intro v hv
            by_cases hz : flip G R v = 0
            · simp [hz]
            · have ho := zmod2_eq_one_of_ne_zero (flip G R v) hz
              simp only [ho]
              exact (CharTwo.add_self_eq_zero 1).symm
      _ = (∑ _v ∈ R, (1 : ZMod 2)) + ∑ v ∈ R, flip G R v := by
            rw [Finset.sum_add_distrib]
      _ = 0 := by rw [sum_flip_self_eq_zero G R]; simpa using hR
  · have ha1 : a = 1 := zmod2_eq_one_of_ne_zero a ha
    subst a
    calc
      (∑ v ∈ R, if flip G R v = 1 then (1 : ZMod 2) else 0) =
          ∑ v ∈ R, flip G R v := by
            apply Finset.sum_congr rfl
            intro v hv
            by_cases ho : flip G R v = 1
            · simp [ho]
            · have hz := zmod2_eq_zero_of_ne_one (flip G R v) ho
              simp [hz]
      _ = 0 := sum_flip_self_eq_zero G R

omit [Fintype V] in
/-- Exact parity statement behind the outer least-root corridor: on an even
real board, every fixed real opener has an odd number of distinct vertices
of the same degree parity. -/
theorem sameDegreeMates_card_eq_one
    (G : SimpleGraph V) (R : Finset V) (x : V) (hx : x ∈ R)
    (hR : (R.card : ZMod 2) = 0) :
    ((sameDegreeMates G R x).card : ZMod 2) = 1 := by
  classical
  let C := degreeParityClass G R (flip G R x)
  have hxC : x ∈ C := by simp [C, degreeParityClass, hx]
  have hC : (C.card : ZMod 2) = 0 :=
    degreeParityClass_card_eq_zero G R (flip G R x) hR
  have hErase : C.erase x = sameDegreeMates G R x := by
    ext y
    simp [C, degreeParityClass, sameDegreeMates, and_assoc]
  have hcard := Finset.card_erase_add_one hxC
  have hcast := congrArg (fun n : Nat ↦ (n : ZMod 2)) hcard
  simp only [Nat.cast_add, Nat.cast_one] at hcast
  rw [hC] at hcast
  have hodd : ((C.erase x).card : ZMod 2) = 1 := by
    calc
      ((C.erase x).card : ZMod 2) =
          (((C.erase x).card : ZMod 2) + 1) + 1 := by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = 0 + 1 := by rw [hcast]
      _ = 1 := by simp
  rwa [hErase] at hodd

omit [Fintype V] in
/-- Membership in the full-board same-degree class is exactly the balance
needed after deleting the two prospective fronts. -/
theorem sameDegreeMate_balances_residual
    (G : SimpleGraph V) (R : Finset V) (x y : V) (hx : x ∈ R)
    (hyMate : y ∈ sameDegreeMates G R x) :
    flip G ((R.erase x).erase y) x =
      flip G ((R.erase x).erase y) y := by
  classical
  have hyErase : y ∈ R.erase x :=
    (Finset.mem_filter.mp hyMate).1
  have hy : y ∈ R := Finset.mem_of_mem_erase hyErase
  have hxy : x ≠ y := fun hxy ↦
    (Finset.ne_of_mem_erase hyErase) hxy.symm
  have hdeg : flip G R y = flip G R x :=
    (Finset.mem_filter.mp hyMate).2
  rw [flip_erase_erase_eq_add hx hy hxy,
    flip_erase_erase_eq_add hx hy hxy, hdeg]
  simp [adjacencyBit_self, adjacencyBit_comm]

omit [Fintype V] in
/-- Adding an isolated dummy to an untouched set does not change any live
degree. -/
theorem flip_insert_dummy
    {G : SimpleGraph V} {d : V} (hd : IsDummy G d) (U : Finset V) (v : V) :
    flip G (insert d U) v = flip G U v := by
  classical
  by_cases hdU : d ∈ U
  · rw [Finset.insert_eq_self.mpr hdU]
  · rw [flip_insert_of_not_mem hdU]
    have hnotadj : ¬G.Adj v d := by simpa [G.adj_comm] using hd v
    simp [adjacencyBit, hnotadj]

omit [Fintype V] in
/-- Root-form balance: deleting a same-degree real pair and retaining the
isolated dummy gives equal consecutive CLOSE charges. -/
theorem sameDegreeMate_balances_dummyResidual
    (G : SimpleGraph V) (R : Finset V) (d x y : V) (hd : IsDummy G d)
    (hx : x ∈ R) (hyMate : y ∈ sameDegreeMates G R x) :
    flip G (insert d ((R.erase x).erase y)) x =
      flip G (insert d ((R.erase x).erase y)) y := by
  rw [flip_insert_dummy hd, flip_insert_dummy hd]
  exact sameDegreeMate_balances_residual G R x y hx hyMate

omit [Fintype V] in
/-- Equal residual degrees make the two consecutive FIFO closes cancel
exactly, including score, phase, queue, and ko flag. -/
theorem balancedFront_close_close
    (G : SimpleGraph V) (U : Finset V) (x y : V) (attacker : Bool)
    (score : ZMod 2) (hbal : flip G U x = flip G U y) :
    step G (balancedFrontState U x y attacker score) .close =
        some (balancedFrontTailState G U x y attacker score) ∧
      step G (balancedFrontTailState G U x y attacker score) .close =
        some (balancedFrontResidualState U attacker score) := by
  constructor
  · simp [step, balancedFrontState, balancedFrontTailState]
  · simp [step, balancedFrontTailState, balancedFrontResidualState, hbal,
      add_assoc, CharTwo.add_self_eq_zero]

omit [Fintype V] in
/-- If the smaller root is even-winning, then after an odd player's first
CLOSE the even player answers with the second CLOSE and reaches that root. -/
theorem evenWins_balancedFrontTail
    (G : SimpleGraph V) (U : Finset V) (x y : V) (attacker : Bool)
    (score : ZMod 2) (hbal : flip G U x = flip G U y)
    (hres : EvenWins G (!attacker)
      (balancedFrontResidualState U attacker score)) :
    EvenWins G (!attacker)
      (balancedFrontTailState G U x y attacker score) := by
  exact EvenWins.choose
    (balancedFrontTailState G U x y attacker score)
    (by simp [balancedFrontTailState]) .close
    (balancedFrontResidualState U attacker score)
    (balancedFront_close_close G U x y attacker score hbal).2 hres

omit [Fintype V] in
/-- Balanced-front spoiler lemma.  Under the smaller-root induction
hypothesis, every explicit odd strategy at the pair checkpoint selects OPEN.
No finite enumeration or positional determinacy is used. -/
theorem oddWins_balancedFront_forces_open
    (G : SimpleGraph V) (U : Finset V) (x y : V) (attacker : Bool)
    (score : ZMod 2) (hbal : flip G U x = flip G U y)
    (hres : EvenWins G (!attacker)
      (balancedFrontResidualState U attacker score))
    (hodd : OddWins G (!attacker)
      (balancedFrontState U x y attacker score)) :
    ∃ v child,
      step G (balancedFrontState U x y attacker score) (.open v) =
          some child ∧
        OddWins G (!attacker) child := by
  cases hodd with
  | terminal _ hterminal _ =>
      simp [Terminal, balancedFrontState] at hterminal
  | answer _ hseat _ _ =>
      simp [balancedFrontState] at hseat
  | choose _ _ m child hstep hchild =>
      cases m with
      | close =>
          have hclose :=
            (balancedFront_close_close G U x y attacker score hbal).1
          rw [hclose] at hstep
          cases hstep
          exact False.elim
            ((evenWins_balancedFrontTail G U x y attacker score hbal hres).not_oddWins
              hchild)
      | pass =>
          simp [step, balancedFrontState] at hstep
      | «open» v =>
          exact ⟨v, child, hstep, hchild⟩

omit [Fintype V] in
/-- Marked-dummy endpoint of the balanced-front corridor.  The forced OPEN
either opens the marked dummy itself or preserves it in the untouched set.
Isolation is not needed for this local persistence statement; it enters when
the resulting endpoint is identified as another isolated-dummy root. -/
theorem oddWins_balancedFront_dummyTail
    (G : SimpleGraph V) (U : Finset V) (d x y : V) (attacker : Bool)
    (score : ZMod 2) (hdU : d ∈ U)
    (hbal : flip G U x = flip G U y)
    (hres : EvenWins G (!attacker)
      (balancedFrontResidualState U attacker score))
    (hodd : OddWins G (!attacker)
      (balancedFrontState U x y attacker score)) :
    ∃ v child,
      step G (balancedFrontState U x y attacker score) (.open v) =
          some child ∧
        OddWins G (!attacker) child ∧
        (v = d ∨ d ∈ child.untouched) := by
  obtain ⟨v, child, hstep, hchild⟩ :=
    oddWins_balancedFront_forces_open G U x y attacker score hbal hres hodd
  refine ⟨v, child, hstep, hchild, ?_⟩
  by_cases hvd : v = d
  · exact Or.inl hvd
  · right
    have hvU : v ∈ U := by
      by_contra hvU
      simp [step, balancedFrontState, hvU] at hstep
    have hdErase : d ∈ U.erase v :=
      Finset.mem_erase.mpr ⟨Ne.symm hvd, hdU⟩
    have hUeq : U.erase v = child.untouched := by
      simpa [step, balancedFrontState, hvU] using
        congrArg (fun s? ↦ Option.map State.untouched s?) hstep
    rw [← hUeq]
    exact hdErase

omit [Fintype V] in
/-- Root-corridor corollary in the paper's variables.  Picking `y` from the
odd same-degree mate class makes the queued pair balanced on the residual
real board plus dummy.  If that smaller isolated-dummy root is even-winning,
the odd spoiler must OPEN; it either opens `d` or leaves `d` untouched. -/
theorem oddWins_sameDegreeMate_dummyRoot_forces_open
    (G : SimpleGraph V) (R : Finset V) (d x y : V) (attacker : Bool)
    (score : ZMod 2) (hd : IsDummy G d) (hx : x ∈ R)
    (hyMate : y ∈ sameDegreeMates G R x)
    (hres : EvenWins G (!attacker)
      (balancedFrontResidualState
        (insert d ((R.erase x).erase y)) attacker score))
    (hodd : OddWins G (!attacker)
      (balancedFrontState (insert d ((R.erase x).erase y))
        x y attacker score)) :
    ∃ v child,
      step G (balancedFrontState (insert d ((R.erase x).erase y))
          x y attacker score) (.open v) = some child ∧
        OddWins G (!attacker) child ∧
        (v = d ∨ d ∈ child.untouched) := by
  apply oddWins_balancedFront_dummyTail G
    (insert d ((R.erase x).erase y)) d x y attacker score
  · simp
  · exact sameDegreeMate_balances_dummyResidual G R d x y hd hx hyMate
  · exact hres
  · exact hodd

/-! ## Rank-minimal hot states

The following four-valued minimax interface forgets a fixed target strategy
and instead asks what either physical player can force from one state.  A
state is `Hot` for a player when that player can force either terminal score.
A state is `ColdAtOwnScore` when both physical players can force preservation
of the score already accumulated at that state.

This distinction makes the minimum-flexibility argument precise.  Below a
rank-minimal hot state, a charge-changing edge would itself give the mover
both targets: use that edge for the new score, or OPEN an untouched vertex for
the old score.  Hence every lower edge is neutral and every lower state is
cold at its own score. -/

/-- A physical player can force the score already accumulated at `s`. -/
def WinsCurrentScore (G : SimpleGraph V) (player : Bool) (s : State V) : Prop :=
  if s.score = 0 then EvenWins G player s else OddWins G (!player) s

/-- Both physical players can force preservation of the current score. -/
def ColdAtOwnScore (G : SimpleGraph V) (s : State V) : Prop :=
  ∀ player, WinsCurrentScore G player s

/-- One physical player can force both possible terminal scores. -/
def Hot (G : SimpleGraph V) (player : Bool) (s : State V) : Prop :=
  EvenWins G player s ∧ OddWins G (!player) s

omit [Fintype V] in
theorem ColdAtOwnScore.evenWins {G : SimpleGraph V} {s : State V}
    (h : ColdAtOwnScore G s) (hscore : s.score = 0) (player : Bool) :
    EvenWins G player s := by
  simpa [ColdAtOwnScore, WinsCurrentScore, hscore] using h player

omit [Fintype V] in
theorem ColdAtOwnScore.oddWins {G : SimpleGraph V} {s : State V}
    (h : ColdAtOwnScore G s) (hscore : s.score ≠ 0) (player : Bool) :
    OddWins G (!player) s := by
  simpa [ColdAtOwnScore, WinsCurrentScore, hscore] using h player

omit [Fintype V] in
theorem EvenWins.answer_child {G : SimpleGraph V} {seat : Bool}
    {s t : State V} {m : Move V} (h : EvenWins G seat s)
    (hseat : s.toMove ≠ seat) (hstep : step G s m = some t) :
    EvenWins G seat t := by
  cases h with
  | terminal _ hterminal _ =>
      exact False.elim (terminal_no_step hterminal ⟨m, t, hstep⟩)
  | choose _ hturn _ _ _ _ => exact False.elim (hseat hturn)
  | answer _ _ _ hchildren => exact hchildren m t hstep

omit [Fintype V] in
theorem OddWins.answer_child {G : SimpleGraph V} {seat : Bool}
    {s t : State V} {m : Move V} (h : OddWins G seat s)
    (hseat : s.toMove = seat) (hstep : step G s m = some t) :
    OddWins G seat t := by
  cases h with
  | terminal _ hterminal _ =>
      exact False.elim (terminal_no_step hterminal ⟨m, t, hstep⟩)
  | choose _ hturn _ _ _ _ => exact False.elim (hturn hseat)
  | answer _ _ _ hchildren => exact hchildren m t hstep

omit [Fintype V] in
/-- If no hot state occurs below a fixed rank bound, then every state below
that bound is cold at its own accumulated score.  In particular every legal
edge between such states preserves the score.

The proof is simultaneous backward induction on the terminating FIFO rank.
If a legal edge changed score, its source has a nonempty untouched set.  The
mover could take that edge and force the new score from the cold child, or
OPEN any untouched vertex and force the old score from the other cold child,
making the source hot. -/
theorem coldAtOwnScore_below_minHot
    (G : SimpleGraph V) (bound : Nat)
    (hnohot : ∀ (player : Bool) (t : State V), rank t < bound →
      ¬Hot G player t) :
    ∀ s : State V, rank s < bound → ColdAtOwnScore G s := by
  intro s
  induction s using (measure rank).wf.induction with
  | h s ih =>
      intro hsbound
      have hscorePreserved : ∀ {m : Move V} {t : State V},
          step G s m = some t → t.score = s.score := by
        intro m t hstep
        by_contra hscore
        have hUne : s.untouched ≠ ∅ := by
          intro hU
          exact hscore (step_score_eq_of_untouched_empty hU hstep)
        obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hUne
        let so : State V := {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove
          score := s.score }
        have hopen : step G s (.open v) = some so := by
          simp [step, so, hv]
        have htbound : rank t < bound :=
          lt_trans (rank_step_lt hstep) hsbound
        have hsobound : rank so < bound :=
          lt_trans (rank_step_lt hopen) hsbound
        have hcoldT : ColdAtOwnScore G t :=
          ih t (rank_step_lt hstep) htbound
        have hcoldO : ColdAtOwnScore G so :=
          ih so (rank_step_lt hopen) hsobound
        have hhot : Hot G s.toMove s := by
          by_cases hs0 : s.score = 0
          · have ht1 : t.score ≠ 0 := by
              intro ht0
              exact hscore (ht0.trans hs0.symm)
            have hevenO : EvenWins G s.toMove so :=
              hcoldO.evenWins (by simp [so, hs0]) s.toMove
            have hoddT : OddWins G (!s.toMove) t :=
              hcoldT.oddWins ht1 s.toMove
            exact ⟨
              EvenWins.choose s rfl (.open v) so hopen hevenO,
              OddWins.choose s (Bool.eq_not_iff.mpr rfl) m t hstep hoddT⟩
          · have hs1 : s.score = 1 :=
              zmod2_eq_one_of_ne_zero _ hs0
            have ht0 : t.score = 0 := by
              by_contra htne
              have ht1 : t.score = 1 :=
                zmod2_eq_one_of_ne_zero _ htne
              exact hscore (ht1.trans hs1.symm)
            have hevenT : EvenWins G s.toMove t :=
              hcoldT.evenWins ht0 s.toMove
            have hoddO : OddWins G (!s.toMove) so :=
              hcoldO.oddWins (by simp [so, hs0]) s.toMove
            exact ⟨
              EvenWins.choose s rfl m t hstep hevenT,
              OddWins.choose s (Bool.eq_not_iff.mpr rfl)
                (.open v) so hopen hoddO⟩
        exact hnohot s.toMove s hsbound hhot
      by_cases hterminal : Terminal s
      · intro player
        by_cases hs0 : s.score = 0
        · simp only [WinsCurrentScore, hs0, if_true]
          exact EvenWins.terminal s hterminal hs0
        · simp only [WinsCurrentScore, hs0, if_false]
          exact OddWins.terminal s hterminal hs0
      · have hasMove : ∃ m t, step G s m = some t :=
          not_terminal_has_step hterminal
        intro player
        by_cases hs0 : s.score = 0
        · simp only [WinsCurrentScore, hs0, if_true]
          by_cases hplayer : s.toMove = player
          · obtain ⟨m, t, hstep⟩ := hasMove
            have hcold : ColdAtOwnScore G t :=
              ih t (rank_step_lt hstep)
                (lt_trans (rank_step_lt hstep) hsbound)
            exact EvenWins.choose s hplayer m t hstep
              (hcold.evenWins ((hscorePreserved hstep).trans hs0) player)
          · refine EvenWins.answer s hplayer hasMove ?_
            intro m t hstep
            have hcold : ColdAtOwnScore G t :=
              ih t (rank_step_lt hstep)
                (lt_trans (rank_step_lt hstep) hsbound)
            exact hcold.evenWins ((hscorePreserved hstep).trans hs0) player
        · simp only [WinsCurrentScore, hs0, if_false]
          by_cases hplayer : s.toMove = player
          · obtain ⟨m, t, hstep⟩ := hasMove
            have hcold : ColdAtOwnScore G t :=
              ih t (rank_step_lt hstep)
                (lt_trans (rank_step_lt hstep) hsbound)
            refine OddWins.choose s ?_ m t hstep
              (hcold.oddWins ?_ player)
            · simpa using Bool.eq_not_iff.mpr hplayer
            · intro ht0
              exact hs0 ((hscorePreserved hstep).symm.trans ht0)
          · have hseat : s.toMove = !player :=
              Bool.eq_not_iff.mp hplayer
            refine OddWins.answer s hseat hasMove ?_
            intro m t hstep
            have hcold : ColdAtOwnScore G t :=
              ih t (rank_step_lt hstep)
                (lt_trans (rank_step_lt hstep) hsbound)
            simpa using hcold.oddWins (by
              intro ht0
              exact hs0 ((hscorePreserved hstep).symm.trans ht0)) player

omit [Fintype V] in
/-- Every edge strictly below a rank-minimal hot state preserves the current
score.  The nonmoving player's current-score strategy contains every legal
child.  If one child changed score, that player could force the old score via
the universal branch and the new score via coldness of the child, making the
child hot. -/
theorem step_score_eq_below_minHot
    (G : SimpleGraph V) (bound : Nat)
    (hnohot : ∀ (player : Bool) (t : State V), rank t < bound →
      ¬Hot G player t)
    {s t : State V} {m : Move V} (hsbound : rank s < bound)
    (hstep : step G s m = some t) : t.score = s.score := by
  have htbound : rank t < bound := lt_trans (rank_step_lt hstep) hsbound
  have hcoldS : ColdAtOwnScore G s :=
    coldAtOwnScore_below_minHot G bound hnohot s hsbound
  have hcoldT : ColdAtOwnScore G t :=
    coldAtOwnScore_below_minHot G bound hnohot t htbound
  let opponent := !s.toMove
  have hnotturn : s.toMove ≠ opponent := by
    simp [opponent]
  by_cases hs0 : s.score = 0
  · have hevenS : EvenWins G opponent s :=
      hcoldS.evenWins hs0 opponent
    have hevenT : EvenWins G opponent t :=
      hevenS.answer_child hnotturn hstep
    by_contra htne
    have ht1 : t.score ≠ 0 := by
      intro ht0
      exact htne (ht0.trans hs0.symm)
    have hoddT : OddWins G (!opponent) t :=
      hcoldT.oddWins ht1 opponent
    exact hnohot opponent t htbound ⟨hevenT, hoddT⟩
  · have hseat : s.toMove = !opponent := by simp [opponent]
    have hoddS : OddWins G (!opponent) s :=
      hcoldS.oddWins hs0 opponent
    have hoddT : OddWins G (!opponent) t :=
      hoddS.answer_child hseat hstep
    by_contra hscore
    have ht0 : t.score = 0 := by
      by_contra htne
      have hs1 : s.score = 1 := zmod2_eq_one_of_ne_zero _ hs0
      have ht1 : t.score = 1 := zmod2_eq_one_of_ne_zero _ htne
      exact hscore (ht1.trans hs1.symm)
    have hevenT : EvenWins G opponent t :=
      hcoldT.evenWins ht0 opponent
    exact hnohot opponent t htbound ⟨hevenT, hoddT⟩

omit [Fintype V] in
/-- Once the untouched set below a rank-minimal hot state is a singleton,
every queued vertex is nonadjacent to it.  Successively closing the FIFO
queue stays below the rank bound, and score neutrality identifies each
singleton flip with the corresponding adjacency bit. -/
theorem queue_nonadjacent_below_minHot
    (G : SimpleGraph V) (bound : Nat)
    (hnohot : ∀ (player : Bool) (t : State V), rank t < bound →
      ¬Hot G player t)
    (z : V) (q : List V) (turn : Bool) (score : ZMod 2)
    (hbound : rank ({
      untouched := {z}
      queue := q
      ko := false
      toMove := turn
      score := score } : State V) < bound) :
    ∀ a ∈ q, adjacencyBit G a z = 0 := by
  induction q generalizing turn score with
  | nil => simp
  | cons f q ih =>
      let s : State V := {
        untouched := {z}
        queue := f :: q
        ko := false
        toMove := turn
        score := score }
      let t : State V := {
        untouched := {z}
        queue := q
        ko := false
        toMove := !turn
        score := score + flip G {z} f }
      have hclose : step G s .close = some t := by
        simp [step, s, t]
      have hscoreEq :=
        step_score_eq_below_minHot G bound hnohot hbound hclose
      have hflip : flip G {z} f = 0 := by
        have hadd : score + flip G {z} f = score + 0 := by
          simpa [s, t] using hscoreEq
        exact add_left_cancel hadd
      have hfront : adjacencyBit G f z = 0 := by
        simpa [flip_singleton_eq_adjacencyBit] using hflip
      intro a ha
      rcases (List.mem_cons.mp ha) with rfl | ha
      · exact hfront
      · exact ih (!turn) (score + flip G {z} f)
          (lt_trans (rank_step_lt hclose) hbound) a ha

omit [Fintype V] in
/-- Exact public shape of a rank-minimal state at which one physical player
can force both score sheets.  From score zero the player to move chooses
between a unit CLOSE and a zero OPEN.  The untouched set is necessarily the
singleton endpoint of that unit edge.

The singleton conclusion is the extra force-set rigidity absent from a
minimum node in one fixed strategy tree.  Below a minimum hot state every
legal edge is neutral.  Thus deleting any one untouched vertex makes the
front charge zero; deleting two in either order would force a second vertex
to be simultaneously adjacent and nonadjacent to the front. -/
theorem minHotState_is_singletonWall
    (G : SimpleGraph V) (player : Bool) (s : State V)
    (hs0 : s.score = 0) (hhot : Hot G player s)
    (hminimal : ∀ (other : Bool) (t : State V), rank t < rank s →
      ¬Hot G other t) :
    s.toMove = player ∧
      ∃ f q z, s.queue = f :: q ∧ s.ko = false ∧
        s.untouched = {z} ∧ adjacencyBit G f z = 1 ∧
          ∀ a ∈ q, adjacencyBit G a z = 0 := by
  classical
  have hcold : ∀ t : State V, rank t < rank s → ColdAtOwnScore G t :=
    coldAtOwnScore_below_minHot G (rank s) hminimal
  have hturn : s.toMove = player := by
    by_contra hturn
    have hodd := hhot.2
    cases hodd with
    | terminal _ _ hscore => exact hscore hs0
    | choose _ hseat _ _ _ _ =>
        exact hseat (Bool.eq_not_iff.mp hturn)
    | answer _ _ hasMove hchildren =>
        obtain ⟨m, t, hstep⟩ := hasMove
        have hevenT : EvenWins G player t :=
          hhot.1.answer_child hturn hstep
        have hoddT : OddWins G (!player) t := hchildren m t hstep
        exact hminimal player t (rank_step_lt hstep) ⟨hevenT, hoddT⟩
  have hoddChoice : ∃ m t, step G s m = some t ∧
      OddWins G (!player) t := by
    cases hhot.2 with
    | terminal _ _ hscore => exact False.elim (hscore hs0)
    | choose _ _ m t hstep hwin => exact ⟨m, t, hstep, hwin⟩
    | answer _ hseat _ _ =>
        exact False.elim ((Bool.eq_not_iff.mpr hturn) hseat)
  obtain ⟨mOne, tOne, hstepOne, hoddOne⟩ := hoddChoice
  have htOne : tOne.score = 1 := by
    have htne : tOne.score ≠ 0 := by
      intro ht0
      have hevenOne : EvenWins G player tOne :=
        (hcold tOne (rank_step_lt hstepOne)).evenWins ht0 player
      exact hminimal player tOne (rank_step_lt hstepOne)
        ⟨hevenOne, hoddOne⟩
    exact zmod2_eq_one_of_ne_zero _ htne
  have hmOne : mOne = .close := by
    cases mOne with
    | «open» v =>
        have hscore := open_score hstepOne
        rw [hs0] at hscore
        exact False.elim (one_ne_zero (htOne.symm.trans hscore))
    | close => rfl
    | pass =>
        have hscore := pass_score hstepOne
        rw [hs0] at hscore
        exact False.elim (one_ne_zero (htOne.symm.trans hscore))
  subst mOne
  obtain ⟨f, q, hqueue, hcloseScore⟩ := close_score hstepOne
  have hko : s.ko = false := by
    cases hk : s.ko with
    | false => rfl
    | true => simp [step, hqueue, hk] at hstepOne
  have hflip : flip G s.untouched f = 1 := by
    rw [hs0, zero_add] at hcloseScore
    exact hcloseScore.symm.trans htOne
  have hevenChoice : ∃ m t, step G s m = some t ∧
      EvenWins G player t := by
    cases hhot.1 with
    | terminal _ hterminal _ =>
        exact False.elim (terminal_no_step hterminal
          ⟨.close, tOne, hstepOne⟩)
    | choose _ _ m t hstep hwin => exact ⟨m, t, hstep, hwin⟩
    | answer _ hseat _ _ => exact False.elim (hseat hturn)
  obtain ⟨mZero, tZero, hstepZero, hevenZero⟩ := hevenChoice
  have htZero : tZero.score = 0 := by
    by_contra htne
    have hoddZero : OddWins G (!player) tZero :=
      (hcold tZero (rank_step_lt hstepZero)).oddWins htne player
    exact hminimal player tZero (rank_step_lt hstepZero)
      ⟨hevenZero, hoddZero⟩
  have hmZero : ∃ z, mZero = .open z := by
    cases mZero with
    | «open» z => exact ⟨z, rfl⟩
    | close =>
        rw [hstepOne] at hstepZero
        cases hstepZero
        exact False.elim (one_ne_zero (htOne.symm.trans htZero))
    | pass => simp [step, hqueue, hko] at hstepZero
  obtain ⟨z, rfl⟩ := hmZero
  have hzU : z ∈ s.untouched := by
    simp only [step] at hstepZero
    split at hstepZero
    · assumption
    · contradiction
  have herase : ∀ w ∈ s.untouched,
      flip G (s.untouched.erase w) f = 0 := by
    intro w hw
    let so : State V := {
      untouched := s.untouched.erase w
      queue := s.queue ++ [w]
      ko := s.queue.isEmpty
      toMove := !s.toMove
      score := s.score }
    have hopen : step G s (.open w) = some so := by
      simp [step, so, hw]
    let soc : State V := {
      untouched := s.untouched.erase w
      queue := q ++ [w]
      ko := false
      toMove := s.toMove
      score := s.score + flip G (s.untouched.erase w) f }
    have hclose : step G so .close = some soc := by
      simp [step, so, soc, hqueue, hko]
    have hscoreEq := step_score_eq_below_minHot G (rank s) hminimal
      (rank_step_lt hopen) hclose
    simpa [so, soc, hs0] using hscoreEq
  have hsingleton : s.untouched = {z} := by
    ext w
    constructor
    · intro hw
      by_contra hwz
      have hwErase : w ∈ s.untouched.erase z :=
        Finset.mem_erase.mpr ⟨hwz, hw⟩
      let soz : State V := {
        untouched := s.untouched.erase z
        queue := s.queue ++ [z]
        ko := s.queue.isEmpty
        toMove := !s.toMove
        score := s.score }
      have hopenz : step G s (.open z) = some soz := by
        simp [step, soz, hzU]
      let sozw : State V := {
        untouched := (s.untouched.erase z).erase w
        queue := (s.queue ++ [z]) ++ [w]
        ko := false
        toMove := s.toMove
        score := s.score }
      have hopenw : step G soz (.open w) = some sozw := by
        simp [step, soz, sozw, hwErase, hqueue]
      let sc : State V := {
        untouched := (s.untouched.erase z).erase w
        queue := (q ++ [z]) ++ [w]
        ko := false
        toMove := !s.toMove
        score := s.score + flip G ((s.untouched.erase z).erase w) f }
      have hclose : step G sozw .close = some sc := by
        simp [step, sozw, sc, hqueue, hko]
      have hdouble : flip G ((s.untouched.erase z).erase w) f = 0 := by
        have hscoreEq := step_score_eq_below_minHot G (rank s) hminimal
          (lt_trans (rank_step_lt hopenw) (rank_step_lt hopenz)) hclose
        simpa [sozw, sc, hs0] using hscoreEq
      have hbitOne : adjacencyBit G f w = 1 := by
        have heq := flip_eq_flip_erase_add (G := G) (f := f) hw
        rw [hflip, herase w hw, zero_add] at heq
        exact heq.symm
      have hbitZero : adjacencyBit G f w = 0 := by
        have heq := flip_eq_flip_erase_add (G := G) (f := f) hwErase
        rw [herase z hzU, hdouble, zero_add] at heq
        exact heq.symm
      exact one_ne_zero (hbitOne.symm.trans hbitZero)
    · simp only [Finset.mem_singleton]
      intro hwz
      subst w
      exact hzU
  have hbit : adjacencyBit G f z = 1 := by
    have heq := flip_eq_flip_erase_add (G := G) (f := f) hzU
    rw [hflip, herase z hzU, zero_add] at heq
    exact heq.symm
  have htail : ∀ a ∈ q, adjacencyBit G a z = 0 := by
    let t : State V := {
      untouched := {z}
      queue := q
      ko := false
      toMove := !s.toMove
      score := s.score + flip G {z} f }
    have hclose : step G s .close = some t := by
      simp [step, t, hqueue, hko, hsingleton]
    exact queue_nonadjacent_below_minHot G (rank s) hminimal z q
      (!s.toMove) (s.score + flip G {z} f) (rank_step_lt hclose)
  exact ⟨hturn, f, q, z, hqueue, hko, hsingleton, hbit, htail⟩

end

end Ogdoad.Fifo
