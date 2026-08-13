import Ogdoad.FifoConsumedDummyBoundary
import Ogdoad.FifoDummyFront

/-!
# Root-gadget interface and the three-label dummy escape

A first-seat root counterstrategy can be assembled from a star of bad pair
states centred at the isolated dummy: after the defender first opens the
dummy, select one real opener; after every real first opener, select the
dummy.  This file makes that sufficient interface exact.

The least consumed-dummy controlled wall does not fill the interface.  On
the three-label edge-plus-isolate board its dummy-front predecessor has an
odd CLOSE child, but the defender can instead OPEN the sole remaining real
label.  That move exhausts the untouched carrier at score zero and is
immediately even-winning.  Thus grafting one consumed wall below the dummy
front cannot produce a root counterstrategy; a scalable disproof gadget must
also poison the whole real OPEN escape fan.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## A structural safe-reply theorem for paired cone cells -/

/-- The untouched carrier is a union of `mate`-pairs. -/
def MateClosed (mate : V → V) (U : Finset V) : Prop :=
  ∀ x, x ∈ U ↔ mate x ∈ U

/-- The live queue is a concatenation of `mate`-pairs in FIFO order. -/
inductive MateQueue (mate : V → V) : List V → Prop
  | nil : MateQueue mate []
  | cell (x : V) {q : List V} (tail : MateQueue mate q) :
      MateQueue mate (x :: mate x :: q)

/-- Every pair has zero aggregate CLOSE charge into every mate-closed
untouched carrier.  This is the exact scalar condition used by the pairing
strategy; the usual even-cross-edge parity between cells implies it. -/
def MateChargeNeutral (G : SimpleGraph V) (mate : V → V) : Prop :=
  ∀ U, MateClosed mate U → ∀ x,
    flip G U x + flip G U (mate x) = 0

omit [Fintype V] in
/-- A mate-closed finite sum of a pairwise cancelling function vanishes. -/
theorem sum_eq_zero_of_mateClosed
    (mate : V → V) (hfixed : ∀ x, mate x ≠ x)
    (hinvolutive : Function.Involutive mate) :
    ∀ (U : Finset V), MateClosed mate U →
      ∀ f : V → ZMod 2, (∀ x, f x + f (mate x) = 0) →
        ∑ x ∈ U, f x = 0 := by
  intro U
  induction U using (measure Finset.card).wf.induction with
  | h U ih =>
      intro hU f hcancel
      by_cases hempty : U = ∅
      · simp [hempty]
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hmx : mate x ∈ U := (hU x).mp hx
        have hmxErase : mate x ∈ U.erase x :=
          Finset.mem_erase.mpr ⟨hfixed x, hmx⟩
        let R := (U.erase x).erase (mate x)
        have hRlt : R.card < U.card := by
          have hRcard := Finset.card_erase_add_one hmxErase
          have hUcard := Finset.card_erase_add_one hx
          change R.card + 1 = (U.erase x).card at hRcard
          omega
        have hRclosed : MateClosed mate R := by
          intro z
          simp only [R, Finset.mem_erase]
          constructor
          · rintro ⟨hzm, hzx, hzU⟩
            refine ⟨?_, ?_, (hU z).mp hzU⟩
            · exact fun hmz ↦ hzx (hinvolutive.injective hmz)
            · intro hmz
              apply hzm
              calc
                z = mate (mate z) := (hinvolutive z).symm
                _ = mate x := congrArg mate hmz
          · rintro ⟨hmzmx, hmzx, hmzU⟩
            refine ⟨?_, ?_, (hU z).mpr hmzU⟩
            · intro hzx
              subst z
              exact hmzx (hinvolutive x)
            · intro hzx
              subst z
              exact hmzmx rfl
        have hRsum : ∑ z ∈ R, f z = 0 :=
          ih R hRlt hRclosed f hcancel
        have hsplit := sum_erase_erase_add f hx hmx (by
          exact fun h ↦ hfixed x h.symm)
        change (∑ z ∈ R, f z) + f (mate x) + f x =
          ∑ z ∈ U, f z at hsplit
        rw [hRsum, zero_add, add_comm, hcancel x] at hsplit
        exact hsplit.symm

omit [Fintype V] in
/-- Even cross-incidence between every two mate-cells implies neutral paired
CLOSE charge into every union of cells. -/
theorem mateChargeNeutral_of_cross
    (G : SimpleGraph V) (mate : V → V)
    (hfixed : ∀ x, mate x ≠ x)
    (hinvolutive : Function.Involutive mate)
    (hcross : ∀ a x,
      (adjacencyBit G a x + adjacencyBit G (mate a) x) +
        (adjacencyBit G a (mate x) +
          adjacencyBit G (mate a) (mate x)) = 0) :
    MateChargeNeutral G mate := by
  intro U hU a
  rw [flip_eq_sum_adjacencyBit, flip_eq_sum_adjacencyBit,
    ← Finset.sum_add_distrib]
  exact sum_eq_zero_of_mateClosed mate hfixed hinvolutive U hU
    (fun x ↦ adjacencyBit G a x + adjacencyBit G (mate a) x)
    (hcross a)

omit [Fintype V] [DecidableEq V] in
theorem MateQueue.append_cell {mate : V → V} {q : List V}
    (hq : MateQueue mate q) (x : V) :
    MateQueue mate (q ++ [x, mate x]) := by
  induction hq with
  | nil => exact .cell x .nil
  | cell a tail ih => simpa using MateQueue.cell a ih

omit [Fintype V] in
theorem MateClosed.erase_pair {mate : V → V} {U : Finset V}
    (hinvolutive : Function.Involutive mate)
    (hU : MateClosed mate U) (x : V) :
    MateClosed mate ((U.erase x).erase (mate x)) := by
  intro z
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hzm, hzx, hzU⟩
    refine ⟨?_, ?_, (hU z).mp hzU⟩
    · exact fun hmz ↦ hzx (hinvolutive.injective hmz)
    · intro hmz
      apply hzm
      calc
        z = mate (mate z) := (hinvolutive z).symm
        _ = mate x := congrArg mate hmz
  · rintro ⟨hmzmx, hmzx, hmzU⟩
    refine ⟨?_, ?_, (hU z).mpr hmzU⟩
    · intro hzx
      subst z
      exact hmzx (hinvolutive x)
    · intro hzx
      subst z
      exact hmzmx rfl

omit [Fintype V] [DecidableEq V] in
theorem MateQueue.nil_or_cell {mate : V → V} {q : List V}
    (hq : MateQueue mate q) :
    q = [] ∨ ∃ x tail, q = x :: mate x :: tail ∧ MateQueue mate tail := by
  cases hq with
  | nil => exact Or.inl rfl
  | cell x tail => exact Or.inr ⟨x, _, rfl, tail⟩

omit [Fintype V] in
/-- Abstract parity-cell pairing strategy from any opponent-to-move public
state.  The opponent may OPEN a cell member or CLOSE the first member of a
queued cell; the designated seat answers with its mate.  Two moves preserve
the mover, restore score zero, and strictly decrease rank. -/
theorem evenWins_of_mate_pairing
    (G : SimpleGraph V) (mate : V → V)
    (hfixed : ∀ x, mate x ≠ x)
    (hinvolutive : Function.Involutive mate)
    (hneutral : MateChargeNeutral G mate) :
    ∀ (seat : Bool) (s : State V),
      s.toMove ≠ seat → s.score = 0 → s.ko = false →
      MateClosed mate s.untouched → MateQueue mate s.queue →
      EvenWins G seat s := by
  intro seat s
  induction s using (measure rank).wf.induction with
  | h s ih =>
      intro hturn hscore hko hU hq
      by_cases hterminal : Terminal s
      · exact EvenWins.terminal s hterminal hscore
      · have hasMove : ∃ m t, step G s m = some t :=
          not_terminal_has_step hterminal
        refine EvenWins.answer s hturn hasMove ?_
        intro m t hstep
        cases m with
        | «open» x =>
            have hx : x ∈ s.untouched := by
              simp only [step] at hstep
              split at hstep
              · assumption
              · contradiction
            let t' : State V := {
              untouched := s.untouched.erase x
              queue := s.queue ++ [x]
              ko := s.queue.isEmpty
              toMove := !s.toMove
              score := s.score }
            have ht : t = t' := by
              simp only [step] at hstep
              rw [if_pos hx] at hstep
              exact Option.some.inj hstep.symm
            subst t
            have hmx : mate x ∈ s.untouched := (hU x).mp hx
            have hmxErase : mate x ∈ s.untouched.erase x := by
              exact Finset.mem_erase.mpr ⟨hfixed x, hmx⟩
            let u : State V := {
              untouched := (s.untouched.erase x).erase (mate x)
              queue := (s.queue ++ [x]) ++ [mate x]
              ko := false
              toMove := s.toMove
              score := s.score }
            have hopenMate : step G t' (.open (mate x)) = some u := by
              simp [step, t', u, hmxErase]
            have htTurn : t'.toMove = seat := by
              have hsTurn : s.toMove = !seat := Bool.eq_not_iff.mpr hturn
              simp [t', hsTurn]
            refine EvenWins.choose t' htTurn (.open (mate x)) u
              hopenMate ?_
            apply ih u
            · exact lt_trans (rank_step_lt hopenMate) (rank_step_lt hstep)
            · simpa [u] using hturn
            · simpa [u] using hscore
            · rfl
            · exact hU.erase_pair hinvolutive x
            · simpa [u, List.append_assoc] using hq.append_cell x
        | close =>
            rcases hq.nil_or_cell with hnil | ⟨x, q, hqueue, htail⟩
            · simp [step, hnil] at hstep
            ·
                let t' : State V := {
                  untouched := s.untouched
                  queue := mate x :: q
                  ko := false
                  toMove := !s.toMove
                  score := s.score + flip G s.untouched x }
                have ht : t = t' := by
                  simp only [step] at hstep
                  rw [hqueue, hko] at hstep
                  exact Option.some.inj hstep.symm
                subst t
                let u : State V := {
                  untouched := s.untouched
                  queue := q
                  ko := false
                  toMove := s.toMove
                  score := s.score + flip G s.untouched x +
                    flip G s.untouched (mate x) }
                have hcloseMate : step G t' .close = some u := by
                  simp [step, t', u]
                have htTurn : t'.toMove = seat := by
                  have hsTurn : s.toMove = !seat :=
                    Bool.eq_not_iff.mpr hturn
                  simp [t', hsTurn]
                refine EvenWins.choose t' htTurn .close u hcloseMate ?_
                apply ih u
                · exact lt_trans (rank_step_lt hcloseMate)
                    (rank_step_lt hstep)
                · simpa [u] using hturn
                · simp [u, hscore, hneutral s.untouched hU x]
                · rfl
                · simpa [u] using hU
                · simpa [u] using htail
        | pass =>
            simp [step, hko] at hstep

/-! ## The even-twin repair in the sharp cone family -/

/-- The sharp nine-real fan with two extra false twins `9,10` adjacent only
to `0`; label `11` is the isolated dummy. -/
def sharpK11ConeGraph : SimpleGraph (Fin 12) :=
  SimpleGraph.fromRel fun x y ↦
    (x = 0 ∧ (y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨
      y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10)) ∨
    (x = 1 ∧ (y = 3 ∨ y = 5)) ∨
    (x = 2 ∧ (y = 5 ∨ y = 8)) ∨
    (x = 3 ∧ (y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8)) ∨
    (x = 4 ∧ y = 6) ∨
    (x = 5 ∧ y = 7) ∨
    (x = 6 ∧ (y = 7 ∨ y = 8)) ∨
    (x = 7 ∧ y = 8)

/-- Pairing visible in the sharp dummy child:
`{0,d},{1,2},{3,8},{4,5},{6,7},{9,10}`. -/
def sharpK11Mate : Fin 12 → Fin 12 :=
  ![11, 2, 1, 8, 5, 4, 7, 6, 3, 10, 9, 0]

theorem sharpK11Mate_ne (x : Fin 12) : sharpK11Mate x ≠ x := by
  fin_cases x <;> decide

theorem sharpK11Mate_involutive : Function.Involutive sharpK11Mate := by
  intro x
  fin_cases x <;> rfl

theorem sharpK11ConeGraph_dummy : IsDummy sharpK11ConeGraph 11 := by
  intro x
  fin_cases x <;>
    simp [sharpK11ConeGraph, SimpleGraph.fromRel_adj]

set_option maxHeartbeats 1000000 in
/-- The displayed cells have even cross-incidence, expressed directly as
the charge identity required by the pairing strategy. -/
theorem sharpK11Mate_chargeNeutral :
    MateChargeNeutral sharpK11ConeGraph sharpK11Mate := by
  apply mateChargeNeutral_of_cross sharpK11ConeGraph sharpK11Mate
    sharpK11Mate_ne sharpK11Mate_involutive
  have htwo : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
  intro a x
  fin_cases a <;> fin_cases x <;>
    simp [adjacencyBit, sharpK11ConeGraph, SimpleGraph.fromRel_adj,
      sharpK11Mate] <;> exact htwo

/-- Structural, non-minimax certificate for the unique safe dummy reply in
the two-twin cone.  After `OPEN 0; OPEN d`, the six displayed cells are
paired in both the untouched carrier and FIFO queue, so player `true` wins
by responding to every OPEN/CLOSE with its mate. -/
theorem sharpK11_dummyReply_evenWins :
    EvenWins sharpK11ConeGraph true
      (afterInitialTwoOpens (0 : Fin 12) 11) := by
  apply evenWins_of_mate_pairing sharpK11ConeGraph sharpK11Mate
    sharpK11Mate_ne sharpK11Mate_involutive sharpK11Mate_chargeNeutral
    true (afterInitialTwoOpens (0 : Fin 12) 11)
  · decide
  · rfl
  · rfl
  · intro x
    fin_cases x <;>
      simp [afterInitialTwoOpens, sharpK11Mate]
  · exact MateQueue.cell 0 MateQueue.nil

/-- Exact data required for a second-seat root counterstrategy after the odd
player selects one fixed initial opener `x`: every distinct defender reply
must have an odd continuation.  This is the interface exhibited by the sharp
nine-real fan except at its unique dummy reply. -/
structure SecondSeatReplyFan (G : SimpleGraph V) (x : V) where
  child : ∀ y, y ∈ (Finset.univ.erase x : Finset V) →
    OddStrategy G true (afterInitialTwoOpens x y)

/-- A complete bad reply fan below one selected first opener reconstructs an
exact second-seat root counterstrategy. -/
def SecondSeatReplyFan.toOddStrategy [Nontrivial V]
    {G : SimpleGraph V} {x : V} (fan : SecondSeatReplyFan G x) :
    OddStrategy G true (initial (V := V)) := by
  let child : OddStrategy G true (afterInitialOpen x) :=
    OddStrategy.answer (afterInitialOpen x) (by simp [afterInitialOpen])
      (afterInitialOpen_hasMove G x) (by
        intro m t hstep
        cases m with
        | close => simp [step, afterInitialOpen] at hstep
        | pass =>
            have hne : (Finset.univ.erase x : Finset V) ≠ ∅ := by
              obtain ⟨y, hyx⟩ := exists_ne x
              exact Finset.nonempty_iff_ne_empty.mp ⟨y, by simp [hyx]⟩
            simp [step, afterInitialOpen, hne] at hstep
        | «open» y =>
            have hy : y ∈ (Finset.univ.erase x : Finset V) := by
              simp only [step, afterInitialOpen] at hstep
              split at hstep
              · assumption
              · contradiction
            have hcanonical :=
              (afterInitialOpen_step_open_iff G x y).2 hy
            rw [hcanonical] at hstep
            have ht : t = afterInitialTwoOpens x y :=
              Option.some.inj hstep.symm
            subst t
            exact fan.child y hy)
  exact OddStrategy.choose (initial (V := V)) (by simp [initial])
    (.open x) (afterInitialOpen x) (initial_step_open G x) child

/-- The k11 two-twin cone cannot fill the sharp reply-fan interface at
opener `0`: its dummy reply is structurally even-winning by cell pairing. -/
theorem no_sharpK11_secondSeatReplyFanAtZero :
    IsEmpty (SecondSeatReplyFan sharpK11ConeGraph (0 : Fin 12)) := by
  refine ⟨fun fan ↦ ?_⟩
  have hdmem : (11 : Fin 12) ∈
      (Finset.univ.erase (0 : Fin 12) : Finset (Fin 12)) := by decide
  exact sharpK11_dummyReply_evenWins.not_oddWins
    (fan.child 11 hdmem).toOddWins

/-- Exact sufficient pair-state interface for a first-seat root
counterstrategy whose selected second-OPEN fan is a star centred at `d`. -/
structure FirstSeatDummyStarGadget (G : SimpleGraph V) (d : V) where
  frontReply : V
  frontReply_ne : frontReply ≠ d
  frontTree : OddStrategy G false
    (afterInitialTwoOpens d frontReply)
  rearTree : ∀ x, x ≠ d →
    OddStrategy G false (afterInitialTwoOpens x d)

/-- A complete dummy-centred star of odd pair states reconstructs one exact
odd strategy at the initial root. -/
def FirstSeatDummyStarGadget.toOddStrategy [Nontrivial V]
    {G : SimpleGraph V} {d : V}
    (gadget : FirstSeatDummyStarGadget G d) :
    OddStrategy G false (initial (V := V)) := by
  let fan : FirstSeatOddFan G := {
    next := fun x ↦ if x = d then gadget.frontReply else d
    next_ne := by
      intro x
      by_cases hxd : x = d
      · subst x
        simpa using gadget.frontReply_ne
      · simp [hxd, Ne.symm hxd]
    tail := by
      intro x
      by_cases hxd : x = d
      · subst x
        simpa using gadget.frontTree
      · simp only [hxd, ↓reduceIte]
        exact gadget.rearTree x hxd }
  exact fan.toOddStrategy G

/-- Propositional constructor for the star gadget.  It isolates the exact
burden of a disproof construction: one bad dummy-front pair and every bad
dummy-rear pair. -/
def FirstSeatDummyStarGadget.ofOddWins
    {G : SimpleGraph V} {d y : V} (hyd : y ≠ d)
    (hfront : OddWins G false (afterInitialTwoOpens d y))
    (hrear : ∀ x, x ≠ d →
      OddWins G false (afterInitialTwoOpens x d)) :
    FirstSeatDummyStarGadget G d where
  frontReply := y
  frontReply_ne := hyd
  frontTree := Classical.choice hfront.nonempty_oddStrategy
  rearTree x hxd := Classical.choice (hrear x hxd).nonempty_oddStrategy

/-- The commuting dummy-front diamond supplies the front arm of the star
only after every dummy-consumed real-pair endpoint has itself been poisoned.
The remaining dummy-rear arms are still separate obligations. -/
def FirstSeatDummyStarGadget.ofConsumedPairFan
    {G : SimpleGraph V} {d y : V} (hd : IsDummy G d) (hyd : y ≠ d)
    (hcarrier : (dummyFrontCarrier d y).Nonempty)
    (hconsumed : ∀ z ∈ dummyFrontCarrier d y,
      OddWins G false (dummyConsumedPairState d y z))
    (hrear : ∀ x, x ≠ d →
      OddWins G false (afterInitialTwoOpens x d)) :
    FirstSeatDummyStarGadget G d :=
  FirstSeatDummyStarGadget.ofOddWins hyd
    (oddWins_dummyFront_of_all_consumedPairs
      G d y hd hcarrier hconsumed)
    hrear

omit [Fintype V] in
/-- Generic safe-reply lemma.  If the defender at a score-zero node can OPEN
the last untouched label, the child has empty carrier and is even-winning;
hence the defender wins immediately. -/
theorem evenWins_of_open_exhausts_untouched
    {G : SimpleGraph V} {seat : Bool} {s t : State V} {z : V}
    (hturn : s.toMove = seat)
    (hstep : step G s (.open z) = some t)
    (hU : t.untouched = ∅) (hscore : t.score = 0) :
    EvenWins G seat s := by
  exact EvenWins.choose s hturn (.open z) t hstep
    (evenWins_of_untouched_empty seat t hU hscore)

/-- On the active three-label edge-plus-isolate board, the dummy-front pair
`[1,2]` has the consumed controlled wall as its CLOSE child. -/
theorem activeNeutral_dummyFront_close_reaches_consumedWall :
    step activeNeutralIntervalGraph
        (afterInitialTwoOpens (1 : Fin 3) 2) .close =
      some consumedDummyWallState := by
  have hclose := afterInitialDummyReal_step_close
    (G := activeNeutralIntervalGraph) (d := (1 : Fin 3)) (y := 2)
    activeNeutralIntervalGraph_dummy
  have hcarrier : dummyFrontCarrier (1 : Fin 3) 2 = {0} := by
    ext x
    fin_cases x <;> simp [dummyFrontCarrier]
  simpa [dummyFrontClearedState, consumedDummyWallState,
    hcarrier] using hclose

/-- The competing real OPEN exhausts the carrier at score zero. -/
theorem activeNeutral_dummyFront_open_real_exhausts :
    ∃ t,
      step activeNeutralIntervalGraph
          (afterInitialTwoOpens (1 : Fin 3) 2) (.open 0) = some t ∧
      t.untouched = ∅ ∧ t.score = 0 ∧
      EvenWins activeNeutralIntervalGraph false t := by
  let t := dummyFrontOpenedState (1 : Fin 3) 2 0
  have hmem : (0 : Fin 3) ∈ dummyFrontCarrier 1 2 := by
    simp [dummyFrontCarrier]
  have hopen := afterInitialDummyReal_step_open
    activeNeutralIntervalGraph (1 : Fin 3) 2 0 hmem
  refine ⟨t, hopen, ?_, rfl, ?_⟩
  · ext x
    fin_cases x <;> simp [t, dummyFrontOpenedState, dummyFrontCarrier]
  · apply evenWins_of_untouched_empty false t
    · ext x
      fin_cases x <;> simp [t, dummyFrontOpenedState, dummyFrontCarrier]
    · rfl

/-- Exact no-go for grafting the least consumed-dummy wall into a root
gadget.  The dummy-front state has an odd CLOSE child, but is itself
even-winning because the defender OPENs the sole remaining real vertex.
Consequently no odd strategy can use it as the front arm of a dummy-star
root counterstrategy. -/
theorem consumedDummyWall_not_a_dummyFront_rootGadget :
    OddWins activeNeutralIntervalGraph false consumedDummyWallState ∧
      step activeNeutralIntervalGraph
          (afterInitialTwoOpens (1 : Fin 3) 2) .close =
        some consumedDummyWallState ∧
      EvenWins activeNeutralIntervalGraph false
        (afterInitialTwoOpens (1 : Fin 3) 2) ∧
      IsEmpty (OddStrategy activeNeutralIntervalGraph false
        (afterInitialTwoOpens (1 : Fin 3) 2)) := by
  obtain ⟨t, hopen, hU, hscore, htEven⟩ :=
    activeNeutral_dummyFront_open_real_exhausts
  have hfrontEven : EvenWins activeNeutralIntervalGraph false
      (afterInitialTwoOpens (1 : Fin 3) 2) :=
    EvenWins.choose (afterInitialTwoOpens (1 : Fin 3) 2) rfl
      (.open 0) t hopen htEven
  refine ⟨oddWins_consumedDummyWall_nonmover,
    activeNeutral_dummyFront_close_reaches_consumedWall,
    hfrontEven, ?_⟩
  exact ⟨fun tree ↦ hfrontEven.not_oddWins tree.toOddWins⟩

/-- Therefore the active three-label board admits no complete dummy-star
gadget centred at its isolated label, despite containing the sharp consumed
wall on the dummy-front CLOSE branch. -/
theorem no_activeNeutral_firstSeatDummyStarGadget :
    IsEmpty (FirstSeatDummyStarGadget
      activeNeutralIntervalGraph (1 : Fin 3)) := by
  refine ⟨fun gadget ↦ ?_⟩
  have hrootOdd : OddStrategy activeNeutralIntervalGraph false
      (initial (V := Fin 3)) := gadget.toOddStrategy
  exact bothEven_consumedDummyBoundary_root.1.not_oddWins hrootOdd.toOddWins

end

end Ogdoad.Fifo
