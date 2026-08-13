import Ogdoad.FifoFirstSeatRoot
import Ogdoad.FifoOuterFan
import Ogdoad.FifoOutcome

/-!
# The parity-seat FIFO root reduction

Exact minimax data suggest a dummy-free root theorem independent of the graph:
the mover should be able to force score zero on odd-order carriers, while the
nonmover should be able to force score zero on even-order carriers.  This file
does not assert that theorem.  It kernel-checks the common first-fan reduction
in both parity cases.

For odd order, an alleged mover-seat odd counterstrategy has a complete initial
OPEN fan of odd cardinality.  For even order, an alleged nonmover-seat odd
counterstrategy selects one first opener, after which the complete second-OPEN
fan again has odd cardinality.  In both cases the entire ancestry-prefix moment
of that odd fan is zero.  Thus the desired root theorem would follow if the
corresponding child continuation representatives could be selected with zero
sum.  The final two theorems make that remaining causal condition exact.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The pointwise dummy-free parity-seat statement under investigation.  It
is a definition of the target proposition, not a theorem or an assumption. -/
def FifoParitySeatAt (G : SimpleGraph V) : Prop :=
  (Odd (Fintype.card V) → EvenWins G false (initial (V := V))) ∧
  (Even (Fintype.card V) → EvenWins G true (initial (V := V)))

/-- The exact extra root property needed to upgrade the parity-selected seat
to both seats.  On odd order it excludes mover control; on even order it
excludes nonmover control. -/
def ParityControlledExclusionAt (G : SimpleGraph V) : Prop :=
  (Odd (Fintype.card V) → ¬MoverControlled G (initial (V := V))) ∧
  (Even (Fintype.card V) → ¬NonmoverControlled G (initial (V := V)))

/-- Both physical seats can force score zero at this initial root. -/
def BothSeatsEvenAt (G : SimpleGraph V) : Prop :=
  ∀ seat, EvenWins G seat (initial (V := V))

omit [Fintype V] in
/-- If the mover already wins even, excluding mover control is exactly the
missing nonmover win. -/
theorem bothEven_iff_not_moverControlled_of_moverEven
    {G : SimpleGraph V} {s : State V} (hM : MoverEvenWins G s) :
    BothEven G s ↔ ¬MoverControlled G s := by
  simp [BothEven, MoverControlled, hM]

omit [Fintype V] in
/-- Dually, if the nonmover already wins even, excluding nonmover control is
exactly the missing mover win. -/
theorem bothEven_iff_not_nonmoverControlled_of_nonmoverEven
    {G : SimpleGraph V} {s : State V} (hN : NonmoverEvenWins G s) :
    BothEven G s ↔ ¬NonmoverControlled G s := by
  simp [BothEven, NonmoverControlled, hN]

/-- Under the parity-seat statement, both-seat winning is exactly exclusion
of the one controlled outcome class left open by the carrier parity. -/
theorem bothSeatsEvenAt_iff_parityControlledExclusionAt
    (G : SimpleGraph V) (hparity : FifoParitySeatAt G) :
    BothSeatsEvenAt G ↔ ParityControlledExclusionAt G := by
  constructor
  · intro hboth
    constructor
    · intro _hodd hcontrolled
      exact hcontrolled.2 (hboth true)
    · intro _heven hcontrolled
      exact hcontrolled.1 (hboth false)
  · intro hexclusion seat
    rcases hparity with ⟨hoddSeat, hevenSeat⟩
    rcases hexclusion with ⟨hoddExclude, hevenExclude⟩
    rcases Nat.even_or_odd (Fintype.card V) with hEven | hOdd
    · have hN : NonmoverEvenWins G (initial (V := V)) := by
        simpa [NonmoverEvenWins, initial] using
          hevenSeat hEven
      have hBoth : BothEven G (initial (V := V)) :=
        (bothEven_iff_not_nonmoverControlled_of_nonmoverEven hN).2
          (hevenExclude hEven)
      cases seat
      · exact hBoth.1
      · exact hBoth.2
    · have hM : MoverEvenWins G (initial (V := V)) := by
        simpa [MoverEvenWins, initial] using
          hoddSeat hOdd
      have hBoth : BothEven G (initial (V := V)) :=
        (bothEven_iff_not_moverControlled_of_moverEven hM).2
          (hoddExclude hOdd)
      cases seat
      · exact hBoth.1
      · exact hBoth.2

/-- Specializing the preceding equivalence to a graph carrying an isolated
dummy does not simplify the remaining proposition: isolation is available,
but the exact missing statement is still the controlled-outcome exclusion. -/
theorem isolated_bothSeatsEvenAt_iff_parityControlledExclusionAt
    (G : SimpleGraph V) (d : V) (_hd : IsDummy G d)
    (hparity : FifoParitySeatAt G) :
    BothSeatsEvenAt G ↔ ParityControlledExclusionAt G :=
  bothSeatsEvenAt_iff_parityControlledExclusionAt G hparity

/-- The live carrier at the initial root is the whole vertex set. -/
theorem liveSet_initial : liveSet (initial (V := V)) = Finset.univ := by
  ext v
  simp [liveSet, initial]

/-- After one initial OPEN, the opened vertex has moved from `untouched` to
the queue, so the live carrier is still the whole vertex set. -/
theorem liveSet_afterInitialOpen (x : V) :
    liveSet (afterInitialOpen x) = Finset.univ := by
  ext v
  by_cases hv : v = x
  · subst v
    simp [liveSet, afterInitialOpen]
  · simp [liveSet, afterInitialOpen]

/-- Every initial OPEN contributes the full-carrier star of its label. -/
theorem moveLiveStar_initial_open (x : V) :
    moveLiveStar (initial (V := V)) (.open x) =
      liveStarVector Finset.univ x := by
  simp [moveLiveStar, liveSet_initial]

/-- Every second initial OPEN also contributes its full-carrier star. -/
theorem moveLiveStar_afterInitialOpen_open (x y : V) :
    moveLiveStar (afterInitialOpen x) (.open y) =
      liveStarVector Finset.univ y := by
  simp [moveLiveStar, liveSet_afterInitialOpen]

/-- The complete initial OPEN fan has zero universal prefix moment. -/
theorem initial_open_fan_prefix_zero :
    ∑ x : V, moveLiveStar (initial (V := V)) (.open x) = 0 := by
  simp only [moveLiveStar_initial_open]
  simpa using sum_liveStarVector_eq_zero (Finset.univ : Finset V)

/-- A selected first OPEN plus the complete fan of all legal second OPENs has
zero universal prefix moment.  This is the even-order ancestry cancellation;
the identity itself does not need the parity hypothesis. -/
theorem initial_two_open_fan_prefix_zero (x : V) :
    moveLiveStar (initial (V := V)) (.open x) +
        ∑ y ∈ (Finset.univ.erase x : Finset V),
          moveLiveStar (afterInitialOpen x) (.open y) = 0 := by
  rw [moveLiveStar_initial_open]
  simp only [moveLiveStar_afterInitialOpen_open]
  calc
    liveStarVector Finset.univ x +
        ∑ y ∈ (Finset.univ.erase x : Finset V),
          liveStarVector Finset.univ y =
        (∑ y ∈ (Finset.univ.erase x : Finset V),
          liveStarVector Finset.univ y) + liveStarVector Finset.univ x :=
      add_comm _ _
    _ = ∑ y ∈ (Finset.univ : Finset V), liveStarVector Finset.univ y :=
      Finset.sum_erase_add _ _ (Finset.mem_univ x)
    _ = 0 := sum_liveStarVector_eq_zero (Finset.univ : Finset V)

omit [DecidableEq V] in
/-- On odd order, the complete first-OPEN fan is an odd list. -/
theorem initial_open_fan_card_odd (hcard : Odd (Fintype.card V)) :
    (Finset.univ.toList : List V).length % 2 = 1 := by
  rw [Finset.length_toList, Finset.card_univ]
  exact Nat.odd_iff.mp hcard

/-- On positive even order, deleting any selected first opener leaves an odd
list of legal second OPEN replies. -/
theorem second_open_fan_card_odd (x : V) (hcard : Even (Fintype.card V)) :
    ((Finset.univ.erase x : Finset V).toList).length % 2 = 1 := by
  rw [Finset.length_toList]
  apply real_open_replies_card_mod_two Finset.univ x (Finset.mem_univ x)
  simpa [Finset.card_univ] using Nat.even_iff.mp hcard

omit [Fintype V] in
private theorem list_sum_map_eq_finset_sum
    (S : Finset V) (f : V → EdgeVector V) :
    (S.toList.map f).sum = ∑ v ∈ S, f v := by
  calc
    (S.toList.map f).sum = S.toList.toFinset.sum f :=
      (List.sum_toFinset f S.nodup_toList).symm
    _ = ∑ v ∈ S, f v := by rw [S.toList_toFinset]

omit [Fintype V] [DecidableEq V] in
private theorem list_sum_map_add
    {I : Type*} (is : List I) (f g : I → EdgeVector V) :
    (is.map fun i ↦ f i + g i).sum =
      (is.map f).sum + (is.map g).sum := by
  induction is with
  | nil => simp
  | cons i rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      abel

/-- Odd-order mover-seat reduction.  The complete initial fan has odd
augmentation and zero prefix.  Therefore zero-sum continuation choices would
put zero in the root affine response space, contradicting any alleged exact
odd counterstrategy. -/
theorem no_oddCard_mover_counterstrategy_of_zero_continuation_sum
    (G : SimpleGraph V) (hcard : Odd (Fintype.card V))
    (hasMove : ∃ m u, step G (initial (V := V)) m = some u)
    (children : ∀ m u, step G (initial (V := V)) m = some u →
      OddStrategy G false u)
    (a : V → EdgeVector V)
    (ha : ∀ x,
      AffineResponseMoment G false
        (children (.open x) (afterInitialOpen x) (initial_step_open G x))
        (a x))
    (hsum : ∑ x : V, a x = 0) :
    False := by
  let root : OddStrategy G false (initial (V := V)) :=
    OddStrategy.answer (initial (V := V)) rfl hasMove children
  let is : List V := Finset.univ.toList
  have hstep : ∀ x ∈ is,
      step G (initial (V := V)) (.open x) = some (afterInitialOpen x) := by
    intro x _hx
    exact initial_step_open G x
  have hodd : is.length % 2 = 1 := by
    exact initial_open_fan_card_odd hcard
  have hdecorated :
      (is.map fun x ↦
        moveLiveStar (initial (V := V)) (.open x) + a x).sum = 0 := by
    rw [list_sum_map_add]
    have hprefix :
        (is.map fun x ↦ moveLiveStar (initial (V := V)) (.open x)).sum = 0 := by
      rw [list_sum_map_eq_finset_sum]
      simpa [is] using initial_open_fan_prefix_zero (V := V)
    have htail : (is.map a).sum = 0 := by
      rw [list_sum_map_eq_finset_sum]
      simpa [is] using hsum
    rw [hprefix, htail, add_zero]
  have hzero : AffineResponseMoment G false root 0 := by
    exact AffineResponseMoment.answer_odd_fan_zero is
      (fun x ↦ .open x) afterInitialOpen hstep a
      (fun x _hx ↦ ha x) hodd hdecorated
  exact no_zero_affineResponseMoment_initial hzero

/-- Even-order nonmover-seat reduction.  The odd player selects the first
OPEN `x`; the even seat then owns the complete odd second-OPEN fan.  Zero-sum
continuation choices at that fan cancel exactly with the selected first-OPEN
ancestry star, again contradicting an exact root odd strategy. -/
theorem no_evenCard_nonmover_counterstrategy_of_zero_continuation_sum
    (G : SimpleGraph V) (x : V) (hcard : Even (Fintype.card V))
    (hasMove : ∃ m u, step G (afterInitialOpen x) m = some u)
    (children : ∀ m u, step G (afterInitialOpen x) m = some u →
      OddStrategy G true u)
    (a : V → EdgeVector V)
    (ha : ∀ y (hy : y ∈ (Finset.univ.erase x : Finset V)),
      AffineResponseMoment G true
        (children (.open y) (afterInitialTwoOpens x y)
          ((afterInitialOpen_step_open_iff G x y).2 hy))
        (a y))
    (hsum : ∑ y ∈ (Finset.univ.erase x : Finset V), a y = 0) :
    False := by
  let child : OddStrategy G true (afterInitialOpen x) :=
    OddStrategy.answer (afterInitialOpen x) rfl hasMove children
  let root : OddStrategy G true (initial (V := V)) :=
    OddStrategy.choose (initial (V := V)) (by simp [initial])
      (.open x) (afterInitialOpen x) (initial_step_open G x) child
  let is : List V := (Finset.univ.erase x).toList
  have hstep : ∀ y ∈ is,
      step G (afterInitialOpen x) (.open y) =
        some (afterInitialTwoOpens x y) := by
    intro y hy
    exact (afterInitialOpen_step_open_iff G x y).2 (by simpa [is] using hy)
  have hodd : is.length % 2 = 1 := by
    exact second_open_fan_card_odd x hcard
  have hprefix :
      (is.map fun y ↦ moveLiveStar (afterInitialOpen x) (.open y)).sum =
        moveLiveStar (initial (V := V)) (.open x) := by
    rw [list_sum_map_eq_finset_sum]
    have hzero := initial_two_open_fan_prefix_zero x
    have hself : moveLiveStar (initial (V := V)) (.open x) +
        moveLiveStar (initial (V := V)) (.open x) = 0 := by
      ext e
      exact CharTwo.add_self_eq_zero _
    calc
      (∑ y ∈ (Finset.univ.erase x : Finset V),
          moveLiveStar (afterInitialOpen x) (.open y)) =
          (moveLiveStar (initial (V := V)) (.open x) +
              moveLiveStar (initial (V := V)) (.open x)) +
            ∑ y ∈ (Finset.univ.erase x : Finset V),
              moveLiveStar (afterInitialOpen x) (.open y) := by
                rw [hself, zero_add]
      _ = moveLiveStar (initial (V := V)) (.open x) +
          (moveLiveStar (initial (V := V)) (.open x) +
            ∑ y ∈ (Finset.univ.erase x : Finset V),
              moveLiveStar (afterInitialOpen x) (.open y)) := by abel
      _ = moveLiveStar (initial (V := V)) (.open x) := by
        rw [hzero, add_zero]
  have hdecorated :
      (is.map fun y ↦
        moveLiveStar (afterInitialOpen x) (.open y) + a y).sum =
          moveLiveStar (initial (V := V)) (.open x) := by
    rw [list_sum_map_add, hprefix]
    rw [list_sum_map_eq_finset_sum, hsum, add_zero]
  have hchildPoint : AffineResponseMoment G true child
      (moveLiveStar (initial (V := V)) (.open x)) := by
    rw [← hdecorated]
    have hoddMap :
        (is.map fun y ↦
          moveLiveStar (afterInitialOpen x) (.open y) + a y).length % 2 = 1 := by
      simpa using hodd
    exact AffineResponseMoment.odd_list_sum _ hoddMap (by
      intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      have hy' : y ∈ (Finset.univ.erase x : Finset V) := by
        simpa [is] using hy
      exact AffineResponseMoment.answerChild
        (hseat := rfl) (hasMove := hasMove) (hchildren := children)
        (hstep := hstep y hy) (ha y hy'))
  have hrootPoint : AffineResponseMoment G true root 0 := by
    have hlift : AffineResponseMoment G true root
        (moveLiveStar (initial (V := V)) (.open x) +
          moveLiveStar (initial (V := V)) (.open x)) :=
      AffineResponseMoment.choose hchildPoint
    have hself : moveLiveStar (initial (V := V)) (.open x) +
        moveLiveStar (initial (V := V)) (.open x) = 0 := by
      ext e
      exact CharTwo.add_self_eq_zero _
    rwa [hself] at hlift
  exact no_zero_affineResponseMoment_initial hrootPoint

end

end Ogdoad.Fifo
