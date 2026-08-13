import Ogdoad.FifoCellSwapOutcomeBoundary
import Ogdoad.FifoFirstSeatRoot
import Ogdoad.FifoMatching
import Ogdoad.FifoNormalization
import Ogdoad.FifoOddSpikeFactor
import Ogdoad.FifoSeparatorFlow

/-!
# Dynamic Gaussian pairing behind a balanced FIFO front

Suppose the two oldest FIFO fronts `x,y` have equal charge into the current
untouched carrier `U`, and `U` still contains an isolated dummy `d`.  If the
opponent opens any real vertex `z`, the next player can open a second vertex
`w` so that `x,y` are balanced again after deleting both.

The selector is constructive at the parity level.  Write
`delta(v) = A(x,v)+A(y,v)`.  Balance says the sum of `delta` on `U` is zero.
If `delta(z)=0`, choose the isolated dummy, whose delta is zero.  If
`delta(z)=1`, deleting `z` leaves a set of delta-sum one, so another unit
coordinate exists.  This is precisely one step of online binary Gaussian
pairing.  It does not handle the exceptional branch `z=d`, nor does it yet
show that the later queued pair `z,w` is itself balanced after `x,y` close.
-/

namespace Ogdoad.Fifo

open scoped BigOperators

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Difference of the two front adjacency rows at one prospective opener. -/
def frontDifference (G : SimpleGraph V) (x y v : V) : ZMod 2 :=
  adjacencyBit G x v + adjacencyBit G y v

omit [Fintype V] in
/-- The aggregate row difference on `U` is the sum of the two close charges. -/
theorem closureValue_frontDifference
    (G : SimpleGraph V) (U : Finset V) (x y : V) :
    closureValue (frontDifference G x y) U =
      flip G U x + flip G U y := by
  simp only [closureValue, frontDifference, Finset.sum_add_distrib,
    flip_eq_sum_adjacencyBit, flip_eq_sum_adjacencyBit]

omit [Fintype V] in
/-- Erasing two coordinates preserves equality of front charges exactly when
their two row-difference bits agree. -/
theorem balanced_after_two_erases_of_frontDifference_eq
    (G : SimpleGraph V) (U : Finset V) (x y z w : V)
    (hz : z ∈ U) (hw : w ∈ U.erase z)
    (hbalanced : flip G U x = flip G U y)
    (hdiff : frontDifference G x y z = frontDifference G x y w) :
    flip G ((U.erase z).erase w) x =
      flip G ((U.erase z).erase w) y := by
  rw [flip_erase_eq_add hw, flip_erase_eq_add hw,
    flip_erase_eq_add hz, flip_erase_eq_add hz]
  change adjacencyBit G x z + adjacencyBit G y z =
    adjacencyBit G x w + adjacencyBit G y w at hdiff
  rw [hbalanced]
  have hyself : adjacencyBit G y z + adjacencyBit G y z = 0 :=
    CharTwo.add_self_eq_zero _
  have hxself : adjacencyBit G x w + adjacencyBit G x w = 0 :=
    CharTwo.add_self_eq_zero _
  have hcoord : adjacencyBit G x z + adjacencyBit G x w =
      adjacencyBit G y z + adjacencyBit G y w := by
    calc
      adjacencyBit G x z + adjacencyBit G x w =
          (adjacencyBit G x z + adjacencyBit G y z) +
            (adjacencyBit G y z + adjacencyBit G x w) := by
              calc
                _ = (adjacencyBit G x z + adjacencyBit G x w) + 0 := by
                  rw [add_zero]
                _ = (adjacencyBit G x z + adjacencyBit G x w) +
                    (adjacencyBit G y z + adjacencyBit G y z) := by rw [hyself]
                _ = _ := by abel
      _ = (adjacencyBit G x w + adjacencyBit G y w) +
            (adjacencyBit G y z + adjacencyBit G x w) := by rw [hdiff]
      _ = adjacencyBit G y z + adjacencyBit G y w := by
        calc
          _ = (adjacencyBit G y z + adjacencyBit G y w) +
              (adjacencyBit G x w + adjacencyBit G x w) := by abel
          _ = _ := by rw [hxself, add_zero]
  simpa only [add_assoc] using
    congrArg (fun t ↦ flip G U y + t) hcoord

omit [Fintype V] in
/-- Dynamic Gaussian response selector.  Behind a balanced front pair, every
real OPEN has a distinct legal partner which restores front balance. -/
theorem exists_paired_open_preserving_front_balance
    {G : SimpleGraph V} {d x y z : V} {U : Finset V}
    (hd : IsDummy G d) (hdU : d ∈ U) (hzU : z ∈ U) (hzd : z ≠ d)
    (hbalanced : flip G U x = flip G U y) :
    ∃ w ∈ U.erase z,
      flip G ((U.erase z).erase w) x =
        flip G ((U.erase z).erase w) y := by
  classical
  let delta := frontDifference G x y
  have hsum : closureValue delta U = 0 := by
    dsimp only [delta]
    rw [closureValue_frontDifference, hbalanced]
    exact CharTwo.add_self_eq_zero _
  by_cases hz0 : delta z = 0
  · have hdmem : d ∈ U.erase z := Finset.mem_erase.mpr ⟨Ne.symm hzd, hdU⟩
    refine ⟨d, hdmem,
      balanced_after_two_erases_of_frontDifference_eq
        G U x y z d hzU hdmem hbalanced ?_⟩
    dsimp only [delta] at hz0 ⊢
    rw [hz0]
    have hxd : ¬G.Adj x d := by simpa [G.adj_comm] using hd x
    have hyd : ¬G.Adj y d := by simpa [G.adj_comm] using hd y
    simp [frontDifference, adjacencyBit, hxd, hyd]
  · have hz1 : delta z = 1 := zmod2_eq_one_of_ne_zero _ hz0
    have herase : closureValue delta (U.erase z) = 1 := by
      rw [closureValue_erase_eq_add delta hzU, hsum, hz1, zero_add]
    obtain ⟨w, hw, hw1⟩ :=
      exists_weight_one_of_closureValue_eq_one delta herase
    refine ⟨w, hw,
      balanced_after_two_erases_of_frontDifference_eq
        G U x y z w hzU hw hbalanced ?_⟩
    dsimp only [delta] at hz1 hw1 ⊢
    exact hz1.trans hw1.symm

/-- Public endpoint after the opponent opens `z` and the even player answers
with its dynamic Gaussian partner `w`.  The original balanced fronts remain
oldest; the new pair is appended behind them. -/
def pairedOpenExtensionState (U : Finset V) (x y z w : V)
    (attacker : Bool) (score : ZMod 2) : State V where
  untouched := (U.erase z).erase w
  queue := [x, y, z, w]
  ko := false
  toMove := attacker
  score := score

omit [Fintype V] in
/-- The dynamic pairing selector is realized by two legal FIFO OPENs and
returns control to the original attacker with the old front pair balanced. -/
theorem balancedFront_open_real_has_paired_open
    (G : SimpleGraph V) (U : Finset V) (d x y z : V)
    (attacker : Bool) (score : ZMod 2)
    (hd : IsDummy G d) (hdU : d ∈ U) (hzU : z ∈ U) (hzd : z ≠ d)
    (hbalanced : flip G U x = flip G U y) :
    ∃ w sz szw,
      step G (balancedFrontState U x y attacker score) (.open z) = some sz ∧
      step G sz (.open w) = some szw ∧
      szw = pairedOpenExtensionState U x y z w attacker score ∧
      flip G szw.untouched x = flip G szw.untouched y := by
  obtain ⟨w, hw, hbalance⟩ :=
    exists_paired_open_preserving_front_balance hd hdU hzU hzd hbalanced
  let sz : State V := {
    untouched := U.erase z
    queue := [x, y, z]
    ko := false
    toMove := !attacker
    score := score }
  let szw := pairedOpenExtensionState U x y z w attacker score
  refine ⟨w, sz, szw, ?_, ?_, rfl, ?_⟩
  · simp [step, balancedFrontState, sz, hzU]
  · simp [step, sz, szw, pairedOpenExtensionState, hw]
  · exact hbalance

/-! ## The two-bit root colour as a second-order Gaussian debt -/

/-- The second-order debt of an ordered pair on a real carrier.  It is the
sum of the two adjacency rows evaluated on the degree-parity vector. -/
def pairSecondMoment (G : SimpleGraph V) (R : Finset V) (x y : V) : ZMod 2 :=
  neighborDegreeBit G R x + neighborDegreeBit G R y

/-- Gram form of the front-row difference against the degree vector on the
twice-punctured residual carrier. -/
def pairResidualGram (G : SimpleGraph V) (R : Finset V) (x y : V) : ZMod 2 :=
  ∑ v ∈ (R.erase x).erase y,
    frontDifference G x y v * flip G ((R.erase x).erase y) v

/-- A simultaneous fibre of two binary labels. -/
def bitPairFiber (U : Finset V) (p r : V → ZMod 2) (a b : ZMod 2) :
    Finset V := U.filter fun v ↦ p v = a ∧ r v = b

omit [Fintype V] [DecidableEq V] in
/-- Equality of two parity bits is represented by the affine indicator
`1 + a + t`. -/
theorem zmod2_equalityIndicator (a t : ZMod 2) :
    (if t = a then 1 else 0) = 1 + a + t := by
  by_cases h : t = a
  · subst t
    rw [if_pos rfl]
    calc
      (1 : ZMod 2) = 1 + 0 := (add_zero 1).symm
      _ = 1 + (a + a) := by rw [CharTwo.add_self_eq_zero]
      _ = 1 + a + a := by abel
  · rw [if_neg h]
    calc
      (0 : ZMod 2) = t + 1 + a :=
        (zmod2_add_one_add_eq_zero_of_ne t a h).symm
      _ = 1 + a + t := by abel

omit [Fintype V] [DecidableEq V] in
/-- Vanishing cardinality, two linear moments, and mixed moment make every
simultaneous two-bit fibre even. -/
theorem bitPairFiber_card_eq_zero_of_moments
    (U : Finset V) (p r : V → ZMod 2)
    (hcard : (U.card : ZMod 2) = 0)
    (hp : (∑ v ∈ U, p v) = 0) (hr : (∑ v ∈ U, r v) = 0)
    (hpr : (∑ v ∈ U, p v * r v) = 0) (a b : ZMod 2) :
    ((bitPairFiber U p r a b).card : ZMod 2) = 0 := by
  classical
  rw [bitPairFiber, Finset.natCast_card_filter]
  calc
    (∑ v ∈ U, if p v = a ∧ r v = b then (1 : ZMod 2) else 0) =
        ∑ v ∈ U, (1 + a + p v) * (1 + b + r v) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [← zmod2_equalityIndicator a (p v),
            ← zmod2_equalityIndicator b (r v)]
          by_cases hpva : p v = a <;> by_cases hrvb : r v = b <;>
            simp [hpva, hrvb]
    _ = (U.card : ZMod 2) * ((1 + a) * (1 + b)) +
          (1 + b) * (∑ v ∈ U, p v) +
          (1 + a) * (∑ v ∈ U, r v) +
          ∑ v ∈ U, p v * r v := by
            have hpoint (v : V) :
                (1 + a + p v) * (1 + b + r v) =
                  (1 + a) * (1 + b) + (1 + b) * p v +
                    (1 + a) * r v + p v * r v := by ring
            simp_rw [hpoint, Finset.sum_add_distrib]
            simp only [Finset.sum_const, nsmul_eq_mul]
            rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = 0 := by rw [hcard, hp, hr, hpr]; ring

omit [Fintype V] in
/-- For a same-degree root pair, the residual Gram debt is exactly the
difference of the two full-board odd-neighbour bits. -/
theorem pairResidualGram_eq_pairSecondMoment_of_sameDegreeMate
    (G : SimpleGraph V) (R : Finset V) (x y : V) (hx : x ∈ R)
    (hyMate : y ∈ sameDegreeMates G R x) :
    pairResidualGram G R x y = pairSecondMoment G R x y := by
  classical
  let S := (R.erase x).erase y
  let p : V → ZMod 2 := fun v ↦ flip G R v
  let delta := frontDifference G x y
  have hyErase : y ∈ R.erase x := (Finset.mem_filter.mp hyMate).1
  have hy : y ∈ R := Finset.mem_of_mem_erase hyErase
  have hxy : x ≠ y := fun h ↦ (Finset.ne_of_mem_erase hyErase) h.symm
  have hdeg : p x = p y := by
    dsimp only [p]
    exact (Finset.mem_filter.mp hyMate).2.symm
  have hbalanced : flip G S x = flip G S y := by
    dsimp only [S]
    exact sameDegreeMate_balances_residual G R x y hx hyMate
  have hfull : pairSecondMoment G R x y =
      ∑ v ∈ S, delta v * p v := by
    have hsx := sum_erase_erase_add
      (f := fun v ↦ adjacencyBit G x v * p v) hx hy hxy
    have hsy := sum_erase_erase_add
      (f := fun v ↦ adjacencyBit G y v * p v) hx hy hxy
    rw [adjacencyBit_self, zero_mul, add_zero] at hsx hsy
    rw [pairSecondMoment, neighborDegreeBit, neighborDegreeBit,
      ← hsx, ← hsy]
    have hendpoint :
        adjacencyBit G x y * p y + adjacencyBit G y x * p x = 0 := by
      rw [adjacencyBit_comm G y x, ← hdeg]
      exact CharTwo.add_self_eq_zero _
    calc
      (∑ z ∈ S, adjacencyBit G x z * p z) +
            adjacencyBit G x y * p y +
          ((∑ z ∈ S, adjacencyBit G y z * p z) +
            adjacencyBit G y x * p x) =
          ((∑ z ∈ S, adjacencyBit G x z * p z) +
            ∑ z ∈ S, adjacencyBit G y z * p z) +
            (adjacencyBit G x y * p y +
              adjacencyBit G y x * p x) := by abel
      _ = (∑ z ∈ S, adjacencyBit G x z * p z) +
            ∑ z ∈ S, adjacencyBit G y z * p z := by
              rw [hendpoint, add_zero]
      _ = ∑ v ∈ S, delta v * p v := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v hv
        dsimp only [delta, frontDifference]
        ring
  rw [pairResidualGram, hfull]
  change (∑ v ∈ S, delta v * flip G S v) =
    ∑ v ∈ S, delta v * p v
  calc
    (∑ v ∈ S, delta v * flip G S v) =
        ∑ v ∈ S,
          delta v * (p v + adjacencyBit G v x + adjacencyBit G v y) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [flip_erase_erase_eq_add (G := G) (w := v) hx hy hxy]
    _ = (∑ v ∈ S, delta v * p v) +
        ∑ v ∈ S, delta v * delta v := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro v hv
          dsimp only [delta, frontDifference]
          rw [adjacencyBit_comm G v x, adjacencyBit_comm G v y]
          ring
    _ = (∑ v ∈ S, delta v * p v) + ∑ v ∈ S, delta v := by
          apply congrArg (fun t ↦ (∑ v ∈ S, delta v * p v) + t)
          apply Finset.sum_congr rfl
          intro v hv
          exact zmod2_sq_eq_self _
    _ = (∑ v ∈ S, delta v * p v) +
        (flip G S x + flip G S y) := by
          congr 1
          dsimp only [delta, frontDifference]
          rw [Finset.sum_add_distrib, ← flip_eq_sum_adjacencyBit,
            ← flip_eq_sum_adjacencyBit]
    _ = ∑ v ∈ S, delta v * p v := by
          rw [hbalanced, CharTwo.add_self_eq_zero, add_zero]

omit [Fintype V] in
/-- The second two-bit handshake, in selector form.  If the initial pair has
equal degree and zero second moment, then every residual vertex has a
distinct residual mate matching both its full degree and its adjacency-row
difference against the queued pair. -/
theorem exists_same_pairSyndrome_mate
    (G : SimpleGraph V) (R : Finset V) (x y z : V)
    (hx : x ∈ R) (hyMate : y ∈ sameDegreeMates G R x)
    (hR : (R.card : ZMod 2) = 0)
    (hmoment : pairSecondMoment G R x y = 0)
    (hz : z ∈ (R.erase x).erase y) :
    ∃ w ∈ ((R.erase x).erase y).erase z,
      flip G R w = flip G R z ∧
        frontDifference G x y w = frontDifference G x y z := by
  classical
  let S := (R.erase x).erase y
  let p : V → ZMod 2 := fun v ↦ flip G R v
  let r : V → ZMod 2 := frontDifference G x y
  let F := bitPairFiber S p r (p z) (r z)
  have hyErase : y ∈ R.erase x := (Finset.mem_filter.mp hyMate).1
  have hy : y ∈ R := Finset.mem_of_mem_erase hyErase
  have hxy : x ≠ y := fun h ↦ (Finset.ne_of_mem_erase hyErase) h.symm
  have hbalanced : flip G S x = flip G S y := by
    dsimp only [S]
    exact sameDegreeMate_balances_residual G R x y hx hyMate
  have hcardS : (S.card : ZMod 2) = 0 := by
    exact (card_erase_erase_cast_eq hx hy hxy).trans hR
  have hp : (∑ v ∈ S, p v) = 0 := by
    have hsum := sum_flip_pairUntouched (G := G) hx hy hxy
    change (∑ v ∈ S, p v) = 0
    rw [hsum, hbalanced, CharTwo.add_self_eq_zero]
  have hr : (∑ v ∈ S, r v) = 0 := by
    change closureValue (frontDifference G x y) S = 0
    rw [closureValue_frontDifference, hbalanced,
      CharTwo.add_self_eq_zero]
  have hpr : (∑ v ∈ S, p v * r v) = 0 := by
    have hgram : pairResidualGram G R x y = 0 :=
      (pairResidualGram_eq_pairSecondMoment_of_sameDegreeMate
        G R x y hx hyMate).trans hmoment
    have hexpand : pairResidualGram G R x y =
        (∑ v ∈ S, p v * r v) + ∑ v ∈ S, r v := by
      rw [pairResidualGram]
      calc
        (∑ v ∈ S, frontDifference G x y v * flip G S v) =
            ∑ v ∈ S, r v * (p v + r v) := by
              apply Finset.sum_congr rfl
              intro v hv
              dsimp only [r, p, S]
              rw [flip_erase_erase_eq_add (G := G) (w := v) hx hy hxy]
              dsimp only [frontDifference]
              rw [adjacencyBit_comm G v x, adjacencyBit_comm G v y]
              ring
        _ = (∑ v ∈ S, p v * r v) + ∑ v ∈ S, r v := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro v hv
              rw [mul_add, zmod2_sq_eq_self]
              ring
    rw [hexpand, hr, add_zero] at hgram
    exact hgram
  have hFcard : (F.card : ZMod 2) = 0 := by
    exact bitPairFiber_card_eq_zero_of_moments S p r hcardS hp hr hpr
      (p z) (r z)
  have hzF : z ∈ F := by
    change z ∈ bitPairFiber S p r (p z) (r z)
    rw [bitPairFiber, Finset.mem_filter]
    exact ⟨hz, rfl, rfl⟩
  have hFeraseCard : ((F.erase z).card : ZMod 2) = 1 := by
    have hsplit := card_erase_cast_add_one hzF
    rw [hFcard] at hsplit
    calc
      ((F.erase z).card : ZMod 2) =
          (((F.erase z).card : ZMod 2) + 1) + 1 := by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = 1 := by rw [hsplit, zero_add]
  have hnonempty : (F.erase z).Nonempty := by
    by_contra hempty
    have heq : F.erase z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [heq] at hFeraseCard
    norm_num at hFeraseCard
  obtain ⟨w, hw⟩ := hnonempty
  have hwF : w ∈ F := Finset.mem_of_mem_erase hw
  have hwz : w ≠ z := Finset.ne_of_mem_erase hw
  have hwData := Finset.mem_filter.mp hwF
  refine ⟨w, Finset.mem_erase.mpr ⟨hwz, hwData.1⟩, ?_, ?_⟩
  · exact hwData.2.1
  · exact hwData.2.2

omit [Fintype V] in
/-- The syndrome mate balances both queued cells after the two new OPENs:
the old pair remains balanced and the appended pair is balanced on the new
residual carrier. -/
theorem exists_twoCell_balanced_extension
    (G : SimpleGraph V) (R : Finset V) (x y z : V)
    (hx : x ∈ R) (hyMate : y ∈ sameDegreeMates G R x)
    (hR : (R.card : ZMod 2) = 0)
    (hmoment : pairSecondMoment G R x y = 0)
    (hz : z ∈ (R.erase x).erase y) :
    ∃ w ∈ ((R.erase x).erase y).erase z,
      flip G ((((R.erase x).erase y).erase z).erase w) x =
        flip G ((((R.erase x).erase y).erase z).erase w) y ∧
      flip G ((((R.erase x).erase y).erase z).erase w) z =
        flip G ((((R.erase x).erase y).erase z).erase w) w := by
  classical
  let S := (R.erase x).erase y
  obtain ⟨w, hw, hp, hr⟩ :=
    exists_same_pairSyndrome_mate G R x y z hx hyMate hR hmoment hz
  have hfront : flip G S x = flip G S y := by
    dsimp only [S]
    exact sameDegreeMate_balances_residual G R x y hx hyMate
  have hold : flip G ((S.erase z).erase w) x =
      flip G ((S.erase z).erase w) y := by
    apply balanced_after_two_erases_of_frontDifference_eq
      G S x y z w hz hw hfront
    exact hr.symm
  have hyErase : y ∈ R.erase x := (Finset.mem_filter.mp hyMate).1
  have hy : y ∈ R := Finset.mem_of_mem_erase hyErase
  have hxy : x ≠ y := fun h ↦ (Finset.ne_of_mem_erase hyErase) h.symm
  have hzwDegree : flip G S w = flip G S z := by
    rw [flip_erase_erase_eq_add (G := G) (w := w) hx hy hxy,
      flip_erase_erase_eq_add (G := G) (w := z) hx hy hxy]
    dsimp only [frontDifference] at hr
    rw [adjacencyBit_comm G w x, adjacencyBit_comm G w y,
      adjacencyBit_comm G z x, adjacencyBit_comm G z y]
    rw [hp]
    simpa only [add_assoc] using
      congrArg (fun t ↦ flip G R z + t) hr
  have hwMate : w ∈ sameDegreeMates G S z := by
    rw [sameDegreeMates, Finset.mem_filter]
    exact ⟨hw, hzwDegree⟩
  have hnew := sameDegreeMate_balances_residual G S z w hz hwMate
  exact ⟨w, hw, hold, hnew⟩

/-- Bilinear cross-debt between two queued row-difference pairs. -/
def pairCrossMoment (G : SimpleGraph V) (S : Finset V)
    (x y z w : V) : ZMod 2 :=
  ∑ v ∈ S, frontDifference G z w v * frontDifference G x y v

omit [Fintype V] in
/-- Exact third-moment obstruction after appending a syndrome-matched cell.
Matching the first pair's degree and row-difference labels balances both
cells, but the new cell's second-order debt is its old full-board debt plus
the bilinear cross-debt against the old cell.  The two-bit handshake does not
control this third scalar. -/
theorem pairSecondMoment_residual_eq_add_crossMoment
    (G : SimpleGraph V) (R : Finset V) (x y z w : V)
    (hx : x ∈ R) (hy : y ∈ R) (hxy : x ≠ y)
    (hdeg : flip G R x = flip G R y)
    (hr : frontDifference G x y z = frontDifference G x y w) :
    pairSecondMoment G ((R.erase x).erase y) z w =
      pairSecondMoment G R z w +
        pairCrossMoment G ((R.erase x).erase y) x y z w := by
  classical
  let S := (R.erase x).erase y
  let p : V → ZMod 2 := fun v ↦ flip G R v
  let r := frontDifference G x y
  let e := frontDifference G z w
  have hendpointRows : e y + e x = 0 := by
    calc
      e y + e x = r z + r w := by
        dsimp only [e, r, frontDifference]
        rw [adjacencyBit_comm G z y, adjacencyBit_comm G w y,
          adjacencyBit_comm G z x, adjacencyBit_comm G w x]
        ring
      _ = 0 := by
        change r z = r w at hr
        rw [← hr, CharTwo.add_self_eq_zero]
  have hendpoint : e y * p y + e x * p x = 0 := by
    have hp : p x = p y := hdeg
    rw [hp]
    calc
      e y * p y + e x * p y = (e y + e x) * p y := by ring
      _ = 0 := by rw [hendpointRows, zero_mul]
  have hfull : pairSecondMoment G R z w = ∑ v ∈ R, e v * p v := by
    rw [pairSecondMoment, neighborDegreeBit, neighborDegreeBit,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [e, frontDifference]
    ring
  have hsplit := sum_erase_erase_add (f := fun v ↦ e v * p v) hx hy hxy
  have hsplit' : (∑ v ∈ S, e v * p v) = ∑ v ∈ R, e v * p v := by
    calc
      (∑ v ∈ S, e v * p v) =
          (∑ v ∈ S, e v * p v) + (e y * p y + e x * p x) := by
            rw [hendpoint, add_zero]
      _ = (∑ v ∈ S, e v * p v) + e y * p y + e x * p x := by
            abel
      _ = ∑ v ∈ R, e v * p v := hsplit
  rw [pairSecondMoment, neighborDegreeBit, neighborDegreeBit,
    pairCrossMoment, hfull, ← hsplit']
  calc
    (∑ v ∈ S, adjacencyBit G z v * flip G S v) +
        ∑ v ∈ S, adjacencyBit G w v * flip G S v =
      ∑ v ∈ S, e v * (p v + r v) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v hv
        rw [flip_erase_erase_eq_add (G := G) (w := v) hx hy hxy]
        dsimp only [e, r, frontDifference, p]
        rw [adjacencyBit_comm G v x, adjacencyBit_comm G v y]
        ring
    _ = (∑ v ∈ S, e v * p v) + ∑ v ∈ S, e v * r v := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v hv
        ring

omit [Fintype V] in
/-- The odd-neighbour bit has even total on either degree-parity class.  This
is the algebraic core of the two-bit handshake: on the odd-degree class it is
the handshake identity for the induced graph, while the even-degree class is
its complement inside the vanishing total two-step moment. -/
theorem sum_neighborDegreeBit_degreeParityClass_eq_zero
    (G : SimpleGraph V) (R : Finset V) (a : ZMod 2) :
    (∑ v ∈ degreeParityClass G R a, neighborDegreeBit G R v) = 0 := by
  classical
  let p : V → ZMod 2 := fun v ↦ flip G R v
  let b : V → ZMod 2 := fun v ↦ neighborDegreeBit G R v
  let O : Finset V := R.filter fun v ↦ p v = 1
  have hbO (v : V) : b v = flip G O v := by
    dsimp only [b, neighborDegreeBit]
    rw [flip_eq_sum_adjacencyBit]
    calc
      (∑ w ∈ R, adjacencyBit G v w * p w) =
          ∑ w ∈ R, p w * adjacencyBit G v w := by
            apply Finset.sum_congr rfl
            intro w hw
            exact mul_comm _ _
      _ = ∑ w ∈ O, adjacencyBit G v w := by
            simpa [O] using
              (sum_bit_mul_eq_filter_one R p (adjacencyBit G v))
  have hO : (∑ v ∈ O, b v) = 0 := by
    calc
      (∑ v ∈ O, b v) = ∑ v ∈ O, flip G O v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hbO v
      _ = 0 := sum_flip_self_eq_zero G O
  have htotal : (∑ v ∈ R, b v) = 0 := by
    dsimp only [b]
    simp only [neighborDegreeBit]
    calc
      (∑ v ∈ R, ∑ w ∈ R,
          adjacencyBit G v w * flip G R w) =
          ∑ w ∈ R, flip G R w * flip G R w := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro w hw
            rw [← Finset.sum_mul]
            have hadj : (∑ v ∈ R, adjacencyBit G v w) = flip G R w := by
              rw [flip_eq_sum_adjacencyBit]
              apply Finset.sum_congr rfl
              intro v hv
              exact adjacencyBit_comm G v w
            rw [hadj]
      _ = ∑ w ∈ R, flip G R w := by
            apply Finset.sum_congr rfl
            intro w hw
            exact zmod2_sq_eq_self _
      _ = 0 := sum_flip_self_eq_zero G R
  by_cases ha : a = 1
  · subst a
    simpa [degreeParityClass, O, p, b] using hO
  · have ha0 : a = 0 := zmod2_eq_zero_of_ne_one a ha
    subst a
    have hfilter := sum_one_add_bit_mul_eq_filter_zero R p b
    have hpO : (∑ v ∈ R, p v * b v) = 0 := by
      rw [sum_bit_mul_eq_filter_one]
      simpa [O] using hO
    have hleft : (∑ z ∈ R, (1 + p z) * b z) =
        (∑ z ∈ R, b z) + ∑ z ∈ R, p z * b z := by
      calc
        (∑ z ∈ R, (1 + p z) * b z) =
            ∑ z ∈ R, (b z + p z * b z) := by
              apply Finset.sum_congr rfl
              intro z hz
              ring
        _ = (∑ z ∈ R, b z) + ∑ z ∈ R, p z * b z := by
              rw [Finset.sum_add_distrib]
    rw [hleft, htotal, hpO, add_zero] at hfilter
    simpa [degreeParityClass, p, b] using hfilter.symm

omit [Fintype V] in
/-- For a fixed first opener, the XOR of the second-order debts over all
same-degree mates vanishes. -/
theorem sum_pairSecondMoment_sameDegreeMates_eq_zero
    (G : SimpleGraph V) (R : Finset V) (x : V) (hx : x ∈ R)
    (hR : (R.card : ZMod 2) = 0) :
    (∑ y ∈ sameDegreeMates G R x, pairSecondMoment G R x y) = 0 := by
  classical
  let C := degreeParityClass G R (flip G R x)
  have hxC : x ∈ C := by simp [C, degreeParityClass, hx]
  have hErase : C.erase x = sameDegreeMates G R x := by
    ext y
    simp [C, degreeParityClass, sameDegreeMates, and_assoc]
  have hclass : (∑ y ∈ C, neighborDegreeBit G R y) = 0 :=
    sum_neighborDegreeBit_degreeParityClass_eq_zero G R (flip G R x)
  have hsplit := Finset.sum_erase_add C (neighborDegreeBit G R) hxC
  rw [hclass] at hsplit
  have htail : (∑ y ∈ C.erase x, neighborDegreeBit G R y) =
      neighborDegreeBit G R x := by
    calc
      (∑ y ∈ C.erase x, neighborDegreeBit G R y) =
          ((∑ y ∈ C.erase x, neighborDegreeBit G R y) +
            neighborDegreeBit G R x) + neighborDegreeBit G R x := by
              rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = neighborDegreeBit G R x := by rw [hsplit, zero_add]
  have hcard : ((C.erase x).card : ZMod 2) = 1 := by
    have hclassCard : (C.card : ZMod 2) = 0 :=
      degreeParityClass_card_eq_zero G R (flip G R x) hR
    have hnat := Finset.card_erase_add_one hxC
    have hcast := congrArg (fun n : Nat ↦ (n : ZMod 2)) hnat
    simp only [Nat.cast_add, Nat.cast_one] at hcast
    rw [hclassCard] at hcast
    calc
      ((C.erase x).card : ZMod 2) =
          (((C.erase x).card : ZMod 2) + 1) + 1 := by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = 1 := by rw [hcast, zero_add]
  rw [← hErase]
  simp only [pairSecondMoment, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul, hcard, one_mul, htail]
  exact CharTwo.add_self_eq_zero _

omit [Fintype V] in
/-- On an even real carrier, every first opener has a distinct same-degree
mate whose second-order debt also vanishes.  Equivalently, the two vertices
have the same two-bit colour `(degree parity, odd-neighbour parity)`. -/
theorem exists_sameDegreeMate_pairSecondMoment_eq_zero
    (G : SimpleGraph V) (R : Finset V) (x : V) (hx : x ∈ R)
    (hR : (R.card : ZMod 2) = 0) :
    ∃ y ∈ sameDegreeMates G R x, pairSecondMoment G R x y = 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hall : ∀ y ∈ sameDegreeMates G R x,
      pairSecondMoment G R x y = 1 := by
    intro y hy
    exact zmod2_eq_one_of_ne_zero _ (hnone y hy)
  have hsum := sum_pairSecondMoment_sameDegreeMates_eq_zero G R x hx hR
  have hcard := sameDegreeMates_card_eq_one G R x hx hR
  have hone : (∑ y ∈ sameDegreeMates G R x,
      pairSecondMoment G R x y) = 1 := by
    calc
      (∑ y ∈ sameDegreeMates G R x, pairSecondMoment G R x y) =
          ∑ _y ∈ sameDegreeMates G R x, (1 : ZMod 2) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hall y hy
      _ = 1 := by simpa using hcard
  rw [hsum] at hone
  exact zero_ne_one hone

/-! ## Sharp third-moment hierarchy boundary -/

/-- A path on `0,…,5`, with `6` adjacent to `3,4`; labels `7,8` are
isolated.  The root pair `6,7` has zero second moment, but after `OPEN 1` its
unique `(degree,row-difference)` mate is `2`, and the new pair has unit second
moment on the residual path. -/
def thirdMomentCounterRel (x y : Fin 9) : Bool := decide (
  (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 3) ∨
  (x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 5) ∨
  (x = 3 ∧ y = 6) ∨ (x = 4 ∧ y = 6))

def thirdMomentCounterGraph : SimpleGraph (Fin 9) :=
  SimpleGraph.fromRel fun x y ↦ thirdMomentCounterRel x y = true

def thirdMomentCounterR : Finset (Fin 9) := Finset.univ.erase 8

def thirdMomentCounterS : Finset (Fin 9) :=
  (thirdMomentCounterR.erase 6).erase 7

theorem thirdMomentCounter_dummy :
    IsDummy thirdMomentCounterGraph 8 := by
  intro v
  fin_cases v <;>
    simp [thirdMomentCounterGraph, thirdMomentCounterRel,
      SimpleGraph.fromRel_adj]

theorem thirdMomentCounter_root_data :
    (6 : Fin 9) ∈ thirdMomentCounterR ∧
      (7 : Fin 9) ∈
        sameDegreeMates thirdMomentCounterGraph thirdMomentCounterR 6 ∧
      pairSecondMoment thirdMomentCounterGraph thirdMomentCounterR 6 7 = 0 := by
  norm_num [thirdMomentCounterR, sameDegreeMates, pairSecondMoment,
    neighborDegreeBit, flip, adjacencyBit, thirdMomentCounterGraph,
    thirdMomentCounterRel, SimpleGraph.fromRel_adj]
  all_goals decide

theorem thirdMomentCounter_unique_syndrome_fiber :
    bitPairFiber thirdMomentCounterS
        (fun v ↦ flip thirdMomentCounterGraph thirdMomentCounterR v)
        (frontDifference thirdMomentCounterGraph 6 7)
        (flip thirdMomentCounterGraph thirdMomentCounterR 1)
        (frontDifference thirdMomentCounterGraph 6 7 1) = {1, 2} := by
  ext v
  fin_cases v <;>
    norm_num [bitPairFiber, thirdMomentCounterS, thirdMomentCounterR,
      frontDifference, flip, adjacencyBit, thirdMomentCounterGraph,
      thirdMomentCounterRel, SimpleGraph.fromRel_adj] <;>
    decide

theorem thirdMomentCounter_new_pair_debt :
    pairSecondMoment thirdMomentCounterGraph thirdMomentCounterS 1 2 = 1 := by
  norm_num [pairSecondMoment, neighborDegreeBit, thirdMomentCounterS,
    thirdMomentCounterR, flip, adjacencyBit, thirdMomentCounterGraph,
    thirdMomentCounterRel, SimpleGraph.fromRel_adj]
  all_goals decide

/-- Even with an isolated dummy and a zero-debt root pair, the two-bit
syndrome response can be unique and necessarily create unit next-cell debt.
This is a no-go for pure OPEN/OPEN recursion, not for FIFO linking. -/
theorem thirdMomentCounter_hierarchy_boundary :
    IsDummy thirdMomentCounterGraph 8 ∧
      (7 : Fin 9) ∈
        sameDegreeMates thirdMomentCounterGraph thirdMomentCounterR 6 ∧
      pairSecondMoment thirdMomentCounterGraph thirdMomentCounterR 6 7 = 0 ∧
      bitPairFiber thirdMomentCounterS
          (fun v ↦ flip thirdMomentCounterGraph thirdMomentCounterR v)
          (frontDifference thirdMomentCounterGraph 6 7)
          (flip thirdMomentCounterGraph thirdMomentCounterR 1)
          (frontDifference thirdMomentCounterGraph 6 7 1) = {1, 2} ∧
      pairSecondMoment thirdMomentCounterGraph thirdMomentCounterS 1 2 = 1 := by
  exact ⟨thirdMomentCounter_dummy, thirdMomentCounter_root_data.2.1,
    thirdMomentCounter_root_data.2.2,
    thirdMomentCounter_unique_syndrome_fiber,
    thirdMomentCounter_new_pair_debt⟩

/-! ## CLOSE/syndrome-OPEN menu obstruction at the dummy branch -/

def phasePivotCounterRel (x y : Fin 7) : Bool := decide (
  (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 0 ∧ y = 3) ∨
  (x = 1 ∧ y = 2) ∨ (x = 1 ∧ y = 4) ∨ (x = 1 ∧ y = 5) ∨
  (x = 2 ∧ y = 3) ∨ (x = 2 ∧ y = 4) ∨
  (x = 3 ∧ y = 5) ∨ (x = 4 ∧ y = 5))

def phasePivotCounterGraph : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel fun x y ↦ phasePivotCounterRel x y = true

def phasePivotCounterR : Finset (Fin 7) := Finset.univ.erase 6

def phasePivotCounterAdj (x y : Fin 7) : Bool :=
  phasePivotCounterRel x y || phasePivotCounterRel y x

def phasePivotCounterFlip (U : Finset (Fin 7)) (v : Fin 7) : ZMod 2 :=
  ((U.filter fun w ↦ phasePivotCounterAdj v w = true).card : ZMod 2)

theorem phasePivotCounterFlip_eq_flip
    (U : Finset (Fin 7)) (v : Fin 7) :
    phasePivotCounterFlip U v = flip phasePivotCounterGraph U v := by
  classical
  simp only [phasePivotCounterFlip, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [phasePivotCounterAdj, phasePivotCounterRel,
      phasePivotCounterGraph, SimpleGraph.fromRel_adj]

def phasePivotCounterStep (s : State (Fin 7)) :
    Move (Fin 7) → Option (State (Fin 7))
  | .open v =>
      if v ∈ s.untouched then
        some {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove
          score := s.score }
      else none
  | .close =>
      match s.queue with
      | [] => none
      | f :: q =>
          if s.ko then none else
            some {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove
              score := s.score + phasePivotCounterFlip s.untouched f }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

theorem phasePivotCounterStep_eq_step
    (s : State (Fin 7)) (m : Move (Fin 7)) :
    phasePivotCounterStep s m = step phasePivotCounterGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [phasePivotCounterStep, step]
  | close =>
      cases q <;> cases ko <;> simp [phasePivotCounterStep, step,
        phasePivotCounterFlip_eq_flip]
  | pass => simp [phasePivotCounterStep, step]

def phasePivotAfterDummy : State (Fin 7) where
  untouched := {0, 3, 4, 5}
  queue := [1, 2, 6]
  ko := false
  toMove := true
  score := 0

def phasePivotAfterClose : State (Fin 7) where
  untouched := {0, 3, 4, 5}
  queue := [2, 6]
  ko := false
  toMove := false
  score := 1

def phasePivotAfterOpenZero : State (Fin 7) where
  untouched := {3, 4, 5}
  queue := [1, 2, 6, 0]
  ko := false
  toMove := false
  score := 0

theorem phasePivotCounter_openDummy :
    step phasePivotCounterGraph (afterInitialTwoOpens (1 : Fin 7) 2)
        (.open 6) = some phasePivotAfterDummy := by
  simp [step, afterInitialTwoOpens, phasePivotAfterDummy]
  ext v
  fin_cases v <;> simp

theorem phasePivotCounter_close :
    step phasePivotCounterGraph phasePivotAfterDummy .close =
      some phasePivotAfterClose := by
  norm_num [step, phasePivotAfterDummy, phasePivotAfterClose, flip,
    phasePivotCounterGraph, phasePivotCounterRel,
    SimpleGraph.fromRel_adj]
  all_goals decide

theorem phasePivotCounter_openZero :
    step phasePivotCounterGraph phasePivotAfterDummy (.open 0) =
      some phasePivotAfterOpenZero := by
  simp [step, phasePivotAfterDummy, phasePivotAfterOpenZero]

def phasePivotCounterMoves : List (Move (Fin 7)) :=
  [.open 0, .open 1, .open 2, .open 3, .open 4, .open 5, .open 6,
    .close, .pass]

theorem mem_phasePivotCounterMoves (m : Move (Fin 7)) :
    m ∈ phasePivotCounterMoves := by
  cases m with
  | «open» v => fin_cases v <;> simp [phasePivotCounterMoves]
  | close => simp [phasePivotCounterMoves]
  | pass => simp [phasePivotCounterMoves]

def phasePivotCloseWinner : Bool :=
  finiteEvenWinner phasePivotCounterMoves phasePivotCounterStep true
    (rank phasePivotAfterClose + 1) phasePivotAfterClose

def phasePivotOpenZeroWinner : Bool :=
  finiteEvenWinner phasePivotCounterMoves phasePivotCounterStep true
    (rank phasePivotAfterOpenZero + 1) phasePivotAfterOpenZero

theorem phasePivotCloseWinner_spec :
    if phasePivotCloseWinner then
      EvenWins phasePivotCounterGraph true phasePivotAfterClose
    else OddWins phasePivotCounterGraph true phasePivotAfterClose := by
  apply finiteEvenWinner_spec phasePivotCounterGraph
    phasePivotCounterMoves mem_phasePivotCounterMoves phasePivotCounterStep
    phasePivotCounterStep_eq_step true
    (rank phasePivotAfterClose + 1) phasePivotAfterClose
  omega

theorem phasePivotOpenZeroWinner_spec :
    if phasePivotOpenZeroWinner then
      EvenWins phasePivotCounterGraph true phasePivotAfterOpenZero
    else OddWins phasePivotCounterGraph true phasePivotAfterOpenZero := by
  apply finiteEvenWinner_spec phasePivotCounterGraph
    phasePivotCounterMoves mem_phasePivotCounterMoves phasePivotCounterStep
    phasePivotCounterStep_eq_step true
    (rank phasePivotAfterOpenZero + 1) phasePivotAfterOpenZero
  omega

theorem phasePivotCloseWinner_loses : phasePivotCloseWinner = false := by
  decide

theorem phasePivotOpenZeroWinner_wins :
    phasePivotOpenZeroWinner = true := by
  decide

theorem phasePivotCounter_root_data :
    (2 : Fin 7) ∈
        sameDegreeMates phasePivotCounterGraph phasePivotCounterR 1 ∧
      pairSecondMoment phasePivotCounterGraph phasePivotCounterR 1 2 = 0 ∧
      IsDummy phasePivotCounterGraph 6 := by
  constructor
  · norm_num [phasePivotCounterR, sameDegreeMates, flip,
      phasePivotCounterGraph, phasePivotCounterRel,
      SimpleGraph.fromRel_adj]
    all_goals decide
  constructor
  · norm_num [pairSecondMoment, neighborDegreeBit, phasePivotCounterR,
      flip, adjacencyBit, phasePivotCounterGraph, phasePivotCounterRel,
      SimpleGraph.fromRel_adj]
    all_goals decide
  · intro v
    fin_cases v <;>
      simp [phasePivotCounterGraph, phasePivotCounterRel,
        SimpleGraph.fromRel_adj]

theorem phasePivotCounter_dummy_syndrome_fiber_empty :
    bitPairFiber phasePivotAfterDummy.untouched
        (fun v ↦ flip phasePivotCounterGraph phasePivotCounterR v)
        (frontDifference phasePivotCounterGraph 1 2)
        (flip phasePivotCounterGraph phasePivotCounterR 6)
        (frontDifference phasePivotCounterGraph 1 2 6) = ∅ := by
  ext v
  fin_cases v <;>
    norm_num [bitPairFiber, phasePivotAfterDummy, phasePivotCounterR,
      frontDifference, flip, adjacencyBit, phasePivotCounterGraph,
      phasePivotCounterRel, SimpleGraph.fromRel_adj] <;>
    decide

/-- At this zero-debt two-bit root, attacker `OPEN dummy` leaves the even
player a winning unrestricted node, but the front CLOSE loses and there is no
syndrome-matching OPEN.  Winning replies such as `OPEN 0` lie strictly
outside the two-action menu. -/
theorem phasePivotCounter_restricted_menu_incomplete :
    EvenWins phasePivotCounterGraph true phasePivotAfterDummy ∧
      ¬EvenWins phasePivotCounterGraph true phasePivotAfterClose ∧
      bitPairFiber phasePivotAfterDummy.untouched
          (fun v ↦ flip phasePivotCounterGraph phasePivotCounterR v)
          (frontDifference phasePivotCounterGraph 1 2)
          (flip phasePivotCounterGraph phasePivotCounterR 6)
          (frontDifference phasePivotCounterGraph 1 2 6) = ∅ := by
  have hopenSpec := phasePivotOpenZeroWinner_spec
  rw [phasePivotOpenZeroWinner_wins] at hopenSpec
  have heven : EvenWins phasePivotCounterGraph true phasePivotAfterDummy :=
    EvenWins.choose phasePivotAfterDummy rfl (.open 0)
      phasePivotAfterOpenZero phasePivotCounter_openZero hopenSpec
  have hcloseSpec := phasePivotCloseWinner_spec
  rw [phasePivotCloseWinner_loses] at hcloseSpec
  exact ⟨heven,
    (oddWins_iff_not_evenWins phasePivotCounterGraph true _).mp hcloseSpec,
    phasePivotCounter_dummy_syndrome_fiber_empty⟩

/-! ### Minimal analytic dummy-branch obstruction -/

/-- Two independent matching edges `0—2`, `1—3`, plus isolated dummy `4`. -/
def dummyBreakRel (x y : Fin 5) : Bool := decide (
  (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 3))

def dummyBreakGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun x y ↦ dummyBreakRel x y = true

def dummyBreakR : Finset (Fin 5) := Finset.univ.erase 4

def dummyBreakAfterOpen : State (Fin 5) where
  untouched := {2, 3}
  queue := [0, 1, 4]
  ko := false
  toMove := true
  score := 0

def dummyBreakAfterClose : State (Fin 5) where
  untouched := {2, 3}
  queue := [1, 4]
  ko := false
  toMove := false
  score := 1

def dummyBreakAfterOpenThree : State (Fin 5) where
  untouched := {2}
  queue := [1, 4, 3]
  ko := false
  toMove := true
  score := 1

def dummyBreakAfterOpenTwo : State (Fin 5) where
  untouched := {3}
  queue := [0, 1, 4, 2]
  ko := false
  toMove := false
  score := 0

theorem dummyBreak_isMatching : IsMatchingGraph dummyBreakGraph := by
  intro v x y hvx hvy
  fin_cases v <;> fin_cases x <;> fin_cases y <;>
    simp [dummyBreakGraph, dummyBreakRel, SimpleGraph.fromRel_adj] at *

theorem dummyBreak_dummy : IsDummy dummyBreakGraph 4 := by
  intro v
  fin_cases v <;>
    simp [dummyBreakGraph, dummyBreakRel, SimpleGraph.fromRel_adj]

theorem dummyBreak_root_data :
    (1 : Fin 5) ∈ sameDegreeMates dummyBreakGraph dummyBreakR 0 ∧
      pairSecondMoment dummyBreakGraph dummyBreakR 0 1 = 0 := by
  constructor
  · norm_num [dummyBreakR, sameDegreeMates, flip, dummyBreakGraph,
      dummyBreakRel, SimpleGraph.fromRel_adj]
    all_goals decide
  · norm_num [pairSecondMoment, neighborDegreeBit, dummyBreakR, flip,
      adjacencyBit, dummyBreakGraph, dummyBreakRel,
      SimpleGraph.fromRel_adj]
    all_goals decide

theorem dummyBreak_openDummy :
    step dummyBreakGraph (afterInitialTwoOpens (0 : Fin 5) 1) (.open 4) =
      some dummyBreakAfterOpen := by
  simp [step, afterInitialTwoOpens, dummyBreakAfterOpen]
  ext v
  fin_cases v <;> simp

theorem dummyBreak_close :
    step dummyBreakGraph dummyBreakAfterOpen .close =
      some dummyBreakAfterClose := by
  norm_num [step, dummyBreakAfterOpen, dummyBreakAfterClose, flip,
    dummyBreakGraph, dummyBreakRel, SimpleGraph.fromRel_adj]
  all_goals decide

theorem dummyBreak_openThree :
    step dummyBreakGraph dummyBreakAfterClose (.open 3) =
      some dummyBreakAfterOpenThree := by
  simp [step, dummyBreakAfterClose, dummyBreakAfterOpenThree]
  ext v
  fin_cases v <;> simp

theorem dummyBreak_openTwo :
    step dummyBreakGraph dummyBreakAfterOpen (.open 2) =
      some dummyBreakAfterOpenTwo := by
  simp [step, dummyBreakAfterOpen, dummyBreakAfterOpenTwo]

theorem dummyBreak_afterOpenThree_noLiveCut :
    NoLiveCut dummyBreakGraph dummyBreakAfterOpenThree := by
  intro u hu v hv
  fin_cases u <;> fin_cases v <;>
    simp [dummyBreakAfterOpenThree, liveSet, dummyBreakGraph,
      dummyBreakRel, SimpleGraph.fromRel_adj] at *

theorem dummyBreak_close_loses :
    ¬EvenWins dummyBreakGraph true dummyBreakAfterClose := by
  have htrap : OddWins dummyBreakGraph true dummyBreakAfterOpenThree :=
    oddWins_of_noLiveCut true dummyBreakAfterOpenThree
      dummyBreak_afterOpenThree_noLiveCut (by decide)
  have hodd : OddWins dummyBreakGraph true dummyBreakAfterClose :=
    OddWins.choose dummyBreakAfterClose (by decide) (.open 3)
      dummyBreakAfterOpenThree dummyBreak_openThree htrap
  exact (oddWins_iff_not_evenWins dummyBreakGraph true _).mp hodd

theorem dummyBreak_openTwo_wins :
    EvenWins dummyBreakGraph true dummyBreakAfterOpenTwo := by
  apply evenWins_of_matching dummyBreak_isMatching true
  · rfl
  · norm_num [MatchingFrontSafe, flip, dummyBreakAfterOpenTwo,
      dummyBreakGraph, dummyBreakRel, SimpleGraph.fromRel_adj]
    all_goals decide

theorem dummyBreak_afterOpen_wins :
    EvenWins dummyBreakGraph true dummyBreakAfterOpen := by
  exact EvenWins.choose dummyBreakAfterOpen rfl (.open 2)
    dummyBreakAfterOpenTwo dummyBreak_openTwo dummyBreak_openTwo_wins

theorem dummyBreak_syndrome_fiber_empty :
    bitPairFiber dummyBreakAfterOpen.untouched
        (fun v ↦ flip dummyBreakGraph dummyBreakR v)
        (frontDifference dummyBreakGraph 0 1)
        (flip dummyBreakGraph dummyBreakR 4)
        (frontDifference dummyBreakGraph 0 1 4) = ∅ := by
  ext v
  fin_cases v <;>
    norm_num [bitPairFiber, dummyBreakAfterOpen, dummyBreakR,
      frontDifference, flip, adjacencyBit, dummyBreakGraph,
      dummyBreakRel, SimpleGraph.fromRel_adj] <;>
    decide

theorem dummyBreak_zeroDifference_fiber_empty :
    (dummyBreakAfterOpen.untouched.filter fun v ↦
      frontDifference dummyBreakGraph 0 1 v = 0) = ∅ := by
  ext v
  fin_cases v <;>
    norm_num [dummyBreakAfterOpen, frontDifference, adjacencyBit,
      dummyBreakGraph, dummyBreakRel, SimpleGraph.fromRel_adj] <;>
    decide

/-- The smallest analytic menu obstruction.  The board is a matching, so
`OPEN 2` wins by the universal matching strategy.  The only front CLOSE
enters a no-live-cut odd trap, while no real vertex even preserves the old
front difference, let alone the full syndrome. -/
theorem dummyBreak_restricted_menu_incomplete :
    IsDummy dummyBreakGraph 4 ∧
      pairSecondMoment dummyBreakGraph dummyBreakR 0 1 = 0 ∧
      EvenWins dummyBreakGraph true dummyBreakAfterOpen ∧
      ¬EvenWins dummyBreakGraph true dummyBreakAfterClose ∧
      (dummyBreakAfterOpen.untouched.filter fun v ↦
        frontDifference dummyBreakGraph 0 1 v = 0) = ∅ := by
  exact ⟨dummyBreak_dummy, dummyBreak_root_data.2,
    dummyBreak_afterOpen_wins, dummyBreak_close_loses,
    dummyBreak_zeroDifference_fiber_empty⟩

/-! ### Positive fixed-front phase pivot -/

omit [Fintype V] in
/-- Fixed-front phase pivot.  Either the front is already neutral and may be
closed now, or a unit adjacency coordinate can be opened so that its next
CLOSE is neutral.  This is the precise CLOSE/OPEN dichotomy; an OPEN-only
version is false when the current zero charge is supported on an even set of
unit coordinates. -/
theorem fixedFront_close_or_open_clear
    (G : SimpleGraph V) (S : Finset V) (x : V) :
    flip G S x = 0 ∨ ∃ w ∈ S, flip G (S.erase w) x = 0 := by
  classical
  by_cases hzero : flip G S x = 0
  · exact Or.inl hzero
  · right
    have hone : flip G S x = 1 := zmod2_eq_one_of_ne_zero _ hzero
    have hvalue : closureValue (adjacencyBit G x) S = 1 := by
      simpa [closureValue] using
        (flip_eq_sum_adjacencyBit G S x).symm.trans hone
    obtain ⟨w, hw, hbit⟩ :=
      exists_weight_one_of_closureValue_eq_one (adjacencyBit G x) hvalue
    refine ⟨w, hw, ?_⟩
    rw [flip_erase_eq_add hw, hone, hbit]
    exact CharTwo.add_self_eq_zero 1

/-- Public state after the attacker opens the dummy behind a queued pair. -/
def dummyOpenedPairState (S : Finset V) (x y d : V)
    (defender : Bool) (score : ZMod 2) : State V where
  untouched := S
  queue := [x, y, d]
  ko := false
  toMove := defender
  score := score

/-- Endpoint when the defender directly closes an already-neutral front. -/
def fixedFrontDirectCloseState (S : Finset V) (y d : V)
    (defender : Bool) (score : ZMod 2) : State V where
  untouched := S
  queue := [y, d]
  ko := false
  toMove := !defender
  score := score

/-- Endpoint after the defender opens `w` and the attacker immediately
closes the now-neutral fixed front `x`. -/
def fixedFrontPivotTailState (S : Finset V) (y d w : V)
    (defender : Bool) (score : ZMod 2) : State V where
  untouched := S.erase w
  queue := [y, d, w]
  ko := false
  toMove := defender
  score := score

omit [Fintype V] in
/-- Exact operational dummy-phase pivot.  From the dummy-opened pair state,
the defender can OPEN a real `w` so that an immediate attacker CLOSE of the
old front is neutral and returns control to the defender at the displayed
three-cell tail. -/
theorem dummyOpenedPair_has_fixedFrontPivot
    (G : SimpleGraph V) (S : Finset V) (x y d : V)
    (defender : Bool) (score : ZMod 2) :
    step G (dummyOpenedPairState S x y d defender score) .close =
        some (fixedFrontDirectCloseState S y d defender score) ∨
      ∃ w middle,
        w ∈ S ∧
        step G (dummyOpenedPairState S x y d defender score) (.open w) =
          some middle ∧
        step G middle .close =
          some (fixedFrontPivotTailState S y d w defender score) := by
  rcases fixedFront_close_or_open_clear G S x with hclear | ⟨w, hw, hclear⟩
  · left
    simp [step, dummyOpenedPairState, fixedFrontDirectCloseState, hclear]
  · right
    let middle : State V := {
      untouched := S.erase w
      queue := [x, y, d, w]
      ko := false
      toMove := !defender
      score := score }
    refine ⟨w, middle, hw, ?_, ?_⟩
    · simp [step, dummyOpenedPairState, middle, hw]
    · simp [step, middle, fixedFrontPivotTailState, hclear]

/-! ### The complete dummy-phase fan and the continuation-coset boundary -/

omit [Fintype V] in
/-- On an even real board, the defender fan at `[x,y,d]` consists of one
front CLOSE and one OPEN for each remaining real vertex, hence is odd. -/
theorem dummyOpenedPair_complete_fan_card_odd
    (R : Finset V) (x y : V) (hx : x ∈ R) (hy : y ∈ R)
    (hxy : x ≠ y) (hR : R.card % 2 = 0) :
    (1 + ((R.erase x).erase y).card) % 2 = 1 := by
  have hyErase : y ∈ R.erase x := by simp [hy, Ne.symm hxy]
  have hxcard := Finset.card_erase_add_one hx
  have hycard := Finset.card_erase_add_one hyErase
  omega

omit [Fintype V] in
/-- The universal live-star prefix of the complete `[x,y,d]` defender fan
vanishes: the CLOSE contributes zero, while the OPEN stars sum to the
three-OPEN ancestry prefix. -/
theorem dummyOpenedPair_complete_fan_prefix_zero
    (R : Finset V) (d x y : V) (hdR : d ∉ R)
    (hx : x ∈ R) (hy : y ∈ R) (hxy : x ≠ y) :
    liveStarVector (insert d R) x +
        liveStarVector (insert d R) y +
        liveStarVector (insert d R) d +
        ∑ w ∈ (R.erase x).erase y,
          liveStarVector (insert d R) w = 0 := by
  have hyErase : y ∈ R.erase x := by simp [hy, Ne.symm hxy]
  have hsplit :
      liveStarVector (insert d R) x +
          liveStarVector (insert d R) y +
          ∑ w ∈ (R.erase x).erase y,
            liveStarVector (insert d R) w =
        ∑ w ∈ R, liveStarVector (insert d R) w := by
    rw [← Finset.sum_erase_add _ _ hx]
    rw [← Finset.sum_erase_add _ _ hyErase]
    abel
  calc
    liveStarVector (insert d R) x +
          liveStarVector (insert d R) y +
          liveStarVector (insert d R) d +
          ∑ w ∈ (R.erase x).erase y,
            liveStarVector (insert d R) w =
        liveStarVector (insert d R) d +
          (liveStarVector (insert d R) x +
            liveStarVector (insert d R) y +
            ∑ w ∈ (R.erase x).erase y,
              liveStarVector (insert d R) w) := by abel
    _ = liveStarVector (insert d R) d +
          ∑ w ∈ R, liveStarVector (insert d R) w := by rw [hsplit]
    _ = 0 := by
      have htotal := sum_liveStarVector_eq_zero (insert d R)
      rw [Finset.sum_insert hdR] at htotal
      exact htotal

omit [Fintype V] [DecidableEq V] in
/-- A balanced dummy-opened pair has zero queue-cut potential at score zero.
This is the scalar hypothesis needed to turn a zero response moment into a
contradiction. -/
theorem dummyOpenedPair_potential_eq_zero
    (G : SimpleGraph V) (S : Finset V) (d x y : V)
    (hd : IsDummy G d) (hbalanced : flip G S x = flip G S y) :
    potential G (dummyOpenedPairState S x y d true 0) = 0 := by
  rw [potential]
  simp only [dummyOpenedPairState, queueCut, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, zero_add]
  rw [flip_dummy hd, hbalanced]
  simpa [two_nsmul] using CharTwo.add_self_eq_zero (flip G S y)

omit [Fintype V] in
/-- Exact reduction of a hypothetical all-odd dummy-phase defender fan to
the already isolated continuation factor equation.  An odd family of child
continuation points contradicts the parent odd strategy precisely when its
aggregate cancels the (here zero) universal move prefix.  This theorem does
not construct that aggregate identity. -/
theorem dummyOpenedPair_factor_extension_contradiction
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (hsWF : WellFormed s)
    (hpot : potential G s = 0)
    {hseat : s.toMove = seat}
    {hasMove : ∃ m u, step G s m = some u}
    {children : ∀ m u, step G s m = some u → OddStrategy G seat u}
    {I : Type*} (is : List I) (m : I → Move V) (t : I → State V)
    (hstep : ∀ i ∈ is, step G s (m i) = some (t i))
    (a dvec : I → EdgeVector V)
    (ha : ∀ i (hi : i ∈ is), AffineResponseMoment G seat
      (children (m i) (t i) (hstep i hi)) (a i))
    (hd : ∀ i (hi : i ∈ is), ResponseDirection G seat
      (children (m i) (t i) (hstep i hi)) (dvec i))
    (hodd : is.length % 2 = 1)
    (hfactor : (is.map fun i ↦ moveLiveStar s (m i) + a i).sum =
      (is.map dvec).sum) : False := by
  let parent := OddStrategy.answer s hseat hasMove children
  have hzero : AffineResponseMoment G seat parent 0 :=
    AffineResponseMoment.answer_factor_extension
      is m t hstep a dvec ha hd hodd hfactor
  have heval := hzero.graphEvaluation_eq
    hsWF
  change (0 : ZMod 2) = 1 + potential G s at heval
  have : (1 : ZMod 2) = 0 := by
    rw [hpot, add_zero] at heval
    exact heval.symm
  exact one_ne_zero this

/-! ## Sharp failure of the universal balanced-pair conjecture -/

/-- A six-real graph with isolated dummy `6`.  The ordered pair `0,4` has
equal full-board degree parity, but is not winning for the physical second
seat. -/
def pairGaussianCounterRel (x y : Fin 7) : Bool := decide (
  (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 0 ∧ y = 5) ∨
  (x = 1 ∧ y = 5) ∨ (x = 2 ∧ y = 4) ∨ (x = 2 ∧ y = 5))

def pairGaussianCounterGraph : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel fun x y ↦ pairGaussianCounterRel x y = true

def pairGaussianCounterAdj (x y : Fin 7) : Bool :=
  pairGaussianCounterRel x y || pairGaussianCounterRel y x

def pairGaussianCounterFlip (U : Finset (Fin 7)) (v : Fin 7) : ZMod 2 :=
  ((U.filter fun w ↦ pairGaussianCounterAdj v w = true).card : ZMod 2)

theorem pairGaussianCounterFlip_eq_flip
    (U : Finset (Fin 7)) (v : Fin 7) :
    pairGaussianCounterFlip U v = flip pairGaussianCounterGraph U v := by
  classical
  simp only [pairGaussianCounterFlip, flip]
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply congrArg Finset.card
  ext w
  fin_cases v <;> fin_cases w <;>
    simp [pairGaussianCounterAdj, pairGaussianCounterRel,
      pairGaussianCounterGraph, SimpleGraph.fromRel_adj]

def pairGaussianCounterStep (s : State (Fin 7)) :
    Move (Fin 7) → Option (State (Fin 7))
  | .open v =>
      if v ∈ s.untouched then
        some {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove
          score := s.score }
      else none
  | .close =>
      match s.queue with
      | [] => none
      | f :: q =>
          if s.ko then none else
            some {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove
              score := s.score +
                pairGaussianCounterFlip s.untouched f }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

theorem pairGaussianCounterStep_eq_step
    (s : State (Fin 7)) (m : Move (Fin 7)) :
    pairGaussianCounterStep s m = step pairGaussianCounterGraph s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [pairGaussianCounterStep, step]
  | close =>
      cases q <;> cases ko <;> simp [pairGaussianCounterStep, step,
        pairGaussianCounterFlip_eq_flip]
  | pass => simp [pairGaussianCounterStep, step]

def pairGaussianCounterMoves : List (Move (Fin 7)) :=
  [.open 0, .open 1, .open 2, .open 3, .open 4, .open 5, .open 6,
    .close, .pass]

theorem mem_pairGaussianCounterMoves (m : Move (Fin 7)) :
    m ∈ pairGaussianCounterMoves := by
  cases m with
  | «open» v => fin_cases v <;> simp [pairGaussianCounterMoves]
  | close => simp [pairGaussianCounterMoves]
  | pass => simp [pairGaussianCounterMoves]

def pairGaussianAfterOpenFive : State (Fin 7) where
  untouched := {1, 2, 3, 6}
  queue := [0, 4, 5]
  ko := false
  toMove := true
  score := 0

theorem pairGaussianCounter_openFive :
    step pairGaussianCounterGraph
        (afterInitialTwoOpens (0 : Fin 7) 4) (.open 5) =
      some pairGaussianAfterOpenFive := by
  simp [step, afterInitialTwoOpens, pairGaussianAfterOpenFive]
  ext x
  fin_cases x <;> simp

def pairGaussianCounterWinner : Bool :=
  finiteEvenWinner pairGaussianCounterMoves pairGaussianCounterStep true
    (rank pairGaussianAfterOpenFive + 1) pairGaussianAfterOpenFive

theorem pairGaussianCounterWinner_spec :
    if pairGaussianCounterWinner then
      EvenWins pairGaussianCounterGraph true pairGaussianAfterOpenFive
    else
      OddWins pairGaussianCounterGraph true pairGaussianAfterOpenFive := by
  apply finiteEvenWinner_spec pairGaussianCounterGraph
    pairGaussianCounterMoves mem_pairGaussianCounterMoves
    pairGaussianCounterStep pairGaussianCounterStep_eq_step true
    (rank pairGaussianAfterOpenFive + 1) pairGaussianAfterOpenFive
  omega

theorem pairGaussianCounterGraph_dummy :
    IsDummy pairGaussianCounterGraph 6 := by
  intro v
  fin_cases v <;>
    simp [pairGaussianCounterGraph, pairGaussianCounterRel,
      SimpleGraph.fromRel_adj]

theorem pairGaussianCounter_equal_full_degree :
    flip pairGaussianCounterGraph Finset.univ 0 =
      flip pairGaussianCounterGraph Finset.univ 4 := by
  norm_num [flip, pairGaussianCounterGraph, pairGaussianCounterRel,
    SimpleGraph.fromRel_adj]
  all_goals decide

theorem pairGaussianCounterWinner_loses :
    pairGaussianCounterWinner = false := by decide

/-- Equal full-degree parity of the initial ordered fronts does not make the
pair state universally winning for the second physical seat.  This refutes
the proposed pair-state theorem, not FIFO linking at the initial root. -/
theorem not_evenWins_true_pairGaussianCounter :
    ¬EvenWins pairGaussianCounterGraph true
      (afterInitialTwoOpens (0 : Fin 7) 4) := by
  have hspec := pairGaussianCounterWinner_spec
  rw [pairGaussianCounterWinner_loses] at hspec
  have hrootOdd : OddWins pairGaussianCounterGraph true
      (afterInitialTwoOpens (0 : Fin 7) 4) :=
    OddWins.choose (afterInitialTwoOpens (0 : Fin 7) 4) (by decide)
      (.open 5) pairGaussianAfterOpenFive
      pairGaussianCounter_openFive hspec
  exact (oddWins_iff_not_evenWins pairGaussianCounterGraph true _).mp hrootOdd

end

end Ogdoad.Fifo
