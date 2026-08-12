import Ogdoad.FifoCrossExitIncidence

/-!
# The complete real root fan

After a real first `OPEN`, all real second `OPEN` replies form an odd family
when the real board has even order.  Their universal live-star prefixes,
together with the first `OPEN` star, vanish after forgetting coordinates
incident to the isolated dummy.  Thus the outer least-root fan has no
remaining prefix defect: its exact obstruction is the sum of the child
continuation points.  Strategy-relative convolution further identifies that
outer point, modulo a lifted response direction, with the protected dummy
child.  Thus the full outer fan exposes the post-dummy `B'` class rather than
contracting it.

This module proves only the graph-independent prefix identity.  It does not
assert that the continuation sum vanishes; that is the strategy-relative
outer-corridor incidence theorem still required for FIFO linking.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- On an even real board, deleting the first opener leaves an odd family of
real second-OPEN replies. -/
theorem real_open_replies_card_eq_one
    (R : Finset V) (x : V) (hxR : x ∈ R)
    (hR : (R.card : ZMod 2) = 0) :
    (((R.erase x).card : Nat) : ZMod 2) = 1 := by
  have hcard := Finset.card_erase_add_one hxR
  have hcast := congrArg (fun n : Nat ↦ (n : ZMod 2)) hcard
  simp only [Nat.cast_add, Nat.cast_one] at hcast
  rw [hR] at hcast
  calc
    (((R.erase x).card : Nat) : ZMod 2) =
        ((((R.erase x).card : Nat) : ZMod 2) + 1) + 1 := by
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [hcast, zero_add]

omit [Fintype V] in
/-- Natural-number parity form used by the root-fan list enumeration. -/
theorem real_open_replies_card_mod_two
    (R : Finset V) (x : V) (hxR : x ∈ R)
    (hR : R.card % 2 = 0) :
    (R.erase x).card % 2 = 1 := by
  have hcard := Finset.card_erase_add_one hxR
  omega

omit [Fintype V] [DecidableEq V] in
private theorem list_sum_map_add {I : Type*} (is : List I)
    (f g : I → EdgeVector V) :
    (is.map fun i ↦ f i + g i).sum =
      (is.map f).sum + (is.map g).sum := by
  induction is with
  | nil => simp
  | cons i rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      abel

omit [Fintype V] in
private theorem list_sum_eq_finset_sum (is : List V) (his : is.Nodup)
    (f : V → EdgeVector V) :
    (is.map f).sum = ∑ v ∈ is.toFinset, f v := by
  induction is with
  | nil => simp
  | cons v rest ih =>
      have hv : v ∉ rest := (List.nodup_cons.mp his).1
      have hrest : rest.Nodup := (List.nodup_cons.mp his).2
      simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
      rw [Finset.sum_insert (by simpa using hv), ih hrest]

omit [Fintype V] in
/-- The sum of all complete-graph live stars on one finite carrier is zero:
every unordered off-diagonal coordinate occurs once from each endpoint. -/
theorem sum_liveStarVector_eq_zero (L : Finset V) :
    ∑ v ∈ L, liveStarVector L v = 0 := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | @insert a L ha ih =>
      let edgeA : V → EdgeVector V :=
        fun v ↦ Finsupp.single s(a, v) 1
      have hcenter :
          liveStarVector (insert a L) a = liveStarVector L a := by
        rw [liveStarVector, liveStarVector]
        rw [Finset.erase_insert ha, Finset.erase_eq_self.mpr ha]
      rw [Finset.sum_insert ha, hcenter]
      have hchange :
          (∑ v ∈ L, liveStarVector (insert a L) v) =
            ∑ v ∈ L, (liveStarVector L v + edgeA v) := by
        apply Finset.sum_congr rfl
        intro v hv
        have hav : a ≠ v := by
          intro h
          subst v
          exact ha hv
        have h := liveStarVector_insert_cancel L a v ha hav
        rw [add_comm] at h
        ext e
        have he := congrArg (fun q : EdgeVector V ↦ q e) h
        simp only [Finsupp.add_apply] at he ⊢
        calc
          (liveStarVector (insert a L) v) e =
              (liveStarVector L v) e +
                ((liveStarVector L v) e +
                  (liveStarVector (insert a L) v) e) := by
                    symm
                    calc
                      (liveStarVector L v) e +
                          ((liveStarVector L v) e +
                            (liveStarVector (insert a L) v) e) =
                          ((liveStarVector L v) e +
                            (liveStarVector L v) e) +
                              (liveStarVector (insert a L) v) e := by abel
                      _ = (liveStarVector (insert a L) v) e := by
                        rw [CharTwo.add_self_eq_zero, zero_add]
          _ = (liveStarVector L v) e + edgeA v e := by
                rw [add_comm ((liveStarVector L v) e)
                  ((liveStarVector (insert a L) v) e), he]
      rw [hchange, Finset.sum_add_distrib, ih, zero_add]
      rw [liveStarVector, Finset.erase_eq_self.mpr ha]
      change (∑ w ∈ L, edgeA w) + ∑ v ∈ L, edgeA v = 0
      ext e
      simp only [Finsupp.add_apply]
      rw [CharTwo.add_self_eq_zero]
      simp

omit [Fintype V] in
/-- A live star centred at the distinguished dummy vanishes in the real-edge
quotient, without any graph hypothesis. -/
theorem realEdgeProjection_liveStarVector_dummy
    (d : V) (L : Finset V) :
    realEdgeProjection d (liveStarVector L d) = 0 := by
  rw [liveStarVector, map_sum]
  apply Finset.sum_eq_zero
  intro v _hv
  exact realEdgeProjection_dummy_single d v 1

omit [Fintype V] in
/-- Exact outer-fan prefix cancellation.  The first real `OPEN x` followed by
the odd family of all other real `OPEN` replies has zero universal moment
after dummy-edge projection. -/
theorem real_root_open_fan_prefix_zero
    (R : Finset V) (d x : V) (hdR : d ∉ R) (hxR : x ∈ R) :
    realEdgeProjection d
      (liveStarVector (insert d R) x +
        ∑ y ∈ R.erase x, liveStarVector (insert d R) y) = 0 := by
  have hRsum :
      liveStarVector (insert d R) x +
          ∑ y ∈ R.erase x, liveStarVector (insert d R) y =
        ∑ y ∈ R, liveStarVector (insert d R) y := by
    rw [← Finset.sum_erase_add _ _ hxR]
    exact add_comm _ _
  rw [hRsum]
  have htotal := sum_liveStarVector_eq_zero (insert d R)
  rw [Finset.sum_insert hdR] at htotal
  have hreal :
      (∑ y ∈ R, liveStarVector (insert d R) y) =
        liveStarVector (insert d R) d := by
    calc
      (∑ y ∈ R, liveStarVector (insert d R) y) =
          (liveStarVector (insert d R) d +
              liveStarVector (insert d R) d) +
            ∑ y ∈ R, liveStarVector (insert d R) y := by
              ext e
              simp only [Finsupp.add_apply]
              symm
              rw [CharTwo.add_self_eq_zero, zero_add]
      _ = liveStarVector (insert d R) d +
          (liveStarVector (insert d R) d +
            ∑ y ∈ R, liveStarVector (insert d R) y) := by abel
      _ = liveStarVector (insert d R) d := by rw [htotal, add_zero]
  rw [hreal, realEdgeProjection_liveStarVector_dummy]

omit [Fintype V] in
/-- Strategy-relative outer-fan comparison with the correct root ancestry.

The post-`O_x` defender node has live carrier `insert d R`, but its real
legal replies enumerate exactly `R.erase x`: the queued opener `x` is live
but cannot be opened again.  Their odd convolution is one affine point of
the defender strategy.  The singleton `O_d` child is another.  Their sum is
therefore a homogeneous response direction, and the direction lifts through
the common `O_x` ancestry to the fixed root.

The final two equalities expose the projected representatives.  The real
point loses its entire `O_x`-plus-real-fan prefix, while the dummy point loses
only the dummy star.  No conclusion says that either point is zero. -/
theorem StrategyPrefix.root_real_fan_diff_dummy_direction
    {G : SimpleGraph V} {seat : Bool} {root s td : State V}
    {hroot : OddStrategy G seat root}
    {hseat : s.toMove = seat}
    {hasMove : ∃ m u, step G s m = some u}
    {hchildren : ∀ m u, step G s m = some u → OddStrategy G seat u}
    {p : EdgeVector V}
    (hp : StrategyPrefix G seat hroot
      (OddStrategy.answer s hseat hasMove hchildren) p)
    (R : Finset V) (d x : V) (hdR : d ∉ R) (hxR : x ∈ R)
    (hR : R.card % 2 = 0)
    (is : List V) (his : is.Nodup) (hset : is.toFinset = R.erase x)
    (t : V → State V)
    (hstep : ∀ v ∈ is, step G s (.open v) = some (t v))
    (a : V → EdgeVector V)
    (ha : ∀ v (hv : v ∈ is), AffineResponseMoment G seat
      (hchildren (.open v) (t v) (hstep v hv)) (a v))
    (hstepd : step G s (.open d) = some td)
    (ad : EdgeVector V)
    (had : AffineResponseMoment G seat
      (hchildren (.open d) td hstepd) ad)
    (hlive : liveSet s = insert d R)
    (hpRoot : p = liveStarVector (insert d R) x) :
    let realPoint :=
      (is.map fun v ↦ moveLiveStar s (.open v) + a v).sum
    let dummyPoint := moveLiveStar s (.open d) + ad
    AffineResponseMoment G seat
        (OddStrategy.answer s hseat hasMove hchildren) realPoint ∧
      AffineResponseMoment G seat
        (OddStrategy.answer s hseat hasMove hchildren) dummyPoint ∧
      ResponseDirection G seat
        (OddStrategy.answer s hseat hasMove hchildren)
          (realPoint + dummyPoint) ∧
      ResponseDirection G seat hroot (realPoint + dummyPoint) ∧
      realEdgeProjection d (p + realPoint) =
        realEdgeProjection d (is.map a).sum ∧
      realEdgeProjection d (p + dummyPoint) =
        realEdgeProjection d (p + ad) := by
  dsimp only
  have hlen : is.length = (R.erase x).card := by
    rw [← List.toFinset_card_of_nodup his, hset]
  have hoddFin := real_open_replies_card_mod_two R x hxR hR
  have hodd : is.length % 2 = 1 := by omega
  have hrealMem : ∀ z ∈
      (is.map fun v ↦ moveLiveStar s (.open v) + a v),
      AffineResponseMoment G seat
        (OddStrategy.answer s hseat hasMove hchildren) z := by
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact AffineResponseMoment.answerChild
      (hstep := hstep v hv) (ha v hv)
  have hreal : AffineResponseMoment G seat
      (OddStrategy.answer s hseat hasMove hchildren)
      (is.map fun v ↦ moveLiveStar s (.open v) + a v).sum := by
    apply AffineResponseMoment.odd_list_sum _
    · simpa using hodd
    · exact hrealMem
  have hdummy : AffineResponseMoment G seat
      (OddStrategy.answer s hseat hasMove hchildren)
      (moveLiveStar s (.open d) + ad) :=
    AffineResponseMoment.answerChild (hstep := hstepd) had
  have hdir : ResponseDirection G seat
      (OddStrategy.answer s hseat hasMove hchildren)
      ((is.map fun v ↦ moveLiveStar s (.open v) + a v).sum +
        (moveLiveStar s (.open d) + ad)) :=
    ⟨_, _, hreal, hdummy, rfl⟩
  have hrootDir := hp.lift_direction hdir
  have hpfxEq :
      (is.map fun v ↦ moveLiveStar s (.open v)).sum =
        ∑ v ∈ R.erase x, liveStarVector (insert d R) v := by
    simp only [moveLiveStar, hlive]
    rw [list_sum_eq_finset_sum is his]
    rw [hset]
  have hpfx :
      realEdgeProjection d
        (p + (is.map fun v ↦ moveLiveStar s (.open v)).sum) = 0 := by
    rw [hpRoot, hpfxEq]
    exact real_root_open_fan_prefix_zero R d x hdR hxR
  have hrealDecomp :
      (is.map fun v ↦ moveLiveStar s (.open v) + a v).sum =
        (is.map fun v ↦ moveLiveStar s (.open v)).sum +
          (is.map a).sum :=
    list_sum_map_add is (fun v ↦ moveLiveStar s (.open v)) a
  have hrealProj :
      realEdgeProjection d
          (p + (is.map fun v ↦ moveLiveStar s (.open v) + a v).sum) =
        realEdgeProjection d (is.map a).sum := by
    rw [hrealDecomp, ← add_assoc, map_add, hpfx, zero_add]
  have hdummyProj :
      realEdgeProjection d (p + (moveLiveStar s (.open d) + ad)) =
        realEdgeProjection d (p + ad) := by
    simp only [moveLiveStar]
    rw [hlive]
    have hdstar := realEdgeProjection_liveStarVector_dummy d (insert d R)
    simp only [map_add, hdstar, zero_add]
  exact ⟨hreal, hdummy, hdir, hrootDir, hrealProj, hdummyProj⟩

end

end Ogdoad.Fifo
