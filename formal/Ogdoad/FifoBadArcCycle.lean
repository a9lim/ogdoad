import Ogdoad.FifoCrossExitIncidence

/-!
# The bad-arc cycle prefix and its augmentation obstruction

At a first-seat counterstrategy, every first `OPEN x` is present at the root
defender node and the strategy selects a second `OPEN f(x)`.  A directed cycle
of this selected-reply map has a genuine common ancestry.  Since an OPEN does
not change the live carrier, the two-OPEN prefix on an arc `x -> y` is the sum
of the two live stars at that common carrier.

This file records the exact consequence.  On any balanced directed list (in
particular, a directed cycle), all two-OPEN prefixes cancel.  This does not
contract an odd counterstrategy: an odd balanced family leaves a continuation
sum with nonzero real-edge projection, while an even balanced family leaves a
homogeneous response direction.  Thus the common-root cycle observation is
real, but continuation-coset coupling remains necessary.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The universal two-OPEN prefix attached to an oriented arc.  At an actual
root pair both stars use the full live carrier, because OPEN preserves that
carrier. -/
def twoOpenArcPrefix (L : Finset V) (e : V × V) : EdgeVector V :=
  liveStarVector L e.1 + liveStarVector L e.2

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

omit [Fintype V] [DecidableEq V] in
private theorem List.Perm.sum_eq {xs ys : List (EdgeVector V)}
    (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons x h ih => simp [ih]
  | swap x y l => exact add_left_comm y x l.sum
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [Fintype V] in
/-- Every balanced directed list has zero aggregate two-OPEN prefix.  The
balance hypothesis says that its source list is a permutation of its target
list; a directed cycle is the basic example. -/
theorem sum_twoOpenArcPrefix_eq_zero_of_balanced
    (L : Finset V) (arcs : List (V × V))
    (hbalanced : (arcs.map Prod.fst).Perm (arcs.map Prod.snd)) :
    (arcs.map (twoOpenArcPrefix L)).sum = 0 := by
  change (arcs.map fun e ↦
    liveStarVector L e.1 + liveStarVector L e.2).sum = 0
  rw [list_sum_map_add arcs
    (fun e ↦ liveStarVector L e.1)
    (fun e ↦ liveStarVector L e.2)]
  have hperm :
      (arcs.map fun e ↦ liveStarVector L e.1).Perm
        (arcs.map fun e ↦ liveStarVector L e.2) := by
    simpa only [List.map_map, Function.comp_def] using
      hbalanced.map (liveStarVector L)
  rw [hperm.sum_eq]
  ext e
  exact CharTwo.add_self_eq_zero _

/-- An odd balanced common-root family cannot make its continuation sum
vanish after isolated-dummy projection.  The balanced prefix cancels, but the
odd family is still an affine response point, and the augmentation lock
forbids projected zero. -/
theorem odd_balanced_arc_continuations_projection_ne_zero
    {G : SimpleGraph V} {d : V} {seat : Bool}
    {hroot : OddStrategy G seat (initial (V := V))}
    (hdummy : IsDummy G d) (L : Finset V) (arcs : List (V × V))
    (hbalanced : (arcs.map Prod.fst).Perm (arcs.map Prod.snd))
    (hodd : arcs.length % 2 = 1)
    (continuation : V × V → EdgeVector V)
    (hpoint : ∀ a ∈ arcs, AffineResponseMoment G seat hroot
      (twoOpenArcPrefix L a + continuation a)) :
    realEdgeProjection d (arcs.map continuation).sum ≠ 0 := by
  intro hzero
  let points := arcs.map fun a ↦
    twoOpenArcPrefix L a + continuation a
  have hpoints : ∀ z ∈ points,
      AffineResponseMoment G seat hroot z := by
    intro z hz
    simp only [points, List.mem_map] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact hpoint a ha
  have hdecomp : points.sum =
      (arcs.map (twoOpenArcPrefix L)).sum +
        (arcs.map continuation).sum := by
    simpa only [points] using list_sum_map_add arcs
      (twoOpenArcPrefix L) continuation
  have hpointsZero : realEdgeProjection d points.sum = 0 := by
    rw [hdecomp, sum_twoOpenArcPrefix_eq_zero_of_balanced L arcs hbalanced,
      zero_add, hzero]
  have heven := projected_decorated_balance_card_even hdummy points []
    hpoints (by simp) (by simpa using hpointsZero)
  have hlen : points.length = arcs.length := by simp [points]
  rw [hlen, hodd] at heven
  exact one_ne_zero heven

omit [Fintype V] in
/-- For an even balanced common-root family, prefix cancellation yields only
a homogeneous response direction.  This is compatible with an odd root
counterstrategy and is therefore not a contraction. -/
theorem even_balanced_arc_continuations_direction
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    (L : Finset V) (arcs : List (V × V))
    (hbalanced : (arcs.map Prod.fst).Perm (arcs.map Prod.snd))
    (heven : arcs.length % 2 = 0)
    (continuation : V × V → EdgeVector V)
    (hpoint : ∀ a ∈ arcs, AffineResponseMoment G seat hroot
      (twoOpenArcPrefix L a + continuation a)) :
    ResponseDirection G seat hroot (arcs.map continuation).sum := by
  let points := arcs.map fun a ↦
    twoOpenArcPrefix L a + continuation a
  have hpoints : ∀ z ∈ points,
      AffineResponseMoment G seat hroot z := by
    intro z hz
    simp only [points, List.mem_map] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact hpoint a ha
  have hdirection : ResponseDirection G seat hroot points.sum :=
    AffineResponseMoment.even_list_sum_direction points (by simpa [points])
      hpoints
  have hdecomp : points.sum =
      (arcs.map (twoOpenArcPrefix L)).sum +
        (arcs.map continuation).sum := by
    simpa only [points] using list_sum_map_add arcs
      (twoOpenArcPrefix L) continuation
  rw [hdecomp, sum_twoOpenArcPrefix_eq_zero_of_balanced L arcs hbalanced,
    zero_add] at hdirection
  exact hdirection

end

end Ogdoad.Fifo
