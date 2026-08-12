import Ogdoad.FifoDummyExitCarrier
import Ogdoad.FifoMinHotCurvature

/-!
# Cross-exit incidence and the augmentation lock

The dummy-exit carrier reduces an odd corridor family to its canonical front
`CLOSE` children.  Any further repair must use earlier universal siblings.
This file records the exact affine parity forced on such a repair.

A descendant continuation representative is not the same thing as its bare
ancestry prefix.  After lifting to the initial root, every decorated point
`prefix + continuation` has graph evaluation one.  An even family of such
points is therefore a homogeneous response direction; an odd family is still
an affine response point.  Consequently earlier siblings can enter the
dummy-exit contraction only in even augmentation.  The odd augmentation stays
on the canonical `CLOSE` family.

The final theorem is the restricted cross-exit interface: an odd family of
canonical exit points, an even family of earlier decorated siblings, and any
homogeneous ladder corrections contract the root as soon as their projected
incidence sum vanishes.  It does not construct that incidence sum; this is the
remaining causal routing theorem.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A strategy prefix transports the representation invariant from its root
to its descendant. -/
theorem StrategyPrefix.wellFormed
    {G : SimpleGraph V} {seat : Bool} {root s : State V}
    {hroot : OddStrategy G seat root} {h : OddStrategy G seat s}
    {p : EdgeVector V} (hp : StrategyPrefix G seat hroot h p)
    (hrootWF : WellFormed root) : WellFormed s := by
  induction hp with
  | root => exact hrootWF
  | @choose s s' hseat m hstep hchild p parent ih =>
      exact wellFormed_step ih hstep
  | @answer s s' hseat hasMove hchildren m hstep p parent ih =>
      exact wellFormed_step ih hstep

omit [Fintype V] in
/-- The graph evaluation of a bare ancestry prefix is the change of cut
potential between its endpoints.  In particular, unlike a decorated affine
point, a prefix has no uniform augmentation value. -/
theorem StrategyPrefix.graphEvaluation_eq_potential_add
    {G : SimpleGraph V} {seat : Bool} {root s : State V}
    {hroot : OddStrategy G seat root} {h : OddStrategy G seat s}
    {p : EdgeVector V} (hp : StrategyPrefix G seat hroot h p)
    (hrootWF : WellFormed root) :
    graphEvaluation G p = potential G root + potential G s := by
  obtain ⟨a, ha⟩ := exists_affineResponseMoment h
  have hsWF : WellFormed s := hp.wellFormed hrootWF
  have hlift := (hp.lift ha).graphEvaluation_eq hrootWF
  have hchild := ha.graphEvaluation_eq hsWF
  rw [map_add, hchild] at hlift
  calc
    graphEvaluation G p =
        (graphEvaluation G p + (1 + potential G s)) +
          (1 + potential G s) := by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = (1 + potential G root) + (1 + potential G s) := by
          rw [hlift]
    _ = potential G root + potential G s := by
          calc
            (1 + potential G root) + (1 + potential G s) =
                (1 + 1) + (potential G root + potential G s) := by abel
            _ = potential G root + potential G s := by
              rw [CharTwo.add_self_eq_zero, zero_add]

omit [Fintype V] in
/-- The sum of an even list of representatives of one affine response space
is a homogeneous response direction. -/
theorem AffineResponseMoment.even_list_sum_direction
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {h : OddStrategy G seat s}
    (zs : List (EdgeVector V)) (heven : zs.length % 2 = 0)
    (hall : ∀ z ∈ zs, AffineResponseMoment G seat h z) :
    ResponseDirection G seat h zs.sum := by
  obtain ⟨b, hb⟩ := exists_affineResponseMoment h
  have hodd : (b :: zs).length % 2 = 1 := by
    simp only [List.length_cons]
    omega
  have hmem : ∀ z ∈ b :: zs, AffineResponseMoment G seat h z := by
    intro z hz
    simp only [List.mem_cons] at hz
    exact hz.elim (fun hzb ↦ hzb ▸ hb) (hall z)
  have hsum : AffineResponseMoment G seat h (b + zs.sum) := by
    simpa using AffineResponseMoment.odd_list_sum (b :: zs) hodd hmem
  refine ⟨b + zs.sum, b, hsum, hb, ?_⟩
  ext e
  simp only [Finsupp.add_apply]
  symm
  calc
    b e + zs.sum e + b e = (b e + b e) + zs.sum e := by abel
    _ = zs.sum e := by rw [CharTwo.add_self_eq_zero, zero_add]

omit [Fintype V] in
/-- Response directions form an additive subgroup of the universal edge
space. -/
theorem ResponseDirection.add
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {h : OddStrategy G seat s} {x y : EdgeVector V}
    (hx : ResponseDirection G seat h x)
    (hy : ResponseDirection G seat h y) :
    ResponseDirection G seat h (x + y) := by
  obtain ⟨a, b, ha, hb, hxab⟩ := hx
  refine ⟨a + y, b, ha.add_direction hy, hb, ?_⟩
  rw [hxab]
  abel

omit [Fintype V] in
/-- A finite sum of continuation directions is again a continuation
direction. -/
theorem ResponseDirection.list_sum
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    {h : OddStrategy G seat s}
    (ds : List (EdgeVector V))
    (hall : ∀ d ∈ ds, ResponseDirection G seat h d) :
    ResponseDirection G seat h ds.sum := by
  induction ds with
  | nil => simpa using ResponseDirection.zero h
  | cons d rest ih =>
      simp only [List.sum_cons]
      exact (hall d (by simp)).add (ih (fun e he ↦ hall e (by simp [he])))

omit [Fintype V] in
/-- A continuation direction at an ancestry hole lifts to a direction at the
same fixed root: the two copies of the prefix cancel. -/
theorem StrategyPrefix.lift_direction
    {G : SimpleGraph V} {seat : Bool} {root s : State V}
    {hroot : OddStrategy G seat root} {h : OddStrategy G seat s}
    {p d : EdgeVector V} (hp : StrategyPrefix G seat hroot h p)
    (hd : ResponseDirection G seat h d) :
    ResponseDirection G seat hroot d := by
  obtain ⟨x, y, hx, hy, rfl⟩ := hd
  refine ⟨p + x, p + y, hp.lift hx, hp.lift hy, ?_⟩
  ext e
  simp only [Finsupp.add_apply]
  calc
    x e + y e = (p e + p e) + (x e + y e) := by
      rw [CharTwo.add_self_eq_zero, zero_add]
    _ = (p e + x e) + (p e + y e) := by abel

/-! ## The canonical CLOSE / earlier OPEN offset square -/

/-- Explicit OPEN successor used only to state the dummy-exit offset square. -/
private def crossExitOpenSuccessor (s : State V) (v : V) : State V where
  untouched := s.untouched.erase v
  queue := s.queue ++ [v]
  ko := s.queue.isEmpty
  toMove := !s.toMove
  score := s.score

omit [Fintype V] in
private theorem eq_crossExitOpenSuccessor_of_step
    {G : SimpleGraph V} {s t : State V} {v : V}
    (h : step G s (.open v) = some t) :
    t = crossExitOpenSuccessor s v := by
  simp only [step] at h
  split at h
  · cases h
    rfl
  · contradiction

/-- Explicit front-CLOSE successor used only in the offset square. -/
private def crossExitCloseSuccessor (G : SimpleGraph V) (s : State V)
    (x : V) (Q : List V) : State V where
  untouched := s.untouched
  queue := Q
  ko := false
  toMove := !s.toMove
  score := s.score + flip G s.untouched x

omit [Fintype V] in
private theorem eq_crossExitCloseSuccessor_of_step
    {G : SimpleGraph V} {s t : State V} {x : V} {Q : List V}
    (hqueue : s.queue = x :: Q)
    (h : step G s .close = some t) :
    t = crossExitCloseSuccessor G s x Q := by
  simp only [step, hqueue] at h
  split at h
  · contradiction
  · cases h
    rfl

omit [Fintype V] in
/-- Exact operational coupling at one dummy-exit parent.

From a clear defender state with queue `x :: Q`, compare the canonical reply
`C_x` followed by the strategy's selected `O_z` with the earlier universal
sibling `O_z`.  The two descendants have the same untouched set, queues
differing by the single front token `x`, opposite movers, and the displayed
ko/score offsets.  Their ancestry live-star difference is exactly the frozen
unit edge `xz`; it is not zero.  Thus the earlier sibling is the correct
one-front-offset partner, but every such pairing creates a labelled holonomy
which must be cancelled across exits. -/
theorem crossExit_closeThenOpen_openSibling_offset
    (G : SimpleGraph V) (s sC sCO sO : State V)
    (x z : V) (Q : List V)
    (hs : WellFormed s) (hz : z ∈ s.untouched)
    (hqueue : s.queue = x :: Q) (_hko : s.ko = false)
    (hC : step G s .close = some sC)
    (hCO : step G sC (.open z) = some sCO)
    (hO : step G s (.open z) = some sO) :
    sCO.untouched = sO.untouched ∧
      sO.queue = x :: sCO.queue ∧
      sCO.toMove = !sO.toMove ∧
      sO.ko = false ∧
      sCO.ko = Q.isEmpty ∧
      sO.score + sCO.score = flip G s.untouched x ∧
      moveLiveStar s (.open z) + moveLiveStar sC (.open z) =
        Finsupp.single s(x, z) 1 := by
  classical
  have hsC := eq_crossExitCloseSuccessor_of_step hqueue hC
  have hsCO := eq_crossExitOpenSuccessor_of_step hCO
  have hsO := eq_crossExitOpenSuccessor_of_step hO
  subst sC
  subst sCO
  subst sO
  rcases hs with ⟨hnodup, hdisjoint⟩
  have hxQ : x ∉ Q := by
    rw [hqueue] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hxU : x ∉ s.untouched := by
    intro hxU
    have hxq : x ∈ s.queue.toFinset := by simp [hqueue]
    exact (Finset.disjoint_left.mp hdisjoint hxU) hxq
  have hxz : x ≠ z := by
    intro h
    subst z
    exact hxU hz
  let L := s.untouched ∪ Q.toFinset
  have hxL : x ∉ L := by simp [L, hxU, hxQ]
  have hliveC :
      liveSet (crossExitCloseSuccessor G s x Q) = L := by
    simp [liveSet, crossExitCloseSuccessor, L]
  have hliveS : liveSet s = insert x L := by
    simp only [liveSet, hqueue, List.toFinset_cons]
    ext v
    simp [L]
  refine ⟨rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · simp [crossExitOpenSuccessor, crossExitCloseSuccessor, hqueue]
  · simp [crossExitOpenSuccessor, crossExitCloseSuccessor]
  · simp [crossExitOpenSuccessor, hqueue]
  · simp only [crossExitOpenSuccessor, crossExitCloseSuccessor]
    calc
      s.score + (s.score + flip G s.untouched x) =
          (s.score + s.score) + flip G s.untouched x := by abel
      _ = flip G s.untouched x := by
        rw [CharTwo.add_self_eq_zero, zero_add]
  · simp only [moveLiveStar]
    rw [hliveS, hliveC]
    have hstar := liveStarVector_insert_cancel L x z hxL hxz
    rw [add_comm]
    exact hstar

omit [Fintype V] in
/-- Selected-sibling complement exchange at a dummy-exit fan.

The ordinary fan has even size.  If `j` is the real `OPEN` sibling paired by
the one-front-offset ladder with the canonical `CLOSE` child, then their sum
is represented by the parent together with every *other* ordinary child.
That replacement family is even: the complement of `j` in an even fan is
odd, and adjoining the parent makes it even.

This is the constructive cross-exit incidence supplied by the complete
universal fan.  It leaves only the ladder's labelled unit holonomy and the
canonical children whose selected attacker move is `CLOSE`. -/
theorem StrategyPrefix.answer_even_fan_selected_complement
    {G : SimpleGraph V} {seat : Bool} {root s t0 : State V}
    {hroot : OddStrategy G seat root}
    {hseat : s.toMove = seat}
    {hasMove : ∃ m u, step G s m = some u}
    {hchildren : ∀ m u, step G s m = some u → OddStrategy G seat u}
    {p : EdgeVector V}
    (hp : StrategyPrefix G seat hroot
      (OddStrategy.answer s hseat hasMove hchildren) p)
    {I : Type*} (left right : List I) (j : I)
    (m : I → Move V) (t : I → State V)
    (hstep : ∀ i ∈ left ++ j :: right, step G s (m i) = some (t i))
    (z : I → EdgeVector V)
    (hz : ∀ i (hi : i ∈ left ++ j :: right),
      AffineResponseMoment G seat
        (hchildren (m i) (t i) (hstep i hi)) (z i))
    (m0 : Move V) (hstep0 : step G s m0 = some t0)
    (z0 : EdgeVector V)
    (hz0 : AffineResponseMoment G seat
      (hchildren m0 t0 hstep0) z0)
    (heven : (left ++ j :: right).length % 2 = 0) :
    ∃ a,
      AffineResponseMoment G seat
          (OddStrategy.answer s hseat hasMove hchildren) a ∧
      AffineResponseMoment G seat hroot (p + a) ∧
      (p + (moveLiveStar s m0 + z0)) +
          (p + (moveLiveStar s (m j) + z j)) =
        (p + a) +
          ((left ++ right).map fun i ↦
            p + (moveLiveStar s (m i) + z i)).sum ∧
      (1 + (left ++ right).length) % 2 = 0 := by
  let is := left ++ j :: right
  have hstep' : ∀ i ∈ is, step G s (m i) = some (t i) := by
    simpa only [is] using hstep
  have hz' : ∀ i (hi : i ∈ is),
      AffineResponseMoment G seat
        (hchildren (m i) (t i) (hstep' i hi)) (z i) := by
    intro i hi
    simpa only [is] using hz i hi
  obtain ⟨a, ha, hroota, hid⟩ :=
    hp.answer_even_fan_cancels_to_distinguished
      is m t hstep' z hz' m0 hstep0 z0 hz0 (by simpa [is] using heven)
  refine ⟨a, ha, hroota, ?_, ?_⟩
  · rw [← hid]
    simp only [is, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons]
    ext e
    simp only [Finsupp.add_apply]
    let P := p e
    let A := a e
    let L := (left.map fun i ↦
      p + (moveLiveStar s (m i) + z i)).sum e
    let J := (p + (moveLiveStar s (m j) + z j)) e
    let R := (right.map fun i ↦
      p + (moveLiveStar s (m i) + z i)).sum e
    change P + A + (L + (J + R)) + J = P + A + (L + R)
    calc
      P + A + (L + (J + R)) + J =
          P + A + (L + R) + (J + J) := by abel
      _ = P + A + (L + R) := by
        rw [CharTwo.add_self_eq_zero, add_zero]
  · simp only [List.length_append, List.length_cons] at heven ⊢
    omega

omit [Fintype V] in
/-- Every factor term's prefix-decorated base is a point of the root affine
response space. -/
theorem StrategyFactorTerm.decorated_mem
    {G : SimpleGraph V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    (t : StrategyFactorTerm G seat hroot) :
    AffineResponseMoment G seat hroot (t.hole.moment + t.base) :=
  t.hole.ancestry.lift t.base_mem

/-- Augmentation lock for strategy-indexed points.  If a family of decorated
root points agrees in the isolated-dummy quotient with a homogeneous family,
then the decorated family has even cardinality.  This is the formal reason an
odd earlier-sibling repair is impossible. -/
theorem projected_decorated_balance_card_even
    {G : SimpleGraph V} {d : V} {seat : Bool}
    {hroot : OddStrategy G seat (initial (V := V))}
    (hdummy : IsDummy G d)
    (points directions : List (EdgeVector V))
    (hpoints : ∀ z ∈ points, AffineResponseMoment G seat hroot z)
    (hdirections : ∀ z ∈ directions, ResponseDirection G seat hroot z)
    (hbalance : realEdgeProjection d points.sum =
      realEdgeProjection d directions.sum) :
    points.length % 2 = 0 := by
  by_contra hneven
  have hodd : points.length % 2 = 1 := by omega
  have hp : AffineResponseMoment G seat hroot points.sum :=
    AffineResponseMoment.odd_list_sum points hodd hpoints
  have hdir : ResponseDirection G seat hroot directions.sum :=
    ResponseDirection.list_sum directions hdirections
  have hpd : AffineResponseMoment G seat hroot
      (points.sum + directions.sum) := hp.add_direction hdir
  have hzero : realEdgeProjection d (points.sum + directions.sum) = 0 := by
    rw [map_add, hbalance]
    rw [← map_add]
    have hself : directions.sum + directions.sum = 0 := by
      ext e
      exact CharTwo.add_self_eq_zero _
    rw [hself, map_zero]
  exact no_zero_projectedAffineResponseMoment_initial hdummy
    ⟨points.sum + directions.sum, hpd, hzero⟩

omit [Fintype V] in
/-- Restricted cross-exit contraction.  The canonical exit family is odd;
the family of earlier decorated universal siblings is even.  Their aggregate
plus arbitrary homogeneous ladder corrections is a root affine point.  A
vanishing projected incidence therefore contracts the root.

This theorem isolates the exact remaining constructive obligation: produce
`hincidence` from the actual corridor and one-front-offset ancestry. -/
theorem crossExit_evenSibling_incidence_zero
    {G : SimpleGraph V} {d : V} {seat : Bool} {root : State V}
    {hroot : OddStrategy G seat root}
    (canonical earlier : List (StrategyFactorTerm G seat hroot))
    (hcanonical : canonical.length % 2 = 1)
    (hearlier : earlier.length % 2 = 0)
    (ladder : EdgeVector V)
    (hladder : ResponseDirection G seat hroot ladder)
    (hincidence : realEdgeProjection d
        ((canonical.map fun t ↦ t.hole.moment + t.base).sum +
          (earlier.map fun t ↦ t.hole.moment + t.base).sum + ladder) = 0) :
    ProjectedAffineResponseMoment d G seat hroot 0 := by
  let cs := canonical.map fun t ↦ t.hole.moment + t.base
  let es := earlier.map fun t ↦ t.hole.moment + t.base
  have hcmem : ∀ z ∈ cs, AffineResponseMoment G seat hroot z := by
    intro z hz
    simp only [cs, List.mem_map] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact t.decorated_mem
  have hemen : ∀ z ∈ es, AffineResponseMoment G seat hroot z := by
    intro z hz
    simp only [es, List.mem_map] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact t.decorated_mem
  have hcodd : cs.length % 2 = 1 := by simpa [cs] using hcanonical
  have heeven : es.length % 2 = 0 := by simpa [es] using hearlier
  have hc : AffineResponseMoment G seat hroot cs.sum :=
    AffineResponseMoment.odd_list_sum cs hcodd hcmem
  have he : ResponseDirection G seat hroot es.sum :=
    AffineResponseMoment.even_list_sum_direction es heeven hemen
  have hce : AffineResponseMoment G seat hroot (cs.sum + es.sum) :=
    hc.add_direction he
  have hcel : AffineResponseMoment G seat hroot
      (cs.sum + es.sum + ladder) := hce.add_direction hladder
  refine ⟨cs.sum + es.sum + ladder, hcel, ?_⟩
  simpa only [cs, es] using hincidence

/-- On an actual isolated-dummy initial odd strategy, the restricted
cross-exit incidence equation is impossible.  Establishing that equation
from the strategy tree is therefore sufficient to eliminate the alleged
counterstrategy. -/
theorem no_crossExit_evenSibling_incidence
    {G : SimpleGraph V} {d : V} {seat : Bool}
    {hroot : OddStrategy G seat (initial (V := V))}
    (hdummy : IsDummy G d)
    (canonical earlier : List (StrategyFactorTerm G seat hroot))
    (hcanonical : canonical.length % 2 = 1)
    (hearlier : earlier.length % 2 = 0)
    (ladder : EdgeVector V)
    (hladder : ResponseDirection G seat hroot ladder) :
    ¬ realEdgeProjection d
        ((canonical.map fun t ↦ t.hole.moment + t.base).sum +
          (earlier.map fun t ↦ t.hole.moment + t.base).sum + ladder) = 0 := by
  intro hincidence
  exact no_zero_projectedAffineResponseMoment_initial hdummy
    (crossExit_evenSibling_incidence_zero canonical earlier
      hcanonical hearlier ladder hladder hincidence)

end

end Ogdoad.Fifo
