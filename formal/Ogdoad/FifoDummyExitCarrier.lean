import Ogdoad.FifoAffine

/-!
# The dummy-exit parent-plus-even-children carrier

At a defender node following an attacker OPEN of the isolated dummy, the real
OPEN replies form an even family.  In the full Type-valued `OddStrategy` the
front CLOSE is also a legal universal child.  Affinely, one can therefore use
the distinguished CLOSE together with every real OPEN child to construct a
canonical parent point.  Adding that parent point back to all real child
points cancels the latter pairwise and leaves exactly the CLOSE child.  No
choice of a distinguished real reply is required.

This module also records the finite-family prefix ledger used by the
least-root corridor.  The corridor construction itself is not formalized
here: the ledger equality is an explicit hypothesis.  The theorem says that
once that universal/projected equality has been supplied, the odd family of
dummy parents plus their even real-child fans has zero aggregate ancestry
prefix.  It does not contract the remaining distinguished CLOSE
continuations.  In particular, later compensation by decorated root points
must have even cardinality; only bare prefix vectors occur in the ledger
below, and they have no uniform graph evaluation.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

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
private theorem even_constant_list_sum_zero {I : Type*}
    (is : List I) (p : EdgeVector V) (heven : is.length % 2 = 0) :
    (is.map fun _ ↦ p).sum = 0 := by
  cases is with
  | nil => simp
  | cons i rest =>
      cases rest with
      | nil =>
          simp only [List.length_cons, List.length_nil] at heven
          omega
      | cons j tail =>
          have htail : tail.length % 2 = 0 := by
            simp only [List.length_cons] at heven
            omega
          have ih := even_constant_list_sum_zero tail p htail
          simp only [List.map_cons, List.sum_cons]
          rw [ih]
          simp only [add_zero]
          ext e
          exact CharTwo.add_self_eq_zero _
termination_by is.length

omit [Fintype V] in
/-- At a defender node, an even family of ordinary children plus one
distinguished child has a canonical odd parent representative.  Adding that
parent representative back to all ordinary lifted child representatives
cancels them pairwise and leaves the distinguished lifted point.

For a dummy exit the ordinary children are all real OPEN replies and the
distinguished child is the legal front CLOSE. -/
theorem AffineResponseMoment.answer_even_fan_cancels_to_distinguished
    {G : SimpleGraph V} {seat : Bool} {s t0 : State V}
    {hseat : s.toMove = seat}
    {hasMove : ∃ m u, step G s m = some u}
    {hchildren : ∀ m u, step G s m = some u → OddStrategy G seat u}
    {I : Type*} (is : List I) (m : I → Move V) (t : I → State V)
    (hstep : ∀ i ∈ is, step G s (m i) = some (t i))
    (z : I → EdgeVector V)
    (hz : ∀ i (hi : i ∈ is),
      AffineResponseMoment G seat
        (hchildren (m i) (t i) (hstep i hi)) (z i))
    (m0 : Move V) (hstep0 : step G s m0 = some t0)
    (z0 : EdgeVector V)
    (hz0 : AffineResponseMoment G seat
      (hchildren m0 t0 hstep0) z0)
    (heven : is.length % 2 = 0) :
    ∃ a,
      AffineResponseMoment G seat
        (OddStrategy.answer s hseat hasMove hchildren) a ∧
      a + (is.map fun i ↦ moveLiveStar s (m i) + z i).sum =
        moveLiveStar s m0 + z0 := by
  let ordinary := is.map fun i ↦ moveLiveStar s (m i) + z i
  let distinguished := moveLiveStar s m0 + z0
  let a := distinguished + ordinary.sum
  have hdist : AffineResponseMoment G seat
      (OddStrategy.answer s hseat hasMove hchildren) distinguished :=
    AffineResponseMoment.answerChild (hstep := hstep0) hz0
  have hord : ∀ w ∈ ordinary,
      AffineResponseMoment G seat
        (OddStrategy.answer s hseat hasMove hchildren) w := by
    intro w hw
    simp only [ordinary, List.mem_map] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    exact AffineResponseMoment.answerChild
      (hstep := hstep i hi) (hz i hi)
  have hodd : (distinguished :: ordinary).length % 2 = 1 := by
    simp only [List.length_cons, ordinary, List.length_map]
    omega
  have hall : ∀ w ∈ distinguished :: ordinary,
      AffineResponseMoment G seat
        (OddStrategy.answer s hseat hasMove hchildren) w := by
    intro w hw
    simp only [List.mem_cons] at hw
    exact hw.elim (fun h ↦ h ▸ hdist) (hord w)
  have ha : AffineResponseMoment G seat
      (OddStrategy.answer s hseat hasMove hchildren) a := by
    simpa [a, ordinary, distinguished] using
      AffineResponseMoment.odd_list_sum
        (distinguished :: ordinary) hodd hall
  refine ⟨a, ha, ?_⟩
  simp only [a, ordinary, distinguished]
  ext e
  simp only [Finsupp.add_apply]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

omit [Fintype V] in
/-- Same-root decorated form of
`answer_even_fan_cancels_to_distinguished`.  Every child inherits the same
ancestry prefix `p`.  Because the ordinary fan is even, its copies of `p`
cancel, while the parent's copy survives.  Thus the parent together with all
ordinary children is exactly the distinguished child after lifting to the
common root.

The `StrategyPrefix` premise certifies that this really is one fixed
Type-valued strategy tree.  It supplies no relation between different dummy
exits; that remains the corridor-level incidence hypothesis. -/
theorem StrategyPrefix.answer_even_fan_cancels_to_distinguished
    {G : SimpleGraph V} {seat : Bool} {root s t0 : State V}
    {hroot : OddStrategy G seat root}
    {hseat : s.toMove = seat}
    {hasMove : ∃ m u, step G s m = some u}
    {hchildren : ∀ m u, step G s m = some u → OddStrategy G seat u}
    {p : EdgeVector V}
    (hp : StrategyPrefix G seat hroot
      (OddStrategy.answer s hseat hasMove hchildren) p)
    {I : Type*} (is : List I) (m : I → Move V) (t : I → State V)
    (hstep : ∀ i ∈ is, step G s (m i) = some (t i))
    (z : I → EdgeVector V)
    (hz : ∀ i (hi : i ∈ is),
      AffineResponseMoment G seat
        (hchildren (m i) (t i) (hstep i hi)) (z i))
    (m0 : Move V) (hstep0 : step G s m0 = some t0)
    (z0 : EdgeVector V)
    (hz0 : AffineResponseMoment G seat
      (hchildren m0 t0 hstep0) z0)
    (heven : is.length % 2 = 0) :
    ∃ a,
      AffineResponseMoment G seat
        (OddStrategy.answer s hseat hasMove hchildren) a ∧
      AffineResponseMoment G seat hroot (p + a) ∧
      (p + a) +
          (is.map fun i ↦ p + (moveLiveStar s (m i) + z i)).sum =
        p + (moveLiveStar s m0 + z0) := by
  obtain ⟨a, ha, hlocal⟩ :=
    AffineResponseMoment.answer_even_fan_cancels_to_distinguished
      is m t hstep z hz m0 hstep0 z0 hz0 heven
  refine ⟨a, ha, hp.lift ha, ?_⟩
  rw [list_sum_map_add]
  rw [even_constant_list_sum_zero is p heven, zero_add]
  calc
    p + a + (is.map fun i ↦ moveLiveStar s (m i) + z i).sum =
        p + (a + (is.map fun i ↦ moveLiveStar s (m i) + z i).sum) :=
      add_assoc _ _ _
    _ = p + (moveLiveStar s m0 + z0) := congrArg (p + ·) hlocal

omit [Fintype V] in
/-- Quotient image of the decorated same-root carrier.  Dummy-incident and
diagonal coordinates may be discarded after, not before, the exact
parent-plus-even-children identity has been established. -/
theorem StrategyPrefix.answer_even_fan_projected_identity
    {G : SimpleGraph V} {seat : Bool} {root s t0 : State V}
    {hroot : OddStrategy G seat root}
    {hseat : s.toMove = seat}
    {hasMove : ∃ m u, step G s m = some u}
    {hchildren : ∀ m u, step G s m = some u → OddStrategy G seat u}
    {p : EdgeVector V}
    (hp : StrategyPrefix G seat hroot
      (OddStrategy.answer s hseat hasMove hchildren) p)
    {I : Type*} (is : List I) (m : I → Move V) (t : I → State V)
    (hstep : ∀ i ∈ is, step G s (m i) = some (t i))
    (z : I → EdgeVector V)
    (hz : ∀ i (hi : i ∈ is),
      AffineResponseMoment G seat
        (hchildren (m i) (t i) (hstep i hi)) (z i))
    (m0 : Move V) (hstep0 : step G s m0 = some t0)
    (z0 : EdgeVector V)
    (hz0 : AffineResponseMoment G seat
      (hchildren m0 t0 hstep0) z0)
    (heven : is.length % 2 = 0) (d : V) :
    ∃ a,
      AffineResponseMoment G seat
        (OddStrategy.answer s hseat hasMove hchildren) a ∧
      AffineResponseMoment G seat hroot (p + a) ∧
      realEdgeProjection d
          ((p + a) +
            (is.map fun i ↦ p + (moveLiveStar s (m i) + z i)).sum) =
        realEdgeProjection d (p + (moveLiveStar s m0 + z0)) := by
  obtain ⟨a, ha, hroota, hidentity⟩ :=
    hp.answer_even_fan_cancels_to_distinguished
      is m t hstep z hz m0 hstep0 z0 hz0 heven
  exact ⟨a, ha, hroota, congrArg (realEdgeProjection d) hidentity⟩

omit [Fintype V] [DecidableEq V] in
/-- Abstract universal prefix ledger for a finite family of dummy exits.
When the sum of the parent ancestry prefixes equals the sum of the complete
real OPEN-fan prefixes, adjoining every parent and every real child makes the
aggregate ancestry prefix zero.  This is precisely the hypothesis boundary
left by the unformalized corridor routing. -/
theorem dummyExitCarrier_prefix_zero
    {I : Type*} (is : Finset I)
    (ancestry realOpenFan : I → EdgeVector V)
    (hledger : (Finset.sum is fun i ↦ ancestry i) =
      Finset.sum is fun i ↦ realOpenFan i) :
    (Finset.sum is fun i ↦ ancestry i + realOpenFan i) = 0 := by
  rw [Finset.sum_add_distrib, hledger]
  ext e
  exact CharTwo.add_self_eq_zero _

omit [Fintype V] in
/-- Projected version of the corridor prefix ledger.  It is enough for the
exact isolated-dummy quotient even when unprojected prefixes retain dummy
star coordinates. -/
theorem dummyExitCarrier_projected_prefix_zero
    {I : Type*} (is : Finset I) (d : V)
    (ancestry realOpenFan : I → EdgeVector V)
    (hledger : (Finset.sum is fun i ↦
        realEdgeProjection d (ancestry i)) =
      Finset.sum is fun i ↦ realEdgeProjection d (realOpenFan i)) :
    (Finset.sum is fun i ↦
      realEdgeProjection d (ancestry i + realOpenFan i)) = 0 := by
  simp_rw [map_add]
  rw [Finset.sum_add_distrib, hledger]
  rw [← map_sum]
  rw [← map_add]
  have hsource :
      (Finset.sum is fun i ↦ realOpenFan i) +
          (Finset.sum is fun i ↦ realOpenFan i) = 0 := by
    ext e
    exact CharTwo.add_self_eq_zero _
  rw [hsource, map_zero]

end

end Ogdoad.Fifo
