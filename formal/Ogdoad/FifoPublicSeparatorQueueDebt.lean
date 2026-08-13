import Ogdoad.FifoPublicSeparatorAncestry

/-!
# The queued separator debt after a selected sheet-one OPEN

Follow a rank-minimal separator-one occurrence whose policy-selected move is
a real `OPEN v`, while the distinguished dummy is still untouched.  The
selected child is a complete-fan node on sheet zero.  Rank minimality then
forces every one of its legal children to remain on sheet zero; in particular
the silent `OPEN d` sibling is zero-sheet, not a new one-sheet occurrence.

Handshaking does find the parity partner of the separator-odd opener `v`.
But every untouched vertex in the complete fan has separator degree zero, so
the partner lies in the already-open FIFO queue.  It is therefore not a legal
`OPEN` sibling.  This is the exact queue-debt obstruction to turning the
silent dummy branch into an immediate alternating-chain descent.

The theorem is strategy-relative and proof-only.  It neither constructs a
constant-one initial policy nor proves one impossible.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A public OPEN preserves the live carrier: it moves its vertex from the
untouched set to the tail of the queue. -/
theorem publicStep_open_liveSet_eq
    {s t : PublicState V} {v : V}
    (hstep : publicStep s (.open v) = some t) :
    liveSet t.toZeroState = liveSet s.toZeroState := by
  obtain ⟨U, q, ko, turn⟩ := s
  simp only [publicStep] at hstep
  split at hstep
  · rename_i hv
    cases hstep
    simp only [PublicState.toZeroState, liveSet, List.toFinset_append,
      List.toFinset_cons, List.toFinset_nil]
    ext w
    simp
    constructor
    · rintro (rfl | ⟨_hne, hwU⟩ | hwq)
      · exact Or.inl hv
      · exact Or.inl hwU
      · exact Or.inr hwq
    · rintro (hwU | hwq)
      · by_cases hwv : w = v
        · exact Or.inl hwv
        · exact Or.inr (Or.inl ⟨hwv, hwU⟩)
      · exact Or.inr (Or.inr hwq)
  · contradiction

omit [Fintype V] in
/-- The opened vertex belongs to the successor queue. -/
theorem publicStep_open_mem_queue
    {s t : PublicState V} {v : V}
    (hstep : publicStep s (.open v) = some t) : v ∈ t.queue.toFinset := by
  obtain ⟨U, q, ko, turn⟩ := s
  simp only [publicStep] at hstep
  split at hstep
  · cases hstep
    simp
  · contradiction

omit [Fintype V] in
/-- The separator evaluation of an OPEN star is the induced degree in the
isolated-dummy graph represented by the functional. -/
theorem publicSeparatorEvaluation_open_eq_flip_graphOfFunctional
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (s : PublicState V) (v : V) :
    publicSeparatorEvaluation d ell
        (moveLiveStar s.toZeroState (.open v)) =
      flip (graphOfRealEdgeFunctional d ell) (liveSet s.toZeroState) v := by
  rw [publicSeparatorEvaluation, ← graphEvaluation_graphOfRealEdgeFunctional,
    moveLiveStar, graphEvaluation_liveStarVector]

/-! ## The exact same-root zero fan -/

omit [Fintype V] in
/-- At a rank-minimal selected sheet-one `OPEN`, the selected complete-fan
child is on sheet zero, and every legal sibling below that child also lies on
sheet zero with zero separator increment.

This statement retains the actual root policy occurrence.  The child sheets
are not chosen independently: they are the displayed complete fan of the
same selected child. -/
theorem selectedOneMinimum_child_completeFan_zero
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s t : PublicState V} (hseat : s.toMove ≠ seat)
    (v : V) (hstep : publicStep s (.open v) = some t)
    (hturn : t.toMove = seat)
    (hasMove : ∃ m u, publicStep t m = some u)
    (children : ∀ m u, publicStep t m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicyMinimalOneSheet d ell seat
      (.choose s hseat (.open v) t hstep
        (.answer t hturn hasMove children))) :
    publicSeparatorEvaluation d ell
        (moveLiveStar s.toZeroState (.open v)) = 1 ∧
      PublicPolicySeparatorSheet d ell seat
        (.answer t hturn hasMove children) 0 ∧
      ∀ (m : Move V) (u : PublicState V)
        (hu : publicStep t m = some u),
        publicSeparatorEvaluation d ell
            (moveLiveStar t.toZeroState m) = 0 ∧
          PublicPolicySeparatorSheet d ell seat (children m u hu) 0 := by
  rcases hminimal with ⟨hrootSheet, hminimal⟩
  have hchildRaw :=
    (publicPolicySeparatorSheet_choose_iff d ell seat hseat (.open v)
      hstep (.answer t hturn hasMove children) 1).1 hrootSheet
  have hopen : publicSeparatorEvaluation d ell
      (moveLiveStar s.toZeroState (.open v)) = 1 := by
    by_contra hne
    have hzero := zmod2_eq_zero_of_ne_one _ hne
    have hchildOne : PublicPolicySeparatorSheet d ell seat
        (.answer t hturn hasMove children) 1 := by
      simpa [hzero] using hchildRaw
    exact hminimal (.answer t hturn hasMove children)
      (PublicPolicyAncestry.choose
        (PublicPolicyAncestry.root (.answer t hturn hasMove children)))
      (publicRank_step_lt hstep) hchildOne
  have hchildZero : PublicPolicySeparatorSheet d ell seat
      (.answer t hturn hasMove children) 0 := by
    simpa [hopen, CharTwo.add_self_eq_zero] using hchildRaw
  refine ⟨hopen, hchildZero, ?_⟩
  have hfan :=
    (publicPolicySeparatorSheet_answer_iff d ell seat hturn hasMove
      children 0).1 hchildZero
  intro m u hu
  have hgrandRaw := hfan m u hu
  have hinc : publicSeparatorEvaluation d ell
      (moveLiveStar t.toZeroState m) = 0 := by
    by_contra hne
    have hone := zmod2_eq_one_of_ne_zero _ hne
    have hgrandOne : PublicPolicySeparatorSheet d ell seat
        (children m u hu) 1 := by
      simpa [hone] using hgrandRaw
    have hancestry : PublicPolicyAncestry seat
        (.choose s hseat (.open v) t hstep
          (.answer t hturn hasMove children))
        (children m u hu) :=
      PublicPolicyAncestry.choose
        (PublicPolicyAncestry.answer
          (PublicPolicyAncestry.root (children m u hu)))
    have hrank : publicRank u < publicRank s :=
      lt_trans (publicRank_step_lt hu) (publicRank_step_lt hstep)
    exact hminimal (children m u hu) hancestry hrank hgrandOne
  exact ⟨hinc, by simpa [hinc] using hgrandRaw⟩

omit [Fintype V] in
/-- The live dummy sibling of the complete child fan is explicitly sheet
zero.  Hence the silent branch supplies no lower sheet-one occurrence. -/
theorem selectedOneMinimum_dummySibling_zero
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s t : PublicState V} (hseat : s.toMove ≠ seat)
    (v : V) (hvd : v ≠ d) (hd : d ∈ s.untouched)
    (hstep : publicStep s (.open v) = some t)
    (hturn : t.toMove = seat)
    (hasMove : ∃ m u, publicStep t m = some u)
    (children : ∀ m u, publicStep t m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicyMinimalOneSheet d ell seat
      (.choose s hseat (.open v) t hstep
        (.answer t hturn hasMove children))) :
    ∃ (td : PublicState V)
      (hdstep : publicStep t (.open d) = some td),
      publicSeparatorEvaluation d ell
          (moveLiveStar t.toZeroState (.open d)) = 0 ∧
        PublicPolicySeparatorSheet d ell seat
          (children (.open d) td hdstep) 0 := by
  have hdt : d ∈ t.untouched := by
    obtain ⟨U, q, ko, turn⟩ := s
    simp only [publicStep] at hstep
    split at hstep
    · rename_i hvU
      cases hstep
      exact Finset.mem_erase.mpr ⟨Ne.symm hvd, hd⟩
    · contradiction
  let td : PublicState V := {
    untouched := t.untouched.erase d
    queue := t.queue ++ [d]
    ko := t.queue.isEmpty
    toMove := !t.toMove }
  have hdstep : publicStep t (.open d) = some td := by
    simp [publicStep, td, hdt]
  have hfan := selectedOneMinimum_child_completeFan_zero
    d ell seat hseat v hstep hturn hasMove children hminimal
  exact ⟨td, hdstep, hfan.2.2 (.open d) td hdstep⟩

/-! ## Handshaking sends the partner into the queue -/

omit [Fintype V] in
/-- The parity partner of the selected separator-odd opener is an already
queued, distinct separator-odd vertex.  It is consequently not a legal OPEN
at the complete-fan child.

This is the smallest exact obstruction to the naive alternating-chain
argument: handshaking produces the next odd vertex, but FIFO ancestry puts it
outside the legal OPEN fan rather than in a lower sheet-one sibling. -/
theorem selectedOneMinimum_exists_queued_oddDebt
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s t : PublicState V} (hseat : s.toMove ≠ seat)
    (v : V) (hstep : publicStep s (.open v) = some t)
    (hturn : t.toMove = seat)
    (hasMove : ∃ m u, publicStep t m = some u)
    (children : ∀ m u, publicStep t m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicyMinimalOneSheet d ell seat
      (.choose s hseat (.open v) t hstep
        (.answer t hturn hasMove children)))
    (hWF : WellFormed t.toZeroState) :
    ∃ r ∈ t.queue.toFinset, r ≠ v ∧
      publicSeparatorEvaluation d ell
          (moveLiveStar t.toZeroState (.open r)) = 1 ∧
        publicStep t (.open r) = none := by
  let H := graphOfRealEdgeFunctional d ell
  let L := liveSet t.toZeroState
  let Q := t.queue.toFinset
  have hfan := selectedOneMinimum_child_completeFan_zero
    d ell seat hseat v hstep hturn hasMove children hminimal
  have hlive := publicStep_open_liveSet_eq hstep
  have hvodd : flip H L v = 1 := by
    have hsOdd : flip H (liveSet s.toZeroState) v = 1 := by
      simpa [H] using
        (publicSeparatorEvaluation_open_eq_flip_graphOfFunctional
          d ell s v).symm.trans hfan.1
    simpa [L, hlive] using hsOdd
  have hUzero : ∀ w ∈ t.untouched, flip H L w = 0 := by
    intro w hw
    let u : PublicState V := {
      untouched := t.untouched.erase w
      queue := t.queue ++ [w]
      ko := t.queue.isEmpty
      toMove := !t.toMove }
    have hu : publicStep t (.open w) = some u := by
      simp [publicStep, u, hw]
    have hz := (hfan.2.2 (.open w) u hu).1
    simpa [H, L] using
      (publicSeparatorEvaluation_open_eq_flip_graphOfFunctional
        d ell t w).symm.trans hz
  have hdisjoint : Disjoint t.untouched Q := by
    simpa [Q, PublicState.toZeroState] using hWF.2
  have hhandshake := sum_flip_self_eq_zero H L
  have hsplit :
      (∑ w ∈ t.untouched, flip H L w) +
          ∑ w ∈ Q, flip H L w = 0 := by
    change (∑ w ∈ t.untouched ∪ t.queue.toFinset,
      flip H (t.untouched ∪ t.queue.toFinset) w) = 0 at hhandshake
    rw [Finset.sum_union hdisjoint] at hhandshake
    have hL : L = t.untouched ∪ t.queue.toFinset := rfl
    rw [hL]
    exact hhandshake
  have hUsum : (∑ w ∈ t.untouched, flip H L w) = 0 := by
    exact Finset.sum_eq_zero (fun w hw ↦ hUzero w hw)
  have hQsum : (∑ w ∈ Q, flip H L w) = 0 := by
    rw [hUsum, zero_add] at hsplit
    exact hsplit
  have hvQ : v ∈ Q := by
    exact publicStep_open_mem_queue hstep
  have hsplitV := Finset.sum_erase_add Q (fun w ↦ flip H L w) hvQ
  have hrest : (∑ w ∈ Q.erase v, flip H L w) = 1 := by
    calc
      (∑ w ∈ Q.erase v, flip H L w) =
          (∑ w ∈ Q.erase v, flip H L w) + (1 + 1) := by
            rw [CharTwo.add_self_eq_zero, add_zero]
      _ = ((∑ w ∈ Q.erase v, flip H L w) + flip H L v) + 1 := by
            rw [hvodd]
            abel
      _ = (∑ w ∈ Q, flip H L w) + 1 := by rw [hsplitV]
      _ = 1 := by rw [hQsum, zero_add]
  have hrestNe : (∑ w ∈ Q.erase v, flip H L w) ≠ 0 := by
    rw [hrest]
    exact one_ne_zero
  obtain ⟨r, hrErase, hrNe⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hrestNe
  have hrQ : r ∈ Q := Finset.mem_of_mem_erase hrErase
  have hrv : r ≠ v := (Finset.mem_erase.mp hrErase).1
  have hrOdd : flip H L r = 1 := zmod2_eq_one_of_ne_zero _ hrNe
  have hrEval : publicSeparatorEvaluation d ell
      (moveLiveStar t.toZeroState (.open r)) = 1 := by
    simpa [H, L] using
      (publicSeparatorEvaluation_open_eq_flip_graphOfFunctional d ell t r).trans
        hrOdd
  have hrNotU : r ∉ t.untouched := by
    intro hrU
    exact Finset.disjoint_left.mp hdisjoint hrU hrQ
  have hrIllegal : publicStep t (.open r) = none := by
    simp [publicStep, hrNotU]
  exact ⟨r, hrQ, hrv, hrEval, hrIllegal⟩

omit [Fintype V] in
/-- In particular the queue *before* the selected odd OPEN was nonempty.
If it had been empty, the successor queue would contain only the opener `v`,
contradicting the distinct queued odd debt supplied by handshaking. -/
theorem selectedOneMinimum_oldQueue_nonempty
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s t : PublicState V} (hseat : s.toMove ≠ seat)
    (v : V) (hstep : publicStep s (.open v) = some t)
    (hturn : t.toMove = seat)
    (hasMove : ∃ m u, publicStep t m = some u)
    (children : ∀ m u, publicStep t m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicyMinimalOneSheet d ell seat
      (.choose s hseat (.open v) t hstep
        (.answer t hturn hasMove children)))
    (hWF : WellFormed t.toZeroState) : s.queue ≠ [] := by
  obtain ⟨r, hrQueue, hrv, _hrOdd, _hrIllegal⟩ :=
    selectedOneMinimum_exists_queued_oddDebt d ell seat hseat v hstep
      hturn hasMove children hminimal hWF
  have htQueue : t.queue = s.queue ++ [v] := by
    obtain ⟨U, q, ko, turn⟩ := s
    simp only [publicStep] at hstep
    split at hstep
    · cases hstep
      rfl
    · contradiction
  intro hsEmpty
  have : r = v := by
    simpa [htQueue, hsEmpty] using hrQueue
  exact hrv this

omit [Fintype V] in
/-- The nonempty old queue makes `CLOSE` a legal silent sibling in the
selected opener's complete child fan.  That sibling remains on sheet zero,
but it immediately enters a policy-selected node (`toMove ≠ seat`).

Therefore the universal fan forces exactly one CLOSE descent here; it does
not force a chain of CLOSEs through the subsequent attacker-pruned policy. -/
theorem selectedOneMinimum_closeSibling_enters_selectedZero
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s t : PublicState V} (hseat : s.toMove ≠ seat)
    (v : V) (hstep : publicStep s (.open v) = some t)
    (hturn : t.toMove = seat)
    (hasMove : ∃ m u, publicStep t m = some u)
    (children : ∀ m u, publicStep t m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicyMinimalOneSheet d ell seat
      (.choose s hseat (.open v) t hstep
        (.answer t hturn hasMove children)))
    (hWF : WellFormed t.toZeroState) :
    ∃ u, ∃ hu : publicStep t .close = some u,
      u.toMove ≠ seat ∧
        publicSeparatorEvaluation d ell
            (moveLiveStar t.toZeroState .close) = 0 ∧
          PublicPolicySeparatorSheet d ell seat (children .close u hu) 0 := by
  have hq : s.queue ≠ [] :=
    selectedOneMinimum_oldQueue_nonempty d ell seat hseat v hstep hturn
      hasMove children hminimal hWF
  obtain ⟨f, q, hsQueue⟩ : ∃ f q, s.queue = f :: q := by
    cases hsq : s.queue with
    | nil => exact False.elim (hq hsq)
    | cons f q => exact ⟨f, q, rfl⟩
  have htQueueRaw : t.queue = s.queue ++ [v] := by
    obtain ⟨U, oldq, ko, turn⟩ := s
    simp only [publicStep] at hstep
    split at hstep
    · cases hstep
      rfl
    · contradiction
  have htQueue : t.queue = f :: (q ++ [v]) := by
    rw [htQueueRaw, hsQueue]
    rfl
  have htKoRaw : t.ko = s.queue.isEmpty := by
    obtain ⟨U, oldq, ko, turn⟩ := s
    simp only [publicStep] at hstep
    split at hstep
    · cases hstep
      rfl
    · contradiction
  have htKo : t.ko = false := by
    rw [htKoRaw, hsQueue]
    rfl
  let u : PublicState V :=
    ⟨t.untouched, q ++ [v], false, !t.toMove⟩
  have hu : publicStep t .close = some u := by
    simp [publicStep, htQueue, htKo, u]
  have hfan := selectedOneMinimum_child_completeFan_zero
    d ell seat hseat v hstep hturn hasMove children hminimal
  have hzero := hfan.2.2 .close u hu
  refine ⟨u, hu, ?_, hzero⟩
  simp [u, hturn]

omit [Fintype V] in
/-- Every later policy-selected edge from a proper zero-sheet descendant of
the same rank-minimal one-sheet root has separator increment zero and retains
sheet zero.  Minimality forbids the alternative increment one because it
would create a lower one-sheet child.

This is the exact global continuation law after the forced CLOSE sibling.
It constrains the selected continuation but does not require it to CLOSE;
the policy may select any legal zero-increment move. -/
theorem PublicPolicyMinimalOneSheet.properSelectedZero_step_zero
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {rootState s t : PublicState V}
    {root : PublicPolicy seat rootState}
    (hminimal : PublicPolicyMinimalOneSheet d ell seat root)
    (hseat : s.toMove ≠ seat) (m : Move V)
    (hstep : publicStep s m = some t) (child : PublicPolicy seat t)
    (hnode : PublicPolicyAncestry seat root
      (.choose s hseat m t hstep child))
    (hrank : publicRank s < publicRank rootState)
    (hsheet : PublicPolicySeparatorSheet d ell seat
      (.choose s hseat m t hstep child) 0) :
    publicSeparatorEvaluation d ell
        (moveLiveStar s.toZeroState m) = 0 ∧
      PublicPolicySeparatorSheet d ell seat child 0 := by
  have hchildRaw :=
    (publicPolicySeparatorSheet_choose_iff d ell seat hseat m hstep child 0).1
      hsheet
  have hinc : publicSeparatorEvaluation d ell
      (moveLiveStar s.toZeroState m) = 0 := by
    by_contra hne
    have hone := zmod2_eq_one_of_ne_zero _ hne
    have hchildOne : PublicPolicySeparatorSheet d ell seat child 1 := by
      simpa [hone] using hchildRaw
    have hchildNode : PublicPolicyAncestry seat root child :=
      hnode.trans
        (PublicPolicyAncestry.choose (PublicPolicyAncestry.root child))
    have hchildRank : publicRank t < publicRank rootState :=
      lt_trans (publicRank_step_lt hstep) hrank
    exact hminimal.2 child hchildNode hchildRank hchildOne
  exact ⟨hinc, by simpa [hinc] using hchildRaw⟩

end

end Ogdoad.Fifo
