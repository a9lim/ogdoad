import Ogdoad.FifoPublicSeparatorAutomaton

/-!
# Strategy-relative minima of the public separator automaton

The exact separator recurrence becomes stronger when it is minimized inside
one displayed public policy rather than over public states.  A rank-minimal
sheet-one subtree cannot have a sheet-one proper descendant.  Consequently
every retained move out of that subtree toggles the separator bit.

At a policy-selected node this forces the selected move to be a real `OPEN`
of separator increment one.  At a universal node it forces *every* legal move
to be such a real `OPEN`; in particular the distinguished dummy has already
been consumed and neither `CLOSE` nor `PASS` is legal.  Thus the silent
`OPEN d` does not by itself contradict a constantly-one policy at the initial
root.  It removes the universal-node alternative while `d` is untouched, but
leaves the sharp selected-real-`OPEN` normal form.

This module is proof-only.  It does not assert that the remaining selected
real-`OPEN` case is impossible and therefore does not prove
`UniversalPublicPolicyAffine` or FIFO linking.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Exact policy ancestry and its decreasing rank -/

/-- Constructor-sensitive subtree membership in one displayed public policy.
At a `choose` node only the selected child is retained; at an `answer` node
every legal child belongs to the ancestry. -/
inductive PublicPolicyAncestry (seat : Bool) :
    {s : PublicState V} → PublicPolicy seat s →
      {t : PublicState V} → PublicPolicy seat t → Prop
  | root {s : PublicState V} (policy : PublicPolicy seat s) :
      PublicPolicyAncestry seat policy policy
  | choose {s s' t : PublicState V} {hseat : s.toMove ≠ seat}
      {m : Move V} {hstep : publicStep s m = some s'}
      {child : PublicPolicy seat s'} {subtree : PublicPolicy seat t}
      (tail : PublicPolicyAncestry seat child subtree) :
      PublicPolicyAncestry seat
        (.choose s hseat m s' hstep child) subtree
  | answer {s s' t : PublicState V} {hseat : s.toMove = seat}
      {hasMove : ∃ m u, publicStep s m = some u}
      {children : ∀ m u, publicStep s m = some u → PublicPolicy seat u}
      {m : Move V} {hstep : publicStep s m = some s'}
      {subtree : PublicPolicy seat t}
      (tail : PublicPolicyAncestry seat (children m s' hstep) subtree) :
      PublicPolicyAncestry seat
        (.answer s hseat hasMove children) subtree

omit [Fintype V] in
/-- Exact policy ancestry is transitive. -/
theorem PublicPolicyAncestry.trans
    {seat : Bool} {r s t : PublicState V}
    {root : PublicPolicy seat r} {middle : PublicPolicy seat s}
    {subtree : PublicPolicy seat t}
    (hrs : PublicPolicyAncestry seat root middle)
    (hst : PublicPolicyAncestry seat middle subtree) :
    PublicPolicyAncestry seat root subtree := by
  induction hrs with
  | root => simpa using hst
  | choose _ ih => exact .choose (ih hst)
  | answer _ ih => exact .answer (ih hst)

/-- The score-free rank of a public state. -/
def publicRank (s : PublicState V) : Nat :=
  4 * s.untouched.card + 2 * s.queue.length + if s.ko then 1 else 0

omit [Fintype V] in
/-- Every public transition strictly decreases the same FIFO rank used by
the concrete game. -/
theorem publicRank_step_lt {s t : PublicState V} {m : Move V}
    (h : publicStep s m = some t) : publicRank t < publicRank s := by
  obtain ⟨U, q, ko, turn⟩ := s
  cases m
  · rename_i v
    simp only [publicStep] at h
    split at h
    · rename_i hv
      cases h
      rw [publicRank, publicRank, Finset.card_erase_of_mem hv,
        List.length_append]
      simp only [List.length_cons, List.length_nil]
      have hcard : 0 < U.card := Finset.card_pos.mpr ⟨v, hv⟩
      have hpred : U.card - 1 + 1 = U.card := by omega
      cases q <;> cases ko <;> simp <;> omega
    · contradiction
  · simp only [publicStep] at h
    split at h
    · contradiction
    · rename_i f q' hq
      split at h
      · contradiction
      · cases h
        simp [publicRank]
        omega
  · simp only [publicStep] at h
    split at h
    · rename_i hp
      cases h
      rcases hp with ⟨rfl, hq, rfl⟩
      simp [publicRank]
    · contradiction

/-! ## Rank-minimal sheet-one subtrees -/

/-- A sheet-one subtree with no lower-rank sheet-one descendant in its own
displayed policy ancestry. -/
def PublicPolicyMinimalOneSheet (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (policy : PublicPolicy seat s) : Prop :=
  PublicPolicySeparatorSheet d ell seat policy 1 ∧
    ∀ {t : PublicState V} (subtree : PublicPolicy seat t),
      PublicPolicyAncestry seat policy subtree → publicRank t < publicRank s →
        ¬PublicPolicySeparatorSheet d ell seat subtree 1

omit [Fintype V] in
/-- Every sheet-one public policy has a rank-minimal sheet-one subtree in its
exact constructor-sensitive ancestry. -/
theorem PublicPolicySeparatorSheet.exists_minimalOneSheet
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {rootState : PublicState V}
    (root : PublicPolicy seat rootState)
    (hroot : PublicPolicySeparatorSheet d ell seat root 1) :
    ∃ (s : PublicState V) (policy : PublicPolicy seat s),
      PublicPolicyAncestry seat root policy ∧
        PublicPolicyMinimalOneSheet d ell seat policy := by
  classical
  let P : Nat → Prop := fun n ↦
    ∃ (s : PublicState V) (policy : PublicPolicy seat s),
      PublicPolicyAncestry seat root policy ∧
        PublicPolicySeparatorSheet d ell seat policy 1 ∧ publicRank s = n
  have hP : ∃ n, P n :=
    ⟨publicRank rootState, rootState, root, .root root, hroot, rfl⟩
  let n := Nat.find hP
  obtain ⟨s, policy, hancestry, hsheet, hrank⟩ := Nat.find_spec hP
  refine ⟨s, policy, hancestry, hsheet, ?_⟩
  intro t subtree hsub hlt hsubsheet
  have hglobal : PublicPolicyAncestry seat root subtree :=
    hancestry.trans hsub
  have hPt : P (publicRank t) :=
    ⟨t, subtree, hglobal, hsubsheet, rfl⟩
  have hnle : n ≤ publicRank t := Nat.find_min' hP hPt
  have hsle : publicRank s ≤ publicRank t := by
    simpa [n, hrank] using hnle
  exact (Nat.not_lt_of_ge hsle) hlt

omit [Fintype V] in
private theorem separatorEvaluation_close_eq_zero (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (s : PublicState V) :
    publicSeparatorEvaluation d ell
      (moveLiveStar s.toZeroState .close) = 0 := by
  have h := publicSeparatorStepBit_close d ell s 0
  simpa [publicSeparatorStepBit] using h

omit [Fintype V] in
private theorem separatorEvaluation_pass_eq_zero (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (s : PublicState V) :
    publicSeparatorEvaluation d ell
      (moveLiveStar s.toZeroState .pass) = 0 := by
  have h := publicSeparatorStepBit_pass d ell s 0
  simpa [publicSeparatorStepBit] using h

omit [Fintype V] in
private theorem separatorEvaluation_open_dummy_eq_zero (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (s : PublicState V) :
    publicSeparatorEvaluation d ell
      (moveLiveStar s.toZeroState (.open d)) = 0 := by
  have h := publicSeparatorStepBit_open_dummy d ell s 0
  simpa [publicSeparatorStepBit] using h

omit [Fintype V] in
/-- Exact local shape of a rank-minimal sheet-one subtree.

* At a selected node, the displayed move is a real `OPEN` with separator
  increment one.
* At a universal node, the dummy is spent, the untouched set is nonempty,
  `CLOSE` is blocked, and every untouched vertex has increment one.

The second alternative makes explicit why silent `OPEN d` sharpens the
normal form but does not eliminate the first alternative. -/
theorem PublicPolicyMinimalOneSheet.operational_shape
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} {policy : PublicPolicy seat s}
    (hminimal : PublicPolicyMinimalOneSheet d ell seat policy) :
    (s.toMove ≠ seat ∧
        ∃ (v : V) (t : PublicState V), v ≠ d ∧
          publicStep s (.open v) = some t ∧
          publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState (.open v)) = 1) ∨
      (s.toMove = seat ∧ d ∉ s.untouched ∧ s.untouched.Nonempty ∧
        (s.queue = [] ∨ s.ko = true) ∧
        ∀ v ∈ s.untouched,
          publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState (.open v)) = 1) := by
  rcases hminimal with ⟨hsheet, hminimal⟩
  cases policy with
  | terminal s ht =>
      have hzero :=
        (publicPolicySeparatorSheet_terminal_iff d ell seat s ht 1).1 hsheet
      exact False.elim (one_ne_zero hzero)
  | choose s hseat m t hstep child =>
      have hchild :=
        (publicPolicySeparatorSheet_choose_iff d ell seat hseat m hstep child 1).1
          hsheet
      have heval : publicSeparatorEvaluation d ell
          (moveLiveStar s.toZeroState m) = 1 := by
        by_contra hne
        have hzero := zmod2_eq_zero_of_ne_one _ hne
        have hchildOne : PublicPolicySeparatorSheet d ell seat child 1 := by
          simpa [hzero] using hchild
        have hnot := hminimal child
          (PublicPolicyAncestry.choose (PublicPolicyAncestry.root child))
          (publicRank_step_lt hstep)
        exact hnot hchildOne
      left
      refine ⟨hseat, ?_⟩
      cases m with
      | «open» v =>
          have hvd : v ≠ d := by
            intro hv
            subst v
            rw [separatorEvaluation_open_dummy_eq_zero] at heval
            exact zero_ne_one heval
          exact ⟨v, t, hvd, hstep, heval⟩
      | close =>
          rw [separatorEvaluation_close_eq_zero] at heval
          exact False.elim (zero_ne_one heval)
      | pass =>
          rw [separatorEvaluation_pass_eq_zero] at heval
          exact False.elim (zero_ne_one heval)
  | answer s hseat hasMove children =>
      have hchildren :=
        (publicPolicySeparatorSheet_answer_iff d ell seat hseat hasMove
          children 1).1 hsheet
      have hall : ∀ (m : Move V) (t : PublicState V)
          (hstep : publicStep s m = some t),
          publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState m) = 1 := by
        intro m t hstep
        have hchild := hchildren m t hstep
        by_contra hne
        have hzero := zmod2_eq_zero_of_ne_one _ hne
        have hchildOne : PublicPolicySeparatorSheet d ell seat
            (children m t hstep) 1 := by
          simpa [hzero] using hchild
        have hnot := hminimal (children m t hstep)
          (PublicPolicyAncestry.answer
            (PublicPolicyAncestry.root (children m t hstep)))
          (publicRank_step_lt hstep)
        exact hnot hchildOne
      have hdspent : d ∉ s.untouched := by
        intro hdmem
        let t : PublicState V := {
          untouched := s.untouched.erase d
          queue := s.queue ++ [d]
          ko := s.queue.isEmpty
          toMove := !s.toMove }
        have hstep : publicStep s (.open d) = some t := by
          simp [publicStep, t, hdmem]
        have hone := hall (.open d) t hstep
        rw [separatorEvaluation_open_dummy_eq_zero] at hone
        exact zero_ne_one hone
      have hU : s.untouched.Nonempty := by
        obtain ⟨m, t, hstep⟩ := hasMove
        have hone := hall m t hstep
        cases m with
        | «open» v =>
            simp only [publicStep] at hstep
            split at hstep
            · rename_i hv
              exact ⟨v, hv⟩
            · contradiction
        | close =>
            rw [separatorEvaluation_close_eq_zero] at hone
            exact False.elim (zero_ne_one hone)
        | pass =>
            rw [separatorEvaluation_pass_eq_zero] at hone
            exact False.elim (zero_ne_one hone)
      have hcloseBlocked : s.queue = [] ∨ s.ko = true := by
        cases hq : s.queue with
        | nil => exact Or.inl rfl
        | cons f q =>
            cases hk : s.ko with
            | true => exact Or.inr rfl
            | false =>
                let t : PublicState V := {
                  untouched := s.untouched
                  queue := q
                  ko := false
                  toMove := !s.toMove }
                have hstep : publicStep s .close = some t := by
                  simp [publicStep, hq, hk, t]
                have hone := hall .close t hstep
                rw [separatorEvaluation_close_eq_zero] at hone
                exact False.elim (zero_ne_one hone)
      have hopen : ∀ v ∈ s.untouched,
          publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState (.open v)) = 1 := by
        intro v hv
        let t : PublicState V := {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove }
        exact hall (.open v) t (by simp [publicStep, t, hv])
      exact Or.inr ⟨hseat, hdspent, hU, hcloseBlocked, hopen⟩

omit [Fintype V] in
/-- If the distinguished dummy is still untouched at a rank-minimal
sheet-one subtree, that subtree is necessarily policy-selected and its
selected move is a real separator-one `OPEN`.  The dummy therefore excludes
the universal case but supplies no contradiction at the selected node. -/
theorem PublicPolicyMinimalOneSheet.liveDummy_selectedRealOpen
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} {policy : PublicPolicy seat s}
    (hminimal : PublicPolicyMinimalOneSheet d ell seat policy)
    (hd : d ∈ s.untouched) :
    s.toMove ≠ seat ∧
      ∃ (v : V) (t : PublicState V), v ≠ d ∧
        publicStep s (.open v) = some t ∧
        publicSeparatorEvaluation d ell
          (moveLiveStar s.toZeroState (.open v)) = 1 := by
  rcases hminimal.operational_shape d ell seat with hselected | huniversal
  · exact hselected
  · exact False.elim (huniversal.2.1 hd)

/-! ## Initial constantly-one policy -/

/-- A constantly-one separator at the initial public root has an exact
ancestry-minimal occurrence with the preceding local shape.  This is the
strongest conclusion supplied by the silent dummy alone. -/
theorem constantOneInitialPolicy_extract_minimal_shape
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) (root : PublicPolicy seat (initial (V := V)).public)
    (hroot : PublicPolicySeparatorSheet d ell seat root 1) :
    ∃ (s : PublicState V) (policy : PublicPolicy seat s),
      PublicPolicyAncestry seat root policy ∧
        PublicPolicyMinimalOneSheet d ell seat policy ∧
          ((s.toMove ≠ seat ∧
              ∃ (v : V) (t : PublicState V), v ≠ d ∧
                publicStep s (.open v) = some t ∧
                publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState (.open v)) = 1) ∨
            (s.toMove = seat ∧ d ∉ s.untouched ∧ s.untouched.Nonempty ∧
              (s.queue = [] ∨ s.ko = true) ∧
              ∀ v ∈ s.untouched,
                publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState (.open v)) = 1)) := by
  obtain ⟨s, policy, hancestry, hminimal⟩ :=
    hroot.exists_minimalOneSheet d ell seat root
  exact ⟨s, policy, hancestry, hminimal,
    hminimal.operational_shape d ell seat⟩

/-- For distinguished seat `false`, the initial node itself cannot be a
rank-minimal sheet-one occurrence: it is a universal node with the silent
dummy `OPEN` available.  Minimality must descend into the displayed policy,
but the theorem does not force all minimizing branches to consume the dummy. -/
theorem constantOneInitialFalse_not_minimal
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (root : PublicPolicy false (initial (V := V)).public)
    (hminimal : PublicPolicyMinimalOneSheet d ell false root) : False := by
  rcases hminimal.operational_shape d ell false with hselected | huniversal
  · exact hselected.1 rfl
  · exact huniversal.2.1 (by simp [initial, State.public])

end

end Ogdoad.Fifo
