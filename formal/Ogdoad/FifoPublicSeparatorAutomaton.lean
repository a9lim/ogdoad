import Ogdoad.FifoPublicPolicyDuality
import Ogdoad.FifoOuterFan

/-!
# The exact one-bit separator automaton for public FIFO policies

Fix a linear functional on the real-edge quotient.  A public policy lies on
the separator sheet `b` when every point of its projected affine response
space has functional value `b`.  This property has an exact structural
recurrence with only one scalar bit of memory:

* a terminal policy lies on sheet zero;
* across a selected move, the bit is toggled by the projected live star; and
* across a complete answer node, every legal child must lie on its
  correspondingly toggled sheet.

Thus the separator-side recursion itself is completely finite-state.  The
isolated dummy is silent in this automaton: opening it, closing any front, or
passing never toggles the bit.  The final example records the sharp limitation
of augmenting that bit only by the current queue front.  Two coherent states
with the same dummy front, the same bit, and the same legal real OPEN have
different separator increments because a previously closed real vertex is no
longer live.  Hence `(front, separator bit)` is not a Markov state for the
recurrence; a successful contraction must retain more of the live carrier or
the actual strategy ancestry.

This module is a recurrence and a finite-memory boundary, not a proof of
`UniversalPublicPolicyAffine`.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Evaluation of a universal live-star moment by a functional on the exact
real-edge quotient. -/
def publicSeparatorEvaluation (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (z : EdgeVector V) : ZMod 2 :=
  ell (realEdgeProjection d z)

omit [Fintype V] in
@[simp] theorem publicSeparatorEvaluation_zero (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2) :
    publicSeparatorEvaluation d ell 0 = 0 := by
  simp [publicSeparatorEvaluation]

omit [Fintype V] in
@[simp] theorem publicSeparatorEvaluation_add (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (x y : EdgeVector V) :
    publicSeparatorEvaluation d ell (x + y) =
      publicSeparatorEvaluation d ell x +
        publicSeparatorEvaluation d ell y := by
  simp [publicSeparatorEvaluation]

/-- Every affine response point of `policy` lies on one separator sheet.
This is the dual form of an alleged failure of the projected-zero target. -/
def PublicPolicySeparatorSheet (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (policy : PublicPolicy seat s)
    (b : ZMod 2) : Prop :=
  ∀ z, PublicPolicyAffineMoment seat policy z →
    publicSeparatorEvaluation d ell z = b

omit [Fintype V] in
/-- Three points on one binary affine sheet sum to another point on that
same sheet. -/
theorem separator_three_same (b : ZMod 2) : b + b + b = b := by
  rw [CharTwo.add_self_eq_zero, zero_add]

omit [Fintype V] in
/-- One actual compatible terminal trace of a public policy, before taking
its affine hull. -/
inductive PublicPolicyLeafMoment (seat : Bool) :
    {s : PublicState V} → PublicPolicy seat s → EdgeVector V → Prop
  | terminal (s : PublicState V) (ht : s.untouched = ∅ ∧ s.queue = []) :
      PublicPolicyLeafMoment seat (.terminal s ht) 0
  | choose {s s' : PublicState V} {hseat : s.toMove ≠ seat}
      {m : Move V} {hstep : publicStep s m = some s'}
      {child : PublicPolicy seat s'} {z : EdgeVector V}
      (tail : PublicPolicyLeafMoment seat child z) :
      PublicPolicyLeafMoment seat (.choose s hseat m s' hstep child)
        (moveLiveStar s.toZeroState m + z)
  | answerChild {s s' : PublicState V} {hseat : s.toMove = seat}
      {hasMove : ∃ m u, publicStep s m = some u}
      {children : ∀ m u, publicStep s m = some u → PublicPolicy seat u}
      {m : Move V} {hstep : publicStep s m = some s'} {z : EdgeVector V}
      (tail : PublicPolicyLeafMoment seat (children m s' hstep) z) :
      PublicPolicyLeafMoment seat (.answer s hseat hasMove children)
        (moveLiveStar s.toZeroState m + z)

omit [Fintype V] in
theorem PublicPolicyLeafMoment.toAffine
    {seat : Bool} {s : PublicState V} {policy : PublicPolicy seat s}
    {z : EdgeVector V} (h : PublicPolicyLeafMoment seat policy z) :
    PublicPolicyAffineMoment seat policy z := by
  induction h with
  | terminal => exact .terminal _ _
  | choose _ ih => exact .choose ih
  | answerChild _ ih => exact .answerChild ih

/-- Uniform separator value on the actual compatible terminal traces. -/
def PublicPolicyLeafSeparatorSheet (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (policy : PublicPolicy seat s)
    (b : ZMod 2) : Prop :=
  ∀ z, PublicPolicyLeafMoment seat policy z →
    publicSeparatorEvaluation d ell z = b

omit [Fintype V] in
private theorem leafSeparatorSheet_terminal_iff (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) (s : PublicState V)
    (ht : s.untouched = ∅ ∧ s.queue = []) (b : ZMod 2) :
    PublicPolicyLeafSeparatorSheet d ell seat (.terminal s ht) b ↔
      b = 0 := by
  constructor
  · intro h
    have hz := h 0 (.terminal s ht)
    simpa using hz.symm
  · intro hb z hz
    subst b
    cases hz
    exact publicSeparatorEvaluation_zero d ell

omit [Fintype V] in
private theorem leafSeparatorSheet_choose_iff (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s s' : PublicState V} (hseat : s.toMove ≠ seat)
    (m : Move V) (hstep : publicStep s m = some s')
    (child : PublicPolicy seat s') (b : ZMod 2) :
    PublicPolicyLeafSeparatorSheet d ell seat
        (.choose s hseat m s' hstep child) b ↔
      PublicPolicyLeafSeparatorSheet d ell seat child
        (b + publicSeparatorEvaluation d ell
          (moveLiveStar s.toZeroState m)) := by
  constructor
  · intro h z hz
    have hroot := h (moveLiveStar s.toZeroState m + z) (.choose hz)
    rw [publicSeparatorEvaluation_add] at hroot
    calc
      publicSeparatorEvaluation d ell z =
          (publicSeparatorEvaluation d ell
              (moveLiveStar s.toZeroState m) +
            publicSeparatorEvaluation d ell
              (moveLiveStar s.toZeroState m)) +
              publicSeparatorEvaluation d ell z := by
        rw [CharTwo.add_self_eq_zero, zero_add]
      _ = publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState m) +
          (publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState m) +
              publicSeparatorEvaluation d ell z) := by abel
      _ = publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState m) + b := by rw [hroot]
      _ = b + publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState m) := by ac_rfl
  · intro h z hz
    cases hz with
    | choose tail =>
        rw [publicSeparatorEvaluation_add, h _ tail]
        calc
          publicSeparatorEvaluation d ell (moveLiveStar s.toZeroState m) +
                (b + publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState m)) =
              (publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState m) +
                publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState m)) + b := by abel
          _ = b := by rw [CharTwo.add_self_eq_zero, zero_add]

omit [Fintype V] in
private theorem leafSeparatorSheet_answer_iff (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (hseat : s.toMove = seat)
    (hasMove : ∃ m u, publicStep s m = some u)
    (children : ∀ m u, publicStep s m = some u → PublicPolicy seat u)
    (b : ZMod 2) :
    PublicPolicyLeafSeparatorSheet d ell seat
        (.answer s hseat hasMove children) b ↔
      ∀ (m : Move V) (u : PublicState V)
        (hstep : publicStep s m = some u),
        PublicPolicyLeafSeparatorSheet d ell seat (children m u hstep)
          (b + publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState m)) := by
  constructor
  · intro h m u hstep z hz
    have hroot := h (moveLiveStar s.toZeroState m + z)
      (.answerChild hz)
    rw [publicSeparatorEvaluation_add] at hroot
    calc
      publicSeparatorEvaluation d ell z =
          (publicSeparatorEvaluation d ell
              (moveLiveStar s.toZeroState m) +
            publicSeparatorEvaluation d ell
              (moveLiveStar s.toZeroState m)) +
              publicSeparatorEvaluation d ell z := by
        rw [CharTwo.add_self_eq_zero, zero_add]
      _ = publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState m) +
          (publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState m) +
              publicSeparatorEvaluation d ell z) := by abel
      _ = publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState m) + b := by rw [hroot]
      _ = b + publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState m) := by ac_rfl
  · intro h z hz
    cases hz with
    | answerChild tail =>
        rw [publicSeparatorEvaluation_add, h _ _ _ _ tail]
        calc
          publicSeparatorEvaluation d ell (moveLiveStar s.toZeroState _) +
                (b + publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState _)) =
              (publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState _) +
                publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState _)) + b := by abel
          _ = b := by rw [CharTwo.add_self_eq_zero, zero_add]

omit [Fintype V] in
/-- Taking the affine hull does not change the statement that every point is
on one separator sheet. -/
theorem publicPolicySeparatorSheet_iff_leafSeparatorSheet (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (policy : PublicPolicy seat s)
    (b : ZMod 2) :
    PublicPolicySeparatorSheet d ell seat policy b ↔
      PublicPolicyLeafSeparatorSheet d ell seat policy b := by
  constructor
  · intro h z hz
    exact h z hz.toAffine
  · intro h z hz
    induction hz generalizing b with
    | terminal s ht => exact h 0 (.terminal s ht)
    | @choose s s' hseat m hstep child z tail ih =>
        have hchild : PublicPolicyLeafSeparatorSheet d ell seat child
            (b + publicSeparatorEvaluation d ell
              (moveLiveStar s.toZeroState m)) :=
          (leafSeparatorSheet_choose_iff d ell seat hseat m hstep child b).1 h
        rw [publicSeparatorEvaluation_add, ih _ hchild]
        calc
          publicSeparatorEvaluation d ell (moveLiveStar s.toZeroState m) +
                (b + publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState m)) =
              (publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState m) +
                publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState m)) + b := by abel
          _ = b := by rw [CharTwo.add_self_eq_zero, zero_add]
    | @answerChild s s' hseat hasMove children m hstep z tail ih =>
        have hchildren :=
          (leafSeparatorSheet_answer_iff d ell seat hseat hasMove children b).1 h
        have hchild := hchildren m s' hstep
        rw [publicSeparatorEvaluation_add, ih _ hchild]
        calc
          publicSeparatorEvaluation d ell (moveLiveStar s.toZeroState m) +
                (b + publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState m)) =
              (publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState m) +
                publicSeparatorEvaluation d ell
                  (moveLiveStar s.toZeroState m)) + b := by abel
          _ = b := by rw [CharTwo.add_self_eq_zero, zero_add]
    | ternary hx hy hz ihx ihy ihz =>
        rw [publicSeparatorEvaluation_add,
          publicSeparatorEvaluation_add, ihx b h, ihy b h, ihz b h,
          separator_three_same]

omit [Fintype V] in
/-- Exact terminal clause of the separator automaton. -/
theorem publicPolicySeparatorSheet_terminal_iff (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) (s : PublicState V)
    (ht : s.untouched = ∅ ∧ s.queue = []) (b : ZMod 2) :
    PublicPolicySeparatorSheet d ell seat (.terminal s ht) b ↔ b = 0 := by
  rw [publicPolicySeparatorSheet_iff_leafSeparatorSheet,
    leafSeparatorSheet_terminal_iff]

omit [Fintype V] in
/-- Exact selected-child clause.  The only memory update is addition of the
selected move's projected live-star evaluation. -/
theorem publicPolicySeparatorSheet_choose_iff (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s s' : PublicState V} (hseat : s.toMove ≠ seat)
    (m : Move V) (hstep : publicStep s m = some s')
    (child : PublicPolicy seat s') (b : ZMod 2) :
    PublicPolicySeparatorSheet d ell seat
        (.choose s hseat m s' hstep child) b ↔
      PublicPolicySeparatorSheet d ell seat child
        (b + publicSeparatorEvaluation d ell
          (moveLiveStar s.toZeroState m)) := by
  rw [publicPolicySeparatorSheet_iff_leafSeparatorSheet,
    leafSeparatorSheet_choose_iff,
    publicPolicySeparatorSheet_iff_leafSeparatorSheet]

omit [Fintype V] in
/-- Exact complete-fan clause.  Every legal child must carry the bit obtained
by toggling with its own move label. -/
theorem publicPolicySeparatorSheet_answer_iff (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (hseat : s.toMove = seat)
    (hasMove : ∃ m u, publicStep s m = some u)
    (children : ∀ m u, publicStep s m = some u → PublicPolicy seat u)
    (b : ZMod 2) :
    PublicPolicySeparatorSheet d ell seat
        (.answer s hseat hasMove children) b ↔
      ∀ (m : Move V) (u : PublicState V)
        (hstep : publicStep s m = some u),
        PublicPolicySeparatorSheet d ell seat (children m u hstep)
          (b + publicSeparatorEvaluation d ell
            (moveLiveStar s.toZeroState m)) := by
  rw [publicPolicySeparatorSheet_iff_leafSeparatorSheet,
    leafSeparatorSheet_answer_iff]
  constructor
  · intro h m u hstep
    exact (publicPolicySeparatorSheet_iff_leafSeparatorSheet
      d ell seat (children m u hstep) _).2 (h m u hstep)
  · intro h m u hstep
    exact (publicPolicySeparatorSheet_iff_leafSeparatorSheet
      d ell seat (children m u hstep) _).1 (h m u hstep)

omit [Fintype V] in
/-- A uniform affine-one separator sheet excludes the projected-zero target.
By the leaf/affine equivalence, it is enough to establish this value on the
actual compatible terminal traces. -/
theorem not_projected_zero_of_leafSeparatorSheet_one (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (policy : PublicPolicy seat s)
    (h : PublicPolicyLeafSeparatorSheet d ell seat policy 1) :
    ¬ProjectedPublicPolicyAffineMoment d seat policy 0 := by
  rintro ⟨z, hz, hprojection⟩
  have hsheet : PublicPolicySeparatorSheet d ell seat policy 1 :=
    (publicPolicySeparatorSheet_iff_leafSeparatorSheet
      d ell seat policy 1).2 h
  have hone := hsheet z hz
  rw [publicSeparatorEvaluation, hprojection, map_zero] at hone
  exact zero_ne_one hone

/-! ## Minimal separator-one occurrences -/

/-- An occurrence of a descendant policy in the actual attacker-pruned
history tree.  Reconvergent public states reached through different histories
remain different occurrences. -/
inductive PublicPolicyNode (seat : Bool) :
    {s : PublicState V} → PublicPolicy seat s →
      {u : PublicState V} → PublicPolicy seat u → Prop
  | root {s : PublicState V} (policy : PublicPolicy seat s) :
      PublicPolicyNode seat policy policy
  | choose {s s' u : PublicState V} {hseat : s.toMove ≠ seat}
      {m : Move V} {hstep : publicStep s m = some s'}
      {child : PublicPolicy seat s'} {desc : PublicPolicy seat u}
      (node : PublicPolicyNode seat child desc) :
      PublicPolicyNode seat (.choose s hseat m s' hstep child) desc
  | answer {s s' u : PublicState V} {hseat : s.toMove = seat}
      {hasMove : ∃ m t, publicStep s m = some t}
      {children : ∀ m t, publicStep s m = some t → PublicPolicy seat t}
      {m : Move V} {hstep : publicStep s m = some s'}
      {desc : PublicPolicy seat u}
      (node : PublicPolicyNode seat (children m s' hstep) desc) :
      PublicPolicyNode seat (.answer s hseat hasMove children) desc

omit [Fintype V] in
/-- Coherence of public data is preserved by every public transition. -/
theorem coherent_toZeroState_publicStep {s u : PublicState V} {m : Move V}
    (hs : Coherent s.toZeroState) (hstep : publicStep s m = some u) :
    Coherent u.toZeroState := by
  let G : SimpleGraph V := ⊥
  have hpublic : publicStep s.toZeroState.public m = some u := by
    simpa [PublicState.toZeroState, State.public] using hstep
  let t := concreteStepOfPublic G s.toZeroState m u hpublic
  have htstep : step G s.toZeroState m = some t :=
    concreteStepOfPublic_step G s.toZeroState m u hpublic
  have htcoherent : Coherent t := coherent_step hs htstep
  have htpublic : t.public = u :=
    concreteStepOfPublic_public G s.toZeroState m u hpublic
  rw [← htpublic]
  simpa [Coherent, WellFormed, PublicState.toZeroState, State.public]
    using htcoherent

omit [Fintype V] in
/-- Every descendant occurrence of a coherent public root is coherent. -/
theorem PublicPolicyNode.coherent
    {seat : Bool} {s u : PublicState V}
    {policy : PublicPolicy seat s} {desc : PublicPolicy seat u}
    (node : PublicPolicyNode seat policy desc)
    (hs : Coherent s.toZeroState) : Coherent u.toZeroState := by
  induction node with
  | root => exact hs
  | @choose s s' u hseat m hstep child desc node ih =>
      exact ih (coherent_toZeroState_publicStep hs hstep)
  | @answer s s' u hseat hasMove children m hstep desc node ih =>
      exact ih (coherent_toZeroState_publicStep hs hstep)

/-- No immediate retained child remains on separator sheet one.  This is the
local property obtained by minimizing rank among separator-one occurrences. -/
def PublicPolicySeparatorOneImmediateMinimal (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (policy : PublicPolicy seat s) : Prop :=
  PublicPolicySeparatorSheet d ell seat policy 1 ∧
    match policy with
    | .terminal _ _ => True
    | .choose _ _ _ _ _ child =>
        ¬PublicPolicySeparatorSheet d ell seat child 1
    | .answer _ _ _ children =>
        ∀ m u (hstep : publicStep s m = some u),
          ¬PublicPolicySeparatorSheet d ell seat (children m u hstep) 1

omit [Fintype V] in
/-- Every separator-one policy contains an immediate-minimal separator-one
occurrence.  The recursion is on the actual policy tree, so this is a genuine
history occurrence rather than a public-state quotient. -/
theorem PublicPolicySeparatorSheet.exists_immediateMinimalOne (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (policy : PublicPolicy seat s)
    (hsheet : PublicPolicySeparatorSheet d ell seat policy 1) :
    ∃ (u : PublicState V) (desc : PublicPolicy seat u),
      PublicPolicyNode seat policy desc ∧
        PublicPolicySeparatorOneImmediateMinimal d ell seat desc := by
  induction policy with
  | terminal s ht =>
      have hzero :=
        (publicPolicySeparatorSheet_terminal_iff d ell seat s ht 1).1 hsheet
      exact False.elim (one_ne_zero hzero)
  | choose s hseat m s' hstep child ih =>
      by_cases hchild : PublicPolicySeparatorSheet d ell seat child 1
      · obtain ⟨u, desc, hnode, hminimal⟩ := ih hchild
        exact ⟨u, desc, .choose hnode, hminimal⟩
      · exact ⟨s, .choose s hseat m s' hstep child, .root _,
          hsheet, hchild⟩
  | answer s hseat hasMove children ih =>
      by_cases hchild : ∃ m u, ∃ hstep : publicStep s m = some u,
          PublicPolicySeparatorSheet d ell seat (children m u hstep) 1
      · obtain ⟨m, u, hstep, hu⟩ := hchild
        obtain ⟨v, desc, hnode, hminimal⟩ := ih m u hstep hu
        exact ⟨v, desc, .answer hnode, hminimal⟩
      · push Not at hchild
        exact ⟨s, .answer s hseat hasMove children, .root _,
          hsheet, hchild⟩

/-- Initial-root form: the extracted minimum is automatically coherent. -/
theorem PublicPolicySeparatorSheet.exists_coherent_immediateMinimalOne_initial
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool)
    (policy : PublicPolicy seat (initial (V := V)).public)
    (hsheet : PublicPolicySeparatorSheet d ell seat policy 1) :
    ∃ (u : PublicState V) (desc : PublicPolicy seat u),
      PublicPolicyNode seat policy desc ∧ Coherent u.toZeroState ∧
        PublicPolicySeparatorOneImmediateMinimal d ell seat desc := by
  obtain ⟨u, desc, hnode, hminimal⟩ :=
    hsheet.exists_immediateMinimalOne d ell seat policy
  refine ⟨u, desc, hnode, ?_, hminimal⟩
  apply hnode.coherent
  change Coherent (initial (V := V))
  exact coherent_initial

omit [Fintype V] in
/-- At a selected-move minimum, the selected live star has separator value
one.  A silent selected edge would leave the child on sheet one. -/
theorem separatorOneImmediateMinimal_choose_increment_eq_one (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s s' : PublicState V} (hseat : s.toMove ≠ seat)
    (m : Move V) (hstep : publicStep s m = some s')
    (child : PublicPolicy seat s')
    (hminimal : PublicPolicySeparatorOneImmediateMinimal d ell seat
      (.choose s hseat m s' hstep child)) :
    publicSeparatorEvaluation d ell (moveLiveStar s.toZeroState m) = 1 := by
  have hchildSheet :=
    (publicPolicySeparatorSheet_choose_iff
      d ell seat hseat m hstep child 1).1 hminimal.1
  have hne : publicSeparatorEvaluation d ell
      (moveLiveStar s.toZeroState m) ≠ 0 := by
    intro hzero
    apply hminimal.2
    simpa [hzero] using hchildSheet
  exact zmod2_eq_one_of_ne_zero _ hne

omit [Fintype V] in
/-- At a complete-fan minimum every legal move has separator increment one.
Any silent legal edge would expose a lower separator-one child. -/
theorem separatorOneImmediateMinimal_answer_increment_eq_one (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (hseat : s.toMove = seat)
    (hasMove : ∃ m u, publicStep s m = some u)
    (children : ∀ m u, publicStep s m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicySeparatorOneImmediateMinimal d ell seat
      (.answer s hseat hasMove children))
    (m : Move V) (u : PublicState V)
    (hstep : publicStep s m = some u) :
    publicSeparatorEvaluation d ell (moveLiveStar s.toZeroState m) = 1 := by
  have hchildren :=
    (publicPolicySeparatorSheet_answer_iff
      d ell seat hseat hasMove children 1).1 hminimal.1
  have hchildSheet := hchildren m u hstep
  have hne : publicSeparatorEvaluation d ell
      (moveLiveStar s.toZeroState m) ≠ 0 := by
    intro hzero
    apply hminimal.2 m u hstep
    simpa [hzero] using hchildSheet
  exact zmod2_eq_one_of_ne_zero _ hne

omit [Fintype V] in
/-- A selected-move minimum selects a real OPEN.  In particular it cannot
select the dummy, CLOSE, or PASS.  The dummy need not yet be consumed. -/
theorem separatorOneImmediateMinimal_choose_real_open (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s s' : PublicState V} (hseat : s.toMove ≠ seat)
    (m : Move V) (hstep : publicStep s m = some s')
    (child : PublicPolicy seat s')
    (hminimal : PublicPolicySeparatorOneImmediateMinimal d ell seat
      (.choose s hseat m s' hstep child)) :
    ∃ v ≠ d, m = .open v := by
  have hone := separatorOneImmediateMinimal_choose_increment_eq_one
    d ell seat hseat m hstep child hminimal
  cases m with
  | close =>
      simp [publicSeparatorEvaluation, moveLiveStar] at hone
  | pass =>
      simp [publicSeparatorEvaluation, moveLiveStar] at hone
  | «open» v =>
      refine ⟨v, ?_, rfl⟩
      intro hv
      subst v
      rw [moveLiveStar, publicSeparatorEvaluation,
        realEdgeProjection_liveStarVector_dummy, map_zero] at hone
      exact zero_ne_one hone

omit [Fintype V] in
/-- A complete-fan minimum has no legal silent transition. -/
theorem separatorOneImmediateMinimal_answer_no_silent_legal (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (hseat : s.toMove = seat)
    (hasMove : ∃ m u, publicStep s m = some u)
    (children : ∀ m u, publicStep s m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicySeparatorOneImmediateMinimal d ell seat
      (.answer s hseat hasMove children))
    (m : Move V) (u : PublicState V)
    (hstep : publicStep s m = some u) :
    publicSeparatorEvaluation d ell (moveLiveStar s.toZeroState m) ≠ 0 := by
  rw [separatorOneImmediateMinimal_answer_increment_eq_one
    d ell seat hseat hasMove children hminimal m u hstep]
  exact one_ne_zero

omit [Fintype V] in
/-- In particular, the isolated coordinate has already been consumed at a
complete-fan separator-one minimum.  If it were untouched, its legal OPEN
would be silent. -/
theorem separatorOneImmediateMinimal_answer_dummy_consumed (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (hseat : s.toMove = seat)
    (hasMove : ∃ m u, publicStep s m = some u)
    (children : ∀ m u, publicStep s m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicySeparatorOneImmediateMinimal d ell seat
      (.answer s hseat hasMove children)) :
    d ∉ s.untouched := by
  intro hd
  let u : PublicState V := {
    untouched := s.untouched.erase d
    queue := s.queue ++ [d]
    ko := s.queue.isEmpty
    toMove := !s.toMove }
  have hstep : publicStep s (.open d) = some u := by
    simp [publicStep, u, hd]
  have hne := separatorOneImmediateMinimal_answer_no_silent_legal
    d ell seat hseat hasMove children hminimal (.open d) u hstep
  apply hne
  rw [moveLiveStar, publicSeparatorEvaluation,
    realEdgeProjection_liveStarVector_dummy, map_zero]

omit [Fintype V] in
/-- CLOSE cannot be legal at a complete-fan separator-one minimum. -/
theorem separatorOneImmediateMinimal_answer_no_close (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (hseat : s.toMove = seat)
    (hasMove : ∃ m u, publicStep s m = some u)
    (children : ∀ m u, publicStep s m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicySeparatorOneImmediateMinimal d ell seat
      (.answer s hseat hasMove children)) :
    ∀ u, publicStep s .close ≠ some u := by
  intro u hstep
  have hne := separatorOneImmediateMinimal_answer_no_silent_legal
    d ell seat hseat hasMove children hminimal .close u hstep
  exact hne (by simp [publicSeparatorEvaluation, moveLiveStar])

omit [Fintype V] in
/-- PASS cannot be legal at a complete-fan separator-one minimum. -/
theorem separatorOneImmediateMinimal_answer_no_pass (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (hseat : s.toMove = seat)
    (hasMove : ∃ m u, publicStep s m = some u)
    (children : ∀ m u, publicStep s m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicySeparatorOneImmediateMinimal d ell seat
      (.answer s hseat hasMove children)) :
    ∀ u, publicStep s .pass ≠ some u := by
  intro u hstep
  have hne := separatorOneImmediateMinimal_answer_no_silent_legal
    d ell seat hseat hasMove children hminimal .pass u hstep
  exact hne (by simp [publicSeparatorEvaluation, moveLiveStar])

omit [Fintype V] in
/-- With reachability coherence restored, the full-fan minimum is exactly at
an empty queue or at a protected singleton queue, and at least one real OPEN
remains.  This is the separator-side analogue of the operational bad-normal
shape. -/
theorem separatorOneImmediateMinimal_answer_public_shape (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (hseat : s.toMove = seat)
    (hasMove : ∃ m u, publicStep s m = some u)
    (children : ∀ m u, publicStep s m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicySeparatorOneImmediateMinimal d ell seat
      (.answer s hseat hasMove children))
    (hcoherent : Coherent s.toZeroState) :
    s.untouched.Nonempty ∧ d ∉ s.untouched ∧
      (s.queue = [] ∨ ∃ f, s.queue = [f] ∧ s.ko = true) := by
  have hnoClose := separatorOneImmediateMinimal_answer_no_close
    d ell seat hseat hasMove children hminimal
  have hnoPass := separatorOneImmediateMinimal_answer_no_pass
    d ell seat hseat hasMove children hminimal
  have hU : s.untouched.Nonempty := by
    obtain ⟨m, u, hstep⟩ := hasMove
    cases m with
    | «open» v =>
        by_cases hv : v ∈ s.untouched
        · exact ⟨v, hv⟩
        · simp [publicStep, hv] at hstep
    | close => exact False.elim (hnoClose u hstep)
    | pass => exact False.elim (hnoPass u hstep)
  refine ⟨hU,
    separatorOneImmediateMinimal_answer_dummy_consumed
      d ell seat hseat hasMove children hminimal, ?_⟩
  cases hq : s.queue with
  | nil => exact Or.inl rfl
  | cons f q =>
      right
      cases hk : s.ko with
      | false =>
          let u : PublicState V :=
            ⟨s.untouched, q, false, !s.toMove⟩
          have hstep : publicStep s .close = some u := by
            simp [publicStep, hq, hk, u]
          exact False.elim (hnoClose u hstep)
      | true =>
          obtain ⟨v, hv⟩ := hcoherent.2 hk
          refine ⟨v, ?_, rfl⟩
          simpa [PublicState.toZeroState, hq] using hv

/-! ## The first retained complete fan below a global minimum -/

/-- Rank of a public state, definitionally the concrete FIFO rank after
installing score zero. -/
def publicSeparatorRank (s : PublicState V) : Nat := rank s.toZeroState

omit [Fintype V] in
theorem publicSeparatorRank_step_lt {s u : PublicState V} {m : Move V}
    (hstep : publicStep s m = some u) :
    publicSeparatorRank u < publicSeparatorRank s := by
  let G : SimpleGraph V := ⊥
  have hpublic : publicStep s.toZeroState.public m = some u := by
    simpa [PublicState.toZeroState, State.public] using hstep
  let t := concreteStepOfPublic G s.toZeroState m u hpublic
  have htstep : step G s.toZeroState m = some t :=
    concreteStepOfPublic_step G s.toZeroState m u hpublic
  have htrank := rank_step_lt htstep
  have htpublic : t.public = u :=
    concreteStepOfPublic_public G s.toZeroState m u hpublic
  change rank u.toZeroState < rank s.toZeroState
  rw [← htpublic]
  have hrank : rank t.public.toZeroState = rank t := by
    obtain ⟨U, q, ko, turn, score⟩ := t
    rfl
  rw [hrank]
  exact htrank

/-- A sheet-one occurrence minimal among every proper descendant occurrence,
not merely among its immediate children. -/
def PublicPolicySeparatorOneRankMinimal (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (policy : PublicPolicy seat s) : Prop :=
  PublicPolicySeparatorSheet d ell seat policy 1 ∧
    ∀ {u : PublicState V} (desc : PublicPolicy seat u),
      PublicPolicyNode seat policy desc →
        publicSeparatorRank u < publicSeparatorRank s →
          ¬PublicPolicySeparatorSheet d ell seat desc 1

omit [Fintype V] in
theorem PublicPolicyNode.trans
    {seat : Bool} {r s u : PublicState V}
    {root : PublicPolicy seat r} {middle : PublicPolicy seat s}
    {desc : PublicPolicy seat u}
    (hroot : PublicPolicyNode seat root middle)
    (htail : PublicPolicyNode seat middle desc) :
    PublicPolicyNode seat root desc := by
  induction hroot with
  | root => simpa using htail
  | choose _ ih => exact .choose (ih htail)
  | answer _ ih => exact .answer (ih htail)

omit [Fintype V] in
/-- Every sheet-one public policy has a rank-minimal sheet-one occurrence in
its exact history ancestry. -/
theorem PublicPolicySeparatorSheet.exists_rankMinimalOne (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} (policy : PublicPolicy seat s)
    (hsheet : PublicPolicySeparatorSheet d ell seat policy 1) :
    ∃ (u : PublicState V) (desc : PublicPolicy seat u),
      PublicPolicyNode seat policy desc ∧
        PublicPolicySeparatorOneRankMinimal d ell seat desc := by
  classical
  let P : Nat → Prop := fun n ↦
    ∃ (u : PublicState V) (desc : PublicPolicy seat u),
      PublicPolicyNode seat policy desc ∧
        PublicPolicySeparatorSheet d ell seat desc 1 ∧
          publicSeparatorRank u = n
  have hP : ∃ n, P n :=
    ⟨publicSeparatorRank s, s, policy, .root policy, hsheet, rfl⟩
  let n := Nat.find hP
  obtain ⟨u, desc, hnode, husheet, hurank⟩ := Nat.find_spec hP
  refine ⟨u, desc, hnode, husheet, ?_⟩
  intro v tail htail hlt hvsheet
  have hvnode : PublicPolicyNode seat policy tail := hnode.trans htail
  have hvP : P (publicSeparatorRank v) :=
    ⟨v, tail, hvnode, hvsheet, rfl⟩
  have hnle : n ≤ publicSeparatorRank v := Nat.find_min' hP hvP
  have hule : publicSeparatorRank u ≤ publicSeparatorRank v := by
    simpa [n, hurank] using hnle
  exact (Nat.not_lt_of_ge hule) hlt

omit [Fintype V] in
/-- Rank minimality implies the earlier immediate-minimal interface. -/
theorem PublicPolicySeparatorOneRankMinimal.immediate
    (d : V) (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s : PublicState V} {policy : PublicPolicy seat s}
    (hminimal : PublicPolicySeparatorOneRankMinimal d ell seat policy) :
    PublicPolicySeparatorOneImmediateMinimal d ell seat policy := by
  refine ⟨hminimal.1, ?_⟩
  cases policy with
  | terminal => trivial
  | choose s hseat m u hstep child =>
      exact hminimal.2 child (.choose (.root child))
        (publicSeparatorRank_step_lt hstep)
  | answer s hseat hasMove children =>
      intro m u hstep
      exact hminimal.2 (children m u hstep) (.answer (.root _))
        (publicSeparatorRank_step_lt hstep)

omit [Fintype V] in
/-- Below a rank-minimal selected real unit OPEN, every legal move in its
complete child fan has separator increment zero.  A unit child edge would
create a lower sheet-one grandchild. -/
theorem separatorRankMinimal_choose_answer_child_increment_zero (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s t : PublicState V} (hseat : s.toMove ≠ seat)
    (v : V) (hstep : publicStep s (.open v) = some t)
    (hturn : t.toMove = seat)
    (hasMove : ∃ m u, publicStep t m = some u)
    (children : ∀ m u, publicStep t m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicySeparatorOneRankMinimal d ell seat
      (.choose s hseat (.open v) t hstep
        (.answer t hturn hasMove children)))
    (m : Move V) (u : PublicState V)
    (hmstep : publicStep t m = some u) :
    publicSeparatorEvaluation d ell (moveLiveStar t.toZeroState m) = 0 := by
  have himmediate := hminimal.immediate d ell seat
  have hvone := separatorOneImmediateMinimal_choose_increment_eq_one
    d ell seat hseat (.open v) hstep (.answer t hturn hasMove children)
      himmediate
  have htSheet : PublicPolicySeparatorSheet d ell seat
      (.answer t hturn hasMove children) 0 := by
    have hchild := (publicPolicySeparatorSheet_choose_iff
      d ell seat hseat (.open v) hstep
        (.answer t hturn hasMove children) 1).1 hminimal.1
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    simpa [hvone, h11] using hchild
  have huSheet := (publicPolicySeparatorSheet_answer_iff
    d ell seat hturn hasMove children 0).1 htSheet m u hmstep
  by_contra hzero
  have hmone := zmod2_eq_one_of_ne_zero _ hzero
  have huOne : PublicPolicySeparatorSheet d ell seat
      (children m u hmstep) 1 := by
    simpa [hmone] using huSheet
  apply hminimal.2 (children m u hmstep)
    (.choose (.answer (.root _)))
    (lt_trans (publicSeparatorRank_step_lt hmstep)
      (publicSeparatorRank_step_lt hstep))
  exact huOne

omit [Fintype V] in
/-- The one-step/two-step contradiction succeeds at an empty queue.  A
rank-minimal selected unit OPEN cannot start a FIFO block: handshaking forces
another unit live star among the complete real OPEN fan, while global
minimality forces every such child increment to zero.  Therefore the exact
remaining obstruction necessarily carries a nonempty earlier queue. -/
theorem separatorRankMinimal_choose_answer_queue_nonempty (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s t : PublicState V} (hseat : s.toMove ≠ seat)
    (v : V) (hstep : publicStep s (.open v) = some t)
    (hturn : t.toMove = seat)
    (hasMove : ∃ m u, publicStep t m = some u)
    (children : ∀ m u, publicStep t m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicySeparatorOneRankMinimal d ell seat
      (.choose s hseat (.open v) t hstep
        (.answer t hturn hasMove children))) :
    s.queue ≠ [] := by
  intro hqueue
  have himmediate := hminimal.immediate d ell seat
  have hvone := separatorOneImmediateMinimal_choose_increment_eq_one
    d ell seat hseat (.open v) hstep (.answer t hturn hasMove children)
      himmediate
  simp only [publicStep] at hstep
  split at hstep
  · rename_i hv
    cases hstep
    have hopenZero : ∀ z ∈ s.untouched.erase v,
        publicSeparatorEvaluation d ell
          (liveStarVector s.untouched z) = 0 := by
      intro z hz
      let u : PublicState V := {
        untouched := (s.untouched.erase v).erase z
        queue := (s.queue ++ [v]) ++ [z]
        ko := false
        toMove := !(!s.toMove) }
      have hzstep : publicStep
          (⟨s.untouched.erase v, s.queue ++ [v],
            s.queue.isEmpty, !s.toMove⟩ : PublicState V)
          (.open z) = some u := by
        simp [publicStep, u, hz]
      have hzero := separatorRankMinimal_choose_answer_child_increment_zero
        d ell seat hseat v
          (by simp [publicStep, hv]) hturn hasMove children
          hminimal (.open z) u hzstep
      have hlive : liveSet
          (⟨s.untouched.erase v, s.queue ++ [v],
            s.queue.isEmpty, !s.toMove⟩ : PublicState V).toZeroState =
          s.untouched := by
        simp [liveSet, PublicState.toZeroState, hqueue,
          Finset.insert_erase hv]
      simpa [moveLiveStar, hlive] using hzero
    have htotal :
        ∑ z ∈ s.untouched,
          publicSeparatorEvaluation d ell
            (liveStarVector s.untouched z) = 0 := by
      change ∑ z ∈ s.untouched,
          ell (realEdgeProjection d (liveStarVector s.untouched z)) = 0
      rw [← map_sum, ← map_sum, sum_liveStarVector_eq_zero,
        map_zero, map_zero]
    rw [← Finset.sum_erase_add _ _ hv] at htotal
    have herase :
        ∑ z ∈ s.untouched.erase v,
          publicSeparatorEvaluation d ell
            (liveStarVector s.untouched z) = 0 :=
      Finset.sum_eq_zero hopenZero
    rw [herase, zero_add] at htotal
    have hvstar : moveLiveStar s.toZeroState (.open v) =
        liveStarVector s.untouched v := by
      simp [moveLiveStar, liveSet, PublicState.toZeroState, hqueue]
    rw [hvstar] at hvone
    rw [hvone] at htotal
    exact one_ne_zero htotal
  · contradiction

omit [Fintype V] in
/-- OPEN preserves the public live carrier exactly. -/
theorem liveSet_toZeroState_publicStep_open
    {s t : PublicState V} {v : V}
    (hstep : publicStep s (.open v) = some t) :
    liveSet t.toZeroState = liveSet s.toZeroState := by
  classical
  simp only [publicStep] at hstep
  split at hstep
  · rename_i hv
    cases hstep
    ext z
    simp [liveSet, PublicState.toZeroState]
    constructor
    · intro h
      rcases h with h | h
      · subst z
        exact Or.inl hv
      · rcases h with ⟨_, hz⟩ | hzq
        · exact Or.inl hz
        · exact Or.inr hzq
    · intro h
      rcases h with hzU | hzq
      · by_cases hzv : z = v
        · exact Or.inl hzv
        · exact Or.inr (Or.inl ⟨hzv, hzU⟩)
      · exact Or.inr (Or.inr hzq)
  · contradiction

omit [Fintype V] in
/-- Exact separator debt left by the failed empty-queue contradiction.  At a
coherent globally minimal selected-unit occurrence, every untouched reply
star is zero after the OPEN, and the entire remaining unit is carried by the
vertices already in the FIFO queue. -/
theorem separatorRankMinimal_choose_answer_queued_debt_eq_one (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (seat : Bool) {s t : PublicState V} (hseat : s.toMove ≠ seat)
    (v : V) (hstep : publicStep s (.open v) = some t)
    (hturn : t.toMove = seat)
    (hasMove : ∃ m u, publicStep t m = some u)
    (children : ∀ m u, publicStep t m = some u → PublicPolicy seat u)
    (hminimal : PublicPolicySeparatorOneRankMinimal d ell seat
      (.choose s hseat (.open v) t hstep
        (.answer t hturn hasMove children)))
    (hcoherent : Coherent s.toZeroState) :
    ∑ q ∈ s.queue.toFinset,
      publicSeparatorEvaluation d ell
        (liveStarVector (liveSet s.toZeroState) q) = 1 := by
  have himmediate := hminimal.immediate d ell seat
  have hvone := separatorOneImmediateMinimal_choose_increment_eq_one
    d ell seat hseat (.open v) hstep (.answer t hturn hasMove children)
      himmediate
  have hlive := liveSet_toZeroState_publicStep_open hstep
  have hv : v ∈ s.untouched := by
    simp only [publicStep] at hstep
    split at hstep
    · assumption
    · contradiction
  have htU : t.untouched = s.untouched.erase v := by
    simp only [publicStep] at hstep
    split at hstep
    · cases hstep
      rfl
    · contradiction
  have hopenZero : ∀ z ∈ s.untouched.erase v,
      publicSeparatorEvaluation d ell
        (liveStarVector (liveSet s.toZeroState) z) = 0 := by
    intro z hz
    have hzt : z ∈ t.untouched := by simpa [htU] using hz
    let u : PublicState V := {
      untouched := t.untouched.erase z
      queue := t.queue ++ [z]
      ko := t.queue.isEmpty
      toMove := !t.toMove }
    have hzstep : publicStep t (.open z) = some u := by
      simp [publicStep, u, hzt]
    have hzero := separatorRankMinimal_choose_answer_child_increment_zero
      d ell seat hseat v hstep hturn hasMove children hminimal
        (.open z) u hzstep
    rw [moveLiveStar, hlive] at hzero
    exact hzero
  have hUntouched :
      ∑ z ∈ s.untouched,
        publicSeparatorEvaluation d ell
          (liveStarVector (liveSet s.toZeroState) z) = 1 := by
    rw [← Finset.sum_erase_add _ _ hv,
      Finset.sum_eq_zero hopenZero, zero_add]
    simpa [moveLiveStar] using hvone
  have htotal :
      ∑ z ∈ liveSet s.toZeroState,
        publicSeparatorEvaluation d ell
          (liveStarVector (liveSet s.toZeroState) z) = 0 := by
    change ∑ z ∈ liveSet s.toZeroState,
        ell (realEdgeProjection d
          (liveStarVector (liveSet s.toZeroState) z)) = 0
    rw [← map_sum, ← map_sum,
      sum_liveStarVector_eq_zero, map_zero, map_zero]
  have hdisjoint : Disjoint s.untouched s.queue.toFinset :=
    hcoherent.1.2
  have hliveRoot : liveSet s.toZeroState =
      s.untouched ∪ s.queue.toFinset := rfl
  rw [hliveRoot] at hUntouched ⊢
  rw [hliveRoot, Finset.sum_union hdisjoint, hUntouched] at htotal
  by_contra hzero
  have hqzero := zmod2_eq_zero_of_ne_one _ hzero
  rw [hqzero, add_zero] at htotal
  exact one_ne_zero htotal

/-- The scalar memory update exposed by the exact recurrence. -/
def publicSeparatorStepBit (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (s : PublicState V) (m : Move V) (b : ZMod 2) : ZMod 2 :=
  b + publicSeparatorEvaluation d ell (moveLiveStar s.toZeroState m)

omit [Fintype V] in
@[simp] theorem publicSeparatorStepBit_close (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (s : PublicState V) (b : ZMod 2) :
    publicSeparatorStepBit d ell s .close b = b := by
  simp [publicSeparatorStepBit, publicSeparatorEvaluation, moveLiveStar]

omit [Fintype V] in
@[simp] theorem publicSeparatorStepBit_pass (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (s : PublicState V) (b : ZMod 2) :
    publicSeparatorStepBit d ell s .pass b = b := by
  simp [publicSeparatorStepBit, publicSeparatorEvaluation, moveLiveStar]

omit [Fintype V] in
/-- Opening the distinguished dummy is also invisible to every functional on
the real-edge quotient. -/
@[simp] theorem publicSeparatorStepBit_open_dummy (d : V)
    (ell : RealEdgeQuotient V d →ₗ[ZMod 2] ZMod 2)
    (s : PublicState V) (b : ZMod 2) :
    publicSeparatorStepBit d ell s (.open d) b = b := by
  rw [publicSeparatorStepBit, publicSeparatorEvaluation, moveLiveStar,
    realEdgeProjection_liveStarVector_dummy, map_zero, add_zero]

/-! ## Front-plus-bit is not a Markov memory -/

/-- The separator graph for the finite-memory obstruction: one real edge
`0--2`, with label `1` isolated. -/
def frontBitBoundaryGraph : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun x y ↦ x = 0 ∧ y = 2

theorem frontBitBoundaryGraph_dummyOne :
    IsDummy frontBitBoundaryGraph 1 := by
  intro v
  simp [frontBitBoundaryGraph, SimpleGraph.fromRel_adj]

/-- Both states have dummy front `1`; in the second, real vertex `2` has
already closed. -/
def frontBitLiveState : PublicState (Fin 3) :=
  ⟨{0, 2}, [1], false, false⟩

def frontBitSpentState : PublicState (Fin 3) :=
  ⟨{0}, [1], false, false⟩

theorem frontBitBoundary_same_front :
    frontBitLiveState.queue.head? = frontBitSpentState.queue.head? := by
  rfl

theorem frontBitBoundary_open_zero_legal :
    (∃ u, publicStep frontBitLiveState (.open 0) = some u) ∧
      (∃ u, publicStep frontBitSpentState (.open 0) = some u) := by
  constructor <;> simp [publicStep, frontBitLiveState, frontBitSpentState]

theorem frontBitLiveState_wellFormed :
    WellFormed frontBitLiveState.toZeroState := by
  change [1].Nodup ∧
    Disjoint ({0, 2} : Finset (Fin 3)) [1].toFinset
  decide

theorem frontBitSpentState_wellFormed :
    WellFormed frontBitSpentState.toZeroState := by
  change [1].Nodup ∧
    Disjoint ({0} : Finset (Fin 3)) [1].toFinset
  decide

theorem frontBitLiveState_coherent :
    Coherent frontBitLiveState.toZeroState := by
  exact ⟨frontBitLiveState_wellFormed, by simp [frontBitLiveState,
    PublicState.toZeroState]⟩

theorem frontBitSpentState_coherent :
    Coherent frontBitSpentState.toZeroState := by
  exact ⟨frontBitSpentState_wellFormed, by simp [frontBitSpentState,
    PublicState.toZeroState]⟩

/-- The same real OPEN has separator increment one when vertex `2` is still
live and zero after `2` has closed. -/
theorem frontBitBoundary_open_increment_ne :
    graphEvaluation frontBitBoundaryGraph
        (moveLiveStar frontBitLiveState.toZeroState (.open 0)) ≠
      graphEvaluation frontBitBoundaryGraph
        (moveLiveStar frontBitSpentState.toZeroState (.open 0)) := by
  rw [graphEvaluation_moveLiveStar _ _ _ frontBitLiveState_wellFormed,
    graphEvaluation_moveLiveStar _ _ _ frontBitSpentState_wellFormed]
  simp [liveDegree, queueCut, flip, frontBitBoundaryGraph,
    frontBitLiveState, frontBitSpentState, PublicState.toZeroState,
    SimpleGraph.fromRel_adj]
  native_decide

/-- Consequently no update rule receiving only the current front, the old
separator bit, and the move can reproduce the true separator bit increment
on all coherent states. -/
theorem no_front_bit_only_separator_update :
    ¬∃ update : Option (Fin 3) → ZMod 2 → Move (Fin 3) → ZMod 2,
      ∀ (s : PublicState (Fin 3)) (b : ZMod 2) (m : Move (Fin 3)),
        Coherent s.toZeroState →
        (∃ u, publicStep s m = some u) →
        update s.queue.head? b m =
          b + graphEvaluation frontBitBoundaryGraph
            (moveLiveStar s.toZeroState m) := by
  rintro ⟨update, hupdate⟩
  have hlive := hupdate frontBitLiveState 0 (.open 0)
    frontBitLiveState_coherent frontBitBoundary_open_zero_legal.1
  have hspent := hupdate frontBitSpentState 0 (.open 0)
    frontBitSpentState_coherent frontBitBoundary_open_zero_legal.2
  rw [frontBitBoundary_same_front] at hlive
  rw [hlive] at hspent
  simp only [zero_add] at hspent
  exact frontBitBoundary_open_increment_ne hspent

end

end Ogdoad.Fifo
