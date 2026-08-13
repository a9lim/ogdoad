import Ogdoad.FifoAffine
import Ogdoad.FifoHub

/-!
# Graph-free affine response spaces of public FIFO policies

The universal affine route is independent of graph scores.  It concerns a
fixed policy for the player outside `seat` in the public FIFO game: policy
nodes retain one selected legal child, while `seat` nodes retain the complete
legal fan.  Terminal leaves carry zero and every edge adds the usual universal
live-star vector.  `PublicPolicyAffineMoment` is the affine hull of those
compatible terminal moments.

The target assertion is that after projecting away a distinguished label,
zero belongs to this affine space at the initial public root.  Unlike
`AffineResponseMoment`, this definition has no graph and no terminal payoff
hypothesis.  If the target is proved, every alleged isolated-dummy odd strategy
forgets to one of these public policies, immediately contradicting its checked
projected affine obstruction.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A graph-free policy tree: `seat` owns universal nodes and the player
outside `seat` selects one legal public move. -/
inductive PublicPolicy (seat : Bool) : PublicState V → Type u
  | terminal (s : PublicState V)
      (ht : s.untouched = ∅ ∧ s.queue = []) : PublicPolicy seat s
  | choose (s : PublicState V) (hseat : s.toMove ≠ seat)
      (m : Move V) (s' : PublicState V)
      (hstep : publicStep s m = some s')
      (child : PublicPolicy seat s') : PublicPolicy seat s
  | answer (s : PublicState V) (hseat : s.toMove = seat)
      (hasMove : ∃ m s', publicStep s m = some s')
      (children : ∀ m s', publicStep s m = some s' →
        PublicPolicy seat s') : PublicPolicy seat s

omit [Fintype V] in
/-- The affine hull of universal live-star moments of all terminal schedules
compatible with one public policy. -/
def PublicState.toZeroState (s : PublicState V) : State V where
  untouched := s.untouched
  queue := s.queue
  ko := s.ko
  toMove := s.toMove
  score := 0

omit [Fintype V] in
@[simp] theorem moveLiveStar_public_toZeroState (s : State V) (m : Move V) :
    moveLiveStar s.public.toZeroState m = moveLiveStar s m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m <;> rfl

omit [Fintype V] in
inductive PublicPolicyAffineMoment (seat : Bool) :
    {s : PublicState V} → PublicPolicy seat s → EdgeVector V → Prop
  | terminal (s : PublicState V) (ht : s.untouched = ∅ ∧ s.queue = []) :
      PublicPolicyAffineMoment seat (.terminal s ht) 0
  | choose {s s' : PublicState V} {hseat : s.toMove ≠ seat}
      {m : Move V} {hstep : publicStep s m = some s'}
      {child : PublicPolicy seat s'} {z : EdgeVector V}
      (tail : PublicPolicyAffineMoment seat child z) :
      PublicPolicyAffineMoment seat
        (.choose s hseat m s' hstep child)
        (moveLiveStar s.toZeroState m + z)
  | answerChild {s s' : PublicState V} {hseat : s.toMove = seat}
      {hasMove : ∃ m u, publicStep s m = some u}
      {children : ∀ m u, publicStep s m = some u → PublicPolicy seat u}
      {m : Move V} {hstep : publicStep s m = some s'} {z : EdgeVector V}
      (tail : PublicPolicyAffineMoment seat (children m s' hstep) z) :
      PublicPolicyAffineMoment seat
        (.answer s hseat hasMove children)
        (moveLiveStar s.toZeroState m + z)
  | ternary {s : PublicState V} {policy : PublicPolicy seat s}
      {x y z : EdgeVector V}
      (hx : PublicPolicyAffineMoment seat policy x)
      (hy : PublicPolicyAffineMoment seat policy y)
      (hz : PublicPolicyAffineMoment seat policy z) :
      PublicPolicyAffineMoment seat policy (x + y + z)

/-- Project away every dummy-incident and diagonal coordinate. -/
def ProjectedPublicPolicyAffineMoment (d : V) (seat : Bool)
    {s : PublicState V} (policy : PublicPolicy seat s)
    (q : RealEdgeQuotient V d) : Prop :=
  ∃ z, PublicPolicyAffineMoment seat policy z ∧ realEdgeProjection d z = q

/-- Universal graph-free affine conjecture.  This is a definition of the
new proof target, not a theorem. -/
def UniversalPublicPolicyAffine : Prop :=
  ∀ (V : Type u) (_ : Fintype V) (_ : DecidableEq V) (d : V)
    (seat : Bool)
    (policy : PublicPolicy seat (initial (V := V)).public),
    ProjectedPublicPolicyAffineMoment d seat policy 0

omit [Fintype V] in
/-- A public successor has a unique concrete successor once the source graph
and source score are restored. -/
theorem exists_concreteStep_of_publicStep (G : SimpleGraph V) (s : State V)
    (m : Move V) (u : PublicState V)
    (hpublic : publicStep s.public m = some u) :
    ∃ t, step G s m = some t ∧ t.public = u := by
  have hmap : (step G s m).map State.public = some u := by
    rw [step_public]
    exact hpublic
  cases hstep : step G s m with
  | none => simp [hstep] at hmap
  | some t =>
      have htpublic : t.public = u := by simpa [hstep] using hmap
      exact ⟨t, rfl, htpublic⟩

omit [Fintype V] in
noncomputable def concreteStepOfPublic (G : SimpleGraph V) (s : State V)
    (m : Move V) (u : PublicState V)
    (hpublic : publicStep s.public m = some u) : State V :=
  Classical.choose (exists_concreteStep_of_publicStep G s m u hpublic)

omit [Fintype V] in
theorem concreteStepOfPublic_step (G : SimpleGraph V) (s : State V)
    (m : Move V) (u : PublicState V)
    (hpublic : publicStep s.public m = some u) :
    step G s m = some (concreteStepOfPublic G s m u hpublic) :=
  (Classical.choose_spec
    (exists_concreteStep_of_publicStep G s m u hpublic)).1

omit [Fintype V] in
theorem concreteStepOfPublic_public (G : SimpleGraph V) (s : State V)
    (m : Move V) (u : PublicState V)
    (hpublic : publicStep s.public m = some u) :
    (concreteStepOfPublic G s m u hpublic).public = u :=
  (Classical.choose_spec
    (exists_concreteStep_of_publicStep G s m u hpublic)).2

omit [Fintype V] in
/-- Any concrete legal move supplies a public legal move. -/
theorem publicHasMove_of_hasMove (G : SimpleGraph V) (s : State V)
    (hasMove : ∃ m t, step G s m = some t) :
    ∃ m u, publicStep s.public m = some u := by
  obtain ⟨m, t, hstep⟩ := hasMove
  exact ⟨m, t.public, by rw [← step_public G s m, hstep]; rfl⟩

omit [Fintype V] in
/-- Forgetting scores turns an exact odd strategy into a graph-free public
policy with identical quantifier structure. -/
def OddStrategy.toPublicPolicy
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (strategy : OddStrategy G seat s) : PublicPolicy seat s.public :=
  match strategy with
  | .terminal s ht hs =>
      .terminal s.public (by simpa [Terminal, State.public] using ht)
  | .choose s hseat m t hstep child =>
      .choose s.public hseat m t.public
        (by rw [← step_public G s m, hstep]; rfl) child.toPublicPolicy
  | .answer s hseat hasMove children =>
      .answer s.public hseat (publicHasMove_of_hasMove G s hasMove)
        (fun m u hpublic ↦
          let t := concreteStepOfPublic G s m u hpublic
          cast (congrArg (PublicPolicy seat)
              (concreteStepOfPublic_public G s m u hpublic))
            (children m t
              (concreteStepOfPublic_step G s m u hpublic)).toPublicPolicy)

omit [Fintype V] in
private theorem PublicPolicyAffineMoment.toAffineResponseMoment_aux
    {G : SimpleGraph V} {seat : Bool} {u : PublicState V}
    {policy : PublicPolicy seat u} {z : EdgeVector V}
    (h : PublicPolicyAffineMoment seat policy z) :
    ∀ {s : State V} (strategy : OddStrategy G seat s),
      s.public = u → HEq strategy.toPublicPolicy policy →
      AffineResponseMoment G seat strategy z := by
  induction h with
  | terminal u ht =>
      intro s strategy hsu hp
      cases hsu
      cases strategy with
      | terminal s ht' hs => exact .terminal s ht' hs
      | choose s hseat m t hstep child => cases hp
      | answer s hseat hasMove children => cases hp
  | choose tail ih =>
      intro s strategy hsu hp
      cases hsu
      cases strategy with
      | terminal s ht hs => cases hp
      | choose s hseat m t hstep child =>
          cases hp
          apply AffineResponseMoment.choose
          apply ih child
          · rfl
          · rfl
      | answer s hseat hasMove children => cases hp
  | @answerChild ps ps' hseatP hasMoveP childrenP mP hstepP zP tail ih =>
      intro s strategy hsu hp
      cases hsu
      cases strategy with
      | terminal s ht hs => cases hp
      | choose s hseat m t hstep child => cases hp
      | answer s hseat hasMove children =>
          cases hp
          let t := concreteStepOfPublic G s mP ps' hstepP
          have htstep : step G s mP = some t :=
            concreteStepOfPublic_step G s mP ps' hstepP
          have htpublic : t.public = ps' :=
            concreteStepOfPublic_public G s mP ps' hstepP
          rw [moveLiveStar_public_toZeroState]
          apply AffineResponseMoment.answerChild (hstep := htstep)
          apply ih (children mP t htstep) htpublic
          change (children mP t htstep).toPublicPolicy ≍
            cast _ (children mP t htstep).toPublicPolicy
          exact (cast_heq _ _).symm
  | ternary hx hy hz ihx ihy ihz =>
      intro s strategy hsu hp
      exact .ternary (ihx strategy hsu hp) (ihy strategy hsu hp)
        (ihz strategy hsu hp)

omit [Fintype V] in
/-- The graph-free affine moment relation on a forgotten odd strategy is
exactly strong enough to reconstruct the corresponding graph-indexed affine
response moment.  In particular, forgetting the score tree loses no schedule
or affine-hull information needed by `AffineResponseMoment`. -/
theorem PublicPolicyAffineMoment.toAffineResponseMoment
    {G : SimpleGraph V} {seat : Bool} {s : State V}
    (strategy : OddStrategy G seat s) {z : EdgeVector V}
    (h : PublicPolicyAffineMoment seat strategy.toPublicPolicy z) :
    AffineResponseMoment G seat strategy z :=
  h.toAffineResponseMoment_aux strategy rfl (HEq.rfl)

/-- The universal graph-free affine statement is sufficient for FIFO
linking.  An alleged odd counterstrategy forgets to a public policy; a
projected-zero public moment then lifts back to the forbidden projected-zero
response moment of that same counterstrategy. -/
theorem UniversalPublicPolicyAffine.implies_fifoLinking
    (h : UniversalPublicPolicyAffine.{u}) : FifoLinkingTheorem.{u} := by
  intro V instF instD G d hd seat
  rw [linking_at_iff_noOddCounterstrategy hd seat]
  intro hodd
  obtain ⟨strategy⟩ := hodd.nonempty_oddStrategy
  obtain ⟨z, hzPublic, hzProjection⟩ :=
    h V instF instD d seat strategy.toPublicPolicy
  exact no_zero_projectedAffineResponseMoment_initial hd
    ⟨z, hzPublic.toAffineResponseMoment strategy, hzProjection⟩

end

end Ogdoad.Fifo
