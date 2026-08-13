import Ogdoad.FifoStrategy
import Ogdoad.FifoRootSelector

/-!
# Label equivariance for FIFO schedules

This file isolates the score-independent part of a label-transposition
argument.  A permutation acts simultaneously on the graph, public state, and
move.  The FIFO transition then commutes with that action, including the
charged score coordinate.  Consequently legality and the entire public move
schedule are invariant under relabelling.

The result does not compare two different edge sets on the same labels.  A
hub argument must separately identify the score defect created when only the
labels in a fixed schedule are transposed while the graph is held fixed.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Relabel a graph by a permutation of its vertices. -/
def relabelGraph (τ : Equiv.Perm V) (G : SimpleGraph V) : SimpleGraph V :=
  G.comap τ.symm

/-- Relabel the vertex payload of an OPEN; CLOSE and PASS have no payload. -/
def relabelMove (τ : Equiv.Perm V) : Move V → Move V
  | .open v => .open (τ v)
  | .close => .close
  | .pass => .pass

/-- Relabel every vertex coordinate of a FIFO state. -/
def relabelState (τ : Equiv.Perm V) (s : State V) : State V where
  untouched := s.untouched.map τ.toEmbedding
  queue := s.queue.map τ
  ko := s.ko
  toMove := s.toMove
  score := s.score

/-- Public FIFO data, with the accumulated graph-dependent score erased. -/
structure PublicState (V : Type*) where
  untouched : Finset V
  queue : List V
  ko : Bool
  toMove : Bool
deriving DecidableEq

/-- Forget only the accumulated score. -/
def State.public (s : State V) : PublicState V where
  untouched := s.untouched
  queue := s.queue
  ko := s.ko
  toMove := s.toMove

/-- Relabel public FIFO data. -/
def PublicState.relabel (τ : Equiv.Perm V) (s : PublicState V) : PublicState V where
  untouched := s.untouched.map τ.toEmbedding
  queue := s.queue.map τ
  ko := s.ko
  toMove := s.toMove

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem relabelState_public (τ : Equiv.Perm V) (s : State V) :
    (relabelState τ s).public = s.public.relabel τ := rfl

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem relabelMove_symm (τ : Equiv.Perm V) (m : Move V) :
    relabelMove τ.symm (relabelMove τ m) = m := by
  cases m <;> simp [relabelMove]

omit [Fintype V] [DecidableEq V] in
/-- Relabelling preserves the adjacency bit. -/
theorem adjacencyBit_relabelGraph (τ : Equiv.Perm V) (G : SimpleGraph V)
    (x y : V) :
    adjacencyBit (relabelGraph τ G) (τ x) (τ y) = adjacencyBit G x y := by
  classical
  simp only [adjacencyBit]
  simp [relabelGraph]

omit [Fintype V] [DecidableEq V] in
/-- Relabelling preserves a close charge when both the graph and untouched
set are transported. -/
theorem flip_relabelGraph (τ : Equiv.Perm V) (G : SimpleGraph V)
    (U : Finset V) (x : V) :
    flip (relabelGraph τ G) (U.map τ.toEmbedding) (τ x) = flip G U x := by
  classical
  unfold flip
  apply congrArg (fun n : Nat ↦ (n : ZMod 2))
  apply Finset.card_bij (fun y _ ↦ τ.symm y)
  · intro y hy
    have hyU : y ∈ U.map τ.toEmbedding := (Finset.mem_filter.mp hy).1
    have ⟨z, hzU, hz⟩ := Finset.mem_map.mp hyU
    subst y
    have hzAdj : (relabelGraph τ G).Adj (τ x) (τ z) :=
      (Finset.mem_filter.mp hy).2
    rw [Finset.mem_filter]
    exact ⟨by simpa using hzU, by simpa [relabelGraph] using hzAdj⟩
  · intro y₁ hy₁ y₂ hy₂ heq
    exact τ.symm.injective heq
  · intro z hz
    rw [Finset.mem_filter] at hz
    refine ⟨τ z, ?_, by simp⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_map.mpr ⟨z, hz.1, rfl⟩,
      by simpa [relabelGraph] using hz.2⟩

omit [Fintype V] in
/-- The full transition, including score, is equivariant when graph, state,
and move are relabelled together. -/
theorem step_relabel (τ : Equiv.Perm V) (G : SimpleGraph V)
    (s : State V) (m : Move V) :
    step (relabelGraph τ G) (relabelState τ s) (relabelMove τ m) =
      (step G s m).map (relabelState τ) := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [step, relabelMove, relabelState]
  | close =>
      cases q with
      | nil => simp [step, relabelMove, relabelState]
      | cons f q =>
          cases ko <;> simp [step, relabelMove, relabelState,
            flip_relabelGraph]
  | pass => simp [step, relabelMove, relabelState]

omit [Fintype V] in
/-- Exact legality equivalence under a label permutation. -/
theorem step_relabel_eq_some_iff (τ : Equiv.Perm V) (G : SimpleGraph V)
    (s t : State V) (m : Move V) :
    step (relabelGraph τ G) (relabelState τ s) (relabelMove τ m) =
        some (relabelState τ t) ↔
      step G s m = some t := by
  rw [step_relabel]
  constructor
  · intro h
    have hmap : (step G s m).map (relabelState τ) =
        some (relabelState τ t) := h
    obtain ⟨u, hu, heq⟩ := Option.map_eq_some_iff.mp hmap
    have : u = t := by
      obtain ⟨Uu, qu, kou, turnu, scoreu⟩ := u
      obtain ⟨Ut, qt, kot, turnt, scoret⟩ := t
      simp only [relabelState, State.mk.injEq] at heq
      rcases heq with ⟨hU, hq, hko, hturn, hscore⟩
      have hU' : Uu = Ut := (Finset.map_injective τ.toEmbedding) hU
      have hq' : qu = qt := (List.map_injective_iff.mpr τ.injective) hq
      subst Ut
      subst qt
      subst kot
      subst turnt
      subst scoret
      rfl
    simpa [this] using hu
  · intro h
    simp [h]

omit [Fintype V] in
/-- Public successor correspondence.  This is the score-erased theorem used
when the public schedule is transported before the graph-dependent terminal
score defect is analyzed separately. -/
theorem step_relabel_public (τ : Equiv.Perm V) (G : SimpleGraph V)
    (s t : State V) (m : Move V) (h : step G s m = some t) :
    ∃ t', step (relabelGraph τ G) (relabelState τ s) (relabelMove τ m) = some t' ∧
      t'.public = t.public.relabel τ := by
  exact ⟨relabelState τ t, (step_relabel_eq_some_iff τ G s t m).2 h, rfl⟩

/-- A legal finite FIFO move word. -/
inductive LegalTrace (G : SimpleGraph V) : State V → List (Move V) → State V → Prop
  | nil (s : State V) : LegalTrace G s [] s
  | cons {s t u : State V} {m : Move V} {ms : List (Move V)}
      (head : step G s m = some t) (tail : LegalTrace G t ms u) :
      LegalTrace G s (m :: ms) u

omit [Fintype V] in
/-- Relabelling transports every legal move word pointwise and transports its
endpoint. -/
theorem LegalTrace.relabel (τ : Equiv.Perm V) (G : SimpleGraph V) :
    ∀ {s t : State V} {ms : List (Move V)}, LegalTrace G s ms t →
      LegalTrace (relabelGraph τ G) (relabelState τ s)
        (ms.map (relabelMove τ)) (relabelState τ t) := by
  intro s t ms h
  induction h with
  | nil s => exact LegalTrace.nil _
  | cons hstep htail ih =>
      exact LegalTrace.cons ((step_relabel_eq_some_iff τ G _ _ _).2 hstep) ih

/-! ## Fixed-graph public equivariance

For a hub comparison the graph is held fixed.  Scores may therefore differ;
only the graph-independent public schedule is transported. -/

/-- The graph-free transition on public FIFO data. -/
def publicStep (s : PublicState V) : Move V → Option (PublicState V)
  | .open v =>
      if v ∈ s.untouched then
        some {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove }
      else none
  | .close =>
      match s.queue with
      | [] => none
      | _ :: q =>
          if s.ko then none else
            some {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove }
  | .pass =>
      if s.untouched = ∅ ∧ s.queue ≠ [] ∧ s.ko = true then
        some { s with ko := false, toMove := !s.toMove }
      else none

omit [Fintype V] in
/-- Forgetting the score after a concrete transition is exactly the
graph-free public transition. -/
theorem step_public (G : SimpleGraph V) (s : State V) (m : Move V) :
    (step G s m).map State.public = publicStep s.public m := by
  obtain ⟨U, q, ko, turn, score⟩ := s
  cases m with
  | «open» v => simp [step, publicStep, State.public]
  | close =>
      cases q with
      | nil => simp [step, publicStep, State.public]
      | cons f q => cases ko <;> simp [step, publicStep, State.public]
  | pass => simp [step, publicStep, State.public]

/-- Public states are related when `t` is obtained from `s` by relabelling
all vertex coordinates by `τ`.  Their scores are deliberately absent. -/
def PublicRelated (τ : Equiv.Perm V) (s t : State V) : Prop :=
  t.public = s.public.relabel τ

omit [Fintype V] in
/-- The graph-free public transition commutes with relabelling. -/
theorem publicStep_relabel (τ : Equiv.Perm V) (s : PublicState V)
    (m : Move V) :
    publicStep (s.relabel τ) (relabelMove τ m) =
      (publicStep s m).map (PublicState.relabel τ) := by
  obtain ⟨U, q, ko, turn⟩ := s
  cases m with
  | «open» v => simp [publicStep, PublicState.relabel, relabelMove]
  | close =>
      cases q with
      | nil => simp [publicStep, PublicState.relabel, relabelMove]
      | cons f q => cases ko <;> simp [publicStep, PublicState.relabel,
          relabelMove]
  | pass => simp [publicStep, PublicState.relabel, relabelMove]

omit [Fintype V] in
/-- Load-bearing fixed-graph hub lemma.  A legal move transports to the same
fixed graph under a public label permutation.  The successor score is not
related to the source score. -/
theorem step_publicRelated (τ : Equiv.Perm V) (G : SimpleGraph V)
    {s t s' : State V} {m : Move V}
    (hst : PublicRelated τ s t) (hs : step G s m = some s') :
    ∃ t', step G t (relabelMove τ m) = some t' ∧
      PublicRelated τ s' t' := by
  have hsPublic : publicStep s.public m = some s'.public := by
    rw [← step_public G s m, hs]
    rfl
  have htPublic : publicStep t.public (relabelMove τ m) =
      some (s'.public.relabel τ) := by
    rw [hst, publicStep_relabel, hsPublic]
    rfl
  have hmapped : (step G t (relabelMove τ m)).map State.public =
      some (s'.public.relabel τ) := by
    rw [step_public]
    exact htPublic
  obtain ⟨t', htStep, htEq⟩ := Option.map_eq_some_iff.mp hmapped
  exact ⟨t', htStep, htEq⟩

omit [Fintype V] in
/-- A complete legal move word transports pointwise under a label
permutation on the same fixed graph, with only public endpoints related. -/
theorem LegalTrace.relabel_fixedGraph (τ : Equiv.Perm V) (G : SimpleGraph V) :
    ∀ {s t u : State V} {ms : List (Move V)}, PublicRelated τ s t →
      LegalTrace G s ms u →
      ∃ v, LegalTrace G t (ms.map (relabelMove τ)) v ∧
        PublicRelated τ u v := by
  intro s t u ms hst htrace
  induction htrace generalizing t with
  | nil s => exact ⟨t, LegalTrace.nil t, hst⟩
  | @cons s s' u m ms hstep htail ih =>
      obtain ⟨t', htStep, hs't'⟩ := step_publicRelated τ G hst hstep
      obtain ⟨v, hvTrace, huv⟩ := ih hs't'
      exact ⟨v, LegalTrace.cons htStep hvTrace, huv⟩

omit [Fintype V] in
/-- The two candidate hub children are publicly related whenever the label
permutation preserves the real carrier, fixes the dummy and opener, and sends
the same-degree mate `y` to the outside reply `z`. -/
theorem afterTwoRealOpens_publicRelated (τ : Equiv.Perm V)
    (R : Finset V) (d x y z : V)
    (hR : R.map τ.toEmbedding = R) (hd : τ d = d) (hx : τ x = x)
    (hyz : τ y = z) :
    PublicRelated τ (afterTwoRealOpens R d x y)
      (afterTwoRealOpens R d x z) := by
  simp only [PublicRelated, afterTwoRealOpens, State.public,
    PublicState.relabel, PublicState.mk.injEq]
  constructor
  · have hd' : τ.toEmbedding d = d := hd
    have hx' : τ.toEmbedding x = x := hx
    have hyz' : τ.toEmbedding y = z := hyz
    have hbase :
        (insert d (R.erase x)).map τ.toEmbedding = insert d (R.erase x) := by
      rw [Finset.map_insert, Finset.map_erase, hR, hd', hx']
    calc
      (insert d (R.erase x)).erase z =
          ((insert d (R.erase x)).map τ.toEmbedding).erase
            (τ.toEmbedding y) := by
              rw [hbase, hyz']
      _ = ((insert d (R.erase x)).erase y).map τ.toEmbedding := by
            rw [Finset.map_erase]
  · simp [hx, hyz]

omit [Fintype V] [DecidableEq V] in
/-- Publicly related endpoints are terminal simultaneously. -/
theorem PublicRelated.terminal_iff {τ : Equiv.Perm V} {s t : State V}
    (h : PublicRelated τ s t) : Terminal t ↔ Terminal s := by
  simp only [PublicRelated, State.public, PublicState.relabel,
    PublicState.mk.injEq] at h
  rcases h with ⟨hU, hq, _, _⟩
  simp only [Terminal]
  constructor
  · rintro ⟨htU, htq⟩
    constructor
    · have : s.untouched.map τ.toEmbedding = ∅ := hU ▸ htU
      simpa using this
    · have : s.queue.map τ = [] := hq ▸ htq
      simpa using this
  · rintro ⟨hsU, hsq⟩
    constructor
    · rw [hU, hsU]
      rfl
    · rw [hq, hsq]
      rfl

/-! ## Universal edge-moment equivariance -/

/-- A vertex permutation acts on unordered edge coordinates. -/
def sym2Relabel (τ : Equiv.Perm V) : Sym2 V ≃ Sym2 V where
  toFun := Sym2.map τ
  invFun := Sym2.map τ.symm
  left_inv e := by
    induction e using Sym2.inductionOn with
    | _ x y => simp
  right_inv e := by
    induction e using Sym2.inductionOn with
    | _ x y => simp

/-- Push an edge vector forward along a vertex permutation. -/
def relabelEdgeVector (τ : Equiv.Perm V) : EdgeVector V ≃+ EdgeVector V :=
  Finsupp.domCongr (sym2Relabel τ)

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem relabelEdgeVector_single (τ : Equiv.Perm V) (x y : V)
    (c : ZMod 2) :
    relabelEdgeVector τ (Finsupp.single s(x, y) c) =
      Finsupp.single s(τ x, τ y) c := by
  simp [relabelEdgeVector, sym2Relabel, Finsupp.domCongr_apply]

omit [Fintype V] in
/-- Relabelling commutes with a complete-graph live-star vector. -/
theorem relabelEdgeVector_liveStarVector (τ : Equiv.Perm V)
    (L : Finset V) (v : V) :
    relabelEdgeVector τ (liveStarVector L v) =
      liveStarVector (L.map τ.toEmbedding) (τ v) := by
  classical
  rw [liveStarVector, map_sum]
  simp only [relabelEdgeVector_single]
  rw [liveStarVector]
  apply Finset.sum_bij (fun w _ ↦ τ w)
  · intro w hw
    rw [Finset.mem_erase] at hw ⊢
    exact ⟨τ.injective.ne hw.1,
      Finset.mem_map.mpr ⟨w, hw.2, rfl⟩⟩
  · intro w₁ hw₁ w₂ hw₂ h
    exact τ.injective h
  · intro w hw
    rw [Finset.mem_erase] at hw
    obtain ⟨x, hxL, hτx⟩ := Finset.mem_map.mp hw.2
    refine ⟨x, Finset.mem_erase.mpr ⟨?_, hxL⟩, hτx⟩
    intro hxv
    subst x
    exact hw.1 hτx.symm
  · intro w hw
    rfl

omit [Fintype V] in
/-- Publicly related states have relabelled live vertex sets. -/
theorem PublicRelated.liveSet_eq {τ : Equiv.Perm V} {s t : State V}
    (h : PublicRelated τ s t) :
    liveSet t = (liveSet s).map τ.toEmbedding := by
  simp only [PublicRelated, State.public, PublicState.relabel,
    PublicState.mk.injEq] at h
  rcases h with ⟨hU, hq, _, _⟩
  simp only [liveSet]
  rw [hU, hq]
  ext w
  simp only [Finset.mem_union, Finset.mem_map, List.mem_toFinset,
    List.mem_map]
  aesop

omit [Fintype V] in
/-- A move's universal live-star moment is equivariant under a fixed-graph
public schedule pairing.  This statement is graph-independent and makes no
claim about the two move charges. -/
theorem moveLiveStar_publicRelated (τ : Equiv.Perm V) {s t : State V}
    (hst : PublicRelated τ s t) (m : Move V) :
    relabelEdgeVector τ (moveLiveStar s m) =
      moveLiveStar t (relabelMove τ m) := by
  cases m with
  | «open» v =>
      simp only [moveLiveStar, relabelMove]
      rw [relabelEdgeVector_liveStarVector, hst.liveSet_eq]
  | close => simp [moveLiveStar, relabelMove, relabelEdgeVector]
  | pass => simp [moveLiveStar, relabelMove, relabelEdgeVector]

omit [Fintype V] in
/-- Paired fixed-graph traces have endpoint moments related by the induced
domain permutation.  In the notation of the hub argument, this is the exact
graph-independent identity `D(λ) = τ D(μ)`. -/
theorem LiveStarTrace.relabel_fixedGraph (τ : Equiv.Perm V)
    (G : SimpleGraph V) :
    ∀ {s t u : State V} {z : EdgeVector V}, PublicRelated τ s t →
      LiveStarTrace G s u z →
      ∃ v, LiveStarTrace G t v (relabelEdgeVector τ z) ∧
        PublicRelated τ u v := by
  intro s t u z hst htrace
  induction htrace generalizing t with
  | refl s =>
      exact ⟨t, by simpa [relabelEdgeVector] using LiveStarTrace.refl (G := G) t,
        hst⟩
  | @cons s s' u m z hstep htail ih =>
      obtain ⟨t', htStep, hs't'⟩ := step_publicRelated τ G hst hstep
      obtain ⟨v, hvTrace, huv⟩ := ih hs't'
      refine ⟨v, ?_, huv⟩
      have hcons := LiveStarTrace.cons htStep hvTrace
      simpa [map_add, moveLiveStar_publicRelated τ hst m] using hcons

end

end Ogdoad.Fifo
