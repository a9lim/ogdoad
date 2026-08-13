import Ogdoad.ImpartialRealizer
import Mathlib.LinearAlgebra.QuadraticForm.Basis

/-!
# Literal-to-deferred FIFO accounting

The paper's arena charges a weighted edge on its second OPEN and a public
coin label on CLOSE.  The existing safe-front compiler instead preloads all
potential charges and toggles a missed edge on CLOSE.  This module proves two
state conjugacies, transports complete normal-play strategy trees in both
directions, and exposes the exact quadratic support expansion used to identify
the preloaded root.  No terminal-charge or move-tree equivalence is assumed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false


open scoped BigOperators
open Ogdoad.Fifo
open Module

namespace Ogdoad.PhysicalDeferred

abbrev F2 := ZMod 2

variable {V : Type*} [Fintype V] [LinearOrder V]

noncomputable def inducedEdgeCharge (G : SimpleGraph V) (S : Finset V) : F2 := by
  classical
  exact ∑ u ∈ S, ∑ v ∈ S, if u < v ∧ G.Adj u v then 1 else 0

theorem inducedEdgeCharge_erase (G : SimpleGraph V) (S : Finset V)
    {z : V} (hz : z ∈ S) :
    inducedEdgeCharge G S = inducedEdgeCharge G (S.erase z) + flip G (S.erase z) z := by
  classical
  rw [inducedEdgeCharge, inducedEdgeCharge]
  rw [← Finset.sum_erase_add _ _ hz]
  have hinner (u : V) :
      (∑ v ∈ S, if u < v ∧ G.Adj u v then (1 : F2) else 0) =
        (∑ v ∈ S.erase z, if u < v ∧ G.Adj u v then 1 else 0) +
          (if u < z ∧ G.Adj u z then 1 else 0) := by
    exact (Finset.sum_erase_add _ (fun v ↦ if u < v ∧ G.Adj u v then (1 : F2) else 0) hz).symm
  rw [Finset.sum_congr rfl (fun u _ ↦ hinner u), Finset.sum_add_distrib,
    hinner z]
  simp only [lt_self_iff_false, false_and, if_false, add_zero]
  rw [add_assoc]
  congr 1
  rw [Ogdoad.Fifo.flip]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hne : u ≠ z := (Finset.mem_erase.mp hu).1
  rcases lt_trichotomy u z with huz | heq | hzu
  · simp [huz, not_lt.mpr huz.le, G.adj_comm]
  · exact False.elim (hne heq)
  · simp [hzu, not_lt.mpr hzu.le, G.adj_comm]

noncomputable def pendingEdgeCharge (G : SimpleGraph V) (U : Finset V) (q : List V) : F2 :=
  inducedEdgeCharge G (U ∪ q.toFinset) + inducedEdgeCharge G q.toFinset

theorem flip_union (G : SimpleGraph V) {A B : Finset V} (h : Disjoint A B) (v : V) :
    flip G (A ∪ B) v = flip G A v + flip G B v := by
  rw [flip_eq_sum_adjacencyBit, flip_eq_sum_adjacencyBit,
    flip_eq_sum_adjacencyBit, Finset.sum_union h]

theorem pendingEdgeCharge_open (G : SimpleGraph V) (U : Finset V) (q : List V)
    {z : V} (hzU : z ∈ U) (hzq : z ∉ q.toFinset) :
    pendingEdgeCharge G (U.erase z) (q ++ [z]) =
      pendingEdgeCharge G U q + flip G q.toFinset z := by
  have hqueue : (q ++ [z]).toFinset = insert z q.toFinset := by
    ext w
    simp [or_comm]
  have hunion : (U.erase z) ∪ (q ++ [z]).toFinset = U ∪ q.toFinset := by
    ext w
    simp only [hqueue, Finset.mem_union, Finset.mem_erase, Finset.mem_insert]
    by_cases hwz : w = z
    · subst w
      simp [hzU]
    · simp [hwz]
  have herase := inducedEdgeCharge_erase G (insert z q.toFinset)
    (Finset.mem_insert_self z q.toFinset)
  rw [Finset.erase_insert hzq] at herase
  rw [pendingEdgeCharge, pendingEdgeCharge, hunion, hqueue, herase]
  abel

theorem pendingEdgeCharge_close (G : SimpleGraph V) (U : Finset V) (q : List V)
    {f : V} (hfU : f ∉ U) (hfq : f ∉ q.toFinset)
    (hdisjoint : Disjoint U q.toFinset) :
    pendingEdgeCharge G U (f :: q) =
      pendingEdgeCharge G U q + flip G U f := by
  have hfunion : f ∉ U ∪ q.toFinset := by simp [hfU, hfq]
  have hu : U ∪ insert f q.toFinset = insert f (U ∪ q.toFinset) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  have hbig := inducedEdgeCharge_erase G (insert f (U ∪ q.toFinset))
    (Finset.mem_insert_self f _)
  rw [Finset.erase_insert hfunion] at hbig
  have hq := inducedEdgeCharge_erase G (insert f q.toFinset)
    (Finset.mem_insert_self f _)
  rw [Finset.erase_insert hfq] at hq
  rw [pendingEdgeCharge, pendingEdgeCharge, List.toFinset_cons, hu, hbig, hq,
    flip_union G hdisjoint f]
  calc
    inducedEdgeCharge G (U ∪ q.toFinset) +
          (flip G U f + flip G q.toFinset f) +
          (inducedEdgeCharge G q.toFinset + flip G q.toFinset f) =
        inducedEdgeCharge G (U ∪ q.toFinset) +
          inducedEdgeCharge G q.toFinset + flip G U f +
          (flip G q.toFinset f + flip G q.toFinset f) := by abel
    _ = inducedEdgeCharge G (U ∪ q.toFinset) +
          inducedEdgeCharge G q.toFinset + flip G U f := by
      rw [CharTwo.add_self_eq_zero, add_zero]

noncomputable def encode (G : SimpleGraph V) (s : State V) : State V :=
  { s with score := s.score + pendingEdgeCharge G s.untouched s.queue }

/-- The literal second-opening convention: OPEN adds the weight of edges to
already-open coins; CLOSE only drains the queue. -/
noncomputable def physicalStep (G : SimpleGraph V) (s : State V) :
    Ogdoad.ImpartialRealizer.Move V → Option (State V)
  | .open v =>
      if v ∈ s.untouched then
        some {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove
          score := s.score + flip G s.queue.toFinset v }
      else none
  | .close =>
      match s.queue with
      | [] => none
      | _ :: q =>
          if s.ko = false ∨ s.untouched = ∅ then
            some {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove
              score := s.score }
          else none

theorem encode_involutive (G : SimpleGraph V) (s : State V) :
    encode G (encode G s) = s := by
  cases s
  simp only [encode]
  congr 1
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem encode_injective (G : SimpleGraph V) : Function.Injective (encode G) := by
  intro a b h
  have h' := congrArg (encode G) h
  simpa only [encode_involutive] using h'

theorem physicalStep_wellFormed {G : SimpleGraph V} {s s' : State V}
    {m : Ogdoad.ImpartialRealizer.Move V} (hs : WellFormed s)
    (h : physicalStep G s m = some s') : WellFormed s' := by
  rcases hs with ⟨hnodup, hdisjoint⟩
  cases m with
  | «open» v =>
      simp only [physicalStep] at h
      split at h
      · rename_i hv
        cases h
        constructor
        · apply List.Nodup.append hnodup (by simp)
          intro a ha hmem
          simp only [List.mem_singleton] at hmem
          subst a
          exact (Finset.disjoint_left.mp hdisjoint) hv (by simpa using ha)
        · rw [List.toFinset_append]
          simp only [Finset.disjoint_union_right]
          exact ⟨Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisjoint,
            by simp⟩
      · contradiction
  | close =>
      simp only [physicalStep] at h
      split at h
      · contradiction
      · rename_i f q hq
        split at h
        · cases h
          have hnodup' : (f :: q).Nodup := by simpa [hq] using hnodup
          constructor
          · exact (List.nodup_cons.mp hnodup').2
          · apply Finset.disjoint_left.mpr
            intro a haU haq
            exact (Finset.disjoint_left.mp hdisjoint) haU (by simp [hq, haq])
        · contradiction

theorem physicalStep_encode_iff {G : SimpleGraph V} {s s' : State V}
    {m : Ogdoad.ImpartialRealizer.Move V} (hs : WellFormed s) :
    physicalStep G s m = some s' ↔
      Ogdoad.ImpartialRealizer.step G (encode G s) m = some (encode G s') := by
  rcases hs with ⟨hnodup, hdisjoint⟩
  cases m with
  | «open» v =>
      simp only [physicalStep, Ogdoad.ImpartialRealizer.step]
      have hmem : v ∈ (encode G s).untouched ↔ v ∈ s.untouched := Iff.rfl
      split <;> rename_i hv
      · simp only [hmem, if_pos hv, Option.some.injEq]
        let p : State V := {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove
          score := s.score + flip G s.queue.toFinset v }
        let d : State V := {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove
          score := (encode G s).score }
        have hvq : v ∉ s.queue.toFinset := by
          intro hvq
          exact (Finset.disjoint_left.mp hdisjoint) hv hvq
        have henc : encode G p = d := by
          simp only [encode, p, d]
          congr 1
          rw [pendingEdgeCharge_open G s.untouched s.queue hv hvq]
          calc
            (s.score + flip G s.queue.toFinset v) +
                (pendingEdgeCharge G s.untouched s.queue +
                  flip G s.queue.toFinset v) =
              s.score + pendingEdgeCharge G s.untouched s.queue +
                (flip G s.queue.toFinset v + flip G s.queue.toFinset v) := by
                  abel
            _ = s.score + pendingEdgeCharge G s.untouched s.queue := by
              rw [CharTwo.add_self_eq_zero, add_zero]
        change p = s' ↔ d = encode G s'
        constructor
        · rintro rfl
          exact henc.symm
        · intro h
          apply encode_injective G
          exact henc.trans h
      · simp [hmem, hv]
  | close =>
      simp only [physicalStep, Ogdoad.ImpartialRealizer.step, encode]
      cases hq : s.queue with
      | nil => simp
      | cons f q =>
          simp only [hq]
          split <;> rename_i hlegal
          · simp only [Option.some.injEq]
            let p : State V := {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove
              score := s.score }
            let d : State V := {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove
              score := s.score + pendingEdgeCharge G s.untouched (f :: q) +
                flip G s.untouched f }
            have hnodup' := List.nodup_cons.mp (by simpa [hq] using hnodup)
            have hfU : f ∉ s.untouched := by
              intro hfU
              exact (Finset.disjoint_left.mp hdisjoint) hfU (by simp [hq])
            have henc : encode G p = d := by
              simp only [encode, p, d]
              congr 1
              rw [pendingEdgeCharge_close G s.untouched q hfU
                (by simpa using hnodup'.1) (by
                  have hd : f ∉ s.untouched ∧ Disjoint s.untouched q.toFinset := by
                    simpa [hq] using hdisjoint
                  exact hd.2)]
              calc
                s.score + pendingEdgeCharge G s.untouched q =
                    s.score + pendingEdgeCharge G s.untouched q +
                      (flip G s.untouched f + flip G s.untouched f) := by
                        rw [CharTwo.add_self_eq_zero, add_zero]
                _ = s.score +
                    (pendingEdgeCharge G s.untouched q + flip G s.untouched f) +
                      flip G s.untouched f := by abel
            change p = s' ↔ d = encode G s'
            constructor
            · rintro rfl
              exact henc.symm
            · intro h
              apply encode_injective G
              exact henc.trans h
          · simp [hlegal]

/-- Normal-play strategies for the literal second-opening transition. -/
inductive PhysicalTailWins (G : SimpleGraph V) (seat : Bool) : State V → Prop
  | terminal (s : State V) (hterminal : Ogdoad.ImpartialRealizer.Terminal s)
      (hwinner : Ogdoad.ImpartialRealizer.TailWinner seat s) :
      PhysicalTailWins G seat s
  | choose (s : State V) (hseat : s.toMove = seat)
      (m : Ogdoad.ImpartialRealizer.Move V) (s' : State V)
      (hstep : physicalStep G s m = some s')
      (hwin : PhysicalTailWins G seat s') : PhysicalTailWins G seat s
  | answer (s : State V) (hseat : s.toMove ≠ seat)
      (hasMove : ∃ m s', physicalStep G s m = some s')
      (hwin : ∀ m s', physicalStep G s m = some s' →
        PhysicalTailWins G seat s') : PhysicalTailWins G seat s

theorem terminal_encode_iff (G : SimpleGraph V) (s : State V) :
    Ogdoad.ImpartialRealizer.Terminal (encode G s) ↔
      Ogdoad.ImpartialRealizer.Terminal s := by
  rfl

theorem tailWinner_encode_of_terminal (G : SimpleGraph V) (seat : Bool)
    {s : State V} (hs : Ogdoad.ImpartialRealizer.Terminal s) :
    Ogdoad.ImpartialRealizer.TailWinner seat (encode G s) ↔
      Ogdoad.ImpartialRealizer.TailWinner seat s := by
  rcases hs with ⟨hU, hq⟩
  simp [Ogdoad.ImpartialRealizer.TailWinner, encode, pendingEdgeCharge, hU, hq,
    inducedEdgeCharge]

theorem physical_to_deferred {G : SimpleGraph V} {seat : Bool} {s : State V}
    (hs : WellFormed s) (hwin : PhysicalTailWins G seat s) :
    Ogdoad.ImpartialRealizer.TailWins G seat (encode G s) := by
  induction hwin with
  | terminal s hterminal hwinner =>
      exact Ogdoad.ImpartialRealizer.TailWins.terminal (encode G s)
        ((terminal_encode_iff G s).2 hterminal)
        ((tailWinner_encode_of_terminal G seat hterminal).2 hwinner)
  | choose s hseat m s' hstep hchild ih =>
      have hs' := physicalStep_wellFormed hs hstep
      exact Ogdoad.ImpartialRealizer.TailWins.choose (encode G s) hseat m
        (encode G s') ((physicalStep_encode_iff hs).1 hstep) (ih hs')
  | answer s hseat hasMove hchildren ih =>
      apply Ogdoad.ImpartialRealizer.TailWins.answer (encode G s) hseat
      · obtain ⟨m, s', hstep⟩ := hasMove
        exact ⟨m, encode G s', (physicalStep_encode_iff hs).1 hstep⟩
      · intro m t hstep
        let s' := encode G t
        have hphysical : physicalStep G s m = some s' := by
          apply (physicalStep_encode_iff hs).2
          simpa [s', encode_involutive] using hstep
        have hs' := physicalStep_wellFormed hs hphysical
        have hdeferred := ih m s' hphysical hs'
        simpa [s', encode_involutive] using hdeferred

theorem deferred_to_physical {G : SimpleGraph V} {seat : Bool} {t : State V}
    (hwin : Ogdoad.ImpartialRealizer.TailWins G seat t) :
    ∀ s, t = encode G s → WellFormed s → PhysicalTailWins G seat s := by
  induction hwin with
  | terminal t hterminal hwinner =>
      intro s hts hs
      subst t
      exact PhysicalTailWins.terminal s ((terminal_encode_iff G s).1 hterminal)
        ((tailWinner_encode_of_terminal G seat
          ((terminal_encode_iff G s).1 hterminal)).1 hwinner)
  | choose t hseat m t' hstep hchild ih =>
      intro s hts hs
      subst t
      let s' := encode G t'
      have hphysical : physicalStep G s m = some s' := by
        apply (physicalStep_encode_iff hs).2
        simpa [s', encode_involutive] using hstep
      have hs' := physicalStep_wellFormed hs hphysical
      exact PhysicalTailWins.choose s hseat m s' hphysical
        (ih s' (by simp [s', encode_involutive]) hs')
  | answer t hseat hasMove hchildren ih =>
      intro s hts hs
      subst t
      apply PhysicalTailWins.answer s hseat
      · obtain ⟨m, t', hstep⟩ := hasMove
        let s' := encode G t'
        refine ⟨m, s', ?_⟩
        apply (physicalStep_encode_iff hs).2
        simpa [s', encode_involutive] using hstep
      · intro m s' hphysical
        have hs' := physicalStep_wellFormed hs hphysical
        have hstep := (physicalStep_encode_iff hs).1 hphysical
        exact ih m (encode G s') hstep s' rfl hs'

theorem physicalTailWins_iff {G : SimpleGraph V} {seat : Bool} {s : State V}
    (hs : WellFormed s) :
    PhysicalTailWins G seat s ↔
      Ogdoad.ImpartialRealizer.TailWins G seat (encode G s) := by
  exact ⟨physical_to_deferred hs, fun h ↦ deferred_to_physical h s rfl hs⟩

/-- Close charges still owed by coins that have not left the FIFO core. -/
noncomputable def pendingCloseCharge (c : V → F2) (U : Finset V) (q : List V) : F2 :=
  ∑ v ∈ U, c v + ∑ v ∈ q.toFinset, c v

theorem pendingCloseCharge_open (c : V → F2) (U : Finset V) (q : List V)
    {z : V} (hzU : z ∈ U) (hzq : z ∉ q.toFinset) :
    pendingCloseCharge c (U.erase z) (q ++ [z]) = pendingCloseCharge c U q := by
  have hqueue : (q ++ [z]).toFinset = insert z q.toFinset := by
    ext w
    simp
  rw [pendingCloseCharge, pendingCloseCharge, hqueue, Finset.sum_insert hzq]
  have herase := Finset.sum_erase_add U c hzU
  calc
    (∑ v ∈ U.erase z, c v) + (c z + ∑ v ∈ q.toFinset, c v) =
        ((∑ v ∈ U.erase z, c v) + c z) + ∑ v ∈ q.toFinset, c v := by
          abel
    _ = (∑ v ∈ U, c v) + ∑ v ∈ q.toFinset, c v := by rw [herase]

theorem pendingCloseCharge_close (c : V → F2) (U : Finset V) (q : List V)
    {f : V} (hfq : f ∉ q.toFinset) :
    pendingCloseCharge c U (f :: q) = pendingCloseCharge c U q + c f := by
  rw [pendingCloseCharge, pendingCloseCharge, List.toFinset_cons,
    Finset.sum_insert hfq]
  abel

noncomputable def closeEncode (c : V → F2) (s : State V) : State V :=
  { s with score := s.score + pendingCloseCharge c s.untouched s.queue }

/-- The literal arena in the paper: second opening charges edge overlap and
each close charges its public coin label. -/
noncomputable def literalStep (G : SimpleGraph V) (c : V → F2) (s : State V) :
    Ogdoad.ImpartialRealizer.Move V → Option (State V)
  | .open v =>
      if v ∈ s.untouched then
        some {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove
          score := s.score + flip G s.queue.toFinset v }
      else none
  | .close =>
      match s.queue with
      | [] => none
      | f :: q =>
          if s.ko = false ∨ s.untouched = ∅ then
            some {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove
              score := s.score + c f }
          else none

theorem closeEncode_involutive (c : V → F2) (s : State V) :
    closeEncode c (closeEncode c s) = s := by
  cases s
  simp only [closeEncode]
  congr 1
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem closeEncode_injective (c : V → F2) : Function.Injective (closeEncode c) := by
  intro a b h
  have h' := congrArg (closeEncode c) h
  simpa only [closeEncode_involutive] using h'

theorem literalStep_wellFormed {G : SimpleGraph V} {c : V → F2} {s s' : State V}
    {m : Ogdoad.ImpartialRealizer.Move V} (hs : WellFormed s)
    (h : literalStep G c s m = some s') : WellFormed s' := by
  rcases hs with ⟨hnodup, hdisjoint⟩
  cases m with
  | «open» v =>
      simp only [literalStep] at h
      split at h
      · rename_i hv
        cases h
        constructor
        · apply List.Nodup.append hnodup (by simp)
          intro a ha hmem
          simp only [List.mem_singleton] at hmem
          subst a
          exact (Finset.disjoint_left.mp hdisjoint) hv (by simpa using ha)
        · rw [List.toFinset_append]
          simp only [Finset.disjoint_union_right]
          exact ⟨Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisjoint,
            by simp⟩
      · contradiction
  | close =>
      simp only [literalStep] at h
      split at h
      · contradiction
      · rename_i f q hq
        split at h
        · cases h
          have hnodup' : (f :: q).Nodup := by simpa [hq] using hnodup
          constructor
          · exact (List.nodup_cons.mp hnodup').2
          · apply Finset.disjoint_left.mpr
            intro a haU haq
            exact (Finset.disjoint_left.mp hdisjoint) haU (by simp [hq, haq])
        · contradiction

theorem literalStep_closeEncode_iff {G : SimpleGraph V} {c : V → F2}
    {s s' : State V} {m : Ogdoad.ImpartialRealizer.Move V} (hs : WellFormed s) :
    literalStep G c s m = some s' ↔
      physicalStep G (closeEncode c s) m = some (closeEncode c s') := by
  rcases hs with ⟨hnodup, hdisjoint⟩
  cases m with
  | «open» v =>
      simp only [literalStep, physicalStep]
      have hmem : v ∈ (closeEncode c s).untouched ↔ v ∈ s.untouched := Iff.rfl
      split <;> rename_i hv
      · simp only [hmem, if_pos hv, Option.some.injEq]
        let p : State V := {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove
          score := s.score + flip G s.queue.toFinset v }
        let d : State V := {
          untouched := s.untouched.erase v
          queue := s.queue ++ [v]
          ko := s.queue.isEmpty
          toMove := !s.toMove
          score := (closeEncode c s).score + flip G s.queue.toFinset v }
        have hvq : v ∉ s.queue.toFinset := fun hvq ↦
          (Finset.disjoint_left.mp hdisjoint) hv hvq
        have henc : closeEncode c p = d := by
          simp only [closeEncode, p, d]
          congr 1
          rw [pendingCloseCharge_open c s.untouched s.queue hv hvq]
          abel
        change p = s' ↔ d = closeEncode c s'
        constructor
        · rintro rfl
          exact henc.symm
        · intro h
          apply closeEncode_injective c
          exact henc.trans h
      · simp [hmem, hv]
  | close =>
      simp only [literalStep, physicalStep, closeEncode]
      cases hq : s.queue with
      | nil => simp
      | cons f q =>
          simp only [hq]
          split <;> rename_i hlegal
          · simp only [Option.some.injEq]
            let p : State V := {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove
              score := s.score + c f }
            let d : State V := {
              untouched := s.untouched
              queue := q
              ko := false
              toMove := !s.toMove
              score := s.score + pendingCloseCharge c s.untouched (f :: q) }
            have hnodup' := List.nodup_cons.mp (by simpa [hq] using hnodup)
            have henc : closeEncode c p = d := by
              simp only [closeEncode, p, d]
              congr 1
              rw [pendingCloseCharge_close c s.untouched q (by simpa using hnodup'.1)]
              abel
            change p = s' ↔ d = closeEncode c s'
            constructor
            · rintro rfl
              exact henc.symm
            · intro h
              apply closeEncode_injective c
              exact henc.trans h
          · simp [hlegal]

inductive LiteralTailWins (G : SimpleGraph V) (c : V → F2) (seat : Bool) :
    State V → Prop
  | terminal (s : State V) (hterminal : Ogdoad.ImpartialRealizer.Terminal s)
      (hwinner : Ogdoad.ImpartialRealizer.TailWinner seat s) :
      LiteralTailWins G c seat s
  | choose (s : State V) (hseat : s.toMove = seat)
      (m : Ogdoad.ImpartialRealizer.Move V) (s' : State V)
      (hstep : literalStep G c s m = some s')
      (hwin : LiteralTailWins G c seat s') : LiteralTailWins G c seat s
  | answer (s : State V) (hseat : s.toMove ≠ seat)
      (hasMove : ∃ m s', literalStep G c s m = some s')
      (hwin : ∀ m s', literalStep G c s m = some s' →
        LiteralTailWins G c seat s') : LiteralTailWins G c seat s

theorem terminal_closeEncode_iff (c : V → F2) (s : State V) :
    Ogdoad.ImpartialRealizer.Terminal (closeEncode c s) ↔
      Ogdoad.ImpartialRealizer.Terminal s := by rfl

theorem tailWinner_closeEncode_of_terminal (c : V → F2) (seat : Bool)
    {s : State V} (hs : Ogdoad.ImpartialRealizer.Terminal s) :
    Ogdoad.ImpartialRealizer.TailWinner seat (closeEncode c s) ↔
      Ogdoad.ImpartialRealizer.TailWinner seat s := by
  rcases hs with ⟨hU, hq⟩
  simp [Ogdoad.ImpartialRealizer.TailWinner, closeEncode, pendingCloseCharge, hU, hq]

theorem literal_to_overlap {G : SimpleGraph V} {c : V → F2} {seat : Bool}
    {s : State V} (hs : WellFormed s) (hwin : LiteralTailWins G c seat s) :
    PhysicalTailWins G seat (closeEncode c s) := by
  induction hwin with
  | terminal s hterminal hwinner =>
      exact PhysicalTailWins.terminal (closeEncode c s)
        ((terminal_closeEncode_iff c s).2 hterminal)
        ((tailWinner_closeEncode_of_terminal c seat hterminal).2 hwinner)
  | choose s hseat m s' hstep hchild ih =>
      have hs' := literalStep_wellFormed hs hstep
      exact PhysicalTailWins.choose (closeEncode c s) hseat m (closeEncode c s')
        ((literalStep_closeEncode_iff hs).1 hstep) (ih hs')
  | answer s hseat hasMove hchildren ih =>
      apply PhysicalTailWins.answer (closeEncode c s) hseat
      · obtain ⟨m, s', hstep⟩ := hasMove
        exact ⟨m, closeEncode c s', (literalStep_closeEncode_iff hs).1 hstep⟩
      · intro m t hstep
        let s' := closeEncode c t
        have hliteral : literalStep G c s m = some s' := by
          apply (literalStep_closeEncode_iff hs).2
          simpa [s', closeEncode_involutive] using hstep
        have hs' := literalStep_wellFormed hs hliteral
        have hoverlap := ih m s' hliteral hs'
        simpa [s', closeEncode_involutive] using hoverlap

theorem overlap_to_literal {G : SimpleGraph V} {c : V → F2} {seat : Bool}
    {t : State V} (hwin : PhysicalTailWins G seat t) :
    ∀ s, t = closeEncode c s → WellFormed s → LiteralTailWins G c seat s := by
  induction hwin with
  | terminal t hterminal hwinner =>
      intro s hts hs
      subst t
      exact LiteralTailWins.terminal s ((terminal_closeEncode_iff c s).1 hterminal)
        ((tailWinner_closeEncode_of_terminal c seat
          ((terminal_closeEncode_iff c s).1 hterminal)).1 hwinner)
  | choose t hseat m t' hstep hchild ih =>
      intro s hts hs
      subst t
      let s' := closeEncode c t'
      have hliteral : literalStep G c s m = some s' := by
        apply (literalStep_closeEncode_iff hs).2
        simpa [s', closeEncode_involutive] using hstep
      have hs' := literalStep_wellFormed hs hliteral
      exact LiteralTailWins.choose s hseat m s' hliteral
        (ih s' (by simp [s', closeEncode_involutive]) hs')
  | answer t hseat hasMove hchildren ih =>
      intro s hts hs
      subst t
      apply LiteralTailWins.answer s hseat
      · obtain ⟨m, t', hstep⟩ := hasMove
        let s' := closeEncode c t'
        refine ⟨m, s', ?_⟩
        apply (literalStep_closeEncode_iff hs).2
        simpa [s', closeEncode_involutive] using hstep
      · intro m s' hliteral
        have hs' := literalStep_wellFormed hs hliteral
        have hstep := (literalStep_closeEncode_iff hs).1 hliteral
        exact ih m (closeEncode c s') hstep s' rfl hs'

theorem literalTailWins_iff {G : SimpleGraph V} {c : V → F2} {seat : Bool}
    {s : State V} (hs : WellFormed s) :
    LiteralTailWins G c seat s ↔ PhysicalTailWins G seat (closeEncode c s) := by
  exact ⟨literal_to_overlap hs, fun h ↦ overlap_to_literal h s rfl hs⟩

section Quadratic

variable {M I : Type*} [AddCommGroup M] [Module F2 M]
  [Fintype I] [LinearOrder I]

theorem quadratic_support_expansion (Q : QuadraticMap F2 M F2)
    (b : Basis I F2 M) (x : M) :
    Q x = ∑ i ∈ (b.repr x).support, Q (b i) +
      ∑ i ∈ (b.repr x).support, ∑ j ∈ (b.repr x).support,
        if i < j then QuadraticMap.polar Q (b i) (b j) else 0 := by
  let S := (b.repr x).support
  have hcoeff : ∀ i ∈ S, b.repr x i = 1 := by
    intro i hi
    exact Ogdoad.Fifo.zmod2_eq_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hi)
  have hx : ∑ i ∈ S, b i = x := by
    calc
      ∑ i ∈ S, b i = ∑ i ∈ S, b.repr x i • b i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoeff i hi, one_smul]
      _ = ∑ i, b.repr x i • b i := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i _ hi
        have hz : b.repr x i = 0 := by
          by_contra hn
          exact hi (Finsupp.mem_support_iff.mpr hn)
        simp [hz]
      _ = x := b.sum_repr x
  have hpairs :
      (∑ ij ∈ S.sym2 with ¬ij.IsDiag,
        QuadraticMap.polarSym2 Q (Sym2.map b ij)) =
        ∑ i ∈ S, ∑ j ∈ S,
          if i < j then QuadraticMap.polar Q (b i) (b j) else 0 := by
    rw [Finset.sum_sym2_filter_not_isDiag, ← Finset.sum_product']
    simp only [Finset.sum_filter]
    calc
      (∑ ij ∈ S.offDiag,
          if ij.1 < ij.2 then
            QuadraticMap.polarSym2 Q (Sym2.map b s(ij.1, ij.2)) else 0) =
          ∑ ij ∈ S.offDiag,
            if ij.1 < ij.2 then QuadraticMap.polar Q (b ij.1) (b ij.2)
            else 0 := by
              apply Finset.sum_congr rfl
              intro ij _
              simp [QuadraticMap.polarSym2_sym2Mk]
      _ = ∑ ij ∈ S ×ˢ S,
          if ij.1 < ij.2 then QuadraticMap.polar Q (b ij.1) (b ij.2)
          else 0 := by
            apply Finset.sum_subset
            · intro ij hij
              simp only [Finset.mem_offDiag] at hij
              exact Finset.mem_product.mpr ⟨hij.1, hij.2.1⟩
            · intro ij hij hnot
              have heq : ij.1 = ij.2 := by
                by_contra hne
                exact hnot (Finset.mem_offDiag.mpr
                  ⟨(Finset.mem_product.mp hij).1, (Finset.mem_product.mp hij).2, hne⟩)
              simp [heq]
  calc
    Q x = Q (∑ i ∈ S, b i) := by rw [hx]
    _ = ∑ i ∈ S, Q (b i) +
        ∑ ij ∈ S.sym2 with ¬ij.IsDiag,
          QuadraticMap.polarSym2 Q (Sym2.map b ij) :=
      QuadraticMap.map_sum Q S b
    _ = _ := by rw [hpairs]

end Quadratic

end Ogdoad.PhysicalDeferred
