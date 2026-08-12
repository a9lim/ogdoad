import Ogdoad.Fifo

/-!
# The FIFO theorem for matching boards

This file proves the exact FIFO linking statement needed by the Gold--Arf
construction after a public Witt change of frame. Such a board is a disjoint
union of edges and isolated vertices. Unlike the stronger arbitrary-graph
conjecture in `Ogdoad.Fifo`, no dummy is needed: either seat can force every
FIFO close to have zero live charge.
-/


namespace Ogdoad.Fifo

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every vertex has at most one neighbour: the graph is a disjoint union of
matching edges and isolated vertices. -/
def IsMatchingGraph (G : SimpleGraph V) : Prop :=
  ∀ ⦃v x y⦄, G.Adj v x → G.Adj v y → x = y

omit [Fintype V] [DecidableEq V] in
/-- Every induced subgraph of a matching plus isolates is again a matching
plus isolates. This is the restriction from an adapted Gold basis to the
active support of one input. -/
theorem IsMatchingGraph.induce {G : SimpleGraph V} (hG : IsMatchingGraph G)
    (S : Set V) : IsMatchingGraph (G.induce S) := by
  intro v x y hvx hvy
  apply Subtype.ext
  exact hG hvx hvy

omit [Fintype V] [DecidableEq V] in
/-- Deleting any collection of edges from a matching preserves the matching
property. This is the fixed-refinement step for weighted Gold source pairs:
zero-weight source edges are simply absent from the proof-auxiliary graph. -/
theorem IsMatchingGraph.mono {G H : SimpleGraph V} (hG : IsMatchingGraph G)
    (hHG : H ≤ G) : IsMatchingGraph H := by
  intro v x y hvx hvy
  exact hG (hHG hvx) (hHG hvy)

/-- At an opponent checkpoint either ko protects the FIFO front, or that
front has zero live charge.  The empty queue satisfies the latter clause
vacuously. -/
def MatchingFrontSafe (G : SimpleGraph V) (s : State V) : Prop :=
  s.ko = true ∨
    ∀ f q, s.queue = f :: q → flip G s.untouched f = 0

omit [Fintype V] [DecidableEq V] in
theorem exists_adj_of_flip_one {G : SimpleGraph V} {U : Finset V} {f : V}
    (hflip : flip G U f = 1) : ∃ u ∈ U, G.Adj f u := by
  classical
  by_contra h
  push Not at h
  have hempty : U.filter (G.Adj f) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro u hu
    exact h u hu
  simp [flip, hempty] at hflip

omit [Fintype V] in
theorem flip_erase_eq_zero_of_matching_one
    {G : SimpleGraph V} (hG : IsMatchingGraph G)
    {U : Finset V} {f u : V} (hfu : G.Adj f u) :
    flip G (U.erase u) f = 0 := by
  classical
  have hempty : (U.erase u).filter (G.Adj f) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro z hz
    rcases Finset.mem_erase.mp hz with ⟨hzu, hzU⟩
    intro hfz
    exact hzu (hG hfz hfu)
  simp [flip, hempty]

omit [Fintype V] in
theorem flip_erase_eq_zero_of_matching_zero
    {G : SimpleGraph V} (hG : IsMatchingGraph G)
    {U : Finset V} {f z : V} (hz : z ∈ U) (hflip : flip G U f = 0) :
    flip G (U.erase z) f = 0 := by
  classical
  by_cases hfz : G.Adj f z
  · have hfilter : U.filter (G.Adj f) = {z} := by
      ext w
      constructor
      · intro hw
        rcases Finset.mem_filter.mp hw with ⟨hwU, hfw⟩
        exact Finset.mem_singleton.mpr (hG hfw hfz)
      · intro hw
        have hwz := Finset.mem_singleton.mp hw
        subst w
        exact Finset.mem_filter.mpr ⟨hz, hfz⟩
    simp [flip, hfilter] at hflip
  · have h := flip_eq_flip_erase_add (G := G) (f := f) hz
    simpa [adjacencyBit, hfz, hflip] using h.symm

omit [Fintype V] in
theorem matchingFrontSafe_of_open_front_one
    {G : SimpleGraph V} (hG : IsMatchingGraph G)
    (s : State V) (f u : V) (q : List V)
    (hq : s.queue = f :: q) (hfu : G.Adj f u) :
    MatchingFrontSafe G {
      untouched := s.untouched.erase u
      queue := s.queue ++ [u]
      ko := s.queue.isEmpty
      toMove := !s.toMove
      score := s.score } := by
  right
  intro f' q' hq'
  rw [hq] at hq'
  simp only [List.cons_append] at hq'
  injection hq' with hff
  subst f'
  exact flip_erase_eq_zero_of_matching_one hG hfu

omit [Fintype V] in
theorem matchingFrontSafe_of_open_front_zero
    {G : SimpleGraph V} (hG : IsMatchingGraph G)
    (s : State V) (f z : V) (q : List V)
    (hq : s.queue = f :: q) (hz : z ∈ s.untouched)
    (hf : flip G s.untouched f = 0) :
    MatchingFrontSafe G {
      untouched := s.untouched.erase z
      queue := s.queue ++ [z]
      ko := s.queue.isEmpty
      toMove := !s.toMove
      score := s.score } := by
  right
  intro f' q' hq'
  rw [hq] at hq'
  simp only [List.cons_append] at hq'
  injection hq' with hff
  subst f'
  exact flip_erase_eq_zero_of_matching_zero hG hz hf

omit [Fintype V] in
theorem matchingFrontSafe_of_open_empty
    {G : SimpleGraph V} (s : State V) (z : V)
    (hq : s.queue = []) :
    MatchingFrontSafe G {
      untouched := s.untouched.erase z
      queue := s.queue ++ [z]
      ko := s.queue.isEmpty
      toMove := !s.toMove
      score := s.score } := by
  left
  simp [hq]

omit [Fintype V] in
/-- On a matching plus isolated vertices, either seat can force even terminal
score from every score-zero position where it is that seat's turn, or where
the opponent is presented with a ko-protected or zero-charge front.

The strategy is local.  If the front has unit charge, open its unique
untouched neighbour.  If the front has zero charge, open any untouched
vertex.  Thus every opponent checkpoint is front-safe. -/
theorem evenWins_of_matching
    {G : SimpleGraph V} (hG : IsMatchingGraph G) (seat : Bool) :
    ∀ s : State V, s.score = 0 →
      (s.toMove = seat ∨ MatchingFrontSafe G s) → EvenWins G seat s := by
  intro s
  induction s using (measure rank).wf.induction with
  | h s ih =>
      intro hscore hmode
      by_cases ht : Terminal s
      · exact EvenWins.terminal s ht hscore
      by_cases hseat : s.toMove = seat
      · by_cases hU : s.untouched = ∅
        · exact evenWins_of_untouched_empty seat s hU hscore
        · obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hU
          cases hq : s.queue with
          | nil =>
              let s' : State V := {
                untouched := s.untouched.erase z
                queue := s.queue ++ [z]
                ko := s.queue.isEmpty
                toMove := !s.toMove
                score := s.score }
              have hstep : step G s (.open z) = some s' := by
                simp [step, s', hz]
              refine EvenWins.choose s hseat (.open z) s' hstep
                (ih s' (rank_step_lt hstep) ?_ (Or.inr ?_))
              · exact hscore
              · exact matchingFrontSafe_of_open_empty s z hq
          | cons f q =>
              by_cases hf1 : flip G s.untouched f = 1
              · obtain ⟨u, hu, hfu⟩ := exists_adj_of_flip_one hf1
                let s' : State V := {
                  untouched := s.untouched.erase u
                  queue := s.queue ++ [u]
                  ko := s.queue.isEmpty
                  toMove := !s.toMove
                  score := s.score }
                have hstep : step G s (.open u) = some s' := by
                  simp [step, s', hu]
                refine EvenWins.choose s hseat (.open u) s' hstep
                  (ih s' (rank_step_lt hstep) ?_ (Or.inr ?_))
                · exact hscore
                · exact matchingFrontSafe_of_open_front_one hG s f u q hq hfu
              · have hf0 : flip G s.untouched f = 0 :=
                  zmod2_eq_zero_of_ne_one _ hf1
                let s' : State V := {
                  untouched := s.untouched.erase z
                  queue := s.queue ++ [z]
                  ko := s.queue.isEmpty
                  toMove := !s.toMove
                  score := s.score }
                have hstep : step G s (.open z) = some s' := by
                  simp [step, s', hz]
                refine EvenWins.choose s hseat (.open z) s' hstep
                  (ih s' (rank_step_lt hstep) ?_ (Or.inr ?_))
                · exact hscore
                · exact matchingFrontSafe_of_open_front_zero hG s f z q hq hz hf0
      · have hasMove : ∃ m s', step G s m = some s' :=
          not_terminal_has_step ht
        refine EvenWins.answer s hseat hasMove ?_
        intro m s' hstep
        have hchildturn : s'.toMove = seat := by
          rw [step_toMove hstep]
          cases hs : s.toMove <;> cases hseat' : seat <;> simp_all
        apply ih s' (rank_step_lt hstep)
        · cases m with
          | «open» v => rw [open_score hstep, hscore]
          | pass => rw [pass_score hstep, hscore]
          | close =>
              obtain ⟨f, q, hq, hs'⟩ := close_score hstep
              rcases hmode with hturn | hsafe
              · exact False.elim (hseat hturn)
              · rcases hsafe with hko | hfront
                · simp [step, hq, hko] at hstep
                · rw [hs', hfront f q hq, add_zero, hscore]
        · exact Or.inl hchildturn

/-- The empty initial queue is front-safe, so the matching theorem applies
to both choices of the designated even seat. -/
theorem evenWins_initial_of_matching
    {G : SimpleGraph V} (hG : IsMatchingGraph G) (seat : Bool) :
    EvenWins G seat (initial (V := V)) := by
  apply evenWins_of_matching hG seat (initial (V := V))
  · rfl
  · by_cases hs : seat = false
    · exact Or.inl (by simpa [initial] using hs.symm)
    · right
      right
      intro f q hq
      simp [initial] at hq

omit [Fintype V] in
/-- Erasing the public mate of the front kills every possible live edge in
any selected submatching.  The selected edge itself need not be present. -/
theorem flip_erase_eq_zero_of_public_matching_mate
    {G0 H : SimpleGraph V} (hG0 : IsMatchingGraph G0) (hHG0 : H ≤ G0)
    {U : Finset V} {f u : V} (hfu : G0.Adj f u) :
    flip H (U.erase u) f = 0 := by
  classical
  have hempty : (U.erase u).filter (H.Adj f) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro z hz
    rcases Finset.mem_erase.mp hz with ⟨hzu, _hzU⟩
    intro hfz
    exact hzu (hG0 (hHG0 hfz) hfu)
  simp [flip, hempty]

omit [Fintype V] [DecidableEq V] in
/-- If the public matching has no live neighbour at the front, neither does
any refinement-selected submatching. -/
theorem flip_eq_zero_of_no_public_matching_neighbor
    {G0 H : SimpleGraph V} (hHG0 : H ≤ G0)
    {U : Finset V} {f : V}
    (hnone : ∀ u ∈ U, ¬G0.Adj f u) :
    flip H U f = 0 := by
  classical
  have hempty : U.filter (H.Adj f) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro u hu
    exact fun hfu ↦ hnone u hu (hHG0 hfu)
  simp [flip, hempty]

omit [Fintype V] in
/-- Opening the public mate makes the opponent front safe simultaneously for
every selected submatching of the public graph. -/
theorem matchingFrontSafe_of_open_public_mate
    {G0 H : SimpleGraph V} (hG0 : IsMatchingGraph G0) (hHG0 : H ≤ G0)
    (s : State V) (f u : V) (q : List V)
    (hq : s.queue = f :: q) (hfu : G0.Adj f u) :
    MatchingFrontSafe H {
      untouched := s.untouched.erase u
      queue := s.queue ++ [u]
      ko := s.queue.isEmpty
      toMove := !s.toMove
      score := s.score } := by
  right
  intro f' q' hq'
  rw [hq] at hq'
  simp only [List.cons_append] at hq'
  injection hq' with hff
  subst f'
  exact flip_erase_eq_zero_of_public_matching_mate hG0 hHG0 hfu

omit [Fintype V] in
/-- When the public front has no live mate, opening any untouched vertex
preserves safety for every selected submatching. -/
theorem matchingFrontSafe_of_open_no_public_neighbor
    {G0 H : SimpleGraph V} (hHG0 : H ≤ G0)
    (s : State V) (f z : V) (q : List V)
    (hq : s.queue = f :: q)
    (hnone : ∀ u ∈ s.untouched, ¬G0.Adj f u) :
    MatchingFrontSafe H {
      untouched := s.untouched.erase z
      queue := s.queue ++ [z]
      ko := s.queue.isEmpty
      toMove := !s.toMove
      score := s.score } := by
  right
  intro f' q' hq'
  rw [hq] at hq'
  simp only [List.cons_append] at hq'
  injection hq' with hff
  subst f'
  apply flip_eq_zero_of_no_public_matching_neighbor hHG0
  intro u hu
  exact hnone u (Finset.mem_of_mem_erase hu)

omit [Fintype V] in
/-- Let `G0` be a public potential matching and let `H ≤ G0` select any
subset of its edges.  Either seat can force even score in `H` by a policy
whose choices use only `G0`: if the current FIFO front has an untouched
public mate, open it whether or not its edge survives in `H`; otherwise open
any untouched vertex.  Thus one policy works uniformly across all
refinement-selected submatchings. -/
theorem evenWins_of_public_matching
    {G0 H : SimpleGraph V} (hG0 : IsMatchingGraph G0) (hHG0 : H ≤ G0)
    (seat : Bool) :
    ∀ s : State V, s.score = 0 →
      (s.toMove = seat ∨ MatchingFrontSafe H s) → EvenWins H seat s := by
  intro s
  induction s using (measure rank).wf.induction with
  | h s ih =>
      intro hscore hmode
      by_cases ht : Terminal s
      · exact EvenWins.terminal s ht hscore
      by_cases hseat : s.toMove = seat
      · by_cases hU : s.untouched = ∅
        · exact evenWins_of_untouched_empty seat s hU hscore
        · obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hU
          cases hq : s.queue with
          | nil =>
              let s' : State V := {
                untouched := s.untouched.erase z
                queue := s.queue ++ [z]
                ko := s.queue.isEmpty
                toMove := !s.toMove
                score := s.score }
              have hstep : step H s (.open z) = some s' := by
                simp [step, s', hz]
              refine EvenWins.choose s hseat (.open z) s' hstep
                (ih s' (rank_step_lt hstep) ?_ (Or.inr ?_))
              · exact hscore
              · exact matchingFrontSafe_of_open_empty s z hq
          | cons f q =>
              by_cases hmate : ∃ u ∈ s.untouched, G0.Adj f u
              · obtain ⟨u, hu, hfu⟩ := hmate
                let s' : State V := {
                  untouched := s.untouched.erase u
                  queue := s.queue ++ [u]
                  ko := s.queue.isEmpty
                  toMove := !s.toMove
                  score := s.score }
                have hstep : step H s (.open u) = some s' := by
                  simp [step, s', hu]
                refine EvenWins.choose s hseat (.open u) s' hstep
                  (ih s' (rank_step_lt hstep) ?_ (Or.inr ?_))
                · exact hscore
                · exact matchingFrontSafe_of_open_public_mate
                    hG0 hHG0 s f u q hq hfu
              · have hnone : ∀ u ∈ s.untouched, ¬G0.Adj f u := by
                  intro u hu hfu
                  exact hmate ⟨u, hu, hfu⟩
                let s' : State V := {
                  untouched := s.untouched.erase z
                  queue := s.queue ++ [z]
                  ko := s.queue.isEmpty
                  toMove := !s.toMove
                  score := s.score }
                have hstep : step H s (.open z) = some s' := by
                  simp [step, s', hz]
                refine EvenWins.choose s hseat (.open z) s' hstep
                  (ih s' (rank_step_lt hstep) ?_ (Or.inr ?_))
                · exact hscore
                · exact matchingFrontSafe_of_open_no_public_neighbor
                    hHG0 s f z q hq hnone
      · have hasMove : ∃ m s', step H s m = some s' :=
          not_terminal_has_step ht
        refine EvenWins.answer s hseat hasMove ?_
        intro m s' hstep
        have hchildturn : s'.toMove = seat := by
          rw [step_toMove hstep]
          cases hs : s.toMove <;> cases hseat' : seat <;> simp_all
        apply ih s' (rank_step_lt hstep)
        · cases m with
          | «open» v => rw [open_score hstep, hscore]
          | pass => rw [pass_score hstep, hscore]
          | close =>
              obtain ⟨f, q, hq, hs'⟩ := close_score hstep
              rcases hmode with hturn | hsafe
              · exact False.elim (hseat hturn)
              · rcases hsafe with hko | hfront
                · simp [step, hq, hko] at hstep
                · rw [hs', hfront f q hq, add_zero, hscore]
        · exact Or.inl hchildturn

/-- Root form of the public-strategy theorem.  The quantifier over `H` makes
the refinement uniformity explicit: one public matching supports both-seat
zero-correction strategies for every one of its submatchings. -/
theorem evenWins_initial_of_every_submatching
    {G0 : SimpleGraph V} (hG0 : IsMatchingGraph G0) (seat : Bool) :
    ∀ H : SimpleGraph V, H ≤ G0 →
      EvenWins H seat (initial (V := V)) := by
  intro H hHG0
  apply evenWins_of_public_matching hG0 hHG0 seat (initial (V := V))
  · rfl
  · by_cases hs : seat = false
    · exact Or.inl (by simpa [initial] using hs.symm)
    · right
      right
      intro f q hq
      simp [initial] at hq

/-- Indices for an adapted alternating basis: left and right endpoints of
each hyperbolic plane, followed by radical/isolated coordinates. -/
abbrev HyperbolicIndex (P I : Type*) := Sum P (Sum P I)

/-- The polar support graph of an adapted alternating basis. -/
def hyperbolicGraph (P I : Type*) : SimpleGraph (HyperbolicIndex P I) :=
  SimpleGraph.fromRel fun x y ↦
    ∃ p : P, x = Sum.inl p ∧ y = Sum.inr (Sum.inl p)

omit [Fintype V] [DecidableEq V] in
theorem isMatchingGraph_hyperbolicGraph
    (P I : Type*) : IsMatchingGraph (hyperbolicGraph P I) := by
  intro v x y hvx hvy
  simp only [hyperbolicGraph, SimpleGraph.fromRel_adj] at hvx hvy
  rcases hvx with ⟨_, ⟨p, rfl, rfl⟩ | ⟨p, rfl, rfl⟩⟩ <;>
    rcases hvy with ⟨_, ⟨q, hqv, hqy⟩ | ⟨q, hqy, hqv⟩⟩ <;>
    simp_all

/-- Hence the FIFO flip theorem holds in every adapted hyperbolic-plus-
radical coordinate frame, for either seat and without a dummy. -/
theorem evenWins_initial_hyperbolicGraph
    {P I : Type*} [Fintype P] [DecidableEq P] [Fintype I] [DecidableEq I]
    (seat : Bool) :
    EvenWins (hyperbolicGraph P I) seat
      (initial (V := HyperbolicIndex P I)) :=
  evenWins_initial_of_matching (isMatchingGraph_hyperbolicGraph P I) seat

end

end Ogdoad.Fifo
