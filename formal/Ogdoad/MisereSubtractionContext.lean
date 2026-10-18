import Ogdoad.MisereSubtraction

/-!
# Subtraction heaps in arbitrary misere contexts

Ferguson's zero/one property gives more than the Bouton outcome formula inside
the subtraction universe.  An individual ordinary subtraction heap has the
same misere outcome as its normal-play Nim heap in every well-founded
impartial context.  The context is arbitrary: it need not itself be a
subtraction game, a Nim position, or a member of a fixed finite quotient.

The proof below uses the exact recurrences for the two disjunctive sums.
It does not assume a canonical-form theorem.  A subtraction option whose SG
value exceeds the current mex can move back to that mex when viewed as a Nim
heap, and so cannot disturb the comparison.  Ferguson's zero-to-one move is
needed precisely when the comparison Nim heap and the context are terminal.
-/

namespace Ogdoad.MisereSubtractionContext

open Ogdoad.MisereSubtraction

variable {G : Type*}

/-- Exact misere recurrence for one subtraction heap plus an arbitrary
impartial context.  A terminal position is not a previous-player win. -/
def SubtractionRecurrence (S : Set Nat) (move : G → G → Prop)
    (W : Nat → G → Prop) : Prop :=
  ∀ n x, W n x ↔
    ((∃ s ∈ S, s ≤ n) ∨ ∃ y, move x y) ∧
    (∀ s ∈ S, s ≤ n → ¬W (n - s) x) ∧
    (∀ y, move x y → ¬W n y)

/-- Exact misere recurrence for one ordinary Nim heap plus the same context.
The legal Nim options are exactly the smaller natural numbers. -/
def NimRecurrence (move : G → G → Prop) (W : Nat → G → Prop) : Prop :=
  ∀ n x, W n x ↔
    (0 < n ∨ ∃ y, move x y) ∧
    (∀ m, m < n → ¬W m x) ∧
    (∀ y, move x y → ¬W n y)

/-- The actual previous-player-win predicate for a subtraction heap plus a
ranked context, defined by the literal misere recursion. -/
def subtractionP (S : Set Nat) (hpos : ∀ s ∈ S, 0 < s)
    (move : G → G → Prop) (rank : G → Nat)
    (hmove : ∀ x y, move x y → rank y < rank x) (n : Nat) (x : G) : Prop :=
  ((∃ s ∈ S, s ≤ n) ∨ ∃ y, move x y) ∧
  (∀ s ∈ S, s ≤ n → ¬subtractionP S hpos move rank hmove (n - s) x) ∧
  (∀ y, move x y → ¬subtractionP S hpos move rank hmove n y)
termination_by n + rank x
decreasing_by
  · have := hpos s ‹s ∈ S›
    omega
  · have := hmove x y ‹move x y›
    omega

/-- The actual previous-player-win predicate for a Nim heap plus the same
ranked context. -/
def nimP (move : G → G → Prop) (rank : G → Nat)
    (hmove : ∀ x y, move x y → rank y < rank x) (n : Nat) (x : G) : Prop :=
  (0 < n ∨ ∃ y, move x y) ∧
  (∀ m, m < n → ¬nimP move rank hmove m x) ∧
  (∀ y, move x y → ¬nimP move rank hmove n y)
termination_by n + rank x
decreasing_by
  · omega
  · have := hmove x y ‹move x y›
    omega

theorem subtractionP_recurrence
    (S : Set Nat) (hpos : ∀ s ∈ S, 0 < s)
    (move : G → G → Prop) (rank : G → Nat)
    (hmove : ∀ x y, move x y → rank y < rank x) :
    SubtractionRecurrence S move (subtractionP S hpos move rank hmove) := by
  intro n x
  rw [subtractionP]

theorem nimP_recurrence
    (move : G → G → Prop) (rank : G → Nat)
    (hmove : ∀ x y, move x y → rank y < rank x) :
    NimRecurrence move (nimP move rank hmove) := by
  intro n x
  rw [nimP]

/-- Against a terminal context, the one-counter Nim heap is a previous-player
win.  This is the terminal exception required in the global comparison. -/
theorem nim_one_of_context_terminal {move : G → G → Prop}
    {W : Nat → G → Prop} (hW : NimRecurrence move W) {x : G}
    (hstop : ∀ y, ¬move x y) : W 1 x := by
  have hzero : ¬W 0 x := by
    intro h
    rcases ((hW 0 x).mp h).1 with h | ⟨y, hy⟩
    · omega
    · exact hstop y hy
  apply (hW 1 x).mpr
  refine ⟨Or.inl (by omega), ?_, ?_⟩
  · intro m hm
    have : m = 0 := by omega
    simpa [this] using hzero
  · intro y hy
    exact (hstop y hy).elim

/-- The global comparison uses only the mex conditions and the additional
zero-to-one property.  Context moves must decrease their supplied rank; no
condition restricts the context's game values or its available moves. -/
theorem context_equivalence_of_sg
    {S : Set Nat} {g : Nat → Nat}
    (hpos : ∀ s ∈ S, 0 < s) (hg : IsSG S g)
    (hzero : ∀ n, (∃ s ∈ S, s ≤ n) → g n = 0 →
      ∃ s ∈ S, s ≤ n ∧ g (n - s) = 1)
    {move : G → G → Prop} (rank : G → Nat)
    (hmove : ∀ x y, move x y → rank y < rank x)
    {Wsub Wnim : Nat → G → Prop}
    (hsub : SubtractionRecurrence S move Wsub)
    (hnim : NimRecurrence move Wnim) :
    ∀ n x, Wsub n x ↔ Wnim (g n) x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ihn =>
      have hcontext : ∀ k x, rank x = k → (Wsub n x ↔ Wnim (g n) x) := by
        intro k
        induction k using Nat.strong_induction_on with
        | h k ihk =>
            intro x hx
            have ihctx : ∀ y, move x y → (Wsub n y ↔ Wnim (g n) y) := by
              intro y hy
              exact ihk (rank y) (by simpa [← hx] using hmove x y hy) y rfl
            constructor
            · intro hw
              obtain ⟨hmoving, hheap, hctx⟩ := (hsub n x).mp hw
              apply (hnim (g n) x).mpr
              refine ⟨?_, ?_, ?_⟩
              · rcases hmoving with hheapmove | hctxmove
                · by_cases hgn : g n = 0
                  · by_cases hctxmove : ∃ y, move x y
                    · exact Or.inr hctxmove
                    · obtain ⟨s, hs, hsn, hsg⟩ := hzero n hheapmove hgn
                      have hless : n - s < n := by
                        have := hpos s hs
                        omega
                      have hnimone : Wnim 1 x := nim_one_of_context_terminal hnim
                        (by simpa using hctxmove)
                      have hsubone : Wsub (n - s) x :=
                        (ihn (n - s) hless x).mpr (by simpa [hsg] using hnimone)
                      exact (hheap s hs hsn hsubone).elim
                  · exact Or.inl (by omega)
                · exact Or.inr hctxmove
              · intro m hm hwm
                obtain ⟨s, hs, hsn, hsg⟩ := hg.reaches n m hm
                have hless : n - s < n := by
                  have := hpos s hs
                  omega
                exact hheap s hs hsn
                  ((ihn (n - s) hless x).mpr (by simpa [hsg] using hwm))
              · intro y hy hwy
                exact hctx y hy ((ihctx y hy).mpr hwy)
            · intro hw
              obtain ⟨hmoving, hheap, hctx⟩ := (hnim (g n) x).mp hw
              apply (hsub n x).mpr
              refine ⟨?_, ?_, ?_⟩
              · rcases hmoving with hgn | hctxmove
                · obtain ⟨s, hs, hsn, _⟩ := hg.reaches n 0 hgn
                  exact Or.inl ⟨s, hs, hsn⟩
                · exact Or.inr hctxmove
              · intro s hs hsn hws
                have hless : n - s < n := by
                  have := hpos s hs
                  omega
                have hchild : Wnim (g (n - s)) x := (ihn (n - s) hless x).mp hws
                have hne : g (n - s) ≠ g n := hg.avoids n s hs hsn
                rcases lt_or_gt_of_ne hne with hlt | hgt
                · exact hheap (g (n - s)) hlt hchild
                · exact ((hnim (g (n - s)) x).mp hchild).2.1 (g n) hgt hw
              · intro y hy hwy
                exact hctx y hy ((ihctx y hy).mp hwy)
      intro x
      exact hcontext (rank x) x rfl

/-- Ferguson's shift supplies the extra zero-to-one hypothesis for every
ordinary subtraction set having a least positive move. -/
theorem subtraction_context_equivalence
    {S : Set Nat} {g : Nat → Nat} (hg : IsSG S g)
    {s : Nat} (hs : s ∈ S) (hspos : 0 < s)
    (hmin : ∀ t ∈ S, s ≤ t)
    {move : G → G → Prop} (rank : G → Nat)
    (hmove : ∀ x y, move x y → rank y < rank x)
    {Wsub Wnim : Nat → G → Prop}
    (hsub : SubtractionRecurrence S move Wsub)
    (hnim : NimRecurrence move Wnim) (n : Nat) (x : G) :
    Wsub n x ↔ Wnim (g n) x := by
  apply context_equivalence_of_sg
    (fun t ht => hspos.trans_le (hmin t ht)) hg ?_ rank hmove hsub hnim n x
  intro m hm hgm
  obtain ⟨t, ht, htm⟩ := hm
  exact zero_has_one_option hg hs hspos hmin ((hmin t ht).trans htm) hgm

/-- For a finite positive subtraction set, the actual recursively defined SG
sequence gives the same comparison in every context.  The empty set is
included: its heaps are terminal. -/
theorem finite_subtraction_context_equivalence
    (S : Finset Nat) (hpos : ∀ s ∈ S, 0 < s)
    {move : G → G → Prop} (rank : G → Nat)
    (hmove : ∀ x y, move x y → rank y < rank x)
    {Wsub Wnim : Nat → G → Prop}
    (hsub : SubtractionRecurrence (S : Set Nat) move Wsub)
    (hnim : NimRecurrence move Wnim) (n : Nat) (x : G) :
    Wsub n x ↔ Wnim (grundy S hpos n) x := by
  apply context_equivalence_of_sg hpos (grundy_isSG S hpos) ?_
    rank hmove hsub hnim n x
  intro m hm hgm
  obtain ⟨t, ht, htm⟩ := hm
  have hne : S.Nonempty := ⟨t, ht⟩
  let s := S.min' hne
  have hs : s ∈ S := Finset.min'_mem S hne
  have hmin : ∀ u ∈ S, s ≤ u := fun u hu => Finset.min'_le S u hu
  exact zero_has_one_option (grundy_isSG S hpos) hs (hpos s hs) hmin
    ((hmin t ht).trans htm) hgm

/-- Every finite ordinary subtraction heap is globally equivalent to its
normal-play Nim heap: the actual outcomes agree after adding any ranked
impartial context.  The heap size and the context rank are unbounded. -/
theorem finite_subtraction_eq_nim
    (S : Finset Nat) (hpos : ∀ s ∈ S, 0 < s)
    (move : G → G → Prop) (rank : G → Nat)
    (hmove : ∀ x y, move x y → rank y < rank x) (n : Nat) (x : G) :
    subtractionP (S : Set Nat) hpos move rank hmove n x ↔
      nimP move rank hmove (grundy S hpos n) x :=
  finite_subtraction_context_equivalence S hpos rank hmove
    (subtractionP_recurrence (S : Set Nat) hpos move rank hmove)
    (nimP_recurrence move rank hmove) n x

end Ogdoad.MisereSubtractionContext
