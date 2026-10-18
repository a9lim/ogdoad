import Ogdoad.MisereTransition

/-!
# Safe saturation of valid misere transition tables

A nonempty transition option set can be enlarged inside its meximal set.
The empty transition needs an additional parity condition: meximality alone
would incorrectly allow a nonempty set of `N`-options for the terminal value.
The saturation below retains that condition and is closed under products.
-/

namespace Ogdoad.MisereTransition

open Set

variable {Q : Type*} [CommMonoid Q]

/-- Enlarge a table's option sets inside their meximal sets, retaining the
misere parity condition at the empty baseline transition. -/
def Saturation (P : Set Q) (T : Set (Transition Q)) : Set (Transition Q) :=
  {t | ∃ E₀, Transition.mk t.value E₀ ∈ T ∧ E₀ ⊆ t.options ∧
    t.options ⊆ Meximal P t.value ∧ ParityCorrect P t}

/-- Meximal safety is stable under the transition product. -/
theorem product_options_subset_meximal
    {P : Set Q} {s t : Transition Q}
    (hs : s.options ⊆ Meximal P s.value)
    (ht : t.options ⊆ Meximal P t.value) :
    (product s t).options ⊆ Meximal P (product s t).value := by
  intro q hq z hboth
  rcases hq with hq | hq
  · obtain ⟨e, he, rfl⟩ := hq
    apply hs he (t.value * z)
    constructor
    · simpa [product, mul_assoc] using hboth.1
    · simpa [mul_assoc, mul_comm, mul_left_comm] using hboth.2
  · obtain ⟨e, he, rfl⟩ := hq
    apply ht he (s.value * z)
    constructor
    · simpa [product, mul_assoc, mul_comm, mul_left_comm] using hboth.1
    · simpa [mul_assoc, mul_comm, mul_left_comm] using hboth.2

private theorem product_options_mono
    {x y : Q} {E₀ E F₀ F : Set Q}
    (hE : E₀ ⊆ E) (hF : F₀ ⊆ F) :
    (product (Transition.mk x E₀) (Transition.mk y F₀)).options ⊆
      (product (Transition.mk x E) (Transition.mk y F)).options := by
  intro q hq
  rcases hq with hq | hq
  · obtain ⟨e, he, rfl⟩ := hq
    exact Or.inl ⟨e, hE he, rfl⟩
  · obtain ⟨f, hf, rfl⟩ := hq
    exact Or.inr ⟨f, hF hf, rfl⟩

/-- A nonempty baseline transition needs no further parity hypothesis when
its option set is enlarged inside the meximal set. -/
theorem nonempty_sandwich_parity
    {P : Set Q} {x : Q} {E₀ E : Set Q}
    (hbase : ParityCorrect P (Transition.mk x E₀))
    (hne : E₀.Nonempty) (hsub : E₀ ⊆ E)
    (hsafe : E ⊆ Meximal P x) :
    ParityCorrect P (Transition.mk x E) := by
  constructor
  · intro hx
    refine ⟨hne.mono hsub, ?_⟩
    intro y hy hyP
    exact hsafe hy 1 ⟨by simpa using hx, by simpa using hyP⟩
  · rintro ⟨_, hall⟩
    exact hbase.mpr ⟨hne, fun y hy => hall y (hsub hy)⟩

/-- The original table is contained in its safe saturation. -/
theorem subset_saturation
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hclosed : Closed T) (hparity : ParityTable P T)
    (hranked : Ranked T R) : T ⊆ Saturation P T := by
  intro t ht
  exact ⟨t.options, ht, Subset.rfl,
    options_subset_meximal hclosed hparity hranked ht, hparity ht⟩

/-- Every sandwich with a nonempty baseline is admitted by safe saturation. -/
theorem nonempty_sandwich_mem_saturation
    {P : Set Q} {T : Set (Transition Q)} {x : Q} {E₀ E : Set Q}
    (hparity : ParityTable P T)
    (hbase : Transition.mk x E₀ ∈ T) (hne : E₀.Nonempty)
    (hsub : E₀ ⊆ E) (hsafe : E ⊆ Meximal P x) :
    Transition.mk x E ∈ Saturation P T := by
  exact ⟨E₀, hbase, hsub, hsafe,
    nonempty_sandwich_parity (hparity hbase) hne hsub hsafe⟩

/-- Safe saturation remains parity-correct by construction. -/
theorem saturation_parity
    {P : Set Q} {T : Set (Transition Q)} :
    ParityTable P (Saturation P T) := by
  rintro t ⟨_, _, _, _, hparity⟩
  exact hparity

/-- Safe saturation preserves all descending representatives and their rank. -/
theorem saturation_ranked
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hclosed : Closed T) (hparity : ParityTable P T)
    (hranked : Ranked T R) : Ranked (Saturation P T) R := by
  intro x
  obtain ⟨E, hE, hdesc⟩ := hranked x
  exact ⟨E, subset_saturation hclosed hparity hranked hE, hdesc⟩

/-- Safe saturation is closed under products. The only exceptional case is
an empty baseline product; determinism then identifies both factors with the
terminal value, and the retained individual parity conditions settle it. -/
theorem saturation_closed
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R) :
    Closed (Saturation P T) := by
  classical
  rintro s t ⟨E₀, hs₀, hEs, hsmex, hspar⟩
    ⟨F₀, ht₀, hFt, htmex, htpar⟩
  let b := product (Transition.mk s.value E₀) (Transition.mk t.value F₀)
  have hb : b ∈ T := hclosed hs₀ ht₀
  have hsub : b.options ⊆ (product s t).options :=
    product_options_mono hEs hFt
  have hmex := product_options_subset_meximal hsmex htmex
  refine ⟨b.options, hb, hsub, hmex, ?_⟩
  by_cases hne : b.options.Nonempty
  · exact nonempty_sandwich_parity (hparity hb) hne hsub hmex
  · have hEempty : E₀ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact hne ⟨t.value * e, Or.inl ⟨e, he, rfl⟩⟩
    have hFempty : F₀ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro f hf
      exact hne ⟨s.value * f, Or.inr ⟨f, hf, rfl⟩⟩
    have hs1 : s.value = 1 :=
      value_eq_of_options_eq hreduced hclosed hparity hranked
        hs₀ hterminal hEempty
    have ht1 : t.value = 1 :=
      value_eq_of_options_eq hreduced hclosed hparity hranked
        ht₀ hterminal hFempty
    have h1 : (1 : Q) ∉ P := by
      intro h
      have := ((hparity hterminal).mp h).1
      simp at this
    constructor
    · intro hp
      exact False.elim (h1 (by simpa [product, hs1, ht1] using hp))
    · rintro ⟨⟨q, hq⟩, hall⟩
      have hsPfree : ∀ e ∈ s.options, e ∉ P := by
        intro e he heP
        exact hall (t.value * e) (Or.inl ⟨e, he, rfl⟩)
          (by simpa [ht1] using heP)
      have htPfree : ∀ f ∈ t.options, f ∉ P := by
        intro f hf hfP
        exact hall (s.value * f) (Or.inr ⟨f, hf, rfl⟩)
          (by simpa [hs1] using hfP)
      rcases hq with hq | hq
      · obtain ⟨e, he, _⟩ := hq
        exact False.elim (h1 (by simpa [hs1] using hspar.mpr ⟨⟨e, he⟩, hsPfree⟩))
      · obtain ⟨f, hf, _⟩ := hq
        exact False.elim (h1 (by simpa [ht1] using htpar.mpr ⟨⟨f, hf⟩, htPfree⟩))

/-- A parity-correct terminal-valued transition is either empty or has a
`P`-option. This is the condition that an unrestricted meximal enlargement
of the empty transition would omit. -/
theorem terminal_parity_iff
    {P : Set Q} {E : Set Q} (h1 : (1 : Q) ∉ P) :
    ParityCorrect P (Transition.mk 1 E) ↔
      E = ∅ ∨ ∃ e ∈ E, e ∈ P := by
  classical
  constructor
  · intro h
    by_cases hE : E.Nonempty
    · right
      by_contra hn
      push Not at hn
      exact h1 (h.mpr ⟨hE, hn⟩)
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hE)
  · intro h
    constructor
    · intro hp
      exact False.elim (h1 hp)
    · rintro ⟨hne, hfree⟩
      rcases h with h | ⟨e, he, heP⟩
      · simp [h] at hne
      · exact False.elim (hfree e he heP)

end Ogdoad.MisereTransition
