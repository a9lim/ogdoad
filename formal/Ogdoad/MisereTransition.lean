import Mathlib.Data.Set.Image
import Mathlib.Tactic

/-!
# Valid transition tables for finite misere quotients

This module isolates the algebraic core of Siegel's transition-table
realization theorem.  The main result is a determinism lemma that is useful
for natural heap rulesets: in a reduced valid table, an option-value set has
at most one value.  The proof is not a finite search.  It chooses a
least-rank context separating two alleged values and uses closure to push the
separation to an option of strictly smaller rank.

The definitions use `Set` rather than a finiteness hypothesis.  Finiteness is
needed later for decision procedures and periodicity bounds, but not for the
determinism argument.
-/

namespace Ogdoad.MisereTransition

open Set

variable {Q : Type*} [CommMonoid Q]

/-- A quotient value together with the set of quotient values of its options. -/
structure Transition (Q : Type*) where
  value : Q
  options : Set Q

/-- Left multiplication of every member of an option-value set. -/
def leftMul (x : Q) (E : Set Q) : Set Q :=
  (fun y => x * y) '' E

/-- The transition pair of a disjunctive sum. -/
def product (s t : Transition Q) : Transition Q where
  value := s.value * t.value
  options := leftMul t.value s.options ∪ leftMul s.value t.options

/-- Misere parity recursion for one transition pair.  The identity terminal
pair has empty option set and is therefore outside `P`. -/
def ParityCorrect (P : Set Q) (t : Transition Q) : Prop :=
  t.value ∈ P ↔ t.options.Nonempty ∧ ∀ y ∈ t.options, y ∉ P

/-- A context separates two quotient values when exactly one product is in
the distinguished `P`-portion. -/
def Separates (P : Set Q) (x y z : Q) : Prop :=
  (x * z ∈ P ∧ y * z ∉ P) ∨ (x * z ∉ P ∧ y * z ∈ P)

/-- The bipartite monoid is reduced: every two distinct values have a
separating context. -/
def Reduced (P : Set Q) : Prop :=
  ∀ ⦃x y : Q⦄, x ≠ y → ∃ z, Separates P x y z

/-- Transition-table closure under disjunctive sum. -/
def Closed (T : Set (Transition Q)) : Prop :=
  ∀ ⦃s t : Transition Q⦄, s ∈ T → t ∈ T → product s t ∈ T

/-- Every table entry obeys misere parity. -/
def ParityTable (P : Set Q) (T : Set (Transition Q)) : Prop :=
  ∀ ⦃t : Transition Q⦄, t ∈ T → ParityCorrect P t

/-- A rank witnesses one well-founded representative for every quotient
value.  Only this descending representative is used by the determinism proof. -/
def Ranked (T : Set (Transition Q)) (R : Q → Nat) : Prop :=
  ∀ x, ∃ E, Transition.mk x E ∈ T ∧ ∀ y ∈ E, R y < R x

/-- The meximal set of `x`: no context makes both `x` and `y` previous-player
wins. -/
def Meximal (P : Set Q) (x : Q) : Set Q :=
  {y | ∀ z, ¬(x * z ∈ P ∧ y * z ∈ P)}

/-- Every option of a valid transition lies in the value's meximal set. -/
theorem options_subset_meximal
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hclosed : Closed T) (hparity : ParityTable P T)
    (hranked : Ranked T R) {t : Transition Q} (ht : t ∈ T) :
    t.options ⊆ Meximal P t.value := by
  intro e he z hboth
  obtain ⟨F, hzT, _⟩ := hranked z
  have hprod : product t (Transition.mk z F) ∈ T := hclosed ht hzT
  have hsafe := (hparity hprod).mp hboth.1
  have hze : z * e ∈ (product t (Transition.mk z F)).options :=
    Or.inl ⟨e, he, rfl⟩
  exact hsafe.2 (z * e) hze (by simpa [mul_comm] using hboth.2)

private theorem lower_separator_of_same_options_oriented
    {P : Set Q} {T : Set (Transition Q)}
    (hclosed : Closed T) (hparity : ParityTable P T)
    {x y z : Q} {E F : Set Q}
    (hx : Transition.mk x E ∈ T) (hy : Transition.mk y E ∈ T)
    (hz : Transition.mk z F ∈ T)
    (hxz : x * z ∈ P) (hyz : y * z ∉ P) :
    ∃ f ∈ F, x * f ∉ P ∧ y * f ∈ P := by
  let tx : Transition Q := Transition.mk x E
  let ty : Transition Q := Transition.mk y E
  let tz : Transition Q := Transition.mk z F
  have htxz : product tx tz ∈ T := hclosed hx hz
  have htyz : product ty tz ∈ T := hclosed hy hz
  have hgoodX := (hparity htxz).mp hxz
  have hbadY :
      ¬((product ty tz).options.Nonempty ∧
        ∀ q ∈ (product ty tz).options, q ∉ P) := by
    intro h
    exact hyz ((hparity htyz).mpr h)
  have hnonemptyY : (product ty tz).options.Nonempty := by
    obtain ⟨q, hq⟩ := hgoodX.1
    rcases hq with hq | hq
    · obtain ⟨e, he, rfl⟩ := hq
      exact ⟨z * e, Or.inl ⟨e, he, rfl⟩⟩
    · obtain ⟨f, hf, rfl⟩ := hq
      exact ⟨y * f, Or.inr ⟨f, hf, rfl⟩⟩
  have hnotsafeY : ¬∀ q ∈ (product ty tz).options, q ∉ P := by
    intro hs
    exact hbadY ⟨hnonemptyY, hs⟩
  push Not at hnotsafeY
  obtain ⟨q, hqY, hqP⟩ := hnotsafeY
  rcases hqY with hqY | hqY
  · obtain ⟨e, he, rfl⟩ := hqY
    exact False.elim (hgoodX.2 (z * e) (Or.inl ⟨e, he, rfl⟩) hqP)
  · obtain ⟨f, hf, rfl⟩ := hqY
    refine ⟨f, hf, ?_, hqP⟩
    exact hgoodX.2 (x * f) (Or.inr ⟨f, hf, rfl⟩)

/-- If equal option sets were assigned two values separated by `z`, then a
descending transition for `z` contains an option that already separates the
same two values. -/
theorem lower_separator_of_same_options
    {P : Set Q} {T : Set (Transition Q)}
    (hclosed : Closed T) (hparity : ParityTable P T)
    {x y z : Q} {E F : Set Q}
    (hx : Transition.mk x E ∈ T) (hy : Transition.mk y E ∈ T)
    (hz : Transition.mk z F ∈ T)
    (hsep : Separates P x y z) :
    ∃ f ∈ F, Separates P x y f := by
  rcases hsep with hsep | hsep
  · obtain ⟨f, hf, hxf, hyf⟩ :=
      lower_separator_of_same_options_oriented hclosed hparity
        hx hy hz hsep.1 hsep.2
    exact ⟨f, hf, Or.inr ⟨hxf, hyf⟩⟩
  · obtain ⟨f, hf, hyf, hxf⟩ :=
      lower_separator_of_same_options_oriented hclosed hparity
        hy hx hz hsep.2 hsep.1
    exact ⟨f, hf, Or.inl ⟨hxf, hyf⟩⟩

/-- **Transition determinism.** In a reduced parity-correct closed table with
a well-founded rank, the option-value set determines the quotient value. -/
theorem value_eq_of_options_eq
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {s t : Transition Q} (hs : s ∈ T) (ht : t ∈ T)
    (hoptions : s.options = t.options) : s.value = t.value := by
  classical
  by_contra hne
  have hsep0 : ∃ z, Separates P s.value t.value z := hreduced hne
  have hexistsRank :
      ∃ n, ∃ z, Separates P s.value t.value z ∧ R z = n := by
    obtain ⟨z, hz⟩ := hsep0
    exact ⟨R z, z, hz, rfl⟩
  let n := Nat.find hexistsRank
  obtain ⟨z, hzsep, hzrank⟩ := Nat.find_spec hexistsRank
  obtain ⟨F, hzT, hdesc⟩ := hranked z
  have htSame : Transition.mk t.value s.options ∈ T := by
    simpa [hoptions] using ht
  obtain ⟨f, hf, hfsep⟩ :=
    lower_separator_of_same_options hclosed hparity hs htSame hzT hzsep
  have hleast : n ≤ R f := by
    apply Nat.find_min' hexistsRank
    exact ⟨f, hfsep, rfl⟩
  have hsmaller : R f < n := by
    change R f < Nat.find hexistsRank
    rw [← hzrank]
    exact hdesc f hf
  omega

section PeriodicConvolution

/-- Products contributed by positive two-heap splits with total size `m`.
Using ordered pairs avoids division; commutativity identifies this set with
the usual octal convention that lists each unordered split once. -/
def splitSet (x : Nat → Q) (m : Nat) : Set Q :=
  {q | ∃ i j, 1 ≤ i ∧ 1 ≤ j ∧ i + j = m ∧ q = x i * x j}

/-- An ultimately periodic heap word has an ultimately periodic split
convolution.  The bound includes the preperiod-crossing pairs explicitly. -/
theorem splitSet_add_period
    (x : Nat → Q) {N p m : Nat}
    (hN : 1 ≤ N) (hp : 1 ≤ p)
    (hperiod : ∀ n, N ≤ n → x (n + p) = x n)
    (hm : 2 * N + p ≤ m) :
    splitSet x (m + p) = splitSet x m := by
  ext q
  constructor
  · rintro ⟨i, j, hi, hj, hij, rfl⟩
    by_cases hiTail : N + p ≤ i
    · refine ⟨i - p, j, ?_, hj, ?_, ?_⟩
      · omega
      · omega
      · have hxi : x i = x (i - p) := by
          have hbase : N ≤ i - p := by omega
          have := hperiod (i - p) hbase
          simpa [Nat.sub_add_cancel (by omega : p ≤ i)] using this
        rw [hxi]
    · have hjTail : N + p ≤ j := by omega
      refine ⟨i, j - p, hi, ?_, ?_, ?_⟩
      · omega
      · omega
      · have hxj : x j = x (j - p) := by
          have hbase : N ≤ j - p := by omega
          have := hperiod (j - p) hbase
          simpa [Nat.sub_add_cancel (by omega : p ≤ j)] using this
        rw [hxj]
  · rintro ⟨i, j, hi, hj, hij, rfl⟩
    by_cases hiTail : N ≤ i
    · refine ⟨i + p, j, ?_, hj, ?_, ?_⟩
      · omega
      · omega
      · rw [hperiod i hiTail]
    · have hjTail : N ≤ j := by omega
      refine ⟨i, j + p, hi, ?_, ?_, ?_⟩
      · omega
      · omega
      · rw [hperiod j hjTail]

end PeriodicConvolution

end Ogdoad.MisereTransition
