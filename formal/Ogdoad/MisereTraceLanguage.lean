import Ogdoad.MisereOctalCertificate

/-!
# Unary language equations for finite octal traces

For a fixed candidate heap word, the indices carrying a quotient value form a
unary language.  The indices at which an option value `q` occurs are described
by a finite Boolean/convolution expression: a finite whole-heap constant,
finite shifts of value languages, and finite shifts of pairwise sums of value
languages whose monoid products are `q`.

The exact option-set language `exactOptionLanguage ... S` is the Boolean cell
where precisely the option values in `S` occur.  A partial deterministic table
therefore gives a system of unary Boolean language equations.  Its failure
language records exactly the coefficients at which the table is undefined.

This module proves only that exact dictionary.  It does not import any external
formal-language decidability or undecidability theorem.
-/

namespace Ogdoad.MisereTraceLanguage

open Set
open Ogdoad.MisereTransition
open Ogdoad.MisereOctalCertificate

variable {Q : Type*} [CommMonoid Q]

/-- The unary language of heap indices carrying the value `q`. -/
def valueLanguage (x : Nat → Q) (q : Q) : Set Nat :=
  {n | x n = q}

/-- The unary language `A_q` of heap indices at which `q` occurs as an option
value.  The three disjuncts are respectively the whole-heap constant, a finite
shift of a value language, and a shifted additive convolution of two value
languages with prescribed monoid product. -/
def optionValueLanguage
    (x : Nat → Q) (whole one two : Set Nat) (q : Q) : Set Nat :=
  {n |
    (q = 1 ∧ n ∈ whole) ∨
    (∃ k, k ∈ one ∧ k < n ∧ q = x (n - k)) ∨
    ∃ k, k ∈ two ∧ k + 2 ≤ n ∧
      ∃ i j, 1 ≤ i ∧ 1 ≤ j ∧ i + j = n - k ∧ q = x i * x j}

/-- Coefficientwise, `A_q` says exactly that `q` belongs to the octal option
set. -/
theorem mem_optionValueLanguage_iff
    (x : Nat → Q) (whole one two : Set Nat) (q : Q) (n : Nat) :
    n ∈ optionValueLanguage x whole one two q ↔
      q ∈ octalOptions x whole one two n := by
  simp only [optionValueLanguage, mem_setOf_eq, octalOptions, mem_union,
    wholeHeapOptions, oneRemainderOptions, twoRemainderOptions, splitSet]
  constructor
  · rintro (hwhole | hone | htwo)
    · exact Or.inl (Or.inl hwhole)
    · exact Or.inl (Or.inr hone)
    · exact Or.inr htwo
  · rintro ((hwhole | hone) | htwo)
    · exact Or.inl hwhole
    · exact Or.inr (Or.inl hone)
    · exact Or.inr (Or.inr htwo)

/-- The Boolean cell `D_S`: exactly the option values in `S`, and no others,
occur at this coefficient.  Writing the condition as an iff is the pointwise
form of intersecting all positive `A_q` and all negative complements. -/
def exactOptionLanguage
    (x : Nat → Q) (whole one two : Set Nat) (S : Set Q) : Set Nat :=
  {n | ∀ q, q ∈ S ↔ n ∈ optionValueLanguage x whole one two q}

/-- Membership in `D_S` is equivalent to equality of the complete octal option
set with `S`. -/
theorem mem_exactOptionLanguage_iff
    (x : Nat → Q) (whole one two : Set Nat) (S : Set Q) (n : Nat) :
    n ∈ exactOptionLanguage x whole one two S ↔
      octalOptions x whole one two n = S := by
  constructor
  · intro hn
    ext q
    rw [← mem_optionValueLanguage_iff]
    exact (hn q).symm
  · intro hoptions q
    rw [mem_optionValueLanguage_iff, hoptions]

/-- One coefficient of the partial table-driven octal recurrence. -/
def traceStep
    (next : Set Q → Option Q) (x : Nat → Q)
    (whole one two : Set Nat) (n : Nat) : Option Q :=
  next (octalOptions x whole one two n)

/-- A candidate heap word obeys every defined coefficient of the partial
table.  This weak form remains meaningful even when the table later fails. -/
def RespectsDefinedTrace
    (next : Set Q → Option Q) (x : Nat → Q)
    (whole one two : Set Nat) : Prop :=
  ∀ n q, traceStep next x whole one two n = some q → x n = q

/-- A total table-driven trace: every coefficient is defined and returns the
asserted heap value. -/
def IsTrace
    (next : Set Q → Option Q) (x : Nat → Q)
    (whole one two : Set Nat) : Prop :=
  ∀ n, traceStep next x whole one two n = some (x n)

/-- The failure-totalized coefficient.  `0 : WithZero Q` is a new absorbing
failure value, distinct from every successful quotient value. -/
def totalizedTraceStep
    (next : Set Q → Option Q) (x : Nat → Q)
    (whole one two : Set Nat) (n : Nat) : WithZero Q :=
  match traceStep next x whole one two n with
  | none => 0
  | some q => q

/-- The unary language of coefficients at which the partial table is
undefined. -/
def failureLanguage
    (next : Set Q → Option Q) (x : Nat → Q)
    (whole one two : Set Nat) : Set Nat :=
  {n | traceStep next x whole one two n = none}

/-- The adjoined failure value occurs exactly on the failure language. -/
theorem totalizedTraceStep_eq_zero_iff
    (next : Set Q → Option Q) (x : Nat → Q)
    (whole one two : Set Nat) (n : Nat) :
    totalizedTraceStep next x whole one two n = 0 ↔
      n ∈ failureLanguage next x whole one two := by
  unfold totalizedTraceStep failureLanguage
  cases hstep : traceStep next x whole one two n <;> simp [hstep]

/-- The table fails at `n` exactly when the exact Boolean cell `D_S` at `n`
is labelled undefined. -/
theorem mem_failureLanguage_iff_exists_exact
    (next : Set Q → Option Q) (x : Nat → Q)
    (whole one two : Set Nat) (n : Nat) :
    n ∈ failureLanguage next x whole one two ↔
      ∃ S, n ∈ exactOptionLanguage x whole one two S ∧ next S = none := by
  constructor
  · intro hn
    refine ⟨octalOptions x whole one two n, ?_, ?_⟩
    · exact (mem_exactOptionLanguage_iff x whole one two _ n).2 rfl
    · exact hn
  · rintro ⟨S, hnS, hnone⟩
    have hoptions :=
      (mem_exactOptionLanguage_iff x whole one two S n).1 hnS
    simpa [failureLanguage, traceStep, hoptions] using hnone

/-- The partial recurrence is defined at every coefficient iff its failure
language is empty. -/
theorem trace_total_iff_failureLanguage_eq_empty
    (next : Set Q → Option Q) (x : Nat → Q)
    (whole one two : Set Nat) :
    (∀ n, ∃ q, traceStep next x whole one two n = some q) ↔
      failureLanguage next x whole one two = ∅ := by
  constructor
  · intro htotal
    apply Set.eq_empty_iff_forall_notMem.2
    intro n hn
    obtain ⟨q, hq⟩ := htotal n
    rw [failureLanguage, mem_setOf_eq] at hn
    rw [hn] at hq
    contradiction
  · intro hempty n
    have hn : n ∉ failureLanguage next x whole one two := by
      simp [hempty]
    rw [failureLanguage, mem_setOf_eq] at hn
    generalize hstep : traceStep next x whole one two n = step
    cases step with
    | none => exact False.elim (hn hstep)
    | some q => exact ⟨q, rfl⟩

/-- A candidate word is a genuine total trace exactly when it respects every
defined table coefficient and the failure language is empty. -/
theorem isTrace_iff_respectsDefinedTrace_and_failureLanguage_eq_empty
    (next : Set Q → Option Q) (x : Nat → Q)
    (whole one two : Set Nat) :
    IsTrace next x whole one two ↔
      RespectsDefinedTrace next x whole one two ∧
        failureLanguage next x whole one two = ∅ := by
  constructor
  · intro htrace
    constructor
    · intro n q hq
      have hxn := htrace n
      rw [hq] at hxn
      exact Option.some.inj hxn.symm
    · apply (trace_total_iff_failureLanguage_eq_empty next x whole one two).1
      intro n
      exact ⟨x n, htrace n⟩
  · rintro ⟨hrespects, hempty⟩ n
    obtain ⟨q, hq⟩ :=
      (trace_total_iff_failureLanguage_eq_empty next x whole one two).2 hempty n
    have hxn : x n = q := hrespects n q hq
    simpa [hxn] using hq

/-- On a total trace, the value language `X_q` is exactly the union of the
Boolean cells `D_S` whose table label is `q`. -/
theorem mem_valueLanguage_iff_exists_exact
    (next : Set Q → Option Q) (x : Nat → Q)
    (whole one two : Set Nat)
    (htrace : IsTrace next x whole one two) (q : Q) (n : Nat) :
    n ∈ valueLanguage x q ↔
      ∃ S, n ∈ exactOptionLanguage x whole one two S ∧ next S = some q := by
  constructor
  · intro hn
    refine ⟨octalOptions x whole one two n, ?_, ?_⟩
    · exact (mem_exactOptionLanguage_iff x whole one two _ n).2 rfl
    · have htraceN := htrace n
      have hxn : x n = q := hn
      rw [hxn] at htraceN
      exact htraceN
  · rintro ⟨S, hnS, hnext⟩
    have hoptions :=
      (mem_exactOptionLanguage_iff x whole one two S n).1 hnS
    have htraceN := htrace n
    rw [traceStep, hoptions] at htraceN
    rw [hnext] at htraceN
    exact Option.some.inj htraceN.symm

/-- Set-level form of the unary Boolean language equation for `X_q`. -/
theorem valueLanguage_eq_table_cells
    (next : Set Q → Option Q) (x : Nat → Q)
    (whole one two : Set Nat)
    (htrace : IsTrace next x whole one two) (q : Q) :
    valueLanguage x q =
      {n | ∃ S, n ∈ exactOptionLanguage x whole one two S ∧ next S = some q} := by
  ext n
  exact mem_valueLanguage_iff_exists_exact next x whole one two htrace q n

end Ogdoad.MisereTraceLanguage
