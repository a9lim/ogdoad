import Ogdoad.MisereParityTrace

/-!
# Repairing a terminal octal record

If one heap is terminal, no persistent octal move is active at any earlier
heap. Every earlier positive heap therefore has either the terminal value
or the star value. This fact repairs the exceptional empty-baseline case
when a new octal option set is known to be meximal-safe.
-/

namespace Ogdoad.MisereOctalTerminal

open Set
open Ogdoad.MisereTransition
open Ogdoad.MisereOctalCertificate
open Ogdoad.MisereNaturalUniversality
open Ogdoad.MisereParityTrace

variable {Q : Type*} [CommMonoid Q]

/-- Before a terminal octal heap, whole-heap removals are the only possible
moves. Persistent one-remainder and split moves would also act at the
terminal heap. -/
theorem options_before_terminal_subset_one
    {x : Nat → Q} {whole one two : Set Nat} {n j : Nat}
    (hterminal : octalOptions x whole one two n = ∅) (hjn : j ≤ n) :
    octalOptions x whole one two j ⊆ ({1} : Set Q) := by
  intro q hq
  rcases hq with (hwhole | hone) | htwo
  · exact hwhole.1
  · obtain ⟨k, hk, hkj, _⟩ := hone
    have hopt : x (n - k) ∈ octalOptions x whole one two n :=
      Or.inl (Or.inr ⟨k, hk, lt_of_lt_of_le hkj hjn, rfl⟩)
    rw [hterminal] at hopt
    exact False.elim hopt
  · obtain ⟨k, hk, hkj, _⟩ := htwo
    obtain ⟨r, hr⟩ := two_bit_forces_nonempty x hk (le_trans hkj hjn)
    have hopt : r ∈ octalOptions x whole one two n := Or.inr hr
    rw [hterminal] at hopt
    exact False.elim hopt

/-- A valid trace before a terminal heap takes only the values `1` and `a`,
where `(a,{1})` is the star record. The empty heap need not be specified. -/
theorem value_before_terminal_eq_one_or_star
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {a : Q} (hstar : Transition.mk a ({1} : Set Q) ∈ T)
    {x : Nat → Q} {whole one two : Set Nat} {n : Nat}
    (htrace : ∀ j, 0 < j → j ≤ n →
      Transition.mk (x j) (octalOptions x whole one two j) ∈ T)
    (hempty : octalOptions x whole one two n = ∅)
    {j : Nat} (hj : 0 < j) (hjn : j ≤ n) :
    x j = 1 ∨ x j = a := by
  classical
  have hsub := options_before_terminal_subset_one hempty hjn
  by_cases hE : (octalOptions x whole one two j).Nonempty
  · right
    have hEq : octalOptions x whole one two j = ({1} : Set Q) := by
      apply Subset.antisymm hsub
      intro q hq
      have hq1 : q = 1 := hq
      obtain ⟨r, hr⟩ := hE
      have hr1 : r = 1 := hsub hr
      simpa [hq1, hr1] using hr
    exact value_eq_of_options_eq hreduced hclosed hparity hranked
      (htrace j hj hjn) hstar hEq
  · left
    exact value_eq_of_options_eq hreduced hclosed hparity hranked
      (htrace j hj hjn) hterminal (not_nonempty_iff_eq_empty.mp hE)

/-- Every octal option over a `1,a` prefix is again `1` or `a`, provided
`a` is an involution and one-remainder removals are positive. Split remainders
are automatically smaller than their source, even at removal offset zero. -/
theorem options_mem_pair_of_prefix
    {a : Q} (ha2 : a ^ 2 = 1)
    {x : Nat → Q} {whole one two : Set Nat} {n : Nat}
    (hone : ∀ k ∈ one, 0 < k)
    (hprefix : ∀ j, 0 < j → j < n → x j = 1 ∨ x j = a) :
    ∀ q ∈ octalOptions x whole one two n, q = 1 ∨ q = a := by
  intro q hq
  rcases hq with (hwhole | honeOpt) | htwoOpt
  · exact Or.inl hwhole.1
  · obtain ⟨k, hk, hkn, rfl⟩ := honeOpt
    exact hprefix (n - k) (by omega) (by have := hone k hk; omega)
  · obtain ⟨k, _, hkn, i, j, hi, hj, hij, rfl⟩ := htwoOpt
    have hi' := hprefix i hi (by omega)
    have hj' := hprefix j hj (by omega)
    rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj'
    · simp [hi', hj']
    · simp [hi', hj']
    · simp [hi', hj']
    · left
      simpa [hi', hj', pow_two] using ha2

/-- A meximal-safe option set consisting of terminal and star values is
already a valid terminal-valued record in the original table. Safety removes
`1`; the only remaining sets are empty and `{a}`. -/
theorem safe_pair_record_mem_table
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {a : Q} (hstar : Transition.mk a ({1} : Set Q) ∈ T)
    {E : Set Q} (hpair : ∀ q ∈ E, q = 1 ∨ q = a)
    (hsafe : E ⊆ Meximal P 1) :
    Transition.mk 1 E ∈ T := by
  classical
  have h1P : (1 : Q) ∉ P := by
    intro hp
    have := ((hparity hterminal).mp hp).1
    simp at this
  have haP : a ∈ P := (hparity hstar).mpr
    ⟨⟨1, by simp⟩, by simpa using h1P⟩
  have hnot1 : (1 : Q) ∉ E := by
    intro h1
    exact hsafe h1 a ⟨by simpa using haP, by simpa using haP⟩
  have hsub : E ⊆ ({a} : Set Q) := by
    intro q hq
    rcases hpair q hq with hq1 | hqa
    · exact False.elim (hnot1 (by simpa [hq1] using hq))
    · exact hqa
  by_cases hE : E.Nonempty
  · have hEq : E = ({a} : Set Q) := by
      apply Subset.antisymm hsub
      intro q hq
      have hqa : q = a := hq
      obtain ⟨r, hr⟩ := hE
      have hra : r = a := hsub hr
      simpa [hqa, hra] using hr
    have ha2 := star_square_eq_one hterminal hreduced hclosed hparity hranked hstar
    simpa [hEq, ha2] using unary_chain_transition hclosed hstar 1
  · simpa [not_nonempty_iff_eq_empty.mp hE] using hterminal

/-- **Terminal repair for actual octal records.** If the original heap is
terminal and its positive prefix is valid, any replacement octal record with
positive one-remainder offsets and meximal-safe options remains valid in the
original table. No assumption on the replacement code's length is needed. -/
theorem terminal_octal_record_repair
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {a : Q} (hstar : Transition.mk a ({1} : Set Q) ∈ T)
    {x : Nat → Q} {whole one two whole' one' two' : Set Nat} {n : Nat}
    (hn : 0 < n)
    (htrace : ∀ j, 0 < j → j ≤ n →
      Transition.mk (x j) (octalOptions x whole one two j) ∈ T)
    (hempty : octalOptions x whole one two n = ∅)
    (hone' : ∀ k ∈ one', 0 < k)
    (hsafe : octalOptions x whole' one' two' n ⊆ Meximal P (x n)) :
    Transition.mk (x n) (octalOptions x whole' one' two' n) ∈ T := by
  have hxn : x n = 1 := value_eq_of_options_eq
    hreduced hclosed hparity hranked (htrace n hn le_rfl) hterminal hempty
  have ha2 := star_square_eq_one hterminal hreduced hclosed hparity hranked hstar
  have hprefix : ∀ j, 0 < j → j < n → x j = 1 ∨ x j = a := by
    intro j hj hjn
    exact value_before_terminal_eq_one_or_star hterminal hreduced hclosed
      hparity hranked hstar htrace hempty hj (Nat.le_of_lt hjn)
  rw [hxn]
  exact safe_pair_record_mem_table hterminal hreduced hclosed hparity hranked hstar
    (options_mem_pair_of_prefix ha2 hone' hprefix) (by simpa [hxn] using hsafe)

end Ogdoad.MisereOctalTerminal
