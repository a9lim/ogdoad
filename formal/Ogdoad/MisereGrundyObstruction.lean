import Ogdoad.MisereTransition
import Mathlib.Combinatorics.Hindman

/-!
# A finite-trace obstruction for misere Grundy's game

This module isolates the algebraic consequence of a monochromatic Schur
triple in a hypothetical finite transition trace.  If one transition record
`(c, E)` has `c ^ 2` among its option values, then every positive transition
power has the next monoid power among its options.  Valid-table loop-freeness
therefore forbids equality of consecutive powers of `c`.

The combinatorial step producing such a record from a finite Grundy trace is
the distinct-summand form of Schur's theorem.  It is derived here from
Mathlib's stronger formalization of Hindman's finite-sums theorem.
-/

namespace Ogdoad.MisereGrundyObstruction

open Set
open Ogdoad.MisereTransition

variable {Q : Type*} [CommMonoid Q]

/-- Every finite coloring of the positive natural numbers has a
monochromatic triple `i`, `j`, `i + j` with `0 < i < j`.

This is the distinct-summand form of Schur's theorem.  We derive it from
Mathlib's stronger Hindman theorem: first find a monochromatic finite-sums
stream inside the positive naturals, then take one stream term and a long
enough disjoint block sum. -/
theorem exists_distinct_summand_monochromatic
    {C : Type*} [Finite C] (x : Nat → C) :
    ∃ i j : Nat, 0 < i ∧ i < j ∧ x i = x j ∧ x j = x (i + j) := by
  let one : Stream' Nat := Stream'.const 1
  let colors : Set (Set Nat) :=
    Set.range fun c : C ↦ {n : Nat | 0 < n ∧ x n = c}
  have hcolors : colors.Finite := Set.finite_range _
  have fs_pos : ∀ (a : Stream' Nat) {m : Nat},
      (∀ k : Nat, 0 < a.get k) → m ∈ Hindman.FS a → 0 < m := by
    intro a m ha hm
    induction hm with
    | head' a => exact ha 0
    | tail' a m hm ih =>
        apply ih
        intro k
        simpa using ha (k + 1)
    | cons' a m hm ih => exact Nat.add_pos_left (ha 0) m
  have hcover : Hindman.FS one ⊆ ⋃₀ colors := by
    intro n hn
    have hnpos : 0 < n := by
      have hone : ∀ k : Nat, 0 < one.get k := by
        intro k
        simp [one]
      exact fs_pos one hone hn
    refine Set.mem_sUnion.mpr ⟨{m : Nat | 0 < m ∧ x m = x n}, ?_, hnpos, rfl⟩
    exact ⟨x n, rfl⟩
  obtain ⟨_, ⟨c, rfl⟩, b, hb⟩ :=
    Hindman.FS_partition_regular one colors hcolors hcover
  let i := b.get 0
  have hiFS : i ∈ Hindman.FS b := Hindman.FS.singleton b 0
  have hi : 0 < i ∧ x i = c := hb hiFS
  obtain ⟨n, hn⟩ := Hindman.FS.add hiFS
  let s := Finset.range (i + 1)
  let j := ∑ k ∈ s, (b.drop n).get k
  have hs : s.Nonempty := by
    simp [s]
  have hjDrop : j ∈ Hindman.FS (b.drop n) :=
    Hindman.FS.finsetSum (b.drop n) s hs
  have hjFS : j ∈ Hindman.FS b :=
    Hindman.FS_iter_tail_sub_FS b n hjDrop
  have hijFS : i + j ∈ Hindman.FS b := hn j hjDrop
  have hj : 0 < j ∧ x j = c := hb hjFS
  have hij : 0 < i + j ∧ x (i + j) = c := hb hijFS
  have hi_lt_j : i < j := by
    have hterm : ∀ k : Nat, 1 ≤ (b.drop n).get k := by
      intro k
      have hkDrop : (b.drop n).get k ∈ Hindman.FS (b.drop n) :=
        Hindman.FS.singleton (b.drop n) k
      exact (hb (Hindman.FS_iter_tail_sub_FS b n hkDrop)).1
    have hsum : i + 1 ≤ j := by
      calc
        i + 1 = ∑ k ∈ s, 1 := by simp [s]
        _ ≤ ∑ k ∈ s, (b.drop n).get k :=
          Finset.sum_le_sum fun k _ ↦ hterm k
        _ = j := rfl
    omega
  exact ⟨i, j, hi.1, hi_lt_j, hi.2.trans hj.2.symm, hj.2.trans hij.2.symm⟩

/-- In any finite-valued split trace, some positive-index record contains the
square of its own value among its options.  The only game-specific input is
that every unequal split `i < j` contributes the product of the two child
values to the record at `i + j`. -/
theorem exists_square_option_of_finite_split_trace
    [Finite Q] (t : Nat → Transition Q)
    (hsplit : ∀ i j : Nat, 0 < i → i < j →
      (t i).value * (t j).value ∈ (t (i + j)).options) :
    ∃ n : Nat, 0 < n ∧ (t n).value ^ 2 ∈ (t n).options := by
  obtain ⟨i, j, hi, hij, hvij, hvsum⟩ :=
    exists_distinct_summand_monochromatic fun n ↦ (t n).value
  refine ⟨i + j, by omega, ?_⟩
  have hopt := hsplit i j hi hij
  rw [hvij, hvsum] at hopt
  simpa [pow_two] using hopt

/-- The `(n + 1)`-fold transition product.  Indexing positive powers from
zero avoids introducing a separate identity transition into closure proofs. -/
def positivePower (t : Transition Q) : Nat → Transition Q
  | 0 => t
  | n + 1 => product (positivePower t n) t

/-- The value field of the `(n + 1)`-fold transition product is the expected
monoid power. -/
theorem positivePower_value (c : Q) (E : Set Q) (n : Nat) :
    (positivePower (Transition.mk c E) n).value = c ^ (n + 1) := by
  induction n with
  | zero => simp [positivePower]
  | succ n ih =>
      simp [positivePower, product, ih, pow_succ]

/-- A closed table contains every positive transition power of each of its
records. -/
theorem positivePower_mem
    {T : Set (Transition Q)} (hclosed : Closed T)
    {t : Transition Q} (ht : t ∈ T) (n : Nat) :
    positivePower t n ∈ T := by
  induction n with
  | zero => exact ht
  | succ n ih => exact hclosed ih ht

/-- If `c ^ 2` is an option value of `c`, then the `(n + 1)`-fold transition
power has `c ^ (n + 2)` among its option values. -/
theorem next_power_mem_positivePower_options
    {c : Q} {E : Set Q} (hc2 : c ^ 2 ∈ E) (n : Nat) :
    c ^ (n + 2) ∈ (positivePower (Transition.mk c E) n).options := by
  induction n with
  | zero => simpa [positivePower] using hc2
  | succ n _ =>
      refine Or.inr ⟨c ^ 2, hc2, ?_⟩
      rw [positivePower_value]
      simp only [pow_add]

/-- **Consecutive-power obstruction.** In a nontrivial valid-table setting,
a record that contains the square of its value among its options forces every
two consecutive positive powers of that value to be distinct. -/
theorem consecutive_powers_ne
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hP : P.Nonempty) (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {c : Q} {E : Set Q} (ht : Transition.mk c E ∈ T)
    (hc2 : c ^ 2 ∈ E) (n : Nat) :
    c ^ (n + 1) ≠ c ^ (n + 2) := by
  intro heq
  have hpowT : positivePower (Transition.mk c E) n ∈ T :=
    positivePower_mem hclosed ht n
  have hnot :=
    value_not_mem_own_options hP hterminal hreduced hclosed hparity hranked hpowT
  apply hnot
  rw [positivePower_value, heq]
  exact next_power_mem_positivePower_options hc2 n

/-- A finite monoid element whose consecutive positive powers are all
distinct has an eventual power period of length at least two.  This is the
precise finite-semigroup content needed below; it avoids committing to any
particular library definition of an aperiodic monoid. -/
theorem finite_eventual_period_at_least_two
    [Finite Q] {c : Q}
    (hnext : ∀ n : Nat, c ^ (n + 1) ≠ c ^ (n + 2)) :
    ∃ m d : Nat, 1 ≤ m ∧ 2 ≤ d ∧
      ∀ k : Nat, c ^ (m + k) = c ^ (m + d + k) := by
  obtain ⟨i, j, hij, hpow⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : Nat ↦ c ^ (n + 1))
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hjne : j ≠ i + 1 := by
      intro hj
      subst j
      exact hnext i hpow
    refine ⟨i + 1, j - i, by omega, by omega, ?_⟩
    intro k
    calc
      c ^ (i + 1 + k) = c ^ (i + 1) * c ^ k := by rw [pow_add]
      _ = c ^ (j + 1) * c ^ k := by rw [hpow]
      _ = c ^ (j + 1 + k) := (pow_add c (j + 1) k).symm
      _ = c ^ (i + 1 + (j - i) + k) := by congr 1; omega
  · have hine : i ≠ j + 1 := by
      intro hi
      subst i
      exact hnext j hpow.symm
    refine ⟨j + 1, i - j, by omega, by omega, ?_⟩
    intro k
    calc
      c ^ (j + 1 + k) = c ^ (j + 1) * c ^ k := by rw [pow_add]
      _ = c ^ (i + 1) * c ^ k := by rw [hpow]
      _ = c ^ (i + 1 + k) := (pow_add c (i + 1) k).symm
      _ = c ^ (j + 1 + (i - j) + k) := by congr 1; omega

/-- In a finite valid-table setting, a value whose square is one of its own
option values generates an eventually periodic power sequence of period at
least two. -/
theorem square_option_forces_nontrivial_period
    [Finite Q]
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hP : P.Nonempty) (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {c : Q} {E : Set Q} (ht : Transition.mk c E ∈ T)
    (hc2 : c ^ 2 ∈ E) :
    ∃ m d : Nat, 1 ≤ m ∧ 2 ≤ d ∧
      ∀ k : Nat, c ^ (m + k) = c ^ (m + d + k) := by
  apply finite_eventual_period_at_least_two
  exact consecutive_powers_ne hP hterminal hreduced hclosed hparity hranked ht hc2

end Ogdoad.MisereGrundyObstruction
