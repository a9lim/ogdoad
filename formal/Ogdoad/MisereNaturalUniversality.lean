import Ogdoad.MisereOctalCertificate

/-!
# Finite-exception natural realization of finite misere quotients

This module proves a universality theorem for a finite-exception heap class
that isolates one obstruction in the octal problem.  A heap has one of
finitely many source-local prefix states, followed by a unary
translation-invariant tail.  Each prefix heap moves only to an earlier-ranked
prefix heap; every tail heap has the one move to its predecessor.  Positions
are finite words of heaps, with a move in one component.

The class is not a superclass of finite octal games: it permits source-local
prefix moves but restricts the tail to one unary move.  The construction does
**not** claim finite-octal universality.  An octal digit applies its
subtraction or split to every larger heap, while the exceptional prefix moves
below are source-local.  The point of the theorem is to isolate the global
cross-talk created when one tries to encode those prefix moves by octal
digits.
-/

namespace Ogdoad.MisereNaturalUniversality

open Set
open Ogdoad.MisereTransition

variable {Q : Type*} [CommMonoid Q]

/-- A nontrivial valid table whose rank has `R 1 = 0` contains a one-move
record `(a,{1})`. -/
theorem exists_star_transition
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hR1 : R 1 = 0) (hne : ∃ x : Q, x ≠ 1) :
    ∃ a : Q, a ≠ 1 ∧ Transition.mk a ({1} : Set Q) ∈ T := by
  classical
  have hex : ∃ n : Nat, ∃ x : Q, x ≠ 1 ∧ R x = n := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨R x, x, hx, rfl⟩
  let n := Nat.find hex
  obtain ⟨a, ha1, haR⟩ := Nat.find_spec hex
  obtain ⟨E, haT, hdesc⟩ := hranked a
  have hEsub : E ⊆ ({1} : Set Q) := by
    intro e he
    by_contra he1
    have hleast : n ≤ R e := by
      apply Nat.find_min' hex
      exact ⟨e, he1, rfl⟩
    have hlt : R e < n := by
      change R e < Nat.find hex
      rw [← haR]
      exact hdesc e he
    omega
  have hEne : E.Nonempty := by
    by_contra hnone
    have hEempty : E = ∅ := not_nonempty_iff_eq_empty.mp hnone
    obtain ⟨F, h1T, h1desc⟩ := hranked (1 : Q)
    have hFempty : F = ∅ := by
      apply not_nonempty_iff_eq_empty.mp
      rintro ⟨f, hf⟩
      have hlt := h1desc f hf
      rw [hR1] at hlt
      omega
    have haval : a = 1 := value_eq_of_options_eq
      hreduced hclosed hparity hranked haT h1T (by simp [hEempty, hFempty])
    exact ha1 haval
  have hE : E = ({1} : Set Q) := by
    apply Subset.antisymm hEsub
    rintro x rfl
    obtain ⟨e, he⟩ := hEne
    have he1 : e = 1 := by simpa using hEsub he
    simpa [← he1] using he
  exact ⟨a, ha1, by simpa [hE] using haT⟩

/-- Powers of the star record are exactly the transition records of a unary
heap chain. -/
theorem unary_chain_transition
    {T : Set (Transition Q)} (hclosed : Closed T)
    {a : Q} (hstar : Transition.mk a ({1} : Set Q) ∈ T) :
    ∀ k : Nat, Transition.mk (a ^ (k + 1)) ({a ^ k} : Set Q) ∈ T := by
  intro k
  induction k with
  | zero => simpa using hstar
  | succ k ih =>
      have hp := hclosed ih hstar
      simpa [product, leftMul, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hp

/-- Prefix heaps carry quotient values; `tail k` is the `(k+1)`st heap after
an inert padding heap. -/
inductive Heap (Q : Type*) where
  | base (q : Q)
  | pad
  | tail (k : Nat)
  deriving DecidableEq

namespace Heap

variable (E : Q → Set Q) (a : Q)

def value : Heap Q → Q
  | .base q => q
  | .pad => 1
  | .tail k => a ^ (k + 1)

def options : Heap Q → Set (Heap Q)
  | .base q => (fun e => Heap.base e) '' E q
  | .pad => ∅
  | .tail 0 => {.pad}
  | .tail (k + 1) => {.tail k}

def rank (R : Q → Nat) : Heap Q → Nat
  | .base q => R q
  | .pad => 0
  | .tail k => k + 1

end Heap

abbrev Position (Q : Type*) := List (Heap Q)

namespace Position

variable (E : Q → Set Q) (a : Q)

def value : Position Q → Q
  | [] => 1
  | h :: t => Heap.value a h * value t

/-- Componentwise moves in a word of heaps. -/
def options : Position Q → Set (Position Q)
  | [] => ∅
  | h :: t =>
      (fun o => o :: t) '' Heap.options E h ∪
      (fun u => h :: u) '' options t

def optionValues (p : Position Q) : Set Q :=
  value a '' options E p

def transition (p : Position Q) : Transition Q :=
  Transition.mk (value a p) (optionValues E a p)

def rank (R : Q → Nat) : Position Q → Nat
  | [] => 0
  | h :: t => Heap.rank R h + rank R t

@[simp] theorem value_append (p c : Position Q) :
    value a (p ++ c) = value a p * value a c := by
  induction p with
  | nil => simp [value]
  | cons h p ih => simp [value, ih, mul_assoc]

end Position

section Records

variable {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
variable (E : Q → Set Q) (a : Q)

theorem heap_option_values
    (h : Heap Q) :
    Heap.value a '' Heap.options E h =
      match h with
      | .base q => E q
      | .pad => ∅
      | .tail 0 => ({1} : Set Q)
      | .tail (k + 1) => ({a ^ (k + 1)} : Set Q) := by
  cases h with
  | base q =>
      ext x
      simp [Heap.options, Heap.value]
  | pad => simp [Heap.options, Heap.value]
  | tail k =>
      cases k with
      | zero => simp [Heap.options, Heap.value]
      | succ k => simp [Heap.options, Heap.value]

theorem heap_transition_mem
    (hclosed : Closed T)
    (htable : ∀ q, Transition.mk q (E q) ∈ T)
    (hstar : Transition.mk a ({1} : Set Q) ∈ T)
    (hidentity : Transition.mk (1 : Q) ∅ ∈ T)
    (h : Heap Q) :
    Transition.mk (Heap.value a h)
      (Heap.value a '' Heap.options E h) ∈ T := by
  cases h with
  | base q =>
      rw [heap_option_values E a]
      simpa [Heap.value] using htable q
  | pad =>
      rw [heap_option_values E a]
      simpa [Heap.value] using hidentity
  | tail k =>
      cases k with
      | zero =>
          rw [heap_option_values E a]
          simpa [Heap.value] using unary_chain_transition hclosed hstar 0
      | succ k =>
          rw [heap_option_values E a]
          simpa [Heap.value] using unary_chain_transition hclosed hstar (k + 1)

theorem position_transition_cons (h : Heap Q) (t : Position Q) :
    Position.transition E a (h :: t) =
      product
        (Transition.mk (Heap.value a h)
          (Heap.value a '' Heap.options E h))
        (Position.transition E a t) := by
  rw [Transition.mk.injEq]
  constructor
  · simp [Position.transition, Position.value, product]
  · ext x
    simp only [Position.transition, Position.optionValues, Position.options,
      Position.value, product, leftMul, Set.mem_union, Set.mem_image]
    constructor
    · rintro ⟨u, hu | hu, rfl⟩
      · obtain ⟨o, ho, rfl⟩ := hu
        exact Or.inl ⟨Heap.value a o, ⟨o, ho, rfl⟩,
          by simp [Position.value, mul_comm]⟩
      · obtain ⟨v, hv, rfl⟩ := hu
        exact Or.inr ⟨Position.value a v, ⟨v, hv, rfl⟩, by simp [Position.value]⟩
    · rintro (hx | hx)
      · obtain ⟨y, ⟨o, ho, rfl⟩, rfl⟩ := hx
        exact ⟨o :: t, Or.inl ⟨o, ho, rfl⟩,
          by simp [Position.value, mul_comm]⟩
      · obtain ⟨y, ⟨v, hv, rfl⟩, rfl⟩ := hx
        exact ⟨h :: v, Or.inr ⟨v, hv, rfl⟩, by simp [Position.value]⟩

theorem position_transition_mem
    (hclosed : Closed T)
    (htable : ∀ q, Transition.mk q (E q) ∈ T)
    (hstar : Transition.mk a ({1} : Set Q) ∈ T)
    (hidentity : Transition.mk (1 : Q) ∅ ∈ T) :
    ∀ p : Position Q, Position.transition E a p ∈ T := by
  intro p
  induction p with
  | nil => simpa [Position.transition, Position.value, Position.optionValues,
      Position.options] using hidentity
  | cons h t ih =>
      rw [position_transition_cons E a]
      exact hclosed (heap_transition_mem E a hclosed htable hstar hidentity h) ih

end Records

section Termination

variable {R : Q → Nat}
variable (E : Q → Set Q)

omit [CommMonoid Q] in
theorem heap_option_rank_lt
    (hdesc : ∀ q e, e ∈ E q → R e < R q)
    {h o : Heap Q} (ho : o ∈ Heap.options E h) :
    Heap.rank R o < Heap.rank R h := by
  cases h with
  | base q =>
      obtain ⟨e, he, rfl⟩ := ho
      simpa [Heap.rank] using hdesc q e he
  | pad => simp [Heap.options] at ho
  | tail k =>
      cases k with
      | zero =>
          simp only [Heap.options, Set.mem_singleton_iff] at ho
          subst o
          simp [Heap.rank]
      | succ k =>
          simp only [Heap.options, Set.mem_singleton_iff] at ho
          subst o
          simp [Heap.rank]

omit [CommMonoid Q] in
theorem position_option_rank_lt
    (hdesc : ∀ q e, e ∈ E q → R e < R q)
    {p u : Position Q} (hu : u ∈ Position.options E p) :
    Position.rank R u < Position.rank R p := by
  induction p generalizing u with
  | nil => simp [Position.options] at hu
  | cons h t ih =>
      rcases hu with hu | hu
      · obtain ⟨o, ho, rfl⟩ := hu
        have hlt := heap_option_rank_lt E hdesc ho
        simp only [Position.rank]
        omega
      · obtain ⟨v, hv, rfl⟩ := hu
        have hlt := ih hv
        simp only [Position.rank]
        omega

end Termination

section Outcome

variable {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
variable (E : Q → Set Q) (a : Q)

/-- The algebraically predicted previous-player-win predicate. -/
def IsP (p : Position Q) : Prop := Position.value a p ∈ P

/-- Misere recursion for an arbitrary candidate outcome predicate. -/
def OutcomeRec (W : Position Q → Prop) : Prop :=
  ∀ p,
    W p ↔ (Position.options E p).Nonempty ∧
      ∀ u ∈ Position.options E p, ¬ W u

theorem isP_recursion
    (hparity : ParityTable P T)
    (htrans : ∀ p : Position Q, Position.transition E a p ∈ T)
    (p : Position Q) :
    IsP (P := P) a p ↔
      (Position.options E p).Nonempty ∧
      ∀ u ∈ Position.options E p, ¬ IsP (P := P) a u := by
  have hp := hparity (htrans p)
  change Position.value a p ∈ P ↔ _
  change Position.value a p ∈ P ↔
    (Position.optionValues E a p).Nonempty ∧
      ∀ y ∈ Position.optionValues E a p, y ∉ P at hp
  rw [hp]
  constructor
  · rintro ⟨⟨v, hv⟩, hsafe⟩
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨⟨u, hu⟩, ?_⟩
    intro w hw hPw
    exact hsafe (Position.value a w) ⟨w, hw, rfl⟩ hPw
  · rintro ⟨⟨u, hu⟩, hsafe⟩
    refine ⟨⟨Position.value a u, u, hu, rfl⟩, ?_⟩
    rintro v ⟨w, hw, rfl⟩ hPv
    exact hsafe w hw hPv

/-- On the acyclic finite-exception ruleset, the misere recursion has a unique
solution.  Hence `IsP` is the actual all-position outcome predicate, not merely
an algebraic labeling. -/
theorem outcome_unique
    (hdesc : ∀ q e, e ∈ E q → R e < R q)
    (hparity : ParityTable P T)
    (htrans : ∀ p : Position Q, Position.transition E a p ∈ T)
    {W : Position Q → Prop} (hW : OutcomeRec E W) :
    ∀ p, W p ↔ IsP (P := P) a p := by
  intro p
  induction hmeasure : Position.rank R p using Nat.strong_induction_on generalizing p with
  | h n ih =>
      rw [hW p, isP_recursion E a hparity htrans p]
      apply and_congr Iff.rfl
      constructor
      · intro hall u hu hPu
        have hlt := position_option_rank_lt E hdesc hu
        rw [hmeasure] at hlt
        exact (ih (Position.rank R u) hlt u rfl).not.mp (hall u hu) hPu
      · intro hall u hu hWu
        have hlt := position_option_rank_lt E hdesc hu
        rw [hmeasure] at hlt
        exact hall u hu ((ih (Position.rank R u) hlt u rfl).mp hWu)

/-- Indistinguishability in the generated universe, expressed by the proved
outcome predicate. -/
def Indist (p q : Position Q) : Prop :=
  ∀ c : Position Q,
    IsP (P := P) a (p ++ c) ↔ IsP (P := P) a (q ++ c)

theorem indist_iff_value_eq
    (hreduced : Reduced P) (p q : Position Q) :
    Indist (P := P) a p q ↔ Position.value a p = Position.value a q := by
  constructor
  · intro hind
    by_contra hne
    obtain ⟨z, hz⟩ := hreduced hne
    have hc := hind [.base z]
    simp only [IsP, Position.value_append, Position.value, Heap.value,
      mul_one] at hc
    exact hz.elim (λ h => h.2 (hc.mp h.1)) (λ h => h.1 (hc.mpr h.2))
  · intro heq c
    simp only [IsP, Position.value_append, heq]

end Outcome

section Universality

variable {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}

/-- **Finite-exception heap universality.** Every nontrivial reduced ranked
valid transition table supplies finitely many abstract ranked prefix heap
rules and a unary uniform tail.  Every position record remains in the table,
the induced outcome predicate is the unique misere-recursive outcome, every
quotient value is represented by a one-heap position, and
indistinguishability is exactly equality of quotient values.

When `Q` is finite, the prefix rule list is finite.  The paper-level transport
to a numerical one-species ruleset enumerates the base constructors by
increasing rank, inserts `pad`, and then enumerates the tail constructors.
That enumeration is not part of the Lean statement below. -/
theorem finite_exception_heap_normal_form
    [Finite Q]
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hR1 : R 1 = 0) (hne : ∃ x : Q, x ≠ 1) :
    ∃ (E : Q → Set Q) (a : Q),
      (∀ q, Transition.mk q (E q) ∈ T) ∧
      (∀ q e, e ∈ E q → R e < R q) ∧
      (∀ p : Position Q, Position.transition E a p ∈ T) ∧
      OutcomeRec E (IsP (P := P) a) ∧
      (∀ W : Position Q → Prop, OutcomeRec E W →
        ∀ p, W p ↔ IsP (P := P) a p) ∧
      (∀ p q : Position Q,
        Indist (P := P) a p q ↔ Position.value a p = Position.value a q) ∧
      (∀ q : Q, Position.value a [.base q] = q) := by
  classical
  obtain ⟨a, _, hstar⟩ :=
    exists_star_transition hreduced hclosed hparity hranked hR1 hne
  choose E htable hdesc using hranked
  have hE1 : E 1 = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨e, he⟩
    have hlt := hdesc 1 e he
    rw [hR1] at hlt
    omega
  have hidentity : Transition.mk (1 : Q) ∅ ∈ T := by
    simpa [hE1] using htable 1
  have htrans : ∀ p : Position Q, Position.transition E a p ∈ T :=
    position_transition_mem E a hclosed htable hstar hidentity
  refine ⟨E, a, htable, hdesc, htrans, ?_, ?_, ?_, ?_⟩
  · exact isP_recursion E a hparity htrans
  · intro W hW
    exact outcome_unique E a hdesc hparity htrans hW
  · exact indist_iff_value_eq a hreduced
  · intro q
    simp [Position.value, Heap.value]

end Universality

/-- A periodic heap trace cannot use a fixed active lag while insisting that
every such option strictly lowers the well-founded table rank.  Thus Siegel's
descending representatives cannot simply be repeated in an octal tail. -/
theorem no_periodic_strict_lag
    (r : Nat → Nat) {N p d : Nat} (hp : 1 ≤ p)
    (hperiod : ∀ n, N ≤ n → r (n + p) = r n)
    (hdesc : ∀ n, N ≤ n → r n < r (n + d)) : False := by
  have hperiod_iter : ∀ k : Nat, r (N + k * p) = r N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hk := hperiod (N + k * p) (by omega)
        rw [Nat.succ_mul, ← Nat.add_assoc]
        exact hk.trans ih
  have hstrict_iter : ∀ k : Nat, 1 ≤ k → r N < r (N + k * d) := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
        by_cases hk0 : k = 0
        · subst k
          simpa using hdesc N (by omega)
        · have hprev : r N < r (N + k * d) := ih (by omega)
          have hnext := hdesc (N + k * d) (by omega)
          rw [Nat.succ_mul, ← Nat.add_assoc]
          exact hprev.trans hnext
  have hlt := hstrict_iter p hp
  have heq := hperiod_iter d
  have harg : N + p * d = N + d * p := by simp [Nat.mul_comm]
  rw [harg, heq] at hlt
  exact Nat.lt_irrefl _ hlt

section OctalPadObstruction

open Ogdoad.MisereOctalCertificate

/-- A one-remainder digit at place `k` gives every later heap a legal option.
This is independent of the quotient labels assigned to the heaps. -/
theorem one_bit_forces_nonempty
    {A : Type*} (x : Nat → A) {one : Set Nat} {k N : Nat}
    (hk : k ∈ one) (hkn : k < N) :
    (oneRemainderOptions x one N).Nonempty := by
  exact ⟨x (N - k), k, hk, hkn, rfl⟩

/-- A split digit at place `k` gives every heap of size at least `k+2` a
legal split option. -/
theorem two_bit_forces_nonempty
    (x : Nat → Q) {two : Set Nat} {k N : Nat}
    (hk : k ∈ two) (hkn : k + 2 ≤ N) :
    (twoRemainderOptions x two N).Nonempty := by
  refine ⟨x 1 * x (N - k - 1), k, hk, hkn, ?_⟩
  exact ⟨1, N - k - 1, by omega, by omega, by omega, rfl⟩

/-- If a heap at least two places beyond the mask bound is terminal, then the
code has no persistent one-remainder or split bits.  Whole-heap bits do not
enter: they are source-local and inactive past their own digit. -/
theorem persistent_masks_empty_of_terminal_past_bound
    (x : Nat → Q) {whole one two : Set Nat} {d N : Nat}
    (hbounded : MasksBounded whole one two d)
    (hN : d + 2 ≤ N)
    (hterminal : octalOptions x whole one two N = ∅) :
    one = ∅ ∧ two = ∅ := by
  rcases hbounded with ⟨_, hone, htwo⟩
  constructor
  · apply not_nonempty_iff_eq_empty.mp
    rintro ⟨k, hk⟩
    have hkn : k < N := lt_of_le_of_lt (hone k hk) (by omega)
    obtain ⟨q, hq⟩ := one_bit_forces_nonempty x hk hkn
    have hqoctal : q ∈ octalOptions x whole one two N := by
      simp only [octalOptions, Set.mem_union]
      exact Or.inl (Or.inr hq)
    rw [hterminal] at hqoctal
    exact hqoctal
  · apply not_nonempty_iff_eq_empty.mp
    rintro ⟨k, hk⟩
    have hkn : k + 2 ≤ N := le_trans (Nat.add_le_add_right (htwo k hk) 2) hN
    obtain ⟨q, hq⟩ := two_bit_forces_nonempty x hk hkn
    have hqoctal : q ∈ octalOptions x whole one two N := by
      simp only [octalOptions, Set.mem_union]
      exact Or.inr hq
    rw [hterminal] at hqoctal
    exact hqoctal

/-- In a deterministic valid table with two distinct nonidentity values, a
chosen descending record must contain a nonidentity option.  Otherwise both
values would have the same singleton option set `{1}` and determinism would
identify them. -/
theorem exists_nonidentity_option_of_three_values
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hR1 : R 1 = 0)
    (E : Q → Set Q)
    (htable : ∀ q, Transition.mk q (E q) ∈ T)
    (hdesc : ∀ q e, e ∈ E q → R e < R q)
    (hthree : ∃ x y : Q, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y) :
    ∃ q e : Q, q ≠ 1 ∧ e ∈ E q ∧ e ≠ 1 := by
  classical
  have hE1 : E 1 = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨e, he⟩
    have hlt := hdesc 1 e he
    rw [hR1] at hlt
    omega
  by_contra hnone
  push Not at hnone
  obtain ⟨x, y, hx1, hy1, hxy⟩ := hthree
  have option_set_eq_singleton (q : Q) (hq1 : q ≠ 1) : E q = {1} := by
    have hnonempty : (E q).Nonempty := by
      by_contra hempty
      have hEq : E q = ∅ := not_nonempty_iff_eq_empty.mp hempty
      have hqeq : q = 1 := value_eq_of_options_eq
        hreduced hclosed hparity hranked (htable q) (htable 1)
        (by simp [hEq, hE1])
      exact hq1 hqeq
    apply Subset.antisymm
    · intro e he
      simpa using hnone q e hq1 he
    · rintro e rfl
      obtain ⟨z, hz⟩ := hnonempty
      have hz1 : z = 1 := hnone q z hq1 hz
      simpa [← hz1] using hz
  have hxeq : E x = {1} := option_set_eq_singleton x hx1
  have hyeq : E y = {1} := option_set_eq_singleton y hy1
  have : x = y := value_eq_of_options_eq
    hreduced hclosed hparity hranked (htable x) (htable y)
    (by rw [hxeq, hyeq])
  exact hxy this

/-- A nonidentity option of an earlier octal heap forces the later heap to be
nonterminal.  A whole-heap removal contributes only `1`; a one- or
two-remainder witness remains legal when the source heap is enlarged. -/
theorem nonidentity_option_persists_to_later_heap
    (x : Nat → Q) {whole one two : Set Nat} {n N : Nat} {e : Q}
    (he : e ∈ octalOptions x whole one two n) (he1 : e ≠ 1)
    (hnN : n < N) :
    (octalOptions x whole one two N).Nonempty := by
  simp only [octalOptions, Set.mem_union] at he
  rcases he with (hwhole | hone) | htwo
  · exact (he1 hwhole.1).elim
  · rcases hone with ⟨k, hk, hkn, _⟩
    obtain ⟨q, hq⟩ := one_bit_forces_nonempty x hk (lt_trans hkn hnN)
    refine ⟨q, ?_⟩
    simp only [octalOptions, Set.mem_union]
    exact Or.inl (Or.inr hq)
  · rcases htwo with ⟨k, hk, hkn, _⟩
    obtain ⟨q, hq⟩ := two_bit_forces_nonempty x hk
      (le_trans hkn (Nat.le_of_lt hnN))
    refine ⟨q, ?_⟩
    simp only [octalOptions, Set.mem_union]
    exact Or.inr hq

/-- **Actual-geometry pad obstruction.** If every chosen ranked record is
encoded exactly by a representative heap lying before an inert pad, then a
table with two distinct nonidentity values is impossible.  Unlike
`finite_exception_inert_pad_obstruction`, this uses the compiler's ordering of
all representatives before the pad and needs no bound on the octal masks. -/
theorem finite_exception_later_inert_pad_obstruction
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hR1 : R 1 = 0)
    (E : Q → Set Q)
    (htable : ∀ q, Transition.mk q (E q) ∈ T)
    (hdesc : ∀ q e, e ∈ E q → R e < R q)
    (hthree : ∃ x y : Q, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y)
    (x : Nat → Q) (representative : Q → Nat)
    {whole one two : Set Nat} {N : Nat}
    (hencode : ∀ q, octalOptions x whole one two (representative q) = E q)
    (hbefore : ∀ q, representative q < N)
    (hterminal : octalOptions x whole one two N = ∅) : False := by
  obtain ⟨q, e, _, he, he1⟩ := exists_nonidentity_option_of_three_values
    hreduced hclosed hparity hranked hR1 E htable hdesc hthree
  have heoctal : e ∈ octalOptions x whole one two (representative q) := by
    rw [hencode q]
    exact he
  obtain ⟨z, hz⟩ := nonidentity_option_persists_to_later_heap
    x heoctal he1 (hbefore q)
  rw [hterminal] at hz
  exact hz

/-- **Pad obstruction for the finite-exception compiler.** Suppose each
chosen ranked prefix option set is encoded exactly by an octal heap.  With two
distinct nonidentity values, one prefix record contains a nonidentity option.
Such an option cannot come from a whole-heap bit, so some persistent one- or
two-remainder bit is active.  It then contradicts a later inert pad beyond the
code support.

This rules out only a verbatim octal encoding of the normal-form compiler; it
does not rule out a different encoding with an active bridge. -/
theorem finite_exception_inert_pad_obstruction
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hR1 : R 1 = 0)
    (E : Q → Set Q)
    (htable : ∀ q, Transition.mk q (E q) ∈ T)
    (hdesc : ∀ q e, e ∈ E q → R e < R q)
    (hthree : ∃ x y : Q, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y)
    (x : Nat → Q) (representative : Q → Nat)
    {whole one two : Set Nat} {d N : Nat}
    (hencode : ∀ q, octalOptions x whole one two (representative q) = E q)
    (hbounded : MasksBounded whole one two d)
    (hN : d + 2 ≤ N)
    (hterminal : octalOptions x whole one two N = ∅) : False := by
  obtain ⟨q, e, hq1, he, he1⟩ := exists_nonidentity_option_of_three_values
    hreduced hclosed hparity hranked hR1 E htable hdesc hthree
  have heoctal : e ∈ octalOptions x whole one two (representative q) := by
    rw [hencode q]
    exact he
  have hpersistent : one.Nonempty ∨ two.Nonempty := by
    simp only [octalOptions, Set.mem_union] at heoctal
    rcases heoctal with (hwhole | hone) | htwo
    · exact (he1 hwhole.1).elim
    · rcases hone with ⟨k, hk, _⟩
      exact Or.inl ⟨k, hk⟩
    · rcases htwo with ⟨k, hk, _⟩
      exact Or.inr ⟨k, hk⟩
  have hempty := persistent_masks_empty_of_terminal_past_bound
    x hbounded hN hterminal
  rcases hpersistent with hone | htwo
  · rw [hempty.1] at hone
    rcases hone with ⟨k, hk⟩
    exact hk
  · rw [hempty.2] at htwo
    rcases htwo with ⟨k, hk⟩
    exact hk

end OctalPadObstruction

end Ogdoad.MisereNaturalUniversality
