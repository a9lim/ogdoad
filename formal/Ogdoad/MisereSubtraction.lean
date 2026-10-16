import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# Ferguson's shift theorem for subtraction games

This module constructs the normal Sprague--Grundy sequence of an arbitrary
finite positive subtraction set and proves Ferguson's zero/one shift theorem.
It also proves that every nonterminal zero-valued heap can move to a
one-valued heap, the extra local property used by the misere Bouton strategy.
No bound on the heap size and no finite census is used.
-/

namespace Ogdoad.MisereSubtraction

private theorem exists_not_mem (E : Finset Nat) : ∃ n, n ∉ E := by
  refine ⟨E.sup id + 1, ?_⟩
  intro h
  have := Finset.le_sup (f := id) h
  simp only [id_eq] at this
  omega

/-- The least natural number omitted by a finite set. -/
noncomputable def mex (E : Finset Nat) : Nat := Nat.find (exists_not_mem E)

theorem mex_not_mem (E : Finset Nat) : mex E ∉ E :=
  Nat.find_spec (exists_not_mem E)

theorem mem_of_lt_mex {E : Finset Nat} {k : Nat} (h : k < mex E) : k ∈ E := by
  by_contra hn
  have := Nat.find_min' (exists_not_mem E) hn
  change mex E ≤ k at this
  omega

theorem mex_le_card (E : Finset Nat) : mex E ≤ E.card := by
  have hsub : Finset.range (mex E) ⊆ E := by
    intro k hk
    exact mem_of_lt_mex (Finset.mem_range.mp hk)
  simpa using Finset.card_le_card hsub

/-- The actual normal-play sequence for a finite positive subtraction set. -/
noncomputable def grundy (S : Finset Nat) (hpos : ∀ s ∈ S, 0 < s) (n : Nat) : Nat :=
  mex (((S.filter (· ≤ n)).attach).image fun s => grundy S hpos (n - s.val))
termination_by n
decreasing_by
  have hs := (Finset.mem_filter.mp s.property)
  have := hpos s.val hs.1
  omega

/-- The two defining mex properties, stated without implementation details. -/
structure IsSG (S : Set Nat) (g : Nat → Nat) : Prop where
  avoids : ∀ n s, s ∈ S → s ≤ n → g (n - s) ≠ g n
  reaches : ∀ n k, k < g n → ∃ s ∈ S, s ≤ n ∧ g (n - s) = k

theorem grundy_isSG (S : Finset Nat) (hpos : ∀ s ∈ S, 0 < s) :
    IsSG (S : Set Nat) (grundy S hpos) := by
  constructor
  · intro n s hs hsn heq
    have hmem : grundy S hpos (n - s) ∈
        ((S.filter (· ≤ n)).attach.image fun t => grundy S hpos (n - t.val)) := by
      exact Finset.mem_image.mpr ⟨⟨s, Finset.mem_filter.mpr ⟨hs, hsn⟩⟩,
        Finset.mem_attach _ _, rfl⟩
    rw [heq] at hmem
    have heqn := grundy.eq_1 S hpos n
    rw [heqn] at hmem
    exact mex_not_mem _ hmem
  · intro n k hk
    rw [grundy] at hk
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (mem_of_lt_mex hk)
    have hs := Finset.mem_filter.mp t.property
    exact ⟨t.val, hs.1, hs.2, ht⟩

/-- The maximum normal heap value is bounded by the number of subtraction
offsets, independently of heap size. -/
theorem grundy_le_card (S : Finset Nat) (hpos : ∀ s ∈ S, 0 < s) (n : Nat) :
    grundy S hpos n ≤ S.card := by
  rw [grundy]
  exact (mex_le_card _).trans (Finset.card_image_le.trans (by
    simpa using Finset.card_filter_le S (· ≤ n)))

variable {S : Set Nat} {g : Nat → Nat}

theorem zero_of_no_move (hg : IsSG S g) {n : Nat}
    (hstop : ∀ s ∈ S, ¬s ≤ n) : g n = 0 := by
  by_contra hne
  obtain ⟨s, hs, hsn, _⟩ := hg.reaches n 0 (by omega)
  exact hstop s hs hsn

/-- Ferguson's theorem. Its hypotheses also permit infinite subtraction sets,
provided an SG sequence is supplied; positivity follows from the least move. -/
theorem ferguson_shift (hg : IsSG S g) {s : Nat} (hs : s ∈ S)
    (hspos : 0 < s) (hmin : ∀ t ∈ S, s ≤ t) (n : Nat) :
    g n = 0 ↔ g (n + s) = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    constructor
    · intro hn
      have hnotzero : g (n + s) ≠ 0 := by
        have h := hg.avoids (n + s) s hs (by omega)
        simpa [hn] using Ne.symm h
      by_contra hnotone
      obtain ⟨t, ht, htn, htone⟩ := hg.reaches (n + s) 1 (by omega)
      have hst := hmin t ht
      have hsmall : s ≤ n + s - t := by
        by_contra hsmall
        have hz : g (n + s - t) = 0 := zero_of_no_move hg (by
          intro u hu
          have := hmin u hu
          omega)
        omega
      have hbase : n + s - t - s < n := by omega
      have hz : g (n + s - t - s) = 0 :=
        (ih _ hbase).mpr (by simpa [Nat.sub_add_cancel hsmall] using htone)
      have heq : n + s - t - s = n - t := by omega
      rw [heq] at hz
      exact hg.avoids n t ht (by omega) (by omega)
    · intro hn
      by_contra hnotzero
      obtain ⟨t, ht, htn, htz⟩ := hg.reaches n 0 (by omega)
      have htpos : 0 < t := lt_of_lt_of_le hspos (hmin t ht)
      have htone := (ih (n - t) (by omega)).mp htz
      have heq : n - t + s = n + s - t := by omega
      rw [heq] at htone
      exact hg.avoids (n + s) t ht (by omega) (by omega)

/-- A nonterminal SG-zero heap always has an SG-one option. -/
theorem zero_has_one_option (hg : IsSG S g) {s n : Nat}
    (hs : s ∈ S) (hspos : 0 < s) (hmin : ∀ t ∈ S, s ≤ t)
    (hn : s ≤ n) (hzero : g n = 0) :
    ∃ t ∈ S, t ≤ n ∧ g (n - t) = 1 := by
  have hne : g (n - s) ≠ 0 := by
    simpa [hzero] using hg.avoids n s hs hn
  obtain ⟨t, ht, htn, htz⟩ := hg.reaches (n - s) 0 (by omega)
  have hone := (ferguson_shift hg hs hspos hmin (n - s - t)).mp htz
  have heq : n - s - t + s = n - t := by omega
  exact ⟨t, ht, by omega, by simpa [heq] using hone⟩

/-- One legal move in a list of heaps. Retaining zero-sized heaps is harmless. -/
inductive Move (S : Set Nat) : List Nat → List Nat → Prop
  | head {n s : Nat} {xs : List Nat} (hs : s ∈ S) (hle : s ≤ n) :
      Move S (n :: xs) ((n - s) :: xs)
  | tail {n : Nat} {xs ys : List Nat} (h : Move S xs ys) :
      Move S (n :: xs) (n :: ys)

/-- Normal xor of a position's individual SG values. -/
def nimSum (g : Nat → Nat) : List Nat → Nat
  | [] => 0
  | n :: xs => g n ^^^ nimSum g xs

/-- Count of components whose normal value exceeds one. -/
def bigCount (g : Nat → Nat) : List Nat → Nat
  | [] => 0
  | n :: xs => (if 2 ≤ g n then 1 else 0) + bigCount g xs

/-- Bouton's misere losing-position criterion. -/
def BoutonP (g : Nat → Nat) (xs : List Nat) : Prop :=
  if bigCount g xs = 0 then nimSum g xs = 1 else nimSum g xs = 0

private theorem xor_small {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ^^^ b ≤ 1 := by
  interval_cases a <;> interval_cases b <;> decide

theorem nimSum_small {xs : List Nat} (h : bigCount g xs = 0) : nimSum g xs ≤ 1 := by
  induction xs with
  | nil => simp [nimSum]
  | cons n xs ih =>
    simp only [bigCount] at h
    have hn : g n ≤ 1 := by split_ifs at h <;> omega
    have ht : bigCount g xs = 0 := by omega
    exact xor_small hn (ih ht)

theorem move_bigCount (h : Move S xs ys) : bigCount g xs ≤ bigCount g ys + 1 := by
  induction h with
  | head hs hle => simp only [bigCount]; split_ifs <;> omega
  | tail h ih => simp only [bigCount]; omega

/-- The ordinary Nim move lemma, using actual subtraction moves. -/
theorem move_to_smaller_nimSum (hg : IsSG S g) {xs : List Nat} {k : Nat}
    (hk : k < nimSum g xs) : ∃ ys, Move S xs ys ∧ nimSum g ys = k := by
  induction xs generalizing k with
  | nil => simp [nimSum] at hk
  | cons n xs ih =>
    rcases Nat.lt_xor_cases hk with hhead | htail
    · obtain ⟨s, hs, hle, hvalue⟩ := hg.reaches n (k ^^^ nimSum g xs) hhead
      refine ⟨(n - s) :: xs, Move.head hs hle, ?_⟩
      simp [nimSum, hvalue]
    · obtain ⟨ys, hm, hsum⟩ := ih htail
      refine ⟨n :: ys, Move.tail hm, ?_⟩
      simp only [nimSum, hsum]
      rw [Nat.xor_comm k, Nat.xor_xor_cancel_left]

/-- If exactly one large heap is present, it can be moved to any prescribed
small xor while eliminating the last large component. -/
theorem single_big_to_small (hg : IsSG S g) {xs : List Nat} {k : Nat}
    (hb : bigCount g xs = 1) (hk : k ≤ 1) :
    ∃ ys, Move S xs ys ∧ bigCount g ys = 0 ∧ nimSum g ys = k := by
  induction xs generalizing k with
  | nil => simp [bigCount] at hb
  | cons n xs ih =>
    by_cases hn : 2 ≤ g n
    · have ht : bigCount g xs = 0 := by simpa [bigCount, hn] using hb
      have hsum := nimSum_small ht
      have htarget : k ^^^ nimSum g xs < g n := by
        have := xor_small hk hsum
        omega
      obtain ⟨s, hs, hle, hvalue⟩ := hg.reaches n _ htarget
      refine ⟨(n - s) :: xs, Move.head hs hle, ?_, ?_⟩
      · have hsval := xor_small hk hsum
        simp [bigCount, hvalue, ht, show ¬2 ≤ k ^^^ nimSum g xs by omega]
      · simp [nimSum, hvalue]
    · have ht : bigCount g xs = 1 := by simpa [bigCount, hn] using hb
      have hsmall : g n ≤ 1 := by omega
      obtain ⟨ys, hm, hzero, hsum⟩ := ih ht (xor_small hk hsmall)
      refine ⟨n :: ys, Move.tail hm, by simp [bigCount, hn, hzero], ?_⟩
      simp only [nimSum, hsum]
      rw [Nat.xor_comm k, Nat.xor_xor_cancel_left]

private theorem nimSum_append (xs ys : List Nat) :
    nimSum g (xs ++ ys) = nimSum g xs ^^^ nimSum g ys := by
  induction xs with
  | nil => simp [nimSum]
  | cons n xs ih => simp [nimSum, ih, Nat.xor_assoc]

private theorem bigCount_append (xs ys : List Nat) :
    bigCount g (xs ++ ys) = bigCount g xs + bigCount g ys := by
  induction xs with
  | nil => simp [bigCount]
  | cons n xs ih => simp [bigCount, ih, Nat.add_assoc]

private theorem move_decompose (h : Move S xs ys) :
    ∃ pre post n t, t ∈ S ∧ t ≤ n ∧
      xs = pre ++ n :: post ∧ ys = pre ++ (n - t) :: post := by
  induction h with
  | head hs hle => exact ⟨[], _, _, _, hs, hle, rfl, rfl⟩
  | @tail n xs ys h ih =>
    obtain ⟨pre, post, m, t, ht, hle, rfl, rfl⟩ := ih
    exact ⟨n :: pre, post, m, t, ht, hle, rfl, rfl⟩

private theorem bouton_move_front (pre post : List Nat) (n : Nat) :
    BoutonP g (pre ++ n :: post) ↔ BoutonP g (n :: (pre ++ post)) := by
  simp [BoutonP, nimSum_append, bigCount_append, nimSum, bigCount,
    Nat.add_left_comm, Nat.xor_left_comm]

private theorem bouton_head_small (h : bigCount g xs = 0) (hp : BoutonP g (n :: xs)) :
    g n ≤ 1 := by
  have ht := nimSum_small h
  by_contra hn
  have hbig : 2 ≤ g n := by omega
  have hxor : g n ^^^ nimSum g xs = 0 := by
    simpa [BoutonP, bigCount, hbig, h, nimSum] using hp
  have hne : g n ≠ nimSum g xs := by omega
  exact (Nat.xor_ne_zero_iff.mpr hne) hxor

private theorem bouton_head_exclusion {n m : Nat} {xs : List Nat}
    (hne : g n ≠ g m) (hp : BoutonP g (n :: xs)) : ¬BoutonP g (m :: xs) := by
  intro hq
  by_cases ht : bigCount g xs = 0
  · have hn := bouton_head_small ht hp
    have hm := bouton_head_small ht hq
    have hs := nimSum_small ht
    have hnp : ¬2 ≤ g n := by omega
    have hmp : ¬2 ≤ g m := by omega
    have hp' : g n ^^^ nimSum g xs = 1 := by
      simpa [BoutonP, bigCount, hnp, ht, nimSum] using hp
    have hq' : g m ^^^ nimSum g xs = 1 := by
      simpa [BoutonP, bigCount, hmp, ht, nimSum] using hq
    apply hne
    have := congrArg (fun v => v ^^^ nimSum g xs) (hp'.trans hq'.symm)
    simpa using this
  · have hnp : bigCount g (n :: xs) ≠ 0 := by simp only [bigCount]; omega
    have hmp : bigCount g (m :: xs) ≠ 0 := by simp only [bigCount]; omega
    have hp' : g n ^^^ nimSum g xs = 0 := by simpa [BoutonP, hnp, nimSum] using hp
    have hq' : g m ^^^ nimSum g xs = 0 := by simpa [BoutonP, hmp, nimSum] using hq
    apply hne
    have := congrArg (fun v => v ^^^ nimSum g xs) (hp'.trans hq'.symm)
    simpa using this

/-- No predicted losing position moves to another predicted losing position. -/
theorem bouton_safe (hg : IsSG S g) {xs ys : List Nat}
    (hm : Move S xs ys) (hp : BoutonP g xs) : ¬BoutonP g ys := by
  obtain ⟨pre, post, n, t, ht, hle, rfl, rfl⟩ := move_decompose hm
  rw [bouton_move_front] at hp ⊢
  exact bouton_head_exclusion (Ne.symm (hg.avoids n t ht hle)) hp

private theorem small_flip (hg : IsSG S g) {s : Nat}
    (hs : s ∈ S) (hspos : 0 < s) (hmin : ∀ t ∈ S, s ≤ t)
    {xs ys : List Nat} (hm : Move S xs ys) (hb : bigCount g xs = 0) :
    ∃ zs, Move S xs zs ∧ bigCount g zs = 0 ∧ nimSum g zs = nimSum g xs ^^^ 1 := by
  induction hm with
  | @head n t xs ht hle =>
    have hn : g n ≤ 1 := by simp only [bigCount] at hb; split_ifs at hb <;> omega
    have htail : bigCount g xs = 0 := by simp only [bigCount] at hb; omega
    have hoption : ∃ u ∈ S, u ≤ n ∧ g (n - u) = (g n ^^^ 1) := by
      by_cases hz : g n = 0
      · simpa [hz] using zero_has_one_option hg hs hspos hmin
          (le_trans (hmin t ht) hle) hz
      · have ho : g n = 1 := by omega
        simpa [ho] using hg.reaches n 0 (by omega)
    obtain ⟨u, hu, hun, hvalue⟩ := hoption
    have hsmall := xor_small hn (show 1 ≤ 1 by omega)
    refine ⟨(n - u) :: xs, Move.head hu hun, ?_, ?_⟩
    · simp [bigCount, hvalue, htail, show ¬2 ≤ g n ^^^ 1 by omega]
    · simp [nimSum, hvalue, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
  | @tail n xs ys hm ih =>
    have hn : g n ≤ 1 := by simp only [bigCount] at hb; split_ifs at hb <;> omega
    have htail : bigCount g xs = 0 := by simp only [bigCount] at hb; omega
    obtain ⟨zs, hmz, hzero, hsum⟩ := ih htail
    refine ⟨n :: zs, Move.tail hmz, ?_, ?_⟩
    · simp [bigCount, hzero, show ¬2 ≤ g n by omega]
    · simp [nimSum, hsum, Nat.xor_assoc]

/-- Every nonterminal position outside Bouton's P-set has a move into it. -/
theorem bouton_winning_move (hg : IsSG S g) {s : Nat}
    (hs : s ∈ S) (hspos : 0 < s) (hmin : ∀ t ∈ S, s ≤ t)
    {xs : List Nat} (hmove : ∃ ys, Move S xs ys) (hp : ¬BoutonP g xs) :
    ∃ ys, Move S xs ys ∧ BoutonP g ys := by
  by_cases hb : bigCount g xs = 0
  · have hsmall := nimSum_small hb
    have hzero : nimSum g xs = 0 := by
      have : nimSum g xs ≠ 1 := by simpa [BoutonP, hb] using hp
      omega
    obtain ⟨ys, hm⟩ := hmove
    obtain ⟨zs, hmz, hzero', hsum⟩ := small_flip hg hs hspos hmin hm hb
    exact ⟨zs, hmz, by simp [BoutonP, hzero', hsum, hzero]⟩
  · by_cases hone : bigCount g xs = 1
    · obtain ⟨ys, hm, hzero, hsum⟩ := single_big_to_small hg hone (show 1 ≤ 1 by omega)
      exact ⟨ys, hm, by simp [BoutonP, hzero, hsum]⟩
    · have hxor : 0 < nimSum g xs := by
        have : nimSum g xs ≠ 0 := by simpa [BoutonP, hb] using hp
        omega
      obtain ⟨ys, hm, hsum⟩ := move_to_smaller_nimSum hg hxor
      have hremain : bigCount g ys ≠ 0 := by
        have := move_bigCount (g := g) hm
        omega
      exact ⟨ys, hm, by simp [BoutonP, hremain, hsum]⟩

theorem move_sum_lt (hpos : ∀ t ∈ S, 0 < t) (hm : Move S xs ys) : ys.sum < xs.sum := by
  induction hm with
  | head hs hle =>
    have := hpos _ hs
    simp only [List.sum_cons]
    omega
  | @tail n xs ys hm ih => simpa using Nat.add_lt_add_left ih n

/-- Literal misere recursion on actual positions: terminals are not P. -/
def misereP (S : Set Nat) (hpos : ∀ t ∈ S, 0 < t) (xs : List Nat) : Prop :=
  (∃ ys, Move S xs ys) ∧ ∀ ys, Move S xs ys → ¬misereP S hpos ys
termination_by xs.sum
decreasing_by exact move_sum_lt hpos (by assumption)

private theorem no_move_values (hg : IsSG S g) {xs : List Nat}
    (h : ¬∃ ys, Move S xs ys) : bigCount g xs = 0 ∧ nimSum g xs = 0 := by
  induction xs with
  | nil => simp [bigCount, nimSum]
  | cons n xs ih =>
    have hn : g n = 0 := zero_of_no_move hg (by
      intro t ht hle
      exact h ⟨(n - t) :: xs, Move.head ht hle⟩)
    have htail : ¬∃ ys, Move S xs ys := by
      rintro ⟨ys, hm⟩
      exact h ⟨n :: ys, Move.tail hm⟩
    obtain ⟨hb, hx⟩ := ih htail
    simp [bigCount, nimSum, hn, hb, hx]

theorem bouton_has_move (hg : IsSG S g) {xs : List Nat} (hp : BoutonP g xs) :
    ∃ ys, Move S xs ys := by
  by_contra hn
  obtain ⟨hb, hx⟩ := no_move_values hg hn
  simp [BoutonP, hb, hx] at hp

/-- Full all-heap, all-multiplicity Bouton outcome theorem for a subtraction
ruleset with a least positive move and its ordinary SG sequence. -/
theorem misereP_iff_bouton (hg : IsSG S g) {s : Nat}
    (hs : s ∈ S) (hspos : 0 < s) (hmin : ∀ t ∈ S, s ≤ t)
    (hpos : ∀ t ∈ S, 0 < t) (xs : List Nat) :
    misereP S hpos xs ↔ BoutonP g xs := by
  induction hsize : xs.sum using Nat.strong_induction_on generalizing xs with
  | h size ih =>
    constructor
    · intro hp
      rw [misereP] at hp
      by_contra hnot
      obtain ⟨ys, hm, hy⟩ := bouton_winning_move hg hs hspos hmin hp.1 hnot
      have hlt : ys.sum < size := by simpa [← hsize] using move_sum_lt hpos hm
      exact hp.2 ys hm ((ih _ hlt ys rfl).mpr hy)
    · intro hp
      rw [misereP]
      refine ⟨bouton_has_move hg hp, ?_⟩
      intro ys hm hy
      have hlt : ys.sum < size := by simpa [← hsize] using move_sum_lt hpos hm
      exact bouton_safe hg hm hp ((ih _ hlt ys rfl).mp hy)

/-- Concrete finite-subtraction specialization of the full outcome theorem. -/
theorem finite_subtraction_outcome (S : Finset Nat) (hpos : ∀ t ∈ S, 0 < t)
    {s : Nat} (hs : s ∈ S) (hmin : ∀ t ∈ S, s ≤ t) (xs : List Nat) :
    misereP (S : Set Nat) hpos xs ↔ BoutonP (grundy S hpos) xs :=
  misereP_iff_bouton (grundy_isSG S hpos) hs (hpos s hs) hmin hpos xs

end Ogdoad.MisereSubtraction
