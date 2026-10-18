import Ogdoad.MisereOctalCertificate

/-!
# Dilation of no-split octal rules

Multiplying every removal offset by `m` separates the heaps into residue
channels. The zero channel is the original game. Every positive residue
channel is ordinary subtraction by the original one-remainder mask.

The identities below concern the actual option sets, including the boundary
where subtraction leaves a positive inert residue heap. They do not assume
periodicity or a finite quotient.
-/

namespace Ogdoad.MisereOctalDilation

open Set
open Ogdoad.MisereTransition
open Ogdoad.MisereOctalCertificate

variable {Q : Type*} [CommMonoid Q]

/-- Multiply every active removal offset by the same positive integer. -/
def dilate (m : Nat) (S : Set Nat) : Set Nat := (fun k => m * k) '' S

/-- Original values on the zero channel and subtraction values elsewhere. -/
def interleave (m : Nat) (x y : Nat → Q) (n : Nat) : Q :=
  if n % m = 0 then x (n / m) else y (n / m)

/-- Unlike octal one-remainder moves, ordinary subtraction may reach zero. -/
def subtractionOptions (y : Nat → Q) (A : Set Nat) (n : Nat) : Set Q :=
  {q | ∃ k ∈ A, k ≤ n ∧ q = y (n - k)}

omit [CommMonoid Q] in
theorem interleave_zero (m : Nat) (hm : 0 < m) (x y : Nat → Q) (n : Nat) :
    interleave m x y (m * n) = x n := by
  simp [interleave, Nat.ne_of_gt hm]

omit [CommMonoid Q] in
theorem interleave_positive (m : Nat) (hm : 0 < m) (x y : Nat → Q)
    (n r : Nat) (hr : 0 < r) (hrm : r < m) :
    interleave m x y (m * n + r) = y n := by
  simp [interleave, Nat.add_mod, Nat.mul_add_div hm, Nat.div_eq_of_lt hrm,
    Nat.mod_eq_of_lt hrm, Nat.ne_of_gt hr]

private theorem sub_scaled (m n k r : Nat) (hk : k ≤ n) :
    m * n + r - m * k = m * (n - k) + r := by
  have hmul : m * k ≤ m * n := Nat.mul_le_mul_left m hk
  rw [Nat.mul_sub_left_distrib]
  omega

theorem zero_channel_options (m : Nat) (hm : 0 < m)
    (x y : Nat → Q) (C A : Set Nat) (n : Nat) :
    octalOptions (interleave m x y) (dilate m C) (dilate m A) ∅ (m * n) =
      octalOptions x C A ∅ n := by
  ext q
  simp only [octalOptions, wholeHeapOptions, oneRemainderOptions,
    twoRemainderOptions, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, false_and, exists_false, or_false]
  constructor
  · rintro (⟨rfl, k, hk, heq⟩ | ⟨_, ⟨k, hk, rfl⟩, hkn, rfl⟩)
    · have : k = n := Nat.eq_of_mul_eq_mul_left hm heq
      exact Or.inl ⟨rfl, by simpa [this] using hk⟩
    · have hkn' : k < n := (Nat.mul_lt_mul_left hm).mp hkn
      right
      refine ⟨k, hk, hkn', ?_⟩
      rw [← Nat.mul_sub_left_distrib, interleave_zero m hm]
  · rintro (⟨rfl, hn⟩ | ⟨k, hk, hkn, rfl⟩)
    · exact Or.inl ⟨rfl, n, hn, rfl⟩
    · right
      refine ⟨m * k, ⟨k, hk, rfl⟩, (Nat.mul_lt_mul_left hm).mpr hkn, ?_⟩
      rw [← Nat.mul_sub_left_distrib, interleave_zero m hm]

theorem positive_channel_options (m : Nat) (hm : 0 < m)
    (x y : Nat → Q) (C A : Set Nat) (n r : Nat)
    (hr : 0 < r) (hrm : r < m) :
    octalOptions (interleave m x y) (dilate m C) (dilate m A) ∅ (m * n + r) =
      subtractionOptions y A n := by
  ext q
  simp only [octalOptions, wholeHeapOptions, oneRemainderOptions,
    twoRemainderOptions, subtractionOptions, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, false_and, exists_false, or_false]
  constructor
  · rintro (⟨_, k, _, heq⟩ | ⟨_, ⟨k, hk, rfl⟩, hkn, rfl⟩)
    · have heq' := congrArg (fun v => v % m) heq
      simp [Nat.add_mod, Nat.mod_eq_of_lt hrm] at heq'
      omega
    · have hkn' : k ≤ n := by
        change m * k < m * n + r at hkn
        by_contra h
        have hmul := Nat.mul_le_mul_left m (show n + 1 ≤ k by omega)
        simp only [Nat.mul_add, Nat.mul_one] at hmul
        omega
      refine ⟨k, hk, hkn', ?_⟩
      rw [sub_scaled m n k r hkn', interleave_positive m hm x y _ r hr hrm]
  · rintro ⟨k, hk, hkn, rfl⟩
    right
    have hmul := Nat.mul_le_mul_left m hkn
    refine ⟨m * k, ⟨k, hk, rfl⟩, by omega, ?_⟩
    rw [sub_scaled m n k r hkn, interleave_positive m hm x y _ r hr hrm]

/-- Exact trace composition: a common table accepting the original game and
the associated subtraction game accepts every heap of the dilated code. -/
theorem dilated_records_mem (m : Nat) (hm : 0 < m)
    (x y : Nat → Q) (C A : Set Nat) (T : Set (Transition Q))
    (hx : ∀ n, Transition.mk (x n) (octalOptions x C A ∅ n) ∈ T)
    (hy : ∀ n, Transition.mk (y n) (subtractionOptions y A n) ∈ T) :
    ∀ n, Transition.mk (interleave m x y n)
      (octalOptions (interleave m x y) (dilate m C) (dilate m A) ∅ n) ∈ T := by
  intro n
  have heq : n = m * (n / m) + n % m := (Nat.div_add_mod n m).symm
  rw [heq]
  by_cases hr : n % m = 0
  · simp only [hr, Nat.add_zero]
    rw [interleave_zero m hm, zero_channel_options m hm]
    exact hx (n / m)
  · have hrpos : 0 < n % m := by omega
    have hrm := Nat.mod_lt n hm
    rw [interleave_positive m hm x y _ _ hrpos hrm,
      positive_channel_options m hm x y C A _ _ hrpos hrm]
    exact hy (n / m)

end Ogdoad.MisereOctalDilation
