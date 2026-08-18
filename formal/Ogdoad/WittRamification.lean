import Mathlib

/-!
# Finite triangular Artin--Schreier reduction in characteristic two

Let `k` be a perfect coefficient field of characteristic two.  A finite
principal part is represented by a finitely supported function `f : ℕ →₀ k`,
where `f n` is the coefficient of the pole of order `n`.  For `m > 0`, adding

```text
(c * pi^(-m))^2 + c * pi^(-m)
```

changes only pole orders `2*m` and `m`.  Choosing `c^2 = f (2*m)` therefore
kills an even pole and introduces data only at the strictly smaller order
`m`.  This is the triangular algebra behind ramified Artin--Schreier
normalization.

The file proves a bounded descending normalization algorithm.  Every positive
even coefficient through the chosen bound vanishes, coefficients above the
bound are unchanged, and the output at order `j` depends only on input
coefficients at orders at least `j`.  Thus a bounded principal part reduces to
odd poles by finitely many exact Artin--Schreier moves.

The square-root operation is supplied explicitly, together with its defining
identity.  Finite residue fields provide such an operation because they are
perfect, but no finite-field or local-field API is needed for the triangular
argument itself.

This file does not formalize substitution along a ramified extension, unit
power-series expansion, Witt residues, or the compatibility of the resulting
coordinates with restriction and Scharlau transfer.  Those remain inputs to a
positive, unbounded local coordinate law.  They cannot produce the literal
fixed finite query-independent arena originally proposed: the final section
proves abstractly that finitely many P/N observations cannot distinguish an
infinite family of source classes.  Applying that obstruction to Witt classes
still requires the external mathematical proof that the selected rank-two
family is infinite.
-/

namespace Ogdoad.WittRamification

/-- A finite principal part, indexed by pole order.  Index zero is retained so
that we can state explicitly that positive-pole Artin--Schreier normalization
does not change it.  In a ramified base change, any new constant contribution
comes from the unit power-series expansion before this reduction begins. -/
abbrev PrincipalPart (k : Type*) [Zero k] := ℕ →₀ k

section CharacteristicTwo

variable {k : Type*} [Field k]

/-- The elementary change in principal-part coefficients caused by adding
`(c*pi^(-m))^2 + c*pi^(-m)`. -/
noncomputable def elementaryAS (m : ℕ) (c : k) : PrincipalPart k :=
  Finsupp.single (2 * m) (c ^ 2) + Finsupp.single m c

@[simp]
theorem elementaryAS_apply_of_ne (m j : ℕ) (c : k)
    (hjm : j ≠ m) (hj2m : j ≠ 2 * m) :
    elementaryAS m c j = 0 := by
  simp [elementaryAS, hjm, hj2m]

/-- Cancel the coefficient at order `2*m` by one elementary
Artin--Schreier move. -/
noncomputable def cancelPole (root : k → k) (f : PrincipalPart k) (m : ℕ) :
    PrincipalPart k :=
  f + elementaryAS m (root (f (2 * m)))

/-- A cancellation is literally addition of an elementary
Artin--Schreier term; no quotient relation is hidden in the algorithm. -/
theorem cancelPole_eq_add_elementaryAS (root : k → k)
    (f : PrincipalPart k) (m : ℕ) :
    cancelPole root f m = f + elementaryAS m (root (f (2 * m))) :=
  rfl

/-- The chosen square root kills the even top pole.  The positivity hypothesis
keeps the newly introduced order `m` distinct from the killed order `2*m`. -/
@[simp]
theorem cancelPole_top_eq_zero (root : k → k)
    [CharP k 2]
    (hsq : ∀ a : k, root a ^ 2 = a)
    (f : PrincipalPart k) {m : ℕ} (hm : 0 < m) :
    cancelPole root f m (2 * m) = 0 := by
  have hmne : 2 * m ≠ m := by omega
  have hmn : m ≠ 2 * m := hmne.symm
  simp only [cancelPole, elementaryAS, Finsupp.add_apply,
    Finsupp.single_eq_same, Finsupp.single_apply, if_neg hmn,
    hsq, add_zero]
  exact CharTwo.add_self_eq_zero (f (2 * m) : k)

/-- One elementary cancellation is triangular: it changes nothing above its
top pole order. -/
theorem cancelPole_apply_of_lt (root : k → k)
    (f : PrincipalPart k) {m j : ℕ} (h : 2 * m < j) :
    cancelPole root f m j = f j := by
  have hj2m : j ≠ 2 * m := by omega
  have hjm : j ≠ m := by omega
  simp [cancelPole, elementaryAS, hj2m, hjm]

/-- Cancelling a positive pole does not change the constant coefficient. -/
theorem cancelPole_zero (root : k → k)
    (f : PrincipalPart k) {m : ℕ} (hm : 0 < m) :
    cancelPole root f m 0 = f 0 := by
  have h0m : 0 ≠ m := by omega
  have h02m : 0 ≠ 2 * m := by omega
  simp [cancelPole, elementaryAS, h0m, h02m]

/-- Perform the cancellation at order `n` when `n` is positive and even.
The witness is selected only from the arithmetic proposition, so the selected
half is independent of the coefficient vector. -/
noncomputable def reduceAt (root : k → k) (n : ℕ)
    (f : PrincipalPart k) : PrincipalPart k := by
  classical
  exact if h : ∃ m : ℕ, 0 < m ∧ n = 2 * m then
      cancelPole root f h.choose
    else
      f

/-- A positive even coefficient is zero after its reduction step. -/
theorem reduceAt_self_eq_zero (root : k → k)
    [CharP k 2]
    (hsq : ∀ a : k, root a ^ 2 = a)
    (f : PrincipalPart k) {n : ℕ}
    (h : ∃ m : ℕ, 0 < m ∧ n = 2 * m) :
    reduceAt root n f n = 0 := by
  rw [reduceAt, dif_pos h]
  calc
    cancelPole root f h.choose n =
        cancelPole root f h.choose (2 * h.choose) :=
      congrArg (cancelPole root f h.choose) h.choose_spec.2
    _ = 0 := cancelPole_top_eq_zero root hsq f
      (m := h.choose) h.choose_spec.1

/-- Reducing order `n` changes no coefficient of strictly larger order. -/
theorem reduceAt_apply_of_lt (root : k → k)
    (f : PrincipalPart k) {n j : ℕ} (hnj : n < j) :
    reduceAt root n f j = f j := by
  rw [reduceAt]
  split_ifs with h
  · apply cancelPole_apply_of_lt
    calc
      2 * h.choose = n := h.choose_spec.2.symm
      _ < j := hnj
  · rfl

/-- Agreement of two inputs from order `j` upward survives one reduction.
This is the single-step dependency statement used in the global triangularity
theorem below. -/
theorem reduceAt_congr_above (root : k → k)
    {f g : PrincipalPart k} {j n : ℕ}
    (hfg : ∀ q, j ≤ q → f q = g q) :
    ∀ q, j ≤ q → reduceAt root n f q = reduceAt root n g q := by
  intro q hjq
  rw [reduceAt, reduceAt]
  split_ifs with h
  · have hn : n = 2 * h.choose := h.choose_spec.2
    by_cases hnj : n < j
    · rw [cancelPole_apply_of_lt root f (hn ▸ lt_of_lt_of_le hnj hjq)]
      rw [cancelPole_apply_of_lt root g (hn ▸ lt_of_lt_of_le hnj hjq)]
      exact hfg q hjq
    · have hjn : j ≤ n := Nat.le_of_not_gt hnj
      have htop : f (2 * h.choose) = g (2 * h.choose) := by
        rw [← hn]
        exact hfg n hjn
      simp only [cancelPole, Finsupp.add_apply]
      rw [htop]
      rw [hfg q hjq]
  · exact hfg q hjq

/-- A single allowed Artin--Schreier move on principal parts. -/
def ASMove (f g : PrincipalPart k) : Prop :=
  ∃ (m : ℕ) (c : k), g = f + elementaryAS m c

/-- Reachability by finitely many elementary Artin--Schreier moves. -/
abbrev ASReachable (f g : PrincipalPart k) : Prop :=
  Relation.ReflTransGen ASMove f g

/-- Every `reduceAt` step is either the identity or one exact elementary
Artin--Schreier move. -/
theorem reduceAt_reachable (root : k → k) (n : ℕ)
    (f : PrincipalPart k) :
    ASReachable f (reduceAt root n f) := by
  rw [reduceAt]
  split_ifs with h
  · apply Relation.ReflTransGen.single
    exact ⟨h.choose, root (f (2 * h.choose)), rfl⟩
  · exact Relation.ReflTransGen.refl

/-- Positive-order reduction preserves the constant coefficient. -/
theorem reduceAt_zero (root : k → k) (n : ℕ)
    (f : PrincipalPart k) :
    reduceAt root n f 0 = f 0 := by
  rw [reduceAt]
  split_ifs with h
  · exact cancelPole_zero root f h.choose_spec.1
  · rfl

/-- Descending finite normalization.  At stage `N+1` it first cancels that
order, then recursively treats all lower orders. -/
noncomputable def normalizeUpTo (root : k → k) :
    ℕ → PrincipalPart k → PrincipalPart k
  | 0, f => f
  | N + 1, f => normalizeUpTo root N (reduceAt root (N + 1) f)

@[simp]
theorem normalizeUpTo_zero (root : k → k) (f : PrincipalPart k) :
    normalizeUpTo root 0 f = f :=
  rfl

@[simp]
theorem normalizeUpTo_succ (root : k → k)
    (N : ℕ) (f : PrincipalPart k) :
    normalizeUpTo root (N + 1) f =
      normalizeUpTo root N (reduceAt root (N + 1) f) :=
  rfl

/-- The bounded normalization changes no coefficient above its bound. -/
theorem normalizeUpTo_apply_of_lt (root : k → k)
    (f : PrincipalPart k) {N j : ℕ} (hNj : N < j) :
    normalizeUpTo root N f j = f j := by
  induction N generalizing f with
  | zero => rfl
  | succ N ih =>
      rw [normalizeUpTo_succ, ih]
      · exact reduceAt_apply_of_lt root f hNj
      · omega

/-- Descending positive-pole normalization never changes the constant
coefficient. -/
@[simp]
theorem normalizeUpTo_zero_apply (root : k → k)
    (f : PrincipalPart k) (N : ℕ) :
    normalizeUpTo root N f 0 = f 0 := by
  induction N generalizing f with
  | zero => rfl
  | succ N ih =>
      rw [normalizeUpTo_succ, ih, reduceAt_zero]

/-- Every positive even pole through the selected bound is eliminated. -/
theorem normalizeUpTo_even_eq_zero (root : k → k)
    [CharP k 2]
    (hsq : ∀ a : k, root a ^ 2 = a)
    (f : PrincipalPart k) {N n : ℕ}
    (hnpos : 0 < n) (hnN : n ≤ N) (hneven : Even n) :
    normalizeUpTo root N f n = 0 := by
  induction N generalizing f with
  | zero => omega
  | succ N ih =>
      rw [normalizeUpTo_succ]
      rcases lt_or_eq_of_le hnN with hnlt | rfl
      · exact ih (reduceAt root (N + 1) f) (by omega)
      · rw [normalizeUpTo_apply_of_lt root _ (by omega)]
        apply reduceAt_self_eq_zero root hsq
        rcases hneven with ⟨m, hm⟩
        refine ⟨m, ?_, ?_⟩
        · omega
        · omega

/-- Bounded inputs normalize completely to odd positive pole orders.  The
first conclusion preserves the bound; the second is the odd-pole normal-form
statement expressed without choosing a parity witness. -/
theorem normalizeUpTo_isOddNormalForm (root : k → k)
    [CharP k 2]
    (hsq : ∀ a : k, root a ^ 2 = a)
    (f : PrincipalPart k) (N : ℕ)
    (hbound : ∀ j, N < j → f j = 0) :
    (∀ j, N < j → normalizeUpTo root N f j = 0) ∧
      (∀ j, 0 < j → Even j → normalizeUpTo root N f j = 0) := by
  constructor
  · intro j hNj
    rw [normalizeUpTo_apply_of_lt root f hNj, hbound j hNj]
  · intro j hjpos hjeven
    by_cases hjN : j ≤ N
    · exact normalizeUpTo_even_eq_zero root hsq f hjpos hjN hjeven
    · have hNj : N < j := Nat.lt_of_not_ge hjN
      rw [normalizeUpTo_apply_of_lt root f hNj, hbound j hNj]

/-- The finite normalization is triangular: its output at order `j` depends
only on input coefficients at orders `q ≥ j`. -/
theorem normalizeUpTo_congr_above (root : k → k)
    {f g : PrincipalPart k} {j N : ℕ}
    (hfg : ∀ q, j ≤ q → f q = g q) :
    normalizeUpTo root N f j = normalizeUpTo root N g j := by
  induction N generalizing f g with
  | zero => exact hfg j le_rfl
  | succ N ih =>
      rw [normalizeUpTo_succ, normalizeUpTo_succ]
      apply ih
      exact reduceAt_congr_above root hfg

/-- The complete bounded normalization is connected to its input by a finite
chain of exact elementary Artin--Schreier moves. -/
theorem normalizeUpTo_reachable (root : k → k)
    (f : PrincipalPart k) (N : ℕ) :
    ASReachable f (normalizeUpTo root N f) := by
  induction N generalizing f with
  | zero => exact Relation.ReflTransGen.refl
  | succ N ih =>
      exact (reduceAt_reachable root (N + 1) f).trans
        (ih (reduceAt root (N + 1) f))

section PerfectCoefficientField

variable [CharP k 2] [PerfectField k]

/-- The canonical inverse-Frobenius square root in a perfect characteristic-two
field.  Finite residue fields acquire this operation automatically. -/
noncomputable def perfectSquareRoot (a : k) : k :=
  (powMulEquiv k 2).symm a

@[simp]
theorem perfectSquareRoot_sq (a : k) : perfectSquareRoot a ^ 2 = a :=
  powMulEquiv_symm_pow_p k 2 a

/-- Specializing the bounded normalizer to the canonical inverse Frobenius
requires no auxiliary choice once the perfect-field structure is present. -/
noncomputable def perfectNormalizeUpTo (N : ℕ)
    (f : PrincipalPart k) : PrincipalPart k :=
  normalizeUpTo perfectSquareRoot N f

theorem perfectNormalizeUpTo_isOddNormalForm
    (f : PrincipalPart k) (N : ℕ)
    (hbound : ∀ j, N < j → f j = 0) :
    (∀ j, N < j → perfectNormalizeUpTo N f j = 0) ∧
      (∀ j, 0 < j → Even j → perfectNormalizeUpTo N f j = 0) := by
  exact normalizeUpTo_isOddNormalForm perfectSquareRoot
    perfectSquareRoot_sq f N hbound

end PerfectCoefficientField

end CharacteristicTwo

section FixedFiniteLocalAccessObstruction

variable {Class Query : Type*}

/-- An infinite class family cannot be faithfully encoded by a fixed finite
vector of P/N outcomes.  `Query → Bool` is finite when the query type is
finite, irrespective of how the observations are computed. -/
theorem not_injective_finitePNOutcomeVector
    [Infinite Class] [Fintype Query]
    (observe : Class → Query → Bool) :
    ¬Function.Injective observe :=
  not_injective_infinite_finite observe

/-- Collision form of `not_injective_finitePNOutcomeVector`: two distinct
classes give exactly the same answer to every query in the fixed finite
family. -/
theorem exists_finitePNOutcomeVector_collision
    [Infinite Class] [Fintype Query]
    (observe : Class → Query → Bool) :
    ∃ x y : Class, x ≠ y ∧ ∀ q : Query, observe x q = observe y q := by
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp
    (not_injective_finitePNOutcomeVector observe)
  exact ⟨x, y, hne, fun q ↦ congrFun hxy q⟩

end FixedFiniteLocalAccessObstruction

end Ogdoad.WittRamification
