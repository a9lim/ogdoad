import Ogdoad.MisereNaturalUniversality

/-!
# Odd-removal and two-element octal traces

The arbitrary-decoder hardness construction uses `0.7`. Validity is decisive
for that very code: every nontrivial valid table has a total `0.7` trace.
More generally, a code that removes only odd numbers of counters, always
allows removal of one counter without splitting, and allows taking the
one-counter heap, has the universal star-parity trace.
-/

namespace Ogdoad.MisereParityTrace

open Set
open Ogdoad.MisereTransition
open Ogdoad.MisereNaturalUniversality
open Ogdoad.MisereOctalCertificate

variable {Q : Type*} [CommMonoid Q]

/-- In every reduced valid transition table, the value of the one-move game
is an involution. The proof uses induction on the ranks of separating
contexts, not a bounded census or a game-theoretic cancellation axiom. -/
theorem star_square_eq_one
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {a : Q} (hstar : Transition.mk a ({1} : Set Q) ∈ T) :
    a ^ 2 = 1 := by
  classical
  have h1P : (1 : Q) ∉ P := by
    intro h
    have := (hparity hterminal).mp h
    simpa using this.1
  have haP : a ∈ P := by
    apply (hparity hstar).mpr
    exact ⟨⟨1, by simp⟩, by simpa using h1P⟩
  have ha2 : Transition.mk (a ^ 2) ({a} : Set Q) ∈ T := by
    simpa using unary_chain_transition hclosed hstar 1
  have ha2notP : a ^ 2 ∉ P := by
    intro h
    exact (hparity ha2).mp h |>.2 a (by simp) haP
  have hcontext : ∀ z : Q, a ^ 2 * z ∈ P ↔ z ∈ P := by
    intro z
    induction z using (measure R).wf.induction with
    | h z ih =>
      obtain ⟨F, hzT, hdesc⟩ := hranked z
      have hazT := hclosed hstar hzT
      have haazT := hclosed ha2 hzT
      by_cases hF : F.Nonempty
      · constructor
        · intro haazP
          apply (hparity hzT).mpr
          refine ⟨hF, ?_⟩
          intro f hf hfP
          have haafP := (ih f (hdesc f hf)).mpr hfP
          exact (hparity haazT).mp haazP |>.2 (a ^ 2 * f)
            (Or.inr ⟨f, hf, rfl⟩) haafP
        · intro hzP
          have haznotP : a * z ∉ P := by
            intro hazP
            apply (hparity hazT).mp hazP |>.2 z
            · exact Or.inl ⟨1, by simp, by simp⟩
            · exact hzP
          apply (hparity haazT).mpr
          refine ⟨⟨z * a, Or.inl ⟨a, by simp, rfl⟩⟩, ?_⟩
          intro q hq hqP
          rcases hq with ⟨b, hb, rfl⟩ | ⟨f, hf, rfl⟩
          · have hb : b = a := by simpa using hb
            subst b
            exact haznotP (by simpa [mul_comm] using hqP)
          · exact (hparity hzT).mp hzP |>.2 f hf ((ih f (hdesc f hf)).mp hqP)
      · have hFempty : F = ∅ := not_nonempty_iff_eq_empty.mp hF
        have hz1 : z = 1 := value_eq_of_options_eq hreduced hclosed hparity hranked
          hzT hterminal (by simpa using hFempty)
        simp [hz1, h1P, ha2notP]
  by_contra hne
  obtain ⟨z, hz⟩ := hreduced hne
  rcases hz with hz | hz
  · exact hz.2 (by simpa using (hcontext z).mp hz.1)
  · exact hz.1 ((hcontext z).mpr (by simpa using hz.2))

/-- Multiplication by the star value has no fixed point in any nontrivial
valid quotient. Together with `star_square_eq_one`, it pairs the whole
quotient, and every star-invariant subset, into two-element orbits. -/
theorem star_mul_ne_self
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {a : Q} (hstar : Transition.mk a ({1} : Set Q) ∈ T) (q : Q) :
    a * q ≠ q := by
  have h1P : (1 : Q) ∉ P := by
    intro h
    have := (hparity hterminal).mp h
    simpa using this.1
  have haP : a ∈ P := by
    apply (hparity hstar).mpr
    exact ⟨⟨1, by simp⟩, by simpa using h1P⟩
  obtain ⟨F, hqT, _⟩ := hranked q
  have hprod := hclosed hstar hqT
  have hnot := value_not_mem_own_options ⟨a, haP⟩ hterminal
    hreduced hclosed hparity hranked hprod
  intro heq
  apply hnot
  change a * q ∈ (product (Transition.mk a {1}) (Transition.mk q F)).options
  rw [heq]
  exact Or.inl ⟨1, by simp, by simp⟩

/-- All records of the code `0.7` are unary power records. This identity
needs no involution hypothesis: each move reduces the total exponent by one. -/
theorem zero_seven_options (a : Q) (n : Nat) :
    octalOptions (fun k ↦ a ^ k) {1} {1} {1} (n + 1) = {a ^ n} := by
  ext q
  constructor
  · rintro ((hwhole | hone) | htwo)
    · rcases hwhole with ⟨rfl, hn⟩
      have hn : n = 0 := by simpa using hn
      simp [hn]
    · rcases hone with ⟨k, hk, hkn, rfl⟩
      have hk : k = 1 := by simpa using hk
      simp [hk]
    · rcases htwo with ⟨k, hk, _, i, j, _, _, hij, rfl⟩
      have hk : k = 1 := by simpa using hk
      have hij : i + j = n := by simpa [hk] using hij
      simp [← pow_add, hij]
  · intro hq
    have hq : q = a ^ n := by simpa using hq
    subst q
    by_cases hn : n = 0
    · subst n
      exact Or.inl (Or.inl ⟨by simp, by simp⟩)
    · exact Or.inl (Or.inr ⟨1, by simp, by omega, by simp⟩)

/-- The same `0.7` code whose totality is undecidable for arbitrary decoders
is automatically total for every nontrivial valid transition table. -/
theorem zero_seven_total
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hR1 : R 1 = 0) (hne : ∃ x : Q, x ≠ 1) :
    ∃ a : Q, a ≠ 1 ∧ ∀ n : Nat,
      Transition.mk (a ^ (n + 1))
        (octalOptions (fun k ↦ a ^ k) {1} {1} {1} (n + 1)) ∈ T := by
  obtain ⟨a, ha1, haT⟩ := exists_star_transition
    hreduced hclosed hparity hranked hR1 hne
  refine ⟨a, ha1, ?_⟩
  intro n
  rw [zero_seven_options]
  exact unary_chain_transition hclosed haT n

/-- For odd-removal codes that can always remove a single counter, every
option has the preceding star power. The split terms are handled exactly by
multiplicativity; their unbounded number introduces no additional states. -/
theorem odd_removal_options
    {a : Q} (ha2 : a ^ 2 = 1)
    {whole one two : Set Nat}
    (hwhole : ∀ k ∈ whole, k % 2 = 1)
    (hone : ∀ k ∈ one, k % 2 = 1)
    (htwo : ∀ k ∈ two, k % 2 = 1)
    (hwhole1 : 1 ∈ whole) (hone1 : 1 ∈ one) (n : Nat) :
    octalOptions (fun k ↦ a ^ k) whole one two (n + 1) = {a ^ n} := by
  have hpow : ∀ i j : Nat, i % 2 = j % 2 → a ^ i = a ^ j := by
    intro i j hij
    rw [pow_eq_pow_mod i ha2, pow_eq_pow_mod j ha2, hij]
  ext q
  constructor
  · rintro ((hwholeOpt | honeOpt) | htwoOpt)
    · rcases hwholeOpt with ⟨rfl, hn⟩
      have hnodd := hwhole (n + 1) hn
      have hnzero : n % 2 = 0 := by omega
      have hnPow : a ^ n = 1 := by simpa using hpow n 0 hnzero
      simpa using hnPow.symm
    · rcases honeOpt with ⟨k, hk, hkn, rfl⟩
      have hkodd := hone k hk
      have hmod : (n + 1 - k) % 2 = n % 2 := by omega
      simpa using hpow (n + 1 - k) n hmod
    · rcases htwoOpt with ⟨k, hk, hkn, i, j, _, _, hij, rfl⟩
      have hkodd := htwo k hk
      have hmod : (i + j) % 2 = n % 2 := by omega
      simpa [pow_add] using hpow (i + j) n hmod
  · intro hq
    have hq : q = a ^ n := by simpa using hq
    subst q
    by_cases hn : n = 0
    · subst n
      exact Or.inl (Or.inl ⟨by simp, hwhole1⟩)
    · exact Or.inl (Or.inr ⟨1, hone1, by omega, by simp⟩)

/-- **Uniform valid-table totality.** Every odd-removal octal ruleset with
both basic one-counter moves has a total trace in every nontrivial valid
table. No bound on the code length or eventual periodicity search is needed. -/
theorem odd_removal_total
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hR1 : R 1 = 0) (hne : ∃ x : Q, x ≠ 1)
    {whole one two : Set Nat}
    (hwhole : ∀ k ∈ whole, k % 2 = 1)
    (hone : ∀ k ∈ one, k % 2 = 1)
    (htwo : ∀ k ∈ two, k % 2 = 1)
    (hwhole1 : 1 ∈ whole) (hone1 : 1 ∈ one) :
    ∃ a : Q, a ≠ 1 ∧ a ^ 2 = 1 ∧ ∀ n : Nat,
      Transition.mk (a ^ (n + 1))
        (octalOptions (fun k ↦ a ^ k) whole one two (n + 1)) ∈ T := by
  obtain ⟨a, ha1, haT⟩ := exists_star_transition
    hreduced hclosed hparity hranked hR1 hne
  obtain ⟨F, h1T, hdesc⟩ := hranked (1 : Q)
  have hFempty : F = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨f, hf⟩
    have hlt := hdesc f hf
    rw [hR1] at hlt
    omega
  have hterminal : Transition.mk 1 ∅ ∈ T := by simpa [hFempty] using h1T
  have ha2 := star_square_eq_one hterminal hreduced hclosed hparity hranked haT
  refine ⟨a, ha1, ha2, ?_⟩
  intro n
  rw [odd_removal_options ha2 hwhole hone htwo hwhole1 hone1]
  exact unary_chain_transition hclosed haT n

/-- An octal option record only depends on earlier values. One-remainder
moves require a positive removal; each positive two-heap remainder is smaller
than the source even when its removal offset is zero. -/
theorem octalOptions_eq_of_prefix_eq
    {x y : Nat → Q} {whole one two : Set Nat} {n : Nat}
    (hone : ∀ k ∈ one, 0 < k)
    (hxy : ∀ i < n, x i = y i) :
    octalOptions x whole one two n = octalOptions y whole one two n := by
  have hsub : ∀ (u v : Nat → Q), (∀ i < n, u i = v i) →
      octalOptions u whole one two n ⊆ octalOptions v whole one two n := by
    intro u v huv q hq
    rcases hq with (hwhole | honeOpt) | htwoOpt
    · exact Or.inl (Or.inl hwhole)
    · rcases honeOpt with ⟨k, hk, hkn, rfl⟩
      refine Or.inl (Or.inr ⟨k, hk, hkn, ?_⟩)
      exact huv (n - k) (by have := hone k hk; omega)
    · rcases htwoOpt with ⟨k, hk, hkn, i, j, hi, hj, hij, rfl⟩
      refine Or.inr ⟨k, hk, hkn, i, j, hi, hj, hij, ?_⟩
      rw [huv i (by omega), huv j (by omega)]
  exact Subset.antisymm (hsub x y hxy) (hsub y x (fun i hi ↦ (hxy i hi).symm))

/-- Any two total traces in the same valid table agree, without a periodicity
or finiteness assumption. -/
theorem total_trace_unique
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {whole one two : Set Nat} (hone : ∀ k ∈ one, 0 < k)
    {x y : Nat → Q} (hzero : x 0 = y 0)
    (hx : ∀ n, Transition.mk (x (n + 1)) (octalOptions x whole one two (n + 1)) ∈ T)
    (hy : ∀ n, Transition.mk (y (n + 1)) (octalOptions y whole one two (n + 1)) ∈ T) :
    x = y := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact hzero
    | succ n =>
      apply value_eq_of_options_eq hreduced hclosed hparity hranked (hx n) (hy n)
      exact octalOptions_eq_of_prefix_eq hone ih

/-- Every total trace for the odd-removal family is periodic from its
initial coefficient, with period two. This is an exact algebraic statement,
not an eventual-period certificate inferred from a finite prefix. -/
theorem odd_removal_trace_period_two
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hR1 : R 1 = 0) (hne : ∃ x : Q, x ≠ 1)
    {whole one two : Set Nat}
    (hwhole : ∀ k ∈ whole, k % 2 = 1)
    (hone : ∀ k ∈ one, k % 2 = 1)
    (htwo : ∀ k ∈ two, k % 2 = 1)
    (hwhole1 : 1 ∈ whole) (hone1 : 1 ∈ one)
    {x : Nat → Q} (hx0 : x 0 = 1)
    (hx : ∀ n, Transition.mk (x (n + 1)) (octalOptions x whole one two (n + 1)) ∈ T) :
    ∀ n, x (n + 2) = x n := by
  obtain ⟨a, _, ha2, haT⟩ := odd_removal_total
    hreduced hclosed hparity hranked hR1 hne hwhole hone htwo hwhole1 hone1
  have honepos : ∀ k ∈ one, 0 < k := by
    intro k hk
    have := hone k hk
    omega
  have hxeq : x = (fun n ↦ a ^ n) := total_trace_unique
    hreduced hclosed hparity hranked honepos (by simpa using hx0) hx haT
  intro n
  simp [hxeq, pow_add, ha2]

/-- A star-power trace has only the two values `1` and `a`, so it cannot
surject onto a larger quotient. -/
theorem star_power_two_values {a : Q} (ha2 : a ^ 2 = 1) (n : Nat) :
    a ^ n = 1 ∨ a ^ n = a := by
  rw [pow_eq_pow_mod n ha2]
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hmod with hmod | hmod <;> simp [hmod]

/-- A valid-table `0.7` trace exists exactly when the target monoid is
nontrivial. This solves totality completely for the fixed code used by the
arbitrary-decoder hardness reduction. -/
theorem zero_seven_total_iff_nontrivial
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hR1 : R 1 = 0) :
    (∃ x : Nat → Q, x 0 = 1 ∧ ∀ n : Nat,
      Transition.mk (x (n + 1)) (octalOptions x {1} {1} {1} (n + 1)) ∈ T) ↔
      ∃ a : Q, a ≠ 1 := by
  constructor
  · rintro ⟨x, _, hx⟩
    obtain ⟨F, h1T, hdesc⟩ := hranked (1 : Q)
    have hFempty : F = ∅ := by
      apply not_nonempty_iff_eq_empty.mp
      rintro ⟨f, hf⟩
      have hlt := hdesc f hf
      rw [hR1] at hlt
      omega
    have h1P : (1 : Q) ∉ P := by
      intro h1
      obtain ⟨f, hf⟩ := (hparity h1T).mp h1 |>.1
      simp [hFempty] at hf
    have hoptions : octalOptions x {1} {1} {1} 1 = ({1} : Set Q) := by
      ext q
      simp [octalOptions, wholeHeapOptions, oneRemainderOptions, twoRemainderOptions]
    have hstar : Transition.mk (x 1) ({1} : Set Q) ∈ T := by
      simpa [hoptions] using hx 0
    have hxP : x 1 ∈ P := by
      apply (hparity hstar).mpr
      exact ⟨⟨1, by simp⟩, by simpa using h1P⟩
    exact ⟨x 1, fun heq ↦ h1P (heq ▸ hxP)⟩
  · intro hne
    obtain ⟨a, _, ha⟩ := zero_seven_total hreduced hclosed hparity hranked hR1 hne
    exact ⟨fun n ↦ a ^ n, by simp, ha⟩

/-- In a two-element valid quotient, every option record is a subsingleton:
loop-freeness leaves at most the one value different from its source. -/
theorem binary_options_subsingleton
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hP : P.Nonempty) (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {a : Q} (hbinary : ∀ q : Q, q = 1 ∨ q = a)
    {t : Transition Q} (ht : t ∈ T) : t.options.Subsingleton := by
  have hnot := value_not_mem_own_options hP hterminal
    hreduced hclosed hparity hranked ht
  intro e he f hf
  rcases hbinary t.value with hv | hv
  · have hea : e = a := by
      rcases hbinary e with he1 | hea
      · exact False.elim (hnot (by simpa [hv, he1] using he))
      · exact hea
    have hfa : f = a := by
      rcases hbinary f with hf1 | hfa
      · exact False.elim (hnot (by simpa [hv, hf1] using hf))
      · exact hfa
    exact hea.trans hfa.symm
  · have he1 : e = 1 := by
      rcases hbinary e with he1 | hea
      · exact he1
      · exact False.elim (hnot (by simpa [hv, hea] using he))
    have hf1 : f = 1 := by
      rcases hbinary f with hf1 | hfa
      · exact hf1
      · exact False.elim (hnot (by simpa [hv, hfa] using hf))
    exact he1.trans hf1.symm

/-- A single unrestricted split offset forces any involution-valued trace
with monochromatic option records to have period two on positive indices.
Comparing `(1,3)` with `(2,2)` first gives `x 3 = x 1`; comparison of
`(1,n+2)` with `(3,n)` then propagates the identity to every positive `n`. -/
theorem period_two_of_singleton_split_records
    (t : Nat → Transition Q) (k : Nat)
    (hoptions : ∀ n, 0 < n → (t n).options.Subsingleton)
    (hsquare : ∀ n, 0 < n → (t n).value * (t n).value = 1)
    (hsplit : ∀ i j : Nat, 0 < i → 0 < j →
      (t i).value * (t j).value ∈ (t (k + (i + j))).options) :
    ∀ n : Nat, 0 < n → (t (n + 2)).value = (t n).value := by
  have h13 : (t 1).value * (t 3).value = 1 := by
    have h := hoptions (k + 4) (by omega)
      (hsplit 1 3 (by omega) (by omega)) (hsplit 2 2 (by omega) (by omega))
    simpa [hsquare 2 (by omega)] using h
  have h31 : (t 3).value = (t 1).value := by
    have h := congrArg (fun q ↦ (t 1).value * q) h13
    simpa [← mul_assoc, hsquare 1 (by omega)] using h
  intro n hn
  have hsplitLeft := hsplit 1 (n + 2) (by omega) (by omega)
  have hsplitRight := hsplit 3 n (by omega) hn
  have hsum : k + (3 + n) = k + (1 + (n + 2)) := by omega
  rw [hsum] at hsplitRight
  have h := hoptions (k + (1 + (n + 2))) (by omega) hsplitLeft hsplitRight
  rw [h31] at h
  have hcancel := congrArg (fun q ↦ (t 1).value * q) h
  simpa [← mul_assoc, hsquare 1 (by omega)] using hcancel

/-- Equal splits are not essential to binary rigidity. With unequal splits
only, comparisons at total sizes five, six, and seven give the same period.
This lemma applies to Grundy's split convention, but the monochromatic-record
hypothesis remains a substantive restriction. -/
theorem period_two_of_singleton_unequal_split_records
    (t : Nat → Transition Q) (k : Nat)
    (hoptions : ∀ n, 0 < n → (t n).options.Subsingleton)
    (hsquare : ∀ n, 0 < n → (t n).value * (t n).value = 1)
    (hsplit : ∀ i j : Nat, 0 < i → i < j →
      (t i).value * (t j).value ∈ (t (k + (i + j))).options) :
    ∀ n : Nat, 0 < n → (t (n + 2)).value = (t n).value := by
  let x : Nat → Q := fun n ↦ (t n).value
  have hsq (n : Nat) (hn : 0 < n) : x n * x n = 1 := hsquare n hn
  have h14 : x 1 * x 4 = x 2 * x 3 :=
    hoptions (k + 5) (by omega)
      (hsplit 1 4 (by omega) (by omega)) (hsplit 2 3 (by omega) (by omega))
  have h15 : x 1 * x 5 = x 2 * x 4 :=
    hoptions (k + 6) (by omega)
      (hsplit 1 5 (by omega) (by omega)) (hsplit 2 4 (by omega) (by omega))
  have h25 : x 2 * x 5 = x 3 * x 4 :=
    hoptions (k + 7) (by omega)
      (hsplit 2 5 (by omega) (by omega)) (hsplit 3 4 (by omega) (by omega))
  have h31 : x 3 = x 1 := by
    calc
      x 3 = x 3 * (x 4 * x 4) := by rw [hsq 4 (by omega), mul_one]
      _ = (x 3 * x 4) * x 4 := (mul_assoc _ _ _).symm
      _ = (x 2 * x 5) * x 4 := by rw [← h25]
      _ = x 5 * (x 2 * x 4) := by ac_rfl
      _ = x 5 * (x 1 * x 5) := by rw [← h15]
      _ = x 1 * (x 5 * x 5) := by ac_rfl
      _ = x 1 := by rw [hsq 5 (by omega), mul_one]
  have hcancel {b c : Q} (h : x 1 * b = x 1 * c) : b = c := by
    have hh := congrArg (fun q ↦ x 1 * q) h
    simpa [← mul_assoc, hsq 1 (by omega)] using hh
  have h42 : x 4 = x 2 := by
    apply hcancel
    simpa [h31, mul_comm] using h14
  have h51 : x 5 = x 1 := by
    apply hcancel
    rw [h15, h42, hsq 2 (by omega), hsq 1 (by omega)]
  intro n hn
  change x (n + 2) = x n
  by_cases hlarge : 4 ≤ n
  · have hleft := hsplit 1 (n + 2) (by omega) (by omega)
    have hright := hsplit 3 n (by omega) (by omega)
    have hsum : k + (3 + n) = k + (1 + (n + 2)) := by omega
    rw [hsum] at hright
    have h : x 1 * x (n + 2) = x 3 * x n :=
      hoptions (k + (1 + (n + 2))) (by omega) hleft hright
    rw [h31] at h
    exact hcancel h
  · interval_cases n <;> simp_all

/-- **Binary split periodicity.** Every total trace in a two-element valid
table with even one active split offset has period two from heap one.
Consequently fixed finite split codes over this quotient admit an exhaustive
four-word certificate search. -/
theorem binary_split_trace_period_two
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hP : P.Nonempty) (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {a : Q} (hstar : Transition.mk a ({1} : Set Q) ∈ T)
    (hbinary : ∀ q : Q, q = 1 ∨ q = a)
    (t : Nat → Transition Q) (k : Nat)
    (hrecord : ∀ n, 0 < n → t n ∈ T)
    (hsplit : ∀ i j : Nat, 0 < i → 0 < j →
      (t i).value * (t j).value ∈ (t (k + (i + j))).options) :
    ∀ n : Nat, 0 < n → (t (n + 2)).value = (t n).value := by
  have ha2 := star_square_eq_one hterminal hreduced hclosed hparity hranked hstar
  apply period_two_of_singleton_split_records t k
  · intro n hn
    exact binary_options_subsingleton hP hterminal hreduced hclosed hparity hranked
      hbinary (hrecord n hn)
  · intro n _
    rcases hbinary (t n).value with h | h
    · simp [h]
    · simpa [h, pow_two] using ha2
  · exact hsplit

/-- The unique valid table on the two-element quotient has exactly the
terminal record and the two complementary singleton records. -/
theorem binary_record_iff
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hP : P.Nonempty) (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {a : Q} (hstar : Transition.mk a ({1} : Set Q) ∈ T)
    (hbinary : ∀ q : Q, q = 1 ∨ q = a) (t : Transition Q) :
    t ∈ T ↔ t = Transition.mk 1 ∅ ∨
      t = Transition.mk a {1} ∨ t = Transition.mk 1 {a} := by
  constructor
  · intro ht
    have hnot := value_not_mem_own_options hP hterminal
      hreduced hclosed hparity hranked ht
    have hsub := binary_options_subsingleton hP hterminal
      hreduced hclosed hparity hranked hbinary ht
    have hteq : t = Transition.mk t.value t.options := by cases t; rfl
    by_cases hE : t.options.Nonempty
    · obtain ⟨e, he⟩ := hE
      have hEeq : t.options = {e} := by
        ext f
        constructor
        · intro hf
          exact hsub hf he
        · intro hf
          have hf : f = e := hf
          simpa [hf] using he
      rcases hbinary t.value with hv | hv
      · rcases hbinary e with he1 | hea
        · exact False.elim (hnot (by simpa [hv, he1] using he))
        · exact Or.inr (Or.inr (by simpa [hv, hEeq, hea] using hteq))
      · rcases hbinary e with he1 | hea
        · exact Or.inr (Or.inl (by simpa [hv, hEeq, he1] using hteq))
        · exact False.elim (hnot (by simpa [hv, hea] using he))
    · have hEempty : t.options = ∅ := not_nonempty_iff_eq_empty.mp hE
      have hv := value_eq_of_options_eq hreduced hclosed hparity hranked
        ht hterminal hEempty
      exact Or.inl (by simpa [hv, hEempty] using hteq)
  · rintro (rfl | rfl | rfl)
    · exact hterminal
    · exact hstar
    · have ha2 := star_square_eq_one hterminal hreduced hclosed hparity hranked hstar
      simpa [ha2] using unary_chain_transition hclosed hstar 1

/-- The four possible binary split traces are obtained by choosing the two
positive parity classes; coefficient zero remains the terminal value. -/
def twoWord (u v : Q) : Nat → Q
  | 0 => 1
  | n + 1 => if n % 2 = 0 then u else v

/-- Every two-word candidate has period two from its first positive index. -/
theorem twoWord_period (u v : Q) :
    ∀ n, 1 ≤ n → twoWord u v (n + 2) = twoWord u v n := by
  intro n hn
  cases n with
  | zero => omega
  | succ n => simp [twoWord]

/-- A positive period-two word is determined by its first two values. -/
theorem eq_twoWord_of_period_two (x : Nat → Q) (hx0 : x 0 = 1)
    (hperiod : ∀ n, 0 < n → x (n + 2) = x n) :
    x = twoWord (x 1) (x 2) := by
  have hpositive : ∀ n : Nat, x (n + 1) = twoWord (x 1) (x 2) (n + 1) := by
    apply Nat.twoStepInduction
    · simp [twoWord]
    · simp [twoWord]
    · intro n hn _
      have hp := hperiod (n + 1) (by omega)
      have hq := twoWord_period (x 1) (x 2) (n + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.trans (hn.trans hq.symm)
  funext n
  cases n with
  | zero => exact hx0
  | succ n => exact hpositive n

/-- Checking coefficients through `d + 5` certifies a two-word trace for a
code supported through digit `d`. This is a finite exact certificate. -/
theorem twoWord_finite_certificate
    (u v : Q) {whole one two : Set Nat} {T : Set (Transition Q)} {d : Nat}
    (hbounded : MasksBounded whole one two d) :
    (∀ n, octalRecord (twoWord u v) whole one two n ∈ T) ↔
      ∀ n, n < d + 6 → octalRecord (twoWord u v) whole one two n ∈ T := by
  constructor
  · intro h n _
    exact h n
  · intro h
    apply octalRecord_mem_of_finite_certificate (twoWord u v)
      (N := 1) (p := 2) (B := d + 4) (by omega) (by omega) hbounded
      (twoWord_period u v) (by omega)
    intro n hn
    exact h n (by omega)

/-- **Complete finite criterion for binary split traces.** For any fixed
finite octal code with an active split bit, totality in a two-element valid
table is equivalent to one of the four two-word candidates passing the finite
record check through heap `d + 5`. -/
theorem binary_split_total_iff_finite_candidate
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat}
    (hP : P.Nonempty) (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    {a : Q} (hstar : Transition.mk a ({1} : Set Q) ∈ T)
    (hbinary : ∀ q : Q, q = 1 ∨ q = a)
    {whole one two : Set Nat} {d : Nat}
    (hbounded : MasksBounded whole one two d) (htwo : two.Nonempty) :
    (∃ x : Nat → Q, x 0 = 1 ∧ ∀ n, octalRecord x whole one two n ∈ T) ↔
      ∃ u v : Q, ∀ n, n < d + 6 → octalRecord (twoWord u v) whole one two n ∈ T := by
  constructor
  · rintro ⟨x, hx0, hxT⟩
    obtain ⟨k, hk⟩ := htwo
    let t : Nat → Transition Q := octalRecord x whole one two
    have hsplit : ∀ i j : Nat, 0 < i → 0 < j →
        (t i).value * (t j).value ∈ (t (k + (i + j))).options := by
      intro i j hi hj
      refine Or.inr ⟨k, hk, by omega, i, j, hi, hj, ?_, rfl⟩
      omega
    have hperiod := binary_split_trace_period_two hP hterminal hreduced hclosed
      hparity hranked hstar hbinary t k (fun n _ ↦ hxT n) hsplit
    have hxeq := eq_twoWord_of_period_two x hx0 hperiod
    refine ⟨x 1, x 2, ?_⟩
    intro n _
    simpa [← hxeq] using hxT n
  · rintro ⟨u, v, hfinite⟩
    exact ⟨twoWord u v, rfl, (twoWord_finite_certificate u v hbounded).mpr hfinite⟩

end Ogdoad.MisereParityTrace
