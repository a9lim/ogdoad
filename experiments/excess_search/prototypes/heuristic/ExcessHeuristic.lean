import Mathlib

/-!
# The random-model skeleton for the `0/1/4` excess rule

This file formalizes only the *logic* of the heuristic, not the heuristic
itself.  An abstract probability space carries, for every index `n`, a random
excess `m n` and a fixed rule value `r n`.  Two hypotheses encode the model:

* `hfail`: for primes `p > N`, the rule fails with probability at least `1/p`,
  and these failure events are independent (`hind`);
* `hbig`: the excess exceeds a fixed level `K` with probability at most
  `C / n^2` (no independence assumed).

Conclusion: almost surely the rule fails for infinitely many `n`, while the
excess is eventually at most `K`.  So, inside the model, "the `0/1/4` rule has
infinitely many counterexamples" and "Lenstra's excesses are bounded" hold
simultaneously; the second uses only the first Borel--Cantelli lemma and is
therefore insensitive to arbitrary dependence between rows, while the first
uses independence (second Borel--Cantelli lemma).

Nothing here says the Conway-selected elements satisfy the hypotheses.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace ExcessHeuristic

/-- `∑ 1/p` over primes `p > N` diverges (a tail of Euler's divergent series). -/
theorem not_summable_one_div_primes_gt (N : ℕ) :
    ¬ Summable (indicator {p : ℕ | p.Prime ∧ N < p} (fun n : ℕ => (1 : ℝ) / n)) := by
  intro h
  apply not_summable_one_div_on_primes
  have hfin : Summable (indicator {p : ℕ | p.Prime ∧ p ≤ N} (fun n : ℕ => (1 : ℝ) / n)) := by
    apply summable_of_hasFiniteSupport
    refine (Set.finite_Iic N).subset ?_
    intro n hn
    by_contra hc
    apply hn
    have : n ∉ {p : ℕ | p.Prime ∧ p ≤ N} := fun h' => hc h'.2
    exact indicator_of_notMem this _
  convert h.add hfin using 1
  funext n
  by_cases hp : n.Prime <;> by_cases hn : N < n
  · have h2 : ¬ n ≤ N := not_le.mpr hn
    simp [indicator, hp, hn, h2]
  · have h2 : n ≤ N := not_lt.mp hn
    simp [indicator, hp, hn, h2]
  · simp [indicator, hp]
  · simp [indicator, hp]

/-- Second Borel--Cantelli: independent events of probability `≥ 1/p` at the
primes `p > N` occur infinitely often almost surely. -/
theorem limsup_failures_eq_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : ℕ → Set Ω) (hm : ∀ n, MeasurableSet (A n)) (hind : iIndepSet A μ) (N : ℕ)
    (hprob : ∀ p, p.Prime → N < p → ENNReal.ofReal (1 / p) ≤ μ (A p)) :
    μ (limsup A atTop) = 1 := by
  apply measure_limsup_eq_one hm hind
  by_contra hne
  have hs : Summable (fun n => (μ (A n)).toReal) := ENNReal.summable_toReal hne
  apply not_summable_one_div_primes_gt N
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · exact indicator_nonneg (fun _ _ => by positivity) _
  · by_cases h : n ∈ {p : ℕ | p.Prime ∧ N < p}
    · rw [indicator_of_mem h]
      have hle := hprob n h.1 h.2
      have hfin : μ (A n) ≠ ∞ := ne_top_of_le_ne_top hne (ENNReal.le_tsum n)
      calc (1 : ℝ) / n = (ENNReal.ofReal (1 / n)).toReal := by
              rw [ENNReal.toReal_ofReal (by positivity)]
        _ ≤ (μ (A n)).toReal := ENNReal.toReal_mono hfin hle
    · rw [indicator_of_notMem h]; exact ENNReal.toReal_nonneg

/-- First Borel--Cantelli: events of probability `≤ C/n^2` occur only finitely
often almost surely, with no independence hypothesis. -/
theorem ae_eventually_small {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (B : ℕ → Set Ω) (C : ℝ) (hC : 0 ≤ C)
    (hprob : ∀ n, μ (B n) ≤ ENNReal.ofReal (C / (n : ℝ) ^ 2)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ B n := by
  apply ae_eventually_notMem
  have hsum : Summable (fun n : ℕ => C / (n : ℝ) ^ 2) := by
    refine ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left C).congr (fun n => ?_)
    ring
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hprob)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

/-- **Model consequences.**  In any model satisfying the two hypotheses, almost
surely the rule fails infinitely often *and* the excess is eventually `≤ K`. -/
theorem model_consequences {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (m : ℕ → Ω → ℕ) (r : ℕ → ℕ) (K N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hmeas : ∀ n, MeasurableSet {ω | m n ω ≠ r n})
    (hind : iIndepSet (fun n => {ω | m n ω ≠ r n}) μ)
    (hfail : ∀ p, p.Prime → N < p → ENNReal.ofReal (1 / p) ≤ μ {ω | m p ω ≠ r p})
    (hbig : ∀ n, μ {ω | K < m n ω} ≤ ENNReal.ofReal (C / (n : ℝ) ^ 2)) :
    ∀ᵐ ω ∂μ, (∃ᶠ n in atTop, m n ω ≠ r n) ∧ (∀ᶠ n in atTop, m n ω ≤ K) := by
  have hP : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  have h1 := limsup_failures_eq_one _ hmeas hind N hfail
  have hlim : ∀ᵐ ω ∂μ, ω ∈ limsup (fun n => {ω | m n ω ≠ r n}) atTop := by
    have hmeasL : MeasurableSet (limsup (fun n => {ω | m n ω ≠ r n}) atTop) :=
      MeasurableSet.measurableSet_limsup hmeas
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff hmeasL).mpr h1
  have h2 := ae_eventually_small (fun n => {ω | K < m n ω}) C hC hbig
  filter_upwards [hlim, h2] with ω hω1 hω2
  refine ⟨?_, ?_⟩
  · rw [mem_limsup_iff_frequently_mem] at hω1
    exact hω1
  · filter_upwards [hω2] with n hn
    simpa using hn

end ExcessHeuristic

#print axioms ExcessHeuristic.model_consequences
