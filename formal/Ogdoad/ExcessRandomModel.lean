import Mathlib

/-!
# The random model behind the `0/1/4` excess heuristic

**This file proves theorems about a probabilistic model. It proves nothing about
Conway's field `On_2`, Lenstra's excess `m_p`, or the `0/1/4` rule.**

## The heuristic being modelled

Each odd prime `p` above the settled range contributes exactly one row of the
`0/1/4` census (see `docs/OPEN.md`, section 2, and `writeups/excess.tex`). The
row selects an element `β_p` of a finite cyclic group, in practice the unit
group `𝔽_{2^E}ˣ` of a binary field with `p ∣ 2^E - 1`, and (by the census's
Euler test, not formalized here) the rule fails at `p` exactly when `β_p` is a
`p`-th power there. The heuristic treats the selected elements as independent
and uniformly distributed. Under that assumption row `p` fails with probability exactly `1/p`, and since `∑ 1/p`
diverges, failures occur infinitely often almost surely.

## What is proved here (Lean-checked, claim level: proved here)

* `ae_infinite_of_tsum_eq_top`: second Borel--Cantelli over any countable index
  type: for independent measurable events with divergent probability sum,
  almost surely infinitely many occur.
* `tsum_inv_oddPrime_eq_top`: `∑_{p odd prime} 1/p = ∞` (from Mathlib's
  divergence of the prime reciprocals).
* `ae_infinite_oddPrime_of_div_le`: independent events `A p` indexed by odd
  primes with `P(A p) ≥ c/p` for a fixed `c > 0` occur infinitely often almost
  surely; `ae_infinite_oddPrime_of_eq_inv` is the case `P(A p) = 1/p`, and
  `ae_exists_gt_oddPrime_of_eq_inv` says that almost surely, past every bound
  (in particular past `727`) some event occurs.
* `ae_cond_infinite_oddPrime_of_eq_inv`: the conclusion survives conditioning
  on any event `B`, e.g. on all census rows below a bound being successes
  (for a null `B` the conditional measure is zero and the statement is empty).
* `integral_card_filter_eq_sum` and `integral_card_filter_oddPrime_eq_sum_inv`:
  the expected number of occurring events with index in a finite set `S` is
  `∑_{p ∈ S} P(A p)`, equal to `∑_{p ∈ S} 1/p` when `P(A p) = 1/p`
  (linearity of expectation; no independence needed).
* `measure_biInter_compl_eq_prod`: the probability that no event with index in
  `S` occurs is `∏_{p ∈ S} (1 - P(A p))` under independence.
* `uniformOn_pthPowers`, `uniformOn_units_pthPowers`: in a finite cyclic group
  whose order is divisible by `p` (e.g. `Kˣ` for a finite field `K`
  with `p ∣ |K| - 1`), a uniform element is a `p`-th power with probability
  exactly `1/p`.
* `RandomModel.ae_infinite_fails`: the model is not vacuous. For any family
  of finite cyclic groups `G p` with `p ∣ |G p|`, the infinite product of
  uniform measures exists, the events `{ω | ω p is a p-th power}` are
  independent with probability `1/p`, and almost surely infinitely many occur.

## The modelling hypothesis that is NOT proved here

That the actual selected elements `β_p` attached to Conway's field behave like
the coordinates of `RandomModel.measure`, i.e. like independent uniform
elements of their cyclic groups. Nothing in this file connects the model to
`On_2`. In particular this file does not show that the `0/1/4` rule fails for
any prime, and divergence of `∑ 1/p` is not evidence that a counterexample
exists. Known caveats on the hypothesis: rows settled by theorem or certificate
carry no remaining uncertainty; the selected elements are built recursively
along prime ancestry, which can create dependence; uniformity should be
hypothesized only after accounting for known structural constraints; the
expected-count formula needs only the marginals, but any "probability of at
least one counterexample" estimate additionally needs independence.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace Ogdoad.ExcessRandomModel

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Second Borel--Cantelli over a countable index type -/

/-- **Second Borel--Cantelli over a countable index type.** If `(A i)` are
independent measurable events whose probabilities have divergent sum, then
almost surely infinitely many of them occur. -/
theorem ae_infinite_of_tsum_eq_top {ι : Type*} [Countable ι] {A : ι → Set Ω}
    (hmeas : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (hdiv : ∑' i, μ (A i) = ∞) :
    ∀ᵐ ω ∂μ, {i | ω ∈ A i}.Infinite := by
  have : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  have hinf : Infinite ι := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    have := Fintype.ofFinite ι
    rw [tsum_fintype] at hdiv
    exact ENNReal.sum_ne_top.2 (fun i _ => measure_ne_top μ (A i)) hdiv
  obtain ⟨hden⟩ := nonempty_denumerable ι
  let e : ℕ ≃ ι := (Denumerable.eqv ι).symm
  have hind' : iIndepSet (A ∘ e) μ := hind.precomp e.injective
  have hdiv' : ∑' n, μ ((A ∘ e) n) = ∞ := by
    simpa [Function.comp] using (e.tsum_eq (fun i => μ (A i))).trans hdiv
  have hone := measure_limsup_eq_one (fun n => hmeas (e n)) hind' hdiv'
  have hlim : MeasurableSet (limsup (A ∘ e) atTop) :=
    MeasurableSet.measurableSet_limsup (fun n => hmeas (e n))
  have hnull : μ (limsup (A ∘ e) atTop)ᶜ = 0 := (prob_compl_eq_zero_iff hlim).2 hone
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  intro hmem
  apply hω
  rw [mem_limsup_iff_frequently_mem, Nat.frequently_atTop_iff_infinite] at hmem
  refine (hmem.image e.injective.injOn).mono ?_
  rintro _ ⟨n, hn, rfl⟩
  exact hn

/-! ### Odd primes and the divergence of `∑ 1/p` -/

/-- The odd primes: the index set of the census rows. -/
def oddPrimes : Set ℕ := {p | p.Prime ∧ p ≠ 2}

/-- The odd primes as a type. -/
abbrev OddPrime : Type := ↥oddPrimes

theorem OddPrime.prime (p : OddPrime) : (p : ℕ).Prime := p.2.1

theorem OddPrime.ne_two (p : OddPrime) : (p : ℕ) ≠ 2 := p.2.2

/-- The reciprocals of the odd primes are not summable. -/
theorem not_summable_inv_oddPrime : ¬ Summable (fun p : OddPrime => ((p : ℕ) : ℝ)⁻¹) := by
  intro h
  have hind : Summable (oddPrimes.indicator (fun n : ℕ => (1 : ℝ) / n)) := by
    rw [← summable_subtype_iff_indicator]
    simp only [one_div]
    exact h
  apply not_summable_one_div_on_primes
  refine Summable.of_nonneg_of_le (fun n => Set.indicator_nonneg (fun _ _ => by positivity) n)
    (fun n => ?_) (hind.add (hasSum_ite_eq 2 (1 : ℝ)).summable)
  by_cases h2 : n = 2
  · subst h2
    simp [Set.indicator, oddPrimes]
    norm_num
  · by_cases hp : n.Prime
    · simp [Set.indicator, oddPrimes, hp, h2]
    · simp [Set.indicator, oddPrimes, hp, h2]

/-- `∑_{p odd prime} 1/p = ∞` in `ℝ≥0∞`. -/
theorem tsum_inv_oddPrime_eq_top : ∑' p : OddPrime, ((p : ℕ) : ℝ≥0∞)⁻¹ = ∞ := by
  by_contra h
  apply not_summable_inv_oddPrime
  have hcoe : ∀ p : OddPrime, ((p : ℕ) : ℝ≥0∞)⁻¹ = ((((p : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    intro p
    rw [ENNReal.coe_inv (by exact_mod_cast p.prime.ne_zero), ENNReal.coe_natCast]
  simp_rw [hcoe] at h
  have hs := ENNReal.tsum_coe_ne_top_iff_summable.1 h
  have := NNReal.summable_coe.2 hs
  simpa using this

/-! ### Infinitely many events, indexed by odd primes -/

/-- Independent events indexed by the odd primes with `P(A p) ≥ c/p` for a fixed
`c ≠ 0` occur infinitely often almost surely. -/
theorem ae_infinite_oddPrime_of_div_le {A : OddPrime → Set Ω}
    (hmeas : ∀ p, MeasurableSet (A p)) (hind : iIndepSet A μ)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hlow : ∀ p : OddPrime, c / ((p : ℕ) : ℝ≥0∞) ≤ μ (A p)) :
    ∀ᵐ ω ∂μ, {p | ω ∈ A p}.Infinite := by
  refine ae_infinite_of_tsum_eq_top hmeas hind ?_
  refine top_unique ?_
  calc (∞ : ℝ≥0∞) = c * ∑' p : OddPrime, ((p : ℕ) : ℝ≥0∞)⁻¹ := by
        rw [tsum_inv_oddPrime_eq_top, ENNReal.mul_top hc]
    _ = ∑' p : OddPrime, c / ((p : ℕ) : ℝ≥0∞) := by
        rw [← ENNReal.tsum_mul_left]
        rfl
    _ ≤ ∑' p : OddPrime, μ (A p) := ENNReal.tsum_le_tsum hlow

/-- The exact random-model case: independent events with `P(A p) = 1/p` occur
for infinitely many odd primes `p`, almost surely. -/
theorem ae_infinite_oddPrime_of_eq_inv {A : OddPrime → Set Ω}
    (hmeas : ∀ p, MeasurableSet (A p)) (hind : iIndepSet A μ)
    (hprob : ∀ p : OddPrime, μ (A p) = ((p : ℕ) : ℝ≥0∞)⁻¹) :
    ∀ᵐ ω ∂μ, {p | ω ∈ A p}.Infinite :=
  ae_infinite_oddPrime_of_div_le hmeas hind one_ne_zero
    (fun p => by rw [hprob p, one_div])

/-- Almost surely, past every bound `N` (for instance `N = 727`), some event
`A p` with `p > N` occurs. -/
theorem ae_exists_gt_oddPrime_of_eq_inv {A : OddPrime → Set Ω}
    (hmeas : ∀ p, MeasurableSet (A p)) (hind : iIndepSet A μ)
    (hprob : ∀ p : OddPrime, μ (A p) = ((p : ℕ) : ℝ≥0∞)⁻¹) :
    ∀ᵐ ω ∂μ, ∀ N : ℕ, ∃ p : OddPrime, N < (p : ℕ) ∧ ω ∈ A p := by
  filter_upwards [ae_infinite_oddPrime_of_eq_inv hmeas hind hprob] with ω hω N
  have himg : ((Subtype.val : OddPrime → ℕ) '' {p | ω ∈ A p}).Infinite :=
    hω.image Subtype.val_injective.injOn
  obtain ⟨_, ⟨p, hp, rfl⟩, hN⟩ := himg.exists_gt N
  exact ⟨p, hN, hp⟩

/-- Conditioning on any event `B` (for instance, on every census row below some
bound being a success) does not change the conclusion. When `μ B = 0` the
conditional measure is zero and the statement holds vacuously. -/
theorem ae_cond_infinite_oddPrime_of_eq_inv {A : OddPrime → Set Ω}
    (hmeas : ∀ p, MeasurableSet (A p)) (hind : iIndepSet A μ)
    (hprob : ∀ p : OddPrime, μ (A p) = ((p : ℕ) : ℝ≥0∞)⁻¹) (B : Set Ω) :
    ∀ᵐ ω ∂μ[|B], {p | ω ∈ A p}.Infinite :=
  cond_absolutelyContinuous.ae_le (ae_infinite_oddPrime_of_eq_inv hmeas hind hprob)

/-! ### Expected counts and the no-hit probability -/

/-- **Expected count.** For any finite measure and measurable events, the
expected number of indices `i ∈ S` with `ω ∈ A i` is `∑_{i ∈ S} P(A i)`.
No independence is needed. -/
theorem integral_card_filter_eq_sum {ι : Type*} [IsFiniteMeasure μ] {A : ι → Set Ω}
    (hmeas : ∀ i, MeasurableSet (A i)) (S : Finset ι) [∀ ω, DecidablePred (fun i => ω ∈ A i)] :
    ∫ ω, ((S.filter (fun i => ω ∈ A i)).card : ℝ) ∂μ = ∑ i ∈ S, μ.real (A i) := by
  have hpt : ∀ ω, ((S.filter (fun i => ω ∈ A i)).card : ℝ) =
      ∑ i ∈ S, (A i).indicator (1 : Ω → ℝ) ω := by
    intro ω
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : ω ∈ A i <;> simp [h]
  simp_rw [hpt]
  refine (integral_finsetSum S (fun i _ => ?_)).trans ?_
  · exact (integrable_const (1 : ℝ)).indicator (hmeas i)
  exact Finset.sum_congr rfl (fun i _ => integral_indicator_one (hmeas i))

/-- **Expected count in the random model.** If `P(A p) = 1/p`, the expected
number of odd primes `p ∈ S` with `ω ∈ A p` is `∑_{p ∈ S} 1/p`. -/
theorem integral_card_filter_oddPrime_eq_sum_inv [IsFiniteMeasure μ] {A : OddPrime → Set Ω}
    (hmeas : ∀ p, MeasurableSet (A p))
    (hprob : ∀ p : OddPrime, μ (A p) = ((p : ℕ) : ℝ≥0∞)⁻¹) (S : Finset OddPrime)
    [∀ ω, DecidablePred (fun p => ω ∈ A p)] :
    ∫ ω, ((S.filter (fun p => ω ∈ A p)).card : ℝ) ∂μ = ∑ p ∈ S, ((p : ℕ) : ℝ)⁻¹ := by
  rw [integral_card_filter_eq_sum hmeas S]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [measureReal_def, hprob p, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **No-hit probability.** Under independence, the probability that none of
the events `A i`, `i ∈ S`, occurs is `∏_{i ∈ S} (1 - P(A i))`. -/
theorem measure_biInter_compl_eq_prod {ι : Type*} {A : ι → Set Ω}
    (hmeas : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ) (S : Finset ι) :
    μ (⋂ i ∈ S, (A i)ᶜ) = ∏ i ∈ S, (1 - μ (A i)) := by
  have : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  rw [iIndepSet_iff_iIndep] at hind
  rw [hind.meas_biInter (fun i _ =>
    (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton (A i))).compl)]
  exact Finset.prod_congr rfl (fun i _ => prob_compl_eq_one_sub (hmeas i))

/-! ### Uniform elements of a finite cyclic group -/

section Cyclic

variable (G : Type*) [CommGroup G] [IsCyclic G] [Fintype G]

/-- In a finite cyclic group of order divisible by `p`, the `p`-th powers form a
subgroup of index `p`. (Primality of `p` is not needed.) -/
theorem index_pthPowers {p : ℕ} (hdvd : p ∣ Nat.card G) :
    (powMonoidHom p : G →* G).range.index = p := by
  rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right hdvd]

/-- In a finite cyclic group of order divisible by `p`, a uniformly random
element is a `p`-th power with probability exactly `1/p`. -/
theorem uniformOn_pthPowers [MeasurableSpace G] [MeasurableSingletonClass G]
    {p : ℕ} (hdvd : p ∣ Nat.card G) :
    uniformOn (Set.univ : Set G) ((powMonoidHom p : G →* G).range : Set G) = (p : ℝ≥0∞)⁻¹ := by
  set R := (powMonoidHom p : G →* G).range
  have hcard : Nat.card R * p = Fintype.card G := by
    rw [← index_pthPowers G hdvd, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hR : (Set.toFinite (R : Set G)).toFinset.card = Nat.card R :=
    (Nat.card_eq_card_finite_toFinset (Set.toFinite (R : Set G))).symm
  rw [uniformOn_univ, Measure.count_apply_finite _ (Set.toFinite _), hR, ← hcard]
  have h0 : (Nat.card R : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := R)).ne'
  push_cast
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl h0) (Or.inl (by simp)),
    mul_comm (Nat.card R : ℝ≥0∞)⁻¹, mul_assoc, ENNReal.inv_mul_cancel h0 (by simp), mul_one]

end Cyclic

/-- The binary-field case: for a finite field `K` and `p ∣ |K| - 1`, a
uniformly random unit of `K` is a `p`-th power with probability exactly `1/p`. -/
theorem uniformOn_units_pthPowers (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [MeasurableSpace Kˣ] [MeasurableSingletonClass Kˣ]
    {p : ℕ} (hdvd : p ∣ Fintype.card K - 1) :
    uniformOn (Set.univ : Set Kˣ) ((powMonoidHom p : Kˣ →* Kˣ).range : Set Kˣ) =
      (p : ℝ≥0∞)⁻¹ :=
  uniformOn_pthPowers Kˣ (by rwa [Nat.card_eq_fintype_card, Fintype.card_units])

/-! ### A constructed model: independent uniform elements -/

namespace RandomModel

variable (G : OddPrime → Type*) [∀ p, CommGroup (G p)] [∀ p, IsCyclic (G p)]
  [∀ p, Fintype (G p)] [∀ p, MeasurableSpace (G p)] [∀ p, MeasurableSingletonClass (G p)]

/-- The random model: one independent uniform element of `G p` for every odd
prime `p`. -/
noncomputable def measure : Measure (∀ p, G p) :=
  Measure.infinitePi (fun p => uniformOn (Set.univ : Set (G p)))

instance : IsProbabilityMeasure (measure G) := by
  unfold measure
  infer_instance

/-- The event "row `p` fails": the `p`-coordinate is a `p`-th power. -/
def fails (p : OddPrime) : Set (∀ q, G q) :=
  Function.eval p ⁻¹' ((powMonoidHom (p : ℕ) : G p →* G p).range : Set (G p))

omit [∀ p, IsCyclic (G p)] in
theorem measurableSet_fails (p : OddPrime) : MeasurableSet (fails G p) :=
  measurable_pi_apply p (Set.toFinite _).measurableSet

theorem measure_fails (p : OddPrime) (hdvd : (p : ℕ) ∣ Nat.card (G p)) :
    measure G (fails G p) = ((p : ℕ) : ℝ≥0∞)⁻¹ := by
  unfold measure fails
  rw [(measurePreserving_eval_infinitePi _ p).measure_preimage
    (Set.toFinite _).measurableSet.nullMeasurableSet]
  exact uniformOn_pthPowers (G p) hdvd

omit [∀ p, IsCyclic (G p)] in
theorem iIndepSet_fails : iIndepSet (fails G) (measure G) := by
  rw [iIndepSet_iff_meas_biInter (measurableSet_fails G)]
  intro S
  have hpi : (⋂ p ∈ S, fails G p) =
      Set.pi (S : Set OddPrime)
        (fun p => ((powMonoidHom (p : ℕ) : G p →* G p).range : Set (G p))) := by
    ext ω
    simp [fails]
  rw [hpi]
  unfold measure
  rw [Measure.infinitePi_pi _ (fun p _ => (Set.toFinite _).measurableSet)]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  exact ((measurePreserving_eval_infinitePi (fun q => uniformOn (Set.univ : Set (G q))) p
    ).measure_preimage (Set.toFinite ((powMonoidHom (p : ℕ) : G p →* G p).range : Set (G p))
    ).measurableSet.nullMeasurableSet).symm

/-- **The random-model theorem.** If every `G p` is a finite cyclic group with
`p ∣ |G p|`, then for independent uniform elements `ω p ∈ G p`, almost surely
`ω p` is a `p`-th power for infinitely many odd primes `p`. -/
theorem ae_infinite_fails (hdvd : ∀ p : OddPrime, (p : ℕ) ∣ Nat.card (G p)) :
    ∀ᵐ ω ∂(measure G), {p | ω ∈ fails G p}.Infinite :=
  ae_infinite_oddPrime_of_eq_inv (measurableSet_fails G) (iIndepSet_fails G)
    (fun p => measure_fails G p (hdvd p))

/-- The same conclusion stated as "past every bound some row fails". -/
theorem ae_exists_gt_fails (hdvd : ∀ p : OddPrime, (p : ℕ) ∣ Nat.card (G p)) :
    ∀ᵐ ω ∂(measure G), ∀ N : ℕ, ∃ p : OddPrime, N < (p : ℕ) ∧ ω ∈ fails G p :=
  ae_exists_gt_oddPrime_of_eq_inv (measurableSet_fails G) (iIndepSet_fails G)
    (fun p => measure_fails G p (hdvd p))

end RandomModel

end Ogdoad.ExcessRandomModel
