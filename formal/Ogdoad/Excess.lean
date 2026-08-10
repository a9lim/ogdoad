import Mathlib

/-!
# Lenstra-excess reductions

This file formalizes algebraic pieces of the four-arm reduction in
`writeups/excess.tex`, with the `2 * 3^k` column and
`experiments/exception_column_m4.py` still supplying most of the finite
certificate surface.

The universal upper bound is deliberately stated but not postulated.  The
proved results isolate the unconditional lower bound, the corrected norm, and
the exact finite-field power obstruction whose uniform nonvanishing is the
remaining conjecture.
-/

namespace Ogdoad.Excess

/-- `a` is a `p`-th power. -/
def IsPthPower {K : Type*} [Monoid K] (p : Nat) (a : K) : Prop :=
  ∃ x, x ^ p = a

/-- `m` is the first translate in a family which is not a `p`-th power.  This
is the part of Lenstra's finite-excess definition used by the column proof. -/
def HasExcessAt {K : Type*} [Monoid K] (p : Nat) (β : Nat → K) (m : Nat) : Prop :=
  (∀ j < m, IsPthPower p (β j)) ∧ ¬IsPthPower p (β m)

/-- An element whose order is coprime to `p` has a `p`-th root inside its
own cyclic subgroup. -/
theorem isPthPower_of_coprime_order {G : Type*} [Group G] {p : Nat} {a : G}
    (hcop : (orderOf a).Coprime p) : IsPthPower p a := by
  let H : Subgroup G := Subgroup.zpowers a
  have hcard : (Nat.card H).Coprime p := by
    simpa only [H, Nat.card_zpowers] using hcop
  obtain ⟨x, hx⟩ := hcard.pow_left_bijective.surjective
    (⟨a, Subgroup.mem_zpowers a⟩ : H)
  exact ⟨x.1, congrArg Subtype.val hx⟩

/-- Exact Euler-quotient criterion in a finite cyclic group.  No
squarefreeness shorthand is hidden: `p ∣ |G|` is the full hypothesis used in
this group-level statement. -/
theorem isPthPower_iff_pow_card_div_eq_one {G : Type*}
    [CommGroup G] [Fintype G] [IsCyclic G] {p : Nat} (hp : p ∣ Fintype.card G)
    (a : G) :
    IsPthPower p a ↔ a ^ (Fintype.card G / p) = 1 := by
  classical
  let P : Subgroup G := (powMonoidHom p : G →* G).range
  let H : Subgroup G := (powMonoidHom (Fintype.card G / p) : G →* G).ker
  have hle : P ≤ H := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    change (y ^ p) ^ (Fintype.card G / p) = 1
    rw [← pow_mul, Nat.mul_div_cancel' hp]
    exact pow_card_eq_one
  have hP : Nat.card P = Fintype.card G / p := by
    rw [IsCyclic.card_powMonoidHom_range]
    rw [Nat.card_eq_fintype_card, Nat.gcd_eq_right_iff_dvd.mpr hp]
  have hH : Nat.card H = Fintype.card G / p := by
    rw [IsCyclic.card_powMonoidHom_ker]
    rw [Nat.card_eq_fintype_card]
    rw [Nat.gcd_eq_right_iff_dvd.mpr (Nat.div_dvd_of_dvd hp)]
  have heq : P = H := by
    apply SetLike.coe_injective
    apply Set.eq_of_subset_of_ncard_le hle
    change Nat.card H ≤ Nat.card P
    rw [hH, hP]
  constructor
  · rintro ⟨x, hx⟩
    have haP : a ∈ P := ⟨x, hx⟩
    have haH : a ∈ H := by rwa [← heq]
    exact haH
  · intro ha
    have haH : a ∈ H := ha
    have haP : a ∈ P := by rwa [heq]
    rcases haP with ⟨x, hx⟩
    exact ⟨x, hx⟩

/-- Order-theoretic form of the exact power criterion.  This is the useful
interface for the four excess arms: when `p` is prime, a selected element
misses the full `p`-primary part of the ambient cyclic group exactly when its
order divides the index-`p` quotient.  No squarefreeness assumption is
present. -/
theorem isPthPower_iff_orderOf_dvd_card_div {G : Type*}
    [CommGroup G] [Fintype G] [IsCyclic G] {p : Nat} (hp : p ∣ Fintype.card G)
    (a : G) :
    IsPthPower p a ↔ orderOf a ∣ Fintype.card G / p := by
  rw [isPthPower_iff_pow_card_div_eq_one hp]
  exact orderOf_dvd_iff_pow_eq_one.symm

/-- Negated order form used by a Kummer certificate: nonexistence of a
`p`-th root is exactly failure of the selected order to divide the
index-`p` quotient. -/
theorem not_isPthPower_iff_not_orderOf_dvd_card_div {G : Type*}
    [CommGroup G] [Fintype G] [IsCyclic G] {p : Nat} (hp : p ∣ Fintype.card G)
    (a : G) :
    ¬IsPthPower p a ↔ ¬orderOf a ∣ Fintype.card G / p := by
  exact not_congr (isPthPower_iff_orderOf_dvd_card_div hp a)

/-- A divisor of `N` equals `N` once it fails to divide every quotient by a
prime divisor of `N`.  This retains the full prime-power information: testing
only the radical of `N` would not suffice for the excess problem. -/
theorem eq_of_dvd_of_not_dvd_prime_quotients {d N : Nat}
    (hN : 0 < N) (hd : d ∣ N)
    (hfull : ∀ p, p.Prime → p ∣ N → ¬d ∣ N / p) :
    d = N := by
  rcases hd with ⟨k, rfl⟩
  have hdpos : 0 < d := by
    by_contra hd0
    simp only [Nat.not_lt, Nat.le_zero] at hd0
    subst d
    simp at hN
  by_contra hne
  have hkne : k ≠ 1 := by
    intro hk
    subst k
    simp at hne
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hkne
  have hpN : p ∣ d * k := dvd_mul_of_dvd_right hpk d
  have hpMul : p * d ∣ d * k := by
    rcases hpk with ⟨t, rfl⟩
    use t
    ac_rfl
  have hdquot : d ∣ (d * k) / p :=
    (Nat.dvd_div_iff_mul_dvd hpN).2 hpMul
  exact hfull p hp hpN hdquot

/-- In a finite cyclic group, a selected element has maximal order exactly
when it is not a `p`-th power for every prime divisor `p` of the group order.
This is the common group-theoretic endpoint of all four excess arms. -/
theorem maximal_order_iff_all_prime_power_obstructions {G : Type*}
    [CommGroup G] [Fintype G] [IsCyclic G] (a : G) :
    orderOf a = Fintype.card G ↔
      ∀ p, p.Prime → p ∣ Fintype.card G → ¬IsPthPower p a := by
  constructor
  · intro horder p hp hpcard hpow
    have hdiv := (isPthPower_iff_orderOf_dvd_card_div hpcard a).mp hpow
    rw [horder] at hdiv
    have hquotpos : 0 < Fintype.card G / p :=
      Nat.div_pos (Nat.le_of_dvd Fintype.card_pos hpcard) hp.pos
    exact (Nat.not_le_of_gt (Nat.div_lt_self Fintype.card_pos hp.one_lt))
      (Nat.le_of_dvd hquotpos hdiv)
  · intro h
    apply eq_of_dvd_of_not_dvd_prime_quotients Fintype.card_pos orderOf_dvd_card
    intro p hp hpcard
    exact (not_isPthPower_iff_not_orderOf_dvd_card_div hpcard a).mp
      (h p hp hpcard)

/-- If a primary factor `r` divides `a` but is coprime to a divisor `b`, then
the whole factor survives in the quotient `a / b`.  Applied to
`a = 2^N - 1` and `b = 2^d - 1`, this is the arithmetic reason every proper
subfield norm annihilates the entire current primary Kummer line rather than
only its radical. -/
theorem full_primary_dvd_quotient_of_coprime {a b r : Nat}
    (hb : b ∣ a) (hr : r ∣ a) (hcop : r.Coprime b) :
    r ∣ a / b := by
  have hfactor : a = b * (a / b) := (Nat.mul_div_cancel' hb).symm
  rw [hfactor] at hr
  exact hcop.dvd_of_dvd_mul_left hr

/-- A decomposition into old and new factors carries no hidden information
at a prime absent from the old factor: its complete primary valuation is
exactly the valuation of the new factor.  This is the abstract reason the
known Conway-tower order factorization does not determine a new Fermat
quotient order. -/
theorem newPrime_factorization_neutral (p old new : Nat) [Fact p.Prime]
    (hold : old ≠ 0) (hnew : new ≠ 0) (hpold : ¬p ∣ old) :
    padicValNat p (old * new) = padicValNat p new := by
  rw [padicValNat.mul hold hnew]
  rw [padicValNat.eq_zero_of_not_dvd hpold]
  simp

/-- The degree-three norm polynomial has a simple zero on every current
Kummer line away from characteristic three.  Thus the norm discards the
selected coordinate, while its first transverse derivative does not. -/
theorem cyclotomic_three_root_is_simple {K : Type*} [Field K]
    (x : K) (hroot : 1 + x + x ^ 2 = 0) (hthree : (3 : K) ≠ 0) :
    1 + 2 * x ≠ 0 := by
  intro hderiv
  apply hthree
  linear_combination 4 * hroot - (1 + 2 * x) * hderiv

/-- Prime-order shortcut behind the unconditional Fermat-prime levels of the
singleton-even arm: a nonidentity element annihilated by a prime exponent has
that exact order. -/
theorem orderOf_eq_prime_of_pow_eq_one {G : Type*} [Monoid G]
    {a : G} {p : Nat} (hp : p.Prime) (ha : a ≠ 1) (hpow : a ^ p = 1) :
    orderOf a = p := by
  have hord_ne_one : orderOf a ≠ 1 := by
    exact mt orderOf_eq_one_iff.mp ha
  have hord_dvd : orderOf a ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hpow
  exact (hp.dvd_iff_eq hord_ne_one).mp hord_dvd |>.symm

section CubicExceptionalResidue

variable {R : Type*} [CommRing R]

/-- Algebraic core of the cubic arm's three-lift exceptional-residue formula.
In the application the ring is integers modulo 3n and x = an; divisibility
of n by three makes x squared zero.  Thus 1 + x has the explicit inverse
1 - x, and the selected congruences force r = x - 1. -/
theorem exceptional_residue_of_square_zero (x t r : R)
    (h2 : IsUnit (2 : R)) (hsq : x ^ 2 = 0)
    (ht : t * (1 + x) = -2) (hr : 2 * r = t) :
    r = x - 1 := by
  have hinv : (1 + x) * (1 - x) = 1 := by
    calc
      (1 + x) * (1 - x) = 1 - x ^ 2 := by ring
      _ = 1 := by rw [hsq]; simp
  have ht' : t = 2 * (x - 1) := by
    calc
      t = t * 1 := by simp
      _ = t * ((1 + x) * (1 - x)) := by rw [hinv]
      _ = (t * (1 + x)) * (1 - x) := by ring
      _ = (-2) * (1 - x) := by rw [ht]
      _ = 2 * (x - 1) := by ring
  apply h2.mul_left_cancel
  calc
    2 * r = t := hr
    _ = 2 * (x - 1) := ht'

end CubicExceptionalResidue

/-- The square-zero input used above really holds modulo \(3n\) whenever
\(3\mid n\): the square of \(an\) contains the modulus \(3n\) as a factor. -/
theorem cubic_linear_term_sq_eq_zero (a n : Nat) (hn : 3 ∣ n) :
    ((a * n : Nat) : ZMod (3 * n)) ^ 2 = 0 := by
  rcases hn with ⟨d, rfl⟩
  calc
    ((a * (3 * d) : Nat) : ZMod (3 * (3 * d))) ^ 2 =
        (a : ZMod (3 * (3 * d))) ^ 2 * d *
          (3 * (3 * d) : Nat) := by push_cast; ring
    _ = 0 := by simp

/-- Kernel-checked form of the cubic arm's exceptional-residue calculation.
If `n` is an odd multiple of three and the two defining congruences hold
modulo `3n`, then the residue is the distinguished lift `an - 1`. -/
theorem cubic_exceptional_residue_mod (a n : Nat) (t r : ZMod (3 * n))
    (hn3 : 3 ∣ n) (hnodd : Odd n)
    (ht : t * (1 + (a * n : Nat)) = -2) (hr : 2 * r = t) :
    r = (a * n : Nat) - 1 := by
  apply exceptional_residue_of_square_zero ((a * n : Nat) : ZMod (3 * n)) t r
  · exact (ZMod.isUnit_iff_coprime 2 (3 * n)).mpr
      ((by norm_num : Odd (3 : Nat)).mul hnodd).coprime_two_left
  · exact cubic_linear_term_sq_eq_zero a n hn3
  · exact ht
  · exact hr

section TraceTower

variable {F K L : Type*} [Field F] [Field K] [Field L]
variable [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
variable [Module.Free F K] [Module.Finite F K]
variable [Module.Free K L] [Module.Finite K L]

/-- A vanishing relative trace forces the absolute trace to vanish.  This is
the formal transitivity step behind the cubic arm's trace-zero obstruction:
the selected `gamma_k` has relative trace zero at every cubic step. -/
theorem absolute_trace_eq_zero_of_relative_trace_eq_zero (x : L)
    (htrace : Algebra.trace K L x = 0) :
    Algebra.trace F L x = 0 := by
  rw [← Algebra.trace_trace (R := F) (S := K) (T := L), htrace]
  exact LinearMap.map_zero (Algebra.trace F K)

end TraceTower

section ReciprocityOrbit

/-- The orbit product which makes base-field Hilbert reciprocity tautological
in every selected Kummer arm.  If an odd-order symbol `A` is seen at the
`ell - 1` cyclotomic lifts as `A^a`, their product is one.  The range includes
`a = 0`, whose factor is harmless; it therefore represents the same product
as the nonzero residue classes modulo `ell`. -/
theorem odd_torsion_conjugate_product_eq_one {G : Type*} [CommGroup G]
    {ell : Nat} (hell : Odd ell) {A : G} (hA : A ^ ell = 1) :
    (∏ a ∈ Finset.range ell, A ^ a) = 1 := by
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]
  rcases hell with ⟨t, rfl⟩
  have hsub : 2 * t + 1 - 1 = 2 * t := by omega
  rw [hsub, Nat.mul_div_assoc _ (dvd_mul_right 2 t)]
  rw [Nat.mul_div_cancel_left t (by decide : 0 < 2), pow_mul, hA]
  simp

end ReciprocityOrbit

/-- The parity obstruction preventing a semiprimitive Gauss-sum evaluation
of the exceptional arm's surviving mixed character.  At a current prime,
the `ℓ`-component forces a minus-one Frobenius exponent to be congruent to
the odd half-order `h` modulo `2 * h`; the conductor-five component forces
the same exponent to be `2` modulo four.  These requirements cannot coexist.
-/
theorem no_mixed_semiprimitive_exponent {h t : Nat}
    (hh : Odd h) (hcurrent : t ≡ h [MOD 2 * h])
    (hfive : t ≡ 2 [MOD 4]) : False := by
  have hmod2odd : t ≡ h [MOD 2] :=
    hcurrent.of_dvd (by exact dvd_mul_right 2 h)
  have htodd : t % 2 = 1 := by
    rw [Nat.ModEq] at hmod2odd
    simpa [Nat.odd_iff.mp hh] using hmod2odd
  have hmod2even : t ≡ 2 [MOD 2] :=
    hfive.of_dvd (by norm_num)
  have hteven : t % 2 = 0 := by
    simpa [Nat.ModEq] using hmod2even
  omega

/-- Factorization of the degree-three norm exponent behind the exceptional
arm's selected norm collapse.  With `A = 2^(3^(k-1))`, the first factor
is `3 * Ψ_k`, so corestriction annihilates the entire current primary line. -/
theorem exceptional_norm_exponent_factorization (A : ℤ) :
    (A ^ 2 - A + 1) * (A ^ 2 + A + 1) = A ^ 4 + A ^ 2 + 1 := by
  ring

/-- Exact finite certificate for the small current prime used by the paper's
actual-degree Conway--Fermat Kummer countermodel. -/
theorem fermatNine_smallFactor_prime : Nat.Prime 2424833 := by
  native_decide

/-- The certified prime above is a divisor of `F₉ = 2^512 + 1`. -/
theorem fermatNine_smallFactor_dvd : 2424833 ∣ 2 ^ 512 + 1 := by
  native_decide

section FirstOrderProducts

variable {R ι : Type*} [CommRing R] [DecidableEq ι]

/-- Exact first-order multiplication in a square-zero direction.  This is
the algebraic core of the weighted Jacobi resolvents in the cubic and
exceptional arms: modulo the square of the local uniformizer, a product
remembers only the sum of its first coefficients. -/
theorem prod_one_sub_squareZero (ε : R) (hε : ε ^ 2 = 0)
    (s : Finset ι) (c : ι → R) :
    (∏ i ∈ s, (1 - ε * c i)) = 1 - ε * ∑ i ∈ s, c i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      calc
        (1 - ε * c a) * (1 - ε * ∑ i ∈ s, c i) =
            1 - ε * (c a + ∑ i ∈ s, c i) + ε ^ 2 * c a * ∑ i ∈ s, c i := by
              ring
        _ = 1 - ε * (c a + ∑ i ∈ s, c i) := by rw [hε]; simp

/-- An equal-weight first-order product is flat whenever its coefficient
sum vanishes.  Character orthogonality supplies this hypothesis for the
unweighted Hasse--Davenport products, so such products cannot decide the
selected Kummer coordinate. -/
theorem prod_one_sub_squareZero_eq_one (ε : R) (hε : ε ^ 2 = 0)
    (s : Finset ι) (c : ι → R) (hsum : ∑ i ∈ s, c i = 0) :
    (∏ i ∈ s, (1 - ε * c i)) = 1 := by
  rw [prod_one_sub_squareZero ε hε s c, hsum]
  simp

/-- Denominator-free first-order identity behind the exceptional arm's
canonical four-Jacobi detector.  The two positive conductor-five phases have
coefficient `C`, the two negative phases have coefficient `-C`, and their
cross product retains exactly `-4 * ε * C` modulo `ε²`. -/
theorem four_jacobi_cross_multiply (ε C : R) (hε : ε ^ 2 = 0) :
    (-1 + ε * C) ^ 2 =
      (1 - 4 * ε * C) * (-1 - ε * C) ^ 2 := by
  have hε3 : ε ^ 3 = 0 := by
    calc
      ε ^ 3 = ε ^ 2 * ε := by ring
      _ = 0 := by rw [hε]; simp
  ring_nf
  simp [hε, hε3]

/-- Denominator-free first-order identity behind the relative Eisenstein
detector.  If the two Eisenstein coordinates acquire tangent coefficients
`u₁,u₂`, their squared cross-ratio retains precisely the alternating
determinant `u₁*e₂-u₂*e₁`; no division or unit hypothesis is needed here. -/
theorem eisenstein_determinant_cross_multiply
    (ε e₁ e₂ u₁ u₂ : R) (hε : ε ^ 2 = 0) :
    (e₁ * (e₂ + ε * u₂)) ^ 2 =
      (e₂ * (e₁ + ε * u₁)) ^ 2 -
        2 * ε * e₁ * e₂ * (u₁ * e₂ - u₂ * e₁) := by
  ring_nf
  simp [hε]

/-- Characteristic-two factorization of the symmetric Berlekamp numerator
for a reciprocal cubic.  The selected cubic substitutes `D = C + 1`, making
this representative vanish; the paper explains why the auxiliary root
coordinate depends on cyclic orientation while this value is invariant. -/
theorem cubic_berlekamp_numerator_factorization
    (C D : R) (hchar : (2 : R) = 0) :
    C ^ 3 + D ^ 3 + C * D + 1 =
      (C + D + 1) * (C ^ 2 + C * D + D ^ 2 + C + D + 1) := by
  symm
  calc
    (C + D + 1) * (C ^ 2 + C * D + D ^ 2 + C + D + 1) =
        C ^ 3 + D ^ 3 + C * D + 1 +
          2 * (C + C ^ 2 + D + D ^ 2 + C * D + C * D ^ 2 + C ^ 2 * D) := by
            ring
    _ = C ^ 3 + D ^ 3 + C * D + 1 := by rw [hchar]; ring

/-- The Berlekamp numerator above is literally zero on the selected
reciprocal coefficient pair `(C,C+1)`. -/
theorem selected_cubic_berlekamp_numerator_zero
    (C : R) (hchar : (2 : R) = 0) :
    C ^ 3 + (C + 1) ^ 3 + C * (C + 1) + 1 = 0 := by
  calc
    C ^ 3 + (C + 1) ^ 3 + C * (C + 1) + 1 =
        2 * (1 + 2 * C + 2 * C ^ 2 + C ^ 3) := by ring
    _ = 0 := by rw [hchar]; simp

end FirstOrderProducts

section SelectorBridgeAlgebra

variable {K : Type*} [Field K]

/-- Algebraic core of the exceptional selector projection.  If the
coboundary is Nbar / N, then its fibotomic projection is the norm N*Nbar
divided by the square of the trace N+Nbar. -/
theorem coboundary_fibotomic_projection
    (N Nbar : K) (hN : N ≠ 0) (htrace : N + Nbar ≠ 0) :
    (Nbar / N) / (Nbar / N + 1) ^ 2 =
      (N * Nbar) / (N + Nbar) ^ 2 := by
  have hsum : Nbar + N ≠ 0 := by simpa [add_comm] using htrace
  rw [div_add_one hN]
  field_simp [hN, htrace, hsum]
  ring

/-- Dividing a monic quadratic relation by the square of its nonzero
linear coefficient gives the normalized Artin--Schreier equation used by
the C-to-D selector bridge. -/
theorem normalize_quadratic_to_artin_schreier
    (N g h : K) (hg : g ≠ 0) (hquad : N ^ 2 + g * N + h = 0) :
    (N / g) ^ 2 + N / g + h / g ^ 2 = 0 := by
  field_simp [hg]
  linear_combination hquad

variable {R : Type*} [CommRing R]

/-- Symmetric characteristic-two identity behind norm coherence of
g_k = gamma_k^2 + gamma_k + 1.  The hypotheses are the elementary
symmetric coefficients of the cubic X^3 + X + t. -/
theorem cubic_auxiliary_norm_coherence
    (x y z t : R) (hchar : (2 : R) = 0)
    (h₁ : x + y + z = 0)
    (h₂ : x * y + x * z + y * z = 1)
    (h₃ : x * y * z = t) :
    (x ^ 2 + x + 1) * (y ^ 2 + y + 1) * (z ^ 2 + z + 1) =
      t ^ 2 + t + 1 := by
  calc
    (x ^ 2 + x + 1) * (y ^ 2 + y + 1) * (z ^ 2 + z + 1) =
        (x + y + z) ^ 2 +
          (x + y + z) * (x * y + x * z + y * z) -
          (x + y + z) * (x * y * z) +
          (x + y + z) +
          (x * y + x * z + y * z) ^ 2 +
          (x * y + x * z + y * z) * (x * y * z) -
          (x * y + x * z + y * z) +
          (x * y * z) ^ 2 - 2 * (x * y * z) + 1 := by ring
    _ = t ^ 2 + t + 1 := by
      rw [h₁, h₂, h₃, hchar]
      ring

variable {F : Type*} [Field F] [CharP F 2]

/-- Denominator-free algebra behind the tower-faithful exceptional
countermodel.  For `w = 1 / (z + 1)`, the Artin--Schreier coefficient is
the inverse of `z + z⁻¹`, while the associated norm-one quotient is exactly
`z`.  In the paper `z` is the selected `3^(k+1)`-st root of unity. -/
theorem cyclotomic_artinSchreier_countermodel
    (z : F) (hz : z ≠ 0) (hz1 : z + 1 ≠ 0) :
    ((((z + 1)⁻¹) ^ 2 + (z + 1)⁻¹) * (z + z⁻¹) = 1) ∧
      (((z + 1)⁻¹ + 1) / (z + 1)⁻¹ = z) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  constructor <;> field_simp [hz, hz1] <;> ring_nf <;> simp [h2]

end SelectorBridgeAlgebra

section KummerNormCoherence

variable {G H : Type*} [CommMonoid G] [CommMonoid H]

/-- If `ell`-th powering is injective in the target, a multiplicative map
must send an `ell`-th root to the unique compatible `ell`-th root.  Applied
to finite-field norms, this is the algebraic core of the cubic arm's complete
lower-tower norm coherence. -/
theorem map_power_root_eq_of_injective
    (N : G →* H) (ell : Nat) (x z : G) (r z₀ : H)
    (hx : x ^ ell = z) (hz : N z = z₀) (hr : r ^ ell = z₀)
    (hinj : Function.Injective fun y : H ↦ y ^ ell) :
    N x = r := by
  apply hinj
  change (N x) ^ ell = r ^ ell
  rw [← map_pow, hx, hz, hr]

variable {R : Type*} [CommRing R]

/-- The three pair-products of roots of a monic cubic have elementary
coefficients `(D, C * E, E²)`.  This is the symmetric-algebra input to the
second generalized Dickson recurrence in the cubic Kummer descent. -/
theorem cubic_pair_product_coefficients
    (x y z C D E : R)
    (h₁ : x + y + z = C)
    (h₂ : x * y + x * z + y * z = D)
    (h₃ : x * y * z = E) :
    x * y + x * z + y * z = D ∧
      (x * y) * (x * z) + (x * y) * (y * z) + (x * z) * (y * z) = C * E ∧
      (x * y) * (x * z) * (y * z) = E ^ 2 := by
  refine ⟨h₂, ?_, ?_⟩
  · calc
      (x * y) * (x * z) + (x * y) * (y * z) + (x * z) * (y * z) =
          (x + y + z) * (x * y * z) := by ring
      _ = C * E := by rw [h₁, h₃]
  · calc
      (x * y) * (x * z) * (y * z) = (x * y * z) ^ 2 := by ring
      _ = E ^ 2 := by rw [h₃]

end KummerNormCoherence

section WeightedFrobeniusWords

variable {G : Type*} [CommMonoid G]

/-- A finite weighted Frobenius word is just exponentiation by the
evaluation of its group-ring exponent.  In the finite-field application
`r = 2`, so this is the algebraic core of the fact that orbit regulators
either erase a selected Kummer class or return a power of that same class. -/
theorem weighted_frobenius_word (x : G) (r : Nat)
    (s : Finset Nat) (w : Nat → Nat) :
    (∏ i ∈ s, (x ^ (r ^ i)) ^ (w i)) =
      x ^ (∑ i ∈ s, w i * r ^ i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih]
      rw [← pow_mul, ← pow_add]
      congr 1
      simp [Nat.mul_comm]

/-- Raising a weighted Frobenius word to an Euler-test exponent evaluates
the same word on the selected power-residue class `x ^ d`. -/
theorem weighted_frobenius_euler (x : G) (r d : Nat)
    (s : Finset Nat) (w : Nat → Nat) :
    ((∏ i ∈ s, (x ^ (r ^ i)) ^ (w i)) ^ d) =
      (x ^ d) ^ (∑ i ∈ s, w i * r ^ i) := by
  rw [weighted_frobenius_word]
  simp only [← pow_mul]
  congr 1
  exact Nat.mul_comm _ _

end WeightedFrobeniusWords

section CoprimePowerDetection

variable {G : Type*} [CommGroup G]

/-- On an element whose order divides `ell`, a power with exponent coprime
to `ell` detects the identity exactly.  This is the group-theoretic half of
the weighted-orbit dichotomy: a nonzero evaluation modulo a prime `ell`
cannot create an independent nonvanishing condition. -/
theorem pow_eq_one_iff_of_coprime (a : G) {ell e : Nat}
    (hell : a ^ ell = 1) (hcop : ell.Coprime e) :
    a ^ e = 1 ↔ a = 1 := by
  constructor
  · intro he
    have hdell : orderOf a ∣ ell := orderOf_dvd_iff_pow_eq_one.mpr hell
    have hde : orderOf a ∣ e := orderOf_dvd_iff_pow_eq_one.mpr he
    have hdgcd : orderOf a ∣ Nat.gcd ell e := Nat.dvd_gcd hdell hde
    have hgcd : Nat.gcd ell e = 1 := hcop.gcd_eq_one
    rw [hgcd] at hdgcd
    have hord : orderOf a = 1 := Nat.eq_one_of_dvd_one hdgcd
    exact orderOf_eq_one_iff.mp hord
  · intro ha
    simp [ha]

/-- If the evaluated weight is coprime to `ell`, the Euler test of a
weighted Frobenius word is trivial exactly when the original selected
Euler class is trivial. -/
theorem weighted_frobenius_euler_eq_one_iff (x : G) (r d ell : Nat)
    (s : Finset Nat) (w : Nat → Nat)
    (hell : (x ^ d) ^ ell = 1)
    (hcop : ell.Coprime (∑ i ∈ s, w i * r ^ i)) :
    ((∏ i ∈ s, (x ^ (r ^ i)) ^ (w i)) ^ d = 1) ↔ x ^ d = 1 := by
  rw [weighted_frobenius_euler]
  exact pow_eq_one_iff_of_coprime (x ^ d) hell hcop

end CoprimePowerDetection

section DepressedDicksonCubic

variable {R : Type*} [CommRing R] [CharP R 2]

/-- Algebraic core of the exceptional arm's depressed-cubic no-go.  In
characteristic two, every trace--constant cubic becomes an Artin--Schreier
cubic after translating by its quadratic coefficient and scaling the variable.
The theorem is denominator-free; when `delta` is a unit, division by its cube
gives the normalized equation used in the paper. -/
theorem dickson_cubic_depresses (a b δ U : R)
    (hδ : δ ^ 2 = a ^ 2 + b) :
    (δ * U + a) ^ 3 + a * (δ * U + a) ^ 2 + b * (δ * U + a) + a ^ 2 =
      δ ^ 3 * (U ^ 3 + U) + (a * b + a ^ 2) := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have h4 : (4 : R) = 0 := by
    calc
      (4 : R) = 2 + 2 := by norm_num
      _ = 0 := by rw [h2]; simp
  have h5 : (5 : R) = 1 := by
    calc
      (5 : R) = 4 + 1 := by norm_num
      _ = 1 := by rw [h4]; simp
  calc
    (δ * U + a) ^ 3 + a * (δ * U + a) ^ 2 + b * (δ * U + a) + a ^ 2 =
        δ ^ 3 * U ^ 3 + δ * U * (a ^ 2 + b) + (a * b + a ^ 2) := by
          ring_nf
          simp [h2, h4, h5]
    _ = δ ^ 3 * (U ^ 3 + U) + (a * b + a ^ 2) := by rw [← hδ]; ring

end DepressedDicksonCubic

section DicksonTraceConstantFactorization

variable {K : Type*} [Field K] [CharP K 2]

/-- Denominator-free kernel check of the four-axis factorization used to
show that a trace--constant reciprocal cubic comes from the smaller Dickson
torus.  In the paper `x`, `u`, and `v` are three successive Frobenius
conjugates of a reciprocal root. -/
theorem trace_constant_torus_factorization (x u v : K)
    (hx : x ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    (x + x⁻¹) * (u + u⁻¹) * (v + v⁻¹) +
        ((x + x⁻¹) + (u + u⁻¹) + (v + v⁻¹)) ^ 2 =
      ((u + x * v) * (v + x * u) * (x + u * v) * (1 + x * u * v)) /
        (x ^ 2 * u ^ 2 * v ^ 2) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h6 : (6 : K) = 0 := by
    calc
      (6 : K) = 3 * 2 := by norm_num
      _ = 0 := by rw [h2]; simp
  field_simp
  ring_nf
  simp [h2, h6]

end DicksonTraceConstantFactorization

section RelativeTraceAxes

variable {K : Type*} [Field K] [CharP K 2]

/-- Additivity of the Artin--Schreier map in characteristic two.  This is
the algebraic identity behind the centered relative-trace collision in the
singleton-even arm. -/
theorem artinSchreier_add (x y : K) :
    (x ^ 2 + x) + (y ^ 2 + y) = (x + y) ^ 2 + (x + y) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ring_nf
  simp [h2]

omit [CharP K 2] in
/-- Centering two transported torus points turns their additive collision
coordinate into the Mobius coordinate of their ratio. -/
theorem centered_ratio_identity (alpha beta : K) (hbeta : beta ≠ 0)
    (hsum : alpha + beta ≠ 0) :
    alpha / (alpha + beta) = (alpha / beta) / (alpha / beta + 1) := by
  field_simp

/-- The Mobius coordinate `rho / (rho + 1)` is fixed by a field
endomorphism exactly when `rho` is fixed.  In the finite-field application
this is the half-field axis of a relative-trace collision. -/
theorem mobius_fixed_iff (sigma : K →+* K) (rho : K) (hrho : rho ≠ 1) :
    sigma (rho / (rho + 1)) = rho / (rho + 1) <-> sigma rho = rho := by
  have hden : rho + 1 ≠ 0 := by
    intro h
    apply hrho
    have : rho = -1 := eq_neg_of_add_eq_zero_left h
    simpa [CharTwo.neg_eq] using this
  have hsigma : sigma rho ≠ 1 := by
    intro h
    apply hrho
    apply sigma.injective
    simpa using h
  have hsden : sigma rho + 1 ≠ 0 := by
    intro h
    apply hsigma
    have : sigma rho = -1 := eq_neg_of_add_eq_zero_left h
    simpa [CharTwo.neg_eq] using this
  rw [map_div₀, map_add, map_one]
  constructor
  · intro h
    have hcross := (div_eq_div_iff hsden hden).mp h
    linear_combination hcross
  · intro h
    rw [h]

/-- The other Mobius collision axis: conjugation sends the centered
coordinate to its Artin--Schreier mate exactly when the underlying ratio
has norm one. -/
theorem mobius_mate_iff (sigma : K →+* K) (rho : K) (hrho : rho ≠ 1) :
    sigma (rho / (rho + 1)) = rho / (rho + 1) + 1 <->
      sigma rho * rho = 1 := by
  have hden : rho + 1 ≠ 0 := by
    intro h
    apply hrho
    have : rho = -1 := eq_neg_of_add_eq_zero_left h
    simpa [CharTwo.neg_eq] using this
  have hsigma : sigma rho ≠ 1 := by
    intro h
    apply hrho
    apply sigma.injective
    simpa using h
  have hsden : sigma rho + 1 ≠ 0 := by
    intro h
    apply hsigma
    have : sigma rho = -1 := eq_neg_of_add_eq_zero_left h
    simpa [CharTwo.neg_eq] using this
  have hmate : rho / (rho + 1) + 1 = 1 / (rho + 1) := by
    field_simp [hden]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [map_div₀, map_add, map_one, hmate]
  constructor
  · intro h
    have hcross := (div_eq_div_iff hsden hden).mp h
    linear_combination hcross
  · intro h
    apply (div_eq_div_iff hsden hden).mpr
    linear_combination h

end RelativeTraceAxes

section ConwayFermatTwoStep

variable {R : Type*} [CommRing R] [CharP R 2]

/-- Eliminating the intermediate Conway value from two consecutive
Artin--Schreier transitions gives the sparse quartic used in the
singleton-even arm's two-step Kummer dichotomy. -/
theorem conwayFermat_twoStep_quartic (b a c : R)
    (ha : a ^ 2 + b * a + b ^ 3 = 0)
    (hc : c ^ 2 + c + a = 0) :
    c ^ 4 + (b + 1) * c ^ 2 + b * c + b ^ 3 = 0 := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have ha' : a = c ^ 2 + c := by
    calc
      a = a + ((c ^ 2 + c) + (c ^ 2 + c)) := by
        rw [CharTwo.add_self_eq_zero, add_zero]
      _ = (c ^ 2 + c + a) + (c ^ 2 + c) := by ac_rfl
      _ = c ^ 2 + c := by rw [hc, zero_add]
  rw [ha'] at ha
  ring_nf at ha ⊢
  simp [h2] at ha ⊢
  exact ha

/-- If a bad two-step factor is obtained by multiplying the conjugate
quadratics `X^2 + s X + r` and `X^2 + s' X + r'`, its three
nonconstant coefficients lie on an exact characteristic-two conic.
In the Conway--Fermat application the inverse formula recovers `s`, so
this conic is a lossless coordinate model of the existing Dickson fibre,
not an additional obstruction. -/
theorem quarticFactor_coefficient_conic (s s' r r' : R) :
    let A := s + s'
    let e := r + r'
    let B := e + s * s'
    let C := s * r' + s' * r
    let d := r * r'
    C ^ 2 + A * e * C + A ^ 2 * d = e ^ 2 * (B + e) := by
  dsimp
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have h6 : (6 : R) = 0 := by
    calc
      (6 : R) = 3 * 2 := by norm_num
      _ = 3 * 0 := by rw [h2]
      _ = 0 := by simp
  ring_nf
  simp [h2, h6]

end ConwayFermatTwoStep

/-- The group-theoretic content of the exceptional lower bound.  The paper's
half-angle splitting puts the first four translates in one order class `A`;
if `p` is coprime to `A`, all four are `p`-th powers. -/
theorem roots_below_four_of_shared_order_class {G : Type*} [Group G]
    {p A : Nat} {β : Nat → G} (hcop : A.Coprime p)
    (horder : ∀ j < 4, orderOf (β j) ∣ A) :
    ∀ j < 4, IsPthPower p (β j) := by
  intro j hj
  exact isPthPower_of_coprime_order (hcop.of_dvd_left (horder j hj))

/-- The unconditional lower-bound interface: if the first four translates
have roots, the excess cannot occur below four. -/
theorem excess_not_below_four {K : Type*} [Monoid K] {p : Nat} {β : Nat → K}
    (hroot : ∀ j < 4, IsPthPower p (β j)) :
    ∀ m < 4, ¬HasExcessAt p β m := by
  intro m hm hexcess
  exact hexcess.2 (hroot m hm)

/-- The unconditional `m_p ≥ 4` theorem in the order-class form supplied by
the cyclotomic/half-angle argument. -/
theorem exceptional_lower_bound {G : Type*} [Group G] {p A : Nat} {β : Nat → G}
    (hcop : A.Coprime p) (horder : ∀ j < 4, orderOf (β j) ∣ A) :
    ∀ m < 4, ¬HasExcessAt p β m :=
  excess_not_below_four (roots_below_four_of_shared_order_class hcop horder)

/-- Once the unconditional roots at `0,1,2,3` are supplied, the exact
exceptional-column assertion is precisely nonexistence of a root at `4`. -/
theorem hasExcessAt_four_iff {K : Type*} [Monoid K] {p : Nat} {β : Nat → K}
    (hroot : ∀ j < 4, IsPthPower p (β j)) :
    HasExcessAt p β 4 ↔ ¬IsPthPower p (β 4) := by
  exact and_iff_right hroot

section CorrectedNorm

variable {K : Type*} [CommRing K] [CharP K 2]

/-- The corrected norm identity.  If the relative Frobenius sends `a` to
`a + 1`, then the norm of `κ + a` is the sparse element on the right.  In the
nimber application `a = 4` and `a² + a = ω = κ²`. -/
theorem corrected_norm_identity (κ a : K) :
    (κ + a) * (κ + (a + 1)) = κ ^ 2 + κ + (a ^ 2 + a) := by
  have ha : a + a = 0 := CharTwo.add_self_eq_zero a
  calc
    (κ + a) * (κ + (a + 1)) =
        κ ^ 2 + κ * (a + a + 1) + (a ^ 2 + a) := by ring
    _ = κ ^ 2 + κ + (a ^ 2 + a) := by rw [ha]; simp

/-- Sparse form used in the exceptional column, after identifying the
Artin–Schreier constant `a² + a` with `ω`. -/
theorem corrected_norm_sparse (κ a ω : K) (hω : a ^ 2 + a = ω) :
    (κ + a) * (κ + (a + 1)) = κ ^ 2 + κ + ω := by
  rw [corrected_norm_identity, hω]

/-- Norm packaging for the actual conjugacy hypothesis. -/
theorem corrected_norm_of_conjugate {F : Type*} [Field F] [CharP F 2]
    (σ : F ≃+* F) (κ a : F) (hκ : σ κ = κ) (ha : σ a = a + 1) :
    (κ + a) * σ (κ + a) = κ ^ 2 + κ + (a ^ 2 + a) := by
  rw [map_add, hκ, ha]
  exact corrected_norm_identity κ a

end CorrectedNorm

section PowerCriterion

variable {F : Type*} [Field F] [Fintype F]

/-- Exact finite-field power criterion for a nonzero element.  This is the
cyclic-group equivalence behind the paper's in-field `m = 4` test. -/
theorem isPthPower_iff_pow_card_sub_one_div_eq_one {p : Nat} {a : F}
    (ha : a ≠ 0) (hp : p ∣ Fintype.card F - 1) :
    IsPthPower p a ↔ a ^ ((Fintype.card F - 1) / p) = 1 := by
  classical
  let au : Fˣ := Units.mk0 a ha
  have hpUnits : p ∣ Fintype.card Fˣ := by
    simpa [Fintype.card_units] using hp
  have hcriterion := isPthPower_iff_pow_card_div_eq_one hpUnits au
  rw [Fintype.card_units] at hcriterion
  constructor
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro hxzero
      apply ha
      rw [← hx, hxzero]
      have hp0 : p ≠ 0 := by
        intro hpzero
        subst p
        simp at hp
        have hcard : 1 < Fintype.card F := Fintype.one_lt_card
        omega
      simp [hp0]
    let xu : Fˣ := Units.mk0 x hx0
    have hxu : IsPthPower p au := by
      refine ⟨xu, Units.ext ?_⟩
      simpa [xu, au] using hx
    have := hcriterion.mp hxu
    simpa [au] using congrArg Units.val this
  · intro hpow
    have hau : au ^ ((Fintype.card F - 1) / p) = 1 := by
      apply Units.ext
      simpa [au] using hpow
    obtain ⟨x, hx⟩ := hcriterion.mpr hau
    refine ⟨(x : F), ?_⟩
    simpa [au] using congrArg Units.val hx

/-- Exact order form of the finite-field criterion.  In particular, when `p`
is prime, a nonzero selected value is not a `p`-th power precisely when its
multiplicative order contains the full `p`-primary part available in the
ambient field. -/
theorem isPthPower_iff_orderOf_dvd_card_sub_one_div {p : Nat} {a : F}
    (ha : a ≠ 0) (hp : p ∣ Fintype.card F - 1) :
    IsPthPower p a ↔ orderOf a ∣ (Fintype.card F - 1) / p := by
  rw [isPthPower_iff_pow_card_sub_one_div_eq_one ha hp]
  exact orderOf_dvd_iff_pow_eq_one.symm

/-- Negated finite-field order criterion, the exact nonvanishing obligation
left in each selected Conway/Kummer arm. -/
theorem not_isPthPower_iff_not_orderOf_dvd_card_sub_one_div {p : Nat} {a : F}
    (ha : a ≠ 0) (hp : p ∣ Fintype.card F - 1) :
    ¬IsPthPower p a ↔ ¬orderOf a ∣ (Fintype.card F - 1) / p := by
  exact not_congr (isPthPower_iff_orderOf_dvd_card_sub_one_div ha hp)

/-- The easy direction of the finite-field power criterion, with all
divisibility explicit.  It is the direction used by a certificate: a nontrivial
Euler quotient rules out a `p`-th root. -/
theorem not_isPthPower_of_pow_ne_one {p : Nat} {a : F}
    (ha : a ≠ 0) (hp0 : p ≠ 0) (hp : p ∣ Fintype.card F - 1)
    (hpow : a ^ ((Fintype.card F - 1) / p) ≠ 1) :
    ¬IsPthPower p a := by
  rintro ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply ha
    rw [← hx, hxzero]
    simp [hp0]
  apply hpow
  calc
    a ^ ((Fintype.card F - 1) / p) =
        (x ^ p) ^ ((Fintype.card F - 1) / p) := by rw [hx]
    _ = x ^ (p * ((Fintype.card F - 1) / p)) := by rw [pow_mul]
    _ = x ^ (Fintype.card F - 1) := by rw [Nat.mul_div_cancel' hp]
    _ = 1 := FiniteField.pow_card_sub_one_eq_one x hx0

/-- A finite-field power certificate closes the `m = 4` claim once the
unconditional roots below four have been established. -/
theorem hasExcessAt_four_of_power_certificate {p : Nat} {β : Nat → F}
    (hroot : ∀ j < 4, IsPthPower p (β j))
    (hβ : β 4 ≠ 0) (hp0 : p ≠ 0) (hp : p ∣ Fintype.card F - 1)
    (hpow : (β 4) ^ ((Fintype.card F - 1) / p) ≠ 1) :
    HasExcessAt p β 4 := by
  exact ⟨hroot, not_isPthPower_of_pow_ne_one hβ hp0 hp hpow⟩

end PowerCriterion

/-- The exact universal exceptional-column target after the reductions in the
paper.  `M k` is the circle element `N^(2^(3^k)-1)` and `Ψ k` is
`Φ_(2*3^k)(2)/3`. -/
def ExceptionalColumnTarget {G : Type*} [Monoid G]
    (Ψ : Nat → Nat) (M : Nat → G) : Prop :=
  ∀ k ≥ 1, Ψ k ∣ orderOf (M k)

section ArithmeticCertificates

/-- `Φ_(2*3^k)(2)` in its sparse closed form.  The development only uses
this at positive `k`; the total definition keeps certificate evaluation
simple. -/
def exceptionalCyclotomicValue (k : Nat) : Nat :=
  2 ^ (2 * 3 ^ (k - 1)) - 2 ^ (3 ^ (k - 1)) + 1

/-- The prime-to-three current factor from the paper. -/
def psi (k : Nat) : Nat :=
  exceptionalCyclotomicValue k / 3

/-- The paper's exact open statement `D'_k : Ψ_k ∣ ord(M_k)` with the
cyclotomic current factor fixed by `psi`. -/
def DPrimeTarget {G : Type*} [Monoid G] (M : Nat → G) : Prop :=
  ExceptionalColumnTarget psi M

/-- The locally recorded complete factor lists for `k = 2,...,6`.  At `k=6`
the final 78-digit factor's primality remains source-assisted, exactly as in
the Python certificate and paper. -/
def certifiedFactors : Nat → List Nat
  | 2 => [19]
  | 3 => [87211]
  | 4 => [163, 135433, 272010961]
  | 5 => [1459, 139483, 10429407431911334611, 918125051602568899753]
  | 6 => [
      227862073,
      3110690934667,
      216892513252489863991753,
      1102099161075964924744009,
      393063301203384521164229656203691748263012766081190297429488962985651210769817]
  | _ => []

/-- A directly decidable screen for `ord_p(2) = 2*3^k`: the full exponent
works, while division by either prime divisor of the exponent does not. -/
def ExactTwoThreePowerResidue (p k : Nat) : Prop :=
  2 ^ (2 * 3 ^ k) % p = 1 ∧
  2 ^ (3 ^ k) % p ≠ 1 ∧
  2 ^ (2 * 3 ^ (k - 1)) % p ≠ 1

instance (p k : Nat) : Decidable (ExactTwoThreePowerResidue p k) := by
  unfold ExactTwoThreePowerResidue
  infer_instance

/-- A divisor of `2*3^k` which disappears after division by either prime
factor is the whole number.  This is the elementary arithmetic behind the
two-exponent residue screen. -/
theorem eq_two_mul_three_pow_of_dvd {d k : Nat} (hk : 1 ≤ k)
    (hd : d ∣ 2 * 3 ^ k) (hnot2 : ¬d ∣ 3 ^ k)
    (hnot3 : ¬d ∣ 2 * 3 ^ (k - 1)) :
    d = 2 * 3 ^ k := by
  have h2d : 2 ∣ d := by
    by_contra h2d
    have hcop : d.Coprime 2 :=
      ((Nat.prime_two.coprime_iff_not_dvd.mpr h2d).symm)
    exact hnot2 (hcop.dvd_of_dvd_mul_left hd)
  obtain ⟨e, rfl⟩ := h2d
  have he : e ∣ 3 ^ k :=
    (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hd
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp he
  have hjpred : ¬j ≤ k - 1 := by
    intro hjpred
    apply hnot3
    exact Nat.mul_dvd_mul_left 2 (pow_dvd_pow 3 hjpred)
  have : j = k := by omega
  rw [this]

/-- The corresponding exact-order theorem in any monoid.  Thus the two
proper-divisor failures in `ExactTwoThreePowerResidue` are sufficient, rather
than an exhaustive divisor search. -/
theorem orderOf_eq_two_mul_three_pow {G : Type*} [Monoid G] {a : G} {k : Nat}
    (hk : 1 ≤ k) (hfull : a ^ (2 * 3 ^ k) = 1)
    (hhalf2 : a ^ (3 ^ k) ≠ 1)
    (hhalf3 : a ^ (2 * 3 ^ (k - 1)) ≠ 1) :
    orderOf a = 2 * 3 ^ k := by
  apply eq_two_mul_three_pow_of_dvd hk
  · exact orderOf_dvd_iff_pow_eq_one.mpr hfull
  · intro hdvd
    exact hhalf2 (orderOf_dvd_iff_pow_eq_one.mp hdvd)
  · intro hdvd
    exact hhalf3 (orderOf_dvd_iff_pow_eq_one.mp hdvd)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 2000 in
/-- Lean-kernel arithmetic check that the recorded lists reconstruct the
entire cyclotomic value at every fully factored level.  This certifies the
product identities, not primality of the factors. -/
theorem certified_factorizations :
    (∀ k ∈ ([2, 3, 4, 5, 6] : List Nat),
      3 * (certifiedFactors k).prod = exceptionalCyclotomicValue k) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 2000 in
/-- The same complete product checks after removing the unique factor `3`. -/
theorem certified_psi_products :
    (∀ k ∈ ([2, 3, 4, 5, 6] : List Nat),
      (certifiedFactors k).prod = psi k) := by
  decide

/-- The modest-size factors through `k=4` also have primality proofs reduced
inside Lean.  Larger factor primality deliberately retains the paper's
source-assisted boundary instead of making the routine build perform a long
probable-prime search. -/
theorem locally_certified_primes_through_k4 :
    Nat.Prime 19 ∧ Nat.Prime 87211 ∧ Nat.Prime 163 ∧
      Nat.Prime 135433 ∧ Nat.Prime 272010961 := by
  norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 2000 in
/-- Every recorded factor passes the exact `2*3^k` residue screen.  Combined
with the separately sourced primality certificates, this is the order-of-two
part of the finite column certification. -/
theorem certified_order_screens :
    ExactTwoThreePowerResidue 19 2 ∧
    ExactTwoThreePowerResidue 87211 3 ∧
    ExactTwoThreePowerResidue 163 4 ∧
    ExactTwoThreePowerResidue 135433 4 ∧
    ExactTwoThreePowerResidue 272010961 4 ∧
    ExactTwoThreePowerResidue 1459 5 ∧
    ExactTwoThreePowerResidue 139483 5 ∧
    ExactTwoThreePowerResidue 10429407431911334611 5 ∧
    ExactTwoThreePowerResidue 918125051602568899753 5 ∧
    ExactTwoThreePowerResidue 227862073 6 ∧
    ExactTwoThreePowerResidue 3110690934667 6 ∧
    ExactTwoThreePowerResidue 216892513252489863991753 6 ∧
    ExactTwoThreePowerResidue 1102099161075964924744009 6 ∧
    ExactTwoThreePowerResidue
      393063301203384521164229656203691748263012766081190297429488962985651210769817 6 := by
  decide

end ArithmeticCertificates

end Ogdoad.Excess
