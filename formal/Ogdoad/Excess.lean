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
