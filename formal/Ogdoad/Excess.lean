import Mathlib

/-!
# The exceptional Lenstra-excess column

This file formalizes the algebraic spine of the `2 * 3^k` column from
`writeups/excess.tex` and `experiments/exception_column_m4.py`.

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
