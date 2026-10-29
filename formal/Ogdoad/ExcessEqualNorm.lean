import Ogdoad.Excess

/-!
# Equal half-norms in two odd Kummer towers

The algebraic mechanism used in the repeated-radicand obstruction to the
zero arm. Besides the characteristic-two sum identity, this file checks
half-norm synchronization along an odd Kummer tower from explicit Frobenius
periods and coprimality. Identifying the literal Conway components and their
finite-field degrees remains a separate input.
-/

namespace Ogdoad.Excess

section EqualNorm

variable {F : Type*} [Field F] [CharP F 2]

/-- Two elements with the same half-norm have an explicitly controlled
Frobenius quotient after addition. -/
theorem equal_half_norm_sum_quotient
    (x y w : F) (d : ℕ)
    (hx : x ^ (2 ^ d + 1) = w) (hy : y ^ (2 ^ d + 1) = w)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hz0 : x + y ≠ 0) :
    (x + y) ^ (2 ^ d - 1) = w / (x * y) := by
  have hfrob : (x + y) ^ (2 ^ d) = x ^ (2 ^ d) + y ^ (2 ^ d) := by
    simpa using add_pow_expChar_pow x y 2 d
  have hqx : x ^ (2 ^ d) * x = w := by simpa [pow_succ] using hx
  have hqy : y ^ (2 ^ d) * y = w := by simpa [pow_succ] using hy
  have hprod : (x + y) ^ (2 ^ d) * (x * y) = w * (x + y) := by
    rw [hfrob]
    calc
      (x ^ (2 ^ d) + y ^ (2 ^ d)) * (x * y) =
          (x ^ (2 ^ d) * x) * y + (y ^ (2 ^ d) * y) * x := by ring
      _ = w * (x + y) := by rw [hqx, hqy]; ring
  apply (eq_div_iff (mul_ne_zero hx0 hy0)).2
  apply (mul_right_cancel₀ hz0)
  calc
    ((x + y) ^ (2 ^ d - 1) * (x * y)) * (x + y) =
        ((x + y) ^ (2 ^ d - 1) * (x + y)) * (x * y) := by ring
    _ = (x + y) ^ (2 ^ d) * (x * y) := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow d 2 (by decide))]
    _ = w * (x + y) := hprod

/-- The ratio of two elements with the same half-norm is unitary; its
inversion-invariant trace belongs to the half-field. -/
theorem equal_half_norm_ratio_trace_fixed
    (x y w : F) (d : ℕ)
    (hx : x ^ (2 ^ d + 1) = w) (hy : y ^ (2 ^ d + 1) = w)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    (x / y + y / x) ^ (2 ^ d) = x / y + y / x := by
  have hw0 : w ≠ 0 := by rw [← hx]; exact pow_ne_zero _ hx0
  have hxq : x ^ (2 ^ d) = w / x := by
    apply (eq_div_iff hx0).2
    simpa [pow_succ] using hx
  have hyq : y ^ (2 ^ d) = w / y := by
    apply (eq_div_iff hy0).2
    simpa [pow_succ] using hy
  rw [add_pow_expChar_pow (x / y) (y / x) 2 d, div_pow, div_pow, hxq, hyq]
  field_simp
  ring

/-- The sum's square factors as the two original components and their
ratio trace. With equal half-norms, the third factor lies in the half-field,
giving a factorization through three proper subfields. -/
theorem sum_sq_eq_mul_ratio_trace
    (x y : F) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    (x + y) ^ 2 = x * y * (x / y + y / x) := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  field_simp
  ring_nf
  simp [htwo]

/-- Equal half-norms force the sum to be a `p`-th power when both summands
and the common norm are `p`-th powers, provided the half-Frobenius exponent
minus one is coprime to `p`. This retains the full primary valuation through
the exact finite-field Euler criterion. -/
theorem equal_half_norm_sum_isPthPower
    [Fintype F] (x y w : F) (d p : ℕ)
    (hx : x ^ (2 ^ d + 1) = w) (hy : y ^ (2 ^ d + 1) = w)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hw0 : w ≠ 0) (hz0 : x + y ≠ 0)
    (hp : p ∣ Fintype.card F - 1) (hpe : p.Coprime (2 ^ d - 1))
    (hxp : IsPthPower p x) (hyp : IsPthPower p y)
    (hwp : IsPthPower p w) :
    IsPthPower p (x + y) := by
  let m := (Fintype.card F - 1) / p
  have hxm : x ^ m = 1 :=
    (isPthPower_iff_pow_card_sub_one_div_eq_one hx0 hp).mp hxp
  have hym : y ^ m = 1 :=
    (isPthPower_iff_pow_card_sub_one_div_eq_one hy0 hp).mp hyp
  have hwm : w ^ m = 1 :=
    (isPthPower_iff_pow_card_sub_one_div_eq_one hw0 hp).mp hwp
  have hrel := equal_half_norm_sum_quotient x y w d hx hy hx0 hy0 hz0
  have hem : ((x + y) ^ m) ^ (2 ^ d - 1) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hrel, div_pow, mul_pow,
      hxm, hym, hwm]
    simp
  have hpm : ((x + y) ^ m) ^ p = 1 := by
    rw [← pow_mul, show m * p = Fintype.card F - 1 from Nat.div_mul_cancel hp]
    exact FiniteField.pow_card_sub_one_eq_one (x + y) hz0
  apply (isPthPower_iff_pow_card_sub_one_div_eq_one hz0 hp).mpr
  exact (_root_.pow_eq_one_iff_of_coprime hpe).mp ⟨hpm, hem⟩

end EqualNorm

/-- The quotient supplied by equal half-norms is a power whenever its three
factors are powers. Raising by a coprime exponent then recovers the power
class of the original sum. -/
theorem isPthPower_of_power_eq_quotient
    {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G]
    (z x y w : G) (p e : ℕ)
    (hp : p ∣ Fintype.card G) (hpe : p.Coprime e)
    (hrel : z ^ e = w / (x * y))
    (hx : IsPthPower p x) (hy : IsPthPower p y)
    (hw : IsPthPower p w) :
    IsPthPower p z := by
  apply (isPthPower_pow_iff_of_coprime hp hpe z).mp
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  obtain ⟨c, rfl⟩ := hw
  refine ⟨c / (a * b), ?_⟩
  rw [hrel, div_pow, mul_pow]

/-- Uniqueness of a root with a known period. In the repeated-radicand
construction `t` is the half-norm of a higher Kummer component, while `w`
is the half-norm of the shared bottom radicand. The exponent is chosen to
act trivially on `w`, and is coprime to the half-field unit-group order. -/
theorem radical_eq_of_coprime_period
    {G : Type*} [CommGroup G] (t w : G) (R N : ℕ)
    (hcop : R.Coprime N)
    (htR : t ^ R = w) (hwR : w ^ R = w)
    (htN : t ^ N = 1) (hwN : w ^ N = 1) :
    t = w := by
  have hR : (t / w) ^ R = 1 := by rw [div_pow, htR, hwR]; simp
  have hN : (t / w) ^ N = 1 := by rw [div_pow, htN, hwN]; simp
  exact div_eq_one.mp ((_root_.pow_eq_one_iff_of_coprime hcop).mp ⟨hR, hN⟩)

/-- The chosen common tower level fixes every possible lower norm as soon
as its exponent is congruent to one modulo the lower-field group order. -/
theorem pow_eq_self_of_modEq_one
    {G : Type*} [Monoid G] (w : G) (R M : ℕ)
    (hw : w ^ M = 1) (hR : Nat.ModEq M R 1) :
    w ^ R = w := by
  simpa using (pow_eq_pow_of_modEq hR hw : w ^ R = w ^ 1)

/-- A binary Frobenius period remains a period at every multiple. The
identity only involves powers, so no characteristic assumption is needed. -/
theorem binary_frobenius_period_mul
    {G : Type*} [Monoid G] (z : G) (b k : ℕ)
    (hz : z ^ (2 ^ b) = z) :
    z ^ (2 ^ (b * k)) = z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih, hz]

/-- An odd number of half-periods has the same action as one half-period. -/
theorem binary_half_frobenius_of_odd
    {G : Type*} [Monoid G] (z : G) (b R : ℕ)
    (hz : z ^ (2 ^ (2 * b)) = z) (hR : Odd R) :
    z ^ (2 ^ (b * R)) = z ^ (2 ^ b) := by
  obtain ⟨k, hk⟩ := hR
  have he : b * R = (2 * b) * k + b := by rw [hk]; ring
  rw [he, pow_add, pow_mul, binary_frobenius_period_mul z (2 * b) k hz]

/-- Extending a quadratic ambient field by an odd degree preserves the
half-norm of an element already in the original field. -/
theorem odd_extension_preserves_half_norm
    {G : Type*} [Monoid G] (z : G) (b S : ℕ)
    (hz : z ^ (2 ^ (2 * b)) = z) (hS : Odd S) :
    z ^ (2 ^ (b * S) + 1) = z ^ (2 ^ b + 1) := by
  rw [pow_succ, binary_half_frobenius_of_odd z b S hz hS, ← pow_succ]

/-- A quadratic norm is fixed by the half-Frobenius. -/
theorem quadratic_norm_fixed
    {G : Type*} [CommMonoid G] (z : G) (q : ℕ)
    (hz : z ^ (q ^ 2) = z) :
    (z ^ (q + 1)) ^ q = z ^ (q + 1) := by
  rw [← pow_mul, show (q + 1) * q = q ^ 2 + q by ring,
    pow_add, hz, pow_succ, mul_comm]

/-- A nonzero Frobenius-fixed element has the corresponding multiplicative
period, including the degenerate period zero when `q=1`. -/
theorem power_pred_eq_one_of_fixed
    {G : Type*} [GroupWithZero G] (z : G) (q : ℕ)
    (hz0 : z ≠ 0) (hq : 1 ≤ q) (hz : z ^ q = z) :
    z ^ (q - 1) = 1 := by
  apply mul_right_cancel₀ hz0
  rw [← pow_succ, Nat.sub_add_cancel hq, hz, one_mul]

/-- The complete norm-synchronization step for one selected odd Kummer
tower. The base element has degree dividing `2b`, the component has degree
dividing `2bR`, and its `R`-th power is the shared radicand. Coprimality makes
the upper half-norm's `R`-th root unique; the congruence forces that root to
be the lower half-norm itself. -/
theorem kummer_half_norm_synchronized
    {F : Type*} [Field F] (x α : F) (b R : ℕ)
    (hx0 : x ≠ 0) (hroot : x ^ R = α)
    (hα : α ^ (2 ^ (2 * b)) = α)
    (hx : x ^ (2 ^ (2 * b * R)) = x)
    (hR : Odd R) (hcop : R.Coprime (2 ^ (b * R) - 1))
    (hcong : Nat.ModEq (2 ^ b - 1) R 1) :
    x ^ (2 ^ (b * R) + 1) = α ^ (2 ^ b + 1) := by
  let q := 2 ^ (b * R)
  let q₀ := 2 ^ b
  let t := x ^ (q + 1)
  let w := α ^ (q₀ + 1)
  have hα0 : α ≠ 0 := by rw [← hroot]; exact pow_ne_zero _ hx0
  have ht0 : t ≠ 0 := pow_ne_zero _ hx0
  have hw0 : w ≠ 0 := pow_ne_zero _ hα0
  have hq : 1 ≤ q := Nat.one_le_pow (b * R) 2 (by decide)
  have hq₀ : 1 ≤ q₀ := Nat.one_le_pow b 2 (by decide)
  have hqsq : q ^ 2 = 2 ^ (2 * b * R) := by
    dsimp [q]
    rw [← pow_mul]
    congr 1
    ring
  have hq₀sq : q₀ ^ 2 = 2 ^ (2 * b) := by
    dsimp [q₀]
    rw [← pow_mul, Nat.mul_comm b 2]
  have htfix : t ^ q = t := by
    apply quadratic_norm_fixed x q
    rw [hqsq, hx]
  have hwfix : w ^ q₀ = w := by
    apply quadratic_norm_fixed α q₀
    rw [hq₀sq, hα]
  have htR : t ^ R = w := by
    calc
      t ^ R = (x ^ R) ^ (q + 1) := by
        dsimp [t]
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (q + 1) R]
      _ = α ^ (q + 1) := by rw [hroot]
      _ = w := by
        dsimp [w, q, q₀]
        rw [pow_succ, binary_half_frobenius_of_odd α b R hα hR, ← pow_succ]
  have htN : t ^ (q - 1) = 1 := power_pred_eq_one_of_fixed t q ht0 hq htfix
  have hwM : w ^ (q₀ - 1) = 1 :=
    power_pred_eq_one_of_fixed w q₀ hw0 hq₀ hwfix
  have hwR : w ^ R = w := pow_eq_self_of_modEq_one w R (q₀ - 1) hwM hcong
  have hwq : w ^ q = w := binary_frobenius_period_mul w b R hwfix
  have hwN : w ^ (q - 1) = 1 := power_pred_eq_one_of_fixed w q hw0 hq hwq
  have hratioR : (t / w) ^ R = 1 := by rw [div_pow, htR, hwR, div_self hw0]
  have hratioN : (t / w) ^ (q - 1) = 1 := by rw [div_pow, htN, hwN]; simp
  have heq : t / w = 1 :=
    (_root_.pow_eq_one_iff_of_coprime hcop).mp ⟨hratioR, hratioN⟩
  exact (div_eq_one_iff_eq hw0).mp heq

/-- A known multiplicative period coprime to `p` explicitly supplies a
`p`-th root. No finite ambient group or cyclicity assumption is required. -/
theorem isPthPower_of_coprime_period
    {G : Type*} [Monoid G] (z : G) (p n : ℕ)
    (hz : z ^ n = 1) (hcop : p.Coprime n) : IsPthPower p z := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · obtain ⟨u, _, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hn
    refine ⟨z ^ u, ?_⟩
    rw [← pow_mul, mul_comm u p, ← Nat.div_add_mod (p * u) n, hu,
      pow_add, pow_mul, hz, one_pow, one_mul, pow_one]
  · interval_cases n
    · have hp : p = 1 := by simpa using hcop
      exact ⟨z, by simp [hp]⟩
    · exact ⟨1, by simpa using hz.symm⟩

/-- A prime of exact binary residue degree `E` is absent from every
positive smaller field degree. -/
theorem coprime_period_of_residue_degree
    (p E d : ℕ) (hp : p.Prime)
    (horder : orderOf (2 : ZMod p) = E) (hd : 0 < d) (hdE : d < E) :
    p.Coprime (2 ^ d - 1) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  have hmod : Nat.ModEq p (2 ^ d) 1 :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow d 2 (by decide))).mpr hdiv).symm
  have hpow : (2 : ZMod p) ^ d = 1 := by
    have hcast := (ZMod.natCast_eq_natCast_iff (2 ^ d) 1 p).mpr hmod
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast
  have hEd : E ∣ d := by
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hpow
  exact (not_le_of_gt hdE) (Nat.le_of_dvd hd hEd)

/-- The proper-subfield power input can be checked using only its
Frobenius period and the exact residue degree of the current prime. -/
theorem isPthPower_of_smaller_frobenius_period
    {F : Type*} [Field F] (z : F) (p E d : ℕ)
    (hp : p.Prime) (horder : orderOf (2 : ZMod p) = E)
    (hz0 : z ≠ 0) (hd : 0 < d) (hdE : d < E)
    (hz : z ^ (2 ^ d) = z) : IsPthPower p z := by
  apply isPthPower_of_coprime_period z p (2 ^ d - 1)
  · exact power_pred_eq_one_of_fixed z (2 ^ d) hz0
      (Nat.one_le_pow d 2 (by decide)) hz
  · exact coprime_period_of_residue_degree p E d hp horder hd hdE

end Ogdoad.Excess
