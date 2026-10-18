import Ogdoad.Excess

/-!
# The order bridge for cubic intermediate-field packing

These lemmas check the coprime factor splitting behind the exact factor of
three between the cubic projective order and the selected Singer order.
They do not establish the finite-field half-angle factorization, the
valuation of the lower field's unit group, or the packing count.  Those
specializations remain paper-level inputs.
-/

namespace Ogdoad.Excess

/-- Removing exactly `k` powers of three from the exponent of an element of
order `3^(k+1)` leaves order three.  The remaining exponent is only required
to be coprime to three. -/
theorem cubic_circle_power_order
    {G : Type*} [Group G] (z : G) (k r : ℕ)
    (hz : orderOf z = 3 ^ (k + 1)) (hr : Nat.Coprime 3 r) :
    orderOf (z ^ (3 ^ k * r)) = 3 := by
  have hbase : orderOf (z ^ (3 ^ k)) = 3 := by
    rw [orderOf_pow_of_dvd (by positivity)]
    · rw [hz, pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
    · rw [hz, pow_succ]
      exact Nat.dvd_mul_right _ _
  rw [pow_mul]
  calc
    orderOf ((z ^ (3 ^ k)) ^ r) = orderOf (z ^ (3 ^ k)) :=
      Nat.Coprime.orderOf_pow (hbase.symm ▸ hr)
    _ = 3 := hbase

/-- A circle factor of order `3^(k+1)` and a real factor of order prime to
three split after the lower-field exponent.  The real-factor gcd hypothesis
records that this exponent removes the same part as the real lower-field
exponent `d`; no gcd formula for the product's order is assumed. -/
theorem cubic_projective_power_order
    {G : Type*} [CommGroup G] [Finite G] (z a : G) (k r d : ℕ)
    (hz : orderOf z = 3 ^ (k + 1))
    (hr : Nat.Coprime 3 r)
    (ha : Nat.Coprime 3 (orderOf a))
    (hreal : Nat.gcd (orderOf a) (3 ^ k * r) = Nat.gcd (orderOf a) d) :
    orderOf ((z * a) ^ (3 ^ k * r)) = 3 * orderOf (a ^ d) := by
  have hzpow := cubic_circle_power_order z k r hz hr
  have hcop : (orderOf (z ^ (3 ^ k * r))).Coprime
      (orderOf (a ^ (3 ^ k * r))) := by
    rw [hzpow]
    exact ha.of_dvd_right (orderOf_pow_dvd (3 ^ k * r))
  rw [mul_pow,
    (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime hcop,
    hzpow, orderOf_pow, orderOf_pow, hreal]

/-- Transfer a bound from the projective packing group to the Singer
coordinate.  The half-angle real factor and `γ` need only have the same
order; the conclusion is the integer ceiling of the bound divided by three.
The actual choice of finite-field factors and the proof of the packing
bound remain explicit hypotheses. -/
theorem cubic_singer_order_ge_of_projective_packing
    {G : Type*} [CommGroup G] [Finite G]
    (z a γ : G) (k r d B : ℕ)
    (hz : orderOf z = 3 ^ (k + 1))
    (hr : Nat.Coprime 3 r)
    (ha : Nat.Coprime 3 (orderOf a))
    (hreal : Nat.gcd (orderOf a) (3 ^ k * r) = Nat.gcd (orderOf a) d)
    (hγ : orderOf γ = orderOf a)
    (hpacking : B ≤ orderOf ((z * a) ^ (3 ^ k * r))) :
    (B + 2) / 3 ≤ orderOf (γ ^ d) := by
  have hbridge := cubic_projective_power_order z a k r d hz hr ha hreal
  have hγpow : orderOf (γ ^ d) = orderOf (a ^ d) := by
    simp only [orderOf_pow, hγ]
  rw [hbridge] at hpacking
  rw [hγpow]
  omega

end Ogdoad.Excess
