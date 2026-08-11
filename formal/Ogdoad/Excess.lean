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

/-- Exact factorization of an element's order into its order in a quotient and
the residual order after raising by that quotient order.  This is the abstract
order bridge behind the relative-order products in a finite field tower; it
does not assert that either relative factor is maximal. -/
theorem orderOf_eq_quotient_order_mul_orderOf_pow
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (x : G) :
    orderOf x =
      orderOf ((QuotientGroup.mk' H) x) *
        orderOf (x ^ orderOf ((QuotientGroup.mk' H) x)) := by
  let m := orderOf ((QuotientGroup.mk' H) x)
  have hm : m ∣ orderOf x := orderOf_map_dvd (QuotientGroup.mk' H) x
  have hm0 : m ≠ 0 := ((isOfFinOrder_of_finite _).orderOf_pos).ne'
  rw [orderOf_pow_of_dvd hm0 hm]
  exact (Nat.mul_div_cancel' hm).symm

/-- Finite-level form of Popovych's primitive-product equivalence.  Once the
selected order is factored into positive relative divisors of the Fermat
numbers, multiplying by the order-three base element is primitive exactly
when every relative divisor is the full Fermat number.  The theorem exposes,
rather than assumes, the universal equalities still needed from the Conway
tower. -/
theorem popovych_primitive_product_iff
    {n : Nat} {G : Type*} [CommGroup G] [Fintype G]
    (c0 cn : G) (δ : Nat → Nat)
    (hc0 : orderOf c0 = 3)
    (hcn : orderOf cn = ∏ j ∈ Finset.Icc 1 n, δ j)
    (hcop : (orderOf c0).Coprime (orderOf cn))
    (hδpos : ∀ j ∈ Finset.Icc 1 n, 0 < δ j)
    (hδ : ∀ j ∈ Finset.Icc 1 n, δ j ∣ Nat.fermatNumber j)
    (hcard : Fintype.card G =
      3 * ∏ j ∈ Finset.Icc 1 n, Nat.fermatNumber j) :
    orderOf (c0 * cn) = Fintype.card G ↔
      ∀ j ∈ Finset.Icc 1 n, δ j = Nat.fermatNumber j := by
  have hordmul :
      orderOf (c0 * cn) = orderOf c0 * orderOf cn :=
    (Commute.all c0 cn).orderOf_mul_eq_mul_orderOf_of_coprime hcop
  have hle :
      ∀ j ∈ Finset.Icc 1 n, δ j ≤ Nat.fermatNumber j := by
    intro j hj
    exact Nat.le_of_dvd
      (Nat.zero_lt_of_lt (Nat.two_lt_fermatNumber j))
      (hδ j hj)
  rw [hordmul, hc0, hcn, hcard]
  constructor
  · intro hprod j hj
    have hprod' :
        (∏ j ∈ Finset.Icc 1 n, δ j) =
          ∏ j ∈ Finset.Icc 1 n, Nat.fermatNumber j := by
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) hprod
    apply le_antisymm (hle j hj)
    by_contra hnot
    have hlt : δ j < Nat.fermatNumber j :=
      Nat.lt_of_not_ge hnot
    have hproducts_lt :
        (∏ j ∈ Finset.Icc 1 n, δ j) <
          ∏ j ∈ Finset.Icc 1 n, Nat.fermatNumber j := by
      exact Finset.prod_lt_prod hδpos hle ⟨j, hj, hlt⟩
    exact (ne_of_lt hproducts_lt) hprod'
  · intro hpoint
    congr 1
    exact Finset.prod_congr rfl hpoint

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

section FermatLocalSymbol

variable {K : Type*} [Field K]

/-- If `c^q = c*w`, then the Euler power of `c` in the new norm-one
factor is exactly the corresponding power of `w`.  In the Conway
application, `w = (c+1)/c`, `h = (q+1)/ell`, and the left exponent is
`(q^2-1)/ell`. -/
theorem conwayUnit_eulerSymbol
    (c w : K) (q h : Nat) (hc : c ≠ 0) (hq : 0 < q)
    (hcq : c ^ q = c * w) :
    c ^ ((q - 1) * h) = w ^ h := by
  have hqsplit : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hpow : c ^ q = c ^ (q - 1) * c := by
    calc
      c ^ q = c ^ (q - 1 + 1) := by rw [hqsplit]
      _ = c ^ (q - 1) * c := by rw [pow_succ]
  have hstep : c ^ (q - 1) * c = w * c := by
    calc
      c ^ (q - 1) * c = c ^ q := hpow.symm
      _ = c * w := hcq
      _ = w * c := mul_comm _ _
  have hbase : c ^ (q - 1) = w := by
    exact mul_right_cancel₀ hc hstep
  rw [pow_mul, hbase]

end FermatLocalSymbol

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

section FermatWeightedSelector

variable {k : Type*} [Field k]

/-- A valuation which is constant on a nontrivial multiplicative coset has
zero cyclotomic weighted sum.  This is the algebraic core of the fact that
selectors coming from either unmixed factor of the canonical compositum
cannot isolate one prime above two. -/
theorem geometric_coset_weight_sum_eq_zero
    (x a weight : k) (f : Nat) (hx : x ≠ 1) (hxf : x ^ f = 1) :
    ∑ j ∈ Finset.range f, (a * x ^ j) * weight = 0 := by
  have hgeom : ∑ j ∈ Finset.range f, x ^ j = 0 := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hx)
    rw [geom_sum_mul, hxf]
    simp
  calc
    ∑ j ∈ Finset.range f, (a * x ^ j) * weight =
        (a * weight) * ∑ j ∈ Finset.range f, x ^ j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = 0 := by rw [hgeom]; simp

/-- Orbitwise-constant weights vanish whenever every orbit has zero sum. -/
theorem constant_coset_weighted_sum_eq_zero
    {I : Type*} (s : Finset I) (orbit : I → Finset k)
    (weight : I → k)
    (horbit : ∀ i ∈ s, ∑ x ∈ orbit i, x = 0) :
    ∑ i ∈ s, ∑ x ∈ orbit i, x * weight i = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.sum_mul, horbit i hi, zero_mul]

/-- An even cyclotomic divisor weight has zero first moment.  In the
Conway--Fermat compositum, `-1` lies in the decomposition group of two, so
every divisor descending from the pure cyclotomic factor has exactly this
symmetry and cannot distinguish the selected prime from its inverse. -/
theorem even_weight_first_moment_eq_zero
    {F : Type*} [Field F] [Fintype F]
    (h2 : (2 : F) ≠ 0) (w : F → F) (hw : ∀ x, w (-x) = w x) :
    (∑ x : F, x * w x) = 0 := by
  let S : F := ∑ x : F, x * w x
  have hneg : S = -S := by
    calc
      S = ∑ x : F, (-x) * w (-x) := by
        simpa [S] using
          (Equiv.sum_comp (Equiv.neg F) (fun x : F => x * w x)).symm
      _ = ∑ x : F, -(x * w x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hw]
        exact neg_mul x (w x)
      _ = -S := by simp [S]
  have hsum : S + S = 0 := by
    calc
      S + S = S + (-S) := congrArg (fun x => S + x) hneg
      _ = 0 := add_neg_cancel S
  have hmul : (2 : F) * S = 0 := by simpa [two_mul] using hsum
  exact (mul_eq_zero.mp hmul).resolve_left h2

end FermatWeightedSelector

section FermatAffineMixedSelector

/-- An invariant function on a transitive orbit is constant.  Applied to
normalized valuations at the primes over two, this is the abstract core of
the paper's proof that a `(1, 0, ..., 0)` valuation vector cannot descend to
the lower Conway field. -/
theorem invariant_function_eq_of_transitive
    {G I V : Type*} [Group G] [MulAction G I]
    (htrans : ∀ i j : I, ∃ g : G, g • i = j)
    (f : I → V)
    (hinv : ∀ (g : G) (i : I), f (g • i) = f i)
    (i j : I) : f i = f j := by
  obtain ⟨g, rfl⟩ := htrans i j
  exact (hinv g i).symm

/-- A transitive invariant cannot take the two distinct values zero and one.
This packages the valuation contradiction used for the affine selector norm. -/
theorem invariant_function_not_one_zero_of_transitive
    {G I V : Type*} [Group G] [MulAction G I] [Zero V] [One V]
    (h10 : (1 : V) ≠ 0)
    (htrans : ∀ i j : I, ∃ g : G, g • i = j)
    (f : I → V)
    (hinv : ∀ (g : G) (i : I), f (g • i) = f i)
    (i j : I) (hi : f i = 1) (hj : f j = 0) : False := by
  apply h10
  rw [← hi, ← hj]
  exact invariant_function_eq_of_transitive htrans f hinv i j

/-- If a value occurs at exactly one point, every symmetry preserving the
function fixes that point.  This is the abstract stabilizer step behind the
degree bound for the mixed affine-selector norm. -/
theorem unique_value_stabilizer_fixes
    {G I V : Type*} [Group G] [MulAction G I]
    (f : I → V) (i : I) (value : V)
    (huniq : ∀ j, f j = value ↔ j = i)
    (g : G) (hinv : ∀ j, f (g • j) = f j) :
    g • i = i := by
  apply (huniq (g • i)).mp
  rw [hinv]
  exact (huniq i).2 rfl

/-- Affine interpolation against a nonzero coefficient isolates exactly one
value of the cyclotomic coordinate.  This is the finite-field algebra behind
the paper's principal selector with weighted two-adic moment one. -/
theorem affine_selector_eq_iff
    {F : Type*} [Field F]
    (u v eta z : F) (hv : v ≠ 0) :
    u + v * z = u + v * eta ↔ z = eta := by
  constructor
  · intro h
    have h' : v * z = v * eta := add_left_cancel h
    exact mul_left_cancel₀ hv h'
  · rintro rfl
    rfl

/-- Relative norm of the affine selector `C - r` across one lifted Conway
quadratic. -/
theorem quadratic_affine_selector_norm
    {R : Type*} [CommRing R]
    (C A r : R) (hC : C ^ 2 + C + A = 0) :
    (C - r) * (-1 - C - r) = A + r + r ^ 2 := by
  have hA : A = -(C ^ 2 + C) := by
    linear_combination hC
  rw [hA]
  ring

/-- A hypothetical affine selector of relative norm two would make the
shifted Conway discriminant a square.  The paper excludes this square by a
global/local quadratic-subfield argument. -/
theorem affine_selector_norm_two_iff_discriminant_square
    {R : Type*} [Field R] [CharZero R] (A r : R) :
    r ^ 2 + r + A = 2 ↔
      (2 * r + 1) ^ 2 = (1 - 4 * A) + 8 := by
  constructor
  · intro h
    linear_combination 4 * h
  · intro h
    have hfour : (4 : R) * (r ^ 2 + r + A - 2) = 0 := by
      linear_combination h
    have hzero : r ^ 2 + r + A - 2 = 0 :=
      (mul_eq_zero.mp hfour).resolve_left (by norm_num)
    exact sub_eq_zero.mp hzero

/-- The two orientations over a root of `A + r + r^2` see reciprocal
values of the norm-one Conway unit.  Consequently the full norm/resultant
forgets the oriented tame residue retained by either affine factor. -/
theorem affine_selector_oriented_values_mul_eq_one
    {F : Type*} [Field F]
    (A r : F) (hrel : A + r + r ^ 2 = 0)
    (hr : r ≠ 0) (hr1 : r + 1 ≠ 0) :
    (A / r ^ 2) * (A / (-1 - r) ^ 2) = 1 := by
  have hA : A = -(r + r ^ 2) := by
    linear_combination hrel
  have hneg : -1 - r ≠ 0 := by
    intro h
    apply hr1
    calc
      r + 1 = -(-1 - r) := by ring
      _ = 0 := by rw [h]; simp
  calc
    (A / r ^ 2) * (A / (-1 - r) ^ 2) =
        (-(r + 1) / r) * (-r / (r + 1)) := by
      rw [hA]
      field_simp [hr, hr1, hneg]
      ring
    _ = 1 := by field_simp [hr, hr1]

/-- Any nonsymmetric element can be rescaled by an involution-fixed scalar
to have a prescribed anti-invariant additive trace.  With `Y = 2*C+1`, this
puts every oriented fractional divisor into the affine form `C - R`; the
paper separately tracks the integrality and local-unit conditions lost by
the rescaling. -/
theorem affine_antiTrace_normalization
    {K : Type*} [Field K]
    (sigma : K ≃+* K) (hsigma : Function.Involutive sigma)
    (Y x : K) (hY : sigma Y = -Y) (hd : x - sigma x ≠ 0) :
    let z := Y / (x - sigma x)
    sigma z = z ∧ z * x - sigma (z * x) = Y := by
  dsimp
  have hden : sigma (x - sigma x) = -(x - sigma x) := by
    rw [map_sub, hsigma x]
    ring
  have hz : sigma (Y / (x - sigma x)) = Y / (x - sigma x) := by
    rw [map_div₀ sigma, hY, map_sub, hsigma]
    have hd' : sigma x - x ≠ 0 := by
      intro h
      apply hd
      linear_combination -h
    field_simp [hd, hd']
    ring
  constructor
  · exact hz
  · rw [map_mul, hz]
    field_simp [hd]

/-- The local oriented Conway residue has a rational `ell`-power
parametrization.  Thus the single split residue equation has no positive-genus
obstruction; only the globally selected orientation can retain information. -/
theorem oriented_residue_rational_parametrization
    {K : Type*} [Field K]
    (z : K) (ell : Nat) (hden : 1 + z ^ ell ≠ 0) :
    let r := -1 / (1 + z ^ ell);
    -(r + 1) / r = z ^ ell := by
  dsimp
  have hr : -1 / (1 + z ^ ell) ≠ 0 := div_ne_zero (by norm_num) hden
  field_simp [hden, hr]
  ring

/-- An anti-invariant character kills the norm of every oriented divisor. -/
theorem antiInvariantCharacter_norm_eq_one
    {D Z : Type*} [CommGroup D] [CommGroup Z]
    (chi : D →* Z) (iota : D →* D)
    (hinv : ∀ d, chi (iota d) = (chi d)⁻¹) (d : D) :
    chi (d * iota d) = 1 := by
  rw [map_mul, hinv]
  exact mul_inv_cancel _

/-- The anti-invariant quotient retains exactly the square of the oriented
character value; for odd Kummer order, this loses no information. -/
theorem antiInvariantCharacter_ratio_eq_sq
    {D Z : Type*} [CommGroup D] [CommGroup Z]
    (chi : D →* Z) (iota : D →* D)
    (hinv : ∀ d, chi (iota d) = (chi d)⁻¹) (d : D) :
    chi (d / iota d) = (chi d) ^ 2 := by
  rw [map_div, hinv]
  simp [div_eq_mul_inv, pow_two]

/-- Abstract multiplicative core of the affine selector's Jacobi collapse.
Once reciprocity has killed the lower ancestral factor and shown that the
distinguished and residual Jacobi symbols multiply to one, the oriented tame
residue is exactly the square of the distinguished symbol. -/
theorem jacobi_halfResultant_collapse
    {G : Type*} [CommGroup G]
    (Rr Ra Aa T H : G)
    (hAa : Aa = 1) (hRg : Rr * Ra = 1)
    (hT : T = Aa * (Ra⁻¹) ^ 2) (hH : H = T⁻¹) :
    T = Rr ^ 2 ∧ H = (Rr ^ 2)⁻¹ := by
  have hRa : Ra⁻¹ = Rr := by
    exact (eq_inv_of_mul_eq_one_left hRg).symm
  constructor
  · rw [hT, hAa, one_mul, hRa]
  · rw [hH, hT, hAa, one_mul, hRa]

end FermatAffineMixedSelector

section FermatTranslateSaturation

variable {G M : Type*} [Fintype G] [AddCommGroup G] [CommMonoid M]

/-- Translation permutes the product over a finite additive group. -/
theorem prod_univ_add_right (f : G → M) (a : G) :
    (∏ x : G, f (x + a)) = ∏ x : G, f x := by
  let e : G ≃ G := Equiv.addRight a
  simpa [e] using (Equiv.prod_comp e f)

/-- Every point in a finite additive group occurs once for each element of
the translating fibre.  Applied to a failed Conway--Fermat root set inside
the trace-one hyperplane, this says that translation by the full trace
kernel saturates the trace-one polynomial with exactly constant multiplicity. -/
theorem prod_translate_saturation (s : Finset G) (f : G → M) :
    (∏ t : G, ∏ x ∈ s, f (t + x)) = (∏ y : G, f y) ^ s.card := by
  rw [Finset.prod_comm]
  simp_rw [prod_univ_add_right]
  exact Finset.prod_const _

end FermatTranslateSaturation

section FermatRayCharacter

/-- A weight-one equivariant orbit map is determined by its value at the
distinguished base point.  In the paper this is the abstract shape of the
Artin values at the primes above two. -/
theorem mulEquivariant_eq_baseScalar
    {F : Type*} [Field F]
    (f : Fˣ → F)
    (hf : ∀ a b, f (a * b) = (a : F) * f b)
    (a : Fˣ) :
    f a = (a : F) * f 1 := by
  simpa using hf a 1

/-- Every base scalar, including zero, gives an equivariant orbit map. -/
theorem every_baseScalar_is_mulEquivariant
    {F : Type*} [Field F]
    (c : F) :
    ∃ f : Fˣ → F,
      (∀ a b, f (a * b) = (a : F) * f b) ∧ f 1 = c := by
  refine ⟨fun a ↦ (a : F) * c, ?_, ?_⟩
  · intro a b
    simp [mul_assoc]
  · simp

/-- Equivariance alone permits both the zero selected value and a nonzero
one; it cannot prove the required ray-character nonvanishing. -/
theorem mulEquivariance_does_not_force_nonzero
    {F : Type*} [Field F] :
    (∃ f : Fˣ → F,
      (∀ a b, f (a * b) = (a : F) * f b) ∧ f 1 = 0) ∧
    (∃ f : Fˣ → F,
      (∀ a b, f (a * b) = (a : F) * f b) ∧ f 1 ≠ 0) := by
  constructor
  · simpa using (every_baseScalar_is_mulEquivariant (F := F) 0)
  · obtain ⟨f, hf, h1⟩ := every_baseScalar_is_mulEquivariant (F := F) 1
    exact ⟨f, hf, by simp [h1]⟩

/-- A fixed source class is annihilated by any nontrivially weighted
equivariant character.  This is the algebraic core of the ambiguous-class
no-go in the mixed ray group. -/
theorem fixed_source_maps_zero
    {F A : Type*} [Field F]
    (act : Fˣ → A → A) (f : A → F)
    (a : Fˣ) (ha : (a : F) ≠ 1)
    (x : A) (hx : act a x = x)
    (hf : f (act a x) = (a : F) * f x) :
    f x = 0 := by
  have hscale : f x = (a : F) * f x := by simpa [hx] using hf
  have hprod : ((a : F) - 1) * f x = 0 := by
    calc
      ((a : F) - 1) * f x = (a : F) * f x - f x := by ring
      _ = 0 := by rw [← hscale]; simp
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr ha)

/-- If a multiplicative map is invariant under every member of a finite
family of endomorphisms, applying it to an integral group-ring product sees
only the augmentation.  This is the abstract algebra behind the paper's
observation that cyclic operations on a Hasse norm witness retain a constant
prime-above-two norm vector. -/
theorem invariant_hom_groupRing_product_eq_augmentation
    {G A B : Type*} [Group G] [Fintype G] [CommGroup A] [CommGroup B]
    (phi : A →* B) (rho : G → A →* A)
    (hinv : ∀ (g : G) (x : A), phi (rho g x) = phi x)
    (y : A) (coeff : G → ℤ) :
    phi (∏ g : G, (rho g y) ^ coeff g) =
      (phi y) ^ (∑ g : G, coeff g) := by
  classical
  rw [map_prod]
  simp_rw [map_zpow, hinv]
  induction (Finset.univ : Finset G) using Finset.induction_on with
  | empty => simp
  | @insert g s hg ih => simp [hg, ih, zpow_add]

/-- The conductor-five quadratic antiunit has a reflection invariant whose
coefficient is a rational function of the fixed trace coordinate.  These two
denominator-free identities are the algebraic core of the paper's second
dihedral reflection descent, for the exceptional arm. -/
theorem conductorFive_reflection_invariant
    {R : Type*} [CommRing R]
    (x s s' : R) (hsum : s + s' = -1) (hprod : s * s' = -1) :
    (x - s) * (x - s') = x ^ 2 + x - 1 ∧
      (x - s) ^ 2 + (x - s') ^ 2 =
        2 * (x ^ 2 + x - 1) + 5 := by
  constructor
  · calc
      (x - s) * (x - s') = x ^ 2 - x * (s + s') + s * s' := by ring
      _ = x ^ 2 + x - 1 := by rw [hsum, hprod]; ring
  · calc
      (x - s) ^ 2 + (x - s') ^ 2 =
          2 * x ^ 2 - 2 * x * (s + s') + (s + s') ^ 2 - 2 * (s * s') := by
            ring
      _ = 2 * (x ^ 2 + x - 1) + 5 := by rw [hsum, hprod]; ring

/-- Quotient form of `conductorFive_reflection_invariant`: the norm-one
antiunit and its inverse add to the lower-field Chebyshev coefficient used in
the exceptional arm's reflection polynomial. -/
theorem conductorFive_antiunit_trace
    {F : Type*} [Field F]
    (x s s' : F)
    (hsum : s + s' = -1) (hprod : s * s' = -1)
    (hxs : x - s ≠ 0) (hxsp : x - s' ≠ 0) :
    let d := (x - s) / (x - s')
    d + d⁻¹ = 2 + 5 / (x ^ 2 + x - 1) := by
  dsimp
  obtain ⟨hden, hnum⟩ :=
    conductorFive_reflection_invariant x s s' hsum hprod
  have hnum' :
      (x - s) ^ 2 + (x - s') ^ 2 =
        2 * ((x - s) * (x - s')) + 5 := by
    rw [hden]
    exact hnum
  rw [← hden]
  field_simp
  simpa [mul_comm, mul_left_comm, mul_assoc] using hnum'

/-- Abstract algebra of the reflection-norm descent.  If `N(y) = a`, the
reflection has the same norm, and base elements have degree-`ell` norm, then
the symmetrized witness `((y * s y)^r) / a` is reflection-fixed and still has
norm `a` whenever `2*r = ell+1`. -/
theorem reflection_symmetrized_norm_witness
    {A : Type*} [CommGroup A]
    (s : A ≃* A) (N : A →* A) (y a : A) (ell r : Nat)
    (hs : Function.Involutive s) (ha : s a = a)
    (hy : N y = a) (hsy : N (s y) = a)
    (hbase : N a = a ^ ell) (hfactor : 2 * r = ell + 1) :
    let z := (y * s y) ^ r / a
    s z = z ∧ N z = a := by
  dsimp
  constructor
  · simp [map_div, map_pow, map_mul, hs y, ha, mul_comm]
  · calc
      N ((y * s y) ^ r / a) = (a * a) ^ r / a ^ ell := by
        rw [map_div, map_pow, map_mul, hy, hsy, hbase]
      _ = a ^ (2 * r) / a ^ ell := by rw [← pow_two, pow_mul]
      _ = a ^ (ell + 1) / a ^ ell := by rw [hfactor]
      _ = a := by rw [pow_succ]; simp [div_eq_mul_inv, mul_assoc]

/-- Under reflection-equivariance of the norm, every norm witness can be
symmetrized to a reflection-fixed one, and a fixed witness is already an
ordinary witness.  Because this is an identity of commutative groups, it
survives every scalar extension.  This is the algebraic core of the paper's
local as well as global reflection-norm equivalence. -/
theorem reflection_fixed_norm_witness_iff
    {A : Type*} [CommGroup A]
    (s : A ≃* A) (N : A →* A) (a : A) (ell r : Nat)
    (hs : Function.Involutive s) (ha : s a = a)
    (hN : ∀ y, N (s y) = s (N y))
    (hbase : N a = a ^ ell) (hfactor : 2 * r = ell + 1) :
    (∃ y, N y = a) ↔ ∃ z, s z = z ∧ N z = a := by
  constructor
  · rintro ⟨y, hy⟩
    let z := (y * s y) ^ r / a
    have hz := reflection_symmetrized_norm_witness
      s N y a ell r hs ha hy (by rw [hN, hy, ha]) hbase hfactor
    exact ⟨z, hz⟩
  · rintro ⟨z, _, hz⟩
    exact ⟨z, hz⟩

/-- In an odd dihedral extension, every homomorphism to an abelian target
kills the translation subgroup.  This is the algebraic core of the paper's
lower-field abelian-descent no-go for the selected Frobenius. -/
theorem dihedral_translation_killed_in_abelian_target
    {G A : Type*} [Group G] [CommGroup A]
    (f : G →* A) (sigma s : G) (ell k : Nat)
    (hell : ell = 2 * k + 1)
    (horder : sigma ^ ell = 1)
    (hconj : s * sigma * s⁻¹ = sigma⁻¹) :
    f sigma = 1 := by
  have hinv : f sigma = (f sigma)⁻¹ := by
    have hmapped := congrArg f hconj
    simpa [map_mul] using hmapped
  have htwo : (f sigma) ^ 2 = 1 := by
    calc
      (f sigma) ^ 2 = (f sigma)⁻¹ * f sigma := by rw [pow_two, ← hinv]
      _ = 1 := inv_mul_cancel _
  have hodd : (f sigma) ^ ell = 1 := by
    rw [← map_pow, horder, map_one]
  rw [hell] at hodd
  simpa [pow_add, pow_mul, htwo] using hodd

/-- An anti-invariant class has coboundary equal to minus twice the class.
This is the additive algebra behind the paper's top-generator Brauer
reduction. -/
theorem antiInvariant_coboundary_eq_neg_two
    {V : Type*} [AddCommGroup V]
    (s : V →+ V) (x : V)
    (hcore : x + s x = 0) :
    s x - x = -(2 • x) := by
  have hs : s x = -x := eq_neg_of_add_eq_zero_right hcore
  rw [hs]
  simp only [two_nsmul]
  abel

/-- Over odd characteristic, the anti-invariant coboundary vanishes exactly
when its source class does. -/
theorem antiInvariant_coboundary_eq_zero_iff
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (s : V →ₗ[F] V) (x : V)
    (hcore : x + s x = 0) (htwo : (2 : F) ≠ 0) :
    s x - x = 0 ↔ x = 0 := by
  have hs : s x = -x := eq_neg_of_add_eq_zero_right hcore
  rw [hs]
  constructor
  · intro h
    have hsum : x + x = 0 := by
      calc
        x + x = -(-x - x) := by abel
        _ = -0 := congrArg Neg.neg h
        _ = 0 := neg_zero
    have hsmul : (2 : F) • x = 0 := by
      simpa only [two_smul] using hsum
    exact (smul_eq_zero.mp hsmul).resolve_left htwo
  · rintro rfl
    simp

end FermatRayCharacter

section FermatMixedNormDetector

variable {k : Type*} [Field k] [CharP k 2]

/-- For an odd-order element in characteristic two, its geometric sum
vanishes exactly away from the identity.  Applied to `T = W^(F_n/ell)`,
this says that the apparent mixed principal selector `T - zeta_ell` has
support above two exactly when the desired Kummer symbol is nontrivial. -/
theorem odd_geom_sum_eq_zero_iff_ne_one
    (t : k) (s : Nat) (ht : t ^ (2 * s + 1) = 1) :
    (∑ j ∈ Finset.range (2 * s + 1), t ^ j) = 0 ↔ t ≠ 1 := by
  constructor
  · intro hsum ht1
    subst t
    simp at hsum
    have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
    rw [htwo, zero_mul, zero_add] at hsum
    exact one_ne_zero hsum
  · intro ht1
    apply mul_right_cancel₀ (sub_ne_zero.mpr ht1)
    rw [geom_sum_mul, ht]
    simp

end FermatMixedNormDetector

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

/-- Denominator-free core of the exceptional arm's one-variable Dickson
coordinate.  For the Artin--Schreier pair `w,w+1`, the norm-one quotient
`M=(w+1)/w` satisfies `M+M⁻¹=(w²+w)⁻¹` in characteristic two. -/
theorem artinSchreier_mobius_trace
    (w : K) (hw : w ≠ 0) (hw1 : w + 1 ≠ 0) (hchar : (2 : K) = 0) :
    (w + 1) / w + ((w + 1) / w)⁻¹ = (w ^ 2 + w)⁻¹ := by
  field_simp [hw, hw1]
  ring_nf
  rw [hchar]
  simp

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

/-- The same selected cubic ancestry forces the relative trace of
`g = x^2+x+1` to be one. -/
theorem cubic_auxiliary_trace_coherence
    (x y z : R) (hchar : (2 : R) = 0) (h₁ : x + y + z = 0) :
    (x ^ 2 + x + 1) + (y ^ 2 + y + 1) + (z ^ 2 + z + 1) = 1 := by
  calc
    _ = (x + y + z) ^ 2 + (x + y + z) + 1 +
          2 * (1 - (x * y + x * z + y * z)) := by ring
    _ = 1 := by rw [h₁, hchar]; simp

/-- The middle elementary-symmetric coordinate of the three auxiliary
conjugates is `t+1`.  The paper's exact `k=4` countermodel retains their
selected trace and norm but changes precisely this coordinate. -/
theorem cubic_auxiliary_e2_coherence
    (x y z t : R) (hchar : (2 : R) = 0)
    (h₁ : x + y + z = 0) (h₂ : x * y + x * z + y * z = 1)
    (h₃ : x * y * z = t) :
    (x ^ 2 + x + 1) * (y ^ 2 + y + 1) +
      (x ^ 2 + x + 1) * (z ^ 2 + z + 1) +
      (y ^ 2 + y + 1) * (z ^ 2 + z + 1) = t + 1 := by
  have hthree : (3 : R) = 1 := by
    calc
      (3 : R) = 2 + 1 := by norm_num
      _ = 1 := by rw [hchar]; simp
  have hneg (u : R) : -u = u := by
    rw [neg_eq_iff_add_eq_zero]
    calc
      u + u = 2 * u := by ring
      _ = 0 := by rw [hchar]; simp
  calc
    _ = 2 * (x + y + z) ^ 2 +
        (x + y + z) * (x * y + x * z + y * z) -
        2 * (x + y + z) * (x * y * z) +
        2 * (x + y + z) +
        (x * y + x * z + y * z) ^ 2 -
        3 * (x * y + x * z + y * z) -
        3 * (x * y * z) + 3 := by ring
    _ = t + 1 := by
      rw [h₁, h₂, h₃, hchar, hthree]
      ring_nf
      rw [sub_eq_add_neg, hneg]

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

/-- If `b` is an `ell`-th root of `a`, `ell * d = q + 1`, and `b` is
fixed by `q`-powering, then the selected root has the choice-free square
`b^2 = a^d`.  This is the algebraic compression used in the
Conway--Fermat Dickson descent. -/
theorem power_root_square_of_complementary_exponent
    (a b : G) (ell d q : Nat)
    (hroot : b ^ ell = a) (hfactor : ell * d = q + 1)
    (hfrob : b ^ q = b) :
    b ^ 2 = a ^ d := by
  calc
    b ^ 2 = b ^ (q + 1) := by rw [pow_two, pow_succ, hfrob]
    _ = b ^ (ell * d) := by rw [hfactor]
    _ = (b ^ ell) ^ d := by rw [pow_mul]
    _ = a ^ d := by rw [hroot]

/-- When `q = 2 * Q`, Frobenius fixity also makes the selected lower
`ell`-th root itself explicit: `b = (a^d)^Q`. -/
theorem power_root_eq_complementary_frobenius
    (a b : G) (ell d q Q : Nat)
    (hroot : b ^ ell = a) (hfactor : ell * d = q + 1)
    (hfrob : b ^ q = b) (hq : 2 * Q = q) :
    b = (a ^ d) ^ Q := by
  have hsquare := power_root_square_of_complementary_exponent
    a b ell d q hroot hfactor hfrob
  calc
    b = b ^ q := hfrob.symm
    _ = b ^ (2 * Q) := by rw [hq]
    _ = (b ^ 2) ^ Q := by rw [pow_mul]
    _ = (a ^ d) ^ Q := by rw [hsquare]

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

/-- Algebraic core of the one-branch quadratic norm descent.  If x and x'
have sum Y and product Y³, the norm of the linear remainder U + X V
is U² + Y U V + Y³ V². -/
theorem quadratic_remainder_norm
    (x x' U V Y : R) (hsum : x + x' = Y) (hprod : x * x' = Y ^ 3) :
    (U + x * V) * (U + x' * V) =
      U ^ 2 + Y * U * V + Y ^ 3 * V ^ 2 := by
  calc
    (U + x * V) * (U + x' * V) =
        U ^ 2 + (x + x') * U * V + (x * x') * V ^ 2 := by ring
    _ = U ^ 2 + Y * U * V + Y ^ 3 * V ^ 2 := by rw [hsum, hprod]

/-- Squaring a linear remainder at a Conway edge, still expressed in the
same quadratic basis. -/
theorem conway_quadratic_pair_square [CharP R 2]
    (x A U V : R) (hx : x ^ 2 = A * x + A ^ 3) :
    (U + x * V) ^ 2 =
      (U ^ 2 + A ^ 3 * V ^ 2) + x * (A * V ^ 2) := by
  rw [add_sq]
  rw [mul_pow, hx]
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  ring_nf
  simp [h2]

/-- The exact odd fast-doubling update for two adjacent linear remainders
at a Conway edge. -/
theorem conway_quadratic_pair_odd [CharP R 2]
    (x A U V P Q : R) (hx : x ^ 2 = A * x + A ^ 3) :
    (P + x * Q) ^ 2 + x * (U + x * V) ^ 2 =
      (P ^ 2 + A ^ 3 * Q ^ 2 + A ^ 4 * V ^ 2) +
        x * (A * Q ^ 2 + U ^ 2 + (A ^ 3 + A ^ 2) * V ^ 2) := by
  rw [conway_quadratic_pair_square x A P Q hx]
  rw [conway_quadratic_pair_square x A U V hx]
  have hxx : x * x = A * x + A ^ 3 := by simpa [pow_two] using hx
  rw [show x * (U ^ 2 + A ^ 3 * V ^ 2 + x * (A * V ^ 2)) =
      x * U ^ 2 + x * A ^ 3 * V ^ 2 + (x * x) * (A * V ^ 2) by ring]
  rw [hxx]
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  ring_nf

/-- Factorization of one quadratic in the universal Dickson--Conway
resultant.  When `x*y = P`, multiplying the two linear factors associated
to `P*x` and `P*y` gives the selected Conway quadratic. -/
theorem conway_kummer_quadratic_factor
    (Z P x y : R) (hxy : x * y = P) :
    (Z + P * x) * (Z + P * y) =
      Z ^ 2 + P * (x + y) * Z + P ^ 3 := by
  calc
    (Z + P * x) * (Z + P * y) =
        Z ^ 2 + P * (x + y) * Z + P ^ 2 * (x * y) := by ring
    _ = Z ^ 2 + P * (x + y) * Z + P ^ 3 := by
      rw [hxy]
      ring

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

section FermatCanonicalLift

variable {K : Type*} [Field K]

/-- Characteristic-free reparametrization of one lifted Conway--Fermat
quadratic step by its norm-one ratio. -/
theorem canonicalLift_normOne_reparam
    (C A : K) (hC : C ≠ 0) (hrel : C ^ 2 + C + A = 0) :
    let W := -(C + 1) / C
    A = W / (W + 1) ^ 2 ∧ A * C = -W / (W + 1) ^ 3 := by
  dsimp
  have hWp : -(C + 1) / C + 1 = -(1 / C) := by
    field_simp
    ring
  have hA : A = -(C ^ 2 + C) := by
    linear_combination hrel
  rw [hWp]
  rw [hA]
  constructor <;> field_simp

/-- The lifted norm-one ratio is the lower ancestral unit times the inverse
square of the new quadratic generator. -/
theorem canonicalLift_normOne_eq_parent_mul_inv_sq
    (C A : K) (hC : C ≠ 0) (hrel : C ^ 2 + C + A = 0) :
    -(C + 1) / C = A * (C⁻¹) ^ 2 := by
  have hA : A = -(C ^ 2 + C) := by
    linear_combination hrel
  rw [hA]
  field_simp

end FermatCanonicalLift

section FermatCanonicalDiscriminant

variable {R : Type*} [CommRing R]

/-- Denominator-free discriminant recursion for the characteristic-zero
lift.  With `Y = 2*C+1`, the old discriminant is `Y^2`, while the new one
has `-Y` as its unique first-order term at the prime above three. -/
theorem canonicalLift_discriminant_recursion
    (C A : R) (hrel : C ^ 2 + C + A = 0) :
    (2 * C + 1) ^ 2 = 1 - 4 * A ∧
      2 * (1 - 4 * (A * C)) =
        (2 * C + 1) ^ 3 - (2 * C + 1) ^ 2 - (2 * C + 1) + 3 := by
  constructor
  · linear_combination 4 * hrel
  · linear_combination -8 * C * hrel

/-- Relative norm of the next lifted Conway discriminant.  Its absolute
prime divisors are the exact places where the simple unramified first-Witt
expansion may fail. -/
theorem canonicalLift_nextDiscriminant_relativeNorm
    (C A : R) (hrel : C ^ 2 + C + A = 0) :
    (1 - 4 * A * C) * (1 + 4 * A + 4 * A * C) =
      1 + 4 * A + 16 * A ^ 3 := by
  linear_combination -16 * A ^ 2 * hrel

end FermatCanonicalDiscriminant

section FermatEllRay

variable {k : Type*} [Field k]

/-- Dividing the first-order expansion of `C^2 + C + A = 0` by the
nonzero residue `c` gives the update used below. -/
theorem canonicalLift_firstOrder_from_expansion
    (c a s defect b : k) (hc : c ≠ 0)
    (ha : a = -c * (c + 1))
    (hexp : c * defect + (2 * c ^ 2 + c) * b + a * s = 0) :
    (2 * c + 1) * b = (c + 1) * s - defect := by
  rw [ha] at hexp
  have hfactor :
      c * (defect + (2 * c + 1) * b - (c + 1) * s) = 0 := by
    linear_combination hexp
  have hzero : defect + (2 * c + 1) * b - (c + 1) * s = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hc
  linear_combination hzero

/-- The denominator-free first-order formula for the critical ray
coefficient of a lifted Conway unit.  The arithmetic interpretation in the
paper additionally assumes an unramified Teichmuller expansion at `ell`. -/
theorem canonicalLift_firstOrder_target
    (c s defect b : k)
    (hb : (2 * c + 1) * b = (c + 1) * s - defect) :
    (2 * c + 1) * (2 * b - s) = s - 2 * defect := by
  linear_combination 2 * hb

/-- One step of the parent coefficient under the same first-order Conway
relation. -/
theorem canonicalLift_firstOrder_parent_update
    (c s defect b s' : k)
    (hb : (2 * c + 1) * b = (c + 1) * s - defect)
    (hs' : s' = s + b) :
    (2 * c + 1) * s' = (3 * c + 2) * s - defect := by
  rw [hs']
  linear_combination hb

/-- Denominator-cleared recurrence for the numerator and denominator of the
ancestral first-order coefficient. -/
theorem canonicalLift_firstOrder_cleared_update
    (c s defect b s' P Q : k)
    (hb : (2 * c + 1) * b = (c + 1) * s - defect)
    (hs' : s' = s + b) (hQs : Q * s = P) :
    (Q * (2 * c + 1)) * s' = (3 * c + 2) * P - defect * Q := by
  have hu := canonicalLift_firstOrder_parent_update c s defect b s' hb hs'
  calc
    (Q * (2 * c + 1)) * s' = Q * ((2 * c + 1) * s') := by ring
    _ = Q * ((3 * c + 2) * s - defect) := by rw [hu]
    _ = (3 * c + 2) * P - defect * Q := by rw [← hQs]; ring

/-- Denominator-cleared numerator of the terminal critical ray coefficient. -/
theorem canonicalLift_firstOrder_cleared_target
    (c s defect b P Q : k)
    (hb : (2 * c + 1) * b = (c + 1) * s - defect)
    (hQs : Q * s = P) :
    (Q * (2 * c + 1)) * (2 * b - s) = P - 2 * defect * Q := by
  have ht := canonicalLift_firstOrder_target c s defect b hb
  calc
    (Q * (2 * c + 1)) * (2 * b - s) =
        Q * ((2 * c + 1) * (2 * b - s)) := by ring
    _ = Q * (s - 2 * defect) := by rw [ht]
    _ = P - 2 * defect * Q := by rw [← hQs]; ring

/-- Away from the derivative and denominator divisors, nonvanishing of the
critical coefficient is exactly nonvanishing of its selected ancestral
numerator. -/
theorem canonicalLift_firstOrder_target_ne_zero_iff
    (c s defect b P Q : k)
    (hb : (2 * c + 1) * b = (c + 1) * s - defect)
    (hQs : Q * s = P) (hQ : Q ≠ 0) (hc : 2 * c + 1 ≠ 0) :
    2 * b - s ≠ 0 ↔ P - 2 * defect * Q ≠ 0 := by
  have ht := canonicalLift_firstOrder_cleared_target c s defect b P Q hb hQs
  have hfactor : Q * (2 * c + 1) ≠ 0 := mul_ne_zero hQ hc
  constructor
  · intro hr hnum
    have hz : (Q * (2 * c + 1)) * (2 * b - s) = 0 := by rw [ht, hnum]
    exact hr ((mul_eq_zero.mp hz).resolve_left hfactor)
  · intro hnum hr
    apply hnum
    rw [← ht, hr, mul_zero]

end FermatEllRay

section FermatRamifiedRay

variable {k : Type*} [Field k]

/-- Below the absolute `ell`-depth, Teichmuller addition contributes no
defect.  The parent principal-unit coefficient therefore propagates by this
homogeneous logarithmic derivative. -/
theorem canonicalLift_ramified_parent_update
    (c s b s' : k)
    (hb : (2 * c + 1) * b = (c + 1) * s)
    (hs' : s' = s + b) :
    (2 * c + 1) * s' = (3 * c + 2) * s := by
  rw [hs']
  linear_combination hb

/-- At an etale terminal step, the leading coefficient of
`A_parent * C^{-2}` is the negative parent coefficient divided by the
quadratic derivative. -/
theorem canonicalLift_ramified_target
    (c s b : k)
    (hb : (2 * c + 1) * b = (c + 1) * s) :
    (2 * c + 1) * (s - 2 * b) = -s := by
  linear_combination -2 * hb

/-- A nonzero ramified coefficient survives one noncritical parent update
provided the logarithmic numerator is also nonzero. -/
theorem canonicalLift_ramified_parent_update_ne_zero
    (c s b s' : k)
    (hb : (2 * c + 1) * b = (c + 1) * s)
    (hs' : s' = s + b)
    (hs : s ≠ 0) (hcNum : 3 * c + 2 ≠ 0) :
    s' ≠ 0 := by
  intro hs'zero
  have hu := canonicalLift_ramified_parent_update c s b s' hb hs'
  rw [hs'zero, mul_zero] at hu
  exact (mul_ne_zero hcNum hs) hu.symm

/-- At the final noncritical step, a nonzero parent coefficient forces a
nonzero leading coefficient for the norm-one unit. -/
theorem canonicalLift_ramified_target_ne_zero
    (c s b : k)
    (hb : (2 * c + 1) * b = (c + 1) * s)
    (hs : s ≠ 0) :
    s - 2 * b ≠ 0 := by
  intro hzero
  have ht := canonicalLift_ramified_target c s b hb
  rw [hzero, mul_zero] at ht
  exact hs (neg_eq_zero.mp ht.symm)

/-- Cayley form of the lifted norm-one unit in the discriminant square-root
coordinate `Y = 2*C+1`. -/
theorem canonicalLift_normOne_eq_cayley
    (C Y : k) (hY : Y = 2 * C + 1)
    (hC : C ≠ 0) (hYm : 1 - Y ≠ 0) :
    -(C + 1) / C = (1 + Y) / (1 - Y) := by
  field_simp [hC, hYm]
  rw [hY]
  ring

/-- Exact first-order decomposition of the Cayley unit; if `Y` is a
uniformizer in residue characteristic other than two, its leading
principal-unit coefficient is `2`. -/
theorem cayley_sub_one
    (Y : k) (hYm : 1 - Y ≠ 0) :
    (1 + Y) / (1 - Y) - 1 = 2 * Y / (1 - Y) := by
  field_simp
  ring

/-- At a simple first derivative prime, `A_parent = 1/4 mod Y^2` and
`C = (-1+Y)/2`; hence the new parent coordinate has leading coefficient
`-1` in the `Y` direction. -/
theorem canonicalLift_firstRamified_parent_coordinate
    (Y : k) (h2 : (2 : k) ≠ 0) :
    (1 / 4 : k) * ((-1 + Y) / 2) =
      (-1 / 8 : k) * (1 - Y) := by
  have h4 : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have h8 : (8 : k) ≠ 0 := by
    rw [show (8 : k) = 2 * 2 * 2 by norm_num]
    exact mul_ne_zero (mul_ne_zero h2 h2) h2
  field_simp [h2, h4, h8]
  ring

/-- Algebraic normalization of the first critical discriminant coefficient:
if the rational unit `4` has Teichmuller coefficient `-q4` and the parent
has coefficient `s`, then `1-4*A_parent` has coefficient `q4-s`. -/
theorem canonicalLift_criticalDiscriminant_coefficient
    (q4 s t : k) (ht : t = -q4) :
    -(t + s) = q4 - s := by
  rw [ht]
  ring

/-- At the repeated residue root, the critical derivative obstruction and
the first discriminant coefficient are the same scalar once
`q4 = 2*defect` is imposed. -/
theorem canonicalLift_criticalDefect_eq_discriminant
    (q4 s defect : k) (h2 : (2 : k) ≠ 0) (hq : q4 = 2 * defect) :
    (s / 2 - defect) * 2 = s - q4 := by
  rw [hq]
  field_simp [h2]

end FermatRamifiedRay

section FermatRayPairingNoGo

variable {F : Type*} [Field F]

/-- Even a nonzero weight-one equivariant map can kill the complete
orbit of a distinguished class.  The first coordinate models the ramified
local-unit line detected by the Witt coefficient; the second models the
prime-above-two orbit. -/
theorem nonzero_equivariant_map_can_kill_selected_orbit :
    ∃ (act : Fˣ → F × F → F × F) (chi : F × F → F)
      (inertia selected : F × F),
      (∀ a x, chi (act a x) = (a : F) * chi x) ∧
      chi inertia ≠ 0 ∧
      (∀ a, chi (act a selected) = 0) := by
  refine ⟨fun a x ↦ ((a : F) * x.1, (a : F) * x.2),
    Prod.fst, (1, 0), (0, 1), ?_, ?_, ?_⟩
  · intro a x
    rfl
  · simp
  · intro a
    simp

/-- The same countermodel can impose the additive shadow of norm one:
the detected Kummer radical is anti-invariant under an involution, while the
selected class remains in the kernel. -/
theorem normOne_equivariant_map_still_does_not_force_selected_pairing :
    ∃ (sigma : F × F → F × F) (chi : F × F → F)
      (radical selected : F × F),
      sigma radical = -radical ∧
      chi radical ≠ 0 ∧
      chi selected = 0 := by
  refine ⟨fun x ↦ (-x.1, x.2), Prod.fst, (1, 0), (0, 1), ?_, ?_, ?_⟩
  · ext <;> simp
  · simp
  · simp

end FermatRayPairingNoGo

section OddKummerSquare

variable {G : Type*} [CommGroup G]

/-- Multiplication by a known `ell`-th power does not affect an odd Kummer
class, and squaring is invertible on that class. -/
theorem isPthPower_mul_sq_iff
    (ell : Nat) (hell : Odd ell) (A W g : G)
    (hA : IsPthPower ell A) (hrel : W = A * g ^ 2) :
    IsPthPower ell W ↔ IsPthPower ell g := by
  rcases hell with ⟨s, rfl⟩
  constructor
  · rintro ⟨z, hz⟩
    rcases hA with ⟨x, hx⟩
    have ht : (z * x⁻¹) ^ (2 * s + 1) = g ^ 2 := by
      rw [mul_pow, inv_pow, hz, hx, hrel]
      simp
    have hts : ((z * x⁻¹) ^ s) ^ (2 * s + 1) = (g ^ 2) ^ s := by
      rw [← pow_mul, Nat.mul_comm s (2 * s + 1), pow_mul, ht]
    refine ⟨g * ((z * x⁻¹) ^ s)⁻¹, ?_⟩
    rw [mul_pow, inv_pow, hts]
    rw [show 2 * s + 1 = 1 + 2 * s by omega, pow_add, pow_mul]
    simp
  · rintro ⟨y, hy⟩
    rcases hA with ⟨x, hx⟩
    have hy2 : (y ^ 2) ^ (2 * s + 1) = g ^ 2 := by
      rw [← pow_mul, Nat.mul_comm 2 (2 * s + 1), pow_mul, hy]
    refine ⟨x * y ^ 2, ?_⟩
    rw [mul_pow, hx, hy2, ← hrel]

end OddKummerSquare

section CyclotomicReflectionAlgebra

/-- The real circular unit used in the cubic arm is the product of a
cyclotomic unit with its inverse conjugate. -/
theorem real_cyclotomic_unit_identity
    {F : Type*} [Field F] (x : F) (hx : x ≠ 0) :
    (1 + x) * (1 + x⁻¹) = 2 + x + x⁻¹ := by
  field_simp
  ring

/-- A relative cyclotomic unit and its complex conjugate multiply to a
known root-of-unity factor times its square.  Since that factor is a known
odd Kummer power in the paper's ordinary arm, realification preserves the
selected Kummer class. -/
theorem relative_unit_realification
    {F : Type*} [Field F] (a z : F)
    (ha : a ≠ 0) (hz : z ≠ 0) (ha1 : a ≠ 1) (hz1 : z ≠ 1) :
    ((1 - a) / (1 - z)) * ((1 - a⁻¹) / (1 - z⁻¹)) =
      (z / a) * (((1 - a) / (1 - z)) ^ 2) := by
  field_simp
  ring

/-- Inverting the cubic tower generator turns the cubic relation into
the reciprocal relation whose quadratic coefficient is the inverse parent.
This is the algebraic core of the unconditional normal-basis theorem for
the cubic inverse selector. -/
theorem reciprocal_cubic_inverse_relation
    {F : Type*} [Field F] (g a : F) (hg : g ≠ 0) (ha : a ≠ 0)
    (hrel : g ^ 3 + g + a = 0) :
    (g⁻¹) ^ 3 + a⁻¹ * (g⁻¹) ^ 2 + a⁻¹ = 0 := by
  apply (mul_eq_zero.mp ?_).resolve_left
    (mul_ne_zero ha (pow_ne_zero 3 hg))
  calc
    (a * g ^ 3) *
        ((g⁻¹) ^ 3 + a⁻¹ * (g⁻¹) ^ 2 + a⁻¹) =
        g ^ 3 + g + a := by
          field_simp [hg, ha]
          ring
    _ = 0 := hrel

section CubicNormalBasisCore

variable {K : Type*} [CommRing K] [CharP K 2]

/-- The trace Gram calculation for the three conjugates of the reciprocal
cubic.  Once their sum is the lower inverse selector and their pair sum is
zero, the diagonal trace is its square and the off-diagonal trace vanishes. -/
theorem cubic_scaled_self_dual_core (x y z a : K)
    (hsum : x + y + z = a)
    (hpair : x * y + y * z + z * x = 0) :
    x ^ 2 + y ^ 2 + z ^ 2 = a ^ 2 ∧
      x * y + y * z + z * x = 0 := by
  constructor
  · rw [← hsum, add_pow_char, add_pow_char]
  · exact hpair

/-- The determinant of the immediate cubic Moore/circulant matrix is the
cube of the lower inverse selector.  Thus the selected normal-basis
determinant contains no new current multiplicative coordinate. -/
theorem cubic_moore_det_core (x y z a : K)
    (hsum : x + y + z = a)
    (hpair : x * y + y * z + z * x = 0) :
    x ^ 3 + y ^ 3 + z ^ 3 + x * y * z = a ^ 3 := by
  have hfour : (4 : K) = 0 := by
    change ((4 : Nat) : K) = 0
    rw [CharP.cast_eq_mod K 2 4]
    norm_num
  calc
    x ^ 3 + y ^ 3 + z ^ 3 + x * y * z =
        (x + y + z) ^ 3 +
          (x + y + z) * (x * y + y * z + z * x) := by
            ring_nf
            rw [show (9 : K) = 1 by
              change ((9 : Nat) : K) = 1
              rw [CharP.cast_eq_mod K 2 9]
              norm_num]
            simp [hfour]
    _ = a ^ 3 := by rw [hpair, mul_zero, add_zero, hsum]

/-- Translating the selected Singer cubic by one swaps its two lower
coefficients.  This is the polynomial core of the paper's normal
translate `epsilon_k = eta_k + 1`. -/
theorem selectedSinger_translate_cubic (x a : K)
    (hrel : x ^ 3 + a * x ^ 2 + (a + 1) * x + 1 = 0) :
    (x + 1) ^ 3 + (a + 1) * (x + 1) ^ 2 +
        a * (x + 1) + 1 = 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K) = 1 := by
    simpa using (CharP.cast_eq_mod K 2 3)
  have h4 : (4 : K) = 0 := by
    simpa using (CharP.cast_eq_mod K 2 4)
  have h5 : (5 : K) = 1 := by
    simpa using (CharP.cast_eq_mod K 2 5)
  ring_nf at hrel ⊢
  simpa [h2, h3, h4, h5] using hrel

/-- Moore/circulant determinant in terms of the first two elementary
symmetric coefficients. -/
theorem cubic_moore_det_symmetric_core (x y z b c : K)
    (hsum : x + y + z = b)
    (hpair : x * y + y * z + z * x = c) :
    x ^ 3 + y ^ 3 + z ^ 3 + x * y * z = b ^ 3 + b * c := by
  have hfour : (4 : K) = 0 := by
    change ((4 : Nat) : K) = 0
    rw [CharP.cast_eq_mod K 2 4]
    norm_num
  calc
    x ^ 3 + y ^ 3 + z ^ 3 + x * y * z =
        (x + y + z) ^ 3 +
          (x + y + z) * (x * y + y * z + z * x) := by
            ring_nf
            rw [show (9 : K) = 1 by
              change ((9 : Nat) : K) = 1
              rw [CharP.cast_eq_mod K 2 9]
              norm_num]
            simp [hfour]
    _ = b ^ 3 + b * c := by rw [hsum, hpair]

/-- Determinant of the constant-off-diagonal trace Gram matrix of the
normal Singer translate.  It depends only on the lower selected scalar. -/
theorem singerTranslate_traceGram_det (b : K) :
    Matrix.det !![b ^ 2, b + 1, b + 1;
                  b + 1, b ^ 2, b + 1;
                  b + 1, b + 1, b ^ 2] =
      b ^ 2 * (b ^ 2 + b + 1) ^ 2 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, CharTwo.sub_eq_add]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h6 : (6 : K) = 0 := by
    change ((6 : Nat) : K) = 0
    rw [CharP.cast_eq_mod K 2 6]
    norm_num
  have h8 : (8 : K) = 0 := by
    change ((8 : Nat) : K) = 0
    rw [CharP.cast_eq_mod K 2 8]
    norm_num
  have h9 : (9 : K) = 1 := by
    change ((9 : Nat) : K) = 1
    rw [CharP.cast_eq_mod K 2 9]
    norm_num
  ring_nf
  simp [h2, h6, h8, h9]

/-- The remaining Moore/Gram factor is nonzero when the field has no
nontrivial cube root of unity. -/
theorem singerTranslate_quadratic_factor_ne_zero
    {F : Type*} [Field F] [CharP F 2]
    (b : F) (hno3 : ∀ x : F, x ^ 3 = 1 → x = 1) :
    b ^ 2 + b + 1 ≠ 0 := by
  intro hquad
  have hcubic : b ^ 3 = 1 := by
    have hmul := congrArg (fun z : F => (b + 1) * z) hquad
    have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
    ring_nf at hmul ⊢
    rw [htwo] at hmul
    simp only [mul_zero, add_zero] at hmul
    have hnegone : (-1 : F) = 1 := by
      rw [neg_eq_iff_add_eq_zero]
      calc
        (1 : F) + 1 = 2 := by norm_num
        _ = 0 := htwo
    calc
      b ^ 3 = -1 := eq_neg_of_add_eq_zero_right hmul
      _ = 1 := hnegone
  have hb : b = 1 := hno3 b hcubic
  rw [hb] at hquad
  have hthree : (3 : F) = 1 := by
    change ((3 : Nat) : F) = 1
    rw [CharP.cast_eq_mod F 2 3]
    norm_num
  ring_nf at hquad
  rw [hthree] at hquad
  exact one_ne_zero hquad

end CubicNormalBasisCore

section CoprimePowerOrder

variable {G : Type*} [Group G] [Finite G]

/-- An exponent coprime to an element's order preserves that order. -/
theorem orderOf_eq_of_eq_pow_coprime
    (x y : G) (e : Nat)
    (hy : y = x ^ e) (hcop : (orderOf x).Coprime e) :
    orderOf y = orderOf x := by
  rw [hy, orderOf_pow, hcop.gcd_eq_one, Nat.div_one]

end CoprimePowerOrder

section ArtinSchreierPowerNaturality

variable {K L : Type*} [Semiring K] [Semiring L]

/-- Ring maps preserve both an Artin--Schreier equation and a chosen
`ell`-th root.  This is the algebraic core of the paper's sharp C/D
countermodel boundary: Frobenius conjugation cannot change the selected
power status once the complete cyclotomic ancestry is fixed. -/
theorem map_artinSchreier_pthPower
    (φ : K →+* L) (w z y : K) (ell : Nat)
    (hAS : w ^ 2 + w = z) (hroot : y ^ ell = w) :
    (φ w) ^ 2 + φ w = φ z ∧ (φ y) ^ ell = φ w := by
  constructor
  · simpa only [map_add, map_pow] using congrArg φ hAS
  · simpa only [map_pow] using congrArg φ hroot

end ArtinSchreierPowerNaturality

section FermatSemiprimitiveGauss

open AddChar MulChar

/-- A nontrivial additive character sums to `-1` on the nonzero field
elements.  This is the exceptional-line input to the semiprimitive Gauss
table. -/
theorem nontrivial_additive_unit_sum
    {F R : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CommRing R] [IsDomain R]
    (psi : AddChar F R) (hpsi : psi ≠ 1) :
    (∑ t : F, if t = 0 then 0 else psi t) = -1 := by
  have hterm : ∀ t : F,
      (1 : MulChar F R) t * psi t = if t = 0 then 0 else psi t := by
    intro t
    by_cases ht : t = 0
    · subst t
      simp
    · rw [if_neg ht, MulChar.one_apply (isUnit_iff_ne_zero.mpr ht), one_mul]
  simpa only [gaussSum, hterm] using
    (gaussSum_one_left (R := F) (R' := R) hpsi)

/-- Multiplicative change of variables for a finite-group Gauss sum. -/
theorem gauss_sum_mul_twist
    {G R : Type*} [CommGroup G] [Fintype G] [CommRing R]
    (chi : G →* R) (psi : G → R) (b : G) :
    chi b * (∑ x : G, chi x * psi (b * x)) =
      ∑ x : G, chi x * psi x := by
  rw [Finset.mul_sum]
  calc
    ∑ x : G, chi b * (chi x * psi (b * x)) =
        ∑ x : G, chi (b * x) * psi (b * x) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [map_mul]
          ring
    _ = ∑ x : G, chi x * psi x := by
      simpa only [Equiv.coe_mulLeft] using
        (Equiv.sum_comp (Equiv.mulLeft b)
          (fun x : G => chi x * psi x))

/-- Solved form of the multiplicative Gauss twist. -/
theorem twist_eq_inv_mul
    {G R : Type*} [CommGroup G] [Fintype G] [Field R]
    (chi : G →* R) (psi : G → R) (b : G) (hb : chi b ≠ 0) :
    (∑ x : G, chi x * psi (b * x)) =
      (chi b)⁻¹ * ∑ x : G, chi x * psi x := by
  have h := gauss_sum_mul_twist chi psi b
  apply (mul_left_cancel₀ hb)
  rw [h]
  field_simp

/-- A quotient-line sum with one exceptional weight evaluates exactly to
`q`.  This is the finite combinatorial core of the paper's semiprimitive
Gauss calculation. -/
theorem gauss_from_one_exceptional_line
    {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (exceptional : I) (weight character : I → R) (q : R)
    (hweight : weight exceptional = q - 1)
    (hother : ∀ i, i ≠ exceptional → weight i = -1)
    (hchar : ∑ i : I, character i = 0)
    (hexceptional : character exceptional = 1) :
    ∑ i : I, character i * weight i = q := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ exceptional)] at hchar ⊢
  rw [hexceptional] at hchar
  rw [hweight, hexceptional]
  have hrest : ∑ x ∈ Finset.univ.erase exceptional, character x = -1 := by
    linear_combination hchar
  have hweighted :
      ∑ x ∈ Finset.univ.erase exceptional, character x * weight x = 1 := by
    calc
      ∑ x ∈ Finset.univ.erase exceptional, character x * weight x =
          ∑ x ∈ Finset.univ.erase exceptional, -(character x) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hother i (Finset.ne_of_mem_erase hi)]
            ring
      _ = -(∑ x ∈ Finset.univ.erase exceptional, character x) := by simp
      _ = 1 := by rw [hrest]; ring
  rw [hweighted]
  ring

/-- Denominator-cleared large signed-period value. -/
theorem period_large_denominator_cleared
    (ell q r : ℤ) (hq : q + 1 = ell * r) :
    ell * ((q - 1) - (r - 1)) = (ell - 1) * q - 1 := by
  linear_combination hq

/-- Denominator-cleared small signed-period value. -/
theorem period_small_denominator_cleared
    (ell q r : ℤ) (hq : q + 1 = ell * r) :
    ell * (-r) = -(q + 1) := by
  linear_combination hq

/-- Moving one exceptional label does not change any symmetric sum of the
labelled table. -/
theorem labelled_exceptional_sum_blind
    {I R S : Type*} [Fintype I] [DecidableEq I] [AddCommMonoid S]
    (first second : I) (large small : R) (f : R → S) :
    (∑ i : I, f (if i = first then large else small)) =
      ∑ i : I, f (if i = second then large else small) := by
  classical
  let swap : I ≃ I := Equiv.swap first second
  calc
    (∑ i : I, f (if i = first then large else small)) =
        ∑ i : I, f (if swap i = first then large else small) :=
      (Equiv.sum_comp swap
        (fun i : I => f (if i = first then large else small))).symm
    _ = ∑ i : I, f (if i = second then large else small) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [swap, Equiv.swap_apply_def]
      by_cases hfs : first = second
      · simp [hfs]
      · by_cases hi : i = first
        · subst i
          simp [hfs, Ne.symm hfs]
        · by_cases hj : i = second
          · subst i
            simp
          · simp [hi, hj]

/-- The trivial label carries the large value exactly when it is the
exceptional label. -/
theorem trivial_label_is_exceptional_iff
    {I R : Type*} [DecidableEq I]
    (trivial exceptional : I) (large small : R) (hne : large ≠ small) :
    (if trivial = exceptional then large else small) = large ↔
      trivial = exceptional := by
  by_cases h : trivial = exceptional
  · simp [h]
  · simp [h, hne.symm]

end FermatSemiprimitiveGauss

section ConwayBitKummer

/-- If an upper block is obtained by multiplying every lower basis vector by
one fixed element, and a multiplicative character is trivial on the lower
block, then its value is constant on the upper block. -/
theorem upper_basis_has_one_phase
    {L M I : Type*} [CommGroup L] [CommGroup M]
    (chi : L →* M) (c : L) (lower upper : I → L)
    (hupper : ∀ i, upper i = c * lower i)
    (hlower : ∀ i, chi (lower i) = 1) :
    ∀ i, chi (upper i) = chi c := by
  intro i
  rw [hupper i, map_mul, hlower i, mul_one]

/-- Every multiplicative monomial in lower and upper basis vectors remembers
only the number of upper factors. -/
theorem basis_monomial_has_only_upper_weight
    {L M I J : Type*} [CommGroup L] [CommGroup M]
    (chi : L →* M) (c : L) (lower : I → L) (upper : J → L)
    (s : Finset I) (t : Finset J)
    (hlower : ∀ i, chi (lower i) = 1)
    (hupper : ∀ j, chi (upper j) = chi c) :
    chi ((∏ i ∈ s, lower i) * (∏ j ∈ t, upper j)) =
      (chi c) ^ t.card := by
  classical
  rw [map_mul, map_prod, map_prod]
  simp only [hlower, Finset.prod_const_one, one_mul, hupper]
  exact Finset.prod_const (chi c)

/-- On an odd-order cyclic target, inverse-squaring detects the identity.
Writing the odd exponent as `2*k+1` avoids any primality machinery. -/
theorem inv_square_eq_one_iff_of_odd_torsion
    {G : Type*} [CommGroup G] (C H : G) (k : Nat)
    (htors : C ^ (2 * k + 1) = 1)
    (hphase : H = C⁻¹ * C⁻¹) :
    H = 1 ↔ C = 1 := by
  constructor
  · intro hH
    have hsquare : C ^ 2 = 1 := by
      calc
        C ^ 2 = (C⁻¹ * C⁻¹)⁻¹ := by group
        _ = H⁻¹ := by rw [hphase]
        _ = 1 := by rw [hH, inv_one]
    have hodd : C ^ (2 * k + 1) = C := by
      calc
        C ^ (2 * k + 1) = C ^ (2 * k) * C ^ 1 := by rw [pow_add]
        _ = (C ^ 2) ^ k * C ^ 1 := by rw [pow_mul]
        _ = C := by rw [hsquare]; simp
    rw [hodd] at htors
    exact htors
  · intro hC
    simp [hphase, hC]

/-- Combining the two cores: the selected phase is trivial exactly when all
upper basis vectors have trivial character. -/
theorem selected_phase_trivial_iff_all_upper_trivial
    {L M I : Type*} [CommGroup L] [CommGroup M] [Nonempty I]
    (chi : L →* M) (c : L) (lower upper : I → L)
    (C H : M) (k : Nat)
    (hC : C = chi c)
    (htors : C ^ (2 * k + 1) = 1)
    (hphase : H = C⁻¹ * C⁻¹)
    (hupper : ∀ i, upper i = c * lower i)
    (hlower : ∀ i, chi (lower i) = 1) :
    H = 1 ↔ ∀ i, chi (upper i) = 1 := by
  rw [inv_square_eq_one_iff_of_odd_torsion C H k htors hphase]
  constructor
  · intro h i
    rw [upper_basis_has_one_phase chi c lower upper hupper hlower i, ← hC, h]
  · intro h
    let i : I := Classical.choice inferInstance
    have hi := h i
    rw [upper_basis_has_one_phase chi c lower upper hupper hlower i, ← hC] at hi
    exact hi

/-- Deleting one point from a uniformly labelled finite set decreases only
the fibre carrying that point.  This is the counting core of the first-upper-
Conway-block histogram. -/
theorem deleted_uniform_fiber_card
    {Q M : Type*} [Fintype Q] [DecidableEq Q] [DecidableEq M]
    (label : Q → M) (base : Q) (one : M) (r : Nat)
    (hbase : label base = one)
    (huniform : ∀ ξ, (Finset.univ.filter fun x => label x = ξ).card = r)
    (ξ : M) :
    ((Finset.univ.erase base).filter fun x => label x = ξ).card =
      if ξ = one then r - 1 else r := by
  rw [Finset.filter_erase]
  by_cases hξ : ξ = one
  · subst ξ
    rw [Finset.card_erase_of_mem]
    · rw [huniform]
      simp
    · simp [hbase]
  · have hnot : base ∉ Finset.univ.filter (fun x => label x = ξ) := by
      simp [hbase, Ne.symm hξ]
    rw [Finset.erase_eq_self.mpr hnot, huniform]
    simp [hξ]

/-- The two Frobenius-norm terms in the first-upper-block factorization
collapse to the additive polynomial in characteristic two. -/
theorem upper_block_norm_collapse
    {R : Type*} [CommRing R] [CharP R 2] (c x xq : R) :
    (c + xq) * (c + x + 1) + (c + 1 + xq) * (c + x) = xq + x := by
  ring_nf
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  rw [htwo]
  simp

end ConwayBitKummer

section CubicNormalBridge

variable {K : Type*} [Field K] [CharP K 2]

/-- In characteristic two, two elements with the same square agree; this
packages the square-root step in the beta/epsilon normal-basis bridge. -/
theorem cubicNormal_square_root_bridge (ε s h : K)
    (hs : s ^ 2 = ε) (hh : h ^ 2 = ε ^ 2 + ε) : h = ε + s := by
  have heq : h ^ 2 = (ε + s) ^ 2 := by
    rw [hh]
    calc
      ε ^ 2 + ε = ε ^ 2 + s ^ 2 := by rw [hs]
      _ = (ε + s) ^ 2 := by
        have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
        ring_nf
        rw [htwo]
        ring
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp heq) with heq | heq
  · exact heq
  · have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hneg (t : K) : -t = t := by
      rw [neg_eq_iff_add_eq_zero, ← two_mul, htwo, zero_mul]
    simpa only [hneg] using heq

/-- Load-bearing three-term identity behind the canonical half-circulant
change from the epsilon normal basis to the beta normal basis. -/
theorem cubicNormal_beta_three_term (β ε s h : K)
    (hs : s ^ 2 = ε) (hh : h ^ 2 = ε ^ 2 + ε) (hβ : h = 1 + β) :
    β = 1 + ε + s := by
  have hb := cubicNormal_square_root_bridge ε s h hs hh
  rw [hβ] at hb
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h11 : (1 : K) + 1 = 0 := by
    calc
      (1 : K) + 1 = 2 := by norm_num
      _ = 0 := htwo
  calc
    β = (1 + β) + 1 := by
      symm
      calc
        (1 + β) + 1 = β + (1 + 1) := by ring
        _ = β := by rw [h11, add_zero]
    _ = (ε + s) + 1 := by rw [hb]
    _ = 1 + ε + s := by ring

variable {R : Type*} [CommRing R]

/-- The Singer exponent identity used before taking the characteristic-two
square root in the normal-basis bridge. -/
theorem singer_square_identity (η : R) (q : Nat)
    (h : η ^ (q + 1) = η + 1) : η ^ (q + 2) = η ^ 2 + η := by
  calc
    η ^ (q + 2) = η ^ (q + 1) * η := by
      rw [show q + 2 = (q + 1) + 1 by omega, pow_succ]
    _ = (η + 1) * η := by rw [h]
    _ = η ^ 2 + η := by ring

end CubicNormalBridge

section CubicFrobeniusTwistCore

variable {E : Type*} [Field E]

/-- Multiplicative Hilbert--90 twists of Frobenius are conjugate to
Frobenius itself. -/
theorem frobenius_twist_conjugacy_core
    (φ : E ≃+* E) (u x : E) :
    u⁻¹ * φ (u * x) = (u⁻¹ * φ u) * φ x := by
  rw [map_mul]
  ring

/-- A norm-one multiplicative twist of an order-three Frobenius still has
cube one. -/
theorem norm_one_twist_cube_core
    (φ : E ≃+* E) (θ x : E)
    (hφ3 : φ (φ (φ x)) = x)
    (hnorm : θ * φ θ * φ (φ θ) = 1) :
    θ * φ (θ * φ (θ * φ x)) = x := by
  simp only [map_mul]
  calc
    θ * (φ θ * (φ (φ θ) * φ (φ (φ x)))) =
        (θ * φ θ * φ (φ θ)) * φ (φ (φ x)) := by ring
    _ = x := by rw [hnorm, one_mul, hφ3]

end CubicFrobeniusTwistCore

section CubicFrobeniusProjectors

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Cumulative trace-shaped projector for the cubic Frobenius tower. -/
def cubicCumulativeProjector (σ : V →ₗ[F] V) (k j : Nat) : V →ₗ[F] V :=
  ∑ r ∈ Finset.range (3 ^ (k - j)), σ ^ (r * 3 ^ j)

/-- Exact cubic Frobenius block obtained from two successive cumulative
projectors. In characteristic two the subtraction is their sum. -/
def cubicExactProjector (σ : V →ₗ[F] V) (k j : Nat) : V →ₗ[F] V :=
  if j = 0 then cubicCumulativeProjector σ k 0
  else cubicCumulativeProjector σ k j -
    cubicCumulativeProjector σ k (j - 1)

theorem cubicExactProjector_zero (σ : V →ₗ[F] V) (k : Nat) :
    cubicExactProjector σ k 0 = cubicCumulativeProjector σ k 0 := by
  simp [cubicExactProjector]

theorem cubicExactProjector_succ_apply
    (σ : V →ₗ[F] V) (k j : Nat) (v : V) :
    cubicExactProjector σ k (j + 1) v =
      cubicCumulativeProjector σ k (j + 1) v -
        cubicCumulativeProjector σ k j v := by
  simp [cubicExactProjector]

theorem cubicExactProjector_succ_value
    (σ : V →ₗ[F] V) (k j : Nat) (v bnext bprev : V)
    (hnext : cubicCumulativeProjector σ k (j + 1) v = bnext)
    (hprev : cubicCumulativeProjector σ k j v = bprev) :
    cubicExactProjector σ k (j + 1) v = bnext - bprev := by
  rw [cubicExactProjector_succ_apply, hnext, hprev]

end CubicFrobeniusProjectors

section CubicDerivativeRecurrence

open Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The logarithmic derivative identity is preserved by the cubic Conway
coefficient recurrence in characteristic two. -/
theorem cubicDerivativeRecurrenceStep (P : R[X])
    (h : X * derivative P = P + 1) :
    X * derivative (P ^ 3 + P ^ 2 + 1) =
      (P ^ 3 + P ^ 2 + 1) + 1 := by
  simp only [derivative_add, derivative_pow, derivative_one]
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have hthree : (3 : R) = 1 := by
    rw [show (3 : R) = 2 + 1 by norm_num, htwo, zero_add]
  simp [htwo, hthree]
  rw [show X * (P ^ 2 * derivative P) =
      P ^ 2 * (X * derivative P) by ring]
  rw [h]
  ring_nf
  have htwoPoly : (2 : R[X]) = 0 := CharP.cast_eq_zero R[X] 2
  rw [htwoPoly, zero_add]

end CubicDerivativeRecurrence

end CyclotomicReflectionAlgebra

section KummerTailTransport

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- Across a quadratic tower edge whose Kummer quotients are identified by
inclusion, norm makes the new root class one half of the old class.  Hence
the product of the included old element and the new root is transported by
the scalar `3/2`: the denominator-free identity is
`2 * kappaNext = 3 * i(kappa)`. -/
theorem quadratic_kummer_tail_transport
    (i : A ≃+ B) (N : B →+ A)
    (hNi : ∀ x, N (i x) = 2 • x)
    (c : B) (kappa : A) (hc : N c = kappa) :
    2 • c = i kappa ∧ 2 • (i kappa + c) = 3 • i kappa := by
  have hcHalf : 2 • i.symm c = kappa := by
    calc
      2 • i.symm c = N (i (i.symm c)) := (hNi _).symm
      _ = N c := by simp
      _ = kappa := hc
  have hcDouble : 2 • c = i kappa := by
    calc
      2 • c = i (2 • i.symm c) := by simp
      _ = i kappa := by rw [hcHalf]
  refine ⟨hcDouble, ?_⟩
  rw [nsmul_add, hcDouble]
  simp only [three_nsmul, two_nsmul]
  ac_rfl

end KummerTailTransport

section FermatEulerTail

variable {G : Type*} [CommMonoid G]

/-- The selected Euler/Kummer symbol is cubed at every Conway edge after
its birth.  Here `a^Q = a` is lower-field Frobenius fixity and
`c^(Q+1) = a` is the relative norm identity. -/
theorem conway_euler_symbol_tail_cube
    (a c : G) (Q h : Nat)
    (ha : a ^ Q = a) (hnorm : c ^ (Q + 1) = a) :
    (a * c) ^ ((Q + 1) * h) = (a ^ h) ^ 3 := by
  rw [mul_pow]
  rw [pow_mul, pow_mul, hnorm]
  rw [pow_succ, ha]
  rw [mul_pow]
  simp [pow_succ, mul_assoc]

/-- The inverse-square Hilbert normalization is cubed by the same tail
transport. -/
theorem inverse_square_cube_transport
    {H : Type*} [CommGroup H] (Bnext Bprev : H)
    (h : Bnext = Bprev ^ 3) :
    (Bnext⁻¹) ^ 2 = ((Bprev⁻¹) ^ 2) ^ 3 := by
  rw [h, inv_pow, ← pow_mul, ← pow_mul]
  norm_num

/-- Dividing the new quadratic generator by the lower-field square root of
its norm produces the canonical norm-one component. -/
theorem canonical_new_component_norm_one
    {H : Type*} [CommGroup H] (s c : H) (Q : Nat)
    (hs : s ^ Q = s) (hc : c ^ (Q + 1) = s ^ 2) :
    (c / s) ^ (Q + 1) = 1 := by
  rw [div_pow, hc, div_eq_one]
  calc
    s ^ 2 = s * s := pow_two s
    _ = s ^ Q * s := by rw [hs]
    _ = s ^ (Q + 1) := (pow_succ s Q).symm

/-- Frobenius ratio is unchanged after dividing by a fixed lower-field
element. -/
theorem canonical_new_component_ratio
    {H : Type*} [CommGroup H] (s c : H) (Q : Nat)
    (hs : s ^ Q = s) :
    (c / s) ^ Q / (c / s) = c ^ Q / c := by
  rw [div_pow, hs]
  simp [div_eq_mul_inv]

end FermatEulerTail

section FermatFibonacciCompression

variable {R : Type*} [CommRing R]

/-- Evaluation at `a` of the characteristic-two Fibonacci polynomials
`S₀ = 0`, `S₁ = 1`, and `Sᵣ₊₂ = Sᵣ₊₁ + a Sᵣ`. -/
def fibPolyValue (a : R) : Nat → R
  | 0 => 0
  | 1 => 1
  | n + 2 => fibPolyValue a (n + 1) + a * fibPolyValue a n

/-- Evaluation at `a` of the formal derivative of `Sᵣ`.  Differentiating
`Sᵣ₊₂ = Sᵣ₊₁ + X Sᵣ` gives the displayed recursive definition. -/
def fibPolyDerivativeValue (a : R) : Nat → R
  | 0 => 0
  | 1 => 0
  | n + 2 =>
      fibPolyDerivativeValue a (n + 1) + fibPolyValue a n +
        a * fibPolyDerivativeValue a n

/-- The recursively presented partial Frobenius trace.  The theorem
`partialFrobeniusTrace_eq_sum` identifies it with
`a + a² + ⋯ + a^(2^(t-1))` after imposing characteristic two. -/
def partialFrobeniusTrace (a : R) : Nat → R
  | 0 => 0
  | t + 1 => (partialFrobeniusTrace a t) ^ 2 + a

@[simp]
theorem partialFrobeniusTrace_zero (a : R) :
    partialFrobeniusTrace a 0 = 0 := by
  rfl

theorem partialFrobeniusTrace_succ (a : R) (t : Nat) :
    partialFrobeniusTrace a (t + 1) =
      (partialFrobeniusTrace a t) ^ 2 + a := by
  rfl

variable [CharP R 2]

/-- In characteristic two, the recursive partial trace is literally the
sum of the first `t` Frobenius conjugates. -/
theorem partialFrobeniusTrace_eq_sum (a : R) (t : Nat) :
    partialFrobeniusTrace a t =
      ∑ j ∈ Finset.range t, a ^ (2 ^ j) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [partialFrobeniusTrace_succ, ih, Finset.sum_range_succ']
      rw [sum_pow_char]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        rw [← pow_mul]
        congr 1
      · simp

/-- Partial Frobenius traces are additive in characteristic two. -/
theorem partialFrobeniusTrace_additive (a b : R) (s : Nat) :
    partialFrobeniusTrace (a + b) s =
      partialFrobeniusTrace a s + partialFrobeniusTrace b s := by
  simp only [partialFrobeniusTrace_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact add_pow_expChar_pow a b 2 j

/-- Frobenius powering commutes with a partial Frobenius trace. -/
theorem partialFrobeniusTrace_pow_two (a : R) (s d : Nat) :
    (partialFrobeniusTrace a s) ^ (2 ^ d) =
      partialFrobeniusTrace (a ^ (2 ^ d)) s := by
  simp only [partialFrobeniusTrace_eq_sum]
  rw [sum_pow_char_pow]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, ← pow_mul]
  congr 1
  ac_rfl

/-- Splitting the index of a partial Frobenius trace. -/
theorem partialFrobeniusTrace_add_index (a : R) (d r : Nat) :
    partialFrobeniusTrace a (d + r) =
      partialFrobeniusTrace a d +
        (partialFrobeniusTrace a r) ^ (2 ^ d) := by
  simp only [partialFrobeniusTrace_eq_sum]
  rw [Finset.sum_range_add]
  congr 1
  rw [sum_pow_char_pow]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    a ^ 2 ^ (d + j) = a ^ (2 ^ j * 2 ^ d) := by
      congr 1
      rw [pow_add]
      ac_rfl
    _ = (a ^ 2 ^ j) ^ 2 ^ d := by rw [pow_mul]

/-- The index split becomes ordinary addition when the coefficient is fixed
by the relevant Frobenius power. -/
theorem partialFrobeniusTrace_add_index_of_fixed
    (A : R) (d r : Nat) (hA : A ^ (2 ^ d) = A) :
    partialFrobeniusTrace A (d + r) =
      partialFrobeniusTrace A d + partialFrobeniusTrace A r := by
  rw [partialFrobeniusTrace_add_index]
  rw [partialFrobeniusTrace_pow_two, hA]

/-- Exact relative-trace descent for the compressed Conway--Fermat ratio:
if the relative conjugate of `a` is `a + A`, the relative trace of
`1 + T_s(a)` is `T_s(A)`. -/
theorem partialFrobeniusTrace_conjugate_descent
    (a A : R) (s d : Nat) (ha : a ^ (2 ^ d) = a + A) :
    (1 + partialFrobeniusTrace a s) ^ (2 ^ d) +
        (1 + partialFrobeniusTrace a s) =
      partialFrobeniusTrace A s := by
  rw [add_pow_expChar_pow]
  rw [one_pow]
  rw [partialFrobeniusTrace_pow_two, ha]
  rw [partialFrobeniusTrace_additive]
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  ring_nf
  simp [h2]

/-- Characteristic-two doubling for the selected Fibonacci recurrence. -/
theorem fibPolyValue_double (a : R) (r : Nat) :
    fibPolyValue a (2 * r) = (fibPolyValue a r) ^ 2 ∧
    fibPolyValue a (2 * r + 1) =
      (fibPolyValue a (r + 1)) ^ 2 + a * (fibPolyValue a r) ^ 2 := by
  induction r with
  | zero => simp [fibPolyValue]
  | succ r ih =>
      rcases ih with ⟨heven, hodd⟩
      have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
      constructor
      · rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega]
        rw [show fibPolyValue a ((2 * r + 1) + 1) =
            fibPolyValue a (2 * r + 1) + a * fibPolyValue a (2 * r) by
              rw [show (2 * r + 1) + 1 = 2 * r + 2 by omega]
              simp only [fibPolyValue]]
        rw [hodd, heven]
        ring_nf
        simp [h2]
      · rw [show 2 * (r + 1) + 1 = (2 * r + 2) + 1 by omega]
        rw [show fibPolyValue a ((2 * r + 2) + 1) =
            fibPolyValue a (2 * r + 2) + a * fibPolyValue a (2 * r + 1) by
              rw [show (2 * r + 2) + 1 = (2 * r + 1) + 2 by omega]
              simp only [fibPolyValue]]
        have hnext : fibPolyValue a (2 * r + 2) =
            (fibPolyValue a (r + 1)) ^ 2 := by
          rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega]
          rw [show fibPolyValue a ((2 * r + 1) + 1) =
              fibPolyValue a (2 * r + 1) + a * fibPolyValue a (2 * r) by
                rw [show (2 * r + 1) + 1 = 2 * r + 2 by omega]
                simp only [fibPolyValue]]
          rw [hodd, heven]
          ring_nf
          simp [h2]
        rw [hnext, hodd]
        rw [show fibPolyValue a (r + 2) =
            fibPolyValue a (r + 1) + a * fibPolyValue a r by
              simp only [fibPolyValue]]
        ring_nf
        simp [h2]

/-- In characteristic two the derivative of every even-index Fibonacci
polynomial vanishes, while the derivative at odd index `2r+1` is `Sᵣ²`. -/
theorem fibPolyDerivativeValue_double (a : R) (r : Nat) :
    fibPolyDerivativeValue a (2 * r) = 0 ∧
    fibPolyDerivativeValue a (2 * r + 1) = (fibPolyValue a r) ^ 2 := by
  induction r with
  | zero => simp [fibPolyDerivativeValue, fibPolyValue]
  | succ r ih =>
      rcases ih with ⟨heven, hodd⟩
      have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
      have hevenNext : fibPolyDerivativeValue a (2 * (r + 1)) = 0 := by
        rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega]
        rw [show fibPolyDerivativeValue a ((2 * r + 1) + 1) =
            fibPolyDerivativeValue a (2 * r + 1) + fibPolyValue a (2 * r) +
              a * fibPolyDerivativeValue a (2 * r) by
                rw [show (2 * r + 1) + 1 = 2 * r + 2 by omega]
                simp only [fibPolyDerivativeValue]]
        rw [hodd, heven, (fibPolyValue_double a r).1]
        ring_nf
        simp [h2]
      constructor
      · exact hevenNext
      · rw [show 2 * (r + 1) + 1 = (2 * r + 2) + 1 by omega]
        rw [show fibPolyDerivativeValue a ((2 * r + 2) + 1) =
            fibPolyDerivativeValue a (2 * r + 2) + fibPolyValue a (2 * r + 1) +
              a * fibPolyDerivativeValue a (2 * r + 1) by
                rw [show (2 * r + 2) + 1 = (2 * r + 1) + 2 by omega]
                simp only [fibPolyDerivativeValue]]
        rw [show fibPolyDerivativeValue a (2 * r + 2) = 0 by
              simpa [Nat.mul_add] using hevenNext]
        rw [(fibPolyValue_double a r).2, hodd]
        ring_nf
        simp [h2]

/-- An odd Fibonacci zero is simple as soon as its half-index value is
nonzero.  This is the kernel-checked multiplicity obstruction used in the
Conway--Fermat selected-factor analysis. -/
theorem fibPolyDerivativeValue_odd_ne_zero
    {K : Type*} [Field K] [CharP K 2] (a : K) (r : Nat)
    (hr : fibPolyValue a r ≠ 0) :
    fibPolyDerivativeValue a (2 * r + 1) ≠ 0 := by
  rw [(fibPolyDerivativeValue_double a r).2]
  exact pow_ne_zero 2 hr

/-- Pulling a power of two out of the Fibonacci index is Frobenius
powering in characteristic two. -/
theorem fibPolyValue_pow_two_mul (a : R) (t h : Nat) :
    fibPolyValue a ((2 ^ t) * h) = (fibPolyValue a h) ^ (2 ^ t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have ht : 2 ^ (t + 1) = (2 ^ t) * 2 := by
        rw [pow_succ]
      calc
        fibPolyValue a ((2 ^ (t + 1)) * h) =
            fibPolyValue a (2 * ((2 ^ t) * h)) := by
              rw [ht]
              congr 1
              ac_rfl
        _ = (fibPolyValue a ((2 ^ t) * h)) ^ 2 :=
          (fibPolyValue_double a ((2 ^ t) * h)).1
        _ = ((fibPolyValue a h) ^ (2 ^ t)) ^ 2 := by rw [ih]
        _ = (fibPolyValue a h) ^ (2 ^ (t + 1)) := by
          rw [ht, ← pow_mul]

/-- Exact trailing-zero compression of a Fibonacci index in characteristic
two.  This is the formal algebraic core of the continued-fraction reduction
for a hypothetical Conway--Fermat failure. -/
theorem fibPolyValue_trailing_zero_compression (a : R) (t h : Nat) :
    fibPolyValue a ((2 ^ t) * h + 1) =
      (fibPolyValue a (h + 1)) ^ (2 ^ t) +
        partialFrobeniusTrace a t * (fibPolyValue a h) ^ (2 ^ t) := by
  induction t with
  | zero => simp [partialFrobeniusTrace]
  | succ t ih =>
      have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
      have ht : 2 ^ (t + 1) = (2 ^ t) * 2 := by
        rw [pow_succ]
      have hA : ((fibPolyValue a (h + 1)) ^ (2 ^ t)) ^ 2 =
          (fibPolyValue a (h + 1)) ^ (2 ^ (t + 1)) := by
        rw [ht, ← pow_mul]
      have hB : ((fibPolyValue a h) ^ (2 ^ t)) ^ 2 =
          (fibPolyValue a h) ^ (2 ^ (t + 1)) := by
        rw [ht, ← pow_mul]
      calc
        fibPolyValue a ((2 ^ (t + 1)) * h + 1) =
            fibPolyValue a (2 * ((2 ^ t) * h) + 1) := by
              rw [ht]
              congr 2
              ac_rfl
        _ = (fibPolyValue a ((2 ^ t) * h + 1)) ^ 2 +
              a * (fibPolyValue a ((2 ^ t) * h)) ^ 2 :=
          (fibPolyValue_double a ((2 ^ t) * h)).2
        _ = ((fibPolyValue a (h + 1)) ^ (2 ^ t) +
                partialFrobeniusTrace a t *
                  (fibPolyValue a h) ^ (2 ^ t)) ^ 2 +
              a * ((fibPolyValue a h) ^ (2 ^ t)) ^ 2 := by
          rw [ih, fibPolyValue_pow_two_mul]
        _ = (fibPolyValue a (h + 1)) ^ (2 ^ (t + 1)) +
              partialFrobeniusTrace a (t + 1) *
                (fibPolyValue a h) ^ (2 ^ (t + 1)) := by
          rw [partialFrobeniusTrace_succ]
          ring_nf
          simp [h2]

/-- Over a field, the trailing-zero compression is equivalently a single
continued-fraction ratio equation. -/
theorem fibPolyValue_trailing_zero_ratio_iff
    {K : Type*} [Field K] [CharP K 2]
    (a : K) (t h : Nat) (hSh : fibPolyValue a h ≠ 0) :
    fibPolyValue a ((2 ^ t) * h + 1) = 0 ↔
      (fibPolyValue a (h + 1) / fibPolyValue a h) ^ (2 ^ t) =
        partialFrobeniusTrace a t := by
  rw [fibPolyValue_trailing_zero_compression, div_pow]
  have hden : (fibPolyValue a h) ^ (2 ^ t) ≠ 0 := pow_ne_zero _ hSh
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  constructor
  · intro hz
    apply (div_eq_iff hden).2
    have hneg :
        - (partialFrobeniusTrace a t * (fibPolyValue a h) ^ (2 ^ t)) =
          partialFrobeniusTrace a t * (fibPolyValue a h) ^ (2 ^ t) := by
      apply eq_of_sub_eq_zero
      ring_nf
      simp [h2]
    exact (eq_neg_of_add_eq_zero_left hz).trans hneg
  · intro hratio
    have heq := (div_eq_iff hden).1 hratio
    rw [heq]
    ring_nf
    simp [h2]

/-- If `delta` divides an index `d = 2^t h + 1` and is larger than the
extracted power of two, neither complementary index can already be a zero
index. -/
theorem fermat_complement_indices_not_dvd
    (delta d t h : Nat) (ht : 0 < t)
    (hd : d = (2 ^ t) * h + 1) (hdelta_d : delta ∣ d)
    (hlarge : 2 ^ t < delta) :
    ¬delta ∣ h ∧ ¬delta ∣ h + 1 := by
  constructor
  · intro hdelta_h
    have hmul : delta ∣ (2 ^ t) * h := dvd_mul_of_dvd_right hdelta_h _
    have hd' : delta ∣ (2 ^ t) * h + 1 := by simpa [hd] using hdelta_d
    have h1 : delta ∣ 1 := (Nat.dvd_add_iff_right hmul).mpr hd'
    have : delta = 1 := Nat.eq_one_of_dvd_one h1
    have hp : 0 < 2 ^ t := pow_pos (by omega) _
    omega
  · intro hdelta_h1
    have hmul : delta ∣ (2 ^ t) * (h + 1) :=
      dvd_mul_of_dvd_right hdelta_h1 _
    have hpow : 1 < 2 ^ t := one_lt_pow₀ (by omega : 1 < 2) ht.ne'
    have heq : (2 ^ t) * (h + 1) = d + (2 ^ t - 1) := by
      rw [Nat.mul_add, hd]
      omega
    have hsum : delta ∣ d + (2 ^ t - 1) := by simpa [heq] using hmul
    have hsmall : delta ∣ 2 ^ t - 1 :=
      (Nat.dvd_add_iff_right hdelta_d).mpr hsum
    have hpos : 0 < 2 ^ t - 1 := by omega
    have hle : delta ≤ 2 ^ t - 1 := Nat.le_of_dvd hpos hsmall
    omega

end FermatFibonacciCompression

section ConwayTopBitCompanion

variable {R : Type*} [CommRing R]

/-- Coordinate identity behind the literal-top-bit multiplication block
`[[0, M^2], [M, M]]`. -/
theorem conwayTopBit_mul_coords
    (A c x₀ x₁ : R) (hc : c ^ 2 = c + A) :
    (A * c) * (x₀ + c * x₁) =
      A ^ 2 * x₁ + c * (A * x₀ + A * x₁) := by
  calc
    (A * c) * (x₀ + c * x₁) =
        A * c * x₀ + A * c ^ 2 * x₁ := by ring
    _ = A * c * x₀ + A * (c + A) * x₁ := by rw [hc]
    _ = A ^ 2 * x₁ + c * (A * x₀ + A * x₁) := by ring

/-- Iteration of the Fibonacci companion `C_a(x,y)=(a*y,x+y)`. -/
def fibCompanionIter (a : R) : Nat → R × R → R × R
  | 0, v => v
  | r + 1, v =>
      let w := fibCompanionIter a r v
      (a * w.2, w.1 + w.2)

/-- Exact entries of every positive power of the Fibonacci companion. -/
theorem fibCompanionIter_succ_formula
    (a x y : R) (r : Nat) :
    fibCompanionIter a (r + 1) (x, y) =
      (a * fibPolyValue a r * x + a * fibPolyValue a (r + 1) * y,
       fibPolyValue a (r + 1) * x + fibPolyValue a (r + 2) * y) := by
  induction r with
  | zero => simp [fibCompanionIter, fibPolyValue]
  | succ r ih =>
      rw [show r + 1 + 1 = (r + 1) + 1 by rfl]
      rw [fibCompanionIter]
      rw [ih]
      simp only
      rw [show fibPolyValue a (r + 3) =
          fibPolyValue a (r + 2) + a * fibPolyValue a (r + 1) by
            simp only [fibPolyValue]]
      rw [show fibPolyValue a (r + 2) =
          fibPolyValue a (r + 1) + a * fibPolyValue a r by
            simp only [fibPolyValue]]
      ring_nf

/-- A positive companion power is scalar exactly at a Fibonacci zero.
Thus its first projective return is the first zero of `S_r(a)`. -/
theorem fibCompanionIter_scalar_iff
    (a scalar : R) (r : Nat) :
    (∀ x y : R, fibCompanionIter a (r + 1) (x, y) =
      (scalar * x, scalar * y)) ↔
      fibPolyValue a (r + 1) = 0 ∧
        scalar = fibPolyValue a (r + 2) := by
  constructor
  · intro h
    have hs : fibPolyValue a (r + 1) = 0 := by
      have hv := congrArg Prod.snd (h 1 0)
      rw [fibCompanionIter_succ_formula] at hv
      simpa using hv
    refine ⟨hs, ?_⟩
    have hv := congrArg Prod.fst (h 1 0)
    rw [fibCompanionIter_succ_formula] at hv
    simp only [mul_one, mul_zero, add_zero] at hv
    rw [show fibPolyValue a (r + 2) =
        fibPolyValue a (r + 1) + a * fibPolyValue a r by
          simp only [fibPolyValue], hs, zero_add]
    exact hv.symm
  · rintro ⟨hs, rfl⟩ x y
    rw [fibCompanionIter_succ_formula]
    rw [show fibPolyValue a (r + 2) =
        fibPolyValue a (r + 1) + a * fibPolyValue a r by
          simp only [fibPolyValue], hs, zero_add]
    simp

end ConwayTopBitCompanion

section ConwayResultantCore

variable {R : Type*} [CommRing R] [CharP R 2]

/-- One Horner step modulo `Y^3 + X*Y + X^2` in characteristic two.
The coefficient triple is ordered as `(constant, Y, Y^2)`. -/
theorem conway_cubic_horner_step
    (X Y u v w c : R)
    (hrel : Y ^ 3 + X * Y + X ^ 2 = 0) :
    c + Y * (u + v * Y + w * Y ^ 2) =
      (c + w * X ^ 2) + (u + w * X) * Y + v * Y ^ 2 := by
  have hY3 : Y ^ 3 = X * Y + X ^ 2 := by
    have h := hrel
    rw [show Y ^ 3 + X * Y + X ^ 2 =
        Y ^ 3 - (X * Y + X ^ 2) by
      rw [CharTwo.sub_eq_add]
      ring] at h
    exact sub_eq_zero.mp h
  rw [show Y * (u + v * Y + w * Y ^ 2) =
      u * Y + v * Y ^ 2 + w * Y ^ 3 by ring, hY3]
  ring

/-- Multiplication by `u + v*Y + w*Y^2` in the cubic basis
`(1,Y,Y^2)`, after reducing by `Y^3 = X*Y + X^2`. Columns are the
reduced products with the three basis vectors. -/
def conwayCubicMulMatrix (X u v w : R) : Matrix (Fin 3) (Fin 3) R :=
  !![u, w * X ^ 2, v * X ^ 2;
     v, u + w * X, v * X + w * X ^ 2;
     w, v, u + w * X]

/-- Determinant/norm formula used by the exact selected resultant step. -/
theorem conway_cubic_mulMatrix_det (X u v w : R) :
    (conwayCubicMulMatrix X u v w).det =
      u * u ^ 2 +
      (u * v ^ 2) * X +
      (v * v ^ 2) * X ^ 2 +
      (u * w ^ 2) * X ^ 2 +
      (v * w ^ 2) * X ^ 3 +
      (u * v * w) * X ^ 2 +
      (w * w ^ 2) * X ^ 4 := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have h3 : (3 : R) = 1 := by
    simpa using (CharP.cast_eq_mod R 2 3)
  rw [Matrix.det_fin_three]
  simp only [conwayCubicMulMatrix, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
    Matrix.cons_val]
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, CharTwo.sub_eq_add]
  ring_nf
  simp [h2, h3]

end ConwayResultantCore

section ConwayResultantParametrization

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The Artin--Schreier projection in the rational normalization of the
Conway resultant correspondence. -/
def conwayAlpha (c : R) : R := c ^ 2 + c

/-- The successor projection in the rational normalization of the Conway
resultant correspondence. -/
def conwayBeta (c : R) : R := c ^ 3 + c ^ 2

omit [CharP R 2] in
/-- The successor projection is the parameter times its Artin--Schreier
parent. -/
theorem conwayBeta_eq_mul_alpha (c : R) :
    conwayBeta c = c * conwayAlpha c := by
  simp only [conwayAlpha, conwayBeta]
  ring

/-- Translation by one fixes the parent projection. -/
theorem conwayAlpha_add_one (c : R) :
    conwayAlpha (c + 1) = conwayAlpha c := by
  have hsquare : (c + 1) ^ 2 = c ^ 2 + 1 := by
    simpa using (add_pow_expChar_pow c (1 : R) 2 1)
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  simp only [conwayAlpha]
  rw [hsquare]
  ring_nf
  simp [h2]

/-- The two successor values above one parent differ by that parent. -/
theorem conwayBeta_add_one (c : R) :
    conwayBeta (c + 1) = conwayBeta c + conwayAlpha c := by
  rw [conwayBeta_eq_mul_alpha, conwayAlpha_add_one,
    conwayBeta_eq_mul_alpha]
  ring

/-- The rational parameterization lies on
`X^2 + Y*X + Y^3 = 0`. -/
theorem conwayResultant_parametrized (c : R) :
    conwayBeta c ^ 2 + conwayAlpha c * conwayBeta c +
        conwayAlpha c ^ 3 = 0 := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have hzero : c ^ 2 + c + conwayAlpha c = 0 := by
    simp only [conwayAlpha]
    ring_nf
    simp [h2]
  rw [conwayBeta_eq_mul_alpha]
  linear_combination (conwayAlpha c) ^ 2 * hzero

/-- The product of the two successor values is the cube of their parent;
this is the exact relative norm used by the unique-parent test. -/
theorem conwayResultant_pair_product (c : R) :
    conwayBeta c * conwayBeta (c + 1) = conwayAlpha c ^ 3 := by
  calc
    conwayBeta c * conwayBeta (c + 1) =
        (c * conwayAlpha c) * ((c + 1) * conwayAlpha (c + 1)) := by
      rw [conwayBeta_eq_mul_alpha, conwayBeta_eq_mul_alpha]
    _ = (c * conwayAlpha c) * ((c + 1) * conwayAlpha c) := by
      rw [conwayAlpha_add_one]
    _ = conwayAlpha c ^ 3 := by
      simp only [conwayAlpha]
      ring

end ConwayResultantParametrization

section CubeFibotomicIntersection

variable {K : Type*} [Field K] [CharP K 2]

/-- The inversion-quotient coordinate on the norm-one torus. -/
def torusPhi (x : K) : K := x / (x + 1) ^ 2

/-- Tripling on the norm-one torus descends to a fixed rational map on
the fibotomic coordinate. -/
theorem torusPhi_cube
    (x : K) (hx1 : x + 1 ≠ 0) (hxq : x ^ 2 + x + 1 ≠ 0) :
    torusPhi (x ^ 3) = (torusPhi x) ^ 3 / (1 + torusPhi x) ^ 2 := by
  have hxq' : x ^ 2 + x + 1 ≠ 0 := hxq
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K) = 1 := by
    calc
      (3 : K) = 2 + 1 := by norm_num
      _ = 1 := by rw [h2]; simp
  have hfac : x ^ 3 + 1 = (x + 1) * (x ^ 2 + x + 1) := by
    ring_nf
    simp [h2]
  have hplus : 1 + torusPhi x =
      (x ^ 2 + x + 1) / (x + 1) ^ 2 := by
    simp only [torusPhi]
    field_simp [hx1]
    ring_nf
    simp [h3]
  rw [hplus]
  simp only [torusPhi]
  rw [hfac]
  field_simp [hx1, hxq']

/-- Consequently `Phi(x^3)` and `1 + Phi(x)` have the same class modulo
cubes.  Thus a cubic fibotomic character is transported to a translate-one
character rather than being forced nontrivial. -/
theorem torusPhi_cubeClass
    (x : K) (hx1 : x + 1 ≠ 0) (hxq : x ^ 2 + x + 1 ≠ 0) :
    torusPhi (x ^ 3) =
      (1 + torusPhi x) * (torusPhi x / (1 + torusPhi x)) ^ 3 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K) = 1 := by
    calc
      (3 : K) = 2 + 1 := by norm_num
      _ = 1 := by rw [h2]; simp
  have hplus : 1 + torusPhi x =
      (x ^ 2 + x + 1) / (x + 1) ^ 2 := by
    simp only [torusPhi]
    field_simp [hx1]
    ring_nf
    simp [h3]
  have hphi : 1 + torusPhi x ≠ 0 := by
    rw [hplus]
    exact div_ne_zero hxq (pow_ne_zero _ hx1)
  rw [torusPhi_cube x hx1 hxq]
  field_simp

omit [CharP K 2] in
/-- The previous Conway driver already makes its successor coefficient
an explicit cube; cubic-residue membership is automatic ancestry data. -/
theorem conwayDriver_explicitCube
    (w rho : K) (hrho : rho ^ 3 = w) :
    w / (w + 1) ^ 3 = (rho / (w + 1)) ^ 3 := by
  rw [← hrho]
  field_simp

end CubeFibotomicIntersection

section NormalizedSingerAlgebra

variable {F : Type*} [Field F]

/-- Denominator-free normalization of the selected reciprocal cubic.
Substituting z = d * τ and zPrev = d³ into
z³ + zPrev*z² + zPrev = 0 gives τ³ + d²*τ² + 1 = 0. -/
theorem normalized_singer_cubic
    (z d τ : F) (hd : d ≠ 0)
    (hz : z ^ 3 + d ^ 3 * z ^ 2 + d ^ 3 = 0)
    (hzt : z = d * τ) :
    τ ^ 3 + d ^ 2 * τ ^ 2 + 1 = 0 := by
  rw [hzt] at hz
  have hmul : d ^ 3 * (τ ^ 3 + d ^ 2 * τ ^ 2 + 1) = 0 := by
    linear_combination hz
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 3 hd)

variable {R : Type*} [CommRing R]

/-- Algebraic core of the normalized coefficient ancestry
s_k³ = s_(k-1) * τ_(k-1)². -/
theorem normalized_singer_coefficient_ancestry
    (d dPrev τPrev s sPrev zPrev : R)
    (hd : d ^ 3 = zPrev) (hz : zPrev = dPrev * τPrev)
    (hs : s = d ^ 2) (hsPrev : sPrev = dPrev ^ 2) :
    s ^ 3 = sPrev * τPrev ^ 2 := by
  calc
    s ^ 3 = (d ^ 3) ^ 2 := by rw [hs]; ring
    _ = zPrev ^ 2 := by rw [hd]
    _ = (dPrev * τPrev) ^ 2 := by rw [hz]
    _ = sPrev * τPrev ^ 2 := by rw [hsPrev]; ring

end NormalizedSingerAlgebra

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

/-- Torsion classes of coprime exponents cannot cancel in one
multiplicative reciprocity product.  This is the abstract group core of the
paper's C/D Kummer-field separation: a product relation can be trivial only
when its two primary coordinates are separately trivial. -/
theorem coprime_torsion_product_eq_one_iff
    (x y : G) {a b : Nat}
    (hx : x ^ a = 1) (hy : y ^ b = 1) (hab : a.Coprime b) :
    x * y = 1 ↔ x = 1 ∧ y = 1 := by
  constructor
  · intro hxy
    have hxb : x ^ b = 1 := by
      rw [eq_inv_of_mul_eq_one_left hxy]
      simp [hy]
    have hxone : x = 1 :=
      (pow_eq_one_iff_of_coprime x hx hab).mp hxb
    constructor
    · exact hxone
    · simpa [hxone] using hxy
  · rintro ⟨rfl, rfl⟩
    simp

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

section SelectedCriticalAlgebra

variable {R : Type*} [CommRing R] [CharP R 2]

/-- Denominator-free semiconjugacy behind the cubic arm's selected
cyclotomic critical factor.  Under the selected inverse-square relation,
the right side transports the actual Conway cubic. -/
theorem cubic_collision_semiconjugacy (z Y : R) :
    (1 + z * Y ^ 2) ^ 3 + (1 + z * Y ^ 2) ^ 2 +
        (z ^ 2 + 1) * (1 + z * Y ^ 2) + 1 =
      z ^ 3 * (Y ^ 3 + Y) ^ 2 + z ^ 2 := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have h4 : (4 : R) = 0 := by
    calc
      (4 : R) = 2 + 2 := by norm_num
      _ = 0 := by rw [h2]; simp
  have h6 : (6 : R) = 0 := by
    calc
      (6 : R) = 3 * 2 := by norm_num
      _ = 0 := by rw [h2]; simp
  ring_nf
  simp [h2, h4, h6]

/-- Once the two cyclic cubic resolvents have the displayed sum and product,
the selected one satisfies the denominator-free Artin--Schreier equation
used by the exceptional terminal cubic. -/
theorem cyclic_resolvent_artinSchreier (a K K' : R)
    (hsum : K + K' = a) (hprod : K * K' = a ^ 2 + 1) :
    K ^ 2 + a * K + a ^ 2 + 1 = 0 := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  calc
    K ^ 2 + a * K + a ^ 2 + 1 =
        K ^ 2 + (K + K') * K + K * K' := by rw [hsum, hprod]; ring
    _ = 0 := by ring_nf; simp [h2]

/-- Denominator-free numerator identity showing that reversal of the
exceptional cyclic orientation changes relative trace by an
Artin--Schreier value. -/
theorem exceptional_orientation_trace_shift (a : R) :
    (a + 1) ^ 2 + (a + 1) * (a ^ 2 + a + 1) =
      a ^ 2 * (a + 1) := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have h4 : (4 : R) = 0 := by
    calc
      (4 : R) = 2 + 2 := by norm_num
      _ = 0 := by rw [h2]; simp
  have h3 : (3 : R) = 1 := by
    calc
      (3 : R) = 2 + 1 := by norm_num
      _ = 1 := by rw [h2]; simp
  ring_nf
  simp [h2, h3, h4]

end SelectedCriticalAlgebra

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
