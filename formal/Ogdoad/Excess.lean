import Mathlib
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Data.Nat.Choose.Lucas

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

/-- The four alternating base-`q` blocks of the exceptional Euler exponent
collapse algebraically to one quotient exponent. -/
theorem exceptional_four_block_exponent_algebra
    {R : Type*} [CommRing R]
    (q ell d a b : R)
    (hq : q + 1 = ell * d)
    (ha : a + d = q)
    (hb : b + 1 = d) :
    ell * (a + b * q + a * q ^ 2 + b * q ^ 3) = q ^ 4 - 1 := by
  have hab : a + b * q = d * (q - 1) := by
    linear_combination ha + q * hb
  calc
    ell * (a + b * q + a * q ^ 2 + b * q ^ 3) =
        ell * (a + b * q) * (1 + q ^ 2) := by ring
    _ = ell * d * (q - 1) * (1 + q ^ 2) := by
      rw [hab]
      ring
    _ = (q + 1) * (q - 1) * (1 + q ^ 2) := by rw [hq]
    _ = q ^ 4 - 1 := by ring

/-- Cross-multiplied commutative-group form of the four-block quotient
identity.  The paper specializes the two paired powers to the
conductor-five antiunit and its inverse. -/
theorem exceptional_four_block_group_balance
    {G : Type*} [CommGroup G]
    (v : G) (q d a b : Nat)
    (ha : a + d = q) (hb : b + 1 = d) :
    v ^ (a + b * q + a * q ^ 2 + b * q ^ 3) *
        (v * v ^ (q ^ 2)) ^ d =
      (v ^ q * v ^ (q ^ 3)) ^ d := by
  have hexp :
      a + b * q + a * q ^ 2 + b * q ^ 3 + d * (1 + q ^ 2) =
        d * (q + q ^ 3) := by
    have hq' : q = a + d := ha.symm
    subst q
    have hd' : d = b + 1 := hb.symm
    subst d
    ring
  calc
    v ^ (a + b * q + a * q ^ 2 + b * q ^ 3) *
          (v * v ^ (q ^ 2)) ^ d =
        v ^ (a + b * q + a * q ^ 2 + b * q ^ 3 +
          d * (1 + q ^ 2)) := by
            simp only [mul_pow, ← pow_add, ← pow_mul]
            congr 1
            ring
    _ = v ^ (d * (q + q ^ 3)) := by rw [hexp]
    _ = (v ^ q * v ^ (q ^ 3)) ^ d := by
      simp only [← pow_add, ← pow_mul]
      congr 1
      ring

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

section CubicTraceFibre

/-- On the selected reciprocal target pair `(a,a+1)`, the universal
cubic-power-map Jacobian numerator is the selected inverse-period
coordinate `a^2+a+1`. -/
theorem cubic_trace_fibre_target_numerator (a : R) :
    a * (a + 1) + 1 = a ^ 2 + a + 1 := by
  ring

/-- In characteristic two the discriminant polynomial of a monic
reciprocal cubic `X^3 + C X^2 + D X + 1` is `(C*D+1)^2`. -/
theorem reciprocal_cubic_discriminant_charTwo [CharP R 2]
    (C D : R) :
    C ^ 2 * D ^ 2 - 4 * D ^ 3 - 4 * C ^ 3 - 27 + 18 * C * D =
      (C * D + 1) ^ 2 := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have h4 : (4 : R) = 0 := by
    calc
      (4 : R) = 2 + 2 := by norm_num
      _ = 0 := by rw [h2]; simp
  have h18 : (18 : R) = 0 := by
    calc
      (18 : R) = 9 * 2 := by norm_num
      _ = 0 := by rw [h2]; simp
  have h27 : (27 : R) = 1 := by
    calc
      (27 : R) = 13 * 2 + 1 := by norm_num
      _ = 1 := by rw [h2]; simp
  have hneg : (-1 : R) = 1 := by
    rw [neg_eq_iff_add_eq_zero]
    norm_num
    exact h2
  rw [h4, h18, h27]
  simp only [zero_mul, sub_zero, add_zero]
  rw [sub_eq_add_neg, hneg]
  ring_nf
  simp [h2]

/-- If an `ell`-th root has target norm one and `ell`-powering is
injective in the base group, its source norm is forced to be one. -/
theorem reciprocal_power_root_norm_one
    {G H : Type*} [CommMonoid G] [CommMonoid H]
    (N : G →* H) (b eta : G) (ell : Nat)
    (hb : b ^ ell = eta) (hNorm : N eta = 1)
    (hinj : Function.Injective fun x : H ↦ x ^ ell) :
    N b = 1 := by
  apply hinj
  change (N b) ^ ell = (1 : H) ^ ell
  rw [← map_pow, hb, hNorm]
  simp

end CubicTraceFibre

section CubicTraceFlagCore

open scoped BigOperators

/-- A stack of additive Fourier exponents which all factor through one top
trace has only the sum of the downstairs Fourier coefficients. -/
theorem sum_comp_linearMap
    {ι V W S : Type*} [Fintype ι] [Semiring S]
    [AddCommMonoid V] [AddCommMonoid W]
    [Module S V] [Module S W]
    (T : V →ₗ[S] W) (g : ι → W →ₗ[S] S) :
    (∑ i, g i).comp T = ∑ i, (g i).comp T := by
  ext x
  simp

/-- A complete compatible lower flag is already forced by its immediate
coordinate. -/
theorem compatible_flag_fibre_eq_immediate
    {ι X Y : Type*} {Z : ι → Type*}
    (top : X → Y) (down : ∀ i, Y → Z i) (a : Y) :
    {x | top x = a ∧ ∀ i, down i (top x) = down i a} =
      {x | top x = a} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · exact And.left
  · intro hx
    refine ⟨hx, ?_⟩
    intro i
    rw [hx]

/-- Every weighting of a compatible full flag factors through the immediate
coordinate. -/
theorem flag_weight_factors_through_immediate
    {ι X Y T : Type*} {Z : ι → Type*}
    (top : X → Y) (down : ∀ i, Y → Z i)
    (weight : (∀ i, Z i) → T) :
    (fun x => weight (fun i => down i (top x))) =
      (fun x => (fun y => weight (fun i => down i y)) (top x)) := by
  rfl

end CubicTraceFlagCore

section CubicSelfPolarAffineLine

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

def cubicAffineLine (gamma : K) : Set K :=
  Set.range fun p : F × F =>
    algebraMap F K p.1 + algebraMap F K p.2 * gamma

/-- Translating a top cubic coordinate by any lower-field scalar does not
change the lower-field affine line that it spans with one. -/
theorem cubicAffineLine_add_algebraMap (gamma : K) (c : F) :
    cubicAffineLine (F := F) (gamma + algebraMap F K c) =
      cubicAffineLine (F := F) gamma := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨(a + b * c, b), ?_⟩
    simp only [map_add, map_mul]
    ring
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨(a - b * c, b), ?_⟩
    simp only [map_sub, map_mul]
    ring

/-- Algebraic core of self-polarity: if a lower-linear trace functional kills
`gamma` and `gamma^2`, then it kills `gamma` times the whole affine line
spanned by `1,gamma`. -/
theorem cubicTrace_mul_affineLine_eq_zero
    (tr : K →ₗ[F] F) (gamma : K)
    (hgamma : tr gamma = 0) (hgammaSq : tr (gamma ^ 2) = 0)
    (a b : F) :
    tr (gamma *
      (algebraMap F K a + algebraMap F K b * gamma)) = 0 := by
  rw [mul_add]
  have hfirst : gamma * algebraMap F K a = a • gamma := by
    simp [Algebra.smul_def, mul_comm]
  have hsecond : gamma * (algebraMap F K b * gamma) =
      b • (gamma ^ 2) := by
    simp [Algebra.smul_def, pow_two]
    ring
  rw [hfirst, hsecond]
  simp [hgamma, hgammaSq]

/-- Set-theoretic self-polar containment.  Dimension three and nondegeneracy
of the finite-field trace upgrade it to the equality used in the paper. -/
theorem cubicAffineLine_subset_traceKernel
    (tr : K →ₗ[F] F) (gamma : K)
    (hgamma : tr gamma = 0) (hgammaSq : tr (gamma ^ 2) = 0) :
    cubicAffineLine (F := F) gamma ⊆
      {x : K | tr (gamma * x) = 0} := by
  rintro x ⟨⟨a, b⟩, rfl⟩
  exact cubicTrace_mul_affineLine_eq_zero
    tr gamma hgamma hgammaSq a b

end CubicSelfPolarAffineLine

section CubicSingerIncidence

open scoped BigOperators

variable {P K : Type*} [Fintype P] [DecidableEq P]
  [CommSemiring K]

def cubicIncidence (M : P → P → K) (f : P → K) (a : P) : K :=
  ∑ x, M a x * f x

/-- Algebraic core of the projective-plane identity `I² = q Id + J`.
The geometric input is exactly the displayed matrix-square hypothesis. -/
theorem cubic_incidence_square
    (M : P → P → K) (q : K)
    (hsquare : ∀ a b, ∑ x, M a x * M x b = if a = b then q + 1 else 1)
    (f : P → K) (a : P) :
    cubicIncidence M (cubicIncidence M f) a = q * f a + ∑ x, f x := by
  simp only [cubicIncidence, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ x, ∑ y, M a y * (M y x * f x) =
        ∑ x, (∑ y, M a y * M y x) * f x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = ∑ x, (if a = x then q + 1 else 1) * f x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hsquare]
    _ = ∑ x, ((if a = x then q else 0) + 1) * f x := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases h : a = x <;> simp [h]
    _ = (∑ x, (if a = x then q * f x else 0)) + ∑ x, f x := by
          simp_rw [add_mul, one_mul, ite_mul, zero_mul]
          exact Finset.sum_add_distrib
    _ = q * f a + ∑ x, f x := by simp

/-- On a zero-sum vector the polarity-incidence operator squares to the
universal scalar `q`. -/
theorem cubic_incidence_square_of_sum_zero
    (M : P → P → K) (q : K)
    (hsquare : ∀ a b, ∑ x, M a x * M x b = if a = b then q + 1 else 1)
    (f : P → K) (hsum : ∑ x, f x = 0) :
    cubicIncidence M (cubicIncidence M f) = fun a ↦ q * f a := by
  funext a
  rw [cubic_incidence_square M q hsquare f a, hsum, add_zero]

omit [Fintype P] [DecidableEq P] in
/-- Once incidence swaps a character and its inverse, a second incidence
step only multiplies by the universal scalar. -/
theorem cubic_phase_swap_square
    (I : (P → K) → (P → K)) (chi chiInv : P → K)
    (c d q : K)
    (hchi : I chi = fun a ↦ c * chiInv a)
    (hchiInv : I chiInv = fun a ↦ d * chi a)
    (hlinear : ∀ (r : K) (f : P → K),
      I (fun a ↦ r * f a) = fun a ↦ r * I f a)
    (hcd : c * d = q) :
    I (I chi) = fun a ↦ q * chi a := by
  rw [hchi, hlinear, hchiInv]
  funext a
  rw [← mul_assoc, hcd]

end CubicSingerIncidence

section NormCoherentEulerTail

variable {G : Type*} [CommMonoid G]

/-- A norm-coherent sequence carries one fixed Euler phase along its whole
tail.  The theorem isolates the formal core common to the ordinary Kummer
spines and the cubic selector tower: the later Euler exponent is the relative
norm exponent times the earlier Euler exponent. -/
theorem norm_coherent_euler_phase_tail
    (x : Nat → G) (E S : Nat → Nat) (k : Nat)
    (hnorm : ∀ j, k < j → x j ^ S j = x (j - 1))
    (hexp : ∀ j, k < j → E j = S j * E (j - 1)) :
    ∀ j, k ≤ j → x j ^ E j = x k ^ E k := by
  intro j hkj
  induction j, hkj using Nat.le_induction with
  | base => rfl
  | succ j hkj ih =>
      have hlt : k < j + 1 := Nat.lt_succ_iff.mpr hkj
      rw [hexp (j + 1) hlt, pow_mul, hnorm (j + 1) hlt]
      simpa using ih

/-- Any affine family with the same norm/exponent recursion has the identical
tail collapse.  In the finite-field applications `z j` is a translate or a
two-ancestor sum rather than the distinguished selector itself. -/
theorem norm_coherent_affine_phase_tail
    (z : Nat → G) (E S : Nat → Nat) (k : Nat)
    (hnorm : ∀ j, k < j → z j ^ S j = z (j - 1))
    (hexp : ∀ j, k < j → E j = S j * E (j - 1))
    (j : Nat) (hkj : k ≤ j) :
    z j ^ E j = z k ^ E k := by
  exact norm_coherent_euler_phase_tail z E S k hnorm hexp j hkj

end NormCoherentEulerTail

section CubicPhaseTail

variable {G : Type*} [CommMonoid G]

/-- A relative cubic norm transports the lower Euler phase without any
loss.  In the finite-field application `S = Q^2 + Q + 1`, `d =
(Q-1)/ell`, and `d*S = (Q^3-1)/ell`. -/
theorem cubic_norm_euler_phase_transport
    (top lower : G) (S d : Nat) (hnorm : top ^ S = lower) :
    top ^ (d * S) = lower ^ d := by
  calc
    top ^ (d * S) = top ^ (S * d) := by rw [Nat.mul_comm]
    _ = (top ^ S) ^ d := by rw [pow_mul]
    _ = lower ^ d := by rw [hnorm]

/-- The arithmetic factorization behind one step of phase conservation.
Writing `Q = 1 + ell*d` avoids truncated subtraction in `Nat`. -/
theorem cubic_euler_exponent_factor
    (Q ell d : Nat) (hQ : Q = 1 + ell * d) :
    Q ^ 3 = 1 + ell * (d * (Q ^ 2 + Q + 1)) := by
  rw [hQ]
  ring

variable {R : Type*} [CommSemiring R]

/-- For the literal cubic selector, the additive recursion and the
multiplicative norm give the same transported phase. -/
theorem cubic_selector_additive_multiplicative_phase
    (top lower : R) (Q d : Nat)
    (hadd : top ^ 3 + top = lower)
    (hnorm : top ^ (Q ^ 2 + Q + 1) = lower) :
    (top ^ 3 + top) ^ d = top ^ (d * (Q ^ 2 + Q + 1)) := by
  rw [hadd]
  exact (cubic_norm_euler_phase_transport top lower
    (Q ^ 2 + Q + 1) d hnorm).symm

/-- The exact descent for an affine translate.  In the cubic finite-field
application the norm polynomial is
`Norm(top + c) = c^3 + c + lower`; hence every later translate phase is
an earlier translate phase, rather than a new current character value. -/
theorem cubic_affine_translate_phase_descent
    (top c lower : R) (S d : Nat)
    (hnorm : (top + c) ^ S = c ^ 3 + c + lower) :
    (top + c) ^ (d * S) = (c ^ 3 + c + lower) ^ d := by
  exact cubic_norm_euler_phase_transport (top + c)
    (c ^ 3 + c + lower) S d hnorm

variable {H : Type*} [CommGroup H]

/-- Restricting a later Euler character to an earlier field raises the
earlier phase by the relative geometric-series quotient. -/
theorem euler_phase_restrict
    (x theta : H) (E r : Nat) (hphase : x ^ E = theta) :
    x ^ (E * r) = theta ^ r := by
  rw [pow_mul, hphase]

/-- At the birth edge of `ell`, the lower selector is automatically flat.
The translated selector is therefore the unique odd-torsion square root of
the inverse top phase. -/
theorem cubic_birth_translate_phase_square
    (top lower shift theta : H) (E : Nat)
    (hselector : lower = top * shift ^ 2)
    (htop : top ^ E = theta)
    (hlower : lower ^ E = 1) :
    (shift ^ E) ^ 2 = theta⁻¹ := by
  have hrel : 1 = theta * (shift ^ E) ^ 2 := by
    calc
      1 = lower ^ E := hlower.symm
      _ = (top * shift ^ 2) ^ E := by rw [hselector]
      _ = top ^ E * (shift ^ 2) ^ E := by rw [mul_pow]
      _ = theta * (shift ^ E) ^ 2 := by
        rw [htop]
        congr 1
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  exact eq_inv_of_mul_eq_one_right hrel.symm

/-- Two `ell`-torsion phases with the same square are equal when `ell` is
odd. -/
theorem odd_torsion_eq_of_sq_eq
    (a b : H) (ell : Nat)
    (ha : a ^ ell = 1) (hb : b ^ ell = 1)
    (hodd : Odd ell) (hsq : a ^ 2 = b ^ 2) :
    a = b := by
  have hzEll : (a * b⁻¹) ^ ell = 1 := by
    rw [mul_pow, ha, inv_pow, hb]
    simp
  have hzSq : (a * b⁻¹) ^ 2 = 1 := by
    rw [mul_pow, hsq, inv_pow]
    simp
  have hcop : ell.Coprime 2 := hodd.coprime_two_right
  have hordEll : orderOf (a * b⁻¹) ∣ ell :=
    orderOf_dvd_iff_pow_eq_one.mpr hzEll
  have hordTwo : orderOf (a * b⁻¹) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr hzSq
  have hordOne : orderOf (a * b⁻¹) ∣ 1 := by
    simpa [hcop.gcd_eq_one] using Nat.dvd_gcd hordEll hordTwo
  have hz : a * b⁻¹ = 1 := by
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hordOne)
  exact (mul_inv_eq_one.mp hz)

/-- After the birth level of `ell`, the literal selector and its translate
have the same Euler phase.  `S = ell*c + 3` is the reduction of the cubic
norm exponent modulo `ell`. -/
theorem cubic_tail_translate_has_same_phase
    (top lower shift theta : H) (E S ell c : Nat)
    (hselector : lower = top * shift ^ 2)
    (htop : top ^ E = theta)
    (hlower : lower ^ E = theta ^ S)
    (hS : S = ell * c + 3)
    (hshiftTors : (shift ^ E) ^ ell = 1)
    (hthetaTors : theta ^ ell = 1)
    (hodd : Odd ell) :
    shift ^ E = theta := by
  have hsq : (shift ^ E) ^ 2 = theta ^ 2 := by
    have hrel : theta ^ S = theta * (shift ^ E) ^ 2 := by
      calc
        theta ^ S = lower ^ E := hlower.symm
        _ = (top * shift ^ 2) ^ E := by rw [hselector]
        _ = top ^ E * (shift ^ 2) ^ E := by rw [mul_pow]
        _ = theta * (shift ^ E) ^ 2 := by
          rw [htop]
          congr 1
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have hthetaS : theta ^ S = theta ^ 3 := by
      rw [hS, pow_add, pow_mul, hthetaTors]
      simp
    rw [hthetaS] at hrel
    have hcube : theta ^ 3 = theta * theta ^ 2 := by
      simp [pow_succ, mul_comm]
    have hcancel : theta * theta ^ 2 = theta * (shift ^ E) ^ 2 :=
      hcube.symm.trans hrel
    exact (mul_left_cancel hcancel).symm
  exact odd_torsion_eq_of_sq_eq (shift ^ E) theta ell
    hshiftTors hthetaTors hodd hsq

end CubicPhaseTail

section CubicBirthSecants

variable {K : Type*} [Field K]

/-- A sum of two real cyclotomic coordinates factors into the two secants
joining their oriented endpoints. -/
theorem real_cyclotomic_pair_factorization
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x + x⁻¹) + (y + y⁻¹) = (x + y) * (1 + (x * y)⁻¹) := by
  field_simp
  ring

variable {H : Type*} [CommGroup H]

/-- If the two active secants have Frobenius weights `2^i` and `2^j`,
their product is one power of the selected real-period phase `u^2`. -/
theorem birth_secant_phase_is_selected_power
    (u theta phi : H) (i j w : Nat)
    (htheta : theta = u ^ 2)
    (hphi : phi = u ^ (2 ^ i) * u ^ (2 ^ j))
    (hw : 2 * w = 2 ^ i + 2 ^ j) :
    phi = theta ^ w := by
  calc
    phi = u ^ (2 ^ i + 2 ^ j) := by rw [hphi, pow_add]
    _ = u ^ (2 * w) := by rw [hw]
    _ = (u ^ 2) ^ w := by rw [pow_mul]
    _ = theta ^ w := by rw [htheta]

/-- Torsion-corrected form of the birth-secant phase transport.  It accepts
the exponent congruence modulo `ell` used by the cyclotomic specialization,
rather than requiring an exact equality of the displayed natural exponents. -/
theorem birth_secant_phase_is_selected_power_mod_torsion
    (u theta phi : H) (ell i j w : Nat)
    (hu : u ^ ell = 1)
    (htheta : theta = u ^ 2)
    (hphi : phi = u ^ (2 ^ i) * u ^ (2 ^ j))
    (hw : 2 * w ≡ 2 ^ i + 2 ^ j [MOD ell]) :
    phi = theta ^ w := by
  calc
    phi = u ^ (2 ^ i + 2 ^ j) := by rw [hphi, pow_add]
    _ = u ^ (2 * w) := pow_eq_pow_of_modEq hw.symm hu
    _ = (u ^ 2) ^ w := by rw [pow_mul]
    _ = theta ^ w := by rw [htheta]

/-- An invertible birth weight detects exactly the original selected phase;
it cannot supply an independent nonvanishing condition. -/
theorem birth_secant_phase_eq_one_iff_selected
    (theta phi : H) (ell w : Nat)
    (hphase : phi = theta ^ w)
    (htors : theta ^ ell = 1)
    (hcop : ell.Coprime w) :
    phi = 1 ↔ theta = 1 := by
  rw [hphase]
  constructor
  · intro hpow
    exact (pow_eq_one_iff_of_coprime hcop).mp ⟨htors, hpow⟩
  · rintro rfl
    simp

/-- A finite multiplicative formula in birth phases again has one total
selected weight. -/
theorem birth_phase_finset_product_has_one_weight
    {ι : Type*} (s : Finset ι) (theta : H)
    (phi : ι → H) (w : ι → Nat)
    (hphase : ∀ i ∈ s, phi i = theta ^ (w i)) :
    ∏ i ∈ s, phi i = theta ^ (∑ i ∈ s, w i) := by
  calc
    ∏ i ∈ s, phi i = ∏ i ∈ s, theta ^ (w i) :=
      Finset.prod_congr rfl hphase
    _ = theta ^ (∑ i ∈ s, w i) := Finset.prod_pow_eq_pow_sum s w theta

/-- A global product of two coprime-primary phases is nontrivial exactly
when at least one primary phase is nontrivial. -/
theorem coprime_phase_product_ne_one_iff
    (x y : H) {a b : Nat}
    (hx : x ^ a = 1) (hy : y ^ b = 1) (hab : a.Coprime b) :
    x * y ≠ 1 ↔ x ≠ 1 ∨ y ≠ 1 := by
  have hprod : x * y = 1 ↔ x = 1 ∧ y = 1 := by
    constructor
    · intro hxy
      have hyx : y = x⁻¹ := eq_inv_of_mul_eq_one_right hxy
      have hxb : x ^ b = 1 := by
        have : (x⁻¹) ^ b = 1 := by simpa [hyx] using hy
        simpa only [inv_pow, inv_eq_one] using this
      have hoa : orderOf x ∣ a := orderOf_dvd_of_pow_eq_one hx
      have hob : orderOf x ∣ b := orderOf_dvd_of_pow_eq_one hxb
      have ho : orderOf x = 1 := by
        apply Nat.eq_one_of_dvd_one
        simpa [hab.gcd_eq_one] using Nat.dvd_gcd hoa hob
      have hx1 : x = 1 := orderOf_eq_one_iff.mp ho
      exact ⟨hx1, by simpa [hx1] using hxy⟩
    · rintro ⟨rfl, rfl⟩
      simp
  rw [ne_eq, hprod]
  tauto

end CubicBirthSecants

section MarkedPhaseBridge

variable {G : Type*} [CommGroup G]

/-- Passing from an equality in an `ell`-Kummer quotient to the Euler phase:
the hidden `ell`-th power dies after the complementary exponent. -/
theorem quotient_phase_transport
    (W N Y : G) (c ell E : ℕ)
    (hW : W = N ^ c * Y ^ ell)
    (hY : Y ^ (ell * E) = 1) :
    W ^ E = (N ^ E) ^ c := by
  have hy : (Y ^ ell) ^ E = 1 := by
    rw [← pow_mul]
    exact hY
  rw [hW, mul_pow]
  rw [hy, mul_one]
  simp only [← pow_mul]
  rw [Nat.mul_comm c E]

/-- If the two adjacent Hilbert coordinates come from `W = D+1`, while
`W` and the corrected norm `N` differ in the Kummer quotient by the unit
`c`, then their Euler phases differ by precisely the same power `c`. -/
theorem adjacent_hilbert_phase_transport
    (W N Y : G) (c ell q e : ℕ)
    (hW : W = N ^ c * Y ^ ell)
    (hqe : ell * e = q + 1)
    (hY : Y ^ ((q - 1) * (q + 1)) = 1) :
    (W ^ (q - 1)) ^ e = ((N ^ (q - 1)) ^ e) ^ c := by
  have hphase := quotient_phase_transport W N Y c ell ((q - 1) * e) hW
  have hexp : ell * ((q - 1) * e) = (q - 1) * (q + 1) := by
    calc
      ell * ((q - 1) * e) = (q - 1) * (ell * e) := by ac_rfl
      _ = (q - 1) * (q + 1) := by rw [hqe]
  have hkill : Y ^ (ell * ((q - 1) * e)) = 1 := by
    rw [hexp]
    exact hY
  specialize hphase hkill
  simpa [pow_mul, Nat.mul_comm e (q - 1)] using hphase

end MarkedPhaseBridge

section SixthRootCoefficient

variable {R : Type*} [CommRing R]

/-- The adjacent-quartic coefficient `1+A^5` is the linear unit `2-A`
on the primitive sixth-root locus `A^2-A+1=0`. -/
theorem sixth_root_adjacent_coefficient (A : R)
    (hA : A ^ 2 - A + 1 = 0) :
    1 + A ^ 5 = 2 - A := by
  linear_combination (A ^ 3 + A ^ 2 - 1) * hA

/-- The inverse multiplier is equally explicit: `(2-A)(1+A)=3` on the
same sixth-root locus.  Modulo a current prime, division by three therefore
recovers the original selected phase from the marked adjacent phase. -/
theorem sixth_root_adjacent_inverse_factor (A : R)
    (hA : A ^ 2 - A + 1 = 0) :
    (2 - A) * (1 + A) = 3 := by
  linear_combination -hA

end SixthRootCoefficient

section SixthRootSupportArithmetic

variable {R : Type*} [Field R]

/-- The quadratic current-factor relation forces cubic Frobenius to act by
inversion. -/
theorem sixth_root_cube_eq_neg_one (A : R)
    (hA : A ^ 2 - A + 1 = 0) :
    A ^ 3 = -1 := by
  have hfactor : A ^ 3 + 1 = (A + 1) * (A ^ 2 - A + 1) := by ring
  have hzero : A ^ 3 + 1 = 0 := by rw [hfactor, hA, mul_zero]
  linear_combination hzero

/-- The same relation makes the sixth Frobenius the identity. -/
theorem sixth_root_six_eq_one (A : R)
    (hA : A ^ 2 - A + 1 = 0) :
    A ^ 6 = 1 := by
  have hcube := sixth_root_cube_eq_neg_one A hA
  calc
    A ^ 6 = (A ^ 3) ^ 2 := by ring
    _ = (-1 : R) ^ 2 := by rw [hcube]
    _ = 1 := by ring

/-- Away from residue characteristic three, the current quadratic root does
not have order two. -/
theorem sixth_root_square_ne_one (A : R)
    (hA : A ^ 2 - A + 1 = 0)
    (hthree : (3 : R) ≠ 0) :
    A ^ 2 ≠ 1 := by
  intro hsquare
  have hAeq : A = 2 := by
    linear_combination -(hA - hsquare)
  rw [hAeq] at hA
  norm_num at hA
  exact hthree hA

/-- In odd residue characteristic, cubic Frobenius is genuinely inversion
rather than the identity. -/
theorem sixth_root_cube_ne_one (A : R)
    (hA : A ^ 2 - A + 1 = 0)
    (htwo : (2 : R) ≠ 0) :
    A ^ 3 ≠ 1 := by
  rw [sixth_root_cube_eq_neg_one A hA]
  intro h
  have : (2 : R) = 0 := by linear_combination -h
  exact htwo this

end SixthRootSupportArithmetic

section CurrentPrimarySupport

variable {G : Type*} [CommGroup G]

/-- Phases of coprime primary orders cannot cancel.  Hence a product detects
only the union of their supports, not that each coordinate is nontrivial. -/
theorem current_primary_product_eq_one_iff
    (x y : G) {a b : Nat}
    (hx : x ^ a = 1) (hy : y ^ b = 1) (hab : a.Coprime b) :
    x * y = 1 ↔ x = 1 ∧ y = 1 := by
  constructor
  · intro hxy
    have hyx : y = x⁻¹ := eq_inv_of_mul_eq_one_right hxy
    have hxb : x ^ b = 1 := by
      have : (x⁻¹) ^ b = 1 := by simpa [hyx] using hy
      simpa only [inv_pow, inv_eq_one] using this
    have hoa : orderOf x ∣ a := orderOf_dvd_of_pow_eq_one hx
    have hob : orderOf x ∣ b := orderOf_dvd_of_pow_eq_one hxb
    have ho : orderOf x = 1 := by
      apply Nat.eq_one_of_dvd_one
      simpa [hab.gcd_eq_one] using Nat.dvd_gcd hoa hob
    have hx1 : x = 1 := orderOf_eq_one_iff.mp ho
    exact ⟨hx1, by simpa [hx1] using hxy⟩
  · rintro ⟨rfl, rfl⟩
    simp

end CurrentPrimarySupport

/-- The alternating `F₄` translate turns the selected depressed cubic into
a norm-coherent twisted cubic. -/
theorem dk_twisted_translate_recursion
    {S : Type*} [CommRing S] [CharP S 2]
    (x a c : S) (hc : c ^ 2 + c = 1) (hx : x ^ 3 + x = a) :
    let u := x + c
    let v := a + c ^ 2
    u ^ 3 + c * u ^ 2 + c * u = v := by
  dsimp
  have htwo : (2 : S) = 0 := CharP.cast_eq_zero S 2
  have hfour : (4 : S) = 0 := by
    calc
      (4 : S) = 2 + 2 := by norm_num
      _ = 0 := by rw [htwo, zero_add]
  have hfive : (5 : S) = 1 := by
    calc
      (5 : S) = 4 + 1 := by norm_num
      _ = 1 := by rw [hfour, zero_add]
  rw [show a = x ^ 3 + x by simpa using hx.symm]
  calc
    (x + c) ^ 3 + c * (x + c) ^ 2 + c * (x + c) =
        x ^ 3 + x * (c ^ 2 + c) + c ^ 2 := by
          ring_nf
          simp [htwo, hfour, hfive]
    _ = x ^ 3 + x + c ^ 2 := by rw [hc, mul_one]

/-- The same alternating translate is an Artin--Schreier root of the actual
exceptional auxiliary coordinate `x²+x+1`. -/
theorem dk_twisted_translate_artinSchreier
    {S : Type*} [CommRing S] [CharP S 2]
    (x c : S) (hc : c ^ 2 + c = 1) :
    (x + c) ^ 2 + (x + c) = x ^ 2 + x + 1 := by
  have htwo : (2 : S) = 0 := CharP.cast_eq_zero S 2
  calc
    (x + c) ^ 2 + (x + c) = x ^ 2 + x + (c ^ 2 + c) := by
      ring_nf
      simp [htwo]
    _ = x ^ 2 + x + 1 := by rw [hc]

/-- Symmetric-coordinate form of the alternating translate's exact norm
identity. -/
theorem dk_twisted_translate_product
    {S : Type*} [CommRing S] [CharP S 2]
    (x y z a c : S)
    (h1 : x + y + z = 0)
    (h2 : x * y + x * z + y * z = 1)
    (h3 : x * y * z = a)
    (hc : c ^ 2 + c = 1) :
    (x + c) * (y + c) * (z + c) = a + c ^ 2 := by
  have htwo : (2 : S) = 0 := CharP.cast_eq_zero S 2
  have hself (w : S) : w + w = 0 := by
    calc
      w + w = (2 : S) * w := by ring
      _ = 0 := by rw [htwo, zero_mul]
  have hnegc : -c = c := neg_eq_of_add_eq_zero_right (hself c)
  have hc' : c ^ 2 = 1 + c := by
    calc
      c ^ 2 = 1 - c := by linear_combination hc
      _ = 1 + c := by rw [sub_eq_add_neg, hnegc]
  have hc'' : c + 1 = c ^ 2 := by simpa [add_comm] using hc'.symm
  have hc3 : c ^ 3 = 1 := by
    calc
      c ^ 3 = c * c ^ 2 := by ring
      _ = c * (1 + c) := by rw [hc']
      _ = c + c ^ 2 := by ring
      _ = 1 := by simpa [add_comm] using hc
  calc
    (x + c) * (y + c) * (z + c) =
        x*y*z + c*(x*y + x*z + y*z) + c^2*(x+y+z) + c^3 := by ring
    _ = a + c + 1 := by simp only [h1, h2, h3, hc3, mul_one, mul_zero, add_zero]
    _ = a + (c + 1) := by ring
    _ = a + c ^ 2 := by rw [hc'']

/-- Multiplication by a known `ell`-th power does not change Kummer
membership. -/
theorem mul_power_isPthPower_iff
    {G : Type*} [CommGroup G] (a u : G) (ell : Nat)
    (ha : IsPthPower ell a) :
    IsPthPower ell (a * u) ↔ IsPthPower ell u := by
  obtain ⟨r, hr⟩ := ha
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z / r, ?_⟩
    rw [div_pow, hz, hr]
    simp
  · rintro ⟨v, hv⟩
    refine ⟨r * v, ?_⟩
    rw [mul_pow, hr, hv]

/-- A multiplicative norm carries an `ell`-th root to the unique lower
`ell`-th root, forcing norm coherence of the complete root chain. -/
theorem norm_of_power_root
    {A B : Type*} [CommMonoid A] [CommMonoid B]
    (N : A →* B) (v u : A) (u0 v0 : B) (ell : Nat)
    (hv : v ^ ell = u) (hNu : N u = u0)
    (huniq : ∀ z : B, z ^ ell = u0 → z = v0) :
    N v = v0 := by
  apply huniq
  rw [← hNu, ← hv, map_pow]

section DKTwistedFibre

variable {G : Type*} [CommMonoid G]

/-- Changing an `ell`-th root by an `ell`-th root of unity does not
change its `ell`-th power. -/
theorem dk_scaled_power_root
    (z v : G) (r ell : Nat) (hz : z ^ ell = 1) :
    (z ^ r * v) ^ ell = v ^ ell := by
  rw [mul_pow]
  calc
    (z ^ r) ^ ell * v ^ ell = (z ^ ell) ^ r * v ^ ell := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm r ell]
    _ = v ^ ell := by simp [hz]

/-- The cubic Frobenius orbit of a scaled Kummer root has unchanged
constant coefficient when the total scaling exponent is trivial. -/
theorem dk_scaled_cubic_product
    (z x₀ x₁ x₂ : G) (r A : Nat)
    (hz : z ^ (r * (1 + A + A ^ 2)) = 1) :
    (z ^ r * x₀) * (z ^ (r * A) * x₁) *
        (z ^ (r * A ^ 2) * x₂) = x₀ * x₁ * x₂ := by
  calc
    (z ^ r * x₀) * (z ^ (r * A) * x₁) *
        (z ^ (r * A ^ 2) * x₂) =
        z ^ (r + r * A + r * A ^ 2) * (x₀ * x₁ * x₂) := by
          rw [pow_add, pow_add]
          ac_rfl
    _ = z ^ (r * (1 + A + A ^ 2)) * (x₀ * x₁ * x₂) := by
          congr 2
          ring
    _ = x₀ * x₁ * x₂ := by simp [hz]

variable {R : Type*} [CommRing R]

/-- Elementary coefficients of a monic cubic, in the plus-sign
normalization appropriate to characteristic two. -/
theorem dk_cubic_from_roots [CharP R 2]
    (X x y z : R) :
    (X + x) * (X + y) * (X + z) =
      X ^ 3 + (x + y + z) * X ^ 2 +
        (x * y + x * z + y * z) * X + x * y * z := by
  ring

/-- For the alternating translate, the universal cubic-power-map
Jacobian numerator specializes to the nonzero selected quantity `gamma`. -/
theorem dk_twisted_fibre_target_numerator [CharP R 2]
    (c gamma uParent : R) (hu : uParent = gamma + c ^ 2) :
    c * c + uParent = gamma := by
  rw [hu]
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  ring_nf
  simp [h2]

end DKTwistedFibre

section DKWeightedFibre

variable {G : Type*} [CommGroup G]

/-- The pseudonorm of a power root is a power root of the selected lower
norm. -/
theorem dk_pseudonorm_is_lower_power_root
    (v u uParent : G) (ell Q : Nat)
    (hv : v ^ ell = u)
    (hu : u ^ (1 + Q + Q ^ 2) = uParent) :
    (v ^ (1 + Q + Q ^ 2)) ^ ell = uParent := by
  calc
    (v ^ (1 + Q + Q ^ 2)) ^ ell =
        (v ^ ell) ^ (1 + Q + Q ^ 2) := by
          rw [← pow_mul, ← pow_mul]
          rw [Nat.mul_comm]
    _ = u ^ (1 + Q + Q ^ 2) := by rw [hv]
    _ = uParent := hu

/-- The cubic pseudonorm is unchanged when the Kummer root is rescaled by a
root of unity whose total cubic Frobenius exponent is trivial. -/
theorem dk_pseudonorm_root_choice_invariant
    (rho v : G) (a Q : Nat)
    (hrho : rho ^ (1 + Q + Q ^ 2) = 1) :
    ((rho ^ a) * v) ^ (1 + Q + Q ^ 2) =
      v ^ (1 + Q + Q ^ 2) := by
  rw [mul_pow]
  calc
    (rho ^ a) ^ (1 + Q + Q ^ 2) * v ^ (1 + Q + Q ^ 2) =
        (rho ^ (1 + Q + Q ^ 2)) ^ a *
          v ^ (1 + Q + Q ^ 2) := by
            rw [← pow_mul, ← pow_mul]
            rw [Nat.mul_comm]
    _ = v ^ (1 + Q + Q ^ 2) := by simp [hrho]

/-- The lower-root-normalized pseudonorm defect evaluates to the original
selected Euler class. -/
theorem dk_pseudonorm_defect_eq_euler
    (v u vParent : G) (ell Q e : Nat)
    (hv : v ^ ell = u)
    (hParent : vParent ^ (Q - 1) = 1)
    (hfactor : ell * e = (1 + Q + Q ^ 2) * (Q - 1)) :
    (v ^ (1 + Q + Q ^ 2) / vParent) ^ (Q - 1) = u ^ e := by
  rw [div_pow, hParent, div_one]
  calc
    (v ^ (1 + Q + Q ^ 2)) ^ (Q - 1) =
        v ^ ((1 + Q + Q ^ 2) * (Q - 1)) := by
          rw [pow_mul]
    _ = v ^ (ell * e) := by rw [hfactor]
    _ = (v ^ ell) ^ e := by rw [pow_mul]
    _ = u ^ e := by rw [hv]

/-- A pure Kummer eigenweight acquires exactly the corresponding power of the
selected monodromy under the full cubic Frobenius. -/
theorem dk_eigenweight_power_monodromy
    (v omega a : G) (m N : Nat)
    (hv : v ^ N = omega * v) (ha : a ^ N = a) :
    (v ^ m * a) ^ N = omega ^ m * (v ^ m * a) := by
  rw [mul_pow]
  calc
    (v ^ m) ^ N * a ^ N = (v ^ N) ^ m * a := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm m N, ha]
    _ = (omega * v) ^ m * a := by rw [hv]
    _ = omega ^ m * (v ^ m * a) := by
      rw [mul_pow]
      ac_rfl

/-- The complementary Fourier modes all multiply to the same
root-choice-invariant cubic pseudonorm. -/
theorem mixed_fourier_complementary_products (v : G) (Q : Nat) :
    v * v ^ (Q + Q ^ 2) = v ^ (1 + Q + Q ^ 2) ∧
      v ^ Q * v ^ (Q ^ 2 + 1) = v ^ (1 + Q + Q ^ 2) ∧
      v ^ (Q ^ 2) * v ^ (1 + Q) = v ^ (1 + Q + Q ^ 2) := by
  constructor
  · calc
      v * v ^ (Q + Q ^ 2) = v ^ 1 * v ^ (Q + Q ^ 2) := by simp
      _ = v ^ (1 + (Q + Q ^ 2)) := (pow_add v 1 (Q + Q ^ 2)).symm
      _ = v ^ (1 + Q + Q ^ 2) := by congr 1; omega
  constructor
  · rw [← pow_add]
    congr 1
    omega
  · rw [← pow_add]
    congr 1
    omega

/-- A monomial whose Kummer weight is zero is a coefficient-field power
of the fixed radical `u`. -/
theorem zero_weight_monomial_collapses
    (v u : G) (ell W a : Nat)
    (hv : v ^ ell = u) (hW : W = ell * a) :
    v ^ W = u ^ a := by
  rw [hW, pow_mul, hv]

end DKWeightedFibre

section CubicPhaseTrace

variable {F : Type*} [Field F] [CharP F 2]

/-- If all three elementary symmetric functions of a triple are one in
characteristic two, a distinguished member of the triple is one.  This is
the elementary-symmetric core of the cubic relative-trace detector. -/
theorem cubic_phase_of_symmetric_eq_one
    (x y z : F)
    (htrace : x + y + z = 1)
    (hpair : x * y + x * z + y * z = 1)
    (hnorm : x * y * z = 1) :
    x = 1 := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hthree : (3 : F) = 1 := by
    simpa using (CharP.cast_eq_mod F 2 3)
  have hxx : x + x = 0 := by
    calc
      x + x = (2 : F) * x := by ring
      _ = 0 := by rw [htwo]; simp
  have hpoly : x ^ 3 + x ^ 2 + x + 1 = 0 := by
    calc
      x ^ 3 + x ^ 2 + x + 1 =
          x ^ 3 + (x + y + z) * x ^ 2 +
            (x * y + x * z + y * z) * x + x * y * z := by
              rw [htrace, hpair, hnorm]
              ring
      _ = (x + x) * (x + y) * (x + z) := by ring
      _ = 0 := by rw [hxx]; simp
  have hcube : (x + 1) ^ 3 = 0 := by
    calc
      (x + 1) ^ 3 = x ^ 3 + (3 : F) * x ^ 2 + (3 : F) * x + 1 := by ring
      _ = x ^ 3 + x ^ 2 + x + 1 := by rw [hthree]; simp
      _ = 0 := hpoly
  have hxadd : x + 1 = 0 := by
    by_contra hx
    exact (pow_ne_zero 3 hx) hcube
  have hneg (u : F) : -u = u := by
    rw [neg_eq_iff_add_eq_zero]
    calc
      u + u = (2 : F) * u := by ring
      _ = 0 := by rw [htwo]; simp
  exact (eq_neg_of_add_eq_zero_left hxadd).trans (hneg 1)

/-- Norm one plus trace one and inverse-trace one force the first phase to
be trivial.  Multiplying the inverse trace by the norm supplies the missing
second elementary symmetric function. -/
theorem cubic_phase_of_trace_inverse_trace_eq_one
    (x y z : F)
    (htrace : x + y + z = 1)
    (hinvtrace : x⁻¹ + y⁻¹ + z⁻¹ = 1)
    (hnorm : x * y * z = 1) :
    x = 1 := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx] at hnorm
    simp at hnorm
  have hy : y ≠ 0 := by
    intro hy
    rw [hy] at hnorm
    simp at hnorm
  have hz : z ≠ 0 := by
    intro hz
    rw [hz] at hnorm
    simp at hnorm
  have hpair : x * y + x * z + y * z = 1 := by
    calc
      x * y + x * z + y * z =
          (x⁻¹ + y⁻¹ + z⁻¹) * (x * y * z) := by
            field_simp [hx, hy, hz]
            all_goals ring
      _ = 1 := by rw [hinvtrace, hnorm]; simp
  exact cubic_phase_of_symmetric_eq_one x y z htrace hpair hnorm

end CubicPhaseTrace

section CubicPhaseOrbit

variable {F : Type*} [Field F] [CharP F 2]

/-- In characteristic two, the reciprocal-cubic half-discriminant coordinate
is the product of the three pairwise root differences, which are sums. -/
theorem cubic_phase_discriminant_factorization (x y z : F) :
    (x + y + z) * (x * y + x * z + y * z) + x * y * z =
      (x + y) * (x + z) * (y + z) := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (x * y * z) * htwo

/-- The half-discriminant coordinate vanishes exactly when two roots collide. -/
theorem cubic_phase_discriminant_eq_zero_iff
    (x y z : F) :
    (x + y + z) * (x * y + x * z + y * z) + x * y * z = 0 ↔
      x = y ∨ x = z ∨ y = z := by
  rw [cubic_phase_discriminant_factorization]
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hself (a : F) : a + a = 0 := by
    calc
      a + a = (2 : F) * a := by ring
      _ = 0 := by rw [htwo]; simp
  have hneg (a : F) : -a = a := by
    rw [neg_eq_iff_add_eq_zero]
    exact hself a
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hleft | hyz
    · rcases mul_eq_zero.mp hleft with hxy | hxz
      · left
        exact (eq_neg_of_add_eq_zero_left hxy).trans (hneg y)
      · right; left
        exact (eq_neg_of_add_eq_zero_left hxz).trans (hneg z)
    · right; right
      exact (eq_neg_of_add_eq_zero_left hyz).trans (hneg z)
  · rintro (rfl | rfl | rfl)
    · rw [hself]; simp
    · rw [hself]; simp
    · rw [hself]; simp

/-- Equality of all three elementary symmetric coordinates forces one root
of the second cubic to lie among the roots of the first cubic. -/
theorem cubic_root_mem_of_symmetric_eq
    (x₀ x₁ x₂ y₀ y₁ y₂ : F)
    (htrace : x₀ + x₁ + x₂ = y₀ + y₁ + y₂)
    (hpair : x₀ * x₁ + x₀ * x₂ + x₁ * x₂ =
      y₀ * y₁ + y₀ * y₂ + y₁ * y₂)
    (hnorm : x₀ * x₁ * x₂ = y₀ * y₁ * y₂) :
    y₀ = x₀ ∨ y₀ = x₁ ∨ y₀ = x₂ := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hself (a : F) : a + a = 0 := by
    calc
      a + a = (2 : F) * a := by ring
      _ = 0 := by rw [htwo]; simp
  have hneg (a : F) : -a = a := by
    rw [neg_eq_iff_add_eq_zero]
    exact hself a
  have hprod : (y₀ + x₀) * (y₀ + x₁) * (y₀ + x₂) = 0 := by
    calc
      (y₀ + x₀) * (y₀ + x₁) * (y₀ + x₂) =
          y₀ ^ 3 + (x₀ + x₁ + x₂) * y₀ ^ 2 +
            (x₀ * x₁ + x₀ * x₂ + x₁ * x₂) * y₀ +
              x₀ * x₁ * x₂ := by
                simpa using dk_cubic_from_roots y₀ x₀ x₁ x₂
      _ = y₀ ^ 3 + (y₀ + y₁ + y₂) * y₀ ^ 2 +
            (y₀ * y₁ + y₀ * y₂ + y₁ * y₂) * y₀ +
              y₀ * y₁ * y₂ := by rw [htrace, hpair, hnorm]
      _ = (y₀ + y₀) * (y₀ + y₁) * (y₀ + y₂) := by
            symm
            simpa using dk_cubic_from_roots y₀ y₀ y₁ y₂
      _ = 0 := by rw [hself]; simp
  rcases mul_eq_zero.mp hprod with h01 | h02
  · rcases mul_eq_zero.mp h01 with h0 | h1
    · left
      exact (eq_neg_of_add_eq_zero_left h0).trans (hneg x₀)
    · right; left
      exact (eq_neg_of_add_eq_zero_left h1).trans (hneg x₁)
  · right; right
    exact (eq_neg_of_add_eq_zero_left h02).trans (hneg x₂)

/-- For norm-one triples, equality of trace and inverse trace puts a
distinguished root of the second triple among the roots of the first.  This is
the algebraic membership core used in the Frobenius-orbit separation. -/
theorem cubic_phase_orbit_mem_of_trace_inverse_trace_eq
    (x₀ x₁ x₂ y₀ y₁ y₂ : F)
    (hxnorm : x₀ * x₁ * x₂ = 1)
    (hynorm : y₀ * y₁ * y₂ = 1)
    (htrace : x₀ + x₁ + x₂ = y₀ + y₁ + y₂)
    (hinvtrace : x₀⁻¹ + x₁⁻¹ + x₂⁻¹ =
      y₀⁻¹ + y₁⁻¹ + y₂⁻¹) :
    y₀ = x₀ ∨ y₀ = x₁ ∨ y₀ = x₂ := by
  have x₀ne : x₀ ≠ 0 := by
    intro h
    rw [h] at hxnorm
    simp at hxnorm
  have x₁ne : x₁ ≠ 0 := by
    intro h
    rw [h] at hxnorm
    simp at hxnorm
  have x₂ne : x₂ ≠ 0 := by
    intro h
    rw [h] at hxnorm
    simp at hxnorm
  have y₀ne : y₀ ≠ 0 := by
    intro h
    rw [h] at hynorm
    simp at hynorm
  have y₁ne : y₁ ≠ 0 := by
    intro h
    rw [h] at hynorm
    simp at hynorm
  have y₂ne : y₂ ≠ 0 := by
    intro h
    rw [h] at hynorm
    simp at hynorm
  have hxpair : x₀ * x₁ + x₀ * x₂ + x₁ * x₂ =
      x₀⁻¹ + x₁⁻¹ + x₂⁻¹ := by
    calc
      x₀ * x₁ + x₀ * x₂ + x₁ * x₂ =
          (x₀⁻¹ + x₁⁻¹ + x₂⁻¹) * (x₀ * x₁ * x₂) := by
            field_simp [x₀ne, x₁ne, x₂ne]
            all_goals ring
      _ = x₀⁻¹ + x₁⁻¹ + x₂⁻¹ := by rw [hxnorm]; simp
  have hypair : y₀ * y₁ + y₀ * y₂ + y₁ * y₂ =
      y₀⁻¹ + y₁⁻¹ + y₂⁻¹ := by
    calc
      y₀ * y₁ + y₀ * y₂ + y₁ * y₂ =
          (y₀⁻¹ + y₁⁻¹ + y₂⁻¹) * (y₀ * y₁ * y₂) := by
            field_simp [y₀ne, y₁ne, y₂ne]
            all_goals ring
      _ = y₀⁻¹ + y₁⁻¹ + y₂⁻¹ := by rw [hynorm]; simp
  apply cubic_root_mem_of_symmetric_eq x₀ x₁ x₂ y₀ y₁ y₂ htrace
  · rw [hxpair, hypair, hinvtrace]
  · rw [hxnorm, hynorm]

omit [CharP F 2] in
/-- Once the powered conjugates are one, the entire cubic power-sum sequence
returns with that period. -/
theorem cubic_power_sum_periodic_of_pow_eq_one
    (x y z : F) (e n : Nat)
    (hx : x ^ e = 1) (hy : y ^ e = 1) (hz : z ^ e = 1) :
    x ^ (n + e) + y ^ (n + e) + z ^ (n + e) =
      x ^ n + y ^ n + z ^ n := by
  rw [pow_add, pow_add, pow_add, hx, hy, hz]
  simp

end CubicPhaseOrbit

section DKPhaseBridgeCore

variable {G : Type*} [CommGroup G]

/-- Raising the norm of a selected element to the downstairs Euler exponent
is the same as raising the original element to the upstairs Euler exponent. -/
theorem norm_euler_phase
    (V U rho : G) (A e E L : Nat)
    (hU : U = V ^ (A + 1)) (hE : (A + 1) * e = E)
    (hphase : V ^ E = rho ^ L) :
    U ^ e = rho ^ L := by
  rw [hU, ← pow_mul, hE, hphase]

/-- The norm phase and the selected cubic phase agree after removing the
prime-to-ell cyclotomic factor. -/
theorem selected_phase_bridge
    (V U a u rho : G) (A e E L : Nat)
    (hNorm : U = V ^ (A + 1)) (hE : (A + 1) * e = E)
    (hV : V ^ E = rho ^ L)
    (hFactor : U = a * u) (ha : a ^ e = 1) :
    u ^ e = rho ^ L := by
  have hPhase : U ^ e = rho ^ L :=
    norm_euler_phase V U rho A e E L hNorm hE hV
  rw [hFactor, mul_pow, ha, one_mul] at hPhase
  exact hPhase

/-- Multiplication by an Euler-trivial ancestry factor does not change the
selected Euler phase. -/
theorem ancestry_factor_phase
    (a u U rho : G) (E L : Nat)
    (hU : U = a * u) (ha : a ^ E = 1) (hphase : U ^ E = rho ^ L) :
    u ^ E = rho ^ L := by
  rw [hU, mul_pow, ha, one_mul] at hphase
  exact hphase

/-- If the invariant product of two oriented factors has trivial phase, their
antiunit quotient carries the square of either oriented phase. -/
theorem antiunit_quotient_phase
    (U U' R rho : G) (E L : Nat)
    (hR : R = U * U'⁻¹)
    (hprod : (U * U') ^ E = 1)
    (hU : U ^ E = rho ^ L) :
    R ^ E = (rho ^ L) ^ 2 := by
  have hprod' : U ^ E * U' ^ E = 1 := by
    simpa [mul_pow] using hprod
  have hU' : U' ^ E = (U ^ E)⁻¹ := by
    exact eq_inv_of_mul_eq_one_right hprod'
  rw [hR, mul_pow, inv_pow, hU', hU]
  group

/-- Formally reversing an assumed inverse-phase identity gives the
corresponding oriented equality. -/
theorem sextic_phase_orientation
    (r Omega : G) (d : Nat) (h : Omega = (r ^ d)⁻¹) :
    r ^ d = Omega⁻¹ := by
  rw [h]
  simp

end DKPhaseBridgeCore

section KummerPowerBasis

variable {F V I : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- In a power-basis-shaped decomposition, a scalar multiple of the
weight-zero basis vector has no nonzero-weight coordinate. -/
theorem nonzero_weight_coordinate_eq_zero
    (b : Module.Basis I F V) (i0 i : I) (c : F)
    (hi : i ≠ i0) :
    b.repr (c • b i0) i = 0 := by
  rw [map_smul, Module.Basis.repr_self]
  simp [hi]

end KummerPowerBasis

variable {F : Type*} [Field F] [CharP F 2]

/-- The quadratic auxiliary coordinate `x^2+x+1` determines `x` only up to
the Artin--Schreier pair `x, x+1`. -/
theorem auxiliary_fiber_eq_or_add_one (x y : F) :
    x ^ 2 + x + 1 = y ^ 2 + y + 1 ↔ x = y ∨ x = y + 1 := by
  have hchar : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hneg (u : F) : -u = u := by
    rw [neg_eq_iff_add_eq_zero]
    calc
      u + u = 2 * u := by ring
      _ = 0 := by rw [hchar]; simp
  constructor
  · intro h
    have hfac : (x + y) * (x + y + 1) = 0 := by
      linear_combination h + (x * y + y + y ^ 2) * hchar
    rcases mul_eq_zero.mp hfac with hzero | hone
    · left
      exact (eq_neg_of_add_eq_zero_left hzero).trans (hneg y)
    · right
      have hzero : x + (y + 1) = 0 := by simpa [add_assoc] using hone
      exact (eq_neg_of_add_eq_zero_left hzero).trans (hneg (y + 1))
  · rintro (rfl | rfl)
    · rfl
    · calc
        (y + 1) ^ 2 + (y + 1) + 1 =
            y ^ 2 + y + 1 + 2 * (y + 1) := by ring
        _ = y ^ 2 + y + 1 := by rw [hchar]; simp

variable {S : Type*} [CommRing S]

/-- Once trace, middle coefficient and norm are all fixed, the three
auxiliary conjugates are exactly the roots of one selected cubic. -/
theorem selected_auxiliary_slice_polynomial
    (T G₀ G₁ G₂ a C : S)
    (h₁ : G₀ + G₁ + G₂ = 1)
    (h₂ : G₀ * G₁ + G₀ * G₂ + G₁ * G₂ = a + 1)
    (h₃ : G₀ * G₁ * G₂ = C) :
    (T + G₀) * (T + G₁) * (T + G₂) =
      T ^ 3 + T ^ 2 + (a + 1) * T + C := by
  calc
    _ = T ^ 3 + (G₀ + G₁ + G₂) * T ^ 2 +
        (G₀ * G₁ + G₀ * G₂ + G₁ * G₂) * T + G₀ * G₁ * G₂ := by ring
    _ = T ^ 3 + T ^ 2 + (a + 1) * T + C := by rw [h₁, h₂, h₃]; ring

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

section FermatRemainderCoordinateCore

open Polynomial

/-- A prescribed quotient and every degree-bounded remainder occur exactly
under division by a fixed monic polynomial. -/
theorem monic_div_rem_of_prescribed_pair
    {F : Type*} [Field F]
    (A Q rho : F[X]) (hA : A.Monic) (hrho : rho.degree < A.degree) :
    (rho + A * Q) /ₘ A = Q ∧ (rho + A * Q) %ₘ A = rho := by
  exact Polynomial.div_modByMonic_unique Q rho hA ⟨rfl, hrho⟩

/-- The quotient/remainder presentation under a monic polynomial is unique
once the remainder degrees are bounded. -/
theorem monic_div_rem_pair_unique
    {F : Type*} [Field F]
    (A Q₁ Q₂ rho₁ rho₂ : F[X])
    (hA : A.Monic)
    (hρ₁ : rho₁.degree < A.degree)
    (hρ₂ : rho₂.degree < A.degree)
    (h : rho₁ + A * Q₁ = rho₂ + A * Q₂) :
    Q₁ = Q₂ ∧ rho₁ = rho₂ := by
  have h₁ := monic_div_rem_of_prescribed_pair A Q₁ rho₁ hA hρ₁
  have h₂ := monic_div_rem_of_prescribed_pair A Q₂ rho₂ hA hρ₂
  constructor
  · calc
      Q₁ = (rho₁ + A * Q₁) /ₘ A := h₁.1.symm
      _ = (rho₂ + A * Q₂) /ₘ A := by rw [h]
      _ = Q₂ := h₂.1
  · calc
      rho₁ = (rho₁ + A * Q₁) %ₘ A := h₁.2.symm
      _ = (rho₂ + A * Q₂) %ₘ A := by rw [h]
      _ = rho₂ := h₂.2

/-- An additive coordinate equivalence neither loses nor creates a zero. -/
theorem coordinate_zero_iff
    {E C : Type*} [AddCommGroup E] [AddCommGroup C]
    (coords : E ≃+ C) (x : E) :
    coords x = 0 ↔ x = 0 := by
  exact coords.map_eq_zero_iff

/-- Every complete coordinate pattern is realized by one and only one
residue. -/
theorem every_coordinate_pattern_unique
    {E C : Type*} [AddCommGroup E] [AddCommGroup C]
    (coords : E ≃+ C) (c : C) :
    ∃! x : E, coords x = c := by
  refine ⟨coords.symm c, ?_, ?_⟩
  · simp
  · intro y hy
    exact coords.injective (hy.trans (by simp))

/-- A freely chosen quotient and a freely chosen coordinate pattern remain
independent product coordinates. -/
theorem quotient_and_coordinates_independent
    {Q E C : Type*} [AddCommGroup E] [AddCommGroup C]
    (coords : E ≃+ C) (q : Q) (c : C) :
    ∃! z : Q × E, z.1 = q ∧ coords z.2 = c := by
  refine ⟨(q, coords.symm c), ⟨rfl, by simp⟩, ?_⟩
  rintro ⟨q', x⟩ ⟨hq, hx⟩
  simp only [Prod.mk.injEq]
  constructor
  · exact hq
  · exact coords.injective (hx.trans (by simp))

end FermatRemainderCoordinateCore

section FermatFibonacciQuotientDefectCore

/-- The odd/even quotient defects reconstruct the original Fibonacci
polynomial when `Snext = S + X*dS`. -/
theorem quotient_defects_reconstruct
    {R : Type*} [CommRing R] [CharP R 2]
    (S Snext dS dA Q X : R)
    (hnext : Snext = S + X * dS) :
    (Snext + X * dA * Q) + X * (dS + dA * Q) = S := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  rw [hnext]
  ring_nf
  simp [h2]

/-- After differentiating `S = A*Q + rho`, the odd defect is the derivative
of the remainder modulo `A`. -/
theorem quotient_odd_defect
    {R : Type*} [CommRing R] [CharP R 2]
    (dS A dA Q dQ drho : R)
    (hderiv : dS = dA * Q + A * dQ + drho) :
    dS + dA * Q = A * dQ + drho := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  rw [hderiv]
  ring_nf
  simp [h2]

/-- The even defect is the even part `rho + X*drho` modulo `A`. -/
theorem quotient_even_defect
    {R : Type*} [CommRing R] [CharP R 2]
    (S Snext dS A dA Q dQ rho drho X : R)
    (hS : S = A * Q + rho)
    (hderiv : dS = dA * Q + A * dQ + drho)
    (hnext : Snext = S + X * dS) :
    Snext + X * dA * Q =
      A * (Q + X * dQ) + (rho + X * drho) := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  rw [hnext, hS, hderiv]
  ring_nf
  simp [h2]

/-- The two parity pieces are an invertible encoding of the original
remainder. -/
theorem parity_defects_reconstruct
    {R : Type*} [CommRing R] [CharP R 2]
    (rho drho X : R) :
    (rho + X * drho) + X * drho = rho := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  ring_nf
  simp [h2]

/-- Under exact divisibility, both special quotient defects are themselves
divisible by the selected factor. -/
theorem quotient_defects_of_exact_factor
    {R : Type*} [CommRing R] [CharP R 2]
    (S Snext dS A dA Q dQ X : R)
    (hS : S = A * Q)
    (hderiv : dS = dA * Q + A * dQ)
    (hnext : Snext = S + X * dS) :
    (∃ u, dS + dA * Q = A * u) ∧
      (∃ v, Snext + X * dA * Q = A * v) := by
  refine ⟨⟨dQ, ?_⟩, ⟨Q + X * dQ, ?_⟩⟩
  · simpa using
      quotient_odd_defect dS A dA Q dQ 0 (by simpa using hderiv)
  · simpa using quotient_even_defect
      S Snext dS A dA Q dQ 0 0 X
        (by simpa using hS) (by simpa using hderiv) hnext

end FermatFibonacciQuotientDefectCore

section FermatQuotientWindowCore

variable {R : Type*} [CommRing R]

/-- Multiplying a local parameter by an invertible factor preserves every
power of its principal ideal.  The explicit inverse keeps the statement
independent of localization APIs. -/
theorem unit_rescaling_power_dvd_iff
    (A U V S z : R) (j : Nat) (hS : S = A * U) (hUV : U * V = 1) :
    S ^ j ∣ z ↔ A ^ j ∣ z := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨U ^ j * c, ?_⟩
    rw [hS, mul_pow]
    ring
  · rintro ⟨c, rfl⟩
    refine ⟨V ^ j * c, ?_⟩
    rw [hS, mul_pow]
    calc
      A ^ j * c = A ^ j * ((U * V) ^ j * c) := by rw [hUV, one_pow, one_mul]
      _ = (A ^ j * U ^ j) * (V ^ j * c) := by rw [mul_pow]; ring

/-- Equality of two dividends in a truncated coefficient ring, together
with invertibility of their common factor, forces equality of the quotient
windows. -/
theorem quotient_window_eq_of_inverse
    (A Ainv Q₁ Q₂ S₁ S₂ : R)
    (hInv : Ainv * A = 1)
    (h₁ : S₁ = A * Q₁) (h₂ : S₂ = A * Q₂)
    (hWindow : S₁ = S₂) :
    Q₁ = Q₂ := by
  calc
    Q₁ = (Ainv * A) * Q₁ := by rw [hInv, one_mul]
    _ = Ainv * S₁ := by rw [h₁]; ring
    _ = Ainv * S₂ := by rw [hWindow]
    _ = (Ainv * A) * Q₂ := by rw [h₂]; ring
    _ = Q₂ := by rw [hInv, one_mul]

/-- The high-coefficient-window core: a quotient whose product with a unit
is one is the inverse of that unit. -/
theorem quotient_window_eq_inverse
    (A Ainv Q : R) (hInv : Ainv * A = 1) (hAQ : A * Q = 1) :
    Q = Ainv := by
  calc
    Q = (Ainv * A) * Q := by rw [hInv, one_mul]
    _ = Ainv * (A * Q) := by ring
    _ = Ainv := by rw [hAQ, mul_one]

/-- In a truncated endpoint ring, if the common factor acts trivially on
the first surviving defect, then quotienting transports that defect without
change. For the polynomial application `delta` is the boundary monomial. -/
theorem quotient_boundary_defect_of_fixed
    (A Ainv Q₁ Q₂ S₁ S₂ delta : R)
    (hInv : Ainv * A = 1)
    (h₁ : S₁ = A * Q₁) (h₂ : S₂ = A * Q₂)
    (hdelta : A * delta = delta)
    (hWindow : S₁ = S₂ + delta) :
    Q₁ = Q₂ + delta := by
  calc
    Q₁ = (Ainv * A) * Q₁ := by rw [hInv, one_mul]
    _ = Ainv * S₁ := by rw [h₁]; ring
    _ = Ainv * (S₂ + delta) := by rw [hWindow]
    _ = Ainv * (A * Q₂ + A * delta) := by rw [h₂, hdelta]
    _ = (Ainv * A) * (Q₂ + delta) := by ring
    _ = Q₂ + delta := by rw [hInv, one_mul]

end FermatQuotientWindowCore

section FermatOddJetArithmeticCore

/-- In any quotient where `d = 0` and `4R` is a unit, the odd-branch
relation `d = 1 + R(4t+3)` makes `t = 0` exactly the residual collision
`3R+1 = 0`.  The paper applies this in `ZMod delta`. -/
theorem odd_branch_zero_iff_collision
    {K : Type*} [CommRing K] (d R t : K)
    (hd : d = 1 + R * (4 * t + 3))
    (hd0 : d = 0)
    (hunit : IsUnit (4 * R)) :
    t = 0 ↔ 3 * R + 1 = 0 := by
  have hsplit : (3 * R + 1) + (4 * R) * t = 0 := by
    calc
      (3 * R + 1) + (4 * R) * t = d := by rw [hd]; ring
      _ = 0 := hd0
  constructor
  · intro ht
    simpa [ht] using hsplit
  · intro hcollision
    have hprod : (4 * R) * t = 0 := by
      simpa [hcollision] using hsplit
    exact hunit.mul_left_cancel (by simpa using hprod)

/-- The two integer presentations of the collision differ by combinations
of the Fermat relation `N = P*R + 1`. -/
theorem collision_linear_combinations
    {K : Type*} [CommRing K] (N R C P : K)
    (hN : N = P * R + 1)
    (hC : C = P - 3) :
    R * C = N - (3 * R + 1) := by
  rw [hN, hC]
  ring

/-- Modulo any odd divisor of the Fermat number, the two collision forms
`3R+1` and `P-3` are equivalent when `P*R+1` is the Fermat relation. -/
theorem collision_forms_iff
    {K : Type*} [CommRing K] (N R C P : K)
    (hN : N = P * R + 1)
    (hC : C = P - 3)
    (hN0 : N = 0)
    (hR : IsUnit R) :
    3 * R + 1 = 0 ↔ C = 0 := by
  have hlin := collision_linear_combinations N R C P hN hC
  constructor
  · intro hB
    have hprod : R * C = 0 := by simpa [hN0, hB] using hlin
    exact hR.mul_left_cancel (by simpa using hprod)
  · intro hC0
    calc
      3 * R + 1 = N - R * C := by rw [hlin]; ring
      _ = 0 := by rw [hN0, hC0, mul_zero, sub_zero]

end FermatOddJetArithmeticCore

section FermatOddJetRecoveryCore

open Polynomial

/-- Once a factor and its complement are both either `1` or at least `L`, a
product below `L^2` has no proper nontrivial factorization.  In the paper
`L = 12*M+1`, `B = 3*R+1`, and `G = Gamma_(n,ell)`. -/
theorem short_factor_window
    {B G H L : ℕ}
    (hB : B = G * H)
    (hG : G = 1 ∨ L ≤ G)
    (hH : H = 1 ∨ L ≤ H)
    (hshort : B < L ^ 2) :
    G = 1 ∨ H = 1 := by
  rcases hG with hG | hG
  · exact Or.inl hG
  rcases hH with hH | hH
  · exact Or.inr hH
  exfalso
  rw [hB, pow_two] at hshort
  exact (not_lt_of_ge (Nat.mul_le_mul hG hH)) hshort

/-- A divisor at least `L` cannot divide a positive collision residue below
`L`.  This is the arithmetic core of the upper-end exclusion
`M-s ≤ n+3`. -/
theorem no_large_divisor_of_small_positive
    {p C L : ℕ}
    (hC0 : 0 < C)
    (hCL : C < L)
    (hpL : L ≤ p)
    (hpC : p ∣ C) : False := by
  have hpC' : p ≤ C := Nat.le_of_dvd hC0 hpC
  omega

/-- If `delta > 1` divides an odd index `h = 2*m+1`, it cannot also divide
the derivative index `m`.  Applied to `S_h' = S_m^2`, this makes the recovered
Hasse jet nonzero. -/
theorem odd_index_derivative_coprime
    {delta h m : ℕ}
    (hdelta : 1 < delta)
    (hh : h = 2 * m + 1)
    (hdh : delta ∣ h) :
    ¬ delta ∣ m := by
  intro hdm
  have hd2m : delta ∣ 2 * m := dvd_mul_of_dvd_right hdm 2
  have hd1 : delta ∣ 1 := by
    have := Nat.dvd_sub hdh hd2m
    simpa [hh] using this
  exact (ne_of_gt hdelta) (Nat.dvd_one.mp hd1)

/-- Lucas parity for the composition coefficient in the recovered jet:
`I = 2^(s+1)`, `W = 2^(s+u+2)`, so `choose (I+W) I` is odd. -/
theorem recovered_hasse_choose_odd (s u : ℕ) :
    (((2 ^ s) * (2 + 2 ^ (u + 2))).choose ((2 ^ s) * 2)) % 2 = 1 := by
  have hscale := @Choose.choose_pow_mul_pow_mul_modEq_choose_nat s
      (2 + 2 ^ (u + 2)) 2 2 (inferInstance)
  change (((2 ^ s) * (2 + 2 ^ (u + 2))).choose ((2 ^ s) * 2)) % 2 = 1
  rw [hscale]
  have hbase := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (n := 2 + 2 ^ (u + 2)) (k := 2) (p := 2)
  rw [hbase]
  simp [pow_succ]

/-- The symmetric composition coefficient is also odd. -/
theorem recovered_hasse_choose_odd_symm (s u : ℕ) :
    (((2 ^ s) * 2 + (2 ^ s) * 2 ^ (u + 2)).choose
      ((2 ^ s) * 2 ^ (u + 2))) % 2 = 1 := by
  rw [← Nat.choose_symm_add]
  simpa [Nat.mul_add] using recovered_hasse_choose_odd s u

/-- In characteristic two the iterated-Hasse composition coefficient is one,
so differentiating first at order `I=2R` and then at
`W=2^(u+2)R` recovers the single jet at order `I+W`. -/
theorem recovered_hasse_comp
    {K : Type*} [CommRing K] [CharP K 2]
    (P : K[X]) (s u : ℕ) :
    (@Polynomial.hasseDeriv K _ ((2 ^ s) * 2 ^ (u + 2)))
        ((@Polynomial.hasseDeriv K _ ((2 ^ s) * 2)) P) =
      (@Polynomial.hasseDeriv K _
        ((2 ^ s) * 2 ^ (u + 2) + (2 ^ s) * 2)) P := by
  let W := (2 ^ s) * 2 ^ (u + 2)
  let I := (2 ^ s) * 2
  have hchooseNat : ((W + I).choose W) % 2 = 1 := by
    dsimp [W, I]
    simpa [add_comm] using recovered_hasse_choose_odd_symm s u
  have hchooseK : (((W + I).choose W : ℕ) : K) = 1 := by
    rw [CharP.cast_eq_mod K 2, hchooseNat, Nat.cast_one]
  have hcomp := Polynomial.hasseDeriv_comp (R := K) W I
  have hsmul :
      (W + I).choose W • (@Polynomial.hasseDeriv K _ (W + I)) =
        @Polynomial.hasseDeriv K _ (W + I) := by
    rw [← Nat.cast_smul_eq_nsmul K, hchooseK, one_smul]
  rw [hsmul] at hcomp
  have happ := LinearMap.congr_fun hcomp P
  simpa [LinearMap.comp_apply, W, I] using happ

/-- The explicit recovered value is nonzero once its three selected factors
are nonzero. -/
theorem recovered_hasse_value_ne_zero
    {K : Type*} [Field K]
    (T a D : K) (R W : ℕ)
    (hT : T ≠ 0) (ha : a ≠ 0) (hD : D ≠ 0) :
    T * a ^ R * D ^ W ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero hT (pow_ne_zero _ ha)) (pow_ne_zero _ hD)

end FermatOddJetRecoveryCore

open scoped BigOperators
open Polynomial

section FermatCollisionNorm

variable {K : Type*} [Field K] [CharP K 2]

/-- The rational semiconjugacy used after the congruence `3R = -1`.
This is the denominator-cleared identity
`phi(z^3) = phi(z)^3 / (1 + phi(z)^2)` for
`phi(z) = z / (z+1)^2`. -/
theorem fermat_phi_cube_cleared (z : K)
    (hz : z + 1 ≠ 0) (hz3 : z ^ 3 + 1 ≠ 0) :
    (z ^ 3 / (z ^ 3 + 1) ^ 2) *
        (1 + (z / (z + 1) ^ 2) ^ 2) =
      (z / (z + 1) ^ 2) ^ 3 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h6 : (6 : K) = 0 := by
    calc (6 : K) = 3 * 2 := by norm_num
      _ = 0 := by rw [h2, mul_zero]
  have h16 : (16 : K) = 0 := by
    calc (16 : K) = 8 * 2 := by norm_num
      _ = 0 := by rw [h2, mul_zero]
  have h22 : (22 : K) = 0 := by
    calc (22 : K) = 11 * 2 := by norm_num
      _ = 0 := by rw [h2, mul_zero]
  field_simp
  ring_nf
  rw [h2, h6, h16, h22]
  ring

omit [CharP K 2] in
/-- Product of a local semiconjugacy relation around a finite Frobenius
cycle.  The equivalence `sigma` is used only to reindex both products. -/
theorem fermat_semiconjugacy_cycle_general
    {ι : Type*} [Fintype ι] (sigma : ι ≃ ι) (x y : ι → K) (g : ℕ)
    (hstep : ∀ i, x i * (y (sigma i)) ^ 2 = (x (sigma i)) ^ g) :
    Finset.univ.prod x *
        (Finset.univ.prod y) ^ 2 =
      (Finset.univ.prod x) ^ g := by
  have hp :
      Finset.univ.prod (fun i : ι => x i * (y (sigma i)) ^ 2) =
        Finset.univ.prod (fun i : ι => (x (sigma i)) ^ g) := by
    apply Fintype.prod_congr
    exact hstep
  have hshift2 := Equiv.prod_comp sigma
    (fun i : ι => (y i) ^ 2)
  have hshiftg := Equiv.prod_comp sigma (fun i : ι => x i ^ g)
  have hpow2 :
      Finset.univ.prod (fun i : ι => (y i) ^ 2) =
        (Finset.univ.prod y) ^ 2 := by
    exact Finset.prod_pow Finset.univ 2 y
  have hpowg : Finset.univ.prod (fun i : ι => x i ^ g) =
      (Finset.univ.prod x) ^ g := by
    exact Finset.prod_pow Finset.univ g x
  rw [Finset.prod_mul_distrib, hshift2, hshiftg] at hp
  rwa [hpow2, hpowg] at hp

omit [CharP K 2] in
/-- The cubic collision is the specialization `y = 1 + x`, `g = 3`. -/
theorem fermat_semiconjugacy_cycle
    {ι : Type*} [Fintype ι] (sigma : ι ≃ ι) (x : ι → K)
    (hstep : ∀ i, x i * (1 + x (sigma i)) ^ 2 = (x (sigma i)) ^ 3) :
    Finset.univ.prod x *
        (Finset.univ.prod (fun i : ι => (1 : K) + x i)) ^ 2 =
      (Finset.univ.prod x) ^ 3 := by
  exact fermat_semiconjugacy_cycle_general sigma x
    (fun i => (1 : K) + x i) 3 hstep

/-- Cancelling the first relative norm and using injectivity of Frobenius
turns an odd-power cyclic product into the precise half-power equality. -/
theorem fermat_norm_semiconjugacy_cancel (A B : K) (e : ℕ)
    (hA : A ≠ 0) (h : A * B ^ 2 = A ^ (2 * e + 1)) :
    B = A ^ e := by
  have hs : B ^ 2 = (A ^ e) ^ 2 := by
    apply (mul_left_cancel₀ hA)
    calc
      A * B ^ 2 = A ^ (2 * e + 1) := h
      _ = A * (A ^ e) ^ 2 := by
        rw [pow_succ', ← pow_mul]
        congr 2
        omega
  have hzero : (B + A ^ e) ^ 2 = 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [pow_two]
    calc
      (B + A ^ e) * (B + A ^ e) = B ^ 2 + (A ^ e) ^ 2 := by
        rw [pow_two, pow_two]
        ring_nf
        simp [h2]
      _ = 0 := by rw [hs]; ring_nf; simp [h2]
  have hsum : B + A ^ e = 0 := by
    exact mul_self_eq_zero.mp (by simpa [pow_two] using hzero)
  calc
    B = (B + A ^ e) + A ^ e := by
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      ring_nf
      simp [h2]
    _ = A ^ e := by rw [hsum, zero_add]

/-- Cubic specialization of `fermat_norm_semiconjugacy_cancel`. -/
theorem fermat_norm_collision_cancel (A B : K)
    (hA : A ≠ 0) (h : A * B ^ 2 = A ^ 3) :
    B = A := by
  simpa using fermat_norm_semiconjugacy_cancel A B 1 hA (by simpa using h)

/-- One selected Conway quadratic edge sends a linear remainder to its
explicit norm polynomial. -/
theorem fermat_selected_edge_norm (x y U V : K)
    (hy : y ^ 2 + x * y + x ^ 3 = 0) :
    (U + y * V) * (U + (y + x) * V) =
      U ^ 2 + x * U * V + x ^ 3 * V ^ 2 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hy' : y ^ 2 = x * y + x ^ 3 := by
    calc
      y ^ 2 = y ^ 2 + (y ^ 2 + x * y + x ^ 3) := by rw [hy]; simp
      _ = x * y + x ^ 3 := by ring_nf; simp [h2]
  calc
    (U + y * V) * (U + (y + x) * V) =
        U ^ 2 + x * U * V + (y ^ 2 + x * y) * V ^ 2 := by
      ring_nf
      simp [h2]
    _ = U ^ 2 + x * U * V + x ^ 3 * V ^ 2 := by
      rw [hy']
      ring_nf
      simp [h2]

omit [CharP K 2] in
/-- Degree-theoretic last step of the lower collision flag: a nonzero
polynomial of degree below `3^rho` cannot contain the selected polynomial
of degree `2^v` once `3^rho ≤ 2^v`. -/
theorem fermat_collision_degree_exclusion
    (A D : K[X]) (v rho : ℕ)
    (hAdeg : A.natDegree = 2 ^ v)
    (hD0 : D ≠ 0) (hDdeg : D.natDegree < 3 ^ rho)
    (hbound : 3 ^ rho ≤ 2 ^ v) :
    ¬ A ∣ D := by
  apply Polynomial.not_dvd_of_natDegree_lt hD0
  rw [hAdeg]
  omega

end FermatCollisionNorm

section FermatFixedAdicJetCore

variable {K : Type*} [CommRing K] [CharP K 2]

/-- Algebraic core of the second fixed-`A` digit.  At a root of `A`, the
second Hasse product rule has the displayed left-hand side; if the second
Fibonacci Hasse jet equals the first derivative, the next digit is already
forced by the residue digit. -/
theorem fermat_second_fixed_adic_digit
    (A1 A2 R0 dR0 R1 : K)
    (hjet : A2 * R0 + A1 * (dR0 + A1 * R1) = A1 * R0) :
    A1 ^ 2 * R1 = (A1 + A2) * R0 + A1 * dR0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h := congrArg (fun z => z + A2 * R0 + A1 * dR0) hjet
  ring_nf at h ⊢
  simpa [h2] using h

/-- Exact polynomial identity behind the apparent first Hasse escape.  In the
application `S = S_d`, `B+C = X*V`, `Sp = B^R = S_d'`, and `H = V^R`.
After reducing by a hypothetical factor of `S`, it forces `H` from `Sp`. -/
theorem fermat_first_hasse_escape_identity
    (X T B C V S Sp H : K) (s : Nat)
    (hS : S = C ^ (2 ^ s) + T * B ^ (2 ^ s))
    (hsum : B + C = X * V)
    (hSp : Sp = B ^ (2 ^ s))
    (hH : H = V ^ (2 ^ s)) :
    X ^ (2 ^ s) * H = S + (1 + T) * Sp := by
  rw [hH, ← mul_pow, ← hsum, add_pow_expChar_pow, hS, hSp]
  ring_nf
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [h2]
  simp

/-- Conditional quotient-factor specialization of
`fermat_first_hasse_escape_identity`. -/
theorem fermat_first_hasse_escape_forced
    (X T B C V S Sp H : K) (s : Nat)
    (hS : S = C ^ (2 ^ s) + T * B ^ (2 ^ s))
    (hsum : B + C = X * V)
    (hSp : Sp = B ^ (2 ^ s))
    (hH : H = V ^ (2 ^ s))
    (hzero : S = 0) :
    X ^ (2 ^ s) * H = (1 + T) * Sp := by
  rw [fermat_first_hasse_escape_identity X T B C V S Sp H s hS hsum hSp hH,
    hzero, zero_add]

/-- At Hasse order `2R`, doubling the odd cofactor writes the first genuinely
new block-start in terms of derivatives of the two half-index Fibonacci
polynomials.  This is only the load-bearing ring normalization; identifying
the terms with Hasse derivatives is the paper-level specialization. -/
theorem fermat_second_hasse_escape_normal_form
    (T X dU dV : K) (s : Nat) :
    dU ^ (2 * (2 ^ s)) +
        T * (dU ^ 2 + X * dV ^ 2) ^ (2 ^ s) =
      (1 + T) * dU ^ (2 * (2 ^ s)) +
        T * X ^ (2 ^ s) * dV ^ (2 * (2 ^ s)) := by
  rw [add_pow_expChar_pow, mul_pow]
  have hu : (dU ^ 2) ^ (2 ^ s) = dU ^ (2 * (2 ^ s)) := by
    rw [← pow_mul]
  have hv : (dV ^ 2) ^ (2 ^ s) = dV ^ (2 * (2 ^ s)) := by
    rw [← pow_mul]
  rw [hu, hv]
  ring

end FermatFixedAdicJetCore

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

section FermatSelectedPrimeTransversality

variable {F : Type*} [CommRing F] [CharP F 2]

/-- Algebraic core of the first Witt-coordinate calculation comparing the
canonical Conway Hensel lift with its selected cyclotomic lift. -/
theorem fermat_firstWitt_difference_simplifies (c x s : F) :
    ((c + 1) * s + (c + 1) + x) + (c + x) = (c + 1) * s + 1 := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  calc
    ((c + 1) * s + (c + 1) + x) + (c + x) =
        (c + 1) * s + 1 + 2 * (c + x) := by ring
    _ = (c + 1) * s + 1 := by rw [htwo]; simp

end FermatSelectedPrimeTransversality

section FermatSelectedPrimeAncestry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- If `c` is genuinely born in the quadratic extension, the simplified
first Witt coordinate cannot vanish: otherwise it solves for `c` over the
preceding field. -/
theorem fermat_markedWittCoefficient_ne_zero
    (c : L) (s : K)
    (hc : c ∉ Set.range (algebraMap K L)) :
    (c + 1) * algebraMap K L s + 1 ≠ 0 := by
  intro h
  have hs : s ≠ 0 := by
    intro hs0
    subst s
    simp at h
  apply hc
  refine ⟨(-1 - s) / s, ?_⟩
  rw [map_div₀, map_sub, map_neg, map_one]
  have hsL : algebraMap K L s ≠ 0 := (map_ne_zero (algebraMap K L)).2 hs
  apply (div_eq_iff hsL).2
  linear_combination -1 * h

end FermatSelectedPrimeAncestry

section FermatPrimitiveRay

variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
/-- The first principal coefficient of the shifted canonical nonunit is
nonzero whenever the marked Witt coefficient is nonzero. -/
theorem fermat_rayCoefficient_ne_zero
    (c s : F) (hc1 : c + 1 ≠ 0)
    (hmarked : (c + 1) * s + 1 ≠ 0) :
    s + (c + 1)⁻¹ ≠ 0 := by
  intro h
  apply hmarked
  calc
    (c + 1) * s + 1 = (c + 1) * (s + (c + 1)⁻¹) := by field_simp
    _ = 0 := by rw [h, mul_zero]

/-- If top conjugation sends `c` to `c+1` and fixes the lower coefficient,
the scaled first ray coefficient has relative trace one. -/
theorem fermat_scaledRayCoefficient_trace_one
    (a c s : F) (ha : a = c * (c + 1))
    (hc : c ≠ 0) (hc1 : c + 1 ≠ 0) :
    a * (s + (c + 1)⁻¹) + a * (s + c⁻¹) = 1 := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [ha]
  field_simp
  calc
    c * ((c + 1) * s + 1) + (c + 1) * (c * s + 1) =
        2 * (c * (c + 1) * s + c) + 1 := by ring
    _ = 1 := by rw [htwo]; simp

/-- The normalized selected intersection itself lies in the affine
trace-one coset. -/
theorem fermat_normalizedIntersection_trace_one (a c s : F) :
    (a * s + c) + (a * s + (c + 1)) = 1 := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination htwo * (a * s + c)

end FermatPrimitiveRay

section FermatPacketGapCore

/-- Dropping an entire prime-power conductor contributes at least `p-1`
to the corresponding Euler-totient quotient. -/
theorem fermat_totient_prime_pow_zero_gap
    {p a B : ℕ} (hp : p.Prime) (ha : 0 < a) (hB : B ≤ p - 1) :
    B ≤ Nat.totient (p ^ a) := by
  rw [Nat.totient_prime_pow hp ha]
  exact le_trans hB (Nat.le_mul_of_pos_left (p - 1) (pow_pos hp.pos _))

/-- If a positive amount of a prime-power conductor remains, lowering its
exponent contributes the exact prime-power quotient. -/
theorem fermat_totient_prime_pow_drop
    {p a b : ℕ} (hp : p.Prime) (hb : 0 < b) (hba : b ≤ a) :
    Nat.totient (p ^ a) = p ^ (a - b) * Nat.totient (p ^ b) := by
  rw [Nat.totient_prime_pow hp (lt_of_lt_of_le hb hba)]
  rw [Nat.totient_prime_pow hp hb]
  have hexp : a - 1 = (a - b) + (b - 1) := by omega
  rw [hexp, pow_add]
  ac_rfl

/-- A nonzero prime-power conductor drop contributes at least the prime. -/
theorem fermat_prime_pow_drop_gap
    {p a b B : ℕ} (hp : p.Prime) (hb : 0 < b) (hba : b < a)
    (hB : B ≤ p) :
    B * Nat.totient (p ^ b) ≤ Nat.totient (p ^ a) := by
  rw [fermat_totient_prime_pow_drop hp hb hba.le]
  have hpow : p ≤ p ^ (a - b) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hba)
    rw [hk, pow_succ]
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right p (pow_pos hp.pos k)
  exact Nat.mul_le_mul_right _ (le_trans hB hpow)

/-- At a prime power, any proper exponent drop contributes a local packet
factor at least `G`, provided `G ≤ p - 1`.  The two branches are exactly
the removed-prime and retained-prime factors in a totient quotient. -/
theorem fermat_local_packet_factor_gap
    {p a b G : ℕ}
    (hp : p.Prime)
    (ha : 0 < a)
    (hba : b < a)
    (hG : G ≤ p - 1) :
    G ≤ if b = 0 then Nat.totient (p ^ a) else p ^ (a - b) := by
  by_cases hb : b = 0
  · simp only [hb, if_pos]
    exact fermat_totient_prime_pow_zero_gap hp ha hG
  · simp only [hb]
    have hGp : G ≤ p := hG.trans (Nat.sub_le p 1)
    have hpow : p ≤ p ^ (a - b) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.sub_ne_zero_of_lt hba)
      rw [hk, pow_succ]
      simpa [Nat.mul_comm] using
        Nat.le_mul_of_pos_right p (pow_pos hp.pos k)
    exact hGp.trans hpow

/-- Once one local factor is at least `G`, multiplying by the remaining
positive local factors preserves the gap.  This is the product step in the
prime-power factorization of `φ(N) / φ(δ)`. -/
theorem packet_gap_of_local_factor
    (G q rest t : ℕ)
    (hfactor : q * rest = t)
    (hlocal : G ≤ q)
    (hrest : 0 < rest) :
    G ≤ t := by
  calc
    G ≤ q := hlocal
    _ = q * 1 := by simp
    _ ≤ q * rest := Nat.mul_le_mul_left q hrest
    _ = t := hfactor

/-- Abstract exact threshold: a full conductor has packet one, while every
proper conductor has packet at least `G`. -/
theorem csdu_full_iff_packet_lt_gap
    (delta N G t : ℕ)
    (hG : 1 < G)
    (hfull : delta = N → t = 1)
    (hproper : delta ≠ N → G ≤ t) :
    delta = N ↔ t < G := by
  constructor
  · intro hdelta
    rw [hfull hdelta]
    exact hG
  · intro ht
    by_contra hdelta
    exact (not_le_of_gt ht) (hproper hdelta)

/-- A single retained prime with `p - 1 ≥ cB` already forces the same
lower bound on the totient of the selected conductor. -/
theorem totient_lower_of_large_prime_divisor
    (B c p delta : ℕ)
    (hp : p.Prime)
    (hpd : p ∣ delta)
    (hdelta : 0 < delta)
    (hgap : c * B + 1 ≤ p) :
    c * B ≤ delta.totient := by
  have hdvd : p.totient ∣ delta.totient := Nat.totient_dvd_of_dvd hpd
  have hle : p.totient ≤ delta.totient :=
    Nat.le_of_dvd (Nat.totient_pos.mpr hdelta) hdvd
  rw [Nat.totient_prime hp] at hle
  omega

/-- The load-bearing inequality behind the global packet sieve.  Once every
prime retained by the selected conductor forces `c * B ≤ φ(δ)`, the exact
packet identity `t * φ(δ) = φ(N)` gives the advertised upper bound without
division or rounding conventions. -/
theorem csdu_packet_upper_of_totient_lower
    (B c t phiN phiDelta : ℕ)
    (hfactor : t * phiDelta = phiN)
    (hphi : c * B ≤ phiDelta) :
    t * (c * B) ≤ phiN := by
  calc
    t * (c * B) ≤ t * phiDelta := Nat.mul_le_mul_left t hphi
    _ = phiN := hfactor

/-- The same bound after replacing the ambient totient by any explicit
upper bound, e.g. `φ(F_n) ≤ F_n - 1 = 2^(2^n)`. -/
theorem csdu_packet_upper_of_ambient_bound
    (B c t phiN phiDelta Q : ℕ)
    (hfactor : t * phiDelta = phiN)
    (hphi : c * B ≤ phiDelta)
    (hambient : phiN ≤ Q) :
    t * (c * B) ≤ Q :=
  (csdu_packet_upper_of_totient_lower
    B c t phiN phiDelta hfactor hphi).trans hambient

/-- The strengthened packet gap and the retained-conductor totient bound
force the square lower bound `G² ≤ φ(N)`. -/
theorem csdu_failure_forces_totient_square
    (G t phiN phiDelta : ℕ)
    (hpacket : G ≤ t)
    (hfactor : t * phiDelta = phiN)
    (hphi : G ≤ phiDelta) :
    G * G ≤ phiN := by
  calc
    G * G ≤ t * phiDelta := Nat.mul_le_mul hpacket hphi
    _ = phiN := hfactor

/-- Division-free closure form of the square threshold. -/
theorem csdu_closes_below_totient_square
    (G t phiN phiDelta : ℕ)
    (hfactor : t * phiDelta = phiN)
    (hphi : G ≤ phiDelta)
    (hsmall : phiN < G * G) :
    t < G := by
  by_contra h
  have hpacket : G ≤ t := Nat.le_of_not_gt h
  have hlarge : G * G ≤ phiN :=
    csdu_failure_forces_totient_square
      G t phiN phiDelta hpacket hfactor hphi
  omega

end FermatPacketGapCore

section FermatHigherWittSaturation

variable {R : Type*} [CommRing R]

/-- Universal two-adic binomial divisibility: the `2^m`-th power of a
principal two-unit is one modulo `2^(m+1)`. -/
theorem principalTwoUnit_pow_two_expansion (z : R) :
    ∀ m : ℕ, ∃ h : R,
      (1 + 2 * z) ^ (2 ^ m) = 1 + (2 : R) ^ (m + 1) * h := by
  intro m
  induction m with
  | zero =>
      refine ⟨z, ?_⟩
      norm_num
  | succ m ih =>
      obtain ⟨h, hh⟩ := ih
      refine ⟨h + (2 : R) ^ m * h ^ 2, ?_⟩
      rw [pow_succ, pow_mul, hh]
      ring

/-- Hence the Fermat exponent `1+2^m` acts identically on a principal
two-unit modulo `2^(m+1)`. -/
theorem fermatExponent_principalTwoUnit_expansion (z : R) (m : ℕ) :
    ∃ h : R,
      (1 + 2 * z) ^ (2 ^ m + 1) =
        (1 + 2 * z) + (2 : R) ^ (m + 1) * h := by
  obtain ⟨h, hh⟩ := principalTwoUnit_pow_two_expansion z m
  refine ⟨(1 + 2 * z) * h, ?_⟩
  rw [pow_add, hh]
  ring

/-- Exact numerator reparametrization for the product over all nontrivial
odd-order torsion coordinates. -/
theorem canonical_allTorsion_numerator
    {K : Type*} [Field K]
    (C W : K) (N : ℕ) (hC : C ≠ 0) (hW : W = -(C + 1) / C) :
    (C - 1) ^ N + C ^ N = C ^ N * ((W + 2) ^ N + 1) := by
  have hshift : C * (W + 2) = C - 1 := by
    rw [hW]
    field_simp
    ring
  calc
    (C - 1) ^ N + C ^ N = (C * (W + 2)) ^ N + C ^ N := by rw [hshift]
    _ = C ^ N * (W + 2) ^ N + C ^ N := by rw [mul_pow]
    _ = C ^ N * ((W + 2) ^ N + 1) := by ring

/-- Exact relative norm of the shifted canonical nonunit
`U=(1-C)/C`; its first-order term forces the trace-one ray coefficient. -/
theorem canonical_shiftedUnit_relativeNorm
    {K : Type*} [Field K]
    (C A : K) (hC : C ≠ 0) (hC1 : C + 1 ≠ 0)
    (hrel : C ^ 2 + C + A = 0) :
    ((1 - C) / C) * ((C + 2) / (-(C + 1))) = 1 + 2 / A := by
  have hA : A = -(C * (C + 1)) := by
    linear_combination hrel
  rw [hA]
  field_simp
  ring

end FermatHigherWittSaturation

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

/-- After translating the first upper Conway block to the trace-one model,
the two norm terms collapse to the universal polynomial `Y^q+Y+1`. -/
theorem universal_trace_one_collapse
    {R : Type*} [CommRing R] [CharP R 2] (y yq : R) :
    (yq + 1) * (y + 1) + yq * y = yq + y + 1 := by
  ring_nf
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  rw [htwo]
  simp

/-- The translated factor's value at the Conway-marked endpoint is exactly
the defect of its one Kummer phase. -/
theorem marked_constant_is_phase_defect
    {R : Type*} [CommRing R] (c w C : R) (d : Nat)
    (hc : c + 1 = c * w) (hC : w ^ d = C) :
    (c + 1) ^ d + c ^ d = c ^ d * (C + 1) := by
  rw [hc, mul_pow, hC]
  ring

end ConwayBitKummer

section OrdinaryAffineTranslate

variable {R : Type*} [CommRing R]

/-- Algebraic core of the ordinary affine-translate orbit polynomial.  The
finite-field product `prod_(c in F_q) (Y+1+c*x)` supplies the two terms on
the left after `x^q=lambda*x`. -/
theorem ordinary_affine_translate_collapse (Y Yq lambda : R) :
    (Yq + 1) + lambda * (Y + 1) = Yq + lambda * Y + (1 + lambda) := by
  ring

end OrdinaryAffineTranslate

section Ordinary359FullConductor

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The first exact odd-Kummer dependency lift in the selected `p=359`
Conway chain. -/
theorem ordinary359_first_dependency_polynomial (X : R) :
    ((X + 1) ^ 5) ^ 4 + (X + 1) ^ 5 + 1 =
      X ^ 20 + X ^ 16 + X ^ 5 + X + 1 := by
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have hsquare (u v : R) : (u + v) ^ 2 = u ^ 2 + v ^ 2 := by
    calc
      (u + v) ^ 2 = u ^ 2 + 2 * u * v + v ^ 2 := by ring
      _ = u ^ 2 + v ^ 2 := by rw [htwo]; ring
  have hfourth (u v : R) : (u + v) ^ 4 = u ^ 4 + v ^ 4 := by
    calc
      (u + v) ^ 4 = ((u + v) ^ 2) ^ 2 := by ring
      _ = (u ^ 2 + v ^ 2) ^ 2 := by rw [hsquare]
      _ = u ^ 4 + v ^ 4 := by rw [hsquare]; ring
  have hfive : (X + 1) ^ 5 = X ^ 5 + X ^ 4 + X + 1 := by
    calc
      (X + 1) ^ 5 = (X + 1) ^ 4 * (X + 1) := by ring
      _ = (X ^ 4 + 1) * (X + 1) := by rw [hfourth]; ring
      _ = X ^ 5 + X ^ 4 + X + 1 := by ring
  rw [hfive]
  calc
    (X ^ 5 + X ^ 4 + X + 1) ^ 4 + (X ^ 5 + X ^ 4 + X + 1) + 1 =
        X ^ 20 + X ^ 16 + X ^ 4 + 1 +
          (X ^ 5 + X ^ 4 + X + 1) + 1 := by
            repeat' rw [hfourth]
            ring
    _ = X ^ 20 + X ^ 16 + X ^ 5 + X + 1 := by
      linear_combination (X ^ 4 + 1) * htwo

variable {F K : Type*} [CommRing F] [CommRing K]

/-- Once the marked irreducible factor is fixed, a field-model change cannot
alter the selected power class. -/
theorem ordinary_marked_power_status_equiv
    (e : F ≃+* K) (x : F) (p : Nat) :
    (∃ y : F, y ^ p = x) ↔ ∃ z : K, z ^ p = e x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e y, by simp⟩
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, ?_⟩
    apply e.injective
    simpa using hz

end Ordinary359FullConductor

section Ordinary719CompactNorm

variable {F I : Type*} [Field F]

/-- Evaluating a monic root product after scalar multiplication needs only
the original polynomial at the inverse scalar.  This is the algebraic core
of `Norm(1 + a*v) = v^d * f_a(v⁻¹)`. -/
theorem compact_scaled_root_product
    (S : Finset I) (a : I → F) (v : F) (hv : v ≠ 0) :
    (∏ i ∈ S, (1 + a i * v)) =
      v ^ S.card * ∏ i ∈ S, (v⁻¹ + a i) := by
  have hpoint (i : I) : 1 + a i * v = v * (v⁻¹ + a i) := by
    field_simp
  simp_rw [hpoint]
  rw [Finset.prod_mul_distrib]
  simp

/-- Once two finite-field norm exponents multiply to the full Euler
exponent, norm transitivity becomes an ordinary power identity. -/
theorem compact_nested_euler_power
    {G : Type*} [CommMonoid G] (x : G)
    (relative small full : Nat) (hfull : full = relative * small) :
    (x ^ relative) ^ small = x ^ full := by
  rw [hfull, pow_mul]

end Ordinary719CompactNorm

section Ordinary727Certificate

/-- The first row after the crossed `p=719` certificate is again prime. -/
theorem ordinary727_prime : Nat.Prime 727 := by norm_num

/-- Exact multiplicative-order arithmetic behind `ord_727(2)=121`.  Since
`121=11^2`, checking the only proper prime quotient `11` is sufficient. -/
theorem ordinary727_order_arithmetic :
    2 ^ 121 % 727 = 1 ∧ 2 ^ 11 % 727 ≠ 1 := by
  norm_num

/-- The selected full-conductor polynomial is
`P_alpha_11(X^121)` and has degree `20*121=2420`. -/
theorem ordinary727_selected_degree : 20 * 121 = 2420 := by norm_num

end Ordinary727Certificate

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

section CubicCoupledKummerRoots

variable {G : Type*} [CommGroup G]

/-- The Singer identity transports a chosen `ell`-th root of `eta` to a
chosen `ell`-th root of `epsilon = eta^(q+1)`. -/
theorem cubic_eta_root_to_epsilon_root
    (t eta epsilon : G) (ell q : Nat)
    (ht : t ^ ell = eta) (hepsilon : epsilon = eta ^ (q + 1)) :
    (t ^ (q + 1)) ^ ell = epsilon := by
  calc
    (t ^ (q + 1)) ^ ell = (t ^ ell) ^ (q + 1) := by
      rw [← pow_mul, ← pow_mul]
      rw [Nat.mul_comm]
    _ = eta ^ (q + 1) := by rw [ht]
    _ = epsilon := hepsilon.symm

/-- Bezout transport of a chosen `eta` root to a chosen `beta` root.
The hypotheses are the exact selected identity
`beta^(q-1) = eta^-1` and `A*(q-1) = 1 + ell*B`. -/
theorem cubic_eta_root_to_beta_root
    (t eta beta : G) (ell q A B : Nat)
    (ht : t ^ ell = eta)
    (hbeta : beta ^ (q - 1) = eta⁻¹)
    (hbezout : A * (q - 1) = 1 + ell * B) :
    ((t⁻¹) ^ A * (beta⁻¹) ^ B) ^ ell = beta := by
  have hetaA : (eta⁻¹) ^ A = beta ^ (1 + ell * B) := by
    calc
      (eta⁻¹) ^ A = (beta ^ (q - 1)) ^ A := by rw [hbeta]
      _ = beta ^ ((q - 1) * A) := by rw [pow_mul]
      _ = beta ^ (A * (q - 1)) := by rw [Nat.mul_comm]
      _ = beta ^ (1 + ell * B) := by rw [hbezout]
  rw [mul_pow]
  calc
    ((t⁻¹) ^ A) ^ ell * ((beta⁻¹) ^ B) ^ ell =
        ((t⁻¹) ^ ell) ^ A * ((beta⁻¹) ^ ell) ^ B := by
          rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
          congr 1 <;> rw [Nat.mul_comm]
    _ = (eta⁻¹) ^ A * ((beta⁻¹) ^ ell) ^ B := by
          rw [inv_pow, ht]
    _ = beta ^ (1 + ell * B) * ((beta⁻¹) ^ ell) ^ B := by
          rw [hetaA]
    _ = beta := by
          rw [pow_add, pow_one, pow_mul, inv_pow]
          group

/-- Scaling the chosen `eta` root by `rho` scales the transported
`epsilon` and `beta` roots by their exact Kummer weights. -/
theorem cubic_coupled_root_scaling
    (rho t beta : G) (q A B : Nat) :
    ((rho * t) ^ (q + 1) = rho ^ (q + 1) * t ^ (q + 1)) ∧
      (((rho * t)⁻¹) ^ A * (beta⁻¹) ^ B =
        (rho⁻¹) ^ A * ((t⁻¹) ^ A * (beta⁻¹) ^ B)) := by
  constructor
  · rw [mul_pow]
  · rw [mul_inv_rev, mul_pow]
    ac_rfl

end CubicCoupledKummerRoots

section CubicCurrentWeight

/-- Removing a current factor `q^2+q+1 = ell*u` from the cubic full-field
exponent gives the monodromy exponent used below. -/
theorem cubic_current_full_exponent_factorization
    (q ell u : Nat) (hq : 1 ≤ q)
    (hN : q ^ 2 + q + 1 = ell * u) :
    q ^ 3 = 1 + ell * ((q - 1) * u) := by
  have hq' : q - 1 + 1 = q := Nat.sub_add_cancel hq
  nlinarith

variable {G : Type*} [CommGroup G]

/-- A chosen `ell`-th root of the normalized Singer coordinate has
full-field Frobenius monodromy equal to the `(q-1)`-st power of the
selected Euler phase `Omega = tau^u`. -/
theorem cubic_current_root_monodromy
    (v tau Omega : G) (ell q u : Nat)
    (hv : v ^ ell = tau) (hOmega : Omega = tau ^ u)
    (hfactor : q ^ 3 = 1 + ell * ((q - 1) * u)) :
    v ^ (q ^ 3) = Omega ^ (q - 1) * v := by
  rw [hfactor, pow_add, pow_one]
  calc
    v * v ^ (ell * ((q - 1) * u)) =
        v * (v ^ ell) ^ ((q - 1) * u) := by rw [pow_mul]
    _ = v * tau ^ ((q - 1) * u) := by rw [hv]
    _ = v * (tau ^ u) ^ (q - 1) := by
      congr 1
      rw [← pow_mul, Nat.mul_comm (q - 1) u]
    _ = Omega ^ (q - 1) * v := by rw [← hOmega]; ac_rfl

/-- Every pure nonzero Kummer weight carries the corresponding invertible
power of the same current Euler monodromy. -/
theorem cubic_current_pure_weight_monodromy
    (v Omega coeff : G) (m q : Nat)
    (hv : v ^ (q ^ 3) = Omega ^ (q - 1) * v)
    (hcoeff : coeff ^ (q ^ 3) = coeff) :
    (v ^ m * coeff) ^ (q ^ 3) =
      Omega ^ (m * (q - 1)) * (v ^ m * coeff) := by
  calc
    (v ^ m * coeff) ^ (q ^ 3) =
        (Omega ^ (q - 1)) ^ m * (v ^ m * coeff) := by
          exact dk_eigenweight_power_monodromy
            v (Omega ^ (q - 1)) coeff m (q ^ 3) hv hcoeff
    _ = Omega ^ (m * (q - 1)) * (v ^ m * coeff) := by
          congr 1
          rw [← pow_mul, Nat.mul_comm (q - 1) m]

end CubicCurrentWeight

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

section CubicAncestralJacobian

variable {R : Type*} [CommRing R] [CharP R 2]

open Polynomial

/-- The derivative of the selected cubic edge is the square of its
translated coordinate. -/
theorem cubicMap_derivative :
    derivative ((X : R[X]) ^ 3 + X) = (X + 1) ^ 2 := by
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have hthree : (3 : R) = 1 := by
    rw [show (3 : R) = 2 + 1 by norm_num, htwo, zero_add]
  have htwoPoly : (2 : R[X]) = 0 := CharP.cast_eq_zero R[X] 2
  simp [derivative_add, derivative_pow, hthree]
  ring_nf
  rw [htwoPoly, mul_zero, add_zero]

/-- The selected cubic map `x |-> x^3+x`, iterated `m` times. -/
def cubicIterate (x : R) : Nat → R
  | 0 => x
  | m + 1 => cubicIterate x m ^ 3 + cubicIterate x m

/-- The canonical square root of the first `m` edge Jacobians. -/
def cubicAncestralRoot (x : R) : Nat → R
  | 0 => 1
  | m + 1 => cubicAncestralRoot x m * (cubicIterate x m + 1)

/-- In characteristic two, one cubic step is the input times the square of
its translated input. -/
theorem cubicStep_eq_mul_translate_sq (x : R) :
    x ^ 3 + x = x * (x + 1) ^ 2 := by
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  calc
    x ^ 3 + x = x ^ 3 + (2 : R) * x ^ 2 + x := by rw [htwo, zero_mul, add_zero]
    _ = x * (x + 1) ^ 2 := by ring

/-- Full iterated factorization: the `m`-fold selected cubic iterate is the
top input times the square of the product of all preceding translates. -/
theorem cubicIterate_eq_mul_ancestralRoot_sq (x : R) :
    ∀ m, cubicIterate x m = x * cubicAncestralRoot x m ^ 2 := by
  intro m
  induction m with
  | zero => simp [cubicIterate, cubicAncestralRoot]
  | succ m ih =>
      rw [cubicIterate, cubicStep_eq_mul_translate_sq, ih]
      simp only [cubicAncestralRoot]
      simp only [ih]
      ring_nf

omit [CharP R 2] in
/-- The canonical roots themselves satisfy the expected prefix-product
recursion. -/
theorem cubicAncestralRoot_succ (x : R) (m : Nat) :
    cubicAncestralRoot x (m + 1) =
      cubicAncestralRoot x m * (cubicIterate x m + 1) := by
  rfl

/-- Product of the genuinely lower ancestral translates, with the top
translate omitted. -/
def cubicAncestralTail (x : R) : Nat → R
  | 0 => 1
  | m + 1 => cubicAncestralTail x m * (cubicIterate x (m + 1) + 1)

omit [CharP R 2] in
/-- Exact algebra behind the lower-field-line collapse: every nonempty
ancestral root is the same top translate times a product involving only
strictly lower iterates. -/
theorem cubicAncestralRoot_succ_eq_translate_mul_tail (x : R) :
    ∀ m, cubicAncestralRoot x (m + 1) =
      (x + 1) * cubicAncestralTail x m := by
  intro m
  induction m with
  | zero => simp [cubicAncestralRoot, cubicAncestralTail, cubicIterate]
  | succ m ih =>
      rw [cubicAncestralRoot_succ, ih]
      simp only [cubicAncestralTail]
      ring

omit [CharP R 2] in
/-- Every lower-coefficient linear combination of nonempty ancestral roots
still lies on the single line generated by the top translate. -/
theorem sum_cubicAncestralRoot_succ_eq_translate_mul_sum
    (x : R) (s : Finset Nat) (a : Nat → R) :
    ∑ m ∈ s, a m * cubicAncestralRoot x (m + 1) =
      (x + 1) * ∑ m ∈ s, a m * cubicAncestralTail x m := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [cubicAncestralRoot_succ_eq_translate_mul_tail]
  ring

end CubicAncestralJacobian

section CubicAncestralJacobianField

variable {K : Type*} [Field K] [CharP K 2]

/-- Ratio form used at the selected tower point: the canonical ancestral
root square is the lower iterate divided by the top coordinate. -/
theorem cubicAncestralRoot_sq_eq_iterate_div (x : K) (m : Nat)
    (hx : x ≠ 0) :
    cubicAncestralRoot x m ^ 2 = cubicIterate x m / x := by
  apply (eq_div_iff hx).2
  rw [mul_comm]
  exact (cubicIterate_eq_mul_ancestralRoot_sq x m).symm

end CubicAncestralJacobianField

section CubicMixedAncestralCoordinates

variable {R : Type*} [CommRing R] [CharP R 2]

/-- Translating the selected Conway cubic by one gives the cubic relation
used by the inhomogeneous ancestral-coordinate normal form. -/
theorem translated_selected_cubic (gamma gammaPrev : R)
    (hgamma : gamma ^ 3 + gamma = gammaPrev) :
    (gamma + 1) ^ 3 + (gamma + 1) ^ 2 + gammaPrev = 0 := by
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have hfour : (4 : R) = 0 := by
    rw [show (4 : R) = 2 + 2 by norm_num, htwo, zero_add]
  have hfive : (5 : R) = 1 := by
    rw [show (5 : R) = 4 + 1 by norm_num, hfour, zero_add]
  rw [show (gamma + 1) ^ 3 + (gamma + 1) ^ 2 + gammaPrev =
      gamma ^ 3 + gamma + gammaPrev by
    ring_nf
    rw [htwo, hfour, hfive]
    ring]
  rw [hgamma]
  have : gammaPrev + gammaPrev = (2 : R) * gammaPrev := by ring
  rw [this, htwo, zero_mul]

/-- Multiplication by the translated top coordinate preserves the quadratic
normal form, using `z^3 = z^2 + gammaPrev` in characteristic two. -/
theorem cubic_normal_form_mul (z gammaPrev a0 a1 a2 : R)
    (hz : z ^ 3 + z ^ 2 + gammaPrev = 0) :
    (a0 + a1 * z + a2 * z ^ 2) * z =
      a2 * gammaPrev + a0 * z + (a1 + a2) * z ^ 2 := by
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have hz' : z ^ 3 = z ^ 2 + gammaPrev := by
    calc
      z ^ 3 = z ^ 3 + (z ^ 3 + z ^ 2 + gammaPrev) := by rw [hz, add_zero]
      _ = z ^ 2 + gammaPrev := by
        ring_nf
        rw [htwo]
        ring
  rw [show (a0 + a1 * z + a2 * z ^ 2) * z =
      a0 * z + a1 * z ^ 2 + a2 * z ^ 3 by ring, hz']
  ring

/-- Coefficients of the canonical quadratic remainder of `X^n` modulo
`X^3 + X^2 + gammaPrev`. -/
def cubicPowerCoeffs (gammaPrev : R) : Nat → R × R × R
  | 0 => (1, 0, 0)
  | n + 1 =>
      let a := cubicPowerCoeffs gammaPrev n
      (a.2.2 * gammaPrev, a.1, a.2.1 + a.2.2)

/-- Every power of the translated selected coordinate has the canonical
quadratic normal form supplied by `cubicPowerCoeffs`. -/
theorem pow_eq_cubicPowerCoeffs (z gammaPrev : R)
    (hz : z ^ 3 + z ^ 2 + gammaPrev = 0) :
    ∀ n, let a := cubicPowerCoeffs gammaPrev n
      z ^ n = a.1 + a.2.1 * z + a.2.2 * z ^ 2 := by
  intro n
  induction n with
  | zero => simp [cubicPowerCoeffs]
  | succ n ih =>
      rw [pow_succ, ih,
        cubic_normal_form_mul z gammaPrev
          (cubicPowerCoeffs gammaPrev n).1
          (cubicPowerCoeffs gammaPrev n).2.1
          (cubicPowerCoeffs gammaPrev n).2.2 hz]
      rfl

omit [CharP R 2] in
/-- The actual ancestral roots and Jacobians are respectively one linear
coordinate and its square, up to fixed coefficients. -/
theorem ancestral_root_jacobian_coordinates {ι : Type*}
    (z : R) (c roots jacobians : ι → R)
    (hroots : ∀ i, roots i = c i * z)
    (hjacobians : ∀ i, jacobians i = roots i ^ 2) (i : ι) :
    roots i = c i * z ∧ jacobians i = c i ^ 2 * z ^ 2 := by
  constructor
  · exact hroots i
  · rw [hjacobians i, hroots i]
    ring

omit [CharP R 2] in
/-- Once one ancestral coefficient is one, the root/Jacobian family already
contains the full quadratic normal-form coordinate. -/
theorem quadratic_normal_form_is_mixed_ancestral {ι : Type*}
    (z a0 a1 a2 : R) (c roots jacobians : ι → R) (i0 : ι)
    (hc : c i0 = 1) (hroots : roots i0 = c i0 * z)
    (hjacobians : jacobians i0 = roots i0 ^ 2) :
    a0 + a1 * z + a2 * z ^ 2 =
      a0 + a1 * roots i0 + a2 * jacobians i0 := by
  rw [hjacobians, hroots, hc, one_mul]

omit [CharP R 2] in
/-- Every generator appearing in the formal mixed ancestral presentation
evaluates to zero. The reverse ideal containment remains paper-level. -/
theorem ancestral_presentation_generators_vanish {ι : Type*}
    (gammaPrev z : R) (c roots jacobians : ι → R)
    (hroots : ∀ i, roots i = c i * z)
    (hjacobians : ∀ i, jacobians i = roots i ^ 2)
    (hz : z ^ 3 + z ^ 2 + gammaPrev = 0) (i : ι) :
    roots i - c i * z = 0 ∧
      jacobians i - roots i ^ 2 = 0 ∧
      z ^ 3 + z ^ 2 + gammaPrev = 0 := by
  simp [hroots i, hjacobians i, hz]

omit [CharP R 2] in
/-- The translated relative cubic is an explicit nonzero formal mixed-degree
relation that vanishes at the selected ancestral root coordinate. -/
theorem ancestral_mixed_kernel_witness {ι : Type*}
    (z gammaPrev : R) (c roots : ι → R) (i0 : ι)
    (hc : c i0 = 1) (hroots : roots i0 = c i0 * z)
    (hz : z ^ 3 + z ^ 2 + gammaPrev = 0) :
    roots i0 ^ 3 + roots i0 ^ 2 + gammaPrev = 0 := by
  rw [hroots, hc, one_mul]
  exact hz

/-- The degree-one ancestral root already recovers the original selected top
coordinate after translating back by one. -/
theorem selected_top_coordinate_recovered {ι : Type*}
    (gamma : R) (c roots : ι → R) (i0 : ι)
    (hc : c i0 = 1) (hroots : roots i0 = c i0 * (gamma + 1)) :
    roots i0 + 1 = gamma := by
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  rw [hroots, hc, one_mul]
  have : (1 : R) + 1 = 2 := by norm_num
  rw [add_assoc, this, htwo, add_zero]

end CubicMixedAncestralCoordinates

section CubicMixedAncestralField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Relative degree three makes the quadratic normal form unique. -/
theorem quadratic_normal_form_eq_zero_iff (z : L)
    (hdeg : (minpoly K z).natDegree = 3) (a0 a1 a2 : K) :
    algebraMap K L a0 + algebraMap K L a1 * z +
        algebraMap K L a2 * z ^ 2 = 0 ↔
      a0 = 0 ∧ a1 = 0 ∧ a2 = 0 := by
  constructor
  · intro h
    have hli := linearIndependent_pow (K := K) z
    rw [hdeg] at hli
    have hs : ∑ i : Fin 3, (![a0, a1, a2] i) • z ^ (i : Nat) = 0 := by
      simpa [Fin.sum_univ_succ, Algebra.smul_def, add_assoc] using h
    have hc := Fintype.linearIndependent_iff.mp hli ![a0, a1, a2] hs
    exact ⟨hc 0, hc 1, hc 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

end CubicMixedAncestralField

end CyclotomicReflectionAlgebra

namespace CubicTwoNormalCounterexample

/-! Exact bit-polynomial arithmetic for the paper's degree-81 countermodel.
Bit `i` is the coefficient of `X^i`; the modulus has degree 81. -/

def modulus : Nat := 0x329341f8b47dd7938af63
def degree : Nat := 81
def q : Nat := 2 ^ 27
def fieldOrder : Nat := 2 ^ degree
def multOrder : Nat := fieldOrder - 1
def torusOrder : Nat := q ^ 2 + q + 1
def ell : Nat := 2593
def eta : Nat := 1629469875507523981620540
def epsilon : Nat := 1629469875507523981620541
def beta : Nat := 2293671573472151973449566

def mulAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, a, b, acc =>
      let acc' := if b % 2 = 1 then Nat.xor acc a else acc
      let a2 := Nat.shiftLeft a 1
      let a' := if a2.testBit degree then Nat.xor a2 modulus else a2
      mulAux fuel a' (b / 2) acc'

def mul (a b : Nat) : Nat := mulAux degree a b 0

def powAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, a, e, acc =>
      if e = 0 then acc
      else
        let acc' := if e % 2 = 1 then mul acc a else acc
        powAux fuel (mul a a) (e / 2) acc'

def fpow (a e : Nat) : Nat := powAux (degree + 2) a e 1

def etaTrace27 : Nat :=
  Nat.xor eta (Nat.xor (fpow eta q) (fpow eta (q ^ 2)))

theorem current_prime : Nat.Prime ell := by norm_num [ell]

theorem current_factor : ell ∣ torusOrder := by
  norm_num [ell, torusOrder, q]

def halfCirculant : Nat :=
  (List.range 79).foldl
    (fun acc j => Nat.xor acc (fpow epsilon (2 ^ (j + 1)))) 0

def polyModAux : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | fuel + 1, a, b =>
      if b = 0 ∨ Nat.log2 a < Nat.log2 b then a
      else polyModAux fuel
        (Nat.xor a (Nat.shiftLeft b (Nat.log2 a - Nat.log2 b))) b

def polyMod (a b : Nat) : Nat := polyModAux 200 a b

def polyGcdAux : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | fuel + 1, a, b =>
      if b = 0 then a else polyGcdAux fuel b (polyMod a b)

def polyGcd (a b : Nat) : Nat := polyGcdAux 200 a b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem singer_equation : fpow eta (q + 1) = Nat.xor eta 1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem torus_norm : fpow eta torusOrder = 1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem current_failure : fpow eta (torusOrder / ell) = 1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem translate_identities :
    epsilon = Nat.xor eta 1 ∧ epsilon = fpow eta (q + 1) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem beta_eta_identity : mul (fpow beta (q - 1)) eta = 1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem beta_normalized_identity :
    beta = Nat.xor 1 (fpow eta (q / 2 + 1)) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem half_circulant_identity : halfCirculant = beta := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem full_kummer_kernel :
    fpow eta (multOrder / ell) = 1 ∧
    fpow epsilon (multOrder / ell) = 1 ∧
    fpow beta (multOrder / ell) = 1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem selected_trace_ancestry_breaks :
    Nat.xor (fpow etaTrace27 (2 ^ 9 + 1))
      (Nat.xor etaTrace27 1) ≠ 0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rabin_certificate :
    fpow 2 (2 ^ 81) = 2 ∧
    polyGcd modulus (Nat.xor (fpow 2 (2 ^ 27)) 2) = 1 := by decide

end CubicTwoNormalCounterexample

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

section FermatAdditiveEdgeArithmetic

/-- A proper odd factorization of `Q^2+1` cannot have the factor parameter
`L = (ell-1)/R` divisible by `Q+1`.  This is the arithmetic step which keeps
the exact semiconjugacy exponent off the preceding Fibonacci zero period. -/
theorem fermat_factor_parameter_not_dvd_half_period
    (Q R L ell d : Nat)
    (hQ : 2 ≤ Q) (hR : 2 ≤ R) (hL : 0 < L)
    (hd : 1 < d) (hdodd : d % 2 = 1)
    (hell : ell = 1 + R * L)
    (hfactor : ell * d = Q ^ 2 + 1) :
    ¬Q + 1 ∣ L := by
  intro hdiv
  obtain ⟨u, rfl⟩ := hdiv
  have hu : 0 < u := by
    by_contra hu0
    have : u = 0 := Nat.eq_zero_of_not_pos hu0
    simp [this] at hL
  have hq : Q ^ 2 + 1 = (Q + 1) * (Q - 1) + 2 := by
    calc
      Q ^ 2 + 1 = ((Q - 1) + 1) ^ 2 + 1 := by
        rw [show Q - 1 + 1 = Q by omega]
      _ = (((Q - 1) + 1) + 1) * (Q - 1) + 2 := by ring
      _ = (Q + 1) * (Q - 1) + 2 := by
        rw [show Q - 1 + 1 = Q by omega]
  have heq :
      d + (Q + 1) * (R * u * d) = (Q + 1) * (Q - 1) + 2 := by
    rw [← hq, ← hfactor, hell]
    ring
  have heq' : (d - 2) + (Q + 1) * (R * u * d) =
      (Q + 1) * (Q - 1) := by omega
  have hmulLeft : Q + 1 ∣ (Q + 1) * (R * u * d) := dvd_mul_right _ _
  have hmulRight : Q + 1 ∣ (Q + 1) * (Q - 1) := dvd_mul_right _ _
  have hsum : Q + 1 ∣ (d - 2) + (Q + 1) * (R * u * d) := by
    rw [heq']
    exact hmulRight
  have hdvd : Q + 1 ∣ d - 2 :=
    (Nat.dvd_add_iff_right hmulLeft).mpr (by
      simpa [add_comm] using hsum)
  obtain ⟨t, htEq⟩ := hdvd
  have hddecomp : 2 + (Q + 1) * t = d := by omega
  have ht : 0 < t := by
    by_contra ht0
    have : t = 0 := Nat.eq_zero_of_not_pos ht0
    have hd2 : d = 2 := by simpa [this] using hddecomp.symm
    omega
  have hellLower : 2 * Q + 3 ≤ ell := by
    rw [hell]
    nlinarith
  have hdLower : Q + 3 ≤ d := by
    nlinarith
  have hprodLower : (2 * Q + 3) * (Q + 3) ≤ ell * d :=
    Nat.mul_le_mul hellLower hdLower
  rw [hfactor] at hprodLower
  nlinarith

/-- If `Q+1` divides `D` and `ell*K + L = H*D`, the preceding lemma
immediately excludes divisibility of the extracted exponent `K` by `Q+1`. -/
theorem fermat_exact_exponent_not_dvd_half_period
    (Q R L ell d D H K : Nat)
    (hQ : 2 ≤ Q) (hR : 2 ≤ R) (hL : 0 < L)
    (hd : 1 < d) (hdodd : d % 2 = 1)
    (hell : ell = 1 + R * L)
    (hfactor : ell * d = Q ^ 2 + 1)
    (hD : Q + 1 ∣ D)
    (hK : ell * K + L = H * D) :
    ¬Q + 1 ∣ K := by
  intro hperiod
  apply fermat_factor_parameter_not_dvd_half_period
    Q R L ell d hQ hR hL hd hdodd hell hfactor
  have hleft : Q + 1 ∣ ell * K := dvd_mul_of_dvd_right hperiod ell
  have hright : Q + 1 ∣ H * D := dvd_mul_of_dvd_right hD H
  rw [← hK] at hright
  exact (Nat.dvd_add_iff_right hleft).mpr hright

end FermatAdditiveEdgeArithmetic

section FermatAdditiveEdge

variable {R : Type*} [CommRing R] [CharP R 2]

omit [CharP R 2] in
/-- Powers along one selected Conway quadratic edge have Fibonacci
coordinates over the preceding field.  The Conway relation is written as
`x^2 = A*x + A^3`. -/
theorem conwayQuadratic_pow_fib_coords
    (x A : R) (hx : x ^ 2 = A * x + A ^ 3) (r : Nat) :
    x ^ (r + 1) =
      A ^ (r + 2) * fibPolyValue A r +
        x * A ^ r * fibPolyValue A (r + 1) := by
  induction r with
  | zero => simp [fibPolyValue]
  | succ r ih =>
      rw [show r + 1 + 1 = (r + 1) + 1 by omega, pow_succ, ih]
      rw [show fibPolyValue A (r + 2) =
          fibPolyValue A (r + 1) + A * fibPolyValue A r by
            simp only [fibPolyValue]]
      calc
        (A ^ (r + 2) * fibPolyValue A r +
              x * A ^ r * fibPolyValue A (r + 1)) * x =
            A ^ (r + 2) * fibPolyValue A r * x +
              x ^ 2 * A ^ r * fibPolyValue A (r + 1) := by ring
        _ = A ^ (r + 1 + 2) * fibPolyValue A (r + 1) +
              x * A ^ (r + 1) *
                (fibPolyValue A (r + 1) + A * fibPolyValue A r) := by
            rw [hx]
            simp only [pow_succ]
            ring

/-- The additive trace of the same power across the Conway quadratic is an
explicit lower Fibonacci value. -/
theorem conwayQuadratic_pow_additive_trace
    (x A : R) (hx : x ^ 2 = A * x + A ^ 3) (r : Nat) :
    x ^ (r + 1) + (x + A) ^ (r + 1) =
      A ^ (r + 1) * fibPolyValue A (r + 1) := by
  have hx' : (x + A) ^ 2 = A * (x + A) + A ^ 3 := by
    rw [add_sq, hx]
    have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
    simp only [htwo, zero_mul, add_zero]
    ring
  rw [conwayQuadratic_pow_fib_coords x A hx r]
  rw [conwayQuadratic_pow_fib_coords (x + A) A hx' r]
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  linear_combination htwo *
    (A ^ (r + 2) * fibPolyValue A r) + htwo *
    (x * A ^ r * fibPolyValue A (r + 1))

/-- Hence equality with a selected Fibonacci value transports its additive
trace to the explicit lower Fibonacci coordinate.  In the finite-field
application the second equality is the preceding-field Frobenius conjugate
of the first. -/
theorem fermat_exact_monomial_additive_trace
    (x A : R) (g r : Nat)
    (hx : x ^ 2 = A * x + A ^ 3)
    (h : fibPolyValue x g = x ^ (r + 1))
    (hconj : fibPolyValue (x + A) g = (x + A) ^ (r + 1)) :
    fibPolyValue x g + fibPolyValue (x + A) g =
      A ^ (r + 1) * fibPolyValue A (r + 1) := by
  rw [h, hconj]
  exact conwayQuadratic_pow_additive_trace x A hx r

/-- The exact lower trace is nonzero whenever the preceding parameter and
the corresponding lower Fibonacci value are nonzero. -/
theorem fermat_exact_monomial_additive_trace_ne_zero
    {K : Type*} [Field K] [CharP K 2]
    (x A : K) (g r : Nat)
    (hx : x ^ 2 = A * x + A ^ 3)
    (h : fibPolyValue x g = x ^ (r + 1))
    (hconj : fibPolyValue (x + A) g = (x + A) ^ (r + 1))
    (hA : A ≠ 0) (hSK : fibPolyValue A (r + 1) ≠ 0) :
    fibPolyValue x g + fibPolyValue (x + A) g ≠ 0 := by
  rw [fermat_exact_monomial_additive_trace x A g r hx h hconj]
  exact mul_ne_zero (pow_ne_zero _ hA) hSK

end FermatAdditiveEdge


section FermatQuotientWindowFibonacciCore

variable {R : Type*} [CommRing R]

/-- Every positive-index Fibonacci value has constant coefficient one:
abstractly it is `1 + x*z`. -/
theorem fibPolyValue_eq_one_add_mul (x : R) (r : Nat) :
    ∃ z : R, fibPolyValue x (r + 1) = 1 + x * z := by
  induction r with
  | zero =>
      refine ⟨0, ?_⟩
      simp [fibPolyValue]
  | succ r ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨z + fibPolyValue x r, ?_⟩
      rw [show r + 1 + 1 = r + 2 by omega]
      rw [show fibPolyValue x (r + 2) =
          fibPolyValue x (r + 1) + x * fibPolyValue x r by
            simp only [fibPolyValue]]
      rw [hz]
      ring

variable [CharP R 2]

/-- If `x^(2^t)=0`, the exact trailing-zero formula loses all dependence on
the positive cofactor index. -/
theorem fibPolyValue_trailing_zero_of_nilpotent
    (x : R) (t r : Nat) (hx : x ^ (2 ^ t) = 0) :
    fibPolyValue x ((2 ^ t) * (r + 1) + 1) =
      1 + partialFrobeniusTrace x t := by
  obtain ⟨u, hu⟩ := fibPolyValue_eq_one_add_mul x r
  obtain ⟨v, hv⟩ := fibPolyValue_eq_one_add_mul x (r + 1)
  have hpow (z : R) : (1 + x * z) ^ (2 ^ t) = 1 := by
    rw [add_pow_expChar_pow, one_pow, mul_pow, hx]
    simp
  rw [fibPolyValue_trailing_zero_compression, hu, hv, hpow, hpow]
  ring

end FermatQuotientWindowFibonacciCore

section FermatShiftBlockCore

variable {R : Type*} [CommRing R]

/-- Once a Fibonacci value vanishes, every shift by its index scales the
sequence by the single following value. -/
theorem fibPolyValue_add_zero_block
    (a : R) (d r : Nat) (hd : fibPolyValue a d = 0) :
    fibPolyValue a (d + r) =
      fibPolyValue a (d + 1) * fibPolyValue a r := by
  induction r using Nat.twoStepInduction with
  | zero => simp [fibPolyValue, hd]
  | one => simp [fibPolyValue]
  | more r hr hr1 =>
      rw [show d + (r + 2) = (d + r) + 2 by omega]
      simp only [fibPolyValue]
      rw [show d + r + 1 = d + (r + 1) by omega]
      rw [hr, hr1]
      ring

/-- All blocks after a Fibonacci zero are scalar copies of the initial
block. -/
theorem fibPolyValue_mul_add_zero_block
    (a : R) (d k r : Nat) (hd : fibPolyValue a d = 0) :
    fibPolyValue a (k * d + r) =
      (fibPolyValue a (d + 1)) ^ k * fibPolyValue a r := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul]
      rw [show k * d + d + r = d + (k * d + r) by omega]
      rw [fibPolyValue_add_zero_block a d (k * d + r) hd]
      rw [ih, pow_succ]
      ring

/-- Cassini's identity for the characteristic-two Fibonacci recurrence. -/
theorem fibPolyValue_cassini
    {R : Type*} [CommRing R] [CharP R 2] (a : R) (d : Nat) :
    (fibPolyValue a (d + 1)) ^ 2 +
        fibPolyValue a d * fibPolyValue a (d + 2) = a ^ d := by
  induction d with
  | zero => simp [fibPolyValue]
  | succ d ih =>
      have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
      have h3 : (3 : R) = 1 := by
        calc
          (3 : R) = 2 + 1 := by norm_num
          _ = 1 := by rw [h2, zero_add]
      calc
        (fibPolyValue a (d + 1 + 1)) ^ 2 +
            fibPolyValue a (d + 1) * fibPolyValue a (d + 1 + 2) =
            a * ((fibPolyValue a (d + 1)) ^ 2 +
              fibPolyValue a d * fibPolyValue a (d + 2)) := by
                rw [show d + 1 + 1 = d + 2 by omega]
                rw [show d + 1 + 2 = (d + 2) + 1 by omega]
                rw [show fibPolyValue a ((d + 2) + 1) =
                    fibPolyValue a (d + 2) +
                      a * fibPolyValue a (d + 1) by
                        simp only [fibPolyValue]]
                rw [show fibPolyValue a (d + 2) =
                    fibPolyValue a (d + 1) +
                      a * fibPolyValue a d by
                        simp only [fibPolyValue]]
                ring_nf
                simp [h2, h3]
        _ = a * a ^ d := by rw [ih]
        _ = a ^ (d + 1) := by rw [pow_succ]; ring

/-- Cassini at a Fibonacci zero: the square of the block scalar is the
corresponding power of the recurrence parameter. -/
theorem fibPolyValue_succ_sq_of_zero
    {R : Type*} [CommRing R] [CharP R 2]
    (a : R) (d : Nat) (hd : fibPolyValue a d = 0) :
    (fibPolyValue a (d + 1)) ^ 2 = a ^ d := by
  simpa [hd] using fibPolyValue_cassini a d

/-- At an index dividing a power-of-two-plus-one index, a zero forces the
next Fibonacci value to be the canonical power root of the parameter. -/
theorem fibPolyValue_zero_block_scalar_root
    {R : Type*} [CommRing R] [CharP R 2]
    (a : R) (m d ell : Nat)
    (hindex : ell * d = 2 ^ m + 1)
    (hd : fibPolyValue a d = 0) :
    (fibPolyValue a (d + 1)) ^ ell = a := by
  have hblock := fibPolyValue_mul_add_zero_block a d ell 1 hd
  simp only [fibPolyValue, mul_one] at hblock
  have hzero := fibPolyValue_mul_add_zero_block a d ell 0 hd
  simp only [fibPolyValue, mul_zero] at hzero
  have hzeroTop : fibPolyValue a (2 ^ m + 1) = 0 := by
    rw [← hindex]
    exact hzero
  have hpow : fibPolyValue a (2 ^ m) = 1 := by
    simpa [fibPolyValue] using fibPolyValue_pow_two_mul a m 1
  calc
    (fibPolyValue a (d + 1)) ^ ell =
        fibPolyValue a (ell * d + 1) := hblock.symm
    _ = fibPolyValue a (2 ^ m + 2) := by rw [hindex]
    _ = fibPolyValue a (2 ^ m + 1) +
          a * fibPolyValue a (2 ^ m) := by
            simp only [fibPolyValue]
    _ = a := by rw [hzeroTop, hpow, zero_add, mul_one]

end FermatShiftBlockCore

section FermatSemiconjugacySaturation

variable {K : Type*} [Field K] [CharP K 2]

/-- The denominator-cleared power-of-two semiconjugacy equation is exactly
the product of the two adjacent Fibonacci values.  Thus its two branches are
the original zero index and the adjacent zero index; it is not a third
selected condition. -/
theorem fibPolyValue_semiconjugacy_factor
    (a : K) (t g : Nat) (hg : 0 < g) :
    a ^ ((2 ^ t) * g) +
        a * (fibPolyValue a g) ^ (2 * (2 ^ t)) =
      a * fibPolyValue a ((2 ^ t) * g - 1) *
        fibPolyValue a ((2 ^ t) * g + 1) := by
  let n := (2 ^ t) * g
  have hn : 0 < n := mul_pos (pow_pos (by omega) _) hg
  have hc := fibPolyValue_cassini a (n - 1)
  have hn0 : n - 1 + 1 = n := by omega
  have hn1 : n - 1 + 2 = n + 1 := by omega
  rw [hn0, hn1] at hc
  have hpow : fibPolyValue a n = (fibPolyValue a g) ^ (2 ^ t) := by
    simpa [n] using fibPolyValue_pow_two_mul a t g
  rw [hpow] at hc
  have hsq : ((fibPolyValue a g) ^ (2 ^ t)) ^ 2 =
      (fibPolyValue a g) ^ (2 * (2 ^ t)) := by
    calc
      ((fibPolyValue a g) ^ (2 ^ t)) ^ 2 =
          (fibPolyValue a g) ^ ((2 ^ t) * 2) := by rw [pow_mul]
      _ = (fibPolyValue a g) ^ (2 * (2 ^ t)) := by
        congr 1
        omega
  rw [hsq] at hc
  have ha : a * a ^ (n - 1) = a ^ n := by
    rw [← pow_succ']
    congr 1
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  calc
    a ^ ((2 ^ t) * g) +
        a * (fibPolyValue a g) ^ (2 * (2 ^ t)) =
      a * (a ^ (n - 1) +
        (fibPolyValue a g) ^ (2 * (2 ^ t))) := by
          rw [show (2 ^ t) * g = n by rfl, ← ha]
          ring
    _ = a * (fibPolyValue a (n - 1) *
        fibPolyValue a (n + 1)) := by
          rw [← hc]
          ring_nf
          simp [h2]
    _ = a * fibPolyValue a ((2 ^ t) * g - 1) *
        fibPolyValue a ((2 ^ t) * g + 1) := by
          simp only [n]
          ring

/-- Over a field and away from zero, the semiconjugacy equation therefore
has exactly the two adjacent Fibonacci branches. -/
theorem fibPolyValue_semiconjugacy_eq_iff
    (a : K) (t g : Nat) (ha : a ≠ 0) (hg : 0 < g) :
    a * (fibPolyValue a g) ^ (2 * (2 ^ t)) =
        a ^ ((2 ^ t) * g) ↔
      fibPolyValue a ((2 ^ t) * g - 1) = 0 ∨
        fibPolyValue a ((2 ^ t) * g + 1) = 0 := by
  have hf := fibPolyValue_semiconjugacy_factor a t g hg
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  constructor
  · intro h
    have hz : a ^ ((2 ^ t) * g) +
        a * (fibPolyValue a g) ^ (2 * (2 ^ t)) = 0 := by
      rw [h]
      ring_nf
      simp [h2]
    rw [hf] at hz
    rcases mul_eq_zero.mp hz with hap | hright
    · rcases mul_eq_zero.mp hap with ha0 | hleft
      · exact (ha ha0).elim
      · exact Or.inl hleft
    · exact Or.inr hright
  · intro hz
    have hp : a * fibPolyValue a ((2 ^ t) * g - 1) *
        fibPolyValue a ((2 ^ t) * g + 1) = 0 := by
      rcases hz with hleft | hright
      · simp [hleft]
      · simp [hright]
    rw [← hf] at hp
    apply eq_of_sub_eq_zero
    rw [sub_eq_add_neg]
    have hneg : -(a ^ ((2 ^ t) * g)) = a ^ ((2 ^ t) * g) := by
      apply eq_of_sub_eq_zero
      ring_nf
      simp [h2]
    rw [hneg]
    simpa [add_comm] using hp

omit [CharP K 2] in
/-- In the odd branch `g = 2e+1`, normalizing by `a^e` turns the
pointwise semiconjugacy relation into a pure Frobenius coboundary. -/
theorem fermat_semiconjugacy_normalized_coboundary
    (a S : K) (R e : Nat) (ha : a ≠ 0)
    (h : a * S ^ (2 * R) = a ^ (R * (2 * e + 1))) :
    a * (S / a ^ e) ^ (2 * R) = a ^ R := by
  have hae : a ^ e ≠ 0 := pow_ne_zero _ ha
  rw [div_pow]
  field_simp
  have hexp : e * (2 * R) + R = R * (2 * e + 1) := by ring
  calc
    a * S ^ (2 * R) = a ^ (R * (2 * e + 1)) := h
    _ = a ^ (e * (2 * R) + R) := by rw [hexp]
    _ = (a ^ e) ^ (2 * R) * a ^ R := by rw [pow_add, pow_mul]

omit [CharP K 2] in
/-- A non-fixed Frobenius coordinate makes the normalized remainder
nontrivial.  This is the exact pointwise nonvanishing left after the cyclic
norm has collapsed to one. -/
theorem fermat_normalized_coboundary_ne_one
    (a z : K) (R : Nat)
    (h : a * z ^ (2 * R) = a ^ R) (hmove : a ^ R ≠ a) :
    z ≠ 1 := by
  intro hz
  rw [hz, one_pow, mul_one] at h
  exact hmove h.symm

/-- Powering by `2 * 2^t` is an iterated Frobenius and is injective in
every reduced characteristic-two ring. -/
theorem pow_two_mul_injective
    {R : Type*} [CommRing R] [IsReduced R] [CharP R 2]
    (t : Nat) : Function.Injective (fun x : R => x ^ (2 * (2 ^ t))) := by
  intro x y hxy
  apply iterateFrobenius_inj R 2 (t + 1)
  simpa [iterateFrobenius_def, pow_succ, Nat.mul_comm] using hxy

/-- Once the arithmetic exponent congruence has identified the two
Frobenius powers, the selected Fibonacci value is the corresponding
monomial itself, not merely an element with the same norm. -/
theorem fermat_selected_monomial_of_power_eq
    (a S : K) (t k : Nat)
    (h : S ^ (2 * (2 ^ t)) = (a ^ k) ^ (2 * (2 ^ t))) :
    S = a ^ k := by
  exact pow_two_mul_injective t h

omit [CharP K 2] in
/-- Abstract order formula behind the relative-torus strengthening: when
the even Frobenius exponent is coprime to the order of `z`, the normalized
remainder has exactly the order of `a^(R-1)`. -/
theorem fermat_normalized_coboundary_order
    {G : Type*} [Group G] [Finite G] (a z : G) (R : Nat)
    (hz : z ^ (2 * R) = a ^ (R - 1))
    (hcop : (orderOf z).Coprime (2 * R)) :
    orderOf z = orderOf a / Nat.gcd (orderOf a) (R - 1) := by
  have hord := congrArg orderOf hz
  rw [orderOf_pow, orderOf_pow, hcop.gcd_eq_one, Nat.div_one] at hord
  exact hord

end FermatSemiconjugacySaturation

section FermatComplementaryCofactorCore

/-- The Fibonacci polynomial of index `2^(t+1)+1` has derivative one in
characteristic two. -/
theorem fibPolyDerivativeValue_pow_two_succ_add_one
    {R : Type*} [CommRing R] [CharP R 2] (a : R) (t : Nat) :
    fibPolyDerivativeValue a (2 ^ (t + 1) + 1) = 1 := by
  rw [show 2 ^ (t + 1) + 1 = 2 * (2 ^ t) + 1 by
    rw [pow_succ]
    omega]
  rw [(fibPolyDerivativeValue_double a (2 ^ t)).2]
  have hpow : fibPolyValue a (2 ^ t) =
      (fibPolyValue a 1) ^ (2 ^ t) := by
    simpa using fibPolyValue_pow_two_mul a t 1
  rw [hpow]
  simp [fibPolyValue]

/-- The differentiated factorization identifies the inverse on whichever
factor does not vanish. -/
theorem factor_cofactor_branch_inverse
    {K : Type*} [Field K] (s q ds dq : K)
    (hprod : s * q = 0) (hderiv : ds * q + s * dq = 1) :
    (s = 0 ∧ ds * q = 1) ∨ (q = 0 ∧ s * dq = 1) := by
  rcases mul_eq_zero.mp hprod with hs | hq
  · left
    refine ⟨hs, ?_⟩
    simpa [hs] using hderiv
  · right
    refine ⟨hq, ?_⟩
    simpa [hq] using hderiv

/-- A zero product together with differentiated Bézout value one forces
exactly one factor to vanish. -/
theorem exactly_one_zero_of_product_and_derivative
    {K : Type*} [Field K] (s q ds dq : K)
    (hprod : s * q = 0) (hderiv : ds * q + s * dq = 1) :
    (s = 0 ∧ q ≠ 0) ∨ (s ≠ 0 ∧ q = 0) := by
  rcases factor_cofactor_branch_inverse s q ds dq hprod hderiv with
      ⟨hs, hunit⟩ | ⟨hq, hunit⟩
  · left
    refine ⟨hs, ?_⟩
    exact right_ne_zero_of_mul_eq_one hunit
  · right
    refine ⟨?_, hq⟩
    exact left_ne_zero_of_mul_eq_one hunit

/-- Over the two-element field, a one-hot pair has sum one. -/
theorem complementary_bits_sum_one
    (r t : ZMod 2)
    (h : (r = 0 ∧ t ≠ 0) ∨ (r ≠ 0 ∧ t = 0)) :
    r + t = 1 := by
  rcases h with ⟨hr, ht⟩ | ⟨hr, ht⟩
  · subst r
    have ht1 : t = 1 := by
      fin_cases t
      · exact (ht rfl).elim
      · rfl
    simp [ht1]
  · subst t
    have hr1 : r = 1 := by
      fin_cases r
      · exact (hr rfl).elim
      · rfl
    simp [hr1]

end FermatComplementaryCofactorCore

section FermatSelectedCrtProjectorCore

/-- A product-zero factorization with differentiated Bezout value one gives
the two complementary CRT idempotents. -/
theorem complementary_crt_idempotents
    {R : Type*} [CommRing R] (s q ds dq : R)
    (hprod : s * q = 0) (hbez : ds * q + s * dq = 1) :
    let failure := ds * q
    let success := s * dq
    failure + success = 1 ∧
      failure * success = 0 ∧
      failure ^ 2 = failure ∧
      success ^ 2 = success := by
  dsimp
  have horth : (ds * q) * (s * dq) = 0 := by
    calc
      (ds * q) * (s * dq) = (ds * dq) * (s * q) := by ring
      _ = 0 := by rw [hprod, mul_zero]
  refine ⟨hbez, horth, ?_, ?_⟩
  · calc
      (ds * q) ^ 2 = (ds * q) * ((ds * q) + (s * dq)) := by
        rw [mul_add, horth, add_zero, pow_two]
      _ = ds * q := by rw [hbez, mul_one]
  · have horth' : (s * dq) * (ds * q) = 0 := by
      rw [mul_comm]
      exact horth
    calc
      (s * dq) ^ 2 = (s * dq) * ((ds * q) + (s * dq)) := by
        rw [mul_add, horth', zero_add, pow_two]
      _ = s * dq := by rw [hbez, mul_one]

/-- On a field quotient, the failure projector is one exactly on the
factor-zero branch and the success projector is one exactly on the
cofactor-zero branch. -/
theorem selected_crt_projector_branches
    {K : Type*} [Field K] (s q ds dq : K)
    (hprod : s * q = 0) (hbez : ds * q + s * dq = 1) :
    (s = 0 ∧ ds * q = 1 ∧ s * dq = 0) ∨
      (q = 0 ∧ ds * q = 0 ∧ s * dq = 1) := by
  rcases mul_eq_zero.mp hprod with hs | hq
  · left
    refine ⟨hs, ?_, by simp [hs]⟩
    simpa [hs] using hbez
  · right
    refine ⟨hq, by simp [hq], ?_⟩
    simpa [hq] using hbez

/-- Every Bezout certificate for the same product-zero factorization gives
the same two support projectors. -/
theorem bezout_support_projectors_unique
    {R : Type*} [CommRing R] (s q ds dq u v : R)
    (hprod : s * q = 0)
    (hderiv : ds * q + s * dq = 1)
    (hbez : u * s + v * q = 1) :
    v * q = ds * q ∧ u * s = s * dq := by
  constructor
  · calc
      v * q = (v * q) * (ds * q + s * dq) := by
        rw [hderiv, mul_one]
      _ = (ds * q) * (u * s + v * q) := by
        rw [mul_add, mul_add]
        rw [show (v * q) * (s * dq) = 0 by
          calc
            (v * q) * (s * dq) = (v * dq) * (s * q) := by ring
            _ = 0 := by rw [hprod, mul_zero]]
        rw [show (ds * q) * (u * s) = 0 by
          calc
            (ds * q) * (u * s) = (ds * u) * (s * q) := by ring
            _ = 0 := by rw [hprod, mul_zero]]
        ring
      _ = ds * q := by rw [hbez, mul_one]
  · calc
      u * s = (u * s) * (ds * q + s * dq) := by
        rw [hderiv, mul_one]
      _ = (s * dq) * (u * s + v * q) := by
        rw [mul_add, mul_add]
        rw [show (u * s) * (ds * q) = 0 by
          calc
            (u * s) * (ds * q) = (u * ds) * (s * q) := by ring
            _ = 0 := by rw [hprod, mul_zero]]
        rw [show (s * dq) * (v * q) = 0 by
          calc
            (s * dq) * (v * q) = (dq * v) * (s * q) := by ring
            _ = 0 := by rw [hprod, mul_zero]]
        ring
      _ = s * dq := by rw [hbez, mul_one]

/-- A quadratic trace kills either selected scalar bit in characteristic
two. -/
theorem quadratic_trace_of_scalar_bit
    {R : Type*} [CommRing R] [CharP R 2] (e : R) :
    e + e = 0 := by
  have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
  calc
    e + e = 2 * e := by ring
    _ = 0 := by rw [htwo, zero_mul]

/-- A quadratic norm returns an idempotent scalar unchanged. -/
theorem quadratic_norm_of_idempotent
    {R : Type*} [CommRing R] (e : R) (he : e ^ 2 = e) :
    e * e = e := by
  simpa [pow_two] using he

end FermatSelectedCrtProjectorCore

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

section CubicChosenRootAncestry

variable {G : Type*} [CommMonoid G]

/-- Every monomial in a chosen Kummer root has its exact residue-weight
normal form. -/
theorem cubic_kummer_monomial_normal_form
    (t eta : G) (ell a m : Nat) (ht : t ^ ell = eta) :
    t ^ (ell * a + m) = eta ^ a * t ^ m := by
  rw [pow_add, pow_mul, ht]

/-- A product of arbitrary Frobenius conjugates of the chosen root reduces
to one Kummer weight; all selected lower ancestry may be absorbed into its
coefficient. -/
theorem cubic_kummer_frobenius_word_normal_form
    (t eta : G) (ell a m : Nat)
    (s : Finset Nat) (w : Nat → Nat)
    (ht : t ^ ell = eta)
    (hweight : ∑ i ∈ s, w i * 2 ^ i = ell * a + m) :
    (∏ i ∈ s, (t ^ (2 ^ i)) ^ (w i)) = eta ^ a * t ^ m := by
  rw [weighted_frobenius_word, hweight]
  exact cubic_kummer_monomial_normal_form t eta ell a m ht

variable {H : Type*} [CommGroup H]

/-- A coefficient-fixed pure weight has precisely the corresponding power
of the original Kummer monodromy under full Frobenius. -/
theorem cubic_kummer_weight_monodromy
    (t omega coeff : H) (m N : Nat)
    (ht : t ^ N = omega * t) (hcoeff : coeff ^ N = coeff) :
    (t ^ m * coeff) ^ N = omega ^ m * (t ^ m * coeff) := by
  exact dk_eigenweight_power_monodromy t omega coeff m N ht hcoeff

end CubicChosenRootAncestry

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

section DQuarticCoset

variable {R : Type*} [CommRing R] [CharP R 2]

private theorem f4_coset_product (y omega : R)
    (homega : omega ^ 2 + omega + 1 = 0) :
    y * (y + 1) * (y + omega) * (y + omega ^ 2) = y ^ 4 + y := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have h4 : (4 : R) = 0 := by
    calc (4 : R) = 2 + 2 := by norm_num
         _ = 0 := by rw [h2]; simp
  have hsum : omega ^ 2 + omega = 1 := by
    linear_combination homega - h2
  have hprod : omega * omega ^ 2 = 1 := by
    linear_combination
      (omega + 1) * homega - (omega ^ 2 + omega + 1) * h2
  calc
    y * (y + 1) * (y + omega) * (y + omega ^ 2) =
        (y ^ 2 + y) * ((y + omega) * (y + omega ^ 2)) := by ring
    _ = (y ^ 2 + y) * (y ^ 2 + y + 1) := by
      rw [show (y + omega) * (y + omega ^ 2) = y ^ 2 + y + 1 by
        calc
          (y + omega) * (y + omega ^ 2) =
              y ^ 2 + y * (omega ^ 2 + omega) + omega * omega ^ 2 := by ring
          _ = y ^ 2 + y + 1 := by rw [hsum, hprod]; ring]
    _ = y ^ 4 + y := by ring_nf; simp [h2]

/-- The four-point F4 coset containing the conductor-five translate compresses
to the primitive quartic evaluated at the selected cyclotomic coordinate. -/
theorem exceptional_F4_coset_product (x u omega : R)
    (homega : omega ^ 2 + omega + 1 = 0)
    (hu : u ^ 2 + u = omega) :
    (x + u) * (x + u + 1) * (x + u + omega) *
        (x + u + omega ^ 2) = x ^ 4 + x + 1 := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have hu_sq : u ^ 4 + u ^ 2 = omega ^ 2 := by
    have := congrArg (fun z : R => z ^ 2) hu
    ring_nf at this ⊢
    simpa [h2] using this
  have hu4 : u ^ 4 + u = 1 := by
    linear_combination hu_sq + hu + homega - (u ^ 2 + 1) * h2
  calc
    (x + u) * (x + u + 1) * (x + u + omega) *
        (x + u + omega ^ 2) = (x + u) ^ 4 + (x + u) :=
      f4_coset_product (x + u) omega homega
    _ = x ^ 4 + x + (u ^ 4 + u) := by
      have h4 : (4 : R) = 0 := by
        calc (4 : R) = 2 + 2 := by norm_num
             _ = 0 := by rw [h2]; simp
      have h6 : (6 : R) = 0 := by
        calc (6 : R) = 3 * 2 := by norm_num
             _ = 0 := by rw [h2]; simp
      ring_nf
      simp [h4, h6]
    _ = x ^ 4 + x + 1 := by rw [hu4]

/-- The quartic representative is the product of the two oriented corrected
norms obtained from the two nontrivial F4 constants. -/
theorem exceptional_correctedNorm_pair (x omega : R)
    (homega : omega ^ 2 + omega + 1 = 0) :
    (x ^ 2 + x + omega) * (x ^ 2 + x + omega ^ 2) =
      x ^ 4 + x + 1 := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have hsum : omega ^ 2 + omega = 1 := by
    linear_combination homega - h2
  have hprod : omega * omega ^ 2 = 1 := by
    linear_combination
      (omega + 1) * homega - (omega ^ 2 + omega + 1) * h2
  calc
    (x ^ 2 + x + omega) * (x ^ 2 + x + omega ^ 2) =
        (x ^ 2 + x) ^ 2 + (x ^ 2 + x) * (omega ^ 2 + omega) +
          omega * omega ^ 2 := by ring
    _ = (x ^ 2 + x) ^ 2 + (x ^ 2 + x) + 1 := by
      rw [hsum, hprod, mul_one]
    _ = x ^ 4 + x + 1 := by ring_nf; simp [h2]

/-- The sparse quartic representative has a symmetric trace-one cubic over
the preceding cubic field. -/
theorem exceptional_quartic_orbit_cubic (T D omega : R)
    (homega : omega ^ 2 + omega + 1 = 0) :
    (T + (1 + D)) * (T + (1 + omega * D)) *
        (T + (1 + omega ^ 2 * D)) =
      T ^ 3 + T ^ 2 + T + (1 + D ^ 3) := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have h3 : (3 : R) = 1 := by
    calc (3 : R) = 2 + 1 := by norm_num
         _ = 1 := by rw [h2]; simp
  have hsum : omega ^ 2 + omega = 1 := by
    linear_combination homega - h2
  have hprod : omega * omega ^ 2 = 1 := by
    linear_combination
      (omega + 1) * homega - (omega ^ 2 + omega + 1) * h2
  have hzero1 : 1 + omega + omega ^ 2 = 0 := by
    linear_combination homega
  have hzero2 : omega + omega ^ 2 + omega * omega ^ 2 = 0 := by
    linear_combination hsum + hprod + h2
  have horbit (Y : R) :
      (Y + D) * (Y + omega * D) * (Y + omega ^ 2 * D) = Y ^ 3 + D ^ 3 := by
    calc
      (Y + D) * (Y + omega * D) * (Y + omega ^ 2 * D) =
          Y ^ 3 + (1 + omega + omega ^ 2) * D * Y ^ 2 +
            (omega + omega ^ 2 + omega * omega ^ 2) * D ^ 2 * Y +
              omega * omega ^ 2 * D ^ 3 := by ring
      _ = Y ^ 3 + D ^ 3 := by rw [hzero1, hzero2, hprod]; ring
  calc
    (T + (1 + D)) * (T + (1 + omega * D)) *
        (T + (1 + omega ^ 2 * D)) = (T + 1) ^ 3 + D ^ 3 := by
      simpa [add_assoc, add_left_comm, add_comm] using horbit (T + 1)
    _ = T ^ 3 + T ^ 2 + T + (1 + D ^ 3) := by
      ring_nf
      simp [h3]

/-- Substituting `D=x*(a+1)` and `x^3=a` identifies the cubic norm with
the fifth cyclotomic polynomial at the lower selected root. -/
theorem exceptional_quartic_norm (x a : R) (hx : x ^ 3 = a) :
    1 + (x ^ 4 + x) ^ 3 = a ^ 4 + a ^ 3 + a ^ 2 + a + 1 := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have h3 : (3 : R) = 1 := by
    calc (3 : R) = 2 + 1 := by norm_num
         _ = 1 := by rw [h2]; simp
  calc
    1 + (x ^ 4 + x) ^ 3 = 1 + (x * (x ^ 3 + 1)) ^ 3 := by ring
    _ = 1 + (x * (a + 1)) ^ 3 := by rw [hx]
    _ = a ^ 4 + a ^ 3 + a ^ 2 + a + 1 := by
      rw [mul_pow, hx]
      ring_nf
      simp [h3]

end DQuarticCoset

section AdjacentHilbert

variable {K : Type*} [Field K] [CharP K 2]

/-- The characteristic-two Möbius coordinate sends an ordered pair `(r,s)`
to adjacent values with the displayed common denominator. -/
theorem adjacent_mobius_add_one (r s : K) (hrs : r + s ≠ 0) :
    (1 + s) / (r + s) + 1 = (1 + r) / (r + s) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  field_simp [hrs]
  linear_combination h2 * s

/-- Cross-multiplication recovers the Möbius coordinate from its two
Frobenius-ratio equations. -/
theorem adjacent_mobius_of_ratio_equation
    (x r s : K) (hrs : r + s ≠ 0)
    (h : s * (x + 1) = r * x + 1) :
    x = (1 + s) / (r + s) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  apply (eq_div_iff hrs).2
  linear_combination h + h2 * (r * x - s)

omit [CharP K 2] in
/-- The inverse-unit identities behind the Hilbert-pair parametrization. -/
theorem adjacent_mobius_inverse_ratio
    (r s : K) (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r + s ≠ 0) :
    (1 + s⁻¹) / (r⁻¹ + s⁻¹) = r * ((1 + s) / (r + s)) := by
  have hsr : s + r ≠ 0 := by simpa [add_comm] using hrs
  field_simp [hr, hs, hrs, hsr]
  ring

/-- A nonzero ratio and the corresponding quadratic norm determine an
element uniquely in characteristic two. -/
theorem adjacent_ratio_norm_rigid
    (x y r n : K) (hr : r ≠ 0)
    (hx : r * x ^ 2 = n) (hy : r * y ^ 2 = n) :
    x = y := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hsq : x ^ 2 = y ^ 2 := by
    apply (mul_left_cancel₀ hr)
    rw [hx, hy]
  have hzero : (x + y) ^ 2 = 0 := by
    rw [add_sq, h2]
    simpa [hsq] using (CharTwo.add_self_eq_zero (y ^ 2))
  have hxy : x + y = 0 := by
    exact mul_self_eq_zero.mp (by simpa [pow_two] using hzero)
  have hneg : -y = y := by
    exact (eq_neg_of_add_eq_zero_left (CharTwo.add_self_eq_zero y)).symm
  calc
    x = -y := eq_neg_of_add_eq_zero_left hxy
    _ = y := hneg

omit [CharP K 2] in
/-- The selected quartic's inverse-Frobenius orientation is `zeta^-5`. -/
theorem adjacent_quartic_inverse_orientation
    (zeta : K) (hzeta : zeta ≠ 0) :
    zeta⁻¹ ^ 4 + zeta⁻¹ = zeta⁻¹ ^ 5 * (zeta ^ 4 + zeta) := by
  field_simp [hzeta]
  ring

/-- The elementary adjacent-power count is exactly the maximal Fermat-curve
count once `q+1 = ell*m`.  Integers avoid truncated-subtraction noise. -/
theorem adjacent_count_is_maximal_fermat
    (q ell m : ℤ) (h : q + 1 = ell * m) :
    ell ^ 2 * (q - 2 + (m - 1) * (m - 2)) + 3 * ell =
      q ^ 2 + 1 + (ell - 1) * (ell - 2) * q := by
  have hq : q = ell * m - 1 := by linarith
  rw [hq]
  ring

end AdjacentHilbert

section GlobalSplitRayReduction

/-! Algebraic cores for the paper's global split-ray reduction.  The
number-field height bound, local conductor calculation, and Artin reciprocity
specialization remain paper-level. -/

variable {G : Type*} [CommGroup G]

/-- Descent through an extension of degree `ell - 1`: the norm equation for an
`ell`-th root produces an `ell`-th root already in the base group. -/
theorem ell_minus_one_power_descent
    (u normWitness : G) (ell : ℕ) (hell : 0 < ell)
    (hNorm : normWitness ^ ell = u ^ (ell - 1)) :
    (u * normWitness⁻¹) ^ ell = u := by
  calc
    (u * normWitness⁻¹) ^ ell = u ^ ell * (normWitness ^ ell)⁻¹ := by
      rw [mul_pow, inv_pow]
    _ = u ^ ell * (u ^ (ell - 1))⁻¹ := by rw [hNorm]
    _ = u := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hell)
      simp [pow_succ]

/-- A rank-one conductor orbit vanishes everywhere exactly when its marked
coefficient vanishes, provided every orbit multiplier is nonzero. -/
theorem marked_zero_iff_orbit_zero
    {F I : Type*} [Field F] [Nonempty I]
    (L : F) (lambda : I → F) (hlambda : ∀ i, lambda i ≠ 0) :
    L = 0 ↔ ∀ i, lambda i * L = 0 := by
  constructor
  · rintro rfl i
    simp
  · intro h
    by_contra hL
    let i := Classical.choice (inferInstance : Nonempty I)
    exact (mul_ne_zero (hlambda i) hL) (h i)

/-- A weight-one character on a transitive orbit is trivial on the entire
orbit as soon as it is trivial at the selected base point. -/
theorem weight_one_orbit_trivial_of_base
    {A X : Type*} (act : A → X → X) (weight : A → Nat)
    (chi : X → G) (base : X)
    (horbit : ∀ x : X, ∃ a : A, x = act a base)
    (hequiv : ∀ (a : A) (x : X), chi (act a x) = (chi x) ^ weight a)
    (hbase : chi base = 1) :
    ∀ x, chi x = 1 := by
  intro x
  obtain ⟨a, rfl⟩ := horbit x
  rw [hequiv, hbase, one_pow]

/-- Numerical core of the exceptional height contradiction:
`19 * log 5 / 12 > log 2`. -/
theorem exceptional_abelian_height_gap : 2 ^ 12 < 5 ^ 19 := by
  norm_num

/-- Numerical core of the ordinary height contradiction:
`11 * log 5 / 12 > 2 * log 2`. -/
theorem ordinary_abelian_height_gap : 2 ^ 24 < 5 ^ 11 := by
  norm_num

/-- Numerical core of the direct cubic circular-unit height contradiction. -/
theorem cubic_abelian_height_gap : 2 ^ 16 < 5 ^ 7 := by
  norm_num

/-- Imposing `g` scalar local conditions leaves a kernel of codimension at
most `g`.  This is the linear-algebra core of the split-ray rank obstruction. -/
theorem finrank_sub_le_finrank_ker
    {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (f : V →ₗ[F] W) :
    Module.finrank F V - Module.finrank F W ≤
      Module.finrank F (LinearMap.ker f) := by
  have hrank := f.finrank_range_add_finrank_ker
  have hrange : Module.finrank F (LinearMap.range f) ≤ Module.finrank F W :=
    (LinearMap.range f).finrank_le
  omega

/-- On a one-dimensional selected eigenspace, the marked vector and the
selected local functional are the two separate nonvanishing inputs. -/
theorem marked_evaluation_ne_zero
    {F : Type*} [Field F] (marked evaluation : F) :
    marked * evaluation ≠ 0 ↔ marked ≠ 0 ∧ evaluation ≠ 0 := by
  exact mul_ne_zero_iff

/-! The complete cubic conjugate lattice produces a multikummer, rather than
merely rank-one, split-ray obstruction.  The number-field unit lattice,
circular-unit index theorem, Kummer theory, and Artin reciprocity remain
paper-level; these lemmas check the exact linear-algebra accounting. -/

/-- If the relation space of a linear realization has dimension at most
`r`, its realized image has codimension at most `r`. -/
theorem finrank_sub_relation_bound_le_image
    {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (f : V →ₗ[F] W) (r : Nat)
    (hker : Module.finrank F (LinearMap.ker f) ≤ r) :
    Module.finrank F V - r ≤ Module.finrank F (LinearMap.range f) := by
  have hrank := f.finrank_range_add_finrank_ker
  omega

/-- A surjection onto an elementary Kummer quotient transfers its dimension
as a lower bound on the split ray space. -/
theorem finrank_le_of_surjective_linearMap
    {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (f : V →ₗ[F] W) (hsurj : Function.Surjective f) :
    Module.finrank F W ≤ Module.finrank F V := by
  exact LinearMap.finrank_le_finrank_of_surjective hsurj

/-- Combining a bounded power-relation kernel with a split-ray surjection
gives the complete conjugate-lattice rank bound in one step. -/
theorem multikummer_split_ray_rank_bound
    {F L R Q : Type*} [Field F]
    [AddCommGroup L] [Module F L]
    [AddCommGroup R] [Module F R]
    [AddCommGroup Q] [Module F Q]
    [FiniteDimensional F L] [FiniteDimensional F R] [FiniteDimensional F Q]
    (kummer : L →ₗ[F] R) (artin : Q →ₗ[F] R) (r : Nat)
    (hker : Module.finrank F (LinearMap.ker kummer) ≤ r)
    (hartin : Function.Surjective artin) :
    Module.finrank F L - r ≤ Module.finrank F Q := by
  calc
    Module.finrank F L - r ≤ Module.finrank F (LinearMap.range kummer) :=
      finrank_sub_relation_bound_le_image kummer r hker
    _ ≤ Module.finrank F R := (LinearMap.range kummer).finrank_le
    _ ≤ Module.finrank F Q := finrank_le_of_surjective_linearMap artin hartin

/-! The complete cubic multikummer extension also has an exact Frobenius-fibre
boundary.  The number-field Kummer extension, semidirect Galois group, and
Chebotarev theorem remain paper-level.  These lemmas check that the `n`-th
power of a lift of the diagonal base Frobenius sees exactly its coordinate on
the one fixed character line. -/

/-- Additive part of the `n`-th power in a semidirect product. -/
def cubicOrbitSum {F A : Type*} [Field F]
    [AddCommGroup A] [Module F A]
    (T : A →ₗ[F] A) (n : Nat) (x : A) : A :=
  ∑ i ∈ Finset.range n, (T ^ i) x

/-- A covariant projection fixed by `T` is fixed by every iterate. -/
theorem cubic_project_iterate
    {F A S : Type*} [Field F]
    [AddCommGroup A] [Module F A]
    [AddCommGroup S] [Module F S]
    (T : A →ₗ[F] A) (project : A →ₗ[F] S)
    (hproject : ∀ x, project (T x) = project x) :
    ∀ (i : Nat) (x : A), project ((T ^ i) x) = project x := by
  intro i
  induction i with
  | zero =>
      intro x
      simp
  | succ i ih =>
      intro x
      rw [pow_succ]
      simp only [Module.End.mul_apply]
      rw [ih, hproject]

/-- The orbit sum projects to `n` copies of the selected coordinate. -/
theorem cubic_project_orbitSum
    {F A S : Type*} [Field F]
    [AddCommGroup A] [Module F A]
    [AddCommGroup S] [Module F S]
    (T : A →ₗ[F] A) (project : A →ₗ[F] S)
    (hproject : ∀ x, project (T x) = project x)
    (n : Nat) (x : A) :
    project (cubicOrbitSum T n x) = n • project x := by
  simp only [cubicOrbitSum, map_sum,
    cubic_project_iterate T project hproject]
  simp

/-- If the orbit norm kills the kernel of the selected projection, it
vanishes exactly when the selected coordinate does. -/
theorem cubic_orbitSum_eq_zero_iff_selected_eq_zero
    {F A S : Type*} [Field F]
    [AddCommGroup A] [Module F A]
    [AddCommGroup S] [Module F S]
    (T : A →ₗ[F] A) (project : A →ₗ[F] S)
    (hproject : ∀ x, project (T x) = project x)
    (n : Nat) (hn : (n : F) ≠ 0)
    (hkill : ∀ x, project x = 0 → cubicOrbitSum T n x = 0)
    (x : A) :
    cubicOrbitSum T n x = 0 ↔ project x = 0 := by
  constructor
  · intro horbit
    have hprojzero : n • project x = 0 := by
      rw [← cubic_project_orbitSum T project hproject n x, horbit]
      simp
    have hscalar : (n : F) • project x = 0 := by
      simpa only [Nat.cast_smul_eq_nsmul F] using hprojzero
    exact (smul_eq_zero.mp hscalar).resolve_left hn
  · exact hkill x

/-- On an eigenline, the orbit sum is its geometric sum times the vector. -/
theorem cubic_orbitSum_eigenvector
    {F A : Type*} [Field F] [AddCommGroup A] [Module F A]
    (T : A →ₗ[F] A) (q : F) (n : Nat) (x : A)
    (heigen : T x = q • x) :
    cubicOrbitSum T n x = (∑ i ∈ Finset.range n, q ^ i) • x := by
  have hiter : ∀ i : Nat, (T ^ i) x = q ^ i • x := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        rw [pow_succ]
        simp only [Module.End.mul_apply, heigen, map_smul, ih]
        simp [pow_succ, smul_smul, mul_comm]
  simp only [cubicOrbitSum, hiter, Finset.sum_smul]

/-- Every nontrivial `n`-th-root eigenline is killed by the orbit norm. -/
theorem cubic_orbitSum_eigenvector_eq_zero
    {F A : Type*} [Field F] [AddCommGroup A] [Module F A]
    (T : A →ₗ[F] A) (q : F) (n : Nat) (x : A)
    (heigen : T x = q • x) (hqpow : q ^ n = 1) (hq : q ≠ 1) :
    cubicOrbitSum T n x = 0 := by
  rw [cubic_orbitSum_eigenvector T q n x heigen]
  have hgeom : (∑ i ∈ Finset.range n, q ^ i) = 0 := by
    have hmul := geom_sum_mul q n
    rw [hqpow] at hmul
    exact (mul_eq_zero.mp (by simpa using hmul)).resolve_right
      (sub_ne_zero.mpr hq)
  simp [hgeom]

/-- Iterating a covariance relation along the decomposition orbit. -/
theorem covariant_orbit_iterate
    {G F : Type*} [CommGroup G] [Field F]
    (L : G → F) (t : G) (q : F)
    (hcov : ∀ a, L (t * a) = q * L a) :
    ∀ (n : ℕ) (a : G), L (t ^ n * a) = q ^ n * L a := by
  intro n
  induction n with
  | zero =>
      intro a
      simp
  | succ n ih =>
      intro a
      calc
        L (t ^ (n + 1) * a) = L (t * (t ^ n * a)) := by
          congr 1
          simp [pow_succ, mul_comm, mul_left_comm]
        _ = q * L (t ^ n * a) := hcov _
        _ = q * (q ^ n * L a) := by rw [ih]
        _ = q ^ (n + 1) * L a := by
          simp [pow_succ, mul_comm, mul_left_comm]

/-- If an even marked functional meets complex conjugation in the
decomposition orbit with the wrong eigenvalue, it vanishes identically. -/
theorem even_covariant_collision_forces_zero
    {G F : Type*} [CommGroup G] [Field F]
    (L : G → F) (t j : G) (q : F) (n : ℕ)
    (hcov : ∀ a, L (t * a) = q * L a)
    (heven : ∀ a, L (j * a) = L a)
    (hcollision : t ^ n = j)
    (hscalar : q ^ n ≠ 1) :
    ∀ a, L a = 0 := by
  intro a
  have horbit := covariant_orbit_iterate L t q hcov n a
  rw [hcollision, heven] at horbit
  have hmul : (q ^ n - 1) * L a = 0 := by
    calc
      (q ^ n - 1) * L a = q ^ n * L a - L a := by ring
      _ = 0 := by rw [← horbit]; simp
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hscalar)

/-- A marked decomposition-prime coordinate can detect only the eigenspace
whose eigenvalue matches arithmetic Frobenius. -/
theorem marked_eigenvalue_must_match
    {F : Type*} [Field F] (marked chi omega : F)
    (hcompat : chi * marked = omega * marked)
    (hmarked : marked ≠ 0) :
    chi = omega := by
  exact mul_right_cancel₀ hmarked hcompat

end GlobalSplitRayReduction

section FermatAdditiveCrossLevel

/-- If an odd modulus sees the product congruent to two, the congruences
for the two adjacent factors have the same common-divisor content. -/
theorem cross_gcd_of_product_mod_two
    (m ell d : Nat) (hodd : m.Coprime 2)
    (hell : 1 ≤ ell) (hd : 2 ≤ d)
    (htop : ell * d ≡ 2 [MOD m]) :
    m.gcd (ell - 1) = m.gcd (d - 2) := by
  apply Nat.dvd_antisymm
  · let k := m.gcd (ell - 1)
    have hkm : k ∣ m := Nat.gcd_dvd_left m (ell - 1)
    have hkell : k ∣ ell - 1 := Nat.gcd_dvd_right m (ell - 1)
    have htopk : ell * d ≡ 2 [MOD k] := htop.of_dvd hkm
    have hellk : ell ≡ 1 [MOD k] :=
      ((Nat.modEq_iff_dvd' hell).mpr hkell).symm
    have hprodk : ell * d ≡ d [MOD k] := by
      simpa using hellk.mul (Nat.ModEq.refl d)
    have hdk : d ≡ 2 [MOD k] := hprodk.symm.trans htopk
    exact Nat.dvd_gcd hkm ((Nat.modEq_iff_dvd' hd).mp hdk.symm)
  · let k := m.gcd (d - 2)
    have hkm : k ∣ m := Nat.gcd_dvd_left m (d - 2)
    have hkd : k ∣ d - 2 := Nat.gcd_dvd_right m (d - 2)
    have htopk : ell * d ≡ 2 [MOD k] := htop.of_dvd hkm
    have hdk : d ≡ 2 [MOD k] :=
      ((Nat.modEq_iff_dvd' hd).mpr hkd).symm
    have htwok : ell * 2 ≡ 1 * 2 [MOD k] := by
      simpa using ((Nat.ModEq.refl ell).mul hdk).symm.trans htopk
    have hkodd : k.Coprime 2 := Nat.Coprime.of_dvd_left hkm hodd
    have hellk : ell ≡ 1 [MOD k] :=
      Nat.ModEq.cancel_right_of_coprime hkodd.gcd_eq_one htwok
    exact Nat.dvd_gcd hkm ((Nat.modEq_iff_dvd' hell).mp hellk.symm)

/-- Adjacent Fermat factors satisfy the exact cross-level gcd identity. -/
theorem fermat_adjacent_factor_cross_gcd
    (Q ell d : Nat) (hQ : 1 ≤ Q) (hQeven : Even Q)
    (hell : 1 ≤ ell) (hd : 2 ≤ d)
    (hprod : ell * d = Q ^ 2 + 1) :
    (Q + 1).gcd (ell - 1) = (Q + 1).gcd (d - 2) := by
  have hdecomp : Q ^ 2 + 1 = (Q + 1) * (Q - 1) + 2 := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hQ
    norm_num [pow_two]
    ring
  have htop : ell * d ≡ 2 [MOD Q + 1] := by
    rw [hprod, hdecomp]
    exact Nat.ModEq.modulus_mul_add
  have hodd : (Q + 1).Coprime 2 := by
    obtain ⟨r, hr⟩ := hQeven
    subst Q
    simp [Nat.Coprime]
  exact cross_gcd_of_product_mod_two (Q + 1) ell d hodd hell hd htop

/-- The exact exponent relation determines the lower period loss. -/
theorem exact_exponent_gcd_period
    (m ell K L H D : Nat)
    (hcop : m.Coprime ell) (hmD : m ∣ D)
    (hrel : ell * K + L = H * D) :
    m.gcd K = m.gcd L := by
  have hsum_m : m ∣ ell * K + L := by
    rw [hrel]
    exact dvd_mul_of_dvd_right hmD H
  apply Nat.dvd_antisymm
  · let k := m.gcd K
    have hkm : k ∣ m := Nat.gcd_dvd_left m K
    have hkK : k ∣ K := Nat.gcd_dvd_right m K
    have hsum_k : k ∣ ell * K + L := dvd_trans hkm hsum_m
    have hprod : k ∣ ell * K := dvd_mul_of_dvd_right hkK ell
    exact Nat.dvd_gcd hkm ((Nat.dvd_add_iff_right hprod).mpr hsum_k)
  · let k := m.gcd L
    have hkm : k ∣ m := Nat.gcd_dvd_left m L
    have hkL : k ∣ L := Nat.gcd_dvd_right m L
    have hsum_k : k ∣ ell * K + L := dvd_trans hkm hsum_m
    have hprod : k ∣ ell * K := (Nat.dvd_add_iff_left hkL).mpr hsum_k
    have hkcop : k.Coprime ell := Nat.Coprime.of_dvd_left hkm hcop
    exact Nat.dvd_gcd hkm (hkcop.dvd_of_dvd_mul_left hprod)

/-- Removing a factor coprime to the modulus does not change the gcd of the
remaining factor. -/
theorem gcd_mul_of_right_coprime
    (m R L : Nat) (hcop : m.Coprime R) :
    m.gcd (R * L) = m.gcd L := by
  apply Nat.dvd_antisymm
  · let k := m.gcd (R * L)
    have hkm : k ∣ m := Nat.gcd_dvd_left m (R * L)
    have hkRL : k ∣ R * L := Nat.gcd_dvd_right m (R * L)
    have hkcop : k.Coprime R := Nat.Coprime.of_dvd_left hkm hcop
    exact Nat.dvd_gcd hkm (hkcop.dvd_of_dvd_mul_left hkRL)
  · simpa [Nat.mul_comm] using Nat.gcd_dvd_gcd_mul_right_right m L R

/-- Full cross-level identity for the exponent loss exposed by the first
additive edge. -/
theorem fermat_AE4_cross_level_gcd
    (Q ell d R L K H D : Nat)
    (hQ : 1 ≤ Q) (hQeven : Even Q)
    (hell : 1 ≤ ell) (hd : 2 ≤ d)
    (hprod : ell * d = Q ^ 2 + 1)
    (hellDef : ell = 1 + R * L)
    (hcopR : (Q + 1).Coprime R)
    (hcopEll : (Q + 1).Coprime ell)
    (hmD : Q + 1 ∣ D)
    (hrel : ell * K + L = H * D) :
    (Q + 1).gcd K = (Q + 1).gcd (ell - 1) ∧
      (Q + 1).gcd K = (Q + 1).gcd (d - 2) := by
  have hKL := exact_exponent_gcd_period
    (Q + 1) ell K L H D hcopEll hmD hrel
  have hellSub : ell - 1 = R * L := by omega
  have hLEll : (Q + 1).gcd L = (Q + 1).gcd (ell - 1) := by
    rw [hellSub, gcd_mul_of_right_coprime (Q + 1) R L hcopR]
  have hcross := fermat_adjacent_factor_cross_gcd
    Q ell d hQ hQeven hell hd hprod
  exact ⟨hKL.trans hLEll, hKL.trans (hLEll.trans hcross)⟩

end FermatAdditiveCrossLevel

section FermatAE4SizeObstruction

/-- Two proper factors with the same exact two-adic offset force that offset
below the square root of the current Fermat power. -/
theorem fermat_common_offset_lt_sqrt
    (Q ell d R L g : Nat)
    (hR : 0 < R) (hL : 0 < L) (hg : 0 < g)
    (hell : ell = 1 + R * L) (hd : d = 1 + R * g)
    (hprod : ell * d = Q ^ 2 + 1) :
    R < Q := by
  have hleL : R + 1 ≤ ell := by rw [hell]; nlinarith
  have hleD : R + 1 ≤ d := by rw [hd]; nlinarith
  have hlower : (R + 1) ^ 2 ≤ ell * d := by
    simpa [pow_two] using Nat.mul_le_mul hleL hleD
  rw [hprod] at hlower
  nlinarith

/-- The exact offset congruence couples the two complementary lower
quotients by a divisibility relation. -/
theorem fermat_cross_exact_offset_sum_dvd
    (Q d R g u h e t : Nat)
    (hd : h * t + 2 = d)
    (hdR : d = 1 + R * g)
    (hQR : Q = R * u)
    (hfactor : h * e = Q + 1)
    (hcop : R.Coprime h) :
    R ∣ t + e := by
  have heq : h * (t + e) = R * (g + u) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  have hdiv : R ∣ h * (t + e) := by
    rw [heq]
    exact dvd_mul_right R (g + u)
  exact hcop.dvd_of_dvd_mul_left hdiv

/-- The two current factors and the preceding factorization force the exact
offset product `R*t` below the square of the complementary lower order. -/
theorem fermat_cross_exact_offset_product
    (Q ell d R h e t : Nat)
    (hR : 0 < R) (hh : 0 < h)
    (hell : R * h + 1 ≤ ell)
    (hd : h * t + 2 = d)
    (hprod : ell * d = Q ^ 2 + 1)
    (hfactor : h * e = Q + 1) :
    R * t < e ^ 2 := by
  have hdlower : h * t + 2 ≤ d := hd.le
  have hlower : (R * h + 1) * (h * t + 2) ≤ ell * d :=
    Nat.mul_le_mul hell hdlower
  have hcross : h ^ 2 * (R * t) < (R * h + 1) * (h * t + 2) := by
    have hpos : 0 < 2 * R * h := by positivity
    nlinarith
  have hQupper : Q ^ 2 + 1 ≤ h ^ 2 * e ^ 2 := by
    calc
      Q ^ 2 + 1 ≤ (Q + 1) ^ 2 := by nlinarith
      _ = h ^ 2 * e ^ 2 := by rw [← hfactor]; ring
  have hscaled : h ^ 2 * (R * t) < h ^ 2 * e ^ 2 := by
    calc
      h ^ 2 * (R * t) < (R * h + 1) * (h * t + 2) := hcross
      _ ≤ ell * d := hlower
      _ = Q ^ 2 + 1 := hprod
      _ ≤ h ^ 2 * e ^ 2 := hQupper
  rw [show h ^ 2 * e ^ 2 = h ^ 2 * (e ^ 2) by ring] at hscaled
  exact (Nat.mul_lt_mul_left (Nat.pow_pos hh)).mp hscaled

/-- The product and divisibility constraints prevent the common two-adic
offset from being twice the surviving complementary lower order. -/
theorem fermat_cross_exact_offset_lt_twice_complement
    (R e t : Nat) (he : 0 < e)
    (hdiv : R ∣ t + e) (hproduct : R * t < e ^ 2) :
    R < 2 * e := by
  have hsumPos : 0 < t + e := by omega
  have hRle : R ≤ t + e := Nat.le_of_dvd hsumPos hdiv
  by_contra hnot
  have htwo : 2 * e ≤ R := Nat.le_of_not_gt hnot
  have het : e ≤ t := by omega
  have hmulOne : R * e ≤ R * t := Nat.mul_le_mul_left R het
  have hmulTwo : e ^ 2 < R * e := by
    have : e < R := by omega
    nlinarith
  omega

end FermatAE4SizeObstruction

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
