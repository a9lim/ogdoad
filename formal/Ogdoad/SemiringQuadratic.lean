import Mathlib

/-!
# Quadratic pairs over cancellative semirings

This file formalizes the finite-polynomial proxy used for the closed
finite-CNF Hessenberg semiring in `writeups/semiring_stability.tex`.

For `MvPolynomial (Fin d) Nat`, Lean proves internally:

* every companion over an additively cancellative semiring is balanced on the
  diagonal;
* the coefficient semiring has no half of one, no nonzero self-double, and no
  scalar unit other than one;
* every invertible square matrix is a permutation matrix;
* regularity of a pair's companion adjoint gives such an invertible Gram
  matrix; and
* symmetry and balance turn its permutation into an explicit disjoint union
  of hyperbolic planes, with even rank and zero quadratic basis labels.

The named endpoint `hessenbergPolynomial_regular_isometric_hyperbolic` starts
from the actual adjoint-bijectivity definition of regularity and constructs a
linear isometry of quadratic pairs with the canonical hyperbolic sum.  The
identification of this polynomial semiring with the ordinal fragment below
`omega^(omega^d)` remains the stated CNF bridge.

The file also checks the exact group-theoretic `ZMod 2` endpoint of the
supertropical ring-image argument and exposes Mathlib's classical
diagonalization theorem.  The concrete supertropical scalar extension remains
outside the kernel.
-/

namespace Ogdoad.SemiringQuadratic

/-- A semiring has no half of one when no element doubles to `1`.  This is the
small fragment of characteristic-zero arithmetic needed to exclude a fixed
point in a balanced permutation Gram matrix. -/
class NoHalfOne (R : Type*) [AddMonoidWithOne R] : Prop where
  two_mul_ne_one : ∀ a : R, a + a ≠ 1

/-- Doubling detects zero.  This holds in every zerosumfree cancellative
semiring, in particular in the Hessenberg fragments. -/
class NoSelfSumZero (R : Type*) [AddMonoid R] : Prop where
  eq_zero_of_add_self_eq_zero : ∀ a : R, a + a = 0 → a = 0

/-- A quadratic pair in the semiring sense.  The companion is packaged as a
bilinear map; unlike over a ring, it is part of the input. -/
structure QuadraticPair (R V : Type*) [CommSemiring R] [AddCommMonoid V]
    [Module R V] where
  q : V → R
  b : V →ₗ[R] V →ₗ[R] R
  map_smul : ∀ (a : R) (x : V), q (a • x) = a ^ 2 * q x
  polar : ∀ x y : V, q (x + y) = q x + q y + b x y
  symmetric : ∀ x y : V, b x y = b y x

/-- An isometry preserves both the quadratic function and its specified
companion. -/
structure QuadraticPair.Isometry
    {R V W : Type*} [CommSemiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    (Q₁ : QuadraticPair R V) (Q₂ : QuadraticPair R W) where
  toLinearEquiv : V ≃ₗ[R] W
  map_q : ∀ x, Q₂.q (toLinearEquiv x) = Q₁.q x
  map_b : ∀ x y, Q₂.b (toLinearEquiv x) (toLinearEquiv y) = Q₁.b x y

/-- A standard coordinate vector, written without choosing a module basis. -/
def basisVector {R I : Type*} [Zero R] [One R] [DecidableEq I]
    (i : I) : I → R :=
  fun j => if j = i then 1 else 0

theorem basisVector_eq_single {R I : Type*} [Zero R] [One R]
    [DecidableEq I] (i : I) : basisVector (R := R) i = Pi.single i 1 := by
  ext j
  by_cases h : i = j
  · subst j
    simp [basisVector]
  · simp [basisVector, Ne.symm h]

/-- Quadratic labels and companion Gram coefficients on a finite standard
basis determine the entire quadratic pair.  This is the formal coordinate
expansion theorem used to interpret `CoefficientIsometry` as genuine pair
data rather than a lossy invariant. -/
theorem quadraticPair_coefficients_determine
    {R I : Type*} [CommSemiring R] [Fintype I] [DecidableEq I]
    (Q₁ Q₂ : QuadraticPair R (I → R))
    (hq : ∀ i, Q₁.q (basisVector i) = Q₂.q (basisVector i))
    (hg : ∀ i j,
      Q₁.b (basisVector i) (basisVector j) =
        Q₂.b (basisVector i) (basisVector j)) :
    Q₁.q = Q₂.q ∧ Q₁.b = Q₂.b := by
  have hb : Q₁.b = Q₂.b := by
    apply (LinearMap.toMatrix₂' R).injective
    ext i j
    simp only [LinearMap.toMatrix₂'_apply]
    simpa only [← basisVector_eq_single] using hg i j
  refine ⟨?_, hb⟩
  funext x
  have hzero (Q : QuadraticPair R (I → R)) : Q.q 0 = 0 := by
    have h := Q.map_smul 0 (0 : I → R)
    simpa using h
  have hs : ∀ s : Finset I,
      Q₁.q (∑ i ∈ s, x i • basisVector i) =
        Q₂.q (∑ i ∈ s, x i • basisVector i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp [hzero]
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        rw [Q₁.polar, Q₂.polar, Q₁.map_smul, Q₂.map_smul,
          hq a, hb, ih]
  have hx : (∑ i : I, x i • basisVector i) = x := by
    ext j
    simp [basisVector]
  rw [← hx]
  exact hs Finset.univ

section Balance

variable {R V : Type*} [CommSemiring R] [IsCancelAdd R]
  [AddCommMonoid V] [Module R V]

/-- Over an additively cancellative semiring, a quadratic form has at most one
companion. -/
theorem companion_unique (q : V → R)
    (b c : V →ₗ[R] V →ₗ[R] R)
    (hb : ∀ x y, q (x + y) = q x + q y + b x y)
    (hc : ∀ x y, q (x + y) = q x + q y + c x y) : b = c := by
  ext x y
  have h : q x + q y + b x y = q x + q y + c x y :=
    (hb x y).symm.trans (hc x y)
  exact add_left_cancel h

/-- Additive cancellation forces the diagonal of every companion to be
`2 q(x)`. -/
theorem companion_diagonal (Q : QuadraticPair R V) (x : V) :
    Q.b x x = Q.q x + Q.q x := by
  have hscale : Q.q (x + x) =
      (Q.q x + Q.q x) + (Q.q x + Q.q x) := by
    calc
      Q.q (x + x) = Q.q ((1 + 1 : R) • x) := by simp [add_smul]
      _ = (1 + 1 : R) ^ 2 * Q.q x := Q.map_smul (1 + 1) x
      _ = (Q.q x + Q.q x) + (Q.q x + Q.q x) := by ring
  have hpolar := Q.polar x x
  have hcancel :
      (Q.q x + Q.q x) + (Q.q x + Q.q x) =
        (Q.q x + Q.q x) + Q.b x x := by
    exact hscale.symm.trans hpolar
  exact (add_left_cancel hcancel).symm

/-- Hence a companion diagonal entry can never be `1` in a semiring with no
half of one. -/
theorem companion_diagonal_ne_one [NoHalfOne R]
    (Q : QuadraticPair R V) (x : V) : Q.b x x ≠ 1 := by
  rw [companion_diagonal Q x]
  exact NoHalfOne.two_mul_ne_one (Q.q x)

end Balance

section PolynomialFragment

/-- The finite-CNF Hessenberg fragment below `omega^(omega^d)` is represented
by `MvPolynomial (Fin d) Nat`: exponent natural sum is addition of exponent
vectors, and natural product is polynomial multiplication.  Applying the
constant-coefficient map shows directly that this semiring has no half of
one. -/
instance mvPolynomialNoHalfOne (sigma : Type*) :
    NoHalfOne (MvPolynomial sigma Nat) where
  two_mul_ne_one p hp := by
    have hconstant := congrArg MvPolynomial.constantCoeff hp
    simp only [map_add, map_one] at hconstant
    omega

instance mvPolynomialNoSelfSumZero (sigma : Type*) :
    NoSelfSumZero (MvPolynomial sigma Nat) where
  eq_zero_of_add_self_eq_zero p hp := by
    ext m
    have hcoeff := congrArg (MvPolynomial.coeff m) hp
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_zero] at hcoeff
    rw [MvPolynomial.coeff_zero]
    omega

/-- The polynomial Hessenberg model has only the trivial scalar unit.  We map
coefficients to `Int`, use the reduced-ring unit classification there, and
pull the resulting constant polynomial back coefficientwise. -/
theorem mvPolynomial_isUnit_eq_one (sigma : Type*)
    (p : MvPolynomial sigma Nat) (hp : IsUnit p) : p = 1 := by
  classical
  let f : Nat →+* Int := Nat.castRingHom Int
  have hmap : IsUnit (MvPolynomial.map f p) := hp.map (MvPolynomial.map f)
  obtain ⟨r, _hr, heq⟩ :=
    MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hmap
  have hpC : p = MvPolynomial.C (p.coeff 0) := by
    ext m
    by_cases hm : m = 0
    · subst m
      rw [MvPolynomial.coeff_zero_C]
    · have hc := congrArg (MvPolynomial.coeff m) heq
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C] at hc
      have h0m : (0 : sigma →₀ Nat) ≠ m := Ne.symm hm
      simp [h0m] at hc
      have hz : p.coeff m = 0 := hc
      rw [hz, MvPolynomial.coeff_C]
      simp [h0m]
  have hn : IsUnit (p.coeff 0) := hp.map MvPolynomial.constantCoeff
  have hone : p.coeff 0 = 1 := Nat.isUnit_iff.mp hn
  rw [hpC, hone, map_one]

end PolynomialFragment

section PolynomialMatrices

/-- Evaluation with every variable equal to one sums all coefficients. -/
def mvCoeffSum (sigma : Type*) : MvPolynomial sigma Nat →+* Nat :=
  MvPolynomial.eval fun _ => 1

/-- Because all coefficients are nonnegative, coefficient sum detects the
zero polynomial. -/
theorem mvCoeffSum_eq_zero {sigma : Type*} (p : MvPolynomial sigma Nat)
    (h : mvCoeffSum sigma p = 0) : p = 0 := by
  classical
  rw [mvCoeffSum, MvPolynomial.eval_eq] at h
  ext m
  have hm : p.coeff m = 0 := by
    by_cases hmem : m ∈ p.support
    · simpa using (Finset.sum_eq_zero_iff.mp h) m hmem
    · exact MvPolynomial.notMem_support_iff.mp hmem
  simp [hm]

/-- A finite sum of natural-coefficient multivariate polynomials is one only
when exactly one summand is one and all others vanish. -/
theorem mvPolynomial_fin_sum_eq_one {sigma : Type*} {n : Nat}
    (f : Fin n → MvPolynomial sigma Nat) (h : ∑ i, f i = 1) :
    ∃ k, f k = 1 ∧ ∀ j, j ≠ k → f j = 0 := by
  classical
  let d : Fin n →₀ Nat :=
    Finsupp.equivFunOnFinite.symm (fun i => mvCoeffSum sigma (f i))
  have hsum : ∑ i, mvCoeffSum sigma (f i) = 1 := by
    rw [← map_sum, h, map_one]
  have hd : d.sum (fun _ v => v) = 1 := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa [d] using hsum
  obtain ⟨k, hk⟩ := (Finsupp.sum_eq_one_iff d).mp hd
  have hjzero : ∀ j, j ≠ k → f j = 0 := by
    intro j hj
    apply mvCoeffSum_eq_zero
    have he := DFunLike.congr_fun hk j
    simpa [d, Finsupp.single_apply, hj] using he
  refine ⟨k, ?_, hjzero⟩
  calc
    f k = ∑ j, f j := by
      symm
      apply Finset.sum_eq_single k
      · intro b _ hbk
        exact hjzero b hbk
      · simp
    _ = 1 := h

/-- Coefficient sum likewise detects every zero summand of a finite sum. -/
theorem mvPolynomial_fin_sum_eq_zero {sigma : Type*} {n : Nat}
    (f : Fin n → MvPolynomial sigma Nat) (h : ∑ i, f i = 0) :
    ∀ i, f i = 0 := by
  intro i
  apply mvCoeffSum_eq_zero
  have hsum : ∑ i, mvCoeffSum sigma (f i) = 0 := by
    rw [← map_sum, h, map_zero]
  exact (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)

/-- The unique-base theorem specialized and proved internally for the
polynomial Hessenberg model: a two-sided invertible matrix is a permutation
matrix, because the coefficient semiring is entire and has only unit one. -/
theorem mvPolynomial_inverseMatrix_permutation {sigma : Type*} {n : Nat}
    (A B : Matrix (Fin n) (Fin n) (MvPolynomial sigma Nat))
    (hAB : A * B = 1) (hBA : B * A = 1) :
    ∃ p : Equiv.Perm (Fin n),
      ∀ i j, A i j = if j = p i then 1 else 0 := by
  classical
  have hchoice : ∀ i, ∃ k,
      A i k = 1 ∧ B k i = 1 ∧
        ∀ j, j ≠ k → A i j * B j i = 0 := by
    intro i
    have hdiag : ∑ k, A i k * B k i = 1 := by
      have hentry := congrFun (congrFun hAB i) i
      simpa [Matrix.mul_apply] using hentry
    obtain ⟨k, hkprod, hkzero⟩ :=
      mvPolynomial_fin_sum_eq_one (fun k => A i k * B k i) hdiag
    have hAu : IsUnit (A i k) :=
      IsUnit.of_mul_eq_one (B k i) hkprod
    have hBu : IsUnit (B k i) :=
      IsUnit.of_mul_eq_one (A i k) (by simpa [mul_comm] using hkprod)
    exact ⟨k, mvPolynomial_isUnit_eq_one sigma (A i k) hAu,
      mvPolynomial_isUnit_eq_one sigma (B k i) hBu, hkzero⟩
  let pfun : Fin n → Fin n := fun i => Classical.choose (hchoice i)
  have hAone : ∀ i, A i (pfun i) = 1 :=
    fun i => (Classical.choose_spec (hchoice i)).1
  have hBone : ∀ i, B (pfun i) i = 1 :=
    fun i => (Classical.choose_spec (hchoice i)).2.1
  have hArow : ∀ i j, A i j = if j = pfun i then 1 else 0 := by
    intro i j
    by_cases hj : j = pfun i
    · simp [hj, hAone]
    · have hentry := congrFun (congrFun hBA (pfun i)) j
      have hsum : ∑ k, B (pfun i) k * A k j = 0 := by
        simpa [Matrix.mul_apply, Matrix.one_apply, Ne.symm hj] using hentry
      have hterm := mvPolynomial_fin_sum_eq_zero
        (fun k => B (pfun i) k * A k j) hsum i
      have hz : A i j = 0 := by simpa [hBone i] using hterm
      simp [hj, hz]
  have hinj : Function.Injective pfun := by
    intro i j hij
    by_contra hne
    have hentry := congrFun (congrFun hAB i) j
    have hsum : ∑ k, A i k * B k j = 0 := by
      simpa [Matrix.mul_apply, Matrix.one_apply, hne] using hentry
    have hterm := mvPolynomial_fin_sum_eq_zero
      (fun k => A i k * B k j) hsum (pfun i)
    rw [hAone i, one_mul, hij, hBone j] at hterm
    exact one_ne_zero hterm
  let p : Equiv.Perm (Fin n) := Equiv.ofBijective pfun
    ((Fintype.bijective_iff_injective_and_card pfun).2 ⟨hinj, rfl⟩)
  refine ⟨p, ?_⟩
  intro i j
  exact hArow i j

end PolynomialMatrices

section RegularPermutationGram

variable {R : Type*} [CommSemiring R] [NoHalfOne R]
  [NoSelfSumZero R]
  {n : Nat}

/-- Once the cited unique-base theorem has made a regular adjoint into a
permutation matrix, symmetry and balance force a fixed-point-free involution,
and every basis vector has quadratic value zero. -/
theorem symmetric_balanced_permutationGram
    (q : Fin n → R) (g : Fin n → Fin n → R) (p : Equiv.Perm (Fin n))
    (hgram : ∀ i j, g i j = if j = p i then 1 else 0)
    (hsymmetric : ∀ i j, g i j = g j i)
    (hbalanced : ∀ i, g i i = q i + q i) :
    (∀ i, p i ≠ i) ∧ Function.Involutive p ∧ (∀ i, q i = 0) := by
  have hfixed : ∀ i, p i ≠ i := by
    intro i hpi
    have hdiag_one : g i i = 1 := by simp [hgram, hpi]
    have htwo_one : q i + q i = 1 := by
      rw [← hbalanced i]
      exact hdiag_one
    exact NoHalfOne.two_mul_ne_one (q i) htwo_one
  have hinvolutive : Function.Involutive p := by
    intro i
    have hforward : g i (p i) = 1 := by simp [hgram]
    have hbackward : g (p i) i = 1 := by
      rw [← hsymmetric i (p i)]
      exact hforward
    rw [hgram] at hbackward
    by_contra hne
    have hcond : ¬i = p (p i) := fun h ↦ hne h.symm
    rw [if_neg hcond] at hbackward
    exact NoHalfOne.two_mul_ne_one (0 : R) (by simpa using hbackward)
  have hqzero : ∀ i, q i = 0 := by
    intro i
    have hdiag_zero : g i i = 0 := by
      rw [hgram, if_neg (fun h ↦ hfixed i h.symm)]
    have hdouble_zero : q i + q i = 0 := by
      rw [← hbalanced i]
      exact hdiag_zero
    exact NoSelfSumZero.eq_zero_of_add_self_eq_zero (q i) hdouble_zero
  exact ⟨hfixed, hinvolutive, hqzero⟩

end RegularPermutationGram

section RegularPairPresentation

variable {R : Type*} [CommSemiring R]
  {n : Nat}

/-- The adjoint of the companion, viewed as a linear map into the dual. -/
def QuadraticPair.adjoint (Q : QuadraticPair R (Fin n → R)) :
    (Fin n → R) →ₗ[R] Module.Dual R (Fin n → R) :=
  Q.b

/-- The standard coordinate vector of a finite free semimodule. -/
def coordinateVector (i : Fin n) : Fin n → R :=
  basisVector i

/-- Coordinates on the dual, obtained by evaluating a functional on the
standard basis. -/
def dualCoordinates : Module.Dual R (Fin n → R) →ₗ[R] (Fin n → R) where
  toFun f i := f (coordinateVector i)
  map_add' f g := by ext i; simp
  map_smul' a f := by ext i; simp

/-- Reconstruct a functional from its finite coordinate vector. -/
def fromDualCoordinates : (Fin n → R) →ₗ[R] Module.Dual R (Fin n → R) where
  toFun c :=
    { toFun := fun x => ∑ i, c i * x i
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        simp [Finset.mul_sum, mul_left_comm] }
  map_add' c d := by
    ext x
    simp [Finset.sum_add_distrib, add_mul]
  map_smul' a c := by
    apply LinearMap.ext
    intro x
    change (∑ i, (a * c i) * x i) = a * ∑ i, c i * x i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc]

theorem dualCoordinates_left
    (f : Module.Dual R (Fin n → R)) :
    fromDualCoordinates (dualCoordinates f) = f := by
  apply LinearMap.ext
  intro x
  change (∑ i, f (coordinateVector i) * x i) = f x
  calc
    ∑ i, f (coordinateVector i) * x i =
        ∑ i, x i * f (coordinateVector i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [mul_comm]
    _ = f (∑ i, x i • coordinateVector i) := by simp
    _ = f x := by
      congr 1
      ext j
      simp [coordinateVector, basisVector]

theorem dualCoordinates_right (c : Fin n → R) :
    dualCoordinates (fromDualCoordinates c) = c := by
  ext i
  simp [dualCoordinates, fromDualCoordinates, coordinateVector, basisVector]

/-- Finite free duality in explicit standard coordinates. -/
def dualCoordinatesEquiv :
    Module.Dual R (Fin n → R) ≃ₗ[R] (Fin n → R) where
  __ := dualCoordinates
  invFun := fromDualCoordinates
  left_inv := dualCoordinates_left
  right_inv := dualCoordinates_right

/-- Regularity means that the companion adjoint is bijective. -/
def QuadraticPair.Regular (Q : QuadraticPair R (Fin n → R)) : Prop :=
  Function.Bijective Q.adjoint

/-- The adjoint followed by the explicit dual-coordinate equivalence. -/
def QuadraticPair.adjointCoordinates
    (Q : QuadraticPair R (Fin n → R)) : Module.End R (Fin n → R) :=
  dualCoordinates.comp Q.adjoint

/-- Quadratic labels and Gram coefficients in the standard basis. -/
def QuadraticPair.basisQ (Q : QuadraticPair R (Fin n → R)) (i : Fin n) : R :=
  Q.q (coordinateVector i)

def QuadraticPair.gram (Q : QuadraticPair R (Fin n → R))
    (i j : Fin n) : R :=
  Q.b (coordinateVector i) (coordinateVector j)

/-- The companion Gram matrix in standard coordinates. -/
def QuadraticPair.gramMatrix (Q : QuadraticPair R (Fin n → R)) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => Q.gram i j

/-- Coordinate regularity: the Gram matrix is a unit in the matrix monoid.
For finite free modules this is the matrix form of the companion adjoint being
an isomorphism. -/
def QuadraticPair.MatrixRegular (Q : QuadraticPair R (Fin n → R)) : Prop :=
  IsUnit Q.gramMatrix

/-- Bijectivity of the companion adjoint implies invertibility of its Gram
matrix.  Symmetry identifies the matrix of the coordinate adjoint with the
Gram matrix rather than its transpose. -/
theorem QuadraticPair.matrixRegular_of_regular
    (Q : QuadraticPair R (Fin n → R)) (hreg : Q.Regular) :
    Q.MatrixRegular := by
  have hbij : Function.Bijective Q.adjointCoordinates :=
    dualCoordinatesEquiv.bijective.comp hreg
  have huEnd : IsUnit Q.adjointCoordinates :=
    (Module.End.isUnit_iff Q.adjointCoordinates).2 hbij
  have huMat : IsUnit Q.adjointCoordinates.toMatrix' :=
    LinearMap.isUnit_toMatrix'_iff.mpr huEnd
  have heq : Q.adjointCoordinates.toMatrix' = Q.gramMatrix := by
    ext i j
    simp only [LinearMap.toMatrix'_apply]
    change Q.b (Pi.single j 1) (coordinateVector i) = Q.gram i j
    rw [← basisVector_eq_single]
    exact Q.symmetric (coordinateVector j) (coordinateVector i)
  rwa [heq] at huMat

/-- Intermediate data saying that a regular Gram matrix is a permutation
matrix.  For the polynomial Hessenberg proxy this certificate is constructed
internally by `hessenbergPolynomial_regular_permutationCertificate`. -/
structure RegularPermutationCertificate
    (Q : QuadraticPair R (Fin n → R)) where
  regular : Q.MatrixRegular
  perm : Equiv.Perm (Fin n)
  gram_eq : ∀ i j, Q.gram i j = if j = perm i then 1 else 0

/-- Over the polynomial Hessenberg model, matrix regularity itself produces
the permutation certificate; no unique-base theorem remains as a hypothesis. -/
theorem hessenbergPolynomial_regular_permutationCertificate
    {sigma : Type*}
    (Q : QuadraticPair (MvPolynomial sigma Nat)
      (Fin n → MvPolynomial sigma Nat))
    (hreg : Q.MatrixRegular) :
    Nonempty (RegularPermutationCertificate Q) := by
  classical
  obtain ⟨u, hu⟩ := hreg
  have hreg' : Q.MatrixRegular := ⟨u, hu⟩
  let B : Matrix (Fin n) (Fin n) (MvPolynomial sigma Nat) := ↑(u⁻¹)
  have hAB : Q.gramMatrix * B = 1 := by
    rw [← hu]
    dsimp [B]
    exact Units.mul_inv u
  have hBA : B * Q.gramMatrix = 1 := by
    rw [← hu]
    dsimp [B]
    exact Units.inv_mul u
  obtain ⟨p, hp⟩ :=
    mvPolynomial_inverseMatrix_permutation Q.gramMatrix B hAB hBA
  exact ⟨⟨hreg', p, hp⟩⟩

end RegularPairPresentation

section HyperbolicMatching

open Function

variable {n : Nat}

/-- The order-selected representative of each two-cycle of `p`. -/
def PairRep (p : Equiv.Perm (Fin n)) := {i : Fin n // i < p i}

instance pairRepFinite (p : Equiv.Perm (Fin n)) : Finite (PairRep p) := by
  unfold PairRep
  infer_instance

instance pairRepDecidableEq (p : Equiv.Perm (Fin n)) : DecidableEq (PairRep p) := by
  unfold PairRep
  infer_instance

noncomputable instance pairRepFintype (p : Equiv.Perm (Fin n)) :
    Fintype (PairRep p) := Fintype.ofFinite _

/-- The two coordinates in the plane represented by `r`: `false` is `r`,
and `true` is its mate. -/
def matchingIndex (p : Equiv.Perm (Fin n)) : PairRep p × Bool → Fin n
  | (r, false) => r.1
  | (r, true) => p r.1

theorem matchingIndex_bijective (p : Equiv.Perm (Fin n))
    (hfixed : ∀ i, p i ≠ i) (hinv : Function.Involutive p) :
    Function.Bijective (matchingIndex p) := by
  constructor
  · rintro ⟨i, bi⟩ ⟨j, bj⟩ h
    cases bi <;> cases bj
    · simp only [matchingIndex] at h
      have hij : i = j := Subtype.ext h
      cases hij
      rfl
    · simp only [matchingIndex] at h
      have hij : i.1 = p j.1 := h
      have hi : p j.1 < p (p j.1) := by simpa only [hij] using i.2
      have hi' : p j.1 < j.1 := by simpa only [hinv j.1] using hi
      exact (lt_asymm hi' j.2).elim
    · simp only [matchingIndex] at h
      have hij : p i.1 = j.1 := h
      have hj : p i.1 < p (p i.1) := by simpa only [← hij] using j.2
      have hj' : p i.1 < i.1 := by simpa only [hinv i.1] using hj
      exact (lt_asymm i.2 hj').elim
    · simp only [matchingIndex] at h
      have hij : i.1 = j.1 := p.injective h
      have hij' : i = j := Subtype.ext hij
      cases hij'
      rfl
  · intro y
    by_cases hlt : y < p y
    · exact ⟨(⟨y, hlt⟩, false), rfl⟩
    · have hne : y ≠ p y := fun h => hfixed y h.symm
      have hmate : p y < y := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
      let r : PairRep p := ⟨p y, by simpa [hinv y] using hmate⟩
      exact ⟨(r, true), by simp [matchingIndex, r, hinv y]⟩

/-- A fixed-point-free involution is explicitly a disjoint union of Boolean
pairs, oriented by the order on `Fin n`. -/
noncomputable def matchingEquiv (p : Equiv.Perm (Fin n))
    (hfixed : ∀ i, p i ≠ i) (hinv : Function.Involutive p) :
    PairRep p × Bool ≃ Fin n :=
  Equiv.ofBijective (matchingIndex p) (matchingIndex_bijective p hfixed hinv)

@[simp] theorem matchingEquiv_apply_false (p : Equiv.Perm (Fin n))
    (hfixed : ∀ i, p i ≠ i) (hinv : Function.Involutive p)
    (r : PairRep p) : matchingEquiv p hfixed hinv (r, false) = r.1 := rfl

@[simp] theorem matchingEquiv_apply_true (p : Equiv.Perm (Fin n))
    (hfixed : ∀ i, p i ≠ i) (hinv : Function.Involutive p)
    (r : PairRep p) : matchingEquiv p hfixed hinv (r, true) = p r.1 := rfl

theorem matchingEquiv_mate (p : Equiv.Perm (Fin n))
    (hfixed : ∀ i, p i ≠ i) (hinv : Function.Involutive p)
    (x : PairRep p × Bool) :
    p (matchingEquiv p hfixed hinv x) =
      matchingEquiv p hfixed hinv (x.1, !x.2) := by
  rcases x with ⟨r, b⟩
  cases b
  · rfl
  · exact hinv r.1

variable {R : Type*} [CommSemiring R] [NoHalfOne R]
  [NoSelfSumZero R]

/-- The canonical Gram function for hyperbolic planes indexed by `I`. -/
noncomputable def hyperbolicGram (I : Type*) :
    I × Bool → I × Bool → R := by
  classical
  exact fun x y => if y = (x.1, !x.2) then 1 else 0

/-- The quadratic function on an orthogonal family of hyperbolic planes. -/
def hyperbolicQ {I : Type*} [Fintype I] (x : I × Bool → R) : R :=
  ∑ i, x (i, false) * x (i, true)

/-- The canonical symmetric companion of `hyperbolicQ`. -/
def hyperbolicCompanion {I : Type*} [Fintype I] :
    (I × Bool → R) →ₗ[R] (I × Bool → R) →ₗ[R] R :=
  LinearMap.mk₂ R
    (fun x y => ∑ i,
      (x (i, false) * y (i, true) + x (i, true) * y (i, false)))
    (by
      intro x z y
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.add_apply]
      ring)
    (by
      intro a x y
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)
    (by
      intro x y z
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.add_apply]
      ring)
    (by
      intro a x y
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)

/-- A canonical orthogonal sum of hyperbolic planes, indexed by `I`. -/
def hyperbolicPair {I : Type*} [Fintype I] :
    QuadraticPair R (I × Bool → R) where
  q := hyperbolicQ
  b := hyperbolicCompanion
  map_smul a x := by
    change (∑ i, (a * x (i, false)) * (a * x (i, true))) =
      a ^ 2 * ∑ i, x (i, false) * x (i, true)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  polar x y := by
    rw [hyperbolicQ, hyperbolicQ, hyperbolicQ]
    change (∑ i, (x (i, false) + y (i, false)) *
      (x (i, true) + y (i, true))) =
      (∑ i, x (i, false) * x (i, true)) +
      (∑ i, y (i, false) * y (i, true)) +
      (∑ i, (x (i, false) * y (i, true) + x (i, true) * y (i, false)))
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  symmetric x y := by
    change (∑ i, (x (i, false) * y (i, true) + x (i, true) * y (i, false))) =
      ∑ i, (y (i, false) * x (i, true) + y (i, true) * x (i, false))
    apply Finset.sum_congr rfl
    intro i _
    ring

omit [NoHalfOne R] [NoSelfSumZero R] in
theorem hyperbolicPair_basisQ {I : Type*} [Fintype I] [DecidableEq I]
    (x : I × Bool) :
    (hyperbolicPair (R := R) (I := I)).q (basisVector x) = 0 := by
  rcases x with ⟨i, b⟩
  cases b <;> simp [hyperbolicPair, hyperbolicQ, basisVector]

omit [NoHalfOne R] [NoSelfSumZero R] in
theorem hyperbolicPair_gram {I : Type*} [Fintype I] [DecidableEq I]
    (x y : I × Bool) :
    (hyperbolicPair (R := R) (I := I)).b (basisVector x) (basisVector y) =
      hyperbolicGram I x y := by
  classical
  rcases x with ⟨i, b⟩
  rcases y with ⟨j, c⟩
  cases b <;> cases c <;>
    simp [hyperbolicPair, hyperbolicCompanion, hyperbolicGram, basisVector]

/-- A coordinate isometry records the complete reindexing of quadratic basis
labels and companion Gram coefficients.  For free modules with unique bases,
this is exactly the coefficient-level content of an isometry. -/
structure CoefficientIsometry {I J : Type*}
    (q₁ : I → R) (g₁ : I → I → R)
    (q₂ : J → R) (g₂ : J → J → R) where
  toEquiv : I ≃ J
  map_q : ∀ i, q₂ (toEquiv i) = q₁ i
  map_g : ∀ i j, g₂ (toEquiv i) (toEquiv j) = g₁ i j

/-- Reindex a finite coordinate module along an equivalence. -/
def reindexLinearEquiv {I J : Type*} (E : I ≃ J) :
    (I → R) ≃ₗ[R] (J → R) :=
  LinearEquiv.piCongrLeft R (fun _ : J => R) E

omit [NoHalfOne R] [NoSelfSumZero R] in
theorem reindexLinearEquiv_basisVector {I J : Type*}
    [DecidableEq I] [DecidableEq J] (E : I ≃ J) (i : I) :
    reindexLinearEquiv (R := R) E (basisVector i) = basisVector (E i) := by
  ext j
  simp only [reindexLinearEquiv, LinearEquiv.piCongrLeft,
    LinearEquiv.piCongrLeft']
  by_cases h : j = E i
  · subst j
    simp [basisVector]
  · have hs : E.symm j ≠ i := by
      intro hs
      apply h
      rw [← E.apply_symm_apply j, hs]
    simp [basisVector, hs, h]

/-- Pull a quadratic pair back along a coordinate reindexing. -/
def QuadraticPair.reindex {I J : Type*}
    (Q : QuadraticPair R (J → R)) (E : I ≃ J) :
    QuadraticPair R (I → R) where
  q x := Q.q (reindexLinearEquiv E x)
  b := Q.b.compl₁₂ (reindexLinearEquiv E).toLinearMap
    (reindexLinearEquiv E).toLinearMap
  map_smul a x := by
    simpa using Q.map_smul a (reindexLinearEquiv E x)
  polar x y := by
    simpa using Q.polar (reindexLinearEquiv E x) (reindexLinearEquiv E y)
  symmetric x y :=
    Q.symmetric (reindexLinearEquiv E x) (reindexLinearEquiv E y)

omit [NoHalfOne R] [NoSelfSumZero R] in
/-- A coefficient isometry between finite quadratic-pair presentations lifts
to an actual linear isometry of the pairs. -/
theorem coefficientIsometry_to_pairIsometry
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (q₁ : I → R) (g₁ : I → I → R)
    (Q : QuadraticPair R (J → R))
    (C : CoefficientIsometry q₁ g₁
      (fun j => Q.q (basisVector j))
      (fun j k => Q.b (basisVector j) (basisVector k)))
    (Q₁ : QuadraticPair R (I → R))
    (hq₁ : ∀ i, Q₁.q (basisVector i) = q₁ i)
    (hg₁ : ∀ i j,
      Q₁.b (basisVector i) (basisVector j) = g₁ i j) :
    Nonempty (QuadraticPair.Isometry Q₁ Q) := by
  let Qr := Q.reindex C.toEquiv
  have hq : ∀ i, Q₁.q (basisVector i) = Qr.q (basisVector i) := by
    intro i
    rw [hq₁ i]
    change q₁ i = Q.q (reindexLinearEquiv C.toEquiv (basisVector i))
    rw [reindexLinearEquiv_basisVector]
    exact (C.map_q i).symm
  have hg : ∀ i j,
      Q₁.b (basisVector i) (basisVector j) =
        Qr.b (basisVector i) (basisVector j) := by
    intro i j
    rw [hg₁ i j]
    change g₁ i j = Q.b
      (reindexLinearEquiv C.toEquiv (basisVector i))
      (reindexLinearEquiv C.toEquiv (basisVector j))
    rw [reindexLinearEquiv_basisVector, reindexLinearEquiv_basisVector]
    exact (C.map_g i j).symm
  obtain ⟨hqall, hball⟩ :=
    quadraticPair_coefficients_determine Q₁ Qr hq hg
  exact ⟨⟨reindexLinearEquiv C.toEquiv,
    fun x => by exact (congrFun hqall x).symm,
    fun x y => by
      exact (DFunLike.congr_fun (DFunLike.congr_fun hball x) y).symm⟩⟩

omit [NoHalfOne R] [NoSelfSumZero R] in
/-- The canonical hyperbolic coefficient presentation therefore lifts to an
actual quadratic-pair isometry. -/
theorem hyperbolicCoefficientIsometry_to_pairIsometry
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (Q : QuadraticPair R (J → R))
    (C : CoefficientIsometry
      (fun _ : I × Bool => (0 : R)) (hyperbolicGram I)
      (fun j => Q.q (basisVector j))
      (fun j k => Q.b (basisVector j) (basisVector k))) :
    Nonempty (QuadraticPair.Isometry
      (hyperbolicPair (R := R) (I := I)) Q) := by
  apply coefficientIsometry_to_pairIsometry _ _ Q C
    (hyperbolicPair (R := R) (I := I))
  · exact hyperbolicPair_basisQ
  · exact hyperbolicPair_gram

/-- End-to-end Hessenberg proxy theorem: a regular symmetric balanced
permutation Gram presentation admits explicit hyperbolic coordinates.  In
those coordinates all quadratic basis labels vanish and the entire Gram
function is the canonical orthogonal sum of hyperbolic planes. -/
theorem symmetric_balanced_permutationGram_hyperbolic
    (q : Fin n → R) (g : Fin n → Fin n → R) (p : Equiv.Perm (Fin n))
    (hgram : ∀ i j, g i j = if j = p i then 1 else 0)
    (hsymmetric : ∀ i j, g i j = g j i)
    (hbalanced : ∀ i, g i i = q i + q i) :
    ∃ (E : PairRep p × Bool ≃ Fin n),
      (∀ x, q (E x) = 0) ∧
      (∀ x y, g (E x) (E y) = hyperbolicGram (PairRep p) x y) := by
  classical
  obtain ⟨hfixed, hinv, hq⟩ :=
    symmetric_balanced_permutationGram q g p hgram hsymmetric hbalanced
  let E := matchingEquiv p hfixed hinv
  refine ⟨E, fun x => hq (E x), ?_⟩
  intro x y
  rw [hgram]
  rw [matchingEquiv_mate p hfixed hinv x]
  rw [hyperbolicGram]
  by_cases h : y = (x.1, !x.2)
  · simp [h, E]
  · have hE : E y ≠ matchingEquiv p hfixed hinv (x.1, !x.2) :=
      fun he => h (E.injective he)
    simp [h, hE]

/-- Classification phrased as a coefficient isometry from a canonical
orthogonal sum of hyperbolic planes to the given regular presentation. -/
theorem symmetric_balanced_permutationGram_isometric_hyperbolic
    (q : Fin n → R) (g : Fin n → Fin n → R) (p : Equiv.Perm (Fin n))
    (hgram : ∀ i j, g i j = if j = p i then 1 else 0)
    (hsymmetric : ∀ i j, g i j = g j i)
    (hbalanced : ∀ i, g i i = q i + q i) :
    Nonempty (CoefficientIsometry
      (fun _ : PairRep p × Bool => (0 : R))
      (hyperbolicGram (PairRep p)) q g) := by
  obtain ⟨E, hq, hg⟩ := symmetric_balanced_permutationGram_hyperbolic
    q g p hgram hsymmetric hbalanced
  exact ⟨⟨E, hq, hg⟩⟩

/-- Once the unique-base certificate is supplied, symmetry and balance are
derived from the quadratic pair itself and Lean constructs the complete
hyperbolic coordinate isometry. -/
theorem regularCertificate_isometric_hyperbolic
    [IsCancelAdd R]
    (Q : QuadraticPair R (Fin n → R))
    (C : RegularPermutationCertificate Q) :
    Nonempty (CoefficientIsometry
      (fun _ : PairRep C.perm × Bool => (0 : R))
      (hyperbolicGram (PairRep C.perm)) Q.basisQ Q.gram) := by
  apply symmetric_balanced_permutationGram_isometric_hyperbolic
    Q.basisQ Q.gram C.perm C.gram_eq
  · intro i j
    exact Q.symmetric (coordinateVector i) (coordinateVector j)
  · intro i
    exact companion_diagonal Q (coordinateVector i)

/-- The same hypotheses force the rank to be even; the witness is the number
of order-selected matching edges. -/
theorem symmetric_balanced_permutationGram_even
    (q : Fin n → R) (g : Fin n → Fin n → R) (p : Equiv.Perm (Fin n))
    (hgram : ∀ i j, g i j = if j = p i then 1 else 0)
    (hsymmetric : ∀ i j, g i j = g j i)
    (hbalanced : ∀ i, g i i = q i + q i) : Even n := by
  letI : Finite (PairRep p) :=
    Finite.of_injective (fun r : PairRep p => r.1) Subtype.val_injective
  letI : Fintype (PairRep p) := Fintype.ofFinite _
  obtain ⟨E, -, -⟩ := symmetric_balanced_permutationGram_hyperbolic
    q g p hgram hsymmetric hbalanced
  have hc := Fintype.card_congr E
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at hc
  refine ⟨Fintype.card (PairRep p), ?_⟩
  omega

/-- A regular permutation certificate also forces even rank. -/
theorem regularCertificate_even [IsCancelAdd R]
    (Q : QuadraticPair R (Fin n → R))
    (C : RegularPermutationCertificate Q) : Even n := by
  apply symmetric_balanced_permutationGram_even
    Q.basisQ Q.gram C.perm C.gram_eq
  · intro i j
    exact Q.symmetric (coordinateVector i) (coordinateVector j)
  · intro i
    exact companion_diagonal Q (coordinateVector i)

/-- Concrete finite-CNF proxy corollary.  No abstract semiring hypotheses
remain: `MvPolynomial (Fin d) Nat` is the exact polynomial model used for the
closed Hessenberg fragment. -/
theorem hessenbergPolynomial_permutationGram_hyperbolic
    (d n : Nat)
    (q : Fin n → MvPolynomial (Fin d) Nat)
    (g : Fin n → Fin n → MvPolynomial (Fin d) Nat)
    (p : Equiv.Perm (Fin n))
    (hgram : ∀ i j, g i j = if j = p i then 1 else 0)
    (hsymmetric : ∀ i j, g i j = g j i)
    (hbalanced : ∀ i, g i i = q i + q i) :
    ∃ (E : PairRep p × Bool ≃ Fin n),
      (∀ x, q (E x) = 0) ∧
      (∀ x y, g (E x) (E y) =
        hyperbolicGram (PairRep p) x y) := by
  exact symmetric_balanced_permutationGram_hyperbolic
    q g p hgram hsymmetric hbalanced

/-- Flagship finite-CNF proxy theorem.  For an actual regular quadratic pair
over the polynomial Hessenberg model, the cited unique-base output is the
single bridge hypothesis; the complete hyperbolic classification after that
bridge is kernel-checked. -/
theorem hessenbergPolynomial_regularCertificate_isometric_hyperbolic
    (d n : Nat)
    (Q : QuadraticPair (MvPolynomial (Fin d) Nat)
      (Fin n → MvPolynomial (Fin d) Nat))
    (C : RegularPermutationCertificate Q) :
    Nonempty (CoefficientIsometry
      (fun _ : PairRep C.perm × Bool =>
        (0 : MvPolynomial (Fin d) Nat))
      (hyperbolicGram (PairRep C.perm)) Q.basisQ Q.gram) :=
  regularCertificate_isometric_hyperbolic Q C

/-- Fully internal finite-CNF Hessenberg collapse.  Starting only from an
actual quadratic pair and invertibility of its companion Gram matrix, Lean
constructs the permutation certificate, proves even rank, and returns a
coefficient isometry with a canonical orthogonal sum of hyperbolic planes. -/
theorem hessenbergPolynomial_matrixRegular_hyperbolic
    (d n : Nat)
    (Q : QuadraticPair (MvPolynomial (Fin d) Nat)
      (Fin n → MvPolynomial (Fin d) Nat))
    (hreg : Q.MatrixRegular) :
    Even n ∧
      ∃ p : Equiv.Perm (Fin n),
        Nonempty (CoefficientIsometry
          (fun _ : PairRep p × Bool =>
            (0 : MvPolynomial (Fin d) Nat))
          (hyperbolicGram (PairRep p)) Q.basisQ Q.gram) := by
  obtain ⟨C⟩ :=
    hessenbergPolynomial_regular_permutationCertificate Q hreg
  exact ⟨regularCertificate_even Q C, C.perm,
    regularCertificate_isometric_hyperbolic Q C⟩

/-- Gold--Arf-style endpoint for the finite-CNF Hessenberg proxy.  Its input
is the paper's actual regularity condition--bijectivity of the companion
adjoint--rather than a permutation or matching hypothesis.  The proof
internally passes through dual coordinates, invertible-matrix monomiality,
balance, and the fixed-point-free matching construction. -/
theorem hessenbergPolynomial_regular_hyperbolic
    (d n : Nat)
    (Q : QuadraticPair (MvPolynomial (Fin d) Nat)
      (Fin n → MvPolynomial (Fin d) Nat))
    (hreg : Q.Regular) :
    Even n ∧
      ∃ p : Equiv.Perm (Fin n),
        Nonempty (CoefficientIsometry
          (fun _ : PairRep p × Bool =>
            (0 : MvPolynomial (Fin d) Nat))
          (hyperbolicGram (PairRep p)) Q.basisQ Q.gram) :=
  hessenbergPolynomial_matrixRegular_hyperbolic d n Q
    (Q.matrixRegular_of_regular hreg)

/-- Strongest endpoint: every regular quadratic pair over the finite
polynomial Hessenberg model is actually isometric, as a pair preserving both
`q` and `b`, to a canonical orthogonal sum of hyperbolic planes. -/
theorem hessenbergPolynomial_regular_isometric_hyperbolic
    (d n : Nat)
    (Q : QuadraticPair (MvPolynomial (Fin d) Nat)
      (Fin n → MvPolynomial (Fin d) Nat))
    (hreg : Q.Regular) :
    Even n ∧
      ∃ p : Equiv.Perm (Fin n),
        Nonempty (QuadraticPair.Isometry
          (hyperbolicPair
            (R := MvPolynomial (Fin d) Nat) (I := PairRep p)) Q) := by
  have hmreg := Q.matrixRegular_of_regular hreg
  obtain ⟨C⟩ :=
    hessenbergPolynomial_regular_permutationCertificate Q hmreg
  obtain ⟨CI⟩ := regularCertificate_isometric_hyperbolic Q C
  exact ⟨regularCertificate_even Q C, C.perm,
    hyperbolicCoefficientIsometry_to_pairIsometry Q CI⟩

end HyperbolicMatching

section CancellativeTargetBoundary

variable {Source Target : Type*} [AddCommMonoid Source]
  [AddCancelCommMonoid Target]

/-- An additive invariant into a cancellative monoid kills any class that its
chosen observation identifies with its double.  In the thermograph
application the external input is that freezing gives the same wall pair to a
nonzero infinitesimal and its double. -/
theorem additiveInvariant_eq_zero_of_eq_double
    (encode : Source →+ Target) (x : Source)
    (h : encode x = encode (x + x)) : encode x = 0 := by
  rw [map_add] at h
  have hcancel : encode x + 0 = encode x + encode x := by simpa using h
  exact (add_left_cancel hcancel).symm

end CancellativeTargetBoundary

section ParityCollapse

variable {G : Type*} [AddCommGroup G]

/-- Once diagonalization has reduced every scalar-extension class to a natural
multiple of one loop and the hyperbolic plane has imposed `2 • loop = 0`, the
multiple depends only on rank parity.  The paper supplies the classical
diagonalization and identifies the loop for the two supertropical companion
lifts; this theorem checks the universal group-theoretic collapse. -/
theorem twoTorsion_nsmul_eq_parity (loop : G) (htwo : 2 • loop = 0)
    (n : Nat) : n • loop = (n % 2) • loop := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | n
      · simp
      · simp
      · calc
          (n + 2) • loop = n • loop + 2 • loop := by rw [add_nsmul]
          _ = n • loop := by rw [htwo, add_zero]
          _ = (n % 2) • loop := ih n (by omega)
          _ = ((n + 2) % 2) • loop := by congr 1; omega

/-- A parity detector proves that the two-torsion loop surviving the
hyperbolic relation is nonzero. -/
theorem loop_ne_zero_of_parityDetector (loop : G)
    (parity : G →+ ZMod 2) (hloop : parity loop = 1) : loop ≠ 0 := by
  intro hzero
  rw [hzero, map_zero] at hloop
  exact zero_ne_one hloop

/-- The exact presentation delivered by diagonalization, normalization, and
the hyperbolic change of basis in the supertropical ring-image quotient.

The fields deliberately record the mathematical joins separately: `cyclic`
is the diagonalization/normalization statement, `hyperbolic` is the relation
coming from the two presentations of the classical hyperbolic plane, and
`parity_loop` is the noncollapse certificate. -/
structure RankParityPresentation (G : Type*) [AddCommGroup G] where
  loop : G
  parity : G →+ ZMod 2
  cyclic : ∀ x : G, ∃ n : Int, x = n • loop
  hyperbolic : 2 • loop = 0
  parity_loop : parity loop = 1

/-- The inverse to rank parity: a residue class acts on the distinguished
loop.  The hyperbolic relation is precisely what makes this well-defined. -/
def RankParityPresentation.fromParity (P : RankParityPresentation G) :
    ZMod 2 →+ G :=
  ZMod.lift 2 ⟨zmultiplesHom G P.loop, by
    change (2 : Int) • P.loop = 0
    simpa only [ofNat_zsmul] using P.hyperbolic⟩

/-- A group with the exact ring-image presentation is not merely generated
by an element of order at most two: its supplied parity detector is an
additive equivalence with `ZMod 2`.  This is the universal group-theoretic
endpoint of the characteristic-not-two supertropical argument. -/
def RankParityPresentation.equivZModTwo
    (P : RankParityPresentation G) : G ≃+ ZMod 2 where
  toFun := P.parity
  invFun := P.fromParity
  map_add' := P.parity.map_add
  left_inv x := by
    obtain ⟨n, rfl⟩ := P.cyclic x
    simp [RankParityPresentation.fromParity, P.parity_loop]
  right_inv z := by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
    simp [RankParityPresentation.fromParity, P.parity_loop]

/-- Named end-to-end group theorem used by both the canonical balanced and
the polar-companion scalar-extension presentations. -/
theorem universal_ringImage_quotient_equiv_zmodTwo
    (P : RankParityPresentation G) : Nonempty (G ≃+ ZMod 2) :=
  ⟨P.equivZModTwo⟩

end ParityCollapse

section ClassicalDiagonalization

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Mathlib's characteristic-not-two diagonalization theorem, exposed with
the ordinary hypothesis `2 ≠ 0` instead of the implementation typeclass
`Invertible 2`.  This supplies the classical diagonalization join in the
supertropical ring-image proof. -/
theorem classical_form_diagonalizes_of_two_ne_zero (h2 : (2 : K) ≠ 0)
    (Q : QuadraticForm K V) :
    ∃ w : Fin (Module.finrank K V) → K,
      Equivalent Q (weightedSumSquares K w) := by
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  exact Q.equivalent_weightedSumSquares

end ClassicalDiagonalization

end Ogdoad.SemiringQuadratic
