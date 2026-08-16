import Mathlib

/-!
# Quadratic pairs over cancellative semirings

This file checks the algebraic core used for the finite-CNF Hessenberg
semiring in `writeups/semiring_stability.tex`.

The external unique-base theorem says that an invertible matrix over an
entire antiring is monomial.  For the Hessenberg fragments the only scalar
unit is `1`, so the adjoint matrix of a regular bilinear companion is a
permutation matrix.  Lean starts at precisely that cited boundary and proves:

* every companion over an additively cancellative semiring is balanced on the
  diagonal;
* a symmetric, balanced permutation Gram matrix has no fixed points, is an
  involution, and has zero quadratic values on every basis vector;
* the coefficient semiring `MvPolynomial (Fin d) Nat`, which models the
  fragment below `omega^(omega^d)`, has no element whose double is `1`.

Thus the permutation consists of transpositions, and each transposition is a
hyperbolic plane.  The finite matching decomposition from a fixed-point-free
involution is standard finite combinatorics and is carried out in the paper.
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

end PolynomialFragment

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

end ParityCollapse

end Ogdoad.SemiringQuadratic
