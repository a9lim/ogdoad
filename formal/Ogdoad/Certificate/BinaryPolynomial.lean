import Mathlib.Data.Nat.Bitwise

/-!
# Binary-polynomial certificate arithmetic

This module owns the executable bit-polynomial arithmetic shared by exact
finite-field certificates. A natural number encodes a polynomial over
`F_2`, with bit `i` equal to the coefficient of `X^i`.

These definitions are certificate evaluators, not a proved finite-field
implementation. Individual certificate modules separately check that their
chosen modulus is irreducible and then use native evaluation for named finite
identities.
-/

namespace Ogdoad.BinaryPolynomialCertificate

/-- Shift-and-reduce multiplication with an explicit recursion budget. -/
def mulAux (modulus degree : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, a, b, acc =>
      let acc' := if b % 2 = 1 then Nat.xor acc a else acc
      let a2 := Nat.shiftLeft a 1
      let a' := if a2.testBit degree then Nat.xor a2 modulus else a2
      mulAux modulus degree fuel a' (b / 2) acc'

/-- Multiplication modulo a monic binary polynomial of the stated degree. -/
def mul (modulus degree a b : Nat) : Nat :=
  mulAux modulus degree degree a b 0

/-- Binary powering with an explicit recursion budget. -/
def powAux (modulus degree : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, a, e, acc =>
      if e = 0 then acc
      else
        let acc' := if e % 2 = 1 then mul modulus degree acc a else acc
        powAux modulus degree fuel (mul modulus degree a a) (e / 2) acc'

/-- Powering modulo a monic binary polynomial. -/
def fpow (modulus degree a e : Nat) : Nat :=
  powAux modulus degree (degree + 2) a e 1

/-- Binary-polynomial remainder with an explicit recursion budget. -/
def polyModAux : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | fuel + 1, a, b =>
      if b = 0 ∨ Nat.log2 a < Nat.log2 b then a
      else polyModAux fuel
        (Nat.xor a (Nat.shiftLeft b (Nat.log2 a - Nat.log2 b))) b

/-- Binary-polynomial remainder. -/
def polyMod (fuel a b : Nat) : Nat := polyModAux fuel a b

/-- Euclidean gcd with explicit outer and remainder budgets. -/
def polyGcdAux (remainderFuel : Nat) : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | fuel + 1, a, b =>
      if b = 0 then a
      else polyGcdAux remainderFuel fuel b (polyMod remainderFuel a b)

/-- Binary-polynomial gcd using one budget for both Euclidean loops. -/
def polyGcd (fuel a b : Nat) : Nat := polyGcdAux fuel fuel a b

end Ogdoad.BinaryPolynomialCertificate
