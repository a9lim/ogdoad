#!/usr/bin/env python3
"""Exact generic H=32 countermodel for the top-orbit S-unit reduction.

This certificate works on

    E : y^2 + y = x^3 + x^2

over ``L = GF(2^64)``.  The point ``P`` has an ``x``-coordinate of exact
degree 32 and satisfies ``P^(2^32) = -P``.  Thus it retains the unmarked top
Frobenius orbit and Fermat-torsion geometry.  It deliberately violates the
literal Conway half-Frobenius selector

    x^(2^16) = x + 1.

At ``ell = 641``, the fixed five-torsion value ``g(P)`` is an ell-th power,
whereas both the orbit-supported value ``Theta`` and the second fixed-support
unit ``s(P)`` have full order ``2^32 + 1``.  This disproves any reduction from
the unmarked top-orbit data alone.  It is not a counterexample to the selected
Conway--Fermat assertion.

Elements of ``K = GF(2^32)`` are coefficient-bit integers modulo
``K_MODULUS``.  Elements ``a + b*y`` of
``L = K[y]/(y^2 + y + D)`` are packed as ``a | (b << 32)``.
"""

from __future__ import annotations


K_MODULUS = 0x1C019C923
K_DEGREE = 32
K_MASK = (1 << K_DEGREE) - 1
Q = 1 << K_DEGREE
HALF_FROBENIUS = 1 << (K_DEGREE // 2)
NORM_ONE_ORDER = Q + 1

ELL = 641
COFACTOR = 6_700_417

X_COORDINATE = 0x2BF5B2FB
ARTIN_SCHREIER_DRIVER = 0xCE655646
Y_GENERATOR = 1 << K_DEGREE
MINPOLY = 0x1B3E069A5

X_PLUS_T = 0x63E1B77900000000
X_MINUS_T = 0x63E1B77963E1B779
Z_PLUS = 0xE22EF88E890F600C
Z_MINUS = 0xE22EF88E6B219882
THETA = 0x06721665E32D6019
G_VALUE = 0x992BFDE0992BFDE1
S_VALUE = 0x37E967739B55F56F


def polynomial_mod(value: int, modulus: int) -> int:
    """Reduce one coefficient-bit polynomial by another over ``GF(2)``."""

    modulus_degree = modulus.bit_length() - 1
    while value and value.bit_length() - 1 >= modulus_degree:
        value ^= modulus << (value.bit_length() - 1 - modulus_degree)
    return value


def polynomial_gcd(left: int, right: int) -> int:
    """Greatest common divisor of coefficient-bit polynomials."""

    while right:
        left, right = right, polynomial_mod(left, right)
    return left


def k_mul(left: int, right: int) -> int:
    """Multiply in ``K``."""

    result = 0
    while right:
        if right & 1:
            result ^= left
        right >>= 1
        left <<= 1
    return polynomial_mod(result, K_MODULUS)


def k_pow(value: int, exponent: int) -> int:
    """Exponentiate in ``K``."""

    result = 1
    while exponent:
        if exponent & 1:
            result = k_mul(result, value)
        exponent >>= 1
        if exponent:
            value = k_mul(value, value)
    return result


def k_eval(polynomial: int, value: int) -> int:
    """Evaluate an ``F_2`` bit-polynomial at an element of ``K``."""

    result = 0
    for index in range(polynomial.bit_length() - 1, -1, -1):
        result = k_mul(result, value)
        if (polynomial >> index) & 1:
            result ^= 1
    return result


def l_unpack(value: int) -> tuple[int, int]:
    """Return the two ``K`` coefficients of a packed element of ``L``."""

    return value & K_MASK, value >> K_DEGREE


def l_pack(constant: int, linear: int) -> int:
    """Pack ``constant + linear*y`` as one integer."""

    return constant | (linear << K_DEGREE)


def l_mul(left: int, right: int) -> int:
    """Multiply in ``L``, using ``y^2 = y + D``."""

    a, b = l_unpack(left)
    c, e = l_unpack(right)
    be = k_mul(b, e)
    return l_pack(
        k_mul(a, c) ^ k_mul(be, ARTIN_SCHREIER_DRIVER),
        k_mul(a, e) ^ k_mul(b, c) ^ be,
    )


def l_pow(value: int, exponent: int) -> int:
    """Exponentiate in ``L``."""

    result = 1
    while exponent:
        if exponent & 1:
            result = l_mul(result, value)
        exponent >>= 1
        if exponent:
            value = l_mul(value, value)
    return result


def l_inverse(value: int) -> int:
    """Invert a nonzero element of ``L``."""

    assert value != 0
    return l_pow(value, (1 << (2 * K_DEGREE)) - 2)


def l_div(left: int, right: int) -> int:
    """Divide in ``L``."""

    return l_mul(left, l_inverse(right))


def l_eval(polynomial: int, value: int) -> int:
    """Evaluate an ``F_2`` bit-polynomial at an element of ``L``."""

    result = 0
    for index in range(polynomial.bit_length() - 1, -1, -1):
        result = l_mul(result, value)
        if (polynomial >> index) & 1:
            result ^= 1
    return result


def is_prime_by_trial_division(value: int) -> bool:
    """Deterministically certify the two small displayed prime factors."""

    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def certify() -> None:
    """Replay the field, point, translated-value, and order certificates."""

    variable = 2
    assert K_MODULUS.bit_length() - 1 == K_DEGREE
    assert k_pow(variable, 1 << K_DEGREE) == variable
    assert (
        polynomial_gcd(
            K_MODULUS,
            k_pow(variable, 1 << (K_DEGREE // 2)) ^ variable,
        )
        == 1
    )

    assert MINPOLY.bit_length() - 1 == K_DEGREE
    assert k_eval(MINPOLY, X_COORDINATE) == 0
    assert k_pow(X_COORDINATE, 1 << K_DEGREE) == X_COORDINATE
    half_x = k_pow(X_COORDINATE, HALF_FROBENIUS)
    assert half_x == 0x5E024149
    assert half_x != X_COORDINATE
    assert half_x != X_COORDINATE ^ 1

    x_squared = k_mul(X_COORDINATE, X_COORDINATE)
    assert (
        k_mul(x_squared, X_COORDINATE) ^ x_squared
        == ARTIN_SCHREIER_DRIVER
    )
    trace = 0
    conjugate = ARTIN_SCHREIER_DRIVER
    for _ in range(K_DEGREE):
        trace ^= conjugate
        conjugate = k_mul(conjugate, conjugate)
    assert trace == 1

    assert l_mul(Y_GENERATOR, Y_GENERATOR) ^ Y_GENERATOR == ARTIN_SCHREIER_DRIVER
    assert l_pow(Y_GENERATOR, Q) == Y_GENERATOR ^ 1

    # On E, adding T=(0,0) gives x'=(y/x)^2+x+1; adding -T=(0,1)
    # replaces y by y+1 in the slope.
    slope_plus = l_div(Y_GENERATOR, X_COORDINATE)
    slope_minus = l_div(Y_GENERATOR ^ 1, X_COORDINATE)
    assert l_mul(slope_plus, slope_plus) ^ X_COORDINATE ^ 1 == X_PLUS_T
    assert l_mul(slope_minus, slope_minus) ^ X_COORDINATE ^ 1 == X_MINUS_T

    assert l_eval(MINPOLY, X_PLUS_T) == Z_PLUS
    assert l_eval(MINPOLY, X_MINUS_T) == Z_MINUS
    assert l_pow(Z_PLUS, Q) == Z_MINUS
    assert l_div(Z_MINUS, Z_PLUS) == THETA
    assert l_pow(THETA, NORM_ONE_ORDER) == 1

    assert NORM_ONE_ORDER == ELL * COFACTOR
    assert is_prime_by_trial_division(ELL)
    assert is_prime_by_trial_division(COFACTOR)
    assert l_pow(THETA, COFACTOR) == 0x477066F36420B4F2
    assert l_pow(THETA, ELL) == 0x543CADD554BC08A2
    assert l_pow(THETA, COFACTOR) != 1
    assert l_pow(THETA, ELL) != 1

    g_value = l_div(Y_GENERATOR ^ 1, Y_GENERATOR)
    assert g_value == G_VALUE
    assert l_pow(g_value, COFACTOR) == 1
    assert g_value != 1

    # iota(x,y)=(x+1,y+x+1), and s=g^2/(g o iota).
    g_iota = l_div(Y_GENERATOR ^ X_COORDINATE, Y_GENERATOR ^ X_COORDINATE ^ 1)
    s_value = l_div(l_mul(g_value, g_value), g_iota)
    assert s_value == S_VALUE
    assert l_pow(s_value, NORM_ONE_ORDER) == 1
    assert l_pow(s_value, COFACTOR) == 0x1F875F8645DBA3F5
    assert l_pow(s_value, ELL) == 0x761AFEB3E584166E
    assert l_pow(s_value, COFACTOR) != 1
    assert l_pow(s_value, ELL) != 1

    print("degree-32 base field and degree-64 Artin--Schreier field certified")
    print("generic point: P^(2^32) = -P and x has exact degree 32")
    print("literal selector fails: x^(2^16) != x + 1")
    print("ord(g(P)) = 6700417, so [g(P)]_641 = 0")
    print("ord(Theta) = ord(s(P)) = 2^32 + 1")
    print("finite generic countermodel certified; no Conway-selected claim")


if __name__ == "__main__":
    certify()
