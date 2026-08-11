"""Exact degree-81 countermodel for the two-normal-basis C-arm package.

This is a finite certificate, not a counterexample to the selected Conway
tower.  It retains the local Singer identities, the normalized beta
coordinate, the determinant-one half-circulant relation, absolute normality
of epsilon, and complete normality of beta, while the current 2593-coordinate
fails.  What it deliberately does not retain is the recursively selected
lower trace ancestry.

Elements of ``GF(2^81)`` are polynomial bit-vectors modulo ``MODULUS``; bit
``i`` is the coefficient of ``X^i``.
"""

from __future__ import annotations


MODULUS = 0x329341F8B47DD7938AF63
DEGREE = 81
LOWER_DEGREE = 27
Q = 1 << LOWER_DEGREE
FIELD_ORDER = 1 << DEGREE
MULTIPLICATIVE_ORDER = FIELD_ORDER - 1
TORUS_ORDER = Q * Q + Q + 1
ELL = 2593

ETA = 1629469875507523981620540
EPSILON = 1629469875507523981620541
BETA = 2293671573472151973449566


def field_mul(a: int, b: int) -> int:
    """Multiply two polynomial bit-vectors modulo ``MODULUS``."""

    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a >> DEGREE:
            a ^= MODULUS
    return result


def field_pow(a: int, exponent: int) -> int:
    """Exponentiate in the represented degree-81 quotient."""

    result = 1
    while exponent:
        if exponent & 1:
            result = field_mul(result, a)
        a = field_mul(a, a)
        exponent >>= 1
    return result


def moore_determinant(x: int, subfield_degree: int) -> int:
    """Return the relative Moore determinant over ``GF(2^d)``."""

    rank = DEGREE // subfield_degree
    frobenius_power = 1 << subfield_degree
    conjugates: list[int] = []
    value = x
    for _ in range(rank):
        conjugates.append(value)
        value = field_pow(value, frobenius_power)

    matrix: list[list[int]] = []
    row = conjugates[:]
    for _ in range(rank):
        matrix.append(row)
        row = [field_pow(value, frobenius_power) for value in row]

    determinant = 1
    for column in range(rank):
        pivot = next(
            (index for index in range(column, rank) if matrix[index][column]),
            None,
        )
        if pivot is None:
            return 0
        matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
        pivot_value = matrix[column][column]
        determinant = field_mul(determinant, pivot_value)
        pivot_inverse = field_pow(pivot_value, MULTIPLICATIVE_ORDER - 1)
        matrix[column] = [
            field_mul(value, pivot_inverse) for value in matrix[column]
        ]
        for index in range(column + 1, rank):
            if matrix[index][column]:
                coefficient = matrix[index][column]
                matrix[index] = [
                    left ^ field_mul(coefficient, right)
                    for left, right in zip(
                        matrix[index], matrix[column], strict=True
                    )
                ]
    return determinant


def polynomial_mul(a: int, b: int) -> int:
    """Carryless multiplication in ``GF(2)[X]`` without reduction."""

    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
    return result


def polynomial_mod(a: int, modulus: int) -> int:
    """Remainder of one bit-polynomial by another."""

    modulus_degree = modulus.bit_length() - 1
    while a.bit_length() - 1 >= modulus_degree:
        a ^= modulus << (a.bit_length() - 1 - modulus_degree)
    return a


def polynomial_gcd(a: int, b: int) -> int:
    """Greatest common divisor of two bit-polynomials."""

    while b:
        a, b = b, polynomial_mod(a, b)
    return a


def square_polynomial_mod(a: int) -> int:
    """Square a bit-polynomial and reduce it by ``MODULUS``."""

    return polynomial_mod(polynomial_mul(a, a), MODULUS)


def certify() -> None:
    """Run the irreducibility, Kummer, incidence, and normality checks."""

    assert MODULUS.bit_length() - 1 == DEGREE
    assert TORUS_ORDER % ELL == 0
    assert field_pow(ETA, Q + 1) == (ETA ^ 1)
    assert field_pow(ETA, TORUS_ORDER) == 1
    assert field_pow(ETA, TORUS_ORDER // ELL) == 1
    assert EPSILON == (ETA ^ 1) == field_pow(ETA, Q + 1)
    assert BETA == (1 ^ field_pow(ETA, Q // 2 + 1))
    assert field_mul(field_pow(BETA, Q - 1), ETA) == 1

    half_circulant = 0
    value = EPSILON
    for _ in range(1, DEGREE - 1):
        value = field_mul(value, value)
        half_circulant ^= value
    assert half_circulant == BETA

    assert field_pow(ETA, MULTIPLICATIVE_ORDER // ELL) == 1
    assert field_pow(EPSILON, MULTIPLICATIVE_ORDER // ELL) == 1
    assert field_pow(BETA, MULTIPLICATIVE_ORDER // ELL) == 1

    eta_trace_27 = ETA ^ field_pow(ETA, Q) ^ field_pow(ETA, Q * Q)
    assert field_pow(eta_trace_27, (1 << 9) + 1) ^ eta_trace_27 ^ 1 != 0

    assert moore_determinant(EPSILON, 1) == 1
    assert [moore_determinant(BETA, degree) for degree in (1, 3, 9, 27)] == [
        1,
        996154457819232351242539,
        1913091018644430508445588,
        1836908266524337706399502,
    ]

    x = 2
    frobenius = x
    residues = {0: x}
    for index in range(1, DEGREE + 1):
        frobenius = square_polynomial_mod(frobenius)
        residues[index] = frobenius
    assert residues[DEGREE] == x
    assert polynomial_gcd(MODULUS, residues[LOWER_DEGREE] ^ x) == 1

    print(
        "degree-81 two-normal-basis countermodel: Singer, normalized beta, "
        "half-circulant, Kummer-kernel, Rabin, and Moore certificates pass"
    )


if __name__ == "__main__":
    certify()
