#!/usr/bin/env python3
"""Exact stdlib certificate for the final rowwise ordinary target ``p=727``.

Here ``ord_727(2)=121=11^2`` and the actual Conway dependency is

    alpha_727 = kappa_121 + m_727,
    P_alpha_11(X) = X^20 + X^16 + X^5 + X + 1,
    P_kappa_121(X) = P_alpha_11(X^121).

Binary polynomials are Python integers: bit ``i`` is the coefficient of
``X^i``.  The checker constructs the literal selected degree-2420 polynomial,
proves it irreducible by Rabin's criterion, and evaluates the exact 727-Euler
power for both finite translates.  The result is

    kappa_121^((2^2420-1)/727) = 1,
    (kappa_121+1)^((2^2420-1)/727) != 1,

so the least finite translate is ``m_727=1``.  No external factor table or
probable-prime test is used.  This is the deliberate rowwise cutoff; the
remaining research target is the global ordinary-spine theorem.
"""

from __future__ import annotations

import hashlib

if not __debug__:
    raise SystemExit("assertions must remain enabled; do not run with python -O")


P = 727
ORDER_TWO = 121
DEGREE_ALPHA_11 = 20
DEGREE = ORDER_TWO * DEGREE_ALPHA_11


def support(poly: int) -> list[int]:
    """Return the increasing set-bit positions of a binary polynomial."""

    out: list[int] = []
    while poly:
        low = poly & -poly
        out.append(low.bit_length() - 1)
        poly ^= low
    return out


def sparse_mul(poly: int, sparse_factor: int) -> int:
    """Multiply binary polynomials when one factor is sparse."""

    out = 0
    for exponent in support(sparse_factor):
        out ^= poly << exponent
    return out


def compose_sparse(poly: int, inner: int) -> int:
    """Return ``poly(inner(X))`` over ``F_2`` by Horner evaluation."""

    out = 0
    for exponent in range(poly.bit_length() - 1, -1, -1):
        out = sparse_mul(out, inner)
        if (poly >> exponent) & 1:
            out ^= 1
    return out


def one_plus_x_pow(exponent: int) -> int:
    """Return ``(1+X)^exponent`` over ``F_2`` by Lucas's theorem."""

    out = 0
    submask = exponent
    while True:
        out |= 1 << submask
        if submask == 0:
            return out
        submask = (submask - 1) & exponent


def monomial_compose(poly: int, exponent: int) -> int:
    """Return ``poly(X^exponent)`` for a bit-packed binary polynomial."""

    return sum(1 << (exponent * i) for i in support(poly))


def poly_mod(value: int, modulus: int) -> int:
    """Reduce one binary polynomial modulo a monic binary polynomial."""

    modulus_degree = modulus.bit_length() - 1
    while value.bit_length() - 1 >= modulus_degree:
        value ^= modulus << (value.bit_length() - 1 - modulus_degree)
    return value


def poly_mul_mod(left: int, right: int, modulus: int) -> int:
    """Multiply binary polynomials modulo ``modulus``."""

    result = 0
    while right:
        if right & 1:
            result ^= left
        right >>= 1
        left <<= 1
        if left.bit_length() >= modulus.bit_length():
            left ^= modulus
    return poly_mod(result, modulus)


def poly_pow_mod(base: int, exponent: int, modulus: int) -> int:
    """Exponentiate a binary polynomial modulo ``modulus``."""

    result = 1
    while exponent:
        if exponent & 1:
            result = poly_mul_mod(result, base, modulus)
        exponent >>= 1
        if exponent:
            base = poly_mul_mod(base, base, modulus)
    return result


def poly_gcd(left: int, right: int) -> int:
    """Return the monic gcd of two binary polynomials."""

    while right:
        left, right = right, poly_mod(left, right)
    return left


def fixed_digest(poly: int) -> str:
    """Hash one field element in the fixed degree-2420 polynomial basis."""

    payload = poly.to_bytes((DEGREE + 7) // 8, "little")
    return hashlib.sha256(payload).hexdigest()


def is_prime(value: int) -> bool:
    """Deterministic trial-division primality check for the small row prime."""

    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor <= value // divisor:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def main() -> None:
    p_alpha_5 = (1 << 4) | (1 << 1) | 1
    p_alpha_11 = compose_sparse(p_alpha_5, one_plus_x_pow(5))
    modulus = monomial_compose(p_alpha_11, ORDER_TWO)

    assert P == 727 and is_prime(P)
    assert pow(2, ORDER_TWO, P) == 1
    assert pow(2, 11, P) != 1
    assert pow(2, 1, P) != 1
    assert p_alpha_11 == 0x110023
    assert modulus.bit_length() - 1 == DEGREE
    assert modulus.bit_count() == 5
    assert fixed_digest(modulus) == (
        "a10b35b0caf07945af6d71c0f3fccb7b3e67c3f5ae3124e19b5482e960cec852"
    )

    # Rabin irreducibility criterion.  The prime divisors of 2420 are
    # 2, 5, and 11, so these are the complete proper-subfield checks.
    generator = 1 << 1
    assert poly_pow_mod(generator, 1 << DEGREE, modulus) == generator
    for prime_divisor in (2, 5, 11):
        subfield_residue = (
            poly_pow_mod(generator, 1 << (DEGREE // prime_divisor), modulus)
            ^ generator
        )
        assert poly_gcd(modulus, subfield_residue) == 1

    group_order = (1 << DEGREE) - 1
    assert group_order % P == 0
    euler_exponent = group_order // P
    phase_zero = poly_pow_mod(generator, euler_exponent, modulus)
    phase_one = poly_pow_mod(generator ^ 1, euler_exponent, modulus)

    assert phase_zero == 1
    assert phase_one != 1
    assert poly_pow_mod(phase_one, P, modulus) == 1
    assert fixed_digest(phase_one) == (
        "1b95861258bcf45a90c284011c3337561996e5cc70ee6e05374b121515103e57"
    )

    print(
        "p727 certificate: verified",
        f"degree={DEGREE}",
        f"modulus_terms={modulus.bit_count()}",
        f"modulus_sha256={fixed_digest(modulus)}",
        "m0_phase=1",
        f"m1_phase_sha256={fixed_digest(phase_one)}",
        "m1_phase_nontrivial=True",
        "m727=1",
    )


if __name__ == "__main__":
    main()
