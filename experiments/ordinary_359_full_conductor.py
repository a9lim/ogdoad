#!/usr/bin/env python3
"""Exact stdlib certificate for the selected p=359 full-conductor polynomial.

Binary polynomials are encoded as Python integers: bit i is the coefficient
of X^i.  The construction is the literal Conway dependency chain

  alpha_179 = kappa_89 + 1,
  alpha_89  = kappa_11 + 1,
  alpha_11  = kappa_5  + 1,
  alpha_5   = kappa_4,

and P_child(Z) = P_parent((Z+1)^Q) at Q = 5, 11, 89.
"""

from __future__ import annotations

import hashlib


def support(poly: int) -> list[int]:
    out: list[int] = []
    while poly:
        low = poly & -poly
        out.append(low.bit_length() - 1)
        poly ^= low
    return out


def sparse_mul(poly: int, sparse_factor: int) -> int:
    """Multiply by a sparse GF(2) polynomial."""
    out = 0
    for exponent in support(sparse_factor):
        out ^= poly << exponent
    return out


def compose_sparse(poly: int, inner: int) -> int:
    """Return poly(inner(X)) over GF(2), using Horner's rule."""
    out = 0
    for exponent in range(poly.bit_length() - 1, -1, -1):
        out = sparse_mul(out, inner)
        if (poly >> exponent) & 1:
            out ^= 1
    return out


def one_plus_x_pow(exponent: int) -> int:
    """Return (1+X)^exponent mod 2 by Lucas's theorem."""
    poly = 0
    submask = exponent
    while True:
        poly |= 1 << submask
        if submask == 0:
            return poly
        submask = (submask - 1) & exponent


def monomial_compose(poly: int, exponent: int) -> int:
    return sum(1 << (exponent * i) for i in support(poly))


def digest(poly: int) -> str:
    degree = poly.bit_length() - 1
    payload = poly.to_bytes((degree + 8) // 8, "little")
    return hashlib.sha256(payload).hexdigest()


def poly_mod(value: int, modulus: int) -> int:
    """Reduce one binary polynomial modulo another."""

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


def report(
    name: str,
    poly: int,
    expected_degree: int,
    expected_terms: int,
    expected_hash: str,
) -> None:
    degree = poly.bit_length() - 1
    terms = poly.bit_count()
    fingerprint = digest(poly)
    assert (degree, terms, fingerprint) == (
        expected_degree,
        expected_terms,
        expected_hash,
    )
    print(f"{name}: degree={degree}, terms={terms}, sha256={fingerprint}")


def main() -> None:
    # Deterministic coefficient field for the compact degree-19,580 factor
    # certificate described in the paper.  Since 179 is prime, these are the
    # complete Rabin irreducibility checks.
    certificate_field_modulus = (
        (1 << 179) | (1 << 4) | (1 << 2) | (1 << 1) | 1
    )
    assert poly_pow_mod(2, 1 << 179, certificate_field_modulus) == 2
    assert poly_gcd(certificate_field_modulus, (1 << 2) | (1 << 1)) == 1

    p_alpha_5 = (1 << 4) | (1 << 1) | 1
    p_alpha_11 = compose_sparse(p_alpha_5, one_plus_x_pow(5))
    p_alpha_89 = compose_sparse(p_alpha_11, one_plus_x_pow(11))
    p_alpha_179 = compose_sparse(p_alpha_89, one_plus_x_pow(89))
    p_kappa_179 = monomial_compose(p_alpha_179, 179)

    report(
        "P_alpha_5",
        p_alpha_5,
        4,
        3,
        "ab897fbdedfa502b2d839b6a56100887dccdc507555c282e59589e06300a62e2",
    )
    report(
        "P_alpha_11",
        p_alpha_11,
        20,
        5,
        "f45955b3fdc3158064b4fefe89e2f63179f4dfcf2ef2b19a6c02bfa63da528f1",
    )
    report(
        "P_alpha_89",
        p_alpha_89,
        220,
        55,
        "128101f817d3f442edb6c1362796c850d871a1eca9ac80123a2376179fc0fbf9",
    )
    report(
        "P_alpha_179",
        p_alpha_179,
        19_580,
        3_447,
        "888b8cd5d208a042c1deaee2cc13844cbfa49eaa352fbd85543dd13326182a33",
    )
    report(
        "P_kappa_179",
        p_kappa_179,
        3_504_820,
        3_447,
        "7f1d6d5cb36c2c233b5b67282540ef1a238f0b2374b81171e9b726cc2c559978",
    )
    print(
        "certificate_field: degree=179, modulus="
        f"{certificate_field_modulus:#x}, rabin=ok"
    )


if __name__ == "__main__":
    main()
