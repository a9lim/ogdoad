"""The Conway--Fermat chain beside Wiedemann's iterated quadratic tower.

In Conway's nimbers put ``c_n = 2^(2^n)``, so that
``c_n^2 + c_n = c_0 c_1 ... c_(n-1)`` and ``c_n`` generates
``E_n = F_(2^(2^(n+1)))`` over ``E_(n-1) = F_q`` with ``q = 2^(2^n)``.
Frobenius over ``F_q`` sends ``c_n`` to ``c_n + 1``, so ``z -> z^(q-1)``
identifies ``E_n^x / E_(n-1)^x`` with the norm-one torus of order
``F_n = q + 1`` and sends ``c_n`` to

    w_n = 1 + c_n^(-1),        w_n + w_n^(-1) = (c_0 ... c_(n-1))^(-1).

Arm ``Z`` of ``writeups/excess.tex`` on the Conway--Fermat chain asks whether
``w_n`` generates that torus.  Wiedemann's conjecture (Fibonacci Quart. 26(4),
1988) asks the same of ``x_n`` with ``x_0 + x_0^(-1) = 1`` and
``x_n + x_n^(-1) = x_(n-1)``.

This script checks, exactly and for ``n <= 5``:

* the displayed identities for ``w_n``;
* that ``w_n`` has full order ``F_n`` (``F_0, ..., F_4`` are prime and
  ``F_5 = 641 * 6700417``);
* whether ``w_n`` lies in the Frobenius orbit of Wiedemann's ``x_n`` (the
  orbit is the set of all compatible root choices; ``x_n^(-1)`` is in it);
* the relative-trace identity and the level-2 minimal polynomials used below.

Result: ``w_n`` and ``x_n`` are Frobenius-conjugate for ``n <= 2`` and not
for any ``n >= 3``.  The second half holds for every ``n``: with
``a_m = c_0 ... c_m`` one has ``Tr_(E_m/E_(m-1))(a_m^(-1)) = a_(m-1)^(-2)`` and
``Tr(w_n) = a_(n-1)^(-1)``, ``Tr(x_n) = x_(n-1)``.  Relative trace commutes
with absolute Frobenius, so conjugacy at level ``n >= 3`` would descend to
conjugacy of ``a_2^(-1)`` and ``x_2``, whose minimal polynomials differ.  The
agreement is levelwise only (``w_1 + w_1^(-1) = 3`` while ``w_0 = 2``).  The
towers are siblings; nothing here transfers an order theorem either way.
"""

from __future__ import annotations

from functools import lru_cache

MAX_LEVEL = 5
FERMAT_FACTORS = {0: [3], 1: [5], 2: [17], 3: [257], 4: [65537], 5: [641, 6700417]}


@lru_cache(maxsize=None)
def nim_mul(a: int, b: int) -> int:
    """Conway nim product by recursive Fermat-2-power splitting."""

    if a < 2 or b < 2:
        return a * b
    top = max(a, b)
    half = 1
    while (1 << (half << 1)) <= top:
        half <<= 1
    fermat = 1 << half
    a_hi, a_lo = divmod(a, fermat)
    b_hi, b_lo = divmod(b, fermat)
    hi = nim_mul(a_hi, b_hi)
    mid = nim_mul(a_hi, b_lo) ^ nim_mul(a_lo, b_hi)
    # fermat * fermat = fermat + fermat/2 in nim arithmetic.
    return ((hi ^ mid) * fermat) ^ nim_mul(a_lo, b_lo) ^ nim_mul(hi, fermat >> 1)


def nim_pow(a: int, exponent: int) -> int:
    result = 1
    while exponent:
        if exponent & 1:
            result = nim_mul(result, a)
        a = nim_mul(a, a)
        exponent >>= 1
    return result


def nim_inv(a: int, bits: int) -> int:
    return nim_pow(a, (1 << bits) - 2)


def frobenius_orbit(x: int, bits: int) -> set[int]:
    orbit, y = set(), x
    for _ in range(bits):
        orbit.add(y)
        y = nim_mul(y, y)
    return orbit


def solve_artin_schreier(t: int, bits: int) -> int:
    """Return ``u`` with ``u^2 + u = t`` in ``F_(2^bits)`` by F_2-linear algebra."""

    # Columns of the F_2-linear map u -> u^2 + u on the bit basis.
    columns = [nim_mul(1 << i, 1 << i) ^ (1 << i) for i in range(bits)]
    rows = []  # (pivot bit, image, preimage)
    for i, image in enumerate(columns):
        pre = 1 << i
        for pivot, r_img, r_pre in rows:
            if image >> pivot & 1:
                image ^= r_img
                pre ^= r_pre
        if image:
            rows.append((image.bit_length() - 1, image, pre))
    solution, target = 0, t
    for pivot, r_img, r_pre in rows:
        if target >> pivot & 1:
            target ^= r_img
            solution ^= r_pre
    if target:
        raise ValueError("t has nonzero absolute trace; no Artin-Schreier root")
    return solution


def minimal_polynomial(y: int, bits: int) -> list[int]:
    """Coefficients (low to high) of the minimal polynomial of ``y`` over F_2."""

    poly = [1]
    for z in frobenius_orbit(y, bits):
        nxt = [0] * (len(poly) + 1)
        for i, coefficient in enumerate(poly):
            nxt[i + 1] ^= coefficient
            nxt[i] ^= nim_mul(coefficient, z)
        poly = nxt
    assert all(c in (0, 1) for c in poly)
    return poly


def main() -> None:
    wiedemann = 2  # x_0 + x_0^(-1) = 1 in F_4
    assert nim_mul(wiedemann, wiedemann) ^ wiedemann == 1
    product = 1  # a_(n-1) = c_0 ... c_(n-1)
    for n in range(MAX_LEVEL + 1):
        q = 1 << (1 << n)
        bits = 1 << (n + 1)
        c = 1 << (1 << n)
        assert nim_pow(c, q) == c ^ 1
        w = nim_pow(c, q - 1)
        assert w == 1 ^ nim_inv(c, bits)
        assert w ^ nim_inv(w, bits) == nim_inv(product, bits)
        fermat = q + 1
        assert nim_pow(w, fermat) == 1
        full_order = all(nim_pow(w, fermat // p) != 1 for p in FERMAT_FACTORS[n])

        previous = wiedemann
        if n > 0:
            # x_n = x_(n-1) u with u^2 + u = x_(n-1)^(-2).
            u = solve_artin_schreier(nim_inv(nim_mul(previous, previous), bits), bits)
            wiedemann = nim_mul(previous, u)
            assert wiedemann ^ nim_inv(wiedemann, bits) == previous
        conjugate = w in frobenius_orbit(wiedemann, bits)
        print(
            f"n={n}: ord(w_n) = F_n: {full_order}; "
            f"w_n Frobenius-conjugate to Wiedemann x_n: {conjugate}"
        )

        # Tr_(E_n/E_(n-1))(a_n^(-1)) = a_(n-1)^(-2).
        a_n = nim_mul(product, c)
        a_inv = nim_inv(a_n, bits)
        assert a_inv ^ nim_pow(a_inv, q) == nim_inv(nim_mul(product, product), bits)
        if n == 2:
            level_two = (a_n, wiedemann)
        product = a_n

    a2, x2 = level_two
    assert minimal_polynomial(nim_inv(a2, 8), 8) != minimal_polynomial(x2, 8)
    print("level 2: minpoly(a_2^-1) != minpoly(x_2), so nonconjugacy holds for every n >= 3")


if __name__ == "__main__":
    main()
