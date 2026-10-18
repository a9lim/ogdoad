"""The Conway--Fermat chain beside Wiedemann's iterated quadratic tower.

In Conway's nimbers put ``c_n = 2^(2^n)`` and ``a_n = c_0 c_1 ... c_n``, so
that ``c_n^2 + c_n = a_(n-1)`` and ``E_n = F_(2^(2^(n+1)))``.  With
``q = |E_(n-1)|``, the map ``z -> z^(q-1)`` identifies ``E_n^x / E_(n-1)^x``
with the norm-one torus ``T_n`` of order ``F_n`` and sends ``c_n`` to

    u_n = (c_n + 1) / c_n,        u_n + u_n^(-1) = a_(n-1)^(-1).

Arm ``Z`` of ``writeups/excess.tex`` on this chain asks whether ``u_n``
generates ``T_n``.  Wiedemann's question asks the same of ``x_n``, where
``x_(-1) = 1`` and ``x_m + x_m^(-1) = x_(m-1)``.  This script checks, exactly
and in the nimber field, the claims of the paper's subsection "Wiedemann's
sibling tower":

* both ``(a_m)`` and ``(x_m)`` have relative trace equal to the previous
  coordinate, with relative norms ``a_(m-1)^3`` and ``1``;
* ``u_n`` and ``x_n`` are Frobenius-conjugate exactly for ``n <= 2``
  (the proof: ``N(a_(n-1)) = a_(n-2)^3 != 1`` for ``n >= 3``), and
  ``ord(a_2) = 85`` while ``ord(x_2) = 17``;
* on the ordinary curve ``y^2 + xy = x^3 + 1`` the Verschiebung acts on
  abscissas by ``x -> x + 1/x``; a point ``Q_n`` with abscissa ``x_n`` is
  rational over ``E_n``, has exact order ``2^(n+3)``, and every odd
  multiple ``[k]Q_n`` has abscissa a Frobenius conjugate of ``x_n``;
* on the supersingular curve ``y^2 + y = x^3 + x^2`` the point
  ``P_n = (c_n, c_(n+1))`` has ``iota P_n = (+-h) P_n`` with
  ``h = 2^(2^(n-1))``, its order is ``F_n`` for ``2 <= n <= 6``, the odd
  multipliers acting on ``<P_n>`` as Frobenius powers are exactly the
  elements of ``H_n = <2> u (h+1)<2>`` modulo ``F_n``, and no two odd
  integers below ``sqrt(h/2)`` differ by a factor in ``H_n`` (while ``9``
  and ``13`` do at ``n = 3``).

As a diagnostic it also prints, for ``3 <= n <= 5``, the least absolute
residue of ``k * 2^j`` where ``u_n = x_n^k``; it is of the size expected for
an unrelated element, so no small monomial relation links the towers there.
"""

from __future__ import annotations

from functools import lru_cache
from math import isqrt

MAX_LEVEL = 5
CONWAY_ORDER_LEVELS = range(2, 7)
FERMAT_FACTORS = {
    0: [3],
    1: [5],
    2: [17],
    3: [257],
    4: [65537],
    5: [641, 6700417],
    6: [274177, 67280421310721],
}


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


def multiplicative_order(x: int, group_order: int, primes: list[int]) -> int:
    order = group_order
    for p in primes:
        while order % p == 0 and nim_pow(x, order // p) == 1:
            order //= p
    return order


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


def wiedemann_tower(levels: int) -> list[int]:
    """Return ``x_0, ..., x_(levels-1)`` for one compatible root choice."""

    tower = [2]  # x_0 + x_0^(-1) = 1 in F_4
    for n in range(1, levels):
        bits = 1 << (n + 1)
        previous = tower[-1]
        # x_n = x_(n-1) v with v^2 + v = x_(n-1)^(-2).
        v = solve_artin_schreier(nim_inv(nim_mul(previous, previous), bits), bits)
        tower.append(nim_mul(previous, v))
    return tower


def ordinary_add(p, q, bits: int):
    """Chord law on ``y^2 + xy = x^3 + 1``; ``None`` is the origin."""

    if p is None:
        return q
    if q is None:
        return p
    (x1, y1), (x2, y2) = p, q
    if x1 == x2:
        if y1 ^ y2 == x1:  # q = -p, including the 2-torsion point (0, 1)
            return None
        slope = x1 ^ nim_mul(y1, nim_inv(x1, bits))
        x3 = nim_mul(slope, slope) ^ slope
        return x3, nim_mul(x1, x1) ^ nim_mul(slope ^ 1, x3)
    slope = nim_mul(y1 ^ y2, nim_inv(x1 ^ x2, bits))
    x3 = nim_mul(slope, slope) ^ slope ^ x1 ^ x2
    return x3, nim_mul(slope, x1 ^ x3) ^ x3 ^ y1


def supersingular_add(p, q, bits: int):
    """Chord law on ``y^2 + y = x^3 + x^2``; ``None`` is the origin."""

    if p is None:
        return q
    if q is None:
        return p
    (x1, y1), (x2, y2) = p, q
    if x1 == x2:
        if y1 ^ y2 == 1:  # q = -p
            return None
        slope = nim_mul(x1, x1)
    else:
        slope = nim_mul(y1 ^ y2, nim_inv(x1 ^ x2, bits))
    x3 = nim_mul(slope, slope) ^ 1 ^ x1 ^ x2
    return x3, nim_mul(slope, x3) ^ y1 ^ nim_mul(slope, x1) ^ 1


def multiple(k: int, point, bits: int, add):
    result = None
    while k:
        if k & 1:
            result = add(result, point, bits)
        point = add(point, point, bits)
        k >>= 1
    return result


def frobenius_point(point, bits: int):
    return nim_mul(point[0], point[0]), nim_mul(point[1], point[1])


def thin_multipliers(level: int) -> set[int]:
    """``H_n = <2> u (h+1)<2>`` modulo ``F_n``."""

    fermat = (1 << (1 << level)) + 1
    h = 1 << (1 << (level - 1))
    powers = {pow(2, b, fermat) for b in range(1 << (level + 1))}
    return powers | {(h + 1) * power % fermat for power in powers}


def check_coset_separation() -> None:
    for n in CONWAY_ORDER_LEVELS:
        fermat = (1 << (1 << n)) + 1
        subgroup = sorted(thin_multipliers(n))
        assert len(subgroup) == 1 << (n + 2)
        bound = isqrt((1 << (1 << (n - 1))) // 2)
        labels = [min(k * x % fermat for x in subgroup) for k in range(1, bound + 1, 2)]
        assert len(set(labels)) == len(labels)
        print(f"n={n}: no two odd integers below sqrt(h/2) = {bound} differ by a factor in H_n")
    subgroup = thin_multipliers(3)
    assert 13 * pow(9, -1, 257) % 257 in subgroup


def check_traces_and_conjugacy(wiedemann: list[int]) -> None:
    a_previous = x_previous = 1  # a_(-1) = x_(-1) = 1
    a_before = 1  # a_(n-2), with a_(-2) taken as 1
    for n in range(MAX_LEVEL + 1):
        bits, q = 1 << (n + 1), 1 << (1 << n)
        c = 1 << (1 << n)
        a, x = nim_mul(a_previous, c), wiedemann[n]

        def relative(z: int) -> tuple[int, int]:
            conjugate = nim_pow(z, q)
            return z ^ conjugate, nim_mul(z, conjugate)

        assert relative(a) == (a_previous, nim_pow(a_previous, 3))
        assert relative(x) == (x_previous, 1)
        u = nim_pow(c, q - 1)
        assert u == nim_pow(a, q - 1) == nim_mul(c ^ 1, nim_inv(c, bits))
        assert u ^ nim_inv(u, bits) == nim_inv(a_previous, bits)
        assert nim_pow(x, q - 1) == nim_inv(nim_mul(x, x), bits)
        full_order = multiplicative_order(u, q + 1, FERMAT_FACTORS[n]) == q + 1
        conjugate = u in frobenius_orbit(x, bits)
        assert conjugate == (n <= 2)
        cube_one = nim_pow(a_before, 3) == 1
        assert cube_one == (n <= 2)
        print(
            f"n={n}: ord(u_n) = F_n: {full_order}; u_n conjugate to x_n: "
            f"{conjugate}; N(a_(n-1)) = a_(n-2)^3 is 1: {cube_one}"
        )
        a_before, a_previous, x_previous = a_previous, a, x

    a_2 = 2 * 4 * 16  # distinct Fermat 2-powers multiply as integers
    assert multiplicative_order(a_2, 255, [3, 5, 17]) == 85
    assert multiplicative_order(wiedemann[2], 255, [3, 5, 17]) == 17
    print("level 2: ord(a_2) = 85, ord(x_2) = 17")


def check_ordinary_realization(wiedemann: list[int]) -> None:
    for n in range(MAX_LEVEL + 1):
        bits = 1 << (n + 1)
        x = wiedemann[n]
        # y = x z with z^2 + z = x + x^(-2), solvable in E_n.
        z = solve_artin_schreier(x ^ nim_inv(nim_mul(x, x), bits), bits)
        point = (x, nim_mul(x, z))
        order = 1 << (n + 3)
        assert multiple(order, point, bits, ordinary_add) is None
        assert multiple(order >> 1, point, bits, ordinary_add) is not None
        # V = [2] o Frobenius^(-1) on geometric points.
        root = (nim_pow(point[0], 1 << (bits - 1)), nim_pow(point[1], 1 << (bits - 1)))
        image = ordinary_add(root, root, bits)
        assert image[0] == x ^ nim_inv(x, bits) == (wiedemann[n - 1] if n else 1)
        orbit = frobenius_orbit(x, bits)
        assert all(
            multiple(k, point, bits, ordinary_add)[0] in orbit
            for k in range(1, order, 2)
        )
        print(
            f"n={n}: Q_n in E'(E_n) has exact order 2^{n + 3}; x(V Q_n) = x_(n-1); "
            "every odd multiple has abscissa conjugate to x_n"
        )


def check_supersingular_thinness() -> None:
    for n in CONWAY_ORDER_LEVELS:
        bits = 1 << (n + 2)  # P_n is rational over E_(n+1)
        fermat = (1 << (1 << n)) + 1
        h = 1 << (1 << (n - 1))
        point = (1 << (1 << n), 1 << (1 << (n + 1)))
        x, y = point
        iota = (x ^ 1, y ^ x ^ 1)
        h_point = multiple(h, point, bits, supersingular_add)
        assert h_point in (iota, (iota[0], iota[1] ^ 1))
        order = fermat
        for p in FERMAT_FACTORS[n]:
            while order % p == 0 and multiple(order // p, point, bits, supersingular_add) is None:
                order //= p
        assert order == fermat
        line = f"n={n}: iota P_n = +-{h} P_n; ord(P_n) = F_n"
        if n <= 4:
            orbit, image = set(), point
            for _ in range(bits):
                orbit.add(image)
                orbit.add((image[0], image[1] ^ 1))
                image = frobenius_point(image, bits)
            frobenius_odd = {
                k
                for k in range(1, fermat, 2)
                if multiple(k, point, bits, supersingular_add) in orbit
            }
            expected = {k for k in thin_multipliers(n) if k % 2}
            assert frobenius_odd == expected
            smallest = min(frobenius_odd - {1})
            assert n == 2 or smallest == h - 1
            line += f"; odd Frobenius multipliers = H_n, smallest > 1: {smallest}"
        print(line)


def discrete_log(base: int, target: int, prime: int, bits: int) -> int:
    """Baby-step giant-step in a subgroup of prime order."""

    step = isqrt(prime) + 1
    table, value = {}, 1
    for j in range(step):
        table.setdefault(value, j)
        value = nim_mul(value, base)
    giant = nim_inv(nim_pow(base, step), bits)
    value = target
    for i in range(step + 1):
        if value in table:
            return (i * step + table[value]) % prime
        value = nim_mul(value, giant)
    raise ValueError("no discrete logarithm")


def print_monomial_screen(wiedemann: list[int]) -> None:
    for n in range(3, 6):
        q = 1 << (1 << n)
        fermat = q + 1
        u, x = nim_pow(1 << (1 << n), q - 1), wiedemann[n]
        residues, moduli = [], []
        for p in FERMAT_FACTORS[n]:
            residues.append(
                discrete_log(
                    nim_pow(x, fermat // p), nim_pow(u, fermat // p), p, 1 << (n + 1)
                )
            )
            moduli.append(p)
        k = 0
        for residue, modulus in zip(residues, moduli):
            rest = fermat // modulus
            k += residue * rest * pow(rest, -1, modulus)
        k %= fermat
        assert nim_pow(x, k) == u
        least = min(
            min(k * pow(2, j, fermat) % fermat, -k * pow(2, j, fermat) % fermat)
            for j in range(1 << (n + 1))
        )
        print(f"n={n}: u_n = x_n^k with least |k 2^j mod F_n| = {least}")


def main() -> None:
    wiedemann = wiedemann_tower(MAX_LEVEL + 1)
    check_traces_and_conjugacy(wiedemann)
    check_ordinary_realization(wiedemann)
    check_supersingular_thinness()
    check_coset_separation()
    print_monomial_screen(wiedemann)


if __name__ == "__main__":
    main()
