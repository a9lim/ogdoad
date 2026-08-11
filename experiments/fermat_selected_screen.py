#!/usr/bin/env python3
"""Exact selected-factor screen for the Conway--Fermat tower.

For a level ``n`` and a divisor ``ell`` of the Fermat number

    F_n = 2^(2^n) + 1,

this script computes the selected Fibonacci residue

    S_(F_n / ell)(a_(n-1))

in the literal Conway quadratic tower.  A zero is an exact counterexample to
full Popovych maximal order.  For a caller-supplied prime divisor, a nonzero
value certifies only that one primary test, not the level or universal
conjecture.  The script checks divisibility, not primality.

The implementation is independent of a precomputed Conway polynomial table.
It builds the selected minimal polynomial from

    A_-1(Y) = Y + 1,
    A_i(X) = Res_Y(A_(i-1)(Y), X^2 + X*Y + Y^3),

then evaluates the characteristic-two Fibonacci recurrence by fast doubling
in ``F_2[X] / (A_(n-1))``.  Polynomials are Python integers with coefficient
bits; multiplication is exact carryless Karatsuba and modular squaring uses a
precomputed four-bit reduction table.

This is a falsification/primary-coordinate harness, not a proof of all-level
maximality.  The paper and Lean ledger retain that boundary explicitly.
"""

from __future__ import annotations

import argparse
import hashlib
import time
from dataclasses import dataclass


FERMATSEARCH_FACTOR_URL = "https://www.fermatsearch.org/factors/composite.php"

# Published prime factors on the FermatSearch current-factor table, accessed
# 2026-08-11.  The remaining cofactors at both levels are composite and
# incompletely factored, so passing this list does not prove the level.
PUBLISHED_FACTORS = {
    12: (
        114_689,
        26_017_793,
        63_766_529,
        190_274_191_361,
        1_256_132_134_125_569,
        568_630_647_535_356_955_169_033_410_940_867_804_839_360_742_060_818_433,
    ),
    13: (
        2_710_954_639_361,
        2_663_848_877_152_141_313,
        3_603_109_844_542_291_969,
        319_546_020_820_551_643_220_672_513,
    ),
}


SQUARE_BYTE = tuple(
    sum(((value >> bit) & 1) << (2 * bit) for bit in range(8)) for value in range(256)
)


def poly_square(poly: int) -> int:
    """Square a binary polynomial represented by its coefficient bits."""

    if poly == 0:
        return 0
    source = poly.to_bytes((poly.bit_length() + 7) // 8, "little")
    target = bytearray(2 * len(source))
    for index, value in enumerate(source):
        spread = SQUARE_BYTE[value]
        target[2 * index] = spread & 0xFF
        target[2 * index + 1] = spread >> 8
    return int.from_bytes(target, "little")


def carryless_mul(left: int, right: int) -> int:
    """Multiply binary polynomials using exact carryless Karatsuba."""

    if left == 0 or right == 0:
        return 0
    width = max(left.bit_length(), right.bit_length())
    if width <= 96:
        if left.bit_count() < right.bit_count():
            left, right = right, left
        result = 0
        while right:
            low = right & -right
            result ^= left << (low.bit_length() - 1)
            right ^= low
        return result

    half = (width + 1) // 2
    mask = (1 << half) - 1
    left_low = left & mask
    left_high = left >> half
    right_low = right & mask
    right_high = right >> half
    low = carryless_mul(left_low, right_low)
    high = carryless_mul(left_high, right_high)
    middle = carryless_mul(left_low ^ left_high, right_low ^ right_high)
    return low ^ ((middle ^ low ^ high) << half) ^ (high << (2 * half))


def reduce_in_cubic(poly: int) -> tuple[int, int, int]:
    """Reduce ``poly(Y)`` modulo ``Y^3 + X*Y + X^2``.

    The returned integers are the binary polynomials ``u(X), v(X), w(X)``
    in ``u + v*Y + w*Y^2``.
    """

    u = v = w = 0
    for exponent in range(poly.bit_length() - 1, -1, -1):
        coefficient = (poly >> exponent) & 1
        u, v, w = (w << 2) ^ coefficient, u ^ (w << 1), v
    return u, v, w


def conway_resultant_step(poly: int) -> int:
    """Apply one exact selected Conway resultant step."""

    u, v, w = reduce_in_cubic(poly)
    u2 = poly_square(u)
    v2 = poly_square(v)
    w2 = poly_square(w)
    result = carryless_mul(u, u2)
    result ^= carryless_mul(u, v2) << 1
    result ^= carryless_mul(v, v2) << 2
    result ^= carryless_mul(u, w2) << 2
    result ^= carryless_mul(v, w2) << 3
    result ^= carryless_mul(carryless_mul(u, v), w) << 2
    result ^= carryless_mul(w, w2) << 4
    return result


def selected_minimal_polynomial(level: int) -> int:
    """Return the minimal polynomial of ``a_(level-1)`` over ``F_2``."""

    if level < 0:
        raise ValueError("level must be nonnegative")
    poly = 0b11  # A_-1(Y) = Y + 1.
    for _ in range(level):
        poly = conway_resultant_step(poly)
    return poly


@dataclass(frozen=True)
class BinaryFieldReducer:
    """Reduction and Frobenius in ``F_2[X] / (modulus)``."""

    modulus: int
    degree: int
    mask: int
    lower: int
    nibble_table: tuple[tuple[int, ...], ...]

    @classmethod
    def build(cls, modulus: int) -> BinaryFieldReducer:
        degree = modulus.bit_length() - 1
        if degree <= 0 or (modulus >> degree) != 1:
            raise ValueError("modulus must be monic of positive degree")
        mask = (1 << degree) - 1
        lower = modulus ^ (1 << degree)

        monomial_remainders: list[int] = []
        remainder = lower  # X^degree modulo the monic modulus.
        for _ in range(degree):
            monomial_remainders.append(remainder)
            top = (remainder >> (degree - 1)) & 1
            remainder = (remainder << 1) & mask
            if top:
                remainder ^= lower

        tables: list[tuple[int, ...]] = []
        for offset in range(0, degree, 4):
            basis = monomial_remainders[offset : offset + 4]
            values: list[int] = []
            for nibble in range(16):
                value = 0
                for bit, basis_value in enumerate(basis):
                    if (nibble >> bit) & 1:
                        value ^= basis_value
                values.append(value)
            tables.append(tuple(values))
        return cls(modulus, degree, mask, lower, tuple(tables))

    def reduce_double(self, poly: int) -> int:
        """Reduce a polynomial of degree below ``2 * degree``."""

        result = poly & self.mask
        high = poly >> self.degree
        index = 0
        while high:
            result ^= self.nibble_table[index][high & 0xF]
            high >>= 4
            index += 1
        return result

    def square(self, value: int) -> int:
        return self.reduce_double(poly_square(value))

    def mul_x(self, value: int) -> int:
        top = (value >> (self.degree - 1)) & 1
        result = (value << 1) & self.mask
        if top:
            result ^= self.lower
        return result


def fibonacci_residue(index: int, field: BinaryFieldReducer) -> tuple[int, int]:
    """Return ``(S_index(X), S_(index+1)(X))`` modulo the field polynomial."""

    if index < 0:
        raise ValueError("index must be nonnegative")
    current = 0
    following = 1
    for bit in bin(index)[2:]:
        current_square = field.square(current)
        following_square = field.square(following)
        middle = following_square ^ field.mul_x(current_square)
        if bit == "0":
            current, following = current_square, middle
        else:
            current, following = middle, following_square
    return current, following


def residue_hash(value: int) -> str:
    payload = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    return hashlib.sha256(payload).hexdigest()


def screen(level: int, factor: int) -> int:
    """Run one exact selected residue screen and print a reproducible fingerprint."""

    if level < 1:
        raise ValueError("level must be at least one")
    fermat_number = (1 << (1 << level)) + 1
    quotient, remainder = divmod(fermat_number, factor)
    if factor <= 1 or remainder:
        raise ValueError(f"{factor} does not divide F_{level}")

    started = time.perf_counter()
    modulus = selected_minimal_polynomial(level)
    built = time.perf_counter()
    expected_degree = 1 << level
    if modulus.bit_length() - 1 != expected_degree:
        raise AssertionError("selected resultant has the wrong degree")
    field = BinaryFieldReducer.build(modulus)
    prepared = time.perf_counter()
    residue, successor = fibonacci_residue(quotient, field)
    finished = time.perf_counter()

    print(f"level={level}")
    print(f"factor={factor}")
    print(f"factor_bits={factor.bit_length()}")
    print(f"quotient_bits={quotient.bit_length()}")
    print(f"modulus_degree={field.degree}")
    print(f"modulus_weight={modulus.bit_count()}")
    print(f"residue_nonzero={residue != 0}")
    print(f"residue_degree={residue.bit_length() - 1 if residue else -1}")
    print(f"residue_sha256={residue_hash(residue)}")
    print(f"successor_nonzero={successor != 0}")
    print(f"successor_degree={successor.bit_length() - 1 if successor else -1}")
    print(f"successor_sha256={residue_hash(successor)}")
    print(f"build_seconds={built - started:.6f}")
    print(f"table_seconds={prepared - built:.6f}")
    print(f"residue_seconds={finished - prepared:.6f}")
    print(f"total_seconds={finished - started:.6f}")
    return 0 if residue else 2


def screen_published(level: int) -> int:
    """Screen every currently published prime factor at a supported level."""

    factors = PUBLISHED_FACTORS.get(level)
    if factors is None:
        supported = ", ".join(map(str, sorted(PUBLISHED_FACTORS)))
        raise ValueError(f"no pinned factor list for level {level}; choose {supported}")

    print(f"factor_source={FERMATSEARCH_FACTOR_URL}")
    print("factor_list_complete=false")
    status = 0
    for position, factor in enumerate(factors, start=1):
        print(f"published_factor={position}/{len(factors)}")
        status = max(status, screen(level, factor))
    return status


def self_test() -> None:
    expected = {
        1: 0x1F,
        2: 0x1A3,
        3: 0x18DCF,
        4: 0x1D05A9A3B,
    }
    for index, value in expected.items():
        actual = selected_minimal_polynomial(index + 1)
        if actual != value:
            raise AssertionError(
                f"A_{index} orientation mismatch: {actual:#x} != {value:#x}"
            )

    # The first composite Fermat level must miss neither known prime factor.
    for factor in (641, 6_700_417):
        fermat = (1 << 32) + 1
        quotient = fermat // factor
        modulus = selected_minimal_polynomial(5)
        residue, _ = fibonacci_residue(quotient, BinaryFieldReducer.build(modulus))
        if residue == 0:
            raise AssertionError(f"unexpected F_5 failure at factor {factor}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--level", type=int)
    parser.add_argument("--factor", type=int)
    parser.add_argument(
        "--published-level",
        type=int,
        help="screen the pinned, incomplete FermatSearch factor list",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_test:
        self_test()
        print("self-test: ok")
        if args.level is None and args.factor is None and args.published_level is None:
            return 0
    if args.published_level is not None:
        if args.level is not None or args.factor is not None:
            raise SystemExit(
                "--published-level cannot be combined with --level/--factor"
            )
        return screen_published(args.published_level)
    if args.level is None or args.factor is None:
        raise SystemExit("--level and --factor must be supplied together")
    return screen(args.level, args.factor)


if __name__ == "__main__":
    raise SystemExit(main())
