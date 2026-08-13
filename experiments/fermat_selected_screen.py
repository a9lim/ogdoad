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
in ``F_2[X] / (A_(n-1))``.  The default ``stdlib`` backend represents
polynomials by Python-integer coefficient bits, with exact carryless Karatsuba
and a precomputed four-bit reduction table.  The optional ``flint`` backend is
the same computation in python-flint's ``FQ_NMOD`` finite field and is intended
for the larger published-factor screens.  A dependency-free invocation of the
latter is, for example,

    uv run --no-project --with python-flint python \
      experiments/fermat_selected_screen.py --backend flint \
      --flint-threads 4 --level 14 \
      --factor 116928085873074369829035993834596371340386703423373313

This is a falsification/primary-coordinate harness, not a proof of all-level
maximality.  The paper and Lean ledger retain that boundary explicitly.
The dependency-free ``--jet-only`` mode skips field construction and evaluates
the paper's factor-sensitive arithmetic obstruction for the first Hasse jet
not forced by the selected quotient residue.  That is a conditional higher-jet
screen, not a substitute for the primary-coordinate computation.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib
import math
import time
from dataclasses import dataclass
from typing import Any


FERMATSEARCH_FACTOR_URL = "https://www.fermatsearch.org/factors/faclist.php"

# Published prime factors on the FermatSearch current-factor table, accessed
# 2026-08-11.  Every listed level is incompletely factored, so passing its
# published coordinates does not prove the level.
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
    14: (
        116_928_085_873_074_369_829_035_993_834_596_371_340_386_703_423_373_313,
    ),
    15: (
        1_214_251_009,
        2_327_042_503_868_417,
        168_768_817_029_516_972_383_024_127_016_961,
    ),
    16: (
        825_753_601,
        188_981_757_975_021_318_420_037_633,
    ),
    17: (
        31_065_037_602_817,
        7_751_061_099_802_522_589_358_967_058_392_886_922_693_580_423_169,
    ),
    18: (
        13_631_489,
        81_274_690_703_860_512_587_777,
    ),
}


@dataclass(frozen=True)
class FactorSensitiveJetScreen:
    """Cheap arithmetic obstruction for the first uncollapsed Hasse jet.

    Conditional on the hypothetical primary failure, the odd branch can
    vanish only if the unknown selected order divides ``arithmetic_gcd``.
    Thus gcd one certifies that higher jet nonzero under failure.  This is not
    the selected Fibonacci residue test and cannot certify maximal order.
    """

    valuation: int
    block: int
    reduced_quotient: int
    half_index_parity: str
    odd_collision_gcd: int
    arithmetic_gcd: int
    nonzero_by_arithmetic: bool


def factor_sensitive_jet_screen(
    level: int, factor: int
) -> FactorSensitiveJetScreen:
    """Return the exact factor-sensitive order-``2R`` jet pre-screen."""

    if level < 2:
        raise ValueError("the factor-sensitive jet screen requires level >= 2")
    fermat_number = (1 << (1 << level)) + 1
    quotient, remainder = divmod(fermat_number, factor)
    if factor <= 1 or factor >= fermat_number or remainder:
        raise ValueError(f"{factor} is not a proper divisor of F_{level}")

    valuation = ((factor - 1) & -(factor - 1)).bit_length() - 1
    block = 1 << valuation
    reduced_quotient, reduced_remainder = divmod(quotient - 1, block)
    if reduced_remainder or reduced_quotient % 2 == 0:
        raise AssertionError("Fermat quotient has the wrong extracted 2-adic block")

    half_index = (reduced_quotient - 1) // 2
    half_index_parity = "odd" if half_index % 2 else "even"
    odd_collision_gcd = math.gcd(quotient, 3 * block + 1)
    multiplier = 3 if half_index_parity == "odd" else 1
    arithmetic_gcd = math.gcd(quotient, multiplier * block + 1)
    if half_index_parity == "odd":
        exponent_gap = (1 << level) - valuation
        alternate_gcd = math.gcd(quotient, (1 << exponent_gap) - 3)
        if alternate_gcd != odd_collision_gcd:
            raise AssertionError("the two odd-branch collision forms disagree")
    return FactorSensitiveJetScreen(
        valuation=valuation,
        block=block,
        reduced_quotient=reduced_quotient,
        half_index_parity=half_index_parity,
        odd_collision_gcd=odd_collision_gcd,
        arithmetic_gcd=arithmetic_gcd,
        nonzero_by_arithmetic=arithmetic_gcd == 1,
    )


def print_factor_sensitive_jet_screen(level: int, factor: int) -> None:
    """Print the fast arithmetic jet screen without finite-field arithmetic."""

    result = factor_sensitive_jet_screen(level, factor)
    print(f"level={level}")
    print(f"factor={factor}")
    print(f"jet_factor_valuation={result.valuation}")
    print(f"jet_block={result.block}")
    print(f"jet_half_index_parity={result.half_index_parity}")
    print(f"jet_odd_collision_gcd={result.odd_collision_gcd}")
    print(f"jet_arithmetic_gcd={result.arithmetic_gcd}")
    print(
        "jet_nonzero_under_failure_by_arithmetic="
        f"{result.nonzero_by_arithmetic}"
    )


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


def poly_remainder(dividend: int, divisor: int) -> int:
    """Return the exact remainder in ``F_2[X]``."""

    if divisor == 0:
        raise ZeroDivisionError("polynomial division by zero")
    divisor_degree = divisor.bit_length() - 1
    while dividend and dividend.bit_length() - 1 >= divisor_degree:
        dividend ^= divisor << (dividend.bit_length() - 1 - divisor_degree)
    return dividend


def poly_gcd(left: int, right: int) -> int:
    """Return the monic gcd in ``F_2[X]``."""

    while right:
        left, right = right, poly_remainder(left, right)
    return left


def is_irreducible_binary(poly: int) -> bool:
    """Rabin irreducibility test for a monic binary polynomial."""

    degree = poly.bit_length() - 1
    if degree <= 0 or (poly >> degree) != 1:
        return False
    reducer = BinaryFieldReducer.build(poly)
    x = 2
    powers = [x]
    for _ in range(degree):
        powers.append(reducer.square(powers[-1]))
    if powers[degree] != x:
        return False
    prime_divisors = {
        prime
        for prime in range(2, degree + 1)
        if degree % prime == 0
        and all(prime % divisor for divisor in range(2, math.isqrt(prime) + 1))
    }
    return all(
        poly_gcd(poly, powers[degree // prime] ^ x) == 1
        for prime in prime_divisors
    )


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


def _flint_element_to_int(value: Any) -> int:
    """Return the coefficient-bit encoding of a python-flint field element."""

    poly = value.polynomial()
    result = 0
    for exponent in range(len(poly)):
        if int(poly[exponent]):
            result |= 1 << exponent
    return result


def fibonacci_residue_flint(
    index: int, modulus: int, threads: int = 1
) -> tuple[int, int, float]:
    """Evaluate the recurrence in python-flint's exact ``FQ_NMOD`` backend."""

    if index < 0:
        raise ValueError("index must be nonnegative")
    if threads < 1:
        raise ValueError("threads must be positive")
    try:
        flint = importlib.import_module("flint")
    except ModuleNotFoundError as error:
        raise RuntimeError(
            "the flint backend requires python-flint; run with "
            "`uv run --no-project --with python-flint python ...`"
        ) from error
    flint.ctx.threads = threads

    prepared_at = time.perf_counter()
    polynomial_ring = flint.fmpz_mod_poly_ctx(2)
    modulus_poly = polynomial_ring(
        [(modulus >> exponent) & 1 for exponent in range(modulus.bit_length())]
    )
    field = flint.fq_default_ctx(
        modulus=modulus_poly,
        var="a",
        fq_type="FQ_NMOD",
        check_modulus=False,
    )
    preparation_seconds = time.perf_counter() - prepared_at

    generator = field.gen()
    current = field.zero()
    following = field.one()
    for bit in bin(index)[2:]:
        current_square = current.square()
        following_square = following.square()
        middle = following_square + generator * current_square
        if bit == "0":
            current, following = current_square, middle
        else:
            current, following = middle, following_square
    return (
        _flint_element_to_int(current),
        _flint_element_to_int(following),
        preparation_seconds,
    )


def residue_hash(value: int) -> str:
    payload = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    return hashlib.sha256(payload).hexdigest()


def screen(
    level: int,
    factor: int,
    backend: str = "stdlib",
    flint_threads: int = 1,
) -> int:
    """Run one exact selected residue screen and print a reproducible fingerprint."""

    if level < 1:
        raise ValueError("level must be at least one")
    fermat_number = (1 << (1 << level)) + 1
    quotient, remainder = divmod(fermat_number, factor)
    if factor <= 1 or remainder:
        raise ValueError(f"{factor} does not divide F_{level}")

    jet_screen = (
        factor_sensitive_jet_screen(level, factor)
        if level >= 2 and factor < fermat_number
        else None
    )

    started = time.perf_counter()
    modulus = selected_minimal_polynomial(level)
    built = time.perf_counter()
    expected_degree = 1 << level
    if modulus.bit_length() - 1 != expected_degree:
        raise AssertionError("selected resultant has the wrong degree")
    if backend == "stdlib":
        field = BinaryFieldReducer.build(modulus)
        prepared = time.perf_counter()
        preparation_seconds = prepared - built
        residue, successor = fibonacci_residue(quotient, field)
    elif backend == "flint":
        residue, successor, preparation_seconds = fibonacci_residue_flint(
            quotient, modulus, flint_threads
        )
        prepared = built + preparation_seconds
    else:
        raise ValueError(f"unknown backend: {backend}")
    finished = time.perf_counter()

    print(f"backend={backend}")
    if backend == "flint":
        print(f"flint_threads={flint_threads}")
    print(f"level={level}")
    print(f"factor={factor}")
    print(f"factor_bits={factor.bit_length()}")
    print(f"quotient_bits={quotient.bit_length()}")
    print(f"jet_screen_applicable={jet_screen is not None}")
    if jet_screen is not None:
        print(f"jet_factor_valuation={jet_screen.valuation}")
        print(f"jet_half_index_parity={jet_screen.half_index_parity}")
        print(f"jet_odd_collision_gcd={jet_screen.odd_collision_gcd}")
        print(f"jet_arithmetic_gcd={jet_screen.arithmetic_gcd}")
        print(
            "jet_nonzero_under_failure_by_arithmetic="
            f"{jet_screen.nonzero_by_arithmetic}"
        )
    print(f"modulus_degree={expected_degree}")
    print(f"modulus_weight={modulus.bit_count()}")
    print(f"residue_nonzero={residue != 0}")
    print(f"residue_degree={residue.bit_length() - 1 if residue else -1}")
    print(f"residue_sha256={residue_hash(residue)}")
    print(f"successor_nonzero={successor != 0}")
    print(f"successor_degree={successor.bit_length() - 1 if successor else -1}")
    print(f"successor_sha256={residue_hash(successor)}")
    print(f"build_seconds={built - started:.6f}")
    print(f"prepare_seconds={preparation_seconds:.6f}")
    print(f"residue_seconds={finished - prepared:.6f}")
    print(f"total_seconds={finished - started:.6f}")
    return 0 if residue else 2


def screen_published(
    level: int,
    backend: str = "stdlib",
    flint_threads: int = 1,
    jet_only: bool = False,
) -> int:
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
        if jet_only:
            print_factor_sensitive_jet_screen(level, factor)
        else:
            status = max(status, screen(level, factor, backend, flint_threads))
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
        jet_screen = factor_sensitive_jet_screen(5, factor)
        if jet_screen.arithmetic_gcd != 1 or not jet_screen.nonzero_by_arithmetic:
            raise AssertionError(f"unexpected F_5 jet obstruction at factor {factor}")

    # A full marked parent conductor need not propagate to its deterministic
    # child.  The first parent is literal; the second is an ambient full-packet
    # factor with a proper child.  This is a route counterexample, not a
    # Conway-ancestry counterexample.
    parents = (0x18DCF, 0x18753)
    children = (0x1D05A9A3B, 0x1DC43DBCF)
    for parent, child in zip(parents, children, strict=True):
        if not is_irreducible_binary(parent):
            raise AssertionError(f"marked parent is reducible: {parent:#x}")
        actual_child = conway_resultant_step(parent)
        if actual_child != child:
            raise AssertionError(
                f"marked child mismatch: {actual_child:#x} != {child:#x}"
            )
        if not is_irreducible_binary(child):
            raise AssertionError(f"marked child is reducible: {child:#x}")

    expected_residues = (
        (0x88F2EF2C, 0x1F3C2614),
        (0xCAD49535, 0),
    )
    for child, expected_pair in zip(children, expected_residues, strict=True):
        field = BinaryFieldReducer.build(child)
        actual_pair = (
            fibonacci_residue(641, field)[0],
            fibonacci_residue(6_700_417, field)[0],
        )
        if actual_pair != expected_pair:
            raise AssertionError(
                f"marked child residue mismatch: {actual_pair} != {expected_pair}"
            )
        if fibonacci_residue((1 << 32) + 1, field)[0] != 0:
            raise AssertionError("marked child does not lie in the F_5 packet")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--level", type=int)
    parser.add_argument("--factor", type=int)
    parser.add_argument(
        "--backend",
        choices=("stdlib", "flint"),
        default="stdlib",
        help="exact arithmetic backend (default: stdlib)",
    )
    parser.add_argument(
        "--flint-threads",
        type=int,
        default=1,
        help="FLINT worker threads (default: 1; ignored by stdlib)",
    )
    parser.add_argument(
        "--published-level",
        type=int,
        help="screen the pinned, incomplete FermatSearch factor list",
    )
    parser.add_argument(
        "--jet-only",
        action="store_true",
        help="run only the fast factor-sensitive higher-jet arithmetic screen",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.flint_threads < 1:
        raise SystemExit("--flint-threads must be positive")
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
        return screen_published(
            args.published_level,
            args.backend,
            args.flint_threads,
            args.jet_only,
        )
    if args.level is None or args.factor is None:
        raise SystemExit("--level and --factor must be supplied together")
    if args.jet_only:
        print_factor_sensitive_jet_screen(args.level, args.factor)
        return 0
    return screen(args.level, args.factor, args.backend, args.flint_threads)


if __name__ == "__main__":
    raise SystemExit(main())
