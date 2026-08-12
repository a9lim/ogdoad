#!/usr/bin/env python3
"""Verify the compact Hilbert-root certificate for the selected p=359 row.

The v1 artifact is a raw little-endian bitstream. Bit 179*i+j is the
coefficient of z^j in y_i for

    y = sum_(i=0)^19579 y_i A^i

in

    k = F_2[z]/(z^179 + z^4 + z^2 + z + 1),
    E = k[A]/(F_179(A)).

Quick mode checks the artifact hash, reconstructs the selected polynomial,
proves y^179=A, and verifies the stored nontrivial 359-phase and trace bit.
It deliberately does not link the stored theta to y. Authoritative full mode
additionally recomputes

    theta = Res_A(F_179(A), 1+y(A)) = Norm_(E/k)(1+y)

and therefore verifies the complete certificate. Full mode takes roughly ten
minutes and about 1.2 GiB with python-flint 0.9.0.

Install the project research extra before running:

    uv pip install -e '.[excess-certificate]'
    python experiments/ordinary_359_hilbert_certificate.py --full
"""

from __future__ import annotations

import argparse
import hashlib
import math
import time
from collections.abc import Iterator
from pathlib import Path
from typing import Any

try:
    import flint
    from flint import fq_default_poly_ctx, nmod_poly
except ModuleNotFoundError as error:
    raise SystemExit(
        "python-flint 0.9.0 is required; install the project "
        "excess-certificate extra or run with "
        "'uv run --no-project --with python-flint==0.9.0 python ...'"
    ) from error

if flint.__version__ != "0.9.0":
    raise SystemExit(f"expected python-flint 0.9.0, found {flint.__version__}")
if not __debug__:
    raise SystemExit("assertions must remain enabled; do not run with python -O")


R = 179
D = 19_580
H_BITS = (1 << 179) | (1 << 4) | (1 << 2) | (1 << 1) | 1
ROOT_BYTES = (R * D + 7) // 8
ROOT_SHA256 = "c62433e428e6b0942c210b2df2543fcff6a9e444b835ceb5390db1c9e433bd9e"
THETA_MASK = 0x28494A54795638CF203B2404FE5133E2AE0E13C2CA4E6
PHASE_MASK = 0x7F81A92C0C3B04E42A5D3AA423E1BC4D0082A3522E87E
DEFAULT_ROOT = (
    Path(__file__).parent
    / "certificates"
    / "ordinary_359_hilbert_root_v1.bin"
)


def support(poly: int) -> Iterator[int]:
    """Yield the set-bit positions of a bit-packed binary polynomial."""

    while poly:
        low = poly & -poly
        yield low.bit_length() - 1
        poly ^= low


def sparse_mul(poly: int, factor: int) -> int:
    """Multiply binary polynomials when factor is sparse."""

    out = 0
    for exponent in support(factor):
        out ^= poly << exponent
    return out


def compose_sparse(poly: int, inner: int) -> int:
    """Compose two bit-packed binary polynomials by Horner evaluation."""

    out = 0
    for exponent in range(poly.bit_length() - 1, -1, -1):
        out = sparse_mul(out, inner)
        if (poly >> exponent) & 1:
            out ^= 1
    return out


def one_plus_x_pow(exponent: int) -> int:
    """Return the bit polynomial (1+X)^exponent in characteristic two."""

    out = 0
    submask = exponent
    while True:
        out |= 1 << submask
        if submask == 0:
            return out
        submask = (submask - 1) & exponent


def modulus_bits() -> int:
    """Construct the selected degree-19,580 polynomial F_179."""

    f5 = (1 << 4) | (1 << 1) | 1
    f11 = compose_sparse(f5, one_plus_x_pow(5))
    f89 = compose_sparse(f11, one_plus_x_pow(11))
    return compose_sparse(f89, one_plus_x_pow(89))


def polynomial_from_bits(bits: int) -> nmod_poly:
    """Convert a bit-packed binary polynomial to a FLINT polynomial."""

    coefficients = [0] * bits.bit_length()
    for exponent in support(bits):
        coefficients[exponent] = 1
    return nmod_poly(coefficients, 2)


def field_element_from_mask(field: Any, mask: int) -> Any:
    """Convert a 179-bit mask to the deterministic coefficient field."""

    coefficients = [0] * max(1, mask.bit_length())
    for exponent in support(mask):
        coefficients[exponent] = 1
    return field(coefficients)


def mask_from_field_element(element: Any) -> int:
    """Return the little-endian polynomial-basis mask of a field element."""

    out = 0
    for exponent, coefficient in enumerate(element.polynomial()):
        if coefficient:
            out |= 1 << exponent
    return out


def resultant_char2(
    f: Any, g: Any, field: Any, started: float
) -> tuple[Any, int]:
    """Compute Res(f,g) by the Euclidean recurrence in characteristic two."""

    accumulator = field.one()
    steps = 0
    while g.degree() > 0:
        degree_f = f.degree()
        remainder = f % g
        if remainder.is_zero():
            return field.zero(), steps
        degree_remainder = remainder.degree()
        accumulator *= g.leading_coefficient() ** (
            degree_f - degree_remainder
        )
        f, g = g, remainder
        steps += 1
        if steps % 1000 == 0:
            print(
                "resultant",
                steps,
                f.degree(),
                g.degree(),
                time.monotonic() - started,
                flush=True,
            )
    accumulator *= g.constant_coefficient() ** f.degree()
    return accumulator, steps


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", nargs="?", type=Path, default=DEFAULT_ROOT)
    parser.add_argument(
        "--full",
        action="store_true",
        help="recompute Res_A(F_179,1+y); quick mode does not link theta to y",
    )
    args = parser.parse_args()
    started = time.monotonic()
    assert math.gcd(R, D) == 1

    payload = args.root.read_bytes()
    assert len(payload) == ROOT_BYTES
    assert hashlib.sha256(payload).hexdigest() == ROOT_SHA256
    packed = int.from_bytes(payload, "little")

    ring = fq_default_poly_ctx(2, R)
    field = ring.base_field()
    assert str(field.modulus()) == "x^179 + x^4 + x^2 + x + 1"
    h = polynomial_from_bits(H_BITS)
    h_unit, h_factors = h.factor()
    assert int(h_unit) == 1 and h_factors == [(h, 1)]
    coefficient_mask = (1 << R) - 1
    y = ring(
        [
            field_element_from_mask(
                field, (packed >> (R * i)) & coefficient_mask
            )
            for i in range(D)
        ]
    )
    f_binary = polynomial_from_bits(modulus_bits())
    f = ring([int(coefficient) for coefficient in f_binary])
    assert f.degree() == D
    assert y.pow_mod(R, f) == ring.gen()
    print("root verified", y.degree(), time.monotonic() - started, flush=True)

    stored_theta = field_element_from_mask(field, THETA_MASK)
    phase = field_element_from_mask(field, PHASE_MASK)
    assert stored_theta ** ((2**R - 1) // 359) == phase
    assert phase != 1
    assert phase**359 == 1
    traced = field.zero()
    trace_term = phase + phase**358
    for _ in range(R):
        traced += trace_term
        trace_term **= 2
    assert traced == 1
    print(
        "stored theta/phase verified",
        "phase-mask",
        hex(PHASE_MASK),
        "nontrivial",
        phase != 1,
        "safe-prime-trace",
        int(traced),
        time.monotonic() - started,
        flush=True,
    )

    if not args.full:
        print("quick mode: theta=Norm(1+y) not recomputed", flush=True)
        return

    f_unit, f_factors = f_binary.factor()
    assert int(f_unit) == 1 and f_factors == [(f_binary, 1)]
    print("F_179 irreducible over F_2", time.monotonic() - started, flush=True)
    theta, steps = resultant_char2(f, y + 1, field, started)
    theta_mask = mask_from_field_element(theta)
    assert theta_mask == THETA_MASK
    print(
        "theta-mask",
        hex(theta_mask),
        "phase-mask",
        hex(PHASE_MASK),
        "steps",
        steps,
        "nontrivial",
        phase != 1,
        "safe-prime-trace",
        int(traced),
        "seconds",
        time.monotonic() - started,
        flush=True,
    )


if __name__ == "__main__":
    main()
