#!/usr/bin/env python3
"""Verify the first compact payload for the crossed-tower p=719 reduction.

The artifact encodes an element ``a`` of

    B = F_(2^179)[A] / (F_179(A))

as a raw little-endian bitstream: bit ``179*i+j`` is the coefficient of
``z^j A^i``.  It is tied to the checked p=359 Hilbert-root certificate ``x``
by the exact relation

    a^359 = (1+x)/c,

where ``c`` is the canonical scalar derived from the certified nontrivial
359-phase.  This verifies the first of the two crossed-certificate payloads
in the paper.  It does not construct the minimal polynomial ``f_a``, the
inner norm ``W``, or the final 719-phase, so ``m_719=1`` remains open.

Run with the project research extra or an ephemeral exact dependency:

    uv run --no-project --with python-flint==0.9.0 python \
      experiments/ordinary_719_crossed_root_certificate.py

Pass ``--full-upstream`` to recompute the inherited p=359 resultant norm
before checking this payload.  Quick mode trusts that already checked link.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import time

import ordinary_359_hilbert_certificate as p359


S = 359
A_SHA256 = "c7385164fedcbb971ff2bb239ef9e0a0d1ccb81b16edd81eee2a139030ba8758"
DEFAULT_A = (
    Path(__file__).parent
    / "certificates"
    / "ordinary_719_crossed_359th_root_v1.bin"
)


def require(condition: bool, message: str) -> None:
    """Raise an explicit certificate failure even under unusual runners."""

    if not condition:
        raise AssertionError(message)


def decode_element(payload: bytes, ring: object, field: object) -> object:
    """Decode one canonical 179-by-19,580 coefficient bitstream."""

    bit_count = p359.R * p359.D
    require(len(payload) == (bit_count + 7) // 8, "wrong artifact length")
    packed = int.from_bytes(payload, "little")
    require(packed >> bit_count == 0, "nonzero artifact padding bits")
    coefficient_mask = (1 << p359.R) - 1
    return ring(
        [
            p359.field_element_from_mask(
                field, (packed >> (p359.R * index)) & coefficient_mask
            )
            for index in range(p359.D)
        ]
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact", type=Path, default=DEFAULT_A)
    parser.add_argument(
        "--full-upstream",
        action="store_true",
        help="recompute the inherited p=359 resultant norm",
    )
    args = parser.parse_args()

    started = time.monotonic()
    payload = args.artifact.read_bytes()
    require(hashlib.sha256(payload).hexdigest() == A_SHA256, "artifact hash mismatch")

    ring = p359.fq_default_poly_ctx(2, p359.R)
    field = ring.base_field()
    a = decode_element(payload, ring, field)
    modulus = ring(
        [int(coefficient) for coefficient in p359.polynomial_from_bits(p359.modulus_bits())]
    )

    root_payload = p359.DEFAULT_ROOT.read_bytes()
    require(
        hashlib.sha256(root_payload).hexdigest() == p359.ROOT_SHA256,
        "p=359 root artifact hash mismatch",
    )
    x = decode_element(root_payload, ring, field)

    eta = p359.field_element_from_mask(field, p359.PHASE_MASK)
    theta = p359.field_element_from_mask(field, p359.THETA_MASK)
    require(
        theta ** ((2**p359.R - 1) // S) == eta,
        "stored p=359 theta/phase link changed",
    )
    require(eta != field.one(), "certified 359-phase became trivial")
    require(eta**S == field.one(), "certified phase is not 359-torsion")
    m_mod_s = ((pow(2, p359.R * p359.D, S * S) - 1) // S) % S
    require(m_mod_s == 241, "crossed scalar exponent changed")
    require((241 * 216) % S == 1, "crossed scalar inverse changed")
    c = eta**216

    if args.full_upstream:
        binary_modulus = p359.polynomial_from_bits(p359.modulus_bits())
        unit, factors = binary_modulus.factor()
        require(
            int(unit) == 1 and factors == [(binary_modulus, 1)],
            "F_179 irreducibility check failed",
        )
        recomputed_theta, steps = p359.resultant_char2(
            modulus, x + 1, field, started
        )
        require(
            p359.mask_from_field_element(recomputed_theta) == p359.THETA_MASK,
            "recomputed p=359 norm differs from the stored theta",
        )
        print(f"full_upstream_resultant_steps={steps}")

    delta = (ring.one() + x) * ring(field.one() / c)
    a_to_s = a.pow_mod(S, modulus)
    require(a_to_s == delta, "a^359 does not equal (1+x)/c")
    require(ring(c) * a_to_s + 1 == x, "crossed reconstruction of x failed")
    require(x.pow_mod(p359.R, modulus) == ring.gen(), "p=359 root equation failed")

    print("p719 crossed 359th root: verified")
    print(f"artifact={args.artifact}")
    print(f"sha256={A_SHA256}")
    print(f"bytes={len(payload)}")
    print(f"representative_degree={a.degree()}")
    print(f"full_upstream={args.full_upstream}")
    print(f"seconds={time.monotonic() - started:.6f}")
    print("boundary=f_a, W, final 719-phase not computed")


if __name__ == "__main__":
    main()
