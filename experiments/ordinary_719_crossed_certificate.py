#!/usr/bin/env python3
"""Verify the complete compact crossed-tower certificate for p=719.

The two 438,103-byte payloads encode ``a`` and the non-leading coefficients
of its monic minimal polynomial ``f_a`` over F_(2^179).  The optional 8,033-
byte payloads encode the crossed norm

    W = v^19580 f_a(v^-1)

and its nontrivial 719-Euler phase in
H = F_(2^179)[V]/(V^359+c).  Default mode recomputes the crossed root,
W, and the full phase, treating W and the phase payloads as checkpoints
rather than trusted inputs.  Authoritative full mode additionally establishes
that the stored polynomial is the selected root's minimal polynomial.

Install the project research extra before running:

    uv pip install -e '.[excess-certificate]'
    python experiments/ordinary_719_crossed_certificate.py

Authoritative ``--full`` mode additionally checks ``f_a(a)=0`` by dense modular
composition.  ``--full-upstream`` also recomputes the inherited p=359 norm.
The default mode takes roughly two minutes and 1.4 GiB with python-flint
0.9.0; full mode is substantially slower.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import time

import ordinary_359_hilbert_certificate as p359


R, D, S, P = p359.R, p359.D, 359, 719
Q = 1 << R
D_PAYLOAD_BYTES = (R * D + 7) // 8
H_PAYLOAD_BYTES = (R * S + 7) // 8
A_SHA256 = "c7385164fedcbb971ff2bb239ef9e0a0d1ccb81b16edd81eee2a139030ba8758"
F_A_SHA256 = "66a4aaa3a406d67bc9aba4ae56c9bc218f65d296d7c68725da6b1417854b92de"
W_SHA256 = "fc00d40eabdba738d950bf17317e68418d0b8813ba3325c1ce35b1975f9569c6"
PHASE_SHA256 = "da5858b2e53bfce7e83944a41e264a0fa01a3f0a1b030b889239afd383708a81"
CERTIFICATE_DIR = Path(__file__).parent / "certificates"
DEFAULT_A = CERTIFICATE_DIR / "ordinary_719_crossed_359th_root_v1.bin"
DEFAULT_F_A = CERTIFICATE_DIR / "ordinary_719_crossed_minpoly_v1.bin"
DEFAULT_W = CERTIFICATE_DIR / "ordinary_719_crossed_norm_v1.bin"
DEFAULT_PHASE = CERTIFICATE_DIR / "ordinary_719_crossed_phase_v1.bin"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def checked_payload(
    path: Path, size: int, meaningful_bits: int, digest: str
) -> bytes:
    payload = path.read_bytes()
    require(len(payload) == size, f"{path}: wrong artifact length")
    require(int.from_bytes(payload, "little") >> meaningful_bits == 0,
            f"{path}: nonzero padding bits")
    require(hashlib.sha256(payload).hexdigest() == digest,
            f"{path}: artifact hash mismatch")
    return payload


def decode_d_coefficients(payload: bytes, field: object) -> list[object]:
    require(len(payload) == D_PAYLOAD_BYTES, "wrong D-polynomial payload length")
    packed = int.from_bytes(payload, "little")
    require(packed >> (R * D) == 0, "nonzero D-polynomial padding bits")
    mask = (1 << R) - 1
    return [
        p359.field_element_from_mask(field, (packed >> (R * i)) & mask)
        for i in range(D)
    ]


def decode_d_element(payload: bytes, ring: object, field: object) -> object:
    return ring(decode_d_coefficients(payload, field))


def encode_h(element: object) -> bytes:
    packed = 0
    for i in range(element.degree() + 1):
        packed |= p359.mask_from_field_element(element[i]) << (R * i)
    require(packed.bit_length() <= R * S, "H element escaped its fixed basis")
    return packed.to_bytes(H_PAYLOAD_BYTES, "little")


def q_frobenius(element: object, kappa: object, ring: object) -> object:
    running = ring.base_field().one()
    coefficients = []
    for coefficient in element:
        coefficients.append(coefficient * running)
        running *= kappa
    return ring(coefficients)


def simultaneous_power(
    bases: list[object], exponents: list[int], modulus: object, ring: object,
    window: int = 7,
) -> object:
    """Exact bucketed simultaneous exponentiation in a commutative group."""

    require(len(bases) == len(exponents), "base/exponent length mismatch")
    result = ring.one()
    blocks = (max(e.bit_length() for e in exponents) + window - 1) // window
    digit_mask = (1 << window) - 1
    for block in range(blocks - 1, -1, -1):
        for _ in range(window):
            result = result.mul_mod(result, modulus)
        buckets: list[object | None] = [None] * (1 << window)
        shift = block * window
        for base, exponent in zip(bases, exponents, strict=True):
            digit = (exponent >> shift) & digit_mask
            if digit:
                previous = buckets[digit]
                buckets[digit] = (
                    base if previous is None else previous.mul_mod(base, modulus)
                )
        running = ring.one()
        for digit in range(digit_mask, 0, -1):
            if buckets[digit] is not None:
                running = running.mul_mod(buckets[digit], modulus)
            result = result.mul_mod(running, modulus)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--a", type=Path, default=DEFAULT_A)
    parser.add_argument("--f-a", type=Path, default=DEFAULT_F_A)
    parser.add_argument("--w", type=Path, default=DEFAULT_W)
    parser.add_argument("--phase", type=Path, default=DEFAULT_PHASE)
    parser.add_argument(
        "--full",
        action="store_true",
        help="also prove f_a(a)=0 by dense modular composition",
    )
    parser.add_argument(
        "--full-upstream",
        action="store_true",
        help="also recompute the inherited p=359 resultant norm; implies --full",
    )
    args = parser.parse_args()
    started = time.monotonic()

    a_payload = checked_payload(
        args.a, D_PAYLOAD_BYTES, R * D, A_SHA256
    )
    f_a_payload = checked_payload(
        args.f_a, D_PAYLOAD_BYTES, R * D, F_A_SHA256
    )
    stored_w = checked_payload(args.w, H_PAYLOAD_BYTES, R * S, W_SHA256)
    stored_phase = checked_payload(
        args.phase, H_PAYLOAD_BYTES, R * S, PHASE_SHA256
    )

    ring = p359.fq_default_poly_ctx(2, R)
    field = ring.base_field()
    binary_modulus = p359.polynomial_from_bits(p359.modulus_bits())
    modulus = ring([int(coefficient) for coefficient in binary_modulus])
    a = decode_d_element(a_payload, ring, field)
    f_a_coefficients = decode_d_coefficients(f_a_payload, field)

    root_payload = checked_payload(
        p359.DEFAULT_ROOT,
        D_PAYLOAD_BYTES,
        R * D,
        p359.ROOT_SHA256,
    )
    x = decode_d_element(root_payload, ring, field)
    theta = p359.field_element_from_mask(field, p359.THETA_MASK)
    eta = p359.field_element_from_mask(field, p359.PHASE_MASK)
    require(theta ** ((Q - 1) // S) == eta,
            "stored p=359 theta/phase link changed")
    require(eta != field.one() and eta**S == field.one(),
            "stored p=359 phase has wrong order")
    # This is the canonical crossed-tower correction.  For
    # M=(2^(179*19580)-1)/359, M=241 mod 359 and 216=241^(-1).
    m_mod_s = ((pow(2, R * D, S * S) - 1) // S) % S
    require(m_mod_s == 241, "crossed scalar exponent changed")
    require((m_mod_s * 216) % S == 1,
            "crossed scalar inverse changed")
    c = eta**216
    require(c**m_mod_s == eta, "crossed scalar correction failed")
    a_to_s = a.pow_mod(S, modulus)
    require(a_to_s == (ring.one() + x) * ring(field.one() / c),
            "a^359 does not equal (1+x)/c")
    require(ring(c) * a_to_s + 1 == x, "crossed reconstruction of x failed")
    require(x.pow_mod(R, modulus) == ring.gen(), "p=359 root equation failed")
    print("crossed root verified", time.monotonic() - started, flush=True)

    if args.full_upstream:
        unit, factors = binary_modulus.factor()
        require(int(unit) == 1 and factors == [(binary_modulus, 1)],
                "F_179 irreducibility check failed")
        recomputed_theta, steps = p359.resultant_char2(
            modulus, x + 1, field, started
        )
        require(p359.mask_from_field_element(recomputed_theta) == p359.THETA_MASK,
                "recomputed p=359 norm differs from stored theta")
        print("full upstream norm verified", steps, time.monotonic() - started,
              flush=True)

    # The leading coefficient is omitted from the payload and known to be one.
    f_a = ring(f_a_coefficients + [field.one()])
    require(f_a.degree() == D, "decoded f_a is not monic of degree 19580")
    if args.full or args.full_upstream:
        evaluation = f_a.compose_mod(a, modulus)
        require(evaluation.is_zero(), "f_a(a) is nonzero")
        print("minimal polynomial evaluation verified", time.monotonic() - started,
              flush=True)

    V = ring.gen()
    h_modulus = V**S + c
    v_inverse = V.inverse_mod(h_modulus)
    value = ring.one()
    for coefficient in reversed(f_a_coefficients):
        value = value.mul_mod(v_inverse, h_modulus) + ring(coefficient)
    W = V.pow_mod(D, h_modulus).mul_mod(value, h_modulus)
    require(encode_h(W) == stored_w, "recomputed crossed norm W differs")
    print("crossed norm verified", time.monotonic() - started, flush=True)

    # V^Q = kappa*V, so Q-Frobenius is diagonal in this Kummer basis.
    kappa = c ** ((Q - 1) // S)
    require(kappa != field.one() and kappa**S == field.one(),
            "Kummer Frobenius multiplier has wrong order")
    sigma_w = q_frobenius(W, kappa, ring)
    require(sigma_w == W.pow_mod(Q, h_modulus),
            "diagonal Q-Frobenius formula failed")
    bases = [W]
    for _ in range(1, S):
        bases.append(q_frobenius(bases[-1], kappa, ring))
    require(q_frobenius(bases[-1], kappa, ring) == W,
            "Q-Frobenius orbit does not close after 359 steps")

    euler_exponent = ((1 << (R * S)) - 1) // P
    digits = []
    remaining = euler_exponent
    for _ in range(S):
        remaining, digit = divmod(remaining, Q)
        digits.append(digit)
    require(remaining == 0, "Euler exponent escaped 359 base-Q digits")
    phase = simultaneous_power(bases, digits, h_modulus, ring)
    require(encode_h(phase) == stored_phase, "recomputed phase differs")
    require(phase != ring.one(), "p=719 Euler phase is trivial")
    require(phase.pow_mod(P, h_modulus) == ring.one(),
            "Euler phase is not 719-torsion")
    if args.full or args.full_upstream:
        print("p719 crossed certificate: verified")
    else:
        print("p719 crossed checkpoints: verified")
    print(f"a_sha256={A_SHA256}")
    print(f"f_a_sha256={F_A_SHA256}")
    print(f"W_sha256={W_SHA256}")
    print(f"phase_sha256={PHASE_SHA256}")
    print("phase_identity=False")
    print(f"full={args.full or args.full_upstream}")
    print(f"full_upstream={args.full_upstream}")
    if not (args.full or args.full_upstream):
        print("boundary=quick mode does not recompute f_a(a)=0")
    print(f"seconds={time.monotonic() - started:.6f}")


if __name__ == "__main__":
    main()
