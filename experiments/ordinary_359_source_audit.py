#!/usr/bin/env python3
"""Audit the two historical exact ``p=359`` Peeters runs.

This is a provenance verifier, not an independent finite-field replay.  It
reads two files directly from a pinned git object in a local clone of
``transfinite-nim-calculator``, verifies their complete-file SHA-256 digests,
and checks the two recorded start/end pairs for the fixed-mark Euler power.

Usage::

    python3 experiments/ordinary_359_source_audit.py \
      /path/to/transfinite-nim-calculator

The final support count being larger than one records nonidentity in the
calculator's exact sparse basis.  Trust in that conclusion still includes the
pinned external implementation and the historical log artifact; no final
coefficient vector is stored, so this is not a local algebraic certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
from pathlib import Path

if not __debug__:
    raise SystemExit("assertions must remain enabled; do not run with python -O")


COMMIT = "7a26543f11f5319d04da5402840beecc9e5b35fe"
CALCULATION_LOG_SHA256 = (
    "2d88249bd90703acb85783d2d80ecd72bc91994c818298e29adef20b14169e11"
)
ALPHA_LOG_SHA256 = (
    "cacc9cd9b9db801b5d0b0176b11289127369b97067068a4518b928fa97f5fedd"
)
EULER_BITS = 3_504_812
FINAL_SUPPORT = 1_743_227
EXPECTED_RUNS = (
    ("2025-09-15 13:55:08", "2025-09-17 11:52:29"),
    ("2025-09-24 05:20:22", "2025-09-26 03:22:17"),
)
EXPECTED_TIMES = (177_379, 177_717)

PROGRESS_RE = re.compile(
    rb"^\[(?P<timestamp>[^]]+)] "
    rb"(?P<done>\d+)/(?P<total>\d+) bits complete .*; "
    rb"curpow/result has (?P<curpow>\d+)/(?P<result>\d+) terms$",
    re.MULTILINE,
)


def git_blob(repo: Path, path: str) -> bytes:
    """Read ``path`` from the pinned historical commit."""

    return subprocess.run(
        ["git", "-C", str(repo), "show", f"{COMMIT}:{path}"],
        check=True,
        stdout=subprocess.PIPE,
    ).stdout


def sha256(payload: bytes) -> str:
    """Return the hexadecimal SHA-256 digest of ``payload``."""

    return hashlib.sha256(payload).hexdigest()


def audit_calculation_log(payload: bytes) -> None:
    """Verify the two complete fixed-mark progress traces."""

    assert sha256(payload) == CALCULATION_LOG_SHA256
    records = [
        {
            key: (int(value) if key != "timestamp" else value.decode("ascii"))
            for key, value in match.groupdict().items()
        }
        for match in PROGRESS_RE.finditer(payload)
    ]
    starts = [
        row
        for row in records
        if row["done"] == 0
        and row["total"] == EULER_BITS
        and row["curpow"] == 2
        and row["result"] == 1
    ]
    ends = [
        row
        for row in records
        if row["done"] == EULER_BITS
        and row["total"] == EULER_BITS
        and row["curpow"] == 2
        and row["result"] == FINAL_SUPPORT
    ]
    assert tuple(row["timestamp"] for row in starts) == tuple(
        pair[0] for pair in EXPECTED_RUNS
    )
    assert tuple(row["timestamp"] for row in ends) == tuple(
        pair[1] for pair in EXPECTED_RUNS
    )


def audit_alpha_log(payload: bytes) -> None:
    """Verify the duplicate stored ``p=359`` result rows and timings."""

    assert sha256(payload) == ALPHA_LOG_SHA256
    rows = []
    for line in payload.decode("utf-8").splitlines():
        fields = line.split()
        if fields and fields[0] == "359":
            rows.append(line)
    assert len(rows) == 2
    for row, elapsed in zip(rows, EXPECTED_TIMES, strict=True):
        assert "[179]" in row
        assert re.search(r"\s1\s+w\^\(w\^39\) \+ 1\s", row)
        assert row.rstrip().endswith(str(elapsed))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path, help="local calculator git clone")
    args = parser.parse_args()
    if not (args.repo / ".git").exists():
        raise SystemExit(f"not a git clone: {args.repo}")

    calculation_log = git_blob(args.repo, "logs/calculation.log")
    alpha_log = git_blob(args.repo, "logs/alpha_log.txt")
    audit_calculation_log(calculation_log)
    audit_alpha_log(alpha_log)
    print(
        f"p359 source audit: commit={COMMIT}, runs={len(EXPECTED_RUNS)}, "
        f"final_support={FINAL_SUPPORT}, timings={EXPECTED_TIMES}"
    )


if __name__ == "__main__":
    main()
