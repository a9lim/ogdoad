"""Shared finite-field trace helpers for the experiment scripts."""

import ogdoad as pl


def frob(x: pl.Nimber, a: int) -> pl.Nimber:
    """Frobenius^a: x -> x^(2^a)."""
    return pl.Nimber(pl.nim_frobenius_iter(x.value, a))


def nim_trace(x: int, m: int) -> int:
    """Trace from F_{2^m} to F_2, returned as 0 or 1."""
    value = pl.nim_trace(x, m)
    # precondition guard, not redundancy: for x outside F_{2^m} the bound
    # trace is garbage-in-garbage-out (e.g. nim_trace(2, 1) == 2)
    assert value in (0, 1), f"trace not in F2: {value}"
    return value
