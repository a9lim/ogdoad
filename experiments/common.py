"""Shared Gold-form helpers for the experiment scripts."""

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


def nim_mul(a: int, b: int) -> int:
    """Nim (Conway) multiplication on raw ints, via the bound engine."""
    return (pl.Nimber(a) * pl.Nimber(b)).value


def gold_lam(v: int, a: int, m: int, lam: int = 1) -> int:
    """Lam-generalized Gold form Q_a(v) = Tr(lam * v^(1+2^a)) over F_{2^m}.

    ``lam`` multiplies the product before the trace.
    """
    x = pl.Nimber(v)
    return nim_trace((pl.Nimber(lam) * x * frob(x, a)).value, m)


def polar_lam(u: int, v: int, a: int, m: int, lam: int = 1) -> int:
    """Lam-generalized polar form B(u,v) = Q(u+v) + Q(u) + Q(v)."""
    return gold_lam(u ^ v, a, m, lam) ^ gold_lam(u, a, m, lam) ^ gold_lam(v, a, m, lam)


def gold(v: int, a: int, m: int) -> int:
    """Gold form Q_a(v) = Tr(v^(1+2^a)) over F_{2^m}."""
    return gold_lam(v, a, m)


def polar(u: int, v: int, a: int, m: int) -> int:
    """Polar form B(u,v) = Q(u+v) + Q(u) + Q(v)."""
    return polar_lam(u, v, a, m)


def gold_table(a: int, m: int, lam: int = 1) -> list:
    """The lam-generalized Gold form over all of F_{2^m}, index = point."""
    return [gold_lam(v, a, m, lam) for v in range(1 << m)]


def report(name: str, ok: bool) -> None:
    """Print "name: PASS/FAIL" and assert ok."""
    print(f"{name}: {'PASS' if ok else 'FAIL'}")
    assert ok
