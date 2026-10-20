"""Census functions for the 0/1/4 excess rule (copy of ../census.py logic,
without the argv-dependent sieve bound).  Q(h), arm, rule, component degrees."""
from __future__ import annotations

import sys
from functools import lru_cache
from math import gcd

sys.setrecursionlimit(100000)
NSIEVE = 2 * 10**6


def _sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i * i :: i] = bytearray(len(s[i * i :: i]))
    return s


_isp = _sieve(NSIEVE)
primes = [i for i in range(NSIEVE + 1) if _isp[i]]
spf = list(range(NSIEVE + 1))
for _p in primes:
    if _p * _p > NSIEVE:
        break
    for _m in range(_p * _p, NSIEVE + 1, _p):
        if spf[_m] == _m:
            spf[_m] = _p


def factor(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    while n > 1:
        if n <= NSIEVE:
            p = spf[n]
            while n % p == 0:
                out[p] = out.get(p, 0) + 1
                n //= p
        else:
            d = 2
            while d * d <= n:
                while n % d == 0:
                    out[d] = out.get(d, 0) + 1
                    n //= d
                d += 1
            if n > 1:
                out[n] = out.get(n, 0) + 1
            return out
    return out


def ordtwo(p: int) -> int:
    o = p - 1
    for q in factor(p - 1):
        while o % q == 0 and pow(2, o // q, p) == 1:
            o //= q
    return o


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def d_finite(m: int) -> int:
    if m <= 1:
        return 1
    k = 1
    while m >= (1 << (1 << k)):
        k += 1
    return 1 << k


def factor_pp(q: int) -> tuple[int, int]:
    ((r, k),) = factor(q).items()
    return r, k


@lru_cache(None)
def b(r: int) -> int:
    """degree of alpha_r"""
    h = ordtwo(r)
    Q = Qset(h)
    return lcm(dsum(Q), d_finite(rule(r, h, Q)))


def dq(q: int) -> int:
    r, _ = factor_pp(q)
    return q if r == 2 else q * b(r)


def dsum(Q) -> int:
    d = 1
    for q in Q:
        d = lcm(d, dq(q))
    return d


@lru_cache(None)
def Qset(h: int) -> tuple:
    if h == 1:
        return ()
    f = factor(h)
    r = min(f)
    q = r ** f[r]
    g = h // q
    Q = Qset(g)
    if dsum(Q) % q != 0:
        Q = tuple(sorted(Q + (q,)))
    return Q


def arm(h: int, Q) -> str:
    if len(Q) == 1 and Q[0] % 2 == 1:
        r = min(factor(Q[0]))
        if r == 3:
            return "C" if h == Q[0] else "D"
        return "O"
    if len(Q) == 1 and Q[0] % 2 == 0:
        return "ZF"
    return "Z"


def rule(p: int, h: int, Q) -> int:
    return {"Z": 0, "ZF": 0, "O": 1, "C": 1, "D": 4}[arm(h, Q)]


def row(p: int):
    h = ordtwo(p)
    Q = Qset(h)
    a = arm(h, Q)
    m = rule(p, h, Q)
    return (p, h, Q, a, m, lcm(dsum(Q), d_finite(m)))
