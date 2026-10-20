"""Emit the component program for one excess row (reference engine driver).

A program lists the components of the closure of Q(f(p)) (plus the finite
components of the tested translates) in dependency order, each with its exact
defining relation, then the target sum and the translates to test.

Relations (term algebra of Lenstra/DiMuro):
  AS  chi_{2^k}:  y^2 + y = prod_{j<k} chi_{2^j}        (degree 2^k)
  K   chi_r:      y^r = sum_{q in Q(f(r))} chi_q + m_r  (r odd prime)
  K   chi_{r^k}:  y^r = chi_{r^(k-1)}                  (k >= 2)
Finite nimber m = XOR over its bits i of prod_{j in bits(i)} chi_{2^(j+1)}.
"""

from __future__ import annotations

import sys
from math import gcd

sys.path.insert(0, __file__.rsplit("/", 2)[0])
import census as C  # noqa: E402


def factor_pp(q: int) -> tuple[int, int]:
    f = C.factor(q)
    ((r, k),) = f.items()
    return r, k


def nimber_terms(m: int) -> list[list[int]]:
    """Finite nimber m as a list of monomials, each a list of 2-power q's."""
    terms = []
    i = 0
    while m >> i:
        if (m >> i) & 1:
            mono = []
            j = 0
            while i >> j:
                if (i >> j) & 1:
                    mono.append(1 << (j + 1))
                j += 1
            terms.append(mono)
        i += 1
    return terms


class Program:
    def __init__(self, excess: dict[int, int]):
        self.excess = excess  # verified m_r for closure primes
        self.order: list[int] = []
        self.rel: dict[int, tuple] = {}

    def add(self, q: int) -> None:
        if q in self.rel:
            return
        r, k = factor_pp(q)
        if r == 2:
            for j in range(1, k):
                self.add(1 << j)
            self.rel[q] = ("AS", [[1 << j for j in range(1, k)]])
        elif k >= 2:
            self.add(q // r)
            self.rel[q] = ("K", r, [[q // r]])
        else:
            Q = C.Qset(C.ordtwo(r))
            hr = C.ordtwo(r)
            assert self.excess[r] == C.rule(r, hr, Q), (r, self.excess[r])
            expr = [[qq] for qq in Q] + nimber_terms(self.excess[r])
            for mono in expr:
                for qq in mono:
                    self.add(qq)
            self.rel[q] = ("K", r, expr)
        self.order.append(q)

    def degree(self, q: int) -> int:
        r, _ = factor_pp(q)
        return q if r == 2 else C.dq(q)


def row_program(p: int, excess: dict[int, int], translates: list[int]) -> str:
    h = C.ordtwo(p)
    Q = C.Qset(h)
    prog = Program(excess)
    for q in Q:
        prog.add(q)
    E = C.dsum(Q)
    for m in translates:
        for mono in nimber_terms(m):
            for qq in mono:
                prog.add(qq)
        E = C.lcm(E, C.d_finite(m))
    assert E % h == 0
    idx = {q: i for i, q in enumerate(prog.order)}
    out = [f"E {E}", f"P {p}", f"N {len(prog.order)}"]
    for q in prog.order:
        rel = prog.rel[q]
        if rel[0] == "AS":
            expr, ell = rel[1], 2
        else:
            ell, expr = rel[1], rel[2]
        terms = " ; ".join((" ".join(str(idx[x]) for x in mono) or "-") for mono in expr)
        out.append(f"C {q} {ell} {prog.degree(q)} {len(expr)} : {terms}")
    tgt = " ; ".join(str(idx[q]) for q in Q)
    out.append(f"T {len(Q)} : {tgt}")
    for m in translates:
        mt = nimber_terms(m)
        terms = " ; ".join((" ".join(str(idx[x]) for x in mono) or "-") for mono in mt)
        out.append(f"M {m} {len(mt)} : {terms}")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    import json

    p = int(sys.argv[1])
    excess = json.loads(sys.argv[2]) if len(sys.argv) > 2 else {}
    excess = {int(k): v for k, v in excess.items()}
    translates = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [0, 1]
    sys.stdout.write(row_program(p, excess, translates))
