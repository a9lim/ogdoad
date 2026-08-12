"""Survey trace-presented quadratic forms and their bent components.

The general quadratic Boolean function on ``F_{2^m}`` has a trace
representation (Carlet; e.g. arXiv:1305.3700)

    Q_c(x) = Σ_{i=1}^{m/2-1} Tr_1^m(c_i · x^{1+2^i})   [ + a half-trace middle term ]

Each displayed term is game-realizable: ``x^{1+2^i} = x times x^{2^i}`` is a
Turning-Corners product of ``x`` with its iterated Frobenius image, the
coefficient is one further nim-product, and sum/trace are XOR. This script
omits affine bookkeeping and the half-trace middle term; it probes a large
trace-presented family, not every Boolean quadratic form.

A form is bent exactly when its polar form is nondegenerate (for even ``m``).
The survey checks two facts:

  * the UNSCALED Gold form Tr(x^{1+2^a}) is NEVER bent: its radical is
    F_{2^{gcd(2a,m)}}, dim ≥ 1, so rank = m - gcd(2a,m) < m (see trace_form_arf.py);
  * but its COMPONENTS Tr(λ·x^{1+2^a}) ARE bent for 2/3 of λ when gcd(a,m)=1 — the
    classical Walsh count ``2(2^m-1)/3`` of bent components of a Gold (APN)
    power map.

On a bent form the radical is ``{0}``, so the symmetric polar-only loopy rule
has Loss-set ``{0}``. This makes bent components a clean stress test for rules
that claim to recover a quadratic zero set from polar data alone.

Scope: the ``i = m/2`` half-trace middle term is omitted here (it needs a
sub-field coefficient and a Tr_1^{m/2}); the i = 1..m/2-1 full-trace monomials
already reach bent, so nothing in the bent thesis depends on it. Runs on m = 8
(F_256) exhaustively; m a power of two only (nim-mult = F_{2^m} only on initial
segments).
"""

from collections import Counter
from math import gcd

import ogdoad as pl

from common import frob, nim_trace

# ----------------------------------------------------------------------------- form


def qform(x, coeffs, m):
    """Q_c(x) = Σ_i Tr(c_i · x^{1+2^i}), coeffs a dict i -> c_i (int). Game-realizable:
    each c_i · x · x^{2^i} is two Turning-Corners products of an i-fold Frobenius."""
    X = pl.Nimber(x)
    acc = pl.Nimber(0)
    for i, c in coeffs.items():
        term = pl.Nimber(c) * X * frob(X, i)
        acc = acc + pl.Nimber(nim_trace(term.value, m))
    return acc.value


def arf_of(coeffs, m):
    """ArfInvariants of Q_c in the bit-basis e_i = 2^i (q diagonal + b polar)."""
    q = [pl.Nimber(qform(1 << i, coeffs, m)) for i in range(m)]
    b = {}
    for i in range(m):
        for j in range(i + 1, m):
            bij = (qform((1 << i) ^ (1 << j), coeffs, m)
                   ^ qform(1 << i, coeffs, m) ^ qform(1 << j, coeffs, m))
            if bij:
                b[(i, j)] = pl.Nimber(1)
    return pl.arf_nimber(pl.NimberAlgebra(q=q, b=b))


# ----------------------------------------------------------------------------- parts


def part1_components_go_bent(m):
    print("=" * 72)
    print("PART 1 — scaled Gold components Tr(λ·x^{1+2^a}): bent counts by exponent")
    print("=" * 72)
    print("  in this scan, unscaled Gold (λ=1) has rank m - gcd(2a,m) < m, so it is not bent.")
    print(f"  scanning all λ ∈ F_{{2^{m}}}* :\n")
    print(f"  {'a':>2} {'gcd(a,m)':>8} {'APN?':>5} | rank distribution over λ        bent count   (2(2^m-1)/3)")
    print("  " + "-" * 86)
    for a in range(1, m // 2):
        ranks = Counter()
        for c in range(1, 1 << m):
            ranks[arf_of({a: c}, m).rank] += 1
        bent = ranks.get(m, 0)
        apn = gcd(a, m) == 1
        dist = "  ".join(f"r{r}:{n}" for r, n in sorted(ranks.items()))
        print(f"  {a:>2} {gcd(a, m):>8} {('yes' if apn else 'no'):>5} | {dist:<30} "
              f"{bent:>6}        {2 * ((1 << m) - 1) // 3 if apn else '—':>10}")
    print("\n  ⇒ gcd(a,m)=1 (APN exponent) gives exactly 2(2^m-1)/3 bent components;")
    print("    gcd(a,m)>1 (non-APN) gives a different split. Either way bent is reached")
    print("    by ONE extra nim-multiplication (the coefficient λ) in these tested cases.\n")


def part2_zero_count(m):
    print("=" * 72)
    print("PART 2 — bent forms validate the Arf zero-count #{Q=0}=2^{m-1}+(-1)^Arf 2^{m/2-1}")
    print("=" * 72)
    arf_seen = Counter()
    checked = 0
    fail = 0
    for c in range(1, 1 << m):
        r = arf_of({1: c}, m)
        if r.rank != m:
            continue
        z = sum(1 for x in range(1 << m) if qform(x, {1: c}, m) == 0)
        pred = (1 << (m - 1)) + (-1 if r.arf else 1) * (1 << (m // 2 - 1))
        arf_seen[r.arf] += 1
        checked += 1
        fail += (z != pred)
    print(f"  bent components of Tr(λ·x^{{1+2}}): {checked} checked, zero-count mismatches: {fail}")
    print(f"  Arf split among bent components: Arf 0 → {arf_seen[0]}, Arf 1 → {arf_seen[1]}")
    print(f"  (Arf 0 ⇒ #{{Q=0}}={ (1<<(m-1)) + (1<<(m//2-1)) } > half; "
          f"Arf 1 ⇒ {(1<<(m-1)) - (1<<(m//2-1))} < half — the conditional win-bias.)\n")


def part3_sums_and_route(m):
    print("=" * 72)
    print("PART 3 — multi-term sums reach bent too; and the route consequence")
    print("=" * 72)
    import random
    rng = random.Random(0xF00D)
    bent = seen = 0
    for _ in range(80):
        k = rng.choice([2, 3])
        idx = rng.sample(range(1, m // 2), min(k, m // 2 - 1))
        coeffs = {i: rng.randrange(1, 1 << m) for i in idx}
        if arf_of(coeffs, m).rank == m:
            bent += 1
        seen += 1
    print(f"  random 2/3-term sums Σ c_i x^{{1+2^i}}: {bent}/{seen} bent.\n")
    # route: on a bent form the radical is trivial, so the symmetric-B loopy Loss-set
    # = R(B) (loopy_quadric.rs) collapses to {0}, and the Sp(B) no-go has no
    # degenerate part to be silent on.
    c = next(c for c in range(1, 1 << m) if arf_of({1: c}, m).rank == m)
    rad = [v for v in range(1 << m)
           if all((qform(v ^ d, {1: c}, m) ^ qform(v, {1: c}, m) ^ qform(d, {1: c}, m)) == 0
                  for d in range(1 << m))]
    print(f"  bent witness λ={c}: radical R(B) = {rad}  (|R(B)|={len(rad)})")
    print("  ⇒ symmetric-B loopy Loss-set = R(B) = {0}: the radical route is empty here.")
    print("  ⇒ bent forms are a clean polar-only stress test: no radical can fake a {Q=0} hit")
    print("    (the (m,a)=(4,1) coincidence in loopy_quadric.rs cannot recur), and the")
    print("    frame-blind Sp(B) obstruction applies without a radical exception.")


if __name__ == "__main__":
    M = 8
    print(f"The game-realizable quadratic family over F_2^{M}, and its bent members.\n")
    part1_components_go_bent(M)
    part2_zero_count(M)
    part3_sums_and_route(M)
