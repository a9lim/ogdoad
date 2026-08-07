"""The abstract linking game: reductions, screens, and the verified strategy.

The general-m linking-theorem chase (2026-06-10) for the echo-fifo+dummy
realizer (writeups/goldarf.tex SS8.3): abstract the verified sigma-valued
FIFO+ko+pass+dummy rule away from Gold forms to arbitrary support graphs,
and reduce the m-uniform exactness claim to one combinatorial statement.

THE REDUCED GAME.  Board: a finite graph on "coins"; state (U, q, ko) with
U = untouched coins, q = FIFO queue of open coins, ko = last-touched coin.
Moves: OPEN any x in U (x != ko, push to back) or CLOSE the queue front f
(f != ko, pop); no legal move => forced pass (clears ko).  A close FLIPS a
bit iff deg_U(f) is odd at that moment.  One player wants total flips even,
the other odd.

Reduction lemmas (each a short whole-play identity, machine-validated here):
  R1. FIFO => coins close in opening order => no chord nesting; a graph
      edge is LINKED iff the two open-windows overlap.  sigma == overlap
      parity of the played interval graph restricted to E(G).
  R2. (overlap accounting) D := sigma ^ |undecided edges| is invariant
      under opens and passes and flips exactly on odd-deg_U(front) closes.
      So the sigma-game IS the odd-close parity game above, with
      sigma_forced = |E| ^ (forced flip parity).
  R3. Opens are never ko-blocked (ko is always a touched coin); the ko
      blocks a close only when the front was just opened onto an empty
      queue; forced passes occur only once U = 0, after which deg_U == 0
      and no flips are possible.  Passes are irrelevant to the flip fight.

THE LINKING THEOREM (target).  If the board contains an isolated coin (the
dummy), the flip count is forced even -- both seats, every graph.  Hence
sigma is forced = |E| mod 2, which on a Gold board is Q(x): m-uniform
exactness of the echo-fifo+dummy realizer.

STATUS (2026-07-20), machine-verified by this file:
  * Rigidity holds for ALL graph iso classes with k <= 8 real coins +
    dummy, both seats (k=8: 12,346 classes, supplied by nauty ``geng``) --
    far beyond the Gold-arising boards of the m=8 sweep.
  * Without the dummy the odd-order failures through n=7 are mover-controlled,
    census {3:1, 5:4, 7:34}; none contains an isolated vertex, and 33/34 at
    n=7 have a dominating vertex.  Order n=8 has exactly seven different,
    anti-mover-controlled failures: the second player can force either declared
    target parity.  Thus the old "initial mover always forces even" heuristic
    is false, while the narrower even-order second-seat-even screen survives.
  * Core Lemma (the empty-queue obstruction; proof = 4-case check): with
    the queue empty, after opening v with R = U \\ {v}, the responder can
    re-even v before it becomes closable UNLESS R is a subset of N(v) with
    |R| even -- the "domination device" (ko-protected zugzwang, flip in 2
    plies).  An isolated coin in U defeats it at every root.  |R| odd
    explains the bonus even-n no-dummy rigidity.
  * The original PREVENTION/DEBT menus (rule_R3/debt_D3 below) beat an
    optimal unrestricted attacker on every class k <= 7, but fail first at
    k = 8.  ``GCRU]w`` needs a proactive odd-corridor poison despite safe
    non-neighbor opens; ``GCZMmw`` needs an odd front left deliberately
    unrepaired.  The broader no-self-flip prevention envelope (every open,
    even-front closes) plus debt_D3 is strictly complete on all 12,346 k=8
    classes, both seats.  Menu semantics remain EXISTENTIAL: a winning move
    is always present, not every admitted move wins.
  * General-n proof: OPEN.  A second pass exposed two additional exact
    reductions.  Queue-empty turns always belong to the initial mover: a
    maximal nonempty-queue block on b coins consumes exactly 2b moves.
    Also, if L is the still-unclosed vertex set when x opens, total flip
    parity equals sum_x deg_L(x): for P = e(queue, U), closes change P by
    the flip bit and opens change it by deg_L(x).  This degree-pairing form
    is the current proof route.  An earlier architecture (Codex spar, thread
    019eb4ff-695b-7762-97e8-c0bea66c4e7e) segments the queue at firewall
    coins (deg_U == 0; the opened dummy is permanent, the untouched dummy
    virtual), mutual induction E (no debt) / O (one debt) per segment;
    certificates bounded by game-tree depth.  The hard obligation is the
    poison transition E -> O (recursive repair-potential), which is also
    exactly where parity-local invariants provably fail (the safe/unsafe
    label is NOT a function of 13 natural parity features; minimal
    distinguishing pairs differ in E(U) repair structure).  The two k=8
    menu witnesses now show that any such induction must admit proactive
    debt before the parity-local trap appears.
  * The proof-frontier note ``writeups/linking_affine.tex`` now replaces that
    local induction by the exact affine target 0 in Aff{D(h)}.  Front deletion
    is a two-graph/Seidel quotient, but its cut and continuation moments remain
    correlated.  This file pins the first stronger-template failures: two
    no-dummy order-8 graphs need exactly two action switches, and a close-first
    k=5 attacker needs a five-leaf rather than three-leaf affine certificate.

The old description of the empty-queue domination device as the unique
local obstruction was too strong.  A nonempty queue can squeeze too: on
the path z-f-y-h, queue (f,h), U={y,z}, and an even front f, either open
makes f odd while closing f exposes the odd front h.  The dummy defeats
this squeeze while untouched, but a proof must track the queued case.

Stages: validate | screen [K] | strategy [K] | graph6 | all (default K =
5; the k=7 screen ~45 s, k=7 strategy ~25 s).  ``graph6`` consumes a
nauty ``geng`` census through ``--graph6-path`` and can parallelize with
``--jobs`` (for example, ``geng -q 8 > graphs8.g6`` followed by
``python linking_game.py graph6 --graph6-path graphs8.g6 --jobs 12``).
Stdlib only, no venv needed.
Cross-validated against experiments/echo_solver.py (the adversarially
reviewed solver) through the SynthForm bridge in stage `validate`.
"""

import argparse
import functools
import multiprocessing
import random
import sys
import time
from itertools import permutations
from pathlib import Path
from typing import Any

sys.setrecursionlimit(10_000)  # matches echo_solver.py; state-space recursion is shallow


# ---------------------------------------------------------------- solvers

def adj_of(n: int, edges) -> list:
    adj = [0] * n
    for (i, j) in edges:
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    return adj


def legal_moves(n, adj, u, seq, ko):
    """All legal moves as (kind, coin, flip, u2, seq2, ko2).

    ``ko`` is true exactly after opening onto an empty queue.  Opens are
    otherwise never blocked: the last touched coin cannot still be untouched,
    and after any close the new front differs from the coin just closed.
    """
    mv = []
    for i in range(n):
        if u >> i & 1:
            mv.append(("o", i, 0, u ^ (1 << i), seq + (i,), not seq))
    if seq and not ko:
        f = seq[0]
        fl = bin(adj[f] & u).count("1") & 1
        mv.append(("c", f, fl, u, seq[1:], False))
    return mv


def rigid_values(k: int, edges, dummy: bool) -> list:
    """[value(P1 wants 0), value(P1 wants 1)] of the flip-parity game,
    d-folded full-state solver (the same move semantics as
    echo_solver.fifo_value; charge convention differs only by bookkeeping
    -- totals agree, validated in stage `validate`)."""
    n = k + (1 if dummy else 0)
    adj = adj_of(n, edges)
    memo: dict = {}

    def win(u, seq, ko, g):
        # mover can force future flip count == g (mod 2)
        if u == 0 and not seq:
            return g == 0
        key = (u, seq, ko, g)
        r = memo.get(key)
        if r is not None:
            return r
        mv = legal_moves(n, adj, u, seq, ko)
        if not mv:
            res = not win(u, seq, False, 1 ^ g)  # forced pass clears ko
        else:
            res = any(not win(u2, s2, ko2, 1 ^ g ^ fl)
                      for (_t, _c, fl, u2, s2, ko2) in mv)
        memo[key] = res
        return res

    par = len(edges) & 1
    full = (1 << n) - 1
    out = []
    for t in (0, 1):
        g = t ^ par  # flips needed for sigma == t
        out.append(t if win(full, (), False, g) else 1 ^ t)
    return out


def sigma_value(k: int, edges, dummy: bool, t: int) -> int:
    """Sigma-explicit oracle for the d-folding (lower-cocycle charges,
    byte-for-byte the echo_solver.fifo_value recursion shape with q = 0)."""
    n = k + (1 if dummy else 0)
    adj = adj_of(n, edges)
    hadj = [adj[i] & ~((2 << i) - 1) for i in range(n)]
    memo: dict = {}

    def rec(u, seq, last, mover, sigma):
        if u == 0 and not seq:
            return sigma
        key = (u, seq, last, mover, sigma)
        r = memo.get(key)
        if r is not None:
            return r
        omask = 0
        for c in seq:
            omask |= 1 << c
        legal = []
        for i in range(n):
            if i != last and u >> i & 1:
                ch = bin(omask & hadj[i]).count("1") & 1
                legal.append((i, ch, u ^ (1 << i), seq + (i,)))
        if seq and seq[0] != last:
            c = seq[0]
            ch = bin(omask & hadj[c]).count("1") & 1
            legal.append((c, ch, u, seq[1:]))
        if not legal:
            res = rec(u, seq, -1, 1 - mover, sigma)
        else:
            want = t if mover == 0 else 1 - t
            res = 1 - want
            for (i, ch, u2, s2) in legal:
                if rec(u2, s2, i, 1 - mover, sigma ^ ch) == want:
                    res = want
                    break
        memo[key] = res
        return res

    return rec((1 << n) - 1, (), -1, 0, 0)


# ---------------------------------------------------------------- iso classes

def iso_classes(k: int) -> list:
    """One representative edge-frozenset per isomorphism class on k labelled
    vertices (orbit marking; fine through k = 7)."""
    pairs = [(i, j) for i in range(k) for j in range(i + 1, k)]
    pidx = {p: ii for ii, p in enumerate(pairs)}
    perms = list(permutations(range(k)))
    seen = set()
    reps = []
    for gmask in range(1 << len(pairs)):
        if gmask in seen:
            continue
        edges = frozenset(p for ii, p in enumerate(pairs) if gmask >> ii & 1)
        reps.append(edges)
        for perm in perms:
            om = 0
            for (i, j) in edges:
                a, b = perm[i], perm[j]
                om |= 1 << pidx[(min(a, b), max(a, b))]
            seen.add(om)
    return reps


def decode_graph6(line: str) -> tuple[int, frozenset]:
    """Decode the small (n <= 62) graph6 form emitted by nauty ``geng``.

    The linking screens are already factorial at the game layer, so the
    extended graph6 size forms would not be useful here.  Keeping the decoder
    local also preserves this experiment's stdlib-only boundary.
    """
    data = line.strip()
    if data.startswith(">>graph6<<"):
        data = data[len(">>graph6<<"):]
    if not data:
        raise ValueError("empty graph6 record")
    n = ord(data[0]) - 63
    if not 0 <= n <= 62:
        raise ValueError("only the one-byte graph6 order form is supported")
    bits = []
    for char in data[1:]:
        value = ord(char) - 63
        if not 0 <= value < 64:
            raise ValueError(f"invalid graph6 byte: {char!r}")
        bits.extend((value >> shift) & 1 for shift in range(5, -1, -1))
    need = n * (n - 1) // 2
    if len(bits) < need:
        raise ValueError("truncated graph6 record")
    edges = []
    cursor = 0
    for j in range(1, n):
        for i in range(j):
            if bits[cursor]:
                edges.append((i, j))
            cursor += 1
    return n, frozenset(edges)


def verify_graph6_record(item: tuple[str, bool]):
    """Return a counterexample description, or ``None`` on success."""
    line, check_strategy = item
    k, edges = decode_graph6(line)
    par = len(edges) & 1
    values = rigid_values(k, edges, True)
    if values != [par, par]:
        return ("theorem", line.strip(), values)
    if check_strategy:
        for seat in (0, 1):
            if not strategy_holds(k, edges, seat):
                return ("menu", line.strip(), seat)
    return None


# ---------------------------------------------------------------- strategy

def rule_R3(n, adj, u, seq, ko):
    """PREVENTION menu (debt 0).  P1 re-even / P2 safe opens + safe close /
    P3 poison-or-close trap branch / P4 endgame close."""
    front = seq[0] if seq else None
    allowed = set()
    if u == 0:
        if front is not None and not ko:
            allowed.add(("c", front))
        return allowed
    if front is not None and bin(adj[front] & u).count("1") & 1:
        for i in range(n):
            if (u >> i & 1) and (adj[front] >> i & 1):
                allowed.add(("o", i))
        return allowed
    nontog = {("o", i) for i in range(n)
              if (u >> i & 1)
              and (front is None or not adj[front] >> i & 1)}
    if nontog:
        allowed |= nontog
        if front is not None and not ko:
            nxt = seq[1] if len(seq) > 1 else None
            if nxt is None or bin(adj[nxt] & u).count("1") % 2 == 0:
                allowed.add(("c", front))
        return allowed
    for i in range(n):
        if u >> i & 1:
            allowed.add(("o", i))
    if front is not None and not ko:
        allowed.add(("c", front))
    return allowed


def rule_R3_corridor(n, adj, u, seq, ko):
    """PREVENTION plus the first recursive repair certificate.

    R3 fails first on the eight-real-vertex graph6 class ``GCRU]w``: it
    preserves an even front with an isolated/non-neighbor open, but every such
    move loses.  Opening a neighbor instead turns the whole four-coin queue
    into an even-length odd corridor; paired closes then discharge the debt.
    This extension admits exactly those proactive poison moves in addition
    to R3.
    """
    allowed = rule_R3(n, adj, u, seq, ko)
    front = seq[0] if seq else None
    if front is None or bin(adj[front] & u).count("1") & 1:
        return allowed
    for i in range(n):
        if not (u >> i & 1) or not (adj[front] >> i & 1):
            continue
        u2 = u ^ (1 << i)
        seq2 = seq + (i,)
        if len(seq2) % 2 == 0 and all(
                bin(adj[v] & u2).count("1") & 1 for v in seq2):
            allowed.add(("o", i))
    return allowed


def rule_no_self_flip(n, adj, u, seq, ko):
    """The no-self-flip prevention envelope.

    The next eight-vertex obstruction, graph6 class ``GCZMmw``, must leave
    an odd front odd by opening a non-neighbor.  Together the first two R3
    failures say that prevention must allow debt proactively, not only in a
    parity-local trap.  The envelope therefore admits every open and exactly
    the safe (even-front) closes: the defender never pays a flip on their own
    move.
    """
    allowed = {("o", i) for i in range(n) if u >> i & 1}
    front = seq[0] if seq else None
    if front is not None and not ko and \
            bin(adj[front] & u).count("1") % 2 == 0:
        allowed.add(("c", front))
    return allowed


def debt_D3(n, adj, u, seq, ko):
    """DEBT menu (debt 1).  D1 counter-close / D2 ko stall / D3 toggle or
    advance / D4 bare opens."""
    front = seq[0] if seq else None
    allowed = set()
    if front is not None and bin(adj[front] & u).count("1") & 1:
        if not ko:
            return {("c", front)}
        for i in range(n):
            if u >> i & 1:
                allowed.add(("o", i))
        return allowed
    if front is not None:
        for i in range(n):
            if (u >> i & 1) and (adj[front] >> i & 1):
                allowed.add(("o", i))
        if not ko:
            allowed.add(("c", front))
        return allowed
    for i in range(n):
        if u >> i & 1:
            allowed.add(("o", i))
    return allowed


def strategy_holds(k: int, edges, seat: int, menu_version: int = 5) -> bool:
    """Defender (flips-even) restricted to a prevention/debt menu, attacker
    unrestricted optimal; STRICT (an empty/illegal menu = defender loss).
    Menu-existential: True means a winning move always exists IN the menu.
    Versions 3 and 4 reproduce the two superseded finite boundaries; version
    5 is the current no-self-flip prevention envelope."""
    if menu_version not in (3, 4, 5):
        raise ValueError(f"unknown menu version: {menu_version}")
    n = k + 1  # always with dummy
    adj = adj_of(n, edges)
    memo: dict = {}

    def W(u, seq, ko, mover, g):
        if u == 0 and not seq:
            return g == 0
        key = (u, seq, ko, mover, g)
        r = memo.get(key)
        if r is not None:
            return r
        lm = legal_moves(n, adj, u, seq, ko)
        if mover == seat and lm:
            prevention = {
                3: rule_R3,
                4: rule_R3_corridor,
                5: rule_no_self_flip,
            }[menu_version]
            rule = prevention if g == 0 else debt_D3
            allowed = rule(n, adj, u, seq, ko)
            mv = [m for m in lm if (m[0], m[1]) in allowed]
            if not mv:
                memo[key] = False
                return False
        else:
            mv = lm
        if not mv:
            res = W(u, seq, False, 1 - mover, g)
        elif mover == seat:
            res = any(W(u2, s2, ko2, 1 - mover, g ^ fl)
                      for (_t, _c, fl, u2, s2, ko2) in mv)
        else:
            res = all(W(u2, s2, ko2, 1 - mover, g ^ fl)
                      for (_t, _c, fl, u2, s2, ko2) in mv)
        memo[key] = res
        return res

    return W((1 << n) - 1, (), False, 0, 0)


def close_first_response_vectors(k: int) -> frozenset[int]:
    """Exact D-vectors against the first-seat close-first attacker.

    Edge bits use ``itertools.combinations(range(k), 2)`` order.  The dummy is
    vertex ``k`` and contributes no coordinate.
    """
    n = k + 1
    dummy = k
    pidx = {pair: bit for bit, pair in
            enumerate((i, j) for i in range(k) for j in range(i + 1, k))}

    def close_vector(front: int, u: int) -> int:
        if front == dummy:
            return 0
        out = 0
        for x in range(k):
            if u >> x & 1:
                out ^= 1 << pidx[min(front, x), max(front, x)]
        return out

    @functools.lru_cache(None)
    def rec(u: int, seq: tuple[int, ...], ko: bool,
            mover: int, score: int) -> frozenset[int]:
        if u == 0 and not seq:
            return frozenset({score})
        opens = [(u ^ (1 << x), seq + (x,), not seq, score)
                 for x in range(n) if u >> x & 1]
        close = None
        if seq and not ko:
            close = (u, seq[1:], False, score ^ close_vector(seq[0], u))
        moves = opens + ([close] if close is not None else [])
        if not moves:
            return rec(u, seq, False, 1 - mover, score)
        if mover == 0:
            chosen = close if close is not None else opens[0]
            assert chosen is not None
            return rec(chosen[0], chosen[1], chosen[2], 1 - mover, chosen[3])
        out: set[int] = set()
        for child in moves:
            out.update(rec(child[0], child[1], child[2], 1 - mover, child[3]))
        return frozenset(out)

    return rec((1 << n) - 1, (), False, 0, 0)


def minimum_worst_switches(k: int, edges) -> int | None:
    """Minimum worst-case action-type switches for a second-seat even player.

    Return ``None`` if that defender cannot force even.  A switch is a defender
    OPEN after an attacker CLOSE or vice versa; forced passes are uncharged.
    """
    n = k
    adj = adj_of(n, edges)
    inf = 10_000

    @functools.lru_cache(None)
    def cost(u: int, seq: tuple[int, ...], ko: bool,
             mover: int, g: int, pending: str) -> int:
        if u == 0 and not seq:
            return 0 if g == 0 else inf
        moves = legal_moves(n, adj, u, seq, ko)
        if not moves:
            return cost(u, seq, False, 1 - mover, g, "")
        values = []
        for kind, _coin, flip, u2, seq2, ko2 in moves:
            extra = int(mover == 1 and pending and kind != pending)
            next_pending = kind if mover == 0 else ""
            values.append(extra + cost(
                u2, seq2, ko2, 1 - mover, g ^ flip, next_pending))
        return max(values) if mover == 0 else min(values)

    answer = cost((1 << n) - 1, (), False, 0, 0, "")
    return None if answer >= inf else answer


# ---------------------------------------------------------------- stages

def stage_validate() -> None:
    print("== d-folded vs sigma-explicit (k <= 4 exhaustive, dummy on/off) ==")
    cnt = 0
    for k in (2, 3, 4):
        pairs = [(i, j) for i in range(k) for j in range(i + 1, k)]
        for gmask in range(1 << len(pairs)):
            edges = frozenset(p for ii, p in enumerate(pairs)
                              if gmask >> ii & 1)
            for dummy in (True, False):
                vals = rigid_values(k, edges, dummy)
                for t in (0, 1):
                    assert vals[t] == sigma_value(k, edges, dummy, t), \
                        (k, edges, dummy, t)
                    cnt += 1
    print(f"   {cnt} agree")

    print("== sigma-explicit vs the verified echo_solver.fifo_value ==")
    from echo_solver import fifo_value, SynthForm
    rng = random.Random(2026)
    cnt = 0
    for _ in range(12):
        k = 5
        pairs = [(i, j) for i in range(k) for j in range(i + 1, k)]
        edges = frozenset(p for p in pairs if rng.random() < 0.5)
        B = [[0] * k for _ in range(k)]
        for (i, j) in edges:
            B[i][j] = B[j][i] = 1
        f: Any = SynthForm(k, [0] * k, B)  # duck-types Form for fifo_value
        for dummy in (True, False):
            for t in (0, 1):
                assert sigma_value(k, edges, dummy, t) == \
                    fifo_value(f, (1 << k) - 1, t, dummy=dummy), \
                    (edges, dummy, t)
                cnt += 1
    print(f"   {cnt} agree (SynthForm bridge, q = 0)")

    print("== reduction identities on random legal plays (R1/R2/R4) ==")
    rng = random.Random(7)
    for _ in range(400):
        k = rng.randrange(2, 7)
        dummy = rng.choice((False, True))
        n = k + int(dummy)
        pairs = [(i, j) for i in range(k) for j in range(i + 1, k)]
        edges = frozenset(p for p in pairs if rng.random() < 0.5)
        adj = adj_of(n, edges)
        hadj = [adj[i] & ~((2 << i) - 1) for i in range(n)]
        u, sigma, tt = (1 << n) - 1, 0, 0
        seq: tuple = ()
        ko = False
        windows = {}
        flips = 0
        live_degree_sum = 0
        while u or seq:
            omask = 0
            for c in seq:
                omask |= 1 << c
            moves = legal_moves(n, adj, u, seq, ko)
            if not moves:
                assert u == 0 and len(seq) == 1 and ko
                ko = False  # the unique terminal pass
                tt += 1
                continue
            opens = [move for move in moves if move[0] == "o"]
            closes = [move for move in moves if move[0] == "c"]
            if opens and (not closes or rng.random() < 0.6):
                _kind, i, _flip, u2, seq2, ko2 = rng.choice(opens)
                live_degree_sum ^= bin(adj[i] & (u | omask)).count("1") & 1
                sigma ^= bin(omask & hadj[i]).count("1") & 1
                windows[i] = [tt, None]
                u, seq, ko = u2, seq2, ko2
            else:
                _kind, c, flip, u2, seq2, ko2 = closes[0]
                sigma ^= bin(omask & hadj[c]).count("1") & 1
                flips ^= flip
                windows[c][1] = tt
                u, seq, ko = u2, seq2, ko2
            tt += 1
        overlap = 0
        for (i, j) in edges:
            (a1, b1), (a2, b2) = windows[i], windows[j]
            assert not (a1 < a2 and b2 < b1) and not (a2 < a1 and b1 < b2), \
                "FIFO nesting impossible (R1)"
            if a1 < a2 < b1 or a2 < a1 < b2:
                overlap ^= 1
        assert sigma == overlap, "sigma != overlap parity (R1)"
        assert flips == (len(edges) & 1) ^ sigma, "flips != |E| ^ sigma (R2)"
        assert flips == live_degree_sum, \
            "flips != sum of live degrees at opens (R4)"
    print("   400 random legal plays (dummy on/off): no nesting; sigma == overlap;"
          " odd-close flips == |E| ^ sigma == live-open degree sum")

    print("== nonempty-queue squeeze witness ==")
    # The path z-f-y-h with queue (f,h) and U={y,z}.  The front f is
    # even, yet either open makes f odd and closing f exposes odd h.
    squeeze_adj = adj_of(4, {(0, 1), (1, 2), (2, 3)})
    moves = legal_moves(4, squeeze_adj, (1 << 0) | (1 << 2), (1, 3), False)
    assert {(kind, coin) for kind, coin, *_rest in moves} == \
        {("o", 0), ("o", 2), ("c", 1)}
    for _kind, _coin, _flip, u2, seq2, ko2 in moves:
        replies = legal_moves(4, squeeze_adj, u2, seq2, ko2)
        assert any(kind == "c" and flip == 1
                   for kind, _coin, flip, *_rest in replies)
    print("   every defender move exposes an immediate odd close")

    print("== first recursive-menu witness ==")
    corridor_k, corridor_edges = decode_graph6("GCRU]w")
    assert corridor_k == 8
    assert rigid_values(corridor_k, corridor_edges, True) == [0, 0]
    assert not strategy_holds(corridor_k, corridor_edges, 1, menu_version=3)
    assert strategy_holds(corridor_k, corridor_edges, 1, menu_version=4)
    print("   GCRU]w defeats R3/D3; an even odd-corridor poison repairs it")

    nonrepair_k, nonrepair_edges = decode_graph6("GCZMmw")
    assert nonrepair_k == 8
    assert rigid_values(nonrepair_k, nonrepair_edges, True) == [1, 1]
    assert not strategy_holds(nonrepair_k, nonrepair_edges, 1, menu_version=4)
    assert strategy_holds(nonrepair_k, nonrepair_edges, 1, menu_version=5)
    print("   GCZMmw defeats the corridor menu; deliberate nonrepair needs"
          " the no-self-flip envelope")

    print("== affine-response and action-switch witnesses ==")
    anti_mover_graphs = (
        "GCZN^{", "GCrU~{", "GEhvn{", "GCx}~{",
        "GEjt~{", "GEl~v{", "GUZv^{",
    )
    for graph6 in anti_mover_graphs:
        order, edges = decode_graph6(graph6)
        assert order == 8
        assert rigid_values(order, edges, False) == [1, 0]
    for graph6 in ("GCZN^{", "GEjt~{"):
        order, edges = decode_graph6(graph6)
        assert minimum_worst_switches(order, edges) == 2
    response_vectors = close_first_response_vectors(5)
    certificate = (359, 443, 221, 222, 223)
    assert len(response_vectors) == 132 and 0 not in response_vectors
    assert not any(x ^ y in response_vectors
                   for x in response_vectors for y in response_vectors
                   if x != y)
    assert all(x in response_vectors for x in certificate)
    assert functools.reduce(int.__xor__, certificate) == 0
    print("   7 no-dummy anti-mover classes; two exact two-switch minima;"
          " k=5 close-first affine support minimum 5")
    print("validate: PASS")


def stage_screen(kmax: int) -> None:
    for k in range(2, kmax + 1):
        t0 = time.time()
        reps = iso_classes(k)
        fails_d, bad = [], []
        for edges in reps:
            par = len(edges) & 1
            if rigid_values(k, edges, True) != [par, par]:
                fails_d.append(tuple(sorted(edges)))
            vn = rigid_values(k, edges, False)
            if vn != [par, par]:
                bad.append((tuple(sorted(edges)), vn))
        niso = sum(1 for (e, _v) in bad
                   if min(sum(1 for (a, b) in e if v in (a, b))
                          for v in range(k)) == 0) if bad else 0
        print(f"k={k}: {len(reps)} classes | WITH dummy fails: {len(fails_d)}"
              f" | no-dummy Bad: {len(bad)} (with isolated vertex: {niso},"
              f" all mover-controlled:"
              f" {all(v == [0, 1] for (_e, v) in bad)})"
              f"  [{time.time()-t0:.0f}s]", flush=True)
        for e in fails_d:
            print(f"   THEOREM COUNTEREXAMPLE {e}")


def stage_strategy(kmax: int) -> None:
    for k in range(2, kmax + 1):
        t0 = time.time()
        reps = iso_classes(k)
        fails = [(tuple(sorted(e)), seat)
                 for e in reps for seat in (0, 1)
                 if not strategy_holds(k, e, seat)]
        print(f"k={k}: {len(reps)} classes x 2 seats | no-self-flip/D3 fails:"
              f" {len(fails)}  [{time.time()-t0:.0f}s]", flush=True)
        for f in fails[:8]:
            print(f"   FAIL {f}")


def stage_graph6(path: str, jobs: int, check_strategy: bool) -> None:
    """Screen an externally generated nonisomorphic graph6 census.

    ``nauty-geng -q 8`` is the intended producer.  The generator remains an
    external research tool; the checked game and menu solvers stay here.
    """
    if jobs < 1:
        raise ValueError("jobs must be positive")
    records = [line for line in Path(path).read_text(encoding="ascii").splitlines()
               if line and not line.startswith(">>")]
    if not records:
        raise ValueError(f"no graph6 records in {path}")
    orders = {decode_graph6(line)[0] for line in records}
    menu = "no-self-flip/D3" if check_strategy else "skipped"
    print(f"graph6: {len(records)} records, orders={sorted(orders)},"
          f" jobs={jobs}, strict_menu={menu}", flush=True)
    t0 = time.time()
    items = ((line, check_strategy) for line in records)
    failures = []
    with multiprocessing.Pool(processes=jobs) as pool:
        for index, result in enumerate(
                pool.imap_unordered(verify_graph6_record, items, chunksize=1), 1):
            if result is not None:
                failures.append(result)
                pool.terminate()
                break
            if index % 1000 == 0:
                print(f"   {index}/{len(records)} [{time.time()-t0:.0f}s]",
                      flush=True)
    if failures:
        raise AssertionError(f"graph6 counterexample: {failures[0]}")
    print(f"graph6: PASS ({len(records)} records in {time.time()-t0:.0f}s)")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", nargs="?", default="all",
                         choices=("validate", "screen", "strategy", "graph6",
                                  "all"))
    parser.add_argument("kmax", nargs="?", type=int, default=5)
    parser.add_argument("--graph6-path")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--skip-strategy", action="store_true")
    args = parser.parse_args()
    if args.stage in ("validate", "all"):
        stage_validate()
    if args.stage in ("screen", "all"):
        stage_screen(args.kmax)
    if args.stage in ("strategy", "all"):
        stage_strategy(args.kmax)
    if args.stage == "graph6":
        if args.graph6_path is None:
            parser.error("graph6 requires --graph6-path")
        stage_graph6(args.graph6_path, args.jobs, not args.skip_strategy)


if __name__ == "__main__":
    main()
