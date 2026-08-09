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

STATUS (2026-08-07), machine-verified by this file:
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
  * The proved two-bit handshake refinement colours a vertex by degree parity
    and odd-neighbour parity.  Every same-colour second reply is minimax-winning
    through k = 7; opening the dummy first is also winning throughout that
    census.  The optional ``refinement`` stage reproduces this root screen.
  * A stronger even-board finite target also survives: on every graph through
    even order 8, the second player can restore the actual flip score to zero
    after every one of their moves.  ``zero_normalized_safe`` is the exact
    ranked repair-forest recursion, and stage ``neutral`` checks a supplied
    even-order graph6 census.  This is tested evidence, not a general proof.
    The normalized subtree is not a graph-independent affine carrier: an
    exact pair of order-8 Euler graphs has a primary repair forest but a
    deterministic attack whose 88 primary-normalized response histories all
    have secondary Euler moment 1.  ``normalized_secondary_moment`` pins this
    obstruction; it does not refute the scalar primary strategy.
  * Bounded affine certificates fail even after quotienting by cuts.  A
    reachable singleton-front subtree projects onto the causal simplex cap
    ``{1^r} union {1^r + e_i}``.  For ``r >= 4`` it has no zero or zero-sum
    triple, and its unique nonempty projected relation has support ``r`` for
    odd ``r`` and ``r+1`` for even ``r``.  The first ``r=4`` witness attains
    the five-leaf bound exactly; ``close_first_schedule_quotient`` checks its
    schedules and quotient labels.
    Pairwise ancestor escape is also false: immediately before that subtree,
    one target-forcing attack keeps the two defender children ``OPEN(1)`` and
    ``OPEN(5)`` inside a 52-point quotient cap.  The independent finite
    safety-game recursion ``quotient_target_response_labels`` pins it.
    More strongly, a five-real-vertex spine ends in ``X={1,3}`` while every
    sibling at every preceding defender fan admits a compatible attack
    avoiding ``{0,2} = {0} union (X+X)``.  Thus even full ancestor-sibling
    escape is false; the required flow must couple several branches at once.
  * The terminal cut boundary has an exact event-controller formula:
    deg_D(v) = n + o_v + c_v modulo two on all vertices, including the
    dummy, when the unique forced pass is omitted from the event positions.
    Deleting the dummy coordinate contributes precisely its disjointness
    bit.  The randomized reduction checks below pin both forms.
  * Three stronger induction templates now have pinned order-8 failures.
    Equal two-bit colour does not make an ordered first cell safe; one opener
    can have no safe same-colour mate; and a Safe even-U checkpoint can require
    a zero CLOSE as its unique response to an attacker OPEN.  ``validate``
    checks all three with the shared operational checkpoint solver.

The old description of the empty-queue domination device as the unique
local obstruction was too strong.  A nonempty queue can squeeze too: on
the path z-f-y-h, queue (f,h), U={y,z}, and an even front f, either open
makes f odd while closing f exposes the odd front h.  The dummy defeats
this squeeze while untouched, but a proof must track the queued case.

Stages: validate | screen [K] | strategy [K] | refinement [K] | graph6 |
neutral | all (default K = 5; the k=7 screen ~45 s, k=7 strategy ~25 s).
``graph6`` and ``neutral`` consume a nauty ``geng`` census through
``--graph6-path`` and can parallelize with
``--jobs`` (for example, ``geng -q 8 > graphs8.g6`` followed by
``python linking_game.py neutral --graph6-path graphs8.g6 --jobs 12``).
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


def even_checkpoint_safe(k: int, edges, u: int, seq: tuple[int, ...],
                         *, ko: bool = False, mover: int = 0, score: int = 0,
                         zero_normalized: bool = False) -> bool:
    """Whether the fixed Even defender wins from one explicit checkpoint.

    ``mover == 0`` is the universal Odd attacker and ``mover == 1`` the
    existential Even defender.  With ``zero_normalized``, every Even move
    must restore the accumulated flip score to zero.  The unrestricted form
    asks only for zero terminal score.  This shared operational recursion is
    useful for pinning proof-template counterexamples at non-root states.
    """
    adj = adj_of(k, edges)
    memo: dict = {}

    def safe(u0, seq0, ko0, mover0, g0):
        if u0 == 0 and not seq0:
            return g0 == 0
        key = (u0, seq0, ko0, mover0, g0)
        result = memo.get(key)
        if result is not None:
            return result
        moves = legal_moves(k, adj, u0, seq0, ko0)
        if not moves:
            # A pass is a move.  In particular, a zero-normalizing Even pass
            # requires that the score already be zero.
            result = (not zero_normalized or mover0 != 1 or g0 == 0) and \
                safe(u0, seq0, False, 1 - mover0, g0)
        elif mover0 == 0:
            result = all(safe(u2, seq2, ko2, 1, g0 ^ flip)
                         for (_kind, _coin, flip, u2, seq2, ko2) in moves)
        elif zero_normalized:
            result = any(g0 ^ flip == 0 and
                         safe(u2, seq2, ko2, 0, 0)
                         for (_kind, _coin, flip, u2, seq2, ko2) in moves)
        else:
            result = any(safe(u2, seq2, ko2, 0, g0 ^ flip)
                         for (_kind, _coin, flip, u2, seq2, ko2) in moves)
        memo[key] = result
        return result

    return safe(u, seq, ko, mover, score)


def zero_normalized_safe(k: int, edges) -> bool:
    """Whether the second player can restore flip score zero after each move.

    This is the exact scalar predicate behind Proposition ``repair-forest`` in
    ``writeups/linking_affine.tex``.  The graph has no dummy and is intended to
    have even order.  Odd moves universally; Even chooses a legal reply, but
    every resulting Even move (including the unique forced pass) must leave
    accumulated flip parity zero.  The recursive strategy certificate is
    strictly stronger than merely winning the final even target.
    """
    return even_checkpoint_safe(
        k, edges, (1 << k) - 1, (), zero_normalized=True)


def two_bit_root_failures(k: int, edges) -> list[tuple]:
    """Failures of the proved two-bit root selector on ``G + d``.

    This is an exact minimax check of a stronger *tested* statement, not the
    proof of :ref:`lem:two-bit` in ``writeups/linking_affine.tex``.  If the odd
    player opens a real vertex, test every same-colour reply, where
    ``colour(v) = (deg(v), number of odd-degree neighbours) mod 2`` in the
    relevant even-order graph.  When ``k`` is even and the odd player opens the
    unmatched dummy, test every real reply.  Also test the first-seat rule that
    the even player opens the dummy.
    """
    n = k + 1
    dummy = k
    adj = adj_of(n, edges)
    full = (1 << n) - 1
    memo: dict = {}

    def even_wins(seat, u, seq, ko, mover, g):
        # Once U is empty, every remaining close has charge zero.
        if u == 0:
            return g == 0
        key = (seat, u, seq, ko, mover, g)
        result = memo.get(key)
        if result is not None:
            return result
        moves = legal_moves(n, adj, u, seq, ko)
        if not moves:
            result = even_wins(seat, u, seq, False, 1 - mover, g)
        else:
            values = [even_wins(seat, u2, seq2, ko2, 1 - mover, g ^ flip)
                      for (_kind, _coin, flip, u2, seq2, ko2) in moves]
            result = any(values) if mover == seat else all(values)
        memo[key] = result
        return result

    failures = []
    if not even_wins(0, full ^ (1 << dummy), (dummy,), True, 1, 0):
        failures.append(("first-open-dummy",))

    colour_order = n if k % 2 else k
    parity = [bin(adj[v] & ((1 << colour_order) - 1)).count("1") & 1
              for v in range(colour_order)]
    odd = sum(1 << v for v, bit in enumerate(parity) if bit)
    colour = [(parity[v], bin(adj[v] & odd).count("1") & 1)
              for v in range(colour_order)]
    for v in range(n):
        if k % 2 == 0 and v == dummy:
            replies = range(k)
        else:
            replies = [w for w in range(colour_order)
                       if w != v and colour[w] == colour[v]]
            if not replies:
                failures.append(("no-mate", v))
                continue
        for w in replies:
            u = full ^ (1 << v) ^ (1 << w)
            if not even_wins(1, u, (v, w), False, 0, 0):
                failures.append(("second-reply", v, w))
    return failures


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


def verify_neutral_graph6_record(line: str):
    """Return an even-board zero-normalization counterexample, if any."""
    k, edges = decode_graph6(line)
    if k % 2:
        return ("odd-order-input", line.strip(), k)
    if not zero_normalized_safe(k, edges):
        return ("zero-normalized", line.strip())
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


def close_first_schedule_quotient(
        k: int, word: tuple[tuple[str, int | None], ...],
        *, policy_after: int, front: int = 0) -> int:
    """Validate one schedule and return its fixed-front cut quotient.

    Vertices ``0..k-1`` are real and ``k`` is the isolated dummy.  Player 0
    moves in the even word positions.  From ``policy_after`` onward, each of
    player 0's moves must close when possible and otherwise open the least
    untouched vertex.  Quotient bits use lexicographic edge order after
    deleting ``front``.

    This is a small exact checker for the causal-simplex witness in
    ``writeups/linking_affine.tex``; game legality is graph-independent.
    """
    n = k + 1
    u = (1 << n) - 1
    seq: tuple[int, ...] = ()
    ko = False
    edge_order = tuple(
        (i, j) for i in range(k) for j in range(i + 1, k))
    edge_bit = {edge: bit for bit, edge in enumerate(edge_order)}
    score = 0

    for turn, (kind, coin) in enumerate(word):
        moves = legal_moves(n, [0] * n, u, seq, ko)
        if turn >= policy_after and turn % 2 == 0:
            closes = [move for move in moves if move[0] == "c"]
            expected = closes[0] if closes else min(
                (move for move in moves if move[0] == "o"),
                key=lambda move: move[1],
            )
            assert (kind, coin) == expected[:2]

        if kind == "p":
            assert coin is None and not moves
            ko = False
            continue

        chosen = next(
            (move for move in moves if move[:2] == (kind, coin)), None)
        assert chosen is not None, (turn, kind, coin, u, seq, ko)
        _kind, chosen_coin, _flip, u2, seq2, ko2 = chosen
        if kind == "c" and chosen_coin != k:
            for other in range(k):
                if u >> other & 1:
                    edge = (min(chosen_coin, other),
                            max(chosen_coin, other))
                    score ^= 1 << edge_bit[edge]
        u, seq, ko = u2, seq2, ko2

    assert u == 0 and not seq
    quotient = 0
    quotient_bit = 0
    for i in range(k):
        if i == front:
            continue
        for j in range(i + 1, k):
            if j == front:
                continue
            ij = (score >> edge_bit[i, j]) & 1
            fi = (score >> edge_bit[min(front, i), max(front, i)]) & 1
            fj = (score >> edge_bit[min(front, j), max(front, j)]) & 1
            quotient |= (ij ^ fi ^ fj) << quotient_bit
            quotient_bit += 1
    return quotient


def quotient_target_response_labels(
        k: int, target: frozenset[int], u: int, seq: tuple[int, ...],
        *, ko: bool = False, mover: int = 0, score: int = 0,
        front: int = 0,
        root_defender_moves: frozenset[tuple[str, int]] | None = None,
        ) -> frozenset[int] | None:
    """Response labels for one lexicographic target-forcing attacker.

    The score is the disjointness vector modulo cut, in the fixed ``front``
    chart.  Attacker 0 chooses the first legal child which keeps every
    terminal label in ``target``; defender 1 is universal.  At the supplied
    root only, ``root_defender_moves`` may restrict the defender fan.  Return
    ``None`` when no such attacker strategy exists.

    This exact finite safety-game recursion checks the two-sibling cap
    obstruction in ``writeups/linking_affine.tex``.
    """
    n = k + 1

    def close_quotient(closing: int, untouched: int) -> int:
        if closing == k:
            return 0

        def edge(a: int, b: int) -> int:
            return int(closing == a and (untouched >> b & 1) or
                       closing == b and (untouched >> a & 1))

        out = 0
        bit = 0
        for i in range(k):
            if i == front:
                continue
            for j in range(i + 1, k):
                if j == front:
                    continue
                out |= (edge(i, j) ^ edge(front, i) ^ edge(front, j)) << bit
                bit += 1
        return out

    @functools.lru_cache(None)
    def rec(u0: int, seq0: tuple[int, ...], ko0: bool,
            mover0: int, score0: int) -> frozenset[int] | None:
        if u0 == 0 and not seq0:
            return frozenset({score0}) if score0 in target else None
        moves = legal_moves(n, [0] * n, u0, seq0, ko0)
        if not moves:
            return rec(u0, seq0, False, 1 - mover0, score0)

        children = []
        for kind, coin, _flip, u2, seq2, ko2 in sorted(
                moves, key=lambda move: move[:2]):
            increment = close_quotient(coin, u0) if kind == "c" else 0
            child = rec(u2, seq2, ko2, 1 - mover0, score0 ^ increment)
            children.append(child)
        if mover0 == 0:
            return next((child for child in children if child is not None),
                        None)
        if any(child is None for child in children):
            return None
        return frozenset().union(*children)

    if root_defender_moves is None:
        return rec(u, seq, ko, mover, score)
    assert mover == 1
    selected = [move for move in legal_moves(n, [0] * n, u, seq, ko)
                if move[:2] in root_defender_moves]
    assert {move[:2] for move in selected} == root_defender_moves
    labels = []
    for kind, coin, _flip, u2, seq2, ko2 in selected:
        increment = close_quotient(coin, u) if kind == "c" else 0
        child = rec(u2, seq2, ko2, 0, score ^ increment)
        if child is None:
            return None
        labels.append(child)
    return frozenset().union(*labels)


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


def normalized_secondary_moment(
        k: int, primary_edges, secondary_edges) -> tuple[int, int]:
    """Secondary score mask below one exact primary-normalized attack.

    The defender may use every reply which restores the ``primary`` score to
    zero after their move.  At attacker nodes, choose lexicographically by
    whether the child secondary mask differs from ``{1}``, then leaf count,
    then prefer CLOSE, then move name.  This constructs a deterministic
    positional attack and returns ``(secondary_mask, terminal_history_count)``.

    It is a counterexample generator for the tempting *graph-independent*
    strengthening of zero normalization: even when the primary graph has a
    repair forest, its normalized response affine set need not meet Cut.
    """
    primary = adj_of(k, primary_edges)
    secondary = adj_of(k, secondary_edges)

    @functools.lru_cache(None)
    def rec(u: int, seq: tuple[int, ...], ko: bool,
            mover: int, primary_score: int,
            secondary_score: int) -> tuple[int, int]:
        if u == 0 and not seq:
            return 1 << secondary_score, 1
        moves = legal_moves(k, primary, u, seq, ko)
        if not moves:
            if mover == 1 and primary_score:
                return 0, 0
            return rec(u, seq, False, 1 - mover,
                       primary_score, secondary_score)

        children = []
        for kind, coin, flip_primary, u2, seq2, ko2 in moves:
            flip_secondary = 0 if kind == "o" else \
                (secondary[coin] & u).bit_count() & 1
            child = rec(u2, seq2, ko2, 1 - mover,
                        primary_score ^ flip_primary,
                        secondary_score ^ flip_secondary)
            if mover == 0 or primary_score ^ flip_primary == 0:
                children.append((kind, coin, child))

        if mover == 0:
            _kind, _coin, answer = min(
                children,
                key=lambda item: (
                    item[2][0] != 2,
                    item[2][1],
                    item[0] == "o",
                    item[0],
                    item[1],
                ),
            )
            return answer

        mask = 0
        count = 0
        for _kind, _coin, (child_mask, child_count) in children:
            mask |= child_mask
            count += child_count
        return mask, count

    return rec((1 << k) - 1, (), False, 0, 0, 0)


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

    print("== zero-normalized repair recursion (even k <= 4 exhaustive) ==")
    cnt = 0
    for k in (2, 4):
        pairs = [(i, j) for i in range(k) for j in range(i + 1, k)]
        for gmask in range(1 << len(pairs)):
            edges = frozenset(p for ii, p in enumerate(pairs)
                              if gmask >> ii & 1)
            assert zero_normalized_safe(k, edges), (k, edges)
            cnt += 1
    print(f"   {cnt} even boards admit repair forests")

    print("== exact failures of stronger response lemmas ==")
    colour_edges = frozenset({
        (0, 1), (0, 3), (0, 5), (0, 7), (1, 2), (1, 4),
        (1, 5), (1, 7), (2, 4), (2, 6), (2, 7), (3, 4),
        (3, 7), (4, 5), (4, 6), (4, 7), (5, 7), (6, 7),
    })
    full8 = (1 << 8) - 1

    def two_bit_colours(edges):
        adj = adj_of(8, edges)
        parity = [bin(adj[v]).count("1") & 1 for v in range(8)]
        odd = sum(1 << v for v, bit in enumerate(parity) if bit)
        return [(parity[v], bin(adj[v] & odd).count("1") & 1)
                for v in range(8)]

    def first_spoilers(edges, u, seq):
        adj = adj_of(8, edges)
        spoilers = []
        for kind, coin, flip, u2, seq2, ko2 in legal_moves(
                8, adj, u, seq, False):
            if not even_checkpoint_safe(
                    8, edges, u2, seq2, ko=ko2, mover=1, score=flip):
                spoilers.append((kind, coin))
        return spoilers

    colour_bits = two_bit_colours(colour_edges)
    assert colour_bits[6] == colour_bits[7]
    assert colour_bits[5][0] != colour_bits[6][0]
    colour_u = full8 ^ (1 << 6) ^ (1 << 7)
    assert not even_checkpoint_safe(
        8, colour_edges, colour_u, (6, 7))
    assert even_checkpoint_safe(
        8, colour_edges, colour_u, (7, 6))
    assert first_spoilers(colour_edges, colour_u, (6, 7)) == [("o", 5)]

    sole_colour_edges = frozenset({
        (0, 4), (0, 5), (1, 5), (2, 5), (0, 6), (1, 6),
        (3, 6), (5, 6), (0, 7), (1, 7), (2, 7), (4, 7),
        (5, 7), (6, 7),
    })
    assert decode_graph6("G?ben[") == (8, sole_colour_edges)
    sole_colours = two_bit_colours(sole_colour_edges)
    assert [v for v in range(8)
            if v != 2 and sole_colours[v] == sole_colours[2]] == [7]
    sole_u = full8 ^ (1 << 2) ^ (1 << 7)
    assert not even_checkpoint_safe(
        8, sole_colour_edges, sole_u, (2, 7))
    assert even_checkpoint_safe(
        8, sole_colour_edges, sole_u, (7, 2))
    assert first_spoilers(sole_colour_edges, sole_u, (2, 7)) == [("o", 3)]

    completion_edges = frozenset({
        (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
        (1, 2), (1, 3), (1, 4), (1, 7), (2, 3), (2, 6),
        (2, 7), (3, 5), (3, 7), (5, 6), (5, 7),
    })
    u = sum(1 << v for v in (0, 1, 2, 5, 6, 7))
    seq = (4, 3)
    assert even_checkpoint_safe(
        8, completion_edges, u, seq, zero_normalized=True)
    adj = adj_of(8, completion_edges)
    attack = next(move for move in legal_moves(8, adj, u, seq, False)
                  if move[:2] == ("o", 6))
    _kind, _coin, attack_flip, u1, seq1, ko1 = attack
    safe_replies = []
    for reply in legal_moves(8, adj, u1, seq1, ko1):
        kind, coin, flip, u2, seq2, ko2 = reply
        if attack_flip ^ flip == 0 and even_checkpoint_safe(
                8, completion_edges, u2, seq2, ko=ko2,
                score=0, zero_normalized=True):
            safe_replies.append((kind, coin))
    assert safe_replies == [("c", 4)], safe_replies

    profile_a = frozenset({(2, 3), (0, 4), (1, 4)})
    profile_b = frozenset({(2, 3), (2, 4), (0, 2), (1, 2)})
    profile_u = sum(1 << v for v in (2, 3, 4))

    def front_signature(edges):
        adj = adj_of(5, edges)
        queue_graph = ((adj[0] >> 1) & 1,)
        untouched = sorted(
            ((adj[u] >> 0) & 1, (adj[u] >> 1) & 1,
             (adj[u] & profile_u).bit_count() & 1)
            for u in (2, 3, 4))
        return queue_graph, untouched

    assert front_signature(profile_a) == front_signature(profile_b)
    assert even_checkpoint_safe(
        5, profile_a, profile_u, (0, 1), zero_normalized=True)
    assert not even_checkpoint_safe(
        5, profile_b, profile_u, (0, 1), zero_normalized=True)

    def named_move(n, adj, u, seq, ko, name):
        return next(move for move in legal_moves(n, adj, u, seq, ko)
                    if move[:2] == name)

    adj_a = adj_of(5, profile_a)
    for attack_name, reply_name in (
            (("c", 0), ("c", 1)),
            (("o", 2), ("o", 3)),
            (("o", 3), ("o", 2)),
            (("o", 4), ("o", 2))):
        attack = named_move(5, adj_a, profile_u, (0, 1), False,
                            attack_name)
        _ak, _av, af, au, aq, ako = attack
        reply = named_move(5, adj_a, au, aq, ako, reply_name)
        _rk, _rv, rf, ru, rq, rko = reply
        assert af ^ rf == 0
        assert even_checkpoint_safe(
            5, profile_a, ru, rq, ko=rko, mover=0, score=0,
            zero_normalized=True)

    adj_b = adj_of(5, profile_b)
    attack = named_move(5, adj_b, profile_u, (0, 1), False, ("c", 0))
    _ak, _av, af, au, aq, ako = attack
    normalized = [move for move in legal_moves(5, adj_b, au, aq, ako)
                  if af ^ move[2] == 0]
    assert [move[:2] for move in normalized] == [("c", 1)]
    _rk, _rv, _rf, ru, rq, rko = normalized[0]
    open_two = named_move(5, adj_b, ru, rq, rko, ("o", 2))
    _ok, _ov, of, ou, oq, oko = open_two
    forced_opens = [move for move in legal_moves(5, adj_b, ou, oq, oko)
                    if of ^ move[2] == 0]
    assert [move[:2] for move in forced_opens] == [("o", 3), ("o", 4)]
    assert all(not even_checkpoint_safe(
        5, profile_b, move[3], move[4], ko=move[5], mover=0,
        score=0, zero_normalized=True) for move in forced_opens)
    print("   same-colour orientation, sole-colour mate, and open-completion"
          " conjectures have pinned order-8 counterexamples;")
    print("   identical rich front signatures can have opposite safety")

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
        touch_windows = {}
        touch = 0
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
                touch_windows[i] = [touch, None]
                u, seq, ko = u2, seq2, ko2
            else:
                _kind, c, flip, u2, seq2, ko2 = closes[0]
                sigma ^= bin(omask & hadj[c]).count("1") & 1
                flips ^= flip
                windows[c][1] = tt
                touch_windows[c][1] = touch
                u, seq, ko = u2, seq2, ko2
            touch += 1
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
        disjoint_degree = [0] * n
        for i in range(n):
            oi, ci = touch_windows[i]
            for j in range(i + 1, n):
                oj, cj = touch_windows[j]
                if ci < oj or cj < oi:
                    disjoint_degree[i] ^= 1
                    disjoint_degree[j] ^= 1
        for v, (opened, closed) in touch_windows.items():
            assert disjoint_degree[v] == (n + opened + closed) & 1, \
                "endpoint-controller boundary identity failed"
        if dummy:
            d = k
            od, cd = touch_windows[d]
            for v in range(k):
                ov, cv = touch_windows[v]
                dvd = int(cv < od or cd < ov)
                real_degree = disjoint_degree[v] ^ dvd
                projected_open = ov - int(od < ov) - int(cd < ov)
                projected_close = cv - int(od < cv) - int(cd < cv)
                assert real_degree == \
                    (k + projected_open + projected_close) & 1, \
                    "projected endpoint-controller identity failed"
    print("   400 random legal plays (dummy on/off): no nesting; sigma == overlap;"
          " odd-close flips == |E| ^ sigma == live-open degree sum;"
          " endpoint boundary identities hold")

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

    print("== causal-simplex quotient cap ==")
    prefix = (
        ("o", 0), ("o", 6), ("c", 0), ("o", 5), ("c", 6),
    )

    def event_word(text: str) -> tuple[tuple[str, int | None], ...]:
        return tuple(
            ("p", None) if token == "P"
            else (token[0].lower(), int(token[1:]))
            for token in text.split()
        )

    continuations = tuple(map(event_word, (
        "O3 C5 C3 O1 O2 C1 C2 O4 P C4",
        "O2 C5 O4 C2 O3 C4 O1 C3 C1",
        "O1 C5 O3 C1 O4 C3 O2 C4 C2",
        "C5 O1 O3 C1 O4 C3 O2 C4 C2",
        "O4 C5 O1 C4 C1 O2 O3 C2 C3",
    )))
    quotient_labels = tuple(
        close_first_schedule_quotient(
            6, prefix + continuation, policy_after=len(prefix))
        for continuation in continuations
    )
    assert quotient_labels == (766, 797, 853, 861, 491)
    assert functools.reduce(int.__xor__, quotient_labels) == 0
    star_bits = (3, 6, 8, 9)  # 15,25,35,45 in the quotient edge order
    star_labels = {
        sum(((label >> bit) & 1) << out_bit
            for out_bit, bit in enumerate(star_bits))
        for label in quotient_labels
    }
    assert star_labels == {0b1111} | {
        0b1111 ^ (1 << bit) for bit in range(4)
    }
    assert 0 not in star_labels
    assert not any(x ^ y in star_labels
                   for x in star_labels for y in star_labels if x != y)
    print("   reachable r=4 cap has no quotient singleton/triple;"
          " five compatible histories XOR to Cut")

    sibling_cap = frozenset({
        7, 11, 13, 14, 15, 29, 30, 31, 71, 78, 79, 141,
        328, 360, 382, 395, 411, 413, 456, 493, 494, 509, 510,
        523, 551, 584, 600, 638, 679, 683, 712, 730, 766, 776,
        777, 792, 827, 829, 832, 836, 840, 844, 871, 887, 955,
        957, 962, 967, 978, 983, 1000, 1003,
    })
    assert 0 not in sibling_cap
    assert not any(x ^ y in sibling_cap
                   for x in sibling_cap for y in sibling_cap if x != y)
    assert functools.reduce(int.__xor__, (7, 11, 13, 14, 15)) == 0
    sibling_labels = quotient_target_response_labels(
        6, sibling_cap, sum(1 << i for i in range(1, 6)), (6,),
        mover=1, root_defender_moves=frozenset({("o", 1), ("o", 5)}),
    )
    assert sibling_labels == sibling_cap
    print("   one level earlier, two complete defender siblings remain inside"
          " an exact 52-point cap")

    # A still stronger ancestor rule fails at five real vertices.  Along the
    # selected path, the terminal child image is X={1,3}, so its forbidden
    # escape set {0} union (X+X) is {0,2}.  Every sibling at every prior
    # defender node has its own compatible target-avoiding attack.  Since the
    # subtrees are disjoint, those attacks combine into one deterministic
    # root strategy.
    avoid_escape = frozenset(set(range(1 << 6)) - {0, 2})
    full6 = (1 << 6) - 1

    def assert_avoids(u: int, seq: tuple[int, ...], score: int) -> None:
        labels = quotient_target_response_labels(
            5, avoid_escape, u, seq, mover=0, score=score)
        assert labels is not None and labels.isdisjoint({0, 2})

    # Root action O0; at the first defender fan retain O2 and check O1,O3,O4,O5.
    for coin in (1, 3, 4, 5):
        assert_avoids(full6 ^ 1 ^ (1 << coin), (0, coin), 0)
    # Selected O2,C0 has quotient score 25.  Retain O1 and check C2,O3,O4,O5.
    middle_u = (1 << 1) | (1 << 3) | (1 << 4) | (1 << 5)
    assert_avoids(middle_u, (), 0)
    for coin in (3, 4, 5):
        assert_avoids(middle_u ^ (1 << coin), (2, coin), 25)
    # Selected O1,O5 reaches the final defender fan.  Retain C2 and check O3,O4.
    last_u = (1 << 3) | (1 << 4)
    for coin in (3, 4):
        assert_avoids(last_u ^ (1 << coin), (2, 1, 5, coin), 25)
    terminal_cap = quotient_target_response_labels(
        5, frozenset({1, 3}), last_u, (1, 5), mover=0, score=1)
    assert terminal_cap == frozenset({1, 3})
    print("   full ancestor cap-escape is false: X={1,3}, while every prior"
          " sibling avoids {0,2}=zero union (X+X)")

    print("== normalized affine-Cut obstruction ==")
    primary = frozenset({
        (0, 2), (0, 3), (0, 6), (0, 7), (1, 3), (1, 5),
        (2, 3), (2, 4), (2, 6), (3, 5), (3, 6), (3, 7),
        (4, 7), (5, 6), (5, 7),
    })
    secondary = frozenset({
        (0, 1), (0, 4), (0, 6), (0, 7), (1, 2), (1, 3),
        (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 7),
        (3, 5), (4, 5), (4, 7), (5, 6), (5, 7), (6, 7),
    })
    assert all(degree.bit_count() % 2 == 0
               for degree in adj_of(8, primary))
    assert all(degree.bit_count() % 2 == 0
               for degree in adj_of(8, secondary))
    assert zero_normalized_safe(8, primary)
    assert normalized_secondary_moment(8, primary, secondary) == (2, 88)
    print("   Euler primary repair forest has 88 normalized response histories;"
          " every one has secondary Euler moment 1")
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


def stage_refinement(kmax: int) -> None:
    """Exact root screen for the two-bit handshake refinement."""
    for k in range(1, kmax + 1):
        t0 = time.time()
        reps = iso_classes(k)
        failures = [(tuple(sorted(edges)), failure)
                    for edges in reps
                    for failure in two_bit_root_failures(k, edges)]
        print(f"k={k}: {len(reps)} classes | two-bit root failures:"
              f" {len(failures)}  [{time.time()-t0:.0f}s]", flush=True)
        for failure in failures[:8]:
            print(f"   FAIL {failure}")


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


def stage_neutral(path: str, jobs: int) -> None:
    """Verify the stronger zero-after-every-Even-move even-board target."""
    if jobs < 1:
        raise ValueError("jobs must be positive")
    records = [line for line in Path(path).read_text(encoding="ascii").splitlines()
               if line and not line.startswith(">>")]
    if not records:
        raise ValueError(f"no graph6 records in {path}")
    orders = {decode_graph6(line)[0] for line in records}
    if any(order % 2 for order in orders):
        raise ValueError(f"neutral requires even graph orders, got {orders}")
    print(f"neutral: {len(records)} records, orders={sorted(orders)},"
          f" jobs={jobs}", flush=True)
    t0 = time.time()
    failures = []
    with multiprocessing.Pool(processes=jobs) as pool:
        for index, result in enumerate(
                pool.imap_unordered(verify_neutral_graph6_record,
                                    records, chunksize=1), 1):
            if result is not None:
                failures.append(result)
                pool.terminate()
                break
            if index % 1000 == 0:
                print(f"   {index}/{len(records)} [{time.time()-t0:.0f}s]",
                      flush=True)
    if failures:
        raise AssertionError(f"neutral counterexample: {failures[0]}")
    print(f"neutral: PASS ({len(records)} records in {time.time()-t0:.0f}s)")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", nargs="?", default="all",
                         choices=("validate", "screen", "strategy",
                                  "refinement", "graph6", "neutral", "all"))
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
    if args.stage == "refinement":
        stage_refinement(args.kmax)
    if args.stage == "graph6":
        if args.graph6_path is None:
            parser.error("graph6 requires --graph6-path")
        stage_graph6(args.graph6_path, args.jobs, not args.skip_strategy)
    if args.stage == "neutral":
        if args.graph6_path is None:
            parser.error("neutral requires --graph6-path")
        stage_neutral(args.graph6_path, args.jobs)


if __name__ == "__main__":
    main()
