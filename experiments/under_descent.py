#!/usr/bin/env python3
"""Bounded descent probe for the `under` thermography open problem.

The question is whether the newly shipped Norton multiplication / overheating
operators respect the temperature-filtration quotient

    gr_T = ⊕_τ F_{≤τ}/F_{<τ}.

This script keeps the test deliberately small and source-backed: build a compact
short-game catalogue, identify pairs equivalent modulo lower temperature, then
ask whether the operators produce equivalent leading outputs.  A failure is a
bounded witness that the operator does not descend to the naive associated
graded with cold numbers quotiented out.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

import ogdoad as pl


@dataclass(frozen=True)
class NamedGame:
    name: str
    game: pl.Game


@dataclass(frozen=True)
class Failure:
    operator: str
    unit: str
    tau: Fraction
    g_name: str
    h_name: str
    delta_temp: Fraction
    left_temp: Fraction
    right_temp: Fraction
    output_delta_temp: Fraction
    output_delta_aw: int | None


def temp(g: pl.Game) -> Fraction:
    value = g.temperature()
    if value is None:
        raise ValueError(f"temperature undefined for {g.display()}")
    return Fraction(str(value))


def dedupe(games: list[NamedGame]) -> list[NamedGame]:
    seen: set[str] = set()
    out: list[NamedGame] = []
    for item in games:
        key = item.game.canonical_string()
        if key in seen:
            continue
        seen.add(key)
        out.append(item)
    return out


def catalogue() -> list[NamedGame]:
    star = pl.Game.star()
    up = pl.Game.up()
    down = -up
    base = [
        NamedGame("*", star),
        NamedGame("*2", pl.Game.nim_heap(2)),
        NamedGame("up", up),
        NamedGame("down", down),
        NamedGame("up+*", up + star),
        NamedGame("down+*", down + star),
        NamedGame("{1|-1}", pl.Game.switch(1, -1)),
    ]

    shifted: list[NamedGame] = []
    for item in base:
        for n in [-1, 0, 1]:
            shift = pl.Game.integer(n)
            suffix = "" if n == 0 else f"{n:+d}"
            shifted.append(NamedGame(f"{item.name}{suffix}", item.game + shift))
    return dedupe(shifted)


def positive_units() -> list[NamedGame]:
    return [
        NamedGame("1", pl.Game.integer(1)),
        NamedGame("2", pl.Game.integer(2)),
    ]


def explicit_non_numeric_failures() -> list[Failure]:
    """The minimal obstruction: the hidden cold integer is multiplied by `up`."""
    g = NamedGame("*", pl.Game.star())
    h = NamedGame("*+1", pl.Game.star() + pl.Game.integer(1))
    unit = NamedGame("up", pl.Game.up())
    out: list[Failure] = []
    for operator in ["norton", "overheat_s_unit_t_0"]:
        if operator == "norton":
            p = g.game.norton_multiply(unit.game)
            q = h.game.norton_multiply(unit.game)
        else:
            p = g.game.overheat(unit.game, pl.Game.zero())
            q = h.game.overheat(unit.game, pl.Game.zero())
        assert p is not None and q is not None
        ok, tp, tq, td, aw = same_leading_output(p, q)
        assert not ok
        out.append(
            Failure(
                operator,
                unit.name,
                Fraction(0),
                g.name,
                h.name,
                temp(g.game - h.game),
                tp,
                tq,
                td,
                aw,
            )
        )
    return out


def same_leading_output(a: pl.Game, b: pl.Game) -> tuple[bool, Fraction, Fraction, Fraction, int | None]:
    ta = temp(a)
    tb = temp(b)
    td = temp(a - b)
    aw = (a - b).atomic_weight_int()
    if ta != tb:
        return False, ta, tb, td, aw
    if ta < 0:
        return (a == b), ta, tb, td, aw
    return td < ta, ta, tb, td, aw


def bounded_numeric_unit_scan() -> tuple[list[Failure], dict[str, int], int, int]:
    games = catalogue()
    units = positive_units()
    taus = sorted({temp(g.game) for g in games if temp(g.game) >= 0})
    failures: list[Failure] = []
    checked_by_operator = {"norton": 0, "overheat_s_unit_t_0": 0}

    for tau in taus:
        for g in games:
            if temp(g.game) > tau:
                continue
            for h in games:
                if temp(h.game) > tau:
                    continue
                delta_temp = temp(g.game - h.game)
                if delta_temp >= tau:
                    continue
                # Ignore pairs that both already lie in the lower filtration;
                # they represent the zero class one layer earlier.  The witness
                # below is stronger: both representatives have leading temp tau.
                if temp(g.game) < tau and temp(h.game) < tau:
                    continue

                for unit in units:
                    p = g.game.norton_multiply(unit.game)
                    q = h.game.norton_multiply(unit.game)
                    if p is not None and q is not None:
                        checked_by_operator["norton"] += 1
                        ok, tp, tq, td, aw = same_leading_output(p, q)
                        if not ok:
                            failures.append(
                                Failure(
                                    "norton",
                                    unit.name,
                                    tau,
                                    g.name,
                                    h.name,
                                    delta_temp,
                                    tp,
                                    tq,
                                    td,
                                    aw,
                                )
                            )

                    p = g.game.overheat(unit.game, pl.Game.zero())
                    q = h.game.overheat(unit.game, pl.Game.zero())
                    if p is not None and q is not None:
                        checked_by_operator["overheat_s_unit_t_0"] += 1
                        ok, tp, tq, td, aw = same_leading_output(p, q)
                        if not ok:
                            failures.append(
                                Failure(
                                    "overheat_s_unit_t_0",
                                    unit.name,
                                    tau,
                                    g.name,
                                    h.name,
                                    delta_temp,
                                    tp,
                                    tq,
                                    td,
                                    aw,
                                )
                            )

    return failures, checked_by_operator, len(games), len(units)


def main() -> None:
    explicit = explicit_non_numeric_failures()
    failures, checked, game_count, unit_count = bounded_numeric_unit_scan()
    print(f"catalogue games: {game_count}; positive units: {unit_count}")
    print(f"checked norton pairs: {checked['norton']}")
    print(f"checked overheat(s=unit,t=0) pairs: {checked['overheat_s_unit_t_0']}")

    print(f"numeric-unit failures in bounded scan: {len(failures)}")
    print(f"explicit non-numeric-unit failures: {len(explicit)}")

    if explicit:
        first = explicit[0]
        print("\nfirst non-numeric-unit failure:")
        print(f"  operator: {first.operator}")
        print(f"  unit: {first.unit}")
        print(f"  layer tau: {first.tau}")
        print(f"  representatives: {first.g_name} and {first.h_name}")
        print(f"  temp(G-H): {first.delta_temp} < {first.tau}")
        print(f"  output temps: {first.left_temp}, {first.right_temp}")
        print(f"  temp(output difference): {first.output_delta_temp}")
        print(f"  atomic_weight_int(output difference): {first.output_delta_aw}")

    if failures:
        first = failures[0]
        print("\nfirst numeric-unit failure:")
        print(first)


if __name__ == "__main__":
    main()
