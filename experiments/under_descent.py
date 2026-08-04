#!/usr/bin/env python3
"""Closure audit for the resolved `under` thermography problem.

The question is whether the newly shipped Norton multiplication / overheating
operators respect the temperature-filtration quotient

    gr_T = ⊕_τ F_{≤τ}/F_{<τ}.

This script keeps the game-tree tests deliberately small and source-backed:
build a compact short-game catalogue, identify pairs equivalent modulo lower
temperature, then ask whether the operators produce equivalent leading outputs.
It records all three parts of the final `under` result: a nonnumeric-unit
counterexample, the exact affine regrading through which every positive dyadic
numeric unit descends, and the nonnegative composition defect that prevents
those transports from being a multiplicative scalar action.
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
class NumericUnit:
    name: str
    game: pl.Game
    scale: Fraction
    shift: Fraction


@dataclass(frozen=True)
class Failure:
    operator: str
    unit: str
    tau: Fraction
    output_layer: Fraction
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
    rational = value.as_rational()
    if rational is None:
        raise ValueError(f"temperature not rational for {g.display()}")
    return Fraction(rational.numerator, rational.denominator)


def as_fraction(value: object) -> Fraction:
    return Fraction(value.numerator, value.denominator)


def number(value: Fraction | int) -> pl.Game:
    value = Fraction(value)
    return pl.Game.from_surreal(pl.Surreal.from_rational(value.numerator, value.denominator))


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
        for value in [Fraction(-1), Fraction(-1, 2), Fraction(0), Fraction(1, 2), Fraction(1)]:
            if value == 0:
                suffix = ""
            elif value.denominator == 1:
                suffix = f"{value.numerator:+d}"
            else:
                suffix = f"{value.numerator:+d}/{value.denominator}"
            shifted.append(NamedGame(f"{item.name}{suffix}", item.game + number(value)))
    return dedupe(shifted)


def positive_units() -> list[NumericUnit]:
    out: list[NumericUnit] = []
    for scale in [
        Fraction(1, 4),
        Fraction(1, 2),
        Fraction(3, 4),
        Fraction(1),
        Fraction(3, 2),
        Fraction(2),
    ]:
        game = number(scale)
        result = game.numeric_norton_regrade()
        if result is None:
            raise AssertionError(f"positive numeric unit {scale} has no regrade")
        bound_scale, bound_shift = map(as_fraction, result)
        if bound_scale != scale:
            raise AssertionError(f"binding reports scale {bound_scale}, expected {scale}")
        out.append(NumericUnit(str(scale), game, scale, bound_shift))
    return out


def dyadic_mesh(value: Fraction) -> Fraction:
    """The canonical option mesh delta_x = 1 / denominator(x)."""
    return Fraction(1, value.denominator)


def composition_defect(first: Fraction, second: Fraction) -> Fraction:
    """Degree of A_second A_first minus the degree of A_(first*second)."""
    return (
        second * (1 - dyadic_mesh(first))
        - dyadic_mesh(second)
        + dyadic_mesh(first * second)
    )


def zero_defect_is_expected(first: Fraction, second: Fraction) -> bool:
    """The exact parity/mesh classification from the composition theorem."""
    if first.denominator > 1:
        return second.numerator == 1  # second = 2^-ell, including 1
    return first.numerator % 2 == 1 or second.denominator == 1


def composition_defect_scan() -> tuple[int, int, int]:
    """Exhaust the theorem arithmetically and pin selected defects on actual games."""
    values = sorted(
        {Fraction(n, 1 << k) for k in range(5) for n in range(1, 17)}
    )
    checked = 0
    positive = 0
    for first in values:
        for second in values:
            defect = composition_defect(first, second)
            if defect < 0:
                raise AssertionError(f"negative defect for {first=}, {second=}: {defect}")
            if (defect == 0) != zero_defect_is_expected(first, second):
                raise AssertionError(
                    f"zero classification failed for {first=}, {second=}: {defect}"
                )
            checked += 1
            positive += defect > 0

    star = pl.Game.star()
    witnessed = 0
    for first, second in [
        (Fraction(1, 2), Fraction(2)),
        (Fraction(2), Fraction(1, 2)),
        (Fraction(3), Fraction(1, 2)),
        (Fraction(1, 2), Fraction(1, 4)),
        (Fraction(3, 2), Fraction(3, 2)),
    ]:
        first_product = star.norton_multiply(number(first))
        composite = first_product.norton_multiply(number(second)) if first_product else None
        direct = star.norton_multiply(number(first * second))
        if composite is None or direct is None:
            raise AssertionError(f"missing numeric Norton composition for {first}, {second}")
        actual = temp(composite) - temp(direct)
        expected = composition_defect(first, second)
        if actual != expected:
            raise AssertionError(
                f"game-level defect failed for {first}, {second}: {actual} != {expected}"
            )
        witnessed += 1
    return checked, positive, witnessed


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
                operator=operator,
                unit=unit.name,
                tau=Fraction(0),
                output_layer=Fraction(0),
                g_name=g.name,
                h_name=h.name,
                delta_temp=temp(g.game - h.game),
                left_temp=tp,
                right_temp=tq,
                output_delta_temp=td,
                output_delta_aw=aw,
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


def exact_numeric_thermic_scan(games: list[NamedGame], units: list[NumericUnit]) -> int:
    checked = 0
    for item in games:
        for unit in units:
            product = item.game.norton_multiply(unit.game)
            predicted = item.game.numeric_norton_mean_temperature(unit.game)
            if product is None or predicted is None:
                raise AssertionError(f"numeric Norton product missing for {item.name}, {unit.name}")
            predicted_mean, predicted_temp = map(as_fraction, predicted)
            actual_mean = as_fraction(product.mean_value().as_rational())
            if actual_mean != predicted_mean or temp(product) != predicted_temp:
                raise AssertionError(
                    f"thermic formula failed for {item.name}, {unit.name}: "
                    f"actual={(actual_mean, temp(product))}, "
                    f"predicted={(predicted_mean, predicted_temp)}"
                )
            checked += 1
    return checked


def bounded_numeric_unit_scan() -> tuple[list[Failure], dict[str, int], int, int, int]:
    games = catalogue()
    units = positive_units()
    thermic_checks = exact_numeric_thermic_scan(games, units)
    failures: list[Failure] = []
    checked_by_operator = {"norton": 0, "overheat_s_unit_t_shift": 0}
    half = number(Fraction(1, 2))
    representatives = [
        (Fraction(0), NamedGame("*", pl.Game.star()), NamedGame("*+1/2", pl.Game.star() + half)),
        (
            Fraction(0),
            NamedGame("up", pl.Game.up()),
            NamedGame("up+1/2", pl.Game.up() + half),
        ),
        (
            Fraction(1),
            NamedGame("{1|-1}", pl.Game.switch(1, -1)),
            NamedGame("{1|-1}+1/2", pl.Game.switch(1, -1) + half),
        ),
        (
            Fraction(2),
            NamedGame("{3|-1}", pl.Game.switch(3, -1)),
            NamedGame("{3|-1}+1/2", pl.Game.switch(3, -1) + half),
        ),
    ]

    for tau, g, h in representatives:
        delta_temp = temp(g.game - h.game)
        if delta_temp >= tau:
            raise AssertionError(f"bad representative pair {g.name}, {h.name}")
        for unit in units:
            output_layer = unit.scale * tau + unit.shift
            for operator in ["norton", "overheat_s_unit_t_shift"]:
                if operator == "norton":
                    p = g.game.norton_multiply(unit.game)
                    q = h.game.norton_multiply(unit.game)
                else:
                    shift_game = number(unit.shift)
                    p = g.game.overheat(unit.game, shift_game)
                    q = h.game.overheat(unit.game, shift_game)
                if p is None or q is None:
                    continue
                checked_by_operator[operator] += 1
                tp, tq, td = temp(p), temp(q), temp(p - q)
                aw = (p - q).atomic_weight_int()
                ok = tp <= output_layer and tq <= output_layer and td < output_layer
                if not ok:
                    failures.append(
                        Failure(
                            operator=operator,
                            unit=unit.name,
                            tau=tau,
                            output_layer=output_layer,
                            g_name=g.name,
                            h_name=h.name,
                            delta_temp=delta_temp,
                            left_temp=tp,
                            right_temp=tq,
                            output_delta_temp=td,
                            output_delta_aw=aw,
                        )
                    )

    return failures, checked_by_operator, len(games), len(units), thermic_checks


def main() -> None:
    explicit = explicit_non_numeric_failures()
    failures, checked, game_count, unit_count, thermic_checks = bounded_numeric_unit_scan()
    defect_checks, positive_defects, game_defect_witnesses = composition_defect_scan()
    print(f"catalogue games: {game_count}; positive units: {unit_count}")
    print(f"exact numeric-unit thermic checks: {thermic_checks}")
    print(f"checked norton pairs: {checked['norton']}")
    print(
        "checked matching overheat(s=unit,t=shift) pairs: "
        f"{checked['overheat_s_unit_t_shift']}"
    )

    print(f"numeric-unit failures in bounded scan: {len(failures)}")
    print(f"explicit non-numeric-unit failures: {len(explicit)}")
    print(
        "composition-defect pairs: "
        f"{defect_checks} ({positive_defects} positive); "
        f"game-level witnesses: {game_defect_witnesses}"
    )

    if explicit:
        first = explicit[0]
        print("\nfirst non-numeric-unit failure:")
        print(f"  operator: {first.operator}")
        print(f"  unit: {first.unit}")
        print(f"  layer tau: {first.tau}")
        print(f"  output layer: {first.output_layer}")
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
