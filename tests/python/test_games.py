"""Combinatorial games: partizan values, thermography, impartial and misere
play, coin-turning and lexicodes, Hackenbush, and the checked game
constructors (Witt--FIFO, Brown selector, Guy--Smith)."""

import itertools
import unittest

import ogdoad as og

from _support import OgdoadTestCase

G = og.Game


def half():
    return G.from_surreal(og.Surreal.from_rational(1, 2))


def sample_games():
    return [G.zero(), G.star(), G.up(), -G.up(), G.integer(1), G.switch(1, -1),
            G.nim_heap(2), half()]


# ---------------------------------------------------------------------------
# Partizan games
# ---------------------------------------------------------------------------


class PartizanGameTests(OgdoadTestCase):
    def test_outcome_classes(self):
        expected = {
            "0": (G.zero(), "P"),
            "*": (G.star(), "N"),
            "up": (G.up(), "L"),
            "down": (-G.up(), "R"),
            "1": (G.integer(1), "L"),
            "-1": (G.integer(-1), "R"),
            "up+*": (G.up() + G.star(), "N"),
            "{1|-1}": (G.switch(1, -1), "N"),
            "*2": (G.nim_heap(2), "N"),
        }
        for label, (game, outcome) in expected.items():
            with self.subTest(game=label):
                self.assertEqual(str(game.outcome_class()), outcome)

    def test_games_form_an_abelian_group_up_to_value(self):
        samples = sample_games()
        zero = G.zero()
        for a in samples:
            self.assertEqual(a + zero, a)
            self.assertEqual(a - a, zero)
            self.assertEqual(a + (-a), zero)
            self.assertEqual(-(-a), a)
        for a, b in itertools.product(samples, repeat=2):
            self.assertEqual(a + b, b + a)
            self.assertEqual(a - b, a + (-b))
        for a, b, c in itertools.product(samples, repeat=3):
            self.assertEqual((a + b) + c, a + (b + c))

    def test_value_equality_is_coarser_than_structural_equality(self):
        up = G.up()
        raw_zero = up - up
        self.assertEqual(raw_zero, G.zero())
        self.assertFalse(raw_zero.structural_eq(G.zero()))
        self.assertEqual(raw_zero.canonical_string(), G.zero().canonical_string())
        self.assertEqual(raw_zero.canonical_string(), "{|}")
        self.assertFalse(raw_zero.is_canonical())
        self.assertTrue(raw_zero.canonical().is_canonical())
        self.assertTrue(up.is_canonical())

    def test_known_identities(self):
        up, star, zero = G.up(), G.star(), G.zero()
        self.assertEqual(star + star, zero)
        self.assertEqual(up + star + star, up)
        self.assertEqual(up.times_int(2), up + up)
        self.assertEqual(up.times_int(-1), -up)
        self.assertEqual(up.times_int(0), zero)
        self.assertEqual((up + up - up).canonical_string(), up.canonical_string())
        self.assertEqual(repr(zero), "0")
        self.assertEqual(repr(star), "{0|0}")
        self.assertEqual(repr(up), "{0|{0|0}}")

    def test_partial_order_via_le_and_fuzzy(self):
        up, star, zero = G.up(), G.star(), G.zero()
        self.assertTrue(zero.le(up))
        self.assertFalse(up.le(zero))
        self.assertTrue(up.fuzzy(star))
        self.assertTrue(star.fuzzy(zero))
        self.assertFalse(zero.fuzzy(zero))
        self.assertTrue(G.integer(2).le(G.integer(3)))
        self.assertFalse(G.integer(3).le(G.integer(2)))
        samples = sample_games()
        for a, b in itertools.product(samples, repeat=2):
            self.assertEqual(a.le(b) and b.le(a), a == b)
            self.assertEqual(a.fuzzy(b), not a.le(b) and not b.le(a))
        # Games carry a partial order only: no ``<`` operator.
        with self.assertRaises(TypeError):
            G.up() < G.integer(1)

    def test_numbers_carry_a_surreal_value(self):
        h = half()
        self.assertEqual(repr(h), "{0|{0|}}")
        self.assertEqual(str(h.number_value()), "1/2")
        self.assertEqual(h.birthday(), 2)
        self.assertEqual(G.integer(5).birthday(), 5)
        self.assertEqual(G.integer(3).number_value(), 3)
        self.assertTrue(G.integer(3).is_number())
        for g in (G.star(), G.up(), G.switch(1, -1)):
            self.assertFalse(g.is_number())
            self.assertIsNone(g.number_value())
        self.assertEqual(h + h, G.integer(1))
        self.assertEqual(str(G.from_surreal(og.Surreal.from_rational(3, 4)).number_value()), "3/4")

    def test_only_dyadic_surreals_are_short_games(self):
        with self.assertRaises(ValueError):
            G.from_surreal(og.Surreal.from_rational(1, 3))
        with self.assertRaises(ValueError):
            G.from_surreal(og.omega())

    def test_nim_heaps_add_by_xor(self):
        # Sprague--Grundy: *a + *b = *(a xor b), checked as game values.
        for a, b in itertools.product(range(8), repeat=2):
            self.assertEqual(G.nim_heap(a) + G.nim_heap(b), G.nim_heap(a ^ b), (a, b))
        self.assertEqual(G.nim_heap(0), G.zero())
        self.assertEqual(G.nim_heap(1), G.star())

    def test_game_construction_from_option_lists(self):
        zero = G.zero()
        self.assertEqual(G.of([], []), zero)
        self.assertEqual(G.of([zero], []), G.integer(1))
        self.assertEqual(G.of([zero], [zero]), G.star())
        self.assertEqual(G.up().left(), [zero])
        self.assertEqual(G.up().right(), [G.star()])

    def test_atomic_weights_of_all_small_games(self):
        up, star = G.up(), G.star()
        table = [(G.zero(), 0), (star, 0), (up, 1), (up + up, 2), (-up, -1), (up + star, 1)]
        for game, weight in table:
            with self.subTest(game=repr(game)):
                self.assertTrue(game.is_all_small())
                self.assertEqual(og.atomic_weight_int(game), weight)
        self.assertIsNone(og.atomic_weight_int(G.integer(1)))  # not all-small
        self.assertEqual(og.atomic_weight_int(up + up + up), 3)  # additive

    def test_hash_is_not_defined_for_games(self):
        with self.assertRaises(TypeError):
            hash(G.up())


class ThermographyTests(OgdoadTestCase):
    def test_temperature_mean_and_stops(self):
        table = [
            (G.switch(1, -1), "1", "0", "1", "-1"),
            (G.switch(3, -1), "2", "1", "3", "-1"),
            (G.switch(2, 0), "1", "1", "2", "0"),
            (G.star(), "0", "0", "0", "0"),
            (G.up(), "0", "0", "0", "0"),
        ]
        for game, temp, mean, left, right in table:
            with self.subTest(game=repr(game)):
                self.assertEqual(
                    (str(game.temperature()), str(game.mean_value()),
                     str(game.left_stop()), str(game.right_stop())),
                    (temp, mean, left, right))

    def test_mean_is_the_average_of_the_stops_of_a_switch(self):
        for a, b in ((3, -1), (5, 1), (2, 0), (4, -4)):
            game = G.switch(a, b)
            self.assertEqual(game.mean_value(), og.Surreal.from_rational(a + b, 2))
            self.assertEqual(game.temperature(), og.Surreal.from_rational(a - b, 2))

    def test_module_level_helpers_agree_with_methods(self):
        hot = G.switch(3, -1)
        self.assertEqual((og.temperature(hot), og.mean_value(hot),
                          og.left_stop(hot), og.right_stop(hot)),
                         (hot.temperature(), hot.mean_value(),
                          hot.left_stop(), hot.right_stop()))

    def test_thermograph_walls_and_cooling(self):
        hot = G.switch(3, -1)
        th = hot.thermograph()
        self.assertEqual((th.mean, th.temperature), (1, 2))
        self.assertEqual(th.left_wall.points(), [(0, 3), (2, 1)])
        self.assertEqual(th.right_wall.points(), [(0, -1), (2, 1)])
        self.assertEqual(th.left_wall.value_at(og.Rational(0)), 3)
        self.assertEqual(th.right_wall.value_at(og.Rational(0)), -1)
        self.assertEqual(hot.cooled_stops(0), (3, -1))
        self.assertEqual(hot.cooled_stops(1), (2, 0))
        self.assertEqual(hot.cooled_stops(5), (1, 1))  # frozen at the mean

    def test_tropical_route_gives_the_same_thermograph(self):
        hot = G.switch(3, -1)
        a, b = hot.thermograph(), hot.thermograph_via_tropical()
        self.assertEqual((a.mean, a.temperature), (b.mean, b.temperature))
        self.assertEqual(a.left_wall.points(), b.left_wall.points())
        self.assertEqual(a.right_wall.points(), b.right_wall.points())

    def test_norton_multiplication_and_overheating(self):
        hot = G.switch(3, -1)
        two = G.integer(2)
        norton = hot.norton_multiply(two)
        self.assertEqual((norton.mean_value(), norton.temperature()), (2, 5))
        self.assertEqual(hot.overheat(two, G.integer(1)), norton)
        scale, shift = two.numeric_norton_regrade()
        self.assertEqual((scale, shift), (2, 1))
        mean, temp = hot.numeric_norton_mean_temperature(two)
        self.assertEqual((str(mean), str(temp)),
                         (str(norton.mean_value()), str(norton.temperature())))
        heated = hot.heat(2)
        self.assertEqual((heated.temperature(), heated.mean_value()), (4, 1))


# ---------------------------------------------------------------------------
# Impartial, loopy and misere play
# ---------------------------------------------------------------------------


def nim_heap_graph(top):
    return [list(range(h)) for h in range(top)]


class ImpartialTests(OgdoadTestCase):
    def test_sprague_grundy_on_single_heaps(self):
        self.assertEqual(og.grundy_graph(nim_heap_graph(8)), list(range(8)))
        self.assertEqual(og.grundy(3, lambda h: list(range(h))), 3)

    def test_sprague_grundy_theorem_for_sums_of_two_heaps(self):
        # Build the product game graph explicitly; its Grundy value is a XOR b.
        size = 6
        index = {(i, j): i * size + j for i in range(size) for j in range(size)}
        graph = [None] * (size * size)
        for (i, j), k in index.items():
            graph[k] = ([index[(x, j)] for x in range(i)]
                        + [index[(i, y)] for y in range(j)])
        values = og.grundy_graph(graph)
        for (i, j), k in index.items():
            self.assertEqual(values[k], i ^ j)

    def test_cycles_make_grundy_values_undefined(self):
        with self.assertRaises(ValueError):
            og.grundy_graph([[1], [0]])

    def test_outcomes_p_positions_and_mex(self):
        succ = [[1], [2, 0], []]
        outcomes = og.outcomes(succ)
        self.assertEqual([o.name() for o in outcomes], ["Loss", "Win", "Loss"])
        self.assertEqual(outcomes[0], og.Outcome.loss())
        self.assertEqual(og.p_positions(succ), [0, 2])
        self.assertEqual((og.mex([0, 1, 3]), og.mex([]), og.mex([1, 2])), (2, 0, 0))

    def test_p_positions_are_exactly_the_zero_grundy_positions(self):
        graph = nim_heap_graph(9)
        values = og.grundy_graph(graph)
        self.assertEqual(og.p_positions(graph), [i for i, v in enumerate(values) if v == 0])

    def test_scoring_games(self):
        score = og.scoring_values([[1, 2], [], []], [0, 3, 7])[0]
        self.assertEqual((score.left, score.right), (7, 3))
        self.assertEqual(repr(score), "ScoreInterval(left=7, right=3)")


class LoopyGameTests(OgdoadTestCase):
    def test_draws_appear_with_cycles(self):
        g = og.LoopyGraph([[1], [0], [3], []])  # 0 <-> 1 drawn; 2 -> 3 terminal
        self.assertEqual(g.succ(), [[1], [0], [3], []])
        self.assertEqual([o.name() for o in g.outcomes()], ["Draw", "Draw", "Win", "Loss"])
        self.assertEqual(g.draw_set(), [0, 1])
        self.assertEqual(g.loss_set(), [3])
        self.assertEqual(g.win_set(), [2])

    def test_loopy_nim_values_with_certificate(self):
        values, cert = og.loopy_nim_values_certified([[1], [0], []])
        self.assertEqual([repr(v) for v in values],
                         ["LoopyNimber.Side", "LoopyNimber.Side", "LoopyNimber.Value(0)"])
        self.assertTrue(cert.recovery_condition_holds)
        self.assertEqual([o.name() for o in cert.outcomes], ["Draw", "Draw", "Loss"])
        self.assertEqual(og.loopy_nim_values([[1], [0], [3], []])[2], og.LoopyNimber.value(1))

    def test_callback_constructors_agree_with_explicit_graphs(self):
        rule = lambda v: [[1], [0], [3], []][v]
        self.assertEqual(og.LoopyGraph.from_rule(4, rule).succ(), [[1], [0], [3], []])
        loss, draw = og.loopy_decision_sets(4, rule)
        self.assertEqual((loss, draw), ([3], [0, 1]))

    def test_out_of_range_successors_are_refused(self):
        with self.assertRaises(ValueError):
            og.LoopyGraph([[5]])

    def test_stoppers_and_the_loopy_value_group(self):
        on, off, over, under = (og.LoopyValue.on(), og.LoopyValue.off(),
                                og.LoopyValue.over(), og.LoopyValue.under())
        self.assertTrue(on.is_stopper() and not og.LoopyValue.dud().is_stopper())
        self.assertEqual(-on, off)
        self.assertEqual(og.LoopyValue.zero() + on, on)
        self.assertEqual(repr(on + off), "dud")
        self.assertEqual(repr(over + under), "None")  # undefined sum is None, not a guess
        self.assertTrue(on > off)

    def test_partizan_tis_and_tisn(self):
        graph = og.LoopyPartizanGraph([[2], [0], []], [[1], [2], []])
        outcomes = graph.partizan_outcomes()
        self.assertEqual(outcomes[2], og.PartizanOutcome.p())
        self.assertIsNone(outcomes[0])  # not a classical outcome class
        self.assertEqual(og.LoopyValue.tis().sides(), (1, 0))


class MisereTests(OgdoadTestCase):
    def test_closed_form_for_misere_nim_matches_exhaustive_search(self):
        # Position p of the abstract game is a Nim heap of size p.
        game = og.AbstractGame([list(range(h)) for h in range(5)])
        for count in range(0, 4):
            for heaps in itertools.combinations_with_replacement(range(1, 5), count):
                with self.subTest(heaps=heaps):
                    is_p = not game.misere_outcome(list(heaps))
                    self.assertEqual(og.misere_nim_p_predicted(list(heaps)), is_p)

    def test_misere_nim_special_cases(self):
        # Three singleton heaps: the mover must lose the last move.
        self.assertTrue(og.misere_nim_p_predicted([1, 1, 1]))
        self.assertTrue(og.misere_nim_p_predicted([1, 2, 3]))
        self.assertFalse(og.misere_nim_p_predicted([2, 1]))
        self.assertFalse(og.misere_nim_p_predicted([]))

    def test_callback_misere_path(self):
        moves = lambda h: list(range(h))
        self.assertFalse(og.try_misere_is_n(1, moves))
        self.assertFalse(og.misere_is_n(1, moves))
        self.assertTrue(og.misere_is_p(1, moves))
        self.assertTrue(og.misere_is_n(2, moves))

    def test_cyclic_move_graphs_are_refused(self):
        with self.assertRaises(ValueError):
            og.AbstractGame([[], [1]]).misere_outcome([1])
        with self.assertRaises(ValueError):
            og.AbstractGame([[], [2], [1]]).misere_outcome([1])
        with self.assertRaises(ValueError):
            og.AbstractGame([[], [1]]).misere_quotient([1], 1, 1)

    def test_bounded_indistinguishability_quotient(self):
        ag = og.AbstractGame([[], [0], [0, 1]])
        q = ag.misere_quotient([1, 2], 2, 2)
        self.assertEqual(q.num_classes, og.misere_quotient(ag, [1, 2], 2, 2).num_classes)
        nim = og.octal_misere_quotient([3, 3, 3], 3, 3, 3)  # 0.333 is Nim
        self.assertEqual(nim.num_classes, 6)
        self.assertEqual(repr(nim), "Quotient(order=6, P-classes=2, partial monoid)")


# ---------------------------------------------------------------------------
# Coin turning, lexicodes
# ---------------------------------------------------------------------------


class CoinTurningTests(OgdoadTestCase):
    def test_grundy_values_and_companions(self):
        self.assertEqual([og.coin_turning_grundy("singleton", n) for n in range(6)],
                         [0, 1, 2, 3, 4, 5])
        self.assertEqual([og.coin_turning_grundy("turtles", n) for n in range(6)],
                         [1, 2, 3, 4, 5, 6])
        self.assertEqual(og.coin_companions("singleton", 4), [1, 2, 4, 8])
        self.assertEqual(og.singleton_companions(4), og.coin_companions("singleton", 4))
        self.assertEqual(og.turtles_companions(4), og.coin_companions("turtles", 4))
        with self.assertRaises(ValueError):
            og.coin_turning_grundy("bogus", 3)

    def test_tartan_product_of_singleton_games_is_nim_multiplication(self):
        # The game-built product reproduces the field multiplication on nimbers.
        for a, b in itertools.product(range(12), repeat=2):
            self.assertEqual(og.coin_turning_tartan_grundy("singleton", "singleton", a, b),
                             og.nim_mul(a, b), (a, b))

    def test_mex_construction_of_the_nim_product(self):
        for a, b in itertools.product(range(16), repeat=2):
            self.assertEqual(og.nim_mul_mex(a, b), og.nim_mul(a, b), (a, b))

    def test_mixed_tartan_product_uses_the_second_games_values(self):
        for a, b in itertools.product(range(5), repeat=2):
            self.assertEqual(
                og.coin_turning_tartan_grundy("singleton", "turtles", a, b),
                og.nim_mul_mex(a, og.coin_turning_grundy("turtles", b)))

    def test_callback_spelling_matches_the_named_families(self):
        singleton = lambda n: [1 << i for i in range(n)]
        self.assertEqual(og.grundy_1d(singleton, 5), 5)
        self.assertEqual(og.tartan_grundy(singleton, singleton, 2, 4), 8)


class LexicodeTests(OgdoadTestCase):
    @staticmethod
    def codewords(code):
        """Codewords as integers, coordinate 0 being the most significant bit."""
        generators = [int("".join(str(b) for b in g), 2) for g in code.generators()]
        words = {0}
        for g in generators:
            words |= {w ^ g for w in words}
        return sorted(words)

    def test_p_positions_of_the_turning_game_are_the_lexicode(self):
        # Conway--Sloane: the lexicode is the set of P-positions of the
        # coin-turning game whose moves are the words of weight < d.
        for n, d in ((4, 3), (7, 3), (8, 4), (6, 2), (9, 3), (10, 5)):
            with self.subTest(n=n, d=d):
                game = og.lexicode_turning_game(n, d)
                self.assertEqual(game.p_positions_bounded(),
                                 self.codewords(og.lexicode(n, d)))

    def test_turning_game_grundy_values_vanish_exactly_on_codewords(self):
        game = og.lexicode_turning_game(4, 3)
        values = game.grundy_values_bounded()
        self.assertEqual([i for i, v in enumerate(values) if v == 0], [0, 7])
        self.assertEqual(game.position_count(), 16)
        self.assertEqual(repr(game), "LexicodeTurningGame(word_len=4, min_distance=3)")

    def test_nim_lexicode_over_base_four(self):
        code = og.nim_lexicode_naive(2, 2, 2)
        self.assertEqual(code.words(), [[0, 0], [1, 1], [2, 2], [3, 3]])
        self.assertTrue(code.is_closed_under_nim_scalars())
        self.assertTrue(code.is_closed_under_nim_add())
        self.assertEqual(code.word_count(), 4)

    def test_naive_and_fast_constructions_agree(self):
        self.assertEqual(og.lexicode_naive(7, 3).weight_enumerator(),
                         og.lexicode(7, 3).weight_enumerator())


# ---------------------------------------------------------------------------
# Hackenbush
# ---------------------------------------------------------------------------


class HackenbushTests(OgdoadTestCase):
    def setUp(self):
        self.B, self.R, self.G = og.Color.blue(), og.Color.red(), og.Color.green()

    def test_blue_red_strings_are_surreal_numbers(self):
        B, R = self.B, self.R
        values = [
            ((B,), "1"), ((R,), "-1"), ((B, B), "2"), ((B, B, B), "3"),
            ((B, R), "1/2"), ((R, B), "-1/2"), ((B, R, R), "1/4"),
        ]
        for string, expected in values:
            with self.subTest(string=[c.name() for c in string]):
                self.assertEqual(str(og.Hackenbush.string(list(string)).value()), expected)

    def test_green_stalks_are_nim_heaps(self):
        for n in range(1, 6):
            stalk = og.Hackenbush.string([self.G] * n)
            self.assertEqual(stalk.grundy(), n)
            self.assertEqual(stalk.to_game(), G.nim_heap(n))

    def test_game_of_a_string_equals_its_number(self):
        B, R = self.B, self.R
        self.assertEqual(og.Hackenbush.string([B, R]).to_game(),
                         G.from_surreal(og.Surreal.from_rational(1, 2)))

    def test_green_cycle_fuses(self):
        # A green triangle fuses to a single loop edge on the ground: *1.
        tri = og.Hackenbush([(0, 1, self.G), (1, 2, self.G), (2, 0, self.G)])
        self.assertEqual(tri.grundy(), 1)
        self.assertEqual(len(tri.edges()), 3)

    def test_unsupported_value_requests_return_none(self):
        self.assertIsNone(og.Hackenbush.string([self.B]).grundy())  # not impartial
        self.assertIsNone(og.Hackenbush.string([self.G, self.B]).value())  # not a number

    def test_colours_compare_and_name(self):
        self.assertEqual(og.Color.blue(), self.B)
        self.assertNotEqual(self.B, self.R)
        self.assertEqual([c.name() for c in (self.B, self.R, self.G)], ["blue", "red", "green"])
        self.assertEqual(og.Hackenbush([(0, 1, self.G)]).edges(), [(0, 1, self.G)])


# ---------------------------------------------------------------------------
# Transfinite number and nimber games
# ---------------------------------------------------------------------------


class TransfiniteGameTests(OgdoadTestCase):
    def test_number_game_of_omega(self):
        w = og.NumberGame.from_surreal(og.omega())
        one = og.NumberGame.from_surreal(og.surreal(1))
        self.assertEqual(w.value(), og.omega())
        self.assertEqual(repr(w.birthday()), "*ω")
        self.assertIsNone(w.to_finite_game())  # transfinite: not a short game
        self.assertEqual((w + one).value(), og.omega() + 1)
        self.assertEqual((-w).value(), -og.omega())
        self.assertTrue(w > one)
        self.assertEqual(repr(w.sign_expansion()), "[(True, *ω)]")

    def test_sign_expansion_round_trip(self):
        w1 = og.NumberGame.from_surreal(og.omega() + 1)
        back = og.NumberGame.from_sign_expansion(w1.sign_expansion())
        self.assertEqual(back.value(), og.omega() + 1)
        self.assertEqual(back, w1)

    def test_number_game_of_a_dyadic_is_a_short_game(self):
        two = og.NumberGame.from_surreal(og.surreal(2))
        self.assertEqual(two.to_finite_game(), G.integer(2))

    def test_nimber_game_obeys_ordinal_nim_arithmetic(self):
        wg = og.NimberGame.from_ordinal(og.Ordinal.omega())
        one = og.NimberGame.nim_heap(1)
        self.assertEqual(repr(wg.grundy()), "*ω")
        self.assertEqual((wg + wg).grundy(), og.Ordinal(0))  # a P-position
        self.assertEqual(repr((wg + one).grundy()), "*(ω + 1)")
        self.assertTrue(wg > one)
        # Conway: omega^3 = 2 under the game-built (turning-corners) product.
        self.assertEqual(wg.turning_corners(wg).turning_corners(wg).grundy(), og.Ordinal(2))
        self.assertIsNone(wg.to_finite_game())
        self.assertEqual(og.NimberGame.nim_heap(3).grundy_finite(), 3)

    def test_sign_expansion_objects(self):
        se = og.SignExpansion.from_finite([True, True, False])
        self.assertEqual(se.as_finite(), [True, True, False])
        self.assertEqual(og.Surreal.from_sign_expansion_record(se), og.Surreal.from_rational(3, 2))
        runs = og.SignExpansion.from_runs(
            [(True, og.Ordinal(1)), (True, og.Ordinal(2)), (False, og.Ordinal(1))])
        self.assertEqual(repr(runs.length()), "*4")
        self.assertEqual(og.Surreal.from_sign_expansion_record(runs),
                         og.Surreal.from_rational(5, 2))  # +++- = 3 - 1/2

    def test_transfinite_birthdays(self):
        w = og.omega()
        self.assertEqual(repr(w.birthday_ordinal()), "*ω")
        self.assertEqual(repr((w + 1).birthday_ordinal()), "*(ω + 1)")
        self.assertIsNone(w.sqrt_to_terms(4).birthday_ordinal())  # outside the represented class
        back = og.Surreal.from_transfinite_sign_expansion((w + 1).transfinite_sign_expansion())
        self.assertEqual(back, w + 1)


# ---------------------------------------------------------------------------
# Checked game constructors: Witt--FIFO, Brown selector, Guy--Smith
# ---------------------------------------------------------------------------


def quadratic_value(diagonal, polar, x):
    """Q(x) over F_2 from the diagonal and polar bitmask rows."""
    n = len(diagonal)
    total = 0
    for i in range(n):
        xi = (x >> i) & 1
        total ^= (1 if diagonal[i] else 0) & xi
        for j in range(i + 1, n):
            xj = (x >> j) & 1
            total ^= ((polar[i] >> j) & 1) & xi & xj
    return total


class WittFifoTests(OgdoadTestCase):
    def test_readme_example(self):
        arena = og.WittFifoArena(diagonal=[True], polar=[0], input=1)
        self.assertTrue(arena.quadratic_value)
        self.assertNotEqual(arena.grundy(state_budget=100_000), 0)
        self.assertEqual(arena.to_game(100_000).outcome_class(), og.PartizanOutcome.n())
        self.assertEqual(repr(arena),
                         "WittFifoArena(dimension=1, input=1, coin_count=3, quadratic_value=true)")

    def test_grundy_value_is_the_quadratic_form(self):
        # The arena realises Q(x) as a Grundy value, for every input vector.
        forms = [
            ([True], [0]),
            ([False], [0]),
            ([True, True], [2, 1]),
            ([False, False], [2, 1]),
            ([True, False], [0, 0]),
            ([False, True, False], [6, 5, 3]),
        ]
        for diagonal, polar in forms:
            for x in range(2 ** len(diagonal)):
                with self.subTest(diagonal=diagonal, polar=polar, x=x):
                    arena = og.WittFifoArena(diagonal, polar, x)
                    q = quadratic_value(diagonal, polar, x)
                    self.assertEqual(arena.quadratic_value, bool(q))
                    self.assertEqual(arena.grundy(1_000_000), q)
                    expected = og.PartizanOutcome.n() if q else og.PartizanOutcome.p()
                    self.assertEqual(arena.to_game(1_000_000).outcome_class(), expected)

    def test_budgets_and_shapes_are_checked(self):
        arena = og.WittFifoArena([True], [0], 1)
        with self.assertRaises(ValueError):
            arena.grundy(1)
        with self.assertRaises(ValueError):
            arena.to_game(1)
        with self.assertRaises(ValueError):
            og.WittFifoArena([True], [0, 1], 1)  # one polar row per diagonal entry
        with self.assertRaises(ValueError):
            og.WittFifoArena([True], [0], 5)  # input outside F_2^dim


class BrownSelectorTests(OgdoadTestCase):
    def test_residues_decode_to_outcome_classes(self):
        # Intrinsic Brown residue r in Z/4 selects N, R, P, L in order.
        names = []
        for residue in range(4):
            selector = og.BrownSelector([residue], [0], 1)
            outcome = selector.outcome_class(100_000)
            names.append(outcome.name())
            self.assertEqual(selector.residue, og.BrownSelector.decode_outcome(outcome))
            self.assertEqual(selector.to_game(100_000).outcome_class(), outcome)
        self.assertEqual(names, ["N", "R", "P", "L"])

    def test_readme_example(self):
        selector = og.BrownSelector(q4=[3], brown_polar=[0], input=1)
        outcome = selector.outcome_class(state_budget_per_follower=100_000)
        self.assertEqual(og.BrownSelector.decode_outcome(outcome), selector.residue)

    def test_budget_is_enforced(self):
        with self.assertRaises(ValueError):
            og.BrownSelector([2], [0], 1).outcome_class(1)

    def test_followers_are_the_two_arenas(self):
        selector = og.BrownSelector([2], [0], 1)
        self.assertEqual(selector.left_follower.quadratic_value, True)
        self.assertEqual(selector.right_follower.dimension, 1)
        self.assertEqual(selector.classical_diagonal, [True])
        self.assertEqual(selector.linear_diagonal, [False])


def octal_grundy(digits, top):
    """Brute-force octal-game Grundy values G(0..top); digits[k-1] is d_k."""
    g = [0] * (top + 1)
    for n in range(1, top + 1):
        options = set()
        for k, d in enumerate(digits, start=1):
            if k > n:
                break
            rest = n - k
            if d & 1 and rest == 0:
                options.add(0)
            if d & 2 and rest > 0:
                options.add(g[rest])
            if d & 4 and rest > 1:
                for a in range(1, rest):
                    options.add(g[a] ^ g[rest - a])
        m = 0
        while m in options:
            m += 1
        g[n] = m
    return g


class GuySmithTests(OgdoadTestCase):
    def test_readme_example(self):
        certificate = og.GuySmithCertificate.compute(og.OctalCode([2]), 1, 2, term_budget=16)
        self.assertEqual(certificate.heap_grundy(10 ** 30), 1)

    def test_demo_certificate(self):
        code = og.OctalCode([2, 0, 0])
        cert = og.GuySmithCertificate.compute(code, 1, 2, 16)
        self.assertEqual(code.digits, [2])  # trailing zeros are trimmed
        self.assertEqual((cert.preperiod, cert.period, cert.proof_window), (1, 2, (1, 5)))
        self.assertEqual(
            repr(cert),
            "GuySmithCertificate(code=OctalCode(digits=[2]), preperiod=1, period=2, proof_window=(1, 5))")
        recheck = og.GuySmithWitness(cert.preperiod, cert.period, cert.checked_nim_values).verify(code, 16)
        self.assertEqual(recheck.heap_grundy(10 ** 30), cert.heap_grundy(10 ** 30))
        self.assertTrue(cert.is_p_position([101, 101]))
        self.assertFalse(cert.is_p_position([1, 2]))

    def test_certificates_agree_with_brute_force(self):
        # Kayles (.77, period 12 after 70) and Dawson's Kayles (.07, period 34
        # after 52) are the classical examples.
        for digits, preperiod, period in (([2], 1, 2), ([7, 7], 71, 12), ([0, 7], 53, 34)):
            with self.subTest(code=digits):
                cert = og.GuySmithCertificate.compute(og.OctalCode(digits), preperiod, period, 3000)
                top = 300
                expected = octal_grundy(digits, top)
                self.assertEqual([cert.heap_grundy(h) for h in range(top + 1)], expected)

    def test_periodicity_extends_beyond_any_checked_window(self):
        cert = og.GuySmithCertificate.compute(og.OctalCode([7, 7]), 71, 12, 3000)
        for huge in (10 ** 12 + 3, 10 ** 30 + 7):
            self.assertEqual(cert.heap_grundy(huge), cert.heap_grundy(71 + (huge - 71) % 12))
        self.assertEqual(cert.position_grundy([5, 7, 10]),
                         cert.heap_grundy(5) ^ cert.heap_grundy(7) ^ cert.heap_grundy(10))

    def test_wrong_claims_are_refused(self):
        code = og.OctalCode([2])
        with self.assertRaises(ValueError):
            og.GuySmithCertificate.compute(code, 1, 3, 16)  # wrong period
        with self.assertRaises(ValueError):
            og.GuySmithCertificate.compute(code, 0, 1, 16)  # preperiod must be positive
        with self.assertRaises(ValueError):
            og.GuySmithCertificate.compute(code, 1, 2, 1)  # budget below the proof window
        with self.assertRaises(ValueError):
            og.GuySmithCertificate.compute(og.OctalCode([4, 4]), 1, 1, 16)
        with self.assertRaises(ValueError):
            og.GuySmithWitness(1, 2, [0, 1, 0, 1]).verify(code, 16)  # too few terms
        with self.assertRaises(ValueError):
            og.OctalCode([8])  # not an octal digit


# ---------------------------------------------------------------------------
# Python callbacks cross the boundary in both directions
# ---------------------------------------------------------------------------


class CallbackBoundaryTests(OgdoadTestCase):
    def test_exceptions_raised_by_callbacks_propagate_unchanged(self):
        def boom(_):
            raise KeyError("callback failed")

        for call in (lambda: og.grundy(3, boom),
                     lambda: og.misere_is_n(3, boom),
                     lambda: og.try_misere_is_n(3, boom),
                     lambda: og.grundy_1d(boom, 3),
                     lambda: og.LoopyGraph.from_rule(3, boom),
                     lambda: og.loopy_decision_sets(3, boom)):
            with self.assertRaises(KeyError):
                call()
        with self.assertRaises(ZeroDivisionError):
            og.grundy(3, lambda h: 1 / 0)
        with self.assertRaises(ZeroDivisionError):
            og.SurrealAlgebra(q=[1]).map(lambda x: 1 / 0)

    def test_callback_results_are_validated(self):
        with self.assertRaises(TypeError):
            og.grundy(3, lambda h: 5)  # not a sequence
        with self.assertRaises(TypeError):
            og.grundy(3, lambda h: ["a"])  # not integers
        with self.assertRaises(OverflowError):
            og.grundy(3, lambda h: [-1])  # positions are unsigned
        with self.assertRaises(TypeError):
            og.grundy(3, 5)  # not callable
        with self.assertRaises(TypeError):
            og.SurrealAlgebra(q=[1]).map(lambda x: og.Nimber(1))  # wrong scalar world

    def test_out_of_range_targets_are_value_errors(self):
        for call in (lambda: og.LoopyGraph.from_rule(3, lambda v: [99]),
                     lambda: og.loopy_decision_sets(4, lambda v: [99]),
                     lambda: og.loopy_quadric_probe(2, lambda v: [99])):
            with self.assertRaises(ValueError) as ctx:
                call()
            self.assertIn("out-of-range", str(ctx.exception))

    def test_companion_masks_must_name_strictly_lower_coins(self):
        for masks in (lambda n: [1 << (n + 3)], lambda n: [1 << n]):
            with self.assertRaises(ValueError):
                og.grundy_1d(masks, 5)
        with self.assertRaises(ValueError):
            og.tartan_grundy(lambda n: [1 << (n + 3)], lambda n: [1 << i for i in range(n)], 2, 4)
        with self.assertRaises(ValueError):
            og.coin_turning_grundy("singleton", 10 ** 6)  # companion sets are u128 bitmasks

    def test_cyclic_callbacks_are_detected_where_the_api_checks_for_them(self):
        with self.assertRaises(ValueError):
            og.misere_is_p(3, lambda h: [h])
        self.assertIsNone(og.try_misere_is_n(3, lambda h: [h]))

    def test_callbacks_may_be_any_callable(self):
        class Moves:
            def __call__(self, h):
                return list(range(h))

        self.assertEqual(og.grundy(4, Moves()), 4)
        self.assertEqual(og.grundy(4, lambda h: tuple(range(h))), 4)


if __name__ == "__main__":
    unittest.main()
