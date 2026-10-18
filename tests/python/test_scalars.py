"""Scalar worlds: ring and field laws, canonical reprs, checked boundaries,
and the monomorphic cross-world contract (AGENTS.md invariant 6)."""

import itertools
import unittest

import ogdoad as og

from _support import OgdoadTestCase


# ---------------------------------------------------------------------------
# Nimbers: the characteristic-two field F_{2^128}
# ---------------------------------------------------------------------------


class NimberTests(OgdoadTestCase):
    N = og.Nimber

    def test_small_subfields_are_fields_exhaustively(self):
        # 0..3 is F_4 and 0..15 is F_16: the nim-subfields F_{2^(2^k)}.
        N = self.N
        for bound in (4, 16):
            elements = [N(i) for i in range(bound)]
            self.assert_field(elements, N(0), N(1))

    def test_large_samples_obey_field_axioms(self):
        N = self.N
        samples = [N(v) for v in (0, 1, 2, 3, 5, 2**64 + 3, 2**100 + 7, 2**127 + 12345)]
        self.assert_field(samples, N(0), N(1))

    def test_characteristic_two_negation_is_identity(self):
        N = self.N
        self.assertEqual(N.characteristic(), 2)
        for v in (0, 1, 2, 9, 2**90 + 1):
            self.assertEqual(-N(v), N(v))
            self.assertEqual(N(v) + N(v), N(0))
            self.assertEqual(N(v) - N(v), N(v) + N(v))

    def test_nim_multiplication_tables(self):
        N = self.N
        self.assertEqual(N(2) * N(2), N(3))
        self.assertEqual(N(2) * N(3), N(1))
        self.assertEqual(N(3) * N(3), N(2))
        self.assertEqual(N(2) + N(3), N(1))
        self.assertEqual(N(4) * N(4), N(6))
        self.assertEqual(N(2) / N(3), N(3))

    def test_construction_validates_the_u128_payload(self):
        N = self.N
        self.assertEqual(N(2**128 - 1).value, 2**128 - 1)
        with self.assertRaises(OverflowError):
            N(2**128)
        with self.assertRaises(OverflowError):
            N(-1)

    def test_integers_coerce_but_other_worlds_do_not(self):
        N = self.N
        self.assertEqual(N(2) + 3, N(1))
        self.assertEqual(3 + N(2), N(1))
        self.assertEqual(N(2) * 3, N(1))
        with self.assertRaises(TypeError):
            N(2) + og.Fp3(1)
        with self.assertRaises(TypeError):
            N(2) + og.Rational(1)
        with self.assertRaises(TypeError):
            N(2) + 1.5

    def test_inverse_and_division_refuse_zero(self):
        N = self.N
        with self.assertRaises(ValueError):
            N(0).inv()
        with self.assertRaises(ValueError):
            N(1) / N(0)
        for v in (1, 2, 3, 2**90 + 17):
            self.assertEqual(N(v) * N(v).inv(), N(1))

    def test_powers(self):
        N = self.N
        x = N(5)
        self.assertEqual(x ** 0, N(1))
        self.assertEqual(N(0) ** 0, N(1))
        self.assertEqual(x ** 3, x * x * x)
        self.assertEqual(x.pow(15), N(1))  # order of *5 is 15
        self.assertEqual(x.multiplicative_order(), 15)
        self.assertIsNone(N(0).multiplicative_order())
        with self.assertRaises((TypeError, OverflowError, ValueError)):
            x ** -1  # negative exponents are refused, never wrapped

    def test_frobenius_and_square_root(self):
        N = self.N
        self.assertEqual(N.ext_degree(), 128)
        for v in (2, 5, 2**70 + 9):
            x = N(v)
            self.assertEqual(x.frobenius(), x * x)
            self.assertEqual(x.sqrt().frobenius(), x)
            self.assertEqual(x.sqrt() ** 2, x)
            self.assertEqual(x.frobenius_iter(128), x)  # F_{2^128}: x^(2^128)=x
            self.assertEqual(x.frobenius_iter(3), x ** 8)
        self.assertTrue(N(7).is_square())  # always true in characteristic two

    def test_field_degree_and_minimal_polynomial(self):
        N = self.N
        self.assertEqual(N(2).degree(), 2)
        self.assertEqual(N(2).min_poly(), [1, 1, 1])  # x^2 + x + 1
        self.assertEqual([c.value for c in N(2).min_poly_monic()], [1, 1, 1])
        self.assertEqual([c.value for c in N(5).conjugates()], [5, 7, 4, 6])
        self.assertEqual(N(1).degree(), 1)

    def test_distinct_nimbers_are_incomparable_games(self):
        N = self.N
        self.assertTrue(N(1).fuzzy(N(2)))
        self.assertFalse(N(1).fuzzy(N(1)))
        with self.assertRaises(TypeError):
            N(1) < N(2)  # no order: the type is not in ORDERED_CLASSES

    def test_hash_agrees_with_equality(self):
        N = self.N
        self.assertEqual(hash(N(2**100)), hash(N(2**100)))
        self.assertEqual(len({N(1), N(1), N(2)}), 2)

    def test_relative_trace_and_norm_to_subfields(self):
        N = self.N
        # *7 lies in F_16; over F_4 the trace is x + x^4 and the norm x * x^4.
        x = N(7)
        self.assertEqual(x.relative_trace_over(4, 2), x + x.frobenius_iter(2))
        self.assertEqual(x.relative_norm_over(4, 2), x * x.frobenius_iter(2))
        self.assertEqual(x.relative_trace_over(4, 2), N(1))
        self.assertEqual(x.relative_norm_over(4, 2), N(3))
        self.assertEqual(og.nim_relative_trace(7, 4, 2), 1)
        self.assertEqual(og.nim_relative_norm(7, 4, 2), 3)
        # Down to the prime field the trace of an element of F_16 is x+x^2+x^4+x^8.
        tr = sum((x.frobenius_iter(k) for k in range(4)), N(0))
        self.assertEqual(x.relative_trace_over(4, 1), tr)

    def test_canonical_repr(self):
        N = self.N
        self.assertEqual(repr(N(0)), "*0")
        self.assertEqual(repr(N(5)), "*5")
        self.assertEqual(str(N(5)), "*5")
        self.assertEqual(repr(N(2**127)), "*170141183460469231731687303715884105728")
        self.assertEqual(N(5).value, 5)


class RawNimFunctionTests(OgdoadTestCase):
    def test_raw_functions_match_the_class(self):
        N = og.Nimber
        pairs = [(2, 3), (5, 7), (2**40 + 1, 2**77 + 3), (1, 0), (0, 0)]
        for a, b in pairs:
            self.assertEqual(og.nim_add(a, b), (N(a) + N(b)).value)
            self.assertEqual(og.nim_mul(a, b), (N(a) * N(b)).value)
            self.assertEqual(og.nim_square(a), (N(a) * N(a)).value)
            self.assertEqual(og.nim_pow(a, 5), (N(a) ** 5).value)
            self.assertEqual(og.nim_sqrt(og.nim_square(a)), a)
        for a in (1, 2, 3, 2**50 + 11):
            self.assertEqual(og.nim_mul(a, og.nim_inv(a)), 1)

    def test_demo_values(self):
        self.assertEqual(
            (og.nim_add(5, 7), og.nim_mul(2, 3), og.nim_pow(2, 3),
             og.nim_square(5), og.nim_frobenius_iter(5, 2), og.nim_inv(3)),
            (2, 1, 1, 7, 4, 2),
        )
        self.assertEqual(og.nim_degree(2), 2)
        self.assertEqual(og.nim_min_poly(2), [1, 1, 1])
        self.assertEqual(og.nim_conjugates(5), [5, 7, 4, 6])
        self.assertEqual(og.nim_multiplicative_order(5), 15)
        self.assertEqual(og.nim_discrete_log(2, 3), 2)  # 2^2 = 3 in F_4

    def test_zero_has_no_inverse_and_returns_none(self):
        self.assertIsNone(og.nim_inv(0))

    def test_u128_payloads_are_validated(self):
        with self.assertRaises(OverflowError):
            og.nim_mul(2**128, 1)
        with self.assertRaises(OverflowError):
            og.nim_add(-1, 1)

    def test_artin_schreier_traces_decide_solvability(self):
        # y^2 + y = c over F_4 is solvable iff Tr(c) = 0.
        solvable = {c: og.nim_solve_artin_schreier(c, 2) for c in range(4)}
        self.assertEqual(solvable[0], 0)
        self.assertIn(solvable[1], (2, 3))
        self.assertIsNone(solvable[2])
        self.assertIsNone(solvable[3])
        for c, y in solvable.items():
            if y is not None:
                self.assertEqual(og.nim_add(og.nim_square(y), y), c)
            self.assertEqual(og.nim_trace(c, 2) == 0, y is not None)


# ---------------------------------------------------------------------------
# Exact rationals and integers
# ---------------------------------------------------------------------------


class RationalTests(OgdoadTestCase):
    R = og.Rational

    def test_field_axioms(self):
        R = self.R
        samples = [R(0), R(1), R(-1), R(1, 2), R(3, 4), R(-7, 3), R(5)]
        self.assert_field(samples, R(0), R(1))

    def test_normalisation_and_repr(self):
        R = self.R
        self.assertEqual(R(6, 8), R(3, 4))
        self.assertEqual(R(3, -6), R(-1, 2))
        self.assertEqual(repr(R(6, 8)), "3/4")
        self.assertEqual(repr(R(-1, 2)), "-1/2")
        self.assertEqual(repr(R(4, 2)), "2")
        self.assertEqual(repr(R(3, 4) - R(1, 6)), "7/12")
        self.assertEqual((R(3, 4).numer(), R(3, 4).denom()), (3, 4))
        self.assertEqual((R.try_new(6, 8).numer(), R.try_new(6, 8).denom()), (3, 4))

    def test_zero_denominator_and_division_by_zero(self):
        R = self.R
        with self.assertRaises(ValueError):
            R(1, 0)
        self.assertIsNone(R.try_new(1, 0))
        with self.assertRaises(ValueError):
            R(1) / R(0)
        with self.assertRaises(ValueError):
            R(0).inv()

    def test_order_is_total_and_compatible_with_addition(self):
        R = self.R
        chain = [R(-3), R(-1, 2), R(0), R(1, 3), R(1, 2), R(2)]
        for a, b in itertools.combinations(chain, 2):
            self.assertTrue(a < b)
            self.assertTrue(b > a)
            self.assertTrue(a + R(1, 7) < b + R(1, 7))
        self.assertEqual([x.sign() for x in chain], [-1, -1, 0, 1, 1, 1])

    def test_roots_decline_with_none(self):
        R = self.R
        self.assertEqual(R(9, 16).sqrt(), R(3, 4))
        self.assertIsNone(R(2).sqrt())
        self.assertEqual(R(8).nth_root(3), R(2))
        self.assertIsNone(R(1, 2).nth_root(2))
        self.assertEqual(R(7, 2).floor(), 3)
        self.assertEqual(R(-7, 2).floor(), -4)

    def test_i128_payload_is_validated(self):
        R = self.R
        self.assertEqual(repr(R(2**127 - 1)), str(2**127 - 1))
        with self.assertRaises(OverflowError):
            R(2**127, 1)

    def test_arithmetic_overflow_is_loud_not_wrapped(self):
        # Scalar operators are not behind the engine's panic guard, so the
        # documented outcome is pyo3_runtime.PanicException (a BaseException).
        R = self.R
        big = R(2**100)
        self.assert_raises_name(("PanicException", "OverflowError", "ValueError"),
                                lambda: big * big)

    def test_embeds_integer_and_pairs_but_not_floats(self):
        R = self.R
        self.assertEqual(R(1, 2) + 1, R(3, 2))
        self.assertEqual(R(1, 2) + (1, 3), R(5, 6))
        self.assertEqual(R(1, 2) + og.Integer(2), R(5, 2))
        with self.assertRaises(TypeError):
            R(1, 2) + 0.5

    def test_repeated_products_and_exact_powers_of_two(self):
        R = self.R
        half = R(1, 2)
        acc = R(1)
        for k in range(1, 20):
            acc = acc * half
            self.assertEqual(acc, R(1, 2**k))


class IntegerTests(OgdoadTestCase):
    Z = og.Integer

    def test_ring_axioms(self):
        Z = self.Z
        samples = [Z(v) for v in (0, 1, -1, 2, -7, 12)]
        self.assert_ring(samples, Z(0), Z(1))

    def test_euclidean_division_is_non_negative_remainder(self):
        Z = self.Z
        self.assertEqual(Z(7).divrem(2), (3, 1))
        self.assertEqual(Z(-7).divrem(2), (-4, 1))
        self.assertEqual(Z(-7) % 3, Z(2))
        self.assertEqual(Z(7) % 3, Z(1))
        self.assertEqual(Z(6).div_exact(3), Z(2))
        with self.assertRaises(ValueError):
            Z(7).div_exact(Z(3))
        with self.assertRaises(ValueError):
            Z(7) / Z(2)  # true division is exact division on Z

    def test_only_units_invert(self):
        Z = self.Z
        self.assertEqual(Z(1).inv(), Z(1))
        self.assertEqual(Z(-1).inv(), Z(-1))
        with self.assertRaises(ValueError):
            Z(2).inv()

    def test_order_and_repr(self):
        Z = self.Z
        self.assertTrue(Z(3) < Z(4) and Z(4) >= Z(4))
        self.assertEqual(repr(Z(-7)), "-7")
        self.assertEqual(Z(-7).value, -7)

    def test_i128_edges(self):
        Z = self.Z
        self.assertEqual(Z(2**127 - 1).value, 2**127 - 1)
        self.assertEqual(Z(-(2**127)).value, -(2**127))
        with self.assertRaises(OverflowError):
            Z(2**127)
        self.assert_raises_name(("PanicException", "OverflowError", "ValueError"),
                                lambda: Z(2**127 - 1) + Z(1))
        self.assert_raises_name(("PanicException", "OverflowError", "ValueError"),
                                lambda: Z(2**100) * Z(2**100))


# ---------------------------------------------------------------------------
# Finite fields
# ---------------------------------------------------------------------------


class PrimeFieldTests(OgdoadTestCase):
    def test_exhaustive_field_axioms(self):
        for cls in (og.Fp2, og.Fp3, og.Fp5, og.Fp7):
            p = cls.modulus()
            elements = [cls(i) for i in range(p)]
            with self.subTest(cls=cls.__name__):
                self.assertEqual(cls.characteristic(), p)
                self.assertTrue(cls.modulus_is_prime())
                self.assert_field(elements, cls(0), cls(1))

    def test_reduction_and_repr(self):
        Fp5 = og.Fp5
        self.assertEqual(Fp5(7), Fp5(2))
        self.assertEqual(Fp5(-1), Fp5(4))
        self.assertEqual(Fp5(2**100), Fp5(2**100 % 5))
        self.assertEqual(repr(Fp5(7)), "2")
        self.assertEqual(Fp5(7).value, 2)
        self.assertEqual(hash(Fp5(7)), hash(Fp5(2)))

    def test_inverse_powers_and_roots(self):
        Fp5 = og.Fp5
        self.assertEqual(Fp5(2).inv(), Fp5(3))
        with self.assertRaises(ValueError):
            Fp5(0).inv()
        self.assertEqual(Fp5(3) ** 4, Fp5(1))  # Fermat
        self.assertEqual(Fp5(2).pow(4), Fp5(1))
        self.assertTrue(Fp5(4).is_square())
        self.assertFalse(Fp5(3).is_square())
        self.assertIsNone(Fp5(3).sqrt())
        self.assertIn(Fp5(4).sqrt(), (Fp5(2), Fp5(3)))
        self.assertEqual(Fp5(4).sqrt() ** 2, Fp5(4))
        with self.assertRaises((TypeError, OverflowError, ValueError)):
            Fp5(2) ** -1

    def test_integer_operands_coerce(self):
        Fp5 = og.Fp5
        self.assertEqual(Fp5(2) + 9, Fp5(1))
        self.assertEqual(9 + Fp5(2), Fp5(1))
        self.assertEqual(4 - Fp5(2), Fp5(2))
        self.assertEqual(Fp5(2) * 7, Fp5(4))
        self.assertEqual(3 / Fp5(2), Fp5(4))


class ExtensionFieldTests(OgdoadTestCase):
    def test_exhaustive_field_axioms(self):
        for cls in (og.F4, og.F8, og.F9):
            order = cls.field_order()
            elements = [cls.from_index(i) for i in range(order)]
            with self.subTest(cls=cls.__name__):
                self.assertEqual(len(set(map(repr, elements))), order)
                self.assert_field(elements, cls.zero(), cls.one())

    def test_f8_structure(self):
        F8 = og.F8
        x = F8.generator()
        self.assertEqual((F8.field_order(), F8.ext_degree(), F8.characteristic()), (8, 3, 2))
        self.assertEqual(x.min_poly(), [1, 1, 0, 1])  # x^3 + x + 1
        self.assertEqual(x.multiplicative_order(), 7)
        self.assertTrue(x.is_primitive())
        self.assertEqual(x ** 7, F8.one())
        self.assertEqual(F8.group_order_factors(), [7])
        self.assertEqual(x ** 3, x + F8.one())
        self.assertEqual(x.frobenius(), x * x)
        self.assertEqual(x.frobenius_iter(3), x)
        self.assertEqual(repr(x), "x")
        self.assertEqual(repr(x * x + x + F8.one()), "x↑2 + x + 1")
        self.assertEqual([repr(F8.from_index(i)) for i in range(3)], ["0", "1", "x"])
        self.assertEqual(F8.from_coeffs([0, 1, 0]), x)
        self.assertEqual(x.into_coeffs(), [0, 1, 0])

    def test_f9_structure(self):
        F9 = og.F9
        prim = F9.primitive_element()
        self.assertEqual(prim.multiplicative_order(), 8)
        self.assertEqual(prim ** 8, F9.one())
        self.assertEqual(F9.characteristic(), 3)
        self.assertEqual([repr(F9.from_index(i)) for i in range(4)], ["0", "1", "2", "x"])

    def test_every_nonzero_element_of_f8_has_a_unique_square_root(self):
        F8 = og.F8
        for i in range(1, 8):
            a = F8.from_index(i)
            self.assertEqual(a.sqrt() ** 2, a)
            self.assertTrue(a.is_square())

    def test_coefficient_vectors_are_validated(self):
        F8 = og.F8
        self.assertEqual(F8.from_coeffs([3, 0, 0]), F8.one())  # reduced mod p
        with self.assertRaises(ValueError):
            F8.from_coeffs([0, 0, 0, 1])  # nonzero term beyond the degree
        with self.assertRaises(ValueError):
            F8.from_index(8)

    def test_division_by_zero_is_refused(self):
        F8 = og.F8
        with self.assertRaises(ValueError):
            F8.zero().inv()
        with self.assertRaises(ValueError):
            F8.one() / F8.zero()

    def test_trace_and_norm_over_the_prime_field(self):
        F8 = og.F8
        x = F8.generator()
        # Tr(x) = x + x^2 + x^4 = 0 and N(x) = x^7 = 1 for the root of x^3+x+1;
        # both land in the prime field and come back as Python integers.
        self.assertEqual(x + x.frobenius() + x.frobenius_iter(2), F8.zero())
        self.assertEqual(x.absolute_trace(), 0)
        self.assertEqual(x.absolute_norm(), 1)
        self.assertEqual((x + F8.one()).absolute_trace(), 1)  # Tr(1) = 3 = 1 in F_2


# ---------------------------------------------------------------------------
# Surreals, surcomplex, omnific integers
# ---------------------------------------------------------------------------


class SurrealTests(OgdoadTestCase):
    S = og.Surreal

    def samples(self):
        w, e = og.omega(), og.epsilon()
        return [og.surreal(0), og.surreal(1), og.surreal(-2), w, e, w + 1,
                og.surreal(3) * w ** 2 - w + 5, -e, self.S.from_rational(3, 4)]

    def test_commutative_ring_axioms_including_transfinite_values(self):
        self.assert_ring(self.samples(), og.surreal(0), og.surreal(1))

    def test_omega_and_epsilon(self):
        w, e = og.omega(), og.epsilon()
        self.assertEqual(w * e, og.surreal(1))
        self.assertEqual(repr(w), "ω")
        self.assertEqual(repr(e), "ω↑-1")
        self.assertEqual(repr((w + 1) * (w - 1)), "ω↑2 - 1")
        self.assertEqual((w + 1) * (w - 1), w ** 2 - 1)
        self.assertEqual(repr(og.surreal(3) * w ** 2 - w + 5),
                         "3⋅ω↑2 - ω + 5")
        self.assertEqual(repr(og.omega_pow(w)), "ω↑(ω)")

    def test_order_is_total_and_archimedean_classes_separate(self):
        w, e = og.omega(), og.epsilon()
        self.assertTrue(og.surreal(0) < e < self.S.from_rational(1, 10**9))
        self.assertTrue(w > 1_000_000)
        self.assertTrue(w + 1 > w)
        self.assertTrue(-w < -e < og.surreal(0))
        self.assertEqual([x.sign() for x in (w, e, -w, og.surreal(0))], [1, 1, -1, 0])

    def test_only_monomials_invert_exactly(self):
        w, e = og.omega(), og.epsilon()
        self.assertEqual(w.inv(), e)
        self.assertEqual(og.surreal(3).inv(), self.S.from_rational(1, 3))
        with self.assertRaises(ValueError):
            (w + 1).inv()
        with self.assertRaises(ValueError):
            og.surreal(0).inv()
        # Truncated Neumann series is an explicit, opt-in approximation.
        self.assertEqual(repr((w + 1).inv_to_terms(3)),
                         "ω↑-1 - ω↑-2 + ω↑-3")

    def test_square_roots_decline_instead_of_approximating(self):
        w = og.omega()
        self.assertEqual(w.exact_sqrt() ** 2, w)
        self.assertTrue(w.is_square())
        self.assertIsNone(og.surreal(2).exact_sqrt())
        self.assertIsNone(og.surreal(2).sqrt_to_terms(4))
        self.assertFalse(og.surreal(-1).is_square())
        self.assertEqual(og.surreal(9).exact_sqrt(), og.surreal(3))
        self.assertEqual((w * w + 2 * w + 1).sqrt_to_terms(2), w + 1)

    def test_dyadic_sign_expansion_and_floor(self):
        S = self.S
        three_quarters = S.from_rational(3, 4)
        self.assertEqual(three_quarters.as_dyadic(), (3, 2))
        self.assertEqual(three_quarters.sign_expansion(), [True, False, True])
        self.assertEqual(S.from_sign_expansion([True, False, True]), three_quarters)
        self.assertEqual(S.simplest_between(0, 1), S.from_rational(1, 2))
        self.assertEqual(
            S.simplest_between(S.from_rational(1, 3), S.from_rational(2, 3)),
            S.from_rational(1, 2))
        w = og.omega()
        half = S.from_rational(1, 2)
        self.assertEqual((w + half).floor(), w)
        self.assertEqual((w + half).frac(), half)

    def test_terms_and_monomials(self):
        S = self.S
        w = og.omega()
        self.assertEqual((og.surreal(3) * w ** 2 - w + 5).terms,
                         [(2, 3), (1, -1), (0, 5)])
        self.assertEqual(repr(S.monomial(2, 7)), "7⋅ω↑2")
        self.assertEqual(S.characteristic(), 0)

    def test_integer_operands_coerce(self):
        self.assertEqual(og.surreal(3), 3)
        self.assertEqual(og.omega() + 1, og.omega() + og.surreal(1))
        self.assertEqual(2 * og.omega(), og.omega() + og.omega())

    def test_power_operator_takes_only_non_negative_integers(self):
        w = og.omega()
        self.assertEqual(og.surreal(2) ** 10, og.surreal(1024))
        self.assertEqual(w ** 0, og.surreal(1))
        with self.assertRaises(TypeError):
            w ** -1
        with self.assertRaises(TypeError):
            w ** w


class SurcomplexTests(OgdoadTestCase):
    def test_complex_unit_and_conjugate_norm(self):
        i = og.Surcomplex.i()
        self.assertEqual(i ** 2, og.Surcomplex(-1, 0))
        z = og.Surcomplex(og.omega(), 1)
        self.assertEqual(z * z.conj(), og.Surcomplex(og.omega() ** 2 + 1, 0))
        self.assertEqual(repr(og.Surcomplex(3, 4)), "3 + 4·i")

    def test_sqrt_is_exact_or_declines(self):
        self.assertEqual(og.Surcomplex(3, 4).sqrt(), og.Surcomplex(2, 1))
        self.assertEqual(og.Surcomplex(og.omega(), 0).sqrt() ** 2,
                         og.Surcomplex(og.omega(), 0))
        self.assertIsNone(og.Surcomplex(2, 0).sqrt())

    def test_inverse_needs_an_invertible_norm(self):
        zz = og.Surcomplex(og.omega() + 1, 1)
        with self.assertRaises(ValueError):
            zz.inv()  # norm (w+1)^2 + 1 is not a monomial
        self.assertEqual(og.Surcomplex(0, 2).inv(), og.Surcomplex(0, og.Surreal.from_rational(-1, 2)))

    def test_field_axioms_on_samples(self):
        S = og.Surcomplex
        samples = [S(0, 0), S(1, 0), S(0, 1), S(3, 4), S(og.omega(), 1)]
        self.assert_ring(samples, S(0, 0), S(1, 0))

    def test_embeds_the_surreals_but_has_no_order(self):
        S = og.Surcomplex
        self.assertEqual(S(2, 0), og.surreal(2))
        self.assertEqual(S(1, 2) + og.omega(), S(og.omega() + 1, 2))
        with self.assertRaises(TypeError):
            S(1, 0) < S(2, 0)


class OmnificTests(OgdoadTestCase):
    def test_omnific_integers_form_a_ring_not_a_field(self):
        w = og.omnific_omega()
        self.assertEqual(repr(w * w), "ω↑2")
        self.assertEqual(og.omnific(3) * og.omnific(4), og.omnific(12))
        with self.assertRaises(ValueError):
            w.inv()  # 1/omega = epsilon is not in Oz
        self.assertEqual(og.omnific(1).inv(), og.omnific(1))
        self.assertEqual(og.omnific(-1).inv(), og.omnific(-1))

    def test_validator_and_checked_embedding(self):
        self.assertTrue(og.is_omnific_integer(og.omega()))
        self.assertFalse(og.is_omnific_integer(og.epsilon()))
        with self.assertRaises(ValueError):
            og.Omnific.from_surreal(og.epsilon())
        self.assertEqual(og.Omnific.from_surreal(og.omega()), og.omnific_omega())

    def test_ring_axioms_on_samples(self):
        O = og.omnific
        samples = [O(0), O(1), O(-3), og.omnific_omega(), og.omnific_omega() + O(2)]
        self.assert_ring(samples, O(0), O(1))


# ---------------------------------------------------------------------------
# Ordinal nimbers On_2
# ---------------------------------------------------------------------------


class OrdinalTests(OgdoadTestCase):
    O = og.Ordinal

    def test_nim_addition_is_xor_and_self_inverse(self):
        O = self.O
        w = O.omega()
        self.assertEqual(w.nim_add(w), O(0))
        self.assertEqual(w + w, O(0))
        self.assertEqual(O.monomial(O(1), 2).nim_add(w), O.from_omega3_coeffs([0, 3, 0]))
        self.assertEqual(repr(O.monomial(O(1), 2).nim_add(w)), "*(ω⋅3)")

    def test_conways_omega_cubed_is_two(self):
        O = self.O
        w = O.omega()
        self.assertEqual(w.nim_mul(w), O.omega_pow(O(2)))
        self.assertEqual(w.nim_mul(w).nim_mul(w), O(2))
        self.assertEqual(w.nim_pow(3), O(2))
        self.assertEqual(w.nim_pow(0), O(1))
        self.assertEqual(O(2).nim_mul(O(2)), O(3))

    def test_field_axioms_on_cube_cell_samples(self):
        O = self.O
        samples = [O(0), O(1), O(2), O.omega(), O.omega_pow(O(2)),
                   O.from_omega3_coeffs([3, 1, 1]), O.from_omega3_coeffs([1, 0, 2])]
        # Nim addition (+) and nim multiplication (*) are the operators.
        self.assert_field(samples, O(0), O(1))

    def test_cantor_ordinal_arithmetic_is_a_separate_namespace(self):
        O = self.O
        w = O.omega()
        self.assertEqual(O(1).ord_add(w), w)  # absorption
        self.assertNotEqual(w.ord_add(O(1)), w)
        self.assertEqual(repr(w.ord_add(w)), "*(ω⋅2)")
        self.assertEqual(w.ord_add(w).terms, [(O(1), 2)])
        self.assertEqual(O(2).ord_mul(w), w)
        self.assertEqual(repr(w.ord_mul(O(2))), "*(ω⋅2)")

    def test_order_and_fuzzy_relation_are_distinct(self):
        O = self.O
        w = O.omega()
        self.assertTrue(O(3) < w < O.omega_pow(O(2)))
        self.assertTrue(w.fuzzy(O.omega_pow(O(2))))
        self.assertFalse(w.fuzzy(w))

    def test_has_no_power_operator(self):
        # AGENTS.md: Ordinal exposes checked nim_pow and has no ``**``.
        with self.assertRaises(TypeError):
            self.O.omega() ** 3

    def test_checked_inverse_and_sqrt_inside_the_boundary(self):
        O = self.O
        w = O.omega()
        self.assertEqual(O(3).checked_inv(), O(2))
        self.assertEqual(w * w.inv(), O(1))
        self.assertEqual(w.checked_sqrt().nim_mul(w.checked_sqrt()), w)
        self.assertIsNone(O(0).checked_inv())
        self.assertEqual(O(5).checked_sqrt().nim_mul(O(5).checked_sqrt()), O(5))

    def test_kummer_boundary_returns_none(self):
        O = self.O
        w = O.omega()
        past = O.omega_pow(O.omega_pow(O.omega_pow(w)))
        self.assertIsNone(past.nim_mul(past))
        self.assertIsNone(past.nim_pow(2))
        self.assertIsNone(past.checked_inv())
        self.assertIsNone(past.checked_sqrt())
        self.assertIsNone(past.finite_subfield_degree())
        with self.assertRaises(ValueError):
            past.inv()  # the unchecked spelling refuses instead of guessing

    def test_checked_powers_never_wrap_silently(self):
        O = self.O
        w = O.omega()
        wpow = O.omega_pow(w)
        self.assertEqual(wpow.nim_mul(w), O.omega_pow(w.ord_add(O(1))))
        self.assertEqual(wpow.nim_pow(5), O(4))
        with self.assertRaises(OverflowError):
            O(3).nim_pow(2**200)
        with self.assertRaises(OverflowError):
            O(3).nim_pow(-1)

    def test_finite_subfield_degrees(self):
        O = self.O
        self.assertEqual([O(v).finite_subfield_degree() for v in (0, 1, 2, 16)], [1, 1, 2, 8])
        self.assertEqual(O.omega().finite_subfield_degree(), 6)
        self.assertEqual(og.ordinal_finite_subfield_degree(O.omega()), 6)
        self.assertEqual(og.ordinal_common_finite_subfield_degree([O.omega(), O(16)]), 24)

    def test_omega_cube_cell_round_trip(self):
        O = self.O
        cell = O.from_omega3_coeffs([3, 1, 1])
        self.assertEqual(cell.as_below_omega3(), [3, 1, 1])
        self.assertEqual(repr(cell), "*(ω↑2 + ω + 3)")
        self.assertIsNone(O.omega().as_finite())
        self.assertEqual(O(5).as_finite(), 5)

    def test_payload_width(self):
        O = self.O
        self.assertEqual(repr(O(2**128 - 1)), "*" + str(2**128 - 1))
        with self.assertRaises(OverflowError):
            O(2**200)
        with self.assertRaises(OverflowError):
            O(-1)


# ---------------------------------------------------------------------------
# p-adic, Laurent, Witt-vector and other local scalar cells
# ---------------------------------------------------------------------------


class LocalScalarTests(OgdoadTestCase):
    def test_zmod_two_to_the_four(self):
        Z = og.Zp2_4
        self.assertEqual((Z.prime(), Z.precision(), Z.modulus()), (2, 4, 16))
        self.assert_ring([Z(i) for i in range(16)], Z(0), Z(1))
        self.assertEqual(Z(16), Z(0))
        self.assertEqual(repr(Z(3)), "3 (mod 2^4)")
        for i in range(1, 16, 2):
            self.assertTrue(Z(i).is_unit())
            self.assertEqual(Z(i) * Z(i).inv(), Z(1))
        with self.assertRaises(ValueError):
            Z(2).inv()
        self.assertEqual(Z(2).valuation(), 1)
        self.assertEqual(hash(Z(3)), hash(Z(19)))

    def test_checked_square_roots_decline_or_refuse(self):
        Z = og.Zp2_4
        self.assertIsNone(Z(3).sqrt())  # 3 is not a square mod 16
        with self.assertRaises(ValueError):
            Z(4).sqrt()  # a square, but the construction is not implemented

    def test_qp_valuation_and_uniformizer(self):
        Q = og.Qp5_4
        self.assertEqual((Q.prime(), Q.precision()), (5, 4))
        self.assertEqual(Q.uniformizer().valuation(), 1)
        self.assertEqual(Q.from_rational(1, 5).valuation(), -1)
        self.assertEqual(Q.from_int(25).valuation(), 2)
        self.assertIsNone(Q.zero().valuation())
        self.assertEqual(Q.from_rational(1, 5) * Q.from_int(5), Q.one())
        root = Q.from_int(4).sqrt()
        self.assertEqual(root * root, Q.from_int(4))
        self.assertIsNone(Q.from_int(2).sqrt())
        self.assertFalse(Q.from_int(2).is_square())
        self.assertEqual(Q.from_int(25).to_integer(), og.Zp5_4(25))
        with self.assertRaises(ValueError):
            Q.zero().inv()

    def test_unramified_extension_and_witt_vectors(self):
        W, Q = og.WittVec3_4_2, og.Qq3_4_2
        prim = og.F9.primitive_element()
        t = W.teichmuller(prim)
        self.assertEqual(t.residue(), prim)
        # The Teichmuller lift is multiplicative.
        other = prim * prim * prim
        self.assertEqual(t * W.teichmuller(other), W.teichmuller(prim * other))
        q = Q.from_witt(t)
        self.assertEqual(q.valuation(), 0)
        self.assertEqual((q * Q.uniformizer()).valuation(), 1)
        self.assertEqual(Q.uniformizer().valuation(), 1)

    def test_laurent_series(self):
        L = og.LaurentFp5_6
        t = L.t()
        self.assertEqual(t.valuation(), 1)
        self.assertEqual(L.one().valuation(), 0)
        self.assertEqual(t * t.inv(), L.one())
        self.assertEqual(repr(t * t), "1·t^2 + O(t^3)")

    def test_ramified_extension_has_valuation_half(self):
        R = og.RamifiedQp5_4_E2
        pi = R.pi()
        self.assertEqual(pi.valuation(), 1)  # normalised on the uniformizer pi
        self.assertEqual((pi * pi).valuation(), 2)
        self.assertEqual(R.uniformizer().valuation(), 1)

    def test_gauss_valued_function_field(self):
        G = og.GaussQp5_4
        self.assertEqual(G.t().valuation(), 0)
        self.assertEqual(G.from_base(5).valuation(), 1)


# ---------------------------------------------------------------------------
# Polynomials and rational functions, tropical semirings
# ---------------------------------------------------------------------------


class PolynomialTests(OgdoadTestCase):
    def test_nimber_polynomials_have_characteristic_two_squares(self):
        P = og.NimberPoly
        one_plus_t = P([1, 1])
        self.assertEqual(one_plus_t * one_plus_t, P([1, 0, 1]))  # (1+t)^2 = 1+t^2
        self.assertEqual(P([1, 0, 1]).gcd(one_plus_t), one_plus_t)
        self.assertEqual(repr(one_plus_t * one_plus_t), "t↑2 + *1")

    def test_integer_polynomial_division_and_evaluation(self):
        P = og.IntegerPoly
        t = P.x()
        self.assertEqual((5 * t + 1) @ 7, 36)
        self.assertTrue(((t * t - 1) % (t - 1)).is_zero())
        self.assertEqual((t * t - 1).divrem(t - 1), (t + 1, P.zero()))
        g = P([2, 2]).gcd(P([4, 4]))
        self.assertEqual(g.degree, 1)
        self.assertTrue((P([2, 2]) % g).is_zero() and (P([4, 4]) % g).is_zero())

    def test_fp5_polynomial_ring_axioms(self):
        P = og.Fp5Poly
        t = P.x()
        samples = [P.zero(), P.one(), t, t + 1, t * t + 2]
        self.assert_ring(samples, P.zero(), P.one())

    def test_rational_function_field_axioms(self):
        F = og.Fp5RationalFunction
        t = F.t()
        samples = [F.zero(), F.one(), t, t + 1, F.one() / (t + 1)]
        self.assert_ring(samples, F.zero(), F.one())
        for s in samples[1:]:
            self.assertEqual(s * s.inv(), F.one())

    def test_nimber_rational_function_arithmetic(self):
        F, P = og.NimberRationalFunction, og.NimberPoly
        func = F([1, 1], [0, 1])  # (1 + t) / t
        t = F.t()
        product = func * t
        self.assertEqual(product.den, P([1]))
        self.assertEqual(product, F([1, 1], [1]))


class TropicalTests(OgdoadTestCase):
    def test_max_plus_semiring_laws(self):
        T = og.MaxPlusTropical
        samples = [T.zero(), T.one(), T.finite(3, 1), T.finite(5, 1), T.finite(-2, 3)]
        zero, one = T.zero(), T.one()
        for a, b, c in itertools.product(samples, repeat=3):
            self.assertEqual(a + b, b + a)
            self.assertEqual((a + b) + c, a + (b + c))
            self.assertEqual((a * b) * c, a * (b * c))
            self.assertEqual(a * (b + c), a * b + a * c)
        for a in samples:
            self.assertEqual(a + zero, a)
            self.assertEqual(a * one, a)
            self.assertEqual(a * zero, zero)
            self.assertEqual(a + a, a)  # idempotent addition
        self.assertEqual((T.finite(3, 1) + T.finite(5, 1)).value(), (5, 1))
        self.assertEqual((T.finite(3, 1) * T.finite(5, 1)).value(), (8, 1))
        self.assertTrue(zero.is_zero() and zero.is_infinity())
        self.assertEqual(zero, T.infinity())
        self.assertFalse(T.one().is_zero())
        self.assertIsNone(zero.value())

    def test_min_plus_semiring_laws(self):
        T = og.MinPlusTropical
        samples = [T.zero(), T.one(), T.finite(3, 1), T.finite(5, 1)]
        for a, b, c in itertools.product(samples, repeat=3):
            self.assertEqual(a * (b + c), a * b + a * c)
        self.assertEqual((T.finite(3, 1) + T.finite(5, 1)).value(), (3, 1))
        self.assertEqual((T.finite(3, 1) * T.finite(5, 1)).value(), (8, 1))

    def test_reprs_mark_the_absorbing_element(self):
        self.assertEqual(repr(og.MaxPlusTropical.zero()), "−∞")
        self.assertEqual(repr(og.MinPlusTropical.zero()), "∞")
        self.assertEqual(repr(og.MaxPlusTropical.finite(3, 1)), "3")

    def test_the_two_tropical_worlds_do_not_mix(self):
        with self.assertRaises(TypeError):
            og.MaxPlusTropical.finite(3, 1) + og.MinPlusTropical.finite(3, 1)
        self.assertNotEqual(og.MaxPlusTropical.one(), og.MinPlusTropical.one())


# ---------------------------------------------------------------------------
# Cross-world contract: AGENTS.md invariant 6
# ---------------------------------------------------------------------------

WORLDS = {
    "Nimber": lambda: og.Nimber(1),
    "Fp2": lambda: og.Fp2(1),
    "Fp3": lambda: og.Fp3(1),
    "Fp5": lambda: og.Fp5(1),
    "Fp7": lambda: og.Fp7(1),
    "Fp11": lambda: og.Fp11(1),
    "Fp13": lambda: og.Fp13(1),
    "F4": lambda: og.F4.one(),
    "F8": lambda: og.F8.one(),
    "F9": lambda: og.F9.one(),
    "F16": lambda: og.F16.one(),
    "F25": lambda: og.F25.one(),
    "F27": lambda: og.F27.one(),
    "Rational": lambda: og.Rational(1),
    "Integer": lambda: og.Integer(1),
    "Surreal": lambda: og.surreal(1),
    "Surcomplex": lambda: og.Surcomplex(1, 0),
    "Omnific": lambda: og.omnific(1),
    "Ordinal": lambda: og.Ordinal(1),
    "Zp2_4": lambda: og.Zp2_4(1),
    "Zp3_4": lambda: og.Zp3_4(1),
    "Qp5_4": lambda: og.Qp5_4.one(),
    "Qq3_4_2": lambda: og.Qq3_4_2.one(),
    "WittVec3_4_2": lambda: og.WittVec3_4_2.one(),
    "LaurentFp5_6": lambda: og.LaurentFp5_6.one(),
    "LaurentRational_6": lambda: og.LaurentRational_6([1]),
    "RamifiedQp5_4_E2": lambda: og.RamifiedQp5_4_E2.one(),
    "GaussQp5_4": lambda: og.GaussQp5_4.one(),
    "NimberPoly": lambda: og.NimberPoly([1]),
    "Fp5Poly": lambda: og.Fp5Poly.one(),
    "IntegerPoly": lambda: og.IntegerPoly([1]),
    "Fp5RationalFunction": lambda: og.Fp5RationalFunction.one(),
    "NimberRationalFunction": lambda: og.NimberRationalFunction.t(),
    "MaxPlus": lambda: og.MaxPlusTropical.finite(1, 1),
    "MinPlus": lambda: og.MinPlusTropical.finite(1, 1),
    "Complex64": lambda: og.Complex64(1, 0),
}

# Deliberate embeddings of a coefficient world into a larger one; the larger
# world accepts the smaller as an operand (and compares equal to it).
COERCIONS = {
    ("Rational", "Integer"),
    ("Surcomplex", "Surreal"),
    ("Omnific", "Surreal"),
    ("Qq3_4_2", "WittVec3_4_2"),
    ("LaurentFp5_6", "Fp5"),
    ("LaurentRational_6", "Rational"),
    ("LaurentRational_6", "Integer"),
    ("RamifiedQp5_4_E2", "Qp5_4"),
    ("GaussQp5_4", "Qp5_4"),
    ("NimberPoly", "Nimber"),
    ("Fp5Poly", "Fp5"),
    ("IntegerPoly", "Integer"),
    ("Fp5RationalFunction", "Fp5"),
    ("Fp5RationalFunction", "Fp5Poly"),
    ("NimberRationalFunction", "Nimber"),
    ("NimberRationalFunction", "NimberPoly"),
}

# Worlds whose ``==`` currently raises TypeError for a foreign operand instead
# of comparing unequal; see ``test_equality_never_raises_for_exact_scalars``.
EQ_RAISES = {"Rational", "Integer", "Surreal", "Omnific"}


def _foreign_pairs():
    for a, b in itertools.permutations(WORLDS, 2):
        if (a, b) not in COERCIONS and (b, a) not in COERCIONS:
            yield a, b


class CrossWorldContractTests(OgdoadTestCase):
    """Per-backend Python types never mix (AGENTS.md invariant 6)."""

    def test_arithmetic_across_worlds_raises_type_error(self):
        for a, b in _foreign_pairs():
            x, y = WORLDS[a](), WORLDS[b]()
            for opname, op in (("+", lambda p, q: p + q), ("*", lambda p, q: p * q),
                               ("-", lambda p, q: p - q)):
                with self.subTest(a=a, b=b, op=opname):
                    with self.assertRaises(TypeError):
                        op(x, y)

    def test_equality_across_worlds_compares_unequal(self):
        for a, b in _foreign_pairs():
            if a in EQ_RAISES or b in EQ_RAISES:
                continue  # covered by the expected-failure test below
            x, y = WORLDS[a](), WORLDS[b]()
            with self.subTest(a=a, b=b):
                self.assertFalse(x == y)
                self.assertTrue(x != y)

    def test_equality_never_raises_for_exact_scalars(self):
        # Cross-world equality compares unequal (AGENTS.md invariant 6): a
        # foreign operand -- another world, None, a str -- never raises, so
        # ``x in [None, x]`` and mixed-key lookups work.
        offenders = []
        for name in sorted(EQ_RAISES):
            x = WORLDS[name]()
            others = [None, "text", 1.5, object()]
            others += [WORLDS[b]() for b in WORLDS if b != name
                       and (name, b) not in COERCIONS and (b, name) not in COERCIONS]
            for other in others:
                for left, right in ((x, other), (other, x)):
                    try:
                        if left == right or not (left != right):
                            offenders.append((name, type(other).__name__, "equal"))
                    except TypeError:
                        offenders.append((name, type(other).__name__, "TypeError"))
        self.assertEqual(offenders, [])

    def test_equality_across_declared_embeddings_is_symmetric(self):
        # Across a declared coefficient embedding ``==`` does not depend on
        # operand order: ``Fp5(1) == Fp5Poly.one()`` agrees with the reverse.
        ones = dict(WORLDS)
        ones["NimberRationalFunction"] = lambda: og.NimberRationalFunction.one()
        asymmetric = []
        for big, small in sorted(COERCIONS):
            x, y = ones[big](), ones[small]()
            outcomes = []
            for left, right in ((x, y), (y, x)):
                try:
                    outcomes.append(bool(left == right))
                except TypeError:
                    outcomes.append("TypeError")
            if outcomes[0] != outcomes[1]:
                asymmetric.append((big, small, outcomes))
        self.assertEqual(asymmetric, [])

    def test_declared_embeddings_work_in_the_documented_direction(self):
        for big, small in sorted(COERCIONS):
            x, y = WORLDS[big](), WORLDS[small]()
            with self.subTest(big=big, small=small):
                self.assertIs(type(x + y), type(x))
                self.assertIs(type(x * y), type(x))

    def test_embeddings_are_one_directional_for_arithmetic(self):
        # Surreal + Surcomplex is refused even though Surcomplex + Surreal works.
        with self.assertRaises(TypeError):
            og.surreal(1) + og.Surcomplex(1, 0)
        with self.assertRaises(TypeError):
            og.Integer(1) + og.Rational(1)

    def test_float_operands_are_never_coerced(self):
        for name in ("Nimber", "Fp5", "Rational", "Surreal", "Integer", "F8"):
            x = WORLDS[name]()
            with self.subTest(world=name):
                with self.assertRaises(TypeError):
                    x + 0.5

    def test_exact_worlds_compare_equal_to_python_integers(self):
        self.assertTrue(og.Integer(7) == 7)
        self.assertTrue(og.Rational(3) == 3)
        self.assertTrue(og.surreal(3) == 3)



# ---------------------------------------------------------------------------
# Integer payload widths, remaining scalar types, rendering
# ---------------------------------------------------------------------------


class PayloadWidthTests(OgdoadTestCase):
    """Python integers are validated against the core i128/u128 widths."""

    I128_HI, I128_LO = 2**127 - 1, -(2**127)

    def test_signed_constructors_accept_exactly_the_i128_range(self):
        constructors = {
            "Integer": og.Integer,
            "Rational": og.Rational,
            "Rational.integer": og.Rational.integer,
            "surreal": og.surreal,
            "Surreal.from_int": og.Surreal.from_int,
            "omnific": og.omnific,
            "MaxPlusTropical.int": og.MaxPlusTropical.int,
            "MinPlusTropical.int": og.MinPlusTropical.int,
            "Fp5": og.Fp5,
            "Zp2_4": og.Zp2_4,
            "Qp5_4.from_int": og.Qp5_4.from_int,
        }
        for name, make in constructors.items():
            with self.subTest(constructor=name):
                make(self.I128_HI)
                make(self.I128_LO)
                for bad in (2**127, -(2**127) - 1, 2**200):
                    with self.assertRaises(OverflowError):
                        make(bad)

    def test_unsigned_constructors_accept_exactly_the_u128_range(self):
        for name, make in (("Nimber", og.Nimber), ("Ordinal", og.Ordinal)):
            with self.subTest(constructor=name):
                make(0)
                make(2**128 - 1)
                for bad in (2**128, -1, 2**300):
                    with self.assertRaises(OverflowError):
                        make(bad)

    def test_wide_values_survive_a_round_trip(self):
        self.assertEqual(og.Integer(self.I128_HI).value, self.I128_HI)
        self.assertEqual(og.Integer(self.I128_LO).value, self.I128_LO)
        self.assertEqual(og.Nimber(2**128 - 1).value, 2**128 - 1)
        wide = og.Rational(self.I128_HI, 3)  # 2^127 - 1 is not divisible by 3
        self.assertEqual((wide.numer(), wide.denom()), (self.I128_HI, 3))

    def test_unsigned_arguments_to_raw_functions_are_validated(self):
        for fn, args in ((og.nim_mul, (2**128, 1)), (og.nim_add, (-1, 1)),
                         (og.nim_pow, (2, 2**128)), (og.nim_square, (2**128,))):
            with self.assertRaises(OverflowError):
                fn(*args)
        self.assertEqual(og.nim_pow(2, 2**128 - 1), og.nim_pow(2, (2**128 - 1) % 3))

    def test_octal_digits_and_field_indices_are_range_checked(self):
        with self.assertRaises(ValueError):
            og.OctalCode([8])
        with self.assertRaises(ValueError):
            og.F8.from_index(8)
        with self.assertRaises(ValueError):
            og.F8.from_index(2**100)


class Complex64Tests(OgdoadTestCase):
    def test_floating_point_complex_arithmetic(self):
        z, w = og.Complex64(1, 2), og.Complex64(3, 4)
        self.assertEqual(repr(z * w), "Complex64(re=-5, im=10)")
        self.assertEqual((z + w).re, 4)
        self.assertEqual((z - w).im, -2)
        self.assertTrue((z * w).approx_eq(og.Complex64(-5, 10), 1e-12))
        self.assertFalse(z.approx_eq(w, 1e-12))
        self.assertEqual(og.Complex64.one().re, 1)
        self.assertAlmostEqual(og.Complex64.cis(0.0).re, 1.0)

    def test_complex64_is_its_own_world(self):
        with self.assertRaises(TypeError):
            og.Complex64(1, 0) + og.Fp5(1)
        self.assertFalse(og.Complex64(1, 0) == og.Fp5(1))


class ReprInjectivityTests(OgdoadTestCase):
    """Canonical display must tell distinct values apart."""

    def assert_injective(self, values):
        seen = {}
        for v in values:
            key = repr(v)
            if key in seen:
                self.assertEqual(seen[key], v, f"{key!r} renders two different values")
            seen[key] = v

    def test_surreal_and_ordinal_reprs(self):
        w, e = og.omega(), og.epsilon()
        values = [og.surreal(0), og.surreal(1), og.surreal(-1), w, e, w + 1, w - 1, -w,
                  w * w, w + e, og.Surreal.from_rational(1, 2), og.Surreal.from_rational(-3, 4),
                  og.surreal(3) * w ** 2 - w + 5, og.omega_pow(w)]
        self.assert_injective(values)
        O = og.Ordinal
        ords = [O(0), O(1), O(2), O.omega(), O.omega().ord_add(O(1)), O.omega_pow(O(2)),
                O.from_omega3_coeffs([3, 1, 1]), O.monomial(O(1), 2), O.omega_pow(O.omega())]
        self.assert_injective(ords)

    def test_finite_field_and_function_field_reprs(self):
        self.assert_injective([og.F9.from_index(i) for i in range(9)])
        self.assert_injective([og.F8.from_index(i) for i in range(8)])
        t = og.Fp5RationalFunction.t()
        one = og.Fp5RationalFunction.one()
        self.assert_injective([t, one, t + one, one / (t + one), t * t, one / t, t / (t + one)])
        nt = og.NimberRationalFunction.t()
        self.assert_injective([nt, nt * nt, og.NimberRationalFunction([1, 1], [0, 1]),
                               og.NimberRationalFunction([1], [0, 1])])

    def test_surcomplex_repr_is_injective(self):
        # A multi-term imaginary part is parenthesised, so Surcomplex(w, 1) and
        # Surcomplex(0, w + 1) render differently.
        w = og.omega()
        a, b = og.Surcomplex(w, 1), og.Surcomplex(0, w + 1)
        self.assertNotEqual(a, b)
        self.assertNotEqual(repr(a), repr(b))

if __name__ == "__main__":
    unittest.main()
