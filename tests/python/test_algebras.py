"""Clifford and divided-power algebras, multivectors, linear maps, spinors,
conformal GA.  Laws and contracts, seeded from demo.py and the README."""

import itertools
import math
import random
import unittest

import ogdoad as og

from _support import OgdoadTestCase, quiet_rust_panics


def random_mv(alg, rng, scalar, terms=5):
    """A reproducible sum of scalar multiples of generator products."""
    total = alg.zero()
    for _ in range(terms):
        word = alg.scalar(scalar(rng))
        for i in range(alg.dim):
            if rng.random() < 0.5:
                word = word * alg.gen(i)
        total = total + word
    return total


SCALARS = {
    "nimber": lambda rng: og.Nimber(rng.randrange(1, 1 << 16)),
    "surreal": lambda rng: og.surreal(rng.randint(-3, 3)),
    "rational": lambda rng: og.Rational(rng.randint(-5, 5), rng.randint(1, 4)),
    "fp3": lambda rng: og.Fp3(rng.randrange(3)),
    "f8": lambda rng: og.F8.from_index(rng.randrange(8)),
}


class AssociativityOracleTests(OgdoadTestCase):
    """The product is associative and distributive for every metric shape
    (the engine's core independent oracle, exercised through the bindings)."""

    def check(self, alg, scalar, seed, rounds=6):
        rng = random.Random(seed)
        for _ in range(rounds):
            a, b, c = (random_mv(alg, rng, scalar) for _ in range(3))
            self.assertEqual((a * b) * c, a * (b * c))
            self.assertEqual(a * (b + c), a * b + a * c)
            self.assertEqual((a + b) * c, a * c + b * c)

    def test_nimber_polar_metric(self):
        alg = og.NimberAlgebra(q=[2, 3, 1], b={(0, 1): 1, (1, 2): 3})
        self.check(alg, SCALARS["nimber"], 1)

    def test_nimber_ordered_contraction_metric(self):
        alg = og.NimberAlgebra(q=[2, 1, 1], a={(0, 1): 1, (0, 2): 2})
        self.check(alg, SCALARS["nimber"], 2)

    def test_surreal_orthogonal_and_general_bilinear(self):
        self.check(og.SurrealAlgebra(q=[1, 1, 1]), SCALARS["surreal"], 3)
        general = og.SurrealAlgebra(q=[1, 1, 2], b=None, a={(0, 1): og.surreal(5), (1, 2): og.surreal(-2)})
        self.check(general, SCALARS["surreal"], 4)

    def test_transfinite_metric(self):
        alg = og.SurrealAlgebra(q=[og.omega(), og.epsilon(), 1])
        self.check(alg, SCALARS["surreal"], 5, rounds=3)

    def test_rational_degenerate_and_pga(self):
        self.check(og.RationalAlgebra(q=[0, 0, 0]), SCALARS["rational"], 6)
        self.check(og.RationalAlgebra.pga(2), SCALARS["rational"], 7)

    def test_odd_and_even_characteristic_finite_fields(self):
        self.check(og.Fp3Algebra([1, 2, 1]), SCALARS["fp3"], 8)
        self.check(og.F8Algebra(q=[1, 0, 1], b={(0, 1): 1}), SCALARS["f8"], 9)


class CharacteristicTwoMetricTests(OgdoadTestCase):
    """q, b (and a) are distinct data in characteristic two."""

    N = og.Nimber

    def algebra(self, q, b=None, a=None):
        return og.NimberAlgebra(q=[self.N(v) for v in q], b=b, a=a)

    def test_square_of_a_generator_is_q_regardless_of_b(self):
        for b in (None, {(0, 1): 1}, {(0, 1): 3}):
            A = self.algebra([2, 3], b)
            self.assertEqual(A.gen(0) ** 2, A.scalar(self.N(2)))
            self.assertEqual(A.gen(1) ** 2, A.scalar(self.N(3)))
            self.assertEqual(A.q(), [self.N(2), self.N(3)])

    def test_anticommutator_is_b_regardless_of_q(self):
        for q in ([2, 3], [0, 0], [5, 7]):
            A = self.algebra(q, {(0, 1): 1})
            e0, e1 = A.gen(0), A.gen(1)
            self.assertEqual(e0 * e1 + e1 * e0, A.scalar(self.N(1)))
            self.assertEqual(A.b_terms(), [(0, 1, self.N(1))])

    def test_without_b_the_generators_commute(self):
        A = self.algebra([2, 3])
        e0, e1 = A.gen(0), A.gen(1)
        self.assertEqual(e0 * e1, e1 * e0)
        self.assertEqual(A.b_terms(), [])
        self.assertEqual(e0 * e1, e0 & e1)

    def test_with_b_the_generators_do_not_commute(self):
        A = self.algebra([2, 3], {(0, 1): 1})
        e0, e1 = A.gen(0), A.gen(1)
        self.assertNotEqual(e0 * e1, e1 * e0)
        self.assertEqual(e0 * e1, e0 & e1)
        self.assertEqual(e1 * e0, A.scalar(self.N(1)) + (e0 & e1))

    def test_vector_square_is_the_quadratic_form_with_polar_cross_term(self):
        # Q(sum u_i e_i) = sum q_i u_i^2 + sum_{i<j} b_ij u_i u_j.
        N = self.N
        q = [N(2), N(3), N(1)]
        b = {(0, 1): N(1), (0, 2): N(2), (1, 2): N(3)}
        A = og.NimberAlgebra(q=q, b=b)
        rng = random.Random(10)
        for _ in range(20):
            u = [N(rng.randrange(1 << 10)) for _ in range(3)]
            vec = sum((u[i] * A.gen(i) for i in range(3)), A.zero())
            expected = sum((q[i] * u[i] * u[i] for i in range(3)), N(0))
            for (i, j), bij in b.items():
                expected = expected + bij * u[i] * u[j]
            self.assertEqual(vec * vec, A.scalar(expected))

    def test_ordered_contraction_does_not_change_the_polar_form(self):
        # a records B(e_i, e_j) for i < j; the polar b = B + B^T is independent.
        A = self.algebra([1, 1], b=None, a={(0, 1): 1})
        e0, e1 = A.gen(0), A.gen(1)
        self.assertEqual(A.a_terms(), [(0, 1, self.N(1))])
        self.assertEqual(A.b_terms(), [])
        self.assertTrue(A.has_upper())
        self.assertEqual(e0 * e1, A.scalar(self.N(1)) + (e0 & e1))
        self.assertEqual(e0 * e1 + e1 * e0, A.zero())
        self.assertFalse(self.algebra([1, 1], {(0, 1): 1}).has_upper())

    def test_demo_noncommutative_nimber_plane(self):
        N = self.N
        A = og.NimberAlgebra(q=[N(2), N(3)], b={(0, 1): 1})
        e0, e1 = A.gen(0), A.gen(1)
        self.assertEqual(repr(e0 * e1), "e0∧e1")
        self.assertEqual(repr(e1 * e0), "*1 + e0∧e1")
        self.assertEqual(repr(e0 * e1 + e1 * e0), "*1")
        self.assertEqual(repr(e0 ** 2), "*2")
        self.assertEqual(e0 * e1 + e1 * e0, A.scalar(N(1)))

    def test_metric_data_is_validated(self):
        N = self.N
        with self.assertRaises(ValueError):
            og.NimberAlgebra(q=[1, 1], b={(0, 5): 1})  # index out of range
        with self.assertRaises(ValueError):
            og.NimberAlgebra(q=[1, 1], b={(0, 0): 1})  # diagonal b is q's job
        with self.assertRaises(TypeError):
            og.NimberAlgebra(q=[og.Fp3(1)])  # another world's scalar
        with self.assertRaises(ValueError):
            og.SurrealAlgebra(q=[1] * 129)  # more than 128 generators
        self.assertEqual(og.SurrealAlgebra(q=[1] * 128).dim, 128)
        with self.assertRaises(ValueError):
            self.algebra([1, 1]).gen(2)

    def test_negation_is_the_identity_so_signs_never_appear(self):
        A = self.algebra([2, 3], {(0, 1): 1})
        for mv in (A.gen(0), A.gen(0) * A.gen(1), A.scalar(self.N(5)) + A.gen(1)):
            self.assertEqual(-mv, mv)
            self.assertEqual(mv - mv, A.zero())
        self.assertEqual((A.gen(0) * A.gen(1)).reverse(), A.gen(1) * A.gen(0))


class SurrealCliffordTests(OgdoadTestCase):
    def setUp(self):
        self.E = og.SurrealAlgebra(q=[1, 1, 1])
        self.e0, self.e1, self.e2 = (self.E.gen(i) for i in range(3))

    def test_generators_square_to_the_metric(self):
        E = self.E
        for i in range(3):
            self.assertEqual(E.gen(i) ** 2, E.scalar(1))
        self.assertEqual(E.q(), [1, 1, 1])
        self.assertEqual(E.dim, 3)
        self.assertTrue(E.is_orthogonal())

    def test_orthogonal_vectors_anticommute(self):
        e0, e1 = self.e0, self.e1
        self.assertEqual(e0 * e1, -(e1 * e0))
        self.assertEqual(e0 * e1, e0 & e1)
        self.assertEqual(e0.anticommutator(e1), self.E.zero())
        self.assertEqual(e0.commutator(e1), 2 * (e0 & e1))
        self.assertEqual(e0.anticommutator(e0), self.E.scalar(2))

    def test_transfinite_metric_from_the_demo(self):
        S = og.SurrealAlgebra(q=[og.omega(), og.epsilon()])
        b = S.gen(0) * S.gen(1)
        self.assertEqual(S.gen(0) ** 2, S.scalar(og.omega()))
        self.assertEqual(S.gen(1) ** 2, S.scalar(og.epsilon()))
        self.assertEqual(b ** 2, S.scalar(-1))  # -(omega * epsilon)
        self.assertEqual(repr(b ** 2), "-1")
        self.assertEqual(repr(S.gen(0) ** 2), "ω")

    def test_wedge_is_graded_antisymmetric_associative_and_nilpotent(self):
        e0, e1, e2 = self.e0, self.e1, self.e2
        x, y = e0 + 2 * e1, e1 - e2
        self.assertEqual(x & y, -(y & x))
        self.assertTrue((x & x).is_zero())
        self.assertEqual((e0 & e1) & e2, e0 & (e1 & e2))
        self.assertEqual(e0 & e1 & e2, self.E.pseudoscalar())
        self.assertEqual(repr(self.E.pseudoscalar()), "e0∧e1∧e2")

    def test_xor_is_a_power_hint_not_a_wedge(self):
        with self.assertRaises(TypeError):
            self.e0 ^ self.e1

    def test_contractions(self):
        e0, e1 = self.e0, self.e1
        self.assertEqual(e0 << (e0 & e1), e1)
        self.assertEqual((e0 & e1) >> e1, e0)
        self.assertEqual(e0.left_contract(e0 & e1), e1)
        self.assertEqual((e0 & e1).right_contract(e1), e0)
        self.assertEqual(e1 << (e0 & e1), -e0)
        self.assertEqual(e0 << e0, self.E.scalar(1))

    def test_reversion_involution_and_conjugate(self):
        e0, e1, e2 = self.e0, self.e1, self.e2
        a, b = e0 + e1 * e2, e1 + e0 * e1
        self.assertEqual((a * b).reverse(), b.reverse() * a.reverse())
        self.assertEqual(~(a * b), ~b * ~a)
        self.assertEqual((a * b).grade_involution(), a.grade_involution() * b.grade_involution())
        self.assertEqual(a.clifford_conjugate(), a.reverse().grade_involution())
        self.assertEqual((e0 & e1).clifford_conjugate(), -(e0 & e1))
        self.assertEqual(repr(~(e0 * e1)), "-e0∧e1")

    def test_grade_projection_and_parts(self):
        mv = self.e0 * self.e1 + self.e2 + self.E.scalar(2)
        self.assertEqual(mv.grade_part(0), self.E.scalar(2))
        self.assertEqual(mv.grade_part(1), self.e2)
        self.assertEqual(mv.grade_part(2), self.e0 * self.e1)
        self.assertTrue(mv.grade_part(3).is_zero())
        self.assertEqual(mv.even_part(), self.E.scalar(2) + self.e0 * self.e1)
        self.assertEqual(mv.scalar_part(), 2)

    def test_terms_are_blade_bitmasks(self):
        mv = 3 * self.e0 + 4 * self.e1
        self.assertEqual(mv.terms, [(1, 3), (2, 4)])
        self.assertEqual(og.bits(5), [0, 2])
        self.assertEqual(og.grade(5), 2)
        self.assertEqual(self.E.zero().terms, [])

    def test_hodge_dual_and_undual_invert(self):
        for mv in (self.e0, self.e0 & self.e1, self.e0 + (self.e1 & self.e2)):
            self.assertEqual(mv.dual().undual(), mv)
        self.assertEqual(repr(self.e0.dual()), "-e1∧e2")
        self.assertEqual(self.E.pseudoscalar() ** 2, self.E.scalar(-1))

    def test_versors_reflections_and_rotors(self):
        e0, e1, e2 = self.e0, self.e1, self.e2
        x = 3 * e0 + 4 * e1
        self.assertEqual(e1.reflect(e0), e0)  # fixed
        self.assertEqual(e1.reflect(e1), -e1)  # negated
        rotor = e0 * e1
        self.assertEqual(repr(rotor.sandwich(x)), "-3⋅e0 - 4⋅e1")
        self.assertEqual(x.norm2(), 25)
        self.assertEqual(rotor.sandwich(x).norm2(), 25)
        self.assertEqual(rotor.spinor_norm(), 1)
        self.assertEqual(rotor.versor_grade_parity(), 0)
        self.assertEqual(e0.versor_grade_parity(), 1)
        info = rotor.classify_versor()
        self.assertEqual((info.spinor_norm, info.dickson), (1, 0))
        self.assertEqual(rotor * rotor.versor_inverse(), self.E.scalar(1))
        self.assertEqual(repr(rotor.versor_inverse()), "-e0∧e1")
        # The twisted adjoint of a vector is the reflection.
        self.assertEqual(repr(e1.twisted_sandwich(x)), "3⋅e0 - 4⋅e1")

    def test_division_requires_an_invertible_versor(self):
        e0, e1 = self.e0, self.e1
        self.assertEqual((3 * e0) / 3, e0)
        self.assertEqual((e0 * e1) / (e0 * e1), self.E.scalar(1))
        with self.assertRaises(ValueError):
            e0 / (self.E.scalar(1) + e0)  # zero divisor

    def test_general_inverse_covers_non_versors(self):
        x = self.E.scalar(1) + self.e0 + self.e1
        self.assertEqual(x * x.multivector_inverse(), self.E.scalar(1))
        self.assertEqual(repr((self.E.scalar(2) + self.e0).multivector_inverse()),
                         "2/3 + (-1/3)⋅e0")
        with self.assertRaises(ValueError):
            (self.E.scalar(1) + self.e0).multivector_inverse()
        with self.assertRaises(ValueError):
            self.E.zero().multivector_inverse()

    def test_power_operator(self):
        e0, e1 = self.e0, self.e1
        self.assertEqual((e0 + e1) ** 0, self.E.scalar(1))
        self.assertEqual((e0 + e1) ** 2, self.E.scalar(2))
        self.assertEqual((e0 + e1) ** 3, 2 * (e0 + e1))
        self.assertEqual((e0 * e1) ** 2, self.E.scalar(-1))

    def test_blades_subspaces_and_meet(self):
        e0, e1, e2 = self.e0, self.e1, self.e2
        blade = (e0 + e1) & e2
        self.assertTrue(blade.is_blade())
        self.assertFalse(((e0 & e1) + e2).is_blade())
        self.assertEqual(blade.blade_subspace(), [[1, 1, 0], [0, 0, 1]])
        self.assertEqual([repr(v) for v in blade.factor_blade()], ["e0 + e1", "e2"])
        self.assertEqual((e0 & e1).meet(e1 & e2), -e1)
        self.assertEqual(blade.terms, [(5, 1), (6, 1)])

    def test_cayley_transform_is_an_involutive_chart(self):
        B = self.e0 & self.e1
        rotor = B.cayley()
        self.assertEqual(rotor.norm2(), 1)
        self.assertEqual(rotor.cayley_inverse(), B)
        rational = og.RationalAlgebra(q=[1, 1, 1])
        Br = rational.gen(0) & rational.gen(1)
        self.assertEqual(Br.cayley().cayley_inverse(), Br)

    def test_exponentials_terminate_only_for_nilpotents(self):
        P = og.SurrealAlgebra.pga(2)  # Cl(2,0,1): e0 is the null direction
        B = P.gen(0) & P.gen(1)
        motor = B.exp_nilpotent()
        self.assertEqual(motor, P.scalar(1) + B)
        self.assertEqual(motor.sandwich(P.gen(1)), P.gen(1) + 2 * P.gen(0))
        with self.assertRaises(ValueError):
            (self.e0 * self.e1).exp_nilpotent()  # squares to -1: not nilpotent

    def test_exterior_hopf_structure(self):
        H = og.SurrealAlgebra(q=[0, 0])
        e0, e1 = H.gen(0), H.gen(1)
        self.assertEqual(e0.antipode(), -e0)
        self.assertEqual((e0 & e1).antipode(), e0 & e1)  # grade 2: (-1)^2
        self.assertEqual(repr(e0.coproduct()), "e0 + e2")  # primitive element
        T = H.tensor_square()
        self.assertEqual(e0.coproduct(), T.embed_first(e0) + T.embed_second(e0, H.dim))
        self.assertEqual(e0.counit(), 0)
        self.assertEqual(H.scalar(3).counit(), 3)
        self.assertEqual(repr(T.embed_second(e1, H.dim)), "e3")

    def test_grassmann_algebra_is_fully_null(self):
        G = og.SurrealAlgebra.grassmann(3)
        for i in range(3):
            self.assertTrue((G.gen(i) * G.gen(i)).is_zero())
        self.assertEqual(G.gen(0) & G.gen(1), G.gen(0) * G.gen(1))
        self.assertEqual(og.SurrealAlgebra(q=[0, 0, 0]).q(), G.q())

    def test_general_bilinear_form_deforms_the_product_not_the_polar(self):
        D = og.SurrealAlgebra(q=[1, 1], b=None, a={(0, 1): og.surreal(5)})
        d0, d1 = D.gen(0), D.gen(1)
        self.assertEqual(repr(d0 * d1), "5 + e0∧e1")
        self.assertEqual(d0 * d1 + d1 * d0, D.zero())
        self.assertEqual(repr((d0 * d1).reverse()), "-5 - e0∧e1")
        self.assertEqual((d0 * d1).reverse(), d1 * d0)
        self.assertEqual(len(D.spinor_rep().basis), 2)
        self.assertEqual(D.a_terms(), [(0, 1, 5)])

    def test_metric_introspection_and_map(self):
        E = self.E
        self.assertEqual((E.q_val(0), E.q_val(9)), (1, 0))
        self.assertFalse(E.has_upper())
        self.assertEqual(E.gram(), [[1, 0, 0], [0, 1, 0], [0, 0, 1]])
        mapped = og.SurrealAlgebra(q=[1, 1]).map(lambda x: -x)
        self.assertEqual(mapped.q(), [-1, -1])
        skew = og.RationalAlgebra([0, 0], b={(0, 1): og.Rational(2)})
        self.assertEqual(skew.gram(), [[0, 1], [1, 0]])
        self.assertEqual(skew.diagonalize().gram(), [[2, 0], [0, og.Rational(-1, 2)]])

    def test_pfister_and_pga_constructors(self):
        self.assertEqual(og.SurrealAlgebra.pfister([-1, -1]).q(), [1, 1, 1, 1])
        self.assertEqual(og.SurrealAlgebra.pfister1(-1).q(), [1, 1])
        self.assertEqual(og.SurrealAlgebra.pga(2).q(), [0, 1, 1])


class OperatorContractTests(OgdoadTestCase):
    """AGENTS.md: operator table, scalar dispatch, monomorphism."""

    def test_scalar_times_multivector_dispatches_to_the_multivector(self):
        N = og.Nimber
        A = og.NimberAlgebra(q=[2, 3])
        e0 = A.gen(0)
        self.assertEqual(N(2) * e0, e0 * N(2))
        self.assertEqual(2 * e0, e0 * 2)
        S = og.SurrealAlgebra(q=[1])
        self.assertEqual(og.omega() * S.gen(0), S.gen(0) * og.omega())
        self.assertEqual(3 * S.gen(0), S.scalar(3) * S.gen(0))
        # Python's reflected dispatch handed the work to the multivector.
        self.assertIsInstance(og.omega() * S.gen(0), type(S.gen(0)))

    def test_cross_world_multivectors_do_not_mix(self):
        S = og.SurrealAlgebra(q=[1])
        N = og.NimberAlgebra(q=[1])
        F = og.Fp3Algebra(q=[1])
        for x, y in ((S.gen(0), N.gen(0)), (N.gen(0), F.gen(0)), (F.gen(0), S.gen(0))):
            for op in (lambda p, q: p + q, lambda p, q: p * q, lambda p, q: p - q,
                       lambda p, q: p & q):
                with self.assertRaises(TypeError):
                    op(x, y)
            self.assertFalse(x == y)
            self.assertTrue(x != y)

    def test_cross_world_scalars_are_refused_by_multivectors(self):
        N = og.NimberAlgebra(q=[1])
        with self.assertRaises(TypeError):
            N.gen(0) * og.Fp3(1)
        with self.assertRaises(TypeError):
            og.Fp3(1) * N.gen(0)
        with self.assertRaises(TypeError):
            N.gen(0) * og.omega()

    def test_multivectors_of_distinct_algebras_in_one_world_refuse_to_mix(self):
        a = og.SurrealAlgebra(q=[1, 1]).gen(0)
        b = og.SurrealAlgebra(q=[2, 1]).gen(0)
        with self.assertRaises(ValueError):
            a + b
        with self.assertRaises(ValueError):
            a * b

    def test_scalar_embedding_is_explicit(self):
        S = og.SurrealAlgebra(q=[1])
        with self.assertRaises(TypeError):
            S.gen(0) + 1  # use S.scalar(1)
        self.assertEqual(repr(S.gen(0) + S.scalar(1)), "1 + e0")

    def test_negative_and_non_integer_powers_are_refused(self):
        S = og.SurrealAlgebra(q=[1])
        with self.assertRaises(TypeError):
            S.gen(0) ** -1
        with self.assertRaises(TypeError):
            2 ** S.gen(0)

    def test_equality_of_unrelated_objects_is_false_not_an_error(self):
        mv = og.SurrealAlgebra(q=[1]).gen(0)
        self.assertFalse(mv == None)  # noqa: E711
        self.assertFalse(mv == "e0")
        self.assertFalse(mv == og.omega())

    def test_canonical_reprs(self):
        S = og.SurrealAlgebra(q=[1, 1, 1])
        self.assertEqual(repr(S), "SurrealAlgebra(dim=3)")
        self.assertEqual(repr(S.zero()), "0")
        self.assertEqual(repr(S.scalar(1)), "1")
        self.assertEqual(repr(3 * S.gen(0) + 4 * S.gen(1)), "3⋅e0 + 4⋅e1")
        self.assertEqual(str(S.gen(2)), "e2")
        self.assertEqual(repr(og.NimberAlgebra(q=[1])), "NimberAlgebra(dim=1)")

    def test_algebra_objects_compare_by_metric(self):
        # Algebras compare by their metric, as their multivectors do: two
        # algebras built from the same metric are equal.
        S1 = og.SurrealAlgebra(q=[1, 1, 1])
        S2 = og.SurrealAlgebra(q=[1, 1, 1])
        self.assertEqual(S1, S2)
        self.assertEqual(S1.gen(0), S2.gen(0))  # already true

    def test_divided_power_vectors_use_a_display_repr(self):
        # Reprs delegate to the canonical Rust Display, never to Debug.
        D = og.RationalDividedPowerAlgebra(1)
        self.assertNotIn("DpVector {", repr(D.gen(0) * D.gen(0)))


class GuardedBoundaryTests(OgdoadTestCase):
    """Panics inside the engine's scalar boundary become ValueError."""

    def test_integer_overflow_in_a_product_is_a_value_error(self):
        A = og.IntegerAlgebra(q=[1])
        big = A.scalar(2**100) * A.gen(0)
        with self.assertRaises(ValueError) as ctx:
            with quiet_rust_panics():
                big * big * big
        self.assertIn("scalar boundary", str(ctx.exception))

    def test_rational_overflow_in_a_product_is_a_value_error(self):
        A = og.RationalAlgebra(q=[1])
        big = A.scalar(og.Rational(2**100)) * A.gen(0)
        with self.assertRaises(ValueError):
            with quiet_rust_panics():
                big * big * big

    def test_no_multivector_operation_leaks_a_native_panic(self):
        # Every operation below overflows i128 internally; the guard must turn
        # each into ValueError rather than pyo3_runtime.PanicException.
        big = 2 ** 100
        for name, world, make in (("Integer", og.IntegerAlgebra, lambda v: v),
                                  ("Rational", og.RationalAlgebra, og.Rational),
                                  ("Surreal", og.SurrealAlgebra, og.surreal)):
            A = world(q=[make(big), make(big), make(1)])
            e0, e1, e2 = A.gen(0), A.gen(1), A.gen(2)
            scale = A.scalar(make(big))
            x = scale * e0 + scale * e1 + e2
            y = scale * e1 + scale * e2 + scale
            operations = {
                "mul": lambda: x * y,
                "pow": lambda: x ** 3,
                "wedge product": lambda: (x & y) * (x & y),
                "sandwich": lambda: x.sandwich(y * y),
                "reflect": lambda: x.reflect(y * y),
                "twisted_sandwich": lambda: x.twisted_sandwich(y * y * y),
                "commutator": lambda: (x * x * x).commutator(y * y * y),
                "dual": lambda: (x * x * x).dual(),
                "meet": lambda: (x * x * x).meet(y * y * y),
                "norm2": lambda: (x * x * x).norm2(),
                "spinor_norm": lambda: (x * x * x).spinor_norm(),
                "multivector_inverse": lambda: (x * x * x).multivector_inverse(),
                "versor_inverse": lambda: (x * x * x).versor_inverse(),
                "cayley": lambda: (scale * (e0 & e1)).cayley(),
                "coproduct": lambda: (x * x * x).coproduct(),
                "antipode": lambda: (x * x * x).antipode(),
                "division": lambda: (x * x * x) / (e0 * scale),
            }
            for label, op in operations.items():
                with self.subTest(world=name, operation=label):
                    with self.assertRaises(ValueError):
                        with quiet_rust_panics():
                            op()

    def test_linear_map_operations_stay_behind_the_guard(self):
        big = 2 ** 100
        A = og.IntegerAlgebra(q=[1, 1])
        f = og.IntegerLinearMap.from_columns([[big, 0], [0, big]])
        for label, op in (("determinant", lambda: A.determinant(f)),
                          ("char_poly", lambda: A.char_poly(f)),
                          ("exterior_power_trace", lambda: A.exterior_power_trace(f, 2)),
                          ("apply_outermorphism", lambda: A.apply_outermorphism(f, A.gen(0) & A.gen(1))),
                          ("compose", lambda: f.compose(f))):
            with self.subTest(operation=label):
                with self.assertRaises(ValueError):
                    with quiet_rust_panics():
                        op()

    def test_divided_power_binomial_overflow_is_a_value_error(self):
        D = og.RationalDividedPowerAlgebra(1)
        left = D.divided_power(0, 2**100)
        with self.assertRaises(ValueError) as ctx:
            with quiet_rust_panics():
                left * left
        self.assertIn("binomial", str(ctx.exception))


class DividedPowerTests(OgdoadTestCase):
    def test_product_is_the_binomial_coefficient_in_characteristic_zero(self):
        D = og.RationalDividedPowerAlgebra(1)
        for i, j in itertools.product(range(6), repeat=2):
            product = D.divided_power(0, i) * D.divided_power(0, j)
            self.assertEqual(product.terms, [([i + j], og.Rational(math.comb(i + j, i)))])
        self.assertEqual(D.gen(0) * D.gen(0), D.scalar_mul(og.Rational(2), D.divided_power(0, 2)))

    def test_binomial_coefficients_reduce_modulo_p(self):
        D = og.Fp3DividedPowerAlgebra(1)
        for i, j in itertools.product(range(7), repeat=2):
            product = D.divided_power(0, i) * D.divided_power(0, j)
            c = math.comb(i + j, i) % 3
            expected = [] if c == 0 else [([i + j], og.Fp3(c))]
            self.assertEqual(product.terms, expected)

    def test_characteristic_two_kills_gamma_one_squared(self):
        D = og.F8DividedPowerAlgebra(1)
        self.assertTrue((D.gen(0) * D.gen(0)).is_zero())
        N = og.NimberDividedPowerAlgebra(1)
        self.assertTrue((N.gen(0) * N.gen(0)).is_zero())
        self.assertEqual((N.divided_power(0, 1) * N.divided_power(0, 2)).terms,
                         [([3], og.Nimber(1))])

    def test_commutative_and_associative_with_two_generators(self):
        D = og.RationalDividedPowerAlgebra(2)
        a = D.divided_power(0, 2) + D.gen(1)
        b = D.gen(0) * D.gen(1) + D.scalar(og.Rational(3))
        c = D.divided_power(1, 3)
        self.assertEqual(a * b, b * a)
        self.assertEqual((a * b) * c, a * (b * c))
        self.assertEqual(a * (b + c), a * b + a * c)
        self.assertEqual(D.dim, 2)

    def test_hopf_counit_and_cross_world_refusal(self):
        D = og.RationalDividedPowerAlgebra(1)
        self.assertEqual(D.one().counit(), 1)
        self.assertEqual(D.divided_power(0, 2).counit(), 0)
        with self.assertRaises(TypeError):
            D.gen(0) * og.F8DividedPowerAlgebra(1).gen(0)

    def test_generator_and_exponent_bounds(self):
        D = og.RationalDividedPowerAlgebra(1)
        with self.assertRaises(ValueError):
            D.gen(1)
        with self.assertRaises(OverflowError):
            D.divided_power(0, -1)


class LinearMapTests(OgdoadTestCase):
    def setUp(self):
        self.R = og.SurrealAlgebra(q=[1, 1])
        # columns are f(e_i): the row matrix is [[2, 1], [3, 4]].
        self.f = og.SurrealLinearMap.from_columns([[2, 3], [1, 4]])
        self.g = og.SurrealLinearMap.from_columns([[1, 1], [0, 1]])

    def test_determinant_trace_and_characteristic_polynomial(self):
        R, f = self.R, self.f
        self.assertEqual(R.determinant(f), 5)
        self.assertEqual(R.trace(f), 6)
        self.assertEqual(R.char_poly(f), [1, -6, 5])  # t^2 - 6t + 5
        self.assertEqual(R.exterior_power_trace(f, 0), 1)
        self.assertEqual(R.exterior_power_trace(f, 1), 6)
        self.assertEqual(R.exterior_power_trace(f, 2), 5)
        self.assertEqual(R.determinant(og.SurrealLinearMap.identity(2)), 1)

    def test_determinant_is_multiplicative(self):
        R = self.R
        fg = self.f.compose(self.g)
        self.assertEqual(R.determinant(fg), R.determinant(self.f) * R.determinant(self.g))

    def test_outermorphism_scales_the_pseudoscalar_by_the_determinant(self):
        R = self.R
        pseudo = R.gen(0) & R.gen(1)
        self.assertEqual(R.apply_outermorphism(self.f, pseudo), R.determinant(self.f) * pseudo)
        self.assertEqual(R.apply_outermorphism(self.f, R.scalar(3)), R.scalar(3))
        # f(a ^ b) = f(a) ^ f(b)
        a, b = R.gen(0), R.gen(0) + R.gen(1)
        self.assertEqual(R.apply_outermorphism(self.f, a & b),
                         R.apply_outermorphism(self.f, a) & R.apply_outermorphism(self.f, b))

    def test_inverse_outermorphism_and_singular_maps(self):
        R = self.R
        inverse = R.inverse_outermorphism(self.f)
        for i in range(2):
            there = R.apply_outermorphism(self.f, R.gen(i))
            self.assertEqual(R.apply_outermorphism(inverse, there), R.gen(i))
        singular = og.SurrealLinearMap.from_columns([[1, 2], [2, 4]])
        self.assertIsNone(R.inverse_outermorphism(singular))

    def test_columns_composition_and_image(self):
        R = self.R
        self.assertEqual(self.f.image(R, 0), 2 * R.gen(0) + 3 * R.gen(1))
        self.assertEqual(self.f.image(R, 1), R.gen(0) + 4 * R.gen(1))
        self.assertEqual(self.f.compose(og.SurrealLinearMap.identity(2)), self.f)
        self.assertEqual(self.f.n, 2)

    def test_dimension_mismatch_is_refused(self):
        big = og.SurrealLinearMap.from_columns([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
        with self.assertRaises(ValueError):
            self.R.determinant(big)

    def test_characteristic_two_determinant_is_the_permanent(self):
        N = og.NimberAlgebra(q=[1, 1])
        f = og.NimberLinearMap.from_columns([[2, 1], [3, 1]])
        # det over F_2^128 in char 2 is the permanent: 2*1 + 3*1 under nim arithmetic.
        expected = og.Nimber(2) * og.Nimber(1) + og.Nimber(1) * og.Nimber(3)
        self.assertEqual(N.determinant(f), expected)
        self.assertEqual(repr(N.determinant(f)), "*1")

    def test_frobenius_linear_maps(self):
        f8 = og.frobenius_linear_map(2, 3)
        self.assertEqual(og.galois_linear_map(2, 3, 1), f8)
        self.assertEqual(og.Fp2Algebra([0, 0, 0]).char_poly(f8),
                         [og.Fp2(c) for c in (1, 0, 0, 1)])  # t^3 + 1
        self.assertEqual(og.nimber_subfield_frobenius_linear_map(4).n, 4)

    def test_odd_characteristic_determinant(self):
        F = og.Fp3Algebra(q=[1, 1])
        f = og.Fp3LinearMap.from_columns([[2, 1], [1, 1]])
        self.assertEqual(F.determinant(f), og.Fp3(2 * 1 - 1 * 1))


class SpinorTests(OgdoadTestCase):
    def test_spinor_matrices_satisfy_the_clifford_relation(self):
        S = og.SurrealAlgebra(q=[1, 1, 1])  # Cl(3,0) = M_2(C)
        spin = S.spinor_rep()
        n = len(spin.basis)
        self.assertEqual(n, 4)  # 2 columns over C, real dimension 4
        M = spin.gen_matrices

        def matmul(a, b):
            return [[sum((a[i][k] * b[k][j] for k in range(n)), og.surreal(0))
                     for j in range(n)] for i in range(n)]

        identity = [[og.surreal(1 if i == j else 0) for j in range(n)] for i in range(n)]
        for i in range(3):
            self.assertEqual(matmul(M[i], M[i]), identity)
        for i, j in itertools.combinations(range(3), 2):
            ab, ba = matmul(M[i], M[j]), matmul(M[j], M[i])
            self.assertEqual(ab, [[-x for x in row] for row in ba])

    def test_characteristic_two_hyperbolic_plane_has_a_two_dimensional_ideal(self):
        H = og.NimberAlgebra(q=[0, 0], b={(0, 1): 1})
        self.assertEqual(len(H.spinor_rep().basis), 2)

    def test_degenerate_metrics_have_no_spinor_rep(self):
        with self.assertRaises(ValueError):
            og.SurrealAlgebra(q=[0, 0]).spinor_rep()

    def test_lazy_spinor_action_reaches_past_the_matrix_cap(self):
        Large = og.RationalAlgebra(q=[1] * 11)
        one = Large.scalar(1)
        e0 = Large.apply_generator(0, one)
        back = Large.apply_vector([1] + [0] * 10, e0)
        self.assertEqual(back, one)  # e0 e0 = q0 = 1
        self.assertEqual(Large.lazy_spinor_rep().apply_generator(0, one), e0)
        self.assertEqual(Large.apply_generator(0, one), e0)


class ConformalTests(OgdoadTestCase):
    def test_rational_cga_inner_product_is_minus_half_the_squared_distance(self):
        Q = og.RationalCga(2)
        pts = [[0, 0], [1, 0], [3, 4], [-2, 5]]
        for a, b in itertools.product(pts, repeat=2):
            d2 = (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2
            self.assertEqual(Q.inner(Q.up(a), Q.up(b)), og.Rational(-d2, 2))
        for p in pts:
            self.assertEqual(Q.inner(Q.up(p), Q.up(p)), 0)  # null vectors

    def test_sphere_contains_exactly_the_points_at_that_radius(self):
        Q = og.RationalCga(2)
        sphere = Q.sphere([0, 0], 1)  # radius squared
        self.assertEqual(Q.inner(Q.up([1, 0]), sphere), 0)
        self.assertEqual(Q.inner(Q.up([0, -1]), sphere), 0)
        self.assertNotEqual(Q.inner(Q.up([2, 0]), sphere), 0)

    def test_meet_spellings_agree(self):
        Q = og.RationalCga(2)
        p0, p1 = Q.up([0, 0]), Q.up([1, 0])
        self.assertEqual(Q.meet(p0, p1), Q.meet_ipns(p0, p1))
        self.assertEqual(Q.meet(p0, p1), Q.outer_join(p0, p1))

    def test_surreal_cga_with_infinite_and_infinitesimal_data(self):
        cga = og.SurrealCga(2)
        far = cga.up([og.omega(), 0])
        self.assertEqual(cga.inner(far, far), og.surreal(0))
        eps = og.epsilon()
        sphere = cga.sphere([0, 0], eps * eps)
        on, off = cga.up([eps, 0]), cga.up([2 * eps, 0])
        self.assertEqual(cga.inner(on, sphere), og.surreal(0))
        self.assertNotEqual(cga.inner(off, sphere), og.surreal(0))
        self.assertEqual(cga.alg().dim, 4)

    def test_adelic_backend_defers_scalar_multiplication_to_the_multivector(self):
        adelic = og.Adele.from_rational(2, 3)
        alg = og.AdeleAlgebra([adelic])
        self.assertEqual((adelic * alg.gen(0)).terms, (alg.gen(0) * adelic).terms)
        self.assertEqual((alg.gen(0) * alg.gen(0)).terms[0][1], adelic)
        cga = og.AdeleCga(1)
        pt = cga.up([adelic])
        self.assertTrue(cga.inner(pt, pt).is_zero())


if __name__ == "__main__":
    unittest.main()
