"""Catalog-wide laws: every monomorphised backend family (86 scalar worlds with
Algebra / MV / LinearMap / DividedPowerAlgebra / DpVector classes, plus the
conformal CGA backends) satisfies the same contract."""

import itertools
import re
import unittest

import ogdoad as og

from _support import OgdoadTestCase

PUBLIC = [n for n in dir(og) if not n.startswith("_")]
NAMES = set(PUBLIC)


def clifford_family_scalars():
    """Scalar class names ``X`` that come with a Clifford algebra ``XAlgebra``."""
    out = []
    for name in PUBLIC:
        if not name.endswith("Algebra") or name.endswith("DividedPowerAlgebra"):
            continue
        scalar = name[: -len("Algebra")]
        if scalar in NAMES and hasattr(getattr(og, scalar), "one"):
            out.append(scalar)
    return sorted(out)


SCALARS = clifford_family_scalars()


def cga_scalar(cga_name):
    base = cga_name[: -len("Cga")]
    if base in NAMES and hasattr(getattr(og, base), "one"):
        return base
    widened = re.sub(r"(Rational)(\d)", r"\1_\2", base)  # LaurentRational6 -> LaurentRational_6
    return widened if widened in NAMES else None


CGA_CLASSES = sorted(n for n in PUBLIC if n.endswith("Cga"))


class CatalogShapeTests(OgdoadTestCase):
    def test_family_size_and_completeness(self):
        self.assertEqual(len(SCALARS), 86)
        for scalar in SCALARS:
            for suffix in ("Algebra", "MV", "LinearMap", "DividedPowerAlgebra", "DpVector"):
                with self.subTest(scalar=scalar, suffix=suffix):
                    self.assertIn(scalar + suffix, NAMES)

    def test_every_public_class_reports_the_ogdoad_module(self):
        offenders = []
        for name in PUBLIC:
            obj = getattr(og, name)
            if isinstance(obj, type) and obj.__module__ != "ogdoad":
                offenders.append((name, obj.__module__))
        self.assertEqual(offenders, [])

    def test_cga_backends_all_resolve_to_a_scalar_world(self):
        self.assertEqual(len(CGA_CLASSES), 35)
        unresolved = [c for c in CGA_CLASSES if cga_scalar(c) is None]
        self.assertEqual(unresolved, [])


class CliffordCatalogTests(OgdoadTestCase):
    def test_every_backend_obeys_the_clifford_laws(self):
        for name in SCALARS:
            S = getattr(og, name)
            one = S.one()
            with self.subTest(world=name):
                A = getattr(og, name + "Algebra")(q=[one, one, one])
                e0, e1, e2 = A.gen(0), A.gen(1), A.gen(2)
                self.assertEqual((A.dim, repr(A)), (3, f"{name}Algebra(dim=3)"))
                self.assertIs(type(e0), getattr(og, name + "MV"))
                for g in (e0, e1, e2):
                    self.assertEqual(g * g, A.scalar(one))
                # Orthogonal generators anticommute -- or commute in characteristic two,
                # where the sign is invisible.
                if S.characteristic() == 2:
                    self.assertEqual(e0 * e1, e1 * e0)
                else:
                    self.assertTrue((e0 * e1 + e1 * e0).is_zero())
                self.assertEqual(e0 * e1, e0 & e1)
                self.assertTrue((e0 & e0).is_zero())
                u, v, w = e0 + e1, e1 + A.scalar(one), e2 + e0 * e1
                self.assertEqual((u * v) * w, u * (v * w))
                self.assertEqual(u * (v + w), u * v + u * w)
                self.assertEqual(A.scalar(one) * e0, e0)
                self.assertEqual(e0 - e0, A.zero())
                self.assertTrue(A.zero().is_zero())
                self.assertEqual((u * v).reverse(), v.reverse() * u.reverse())
                self.assertEqual((u * v).grade_involution(),
                                 u.grade_involution() * v.grade_involution())
                self.assertEqual(A.pseudoscalar(), e0 & e1 & e2)
                self.assertEqual(sorted(t[0] for t in (e0 + e1 + e2).terms), [1, 2, 4])

    def test_gram_data_round_trips_through_the_metric(self):
        for name in SCALARS:
            S = getattr(og, name)
            one = S.one()
            two = one + one
            with self.subTest(world=name):
                A = getattr(og, name + "Algebra")(q=[one, two], b={(0, 1): one})
                self.assertEqual(A.q(), [one, two])
                self.assertEqual(A.b_terms(), [(0, 1, one)])
                self.assertEqual(A.a_terms(), [])
                e0, e1 = A.gen(0), A.gen(1)
                self.assertEqual(e0 * e1 + e1 * e0, A.scalar(one))  # anticommutator = b
                self.assertEqual(e0 * e0, A.scalar(one))
                self.assertEqual(e1 * e1, A.scalar(two))

    def test_scalar_times_multivector_dispatches_to_the_multivector(self):
        # AGENTS.md: a scalar ``__mul__`` returns NotImplemented for a
        # multivector so Python reaches the multivector's ``__rmul__``.
        for name in SCALARS:
            S = getattr(og, name)
            one = S.one()
            A = getattr(og, name + "Algebra")(q=[one, one])
            e0 = A.gen(0)
            MV = getattr(og, name + "MV")
            with self.subTest(world=name):
                self.assertIs(type(one * e0), MV)
                self.assertEqual(one * e0, e0)
                self.assertEqual(e0 * one, e0)
                # Python integers coerce into the scalar world: 0 and 1 always
                # mean the ring elements.  (Nimbers read an int as the nimber of
                # that value, so ``2 * e0`` is only ``e0 + e0`` outside char 2.)
                self.assertEqual(1 * e0, e0)
                self.assertEqual(e0 * 1, e0)
                self.assertTrue((0 * e0).is_zero())
                if S.characteristic() != 2:
                    self.assertEqual(2 * e0, e0 + e0)
                    self.assertEqual(e0 * 2, e0 + e0)
                self.assertEqual(e0 / one, e0)
                with self.assertRaises(TypeError):
                    e0 + one  # scalars embed explicitly through ``A.scalar``
                with self.assertRaises(TypeError):
                    one - e0

    def test_multivectors_accept_exactly_the_scalars_that_widen_into_their_world(self):
        # MV(S) * T-scalar works iff the scalar product S * T already lands in S.
        families = {}
        for name in SCALARS:
            S = getattr(og, name)
            A = getattr(og, name + "Algebra")(q=[S.one(), S.one()])
            families[name] = (S, A.gen(0))
        for a, b in itertools.permutations(families, 2):
            S, x = families[a]
            T = getattr(og, b)
            try:
                lands_in_S = type(S.one() * T.one()) is type(S.one())
            except TypeError:
                lands_in_S = False
            try:
                x * T.one()
                accepted = True
            except TypeError:
                accepted = False
            self.assertEqual(accepted, lands_in_S, (a, b))

    def test_distinct_worlds_never_mix_at_the_multivector_layer(self):
        gens = {}
        for name in SCALARS:
            S = getattr(og, name)
            A = getattr(og, name + "Algebra")(q=[S.one(), S.one()])
            gens[name] = A.gen(0)
        for a, b in itertools.permutations(gens, 2):
            x, y = gens[a], gens[b]
            self.assertFalse(x == y, (a, b))
            self.assertTrue(x != y, (a, b))
            for op in (lambda p, q: p + q, lambda p, q: p * q, lambda p, q: p & q):
                with self.assertRaises(TypeError, msg=(a, b)):
                    op(x, y)


class DividedPowerCatalogTests(OgdoadTestCase):
    def test_every_backend_obeys_the_binomial_product_rule(self):
        for name in SCALARS:
            S = getattr(og, name)
            one = S.one()
            two, three = one + one, one + one + one
            with self.subTest(world=name):
                D = getattr(og, name + "DividedPowerAlgebra")(1)
                g = D.gen(0)
                self.assertIs(type(g), getattr(og, name + "DpVector"))
                self.assertEqual(g * g, D.scalar_mul(two, D.divided_power(0, 2)))
                self.assertEqual(D.divided_power(0, 1) * D.divided_power(0, 2),
                                 D.scalar_mul(three, D.divided_power(0, 3)))
                self.assertEqual(D.one() * g, g)
                self.assertEqual(g * D.one(), g)
                self.assertEqual(D.one().counit(), one)
                self.assertTrue(g.counit() == S.zero())

    def test_scalars_act_on_dp_vectors_from_the_left(self):
        for name in SCALARS:
            S = getattr(og, name)
            one = S.one()
            D = getattr(og, name + "DividedPowerAlgebra")(1)
            g = D.gen(0)
            with self.subTest(world=name):
                self.assertEqual(one * g, g)
                self.assertEqual((one + one) * g, g + g)
                self.assertEqual(1 * g, g)
                self.assertTrue((0 * g).is_zero())
                if S.characteristic() != 2:
                    self.assertEqual(2 * g, g + g)

    def test_scalars_act_on_dp_vectors_from_the_right(self):
        # The scalar ring is commutative, so a scalar acts on a divided-power
        # vector from either side.
        offenders = []
        for name in SCALARS:
            S = getattr(og, name)
            one = S.one()
            g = getattr(og, name + "DividedPowerAlgebra")(1).gen(0)
            try:
                if g * one != g:
                    offenders.append(name)
            except TypeError:
                offenders.append(name)
        self.assertEqual(offenders, [])

    def test_scale_is_the_method_spelling_of_the_scalar_action(self):
        for name in SCALARS:
            S = getattr(og, name)
            one = S.one()
            g = getattr(og, name + "DividedPowerAlgebra")(1).gen(0)
            with self.subTest(world=name):
                self.assertEqual(g.scale(one + one), (one + one) * g)

    def test_dp_vectors_of_distinct_worlds_do_not_mix(self):
        names = ["Rational", "Fp5", "Nimber", "Surreal", "F8"]
        gens = {n: getattr(og, n + "DividedPowerAlgebra")(1).gen(0) for n in names}
        for a, b in itertools.permutations(names, 2):
            with self.assertRaises(TypeError):
                gens[a] * gens[b]
            self.assertFalse(gens[a] == gens[b])


class LinearMapCatalogTests(OgdoadTestCase):
    def test_every_backend_computes_determinant_and_trace(self):
        for name in SCALARS:
            S = getattr(og, name)
            one, zero = S.one(), S.zero()
            two = one + one
            with self.subTest(world=name):
                A = getattr(og, name + "Algebra")(q=[one, one])
                L = getattr(og, name + "LinearMap")
                ident = L.identity(2)
                diag = L.from_columns([[one, zero], [zero, two]])
                self.assertEqual(A.determinant(ident), one)
                self.assertEqual(A.determinant(diag), two)
                self.assertEqual(A.trace(diag), one + two)
                self.assertEqual(A.determinant(diag.compose(diag)), two * two)
                self.assertEqual(A.apply_outermorphism(diag, A.gen(1)), A.gen(1) * two)
                self.assertEqual(diag.n, 2)


class CgaCatalogTests(OgdoadTestCase):
    def test_every_cga_backend_embeds_points_as_null_vectors(self):
        for cga_name in CGA_CLASSES:
            scalar = cga_scalar(cga_name)
            S = getattr(og, scalar)
            one, zero = S.one(), S.zero()
            half = (one + one).inv()
            with self.subTest(cga=cga_name):
                C = getattr(og, cga_name)(2)
                origin, east = C.up([zero, zero]), C.up([one, zero])
                self.assertTrue(C.inner(origin, origin).is_zero())
                self.assertTrue(C.inner(east, east).is_zero())
                # <up(a), up(b)> = -|a-b|^2 / 2
                self.assertEqual(C.inner(origin, east), -half)
                self.assertEqual(C.alg().dim, 4)


if __name__ == "__main__":
    unittest.main()
