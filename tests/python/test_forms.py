"""Quadratic-form classification, Witt/Brauer--Wall invariants, local--global
principles and integral lattices through the Python bindings."""

import unittest
from fractions import Fraction

import ogdoad as og

from _support import OgdoadTestCase


def rational_to_fraction(r):
    return Fraction(r.numer(), r.denom())


# ---------------------------------------------------------------------------
# Characteristic two: the Arf invariant
# ---------------------------------------------------------------------------


class ArfInvariantTests(OgdoadTestCase):
    def nimber_form(self, qs, bs):
        return og.NimberAlgebra(q=[og.Nimber(v) for v in qs], b={k: 1 for k in bs})

    def test_hyperbolic_and_anisotropic_planes(self):
        hyperbolic = og.arf_nimber(self.nimber_form([0, 0], [(0, 1)]))
        aniso = og.arf_nimber(self.nimber_form([1, 1], [(0, 1)]))
        self.assertEqual((hyperbolic.arf, hyperbolic.o_type), (0, "O+"))
        self.assertEqual((aniso.arf, aniso.o_type), (1, "O-"))
        self.assertEqual(
            repr(hyperbolic),
            "ArfInvariants(arf=0, O+, rank=2, radical_dim=0, radical_anisotropic=false)")
        self.assertEqual(
            repr(aniso),
            "ArfInvariants(arf=1, O-, rank=2, radical_dim=0, radical_anisotropic=false)")
        self.assertEqual((aniso.rank, aniso.radical_dim, aniso.radical_anisotropic), (2, 0, False))

    def test_arf_is_additive_over_orthogonal_sums(self):
        # A + A = H + H, so the Arf invariant of A (+) A is 0 while A (+) H is 1.
        aa = og.arf_nimber(self.nimber_form([1, 1, 1, 1], [(0, 1), (2, 3)]))
        ah = og.arf_nimber(self.nimber_form([1, 1, 0, 0], [(0, 1), (2, 3)]))
        aaa = og.arf_nimber(self.nimber_form([1] * 6, [(0, 1), (2, 3), (4, 5)]))
        self.assertEqual((aa.arf, aa.o_type), (0, "O+"))
        self.assertEqual(ah.arf, 1)
        self.assertEqual(aaa.arf, 1)

    def test_raw_f2_bitmask_entry_point_agrees(self):
        self.assertEqual(og.arf_f2(2, [True, True], [2, 1]).arf, 1)
        self.assertEqual(og.arf_f2(2, [False, False], [2, 1]).arf, 0)

    def test_the_artin_schreier_trace_decides_arf(self):
        # Q = x^2 + x y + c y^2 has Arf class Tr_{K/F_2}(c), where K is the
        # smallest nim-subfield containing the coefficients (F_2 for c < 2,
        # F_4 for c < 4); the Witt class reports that field degree.
        for c, degree in ((0, 1), (1, 1), (2, 2), (3, 2)):
            form = og.NimberAlgebra(q=[1, c], b={(0, 1): 1})
            self.assertEqual(og.arf_nimber(form).arf, og.nim_trace(c, degree), c)
            self.assertEqual(og.witt_class(form).field_degree, degree, c)
        self.assertEqual([og.arf_nimber(og.NimberAlgebra(q=[1, c], b={(0, 1): 1})).arf
                          for c in range(4)], [0, 1, 1, 1])

    def test_degenerate_forms_report_their_radical(self):
        rad = og.arf_nimber(og.NimberAlgebra(q=[1, 0, 0], b={(1, 2): 1}))
        self.assertEqual((rad.rank, rad.radical_dim, rad.radical_anisotropic), (2, 1, True))
        self.assertEqual(rad.arf, 0)

    def test_witt_group_is_z_mod_2(self):
        A = self.nimber_form([1, 1], [(0, 1)])
        H = self.nimber_form([0, 0], [(0, 1)])
        wA, wH = og.witt_class(A), og.witt_class(H)
        zero = og.WittClass.zero()
        self.assertEqual(wA + wA, zero)
        self.assertEqual(wA + zero, wA)
        self.assertEqual(wH, zero)
        self.assertEqual(-wA, wA)
        self.assertNotEqual(wA, zero)
        self.assertEqual(wA.arf, 1)
        self.assertTrue((wA + wA).is_hyperbolic)
        self.assertEqual(og.WittClass.try_from_metric(A), wA)
        self.assertEqual(
            repr(wA), "[anisotropic plane] (Arf 1 over F_2^1)")
        self.assertEqual(
            repr(wA + wA), "0 (hyperbolic class over F_2^1)")

    def test_isometry_classification_by_arf(self):
        H = self.nimber_form([0, 0], [(0, 1)])
        A = self.nimber_form([1, 1], [(0, 1)])
        self.assertTrue(og.isometric_nimber(H, H))
        self.assertFalse(og.isometric_nimber(H, A))

    def test_dickson_invariant_counts_reflections(self):
        self.assertEqual(og.dickson_matrix([[0, 1], [1, 0]]), 1)  # a transvection-like swap
        self.assertEqual(og.dickson_matrix([[2, 0], [0, 3]]), 0)  # lies in SO

    def test_symmetry_factorisation_is_certified(self):
        fact = og.factor_char2_isometry([0, 0], {(0, 1): 1}, [[0, 1], [1, 0]])
        self.assertEqual(fact.factors, [[1, 1]])
        self.assertTrue(fact.clifford_verified)
        self.assertEqual(og.char2_spinor_norm([0, 0], {(0, 1): 1}, [[0, 1], [1, 0]]), 1)
        with self.assertRaises(ValueError):
            # does not preserve x0*x1
            og.factor_char2_isometry([0, 0], {(0, 1): 1}, [[1, 1], [0, 1]])

    def test_gold_and_trace_forms(self):
        gold = og.gold_form_arf(8, 1)
        self.assertEqual((gold.rank, gold.radical_dim, gold.arf), (6, 2, 1))
        self.assertEqual(og.arf_nimber(og.gold_form(4, 1)).arf, 1)
        self.assertEqual(og.trace_form_arf(3).arf, 1)

    def test_quadric_fitting(self):
        fit = og.fit_f2_quadratic([0, 1, 2], 2)  # the zero set of x0*x1
        self.assertTrue(fit.is_genuinely_quadratic())
        self.assertEqual(
            repr(fit),
            "QuadricFit(quadratic=true, constant=false, rank=2, arf=0, radical_dim=0, bias=0)")

    def test_brown_invariant_of_doubled_form(self):
        self.assertEqual(og.brown_f2(1, [1], [0]).beta, 1)
        self.assertEqual(og.double_f2([True, True], [2, 1]).beta, 4)


# ---------------------------------------------------------------------------
# Characteristic zero: signature classification
# ---------------------------------------------------------------------------


class RealClassificationTests(OgdoadTestCase):
    def classify(self, qs):
        return og.classify_surreal(og.SurrealAlgebra(q=qs))

    def test_bott_periodicity_table_from_the_demo(self):
        table = {
            (0, 2): "H",
            (3, 0): "M_2(C)",
            (1, 3): "M_2(H)",
            (3, 1): "M_4(R)",
            (4, 1): "M_4(C)",
        }
        for (p, q), expected in table.items():
            with self.subTest(p=p, q=q):
                self.assertEqual(str(self.classify([1] * p + [-1] * q)), expected)
                self.assertEqual(str(og.classify_real(p, q)), expected)

    def test_minkowski_signature_order_matters(self):
        # Cl(1,3) and Cl(3,1) are different algebras.
        self.assertNotEqual(str(og.classify_real(1, 3)), str(og.classify_real(3, 1)))

    def test_classify_real_follows_the_period_eight_clock(self):
        names = [str(og.classify_real(0, n)) for n in range(0, 9)]
        self.assertEqual(names, ["R", "C", "H", "H ⊕ H", "M_2(H)",
                                 "M_4(C)", "M_8(R)", "M_8(R) ⊕ M_8(R)", "M_16(R)"])
        # Cl(0, n + 8) = M_16(Cl(0, n)).

    def test_small_cases(self):
        self.assertEqual(str(self.classify([1])), "R ⊕ R")
        self.assertEqual(str(self.classify([-1])), "C")
        self.assertEqual(str(self.classify([1, 1])), "M_2(R)")
        self.assertEqual(str(self.classify([1, -1])), "M_2(R)")
        self.assertEqual(str(self.classify([])), "R")
        self.assertEqual(str(self.classify([-1, -1, -1])), "H ⊕ H")

    def test_degenerate_metric_reports_its_exterior_factor(self):
        self.assertEqual(str(self.classify([0])), "R ⊗̂ Λ(R^1)")
        info = self.classify([1, -1, 0])
        self.assertEqual(info.radical_dim, 1)

    def test_nondiagonal_metric_is_diagonalised_first(self):
        skew = og.SurrealAlgebra(q=[0, 0], b={(0, 1): 1})
        self.assertEqual(str(og.classify_surreal(skew)), "M_2(R)")  # hyperbolic <1,-1>
        self.assertTrue(og.isometric_real(skew, og.SurrealAlgebra(q=[1, -1])))
        self.assertFalse(og.isometric_real(og.SurrealAlgebra(q=[1, 1]), og.SurrealAlgebra(q=[1, -1])))

    def test_complex_classification(self):
        names = [str(og.classify_complex(n)) for n in range(0, 6)]
        self.assertEqual(names, ["C", "C ⊕ C", "M_2(C)", "M_2(C) ⊕ M_2(C)",
                                 "M_4(C)", "M_4(C) ⊕ M_4(C)"])
        c2 = og.classify_surcomplex(
            og.SurcomplexAlgebra([og.Surcomplex(1), og.Surcomplex(1)]))
        self.assertEqual(str(c2), "M_2(C)")

    def test_signature_and_witt_decomposition(self):
        self.assertEqual(og.surreal_signature(og.SurrealAlgebra(q=[1, -1, 0])), (1, 1, 1))
        dec = og.witt_decompose_real(og.SurrealAlgebra(q=[1, 1, 1, -1, -1]))
        self.assertEqual((dec.witt_index, dec.anisotropic_pos, dec.anisotropic_neg, dec.radical_dim),
                         (2, 1, 0, 0))
        self.assertEqual(
            og.surcomplex_rank(og.SurcomplexAlgebra(q=[og.Surcomplex(1, 0), og.Surcomplex(0, 0)])),
            (1, 1))

    def test_pfister_forms_lie_in_the_fundamental_ideal(self):
        pf = og.SurrealAlgebra.pfister([-1, -1])
        self.assertTrue(pf.in_fundamental_ideal())
        self.assertEqual(pf.dim, 4)
        self.assertEqual(str(og.classify_surreal(pf)), "M_2(H)")

    def test_even_subalgebra_and_graded_tensor_product(self):
        cl30 = og.SurrealAlgebra(q=[1, 1, 1])
        self.assertEqual(str(og.classify_surreal(cl30.even_subalgebra())), "H")  # Cl(3,0)^0 = Cl(0,2)
        tens = og.SurrealAlgebra(q=[1]).graded_tensor(og.SurrealAlgebra(q=[-1]))
        self.assertEqual(str(og.classify_surreal(tens)), "M_2(R)")  # Cl(1,0) ^ Cl(0,1) = Cl(1,1)

    def test_e_staircase_over_the_reals(self):
        self.assertEqual([og.e_real(4, n) for n in range(4)], [0, 0, 1, None])

    def test_springer_decomposition_by_valuation(self):
        sp = og.springer_decompose(og.SurrealAlgebra(q=[og.omega(), og.epsilon(), 1, -1]))
        self.assertEqual([(g.valuation, g.signature) for g in sp.graded],
                         [(1, (1, 0)), (0, (1, 1)), (-1, (1, 0))])
        self.assertEqual(sp.radical_dim, 0)
        self.assertEqual(sp.total_signature, (3, 1))

    def test_hermitian_forms(self):
        i = og.Surcomplex(0, 1)
        H = og.HermitianForm.from_gram([[og.Surcomplex(2, 0), i], [-i, og.Surcomplex(2, 0)]])
        self.assertEqual(repr(H.signature()), "HermitianSignature(pos=2, neg=0, radical=0)")
        self.assertEqual(H.diagonalize(), [2, og.Surreal.from_rational(3, 2)])
        diag = og.HermitianForm.diagonal([1, -1, 0])
        self.assertEqual((diag.signature().pos, diag.signature().neg, diag.signature().radical),
                         (1, 1, 1))
        # Restriction of scalars doubles the dimension and the signature.
        restricted = diag.restrict_scalars()
        self.assertEqual(restricted.dim, 6)
        self.assertEqual(og.surreal_signature(restricted), (2, 2, 2))
        with self.assertRaises(ValueError):
            og.HermitianForm.from_gram([[og.Surcomplex(0, 1)]])  # not Hermitian

    def test_symplectic_forms_are_classified_by_rank_alone(self):
        self.assertEqual(
            repr(og.SymplecticForm.hyperbolic(2).classify()),
            "SymplecticInvariants(rank=4, radical_dim=0, planes=2)")
        self.assertEqual(og.SymplecticForm.from_gram([[0, 1], [-1, 0]]).classify().planes(), 1)
        self.assertEqual(og.classify_symplectic_nimber([[0, 1], [1, 0]]).planes(), 1)
        with self.assertRaises(ValueError):
            og.SymplecticForm.from_gram([[0, 1], [1, 0]])  # not alternating in char 0
        with self.assertRaises(ValueError):
            og.classify_symplectic_nimber([[1, 1], [1, 0]])


class RationalClassificationTests(OgdoadTestCase):
    def test_isometry_over_q(self):
        R = og.RationalAlgebra
        self.assertTrue(og.isometric_rational(R(q=[1, -1]), R(q=[-1, 1])))
        self.assertTrue(og.isometric_rational(R(q=[1, 1]), R(q=[2, 2])))
        self.assertFalse(og.isometric_rational(R(q=[1, 1]), R(q=[1, 2])))

    def test_invariants_of_a_binary_form(self):
        rq = og.classify_rational(og.RationalAlgebra([og.Rational(1), og.Rational(-3)]))
        self.assertEqual(
            str(rq),
            "Q: dim 2 disc -3 sig (1,1) hasse [R:+1, Q_2:+1, Q_3:+1]; over R: M_2(R)")
        self.assertEqual(len(rq.local_hasse), 3)

    def test_a2_lattice_metric_ramifies_at_two_and_three(self):
        info = og.classify_rational(og.a_n(2).clifford_metric())
        self.assertEqual(
            str(info),
            "Q: dim 2 disc 3 sig (2,0) hasse [R:+1, Q_2:-1, Q_3:-1]; over R: M_2(R)")

    def test_brauer_wall_group_of_q(self):
        rq = og.bw_class_rational(og.RationalAlgebra(q=[-1]))
        self.assertEqual(rq.real_class(), og.BrauerWallClass.real(1))
        self.assertEqual(
            str(rq + rq),
            "BW(Q): parity 0 signed_disc -1 c(q) ramified {Real, Prime(2)}")


# ---------------------------------------------------------------------------
# Brauer--Wall classes
# ---------------------------------------------------------------------------


class BrauerWallTests(OgdoadTestCase):
    def test_bott_clock_over_the_reals(self):
        g = og.bw_class_real(og.SurrealAlgebra(q=[-1]))
        cur = g
        for n in range(1, 17):
            self.assertEqual(cur, og.BrauerWallClass.real(n % 8), n)
            cur = cur + g
        plus = og.bw_class_real(og.SurrealAlgebra(q=[1]))
        self.assertEqual(g + plus, og.BrauerWallClass.real(0))
        self.assertEqual(plus, og.BrauerWallClass.real(7))
        self.assertEqual(repr(og.BrauerWallClass.real(9)), "BrauerWallClass::Real(1)")

    def test_char2_classes_are_arf_classes(self):
        a = og.bw_class_nimber(og.NimberAlgebra(q=[1, 1], b={(0, 1): 1}))
        self.assertEqual(a, og.BrauerWallClass.char2(1))
        self.assertEqual(a + a, og.BrauerWallClass.char2(1) + og.BrauerWallClass.char2(1))
        self.assertEqual(repr(a), "BrauerWallClass::Char2(field_degree=1, arf=1)")
        self.assertEqual(a + a, a.zero_like())

    def test_classes_over_different_fields_do_not_add(self):
        with self.assertRaises(ValueError):
            og.BrauerWallClass.real(1) + og.BrauerWallClass.char2(1)

    def test_finite_field_class(self):
        cls = og.OddFiniteFieldForm(3, [1]).bw_class()
        self.assertEqual(repr(cls), "BrauerWallClass::OddChar(field_order=3, kappa=1, e0=1, sclass=0)")
        self.assertEqual(
            repr(og.bw_class_finite_algebra(og.Fp3Algebra([1, 2]))),
            "BrauerWallClass::OddChar(field_order=3, kappa=1, e0=0, sclass=0)")


# ---------------------------------------------------------------------------
# Finite fields of odd characteristic
# ---------------------------------------------------------------------------


class OddFiniteFieldFormTests(OgdoadTestCase):
    O = og.OddFiniteFieldForm

    def test_dimension_discriminant_hasse_trichotomy(self):
        O = self.O
        cases = [
            (3, [1, 1], 1, "F_3: dim 2 disc □ hasse +1"),
            (3, [1, 2], 2, "F_3: dim 2 disc ✶ hasse +1"),
            (5, [1, 2, 3], 1, "F_5: dim 3 disc □ hasse +1"),
            (7, [1, 3], 3, "F_7: dim 2 disc ✶ hasse +1"),
        ]
        for p, diag, disc, text in cases:
            with self.subTest(p=p, diag=diag):
                form = O(p, diag)
                self.assertEqual(form.discriminant(), disc)
                self.assertEqual(form.hasse_invariant(), 1)  # always +1 over a finite field
                self.assertEqual(form.classify().display(), text)

    def test_isometry_is_dimension_and_discriminant(self):
        O = self.O
        self.assertTrue(O(5, [1, 1]).isometric_to(O(5, [2, 3])))
        self.assertFalse(O(5, [1, 1]).isometric_to(O(5, [1, 2])))
        with self.assertRaises(ValueError):
            O(5, [1, 1]).isometric_to(O(3, [1, 1]))  # different finite fields

    def test_witt_group_of_f3_is_z_mod_4(self):
        O = self.O
        g, zero = O(3, [1]).witt_class(), O(3, []).witt_class()
        self.assertEqual([sum([g] * k, zero) == zero for k in (1, 2, 3, 4)],
                         [False, False, False, True])
        self.assertEqual(g + g, O(3, [1, 1]).witt_class())

    def test_witt_group_of_f5_is_klein_four(self):
        O = self.O
        g, h, zero = O(5, [1]).witt_class(), O(5, [2]).witt_class(), O(5, []).witt_class()
        self.assertEqual(g + g, zero)
        self.assertEqual(h + h, zero)
        self.assertNotEqual(g, h)
        self.assertNotEqual(g + h, zero)

    def test_witt_classes_of_different_fields_do_not_add(self):
        with self.assertRaises(ValueError):
            self.O(3, [1]).witt_class() + self.O(5, [1]).witt_class()

    def test_hyperbolic_plane_over_f5_and_anisotropic_plane_over_f3(self):
        h5 = self.O(5, [1, 1]).witt_decompose()
        self.assertEqual((h5.witt_index, h5.anisotropic_dim), (1, 0))
        a3 = self.O(3, [1, 1]).witt_decompose()
        self.assertEqual((a3.witt_index, a3.anisotropic_dim), (0, 2))

    def test_unsupported_fields_are_refused(self):
        for p in (2, 4, 6):
            with self.assertRaises(ValueError):
                self.O(p, [1])

    def test_extension_field_f9(self):
        f9 = self.O(3, [1, 1], degree=2)
        self.assertEqual(f9.field_order, 9)
        self.assertEqual(f9.classify().display(), "F_9: dim 2 disc □ hasse +1")
        self.assertTrue(f9.isometric_to(f9))

    def test_staircase_stabilises_at_the_second_step(self):
        stair = self.O(5, [1, 2, 3]).e_staircase()
        self.assertEqual((stair.e0, stair.e1, stair.e2, stair.stabilizes_at), (1, 0, 1, 2))

    def test_numeric_field_invariants(self):
        inv = og.finite_field_numeric_invariants(3, 2)
        self.assertEqual((inv.field_order, inv.level, inv.pythagoras_number, inv.u_invariant),
                         (9, 1, 2, 2))
        self.assertEqual((og.level(5, 1), og.level(3, 1)), (1, 2))
        self.assertTrue(og.is_sum_of_n_squares(3, 2, 2))
        self.assertFalse(og.is_sum_of_n_squares(3, 2, 1))

    def test_transfer_and_trace_forms_land_in_the_base_field(self):
        transfer = og.transfer_diagonal(3, 2, [1])  # Scharlau transfer F_9/F_3 <1>
        self.assertEqual(transfer.dim, 2)
        self.assertEqual(og.classify_finite_algebra(transfer).display(),
                         "F_3: dim 2 disc ✶ hasse +1")


class Char2FiniteFieldFormTests(OgdoadTestCase):
    def test_arf_and_isometry_over_f2_and_f8(self):
        C = og.Char2FiniteFieldForm
        f2a = C([1, 1], {(0, 1): 1})
        self.assertEqual(f2a.classify().arf, 1)
        self.assertEqual(f2a.classify_unified().kind, "char2")
        h = C([0, 0], {(0, 1): 3}, degree=3)
        self.assertEqual(h.classify().arf, 0)
        self.assertTrue(h.isometric_to(C([0, 0], {(0, 1): 1}, degree=3)))
        self.assertFalse(h.isometric_to(C([1, 1], {(0, 1): 1}, degree=3)))


# ---------------------------------------------------------------------------
# Hilbert symbols and the local--global principle
# ---------------------------------------------------------------------------


class LocalGlobalTests(OgdoadTestCase):
    def test_hilbert_symbol_values(self):
        self.assertEqual(og.hilbert_symbol_qp(-1, -1, 2), -1)  # Hamilton's quaternions
        self.assertEqual(og.hilbert_symbol_at(-1, -1), -1)  # ... and at infinity
        self.assertEqual(og.hilbert_symbol_qp(2, 3, 5), 1)
        self.assertEqual(og.hilbert_symbol(5, 2, 3), 1)  # finite-field symbol

    def test_hilbert_reciprocity(self):
        pairs = [(-1, -1), (2, 3), (-3, 5), (6, -10), (7, 7), (11, -2), (30, 77)]
        for a, b in pairs:
            with self.subTest(a=a, b=b):
                self.assertEqual(og.hilbert_product((a, 1), (b, 1)), 1)
                # The local invariants of the quaternion algebra sum to an
                # integer (0 in Q/Z).
                total = rational_to_fraction(og.brauer_invariant_sum((a, 1), (b, 1)))
                self.assertEqual(total.denominator, 1)

    def test_quaternion_algebra_invariants(self):
        invs = og.brauer_local_invariants((-1, 1), (-1, 1))
        self.assertEqual([(repr(place), repr(inv)) for place, inv in invs],
                         [("RationalPlace.Real", "1/2"), ("RationalPlace.Prime(2)", "1/2")])
        quat = og.Brauer2Class.quaternion(-1, -1)
        self.assertEqual([repr(p) for p in quat.ramified_places()],
                         ["RationalPlace.Real", "RationalPlace.Prime(2)"])
        full = og.BrauerClass.from_two_torsion(quat)
        self.assertEqual(full.invariant_sum(), 0)
        self.assertEqual([repr(p) for p, _ in full.local()],
                         ["RationalPlace.Real", "RationalPlace.Prime(2)"])

    def test_checked_boundaries_refuse_non_primes_and_zero(self):
        with self.assertRaises(ValueError):
            og.hilbert_symbol_qp(2, 3, 9)
        with self.assertRaises(ValueError):
            og.hilbert_symbol_qp(0, 3, 5)
        with self.assertRaises(ValueError):
            og.is_square_qp(2, 9)
        with self.assertRaises(ValueError):
            og.is_isotropic_at_p([1, 1, 1], 9)

    def test_hasse_minkowski_agrees_with_every_place(self):
        forms = [[1, 1, 1], [1, 1, -1], [1, 1, -3], [1, 1, 1, 1, -1], [2, 3, -5], [1, 2, 3, 4, 5]]
        expected = {(1, 1, 1): False, (1, 1, -1): True, (1, 1, -3): False,
                    (1, 1, 1, 1, -1): True}
        for form in forms:
            with self.subTest(form=form):
                adelic = og.isotropy_over_adeles(form)
                self.assertEqual(og.is_isotropic_q(form), adelic.is_global())
                if tuple(form) in expected:
                    self.assertEqual(og.is_isotropic_q(form), expected[tuple(form)])

    def test_ternary_form_x2_y2_minus_3z2_fails_only_at_two_and_three(self):
        local = {p: og.is_isotropic_at_p([1, 1, -3], p) for p in (2, 3, 5, 7)}
        self.assertEqual(local, {2: False, 3: False, 5: True, 7: True})
        self.assertFalse(og.is_isotropic_q([1, 1, -3]))

    def test_small_rank_isotropy(self):
        self.assertTrue(og.is_isotropic_q([1, -1]))
        self.assertFalse(og.is_isotropic_q([1, 1]))
        self.assertFalse(og.is_isotropic_q([]))
        self.assertTrue(og.is_isotropic_q([0]))
        with self.assertRaises(ValueError):
            og.isotropy_over_adeles([1, 1])  # the adelic report needs rank >= 3

    def test_p_adic_springer_decomposition(self):
        sp = og.springer_decompose_qp(5, [(1, 1), (5, 1)])
        self.assertEqual([(g.valuation, g.dim, g.disc_is_square) for g in sp.graded],
                         [(1, 1, True), (0, 1, True)])
        sp2 = og.springer_decompose_qp(5, [(1, 2), (2, 2), (5, 1), (1, 1)])
        self.assertEqual([(g.valuation, g.dim, g.disc_is_square) for g in sp2.graded],
                         [(1, 1, True), (0, 3, False)])
        self.assertEqual(sp.radical_dim, 0)

    def test_newton_polygon_of_x2_minus_5(self):
        poly = og.newton_polygon([og.Qp5_4.from_int(-5), og.Qp5_4.zero(), og.Qp5_4.one()])
        self.assertEqual([(str(s), m) for s, m in poly.root_valuations()], [("1/2", 2)])
        self.assertEqual(str(og.tropicalize(og.Qp5_4.from_p_power(2))), "2")

    def test_global_function_field_reciprocity(self):
        t = ([0, 1], [1])  # t in F_5(t)
        two = ([2], [1])
        self.assertEqual(og.try_hilbert_reciprocity_product_ff(5, t, two), 1)
        self.assertEqual(og.tame_symbol_invariant_sum_ff(5, 4, t, two), 0)
        self.assertFalse(og.try_is_isotropic_ff(5, [([1], [1]), ([0, 4], [1]), ([3], [1]), ([0, 2], [1])]))
        self.assertEqual(og.monic_irreducible_factors(5, [2, 0, 1]), [[2, 0, 1]])
        self.assertEqual(og.char2_monic_irreducible_factors([1, 1, 1]), [[1, 1, 1]])

    def test_artin_schreier_symbol_reciprocity_in_characteristic_two(self):
        one, t = ([1], [1]), ([0, 1], [1])
        self.assertEqual(og.as_symbol_reciprocity_sum(one, t), 0)
        self.assertEqual(len(og.as_symbol_places(one, t)), 2)
        self.assertTrue(og.global_is_pe(([0, 1, 1], [1])))  # t^2 + t = wp(t)
        self.assertFalse(og.global_is_pe(t))

    def test_runtime_p_adic_cells_and_adeles(self):
        k3 = og.adele_prec(3)
        third = og.LocalQp.from_rational(3, k3, 1, 3)
        self.assertEqual(third.valuation(), -1)
        two = og.LocalQp.from_int(3, k3, 2)
        self.assertEqual(repr(two * third), "2·3^-1 (mod 3^16)")
        adele = og.Adele.from_rational(2, 3)
        self.assertTrue(adele.satisfies_product_formula())
        self.assertEqual(adele.idele_norm(), (1, 1))


# ---------------------------------------------------------------------------
# Integral lattices
# ---------------------------------------------------------------------------


class LatticeTests(OgdoadTestCase):
    def test_root_lattice_invariants(self):
        for n in range(1, 6):
            lat = og.a_n(n)
            with self.subTest(root="A", n=n):
                self.assertEqual(lat.determinant(), n + 1)
                self.assertEqual(lat.minimum(), 2)
                self.assertEqual(lat.kissing_number(), n * (n + 1))
                self.assertEqual(og.coxeter_number(lat), n + 1)
                self.assertTrue(og.is_root_lattice(lat))
        for n in range(4, 7):
            lat = og.d_n(n)
            with self.subTest(root="D", n=n):
                self.assertEqual(lat.determinant(), 4)
                self.assertEqual(lat.kissing_number(), 2 * n * (n - 1))
                self.assertEqual(og.coxeter_number(lat), 2 * n - 2)
        self.assertEqual([f().determinant() for f in (og.e_6, og.e_7, og.e_8)], [3, 2, 1])
        self.assertEqual([f().kissing_number() for f in (og.e_6, og.e_7, og.e_8)], [72, 126, 240])
        self.assertEqual([og.coxeter_number(f()) for f in (og.e_6, og.e_7, og.e_8)], [12, 18, 30])

    def test_e8_is_even_unimodular_and_its_theta_series_is_e4(self):
        e8 = og.e_8()
        self.assertTrue(e8.is_even())
        self.assertTrue(e8.is_unimodular())
        self.assertEqual(e8.automorphism_group_order(), 696729600)
        self.assertEqual(e8.theta_series(3), [1, 240, 2160])
        self.assertEqual(e8.theta_series(3), og.eisenstein_e4(3))

    def test_a2_theta_signature_and_genus(self):
        a2 = og.a_n(2)
        self.assertEqual(a2.signature(), (2, 0))
        self.assertEqual(a2.theta_series(4), [1, 6, 0, 6])
        gen = a2.genus()
        self.assertEqual(gen.primes(), [2, 3])
        self.assertEqual(gen.det, 3)

    def test_siegel_mass_formula_matches_the_class_sum(self):
        # Mass of the genus = sum over classes of 1/|Aut|.
        num8, den8 = og.mass_even_unimodular(8)
        self.assertEqual(Fraction(num8, den8), Fraction(1, og.E8_WEYL_GROUP_ORDER))
        num16, den16 = og.mass_even_unimodular(16)
        classes16 = Fraction(1, 2 * og.E8_WEYL_GROUP_ORDER ** 2) + Fraction(1, og.D16_PLUS_AUT_ORDER)
        self.assertEqual(Fraction(num16, den16), classes16)
        num24, den24 = og.mass_even_unimodular(24)
        self.assertEqual(Fraction(num24, den24), rational_to_fraction(og.niemeier_mass_sum()))
        self.assertIsNone(og.mass_even_unimodular(7))  # no even unimodular lattice

    def test_niemeier_catalogue_and_modular_average(self):
        self.assertEqual(len(og.niemeier_classes()), 24)
        self.assertEqual(og.niemeier_weighted_theta_average(4), og.eisenstein_e12(4))

    def test_leech_constants_without_the_expensive_minimum(self):
        leech = og.leech()
        self.assertEqual((leech.dim, leech.determinant()), (24, 1))
        self.assertTrue(leech.is_even() and leech.is_unimodular())
        self.assertEqual(og.leech_aut_order(), 8315553613086720000)
        self.assertEqual(og.LEECH_AUT_ORDER, og.leech_aut_order())

    def test_d16_plus_is_even_unimodular_but_not_e8_squared(self):
        d16p = og.d16_plus()
        self.assertEqual((d16p.dim, d16p.determinant()), (16, 1))
        self.assertTrue(d16p.is_even())
        self.assertEqual(d16p.theta_series(2), [1, 480])  # 480 roots, same as E8 + E8
        self.assertTrue(og.are_in_same_genus(d16p, og.e_8().direct_sum(og.e_8())))

    def test_genus_distinguishes_odd_from_even_unimodular(self):
        self.assertTrue(og.are_in_same_genus(og.e_8(), og.e_8()))
        self.assertFalse(og.are_in_same_genus(og.IntegralForm.diagonal([1] * 8), og.e_8()))

    def test_discriminant_form_milgram_formula(self):
        for n in range(1, 7):
            lat = og.a_n(n)
            disc = og.DiscriminantForm.from_lattice(lat)
            with self.subTest(n=n):
                self.assertEqual(disc.milgram_signature_mod8(), og.genus_signature_mod8(lat))
                self.assertEqual(disc.milgram_signature_mod8(), n % 8)  # signature of A_n
                self.assertTrue(disc.verify_weil_relations())
        self.assertTrue(og.verify_milgram(og.a_n(2)))
        self.assertTrue(og.verify_odd_milgram(og.IntegralForm.diagonal([3])))

    def test_kneser_neighbour_of_e8_is_e8(self):
        report = og.even_unimodular_kneser_report(8)
        self.assertTrue(report.mass_closed)
        self.assertEqual(report.generated_class_labels, ["E8"])
        neighbour = og.e_8().kneser_neighbors(2, 1)[0].lattice
        self.assertTrue(neighbour.is_even() and neighbour.is_unimodular())

    def test_weyl_group_versors_in_pin(self):
        e8 = og.weyl_versor_report("E", 8)
        self.assertEqual((e8.weyl_group_order, e8.coxeter_versor_order), (696729600, 30))
        self.assertTrue(e8.simple_reflections_match_cartan)
        a3 = og.weyl_versor_report("A", 3)
        self.assertEqual((a3.weyl_group_order, a3.coxeter_versor_order), (24, 4))

    def test_determinant_overflow_is_loud(self):
        # The Bareiss determinant is outside the engine's guard: overflow
        # surfaces as pyo3_runtime.PanicException (documented), never a wrapped value.
        huge = og.IntegralForm.diagonal([2 ** 100, 2 ** 100, 2 ** 100])
        self.assert_raises_name(("PanicException", "ValueError", "OverflowError"),
                                huge.determinant)

    def test_gram_matrices_are_validated(self):
        with self.assertRaises(ValueError):
            og.IntegralForm([[1, 2], [3, 4]])  # not symmetric

    def test_pinned_constants(self):
        self.assertEqual(og.E8_WEYL_GROUP_ORDER, 696729600)
        self.assertEqual(og.D16_PLUS_AUT_ORDER, 685597979049984000)
        self.assertEqual(og.AUTO_NODE_BUDGET, 100_000_000)


class CodeTests(OgdoadTestCase):
    def test_extended_hamming_code_builds_e8_by_construction_a(self):
        code = og.BinaryCode.extended_hamming()
        self.assertEqual(code.weight_enumerator(), [1, 0, 0, 0, 14, 0, 0, 0, 1])
        self.assertEqual((code.len(), code.dim(), code.minimum_distance()), (8, 4, 4))
        self.assertTrue(code.is_self_dual())
        self.assertTrue(code.is_doubly_even())
        self.assertEqual(code.theta_series_via_weight_enumerator(3), [1, 240, 2160])
        lattice = code.construction_a()
        self.assertEqual(lattice.kissing_number(), 240)

    def test_golay_code_parameters_and_weight_enumerator(self):
        golay = og.BinaryCode.golay()
        self.assertEqual((golay.len(), golay.dim(), golay.minimum_distance()), (24, 12, 8))
        enumerator = golay.weight_enumerator()
        self.assertEqual({i: c for i, c in enumerate(enumerator) if c},
                         {0: 1, 8: 759, 12: 2576, 16: 759, 24: 1})
        self.assertEqual(sum(enumerator), 2 ** 12)

    def test_macwilliams_identity_for_the_self_dual_golay_code(self):
        golay = og.BinaryCode.golay()
        self.assertEqual(golay.dual().weight_enumerator(), golay.weight_enumerator())

    def test_ternary_golay_code(self):
        code = og.PrimeCode.ternary_golay()
        self.assertEqual(code.p, 3)
        self.assertEqual(code.weight_enumerator()[6], 264)
        self.assertEqual(sum(code.weight_enumerator()), 3 ** 6)

    def test_reed_muller_nesting_and_barnes_wall(self):
        rm1, rm2 = og.BinaryCode.reed_muller(1, 4), og.reed_muller_code(2, 4)
        self.assertEqual((rm1.dim(), rm2.dim()), (5, 11))
        self.assertTrue(rm2.contains(rm1))
        bw = og.barnes_wall_16()
        self.assertEqual((bw.determinant(), bw.minimum(), bw.kissing_number()), (256, 4, 4320))

    def test_lexicodes_are_the_classical_codes(self):
        self.assertEqual(og.lexicode(7, 3).weight_enumerator(),
                         og.BinaryCode.hamming().weight_enumerator())
        self.assertEqual(og.lexicode(8, 4).weight_enumerator(),
                         og.BinaryCode.extended_hamming().weight_enumerator())
        # Greedy lexicodes meet the best known linear parameters here.
        for n, d, k in ((15, 5, 7), (16, 6, 7), (15, 3, 11)):
            code = og.lexicode(n, d)
            self.assertEqual((code.len(), code.dim(), code.minimum_distance()), (n, k, d))
            self.assertEqual(sum(code.weight_enumerator()), 2 ** k)
            self.assertEqual(code.size(), 2 ** k)
        self.assertEqual(og.lexicode(7, 3).weight_enumerator(), [1, 0, 0, 7, 7, 0, 0, 1])

    def test_lexicode_budget_returns_none_instead_of_a_partial_code(self):
        self.assertIsNone(og.lexicode_bounded(10, 3, 1))
        self.assertEqual(og.lexicode_bounded(7, 3, 10 ** 6).size(), 16)


class FiniteQuadraticModuleTests(OgdoadTestCase):
    def test_cyclic_module_witt_class_and_nikulin_existence(self):
        fqm = og.FiniteQuadraticModule.cyclic(2, og.Rational(1, 2))
        witt = fqm.witt_class()
        self.assertEqual(witt.order, 2)
        report = fqm.nikulin_existence_report((1, 0))
        self.assertTrue(report.exists())

    def test_extraspecial_two_group_commutators_are_central(self):
        extra = og.extraspecial_group_f2([False, False], [0b10, 0b01])
        x0, x1 = extra.generator(0), extra.generator(1)
        weil = extra.heisenberg_weil_representation()
        self.assertTrue(extra.commutator(x0, x1).central)
        self.assertEqual(weil.hilbert_dim_u128(), 2)
        self.assertEqual(repr(extra), "Extraspecial2Group(dim=2, order_exponent=3, type=+)")

    def test_function_field_brauer_wall(self):
        alg = og.Fp3RationalFunctionAlgebra(q=[og.Fp3RationalFunction.one()])
        cls = og.bw_class_function_field(alg)
        self.assertEqual(cls.field_order, 3)

    def test_finite_hermitian_restriction_of_scalars(self):
        form = og.FiniteHermitianForm.diagonal(3, 2, [1, 1, 0])
        cls = form.classify()
        self.assertEqual((cls.rank, cls.radical_dim, cls.base_field_order, cls.extension_field_order),
                         (2, 1, 3, 9))
        self.assertEqual(form.restrict_scalars().dim, 6)
        norm_form = og.FiniteHermitianForm.diagonal(2, 4, [1]).restrict_scalars()
        info = og.classify_finite_algebra(norm_form)
        self.assertEqual((info.arf, info.rank), (1, 2))


if __name__ == "__main__":
    unittest.main()
