"""The documented examples keep working: the README's Python block and the
``demo.py`` tour are executed verbatim, so their embedded assertions are part
of the suite (CI also runs ``demo.py`` on its own)."""

import contextlib
import io
import pathlib
import re
import runpy
import unittest

import ogdoad as og

from _support import OgdoadTestCase

REPO = pathlib.Path(__file__).resolve().parents[2]


def readme_python_blocks():
    readme = REPO / "README.md"
    if not readme.is_file():
        raise unittest.SkipTest("README.md is not available (not a checkout)")
    return re.findall(r"```python\n(.*?)```", readme.read_text(encoding="utf-8"), re.S)


class ReadmeTests(OgdoadTestCase):
    def test_readme_has_a_python_example(self):
        blocks = readme_python_blocks()
        self.assertTrue(blocks)
        self.assertIn("NimberWeylAlgebra", blocks[0])

    def test_readme_example_executes(self):
        namespace = {}
        for block in readme_python_blocks():
            exec(compile(block, "README.md", "exec"), namespace)

    def test_readme_claims_stated_as_assertions(self):
        # Mirrors the example's key claims against the live module.
        A = og.NimberAlgebra(q=[og.Nimber(2), og.Nimber(3)], b={(0, 1): 1})
        e0, e1 = A.gen(0), A.gen(1)
        self.assertEqual(e0 * e1 + e1 * e0, A.scalar(og.Nimber(1)))

        W = og.NimberWeylAlgebra(1)
        x, d = W.x(0), W.d(0)
        self.assertEqual(W.commutator(d, x), W.one())
        P = W.psymbol([og.Nimber(2), og.Nimber(3)], 4)
        self.assertEqual(P.p_residue(x * d), og.Nimber(1))
        self.assertEqual(P.cyclic_factor(0, 4), (og.Nimber(3), og.Nimber(1)))

        W3 = og.Fp3WeylAlgebra(1)
        P3 = W3.psymbol([og.Fp3(2), og.Fp3(1)], 9)
        self.assertTrue(P3.certify_split([og.Fp3(2), og.Fp3(1)], 9, 100, 1_000_000))
        self.assertTrue(P3.split_trace_matches_residue(
            W3.monomial([2, 2], 1), [og.Fp3(2), og.Fp3(1)], 9, 100, 1_000_000))
        self.assertTrue(W.clifford_fiber_products_agree(
            d * x, x + d, [og.Nimber(2), og.Nimber(3)], 4, max_terms=32, max_steps=1_000))

        S = og.SurrealAlgebra(q=[og.omega(), og.epsilon()])
        self.assertEqual((S.gen(0) * S.gen(1)) ** 2, S.scalar(og.Surreal.from_int(-1)))

        H = og.HermitianForm.diagonal([1, -1])
        Q = H.restrict_scalars()
        self.assertTrue(Q.dim == 4 and og.surreal_signature(Q) == (2, 2, 0))

        arena = og.WittFifoArena(diagonal=[True], polar=[0], input=1)
        self.assertTrue(arena.quadratic_value and arena.grundy(state_budget=100_000) != 0)
        selector = og.BrownSelector(q4=[3], brown_polar=[0], input=1)
        outcome = selector.outcome_class(state_budget_per_follower=100_000)
        self.assertEqual(og.BrownSelector.decode_outcome(outcome), selector.residue)
        code = og.OctalCode([2])
        certificate = og.GuySmithCertificate.compute(code, 1, 2, term_budget=16)
        self.assertEqual(certificate.heap_grundy(10 ** 30), 1)


class DemoTests(OgdoadTestCase):
    def test_demo_script_runs_to_completion(self):
        demo = REPO / "demo.py"
        if not demo.is_file():
            self.skipTest("demo.py is not available (not a checkout)")
        with contextlib.redirect_stdout(io.StringIO()) as captured:
            runpy.run_path(str(demo), run_name="__main__")
        text = captured.getvalue()
        # A few anchors from the tour, so a silently truncated run is noticed.
        self.assertIn("── nimbers On₂", text)
        self.assertIn("checked Guy–Smith certificate", text)
        self.assertGreater(text.count("── "), 60)


if __name__ == "__main__":
    unittest.main()
