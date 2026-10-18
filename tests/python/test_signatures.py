"""Curated stub signatures must match the runtime's keyword interface.

PyO3's abi3 build exposes no introspectable signatures, so ``ogdoad.pyi`` types
most callables as ``(*args, **kwargs)`` and carries hand-curated signatures for
the rest (all of the Weyl surface, the Hermitian/Brown/Guy--Smith constructors
and about fifty module functions).  Nothing else ties those names to the Rust
``#[pyo3(signature = ...)]`` attributes, so this test does: every declared
parameter must be accepted by keyword, every parameter declared without a
default must be required, and every parameter declared with one must be
optional.  A call with sentinel objects never reaches the mathematics -- the
argument parser rejects or converts the sentinels first.
"""

import ast
import pathlib
import unittest

import ogdoad as og

from _support import OgdoadTestCase

REPO = pathlib.Path(__file__).resolve().parents[2]
PACKAGE = pathlib.Path(og.__file__).resolve().parent


def load_stub():
    for candidate in (REPO / "ogdoad.pyi", PACKAGE / "__init__.pyi"):
        if candidate.is_file():
            return ast.parse(candidate.read_text(encoding="utf-8"))
    raise unittest.SkipTest("ogdoad.pyi is not available")


def parameters(fn, drop_receiver):
    """(required, optional) parameter names of a stub function definition."""
    args = fn.args
    names = [a.arg for a in args.args]
    if drop_receiver and names and names[0] in ("self", "cls"):
        names = names[1:]
    defaults = len(args.defaults)
    required = names[: len(names) - defaults] if defaults else list(names)
    optional = names[len(names) - defaults:] if defaults else []
    for arg, default in zip(args.kwonlyargs, args.kw_defaults):
        (optional if default is not None else required).append(arg.arg)
    return required, optional


def curated(fn):
    return not fn.args.vararg and not fn.args.kwarg


def call_with_sentinels(call, names):
    """Call by keyword with sentinel objects; return the TypeError text, if any."""
    try:
        call(**{n: object() for n in names})
    except TypeError as exc:
        return str(exc)
    except BaseException:  # noqa: BLE001 - recognised, then failed deeper: fine
        return None
    return None


def signature_problems(call, required, optional):
    problems = []
    every = required + optional
    text = call_with_sentinels(call, every)
    if text and ("unexpected keyword" in text or "missing" in text):
        problems.append(f"declared keywords rejected: {text[:90]}")
    for name in required:
        text = call_with_sentinels(call, [n for n in every if n != name])
        if not (text and "missing" in text):
            problems.append(f"required parameter {name!r} is not enforced")
    for name in optional:
        text = call_with_sentinels(call, [n for n in every if n != name])
        if text and "missing" in text and f"'{name}'" in text:
            problems.append(f"optional parameter {name!r} is required at runtime")
    return problems


def instances():
    """One instance per class whose curated methods need a receiver."""
    made = {}
    families = (
        ("Rational", og.RationalWeylAlgebra, og.Rational, og.RationalSparsePolynomial, None),
        ("Fp3", og.Fp3WeylAlgebra, og.Fp3, og.Fp3SparsePolynomial, 9),
        ("Nimber", og.NimberWeylAlgebra, og.Nimber, og.NimberSparsePolynomial, 4),
    )
    for name, alg, scalar, poly, fibre in families:
        W = alg(1)
        made[name + "WeylAlgebra"] = W
        made[name + "WeylElement"] = W.x(0)
        made[name + "SparsePolynomial"] = poly(2)
        if fibre is not None:
            made[name + "WeylPSymbol"] = W.psymbol([scalar(2), scalar(1)], fibre)
    made["GuySmithCertificate"] = og.GuySmithCertificate.compute(og.OctalCode([2]), 1, 2, 16)
    made["BrownSelector"] = og.BrownSelector([1], [0], 1)
    made["WittFifoArena"] = og.WittFifoArena([True], [0], 1)
    return made


class SignatureDriftTests(OgdoadTestCase):
    @classmethod
    def setUpClass(cls):
        cls.tree = load_stub()
        cls.instances = instances()

    def test_the_checker_itself_detects_wrong_names_and_wrong_arity(self):
        # Control group: deliberately wrong declarations must be flagged.
        self.assertTrue(signature_problems(og.nim_add, ["x", "y"], []))  # real names are (a, b)
        self.assertTrue(signature_problems(og.nim_add, ["a"], []))  # too few
        self.assertTrue(signature_problems(og.nim_add, ["a"], ["b"]))  # b is required
        self.assertTrue(signature_problems(og.nim_add, ["a", "b", "c"], []))  # extra
        self.assertEqual(signature_problems(og.nim_add, ["a", "b"], []), [])

    def test_curated_module_functions_match_the_runtime(self):
        checked, problems = 0, []
        for node in self.tree.body:
            if isinstance(node, ast.FunctionDef) and curated(node):
                required, optional = parameters(node, drop_receiver=False)
                if not (required or optional):
                    continue
                checked += 1
                for problem in signature_problems(getattr(og, node.name), required, optional):
                    problems.append(f"{node.name}: {problem}")
        self.assertGreater(checked, 40)
        self.assertEqual(problems, [])

    def test_curated_methods_match_the_runtime(self):
        checked, problems = 0, []
        for node in self.tree.body:
            if not isinstance(node, ast.ClassDef):
                continue
            for item in node.body:
                if not isinstance(item, ast.FunctionDef) or not curated(item) or item.name.startswith("__"):
                    continue
                static = any(isinstance(d, ast.Name) and d.id == "staticmethod"
                             for d in item.decorator_list)
                required, optional = parameters(item, drop_receiver=not static)
                if not (required or optional):
                    continue
                if static:
                    call = getattr(getattr(og, node.name), item.name)
                else:
                    receiver = self.instances.get(node.name)
                    if receiver is None:
                        continue
                    call = getattr(receiver, item.name)
                checked += 1
                for problem in signature_problems(call, required, optional):
                    problems.append(f"{node.name}.{item.name}: {problem}")
        self.assertGreater(checked, 150)
        self.assertEqual(problems, [])

    def test_every_weyl_method_has_a_curated_signature(self):
        # The Weyl surface is new in 2.0; none of it should fall back to *args.
        weyl_classes = {f"{backend}{kind}" for backend in ("Rational", "Fp3", "Nimber")
                        for kind in ("WeylAlgebra", "WeylElement", "SparsePolynomial", "WeylPSymbol")}
        uncurated, seen = [], set()
        for node in self.tree.body:
            if isinstance(node, ast.ClassDef) and node.name in weyl_classes:
                seen.add(node.name)
                for item in node.body:
                    if isinstance(item, ast.FunctionDef) and not item.name.startswith("__") \
                            and not curated(item):
                        uncurated.append(f"{node.name}.{item.name}")
        self.assertEqual(seen, weyl_classes)
        self.assertEqual(uncurated, [])


# ---------------------------------------------------------------------------
# Declared return types of the Weyl surface
# ---------------------------------------------------------------------------


def conforms(value, node):
    """Does ``value`` inhabit the stub annotation ``node``?  (Subset of typing
    the generated stub actually uses: builtins, classes, ``X | None``,
    ``list[X]`` and ``tuple[X, ...]``.)"""
    if isinstance(node, ast.Constant) and node.value is None:
        return value is None
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) \
            and node.value.id == "builtins":
        expected = {"int": int, "bool": bool, "str": str, "float": float}[node.attr]
        return type(value) is expected
    if isinstance(node, ast.Name):
        if node.id == "Any":
            return True
        return isinstance(value, getattr(og, node.id))
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        return conforms(value, node.left) or conforms(value, node.right)
    if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name):
        outer = node.value.id
        inner = node.slice
        if outer == "list":
            return isinstance(value, list) and all(conforms(v, inner) for v in value)
        if outer == "tuple":
            parts = inner.elts if isinstance(inner, ast.Tuple) else [inner]
            return (isinstance(value, tuple) and len(value) == len(parts)
                    and all(conforms(v, n) for v, n in zip(value, parts)))
    raise AssertionError(f"unsupported annotation: {ast.dump(node)}")


class _Ctx:
    """Valid arguments for every Weyl entry point of one backend family."""

    def __init__(self, backend):
        names = {"Rational": (og.Rational, 0), "Fp3": (og.Fp3, 3), "Nimber": (og.Nimber, 2)}
        self.name = backend
        self.S, self.p = names[backend]
        self.Alg = getattr(og, backend + "WeylAlgebra")
        self.Poly = getattr(og, backend + "SparsePolynomial")
        S = self.S
        self.one, self.two = S(1), S(2)
        self.W = self.Alg(1)
        self.W2 = self.Alg(2)
        self.x, self.d = self.W.x(0), self.W.d(0)
        self.e = self.x * self.d + self.d
        self.t = self.Poly.monomial([2], self.one)
        self.poly2 = self.Poly.variable(2, 0) * self.Poly.variable(2, 1)
        self.values = [self.two, self.one]
        self.dim = max(self.p, 1) ** 2
        self.G = self.Alg.from_commutator([[S(0), S(1), S(1)], [-S(1), S(0), S(2)], [-S(1), -S(2), S(0)]])
        self.g0, self.g1 = self.G.generator(0), self.G.generator(1)
        self.identity = [[S(1), S(0)], [S(0), S(1)]]
        self.embed = [[S(1), S(0)], [S(0), S(0)], [S(0), S(1)], [S(0), S(0)]]
        self.gdim = self.dim * max(self.p, 1)  # fibre of the rank-3 general presentation
        self.roots = {0: [S(1), S(1)], 3: [S(2), S(1)], 2: [S(2).sqrt(), S(1)]}[self.p]
        self.P = self.W.psymbol(self.values, self.dim) if self.p else None


def weyl_calls(c):
    one, two, W = c.one, c.two, c.W
    x, d, e = c.x, c.d, c.e
    budget = {"max_terms": 10 ** 6, "max_steps": 10 ** 9}
    alg = {
        "act_on_sparse_polynomial": lambda: W.act_on_sparse_polynomial(x, c.t, **budget),
        "affine_map_to": lambda: W.affine_map_to(c.W2, e, c.embed, [one, two], **budget),
        "bernstein_degree": lambda: W.bernstein_degree(e),
        "center_basis_element": lambda: W.center_basis_element(1, **budget),
        "center_generators": lambda: W.center_generators(**budget),
        "center_rank_over_center": lambda: W.center_rank_over_center(),
        "central_character_generator_matrices": lambda: W.central_character_generator_matrices(
            c.values, c.roots, c.dim, 100, 10 ** 6),
        "central_reduce": lambda: W.central_reduce(e, c.values, c.dim),
        "clifford_fiber_products_agree": lambda: W.clifford_fiber_products_agree(
            x, d, c.values, c.dim, **budget),
        "commutator": lambda: W.commutator(x, d, **budget),
        "commutator_form": lambda: W.commutator_form(),
        "d": lambda: W.d(0),
        "darboux_from_normal": lambda: c.G.darboux_from_normal(c.G.darboux_to_normal(c.g0)[1], **budget),
        "darboux_ranks": lambda: c.G.darboux_ranks(),
        "darboux_to_normal": lambda: c.G.darboux_to_normal(c.g0 * c.g1, **budget),
        "differential_order": lambda: W.differential_order(e),
        "dim": lambda: W.dim(),
        "direct_sum": lambda: W.direct_sum(W),
        "formal_adjoint": lambda: W.formal_adjoint(e, **budget),
        "fourier": lambda: W.fourier(e, **budget),
        "fourier_central_character": lambda: W.fourier_central_character(c.values, c.dim, **budget),
        "fourier_inverse": lambda: W.fourier_inverse(e, **budget),
        "from_commutator": lambda: c.Alg.from_commutator([[c.S(0), one], [-one, c.S(0)]]),
        "generator": lambda: W.generator(1),
        "hbar_commutator": lambda: W.hbar_commutator(x, d, one, **budget),
        "hbar_product": lambda: W.hbar_product(x, d, one, **budget),
        "is_central": lambda: W.is_central(e, **budget),
        "monomial": lambda: W.monomial([1, 1], one),
        "mul": lambda: W.mul(x, d, **budget),
        "one": lambda: W.one(),
        "parity": lambda: W.parity(e, **budget),
        "poisson_bracket": lambda: W.poisson_bracket(c.poly2, c.Poly.variable(2, 1), **budget),
        "pow": lambda: W.pow(e, 3, **budget),
        "principal_symbol": lambda: W.principal_symbol(e, "bernstein"),
        "psymbol": lambda: W.psymbol(c.values, c.dim),
        "radical_generators": lambda: c.G.radical_generators(**budget),
        "scalar": lambda: W.scalar(two),
        "scaling": lambda: W.scaling(e, [two], **budget),
        "scaling_central_character": lambda: W.scaling_central_character(c.values, [two], c.dim, **budget),
        "shear": lambda: W.shear(e, [[one]], **budget),
        "shear_central_character": lambda: W.shear_central_character(c.values, [[one]], c.dim, **budget),
        "standard_pairs": lambda: W.standard_pairs(),
        "translation": lambda: W.translation(e, [one, two], **budget),
        "translation_central_character": lambda: W.translation_central_character(
            c.values, [one, two], c.dim, **budget),
        "transported_central_reduce": lambda: c.G.transported_central_reduce(
            c.g0 * c.g1, c.values, [one], c.gdim, **budget),
        "transported_fiber_products_agree": lambda: c.G.transported_fiber_products_agree(
            c.g0, c.g1, c.values, [one], c.gdim, **budget),
        "x": lambda: W.x(0),
        "zero": lambda: W.zero(),
    }
    element = {
        "algebra": lambda: x.algebra(),
        "dim": lambda: x.dim(),
        "is_zero": lambda: x.is_zero(),
        "mul": lambda: x.mul(d, **budget),
        "pow": lambda: e.pow(2, **budget),
        "scale": lambda: x.scale(two),
        "term_count": lambda: e.term_count(),
        "terms": lambda: e.terms(),
    }
    P = c.Poly
    poly = {
        "dim": lambda: c.t.dim(),
        "is_zero": lambda: c.t.is_zero(),
        "monomial": lambda: P.monomial([1, 2], one),
        "mul": lambda: c.t.mul(c.t, **budget),
        "partial_derivative": lambda: c.t.partial_derivative(0),
        "scalar": lambda: P.scalar(2, two),
        "scale": lambda: c.t.scale(two),
        "term_count": lambda: c.t.term_count(),
        "terms": lambda: c.t.terms(),
        "total_degree": lambda: c.t.total_degree(),
        "variable": lambda: P.variable(2, 1),
    }
    psym = {
        "brauer_split": lambda: c.P.brauer_split(),
        "certify_split": lambda: c.P.certify_split(c.roots, c.dim, 100, 10 ** 6),
        "characteristic": lambda: c.P.characteristic(),
        "cyclic_factor": lambda: c.P.cyclic_factor(0, c.dim, **budget),
        "p_residue": lambda: c.P.p_residue(e),
        "pairs": lambda: c.P.pairs(),
        "split_trace_matches_residue": lambda: c.P.split_trace_matches_residue(
            e, c.roots, c.dim, 100, 10 ** 6),
        "tensor_rank": lambda: c.P.tensor_rank(),
    }
    return {"WeylAlgebra": alg, "WeylElement": element, "SparsePolynomial": poly, "WeylPSymbol": psym}



# Entry points that refuse a backend by design (ValueError), per backend.
POSITIVE_CHARACTERISTIC_ONLY = {
    "center_basis_element", "center_generators", "center_rank_over_center",
    "central_character_generator_matrices", "central_reduce",
    "clifford_fiber_products_agree", "fourier_central_character", "psymbol",
    "scaling_central_character", "shear_central_character",
    "translation_central_character", "transported_central_reduce",
    "transported_fiber_products_agree",
}
DOCUMENTED_REFUSALS = {
    "Rational": POSITIVE_CHARACTERISTIC_ONLY,
    "Fp3": {"clifford_fiber_products_agree"},  # characteristic two only
    "Nimber": {"certify_split"},  # odd characteristic only
}


class WeylStubReturnTypeTests(OgdoadTestCase):
    @classmethod
    def setUpClass(cls):
        cls.tree = load_stub()

    def stub_methods(self, class_name):
        for node in self.tree.body:
            if isinstance(node, ast.ClassDef) and node.name == class_name:
                return {item.name: item for item in node.body
                        if isinstance(item, ast.FunctionDef) and not item.name.startswith("__")}
        self.fail(f"{class_name} is not in the stub")

    def test_every_weyl_method_returns_its_declared_type(self):
        exercised = 0
        for backend in ("Rational", "Fp3", "Nimber"):
            ctx = _Ctx(backend)
            tables = weyl_calls(ctx)
            for kind, table in tables.items():
                class_name = backend + kind
                methods = self.stub_methods(class_name)
                # the table must cover exactly the declared methods
                self.assertEqual(sorted(table), sorted(methods), class_name)
                for name, call in table.items():
                    with self.subTest(method=f"{class_name}.{name}"):
                        if backend == "Rational" and kind == "WeylPSymbol":
                            continue  # characteristic zero has no p-symbol presentation
                        refusals = DOCUMENTED_REFUSALS[backend]
                        if kind == "WeylAlgebra" and name in refusals:
                            with self.assertRaises(ValueError):
                                call()
                            continue
                        if kind == "WeylPSymbol" and name in refusals:
                            with self.assertRaises(ValueError):
                                call()
                            continue
                        value = call()
                        exercised += 1
                        returns = methods[name].returns
                        self.assertTrue(conforms(value, returns),
                                        f"{class_name}.{name} returned {value!r}; stub says "
                                        f"{ast.unparse(returns)}")
        self.assertGreater(exercised, 120)

    def test_annotation_checker_itself(self):
        parse = lambda text: ast.parse(text, mode="eval").body
        self.assertTrue(conforms(3, parse("builtins.int")))
        self.assertFalse(conforms(True, parse("builtins.int")))
        self.assertTrue(conforms(None, parse("builtins.int | None")))
        self.assertTrue(conforms([(1, og.Nimber(1))], parse("list[tuple[builtins.int, Nimber]]")))
        self.assertFalse(conforms([(1, 2)], parse("list[tuple[builtins.int, Nimber]]")))
        self.assertFalse(conforms((1, 2, 3), parse("tuple[builtins.int, builtins.int]")))


if __name__ == "__main__":
    unittest.main()
