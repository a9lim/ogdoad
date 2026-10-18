"""The generated ``ogdoad.pyi`` must describe the module that actually imports.

``scripts/generate_stubs.py --check`` guards the stub against the *built*
extension in CI; these tests make the same promise from the installed wheel's
point of view, plus the packaging facts a user can observe (typing payload,
version, classes reporting the ``ogdoad`` module).
"""

import ast
import importlib.metadata
import pathlib
import unittest

import ogdoad as og

from _support import OgdoadTestCase

REPO = pathlib.Path(__file__).resolve().parents[2]
PACKAGE = pathlib.Path(og.__file__).resolve().parent


def stub_path():
    """The committed stub when running from a checkout, else the installed one."""
    for candidate in (REPO / "ogdoad.pyi", PACKAGE / "__init__.pyi"):
        if candidate.is_file():
            return candidate
    return None


def parse_stub():
    path = stub_path()
    if path is None:
        raise unittest.SkipTest("ogdoad.pyi is not available")
    return ast.parse(path.read_text(encoding="utf-8"))


def stub_surface(tree):
    classes, functions, constants = {}, [], []
    for node in tree.body:
        if isinstance(node, ast.ClassDef):
            members = []
            for item in node.body:
                if isinstance(item, ast.FunctionDef):
                    members.append(item.name)
                elif isinstance(item, ast.AnnAssign) and isinstance(item.target, ast.Name):
                    members.append(item.target.id)
            classes[node.name] = members
        elif isinstance(node, ast.FunctionDef):
            functions.append(node.name)
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            constants.append(node.target.id)
    return classes, functions, constants


class StubDriftTests(OgdoadTestCase):
    @classmethod
    def setUpClass(cls):
        cls.classes, cls.functions, cls.constants = stub_surface(parse_stub())

    def test_stub_is_nonempty_and_large(self):
        # 675 classes in 2.0; a collapse to a handful means the parse is wrong.
        self.assertGreater(len(self.classes), 600)
        self.assertGreater(len(self.functions), 200)
        self.assertGreaterEqual(len(self.constants), 10)

    def test_every_class_in_the_stub_exists(self):
        missing = [n for n in self.classes if not hasattr(og, n)]
        self.assertEqual(missing, [])

    def test_every_function_in_the_stub_exists_and_is_callable(self):
        missing = [n for n in self.functions if not callable(getattr(og, n, None))]
        self.assertEqual(missing, [])

    def test_every_constant_in_the_stub_exists(self):
        missing = [n for n in self.constants if not hasattr(og, n)]
        self.assertEqual(missing, [])

    def test_every_member_of_every_stub_class_exists(self):
        missing = []
        for cls_name, members in self.classes.items():
            cls = getattr(og, cls_name, None)
            if cls is None:
                continue
            for member in members:
                if not hasattr(cls, member):
                    missing.append(f"{cls_name}.{member}")
        self.assertEqual(missing, [])

    def test_the_module_exports_nothing_the_stub_omits(self):
        declared = set(self.classes) | set(self.functions) | set(self.constants)
        extra = []
        for name in dir(og):
            if name.startswith("_") or name in declared:
                continue
            if isinstance(getattr(og, name), type(og)):
                continue  # submodule attributes such as ``ogdoad.ogdoad``
            extra.append(name)
        self.assertEqual(extra, [])

    def test_public_methods_of_stub_classes_are_all_declared(self):
        undeclared = []
        for cls_name, members in self.classes.items():
            cls = getattr(og, cls_name, None)
            if cls is None:
                continue
            declared = set(members)
            for member in vars(cls):
                if member.startswith("_") or member in declared:
                    continue
                undeclared.append(f"{cls_name}.{member}")
        self.assertEqual(undeclared, [])


class PackagingTests(OgdoadTestCase):
    def test_typing_payload_ships_with_the_package(self):
        self.assertTrue((PACKAGE / "py.typed").is_file())
        self.assertTrue((PACKAGE / "__init__.pyi").is_file())

    def test_installed_stub_declares_the_same_surface_as_the_committed_stub(self):
        # Compared structurally, not byte for byte: docstring-only edits to the
        # Rust doc comments change the generated text without changing the API.
        committed = REPO / "ogdoad.pyi"
        installed = PACKAGE / "__init__.pyi"
        if not committed.is_file() or not installed.is_file():
            self.skipTest("needs both a checkout and an installed wheel")

        def surface(path):
            return stub_surface(ast.parse(path.read_text(encoding="utf-8")))

        self.assertEqual(surface(committed), surface(installed))

    def test_version_matches_the_installed_distribution(self):
        try:
            installed = importlib.metadata.version("ogdoad")
        except importlib.metadata.PackageNotFoundError:
            self.skipTest("ogdoad is not installed as a distribution")
        self.assertEqual(og.version(), installed)

    def test_version_matches_cargo_toml(self):
        cargo = REPO / "Cargo.toml"
        if not cargo.is_file():
            self.skipTest("no checkout")
        for line in cargo.read_text(encoding="utf-8").splitlines():
            if line.startswith("version"):
                declared = line.split("=", 1)[1].strip().strip('"')
                break
        else:
            self.fail("Cargo.toml has no version line")
        self.assertEqual(og.version(), declared)

    def test_version_is_a_dotted_triple(self):
        parts = og.version().split(".")
        self.assertEqual(len(parts), 3)
        self.assertTrue(all(p.isdigit() for p in parts))


if __name__ == "__main__":
    unittest.main()
