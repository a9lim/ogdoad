#!/usr/bin/env python3
"""Generate ``ogdoad.pyi`` type stubs from the built extension module.

PyO3's abi3 build does **not** preserve ``__text_signature__``, so argument
signatures cannot be recovered by introspection. What *is* recoverable — and
what this generator emits — is:

  * every class, with every public method, property and operator it defines,
    each carrying the Rust ``///`` doc-comment that PyO3 preserves as a
    docstring;
  * every module-level function and integer constant;
  * precise, source-verified signatures for the headline public API (the README
    surface) from the ``OVERRIDES`` table, plus the structural ``*Algebra``
    constructor patterns the ``backend!`` macro guarantees;
  * ``(self, *args: Any, **kwargs: Any) -> Any`` for everything else — honest
    about the unknown signature while keeping the name + docs discoverable.

Usage::

    python scripts/generate_stubs.py            # (re)write ogdoad.pyi in repo root
    python scripts/generate_stubs.py --check     # exit 1 if the committed stub is stale

For a pure-Rust maturin project, dropping ``ogdoad.pyi`` in the repo root makes
maturin ship it (and a ``py.typed`` marker) inside the wheel automatically.
"""

from __future__ import annotations

import inspect
import sys
from pathlib import Path

import ogdoad  # type: ignore[import-not-found]  # compiled extension, resolved at runtime

# --------------------------------------------------------------------------- #
# Curated, source-verified signatures for the headline public API.            #
# Keyed by bare function name (module level) or "Class.method" (members).      #
# Everything not listed here falls back to an opaque `*args`/`**kwargs` stub.  #
# --------------------------------------------------------------------------- #

# Builtin type tokens are written `builtins.int` etc. throughout: some classes
# expose methods named exactly `int` / `bool` / ... which would otherwise shadow
# the builtin inside the class body and break `-> int` annotations there.
FUNCTION_OVERRIDES: dict[str, str] = {
    "version": "() -> builtins.str",
    "ogham_eval": "(world: builtins.str, src: builtins.str) -> builtins.str",
    "omega": "() -> Surreal",
    "epsilon": "() -> Surreal",
    "omega_pow": "(exp: Any) -> Surreal",
    "classify_real": "(p: builtins.int, q: builtins.int, r: builtins.int = 0) -> CliffordInvariants",
    "classify_complex": "(n: builtins.int, r: builtins.int = 0) -> CliffordInvariants",
    "arf_nimber": "(alg: NimberAlgebra) -> ArfInvariants",
    "bw_class_nimber": "(alg: NimberAlgebra) -> BrauerWallClass",
    "is_isotropic_q": "(entries: Sequence[builtins.int]) -> builtins.bool",
    "hilbert_product": "(a: tuple[builtins.int, builtins.int], b: tuple[builtins.int, builtins.int]) -> builtins.int",
    "hilbert_symbol": "(p: builtins.int, a: builtins.int, b: builtins.int) -> builtins.int",
}

# "Class.method" -> signature. A leading "@staticmethod " marks a staticmethod
# (the `self` is then omitted from the signature string).
MEMBER_OVERRIDES: dict[str, str] = {
    # scalar constructors
    "Nimber.__init__": "(self, value: builtins.int) -> None",
    "Rational.__init__": "(self, num: builtins.int, den: builtins.int = 1) -> None",
    "Integer.__init__": "(self, value: builtins.int) -> None",
    "Surcomplex.__init__": "(self, re: Any, im: Any | None = None) -> None",
    "Surreal.__init__": "(self, coeffs: Sequence[Any]) -> None",
    # games bridge (README quickstart)
    "Color.blue": "@staticmethod () -> Color",
    "Color.red": "@staticmethod () -> Color",
    "Color.green": "@staticmethod () -> Color",
    "Hackenbush.string": "@staticmethod (colors: Sequence[Color]) -> Hackenbush",
    "Hackenbush.value": "(self) -> Surreal",
    "Hackenbush.grundy": "(self) -> Nimber",
}

# --------------------------------------------------------------------------- #
# Operator / protocol dunders: kept (with canonical signatures), everything    #
# else dunder-shaped is dropped from the stub as noise.                        #
# --------------------------------------------------------------------------- #

_BINARY = "(self, other: Any) -> Any"
_COMPARE = "(self, other: Any) -> builtins.bool"
DUNDER_SIGNATURES: dict[str, str] = {
    "__add__": _BINARY, "__radd__": _BINARY, "__sub__": _BINARY, "__rsub__": _BINARY,
    "__mul__": _BINARY, "__rmul__": _BINARY, "__truediv__": _BINARY, "__rtruediv__": _BINARY,
    "__floordiv__": _BINARY, "__mod__": _BINARY, "__rmod__": _BINARY,
    "__pow__": _BINARY, "__rpow__": _BINARY, "__matmul__": _BINARY, "__rmatmul__": _BINARY,
    "__and__": _BINARY, "__rand__": _BINARY, "__or__": _BINARY, "__ror__": _BINARY,
    "__xor__": _BINARY, "__rxor__": _BINARY,
    "__lshift__": _BINARY, "__rlshift__": _BINARY, "__rshift__": _BINARY, "__rrshift__": _BINARY,
    "__neg__": "(self) -> Any", "__pos__": "(self) -> Any",
    "__abs__": "(self) -> Any", "__invert__": "(self) -> Any",
    "__eq__": "(self, other: builtins.object) -> builtins.bool",
    "__ne__": "(self, other: builtins.object) -> builtins.bool",
    "__lt__": _COMPARE, "__le__": _COMPARE, "__gt__": _COMPARE, "__ge__": _COMPARE,
    "__hash__": "(self) -> builtins.int", "__repr__": "(self) -> builtins.str",
    "__str__": "(self) -> builtins.str",
    "__bool__": "(self) -> builtins.bool", "__len__": "(self) -> builtins.int",
    "__int__": "(self) -> builtins.int", "__index__": "(self) -> builtins.int",
    "__float__": "(self) -> builtins.float",
    "__getitem__": "(self, key: Any) -> Any", "__setitem__": "(self, key: Any, value: Any) -> None",
    "__contains__": "(self, item: Any) -> builtins.bool",
    "__iter__": "(self) -> Iterator[Any]", "__next__": "(self) -> Any",
    "__call__": "(self, *args: Any, **kwargs: Any) -> Any",
}

HEADER = """\
# This file is @generated by scripts/generate_stubs.py from the built ogdoad
# extension module. Do NOT edit by hand: run `python scripts/generate_stubs.py`
# to regenerate it.
#
# PyO3's abi3 build does not preserve argument signatures, so methods without a
# curated override in the generator are typed `(*args: Any, **kwargs: Any)`. The
# Rust `///` doc-comments are preserved verbatim as docstrings.
import builtins
from collections.abc import Iterator, Mapping, Sequence
from typing import Any
"""


def _is_constructible(cls: type) -> bool:
    """A PyO3 class without `#[new]` reports `cannot create ... instances`."""
    try:
        cls()
        return True
    except TypeError as exc:
        return "cannot create" not in str(exc)
    except Exception:
        return True


def _static_kind(cls: type, name: str) -> str:
    """'static', 'class', or 'instance' for a member, via the unbound descriptor."""
    try:
        raw = inspect.getattr_static(cls, name)
    except AttributeError:
        return "instance"
    if isinstance(raw, staticmethod):
        return "static"
    if isinstance(raw, classmethod):
        return "class"
    return "instance"


def _docstring_block(obj: object, indent: str) -> list[str]:
    # Raw `__doc__` only — never `inspect.getdoc`, which walks the MRO and would
    # graft misleading inherited boilerplate onto dunders (e.g. `__hash__`).
    doc = getattr(obj, "__doc__", None)
    if not doc:
        return []
    doc = inspect.cleandoc(doc)
    if not doc:
        return []
    doc = doc.replace("\\", "\\\\")
    if '"""' in doc:
        doc = doc.replace('"""', '\\"\\"\\"')
    lines = doc.splitlines()
    if len(lines) == 1:
        return [f'{indent}"""{lines[0]}"""']
    out = [f'{indent}"""{lines[0]}']
    out.extend(f"{indent}{ln}".rstrip() for ln in lines[1:])
    out.append(f'{indent}"""')
    return out


def _is_property(cls: type, name: str) -> bool:
    try:
        raw = inspect.getattr_static(cls, name)
    except AttributeError:
        return False
    return type(raw).__name__ in ("getset_descriptor", "property", "member_descriptor")


def _emit_function(name: str) -> list[str]:
    fn = getattr(ogdoad, name)
    sig = FUNCTION_OVERRIDES.get(name, "(*args: Any, **kwargs: Any) -> Any")
    head = f"def {name}{sig}:"
    body = _docstring_block(fn, "    ")
    if body:
        return [head, *body, ""]
    return [f"{head} ...", ""]


def _constructor_signature(cls: type, name: str) -> str | None:
    """Return the `__init__` signature body, or None to omit it entirely."""
    override = MEMBER_OVERRIDES.get(f"{name}.__init__")
    if override:
        return override
    if not _is_constructible(cls):
        return None
    if name.endswith("DividedPowerAlgebra"):
        return "(self, dim: builtins.int) -> None"
    if name.endswith("Algebra"):
        return (
            "(self, q: Sequence[Any], "
            "b: Mapping[tuple[builtins.int, builtins.int], Any] | None = None, "
            "a: Mapping[tuple[builtins.int, builtins.int], Any] | None = None) -> None"
        )
    return "(self, *args: Any, **kwargs: Any) -> None"


def _member_signature(cls_name: str, name: str, kind: str) -> str:
    """Signature body for a non-dunder method, honouring overrides + structure."""
    key = f"{cls_name}.{name}"
    if key in MEMBER_OVERRIDES:
        sig = MEMBER_OVERRIDES[key]
        return sig.removeprefix("@staticmethod ").strip() if sig.startswith("@staticmethod") else sig
    # `<World>Algebra.gen(i)` returns the matching `<World>MV` (backend! macro).
    if name == "gen" and cls_name.endswith("Algebra") and not cls_name.endswith("DividedPowerAlgebra"):
        mv = cls_name[: -len("Algebra")] + "MV"
        if hasattr(ogdoad, mv):
            return f"(self, i: builtins.int) -> {mv}"
    if kind == "static":
        return "(*args: Any, **kwargs: Any) -> Any"
    if kind == "class":
        return "(cls, *args: Any, **kwargs: Any) -> Any"
    return "(self, *args: Any, **kwargs: Any) -> Any"


def _emit_class(name: str) -> list[str]:
    cls = getattr(ogdoad, name)
    lines = [f"class {name}:"]
    body: list[str] = []

    cdoc = _docstring_block(cls, "    ")
    if cdoc:
        body.extend(cdoc)

    own = set(vars(cls))

    # constructor
    ctor = _constructor_signature(cls, name)
    if ctor is not None:
        body.append(f"    def __init__{ctor}: ...")

    # properties (PyO3 getters) come first, sorted
    props = sorted(n for n in own if not n.startswith("_") and _is_property(cls, n))
    for n in props:
        body.append("    @property")
        head = f"    def {n}(self) -> Any:"
        doc = _docstring_block(inspect.getattr_static(cls, n), "        ")
        body.extend([head, *doc] if doc else [f"{head} ..."])

    # regular methods, sorted
    methods = sorted(
        n for n in own
        if not n.startswith("_") and not _is_property(cls, n)
    )
    for n in methods:
        kind = _static_kind(cls, n)
        sig = _member_signature(name, n, kind)
        member_override = MEMBER_OVERRIDES.get(f"{name}.{n}", "")
        is_static = kind == "static" or member_override.startswith("@staticmethod")
        if is_static:
            body.append("    @staticmethod")
        elif kind == "class":
            body.append("    @classmethod")
        head = f"    def {n}{sig}:"
        doc = _docstring_block(getattr(cls, n), "        ")
        body.extend([head, *doc] if doc else [f"{head} ..."])

    # operator / protocol dunders, sorted. No docstrings: PyO3 leaves these with
    # inherited boilerplate, not real `///` docs.
    dunders = sorted(n for n in own if n in DUNDER_SIGNATURES)
    for n in dunders:
        body.append(f"    def {n}{DUNDER_SIGNATURES[n]}: ...")

    if not body:
        body.append("    ...")
    lines.extend(body)
    lines.append("")
    return lines


def build() -> str:
    names = [n for n in dir(ogdoad) if not n.startswith("_")]
    consts, funcs, classes = [], [], []
    for n in names:
        obj = getattr(ogdoad, n)
        if inspect.isclass(obj):
            classes.append(n)
        elif inspect.isroutine(obj):
            funcs.append(n)
        elif isinstance(obj, int) and not isinstance(obj, bool):
            consts.append(n)
        # modules and anything else are skipped

    out = [HEADER, ""]
    for n in sorted(consts):
        out.append(f"{n}: builtins.int")
    if consts:
        out.append("")
    for n in sorted(classes):
        out.extend(_emit_class(n))
    for n in sorted(funcs):
        out.extend(_emit_function(n))
    text = "\n".join(out).rstrip() + "\n"
    return text


def main() -> int:
    target = Path(__file__).resolve().parent.parent / "ogdoad.pyi"
    text = build()
    if "--check" in sys.argv:
        if not target.exists() or target.read_text() != text:
            print(
                f"ogdoad.pyi is stale — run `python {Path(__file__).name}` and commit.",
                file=sys.stderr,
            )
            return 1
        print("ogdoad.pyi is up to date.")
        return 0
    target.write_text(text)
    n_classes = text.count("\nclass ")
    print(f"wrote {target} ({text.count(chr(10))} lines, {n_classes} classes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
