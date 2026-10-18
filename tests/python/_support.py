"""Shared helpers for the ogdoad Python binding tests.

The suite uses only the standard library.  Run it from the repository root
after installing the wheel:

    python -m unittest discover -s tests/python -v
"""

import contextlib
import itertools
import os
import sys
import unittest


@contextlib.contextmanager
def quiet_rust_panics():
    """Silence Rust's default panic report while a call is expected to panic.

    PyO3 turns a Rust panic into ``pyo3_runtime.PanicException`` (or, behind a
    guarded boundary, ``ValueError``), but the Rust panic hook still prints
    ``thread ... panicked at ...`` to file descriptor 2.  The exception is the
    contract under test; the report is noise, so mute fd 2 for the duration.
    """
    sys.stderr.flush()
    saved = os.dup(2)
    devnull = os.open(os.devnull, os.O_WRONLY)
    try:
        os.dup2(devnull, 2)
        yield
    finally:
        sys.stderr.flush()
        os.dup2(saved, 2)
        os.close(saved)
        os.close(devnull)


class OgdoadTestCase(unittest.TestCase):
    """``unittest.TestCase`` with algebraic-law helpers."""

    # -- generic laws ---------------------------------------------------

    def assert_abelian_group(self, samples, zero):
        """Additive abelian-group axioms on ``samples``."""
        for a in samples:
            self.assertEqual(a + zero, a)
            self.assertEqual(zero + a, a)
            self.assertEqual(a - a, zero)
            self.assertEqual(a + (-a), zero)
        for a, b in itertools.product(samples, repeat=2):
            self.assertEqual(a + b, b + a)
            self.assertEqual(a - b, a + (-b))
        for a, b, c in itertools.product(samples, repeat=3):
            self.assertEqual((a + b) + c, a + (b + c))

    def assert_ring(self, samples, zero, one, commutative=True):
        """Commutative-ring (or ring) axioms on ``samples``.

        Callers pass samples closed enough for the checks to be meaningful;
        the laws are asserted, not searched for.
        """
        self.assert_abelian_group(samples, zero)
        for a in samples:
            self.assertEqual(a * one, a)
            self.assertEqual(one * a, a)
            self.assertEqual(a * zero, zero)
            self.assertEqual(zero * a, zero)
        for a, b in itertools.product(samples, repeat=2):
            if commutative:
                self.assertEqual(a * b, b * a)
        for a, b, c in itertools.product(samples, repeat=3):
            self.assertEqual((a * b) * c, a * (b * c))
            self.assertEqual(a * (b + c), a * b + a * c)
            self.assertEqual((a + b) * c, a * c + b * c)

    def assert_field(self, samples, zero, one):
        """Field axioms: a commutative ring where nonzero elements invert."""
        self.assert_ring(samples, zero, one, commutative=True)
        for a in samples:
            if a == zero:
                continue
            inv = a.inv()
            self.assertEqual(a * inv, one)
            self.assertEqual(inv * a, one)
            for b in samples:
                self.assertEqual(b / a, b * inv)

    def assert_raises_name(self, names, fn, *args, **kwargs):
        """Assert ``fn`` raises an exception whose class name is in ``names``.

        Used for ``pyo3_runtime.PanicException``, which is a ``BaseException``
        and cannot be imported by name.
        """
        if isinstance(names, str):
            names = (names,)
        try:
            with quiet_rust_panics():
                fn(*args, **kwargs)
        except BaseException as exc:  # noqa: BLE001 - classifying by name
            self.assertIn(type(exc).__name__, names, repr(exc))
        else:
            self.fail(f"expected one of {names}, but no exception was raised")

