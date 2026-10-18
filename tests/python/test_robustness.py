"""Inputs that must end in a Python exception, never in a dead interpreter.

Each probe runs in a child interpreter so a native stack overflow cannot take
the test runner down.  The probes that currently crash are marked
``expectedFailure`` and describe the contract they violate; once the Rust side
reports an error (or evaluates iteratively) they flip to "unexpected success"
and the marker should be removed.
"""

import os
import subprocess
import sys
import textwrap
import unittest

import ogdoad as og

from _support import OgdoadTestCase

POSIX = os.name == "posix"


def run_child(body, timeout=120):
    """Run ``body`` in a fresh isolated interpreter.

    The child prints ``OK <detail>`` when the call returns and
    ``EXC <ExceptionName>`` when it raises a Python exception; a crash shows up
    as a non-zero (on POSIX, negative) return code and no output.
    """
    code = "import ogdoad as og\ntry:\n" + textwrap.indent(textwrap.dedent(body), "    ") + (
        "\nexcept BaseException as exc:\n    print('EXC', type(exc).__name__)\n")
    kwargs = {}
    if POSIX:
        def no_core_dumps():
            import resource
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        kwargs["preexec_fn"] = no_core_dumps
    return subprocess.run([sys.executable, "-I", "-c", code], capture_output=True,
                          text=True, timeout=timeout, **kwargs)


def survived(proc):
    return proc.returncode == 0 and proc.stdout.strip().split(" ")[0] in ("OK", "EXC")


@unittest.skipUnless(POSIX, "native-crash probes assume POSIX signals")
class ChildHarnessTests(OgdoadTestCase):
    def test_harness_reports_ok_and_exceptions(self):
        ok = run_child("print('OK', og.version())")
        self.assertTrue(survived(ok), (ok.returncode, ok.stdout, ok.stderr))
        bad = run_child("og.Nimber(2**200)")
        self.assertTrue(survived(bad), (bad.returncode, bad.stdout, bad.stderr))
        self.assertEqual(bad.stdout.strip(), "EXC OverflowError")

    def test_harness_detects_a_dead_child(self):
        dead = run_child("import os, signal; os.kill(os.getpid(), signal.SIGSEGV)")
        self.assertFalse(survived(dead))


@unittest.skipUnless(POSIX, "native-crash probes assume POSIX signals")
class GraphKernelsAreIterativeTests(OgdoadTestCase):
    """Control group: the explicit-graph entry points handle large inputs."""

    def test_long_chains_and_cycles_are_handled_in_process(self):
        n = 100_000
        chain = [[i - 1] if i else [] for i in range(n)]
        self.assertEqual(og.grundy_graph(chain)[-1], (n - 1) % 2)
        self.assertEqual(len(og.outcomes(chain)), n)
        with self.assertRaises(ValueError):
            og.grundy_graph([[(i + 1) % 1000] for i in range(1000)])

    def test_chain_values_alternate(self):
        values = og.grundy_graph([[i - 1] if i else [] for i in range(50_001)])
        self.assertEqual(values[:6], [0, 1, 0, 1, 0, 1])
        self.assertEqual(values[-1], 50_000 % 2)


@unittest.skipUnless(POSIX, "native-crash probes assume POSIX signals")
class CallbackRecursionTests(OgdoadTestCase):
    def test_cyclic_grundy_callback_is_an_error_not_a_crash(self):
        # ``grundy`` needs an acyclic game; a cyclic callback raises ValueError,
        # as ``grundy_graph`` and ``misere_is_n`` do.
        proc = run_child("print('OK', og.grundy(3, lambda h: [h]))")
        self.assertEqual(proc.stdout.strip(), "EXC ValueError", (proc.returncode, proc.stderr))

    def test_deep_acyclic_grundy_callback_does_not_overflow_the_native_stack(self):
        # The callback evaluator is iterative, so a long legal chain (here
        # 1,000,000 positions) needs no native stack.
        proc = run_child("print('OK', og.grundy(1_000_000, lambda h: [h - 1] if h else []))")
        self.assertEqual(proc.stdout.strip(), "OK 0", (proc.returncode, proc.stderr))

    def test_deep_misere_callback_does_not_overflow_the_native_stack(self):
        # Misère: the terminal heap is N, so even chain lengths are N.
        proc = run_child("print('OK', og.misere_is_n(1_000_000, lambda h: [h - 1] if h else []))")
        self.assertEqual(proc.stdout.strip(), "OK True", (proc.returncode, proc.stderr))

    @unittest.expectedFailure
    def test_deeply_nested_game_values_do_not_overflow_the_native_stack(self):
        # BUG (core/bindings): Game trees are recursive Rust values, so
        # ``Game.integer(n)`` (depth n) aborts the interpreter for large n --
        # in the unoptimised dev build already at n = 6000.
        proc = run_child("print('OK', og.Game.integer(1_000_000).birthday())")
        self.assertTrue(survived(proc), (proc.returncode, proc.stdout))


if __name__ == "__main__":
    unittest.main()
