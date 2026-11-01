"""Fixture tests for the Week 2 CI scripts; never invokes Lean."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def run(script, *args):
    return subprocess.run(
        [sys.executable, str(ROOT / script), *args],
        capture_output=True, text=True, check=False)


class Week2CITests(unittest.TestCase):
    def test_duplicate_and_semantic_conflict(self):
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            (d / "a.lean").write_text(
                "namespace A\n"
                "def Foo (x : Nat) : Nat := x + 1\n"
                "def IsStable (p : Nat) : Prop := p = 0\n"
                "theorem_wanted bar_baz : True\n"
                "end A\n")
            (d / "b.lean").write_text(
                "namespace B\n"
                "def Foo (x : Nat) : Nat := x + 1\n"
                "def IsStable (mu : String) : Prop := True\n"
                "end B\n")
            (d / "c.lean").write_text(
                "namespace C\nabbrev Foo := A.Foo\nend C\n")
            result = run("check_duplicate_defs.py", str(d))
            self.assertEqual(result.returncode, 1)
            self.assertIn("BLOCK duplicate: Foo", result.stdout)
            self.assertIn("BLOCK semantic-conflict: IsStable", result.stdout)
            # Alias shim file must not count as a third home for Foo.
            self.assertNotIn("3 files", result.stdout)

    def test_hypothesis_debt(self):
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            (d / "a.lean").write_text("theorem_wanted bar_baz : True\n")
            result = run("check_hypothesis_debt.py", str(d))
            self.assertEqual(result.returncode, 0)
            self.assertIn("DEBT", result.stdout)
            self.assertIn("Total debt items: 1", result.stdout)


if __name__ == "__main__":
    unittest.main()
