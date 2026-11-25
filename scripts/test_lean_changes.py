#!/usr/bin/env python3
"""Regressions for scripts/lean_changes.py; standard library and git only, no Lean.

Run with: python3 -m unittest discover -s scripts -p test_lean_changes.py
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import lean_changes
from lean_changes import ChangedFile

DIFF = """\
diff --git a/MathlibExt/A.lean b/MathlibExt/A.lean
index 1111111..2222222 100644
--- a/MathlibExt/A.lean
+++ b/MathlibExt/A.lean
@@ -2 +2 @@ theorem a
-old
+new
@@ -5,0 +6,2 @@ theorem b
+added one
+added two
@@ -9,3 +10,0 @@ theorem c
-gone
-gone
-gone
diff --git a/MathlibExt/New.lean b/MathlibExt/New.lean
new file mode 100644
--- /dev/null
+++ b/MathlibExt/New.lean
@@ -0,0 +1,3 @@
+module
+
+theorem t : True := trivial
"""


def git(cwd: Path, *args: str) -> None:
    subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@example.com", *args],
                   cwd=cwd, check=True, capture_output=True)


class ParseTests(unittest.TestCase):
    def test_parse_diff_collects_added_lines(self):
        self.assertEqual(lean_changes.parse_diff(DIFF), {
            "MathlibExt/A.lean": frozenset({2, 6, 7}),
            "MathlibExt/New.lean": frozenset({1, 2, 3}),
        })

    def test_parse_name_status_handles_renames(self):
        text = "M\0MathlibExt/A.lean\0R087\0MathlibExt/B.lean\0MathlibExt/C.lean\0A\0Domains/D.lean\0"
        self.assertEqual(lean_changes.parse_name_status(text), {
            "MathlibExt/A.lean": "M", "MathlibExt/C.lean": "R", "Domains/D.lean": "A"})

    def test_changed_file_module_and_library(self):
        file = ChangedFile("CSLibExt/Algorithms/Sort.lean", "M", frozenset())
        self.assertEqual(file.library, "CSLibExt")
        self.assertEqual(file.module, "CSLibExt.Algorithms.Sort")

    def test_annotation_escapes_properties_and_message(self):
        self.assertEqual(
            lean_changes.annotation("warning", "MathlibExt/A,B.lean", 3, "linter.x: y",
                                    "50% off\nsecond line", col=7),
            "::warning file=MathlibExt/A%2CB.lean,line=3,col=7,title=linter.x%3A y"
            "::50%25 off%0Asecond line")

    def test_relative_accepts_absolute_and_relative_paths(self):
        root = Path("/repo")
        self.assertEqual(lean_changes.relative("/repo/MathlibExt/A.lean", root),
                         "MathlibExt/A.lean")
        self.assertEqual(lean_changes.relative("MathlibExt/A.lean", root), "MathlibExt/A.lean")


class GitTests(unittest.TestCase):
    def test_changed_files_reads_the_change_since_the_merge_base(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            git(root, "init", "-q", "-b", "main")
            (root / "MathlibExt").mkdir()
            (root / "MathlibExtTest").mkdir()
            (root / "MathlibExt/A.lean").write_text("a\nb\nc\n")
            (root / "MathlibExt/B.lean").write_text("".join(f"line {i}\n" for i in range(10)))
            (root / "MathlibExt/Gone.lean").write_text("x\n")
            (root / "MathlibExtTest/T.lean").write_text("t\n")
            git(root, "add", "-A")
            git(root, "commit", "-q", "-m", "base")
            git(root, "checkout", "-q", "-b", "change")
            (root / "MathlibExt/A.lean").write_text("a\nB\nc\nd\n")
            git(root, "mv", "MathlibExt/B.lean", "MathlibExt/C.lean")
            (root / "MathlibExt/C.lean").write_text(
                "".join(f"line {i}\n" for i in range(9)) + "changed\n")
            (root / "MathlibExt/D.lean").write_text("new\nfile\n")
            (root / "MathlibExt/Gone.lean").unlink()
            (root / "MathlibExtTest/T.lean").write_text("test\n")
            (root / "MathlibExt/notes.md").write_text("not Lean\n")
            git(root, "add", "-A")
            git(root, "commit", "-q", "-m", "change")
            files = lean_changes.changed_files("main", cwd=root)
        self.assertEqual(files, [
            ChangedFile("MathlibExt/A.lean", "M", frozenset({2, 4})),
            ChangedFile("MathlibExt/C.lean", "R", frozenset({10})),
            ChangedFile("MathlibExt/D.lean", "A", frozenset({1, 2})),
        ])


class AggregatorTests(unittest.TestCase):
    def test_writes_one_plain_aggregator_per_library_and_removes_it(self):
        files = [ChangedFile("MathlibExt/X/A.lean", "M", frozenset({1})),
                 ChangedFile("MathlibExt/B.lean", "A", frozenset({1})),
                 ChangedFile("Domains/C.lean", "M", frozenset({2}))]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "MathlibExt").mkdir()
            (root / "Domains").mkdir()
            with lean_changes.aggregators(files, cwd=root) as names:
                self.assertEqual(names, ["Domains.LintChanged", "MathlibExt.LintChanged"])
                self.assertEqual((root / "MathlibExt/LintChanged.lean").read_text(),
                                 "import MathlibExt.B\nimport MathlibExt.X.A\n")
                self.assertEqual((root / "Domains/LintChanged.lean").read_text(),
                                 "import Domains.C\n")
            self.assertEqual(sorted(os.listdir(root / "MathlibExt")), [])

    def test_refuses_to_overwrite_a_module(self):
        files = [ChangedFile("MathlibExt/B.lean", "A", frozenset({1}))]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "MathlibExt").mkdir()
            (root / "MathlibExt/LintChanged.lean").write_text("theorem kept : True := trivial\n")
            with self.assertRaises(FileExistsError):
                with lean_changes.aggregators(files, cwd=root):
                    pass
            self.assertIn("kept", (root / "MathlibExt/LintChanged.lean").read_text())


if __name__ == "__main__":
    unittest.main()
