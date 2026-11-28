"""Regression tests for scripts/tech_debt.py; no Lean is invoked."""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import tech_debt  # noqa: E402

LOG = """\
2026-11-25T06:57:07.1Z \x1b[33m⚠ [1/3] Replayed MathlibExt.A\x1b[0m
2026-11-25T06:57:07.1Z warning: MathlibExt/A.lean:3:6: Unused tactic linter: `try` can be removed.
2026-11-25T06:57:07.1Z
2026-11-25T06:57:07.1Z Note: This linter can be disabled with `set_option linter.unusedTactic false`
2026-11-25T06:57:07.1Z warning: MathlibExt/A.lean:9:2: `Nat.foo` has been deprecated: use `Nat.bar` instead
2026-11-25T06:57:07.1Z warning: CSLibExt/B.lean: imports `Mathlib.X` from package `mathlib`, which is fine
2026-11-25T06:57:07.1Z warning: CSLibExt/B.lean:1:0: 'Mathlib.Data.Real.Basic' has been deprecated: use Real
⚠ [2/3] Replayed MathlibExt.A
warning: MathlibExt/A.lean:3:6: Unused tactic linter: `try` can be removed.

Note: This linter can be disabled with `set_option linter.unusedTactic false`
"""


class WarningCounts(unittest.TestCase):
    def test_groups_by_linter_and_library_once_per_warning(self):
        by_linter, by_library = tech_debt.warning_counts(LOG.splitlines(keepends=True))
        self.assertEqual(dict(by_linter), {
            "linter.unusedTactic": 1,
            "deprecated declaration used": 1,
            "other: imports … from package": 1,
            "deprecated module imported": 1,
        })
        self.assertEqual(dict(by_library), {"MathlibExt": 2, "CSLibExt": 2})


class SourceCounts(unittest.TestCase):
    def test_counts_tracked_library_files_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "MathlibExt").mkdir()
            (root / "MathlibExtTest").mkdir()
            (root / "MathlibExt" / "A.lean").write_text(
                "open Classical\nopen Classical in\nopen ClassicalFoo\nset_option maxHeartbeats 400000 in\ntheorem t : True := by\n  erw [x]\n",
                encoding="utf-8")
            (root / "MathlibExt" / "Untracked.lean").write_text("erw [y]\n", encoding="utf-8")
            (root / "MathlibExtTest" / "T.lean").write_text("erw [z]\nexample : True := by native_decide\n",
                                                             encoding="utf-8")
            (root / "provenance" / "formal-math-sync.d").mkdir(parents=True)
            (root / "provenance" / "formal-math-sync.json").write_text('{"schema_version": 2}', encoding="utf-8")
            (root / "provenance" / "formal-math-sync.d" / "MathlibExt.json").write_text(json.dumps({"rows": [
                {"path": "MathlibExt/A.lean", "disposition": "diverged", "backport": "pending"},
                {"path": "MathlibExt/B.lean", "disposition": "identical"}]}), encoding="utf-8")
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "-C", str(root), "add", "MathlibExt/A.lean", "MathlibExtTest/T.lean"], check=True)
            counts = tech_debt.source_counts(root)
        self.assertEqual(counts["`erw` rewrites"], 1)
        self.assertEqual(counts["`maxHeartbeats` raises"], 1)
        self.assertEqual(counts["top-level `open Classical`"], 1)
        self.assertEqual(counts["`native_decide` in tests"], 1)
        self.assertEqual(counts["Formal-Math divergences with a pending backport"], 1)
        self.assertEqual(counts["`TODO` and `FIXME` comments"], 0)


class Markdown(unittest.TestCase):
    def test_reports_changes_against_a_base(self):
        new = {"commit": "b" * 40, "source": {"`erw` rewrites": 3},
               "warnings": {"total": 5, "by_linter": {"linter.flexible": 5}, "by_library": {"MathlibExt": 5}}}
        old = {"commit": "a" * 40, "source": {"`erw` rewrites": 4},
               "warnings": {"total": 2, "by_linter": {"linter.flexible": 2}, "by_library": {"MathlibExt": 2}}}
        text = tech_debt.markdown(new, old)
        self.assertIn("compared with `aaaaaaaaaa`", text)
        self.assertIn("| 3 | -1 | `erw` rewrites |", text)
        self.assertIn("Compiler warnings: 5 (+3).", text)
        self.assertIn("| 5 | +3 | `linter.flexible` |", text)
        self.assertNotIn("| -1 |", tech_debt.markdown(new, None))


if __name__ == "__main__":
    unittest.main()
