#!/usr/bin/env python3
"""Tests for scripts/check_folder_listings.py."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from scripts.check_folder_listings import unlisted


class FolderListingTests(unittest.TestCase):
    def check(self, files: dict[str, str]) -> list[str]:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name, text in files.items():
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                (root / name).write_text(text, encoding="utf-8")
            return unlisted(root)

    def test_listed_pages_and_folders_pass(self):
        self.assertEqual(self.check({
            "README.md": "- [Algebra](Algebra/)\n",
            "Algebra/README.md": "- [A lemma](a%20lemma.md)\n\n[Groups][g]\n\n[g]: groups/README.md\n",
            "Algebra/a lemma.md": "# A lemma\n",
            "Algebra/groups/README.md": "- [Lagrange](lagrange.md)\n",
            "Algebra/groups/lagrange.md": "# Lagrange\n",
        }), [])

    def test_unlisted_pages_fail_and_code_does_not_list(self):
        self.assertEqual(self.check({
            "README.md": "# Root\n",
            "Algebra/README.md": "`[In code](b.md)`\n",
            "Algebra/b.md": "# B\n",
            "plain/c.md": "# C\n",
        }), [
            "Algebra/README.md: not listed on README.md",
            "Algebra/b.md: not listed on Algebra/README.md",
            "plain/c.md: not listed on README.md",
        ])

    def test_the_required_graph_job_runs_both_checks(self):
        job = Path(__file__).resolve().parent.parent.joinpath(".github/workflows/ci.yml").read_text()
        job = job.split("\n  graph:\n", 1)[1].split("\n  build:\n", 1)[0]
        self.assertIn("autoform check blueprint --lean-root .", job)
        self.assertIn("python scripts/check_folder_listings.py", job)


if __name__ == "__main__":
    unittest.main()
