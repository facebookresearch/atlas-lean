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
            "Algebra/README.md": "- [A lemma](a%20lemma.md): a card's description\n\n- [Groups][g]\n\n[g]: groups/README.md\n",
            "Algebra/a lemma.md": "# A lemma\n",
            "Algebra/groups/README.md": "## [Part 1](part-01/README.md)\n",
            "Algebra/groups/part-01/README.md": "- [Lagrange on $[0, 1]$](lagrange.md)\n",
            "Algebra/groups/part-01/lagrange.md": "# Lagrange\n",
        }), [])

    def test_unlisted_pages_fail_and_only_entries_list(self):
        self.assertEqual(self.check({
            "README.md": "# Root\n",
            "Algebra/README.md": ("- [A](a.md): see [B](b.md)\n\nProse links [C](c.md).\n\n`- [In code](d.md)`\n\n"
                                  "## Related topics\n\n- [E](e.md)\n"),
            "Algebra/a.md": "# A\n",
            "Algebra/b.md": "# B\n",
            "Algebra/c.md": "# C\n",
            "Algebra/d.md": "# D\n",
            "Algebra/e.md": "# E\n",
            "plain/c.md": "# C\n",
        }), [
            "Algebra/README.md: not listed on README.md",
            "Algebra/b.md: not listed on Algebra/README.md",
            "Algebra/c.md: not listed on Algebra/README.md",
            "Algebra/d.md: not listed on Algebra/README.md",
            "Algebra/e.md: not listed on Algebra/README.md",
            "plain/c.md: not listed on README.md",
        ])


if __name__ == "__main__":
    unittest.main()
