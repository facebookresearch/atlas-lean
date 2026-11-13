#!/usr/bin/env python3
"""Keep newer library roots visible in the curated blueprint taxonomy."""

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import generate_wiki as wiki
from scripts import sync_wiki


class BlueprintTaxonomyTests(unittest.TestCase):
    def test_new_library_roots_have_valid_fallback_subjects(self):
        taxonomy = wiki.load_taxonomy()
        cases = {
            "MathlibExt": ("Economics", "Quantum"),
            "CSLibExt": ("Privacy", "Tactic"),
            "PhyslibExt": (
                "Chemistry", "ClassicalMechanics", "EarthScience",
                "Electromagnetism", "Quantum", "Units",
            ),
        }
        for library, roots in cases.items():
            for root in roots:
                with self.subTest(library=library, root=root):
                    subject = wiki.LIBRARIES[library].get(root, root)
                    self.assertIn(subject, taxonomy["subjects"])

    def test_every_subject_is_in_exactly_one_region(self):
        taxonomy = wiki.load_taxonomy()
        subjects = [subject for group in taxonomy["regions"].values()
                    for subject in group]
        self.assertEqual(len(subjects), len(set(subjects)))
        self.assertEqual(set(subjects), set(taxonomy["subjects"]))

    def test_refresh_catalog_preserves_editorial_articles(self):
        with tempfile.TemporaryDirectory() as directory:
            vault = Path(directory)
            article = vault / "roadmap" / "article.md"
            article.parent.mkdir()
            article.write_text("# Editorial article\n\nKeep this prose.\n")
            atlas = vault / "atlas.json"
            coverage = vault / "coverage" / "README.md"
            generated = {
                atlas: '{"schema": "autoform-atlas/v1", "areas": {}}\n',
                coverage: "# Updated coverage\n",
                article: "# Do not replace editorial prose\n",
            }
            with patch.object(wiki, "VAULT", vault):
                sync_wiki.refresh_catalog(generated)
            self.assertEqual(atlas.read_text(), generated[atlas])
            self.assertEqual(coverage.read_text(), generated[coverage])
            self.assertEqual(article.read_text(),
                             "# Editorial article\n\nKeep this prose.\n")

    def test_new_subjects_use_explicit_unclassified_topics(self):
        taxonomy = wiki.load_taxonomy()
        for subject in ("Economics", "Physics", "Chemistry", "EarthScience"):
            with self.subTest(subject=subject):
                target = wiki.Target(
                    book="PhyslibExt", idx=0, title="Example", slug="example",
                    location=subject, description="A statement.",
                    declaration="theorem", lean=None, statement=False,
                    proof=False, names=["example"],
                    module=("PhyslibExt", subject, "Example"),
                )
                tree = wiki.subject_tree(subject, [target], taxonomy)
                self.assertEqual(tree.children[0].slug,
                                 wiki.UNPLACED["slug"])


if __name__ == "__main__":
    unittest.main()
