#!/usr/bin/env python3
"""Keep newer library roots visible in the curated blueprint taxonomy."""

import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
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

    def test_library_fallbacks_name_subjects(self):
        taxonomy = wiki.load_taxonomy()
        for library, folders in wiki.LIBRARIES.items():
            for folder, subject in folders.items():
                with self.subTest(folder=f"{library}/{folder}"):
                    self.assertIn(subject, taxonomy["subjects"])

    def test_a_folder_without_a_subject_waits_instead_of_stopping(self):
        # Upstream adds library folders often; until one gets a subject its modules get no pages.
        with tempfile.TemporaryDirectory() as root:
            module = Path(root, "MathlibExt", "BrandNewFolder", "Fact.lean")
            module.parent.mkdir(parents=True)
            module.write_text("/-- A fact. -/\ntheorem fact : True := trivial\n")
            taxonomy = {"subjects": {"Algebra": {}}, "placements": {}}
            with patch.object(wiki, "ROOT", Path(root)):
                targets, summary = wiki.load_library("MathlibExt", SimpleNamespace(declarations={}), taxonomy)
        self.assertEqual(targets, [])
        self.assertEqual(summary["unsubjected"], ["MathlibExt/BrandNewFolder/Fact.lean"])
        # The coverage still counts the waiting declaration.
        self.assertEqual((summary["public"], summary["documented"], summary["instances"]), (1, 1, 0))

    def test_field_and_subfield_slugs_are_unique(self):
        # A repeated slug would be silently ignored: the generator places topics on its first occurrence.
        taxonomy = wiki.load_taxonomy()
        for subject, entry in taxonomy["subjects"].items():
            fields = [field["slug"] for field in entry["fields"]]
            self.assertEqual(len(fields), len(set(fields)), subject)
            for field in entry["fields"]:
                subfields = [subfield["slug"] for subfield in field["subfields"]]
                self.assertEqual(len(subfields), len(set(subfields)), f"{subject}/{field['slug']}")

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
