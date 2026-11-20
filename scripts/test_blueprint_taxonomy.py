#!/usr/bin/env python3
"""Keep newer library roots visible in the curated blueprint taxonomy."""

import re
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

    def test_module_private_declarations_get_no_page_and_no_count(self):
        # In a `module` file a declaration outside `public section` is private: no page, no count. A declaration
        # written `public`, one in a `public section`, and a wanted command (a private placeholder anyway) stay.
        with tempfile.TemporaryDirectory() as root:
            module = Path(root, "MathlibExt", "Algebra", "Fact.lean")
            module.parent.mkdir(parents=True)
            module.write_text("/- Copyright. -/\nmodule\n\npublic import Mathlib.Logic.Basic\n\n"
                              "/-- A helper. -/\ntheorem helper : True := trivial\n\n"
                              "/-- Hidden. -/\nprivate theorem hidden : True := trivial\n\n"
                              "/-- Exported. -/\npublic theorem exported : True := trivial\n\n"
                              "/-- Asked for. -/\ntheorem_wanted asked : True\n\n"
                              "public section\n\n/-- A result. -/\ntheorem result : True := trivial\n\nend\n")
            taxonomy = {"subjects": {"Algebra": {}}, "placements": {}}
            path = Path("MathlibExt/Algebra/Fact.lean")
            text = module.read_text().splitlines()
            declarations = {}
            for number, line in enumerate(text):
                head = re.match(r"(?:private |public )?(theorem_wanted|theorem) (\w+)", line)
                if head:
                    declarations[head.group(2)] = SimpleNamespace(path=path, line=number + 1, keyword=head.group(1), name=head.group(2))
            index = SimpleNamespace(declarations=declarations)
            with patch.object(wiki, "ROOT", Path(root)):
                targets, summary = wiki.load_library("MathlibExt", index, taxonomy)
        self.assertEqual([target.names[0] for target in targets], ["exported", "asked", "result"])
        self.assertEqual((summary["public"], summary["documented"]), (3, 3))

    def test_module_private_lines(self):
        def private(text):
            lines = text.split("\n")
            return [line.strip() for number, line in enumerate(lines)
                    if number in wiki.module_private_lines(lines) and line.strip().startswith(("theorem", "def"))]

        # Not a module: nothing is private by visibility.
        self.assertEqual(private("theorem a : True := trivial"), [])
        # Scopes nest; a `public section` makes everything in it public, through namespaces, sections and mutual.
        text = ("/-! Doc. -/\nmodule\ntheorem a : True := trivial\n@[expose] public section\nnamespace N\n"
                "theorem b : True := trivial\nsection\ntheorem c : True := trivial\nend\nmutual\n"
                "  def d : Nat := 0\nend\ntheorem e : True := trivial\nend N\nend\ntheorem f : True := trivial\n"
                "public noncomputable section\ndef g : Nat := 0\nend\nnoncomputable section\ndef h : Nat := 0\nend")
        self.assertEqual(private(text), ["theorem a : True := trivial", "theorem f : True := trivial", "def h : Nat := 0"])
        # Scope commands in comments and strings are text.
        text = 'module\n/- public section -/\ntheorem a : True := trivial\ndef s : String := "\npublic section"\ndef t : Nat := 0'
        self.assertEqual(private(text), ["theorem a : True := trivial", 'def s : String := "', "def t : Nat := 0"])
        # A dotted name opens and closes one scope per component, as in Lean.
        text = ("module\npublic section\nnamespace Outer.Inner\ndef first : Nat := 1\nend Inner\ndef second : Nat := 2\n"
                "end Outer\ndef third : Nat := 3\nend\ndef fourth : Nat := 4\nnamespace A.B\npublic section C.D\n"
                "def fifth : Nat := 5\nend C.D\ndef sixth : Nat := 6\nend A.B")
        self.assertEqual(private(text), ["def fourth : Nat := 4", "def sixth : Nat := 6"])
        # An `end` with nothing to close, or a quoted scope name: fail open, nothing is private.
        self.assertEqual(private("module\ntheorem a : True := trivial\nend\ntheorem b : True := trivial"), [])
        self.assertEqual(private("module\ntheorem a : True := trivial\nnamespace A.B\nend A.B.C\ntheorem b : True := trivial"), [])
        # A quoted name is one component; a quote left open fails open.
        self.assertEqual(private("module\nnamespace «A.B»\ntheorem a : True := trivial\nend «A.B»"), ["theorem a : True := trivial"])
        self.assertEqual(private("module\nnamespace «A.B\ntheorem a : True := trivial\nend"), [])

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
