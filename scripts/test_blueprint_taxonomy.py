#!/usr/bin/env python3
"""Keep newer library roots visible in the curated blueprint taxonomy."""

import json
import re
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from scripts import generate_wiki as wiki
from scripts import sync_wiki


class BlueprintTaxonomyTests(unittest.TestCase):
    # A PR that changes only scripts/taxonomy.json or scripts/wiki-sync.json skips the site's build and runs these
    # tests alone: the next ones read the committed files as the build and the declarations sync do.
    def test_every_committed_placement_names_a_field_or_subfield_of_its_subject(self):
        # The generator and the importer read every placement's `to` and `title` (placement, topic_folders), the
        # title being a topic's one-line name, and the generator refuses a subject that places topics in fields it does
        # not have (subject_tree); a topic may also wait in its subject's not-yet-classified folder.
        taxonomy = wiki.load_taxonomy()
        wrong = []
        for key, spot in sorted(taxonomy["placements"].items()):
            title = spot.get("title")
            if not isinstance(spot.get("to"), str) or not isinstance(title, str) or not title.strip() \
                    or title.splitlines() != [title]:
                wrong.append((key, "a `to` and a one-line `title`"))
                continue
            subject, _, rest = spot["to"].partition("/")
            if subject not in taxonomy["subjects"]:
                wrong.append((key, spot["to"]))
                continue
            fields = taxonomy["subjects"][subject].get("fields", [])
            known = {wiki.UNPLACED["slug"], *(field["slug"] for field in fields),
                     *(f"{field['slug']}/{sub['slug']}" for field in fields for sub in field.get("subfields", []))}
            if rest not in known:
                wrong.append((key, spot["to"]))
        self.assertEqual(wrong, [])

    def test_every_subject_field_and_subfield_names_a_path_of_the_site_and_describes_itself(self):
        # Each names a folder of the wiki and a page of the site, in the grammar of docs/mathgraph-import.md's page
        # folders (a subject's capital also keeps it apart from the Mathlib pages' own `outside` page), and the
        # generator reads its `description` (subject_tree), which may be empty.
        taxonomy = wiki.load_taxonomy()

        def named(component, grammar, spec, suffix=""):
            # A file or folder name is at most 255 bytes: a subject's annotations are `<subject>.jsonl`
            # (sync_wiki.links_file).
            return bool(re.fullmatch(grammar, component)) and len((component + suffix).encode()) <= 255 \
                and isinstance(spec.get("description"), str)

        slug = r"[a-z0-9]+(?:-[a-z0-9]+)*"
        wrong = []
        for subject, entry in taxonomy["subjects"].items():
            if not named(subject, r"[A-Z][A-Za-z]*", entry, ".jsonl"):
                wrong.append(subject)
            for field in entry.get("fields", []):
                path = f"{subject}/{field['slug']}"
                if not named(field["slug"], slug, field):
                    wrong.append(path)
                wrong += [f"{path}/{sub['slug']}" for sub in field.get("subfields", [])
                          if not named(sub["slug"], slug, sub)]
        self.assertEqual(wrong, [])

    def test_the_committed_taxonomy_writes_as_utf8(self):
        # The build writes its titles, descriptions and reasons into UTF-8 files: a lone surrogate would stop it.
        json.dumps(wiki.load_taxonomy(), ensure_ascii=False).encode("utf-8")

    def test_the_committed_docstring_baseline_reads_as_the_sync_reads_it(self):
        # The declarations sync, which Graph sync runs on every PR, reads json.loads(STATE.read_text())["docstrings"]:
        # declaration names mapped to strings.
        state = json.loads(sync_wiki.STATE.read_text())["docstrings"]
        self.assertIsInstance(state, dict)
        self.assertEqual([key for key, value in state.items() if not isinstance(value, str)], [])
        # The sync writes it back as UTF-8.
        json.dumps(state, ensure_ascii=False).encode("utf-8")

    def test_new_library_roots_have_valid_fallback_subjects(self):
        taxonomy = wiki.load_taxonomy()
        cases = {
            "MathlibExt": ("Economics", "Quantum"),
            "Domains": ("Biology", "Chemistry", "Economics", "MaterialsScience", "OperationsResearch", "Transport", "Urban"),
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

    def test_extracted_declarations_are_published_in_their_source_field(self):
        # A stable Lean name may retain its original namespace after the source module moves.
        # Index the actual modules: other declarations in those namespaces still belong to Biology.
        cases = {
            "MathlibExt/Probability/Causality/PotentialOutcomes": "Probability/nonparametric-survival",
            "MathlibExt/Probability/ChineseRestaurant": "Probability/bayesian-statistics",
            "MathlibExt/Combinatorics/SimpleGraph/TreeMetric": "GraphTheory/graph-families-and-operations",
            "Domains/Biology/StatisticalGenetics/MendelianRandomization": "Biology/statistical-genetics",
        }
        placements = wiki.load_taxonomy()["placements"]
        annotations = sync_wiki.read_annotations()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for module, field in cases.items():
                with self.subTest(module=module):
                    self.assertEqual(placements[module]["to"], field)
                path = Path(module + ".lean")
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_bytes((wiki.ROOT / path).read_bytes())
            index = wiki.index_project(root)

        covered = set()
        seen = set()
        for shard, rows in annotations.items():
            for row in rows:
                name = sync_wiki.lean_name(row)
                if name not in index.declarations:
                    continue
                module = index.declarations[name].path.with_suffix("").as_posix()
                page = sync_wiki.subject_path(row)
                with self.subTest(name=name):
                    self.assertNotIn(name, seen)
                    self.assertTrue(page.is_file(), page)
                    self.assertTrue(page.is_relative_to(wiki.ROADMAP / cases[module]), page)
                    self.assertEqual(shard, sync_wiki.links_file(page))
                covered.add(module)
                seen.add(name)
        self.assertEqual(covered, set(cases))

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
