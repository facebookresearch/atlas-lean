"""The committed wiki keeps its own text, and lean-facts adds only what the Lean decides."""

from __future__ import annotations

import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from scripts import extract_v2_lean_dependencies as extract
from scripts import generate_wiki as wiki
from scripts import sync_wiki as sync

# The ids of rows a test unlinks or keeps: every committed row has one (What the tools own), and lean-facts keeps it.
UNLINKED, KEPT = "af_0000000000000000000000a1", "af_0000000000000000000000a2"
# lean-facts' own test of its checkout: the vaults below stand for a clean checkout, and CleanCheckout runs it.
CHECKOUT_PROBLEM = sync.checkout_problem


def duplicates_digest() -> str:
    """The digest of the vault's duplicates lists, as a registry made for its rows records it."""
    return extract.aliases_digest(sync.listed_duplicates(sync.read_annotations())[0])


def paired(registry: object, dependency_file: Path) -> object:
    """A registry as the extractor writes it beside *dependency_file*: with that extraction's digest."""
    if isinstance(registry, dict) and isinstance(registry.get("inputs"), dict):
        digest = hashlib.sha256(dependency_file.read_bytes()).hexdigest()
        return {**registry, "inputs": {"extraction_sha256": digest, **registry["inputs"]}}
    return registry


class Sections(unittest.TestCase):
    def test_lean_sections_go_and_sources_stay(self) -> None:
        body = "# T\n\nStatement.\n\n## Depends on\n\n- [A](a.md)\n\n## Proof depends on\n\n- [B](b.md)\n\n## Sources\n\n- Book.\n"
        self.assertEqual(sync.without_sections(body, sync.LEAN_SECTIONS), "# T\n\nStatement.\n\n## Sources\n\n- Book.\n")

    def test_the_statement_keeps_its_blank_lines(self) -> None:
        # Two display formulas in a row are written with two blank lines between them.
        body = "# T\n\n$$a$$\n\n\n\n$$b$$\n\n## Depends on\n\n- [A](a.md)\n"
        self.assertEqual(sync.without_sections(body, sync.LEAN_SECTIONS), "# T\n\n$$a$$\n\n\n\n$$b$$\n")

    def test_sections_go_before_sources(self) -> None:
        body = "# T\n\nStatement.\n\n## Sources\n\n- Book.\n"
        self.assertEqual(
            sync.with_sections(body, [("Depends on", ["- [A](a.md)"])]),
            "# T\n\nStatement.\n\n## Depends on\n\n- [A](a.md)\n\n## Sources\n\n- Book.\n",
        )

    def test_sections_end_an_article_without_sources(self) -> None:
        self.assertEqual(
            sync.with_sections("# T\n\nStatement.\n", [("Depends on", ["This node has no prerequisites."])]),
            "# T\n\nStatement.\n\n## Depends on\n\nThis node has no prerequisites.\n",
        )

    def test_writing_twice_changes_nothing(self) -> None:
        once = sync.with_sections("# T\n\nStatement.\n", [("Depends on", ["- [A](a.md)"])])
        self.assertEqual(sync.with_sections(once, [("Depends on", ["- [A](a.md)"])]), once)


class TitleLead(unittest.TestCase):
    def test_a_bold_restatement_of_the_title_goes(self) -> None:
        for body in ("**Hasse bound.** The bound holds.\n", "**Hasse bound**. The bound holds.\n",
                     "**Hasse bound**\nThe bound holds.\n", "**hasse  bound:** The bound holds.\n"):
            self.assertEqual(sync.without_title_lead("Hasse bound", body), "The bound holds.\n", body)
        self.assertEqual(sync.without_title_lead("The map ℤ(∞)", "**The map ℤ[∞].** For a set.\n"), "For a set.\n")
        for body in ("**Hasse bound**: the bound holds.\n", "**Hasse bound:** the bound holds.\n"):
            self.assertEqual(sync.without_title_lead("Hasse bound", body), "The bound holds.\n", body)

    def test_anything_else_stays_as_written(self) -> None:
        for title, body in (("Hasse bound", "**Hasse bound** is a bound.\n"), ("Hasse bound", "**Weil bound.** It holds.\n"),
                            ("Hasse bound", "**Hasse bound.** and more.\n"), ("Hasse bound", "**Hasse bound.**\n\n## Sources\n"),
                            ("Hasse bound", "The bound holds.\n")):
            self.assertEqual(sync.without_title_lead(title, body), body, body)


class Vault(unittest.TestCase):
    """A temporary blueprint/ the module's paths point into."""

    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp()).resolve()
        vault = self.tmp / "blueprint"
        patches = [
            patch.object(wiki, "ROOT", self.tmp),
            patch.object(wiki, "VAULT", vault),
            patch.object(wiki, "ROADMAP", vault / "roadmap"),
            patch.object(wiki, "PAGE_MAP", vault / "pages.json"),
            patch.object(sync, "LINKS", vault / "links"),
            patch.object(sync, "STATE", self.tmp / "wiki-sync.json"),
            patch.object(sync, "checkout_problem", lambda: None),
        ]
        for one in patches:
            one.start()
            self.addCleanup(one.stop)

    def annotate(self, rows: list[dict]) -> None:
        self.links_folder()
        sync.write_annotations({sync.LINKS / "Algebra.jsonl": rows})

    def links_folder(self) -> None:
        """The links folder with the defaults file the repository's has, which Autoform merges every row over."""
        sync.LINKS.mkdir(parents=True, exist_ok=True)
        if not (sync.LINKS / "_defaults.json").exists():
            (sync.LINKS / "_defaults.json").write_text(json.dumps(sync.DEFAULTS) + "\n")

    def assert_ids_kept(self, ids: list[str]) -> None:
        """Each row of Algebra.jsonl, as written, still has its id, right after its subject (What the tools own)."""
        rows = [json.loads(line) for line in (sync.LINKS / "Algebra.jsonl").read_text().splitlines() if line.strip()]
        self.assertEqual([(list(row)[:2], row.get("id")) for row in rows], [(["subject", "id"], i) for i in ids])

    def about(self, relative: str, **fields) -> dict:
        return {"subject": [{"type": "generic", "uri": f"../roadmap/{relative}"}], **fields}

    def page(self, relative: str, text: str) -> Path:
        path = wiki.ROADMAP / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path


class Seed(Vault):
    def test_facts_move_to_annotations_and_text_stays(self) -> None:
        article = wiki.ROADMAP / "Algebra" / "groups" / "lagrange.md"
        wanted = wiki.ROADMAP / "Algebra" / "groups" / "conjecture.md"
        field = wiki.ROADMAP / "Algebra" / "groups" / "README.md"
        files = {
            article: "---\narticle_id: af_000000000000000000000001\ndeclaration: theorem\norigin: cited\n"
            "statement: formalized\nproof: formalized\nlean: Ext.lagrange\n---\n\n# Lagrange's theorem\n\nIt divides.\n\n"
            "## Depends on\n\n- [Conjecture](conjecture.md)\n\n## Sources\n\n- [Book](https://example.org)\n",
            wanted: "---\ndeclaration: theorem\n---\n\n# Conjecture\n\nOpen.\n\n## Depends on\n\nThis node has no prerequisites.\n",
            field: "---\nnavigation: module\n---\n\n# Groups\n\n- [Lagrange's theorem](lagrange.md)\n",
            wiki.VAULT / "atlas.json": "{}\n",
            wiki.PAGE_MAP: "{}\n",
        }
        targets = [
            SimpleNamespace(path=article, lean="Ext.lagrange", module=("Ext", "Groups"), names=["Ext.lagrange"]),
            SimpleNamespace(path=wanted, lean=None, module=("Ext", "Groups"), names=["conjecture"]),
        ]

        def generate(titles, dependency_file, out):
            out.extend(targets)
            return files

        with patch.object(wiki, "generate", generate):
            pages, annotations = sync.seed({}, Path("deps.json"))
        self.assertEqual(pages[article], "# Lagrange's theorem\n\nIt divides.\n\n## Sources\n\n- [Book](https://example.org)\n")
        self.assertEqual(pages[wanted], "# Conjecture\n\nOpen.\n")
        self.assertEqual(pages[field], "# Groups\n\n- [Lagrange's theorem](lagrange.md)\n")
        self.assertNotIn(wiki.PAGE_MAP, pages)
        self.assertEqual(pages[wiki.VAULT / "atlas.json"], "{}\n")
        rows = annotations[sync.LINKS / "Algebra.jsonl"]
        self.assertEqual(rows, [
            {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/README.md"}],
             "extensions": {"org.autoform": {"navigation": "module"}}},
            {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/conjecture.md"}]},
            {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/lagrange.md"}],
             "object": [{"location": {"declaration": "Ext.lagrange"}}],
             "id": "af_000000000000000000000001",
             "extensions": {"org.autoform": {"origin": "cited"}}},
        ])


class LeanFacts(Vault):
    def test_unlinked_docstring_provenance_stays_editorial(self) -> None:
        page = self.page("Algebra/unlinked.md", "# Unlinked\n\nKeep the edited statement.\n")
        annotation = self.about("Algebra/unlinked.md", id="af_unlinked",
                                extensions={sync.OWN: {"from": "docstring"}})
        self.annotate([annotation])
        index = SimpleNamespace(declarations={})
        for _ in range(2):
            counts, unlinked = sync.apply_lean_facts(index, {})
            # A page whose annotation names no declaration is planned, not unresolved.
            self.assertEqual(counts, {"articles": 0, "unresolved": 0, "edges": 0, "mathlib": 0})
            self.assertEqual(unlinked, [])
            self.assertEqual(page.read_text(), "# Unlinked\n\nKeep the edited statement.\n")
        row = sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][0]
        self.assertEqual(row, annotation)
        self.assertIsNone(sync.annotation_key(row))

    def test_incomplete_private_target_metadata_has_no_source_key(self) -> None:
        for own in ({"from": "docstring"}, {"module": "Ext.Groups"}, {"name": "missing"}):
            with self.subTest(own=own):
                self.assertEqual(sync.lean_facts_for(None, own,
                                                   SimpleNamespace(declarations={}),
                                                   lambda _: False), (None, None))
                self.assertIsNone(sync.annotation_key({"extensions": {sync.OWN: own}}))

    def test_kinds_statuses_and_dependencies(self) -> None:
        source = self.tmp / "Ext" / "Groups.lean"
        source.parent.mkdir(parents=True)
        source.write_text("theorem lagrange : True := trivial\ndef order := 1\ntheorem_wanted conjecture : True\n")
        sorry_source = self.tmp / "Ext" / "Open.lean"
        sorry_source.write_text("theorem hard : True := sorry\ndef partial := sorry\n")
        lagrange = self.page("Algebra/lagrange.md", "# Lagrange's theorem\n\nIt divides.\n\n## Sources\n\n- Book.\n")
        order = self.page("Algebra/order.md", "# Order\n\nA number.\n")
        hard = self.page("Algebra/hard.md", "# Hard\n\nSorry.\n")
        partial = self.page("Algebra/partial.md", "# Partial\n\nSorry.\n")
        conjecture = self.page("Algebra/conjecture.md", "# Conjecture\n\nOpen.\n")
        self.page("Algebra/README.md", "# Algebra\n\n- [Order](order.md)\n")
        self.annotate([
            self.about("Algebra/README.md", extensions={"org.autoform": {"navigation": "module"}}),
            self.about("Algebra/lagrange.md", object=[{"location": {"declaration": "Ext.lagrange"}}]),
            self.about("Algebra/order.md", object=[{"location": {"declaration": "Ext.order"}}]),
            self.about("Algebra/hard.md", object=[{"location": {"declaration": "Ext.hard"}}]),
            self.about("Algebra/partial.md", object=[{"location": {"declaration": "Ext.partial"}}]),
            self.about("Algebra/conjecture.md", extensions={"org.atlas-wiki": {"module": "Ext.Groups", "name": "conjecture"}}),
        ])
        declarations = {
            "Ext.lagrange": SimpleNamespace(keyword="theorem", path=Path("Ext/Groups.lean")),
            "Ext.order": SimpleNamespace(keyword="def", path=Path("Ext/Groups.lean")),
            "Ext.hard": SimpleNamespace(keyword="theorem", path=Path("Ext/Open.lean")),
            "Ext.partial": SimpleNamespace(keyword="def", path=Path("Ext/Open.lean")),
            "Ext.conjecture": SimpleNamespace(keyword="theorem_wanted", path=Path("Ext/Groups.lean")),
        }
        dependencies = {
            "Ext.lagrange": {"module": "Ext.Groups", "statement": ["Ext.order", "Ext.lagrange"], "proof": ["Ext.conjecture", "Ext.order"]},
            "Ext.conjecture": {"module": "Ext.Groups", "statement": [], "proof": []},
        }
        counts, unlinked = sync.apply_lean_facts(SimpleNamespace(declarations=declarations), dependencies)
        self.assertEqual(counts, {"articles": 5, "unresolved": 0, "edges": 2, "mathlib": 0})
        self.assertEqual(unlinked, [])
        rows = {sync.subject_path(row).name: row for row in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        facts = {name: (row.get("kind"), row.get("status")) for name, row in rows.items()}
        self.assertEqual(facts, {
            "README.md": (None, None),
            "lagrange.md": ("theorem", "formalized"),
            "order.md": ("def", "formalized"),
            "hard.md": ("theorem", "stated"),
            "partial.md": ("def", None),
            "conjecture.md": ("theorem", "stated"),
        })
        self.assertEqual(
            lagrange.read_text(),
            "# Lagrange's theorem\n\nIt divides.\n\n## Depends on\n\n- [Order](order.md)\n\n"
            "## Proof depends on\n\n- [Conjecture](conjecture.md)\n\n## Sources\n\n- Book.\n",
        )
        self.assertEqual(order.read_text(), "# Order\n\nA number.\n\n## Depends on\n\nThis node has no prerequisites.\n")
        self.assertEqual(conjecture.read_text(), "# Conjecture\n\nOpen.\n\n## Depends on\n\nThis node has no prerequisites.\n")
        self.assertEqual((wiki.ROADMAP / "Algebra" / "README.md").read_text(), "# Algebra\n\n- [Order](order.md)\n")

    def test_mathlib_credited_pages_keep_their_link_and_get_their_edges(self) -> None:
        mathlib = lambda name: [{"type": "lean", "uri": sync.MATHLIB,
                                 "location": {"declaration": name, "module": "Mathlib.Measure"}}]
        flag = {"org.autoform": {"mathlib": True}}
        atlas = self.page("Algebra/atlas.md", "# Atlas\n\nUses a measure.\n")
        measure = self.page("Algebra/measure.md", "# Measure\n\nA measure.\n\n## Depends on\n\n- [Stray](atlas.md)\n")
        space = self.page("Algebra/space.md", "# Space\n\nA space.\n")
        gone = self.page("Algebra/gone.md", "# Gone\n\nNo longer in Mathlib.\n")
        self.annotate([
            self.about("Algebra/atlas.md", object=[{"location": {"declaration": "Ext.atlas"}}]),
            self.about("Algebra/measure.md", object=mathlib("M.measure"), status="formalized", extensions=flag),
            self.about("Algebra/space.md", object=mathlib("M.space"), extensions=flag),
            self.about("Algebra/gone.md", object=mathlib("M.gone"), extensions=flag),
        ])
        self.assertEqual(sync.lean_name(sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][1]), None)
        index = SimpleNamespace(declarations={"Ext.atlas": SimpleNamespace(keyword="theorem", path=Path("Ext/A.lean"))})
        (wiki.ROOT / "Ext").mkdir(parents=True, exist_ok=True)
        (wiki.ROOT / "Ext" / "A.lean").write_text("theorem atlas : True := trivial\n")
        dependencies = {"Ext.atlas": {"module": "Ext.A", "statement": [], "proof": []}}
        registry = {"left_out": {}, "bridges": {"Ext.atlas": {"statement": ["M.measure"], "proof": ["M.space"]}},
                    "mathlib": {"M.measure": {"module": "Mathlib.Measure", "kind": "def", "proposition": False, "statement": ["M.space"],
                                              "proof": []},
                                "M.space": {"module": "Mathlib.Measure", "kind": "structure", "proposition": False, "statement": [],
                                            "proof": []}},
                    "missing": ["M.gone"], "project": [], "mutual": []}
        registry["inputs"] = {"names_sha256": sync.names_digest(sync.credited_mathlib(sync.read_annotations())[0]),
                              "dump_sha256": "d" * 64, "mathlib_rev": None, "requested": 3,
                              "aliases_sha256": duplicates_digest(), "format": sync.REGISTRY_FORMAT}
        self.assertEqual(sync.registry_problems(registry, sync.read_annotations()), [])
        counts, unlinked = sync.apply_lean_facts(index, dependencies, registry)
        self.assertEqual(counts, {"articles": 1, "unresolved": 1, "edges": 3, "mathlib": 2})
        self.assertEqual(unlinked, ["M.gone (Algebra/gone.md, credited to Mathlib, missing from Mathlib)"])
        rows = {sync.subject_path(row).name: row for row in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        self.assertEqual((rows["measure.md"]["kind"], "status" in rows["measure.md"]), ("def", False))
        self.assertEqual(rows["measure.md"]["object"], mathlib("M.measure"))
        self.assertEqual(rows["space.md"]["kind"], "structure")
        # A missing declaration's page loses its link and the flag that would still show it as in Mathlib.
        self.assertEqual({key: rows["gone.md"].get(key) for key in ("object", "extensions", "kind", "status")},
                         {"object": None, "extensions": None, "kind": None, "status": None})
        self.assertEqual(atlas.read_text(), "# Atlas\n\nUses a measure.\n\n## Depends on\n\n- [Measure](measure.md)\n\n"
                                            "## Proof depends on\n\n- [Space](space.md)\n")
        self.assertEqual(measure.read_text(), "# Measure\n\nA measure.\n\n## Depends on\n\n- [Space](space.md)\n")
        # The registry follows every use, so a page it lists nothing for has no prerequisites among the pages.
        self.assertEqual(space.read_text(), "# Space\n\nA space.\n\n## Depends on\n\nThis node has no prerequisites.\n")
        self.assertEqual(gone.read_text(), "# Gone\n\nNo longer in Mathlib.\n")

    def test_a_proof_bridges_only_to_a_declaration_it_names_itself(self) -> None:
        # From the dump's rows to the pages: Ext.atlas's statement names M.stated itself, and its proof names M.named
        # itself but reaches M.mediated only through the project's theorem Ext.hidden, which is no article. The page
        # depends on M.stated and, in its proof, on M.named; M.mediated is in neither the registry's bridges nor the
        # page. Every witness kept is direct, so either bridge rule gives the same.
        from scripts import extract_v2_lean_dependencies as extract
        from scripts.test_extract_v2_lean_dependencies import credited, row, with_mathlib

        targets = ("stated", "named", "mediated")
        flag = {"org.autoform": {"mathlib": True}}
        atlas = self.page("Algebra/atlas.md", "# Atlas\n\nA theorem.\n")
        for name in targets:
            self.page(f"Algebra/{name}.md", f"# {name.title()}\n\nA Mathlib theorem.\n")
        self.annotate([self.about("Algebra/atlas.md", object=[{"location": {"declaration": "Ext.atlas"}}])] + [
            self.about(f"Algebra/{name}.md", extensions=flag, object=[
                {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": f"M.{name}", "module": "Mathlib.T"}}])
            for name in targets])
        rows = {
            "Ext.hidden": with_mathlib(row("Ext.hidden", "theorem", [], []), [], ["M.mediated"], direct=["M.mediated"]),
            "Ext.atlas": with_mathlib(row("Ext.atlas", "theorem", [], ["Ext.hidden"]), ["M.stated"], ["M.named"],
                                      direct=["M.named"], type_direct=["M.stated"])}
        registry = extract.registry(rows, {"Ext.atlas"}, {f"M.{name}": credited(f"M.{name}", "theorem", [], [])
                                                          for name in targets})
        self.assertEqual((registry["bridges"], registry["left_out"]),
                         ({"Ext.atlas": {"statement": ["M.stated"], "proof": ["M.named"]}},
                          {"Ext.atlas": {"statement": [], "proof": ["M.mediated"]}}))
        registry["inputs"] = {"names_sha256": sync.names_digest(sync.credited_mathlib(sync.read_annotations())[0]),
                              "dump_sha256": "d" * 64, "mathlib_rev": None, "requested": 3,
                              "aliases_sha256": duplicates_digest(), "format": sync.REGISTRY_FORMAT}
        self.assertEqual(sync.registry_problems(registry, sync.read_annotations()), [])
        (wiki.ROOT / "Ext").mkdir(parents=True, exist_ok=True)
        (wiki.ROOT / "Ext" / "A.lean").write_text("theorem atlas : True := trivial\n")
        index = SimpleNamespace(declarations={"Ext.atlas": SimpleNamespace(keyword="theorem", path=Path("Ext/A.lean"))})
        counts, _ = sync.apply_lean_facts(index, {"Ext.atlas": {"module": "Ext.A", "statement": [], "proof": []}},
                                          registry)
        self.assertEqual((counts["edges"], counts["mathlib"]), (2, 3))
        self.assertEqual(atlas.read_text(), "# Atlas\n\nA theorem.\n\n## Depends on\n\n- [Stated](stated.md)\n\n"
                                            "## Proof depends on\n\n- [Named](named.md)\n")

    def test_a_registry_no_consumer_may_act_on_writes_nothing(self) -> None:
        # A bridge both kept and left out, a `left_out` missing or malformed, a bridge from a declaration no page
        # credits or to one the registry does not find, and a registry that is JSON null: lean-facts refuses each
        # before it writes, and the vault keeps every byte. The registry as written passes.
        from scripts import extract_v2_lean_dependencies as extract
        from scripts.test_extract_v2_lean_dependencies import credited, row, with_mathlib

        targets = ("stated", "named", "mediated")
        self.page("Algebra/atlas.md", "# Atlas\n\nA theorem.\n")
        for name in targets:
            self.page(f"Algebra/{name}.md", f"# {name.title()}\n\nA Mathlib theorem.\n")
        self.annotate([self.about("Algebra/atlas.md", object=[{"location": {"declaration": "Ext.atlas"}}])] + [
            self.about(f"Algebra/{name}.md", extensions={"org.autoform": {"mathlib": True}}, object=[
                {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": f"M.{name}", "module": "Mathlib.T"}}])
            for name in targets])
        rows = {"Ext.atlas": with_mathlib(row("Ext.atlas", "theorem", [], []), ["M.stated"], ["M.named", "M.mediated"],
                                          direct=["M.named"], type_direct=["M.stated"])}
        good = extract.registry(rows, {"Ext.atlas"}, {f"M.{name}": credited(f"M.{name}", "theorem", [], [])
                                                      for name in targets})
        good["inputs"] = {"names_sha256": sync.names_digest(sync.credited_mathlib(sync.read_annotations())[0]),
                          "dump_sha256": "d" * 64, "mathlib_rev": None, "requested": 3,
                          "aliases_sha256": duplicates_digest(), "format": sync.REGISTRY_FORMAT}
        self.assertEqual(good["left_out"], {"Ext.atlas": {"statement": [], "proof": ["M.mediated"]}})
        kept = good["bridges"]["Ext.atlas"]
        cases = {
            "kept and left out": ({**good, "bridges": {"Ext.atlas": {**kept, "proof": ["M.mediated", "M.named"]}}},
                                  "the registry both keeps and leaves out the bridge Ext.atlas -> M.mediated"),
            "no left_out": ({key: value for key, value in good.items() if key != "left_out"},
                            "the registry is not one extract_v2_lean_dependencies.py --registry writes"),
            "left_out a string": ({**good, "left_out": "M.mediated"},
                                  "the registry is not one extract_v2_lean_dependencies.py --registry writes"),
            "left_out entry a list": ({**good, "left_out": {"Ext.atlas": ["M.mediated"]}},
                                      "the registry's left_out entry for Ext.atlas is malformed"),
            "unknown source": ({**good, "left_out": {"Ext.other": {"statement": [], "proof": ["M.mediated"]}}},
                               "the registry's left_out name Ext.other, which no page credits to this project"),
            "unknown target": ({**good, "bridges": {"Ext.atlas": {**kept, "statement": ["M.absent", "M.stated"]}}},
                               "the registry's bridges entry for Ext.atlas names M.absent, which it does not find"),
            "null": (None, "the registry is not one extract_v2_lean_dependencies.py --registry writes"),
            # A table of another type is no extractor's registry, refused before any table is read.
            **{f"{table} of another type": ({**good, table: other},
                                            "the registry is not one extract_v2_lean_dependencies.py --registry writes")
               for table, other in (("mathlib", []), ("bridges", []), ("left_out", []), ("inputs", []),
                                    ("missing", {}), ("project", {}))},
        }
        (wiki.ROOT / "Ext").mkdir(parents=True, exist_ok=True)
        (wiki.ROOT / "Ext" / "A.lean").write_text("theorem atlas : True := trivial\n")
        index = SimpleNamespace(declarations={"Ext.atlas": SimpleNamespace(keyword="theorem", path=Path("Ext/A.lean"))})
        lean = SimpleNamespace(index_project=lambda *args, **kwargs: index)
        reader = sync.reader()
        dependency_file, registry_file = self.tmp / "lean-dependencies.json", self.tmp / "mathlib-registry.json"
        dependency_file.write_text(json.dumps({"missing_articles": {}, "articles": {
            "Ext.atlas": {"module": "Ext.A", "statement": [], "proof": []}}}))

        def run(registry) -> tuple[int, str, bool]:
            registry_file.write_text(json.dumps(paired(registry, dependency_file)))
            files = lambda: {path: path.read_bytes() for path in sorted([*wiki.ROADMAP.rglob("*"),
                                                                          *sync.LINKS.iterdir()]) if path.is_file()}
            before = files()
            with patch.dict("sys.modules", {"autoform_cli": SimpleNamespace(lean=lean, annotations=reader),
                                            "autoform_cli.lean": lean, "autoform_cli.annotations": reader}), \
                    patch("sys.stdout", new_callable=io.StringIO), patch("sys.stderr", new_callable=io.StringIO) as err:
                code = sync.run_lean_facts(dependency_file, registry_file)
            return code, err.getvalue(), files() == before

        for case, (registry, message) in cases.items():
            with self.subTest(case=case):
                self.assertIn(message, sync.registry_problems(registry, sync.read_annotations()))
                self.assertEqual(run(registry)[0::2], (1, True))
        code, err, unchanged = run(good)
        self.assertEqual((code, unchanged), (0, False), err)
        self.assertIn("## Proof depends on\n\n- [Named](named.md)\n",
                      (wiki.ROADMAP / "Algebra" / "atlas.md").read_text())

    def test_a_statement_that_reaches_a_mathlib_declaration_only_through_another_constant_gives_no_edge(self) -> None:
        # Ext.T's statement reaches M.r only through an intermediate constant: the registry lists the bridge apart,
        # and lean-facts gives the page no edge to M.r. A registry of the previous format, which kept that bridge, is
        # refused before anything is written.
        from scripts import extract_v2_lean_dependencies as extract
        from scripts.test_extract_v2_lean_dependencies import credited, row, with_mathlib

        page = self.page("Algebra/t.md", "# T\n\nA theorem.\n")
        self.page("Algebra/m.md", "# M\n\nA Mathlib theorem.\n")
        self.annotate([self.about("Algebra/t.md", object=[{"location": {"declaration": "Ext.T"}}]),
                       self.about("Algebra/m.md", extensions={"org.autoform": {"mathlib": True}}, object=[
                           {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.r",
                                                                              "module": "Mathlib.T"}}])])
        registry = extract.registry({"Ext.T": with_mathlib(row("Ext.T", "theorem", [], []), ["M.r"], [])}, {"Ext.T"},
                                    {"M.r": credited("M.r", "theorem", [], [])})
        registry["inputs"] = {"names_sha256": sync.names_digest(sync.credited_mathlib(sync.read_annotations())[0]),
                              "dump_sha256": "d" * 64, "mathlib_rev": None, "requested": 1,
                              "aliases_sha256": duplicates_digest(), "format": sync.REGISTRY_FORMAT}
        self.assertEqual((registry["bridges"], registry["left_out"]),
                         ({}, {"Ext.T": {"statement": ["M.r"], "proof": []}}))
        older = {**registry, "bridges": {"Ext.T": {"statement": ["M.r"], "proof": []}}, "left_out": {},
                 "inputs": {**registry["inputs"], "format": 4, "bridge_rule": "statement-and-direct-proof"}}
        (wiki.ROOT / "Ext.lean").write_text("theorem T : True := trivial\n")
        index = SimpleNamespace(declarations={"Ext.T": SimpleNamespace(keyword="theorem", path=Path("Ext.lean"),
                                                                       line=1)})
        lean = SimpleNamespace(index_project=lambda *args, **kwargs: index)
        reader = sync.reader()
        dependency_file, registry_file = self.tmp / "lean-dependencies.json", self.tmp / "mathlib-registry.json"
        dependency_file.write_text(json.dumps({"missing_articles": {}, "articles": {
            "Ext.T": {"module": "Ext", "statement": [], "proof": []}}}))

        def run(given: dict) -> tuple[int, str, bool]:
            registry_file.write_text(json.dumps(paired(given, dependency_file)))
            files = lambda: {path: path.read_bytes() for path in sorted([*wiki.ROADMAP.rglob("*"),
                                                                          *sync.LINKS.iterdir()]) if path.is_file()}
            before = files()
            with patch.dict("sys.modules", {"autoform_cli": SimpleNamespace(lean=lean, annotations=reader),
                                            "autoform_cli.lean": lean, "autoform_cli.annotations": reader}), \
                    patch("sys.stdout", new_callable=io.StringIO), patch("sys.stderr", new_callable=io.StringIO) as err:
                code = sync.main(["lean-facts", str(dependency_file), "--registry", str(registry_file)])
            return code, err.getvalue(), files() == before

        code, err, unchanged = run(older)
        self.assertEqual((code, unchanged), (1, True))
        self.assertIn(f"the registry's format is 4, not {sync.REGISTRY_FORMAT}", err)
        code, err, _ = run(registry)
        self.assertEqual(code, 0, err)
        self.assertEqual(page.read_text(), "# T\n\nA theorem.\n\n## Depends on\n\nThis node has no prerequisites.\n")

    def test_a_registry_made_for_other_duplicates_lists_writes_nothing(self) -> None:
        # Ext.T's proof uses the hidden theorem Ext.h, which names M.r itself. Once T's row lists Ext.h as a duplicate,
        # Ext.h is part of Ext.T and M.r a proof bridge, while the extraction stays as it was. A registry made before
        # that edit, one that records no duplicates lists, and one of the earlier format, which recorded none, are
        # refused before anything is written; the registry made for the edited rows gives the page the bridge.
        from scripts.test_extract_v2_lean_dependencies import credited, row, with_mathlib

        page = self.page("Algebra/t.md", "# T\n\nA theorem.\n")
        self.page("Algebra/m.md", "# M\n\nA Mathlib theorem.\n")
        mathlib = self.about("Algebra/m.md", extensions={"org.autoform": {"mathlib": True}}, object=[
            {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.r", "module": "Mathlib.T"}}])
        theorem = self.about("Algebra/t.md", object=[{"location": {"declaration": "Ext.T"}}])
        self.annotate([theorem, mathlib])
        rows = {"Ext.T": with_mathlib(row("Ext.T", "theorem", [], ["Ext.h"]), [], []),
                "Ext.h": with_mathlib(row("Ext.h", "theorem", [], []), [], ["M.r"], direct=["M.r"])}

        def made(aliases: dict[str, str]) -> dict:
            registry = extract.registry(rows, {"Ext.T"}, {"M.r": credited("M.r", "theorem", [], [])}, aliases)
            registry["inputs"] = {"names_sha256": sync.names_digest(sync.credited_mathlib(sync.read_annotations())[0]),
                                  "dump_sha256": "d" * 64, "mathlib_rev": None, "requested": 1,
                                  "aliases_sha256": extract.aliases_digest(aliases), "format": sync.REGISTRY_FORMAT}
            return registry

        before, after = made({}), made({"Ext.h": "Ext.T"})
        self.assertEqual(((before["bridges"], before["left_out"]), (after["bridges"], after["left_out"])),
                         (({}, {"Ext.T": {"statement": [], "proof": ["M.r"]}}),
                          ({"Ext.T": {"statement": [], "proof": ["M.r"]}}, {})))
        self.assertEqual(sync.registry_problems(before, sync.read_annotations()), [])
        self.annotate([{**theorem, "extensions": {sync.OWN: {"duplicates": ["Ext.h"]}}}, mathlib])
        (wiki.ROOT / "Ext.lean").write_text("theorem T : True := trivial\ntheorem h : True := trivial\n")
        index = SimpleNamespace(declarations={name: SimpleNamespace(keyword="theorem", path=Path("Ext.lean"), line=1)
                                              for name in ("Ext.T", "Ext.h")})
        lean = SimpleNamespace(index_project=lambda *args, **kwargs: index)
        reader = sync.reader()
        dependency_file, registry_file = self.tmp / "lean-dependencies.json", self.tmp / "mathlib-registry.json"
        dependency_file.write_text(json.dumps({"missing_articles": {}, "articles": {
            "Ext.T": {"module": "Ext", "statement": [], "proof": []}}}))

        def run(given: dict) -> tuple[int, str, bool]:
            registry_file.write_text(json.dumps(paired(given, dependency_file)))
            files = lambda: {path: path.read_bytes() for path in sorted([*wiki.ROADMAP.rglob("*"),
                                                                          *sync.LINKS.iterdir()]) if path.is_file()}
            unchanged = files()
            with patch.dict("sys.modules", {"autoform_cli": SimpleNamespace(lean=lean, annotations=reader),
                                            "autoform_cli.lean": lean, "autoform_cli.annotations": reader}), \
                    patch("sys.stdout", new_callable=io.StringIO), patch("sys.stderr", new_callable=io.StringIO) as err:
                code = sync.main(["lean-facts", str(dependency_file), "--registry", str(registry_file)])
            return code, err.getvalue(), files() == unchanged

        unrecorded = {**after, "inputs": {key: value for key, value in after["inputs"].items()
                                          if key != "aliases_sha256"}}
        for given, message in (
                (before, "error: the registry was made for other duplicates lists than the checkout's (its "
                         "`inputs.aliases_sha256` differs), so its bridges may not be the checkout's"),
                (unrecorded, "error: the registry does not record the duplicates lists it was made for"),
                ({**after, "inputs": {**after["inputs"], "format": 5}}, "error: the registry's format is 5, not 6")):
            with self.subTest(message=message):
                code, err, unchanged = run(given)
                self.assertEqual((code, unchanged), (1, True), err)
                self.assertIn(message, err)
        code, err, _ = run(after)
        self.assertEqual(code, 0, err)
        self.assertIn("## Proof depends on\n\n- [M](m.md)\n", page.read_text())

    def test_no_registry_passes_for_a_list_whose_name_spells_other_entries(self) -> None:
        # Ext.T's row lists Ext.a and Ext.b, and the registry was made for that list. An edit to the one name
        # `Ext.a<TAB>Ext.T<LF>Ext.b` spelled the same digest lines, so the registry passed for the edited rows. No Lean
        # name holds a control character: such a list is refused, and the digest now spells the two lists apart.
        self.page("Algebra/t.md", "# T\n\nA theorem.\n")
        theorem = self.about("Algebra/t.md", object=[{"location": {"declaration": "Ext.T"}}])
        listing = lambda names: {**theorem, "extensions": {sync.OWN: {"duplicates": names}}}
        self.annotate([listing(["Ext.a", "Ext.b"])])
        registry = {"left_out": {}, "bridges": {}, "mathlib": {}, "missing": [], "project": [], "mutual": [],
                    "inputs": {"names_sha256": hashlib.sha256(b"").hexdigest(), "dump_sha256": "d" * 64,
                               "mathlib_rev": None, "requested": 0, "aliases_sha256": duplicates_digest(),
                               "format": sync.REGISTRY_FORMAT}}
        self.assertEqual(sync.registry_problems(registry, sync.read_annotations()), [])
        self.annotate([listing(["Ext.a\tExt.T\nExt.b"])])
        self.assertEqual(sync.registry_problems(registry, sync.read_annotations()),
                         ["Algebra/t.md: its duplicates list is not a list of declaration names, each given once"])
        self.assertNotEqual(extract.aliases_digest({"Ext.a\tExt.T\nExt.b": "Ext.T"}),
                            registry["inputs"]["aliases_sha256"])

    def test_an_extraction_without_a_live_credited_declaration_writes_nothing(self) -> None:
        # Ext.main's page was added after the extraction was made: its statement depends on Ext.blocked, but the
        # earlier extraction, otherwise valid, has no row for Ext.main, nor for Ext.old, which an earlier sync's
        # module and name stand for. lean-facts refuses rather than give either page no prerequisites, and writes
        # nothing; the fresh extraction passes. A credited declaration the extraction lists as missing and the
        # sources no longer declare is unlinked, as before.
        (wiki.ROOT / "Ext.lean").write_text("theorem main : True := sorry\ntheorem blocked : True := sorry\n"
                                            "theorem old : True := trivial\n")
        index = SimpleNamespace(declarations={name: SimpleNamespace(keyword="theorem", path=Path("Ext.lean"), line=1)
                                              for name in ("Ext.main", "Ext.blocked", "Ext.old")})
        lean = SimpleNamespace(index_project=lambda *args, **kwargs: index)
        reader = sync.reader()
        main = self.page("Algebra/main.md", "# Main\n\nA statement.\n")
        self.page("Algebra/blocked.md", "# Blocked\n\nA statement.\n")
        self.page("Algebra/gone.md", "# Gone\n\nA statement.\n")
        old = self.page("Algebra/old.md", "# Old\n\nA statement.\n")
        self.annotate([self.about(f"Algebra/{name}.md", object=[{"location": {"declaration": f"Ext.{name}"}}])
                       for name in ("main", "blocked", "gone")]
                      + [self.about("Algebra/old.md", extensions={sync.OWN: {"module": "Ext", "name": "old"}})])
        dependency_file = self.tmp / "lean-dependencies.json"
        blocked = {"module": "Ext", "statement": [], "proof": []}

        def run(extraction: dict) -> tuple[int, str, bool]:
            dependency_file.write_text(json.dumps(extraction))
            files = lambda: {path: path.read_bytes() for path in sorted([*wiki.ROADMAP.rglob("*"),
                                                                          *sync.LINKS.iterdir()]) if path.is_file()}
            before = files()
            with patch.dict("sys.modules", {"autoform_cli": SimpleNamespace(lean=lean, annotations=reader),
                                            "autoform_cli.lean": lean, "autoform_cli.annotations": reader}), \
                    patch("sys.stdout", new_callable=io.StringIO), patch("sys.stderr", new_callable=io.StringIO) as err:
                code = sync.run_lean_facts(dependency_file)
            return code, err.getvalue(), files() == before

        code, err, unchanged = run({"missing_articles": {"Ext": ["Ext.gone"]}, "articles": {"Ext.blocked": blocked}})
        self.assertEqual((code, unchanged), (1, True))
        self.assertIn("error: a page credits Ext.main, which the Lean sources declare, but", err)
        self.assertIn("error: a page credits Ext.old, which the Lean sources declare, but", err)
        self.assertNotIn("Ext.gone", err)
        code, err, unchanged = run({"missing_articles": {"Ext": ["Ext.gone"]}, "articles": {
            "Ext.blocked": blocked, "Ext.main": {"module": "Ext", "statement": ["Ext.blocked"], "proof": []},
            "Ext.old": {"module": "Ext", "statement": ["Ext.blocked"], "proof": []}}})
        self.assertEqual((code, unchanged), (0, False), err)
        self.assertIn("the Lean no longer declares Ext.gone (Algebra/gone.md)", err)
        self.assertEqual(main.read_text(), "# Main\n\nA statement.\n\n## Depends on\n\n- [Blocked](blocked.md)\n")
        self.assertEqual(old.read_text(), "# Old\n\nA statement.\n\n## Depends on\n\n- [Blocked](blocked.md)\n")

    def test_a_name_looked_for_only_in_imported_modules_says_which_module_was_missing(self) -> None:
        self.page("Algebra/gone.md", "# Gone\n\nNot found.\n")
        end = [{"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.gone", "module": "Mathlib.New"}}]
        self.annotate([self.about("Algebra/gone.md", object=end, extensions={"org.autoform": {"mathlib": True}})])
        registry = {"left_out": {}, "bridges": {}, "mathlib": {}, "missing": ["M.gone"], "project": [],
                    "unplaced": ["M.gone"],
                    "mutual": []}
        _, unlinked = sync.apply_lean_facts(SimpleNamespace(declarations={}), {}, registry)
        self.assertEqual(unlinked, ["M.gone (Algebra/gone.md, credited to Mathlib, not in the modules the build "
                                    "imported; the build's Mathlib has no module Mathlib.New)"])

    def test_without_a_registry_a_mathlib_credited_page_stays_as_committed(self) -> None:
        page = self.page("Algebra/measure.md", "# Measure\n\nA measure.\n")
        end = [{"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.measure"}}]
        self.annotate([self.about("Algebra/measure.md", object=end, extensions={"org.autoform": {"mathlib": True}})])
        counts, unlinked = sync.apply_lean_facts(SimpleNamespace(declarations={}), {})
        self.assertEqual((counts["unresolved"], unlinked), (0, []))
        self.assertEqual(sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][0]["object"], end)
        self.assertEqual(page.read_text(), "# Measure\n\nA measure.\n")

    def test_mathlib_names_lists_the_credited_declarations(self) -> None:
        end = lambda name, module=None: [{"type": "lean", "uri": sync.MATHLIB, "location": {
            "declaration": name, **({"module": module} if module else {})}}]
        # The build has Mathlib.B; a module it lacks, which the dump could not import, is left out.
        source = self.tmp / ".lake" / "packages" / "mathlib" / "Mathlib" / "B.lean"
        source.parent.mkdir(parents=True)
        source.write_text("")
        flag = {"org.autoform": {"mathlib": True}}
        rows = [self.about("Algebra/b.md", object=end("M.b", "Mathlib.B"), extensions=flag),
                self.about("Algebra/a.md", object=end("M.a"), extensions=flag),
                self.about("Algebra/d.md", object=end("M.d", "Mathlib.Nowhere"), extensions=flag),
                self.about("Algebra/c.md", object=[{"location": {"declaration": "Ext.c"}}]),
                # A Mathlib end on a row without the flag is a reference: the page is Ext.e's, and credits no M.e.
                self.about("Algebra/e.md", object=[{"location": {"declaration": "Ext.e"}, "role": "states"},
                                                   *end("M.e")])]
        self.annotate(rows)
        output = self.tmp / "build" / "names.txt"
        with patch("sys.stdout", new_callable=io.StringIO):
            self.assertEqual(sync.main(["mathlib-names", str(output)]), 0)
        self.assertEqual(output.read_text(), "M.a\nM.b\tMathlib.B\nM.d\n")
        # Two pages crediting one declaration, or a flagged row that also names a declaration of the project, leave
        # the credit ambiguous: nothing is written.
        for extra in (self.about("Algebra/f.md", object=end("M.a"), extensions=flag),
                      self.about("Algebra/g.md", object=[{"location": {"declaration": "Ext.g"}}, *end("M.g")],
                                 extensions=flag)):
            output.unlink(missing_ok=True)
            self.annotate(rows + [extra])
            with patch("sys.stdout", new_callable=io.StringIO), patch("sys.stderr", new_callable=io.StringIO) as err:
                self.assertEqual(sync.main(["mathlib-names", str(output)]), 1)
            self.assertFalse(output.exists())
            self.assertIn("error: ", err.getvalue())

    def test_a_mathlib_reference_never_takes_the_credit_of_the_page_s_own_declaration(self) -> None:
        # A page states Ext.t and refers to Mathlib's M.t, without the flag: the page stays Ext.t's article, even when
        # the registry does not find M.t, and Git's `.git` spelling of Mathlib's address is still Mathlib's.
        page = self.page("Algebra/t.md", "# T\n\nA theorem.\n")
        reference = {"type": "lean", "uri": sync.MATHLIB + ".git", "location": {"declaration": "M.t"}}
        self.annotate([self.about("Algebra/t.md", object=[{"location": {"declaration": "Ext.t"}, "role": "states"},
                                                          reference], status="formalized")])
        row = sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][0]
        self.assertEqual((sync.lean_name(row), sync.mathlib_name(row), sync.is_mathlib(reference["uri"])),
                         ("Ext.t", None, True))
        index = SimpleNamespace(declarations={"Ext.t": SimpleNamespace(keyword="theorem", path=Path("Ext/T.lean"))})
        (wiki.ROOT / "Ext").mkdir(parents=True, exist_ok=True)
        (wiki.ROOT / "Ext" / "T.lean").write_text("theorem t : True := trivial\n")
        registry = {"left_out": {}, "bridges": {}, "mathlib": {}, "missing": [], "project": [], "mutual": [],
                    "inputs": {"names_sha256": hashlib.sha256(b"").hexdigest(), "dump_sha256": "d" * 64,
                               "mathlib_rev": None, "requested": 0,
                               "aliases_sha256": duplicates_digest(), "format": sync.REGISTRY_FORMAT}}
        self.assertEqual(sync.registry_problems(registry, sync.read_annotations()), [])
        counts, unlinked = sync.apply_lean_facts(index, {"Ext.t": {"module": "Ext.T", "statement": [], "proof": []}},
                                                 registry)
        self.assertEqual((counts["articles"], counts["mathlib"], unlinked), (1, 0, []))
        row = sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][0]
        self.assertEqual((row["kind"], row["status"], len(row["object"])), ("theorem", "formalized", 2))
        self.assertIn("This node has no prerequisites.", page.read_text())

    def test_nothing_is_written_from_a_registry_that_does_not_speak_for_the_checkout(self) -> None:
        end = lambda name, module=None: [{"type": "lean", "uri": sync.MATHLIB, "location": {
            "declaration": name, **({"module": module} if module else {})}}]
        flag = {"org.autoform": {"mathlib": True}}
        self.page("Algebra/a.md", "# A\n\nA.\n")
        self.page("Algebra/b.md", "# B\n\nB.\n")
        self.annotate([self.about("Algebra/a.md", object=end("M.a", "Mathlib.Wrong"), extensions=flag),
                       self.about("Algebra/b.md", object=end("M.b"), extensions=flag)])
        files = sync.read_annotations()
        digest = sync.names_digest(sync.credited_mathlib(files)[0])
        good = {"left_out": {}, "bridges": {}, "mutual": [], "project": [], "missing": ["M.b"],
                "inputs": {"names_sha256": digest, "dump_sha256": "d" * 64, "mathlib_rev": None, "requested": 2,
                           "aliases_sha256": duplicates_digest(), "format": sync.REGISTRY_FORMAT},
                "mathlib": {"M.a": {"module": "Mathlib.Wrong", "kind": "def", "proposition": False, "statement": [], "proof": []}}}
        self.assertEqual(sync.registry_problems(good, files), [])
        cases = {
            "names": ({**good, "inputs": {**good["inputs"], "names_sha256": "0" * 64}},
                      "another list of credited Mathlib names"),
            "dump": ({**good, "inputs": {**good["inputs"], "dump_sha256": None}}, "does not name the dump"),
            "count": ({**good, "inputs": {**good["inputs"], "requested": 3}}, "another number of credited"),
            "split": ({**good, "missing": []}, "do not split the checkout's credited names"),
            # An empty registry is not one that found nothing: it answers none of the credited names.
            "empty": ({**good, "mathlib": {}, "missing": []}, "do not split the checkout's credited names"),
            "module": ({**good, "mathlib": {"M.a": {**good["mathlib"]["M.a"], "module": "Mathlib.Right"}}},
                       "Algebra/a.md names the module Mathlib.Wrong for M.a, which is in Mathlib.Right"),
            "shape": ({"mathlib": {}}, "not one extract_v2_lean_dependencies.py --registry writes"),
            "format": ({**good, "inputs": {**good["inputs"], "format": None}}, "the registry's format is None"),
            "duplicates": ({**good, "inputs": {**good["inputs"], "aliases_sha256": "0" * 64}},
                           "the registry was made for other duplicates lists than the checkout's"),
            "no duplicates digest": (
                {**good, "inputs": {key: value for key, value in good["inputs"].items() if key != "aliases_sha256"}},
                "the registry does not record the duplicates lists it was made for"),
            # A malformed edge list is refused before anything is written.
            "edges": ({**good, "bridges": {"Ext.a": {"statement": "M.a", "proof": []}}},
                      "the registry's bridges entry for Ext.a is malformed"),
        }
        for case, (registry, message) in cases.items():
            with self.subTest(case):
                self.assertTrue(any(message in problem for problem in sync.registry_problems(registry, files)))
        # A credited page whose file is missing is refused before anything is written.
        (wiki.ROADMAP / "Algebra" / "b.md").unlink()
        self.assertIn("Algebra/b.md credits M.b, but the page is missing", sync.registry_problems(good, files))
        self.page("Algebra/b.md", "# B\n\nB.\n")
        # A registry made at another Mathlib than the checkout's pin.
        (wiki.ROOT / "lake-manifest.json").write_text(json.dumps({"packages": [{"name": "mathlib", "rev": "a" * 40}]}))
        self.assertTrue(any(f"pins {'a' * 40}" in problem for problem in sync.registry_problems(good, files)))
        self.assertEqual(sync.registry_problems({**good, "inputs": {**good["inputs"], "mathlib_rev": "a" * 40}}, files),
                         [])

    def test_only_a_lean_link_to_mathlib_credits_and_a_page_has_one_row(self) -> None:
        flag = {"org.autoform": {"mathlib": True}}
        html = [{"type": "html", "uri": sync.MATHLIB, "location": {"declaration": "M.a"}}]
        lean = lambda name: [{"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": name}}]
        self.annotate([self.about("Algebra/a.md", object=html, extensions=flag)])
        self.assertTrue(sync.credited_mathlib(sync.read_annotations())[1])
        self.annotate([self.about("Algebra/a.md", object=lean("M.a"), extensions=flag),
                       self.about("Algebra/a.md", object=lean("M.b"), extensions=flag)])
        self.assertEqual(sync.credited_mathlib(sync.read_annotations())[1],
                         ["Algebra/a.md has 2 rows, which Autoform reads together; a page has one row"])
        # One file under two spellings, and a page with a local row beside its Mathlib-credited one.
        for other in ({"subject": [{"type": "generic", "uri": "../roadmap/Algebra/./a.md"}],
                       "object": lean("M.b"), "extensions": flag},
                      self.about("Algebra/a.md", object=[{"location": {"declaration": "Ext.a"}}])):
            self.annotate([self.about("Algebra/a.md", object=lean("M.a"), extensions=flag), other])
            self.assertTrue(sync.credited_mathlib(sync.read_annotations())[1])

    def test_only_lean_links_to_this_project_are_its_declarations(self) -> None:
        self.links_folder()
        other = "https://github.com/someone/elsewhere"
        # A reference to another repository, or a link of another type, leaves the page's own declaration alone.
        row = {"object": [{"location": {"declaration": "Ext.a"}},
                          {"type": "lean", "uri": other, "location": {"declaration": "Other.x"}, "role": "uses"},
                          {"type": "html", "uri": "https://example.org/notes.html", "location": {"declaration": "y"}}]}
        self.assertEqual(sync.lean_name(row), "Ext.a")
        # A link to another repository that shares a name of this project credits nothing.
        self.assertIsNone(sync.lean_name({"object": [{"type": "lean", "uri": other,
                                                      "location": {"declaration": "Ext.a"}}]}))
        # Losing a Mathlib credit keeps the row's references to other repositories.
        flagged = {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/a.md"}],
                   "object": [{"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.a"}},
                              {"type": "lean", "uri": other, "location": {"declaration": "Other.x"}}],
                   "extensions": {"org.autoform": {"mathlib": True}}}
        self.assertEqual(sync.mathlib_credit(flagged), ("M.a", None))
        sync.drop_mathlib_credit(flagged)
        self.assertEqual(flagged["object"], [{"type": "lean", "uri": other, "location": {"declaration": "Other.x"}}])
        # A Mathlib-credited row that also names a declaration of this project is ambiguous.
        with self.assertRaises(sync.CreditError):
            sync.mathlib_credit({"object": [{"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.a"}},
                                            {"location": {"declaration": "Ext.a"}}],
                                 "extensions": {"org.autoform": {"mathlib": True}}})

    def autoform_owners(self, rows: dict[str, dict]) -> dict[str, tuple | str]:
        """Whom Autoform's own loader shows each page `Algebra/<key>.md` crediting, its row (*rows*, with a subject
        naming the page) recording a formalized theorem: (`mathlib`, name, Mathlib file) for a page it shows as in
        Mathlib with one Mathlib declaration and none of this project, `ambiguous` for any other page it shows as in
        Mathlib, (`atlas`, name, None) when it keeps the theorem's status, which it does only for the declaration
        that takes the credit, listed first, and (`none`, None, None) otherwise."""
        from autoform_cli.graph import declaration_names, load_graph

        self.page("README.md", "# Roadmap\n\n- [Algebra](Algebra/README.md)\n")
        self.page("Algebra/README.md", "# Algebra\n\n" + "".join(f"- [{key}]({key}.md)\n" for key in rows))
        for key in rows:
            self.page(f"Algebra/{key}.md", f"# {key}\n\nA statement.\n")
        self.annotate([{**row, "kind": "theorem", "status": "formalized"} for row in rows.values()])
        graph = load_graph(wiki.VAULT)
        owners: dict[str, tuple | str] = {}
        for key in rows:
            node = graph.nodes[f"Algebra/{key}"]
            if node.mathlib:
                names = declaration_names(node.mathlib_declaration or "")
                owners[key] = (("mathlib", names[0], node.mathlib_file) if len(names) == 1 and node.lean is None
                               else "ambiguous")
            elif node.statement_formalized:
                owners[key] = ("atlas", declaration_names(node.lean)[0], None)
            else:
                owners[key] = ("none", None, None)
        return owners

    def test_one_rule_says_which_declaration_a_row_credits(self) -> None:
        # Every case reviews found, through the one function extraction, lean-facts, declarations and the cards call,
        # and each checked against what Autoform's own loader shows for the same row, over the repository's defaults.
        local = lambda name, **more: {"location": {"declaration": name}, **more}
        other = lambda uri, name, **more: {"type": "lean", "uri": uri, "location": {"declaration": name}, **more}
        upstream = lambda name, **more: other(sync.MATHLIB, name, **more)
        flag = {"org.autoform": {"mathlib": True}}
        elsewhere = "https://github.com/x/y"
        cases = {
            "one local link with no role": ([local("Ext.a")], None, ("atlas", "Ext.a", None)),
            # The page named with a percent-encoded hyphen is the same page.
            "a percent-encoded subject": ([local("Ext.a")], None, ("atlas", "Ext.a", None)),
            "a helper beside the stated declaration": ([local("Ext.h", role="uses"), local("Ext.a", role="states")],
                                                      None, ("atlas", "Ext.a", None)),
            "two local links, none stated": ([local("Ext.a"), local("Ext.b")], None, ("none", None, None)),
            "two stated local links": ([local("Ext.a", role="states"), local("Ext.b", role="states")], None,
                                       ("none", None, None)),
            "the project root spelled out": ([other("../..", "Ext.a")], None, ("atlas", "Ext.a", None)),
            "the project root percent-encoded": ([other("..%2F..", "Ext.a")], None, ("atlas", "Ext.a", None)),
            "another repository by URL": ([local("Ext.a"), other(elsewhere, "Y.b", role="uses")],
                                          None, ("atlas", "Ext.a", None)),
            "a sibling checkout by relative path": ([local("Ext.a"), other("../../../sibling", "S.b", role="uses")],
                                                    None, ("atlas", "Ext.a", None)),
            "a sibling's declaration sharing a local name": ([other("../../../sibling", "Ext.a")], None,
                                                             ("none", None, None)),
            "stated in another repository": ([local("Ext.a"), other(elsewhere, "Y.b", role="states")],
                                             None, ("none", None, None)),
            "a link of another type": ([local("Ext.a"), {"type": "html", "uri": "https://e.org/n.html"}], None,
                                       ("atlas", "Ext.a", None)),
            # A PDF or HTML end is a reference, even one that states the page.
            "an HTML end that states the page": ([local("Ext.a"), {"type": "html", "uri": "https://e.org/n.html",
                                                                   "role": "states"}], None, ("atlas", "Ext.a", None)),
            "a PDF end that states the page beside a stated theorem": (
                [{"type": "pdf", "uri": "https://e.org/b.pdf", "role": "states"}, local("Ext.a", role="states")],
                None, ("atlas", "Ext.a", None)),
            # An end of a type Autoform does not know is left out, but one stating the page still states it elsewhere.
            "an end of an unknown type that states the page": (
                [local("Ext.a"), {"type": "doi", "uri": "https://doi.org/10.1000/x", "role": "states"}], None,
                ("none", None, None)),
            # The folder defaults give their type only to an end with no uri: one with a uri and no type is left out.
            "an end with a uri and no type": ([{"uri": "../..", "location": {"declaration": "Ext.a"}}], None,
                                              ("none", None, None)),
            "an end with a uri and no type beside a local theorem": (
                [local("Ext.a"), {"uri": "../..", "location": {"declaration": "Ext.b"}, "role": "uses"}], None,
                ("atlas", "Ext.a", None)),
            "an end with a uri and no type that states the page": (
                [local("Ext.a"), {"uri": "../..", "location": {"declaration": "Ext.b"}, "role": "states"}], None,
                ("none", None, None)),
            # A Lean end with no location names a whole project.
            "another project stating the page with no location": (
                [local("Ext.a"), {"type": "lean", "uri": elsewhere, "role": "states"}], None, ("none", None, None)),
            "this project stating the page with no location": (
                [local("Ext.a"), {"type": "lean", "uri": "../..", "role": "states"}], None, ("atlas", "Ext.a", None)),
            "a declaration that is not text": ([local(7)], None, ("none", None, None)),
            "a Mathlib reference": ([local("Ext.a"), upstream("M.b")], None, ("atlas", "Ext.a", None)),
            "a Mathlib reference that states the page": ([local("Ext.a"), upstream("M.b", role="states")], None,
                                                         ("none", None, None)),
            "a Mathlib credit": ([upstream("M.b")], flag, ("mathlib", "M.b", None)),
            "a Mathlib credit that states the page": ([upstream("M.b", role="states")], flag, ("mathlib", "M.b", None)),
            "a Mathlib credit naming its module": (
                [{"type": "lean", "uri": sync.MATHLIB + ".git",
                  "location": {"declaration": "M.b", "module": "Mathlib.B"}}], flag, ("mathlib", "M.b", "Mathlib.B")),
            "a Mathlib credit with a reference elsewhere": ([upstream("M.b"), other(elsewhere, "Y.c")],
                                                            flag, ("mathlib", "M.b", None)),
            "a Mathlib credit beside a page reference that states it": (
                [upstream("M.b"), {"type": "html", "uri": "https://e.org/n.html", "role": "states"}], flag,
                ("mathlib", "M.b", None)),
        }
        refused = {
            "a Mathlib credit beside a local declaration": ([upstream("M.b"), local("Ext.a")], flag),
            "a Mathlib flag with no Mathlib declaration": ([local("Ext.a")], flag),
            "a flag that is not a Boolean": ([upstream("M.b")], {"org.autoform": {"mathlib": "true"}}),
            "two Mathlib declarations": ([upstream("M.b"), upstream("M.c")], flag),
            "a Mathlib end with a uri and no type": ([{"uri": sync.MATHLIB, "location": {"declaration": "M.b"}}], flag),
        }
        keys = {case: f"case-{number}" for number, case in enumerate([*cases, *refused])}
        rows = {keys[case]: self.about(f"Algebra/{keys[case]}.md", object=ends,
                                       **({"extensions": extensions} if extensions else {}))
                for case, (ends, extensions, *_) in [*cases.items(), *refused.items()]}
        encoded = keys["a percent-encoded subject"].replace("-", "%2D")
        rows[keys["a percent-encoded subject"]]["subject"] = [{"type": "generic",
                                                              "uri": f"../roadmap/Algebra/{encoded}.md"}]
        shown = self.autoform_owners(rows)
        for case, (_ends, _extensions, expected) in cases.items():
            with self.subTest(case=case):
                row = rows[keys[case]]
                self.assertEqual(sync.subject_path(row), wiki.ROADMAP / "Algebra" / f"{keys[case]}.md")
                self.assertEqual(sync.page_owner(row), expected)
                owner, name, module = expected
                self.assertEqual(shown[keys[case]], (owner, name, module and module.replace(".", "/") + ".lean"))
        for case in refused:
            with self.subTest(case=case):
                with self.assertRaises(sync.CreditError):
                    sync.page_owner(rows[keys[case]])
                # Autoform does not show such a page as one Mathlib declaration's either.
                self.assertFalse(isinstance(shown[keys[case]], tuple) and shown[keys[case]][0] == "mathlib")

    def test_one_reading_joins_a_row_to_its_page(self) -> None:
        # Each spelling of a row's subject, read as extraction, the sync and the cards read it, against the page that
        # Autoform's own loader gives the row's facts to. A row it leaves out, about part of a page, several pages or
        # none, is about no page, and is a problem every one of them refuses.
        from autoform_cli.graph import load_graph

        cases = [
            # The page, the row's subject ends (below roadmap/), and whether the row is about the page.
            ("Algebra/plain.md", ["Algebra/plain.md"], True),
            ("Algebra/t-main.md", ["Algebra/t%2Dmain.md"], True),
            ("Algebra/dots.md", ["Algebra/./x/../dots.md"], True),
            ("Algebra/whole.md", ["Algebra/whole.md#statement", "Algebra/whole.md"], True),
            ("Algebra/query.md", ["Algebra/query.md?v=2"], False),
            ("Algebra/fragment.md", ["Algebra/fragment.md#statement"], False),
            ("Algebra/located.md", [{"type": "generic", "uri": "../roadmap/Algebra/located.md",
                                     "location": {"lines": [1, 2]}}], False),
            ("Algebra/two.md", ["Algebra/two.md", "Algebra/plain.md"], False),
            ("Algebra/text.md", ["Algebra/text.txt"], False),
        ]
        self.page("README.md", "# Roadmap\n\n- [Algebra](Algebra/README.md)\n")
        self.page("Algebra/README.md", "# Algebra\n\n" + "".join(f"- [{Path(page).stem}]({Path(page).name})\n"
                                                                 for page, _, _ in cases))
        rows = []
        for page, ends, _ in cases:
            self.page(page, f"# {Path(page).stem}\n\nA statement.\n")
            subject = [end if isinstance(end, dict) else {"type": "generic", "uri": f"../roadmap/{end}"}
                       for end in ends]
            rows.append({"subject": subject, "kind": "theorem", "status": "formalized",
                         "object": [{"location": {"declaration": f"Ext.{Path(page).stem.replace('-', '_')}"}}]})
        self.annotate(rows)
        graph = load_graph(wiki.VAULT)
        problems = sync.credit_problems(sync.read_annotations())
        for (page, ends, about), row in zip(cases, rows):
            with self.subTest(page=page):
                node = graph.nodes[page.removesuffix(".md")]
                self.assertEqual(sync.subject_path(row), (wiki.ROADMAP / page).resolve() if about else None)
                credited = row["object"][0]["location"]["declaration"]
                self.assertEqual((node.statement_formalized, node.lean), (True, credited) if about else (False, None))
                self.assertEqual(any(f"about {sync.page_name(row)} is one Autoform leaves out" in problem
                                     for problem in problems), not about)
        self.assertEqual(len(problems), sum(not about for _, _, about in cases))
        # Two spellings of one page are two rows for it, which Autoform reads together: a page has one row.
        self.annotate([*rows, self.about("Algebra/plai%6E.md", object=[{"location": {"declaration": "Ext.other"}}])])
        self.assertIn("Algebra/plain.md has 2 rows, which Autoform reads together; a page has one row",
                      sync.credit_problems(sync.read_annotations()))

    def test_rows_autoform_reads_otherwise_stop_the_sync_before_it_writes(self) -> None:
        # A row about part of its page, a page with two rows, and a flagged row that also names a declaration of the
        # project: lean-facts and mathlib-names name each and write nothing, as extraction and the cards refuse them.
        self.page("Algebra/a.md", "# A\n\nA.\n")
        self.page("Algebra/b.md", "# B\n\nB.\n")
        good = self.about("Algebra/a.md", object=[{"location": {"declaration": "Ext.a"}}])
        mathlib = {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.b"}}
        cases = {
            "part of a page": (self.about("Algebra/b.md#statement", object=[{"location": {"declaration": "Ext.b"}}]),
                               "a row of Algebra.jsonl about ../roadmap/Algebra/b.md#statement is one Autoform leaves "
                               "out: its subject names only part of its page"),
            "two rows for a page": (self.about("Algebra/./a.md", object=[{"location": {"declaration": "Ext.b"}}]),
                                    "Algebra/a.md has 2 rows, which Autoform reads together; a page has one row"),
            "a flagged row with a local declaration": (
                self.about("Algebra/b.md", object=[{"location": {"declaration": "Ext.b"}}, mathlib],
                           extensions={"org.autoform": {"mathlib": True}}),
                "Algebra/b.md sets `mathlib` but names 1 Mathlib declarations in Lean links and 1 of this project"),
        }
        dependency_file = self.tmp / "lean-dependencies.json"
        dependency_file.write_text(json.dumps({"missing_articles": {}, "articles": {}}))
        output = self.tmp / "names.txt"
        for case, (row, message) in cases.items():
            with self.subTest(case=case):
                self.annotate([good, row])
                before = (sync.LINKS / "Algebra.jsonl").read_bytes()
                with patch.object(sync, "apply_lean_facts") as apply, patch("sys.stdout", new_callable=io.StringIO), \
                        patch("sys.stderr", new_callable=io.StringIO) as err:
                    self.assertEqual(sync.run_lean_facts(dependency_file), 1)
                    self.assertEqual(sync.main(["mathlib-names", str(output)]), 1)
                apply.assert_not_called()
                self.assertFalse(output.exists())
                self.assertEqual((sync.LINKS / "Algebra.jsonl").read_bytes(), before)
                self.assertEqual(err.getvalue().count(f"error: {message}"), 2, err.getvalue())

    def test_a_page_that_loses_its_declaration_keeps_its_references(self) -> None:
        # Only the ends naming the declaration the Lean no longer has go; the row's references stay, and no row the
        # sync writes back takes the folder defaults it is read with.
        (wiki.ROOT / "Ext").mkdir()
        (wiki.ROOT / "Ext" / "K.lean").write_text("theorem kept : True := trivial\n")
        self.page("Algebra/gone.md", "# Gone\n\nA statement.\n")
        self.page("Algebra/kept.md", "# Kept\n\nA statement.\n")
        html = {"type": "html", "uri": "https://example.org/notes.html", "role": "states"}
        reference = {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.g"}}
        self.annotate([
            self.about("Algebra/gone.md", id=UNLINKED,
                       object=[{"location": {"declaration": "Ext.gone"}}, html, reference]),
            self.about("Algebra/kept.md", id=KEPT, object=[{"location": {"declaration": "Ext.kept"}}])])
        index = SimpleNamespace(declarations={"Ext.kept": SimpleNamespace(keyword="theorem", path=Path("Ext/K.lean"))})
        _, unlinked = sync.apply_lean_facts(index, {"Ext.kept": {"module": "Ext.K", "statement": [], "proof": []}})
        self.assertEqual(unlinked, ["Ext.gone (Algebra/gone.md)"])
        self.assertEqual(sync.read_annotations()[sync.LINKS / "Algebra.jsonl"], [
            self.about("Algebra/gone.md", id=UNLINKED, object=[html, reference]),
            self.about("Algebra/kept.md", id=KEPT, object=[{"location": {"declaration": "Ext.kept"}}],
                       kind="theorem", status="formalized")])
        self.assert_ids_kept([UNLINKED, KEPT])

    def test_an_unlinked_page_never_passes_to_a_declaration_it_refers_to(self) -> None:
        # T states the missing Ext.gone and names the live Ext.a with no role (spelled out, or through the folder
        # defaults), and cites a PDF. Unlinked, it keeps Ext.a as a reference (role `uses`) and the PDF: read again,
        # it credits nothing, a second identical pass leaves it as it is, and Autoform's loader never shows it as
        # Ext.a's theorem. A helper already marked `uses` stays as it was.
        from autoform_cli.graph import load_graph

        (wiki.ROOT / "Ext").mkdir()
        (wiki.ROOT / "Ext" / "A.lean").write_text("theorem a : True := trivial\n")
        index = SimpleNamespace(declarations={"Ext.a": SimpleNamespace(keyword="theorem", path=Path("Ext/A.lean"))})
        pdf = {"type": "pdf", "uri": "https://example.org/book.pdf"}
        gone = {"location": {"declaration": "Ext.gone"}, "role": "states"}
        helpers = {
            "spelled out": {"type": "lean", "uri": "../..", "location": {"declaration": "Ext.a"}},
            "through the defaults": {"location": {"declaration": "Ext.a"}},
            "already a reference": {"location": {"declaration": "Ext.a"}, "role": "uses"},
        }
        self.page("README.md", "# Roadmap\n\n- [Algebra](Algebra/README.md)\n")
        self.page("Algebra/README.md", "# Algebra\n\n- [T](t.md)\n")
        self.page("Algebra/t.md", "# T\n\nA statement.\n")
        for case, helper in helpers.items():
            with self.subTest(case=case):
                self.annotate([self.about("Algebra/t.md", id=UNLINKED, object=[gone, helper, pdf], kind="theorem",
                                          status="formalized")])
                self.assertEqual(sync.page_owner(sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][0]),
                                 ("atlas", "Ext.gone", None))
                _, unlinked = sync.apply_lean_facts(index, {})
                self.assertEqual(unlinked, ["Ext.gone (Algebra/t.md)"])
                once = sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]
                self.assertEqual(once, [self.about("Algebra/t.md", id=UNLINKED,
                                                   object=[{**helper, "role": "uses"}, pdf])])
                self.assert_ids_kept([UNLINKED])
                for _ in range(2):
                    row = sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][0]
                    self.assertEqual(sync.page_owner(row), ("none", None, None))
                    node = load_graph(wiki.VAULT).nodes["Algebra/t"]
                    self.assertEqual((node.lean, node.statement_formalized, node.proof_formalized),
                                     ("Ext.a", False, False))
                    _, unlinked = sync.apply_lean_facts(index, {})
                    self.assertEqual(unlinked, [])
                    self.assertEqual(sync.read_annotations()[sync.LINKS / "Algebra.jsonl"], once)
                self.assertEqual(sync.unowned(sync.read_annotations()), ["Algebra/t.md"])

    def test_unlinking_masks_what_the_folder_defaults_would_credit(self) -> None:
        # Under other folder defaults, a value only the defaults give (a `mathlib` flag, a declaration in the end
        # template) would survive the removal of the row's own entries: unlinking masks it, so the row read again
        # credits nothing, as Autoform's loader reads it too.
        from autoform_cli.graph import load_graph

        self.page("README.md", "# Roadmap\n\n- [Algebra](Algebra/README.md)\n")
        self.page("Algebra/README.md", "# Algebra\n\n- [T](t.md)\n")
        self.page("Algebra/t.md", "# T\n\nA statement.\n")
        mathlib = {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.gone"}}
        cases = {
            "an inherited flag": ({**sync.DEFAULTS, "extensions": {"org.autoform": {"mathlib": True}}},
                                  self.about("Algebra/t.md", id=UNLINKED, object=[mathlib], kind="theorem"),
                                  self.about("Algebra/t.md", id=UNLINKED,
                                             extensions={"org.autoform": {"mathlib": False}}),
                                  "M.gone (Algebra/t.md, credited to Mathlib, missing from Mathlib)"),
            "an inherited declaration": (
                {"object": {**sync.DEFAULTS["object"], "location": {"declaration": "Ext.gone"}}},
                self.about("Algebra/t.md", id=UNLINKED, kind="theorem", status="formalized"),
                self.about("Algebra/t.md", id=UNLINKED, object=[]), "Ext.gone (Algebra/t.md)"),
        }
        registry = {"left_out": {}, "bridges": {}, "mathlib": {}, "missing": ["M.gone"], "project": []}
        for case, (defaults, row, unlinked_row, message) in cases.items():
            with self.subTest(case=case):
                self.links_folder()
                (sync.LINKS / "_defaults.json").write_text(json.dumps(defaults, indent=1) + "\n")
                self.annotate([row])
                self.assertNotEqual(sync.page_owner(row)[0], "none")
                for run in range(2):
                    _, unlinked = sync.apply_lean_facts(SimpleNamespace(declarations={}), {}, registry)
                    self.assertEqual(unlinked, [message] if run == 0 else [])
                    self.assertEqual(sync.read_annotations()[sync.LINKS / "Algebra.jsonl"], [unlinked_row])
                    self.assert_ids_kept([UNLINKED])
                    self.assertEqual(sync.page_owner(unlinked_row), ("none", None, None))
                    node = load_graph(wiki.VAULT).nodes["Algebra/t"]
                    self.assertEqual((node.lean, node.mathlib, node.statement_formalized), (None, False, False))

    def test_an_unlinked_page_retires_the_module_and_name_an_earlier_sync_wrote(self) -> None:
        # T credits the missing Ext.gone, and keeps an earlier sync's module and name, which the Lean index resolves to
        # the live Ext.helper. Unlinking Ext.gone retires them too: the page then stands for nothing, by a Lean link or
        # by them, and two more identical passes leave it as it is, never Ext.helper's article; Autoform's loader shows
        # it unproved. The same holds for a Mathlib credit the registry does not find. A row with only the module and
        # name still resolves as before (test_a_legacy_row_never_shares_a_declaration_with_another_page).
        from autoform_cli.graph import load_graph

        (wiki.ROOT / "Ext.lean").write_text("theorem helper : True := trivial\n")
        index = SimpleNamespace(declarations={"Ext.helper": SimpleNamespace(keyword="theorem", path=Path("Ext.lean"),
                                                                            line=1)})
        registry = {"left_out": {}, "bridges": {}, "mathlib": {}, "missing": ["M.gone"], "project": []}
        legacy = {"module": "Ext", "name": "helper"}
        mathlib = {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.gone"}}
        self.page("README.md", "# Roadmap\n\n- [Algebra](Algebra/README.md)\n")
        self.page("Algebra/README.md", "# Algebra\n\n- [T](t.md)\n")
        self.page("Algebra/t.md", "# T\n\nA statement.\n")
        cases = {
            "an ATLAS link": (
                self.about("Algebra/t.md", id=UNLINKED, object=[{"location": {"declaration": "Ext.gone"}}],
                           kind="theorem", status="formalized", extensions={sync.OWN: {**legacy, "from": "docstring"}}),
                self.about("Algebra/t.md", id=UNLINKED, extensions={sync.OWN: {"from": "docstring"}}),
                "Ext.gone (Algebra/t.md)"),
            "a Mathlib credit": (
                self.about("Algebra/t.md", id=UNLINKED, object=[mathlib], kind="theorem",
                           extensions={"org.autoform": {"mathlib": True}, sync.OWN: legacy}),
                self.about("Algebra/t.md", id=UNLINKED),
                "M.gone (Algebra/t.md, credited to Mathlib, missing from Mathlib)"),
        }
        for case, (row, unlinked_row, message) in cases.items():
            with self.subTest(case=case):
                self.annotate([row])
                for run in range(3):
                    counts, unlinked = sync.apply_lean_facts(index, {}, registry)
                    self.assertEqual((unlinked, counts["articles"]), ([message] if run == 0 else [], 0))
                    rows = sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]
                    self.assertEqual(rows, [unlinked_row])
                    self.assert_ids_kept([UNLINKED])
                    self.assertEqual((sync.page_owner(rows[0]), sync.legacy_pair(rows[0]),
                                      sync.annotation_key(rows[0], index)), (("none", None, None), None, None))
                    node = load_graph(wiki.VAULT).nodes["Algebra/t"]
                    self.assertEqual((node.lean, node.statement_formalized, node.proof_formalized),
                                     (None, False, False))

    def test_an_unlink_that_would_leave_an_owner_writes_nothing(self) -> None:
        # The check every unlink ends with: a row that still credits a declaration, read again, is refused, and
        # lean-facts then stops before it writes anything.
        self.links_folder()
        credited = self.about("Algebra/t.md", object=[{"location": {"declaration": "Ext.a"}}])
        with self.assertRaises(sync.UnlinkError):
            sync.unowned_after(credited, "Ext.gone")
        sync.unowned_after(self.about("Algebra/t.md", object=[{"location": {"declaration": "Ext.a"}, "role": "uses"}]),
                           "Ext.gone")
        # A module and name an earlier sync wrote, left on a row with no Lean link, would stand for a declaration too.
        with self.assertRaises(sync.UnlinkError):
            sync.unowned_after(self.about("Algebra/t.md", extensions={sync.OWN: {"module": "Ext", "name": "a"}}),
                               "Ext.gone")
        self.page("Algebra/t.md", "# T\n\nA statement.\n")
        self.annotate([credited])
        before = (sync.LINKS / "Algebra.jsonl").read_bytes()
        dependency_file = self.tmp / "lean-dependencies.json"
        dependency_file.write_text(json.dumps({"missing_articles": {}, "articles": {}}))
        lean = SimpleNamespace(index_project=lambda *args, **kwargs: SimpleNamespace(declarations={}))
        reader = sync.reader()
        refused = sync.UnlinkError("unlinking Ext.gone from Algebra/t.md would leave it crediting Ext.a; fix its row")
        with patch.dict("sys.modules", {"autoform_cli": SimpleNamespace(lean=lean, annotations=reader),
                                        "autoform_cli.lean": lean, "autoform_cli.annotations": reader}), \
                patch.object(sync, "apply_lean_facts", side_effect=refused), \
                patch("sys.stderr", new_callable=io.StringIO) as err:
            self.assertEqual(sync.run_lean_facts(dependency_file), 1)
        self.assertIn(f"error: {refused}", err.getvalue())
        self.assertEqual((sync.LINKS / "Algebra.jsonl").read_bytes(), before)

    def test_a_legacy_row_never_shares_a_declaration_with_another_page(self) -> None:
        # An earlier sync's module and name that the Lean index resolves to Ext.main, beside a page crediting Ext.main
        # or another such row: lean-facts refuses before it writes any page. A lone such row still gets Ext.main's
        # facts, and one the index does not resolve stays stale.
        (wiki.ROOT / "Ext.lean").write_text("theorem main : True := trivial\n")
        index = SimpleNamespace(declarations={"Ext.main": SimpleNamespace(keyword="theorem", path=Path("Ext.lean"),
                                                                          line=1)})
        lean = SimpleNamespace(index_project=lambda *args, **kwargs: index)
        reader = sync.reader()
        dependency_file = self.tmp / "lean-dependencies.json"
        dependency_file.write_text(json.dumps({"missing_articles": {}, "articles": {
            "Ext.main": {"module": "Ext", "statement": [], "proof": []}}}))
        for name in "abc":
            self.page(f"Algebra/{name}.md", f"# {name.upper()}\n\nA statement.\n")
        explicit = self.about("Algebra/a.md", object=[{"location": {"declaration": "Ext.main"}}])
        legacy = lambda page, module="Ext": self.about(page, extensions={sync.OWN: {"module": module, "name": "main"}})
        planned = self.about

        def run(rows: list[dict]) -> tuple[int, str, bool]:
            self.annotate(rows)
            files = lambda: {path: path.read_bytes() for path in sorted([*wiki.ROADMAP.rglob("*"),
                                                                          *sync.LINKS.iterdir()]) if path.is_file()}
            before = files()
            with patch.dict("sys.modules", {"autoform_cli": SimpleNamespace(lean=lean, annotations=reader),
                                            "autoform_cli.lean": lean, "autoform_cli.annotations": reader}), \
                    patch("sys.stdout", new_callable=io.StringIO), patch("sys.stderr", new_callable=io.StringIO) as err:
                code = sync.run_lean_facts(dependency_file)
            return code, err.getvalue(), files() == before

        shared = "stand for the declaration Ext.main of this project; a declaration has one page"
        legacy_mark = "(by the module and name an earlier sync wrote)"
        for rows, message in (
                ([explicit, legacy("Algebra/b.md"), planned("Algebra/c.md")],
                 f"Algebra/a.md and Algebra/b.md {legacy_mark} both {shared}"),
                ([planned("Algebra/a.md"), legacy("Algebra/b.md"), legacy("Algebra/c.md")],
                 f"Algebra/b.md {legacy_mark} and Algebra/c.md {legacy_mark} both {shared}")):
            with self.subTest(message=message):
                code, err, unchanged = run(rows)
                self.assertEqual((code, unchanged), (1, True))
                self.assertIn(f"error: {message}", err)
        # Controls: the lone resolvable row is Ext.main's page; one whose module the index lacks stays stale.
        for module, facts in (("Ext", ("theorem", "formalized")), ("Ext.Elsewhere", (None, None))):
            with self.subTest(module=module):
                code, err, _ = run([planned("Algebra/a.md"), legacy("Algebra/b.md", module), planned("Algebra/c.md")])
                self.assertEqual(code, 0, err)
                row = {sync.page_name(row): row for row in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
                self.assertEqual((row["Algebra/b.md"].get("kind"), row["Algebra/b.md"].get("status")), facts)

    def test_rows_are_read_over_the_links_folder_s_own_defaults(self) -> None:
        # The folder's defaults file decides, as for Autoform's loader: without one the shorthand end has no type and
        # credits nothing; one Autoform cannot use leaves it no row at all, and the sync refuses it; and an annotation
        # file only one of them reads is named, so that no row is read two ways.
        from autoform_cli.graph import load_graph

        self.page("README.md", "# Roadmap\n\n- [Algebra](Algebra/README.md)\n")
        self.page("Algebra/README.md", "# Algebra\n\n- [A](a.md)\n")
        self.page("Algebra/a.md", "# A\n\nA statement.\n")
        row = self.about("Algebra/a.md", object=[{"location": {"declaration": "Ext.a"}}], kind="theorem",
                         status="formalized")
        self.annotate([row])
        shown = lambda: load_graph(wiki.VAULT).nodes["Algebra/a"]
        self.assertEqual((sync.page_owner(row), shown().statement_formalized), (("atlas", "Ext.a", None), True))
        (sync.LINKS / "_defaults.json").unlink()
        self.assertEqual((sync.page_owner(row), shown().statement_formalized), (("none", None, None), False))
        self.assertEqual(sync.credit_problems(sync.read_annotations()), [])
        (sync.LINKS / "_defaults.json").write_text("[]\n")
        self.assertEqual(sync.credit_problems(sync.read_annotations()),
                         ["Autoform cannot use blueprint/links/_defaults.json, so it reads no row of blueprint/links"])
        self.assertEqual((sync.subject_path(row), sync.page_owner(row), shown().lean),
                         (None, ("none", None, None), None))
        # A page's kind and status are the Lean's, which lean-facts writes or removes: no defaults give them.
        (sync.LINKS / "_defaults.json").write_text(json.dumps({**sync.DEFAULTS, "kind": "def", "status": "formalized"}))
        self.assertEqual(sync.credit_problems(sync.read_annotations()), [
            f"blueprint/links/_defaults.json sets `{key}`, which lean-facts derives for each page from the Lean; "
            "remove it" for key in ("kind", "status")])
        (sync.LINKS / "_defaults.json").write_text(json.dumps(sync.DEFAULTS) + "\n")
        (sync.LINKS / "extra.json").write_text(json.dumps(self.about("Algebra/a.md", status="stated")) + "\n")
        (sync.LINKS / ".hidden.jsonl").write_text("")
        self.assertEqual(sync.credit_problems(sync.read_annotations()), [
            "Autoform reads blueprint/links/extra.json, which the sync does not; keep annotations in "
            "blueprint/links/*.jsonl",
            "the sync reads blueprint/links/.hidden.jsonl, which Autoform does not: it is hidden, a symbolic link or "
            "not a regular file"])
        (sync.LINKS / "extra.json").unlink()
        (sync.LINKS / ".hidden.jsonl").unlink()
        # A line Autoform's parser does not read, here a key given twice, which Python's would read.
        (sync.LINKS / "Algebra.jsonl").write_text(json.dumps(row)[:-1] + ', "kind": "def"}\n')
        self.assertEqual(sync.credit_problems(sync.read_annotations()), [
            "Autoform's reader leaves out what it cannot read: annotations that are not JSON are left out (1): "
            "links/Algebra.jsonl:1 (duplicate key 'kind' in one object)"])

    def test_a_row_that_credits_none_of_its_declarations_is_reported(self) -> None:
        both = self.about("Algebra/a.md", object=[{"location": {"declaration": "Ext.a"}},
                                                  {"location": {"declaration": "Ext.b"}}])
        self.annotate([both, self.about("Algebra/c.md", object=[{"location": {"declaration": "Ext.c"}}])])
        self.assertEqual(sync.unowned(sync.read_annotations()), ["Algebra/a.md"])

    def test_the_declaration_a_page_states_is_never_chosen_by_position(self) -> None:
        # A helper link before the stated declaration: the stated one is the page's, as Autoform reads it.
        self.links_folder()
        row = {"object": [{"location": {"declaration": "Ext.helper"}, "role": "uses"},
                          {"location": {"declaration": "Ext.a"}, "role": "states"}]}
        self.assertEqual(sync.lean_name(row), "Ext.a")
        self.assertIsNone(sync.lean_name({"object": [{"location": {"declaration": "Ext.b"}},
                                                     {"location": {"declaration": "Ext.c"}}]}))

    def test_the_registry_check_needs_no_mathlib_checkout(self) -> None:
        # The wiki job lists M.t with its module, which its Mathlib checkout has; the cards job, with no checkout,
        # still recognises the registry made from that list.
        flag = {"org.autoform": {"mathlib": True}}
        end = [{"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.t", "module": "Mathlib.Right"}}]
        self.page("Algebra/t.md", "# T\n\nT.\n")
        self.annotate([self.about("Algebra/t.md", object=end, extensions=flag)])
        source = self.tmp / ".lake" / "packages" / "mathlib" / "Mathlib" / "Right.lean"
        source.parent.mkdir(parents=True)
        source.write_text("")
        files = sync.read_annotations()
        credited = sync.credited_mathlib(files)[0]
        self.assertEqual(sync.names_text(credited), "M.t\tMathlib.Right\n")
        registry = {"left_out": {}, "bridges": {}, "mutual": [], "project": [], "missing": [], "unplaced": [],
                    "mathlib": {"M.t": {"module": "Mathlib.Right", "kind": "theorem", "proposition": False, "statement": [], "proof": []}},
                    "inputs": {"names_sha256": sync.names_digest(credited), "dump_sha256": "d" * 64,
                               "mathlib_rev": None, "requested": 1,
                               "aliases_sha256": duplicates_digest(), "format": sync.REGISTRY_FORMAT}}
        self.assertEqual(sync.registry_problems(registry, files), [])
        shutil.rmtree(self.tmp / ".lake")
        self.assertEqual(sync.names_text(credited), "M.t\n")
        self.assertEqual(sync.registry_problems(registry, files), [])

    def test_a_missing_credit_leaves_the_row_s_other_links(self) -> None:
        citation = {"type": "doi", "uri": "https://doi.org/10.1000/x"}
        row = {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/a.md"}],
               "object": [{"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.a"}}, citation],
               "extensions": {"org.autoform": {"mathlib": True, "navigation": "module"}}, "kind": "def"}
        sync.drop_mathlib_credit(row)
        self.assertEqual(row, {"subject": row["subject"], "object": [citation],
                               "extensions": {"org.autoform": {"navigation": "module"}}})

    def test_a_mathlib_credited_row_names_no_declaration_of_the_project(self) -> None:
        # An earlier sync's module-and-name hints on a Mathlib-credited row never bind it to a project declaration.
        row = {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/a.md"}],
               "object": [{"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.a"}}],
               "extensions": {"org.autoform": {"mathlib": True}, sync.OWN: {"module": "Ext.A", "name": "a"}}}
        index = SimpleNamespace(declarations={"Ext.a": SimpleNamespace(keyword="def", path=Path("Ext/A.lean"))})
        self.assertIsNone(sync.annotation_key(row, index))

    def test_a_second_pass_replaces_the_facts_of_the_first(self) -> None:
        # A proof dependency that is gone leaves no section, and a definition that gains `sorry` loses its status.
        source = self.tmp / "Ext" / "Groups.lean"
        source.parent.mkdir(parents=True)
        source.write_text("theorem a : True := trivial\ntheorem b : True := trivial\ndef d := 1\n")
        page_a = self.page("Algebra/a.md", "# A\n\nStatement.\n")
        self.page("Algebra/b.md", "# B\n\nAnother.\n")
        self.page("Algebra/d.md", "# D\n\nA number.\n")
        self.annotate([self.about(f"Algebra/{n}.md", object=[{"location": {"declaration": f"Ext.{n}"}}]) for n in "abd"])
        index = SimpleNamespace(declarations={
            f"Ext.{n}": SimpleNamespace(keyword=k, path=Path("Ext/Groups.lean"))
            for n, k in (("a", "theorem"), ("b", "theorem"), ("d", "def"))})
        dependencies = {"Ext.a": {"module": "Ext.Groups", "statement": [], "proof": ["Ext.b"]}}
        sync.apply_lean_facts(index, dependencies)
        self.assertIn("## Proof depends on", page_a.read_text())
        status = lambda: {sync.subject_path(r).name: r.get("status") for r in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        self.assertEqual(status()["d.md"], "formalized")
        source.write_text("theorem a : True := trivial\ntheorem b : True := trivial\ndef d := sorry\n")
        sync.apply_lean_facts(index, {"Ext.a": {"module": "Ext.Groups", "statement": [], "proof": []}})
        self.assertEqual(page_a.read_text(), "# A\n\nStatement.\n\n## Depends on\n\nThis node has no prerequisites.\n")
        self.assertIsNone(status()["d.md"])

    def test_a_sorry_in_an_interpolated_term_is_no_formalized_definition(self) -> None:
        source = self.tmp / "Ext" / "Groups.lean"
        source.parent.mkdir(parents=True)
        source.write_text('def unfinished : String := s!"{(sorry : Nat)}"\ndef done : String := "sorry"\n')
        sorry_source = self.tmp / "Ext" / "Done.lean"
        sorry_source.write_text('def done : String := "sorry"\n')
        self.page("Algebra/unfinished.md", "# Unfinished\n\nA string.\n")
        self.page("Algebra/done.md", "# Done\n\nA string.\n")
        self.annotate([self.about("Algebra/unfinished.md", object=[{"location": {"declaration": "Ext.unfinished"}}]),
                       self.about("Algebra/done.md", object=[{"location": {"declaration": "Ext.done"}}])])
        index = SimpleNamespace(declarations={
            "Ext.unfinished": SimpleNamespace(keyword="def", path=Path("Ext/Groups.lean")),
            "Ext.done": SimpleNamespace(keyword="def", path=Path("Ext/Done.lean"))})
        sync.apply_lean_facts(index, {})
        rows = {sync.subject_path(r).name: r for r in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        self.assertEqual((rows["unfinished.md"].get("kind"), rows["unfinished.md"].get("status")), ("def", None))
        self.assertEqual((rows["done.md"].get("kind"), rows["done.md"].get("status")), ("def", "formalized"))

    def test_a_legacy_page_resolves_through_the_index_when_unambiguous(self) -> None:
        # A page an earlier sync wrote with a module and a name only gets the facts of the one declaration of that
        # module the index gives that name; with two such declarations, it gets none rather than a guess.
        source = self.tmp / "Ext" / "Groups.lean"
        source.parent.mkdir(parents=True)
        source.write_text("theorem_wanted conjecture : True\ndef_wanted wish : Nat\n")
        for name in ("conjecture", "wish", "same"):
            self.page(f"Algebra/{name}.md", f"# {name}\n\nOpen.\n")
        self.annotate([self.about(f"Algebra/{name}.md", extensions={"org.atlas-wiki": {"module": "Ext.Groups", "name": name}})
                       for name in ("conjecture", "wish", "same")])
        path = Path("Ext/Groups.lean")
        index = SimpleNamespace(declarations={
            "Ext.conjecture": SimpleNamespace(keyword="theorem_wanted", path=path),
            "Ext.wish": SimpleNamespace(keyword="def_wanted", path=path),
            "Ext.A.same": SimpleNamespace(keyword="theorem_wanted", path=path),
            "Ext.B.same": SimpleNamespace(keyword="def_wanted", path=path)})
        counts, _ = sync.apply_lean_facts(index, {})
        self.assertEqual((counts["articles"], counts["unresolved"]), (2, 1))
        rows = {sync.subject_path(r).name: r for r in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        self.assertEqual({n: (r.get("kind"), r.get("status")) for n, r in rows.items()},
                         {"conjecture.md": ("theorem", "stated"), "wish.md": ("def", None), "same.md": (None, None)})

    def test_a_page_that_loses_its_declaration_loses_its_facts(self) -> None:
        source = self.tmp / "Ext" / "Groups.lean"
        source.parent.mkdir(parents=True)
        source.write_text("theorem a : True := trivial\n")
        page_a = self.page("Algebra/a.md", "# A\n\nStatement.\n")
        self.annotate([self.about("Algebra/a.md", object=[{"location": {"declaration": "Ext.a"}}])])
        index = SimpleNamespace(declarations={"Ext.a": SimpleNamespace(keyword="theorem", path=Path("Ext/Groups.lean"))})
        sync.apply_lean_facts(index, {})
        self.assertIn("## Depends on", page_a.read_text())
        sync.apply_lean_facts(SimpleNamespace(declarations={}), {})
        self.assertEqual(page_a.read_text(), "# A\n\nStatement.\n")
        row = sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][0]
        self.assertNotIn("kind", row)
        self.assertNotIn("status", row)

    def test_a_planned_page_keeps_its_prerequisites_but_not_a_committed_kind(self) -> None:
        # A page whose annotation names no declaration records its prerequisites by hand (Graph rules, Edges). The
        # Lean owns an annotation's kind and status, so lean-facts drops any committed beside its subject; such a page
        # records its kind under OWN (test_a_page_with_no_lean_link_takes_the_kind_it_records).
        body = ("# Main\n\nPlanned.\n\n## Depends on\n\n- [Base](base.md)\n\n"
                "## Proof depends on\n\n- [Lemma](lemma.md)\n")
        page = self.page("Algebra/main.md", body)
        self.annotate([self.about("Algebra/main.md", kind="theorem", status="stated", id="af_0123456789abcdef01234567",
                                  extensions={"org.autoform": {"not_ready": True}})])
        for _ in range(2):
            counts, unlinked = sync.apply_lean_facts(SimpleNamespace(declarations={}), {})
            self.assertEqual((counts["unresolved"], unlinked), (0, []))
            self.assertEqual(page.read_text(), body)
        row = sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][0]
        self.assertEqual(row, self.about("Algebra/main.md", id="af_0123456789abcdef01234567",
                                         extensions={"org.autoform": {"not_ready": True}}))

    def test_a_held_page_takes_the_kind_of_the_declaration_it_holds_back(self) -> None:
        # A held page is a statement not yet in Lean (docs/BLUEPRINT.md, Writing pages): it takes the kind its
        # declaration would give a linked page, and no status. It keeps the prerequisites it records and is no other
        # page's Lean target.
        (self.tmp / "Ext").mkdir()
        (self.tmp / "Ext" / "Held.lean").write_text(
            "theorem false_claim : 1 = 2 := sorry\ndef bad : Nat := 1\ntheorem_wanted vacuous : True\n"
            "private theorem helper : True := trivial\ndef claim_prop : Prop := 1 = 2\n"
            "theorem typed : True := trivial\n")
        (self.tmp / "Ext" / "Groups.lean").write_text("theorem user : True := trivial\n")
        body = "# Claim\n\nThe source's statement.\n\n## Depends on\n\n- [Bad](bad.md)\n"
        claim = self.page("Algebra/claim.md", body)
        for name in ("bad", "vacuous", "helper", "missing"):
            self.page(f"Algebra/{name}.md", f"# {name}\n\nHeld.\n")
        user = self.page("Algebra/user.md", "# User\n\nUses the helper.\n")

        def held(name: str, reason: str, issue: int | None = 1) -> dict:
            return {sync.OWN: {"held": {"declaration": name, "reason": reason, **({"issue": issue} if issue else {})}}}

        # A page stating a result held back as a `def` of a proposition records `theorem`, which it takes; a recorded
        # kind changes no other held page's (a held theorem recorded as `def` stays a theorem).
        result = held("Ext.claim_prop", "false")
        result[sync.OWN]["kind"] = "theorem"
        self.page("Algebra/result.md", "# Result\n\nA result.\n")
        typed = held("Ext.typed", "false")
        typed[sync.OWN]["kind"] = "def"
        self.page("Algebra/typed.md", "# Typed\n\nA result.\n")
        self.annotate([
            self.about("Algebra/claim.md", extensions=held("Ext.false_claim", "false")),
            self.about("Algebra/bad.md", status="formalized", extensions=held("Ext.bad", "mis-specified")),
            self.about("Algebra/vacuous.md", extensions=held("Ext.vacuous", "vacuous")),
            self.about("Algebra/helper.md", extensions=held("Ext.helper", "private by design", None)),
            self.about("Algebra/missing.md", extensions=held("Ext.missing", "false")),
            self.about("Algebra/result.md", extensions=result),
            self.about("Algebra/typed.md", extensions=typed),
            self.about("Algebra/user.md", object=[{"location": {"declaration": "Ext.user"}}]),
        ])
        held_source, source = Path("Ext/Held.lean"), Path("Ext/Groups.lean")
        index = SimpleNamespace(declarations={
            "Ext.false_claim": SimpleNamespace(keyword="theorem", path=held_source),
            "Ext.bad": SimpleNamespace(keyword="def", path=held_source),
            "Ext.vacuous": SimpleNamespace(keyword="theorem_wanted", path=held_source),
            "Ext.helper": SimpleNamespace(keyword="theorem", path=held_source),
            "Ext.claim_prop": SimpleNamespace(keyword="def", path=held_source),
            "Ext.typed": SimpleNamespace(keyword="theorem", path=held_source),
            "Ext.user": SimpleNamespace(keyword="theorem", path=source)})
        dependencies = {"Ext.user": {"module": "Ext.Groups", "statement": [], "proof": ["Ext.helper"]}}
        for _ in range(2):
            counts, unlinked = sync.apply_lean_facts(index, dependencies)
            self.assertEqual((counts, unlinked), ({"articles": 1, "unresolved": 0, "edges": 0, "mathlib": 0}, []))
            rows = {sync.subject_path(r).name: r for r in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
            facts = {name: (row.get("kind"), row.get("status"), "object" in row) for name, row in rows.items()}
            self.assertEqual(facts, {
                "claim.md": ("theorem", None, False), "bad.md": ("def", None, False),
                "vacuous.md": ("theorem", None, False), "helper.md": ("theorem", None, False),
                "missing.md": (None, None, False), "result.md": ("theorem", None, False),
                "typed.md": ("theorem", None, False), "user.md": ("theorem", "formalized", True)})
            self.assertEqual(claim.read_text(), body)
            self.assertEqual(user.read_text(),
                             "# User\n\nUses the helper.\n\n## Depends on\n\nThis node has no prerequisites.\n")

    def test_a_held_marker_that_declarations_reports_gives_no_kind(self) -> None:
        # Held markers count as declarations takes them: one that an earlier page already holds, that the index does
        # not resolve or that names no declaration gives its page no kind, even one the row records, so no declaration
        # is counted twice; so does one whose declaration another page links, which run_lean_facts refuses first
        # (held_conflicts). Folder rows hold nothing, and lean-facts reads none of them, malformed or not.
        (self.tmp / "Ext").mkdir()
        (self.tmp / "Ext" / "Held.lean").write_text("theorem a : True := trivial\ntheorem b : True := trivial\n")
        for name in ("linked", "holds-linked", "first", "second", "unresolved", "unnamed"):
            self.page(f"Algebra/{name}.md", f"# {name}\n\nText.\n")

        def held(name: str | None, kind: str | None = None) -> dict:
            marker = {"held": {"reason": "false", "issue": 1, **({"declaration": name} if name else {})}}
            return {sync.OWN: {**marker, **({"kind": kind} if kind else {})}}

        folders = [{"subject": [{"type": "generic", "uri": "../roadmap/Algebra/README.md"}], "extensions": None},
                   self.about("Algebra/sub/README.md", extensions={sync.OWN: "module name"})]
        self.annotate([*folders,
                       self.about("Algebra/linked.md", object=[{"location": {"declaration": "Ext.a"}}]),
                       self.about("Algebra/holds-linked.md", extensions=held("Ext.a", "theorem")),
                       self.about("Algebra/first.md", extensions=held("Ext.b")),
                       self.about("Algebra/second.md", extensions=held("Ext.b", "def")),
                       self.about("Algebra/unresolved.md", extensions=held("Ext.gone", "theorem")),
                       self.about("Algebra/unnamed.md", extensions=held(None, "lemma"))])
        path = Path("Ext/Held.lean")
        index = SimpleNamespace(declarations={"Ext.a": SimpleNamespace(keyword="theorem", path=path),
                                              "Ext.b": SimpleNamespace(keyword="lemma", path=path)})
        for _ in range(2):
            sync.apply_lean_facts(index, {"Ext.a": {"module": "Ext.Held", "statement": [], "proof": []}})
            rows = sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]
            self.assertEqual(rows[:2], folders)
            self.assertEqual({sync.subject_path(row).name: row.get("kind") for row in rows[2:]},
                             {"linked.md": "theorem", "holds-linked.md": None, "first.md": "lemma", "second.md": None,
                              "unresolved.md": None, "unnamed.md": None})

    def test_every_page_that_builds_unlinked_takes_its_kind_the_same_way(self) -> None:
        # Planned, stale (a declaration of this project or of Mathlib that the build does not have, or a module and
        # name the index does not resolve), held: each page that builds with no Lean link takes the kind it records,
        # or its held declaration's, and no status; a later holder of a declaration gets none. A second pass writes
        # what the first wrote.
        (self.tmp / "Ext").mkdir()
        (self.tmp / "Ext" / "Groups.lean").write_text("def d : Nat := 1\ntheorem e : True := trivial\n")
        planned = self.page("Algebra/planned.md", "# Planned\n\nText.\n\n## Depends on\n\n- [Linked](linked.md)\n")
        for name in ("gone", "legacy", "unfound", "holder", "late", "linked"):
            self.page(f"Algebra/{name}.md", f"# {name}\n\nText.\n")

        def own(**fields) -> dict:
            return {sync.OWN: fields}

        held = {"declaration": "Ext.e", "reason": "false", "issue": 1}
        unfound = [{"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.gone"}}]
        self.annotate([
            self.about("Algebra/planned.md", extensions=own(kind="def")),
            self.about("Algebra/gone.md", object=[{"location": {"declaration": "Ext.gone"}}],
                       extensions=own(kind="lemma")),
            self.about("Algebra/legacy.md", extensions=own(module="Ext.Moved", name="moved", kind="theorem")),
            self.about("Algebra/unfound.md", object=unfound,
                       extensions={"org.autoform": {"mathlib": True}, **own(kind="def")}),
            self.about("Algebra/holder.md", extensions=own(held=held)),
            self.about("Algebra/late.md", extensions=own(held=held, kind="def")),
            self.about("Algebra/linked.md", object=[{"location": {"declaration": "Ext.d"}}]),
        ])
        source = Path("Ext/Groups.lean")
        index = SimpleNamespace(declarations={"Ext.d": SimpleNamespace(keyword="def", path=source),
                                              "Ext.e": SimpleNamespace(keyword="theorem", path=source)})
        registry = {"left_out": {}, "bridges": {}, "mathlib": {}, "missing": ["M.gone"], "project": [], "mutual": []}

        def written() -> dict[Path, bytes]:
            return {path: path.read_bytes() for path in sorted(self.tmp.rglob("*")) if path.is_file()}

        outputs = []
        for _ in range(2):
            sync.apply_lean_facts(index, {"Ext.d": {"module": "Ext.Groups", "statement": [], "proof": []}}, registry)
            outputs.append(written())
        self.assertEqual(outputs[0], outputs[1])
        rows = {sync.subject_path(r).name: r for r in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        facts = {name: (row.get("kind"), row.get("status"), "object" in row) for name, row in rows.items()}
        self.assertEqual(facts, {
            "planned.md": ("def", None, False), "gone.md": ("lemma", None, False),
            "legacy.md": ("theorem", None, False), "unfound.md": ("def", None, False),
            "holder.md": ("theorem", None, False), "late.md": (None, None, False),
            "linked.md": ("def", "formalized", True)})
        self.assertEqual(planned.read_text(), "# Planned\n\nText.\n\n## Depends on\n\n- [Linked](linked.md)\n")

    def test_a_page_with_no_lean_link_takes_the_kind_it_records(self) -> None:
        # A page that holds no declaration back, or whose declaration the Lean no longer has, takes the kind its
        # annotation records under OWN when it is a kind lean-facts gives linked pages (run_lean_facts refuses any other
        # value first, kind_problems); a linked page takes the Lean's.
        (self.tmp / "Ext").mkdir()
        (self.tmp / "Ext" / "Groups.lean").write_text("theorem lagrange : True := trivial\n")
        body = "# Planned\n\nA definition.\n\n## Depends on\n\n- [Lagrange](lagrange.md)\n"
        planned = self.page("Algebra/planned.md", body)
        for name in ("lagrange", "stated", "typo", "listed", "gone", "legacy"):
            self.page(f"Algebra/{name}.md", f"# {name}\n\nText.\n")

        def own(**fields) -> dict:
            return {sync.OWN: fields}

        self.annotate([
            self.about("Algebra/planned.md", extensions=own(kind="def")),
            self.about("Algebra/stated.md", kind="def", status="stated", extensions=own(kind="theorem")),
            self.about("Algebra/typo.md", extensions=own(kind="theroem")),
            self.about("Algebra/listed.md", extensions=own(kind=["theorem"])),
            self.about("Algebra/gone.md", object=[{"location": {"declaration": "Ext.gone"}}],
                       extensions=own(kind="theorem")),
            self.about("Algebra/legacy.md", extensions=own(module="Ext.Moved", name="moved", kind="lemma")),
            self.about("Algebra/lagrange.md", object=[{"location": {"declaration": "Ext.lagrange"}}],
                       extensions=own(kind="def")),
        ])
        lagrange = SimpleNamespace(keyword="theorem", path=Path("Ext/Groups.lean"))
        index = SimpleNamespace(declarations={"Ext.lagrange": lagrange})
        for _ in range(2):
            sync.apply_lean_facts(index, {"Ext.lagrange": {"module": "Ext.Groups", "statement": [], "proof": []}})
            rows = {sync.subject_path(r).name: r for r in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
            self.assertEqual({name: (row.get("kind"), row.get("status")) for name, row in rows.items()}, {
                "planned.md": ("def", None), "stated.md": ("theorem", None), "typo.md": (None, None),
                "listed.md": (None, None), "gone.md": ("theorem", None), "legacy.md": ("lemma", None),
                "lagrange.md": ("theorem", "formalized")})
            self.assertNotIn("object", rows["gone.md"])
            self.assertEqual(planned.read_text(), body)

    def test_a_task_never_names_a_declaration_its_page_only_refers_to(self) -> None:
        # Autoform takes every declaration of this project a row names, a reference included, for its page's Lean
        # target: a page that builds with no Lean link but still names one, held or left with a helper when its own
        # declaration went, gets no kind, so `autoform work list` gives it no task naming that declaration. A held
        # page that names none is a statement task with no Lean target.
        from autoform_cli.work import list_ready_work

        (self.tmp / "Ext").mkdir()
        (self.tmp / "Ext" / "Groups.lean").write_text("theorem helper : True := trivial\n")
        (self.tmp / "Ext" / "Held.lean").write_text("theorem claim : 1 = 2 := sorry\ndef bad : Nat := 1\n")
        names = ("plain", "refers", "stale", "helper")
        self.page("README.md", "# Roadmap\n\n- [Algebra](Algebra/README.md)\n")
        self.page("Algebra/README.md", "# Algebra\n\n" + "".join(f"- [{name}]({name}.md)\n" for name in names))
        for name in names:
            self.page(f"Algebra/{name}.md", f"# {name}\n\nA statement.\n")

        def held(name: str) -> dict:
            return {sync.OWN: {"held": {"declaration": name, "reason": "false", "issue": 1}}}

        uses = {"location": {"declaration": "Ext.helper"}, "role": "uses"}
        self.annotate([
            self.about("Algebra/plain.md", id="af_000000000000000000000001", extensions=held("Ext.claim")),
            self.about("Algebra/refers.md", id="af_000000000000000000000002", object=[uses],
                       extensions=held("Ext.bad")),
            self.about("Algebra/stale.md", id="af_000000000000000000000003",
                       object=[{"location": {"declaration": "Ext.gone"}, "role": "states"},
                               {"location": {"declaration": "Ext.helper"}}],
                       extensions={sync.OWN: {"kind": "lemma"}}),
            self.about("Algebra/helper.md", id="af_000000000000000000000004",
                       object=[{"location": {"declaration": "Ext.helper"}}]),
        ])
        source, held_source = Path("Ext/Groups.lean"), Path("Ext/Held.lean")
        index = SimpleNamespace(declarations={"Ext.helper": SimpleNamespace(keyword="theorem", path=source),
                                              "Ext.claim": SimpleNamespace(keyword="theorem", path=held_source),
                                              "Ext.bad": SimpleNamespace(keyword="def", path=held_source)})
        sync.apply_lean_facts(index, {"Ext.helper": {"module": "Ext.Groups", "statement": [], "proof": []}})
        rows = {sync.subject_path(r).name: r for r in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        self.assertEqual({name: rows[f"{name}.md"].get("kind") for name in names},
                         {"plain": "theorem", "refers": None, "stale": None, "helper": "theorem"})
        self.assertEqual(rows["stale.md"]["object"], [uses])
        tasks = {item.node_id: (item.phase, [target.declaration for target in item.lean_targets])
                 for item in list_ready_work(wiki.VAULT).items}
        self.assertEqual(tasks, {"Algebra/plain": ("statement", [])})

    def test_lean_facts_reads_held_markers_as_declarations_does(self) -> None:
        # One reading of held markers, a folder row's included: lean-facts gives the declaration's kind to exactly
        # the pages whose marker declarations lists as held, and to none whose marker it reports, whatever they record.
        (self.tmp / "Ext").mkdir()
        (self.tmp / "Ext" / "Held.lean").write_text("theorem f : True := trivial\ndef g : Nat := 0\n")
        self.page("Algebra/README.md", "# Algebra\n\n" + "".join(f"- [{name}]({name}.md)\n" for name in "dfgh")
                  + "- [Sub](sub/README.md)\n")
        self.page("Algebra/sub/README.md", "# Sub\n\nA folder.\n")
        for name in "dfgh":
            self.page(f"Algebra/{name}.md", f"# {name}\n\nHeld.\n")

        def held(name: str, **own) -> dict:
            return {sync.OWN: {"held": {"declaration": name, "reason": "false", "issue": 1}, **own}}

        self.annotate([
            self.about("Algebra/sub/README.md", extensions=held("Ext.f")),
            self.about("Algebra/f.md", extensions=held("Ext.f", kind="theorem")),
            self.about("Algebra/g.md", extensions=held("Ext.g")),
            self.about("Algebra/h.md", extensions=held("Ext.g", kind="def")),
            self.about("Algebra/d.md", extensions=held("Ext.renamed", kind="theorem")),
        ])
        path = Path("Ext/Held.lean")
        index = SimpleNamespace(declarations={"Ext.f": SimpleNamespace(keyword="theorem", path=path),
                                              "Ext.g": SimpleNamespace(keyword="def", path=path)})
        report = sync.apply_declarations([declaration("Ext.f", "f", "F", "F."), declaration("Ext.g", "g", "G", "G.")],
                                         index)
        self.assertEqual(report["held"], ["Ext.f (Algebra/sub/README.md)", "Ext.g (Algebra/g.md)"])
        self.assertEqual(report["held_problems"], [
            "Algebra/d.md: it holds Ext.renamed back, which the Lean index does not resolve",
            "Algebra/f.md: it holds Ext.f back, as Algebra/sub/README.md does",
            "Algebra/h.md: it holds Ext.g back, as Algebra/g.md does",
        ])
        sync.apply_lean_facts(index, {})
        rows = sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]
        self.assertEqual({str(sync.subject_path(row).relative_to(wiki.ROADMAP / "Algebra")): row.get("kind")
                          for row in rows},
                         {"sub/README.md": None, "f.md": None, "g.md": "def", "h.md": None, "d.md": None})

    def test_lean_facts_refuses_a_kind_it_would_not_take(self) -> None:
        # A recorded kind lean-facts would not take is an error before anything is written, not a page silently left
        # uncounted or counted as its held declaration's kind: a value that is no kind, and a kind on a held page other
        # than `theorem` or `lemma` over a definition command. Folder rows are not read.
        (self.tmp / "Ext").mkdir()
        (self.tmp / "Ext" / "Held.lean").write_text("theorem claim : True := trivial\ndef claim_prop : Prop := True\n")
        names = ("typo", "listed", "planned", "over-theorem", "over-def", "def-over-def")
        self.page("README.md", "# Roadmap\n\n- [Algebra](Algebra/README.md)\n")
        self.page("Algebra/README.md", "# Algebra\n\n" + "".join(f"- [{name}]({name}.md)\n" for name in names))
        for name in names:
            self.page(f"Algebra/{name}.md", f"# {name}\n\nA statement.\n")

        def own(**fields) -> dict:
            return {sync.OWN: fields}

        held = lambda name: {"declaration": name, "reason": "false", "issue": 1}
        self.annotate([
            self.about("README.md"),
            self.about("Algebra/README.md", extensions=own(kind="theroem")),
            self.about("Algebra/typo.md", extensions=own(kind="theroem")),
            self.about("Algebra/listed.md", extensions=own(kind=["theorem"])),
            self.about("Algebra/planned.md", extensions=own(kind="lemma")),
            self.about("Algebra/over-theorem.md", extensions=own(held=held("Ext.claim"), kind="def")),
            self.about("Algebra/over-def.md", extensions=own(held=held("Ext.claim_prop"), kind="theorem")),
            self.about("Algebra/def-over-def.md", extensions=own(held=held("Ext.claim_prop"), kind="def")),
        ])
        path = Path("Ext/Held.lean")
        index = SimpleNamespace(declarations={"Ext.claim": SimpleNamespace(keyword="theorem", path=path),
                                              "Ext.claim_prop": SimpleNamespace(keyword="def", path=path)})
        files = sync.read_annotations()
        self.assertEqual([problem.split(":")[0] for problem in sync.kind_problems(files)],
                         ["Algebra/typo.md", "Algebra/listed.md"])
        self.assertEqual([problem.split(":")[0] for problem in sync.kind_problems(files, index)],
                         ["Algebra/typo.md", "Algebra/listed.md", "Algebra/over-theorem.md", "Algebra/def-over-def.md"])
        self.assertIn("it records the kind 'theroem', which is none of", sync.kind_problems(files)[0])
        before = (sync.LINKS / "Algebra.jsonl").read_bytes()
        (self.tmp / "deps.json").write_text(json.dumps({"articles": {}}))
        with patch("autoform_cli.lean.index_project", return_value=index):
            err = io.StringIO()
            with redirect_stderr(err):
                code = sync.run_lean_facts(self.tmp / "deps.json")
        self.assertEqual(code, 1)
        self.assertIn("Algebra/over-theorem.md: it holds Ext.claim back, a theorem, and records the kind def",
                      err.getvalue())
        self.assertEqual((sync.LINKS / "Algebra.jsonl").read_bytes(), before)

    def test_an_expansion_keeps_a_planned_prerequisite_only_on_a_planned_page(self) -> None:
        # Graph rules, expanding a node: a new page whose proof needs the planned page B stays planned and keeps that
        # edge; made a wanted statement too early, it would lose it, since its edges come only from the Lean.
        source = self.tmp / "Ext" / "Groups.lean"
        source.parent.mkdir(parents=True)
        source.write_text("theorem_wanted early : True\n")
        self.page("Algebra/b.md", "# B\n\nStill planned.\n")
        waiting = "# Waiting\n\nPlanned.\n\n## Depends on\n\nThis node has no prerequisites.\n\n## Proof depends on\n\n- [B](b.md)\n"
        kept = self.page("Algebra/waiting.md", waiting)
        early = self.page("Algebra/early.md", "# Early\n\nWanted.\n\n## Proof depends on\n\n- [B](b.md)\n")
        self.annotate([self.about("Algebra/b.md"), self.about("Algebra/waiting.md"),
                       self.about("Algebra/early.md", object=[{"location": {"declaration": "Ext.early"}}])])
        index = SimpleNamespace(declarations={"Ext.early": SimpleNamespace(keyword="theorem_wanted",
                                                                           path=Path("Ext/Groups.lean"))})
        sync.apply_lean_facts(index, {"Ext.early": {"module": "Ext.Groups", "statement": [], "proof": []}})
        self.assertEqual(kept.read_text(), waiting)
        self.assertEqual(early.read_text(), "# Early\n\nWanted.\n\n## Depends on\n\nThis node has no prerequisites.\n")

    def test_a_wanted_statement_records_no_proof_edge_to_an_unproved_prerequisite(self) -> None:
        # Graph rules, expanding a node: B is in Lean but unproved. A wanted statement has no proof, so the Lean
        # records no proof edge from it to B; only a page that stays planned keeps that edge.
        source = self.tmp / "Ext" / "Groups.lean"
        source.parent.mkdir(parents=True)
        source.write_text("theorem_wanted b : True\ntheorem_wanted early : True\n")
        self.page("Algebra/b.md", "# B\n\nUnproved.\n")
        waiting = "# Waiting\n\nPlanned.\n\n## Depends on\n\nThis node has no prerequisites.\n\n## Proof depends on\n\n- [B](b.md)\n"
        kept = self.page("Algebra/waiting.md", waiting)
        early = self.page("Algebra/early.md", "# Early\n\nWanted.\n\n## Proof depends on\n\n- [B](b.md)\n")
        self.annotate([self.about("Algebra/b.md", object=[{"location": {"declaration": "Ext.b"}}]),
                       self.about("Algebra/waiting.md"),
                       self.about("Algebra/early.md", object=[{"location": {"declaration": "Ext.early"}}])])
        wanted = SimpleNamespace(keyword="theorem_wanted", path=Path("Ext/Groups.lean"))
        sync.apply_lean_facts(SimpleNamespace(declarations={"Ext.b": wanted, "Ext.early": wanted}),
                              {name: {"module": "Ext.Groups", "statement": [], "proof": []} for name in ("Ext.b", "Ext.early")})
        rows = {sync.subject_path(r).name: r for r in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        self.assertEqual((rows["b.md"]["kind"], rows["b.md"]["status"]), ("theorem", "stated"))
        self.assertEqual(kept.read_text(), waiting)
        self.assertEqual(early.read_text(), "# Early\n\nWanted.\n\n## Depends on\n\nThis node has no prerequisites.\n")

    def test_pages_taken_from_docstrings_get_their_facts(self) -> None:
        # declarations marks its pages with OWN's "from", which names a module only for a page with no Lean name.
        source = self.tmp / "Ext" / "Groups.lean"
        source.parent.mkdir(parents=True)
        source.write_text("theorem lagrange : True := trivial\ntheorem_wanted conjecture : True\n")
        self.page("Algebra/lagrange.md", "# Lagrange's theorem\n\nIt divides.\n")
        self.page("Algebra/conjecture.md", "# Conjecture\n\nOpen.\n")
        self.annotate([
            self.about("Algebra/lagrange.md", object=[{"location": {"declaration": "Ext.lagrange"}}],
                       extensions={"org.atlas-wiki": {"from": "docstring"}}),
            self.about("Algebra/conjecture.md",
                       extensions={"org.atlas-wiki": {"from": "docstring", "module": "Ext.Groups", "name": "conjecture"}}),
        ])
        declarations = {"Ext.lagrange": SimpleNamespace(keyword="theorem", path=Path("Ext/Groups.lean")),
                        "Ext.conjecture": SimpleNamespace(keyword="theorem_wanted", path=Path("Ext/Groups.lean"))}
        dependencies = {"Ext.lagrange": {"module": "Ext.Groups", "statement": ["Ext.conjecture"], "proof": []},
                        "Ext.conjecture": {"module": "Ext.Groups", "statement": [], "proof": []}}
        counts, unlinked = sync.apply_lean_facts(SimpleNamespace(declarations=declarations), dependencies)
        self.assertEqual((counts, unlinked), ({"articles": 2, "unresolved": 0, "edges": 1, "mathlib": 0}, []))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "lagrange.md").read_text(),
                         "# Lagrange's theorem\n\nIt divides.\n\n## Depends on\n\n- [Conjecture](conjecture.md)\n")

    def test_a_declaration_the_lean_dropped_leaves_its_page_unlinked(self) -> None:
        # A Lean change that renames or deletes a declaration must not fail the wiki's build.
        self.page("Algebra/gone.md", "# Gone\n\nRemoved upstream.\n")
        self.annotate([self.about("Algebra/gone.md", object=[{"location": {"declaration": "Ext.gone"}}], id="af_1")])
        counts, unlinked = sync.apply_lean_facts(SimpleNamespace(declarations={}), {})
        self.assertEqual(counts["unresolved"], 1)
        self.assertEqual(unlinked, ["Ext.gone (Algebra/gone.md)"])
        row = sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][0]
        self.assertEqual(row, {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/gone.md"}], "id": "af_1"})
        self.assertEqual((wiki.ROADMAP / "Algebra" / "gone.md").read_text(), "# Gone\n\nRemoved upstream.\n")

    def test_pages_the_declarations_sync_wrote_get_their_facts(self) -> None:
        # declarations marks its pages with {"from": "docstring"}; an earlier sync also wrote a module and a name for
        # a page without a Lean link, which lean-facts reads through the index.
        source = self.tmp / "Ext" / "Groups.lean"
        source.parent.mkdir(parents=True)
        source.write_text("theorem order_pos : True := trivial\ntheorem_wanted conjecture : True\n")
        self.page("Algebra/order-pos.md", "# Order is positive\n\nIt is.\n")
        self.page("Algebra/conjecture.md", "# Conjecture\n\nOpen.\n")
        self.annotate([
            self.about("Algebra/order-pos.md", object=[{"location": {"declaration": "Ext.order_pos"}}],
                       extensions={"org.atlas-wiki": {"from": "docstring"}}),
            self.about("Algebra/conjecture.md",
                       extensions={"org.atlas-wiki": {"from": "docstring", "module": "Ext.Groups", "name": "conjecture"}}),
        ])
        declarations = {"Ext.order_pos": SimpleNamespace(keyword="theorem", path=Path("Ext/Groups.lean")),
                        "Ext.conjecture": SimpleNamespace(keyword="theorem_wanted", path=Path("Ext/Groups.lean"))}
        dependencies = {
            "Ext.order_pos": {"module": "Ext.Groups", "statement": [], "proof": ["Ext.conjecture"]},
            "Ext.conjecture": {"module": "Ext.Groups", "statement": [], "proof": []},
        }
        counts, unlinked = sync.apply_lean_facts(SimpleNamespace(declarations=declarations), dependencies)
        self.assertEqual(counts, {"articles": 2, "unresolved": 0, "edges": 1, "mathlib": 0})
        self.assertEqual(unlinked, [])
        rows = {sync.subject_path(row).name: row for row in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        self.assertEqual((rows["order-pos.md"]["kind"], rows["order-pos.md"]["status"]), ("theorem", "formalized"))
        self.assertEqual(rows["order-pos.md"]["extensions"], {"org.atlas-wiki": {"from": "docstring"}})
        self.assertEqual(rows["conjecture.md"]["kind"], "theorem")
        self.assertEqual(
            (wiki.ROADMAP / "Algebra" / "order-pos.md").read_text(),
            "# Order is positive\n\nIt is.\n\n## Depends on\n\nThis node has no prerequisites.\n\n"
            "## Proof depends on\n\n- [Conjecture](conjecture.md)\n",
        )


def declaration(name: str | None, short: str, title: str, text: str, module=("Ext", "Groups")) -> wiki.Target:
    return wiki.Target(book="Ext", idx=0, title=title, slug=wiki.slugify(short), location="Algebra", description=text,
                       declaration="theorem", lean=name, statement=True, proof=True, names=[name or short], module=module,
                       path=wiki.ROADMAP / "Algebra" / "elsewhere" / f"{short}.md")


class UncompiledArticles(unittest.TestCase):
    def test_a_declared_article_without_a_compiled_row_is_reported(self) -> None:
        extracted = {"missing_articles": {"MathlibExt": ["Ext.declared", "Ext.removed"]}, "articles": {}}
        index = SimpleNamespace(declarations={"Ext.declared": None})
        self.assertEqual(sync.uncompiled_articles(extracted, index), ["Ext.declared"])

    def test_a_removed_declaration_is_left_to_unlinking(self) -> None:
        extracted = {"missing_articles": {"MathlibExt": ["Ext.removed"]}, "articles": {}}
        self.assertEqual(sync.uncompiled_articles(extracted, SimpleNamespace(declarations={})), [])

    def test_lean_facts_stops_before_writing(self) -> None:
        index = SimpleNamespace(declarations={"Ext.declared": None})
        lean = SimpleNamespace(index_project=lambda *args, **kwargs: index)
        with tempfile.TemporaryDirectory() as directory:
            dependency_file = Path(directory) / "lean-dependencies.json"
            dependency_file.write_text(json.dumps({"missing_articles": {"MathlibExt": ["Ext.declared"]}, "articles": {}}))
            # Autoform's annotation reader stays the real one: rows are read with it.
            reader = sync.reader()
            with patch.dict("sys.modules", {"autoform_cli": SimpleNamespace(lean=lean, annotations=reader),
                                            "autoform_cli.lean": lean, "autoform_cli.annotations": reader}), \
                    patch.object(sync, "apply_lean_facts") as apply:
                self.assertEqual(sync.run_lean_facts(dependency_file), 1)
                apply.assert_not_called()



class StrayPages(Vault):
    def test_a_page_without_an_annotation_row_stops_lean_facts(self) -> None:
        # An imported folder page with no row would build as a stray page; lean-facts names it and stops.
        self.page("Algebra/README.md", "# Algebra\n")
        self.page("Algebra/groups/README.md", "# Groups\n")
        self.page("Algebra/groups/lagrange.md", "# Lagrange\n")
        self.annotate([self.about("Algebra/README.md"),
                       self.about("Algebra/groups/lagrange.md", object=[{"location": {"declaration": "Ext.lagrange"}}])])
        self.assertEqual(sync.pages_without_rows(), [(wiki.ROADMAP / "Algebra/groups/README.md").resolve()])
        dependency_file = self.tmp / "lean-dependencies.json"
        dependency_file.write_text(json.dumps({"missing_articles": {}, "articles": {}}))
        stderr = io.StringIO()
        with patch.object(sync, "apply_lean_facts") as apply, redirect_stderr(stderr):
            self.assertEqual(sync.run_lean_facts(dependency_file), 1)
            apply.assert_not_called()
        self.assertIn("no annotation row names Algebra/groups/README.md", stderr.getvalue())
        self.annotate([self.about("Algebra/README.md"), self.about("Algebra/groups/README.md"),
                       self.about("Algebra/groups/lagrange.md", object=[{"location": {"declaration": "Ext.lagrange"}}])])
        self.assertEqual(sync.pages_without_rows(), [])

INDEX = SimpleNamespace(declarations={"Ext.old": None})


class Declarations(Vault):
    def test_new_declarations_get_pages_beside_their_module(self) -> None:
        self.page("Algebra/groups/README.md", "# Groups\n\nProse.\n\n- [Old](old.md)\n")
        old = self.page("Algebra/groups/old.md", "# Old, as the wiki wrote it\n\nEdited text.\n")
        self.page("Algebra/README.md", "# Algebra\n\n- [Groups](groups/README.md)\n")
        self.annotate([
            self.about("Algebra/groups/old.md", id="af_000000000000000000000001",
                       object=[{"location": {"declaration": "Ext.old"}}]),
            self.about("Algebra/groups/gone.md", object=[{"location": {"declaration": "Ext.gone"}}]),
        ])
        targets = [
            declaration("Ext.old", "old", "Old", "Upstream text."),
            declaration("Ext.new", "new", "New result", "A new statement."),
            declaration(None, "wanted", "Wanted", "Not in the index."),
            declaration("Other.lone", "lone", "Lone", "A new module.", module=("Other", "Lone")),
        ]
        undocumented = self.tmp / "Ext" / "Groups.lean"
        undocumented.parent.mkdir(parents=True, exist_ok=True)
        undocumented.write_text("theorem kept : True := trivial\n")
        self.annotate([
            *sync.read_annotations()[sync.LINKS / "Algebra.jsonl"],
            self.about("Algebra/groups/kept.md", object=[{"location": {"declaration": "Ext.kept"}}]),
        ])
        index = SimpleNamespace(declarations={"Ext.old": None, "Ext.new": None, "Ext.kept": None})
        report = sync.apply_declarations(targets, index)
        self.assertEqual(report["added"], ["Ext.new -> Algebra/groups/new.md", "Other.lone -> Algebra/lone.md"])
        self.assertEqual(report["unindexed"], ["wanted (no Lean name)"])
        self.assertEqual(report["gone"], ["Ext.gone (Algebra/groups/gone.md)"])
        self.assertEqual(report["changed"], [])
        self.assertEqual(old.read_text(), "# Old, as the wiki wrote it\n\nEdited text.\n")
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "new.md").read_text(), "# New result\n\nA new statement.\n")
        # In source order: the targets' order here.
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         "# Groups\n\nProse.\n\n- [Old](old.md)\n- [New result](new.md)\n")
        self.assertEqual((wiki.ROADMAP / "Algebra" / "README.md").read_text(),
                         "# Algebra\n\n- [Groups](groups/README.md)\n- [Lone](lone.md)\n")
        rows = {sync.subject_path(row).name: row for row in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        self.assertEqual(rows["new.md"]["object"], [{"location": {"declaration": "Ext.new"}}])
        self.assertEqual(rows["new.md"]["extensions"], {"org.atlas-wiki": {"from": "docstring"}})
        self.assertNotIn("wanted.md", rows)
        # Each row the sync adds gets a fresh id (What the tools own); one it already had keeps its own, and one without
        # stays without, for `ids` to give it one.
        self.assertEqual(rows["old.md"]["id"], "af_000000000000000000000001")
        self.assertNotIn("id", rows["gone.md"])
        added = [rows["new.md"]["id"], rows["lone.md"]["id"]]
        for article_id in added:
            self.assertRegex(article_id, r"^af_[0-9a-f]{24}$")
        self.assertEqual(len(set(added + ["af_000000000000000000000001"])), 3)

    def test_a_new_page_never_joins_a_card(self) -> None:
        # A card holds only the statements its editors placed in it (docs/cards.md): a new declaration whose module's
        # pages sit in a card goes beside the card, and the run lists it for an editor.
        self.page("Algebra/README.md", "# Algebra\n\n- [Groups](groups/README.md)\n")
        self.page("Algebra/groups/README.md", "# Groups\n\nProse.\n\n- [Orders](orders/README.md)\n")
        self.page("Algebra/groups/orders/README.md", "# Orders\n\nIt says.\n\n## Idea\n\nWhy.\n\n## Statements\n\n"
                  "- [Old](old.md)\n")
        self.page("Algebra/groups/orders/old.md", "# Old\n\nText.\n")
        card = {"kind": "result", "main": "af_000000000000000000000001", "importance": "key", "level": "undergraduate"}
        self.annotate([
            self.about("Algebra/README.md"), self.about("Algebra/groups/README.md"),
            self.about("Algebra/groups/orders/README.md", id="af_000000000000000000000002",
                       extensions={"org.atlas-wiki": {"card": card}}),
            self.about("Algebra/groups/orders/old.md", id="af_000000000000000000000001",
                       object=[{"location": {"declaration": "Ext.old"}}]),
        ])
        targets = [declaration("Ext.old", "old", "Old", "Text."), declaration("Ext.new", "new", "New", "New text.")]
        report = sync.apply_declarations(targets, SimpleNamespace(declarations={"Ext.old": None, "Ext.new": None}))
        self.assertEqual(report["added"], ["Ext.new -> Algebra/groups/new.md"])
        self.assertEqual(report["unassigned"], ["Algebra/groups/new.md"])
        self.assertFalse((wiki.ROADMAP / "Algebra/groups/orders/new.md").exists())
        self.assertEqual((wiki.ROADMAP / "Algebra/groups/README.md").read_text(),
                         "# Groups\n\nProse.\n\n- [Orders](orders/README.md)\n- [New](new.md)\n")
        self.assertNotIn("New", (wiki.ROADMAP / "Algebra/groups/orders/README.md").read_text())

    def card_beside_a_folder(self) -> None:
        """Algebra/groups holds a page of module Groups and the card orders (docs/cards.md)."""
        self.page("Algebra/README.md", "# Algebra\n\n- [Groups](groups/README.md)\n")
        self.page("Algebra/groups/README.md", "# Groups\n\nProse.\n\n- [G](g.md)\n- [Orders](orders/README.md)\n")
        self.page("Algebra/groups/g.md", "# G\n\nText.\n")
        self.page("Algebra/groups/orders/README.md", "# Orders\n\nIt says.\n\n## Idea\n\nWhy.\n\n## Statements\n\n"
                  "- [Old](old.md)\n")
        self.page("Algebra/groups/orders/old.md", "# Old\n\nText.\n")
        card = {"kind": "result", "main_article_id": "af_000000000000000000000001", "importance": "key",
                "level": "undergraduate"}
        self.annotate([
            self.about("Algebra/README.md"), self.about("Algebra/groups/README.md"),
            self.about("Algebra/groups/g.md", id="af_000000000000000000000003",
                       object=[{"location": {"declaration": "Ext.g"}}]),
            self.about("Algebra/groups/orders/README.md", id="af_000000000000000000000002",
                       extensions={"org.atlas-wiki": {"card": card}}),
            self.about("Algebra/groups/orders/old.md", id="af_000000000000000000000001",
                       object=[{"location": {"declaration": "Ext.old"}}]),
        ])

    def new_module_below_the_card(self, generated: bool) -> dict:
        # generate_wiki lays a new module's folder out inside the card; the run makes no folder or page there,
        # with or without generate_wiki's folder page for it.
        self.card_beside_a_folder()
        new = declaration("Ext.new", "new", "New", "New text.", module=("Ext", "Fresh"))
        new.path = wiki.ROADMAP / "Algebra" / "groups" / "orders" / "fresh" / "new.md"
        layout = {wiki.ROADMAP / "Algebra/groups/orders/fresh/README.md": "# Fresh\n\n- [New](new.md)\n"}
        return sync.apply_declarations(
            [declaration("Ext.g", "g", "G", "Text."), declaration("Ext.old", "old", "Old", "Text."), new],
            SimpleNamespace(declarations={"Ext.g": None, "Ext.old": None, "Ext.new": None}),
            generated=layout if generated else {})

    def assert_beside_the_card(self, report: dict) -> None:
        self.assertEqual(report["added"], ["Ext.new -> Algebra/groups/new.md"])
        self.assertEqual(report["unassigned"], ["Algebra/groups/new.md"])
        self.assertEqual(sorted(path.name for path in (wiki.ROADMAP / "Algebra/groups/orders").iterdir()),
                         ["README.md", "old.md"])

    def test_a_new_module_laid_out_below_a_card_goes_beside_it(self) -> None:
        self.assert_beside_the_card(self.new_module_below_the_card(generated=True))

    def test_the_fallback_to_the_nearest_folder_page_never_lands_in_a_card(self) -> None:
        self.assert_beside_the_card(self.new_module_below_the_card(generated=False))

    def test_a_new_folder_takes_no_recorded_address(self) -> None:
        # generate_wiki lays a new module out in Algebra/groups/former/, an address a moved page left: the run makes
        # no folder there and places the page in the nearest folder the wiki has.
        self.card_beside_a_folder()
        (wiki.ROOT / "scripts").mkdir(exist_ok=True)
        (wiki.ROOT / "scripts" / "card-moves.jsonl").write_text(json.dumps(
            {"page": "Algebra/groups/former", "to": "Algebra/groups/orders/old", "article_id": "af_000000000000000000000001"})
            + "\n")
        new = declaration("Ext.new", "new", "New", "New text.", module=("Ext", "Fresh"))
        new.path = wiki.ROADMAP / "Algebra" / "groups" / "former" / "new.md"
        layout = {wiki.ROADMAP / "Algebra/groups/former/README.md": "# Former\n\n- [New](new.md)\n"}
        report = sync.apply_declarations(
            [declaration("Ext.g", "g", "G", "Text."), declaration("Ext.old", "old", "Old", "Text."), new],
            SimpleNamespace(declarations={"Ext.g": None, "Ext.old": None, "Ext.new": None}), generated=layout)
        self.assertEqual(report["added"], ["Ext.new -> Algebra/groups/new.md"])
        self.assertFalse((wiki.ROADMAP / "Algebra/groups/former").exists())

    def test_a_new_page_takes_no_name_a_folder_or_a_recorded_address_has(self) -> None:
        # A page named like the card's folder would share its node id; a moved page's old address keeps
        # redirecting to its article.
        self.card_beside_a_folder()
        (wiki.ROOT / "scripts").mkdir(exist_ok=True)
        (wiki.ROOT / "scripts" / "card-moves.jsonl").write_text(json.dumps(
            {"page": "Algebra/groups/gone", "to": "Algebra/groups/orders/old", "article_id": "af_000000000000000000000001"})
            + "\n")
        report = sync.apply_declarations(
            [declaration("Ext.g", "g", "G", "Text."), declaration("Ext.old", "old", "Old", "Text."),
             declaration("Ext.orders", "orders", "Orders lemma", "A statement."),
             declaration("Ext.gone", "gone", "Gone lemma", "Another statement.")],
            SimpleNamespace(declarations={"Ext.g": None, "Ext.old": None, "Ext.orders": None, "Ext.gone": None}))
        self.assertEqual(sorted(report["added"]), ["Ext.gone -> Algebra/groups/gone-2.md",
                                                   "Ext.orders -> Algebra/groups/orders-2.md"])

    def test_a_new_page_takes_no_address_a_retired_statement_had(self) -> None:
        # An expansion retired the statement page Algebra/groups/gone, whose address keeps leading to what replaced it
        # (docs/cards.md#move-ledger): a new declaration's page takes another name.
        self.card_beside_a_folder()
        (wiki.ROOT / "scripts").mkdir(exist_ok=True)
        (wiki.ROOT / "scripts" / "card-moves.jsonl").write_text(json.dumps(
            {"statement": "af_000000000000000000000001", "page": "Algebra/groups/gone",
             "replaced_by": "af_000000000000000000000002"}) + "\n")
        self.assertEqual(sync.retired_addresses(), {"Algebra/groups/gone"})
        report = sync.apply_declarations(
            [declaration("Ext.g", "g", "G", "Text."), declaration("Ext.old", "old", "Old", "Text."),
             declaration("Ext.gone", "gone", "Gone lemma", "Another statement.")],
            SimpleNamespace(declarations={"Ext.g": None, "Ext.old": None, "Ext.gone": None}))
        self.assertEqual(report["added"], ["Ext.gone -> Algebra/groups/gone-2.md"])
        self.assertFalse((wiki.ROADMAP / "Algebra/groups/gone.md").exists())

    def test_a_held_declaration_keeps_its_page_unlinked_and_gets_no_other(self) -> None:
        self.page("Algebra/README.md", "# Algebra\n\n- [Claim](claim.md)\n")
        claim = self.page("Algebra/claim.md", "# Claim\n\nThe source's statement.\n")
        held = {"declaration": "Ext.claim", "reason": "false", "issue": 1}
        self.annotate([self.about("Algebra/claim.md", extensions={"org.atlas-wiki": {"held": held}})])
        targets = [declaration("Ext.claim", "claim", "Claim", "A statement that is false as written."),
                   declaration("Ext.new", "new", "New result", "A new statement.")]
        report = sync.apply_declarations(targets, SimpleNamespace(declarations={"Ext.claim": None, "Ext.new": None}))
        self.assertEqual(report["added"], ["Ext.new -> Algebra/new.md"])
        self.assertEqual(report["held"], ["Ext.claim (Algebra/claim.md)"])
        self.assertEqual(claim.read_text(), "# Claim\n\nThe source's statement.\n")
        self.assertFalse((wiki.ROADMAP / "Algebra" / "claim-2.md").exists())
        rows = {sync.subject_path(row).name: row for row in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        self.assertNotIn("object", rows["claim.md"])
        self.assertEqual(rows["claim.md"]["extensions"], {"org.atlas-wiki": {"held": held}})

    def test_a_held_marker_that_cannot_hold_its_declaration_back_is_reported(self) -> None:
        self.page("Algebra/README.md", "# Algebra\n\n" + "".join(f"- [{n.upper()}]({n}.md)\n" for n in "abcdefghi"))
        for name in "abcdefghi":
            self.page(f"Algebra/{name}.md", f"# {name.upper()}\n")
        held = lambda value: {"org.atlas-wiki": {"held": value}}
        self.annotate([
            self.about("Algebra/a.md", extensions=held("Ext.a")),
            self.about("Algebra/b.md", extensions=held({"declaration": ["Ext.b"]})),
            self.about("Algebra/c.md", object=[{"location": {"declaration": "Ext.c"}}],
                       extensions=held({"declaration": "Ext.c", "reason": "false"})),
            self.about("Algebra/d.md", extensions=held({"declaration": "Ext.renamed", "reason": "false"})),
            self.about("Algebra/e.md", object=[{"location": {"declaration": "Ext.e"}}]),
            self.about("Algebra/f.md", extensions=held({"declaration": "Ext.e", "reason": "false"})),
            self.about("Algebra/g.md", extensions=held({"declaration": "Ext.g", "reason": "false"})),
            self.about("Algebra/h.md", extensions=held({"declaration": "Ext.g", "reason": "vacuous"})),
            self.about("Algebra/i.md", object=[{"type": "lean", "uri": sync.MATHLIB, "location": {
                "declaration": "M.real", "module": "Mathlib.A"}}],
                extensions={**held({"declaration": "Ext.i", "reason": "false"}), "org.autoform": {"mathlib": True}}),
        ])
        targets = [declaration("Ext.c", "c", "C", "C."), declaration("Ext.e", "e", "E", "E."),
                   declaration("Ext.g", "g", "G", "G."), declaration("Ext.new", "new", "New", "A new statement.")]
        report = sync.apply_declarations(targets, SimpleNamespace(declarations={f"Ext.{n}": None for n in ("c", "e", "g", "new")}))
        self.assertEqual(report["held"], ["Ext.g (Algebra/g.md)"])
        self.assertEqual(report["held_problems"], [
            "Algebra/a.md: its held marker names no declaration",
            "Algebra/b.md: its held marker names no declaration",
            "Algebra/c.md: it holds Ext.c back but is linked to Ext.c",
            "Algebra/d.md: it holds Ext.renamed back, which the Lean index does not resolve",
            "Algebra/f.md: it holds Ext.e back, which Algebra/e.md links",
            "Algebra/h.md: it holds Ext.g back, as Algebra/g.md does",
            "Algebra/i.md: it holds Ext.i back but is linked to M.real",
        ])
        # A marker the run cannot use stops it before it writes anything.
        self.assertEqual(report["added"], [])
        self.assertFalse((wiki.ROADMAP / "Algebra" / "new.md").exists())

    def test_a_duplicate_gets_no_page_and_is_listed(self) -> None:
        # Lean states Ext.canonical's result again as Ext.twin, which the page's row lists: the run writes no page for
        # the twin, lists it, and leaves the row as it is; a new declaration still gets its page.
        self.page("Algebra/README.md", "# Algebra\n\n- [Canonical](canonical.md)\n")
        canonical = self.page("Algebra/canonical.md", "# Canonical\n\nThe statement.\n")
        row = self.about("Algebra/canonical.md", id="af_000000000000000000000001",
                         object=[{"location": {"declaration": "Ext.canonical"}}],
                         extensions={"org.atlas-wiki": {"from": "docstring", "duplicates": ["Ext.twin"]}})
        self.annotate([self.about("Algebra/README.md"), row])
        targets = [declaration("Ext.canonical", "canonical", "Canonical", "The statement."),
                   declaration("Ext.twin", "twin", "Twin", "The statement, again."),
                   declaration("Ext.new", "new", "New result", "A new statement.")]
        report = sync.apply_declarations(targets, SimpleNamespace(declarations={
            "Ext.canonical": None, "Ext.twin": None, "Ext.new": None}))
        self.assertEqual((report["added"], report["duplicates"], report["duplicate_problems"]),
                         (["Ext.new -> Algebra/new.md"], ["Ext.twin (Algebra/canonical.md)"], []))
        self.assertFalse((wiki.ROADMAP / "Algebra" / "twin.md").exists())
        self.assertEqual(canonical.read_text(), "# Canonical\n\nThe statement.\n")
        self.assertEqual(sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][1], row)
        with redirect_stdout(io.StringIO()) as printed:
            sync.print_report(report)
        self.assertIn("Declarations a page's row lists as stating its result again, which get no page of their own: 1\n"
                      "  Ext.twin (Algebra/canonical.md)\n", printed.getvalue())

    def test_a_duplicates_list_the_run_cannot_use_stops_it(self) -> None:
        names = "abcdefghijklmnopqrs"
        self.page("Algebra/README.md", "# Algebra\n\n" + "".join(f"- [{n.upper()}]({n}.md)\n" for n in names))
        for name in names:
            self.page(f"Algebra/{name}.md", f"# {name.upper()}\n")
        own = lambda **fields: {"org.atlas-wiki": fields}
        link = lambda name: [{"location": {"declaration": name}}]
        uses = lambda name: {"location": {"declaration": name}, "role": "uses"}
        mathlib = {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.real", "module": "Mathlib.A"}}
        self.annotate([
            self.about("Algebra/a.md", object=link("Ext.a"), extensions=own(duplicates="Ext.x")),
            self.about("Algebra/b.md", object=link("Ext.b"), extensions=own(duplicates=["Ext.y", "Ext.y"])),
            self.about("Algebra/c.md", object=link("Ext.c"), extensions=own(duplicates=["Ext.z", ""])),
            self.about("Algebra/d.md", extensions=own(duplicates=["Ext.w"])),
            self.about("Algebra/e.md", extensions=own(held={"declaration": "Ext.e", "reason": "false"},
                                                       duplicates=["Ext.v"])),
            self.about("Algebra/f.md", object=[mathlib],
                       extensions={**own(duplicates=["Ext.u"]), "org.autoform": {"mathlib": True}}),
            self.about("Algebra/g.md", object=link("Ext.g"), extensions=own(duplicates=["Ext.g"])),
            self.about("Algebra/h.md", object=link("Ext.h"), extensions=own(duplicates=["Ext.renamed"])),
            self.about("Algebra/i.md", object=link("Ext.i"), extensions=own(duplicates=["Ext.j"])),
            self.about("Algebra/j.md", object=link("Ext.j")),
            self.about("Algebra/k.md", object=link("Ext.k"), extensions=own(duplicates=["Ext.e"])),
            self.about("Algebra/l.md", object=link("Ext.l"), extensions=own(duplicates=["Ext.t"])),
            self.about("Algebra/m.md", object=link("Ext.m"), extensions=own(duplicates=["Ext.t"])),
            # Another row's reference counts as a credit does: a planned page that uses Ext.s, a page that credits
            # Ext.p and uses Ext.r, and a page an earlier sync wrote with a module and a name the index resolves.
            self.about("Algebra/n.md", object=[uses("Ext.s")]),
            self.about("Algebra/o.md", object=link("Ext.o"), extensions=own(duplicates=["Ext.s"])),
            self.about("Algebra/p.md", object=[{**link("Ext.p")[0], "role": "states"}, uses("Ext.r")]),
            self.about("Algebra/q.md", object=link("Ext.q"), extensions=own(duplicates=["Ext.r"])),
            self.about("Algebra/r.md", extensions=own(module="Ext.Legacy", name="legacy")),
            self.about("Algebra/s.md", object=link("Ext.s2"), extensions=own(duplicates=["Ext.legacy"])),
        ])
        declared = [*"abceghijklmopqrstuvwxyz", "s2", "new"]
        index = SimpleNamespace(declarations={**{f"Ext.{n}": None for n in declared},
                                              "Ext.legacy": SimpleNamespace(path=Path("Ext/Legacy.lean"))})
        report = sync.apply_declarations([declaration("Ext.new", "new", "New", "A new statement.")], index)
        self.assertEqual(report["duplicate_problems"], [
            "Algebra/a.md: its duplicates list is not a list of declaration names, each given once",
            "Algebra/b.md: its duplicates list is not a list of declaration names, each given once",
            "Algebra/c.md: its duplicates list is not a list of declaration names, each given once",
            "Algebra/d.md: it lists duplicates but credits no declaration of this project by a Lean link of its own",
            "Algebra/e.md: it lists duplicates but credits no declaration of this project by a Lean link of its own",
            "Algebra/f.md: it lists duplicates but credits the Mathlib declaration M.real; a Mathlib-credited page "
            "lists none",
            "Algebra/g.md: it lists its own declaration Ext.g as a duplicate",
            "Algebra/i.md: it lists Ext.j as a duplicate, which Algebra/j.md links",
            "Algebra/k.md: it lists Ext.e as a duplicate, which Algebra/e.md holds back",
            "Algebra/m.md: it lists Ext.t as a duplicate, as Algebra/l.md does",
            "Algebra/o.md: it lists Ext.s as a duplicate, which Algebra/n.md links",
            "Algebra/q.md: it lists Ext.r as a duplicate, which Algebra/p.md links",
            "Algebra/s.md: it lists Ext.legacy as a duplicate, which Algebra/r.md links",
        ])
        self.assertEqual(report["held_problems"], [])
        # A name the Lean index does not resolve is the Lean's change, listed for an editor.
        self.assertEqual(report["stale_duplicates"], [
            "Ext.renamed (Algebra/h.md): the Lean index does not resolve it; drop the entry from `duplicates`, keeping "
            "the row's article id and its credit"])
        # A list the run cannot use stops it before it writes anything.
        self.assertEqual(report["added"], [])
        self.assertFalse((wiki.ROADMAP / "Algebra" / "new.md").exists())

    def test_a_duplicates_entry_the_lean_left_stale_is_listed_and_stops_nothing(self) -> None:
        # The Lean deleted Ext.gone, which Lagrange's row lists, and Ext.old, whose row lists Ext.kept: Lean changes,
        # which fail no run. The run writes the new declaration's page and lists both entries for an editor.
        self.page("Algebra/README.md", "# Algebra\n\n- [Lagrange](lagrange.md)\n- [Old](old.md)\n")
        self.page("Algebra/lagrange.md", "# Lagrange\n")
        self.page("Algebra/old.md", "# Old\n")
        listed = lambda *names: {"org.atlas-wiki": {"duplicates": list(names)}}
        self.annotate([self.about("Algebra/README.md"),
                       self.about("Algebra/lagrange.md", object=[{"location": {"declaration": "Ext.lagrange"}}],
                                  extensions=listed("Ext.gone")),
                       self.about("Algebra/old.md", object=[{"location": {"declaration": "Ext.old"}}],
                                  extensions=listed("Ext.kept"))])
        index = SimpleNamespace(declarations={"Ext.lagrange": None, "Ext.kept": None, "Ext.new": None})
        report = sync.apply_declarations([declaration("Ext.lagrange", "lagrange", "Lagrange", "Lagrange."),
                                          declaration("Ext.kept", "kept", "Kept", "Kept."),
                                          declaration("Ext.new", "new", "New", "A new statement.")], index)
        self.assertEqual((report["duplicate_problems"], report["added"]), ([], ["Ext.new -> Algebra/new.md"]))
        self.assertEqual(report["gone"], ["Ext.old (Algebra/old.md)"])
        self.assertEqual(report["stale_duplicates"], [
            "Ext.gone (Algebra/lagrange.md): the Lean index does not resolve it; drop the entry from `duplicates`, "
            "keeping the row's article id and its credit",
            "Ext.kept (Algebra/old.md): the Lean index does not resolve the page's declaration Ext.old, so a use of "
            "Ext.kept counts for no page; relink the page or drop the entry"])
        with redirect_stdout(io.StringIO()) as printed:
            sync.print_report(report)
        self.assertIn("Duplicates entries the Lean left stale, to drop or relink: 2\n", printed.getvalue())

    def test_a_duplicates_list_needs_the_row_s_own_lean_link(self) -> None:
        # The links folder's defaults link Ext.t, so a row with no `object`, or with an end the defaults fill in whole
        # (`{}`, or one giving only a role), credits it as Autoform reads it; the folder page's row masks them. Such a
        # row lists no duplicates: its own `object` names no declaration. Nor does a row whose end with role `states`
        # takes Ext.t from the defaults while another end names it, with role `uses` or with no role, whatever their
        # order: that end is a reference, and the credit is not its. The shorthand end that names the declaration and
        # takes the defaults' type and uri is the row's own, beside an inherited reference too, and so is one of the
        # ends with no role that give the credit together.
        self.page("Algebra/README.md", "# Algebra\n\n- [T](t.md)\n")
        self.page("Algebra/t.md", "# T\n")
        self.links_folder()
        (sync.LINKS / "_defaults.json").write_text(json.dumps(
            {"object": {**sync.DEFAULTS["object"], "location": {"declaration": "Ext.t"}}}) + "\n")
        listed = {"org.atlas-wiki": {"duplicates": ["Ext.twin"]}}
        index = SimpleNamespace(declarations={"Ext.t": None, "Ext.twin": None})
        problem = ("Algebra/t.md: it lists duplicates but credits no declaration of this project by a Lean link of "
                   "its own")
        named = {"location": {"declaration": "Ext.t"}}
        for fields, problems in (({}, [problem]), ({"object": [{}]}, [problem]),
                                 ({"object": [{"role": "states"}]}, [problem]),
                                 ({"object": [{"role": "states"}, {"role": "uses", **named}]}, [problem]),
                                 ({"object": [{"role": "uses", **named}, {"role": "states"}]}, [problem]),
                                 ({"object": [{"role": "states"}, named]}, [problem]),
                                 ({"object": [named]}, []),
                                 ({"object": [{"role": "states", **named}, {"role": "uses"}]}, []),
                                 ({"object": [{"role": "uses"}, {"role": "states", **named}]}, []),
                                 ({"object": [{}, named]}, [])):
            with self.subTest(fields=fields):
                self.annotate([self.about("Algebra/README.md", object=[]),
                               self.about("Algebra/t.md", **fields, extensions=listed)])
                self.assertEqual(sync.page_owner(sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][1])[:2],
                                 ("atlas", "Ext.t"))
                self.assertEqual(sync.apply_declarations([], index)["duplicate_problems"], problems)

    def test_a_new_page_never_takes_the_name_of_its_folder_page(self) -> None:
        self.page("Algebra/groups/README.md", "# Groups\n")
        self.page("Algebra/groups/old.md", "# Old\n")
        self.annotate([self.about("Algebra/groups/old.md", object=[{"location": {"declaration": "Ext.old"}}])])
        index = SimpleNamespace(declarations={"Ext.old": None, "Ext.index": None})
        targets = [declaration("Ext.old", "old", "Old", "Old."), declaration("Ext.index", "index", "Index", "An index.")]
        self.assertEqual(sync.apply_declarations(targets, index)["added"], ["Ext.index -> Algebra/groups/index-2.md"])

    def test_a_new_page_drops_the_bold_title_its_docstring_opens_with(self) -> None:
        self.page("Algebra/README.md", "# Algebra\n")
        sync.LINKS.mkdir(parents=True)
        sync.apply_declarations([declaration("Ext.new", "new", "New result", "**New result.** A new statement.")],
                                SimpleNamespace(declarations={"Ext.new": None}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "new.md").read_text(), "# New result\n\nA new statement.\n")
        # A page's first item sits a blank line below the text above it.
        self.assertEqual((wiki.ROADMAP / "Algebra" / "README.md").read_text(), "# Algebra\n\n- [New result](new.md)\n")

    def test_a_deprecated_declaration_gets_no_page(self) -> None:
        # A page the wiki dropped for a deprecated declaration must stay dropped.
        self.page("Algebra/README.md", "# Algebra\n")
        source = self.tmp / "Ext" / "Groups.lean"
        source.parent.mkdir(parents=True)
        source.write_text('/-- Old. -/\n@[deprecated Mathlib.old (since := "2026-11-09")]\ntheorem old : True := trivial\n'
                          '/-- Also old. -/\n@[simp, deprecated (since := "2026-11-09")] theorem older : True := trivial\n'
                          '/-- Split. -/\n@[deprecated Mathlib.split\n  (since := "2026-11-09")]\ntheorem split : True := trivial\n'
                          '/-- Listed. -/\n@[simp,\n  deprecated (since := "2026-11-09")]\ntheorem listed : True := trivial\n'
                          "/-- New. -/\n@[simp]\ntheorem new : True := trivial\n")
        sync.LINKS.mkdir(parents=True)
        targets = [declaration("Ext.old", "old", "Old", "Old."), declaration("Ext.older", "older", "Older", "Also old."),
                   declaration("Ext.split", "split", "Split", "Split."),
                   declaration("Ext.listed", "listed", "Listed", "Listed."), declaration("Ext.new", "new", "New", "New.")]
        index = SimpleNamespace(declarations={"Ext.old": None, "Ext.older": None, "Ext.split": None, "Ext.listed": None,
                                              "Ext.new": None})
        self.assertEqual(sync.apply_declarations(targets, index)["added"], ["Ext.new -> Algebra/new.md"])

    def test_deprecated_reads_the_declaration_at_its_own_line(self) -> None:
        # Two declarations of a module share their last name component; only `A.same` is deprecated, in either order.
        old = '/-- Old entry. -/\n@[deprecated (since := "2026-01-01")]\ndef same : Nat := 1\n'
        new = "/-- Current entry. -/\ndef same : Nat := 2\n"
        source = self.tmp / "MathlibExt" / "Algebra" / "Example.lean"
        source.parent.mkdir(parents=True, exist_ok=True)
        path = Path("MathlibExt/Algebra/Example.lean")
        for blocks in ((("A", old), ("B", new)), (("B", new), ("A", old))):
            with self.subTest(first=blocks[0][0]):
                text, lines = "", {}
                for space, body in blocks:
                    text += f"namespace {space}\n"
                    lines[f"{space}.same"] = text.count("\n") + body.count("\n")
                    text += body + f"end {space}\n"
                source.write_text(text)
                index = SimpleNamespace(declarations={
                    name: SimpleNamespace(path=path, line=line, keyword="def", name=name) for name, line in lines.items()})
                targets, _ = wiki.load_library("MathlibExt", index, {"subjects": {"Algebra": {}}, "placements": {}})
                self.assertEqual({t.lean: (t.line, sync.deprecated(t)) for t in targets},
                                 {"A.same": (lines["A.same"], True), "B.same": (lines["B.same"], False)})

    def test_deprecated_without_a_line_reads_code_not_comments(self) -> None:
        # A target with no line is found by its last name component in the module's code only.
        source = self.tmp / "Ext" / "Groups.lean"
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text('/-- Formerly `def lagrange`:\n@[deprecated (since := "2026-01-01")]\ndef lagrange : Nat := 0\n-/\n'
                          "def lagrange : Nat := 1\n")
        self.assertFalse(sync.deprecated(SimpleNamespace(module=("Ext", "Groups"), names=["Ext.lagrange"])))
        source.write_text('/-- Old. -/\n@[deprecated (since := "2026-01-01")]\ndef lagrange : Nat := 1\n')
        self.assertTrue(sync.deprecated(SimpleNamespace(module=("Ext", "Groups"), names=["Ext.lagrange"])))

    def test_a_page_rebound_to_its_moved_declaration_keeps_its_place(self) -> None:
        # Upstream moved a declaration to another module and namespace. Until an editor points the page's annotation at
        # the new name, the page is gone and the new name would get a second page; after it, neither.
        readme = "# Groups\n\n- [Old](old.md)\n"
        self.page("Algebra/README.md", "# Algebra\n")
        self.page("Algebra/groups/README.md", readme)
        old = self.page("Algebra/groups/old.md", "# Old, as the wiki wrote it\n\nEdited text.\n")
        self.annotate([self.about("Algebra/groups/old.md", object=[{"location": {"declaration": "Ext.Groups.old"}}])])
        index = SimpleNamespace(declarations={"Ext.Framework.old": None})
        moved = [declaration("Ext.Framework.old", "old", "Old", "Upstream text.", module=("Ext", "Framework"))]
        before = sync.apply_declarations(moved, index)
        self.assertEqual(before["gone"], ["Ext.Groups.old (Algebra/groups/old.md)"])
        self.assertEqual(before["added"], ["Ext.Framework.old -> Algebra/old.md"])
        (wiki.ROADMAP / "Algebra" / "old.md").unlink()
        self.page("Algebra/README.md", "# Algebra\n")
        self.annotate([self.about("Algebra/groups/old.md", object=[{"location": {"declaration": "Ext.Framework.old"}}])])
        after = sync.apply_declarations(moved, index)
        self.assertEqual((after["added"], after["gone"], after["changed"]), ([], [], []))
        self.assertEqual(old.read_text(), "# Old, as the wiki wrote it\n\nEdited text.\n")
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(), readme)
        self.assertEqual((wiki.ROADMAP / "Algebra" / "README.md").read_text(), "# Algebra\n")
        self.assertEqual(sync.read_annotations()[sync.LINKS / "Algebra.jsonl"],
                         [self.about("Algebra/groups/old.md", object=[{"location": {"declaration": "Ext.Framework.old"}}])])

    def test_new_pages_join_their_module_page_in_source_order(self) -> None:
        self.page("Algebra/groups/README.md", "# Groups\n\n## Basics\n\n- [A](a.md)\n- [C](c.md)\n\n## Results\n\n- [E](e.md)\n")
        for short in "ace":
            self.page(f"Algebra/groups/{short}.md", f"# {short.upper()}\n")
        self.annotate([self.about(f"Algebra/groups/{short}.md", object=[{"location": {"declaration": f"Ext.{short}"}}])
                       for short in "ace"])
        targets = []
        for number, (short, section) in enumerate([("z", "Basics"), ("a", "Basics"), ("b", "Basics"), ("c", "Basics"),
                                                   ("d", "Results"), ("e", "Results"), ("f", "Results")]):
            target = declaration(f"Ext.{short}", short, short.upper(), f"{short}.")
            target.idx, target.sections = number, (section, "", "")
            targets.append(target)
        sync.apply_declarations(targets, SimpleNamespace(declarations={f"Ext.{short}": None for short in "zabcdef"}))
        # d opens the second section, so it goes ahead of e rather than after c.
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         "# Groups\n\n## Basics\n\n- [Z](z.md)\n- [A](a.md)\n- [B](b.md)\n- [C](c.md)\n\n"
                         "## Results\n\n- [D](d.md)\n- [E](e.md)\n- [F](f.md)\n")

    def test_a_new_module_joins_a_folder_where_generate_wiki_lists_it(self) -> None:
        self.page("Algebra/groups/README.md", "# Groups\n\n- [Old](old.md)\n- [Late](late.md)\n")
        self.annotate([self.about(f"Algebra/groups/{short}.md", object=[{"location": {"declaration": f"Ext.{short}"}}])
                       for short in ("old", "late")])
        sylow = declaration("Ext.sylow", "sylow", "Sylow", "Sylow.", module=("Ext", "Sylow"))
        sylow.path = wiki.ROADMAP / "Algebra" / "groups" / "sylow.md"
        generated = {sylow.path.parent / "README.md": "# Groups\n\n- [Old](old.md)\n- [Sylow](sylow.md)\n- [Late](late.md)\n"}
        sync.apply_declarations([sylow], SimpleNamespace(declarations={"Ext.sylow": None}), generated)
        self.assertEqual((sylow.path.parent / "README.md").read_text(),
                         "# Groups\n\n- [Old](old.md)\n- [Sylow](sylow.md)\n- [Late](late.md)\n")

    def test_a_new_module_gets_the_folders_the_taxonomy_lays_out(self) -> None:
        self.page("Algebra/README.md", "# Algebra\n\n- [Fields](fields/README.md)\n- [Topology](topology/README.md)\n")
        source = self.tmp / "Ext" / "Rings.lean"
        source.parent.mkdir(parents=True)
        source.write_text('/-- Old. -/\n@[deprecated (since := "2026-11-11")]\ntheorem old : True := trivial\n'
                          "/-- An ideal. -/\ntheorem ideal : True := trivial\n/-- A unit. -/\ntheorem unit : True := trivial\n")
        sync.LINKS.mkdir(parents=True)
        ideals = wiki.ROADMAP / "Algebra" / "rings" / "ideals"
        targets = []
        for short, title in (("old", "Old"), ("ideal", "Ideal"), ("unit", "Unit")):
            target = declaration(f"Ext.{short}", short, title, f"{title}.", module=("Ext", "Rings"))
            target.path = ideals / f"{short}.md"
            targets.append(target)
        generated = {
            wiki.ROADMAP / "Algebra" / "README.md": "# Algebra\n\n- [Fields](fields/README.md)\n- [Groups](groups/README.md)\n"
            "- [Rings](rings/README.md)\n- [Topology](topology/README.md)\n",
            ideals.parent / "README.md": "# Rings\n\nRing theory.\n\n- [Ideals](ideals/README.md)\n",
            ideals / "README.md": "---\nnavigation: module\n---\n\n# Ideals\n\n## Basics\n\n- [Old](old.md)\n\n"
            "## Results\n\n- [Ideal](ideal.md)\n- [Unit](unit.md)\n",
        }
        index = SimpleNamespace(declarations={"Ext.old": None, "Ext.ideal": None, "Ext.unit": None})
        report = sync.apply_declarations(targets, index, generated)
        self.assertEqual(report["added"], ["Ext.ideal -> Algebra/rings/ideals/ideal.md", "Ext.unit -> Algebra/rings/ideals/unit.md"])
        self.assertEqual(report["folders"], ["Algebra/rings", "Algebra/rings/ideals"])
        self.assertEqual((ideals.parent / "README.md").read_text(), "# Rings\n\nRing theory.\n\n- [Ideals](ideals/README.md)\n")
        # The deprecated declaration's item goes, and with it the heading above it.
        self.assertEqual((ideals / "README.md").read_text(), "# Ideals\n\n## Results\n\n- [Ideal](ideal.md)\n- [Unit](unit.md)\n")
        self.assertEqual((ideals / "ideal.md").read_text(), "# Ideal\n\nIdeal.\n")
        self.assertEqual((wiki.ROADMAP / "Algebra" / "README.md").read_text(),
                         "# Algebra\n\n- [Fields](fields/README.md)\n- [Rings](rings/README.md)\n- [Topology](topology/README.md)\n")
        rows = {sync.subject_path(row).relative_to(wiki.ROADMAP).as_posix(): row for row in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        self.assertEqual(rows["Algebra/rings/README.md"]["subject"], [{"type": "generic", "uri": "../roadmap/Algebra/rings/README.md"}])
        self.assertEqual(set(rows["Algebra/rings/README.md"]), {"subject", "id"})
        self.assertRegex(rows["Algebra/rings/README.md"]["id"], r"^af_[0-9a-f]{24}$")
        self.assertEqual(rows["Algebra/rings/ideals/README.md"]["extensions"], {"org.autoform": {"navigation": "module"}})
        self.assertNotIn("Algebra/rings/ideals/old.md", rows)

    def test_pages_moved_to_a_folder_without_a_page_get_the_generated_one(self) -> None:
        self.page("Algebra/README.md", "# Algebra\n\n- [Fields](fields/README.md)\n")
        self.page("Algebra/rings/ideals/ideal.md", "# Ideals of a ring\n")
        self.page("Algebra/rings/ideals/old-name.md", "# Prime ideal\n")
        self.annotate([self.about("Algebra/rings/ideals/ideal.md", object=[{"location": {"declaration": "Ext.ideal"}}]),
                       self.about("Algebra/rings/ideals/old-name.md", object=[{"location": {"declaration": "Ext.prime"}}])])
        ideals = wiki.ROADMAP / "Algebra" / "rings" / "ideals"
        targets = []
        for short, title in (("ideal", "Ideal"), ("prime", "Prime ideal"), ("unit", "Unit")):
            target = declaration(f"Ext.{short}", short, title, f"{title}.", module=("Ext", "Rings"))
            target.path = ideals / f"{short}.md"
            targets.append(target)
        generated = {
            wiki.ROADMAP / "Algebra" / "README.md": "# Algebra\n\n- [Fields](fields/README.md)\n- [Rings](rings/README.md)\n",
            ideals.parent / "README.md": "# Rings\n\n- [Ideals](ideals/README.md)\n",
            ideals / "README.md": "# Ideals\n\n- [Ideal](ideal.md)\n- [Prime ideal](prime.md)\n- [Unit](unit.md)\n",
        }
        index = SimpleNamespace(declarations={"Ext.ideal": None, "Ext.prime": None, "Ext.unit": None})
        report = sync.apply_declarations(targets, index, generated)
        self.assertEqual(report["added"], ["Ext.unit -> Algebra/rings/ideals/unit.md"])
        self.assertEqual(report["folders"], ["Algebra/rings", "Algebra/rings/ideals"])
        # Items take their pages' titles, and the page under another name than the generated one is listed too.
        self.assertEqual((ideals / "README.md").read_text(),
                         "# Ideals\n\n- [Ideals of a ring](ideal.md)\n- [Unit](unit.md)\n- [Prime ideal](old-name.md)\n")
        self.assertEqual((wiki.ROADMAP / "Algebra" / "README.md").read_text(),
                         "# Algebra\n\n- [Fields](fields/README.md)\n- [Rings](rings/README.md)\n")

    def test_a_page_with_no_listed_neighbour_ends_its_folders_own_list(self) -> None:
        # Not under "Related topics" or "Sources", which follow that list. Where the list runs over sections, a page
        # joins one only beside its module's pages, whatever generate_wiki's order across modules, and else starts one
        # of its own, under its module's title.
        related = "## Related topics\n\n- [Rings](../rings/README.md): rings.\n\n## Sources\n\n- [Book](https://example.org)\n"
        self.page("Algebra/groups/README.md", f"# Groups\n\nProse.\n\n- [Old](old.md) (wanted)\n\n{related}")
        self.page("Algebra/bakery/README.md", "# Bakery\n\n## The algorithm\n\n- [State](state.md)\n\n## Mutual exclusion\n\n"
                  f"- [Invariant](invariant.md)\n\n{related}")
        self.page("Algebra/fields/README.md", f"# Fields\n\nProse.\n\n{related}")
        sync.LINKS.mkdir(parents=True)
        targets = []
        for short, folder, module in (("sylow", "groups", "Sylow"), ("turn", "bakery", "TwoProcess"), ("galois", "fields", "Galois")):
            target = declaration(f"Ext.{short}", short, short.title(), f"{short}.", module=("Ext", module))
            target.path = wiki.ROADMAP / "Algebra" / folder / f"{short}.md"
            targets.append(target)
        targets[1].module_title = "Two-process bakery"
        generated = {targets[1].path.parent / "README.md": "# Bakery\n\n- [State](state.md)\n- [Invariant](invariant.md)\n- [Turn](turn.md)\n"}
        sync.apply_declarations(targets, SimpleNamespace(declarations={f"Ext.{t.slug}": None for t in targets}), generated)
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         f"# Groups\n\nProse.\n\n- [Old](old.md) (wanted)\n- [Sylow](sylow.md)\n\n{related}")
        self.assertEqual((wiki.ROADMAP / "Algebra" / "bakery" / "README.md").read_text(),
                         "# Bakery\n\n## The algorithm\n\n- [State](state.md)\n\n## Mutual exclusion\n\n- [Invariant](invariant.md)\n\n"
                         f"## Two-process bakery\n\n- [Turn](turn.md)\n\n{related}")
        self.assertEqual((wiki.ROADMAP / "Algebra" / "fields" / "README.md").read_text(),
                         f"# Fields\n\nProse.\n\n- [Galois](galois.md)\n\n{related}")

    def test_a_flat_folder_stays_flat_and_each_topic_keeps_its_folder(self) -> None:
        # generate_wiki splits a folder of more than MAX_CHILDREN entries into parts, numbered afresh as it grows. A
        # folder the wiki has keeps its layout, so no page moves: no part folder goes beside its entries, and a topic
        # that generate_wiki puts in a part keeps the folder it has.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        self.page("Algebra/groups/README.md", "# Groups\n\n- [Sylow theorems](sylow/README.md)\n- [Old](old.md)\n")
        self.page("Algebra/groups/old.md", "# Old\n")
        self.page("Algebra/groups/sylow/README.md", "# Sylow theorems\n\n- [Sylow](sylow.md)\n")
        self.page("Algebra/groups/sylow/sylow.md", "# Sylow\n")
        self.annotate([self.about("Algebra/groups/old.md", object=[{"location": {"declaration": "Ext.old"}}]),
                       self.about("Algebra/groups/sylow/sylow.md", object=[{"location": {"declaration": "Ext.sylow"}}])])
        burnside = declaration("Ext.burnside", "burnside", "Burnside", "Burnside.", module=("Ext", "Burnside"))
        burnside.path = groups / "part-02" / "burnside.md"
        counting = declaration("Ext.counting", "counting", "Counting", "Counting.", module=("Ext", "SylowCounting"))
        counting.path = groups / "part-02" / "sylow" / "counting.md"
        generated = {
            groups / "README.md": "# Groups\n\n## [Part 1 of 2](part-01/README.md)\n\n- [Old](part-01/old.md)\n\n"
            "## [Part 2 of 2](part-02/README.md)\n\n- [Sylow theorems](part-02/sylow/README.md)\n- [Burnside](part-02/burnside.md)\n",
            groups / "part-01" / "README.md": "# Part 1 of 2\n\n- [Old](old.md)\n",
            groups / "part-02" / "README.md": "# Part 2 of 2\n\n- [Sylow theorems](sylow/README.md)\n- [Burnside](burnside.md)\n",
            groups / "part-02" / "sylow" / "README.md": "# Sylow theorems\n\n- [Sylow](sylow.md)\n- [Counting](counting.md)\n",
        }
        index = SimpleNamespace(declarations={"Ext.old": None, "Ext.sylow": None, "Ext.burnside": None, "Ext.counting": None})
        report = sync.apply_declarations([burnside, counting], index, generated)
        self.assertEqual(report["added"], ["Ext.burnside -> Algebra/groups/burnside.md", "Ext.counting -> Algebra/groups/sylow/counting.md"])
        self.assertEqual(report["folders"], [])
        self.assertFalse((groups / "part-02").exists())
        self.assertEqual((groups / "README.md").read_text(),
                         "# Groups\n\n- [Sylow theorems](sylow/README.md)\n- [Old](old.md)\n- [Burnside](burnside.md)\n")
        self.assertEqual((groups / "sylow" / "README.md").read_text(), "# Sylow theorems\n\n- [Sylow](sylow.md)\n- [Counting](counting.md)\n")

    def test_a_folder_split_into_parts_keeps_its_parts(self) -> None:
        # A topic keeps its folder in whichever part holds it; a new page or folder joins the last part, and the folder
        # page's copy of each part's list follows the part.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        self.page("Algebra/groups/README.md", "# Groups\n\n## [Part 1 of 2](part-01/README.md)\n\n- [Sylow theorems](part-01/sylow/README.md)\n"
                  "- [Old](part-01/old.md)\n\n## [Part 2 of 2](part-02/README.md)\n\n- [Late](part-02/late.md)\n\n"
                  "## Related topics\n\n- [Rings](../rings/README.md): rings.\n")
        self.page("Algebra/groups/part-01/README.md", "# Part 1 of 2\n\n- [Sylow theorems](sylow/README.md)\n- [Old](old.md)\n")
        self.page("Algebra/groups/part-02/README.md", "# Part 2 of 2\n\n- [Late](late.md)\n")
        self.page("Algebra/groups/part-01/sylow/README.md", "# Sylow theorems\n\n- [Sylow](sylow.md)\n")
        for page in ("part-01/old.md", "part-01/sylow/sylow.md", "part-02/late.md"):
            self.page(f"Algebra/groups/{page}", f"# {Path(page).stem.title()}\n")
        self.annotate([self.about(f"Algebra/groups/{page}", object=[{"location": {"declaration": f"Ext.{Path(page).stem}"}}])
                       for page in ("part-01/old.md", "part-01/sylow/sylow.md", "part-02/late.md")])
        burnside = declaration("Ext.burnside", "burnside", "Burnside", "Burnside.", module=("Ext", "Burnside"))
        burnside.path = groups / "part-03" / "burnside.md"
        counting = declaration("Ext.counting", "counting", "Counting", "Counting.", module=("Ext", "SylowCounting"))
        counting.path = groups / "part-03" / "sylow" / "counting.md"
        index = SimpleNamespace(declarations={f"Ext.{name}": None for name in ("old", "sylow", "late", "burnside", "counting")})
        report = sync.apply_declarations([burnside, counting], index)
        self.assertEqual(report["added"], ["Ext.burnside -> Algebra/groups/part-02/burnside.md",
                                           "Ext.counting -> Algebra/groups/part-01/sylow/counting.md"])
        self.assertFalse((groups / "part-03").exists())
        self.assertEqual((groups / "part-02" / "README.md").read_text(), "# Part 2 of 2\n\n- [Late](late.md)\n- [Burnside](burnside.md)\n")
        self.assertEqual((groups / "README.md").read_text(),
                         "# Groups\n\n## [Part 1 of 2](part-01/README.md)\n\n- [Sylow theorems](part-01/sylow/README.md)\n"
                         "- [Old](part-01/old.md)\n\n## [Part 2 of 2](part-02/README.md)\n\n- [Late](part-02/late.md)\n"
                         "- [Burnside](part-02/burnside.md)\n\n## Related topics\n\n- [Rings](../rings/README.md): rings.\n")

    def test_a_new_page_of_a_module_split_into_parts_joins_its_last_part(self) -> None:
        # A module of more than MAX_MODULE_CHILDREN pages fills parts of MAX_CHILDREN in turn: its next page goes in its
        # last part, not in the full early part that holds most of its pages.
        sylow = wiki.ROADMAP / "Algebra" / "sylow"
        names = [f"lemma-{number:03}" for number in range(wiki.MAX_MODULE_CHILDREN + 1)]
        chunks = [names[start:start + wiki.MAX_CHILDREN] for start in range(0, len(names), wiki.MAX_CHILDREN)]
        lines = ["# Sylow", ""]
        for number, chunk in enumerate(chunks, 1):
            part = f"part-{number:02}"
            self.page(f"Algebra/sylow/{part}/README.md",
                      f"# Part {number} of {len(chunks)}\n\n" + "".join(f"- [{name}]({name}.md)\n" for name in chunk))
            for name in chunk:
                self.page(f"Algebra/sylow/{part}/{name}.md", f"# {name}\n")
            lines += [f"## [Part {number} of {len(chunks)}]({part}/README.md)", "", *(f"- [{name}]({part}/{name}.md)" for name in chunk), ""]
        self.page("Algebra/sylow/README.md", "\n".join(lines))
        self.annotate([self.about(f"Algebra/sylow/part-{number:02}/{name}.md", object=[{"location": {"declaration": f"Ext.{name}"}}])
                       for number, chunk in enumerate(chunks, 1) for name in chunk])
        targets = [declaration(f"Ext.{name}", name, name, f"{name}.", module=("Ext", "Sylow")) for name in names]
        last = declaration("Ext.next", "next", "Next", "Next.", module=("Ext", "Sylow"))
        report = sync.apply_declarations([*targets, last], SimpleNamespace(declarations={f"Ext.{n}": None for n in [*names, "next"]}))
        self.assertEqual(len(chunks), 7)
        self.assertEqual(report["added"], ["Ext.next -> Algebra/sylow/part-07/next.md"])
        self.assertEqual((sylow / "part-07" / "README.md").read_text(), "# Part 7 of 7\n\n- [lemma-120](lemma-120.md)\n- [Next](next.md)\n")
        self.assertTrue((sylow / "README.md").read_text().endswith("- [lemma-120](part-07/lemma-120.md)\n- [Next](part-07/next.md)\n"))

    def test_a_new_page_of_a_module_on_a_split_page_stays_beside_its_own(self) -> None:
        # A topic folder, or a page that merges several modules, split into parts holds other modules' pages in its
        # last part: a module whose pages are all in an earlier part takes its next page there, beside its own.
        for name, layout, module in (
                ("topic folder", {"part-01": [("brooks", "Brooks"), ("greedy", "Greedy")], "part-02": [("hajos", "Hajos")]}, "Brooks"),
                ("merged module page", {"part-01": [("grid", "Grid"), ("grid-two", "Grid")], "part-02": [("lower", "Lower")],
                                        "part-03": [("theta", "Theta"), ("upper", "Upper")]}, "Grid"),
                ("pages in an earlier and a later part", {"part-01": [("first", "Many")], "part-02": [("other", "Other")],
                                                         "part-03": [("third", "Many"), ("fourth", "Many")]}, "Many")):
            with self.subTest(name):
                shutil.rmtree(wiki.ROADMAP / "Combinatorics", ignore_errors=True)
                shutil.rmtree(sync.LINKS, ignore_errors=True)
                lines = ["# Coloring", ""]
                for number, (part, pages) in enumerate(layout.items(), 1):
                    self.page(f"Combinatorics/coloring/{part}/README.md",
                              f"# Part {number} of {len(layout)}\n\n" + "".join(f"- [{page}]({page}.md)\n" for page, _ in pages))
                    for page, _ in pages:
                        self.page(f"Combinatorics/coloring/{part}/{page}.md", f"# {page}\n")
                    lines += [f"## [Part {number} of {len(layout)}]({part}/README.md)", "", *(f"- [{page}]({part}/{page}.md)" for page, _ in pages), ""]
                self.page("Combinatorics/coloring/README.md", "\n".join(lines))
                self.annotate([self.about(f"Combinatorics/coloring/{part}/{page}.md", object=[{"location": {"declaration": f"Ext.{page}"}}])
                               for part, pages in layout.items() for page, _ in pages])
                targets = [declaration(f"Ext.{page}", page, page, f"{page}.", module=("Ext", owner))
                           for pages in layout.values() for page, owner in pages]
                last = declaration("Ext.next", "next", "Next", "Next.", module=("Ext", module))
                index = SimpleNamespace(declarations={f"Ext.{page}": None for pages in layout.values() for page, _ in pages} | {"Ext.next": None})
                report = sync.apply_declarations([*targets, last], index)
                home = max((part for part, pages in layout.items() if any(owner == module for _, owner in pages)))
                self.assertEqual(report["added"], [f"Ext.next -> Combinatorics/coloring/{home}/next.md"])

    def test_a_new_page_joins_the_last_part_whatever_part_generate_wiki_names(self) -> None:
        # generate_wiki's part numbers are its own partition of the folder, so a part of the wiki's that has the number
        # takes nothing for it; a topic still keeps its folder, in whichever part holds it.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        self.page("Algebra/groups/README.md", "# Groups\n\n## [Part 1 of 2](part-01/README.md)\n\n- [Sylow theorems](part-01/sylow/README.md)\n"
                  "- [Old](part-01/old.md)\n\n## [Part 2 of 2](part-02/README.md)\n\n- [Late](part-02/late.md)\n")
        self.page("Algebra/groups/part-01/README.md", "# Part 1 of 2\n\n- [Sylow theorems](sylow/README.md)\n- [Old](old.md)\n")
        self.page("Algebra/groups/part-02/README.md", "# Part 2 of 2\n\n- [Late](late.md)\n")
        self.page("Algebra/groups/part-01/sylow/README.md", "# Sylow theorems\n\n- [Sylow](sylow.md)\n")
        sync.LINKS.mkdir(parents=True)
        lagrange = declaration("Ext.lagrange", "lagrange", "Lagrange", "Lagrange.", module=("Ext", "Lagrange"))
        lagrange.path = groups / "part-01" / "lagrange.md"
        counting = declaration("Ext.counting", "counting", "Counting", "Counting.", module=("Ext", "SylowCounting"))
        counting.path = groups / "part-02" / "sylow" / "counting.md"
        report = sync.apply_declarations([lagrange, counting], SimpleNamespace(declarations={"Ext.lagrange": None, "Ext.counting": None}))
        self.assertEqual(report["added"], ["Ext.counting -> Algebra/groups/part-01/sylow/counting.md",
                                           "Ext.lagrange -> Algebra/groups/part-02/lagrange.md"])
        self.assertEqual((groups / "part-01" / "README.md").read_text(), "# Part 1 of 2\n\n- [Sylow theorems](sylow/README.md)\n- [Old](old.md)\n")
        self.assertEqual((groups / "part-02" / "README.md").read_text(), "# Part 2 of 2\n\n- [Late](late.md)\n- [Lagrange](lagrange.md)\n")

    def test_a_folder_page_split_into_parts_lists_what_its_parts_list(self) -> None:
        groups = wiki.ROADMAP / "Algebra" / "groups"
        self.page("Algebra/groups/README.md", "# Groups\n\n## [Part 1 of 2](part-01/README.md)\n\n- [Old](part-01/old.md)\n\n"
                  "## [Part 2 of 2](part-02/README.md)\n\n- [A](part-02/a.md)\n- [C](part-02/c.md)\n")
        self.page("Algebra/groups/part-01/README.md", "# Part 1 of 2\n\n- [Old](old.md)\n")
        self.page("Algebra/groups/part-02/README.md", "# Part 2 of 2\n\n- [A](a.md)\n- [C](c.md)\n")
        for page in ("part-01/old.md", "part-02/a.md", "part-02/c.md"):
            self.page(f"Algebra/groups/{page}", f"# {Path(page).stem.upper()}\n")
        self.annotate([self.about(f"Algebra/groups/{page}", object=[{"location": {"declaration": f"Ext.{Path(page).stem}"}}])
                       for page in ("part-01/old.md", "part-02/a.md", "part-02/c.md")])
        targets = [declaration(f"Ext.{short}", short, short.upper(), f"{short}.") for short in "abc"]
        for number, target in enumerate(targets):
            target.idx = number
        sync.apply_declarations(targets, SimpleNamespace(declarations={f"Ext.{short}": None for short in ("old", "a", "b", "c")}))
        self.assertEqual((groups / "part-02" / "README.md").read_text(), "# Part 2 of 2\n\n- [A](a.md)\n- [B](b.md)\n- [C](c.md)\n")
        self.assertEqual((groups / "README.md").read_text(),
                         "# Groups\n\n## [Part 1 of 2](part-01/README.md)\n\n- [Old](part-01/old.md)\n\n"
                         "## [Part 2 of 2](part-02/README.md)\n\n- [A](part-02/a.md)\n- [B](part-02/b.md)\n- [C](part-02/c.md)\n")

    def test_a_part_list_gives_way_to_the_part_and_nothing_else(self) -> None:
        # With no declaration to add: under a part's heading only the items that link the part's pages are the part's
        # copy; another item and an editor's paragraph there stay.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        part_one = ("## [Part 1 of 2](part-01/README.md)\n\n- [Introduction](introduction.md)\n- [A](part-01/a.md)\n\n"
                    "The first part follows the book.\n\n")
        self.page("Algebra/groups/README.md", f"# Groups\n\n{part_one}## [Part 2 of 2](part-02/README.md)\n\n- [B](part-02/b.md)\n")
        self.page("Algebra/groups/part-01/README.md", "# Part 1 of 2\n\n- [A](a.md)\n")
        self.page("Algebra/groups/part-02/README.md", "# Part 2 of 2\n\n- [B](b.md)\n- [C](c.md)\n")
        sync.LINKS.mkdir(parents=True)
        sync.apply_declarations([], SimpleNamespace(declarations={}))
        self.assertEqual((groups / "README.md").read_text(),
                         f"# Groups\n\n{part_one}## [Part 2 of 2](part-02/README.md)\n\n- [B](part-02/b.md)\n- [C](part-02/c.md)\n")

    def test_a_part_list_copies_simple_entries_with_their_notes(self) -> None:
        # A simple entry is "- [title](page)" and plain text, on one line; math's "<" and backslashes are plain text.
        self.page("Algebra/groups/README.md", "# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n- [A](part-01/a.md)\n")
        self.page("Algebra/groups/part-01/README.md",
                  "# Part 1 of 1\n\n- [A](a.md) (wanted)\n- [Units of $\\mathbb{Z}/n$ in $\\{1, \\dots, n\\}$ for $n < 9$](u.md): a note\n")
        sync.LINKS.mkdir(parents=True)
        report = sync.apply_declarations([], SimpleNamespace(declarations={}))
        self.assertEqual(report["parts"], [])
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         "# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n- [A](part-01/a.md) (wanted)\n"
                         "- [Units of $\\mathbb{Z}/n$ in $\\{1, \\dots, n\\}$ for $n < 9$](part-01/u.md): a note\n")

    def test_a_part_list_with_an_item_that_is_not_simple_is_left_to_an_editor(self) -> None:
        # Any other item in a part's page, or in the copy of its list, leaves the copy as it is, and the part is
        # reported: the sync never reads a page's place in a list from code, a bracket, HTML or an escape.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        copy = "- [A](part-01/a.md)\n- [C](part-01/c.md)\n"
        for name, part, listed in (
                ("code span with a bracket", "- [`a[i]`](a.md)\n", copy),
                ("code span with a closing bracket", "- [`a]b`](a.md)\n", copy),
                ("tilde fence in an item", "- [A](a.md)\n  ~~~\n  [B](b.md)\n  ~~~\n", copy),
                ("backtick fence closed by a longer run", "- [A](a.md)\n  ```\n  [B](b.md)\n  ````\n", copy),
                ("link in a note", "- [A](a.md) — see [B](b.md)\n", copy),
                ("code in a note", "- [A](a.md): written `[A](a.md)`\n", copy),
                ("escaped bracket", "- [A\\](a.md)\n", copy),
                ("HTML", "- [A](a.md) <br>\n", copy),
                ("another bullet", "* [A](a.md)\n", copy),
                ("loose item", "- [A](a.md): first\n\n  second with [B](b.md)\n", copy),
                ("note after a blank line", "- [A](a.md)\n\n  Note about A.\n", copy),
                ("note after several blank lines", "- [A](a.md)\n\n\n  Note about A.\n", copy),
                ("dot segment", "- [A](./a.md)\n", copy),
                ("link title", '- [A](a.md "A")\n', copy),
                ("escaped destination", "- [A](a\\(1\\).md)\n", copy),
                ("destination in angle brackets", "- [A](<a b.md>)\n", copy),
                ("copy with code", "- [A](a.md)\n", "- [`A`](part-01/a.md)\n"),
                ("copy over a paragraph", "- [A](a.md)\n", "- [A](part-01/a.md)\n\nA note on A.\n\n- [C](part-01/c.md)\n"),
                ("copy over another item", "- [A](a.md)\n", "- [A](part-01/a.md)\n- [Intro](intro.md)\n- [C](part-01/c.md)\n")):
            with self.subTest(name):
                text = f"# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n{listed}"
                self.page("Algebra/groups/README.md", text)
                self.page("Algebra/groups/part-01/README.md", f"# Part 1 of 1\n\n{part}- [B](b.md)\n")
                sync.LINKS.mkdir(parents=True, exist_ok=True)
                report = sync.apply_declarations([], SimpleNamespace(declarations={}))
                self.assertEqual((groups / "README.md").read_text(), text)
                self.assertEqual(report["parts"], ["Algebra/groups/part-01"])

    def test_a_part_list_reads_nothing_inside_a_comment(self) -> None:
        # Neither an item nor a part heading in a comment counts, and the comment stays as written.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        text = ("# Groups\n\n## [Part 1 of 2](part-01/README.md)\n\n<!-- Retired navigation entry:\n- [Retired](part-01/retired.md)\n"
                "-->\n\n- [A](part-01/a.md)\n\n## [Part 2 of 2](part-02/README.md)\n\n- [B](part-02/b.md)\n\n<!--\n"
                "## [Part 3 of 3](part-03/README.md)\n\n- [D](part-03/d.md)\n-->\n")
        self.page("Algebra/groups/README.md", text)
        self.page("Algebra/groups/part-01/README.md", "# Part 1 of 2\n\n- [A](a.md)\n")
        self.page("Algebra/groups/part-02/README.md", "# Part 2 of 2\n\n- [B](b.md)\n")
        self.page("Algebra/groups/part-03/README.md", "# Part 3 of 3\n\n- [E](e.md)\n")
        sync.LINKS.mkdir(parents=True)
        sync.apply_declarations([], SimpleNamespace(declarations={}))
        self.assertEqual((groups / "README.md").read_text(), text)

    def test_a_part_list_reads_nothing_inside_a_code_fence(self) -> None:
        # A sample in a fenced code block, of backticks or tildes, is no part heading and no item, and stays as written.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        text = ("# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n- [A](part-01/a.md)\n\nA part's heading links it:\n\n"
                "````markdown\n## [Part 1 of 1](part-01/README.md)\n\n- [Old](part-01/old.md)\n````\n\n"
                "~~~\n## [Part 1 of 1](part-01/README.md)\n~~~\n")
        self.page("Algebra/groups/README.md", text)
        self.page("Algebra/groups/part-01/README.md", "# Part 1 of 1\n\n- [A](a.md)\n")
        sync.LINKS.mkdir(parents=True)
        sync.apply_declarations([], SimpleNamespace(declarations={}))
        self.assertEqual((groups / "README.md").read_text(), text)

    def test_a_page_that_is_not_simple_takes_a_new_page_at_its_end(self) -> None:
        # A code span hiding a bracket, a backtick left open, a note after one blank line or several, a loose item, or
        # another kind of list item: the page is never edited within; the new page goes at its end, after "Related
        # topics", where it is a list item of its own, and is reported for an editor to place.
        related = "## Related topics\n\n- [Rings](../rings/README.md): rings.\n"
        for name, listed in (("code span hiding a bracket", "- [`a]b`](old.md)\n- [Late](late.md)\n"),
                             ("backtick left open", "- [The ` sign](old.md)\n"),
                             ("note after a blank line", "- [Old](old.md)\n\n  Note about Old.\n"),
                             ("note after several blank lines", "- [Old](old.md)\n\n\n\n  Note belonging to Old.\n"),
                             ("loose item", "- [Old](old.md): first\n\n  second with [Late](late.md)\n"),
                             ("another bullet", "## Basics\n\n- [Old](old.md)\n\n## Results\n\n+ [Late](late.md)\n")):
            with self.subTest(name):
                self.page("Algebra/groups/README.md", f"# Groups\n\n{listed}\n{related}")
                self.annotate([])
                (wiki.ROADMAP / "Algebra" / "groups" / "sylow.md").unlink(missing_ok=True)
                sylow = declaration("Ext.sylow", "sylow", "Sylow", "Sylow.", module=("Ext", "Sylow"))
                sylow.path = wiki.ROADMAP / "Algebra" / "groups" / "sylow.md"
                report = sync.apply_declarations([sylow], SimpleNamespace(declarations={"Ext.sylow": None}))
                self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                                 f"# Groups\n\n{listed}\n{related}\n- [Sylow](sylow.md)\n")
                self.assertEqual(report["appended"], ["Algebra/groups/sylow.md"])

    def test_an_own_list_with_code_in_its_titles_takes_a_new_page_by_its_neighbours(self) -> None:
        # Balanced code spans that hide nothing of an item's link leave the own list simple: B joins it between A and C.
        listed = "- [The `a` lemma](a.md)\n- [The ``c`d`` bound](c.md)\n"
        self.page("Algebra/groups/README.md", f"# Groups\n\n{listed}\n## Related topics\n\n- [Rings](../rings/README.md): rings.\n")
        for short in "ac":
            self.page(f"Algebra/groups/{short}.md", f"# {short.upper()}\n")
        self.annotate([self.about(f"Algebra/groups/{short}.md", object=[{"location": {"declaration": f"Ext.{short}"}}])
                       for short in "ac"])
        targets = []
        for number, short in enumerate("abc"):
            target = declaration(f"Ext.{short}", short, short.upper(), f"{short}.")
            target.idx = number
            targets.append(target)
        report = sync.apply_declarations(targets, SimpleNamespace(declarations={f"Ext.{short}": None for short in "abc"}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         "# Groups\n\n- [The `a` lemma](a.md)\n- [B](b.md)\n- [The ``c`d`` bound](c.md)\n\n"
                         "## Related topics\n\n- [Rings](../rings/README.md): rings.\n")
        self.assertEqual(report["appended"], [])

    def test_an_item_with_a_note_is_a_neighbour(self) -> None:
        # B follows Old in source order and in Old's section, so it joins Basics after Old, note and all.
        self.page("Algebra/groups/README.md", "# Groups\n\n## Basics\n\n- [Old](old.md) (wanted)\n\n## Results\n\n- [C](c.md)\n")
        for short in ("old", "c"):
            self.page(f"Algebra/groups/{short}.md", f"# {short}\n")
        self.annotate([self.about(f"Algebra/groups/{short}.md", object=[{"location": {"declaration": f"Ext.{short}"}}])
                       for short in ("old", "c")])
        targets = []
        for number, (short, section) in enumerate([("old", "Basics"), ("b", "Basics"), ("c", "Results")]):
            target = declaration(f"Ext.{short}", short, short.upper(), f"{short}.")
            target.idx, target.sections = number, (section, "", "")
            targets.append(target)
        report = sync.apply_declarations(targets, SimpleNamespace(declarations={f"Ext.{short}": None for short in ("old", "b", "c")}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         "# Groups\n\n## Basics\n\n- [Old](old.md) (wanted)\n- [B](b.md)\n\n## Results\n\n- [C](c.md)\n")
        self.assertEqual(report["appended"], [])

    def test_a_link_to_the_site_root_or_a_fragment_is_no_page_of_the_folder(self) -> None:
        # Such an item under "Related topics" is not in the own list, so the new page ends the own list ahead of it.
        related = "## Related topics\n\n- [Index](/index.md)\n- [Glossary](#glossary)\n"
        self.page("Algebra/groups/README.md", f"# Groups\n\n- [Old](old.md)\n\n{related}")
        sync.LINKS.mkdir(parents=True)
        sylow = declaration("Ext.sylow", "sylow", "Sylow", "Sylow.", module=("Ext", "Sylow"))
        sylow.path = wiki.ROADMAP / "Algebra" / "groups" / "sylow.md"
        report = sync.apply_declarations([sylow], SimpleNamespace(declarations={"Ext.sylow": None}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         f"# Groups\n\n- [Old](old.md)\n- [Sylow](sylow.md)\n\n{related}")
        self.assertEqual(report["appended"], [])

    def test_a_marker_indented_four_spaces_opens_no_block(self) -> None:
        # Four spaces in, "<!--", a fence or its closer is indented code, which hides none of the lines after it: the
        # page is no simple one, and the new page, at its end, is listed.
        for marker in ("<!--", "```", "~~~"):
            with self.subTest(marker=marker):
                text = (f"# Groups\n\nAn example:\n\n    {marker}\n\n- [Old](old.md)\n\n"
                        "## Related topics\n\n- [Rings](../rings/README.md): rings.\n")
                self.page("Algebra/groups/README.md", text)
                self.annotate([])
                (wiki.ROADMAP / "Algebra" / "groups" / "sylow.md").unlink(missing_ok=True)
                sylow = declaration("Ext.sylow", "sylow", "Sylow", "Sylow.", module=("Ext", "Sylow"))
                sylow.path = wiki.ROADMAP / "Algebra" / "groups" / "sylow.md"
                report = sync.apply_declarations([sylow], SimpleNamespace(declarations={"Ext.sylow": None}))
                self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                                 f"{text}\n- [Sylow](sylow.md)\n")
                self.assertEqual(report["appended"], ["Algebra/groups/sylow.md"])
        # Nor does a closer four spaces in close a fence that a line opened.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        text = "# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n- [A](part-01/a.md)\n\n```\n    ```\n- [Z](part-01/z.md)\n```\n"
        self.page("Algebra/groups/README.md", text)
        self.page("Algebra/groups/part-01/README.md", "# Part 1 of 1\n\n- [A](a.md)\n")
        sync.apply_declarations([], SimpleNamespace(declarations={}))
        self.assertEqual((groups / "README.md").read_text(), text)

    def add_sylow(self, text: str) -> dict:
        """The report of a run that adds Ext.sylow to a groups folder whose page is *text*, its page as it was gone."""
        self.page("Algebra/groups/README.md", text)
        self.annotate([])
        (wiki.ROADMAP / "Algebra" / "groups" / "sylow.md").unlink(missing_ok=True)
        sylow = declaration("Ext.sylow", "sylow", "Sylow", "Sylow.", module=("Ext", "Sylow"))
        sylow.path = wiki.ROADMAP / "Algebra" / "groups" / "sylow.md"
        return sync.apply_declarations([sylow], SimpleNamespace(declarations={"Ext.sylow": None}))

    def test_a_page_with_raw_html_or_a_code_fence_is_left_as_it_is(self) -> None:
        # An item appended after raw HTML or a fence the sync does not read could be part of it, not a link: whether
        # closed or not, the page is left as it is, and the new page is reported as listed nowhere.
        related = "## Related topics\n\n- [Rings](../rings/README.md): rings.\n"
        for name, block in (("comment in the list", "- [Old](old.md)\n<!--\n## Planned\n- [Wish](wish.md)\n-->\n- [Late](late.md)\n"),
                            ("backtick fence", "```\n- [H](h.md)\n```\n"), ("tilde fence", "~~~ text\n- [H](h.md)\n~~~\n"),
                            ("pre", "<pre>\n- [Sample](old.md)\n\n</pre>\n"), ("pre closed by </pre", "<pre>\nx\n</pre\n"),
                            ("pre closed by another tag", "<pre>\nx\n</pre-extra>\n"), ("xml", "<?xml version=\"1.0\"\n"),
                            ("doctype", "<!DOCTYPE html\n"), ("cdata", "<![CDATA[\nx\n"),
                            ("div", "<div>\n- [Sample](old.md)\n</div>\n"), ("tag alone", '<span class="x">\n'),
                            ("nested details", "<details>\n<details>\n</details>\n"),
                            ("fence left open", "```\n- [Sample](old.md)\n"),
                            ("comment left open", "<!-- To do:\n"), ("pre left open", "<pre>\n- [Sample](old.md)\n\nmore\n")):
            with self.subTest(name):
                text = f"# Groups\n\n- [Old](old.md)\n\n{related}\n{block}"
                report = self.add_sylow(text)
                self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(), text)
                self.assertEqual((report["appended"], report["unlisted"]), ([], ["Algebra/groups/sylow.md"]))

    def test_a_page_with_another_block_takes_a_new_page_at_its_end(self) -> None:
        # Any CommonMark block other than a heading, a simple item, a blank line or a paragraph of plain text, and any
        # item that links a path back into the folder, makes the page not simple: the new page goes at its end.
        for name, block in (("setext heading", "Groups\n======\n"), ("setext heading with dashes", "Groups\n------\n"),
                            ("thematic break", "___\n"), ("starred thematic break", "* * *\n"),
                            ("link reference definition", "[book]: https://example.org\n"),
                            ("table", "Name | Size\n:--- | ---:\nA | 1\n"), ("block quote", "> A quote.\n"),
                            ("ordered list", "1. [Late](late.md)\n"), ("indented code", "    code\n"),
                            ("attribute list", "{: .note }\n"), ("second level-1 heading", "# Second topic\n\n- [Late](late.md)\n"),
                            ("dot segment", "- [Rings](./../rings/README.md): rings.\n"),
                            ("dot-dot segment", "- [Rings](sub/../../rings/README.md): rings.\n"),
                            ("dot segment in the list", "- [Late](./late.md)\n")):
            with self.subTest(name):
                text = f"# First topic\n\n- [Old](old.md)\n\n## Related topics\n\n{block}"
                report = self.add_sylow(text)
                self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(), f"{text}\n- [Sylow](sylow.md)\n")
                self.assertEqual((report["appended"], report["unlisted"]), (["Algebra/groups/sylow.md"], []))

    def test_a_page_listed_nowhere_fails_the_run(self) -> None:
        report = {kind: [] for kind in ("added", "folders", "gone", "changed", "unindexed", "parts", "replaced", "appended",
                                         "held", "held_problems", "duplicates", "duplicate_problems",
                                         "stale_duplicates", "unassigned")}
        report["unlisted"] = ["Algebra/groups/sylow.md"]
        lean = SimpleNamespace(index_project=lambda *args, **kwargs: SimpleNamespace(declarations={}))
        with patch.dict("sys.modules", {"autoform_cli": SimpleNamespace(lean=lean), "autoform_cli.lean": lean}), \
                patch.object(wiki, "generate", lambda *args: {}), patch.object(sync, "apply_declarations", lambda *args: report), \
                patch.object(sync, "refresh_catalog", lambda generated: None), \
                patch("sys.stdout", new_callable=io.StringIO) as output, patch("sys.stderr", new_callable=io.StringIO) as errors:
            self.assertEqual(sync.run_declarations(), 1)
        self.assertIn("error: Algebra/groups/sylow.md is listed on no folder page", errors.getvalue())
        self.assertIn("Lines of a part list that the refresh replaced or removed", output.getvalue())

    def test_a_held_marker_to_fix_stops_the_run_before_the_catalog(self) -> None:
        report = {kind: [] for kind in ("added", "folders", "gone", "changed", "unindexed", "parts", "replaced", "appended",
                                         "unlisted", "held")}
        report["held_problems"] = ["Algebra/a.md: its held marker names no declaration"]
        refreshed = []
        lean = SimpleNamespace(index_project=lambda *args, **kwargs: SimpleNamespace(declarations={}))
        with patch.dict("sys.modules", {"autoform_cli": SimpleNamespace(lean=lean), "autoform_cli.lean": lean}), \
                patch.object(wiki, "generate", lambda *args: {}), patch.object(sync, "apply_declarations", lambda *args: report), \
                patch.object(sync, "refresh_catalog", refreshed.append), \
                patch("sys.stdout", new_callable=io.StringIO) as output, patch("sys.stderr", new_callable=io.StringIO) as errors:
            self.assertEqual(sync.run_declarations(), 1)
        self.assertEqual(refreshed, [])
        self.assertEqual(output.getvalue(), "Held markers to fix: 1; the run wrote nothing\n")
        self.assertIn("error: Algebra/a.md: its held marker names no declaration; fix the marker", errors.getvalue())

    def test_a_duplicates_list_to_fix_stops_the_run_before_the_catalog(self) -> None:
        report = {kind: [] for kind in ("added", "folders", "gone", "changed", "unindexed", "parts", "replaced", "appended",
                                         "unlisted", "held", "held_problems", "duplicates")}
        report["duplicate_problems"] = ["Algebra/a.md: it lists its own declaration Ext.a as a duplicate"]
        refreshed = []
        lean = SimpleNamespace(index_project=lambda *args, **kwargs: SimpleNamespace(declarations={}))
        with patch.dict("sys.modules", {"autoform_cli": SimpleNamespace(lean=lean), "autoform_cli.lean": lean}), \
                patch.object(wiki, "generate", lambda *args: {}), patch.object(sync, "apply_declarations", lambda *args: report), \
                patch.object(sync, "refresh_catalog", refreshed.append), \
                patch("sys.stdout", new_callable=io.StringIO) as output, patch("sys.stderr", new_callable=io.StringIO) as errors:
            self.assertEqual(sync.run_declarations(), 1)
        self.assertEqual(refreshed, [])
        self.assertEqual(output.getvalue(), "Duplicates lists to fix: 1; the run wrote nothing\n")
        self.assertIn("error: Algebra/a.md: it lists its own declaration Ext.a as a duplicate; fix the list and run "
                      "again", errors.getvalue())

    def test_a_row_whose_credit_is_refused_neither_places_nor_keeps_a_page(self) -> None:
        # A flagged row that also names Ext.a is reported and left alone, as lean-facts and mathlib-names refuse it: it
        # neither keeps Ext.a from a page nor places the module's new page, and the run writes nothing until it is
        # fixed. Fixed, the page keeps Ext.a and the new page joins it.
        self.page("Algebra/README.md", "# Algebra\n\n- [Groups](groups/README.md)\n")
        self.page("Algebra/groups/README.md", "# Groups\n\n- [A](a.md)\n")
        self.page("Algebra/groups/a.md", "# A\n\nA statement.\n")
        mathlib = {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.a"}}
        flagged = self.about("Algebra/groups/a.md", id="af_000000000000000000000001",
                             object=[mathlib, {"location": {"declaration": "Ext.a"}}],
                             extensions={"org.autoform": {"mathlib": True}})
        folders = [self.about("Algebra/README.md"), self.about("Algebra/groups/README.md")]
        self.annotate([*folders, flagged])
        files = lambda: {path: path.read_bytes() for path in sorted([*wiki.ROADMAP.rglob("*"), *sync.LINKS.iterdir()])
                         if path.is_file()}
        before = files()
        targets = [declaration("Ext.a", "a", "A", "A statement."), declaration("Ext.new", "new", "New", "New.")]
        index = SimpleNamespace(declarations={"Ext.a": None, "Ext.new": None})
        report = sync.apply_declarations(targets, index)
        self.assertEqual(report["credit_problems"], [
            "Algebra/groups/a.md sets `mathlib` but names 1 Mathlib declarations in Lean links and 1 of this project; "
            "a Mathlib-credited row names exactly one Mathlib declaration and none of this project"])
        self.assertEqual((report["added"], report["gone"]), ([], []))
        self.assertEqual(files(), before)
        self.assertFalse(sync.STATE.exists())
        lean = SimpleNamespace(index_project=lambda *args, **kwargs: index)
        reader = sync.reader()
        refreshed = []
        with patch.dict("sys.modules", {"autoform_cli": SimpleNamespace(lean=lean, annotations=reader),
                                        "autoform_cli.lean": lean, "autoform_cli.annotations": reader}), \
                patch.object(wiki, "generate", lambda *args: {}), \
                patch.object(sync, "refresh_catalog", refreshed.append), \
                patch("sys.stdout", new_callable=io.StringIO) as output, \
                patch("sys.stderr", new_callable=io.StringIO) as errors:
            self.assertEqual(sync.run_declarations(), 1)
        self.assertEqual((refreshed, output.getvalue()), ([], "Rows to fix: 1; the run wrote nothing\n"))
        self.assertIn("error: Algebra/groups/a.md sets `mathlib` but names 1 Mathlib declarations", errors.getvalue())
        self.assertEqual(files(), before)
        # The Mathlib link kept as a reference, without the flag: the page credits Ext.a again.
        self.annotate([*folders, {key: value for key, value in flagged.items() if key != "extensions"}])
        report = sync.apply_declarations(targets, index)
        self.assertEqual((report["credit_problems"], report["added"]), ([], ["Ext.new -> Algebra/groups/new.md"]))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         "# Groups\n\n- [A](a.md)\n- [New](new.md)\n")

    def test_a_declaration_two_pages_credit_neither_places_nor_keeps_a_page(self) -> None:
        # Two valid rows on two pages crediting one declaration, Mathlib's or this project's, leave its owner
        # ambiguous: the run reports them and writes nothing, as mathlib-names, lean-facts and extraction refuse them.
        self.page("Algebra/README.md", "# Algebra\n\n- [Groups](groups/README.md)\n")
        self.page("Algebra/groups/README.md", "# Groups\n\n- [A](a.md)\n- [B](b.md)\n")
        self.page("Algebra/groups/a.md", "# A\n\nA statement.\n")
        self.page("Algebra/groups/b.md", "# B\n\nA statement.\n")
        mathlib = [{"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.a"}}]
        flag = {"org.autoform": {"mathlib": True}}
        cases = {
            "Mathlib's": ({"object": mathlib, "extensions": flag},
                          "Algebra/groups/a.md and Algebra/groups/b.md both credit the Mathlib declaration M.a; a "
                          "declaration has one page"),
            "this project's": ({"object": [{"location": {"declaration": "Ext.a"}}]},
                               "Algebra/groups/a.md and Algebra/groups/b.md both credit the declaration Ext.a of this "
                               "project; a declaration has one page"),
        }
        targets = [declaration("Ext.a", "a", "A", "A statement."), declaration("Ext.new", "new", "New", "New.")]
        index = SimpleNamespace(declarations={"Ext.a": None, "Ext.new": None})
        for case, (fields, message) in cases.items():
            with self.subTest(case=case):
                self.annotate([self.about("Algebra/README.md"), self.about("Algebra/groups/README.md"),
                               self.about("Algebra/groups/a.md", **fields),
                               self.about("Algebra/groups/b.md", **fields)])
                files = lambda: {path: path.read_bytes() for path in sorted([*wiki.ROADMAP.rglob("*"),
                                                                              *sync.LINKS.iterdir()]) if path.is_file()}
                before = files()
                report = sync.apply_declarations(targets, index)
                self.assertEqual((report["credit_problems"], report["added"]), ([message], []))
                self.assertEqual(files(), before)
                self.assertFalse(sync.STATE.exists())
                self.assertIn(message, sync.credited_mathlib(sync.read_annotations())[1])

    def test_a_legacy_row_and_an_explicit_one_neither_place_nor_keep_a_page(self) -> None:
        # A page crediting Ext.main and an earlier sync's module and name the index resolves to it: the run reports
        # them and writes nothing. Once the explicit credit goes, the lone legacy row keeps Ext.main its page.
        self.page("Algebra/README.md", "# Algebra\n\n- [A](a.md)\n- [B](b.md)\n")
        self.page("Algebra/a.md", "# A\n\nA statement.\n")
        self.page("Algebra/b.md", "# B\n\nA statement.\n")
        legacy = self.about("Algebra/b.md", extensions={sync.OWN: {"module": "Ext", "name": "main"}})
        index = SimpleNamespace(declarations={"Ext.main": SimpleNamespace(path=Path("Ext.lean"), line=1,
                                                                          keyword="theorem")})
        targets = [declaration("Ext.main", "main", "Main", "Main.")]
        self.annotate([self.about("Algebra/README.md"),
                       self.about("Algebra/a.md", object=[{"location": {"declaration": "Ext.main"}}]), legacy])
        files = lambda: {path: path.read_bytes() for path in sorted([*wiki.ROADMAP.rglob("*"), *sync.LINKS.iterdir()])
                         if path.is_file()}
        before = files()
        report = sync.apply_declarations(targets, index)
        self.assertEqual(report["credit_problems"], [
            "Algebra/a.md and Algebra/b.md (by the module and name an earlier sync wrote) both stand for the "
            "declaration Ext.main of this project; a declaration has one page"])
        self.assertEqual((files(), sync.STATE.exists()), (before, False))
        self.annotate([self.about("Algebra/README.md"), self.about("Algebra/a.md"), legacy])
        report = sync.apply_declarations(targets, index)
        self.assertEqual((report["credit_problems"], report["added"], report["unindexed"]), ([], [], []))

    def test_an_edit_that_does_not_render_as_meant_is_left_out(self) -> None:
        # The whitelist admits a heading holding raw HTML, but a browser builds the rest of the page inside the
        # textarea it opens: the new page's item would show no link, so the page is left as it is and the new page
        # reported as listed nowhere. Raw HTML inline, in a quote or in a list item is caught the same way, while a
        # fence that renders it as code takes the item.
        for name, text, simple in (
                ("heading", "# T\n\n- [Old](old.md)\n\n## Example <textarea>\n\n- [Late](late.md)\n", True),
                ("inline", "# T\n\nExample: <textarea>\n\n- [Old](old.md)\n", False),
                ("quoted", "# T\n\n- [Old](old.md)\n\n> <textarea>\n", False),
                ("in a list item", "# T\n\n- [Old](old.md)\n  <textarea>\n", False),
                # A select drops the list that follows; a table keeps the heading open, which takes in that list.
                ("select in a heading", "# T\n\n- [Old](old.md)\n\n## Example <select>\n\n- [Late](late.md)\n", True),
                ("table in a heading", "# T\n\n- [Old](old.md)\n\n## Example <table>\n\n- [Late](late.md)\n", True)):
            with self.subTest(name):
                self.assertEqual(sync.simple_page(text, code=True), simple)
                report = self.add_sylow(text)
                self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(), text)
                self.assertEqual((report["appended"], report["unlisted"]), ([], ["Algebra/groups/sylow.md"]))
        text = "# T\n\n- [Old](old.md)\n\n    ```\n    <textarea>\n    ```\n"
        report = self.add_sylow(text)
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(), f"{text}\n- [Sylow](sylow.md)\n")
        self.assertEqual((report["appended"], report["unlisted"]), (["Algebra/groups/sylow.md"], []))

    def test_a_part_copy_that_does_not_render_as_meant_is_left_to_an_editor(self) -> None:
        # The whitelist admits a part's entry whose math runs past the link, or whose attribute list sets another
        # href; its copy would show no link, or a link to the wrong page, so the copy stays as it is.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        for name, entry in (("math across the link", "- [$A](a.md)$\n"), ("attribute list", '- [A](a.md){: href="x.md"}\n')):
            with self.subTest(name):
                part = f"# Part 1 of 1\n\n{entry}- [B](b.md)\n"
                self.assertTrue(sync.simple_page(part))
                text = "# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n- [B](part-01/b.md)\n"
                self.page("Algebra/groups/README.md", text)
                self.page("Algebra/groups/part-01/README.md", part)
                sync.LINKS.mkdir(parents=True, exist_ok=True)
                report = sync.apply_declarations([], SimpleNamespace(declarations={}))
                self.assertEqual((groups / "README.md").read_text(), text)
                self.assertEqual(report["parts"], ["Algebra/groups/part-01"])

    def test_a_part_list_keeps_every_entry_it_cannot_read(self) -> None:
        # A part's entry with a fragment, a query, a dot in its name, a deeper path, another extension or a scheme is
        # no entry the copy can take, and a copy's item with a fragment or a deeper path is none it can replace: the
        # copy stays as it is, and no item is dropped from the folder page.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        copy = "- [A](part-01/a.md)\n- [B](part-01/b.md)\n"
        for name, part, listed in (("fragment", "- [A](a.md#statement)\n", copy), ("query", "- [A](a.md?x=1)\n", copy),
                                   ("dot in the name", "- [A](a.b.md)\n", copy), ("deeper path", "- [A](deep/a.md)\n", copy),
                                   ("other extension", "- [A](a.markdown)\n", copy), ("scheme", "- [A](urn:x)\n", copy),
                                   ("copy with a fragment", "- [A](a.md)\n", "- [A](part-01/a.md#appendix)\n- [B](part-01/b.md)\n"),
                                   ("copy with a deeper path", "- [A](a.md)\n", copy + "- [Note](part-01/deep/note.md)\n")):
            with self.subTest(name):
                text = f"# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n{listed}"
                self.page("Algebra/groups/README.md", text)
                self.page("Algebra/groups/part-01/README.md", f"# Part 1 of 1\n\n{part}- [B](b.md)\n- [C](c.md)\n")
                sync.LINKS.mkdir(parents=True, exist_ok=True)
                report = sync.apply_declarations([], SimpleNamespace(declarations={}))
                self.assertEqual((groups / "README.md").read_text(), text)
                self.assertEqual(report["parts"], ["Algebra/groups/part-01"])

    def test_an_encoded_link_makes_a_page_not_simple(self) -> None:
        # "%2e%2e/" reads as "../", so it could lead anywhere: the new page goes at the end. "&period;&period;&sol;" is
        # that too, but the site already shows a page with a character reference as typed, so the page is left alone.
        text = "# Groups\n\n- [Old](old.md)\n\n## Related topics\n\n- [Rings](%2e%2e/rings/README.md): rings.\n"
        report = self.add_sylow(text)
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(), f"{text}\n- [Sylow](sylow.md)\n")
        self.assertEqual((report["appended"], report["unlisted"]), (["Algebra/groups/sylow.md"], []))
        text = text.replace("%2e%2e/", "&period;&period;&sol;")
        report = self.add_sylow(text)
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(), text)
        self.assertEqual((report["appended"], report["unlisted"]), ([], ["Algebra/groups/sylow.md"]))

    def test_a_closing_section_holds_none_of_the_own_list(self) -> None:
        # A page whose only list of its folder's pages is under "Sources", or a section within "Related topics", has no
        # own list: the new page goes ahead of the first section, not into either.
        # A closing heading with emphasis or code marks is read as the site shows it.
        for name, closing in (("sources", "## Sources\n\n- [Notes](notes.md)\n"),
                              ("within related topics", "## Related topics\n\n### Here\n\n- [Notes](notes.md)\n"),
                              ("bold", "## **Sources**\n\n- [Notes](notes.md)\n"), ("code", "## `Sources`\n\n- [Notes](notes.md)\n"),
                              ("emphasis", "## _Related topics_\n\n### Here\n\n- [Notes](notes.md)\n"),
                              ("starred emphasis", "## *Sources*\n\n- [Notes](notes.md)\n"),
                              ("two spaces", "## Related  topics\n\n- [Notes](notes.md)\n"),
                              ("closing sequence", "## Sources ##\n\n- [Notes](notes.md)\n")):
            with self.subTest(name):
                report = self.add_sylow(f"# Groups\n\nProse.\n\n{closing}")
                self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                                 f"# Groups\n\nProse.\n\n- [Sylow](sylow.md)\n\n{closing}")
                self.assertEqual((report["appended"], report["unlisted"]), ([], []))

    def test_a_literal_hash_makes_another_title(self) -> None:
        # The site keeps a "#" inside a title: "Sources #2" closes nothing, so the list under it is the own list.
        report = self.add_sylow("# Groups\n\nProse.\n\n## Sources #2\n\n- [Notes](notes.md)\n")
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         "# Groups\n\nProse.\n\n## Sources #2\n\n- [Notes](notes.md)\n- [Sylow](sylow.md)\n")
        self.assertEqual((report["appended"], report["unlisted"]), ([], []))

    def test_a_new_section_keeps_its_modules_code(self) -> None:
        # page_title drops a title's backticks, which would leave "<textarea>" as raw HTML: the heading keeps them. A
        # "<" or "&" outside code is written as it is, as generate_wiki writes it; a title Autoform's check would have
        # the site show as typed, taking the page's links with it, gives way to the module's name.
        text = "# Bakery\n\n## The algorithm\n\n- [State](state.md)\n\n## Mutual exclusion\n\n- [Invariant](invariant.md)\n"
        for title, heading in (("The `<textarea>` example", "The `<textarea>` example"),
                               ("Bounds for 1 < |x| < 3", "Bounds for 1 < |x| < 3"), ("Sheaves & sites", "Sheaves & sites"),
                               ("Ratio &lt; one", "Two Process"), ("Orders<sup>2</sup>", "Two Process")):
            with self.subTest(title):
                self.page("Algebra/bakery/README.md", text)
                self.annotate([])
                (wiki.ROADMAP / "Algebra" / "bakery" / "turn.md").unlink(missing_ok=True)
                turn = declaration("Ext.turn", "turn", "Turn", "Turn.", module=("Ext", "TwoProcess"))
                turn.path, turn.module_title = wiki.ROADMAP / "Algebra" / "bakery" / "turn.md", title
                report = sync.apply_declarations([turn], SimpleNamespace(declarations={"Ext.turn": None}))
                self.assertEqual((wiki.ROADMAP / "Algebra" / "bakery" / "README.md").read_text(),
                                 f"{text}\n## {heading}\n\n- [Turn](turn.md)\n")
                self.assertEqual((report["appended"], report["unlisted"]), ([], []))

    def test_an_edit_keeps_the_pages_line_ends_and_bytes(self) -> None:
        # A page written with "\r\n" keeps them, the new item's included, and nothing at its end is dropped.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        for name, text, edited in (
                ("insert", "# Groups\n\n- [Old](old.md)\n\n## Related topics\n\n- [Rings](../rings/README.md)\n",
                 "# Groups\n\n- [Old](old.md)\n- [Sylow](sylow.md)\n\n## Related topics\n\n- [Rings](../rings/README.md)\n"),
                ("append", "# Groups\n\n- [Old](old.md)\n  note\n", "# Groups\n\n- [Old](old.md)\n  note\n\n- [Sylow](sylow.md)\n"),
                ("no line end at the end", "# Groups\n\n- [Old](old.md)", "# Groups\n\n- [Old](old.md)\n- [Sylow](sylow.md)"),
                ("blank lines at the end", "# Groups\n\n- [Old](old.md)\n\n\n", "# Groups\n\n- [Old](old.md)\n- [Sylow](sylow.md)\n\n\n")):
            for newline in ("\n", "\r\n"):
                with self.subTest(name, newline=newline):
                    (groups / "README.md").parent.mkdir(parents=True, exist_ok=True)
                    (groups / "README.md").write_bytes(text.replace("\n", newline).encode())
                    self.annotate([])
                    (groups / "sylow.md").unlink(missing_ok=True)
                    sylow = declaration("Ext.sylow", "sylow", "Sylow", "Sylow.", module=("Ext", "Sylow"))
                    sylow.path = groups / "sylow.md"
                    sync.apply_declarations([sylow], SimpleNamespace(declarations={"Ext.sylow": None}))
                    self.assertEqual((groups / "README.md").read_bytes(), edited.replace("\n", newline).encode())
        # A part's copy refreshed on a page written with "\r\n" keeps them too.
        text = "# Groups\r\n\r\n## [Part 1 of 1](part-01/README.md)\r\n\r\n- [A](part-01/a.md)\r\n"
        (groups / "README.md").write_bytes(text.encode())
        self.page("Algebra/groups/part-01/README.md", "# Part 1 of 1\n\n- [A](a.md)\n- [B](b.md)\n")
        self.annotate([])
        sync.apply_declarations([], SimpleNamespace(declarations={}))
        self.assertEqual((groups / "README.md").read_bytes(), (text + "- [B](part-01/b.md)\r\n").encode())

    def test_a_page_with_mixed_line_ends_takes_a_new_page_at_its_end(self) -> None:
        text = "# Groups\r\n\r\n- [Old](old.md)\n"
        groups = wiki.ROADMAP / "Algebra" / "groups"
        groups.mkdir(parents=True)
        (groups / "README.md").write_bytes(text.encode())
        sync.LINKS.mkdir(parents=True)
        sylow = declaration("Ext.sylow", "sylow", "Sylow", "Sylow.", module=("Ext", "Sylow"))
        sylow.path = groups / "sylow.md"
        report = sync.apply_declarations([sylow], SimpleNamespace(declarations={"Ext.sylow": None}))
        self.assertEqual((groups / "README.md").read_bytes(), (text + "\n- [Sylow](sylow.md)\n").encode())
        self.assertEqual(report["appended"], ["Algebra/groups/sylow.md"])

    def test_a_page_the_site_shows_as_typed_is_left_as_it_is(self) -> None:
        # autoform render publishes a page that Autoform's check flags as typed, in one block with no link or heading:
        # a new page listed there would be listed nowhere, so the page is left as it is and the new page reported.
        for name, text in (("raw HTML in a heading", "# Groups\n\n- [Old](old.md)\n\n## Orders<sup>2</sup>\n\n- [Late](late.md)\n"),
                           ("character reference", "# Groups\n\nGroups &mdash; and their actions.\n\n- [Old](old.md)\n"),
                           ("attribute list", "# Groups\n\nGroups and their actions.\n{: .lead}\n\n- [Old](old.md)\n"),
                           ("unsafe scheme", "# Groups\n\n- [Old](old.md)\n\n## Related topics\n\n- [Book](urn:isbn:0)\n"),
                           ("open comment", "# Groups\n\n- [Old](old.md)\n\n<!-- todo\n")):
            with self.subTest(name):
                report = self.add_sylow(text)
                self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(), text)
                self.assertEqual((report["appended"], report["unlisted"]), ([], ["Algebra/groups/sylow.md"]))
        # A part's entry with a character reference would take its folder page off the site the same way.
        text = "# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n- [B](part-01/b.md)\n"
        self.page("Algebra/groups/README.md", text)
        self.page("Algebra/groups/part-01/README.md", "# Part 1 of 1\n\n- [A &amp; B](a.md)\n- [B](b.md)\n")
        report = sync.apply_declarations([], SimpleNamespace(declarations={}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(), text)
        self.assertEqual(report["parts"], ["Algebra/groups/part-01"])

    def test_a_style_that_hides_the_new_link_is_caught(self) -> None:
        # The tree a browser builds still holds a link a style hides; Autoform's check rejects the style, so the page is
        # left as it is and the new page reported as listed nowhere.
        for rule in ("display:none", "opacity: 0"):
            with self.subTest(rule):
                text = f'# Groups\n\n- [Old](old.md)\n\n## Notes <style>a[href="sylow.md"] {{ {rule} }}</style>\n'
                self.assertTrue(sync.simple_page(text, code=True))
                report = self.add_sylow(text)
                self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(), text)
                self.assertEqual((report["appended"], report["unlisted"]), ([], ["Algebra/groups/sylow.md"]))

    def test_a_new_section_follows_the_sections_within_the_last_one(self) -> None:
        # The last section's own sections are part of it: the new section goes after them, so that none of them falls
        # under it.
        text = ("# Bakery\n\n## The algorithm\n\n- [State](state.md)\n\n## Mutual exclusion\n\n- [Invariant](invariant.md)\n\n"
                "### Further reading\n\nThe original paper.\n\n## Related topics\n\n- [Locks](../locks/README.md)\n")
        self.page("Algebra/bakery/README.md", text)
        self.annotate([])
        turn = declaration("Ext.turn", "turn", "Turn", "Turn.", module=("Ext", "TwoProcess"))
        turn.path, turn.module_title = wiki.ROADMAP / "Algebra" / "bakery" / "turn.md", "Two-process bakery"
        report = sync.apply_declarations([turn], SimpleNamespace(declarations={"Ext.turn": None}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "bakery" / "README.md").read_text(), text.replace(
            "## Related topics", "## Two-process bakery\n\n- [Turn](turn.md)\n\n## Related topics"))
        self.assertEqual((report["appended"], report["unlisted"]), ([], []))

    def test_a_new_section_takes_the_level_of_the_shallowest_one(self) -> None:
        # The last section of the list is an "### Theorems" within "## Main results": a new "###" section there would
        # sit under a heading that says nothing of its module, so it takes the level of "## Basics", after all that
        # "## Main results" holds.
        text = ("# Bakery\n\n## Basics\n\n- [State](state.md)\n\n## Main results\n\nThe main theorems.\n\n### Theorems\n\n"
                "- [Invariant](invariant.md)\n\n## Related topics\n\n- [Locks](../locks/README.md)\n")
        self.page("Algebra/bakery/README.md", text)
        self.annotate([])
        turn = declaration("Ext.turn", "turn", "Turn", "Turn.", module=("Ext", "TwoProcess"))
        turn.path, turn.module_title = wiki.ROADMAP / "Algebra" / "bakery" / "turn.md", "Two-process bakery"
        report = sync.apply_declarations([turn], SimpleNamespace(declarations={"Ext.turn": None}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "bakery" / "README.md").read_text(), text.replace(
            "## Related topics", "## Two-process bakery\n\n- [Turn](turn.md)\n\n## Related topics"))
        self.assertEqual((report["appended"], report["unlisted"]), ([], []))

    def test_a_new_sections_heading_takes_no_other_headings_id(self) -> None:
        # A new "Examples" ahead of the page's own would take its id, "examples", and move the links to it: the
        # section takes its module's name instead.
        text = ("# Bakery\n\n## The algorithm\n\n- [State](state.md)\n\n## Mutual exclusion\n\n- [Invariant](invariant.md)\n\n"
                "## Examples\n\nSee the exercises.\n")
        self.page("Algebra/bakery/README.md", text)
        self.annotate([])
        turn = declaration("Ext.turn", "turn", "Turn", "Turn.", module=("Ext", "TwoProcess"))
        turn.path, turn.module_title = wiki.ROADMAP / "Algebra" / "bakery" / "turn.md", "Examples"
        report = sync.apply_declarations([turn], SimpleNamespace(declarations={"Ext.turn": None}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "bakery" / "README.md").read_text(), text.replace(
            "## Examples", "## Two Process\n\n- [Turn](turn.md)\n\n## Examples"))
        self.assertEqual((report["appended"], report["unlisted"]), ([], []))

    def test_a_new_sections_heading_takes_no_id_an_earlier_heading_has(self) -> None:
        # Another "Examples" after the page's own would be given "examples_1", so its id is not the one its title has:
        # the section takes its module's name instead, and when that is taken too, the new page is listed nowhere. A
        # section named as the page itself is kept: its id takes "_1" after the title's, which keeps its own, so no id
        # moves; but not when a section has that name too.
        for name, title, earlier, heading in (
                ("title taken", "Bakery", "## Examples\n\n- [State](state.md)\n", "Two Process"),
                ("title and name taken", "Bakery", "## Examples\n\n- [State](state.md)\n\n## Two Process\n\nText.\n", None),
                ("the page's title", "Examples", "## Basics\n\n- [State](state.md)\n", "Examples"),
                ("the page's title and a section's", "Examples", "## Examples\n\n- [State](state.md)\n", "Two Process")):
            with self.subTest(name):
                text = f"# {title}\n\n{earlier}\n## Mutual exclusion\n\n- [Invariant](invariant.md)\n"
                self.page("Algebra/bakery/README.md", text)
                self.annotate([])
                (wiki.ROADMAP / "Algebra" / "bakery" / "turn.md").unlink(missing_ok=True)
                turn = declaration("Ext.turn", "turn", "Turn", "Turn.", module=("Ext", "TwoProcess"))
                turn.path, turn.module_title = wiki.ROADMAP / "Algebra" / "bakery" / "turn.md", "Examples"
                report = sync.apply_declarations([turn], SimpleNamespace(declarations={"Ext.turn": None}))
                self.assertEqual((wiki.ROADMAP / "Algebra" / "bakery" / "README.md").read_text(),
                                 f"{text}\n## {heading}\n\n- [Turn](turn.md)\n" if heading else text)
                self.assertEqual(report["unlisted"], [] if heading else ["Algebra/bakery/turn.md"])

    def test_a_section_named_as_its_page_is_kept(self) -> None:
        # The "Resolution" module on the "Resolution" page: its "## Resolution" is given "resolution_1", while the
        # title keeps "resolution", so links to the title still land on it.
        text = ("# Resolution\n\n- [Resolvent](resolvent.md)\n\n## Soundness\n\n- [Soundness](satisfies.md)\n\n"
                "## Completeness\n\n- [Completeness](completeness.md)\n\n## Related topics\n\n- [Size](../size/README.md)\n")
        self.page("Logic/resolution/README.md", text)
        self.annotate([])
        lit = declaration("Ext.lit", "lit", "Lit", "A literal.", module=("Ext", "Resolution"))
        lit.path, lit.module_title = wiki.ROADMAP / "Logic" / "resolution" / "lit.md", "Resolution"
        report = sync.apply_declarations([lit], SimpleNamespace(declarations={"Ext.lit": None}))
        self.assertEqual((wiki.ROADMAP / "Logic" / "resolution" / "README.md").read_text(), text.replace(
            "## Related topics", "## Resolution\n\n- [Lit](lit.md)\n\n## Related topics"))
        self.assertEqual((report["appended"], report["unlisted"]), ([], []))

    def test_a_line_break_only_autoform_reads_makes_a_page_not_simple(self) -> None:
        # Autoform splits lines wherever str.splitlines does, at a form feed or U+2028 too: such a page takes the new
        # page at its end.
        for name, character in (("form feed", "\f"), ("line separator", "\u2028"), ("next line", "\x85")):
            with self.subTest(name):
                text = f"# Groups\n\nProse.{character}More prose.\n\n- [Old](old.md)\n"
                self.assertFalse(sync.simple_page(text, code=True))
                report = self.add_sylow(text)
                self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(), f"{text}\n- [Sylow](sylow.md)\n")
                self.assertEqual((report["appended"], report["unlisted"]), (["Algebra/groups/sylow.md"], []))

    def test_nothing_is_written_when_the_edit_check_cannot_be_built(self) -> None:
        # A site configuration the check cannot read, or a module it needs only to read the rendered page, stops the
        # run before any page is written, so none is orphaned.
        site = self.tmp / "mkdocs.yml"
        site.write_text("markdown_extensions:\n  - toc:\n      title: !ENV TITLE\n")
        self.addCleanup(sync.renderer.cache_clear)
        for name, broken in (("site configuration", patch.object(sync, "SITE", site)),
                             ("rendered page", patch.dict("sys.modules", {"html5lib": None}))):
            with self.subTest(name):
                sync.renderer.cache_clear()
                self.page("Algebra/groups/README.md", "# Groups\n\n- [Old](old.md)\n")
                self.annotate([])
                sylow = declaration("Ext.sylow", "sylow", "Sylow", "Sylow.", module=("Ext", "Sylow"))
                sylow.path = wiki.ROADMAP / "Algebra" / "groups" / "sylow.md"
                with broken, self.assertRaises(Exception):
                    sync.apply_declarations([sylow], SimpleNamespace(declarations={"Ext.sylow": None}))
                self.assertFalse(sylow.path.exists())
                self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(), "# Groups\n\n- [Old](old.md)\n")

    def test_a_part_heading_with_a_section_within_it_is_left_to_an_editor(self) -> None:
        # The copy is read only up to the next heading: part links under a section within the part's, or anywhere in
        # its section but the copy, would be left as they are, stale or not. The copy stays as it is, and the part is
        # reported, even when nothing under the inner heading links a part.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        for name, under in (("part links under a section within", "\n### Note\n\n- [Old](part-01/old.md)\n"),
                            ("no part link under a section within", "\n### Note\n\nSee the overview.\n"),
                            ("part link in text", "\nSee [Old](part-01/old.md) for more.\n")):
            with self.subTest(name):
                text = f"# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n- [A](part-01/a.md)\n{under}"
                self.page("Algebra/groups/README.md", text)
                self.page("Algebra/groups/part-01/README.md", "# Part 1 of 1\n\n- [A](a.md)\n- [B](b.md)\n")
                sync.LINKS.mkdir(parents=True, exist_ok=True)
                report = sync.apply_declarations([], SimpleNamespace(declarations={}))
                self.assertEqual((groups / "README.md").read_text(), text)
                self.assertEqual(report["parts"], ["Algebra/groups/part-01"])

    def test_a_part_page_with_a_section_within_its_own_part_is_left_to_an_editor(self) -> None:
        # A part split into parts lists its own parts under their headings: a section within one of them, with items
        # under it or none, could make those items read as the part's own entries, so the outer copy stays as it is.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        copy = "- [Part 1 of 2](part-01/part-01/README.md)\n- [Part 2 of 2](part-01/part-02/README.md)\n"
        for name, note in (("items under it", "\n### Note\n\n- [C](c.md)\n"), ("nothing under it", "\n### Note\n")):
            with self.subTest(name):
                text = f"# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n{copy}"
                self.page("Algebra/groups/README.md", text)
                self.page("Algebra/groups/part-01/README.md", "# Part 1 of 1\n\n## [Part 1 of 2](part-01/README.md)\n\n- [A](part-01/a.md)\n\n"
                          f"## [Part 2 of 2](part-02/README.md)\n\n- [B](part-02/b.md)\n{note}")
                sync.LINKS.mkdir(parents=True, exist_ok=True)
                report = sync.apply_declarations([], SimpleNamespace(declarations={}))
                self.assertEqual((groups / "README.md").read_text(), text)
                self.assertEqual(report["parts"], ["Algebra/groups/part-01"])

    def test_a_part_refresh_reports_a_line_it_replaces_or_removes(self) -> None:
        # A note added on the folder page's copy only is not the part's entry, nor is a line for a page the part no
        # longer lists: the refresh replaces the one, removes the other, and says so.
        text = "# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n- [A](part-01/a.md) (start here)\n- [C](part-01/c.md)\n"
        self.page("Algebra/groups/README.md", text)
        self.page("Algebra/groups/part-01/README.md", "# Part 1 of 1\n\n- [A](a.md)\n- [B](b.md)\n")
        report = sync.apply_declarations([], SimpleNamespace(declarations={}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         "# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n- [A](part-01/a.md)\n- [B](part-01/b.md)\n")
        self.assertEqual(report["replaced"], ["Algebra/groups/part-01: - [A](part-01/a.md) (start here)",
                                              "Algebra/groups/part-01: - [C](part-01/c.md)"])
        # One copy of a line too many is removed, and reported once for each copy.
        text = "# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n- [A](part-01/a.md)\n- [A](part-01/a.md)\n- [B](part-01/b.md)\n"
        self.page("Algebra/groups/README.md", text)
        report = sync.apply_declarations([], SimpleNamespace(declarations={}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         "# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n- [A](part-01/a.md)\n- [B](part-01/b.md)\n")
        self.assertEqual(report["replaced"], ["Algebra/groups/part-01: - [A](part-01/a.md)"])

    def test_verify_edit_reads_the_page_as_the_site_renders_it(self) -> None:
        page = "# T\n\n- [A](a.md)\n\n## Related topics\n\n- [R](../r/README.md)\n"
        good = "# T\n\n- [A](a.md)\n- [B](b.md)\n\n## Related topics\n\n- [R](../r/README.md)\n"
        self.assertTrue(sync.verify_edit(page, good, [("- [B](b.md)", "b.md", (0, "# T"))]))
        # Under the wrong heading, merged into a paragraph, losing a link, or hidden in code: each fails.
        self.assertFalse(sync.verify_edit(page, good, [("- [B](b.md)", "b.md", (1, "## Related topics"))]))
        self.assertFalse(sync.verify_edit(page, page.replace("- [A](a.md)\n", "- [A](a.md)\nB [B](b.md)\n"),
                                          [("- [B](b.md)", "b.md", (0, "# T"))]))
        self.assertFalse(sync.verify_edit(page, good.replace("- [R](../r/README.md)\n", ""), [("- [B](b.md)", "b.md", (0, "# T"))]))
        self.assertFalse(sync.verify_edit(page, page + "\n```\n- [B](b.md)\n```\n", [("- [B](b.md)", "b.md", None)]))
        # A heading added ahead of another's own sections takes them in; one whose id another heading had moves it.
        nested = "# T\n\n## A\n\n- [A](a.md)\n\n### Notes\n\nText.\n"
        self.assertFalse(sync.verify_edit(nested, nested.replace("### Notes", "## New\n\n- [B](b.md)\n\n### Notes"),
                                          [("- [B](b.md)", "b.md", (2, "## New"))], added=(2, "## New")))
        self.assertTrue(sync.verify_edit(nested, nested + "\n## New\n\n- [B](b.md)\n",
                                         [("- [B](b.md)", "b.md", (3, "## New"))], added=(3, "## New")))
        examples = "# T\n\n## A\n\n- [A](a.md)\n\n## Examples\n\nText.\n"
        self.assertFalse(sync.verify_edit(examples, examples.replace("## Examples", "## Examples\n\n- [B](b.md)\n\n## Examples"),
                                          [("- [B](b.md)", "b.md", (2, "## Examples"))], added=(2, "## Examples")))

    def test_a_new_section_follows_all_that_the_last_one_holds(self) -> None:
        # The prose after the last item stays in the section it closes.
        tail = "- [Invariant](invariant.md)\n\nThe invariant is Lamport's.\nIt is short.\n\n"
        self.page("Algebra/bakery/README.md", f"# Bakery\n\n## The algorithm\n\n- [State](state.md)\n\n## Mutual exclusion\n\n{tail}"
                  "## Related topics\n\n- [Rings](../rings/README.md): rings.\n")
        sync.LINKS.mkdir(parents=True)
        turn = declaration("Ext.turn", "turn", "Turn", "Turn.", module=("Ext", "TwoProcess"))
        turn.path, turn.module_title = wiki.ROADMAP / "Algebra" / "bakery" / "turn.md", "Two-process bakery"
        report = sync.apply_declarations([turn], SimpleNamespace(declarations={"Ext.turn": None}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "bakery" / "README.md").read_text(),
                         f"# Bakery\n\n## The algorithm\n\n- [State](state.md)\n\n## Mutual exclusion\n\n{tail}"
                         "## Two-process bakery\n\n- [Turn](turn.md)\n\n## Related topics\n\n- [Rings](../rings/README.md): rings.\n")
        self.assertEqual(report["appended"], [])

    def test_two_sections_with_one_title_stay_two(self) -> None:
        # A page with no listed neighbour starts a section of its own rather than join the second "Results".
        text = "# Bakery\n\n## Results\n\n- [State](state.md)\n\n## Results\n\n- [Invariant](invariant.md)\n"
        self.page("Algebra/bakery/README.md", text)
        sync.LINKS.mkdir(parents=True)
        turn = declaration("Ext.turn", "turn", "Turn", "Turn.", module=("Ext", "TwoProcess"))
        turn.path, turn.module_title = wiki.ROADMAP / "Algebra" / "bakery" / "turn.md", "Two-process bakery"
        report = sync.apply_declarations([turn], SimpleNamespace(declarations={"Ext.turn": None}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "bakery" / "README.md").read_text(),
                         f"{text}\n## Two-process bakery\n\n- [Turn](turn.md)\n")
        self.assertEqual(report["appended"], [])

    def test_a_heading_with_a_tab_after_its_marker_is_not_simple(self) -> None:
        text = "# Bakery\n\n## Basics\n\n- [State](state.md)\n\n##\tResults\n\n- [Invariant](invariant.md)\n"
        self.page("Algebra/bakery/README.md", text)
        sync.LINKS.mkdir(parents=True)
        turn = declaration("Ext.turn", "turn", "Turn", "Turn.", module=("Ext", "TwoProcess"))
        turn.path, turn.module_title = wiki.ROADMAP / "Algebra" / "bakery" / "turn.md", "Two-process bakery"
        report = sync.apply_declarations([turn], SimpleNamespace(declarations={"Ext.turn": None}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "bakery" / "README.md").read_text(), f"{text}\n- [Turn](turn.md)\n")
        self.assertEqual(report["appended"], ["Algebra/bakery/turn.md"])

    def test_a_comment_opened_in_a_code_span_hides_nothing(self) -> None:
        self.page("Algebra/groups/README.md", "# Groups\n\nUse `<!--` to open a comment.\n\n- [Old](old.md)\n\n"
                  "## Related topics\n\n- [Rings](../rings/README.md): rings.\n\n## Sources\n\nA book.\n")
        sync.LINKS.mkdir(parents=True)
        sylow = declaration("Ext.sylow", "sylow", "Sylow", "Sylow.", module=("Ext", "Sylow"))
        sylow.path = wiki.ROADMAP / "Algebra" / "groups" / "sylow.md"
        report = sync.apply_declarations([sylow], SimpleNamespace(declarations={"Ext.sylow": None}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         "# Groups\n\nUse `<!--` to open a comment.\n\n- [Old](old.md)\n- [Sylow](sylow.md)\n\n"
                         "## Related topics\n\n- [Rings](../rings/README.md): rings.\n\n## Sources\n\nA book.\n")
        self.assertEqual(report["appended"], [])

    def test_a_docstring_edit_is_reported_from_the_second_run(self) -> None:
        self.page("Algebra/groups/README.md", "# Groups\n\n- [Old](old.md)\n")
        self.page("Algebra/groups/old.md", "# Old\n\nWiki text.\n")
        self.annotate([self.about("Algebra/groups/old.md", object=[{"location": {"declaration": "Ext.old"}}])])
        self.assertEqual(sync.apply_declarations([declaration("Ext.old", "old", "Old", "First.")], INDEX)["changed"], [])
        self.assertEqual(sync.apply_declarations([declaration("Ext.old", "old", "Old", "First.")], INDEX)["changed"], [])
        changed = sync.apply_declarations([declaration("Ext.old", "old", "Old", "Second.")], INDEX)["changed"]
        self.assertEqual(changed, ["Ext.old (Algebra/groups/old.md)"])
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "old.md").read_text(), "# Old\n\nWiki text.\n")


class DocstringReport(Vault):
    def setUp(self) -> None:
        super().setUp()
        self.page("Algebra/groups/README.md", "# Groups\n\n- [Old](old.md)\n")
        self.page("Algebra/groups/old.md", "# Old\n\nWiki text.\n")
        self.annotate([self.about("Algebra/groups/old.md", object=[{"location": {"declaration": "Ext.old"}}])])
        self.source = self.tmp / "Ext" / "Groups.lean"
        self.source.parent.mkdir(parents=True, exist_ok=True)
        self.source.write_text("/-- First. -/\ntheorem old : True := trivial\n")
        self.index = SimpleNamespace(declarations={"Ext.old": SimpleNamespace(path=Path("Ext/Groups.lean"), line=2)})

    def test_a_citation_only_edit_is_reported(self) -> None:
        target = declaration("Ext.old", "old", "Old", "First.")
        target.citations = ["Book, p. 1."]
        self.assertEqual(sync.apply_declarations([target], self.index)["changed"], [])
        target.citations = ["Book, p. 2."]
        self.assertEqual(sync.apply_declarations([target], self.index)["changed"], ["Ext.old (Algebra/groups/old.md)"])

    def test_a_docstring_without_sources_keeps_its_digest(self) -> None:
        self.assertEqual(sync.docstring_digest(declaration("Ext.old", "old", "Old", "First.")), sync.digest("First."))

    def test_a_removed_docstring_is_reported_until_it_returns(self) -> None:
        self.assertEqual(sync.apply_declarations([declaration("Ext.old", "old", "Old", "First.")], self.index)["changed"], [])
        self.source.write_text("theorem old : True := trivial\n")
        self.index.declarations["Ext.old"].line = 1
        for _ in range(2):
            self.assertEqual(sync.apply_declarations([], self.index)["changed"],
                             ["Ext.old (Algebra/groups/old.md; docstring removed)"])
        self.source.write_text("/-- First. -/\ntheorem old : True := trivial\n")
        self.index.declarations["Ext.old"].line = 2
        self.assertEqual(sync.apply_declarations([declaration("Ext.old", "old", "Old", "First.")], self.index)["changed"], [])

    def test_a_documented_declaration_the_sync_leaves_out_is_not_reported(self) -> None:
        # A page of a declaration the sync no longer pages (one private by module visibility, say) keeps quiet.
        self.assertEqual(sync.apply_declarations([declaration("Ext.old", "old", "Old", "First.")], self.index)["changed"], [])
        self.assertEqual(sync.apply_declarations([], self.index)["changed"], [])


class UnindexedDeclarations(Vault):
    """A declaration the Lean index lacks (a name declared in two modules, which the index leaves unselected) gets
    no page: no identity is ever rebuilt from the source. It is reported for an editor; a page an earlier sync wrote
    for one is kept, and read through the index only when the index makes it unambiguous."""

    def library(self, text: str):
        source = self.tmp / "MathlibExt" / "Algebra" / "Wanted.lean"
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(text)
        taxonomy = {"subjects": {"Algebra": {}}, "placements": {}}
        return wiki.load_library("MathlibExt", SimpleNamespace(declarations={}), taxonomy)

    def test_unindexed_declarations_get_no_page_and_are_reported(self) -> None:
        cases = [
            # A root declaration and a namespaced one written alike.
            ("/-- Root. -/\ntheorem_wanted same : True\nnamespace B\n/-- B's. -/\ndef_wanted same : Nat\nend B\n", [2, 5]),
            # A quoted scope before two namespace-local declarations written alike.
            ("namespace «Auxiliary.Scope»\nend «Auxiliary.Scope»\nnamespace A\n/-- A's. -/\ntheorem_wanted\n  same : True\n"
             "end A\nnamespace B\n/-- B's. -/\ndef_wanted\n  same : Nat\nend B\n", [5, 10]),
        ]
        self.page("Algebra/README.md", "# Algebra\n")
        self.annotate([self.about("Algebra/README.md")])
        for text, lines in cases:
            with self.subTest(lines=lines):
                targets, summary = self.library(text)
                expected = [f"MathlibExt/Algebra/Wanted.lean:{line} same" for line in lines]
                self.assertEqual((targets, summary["unindexed"]), ([], expected))
                report = sync.apply_declarations(targets, SimpleNamespace(declarations={}), unindexed=summary["unindexed"])
                self.assertEqual((report["added"], report["unindexed"]), ([], sorted(expected)))

    def test_a_legacy_page_is_kept_and_reported_when_the_index_cannot_name_it(self) -> None:
        # Deleting the root `same` must not rebind its page to `B.same`: the index names neither, so the page waits.
        self.library("namespace B\n/-- B's. -/\ndef_wanted same : Nat\nend B\n")
        self.page("Algebra/README.md", "# Algebra\n\n- [Same](same.md)\n")
        self.page("Algebra/same.md", "# Same\n\nRoot.\n")
        row = self.about("Algebra/same.md", extensions={"org.atlas-wiki": {"module": "MathlibExt.Algebra.Wanted", "name": "same"}})
        self.annotate([self.about("Algebra/README.md"), row])
        index = SimpleNamespace(declarations={})
        self.assertIsNone(sync.annotation_key(row, index))
        report = sync.apply_declarations([], index)
        self.assertEqual((report["added"], report["gone"]), ([], []))
        self.assertEqual(report["unindexed"], ["Algebra/same.md (MathlibExt.Algebra.Wanted:same)"])
        self.assertTrue((wiki.ROADMAP / "Algebra" / "same.md").is_file())

    def test_a_legacy_page_named_by_the_index_keeps_its_page(self) -> None:
        self.library("namespace Deep.Space\n/-- A wish. -/\ntheorem_wanted wish : True\nend Deep.Space\n")
        self.page("Algebra/README.md", "# Algebra\n\n- [Wish](wish.md)\n")
        self.page("Algebra/wish.md", "# Wish\n\nA wish.\n")
        row = self.about("Algebra/wish.md", extensions={"org.atlas-wiki": {"module": "MathlibExt.Algebra.Wanted", "name": "wish"}})
        self.annotate([self.about("Algebra/README.md"), row])
        index = SimpleNamespace(declarations={"Deep.Space.wish": SimpleNamespace(
            path=Path("MathlibExt/Algebra/Wanted.lean"), line=3, keyword="theorem_wanted", name="Deep.Space.wish")})
        targets, _ = wiki.load_library("MathlibExt", index, {"subjects": {"Algebra": {}}, "placements": {}})
        for target in targets:
            target.path = wiki.ROADMAP / "Algebra" / f"{target.slug}.md"
        self.assertEqual(sync.annotation_key(row, index), "Deep.Space.wish")
        report = sync.apply_declarations(targets, index)
        self.assertEqual((report["added"], report["gone"], report["unindexed"]), ([], [], []))

    def test_a_legacy_page_without_a_compiled_row_claims_no_prerequisites(self) -> None:
        # A row an earlier sync wrote with a module and a name that the Lean index resolves stands for that
        # declaration as a Lean link does: an extraction without its row is refused (uncovered_owners) before the page
        # could claim to have no prerequisites, and lean-facts gives the build's row the declaration's Lean link.
        source = self.tmp / "MathlibExt" / "Algebra" / "Wanted.lean"
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text("/-- A wish. -/\ntheorem_wanted wish : True\n")
        self.page("Algebra/wish.md", "# Wish\n\nA wish.\n")
        legacy = {"org.atlas-wiki": {"module": "MathlibExt.Algebra.Wanted", "name": "wish"}}
        self.annotate([self.about("Algebra/wish.md", extensions=legacy)])
        index = SimpleNamespace(declarations={"MathlibExt.wish": SimpleNamespace(
            path=Path("MathlibExt/Algebra/Wanted.lean"), line=2, keyword="theorem_wanted")})
        empty = {"articles": {}, "missing_articles": {}}
        self.assertEqual(sync.uncovered_owners(sync.read_annotations(), empty, index), ["MathlibExt.wish"])
        counts, _ = sync.apply_lean_facts(index, {"MathlibExt.wish": {"module": "MathlibExt.Algebra.Wanted",
                                                                      "statement": [], "proof": []}})
        self.assertEqual(counts["articles"], 1)
        row = sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][0]
        self.assertEqual((row["object"], row["kind"], row["status"]),
                         ([{"location": {"declaration": "MathlibExt.wish"}, "role": "states"}], "theorem", "stated"))

    def test_no_identity_is_rebuilt_from_the_source(self) -> None:
        # Keys are Lean names from the index: nothing builds `module:name` keys, and a last name component is taken
        # only for titles and slugs, for reading an earlier sync's annotation through the index, and for
        # deprecated()'s no-line test path.
        sources = {name: (Path(wiki.__file__).parent / f"{name}.py").read_text() for name in ("generate_wiki", "sync_wiki")}
        lines = [line.strip() for text in sources.values() for line in text.splitlines()]
        self.assertEqual([line for line in lines if 'rsplit(":"' in line], [])
        # Only the report formats `module:name` or `path:line`, for a reader.
        self.assertEqual([line for line in lines if "}:{" in line], [
            'summary["unindexed"].append(f"{relative.as_posix()}:{number + 1} {written}")',
            'return f"{path.relative_to(wiki.ROOT).as_posix()}:{line}"',
            '+ [f"{subject_path(a).relative_to(wiki.ROADMAP)} ({a[\'extensions\'][OWN][\'module\']}:{a[\'extensions\'][OWN][\'name\']})"',
        ])
        for helper in ("declaration_identity", "split_identity", "fallback_metadata", "match_fallback", "qualified_name",
                       "source_declaration"):
            self.assertFalse(hasattr(wiki, helper) or hasattr(sync, helper), helper)
        self.assertEqual([line for line in lines if 'split(".")[-1]' in line], [
            'titles = [value if position == 0 else humanize(value.split(".")[-1]) if value else "" for value in values]',
            'short = written.split(".")[-1]',
            'and name.split(".")[-1] == own["name"].split(".")[-1]]',
            'short = target.names[0].split(".")[-1]',
            'if (match := wiki.V2_DECLARATION.match(row)) and match.group("name").split(".")[-1] == short]',
        ])


class ArticleIds(Vault):
    """`ids` gives each annotation without an id a fresh one and changes no other byte (What the tools own, in
    docs/BLUEPRINT.md)."""

    def links(self, name: str, text: str) -> Path:
        sync.LINKS.mkdir(parents=True, exist_ok=True)
        path = sync.LINKS / name
        path.write_bytes(text.encode("utf-8"))
        return path

    def row(self, page: str, **fields) -> str:
        return json.dumps(self.about(page, **fields), ensure_ascii=False)

    def test_each_row_without_an_id_gets_one_after_its_subject_and_keeps_every_other_byte(self) -> None:
        kept = self.row("Algebra/a.md", object=[{"location": {"declaration": "Ext.a"}}], id="af_000000000000000000000001")
        rows = [
            kept,
            self.row("Algebra/b.md", object=[{"location": {"declaration": "Ext.b"}}],
                     extensions={"org.atlas-wiki": {"from": "docstring"}}),
            self.row("Algebra/README.md", extensions={"org.autoform": {"navigation": "module"}}),
            self.row("Algebra/théorème.md", extensions={"org.atlas-wiki": {"held": {"declaration": "Ext.c", "reason": "false",
                                                                                     "issue": 1}}}),
        ]
        algebra = self.links("Algebra.jsonl", "\n".join(rows) + "\n")
        root = self.links("roadmap.jsonl", self.row("README.md") + "\n")
        without, problems = sync.apply_ids()
        self.assertEqual(problems, [])
        self.assertEqual(without, ["blueprint/links/Algebra.jsonl:2", "blueprint/links/Algebra.jsonl:3",
                                   "blueprint/links/Algebra.jsonl:4", "blueprint/links/roadmap.jsonl:1"])
        filled = algebra.read_bytes().decode("utf-8").split("\n")
        self.assertEqual((filled[0], filled[-1], len(filled)), (kept, "", len(rows) + 1))
        ids = ["af_000000000000000000000001"]
        for before, after in zip([*rows[1:], self.row("README.md")], [*filled[1:-1], root.read_text().rstrip("\n")]):
            added = re.search(r', "id": "(af_[0-9a-f]{24})"', after)
            # Without its id the row is the row it was, byte for byte; with it, it is the row declarations would write.
            self.assertEqual(after[:added.start()] + after[added.end():], before)
            annotation = json.loads(before)
            self.assertEqual(after, json.dumps({"subject": annotation.pop("subject"), "id": added.group(1), **annotation},
                                               ensure_ascii=False))
            ids.append(added.group(1))
        self.assertEqual(len(set(ids)), len(ids))
        # A second run finds no row without an id and changes nothing.
        written = {path: path.read_bytes() for path in (algebra, root)}
        self.assertEqual(sync.apply_ids(), ([], []))
        self.assertEqual({path: path.read_bytes() for path in (algebra, root)}, written)

    def test_a_row_written_another_way_keeps_its_bytes(self) -> None:
        rows = ['{"subject":[{"uri":"../roadmap/Algebra/a.md","type":"generic"}] , "object": [ ]}\r',
                '{ "subject" : [{"type": "generic", "uri": "../roadmap/Algebra/b.md"}]}\r']
        path = self.links("Algebra.jsonl", "\n".join(rows) + "\n")
        self.assertEqual(sync.apply_ids()[1], [])
        filled = path.read_bytes().decode("utf-8").split("\n")
        self.assertRegex(filled[0], r'\A\{"subject":\[\{"uri":"\.\./roadmap/Algebra/a\.md","type":"generic"\}\], "id": "af_[0-9a-f]{24}" , "object": \[ \]\}\r\Z')
        self.assertRegex(filled[1], r'\A\{ "subject" : \[\{"type": "generic", "uri": "\.\./roadmap/Algebra/b\.md"\}\], "id": "af_[0-9a-f]{24}"\}\r\Z')
        self.assertEqual(filled[2], "")

    def test_a_malformed_shared_or_repeated_id_or_a_row_it_cannot_read_stops_the_run(self) -> None:
        text = "\n".join([
            self.row("Algebra/a.md", id="af_000000000000000000000001"),
            self.row("Algebra/b.md", id="af_000000000000000000000001"),
            self.row("Algebra/c.md", id="af_1"),
            # JSON keeps the last of two ids, so the first, malformed, one would pass unseen.
            self.row("Algebra/d.md", id="broken")[:-1] + ', "id": "af_000000000000000000000003"}',
            "{not json",
            '{"object": []}',
            '{"subject": [{"type": "generic", "uri": "../roadmap/Algebra/g.md", "uri": "../roadmap/Algebra/h.md"}]}',
            '{"subject": [{"type": "generic", "uri": "../roadmap/Algebra/i.md"}], "weight": NaN}',
            self.row("Algebra/e.md"),
        ]) + "\n"
        path = self.links("Algebra.jsonl", text)
        other = self.links("Logic.jsonl", self.row("Logic/f.md") + "\n")
        self.assertEqual(sync.apply_ids(), (["blueprint/links/Algebra.jsonl:9", "blueprint/links/Logic.jsonl:1"], [
            "blueprint/links/Algebra.jsonl:2: its id af_000000000000000000000001 is the id of blueprint/links/Algebra.jsonl:1 too",
            'blueprint/links/Algebra.jsonl:3: its id "af_1" is not af_ and 24 hex digits',
            "blueprint/links/Algebra.jsonl:4: the row repeats id",
            "blueprint/links/Algebra.jsonl:5: the row is not a JSON object",
            "blueprint/links/Algebra.jsonl:6: the row has no subject",
            "blueprint/links/Algebra.jsonl:7: the row repeats uri",
            "blueprint/links/Algebra.jsonl:8: the row holds NaN, which JSON does not allow",
        ]))
        with redirect_stderr(io.StringIO()) as errors:
            self.assertEqual(sync.main(["ids"]), 1)
        self.assertIn("error: 7 rows to fix; the run wrote nothing", errors.getvalue())
        # Neither file is written, the one without a problem included.
        self.assertEqual(path.read_bytes().decode("utf-8"), text)
        self.assertEqual(other.read_bytes().decode("utf-8"), self.row("Logic/f.md") + "\n")

    def test_a_line_that_holds_only_a_form_feed_is_no_blank_line(self) -> None:
        text = self.row("Algebra/a.md") + "\n\x0c\n\n"
        path = self.links("Algebra.jsonl", text)
        other = self.links("Logic.jsonl", self.row("Logic/b.md") + "\n")
        self.assertEqual(sync.apply_ids(), (["blueprint/links/Algebra.jsonl:1", "blueprint/links/Logic.jsonl:1"],
                                            ["blueprint/links/Algebra.jsonl:2: the row is not a JSON object"]))
        self.assertEqual(path.read_bytes().decode("utf-8"), text)
        self.assertEqual(other.read_bytes().decode("utf-8"), self.row("Logic/b.md") + "\n")

    def test_a_links_file_that_is_a_symbolic_link_stops_the_run(self) -> None:
        outside = sync.LINKS.parents[1] / "outside.jsonl"
        outside.write_text(self.row("Logic/b.md") + "\n")
        sync.LINKS.mkdir(parents=True, exist_ok=True)
        (sync.LINKS / "Logic.jsonl").symlink_to(outside)
        text = self.row("Algebra/a.md") + "\n"
        path = self.links("Algebra.jsonl", text)
        self.assertEqual(sync.apply_ids(), (["blueprint/links/Algebra.jsonl:1"],
                                            ["blueprint/links/Logic.jsonl: it is not a regular file"]))
        self.assertEqual(path.read_text(), text)
        self.assertEqual(outside.read_text(), self.row("Logic/b.md") + "\n")

    def test_a_row_whose_subject_is_not_first_gets_the_id_right_after_its_subject(self) -> None:
        kept = '{"extensions": {}, "subject": [{"type": "generic", "uri": "../roadmap/Algebra/a.md"}], "id": "af_000000000000000000000001"}'
        row = '{"object": [{"location": {"declaration": "Ext.b"}}], "subject": [{"type": "generic", "uri": "../roadmap/Algebra/b.md"}]}'
        path = self.links("Algebra.jsonl", f"{kept}\n{row}\n")
        self.assertEqual(sync.apply_ids(), (["blueprint/links/Algebra.jsonl:2"], []))
        filled = path.read_bytes().decode("utf-8").split("\n")
        self.assertEqual(filled[0], kept)
        self.assertRegex(filled[1], r'\A' + re.escape(row[:-1]) + r', "id": "af_[0-9a-f]{24}"\}\Z')

    def test_a_check_writes_nothing(self) -> None:
        text = self.row("Algebra/a.md") + "\n"
        path = self.links("Algebra.jsonl", text)
        self.assertEqual(sync.apply_ids(write=False), (["blueprint/links/Algebra.jsonl:1"], []))
        self.assertEqual(path.read_bytes().decode("utf-8"), text)


class ScopedRows(Vault):
    """A scoped run adds each row where its page's path puts it among the others, and changes no other byte."""

    def test_a_row_goes_after_the_row_whose_page_comes_last_before_its_own(self) -> None:
        sync.LINKS.mkdir(parents=True)
        path = sync.LINKS / "Algebra.jsonl"
        rows = ['{"subject": [{"type": "generic", "uri": "../roadmap/Algebra/b.md"}], "id": "af_000000000000000000000002"}',
                # A row written another way, and one out of order, keep their bytes and their places.
                '{ "subject":[{"uri":"../roadmap/Algebra/d/README.md","type":"generic"}],"id":"af_000000000000000000000004"}',
                '{"subject": [{"type": "generic", "uri": "../roadmap/Algebra/a.md"}], "id": "af_000000000000000000000001"}']
        path.write_text("\n".join(rows) + "\n")
        new = [self.about(page, id=f"af_00000000000000000000000{number}")
               for number, page in ((5, "Algebra/c.md"), (6, "Algebra/d/e.md"), (7, "Algebra/0.md"), (8, "Algebra/d/f.md"))]
        sync.insert_rows(path, new)
        dumped = [json.dumps(row, ensure_ascii=False) for row in new]
        self.assertEqual(path.read_text().split("\n"),
                         # "0.md" comes before every page; "c.md" after "b.md" (not "a.md", which sorts lower but sits
                         # later); "d/e.md" and "d/f.md" after the folder page of d/.
                         [dumped[2], rows[0], dumped[0], rows[1], dumped[1], dumped[3], rows[2], ""])
        # A file that is not there yet holds the rows alone, in path order.
        sync.insert_rows(sync.LINKS / "Logic.jsonl", [self.about("Logic/b.md"), self.about("Logic/a.md")])
        self.assertEqual((sync.LINKS / "Logic.jsonl").read_text(),
                         "".join(json.dumps(self.about(f"Logic/{name}.md")) + "\n" for name in "ab"))

    def test_rows_added_to_a_file_of_carriage_returns_come_out_whole(self) -> None:
        # Each record keeps its own separator, and the added rows take the file's: taking them out gives back its
        # bytes, whatever its separators.
        sync.LINKS.mkdir(parents=True)
        path = sync.LINKS / "Algebra.jsonl"
        for separator, last in (("\r\n", "\r\n"), ("\r", "\r"), ("\n", ""), ("\r\n", "")):
            rows = [json.dumps(self.about(f"Algebra/{name}.md")) for name in "bd"]
            original = separator.join(rows) + last
            path.write_bytes(original.encode())
            added = [self.about(f"Algebra/{name}.md") for name in "ace"]
            sync.insert_rows(path, added)
            text = path.read_bytes().decode()
            lines, ends = sync.records(text)
            self.assertEqual([json.loads(line)["subject"][0]["uri"] for line in lines if line],
                             [f"../roadmap/Algebra/{name}.md" for name in "abcde"], repr(separator + last))
            for row in added:
                dumped = json.dumps(row)
                text = text.replace(dumped + separator, "", 1) if dumped + separator in text else text.replace(
                    separator + dumped, "", 1)
            self.assertEqual(text, original, repr(separator + last))

    def test_each_row_is_placed_by_its_page_once(self) -> None:
        sync.LINKS.mkdir(parents=True)
        path = sync.LINKS / "Algebra.jsonl"
        path.write_text("".join(json.dumps(self.about(f"Algebra/p{number:02d}.md")) + "\n" for number in range(20)))
        calls = []
        real = sync.page_name
        with patch.object(sync, "page_name", lambda row: calls.append(1) or real(row)):
            sync.insert_rows(path, [self.about(f"Algebra/q{number}.md") for number in range(3)])
        self.assertEqual(len(calls), 23)

    def test_a_file_without_a_last_line_end_keeps_its_bytes(self) -> None:
        sync.LINKS.mkdir(parents=True)
        path = sync.LINKS / "Algebra.jsonl"
        last = json.dumps(self.about("Algebra/b.md"))
        path.write_text(last)
        sync.insert_rows(path, [self.about("Algebra/a.md")])
        self.assertEqual(path.read_text(), json.dumps(self.about("Algebra/a.md")) + "\n" + last)


class ScopedLayout(Vault):
    def test_a_scoped_run_passes_over_generate_wikis_parts_in_the_folders_it_makes(self) -> None:
        # generate_wiki splits a field by what it lays out for every declaration, most of which a scoped run leaves out:
        # its "Part 2 of 10" would stand alone. A folder the wiki has keeps its parts either way.
        self.page("Algebra/README.md", "# Algebra\n")
        self.page("Algebra/split/README.md", "# Split\n\n## [Part 1 of 2](part-01/README.md)\n\n- [A](part-01/a.md)\n")
        self.page("Algebra/split/part-01/README.md", "# Part 1 of 2\n\n- [A](a.md)\n")
        new = wiki.ROADMAP / "Algebra" / "not-yet-classified" / "part-02" / "rings"
        folder, laid_out = sync.kept_layout(new, {})
        self.assertEqual((folder, laid_out[new / "README.md"]), (new, new / "README.md"))
        flat = wiki.ROADMAP / "Algebra" / "not-yet-classified" / "rings"
        folder, laid_out = sync.kept_layout(new, {}, flat=True)
        # Each folder the run makes takes generate_wiki's page of the folder it stands for.
        self.assertEqual((folder, laid_out[flat / "README.md"], laid_out[flat.parent / "README.md"]),
                         (flat, new / "README.md", flat.parent / "README.md"))
        self.assertNotIn(new.parent / "README.md", laid_out)
        kept = wiki.ROADMAP / "Algebra" / "split" / "part-03" / "fields"
        self.assertEqual(sync.kept_layout(kept, {}, flat=True)[0], wiki.ROADMAP / "Algebra" / "split" / "part-01" / "fields")

    def test_a_scoped_refresh_copies_only_the_parts_it_adds_to(self) -> None:
        text = ("# Groups\n\n## [Part 1 of 2](part-01/README.md)\n\n- [Old](part-01/old.md)\n\n"
                "## [Part 2 of 2](part-02/README.md)\n\n- [Late](part-02/late.md)\n")
        readme = self.page("Algebra/groups/README.md", text)
        self.page("Algebra/groups/part-01/README.md", "# Part 1 of 2\n\n- [Old](old.md)\n- [Older](older.md)\n")
        self.page("Algebra/groups/part-02/README.md", "# Part 2 of 2\n\n- [Late](late.md)\n- [New](new.md)\n")
        refreshed, unrefreshed, dropped = sync.with_part_lists(readme, text, {"part-02/README.md"})
        self.assertEqual(refreshed, text + "- [New](part-02/new.md)\n")
        self.assertEqual((unrefreshed, dropped), ([], []))
        self.assertIn("- [Older](part-01/older.md)\n", sync.with_part_lists(readme, text)[0])


class ScopedRun(unittest.TestCase):
    """declarations --base, the run a graph pull request or a graph-sync batch makes, on a repository of a few files
    with a git history: a base commit, then the pull request's changes in the working tree."""

    TAXONOMY = {"schema": wiki.TAXONOMY_SCHEMA, "regions": {"Algebra & Number Theory": ["Algebra"]},
                "subjects": {"Algebra": {"title": "Algebra", "description": "Operations.", "fields": [
                    {"slug": "groups", "title": "Groups", "description": "Groups.", "subfields": []}]}},
                "placements": {"MathlibExt/Algebra/Groups": {"to": "Algebra/groups", "title": "Group basics"}}}
    LAGRANGE = "The order of a subgroup divides the order of the group."
    GROUPS = ("namespace Ext\n\n/-- {lagrange} -/\ntheorem lagrange : True := trivial\n\n"
              "/-- A result that has no page yet. -/\ntheorem backlog : True := trivial\n\n{more}end Ext\n")
    PAGES = {"README.md": "# ATLAS roadmap\n\n## Algebra & Number Theory\n\n- [Algebra](Algebra/README.md)\n",
             "Algebra/README.md": "# Algebra\n\nOperations.\n\n- [Groups](groups/README.md)\n",
             "Algebra/groups/README.md": "# Groups\n\nGroups.\n\n- [Group basics](group-basics/README.md)\n",
             "Algebra/groups/group-basics/README.md": "# Group basics\n\n- [Lagrange](lagrange.md)\n",
             "Algebra/groups/group-basics/lagrange.md": f"# Lagrange\n\n{LAGRANGE}\n"}

    def setUp(self) -> None:
        self.root = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, self.root, True)
        vault = self.root / "blueprint"
        for one in (patch.object(wiki, "ROOT", self.root), patch.object(wiki, "VAULT", vault),
                    patch.object(wiki, "ROADMAP", vault / "roadmap"), patch.object(wiki, "PAGE_MAP", vault / "pages.json"),
                    patch.object(wiki, "SOURCES", vault / "sources"),
                    patch.object(wiki, "TAXONOMY", self.root / "scripts" / "taxonomy.json"),
                    patch.object(sync, "LINKS", vault / "links"),
                    patch.object(sync, "STATE", self.root / "scripts" / "wiki-sync.json")):
            one.start()
            self.addCleanup(one.stop)
        self.write("scripts/taxonomy.json", json.dumps(self.TAXONOMY))
        self.groups()
        rows = []
        for number, (page, text) in enumerate(self.PAGES.items(), 1):
            self.write(f"blueprint/roadmap/{page}", text)
            row = {"subject": [{"type": "generic", "uri": f"../roadmap/{page}"}], "id": f"af_{number:024x}"}
            if page.endswith("lagrange.md"):
                row["object"] = [{"location": {"declaration": "Ext.lagrange"}}]
            if page.endswith("group-basics/README.md"):
                row["extensions"] = {"org.autoform": {"navigation": "module"}}
            rows.append(row)
        self.write("blueprint/links/roadmap.jsonl", json.dumps(rows[0]) + "\n")
        self.write("blueprint/links/Algebra.jsonl", "".join(json.dumps(row) + "\n" for row in rows[1:]))
        # The defaults the repository's links folder has, which Autoform merges every row over.
        self.write("blueprint/links/_defaults.json", json.dumps(sync.DEFAULTS) + "\n")
        self.write("scripts/wiki-sync.json", json.dumps({"docstrings": {
            "Ext.backlog": sync.digest("A result that has no page yet."), "Ext.lagrange": sync.digest(self.LAGRANGE)}},
            indent=0) + "\n")
        self.git("init", "-q")
        self.git("add", "-A")
        self.git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", "base")
        self.base = self.git("rev-parse", "HEAD")

    def write(self, path: str, text: str) -> Path:
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
        return target

    def git(self, *args: str) -> str:
        return subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True, text=True).stdout.strip()

    def groups(self, lagrange: str = LAGRANGE, more: str = "", name: str = "lagrange") -> None:
        text = self.GROUPS.format(lagrange=lagrange, more=more)
        self.write("MathlibExt/Algebra/Groups.lean", text.replace("theorem lagrange", f"theorem {name}"))

    def run_sync(self, *flags: str) -> tuple[int, str, str, dict]:
        out, err = io.StringIO(), io.StringIO()
        report = self.root.parent / f"{self.root.name}-report.json"
        self.addCleanup(report.unlink, True)
        with redirect_stdout(out), redirect_stderr(err):
            status = sync.main(["declarations", "--base", self.base, *flags, "--report", str(report)])
        return status, out.getvalue(), err.getvalue(), json.loads(report.read_text())

    def tree(self) -> dict[str, bytes]:
        return {path.relative_to(self.root).as_posix(): path.read_bytes() for path in sorted(self.root.rglob("*"))
                if path.is_file() and ".git" not in path.relative_to(self.root).parts}

    def test_a_pull_request_writes_its_own_declarations_pages_and_nothing_else(self) -> None:
        # A new declaration in a module the wiki has, beside an older one with no page, which stays without, and a
        # new module the taxonomy does not place yet.
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.write("MathlibExt/Algebra/Rings.lean", "namespace Ext.Rings\n\n/-- Rings have units. -/\ntheorem units : True := "
                   "trivial\n\n/-- Fields are rings. -/\ntheorem fields : True := trivial\n\nend Ext.Rings\n")
        before = self.tree()
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 0, err)
        self.assertEqual(sorted(report["new"]), ["Ext.Rings.fields", "Ext.Rings.units", "Ext.fresh"])
        roadmap = self.root / "blueprint" / "roadmap"
        self.assertEqual((roadmap / "Algebra/groups/group-basics/fresh.md").read_text(), "# Fresh\n\nA new result.\n")
        self.assertEqual((roadmap / "Algebra/groups/group-basics/README.md").read_text(),
                         "# Group basics\n\n- [Lagrange](lagrange.md)\n- [Fresh](fresh.md)\n")
        self.assertEqual(list(roadmap.rglob("backlog.md")), [])
        self.assertEqual(sorted(path.name for path in (roadmap / "Algebra/not-yet-classified/rings").iterdir()),
                         ["README.md", "fields.md", "units.md"])
        self.assertIn("- [Not yet classified](not-yet-classified/README.md)", (roadmap / "Algebra/README.md").read_text())
        self.assertIn("- [Rings](rings/README.md)", (roadmap / "Algebra/not-yet-classified/README.md").read_text())
        # Only the new pages, the folder pages that list them, the links file and the baseline changed; no catalog.
        after = self.tree()
        self.assertEqual(sorted(path for path in after if before.get(path) != after[path]), sorted(report["written"]))
        self.assertEqual(sorted(report["written"]), [
            "blueprint/links/Algebra.jsonl", "blueprint/roadmap/Algebra/README.md",
            "blueprint/roadmap/Algebra/groups/group-basics/README.md", "blueprint/roadmap/Algebra/groups/group-basics/fresh.md",
            "blueprint/roadmap/Algebra/not-yet-classified/README.md",
            "blueprint/roadmap/Algebra/not-yet-classified/rings/README.md",
            "blueprint/roadmap/Algebra/not-yet-classified/rings/fields.md",
            "blueprint/roadmap/Algebra/not-yet-classified/rings/units.md", "scripts/wiki-sync.json"])
        # The rows the base had keep their bytes and places; each new one sits in path order with a fresh id.
        old = before["blueprint/links/Algebra.jsonl"].decode().splitlines()
        new = after["blueprint/links/Algebra.jsonl"].decode().splitlines()
        self.assertEqual([row for row in new if row in old], old)
        rows = [json.loads(row) for row in new]
        self.assertEqual(rows, sorted(rows, key=sync.row_order))
        ids = [json.loads(row)["id"] for row in new]
        self.assertEqual(len(set(ids)), len(ids))
        self.assertTrue(all(sync.ARTICLE_ID.fullmatch(article_id) for article_id in ids))
        state = json.loads(after["scripts/wiki-sync.json"])["docstrings"]
        self.assertEqual(sorted(state), ["Ext.Rings.fields", "Ext.Rings.units", "Ext.backlog", "Ext.fresh", "Ext.lagrange"])
        self.assertEqual(state["Ext.fresh"], sync.digest("A new result."))
        # A second run writes nothing, and the check finds the tree in step, its wiki changes the sync's own.
        status, out, err, report = self.run_sync()
        self.assertEqual((status, report["missing"], report["digests"]), (0, [], {}))
        self.assertIn("Nothing to write.", out)
        self.assertEqual(self.tree(), after)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "sync"), out + err)
        self.assertEqual(self.tree(), after)

    def test_the_check_names_what_a_lean_change_still_needs_and_the_command_that_writes_it(self) -> None:
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qam", "head")
        before = self.tree()
        status, out, err, report = self.run_sync("--check")
        self.assertEqual(status, 1)
        self.assertEqual((report["in_step"], report["missing"], report["wiki_changes"]), (False, ["Ext.fresh"], "none"))
        self.assertEqual(report["digests"], {"Ext.fresh": sync.digest("A new result.")})
        self.assertIn(f"  python3 scripts/sync_wiki.py declarations --base {self.base}\n", out)
        self.assertEqual(self.tree(), before)

    def test_a_docstring_edit_rewrites_its_digest_and_names_its_page(self) -> None:
        self.groups(lagrange="The order of a subgroup divides the order of a finite group.")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["missing"]), (1, []))
        self.assertEqual(report["changed"], ["Ext.lagrange (Algebra/groups/group-basics/lagrange.md)"])
        status, out, err, report = self.run_sync()
        self.assertEqual((status, report["written"]), (0, ["scripts/wiki-sync.json"]))
        self.assertEqual(json.loads((self.root / "scripts/wiki-sync.json").read_text())["docstrings"]["Ext.lagrange"],
                         sync.digest("The order of a subgroup divides the order of a finite group."))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"]), (0, "sync"))

    def test_a_renamed_declaration_stops_the_run_until_its_link_follows(self) -> None:
        self.groups(name="lagrange_divides")
        before = self.tree()
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 1)
        self.assertIn("error: blueprint/links/Algebra.jsonl:4 (Algebra/groups/group-basics/lagrange.md) links Ext.lagrange, "
                      "which the Lean no longer has", err)
        self.assertIn("The run wrote nothing", err)
        self.assertEqual(self.tree(), before)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["missing"], len(report["errors"])), (1, ["Ext.lagrange_divides"], 1))
        # The link follows the declaration and keeps its id: the page stays, and the new name needs no other.
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text().replace('"Ext.lagrange"', '"Ext.lagrange_divides"'))
        status, out, err, report = self.run_sync()
        self.assertEqual((status, report["missing"], report["written"]), (0, [], ["scripts/wiki-sync.json"]))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "other"))
        # The sync never relinks a row: on the base's wiki it stops at the stale link instead.
        self.assertEqual(report["differences"], [
            "the sync stops on the base's wiki: blueprint/links/Algebra.jsonl:4 (Algebra/groups/group-basics/lagrange.md) "
            "links Ext.lagrange, which the Lean no longer has: relink the row to the declaration's successor and keep its "
            "article id, or remove the link and keep the page as a planned page"])

    def test_a_held_marker_the_changes_leave_unusable_stops_the_run(self) -> None:
        links = self.root / "blueprint/links/Algebra.jsonl"
        self.write("blueprint/roadmap/Algebra/groups/group-basics/backlog.md", "# Backlog\n\nAs the source states it.\n")
        held = {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/backlog.md"}],
                "id": "af_" + "f" * 24, "extensions": {"org.atlas-wiki": {"held": {"declaration": "Ext.backlog",
                                                                                     "reason": "vacuous", "issue": 1}}}}
        links.write_text(links.read_text() + json.dumps(held) + "\n")
        self.git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qam", "held")
        self.base = self.git("rev-parse", "HEAD")
        self.write("MathlibExt/Algebra/Groups.lean", self.GROUPS.format(lagrange=self.LAGRANGE, more="").replace(
            "/-- A result that has no page yet. -/\ntheorem backlog : True := trivial\n\n", ""))
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 1)
        self.assertIn("error: Algebra/groups/group-basics/backlog.md: it holds Ext.backlog back, which the Lean index does "
                      "not resolve: fix the held marker", err)

    def list_duplicates(self, value: object = None, line: int = 4) -> None:
        """Have the row on *line* of Algebra.jsonl (the Lagrange page's by default) list *value* under `duplicates`, or
        list nothing; the other rows keep their bytes."""
        links = self.root / "blueprint/links/Algebra.jsonl"
        lines = links.read_text().splitlines()
        row = json.loads(lines[line - 1])
        extensions = row.setdefault("extensions", {})
        if value is None:
            extensions.pop("org.atlas-wiki", None)
        else:
            extensions["org.atlas-wiki"] = {"duplicates": value}
        if not extensions:
            del row["extensions"]
        lines[line - 1] = json.dumps(row)
        links.write_text("".join(f"{text}\n" for text in lines))

    def commit_base(self, message: str) -> None:
        self.git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qam", message)
        self.base = self.git("rev-parse", "HEAD")

    def test_a_declaration_a_page_lists_as_a_duplicate_gets_no_page(self) -> None:
        # The pull request adds Ext.lagrange_again, which states Lagrange's theorem again: unlisted, it needs a page;
        # listed under the Lagrange page's duplicates, it needs none, and only its baseline entry is written.
        self.groups(more="/-- Lagrange's theorem, stated again. -/\ntheorem lagrange_again : True := trivial\n\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["missing"], report["duplicates"]), (1, ["Ext.lagrange_again"], []))
        self.list_duplicates(["Ext.lagrange_again"])
        before = self.tree()
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 0, err)
        self.assertEqual((report["missing"], report["duplicates"], report["written"]),
                         ([], ["Ext.lagrange_again"], ["scripts/wiki-sync.json"]))
        self.assertIn("Of them, those a page's row lists as duplicates, so with no page: 1\n  Ext.lagrange_again\n",
                      out)
        self.assertEqual([path for path, text in self.tree().items() if before.get(path) != text],
                         ["scripts/wiki-sync.json"])
        # In step; the list on a row the base has is an editor's change, not the sync's.
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "other"), out + err)

    def test_a_duplicate_the_lean_drops_stops_the_run_until_its_entry_goes(self) -> None:
        self.list_duplicates(["Ext.backlog"])
        self.commit_base("listed")
        self.write("MathlibExt/Algebra/Groups.lean", self.GROUPS.format(lagrange=self.LAGRANGE, more="").replace(
            "/-- A result that has no page yet. -/\ntheorem backlog : True := trivial\n\n", ""))
        before = self.tree()
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 1)
        self.assertIn("error: blueprint/links/Algebra.jsonl:4 (Algebra/groups/group-basics/lagrange.md) lists "
                      "Ext.backlog as a duplicate, which the Lean no longer has: drop the entry from `duplicates`, "
                      "keeping the row's article id and its credit", err)
        self.assertIn("The run wrote nothing", err)
        self.assertEqual(self.tree(), before)
        # Its entry gone, the row keeps its id and its credit, and the run drops the declaration's baseline entry.
        self.list_duplicates(None)
        status, out, err, report = self.run_sync()
        self.assertEqual((status, report["written"]), (0, ["scripts/wiki-sync.json"]), err)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (0, True), out + err)

    def test_a_duplicates_list_the_changes_leave_unusable_stops_the_run(self) -> None:
        # The pull request lists Ext.backlog on a folder page's row, which credits nothing.
        self.list_duplicates(["Ext.backlog"], line=3)
        before = self.tree()
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 1)
        self.assertIn("error: Algebra/groups/group-basics/README.md: it lists duplicates but credits no declaration of "
                      "this project by a Lean link of its own: fix the duplicates list", err)
        self.assertEqual(self.tree(), before)

    def test_a_duplicates_list_the_base_had_unusable_stops_no_run(self) -> None:
        # The base lists Ext.backlog twice. A pull request that leaves the list as it is, as one that leaves a held
        # marker unusable, is judged on its own changes: the run writes the page and the docstring digests they need,
        # and the check finds its wiki changes the sync's.
        self.list_duplicates(["Ext.backlog", "Ext.backlog"])
        self.commit_base("listed twice")
        self.groups(lagrange="The order of a subgroup divides the order of a finite group.",
                    more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        status, out, err, report = self.run_sync()
        self.assertEqual((status, report["errors"]), (0, []), err)
        self.assertIn("blueprint/roadmap/Algebra/groups/group-basics/fresh.md", report["written"])
        self.assertIn("scripts/wiki-sync.json", report["written"])
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "sync"), out + err)

    def add_page(self, name: str, **fields) -> None:
        """Add the page *name*.md beside Lagrange's, listed on its folder page, with a row of *fields*."""
        folder = "blueprint/roadmap/Algebra/groups/group-basics"
        self.write(f"{folder}/{name}.md", f"# {name.title()}\n\nA statement.\n")
        readme = self.root / folder / "README.md"
        readme.write_text(readme.read_text() + f"- [{name.title()}]({name}.md)\n")
        links = self.root / "blueprint/links/Algebra.jsonl"
        row = {"subject": [{"type": "generic", "uri": f"../roadmap/Algebra/groups/group-basics/{name}.md"}],
               "id": "af_" + hashlib.sha256(name.encode()).hexdigest()[:24], **fields}
        links.write_text(links.read_text() + json.dumps(row) + "\n")

    def test_a_duplicate_another_row_links_stops_the_run(self) -> None:
        # The base's Other page uses Ext.backlog, by a reference: listing it as Lagrange's duplicate is the changes'.
        self.add_page("other", object=[{"location": {"declaration": "Ext.lagrange"}, "role": "uses"},
                                       {"location": {"declaration": "Ext.backlog"}, "role": "uses"}])
        self.base = self.commit("a reference to Ext.backlog")
        self.list_duplicates(["Ext.backlog"])
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (1, False))
        self.assertIn("error: Algebra/groups/group-basics/lagrange.md: it lists Ext.backlog as a duplicate, which "
                      "Algebra/groups/group-basics/other.md links: fix the duplicates list", err)

    def test_a_name_the_lean_lacks_is_the_changes_once_they_list_it_as_a_duplicate(self) -> None:
        # The base's Lagrange row uses Ext.gone, which the Lean lacks: that stale reference is the base's. Moving the
        # name from the reference into the row's duplicates makes a stale entry of the changes' own.
        links = self.root / "blueprint/links/Algebra.jsonl"
        lagrange, gone = ('"object": [{"location": {"declaration": "Ext.lagrange"}}]',
                          ', {"location": {"declaration": "Ext.gone"}, "role": "uses"}')
        links.write_text(links.read_text().replace(lagrange, lagrange[:-1] + gone + "]"))
        self.commit_base("a stale reference")
        links.write_text(links.read_text().replace(gone, ""))
        self.list_duplicates(["Ext.gone"])
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (1, False))
        self.assertIn("error: blueprint/links/Algebra.jsonl:4 (Algebra/groups/group-basics/lagrange.md) lists Ext.gone "
                      "as a duplicate, which the Lean no longer has: drop the entry from `duplicates`", err)
        # A stale entry the base already had stays the base's: an unrelated change is written.
        self.commit_base("a stale entry")
        self.groups(lagrange="The order of a subgroup divides the order of a finite group.")
        status, out, err, report = self.run_sync()
        self.assertEqual((status, report["errors"], report["written"]), (0, [], ["scripts/wiki-sync.json"]), err)

    def test_rows_that_list_one_duplicate_are_judged_by_their_pairs(self) -> None:
        # On the base, the Lagrange, Other and Third rows all list Ext.backlog: one problem for each pair of them.
        for name in ("other", "third"):
            self.add_page(name, object=[{"location": {"declaration": f"Ext.{name}"}}],
                          extensions={"org.atlas-wiki": {"duplicates": ["Ext.backlog"]}})
        self.groups(more="theorem other : True := trivial\n\ntheorem third : True := trivial\n\n")
        self.list_duplicates(["Ext.backlog"])
        self.base = self.commit("three rows list Ext.backlog")
        # Taking the first claim away, then putting the rows in another order, makes no new pair.
        self.list_duplicates(None)
        links = self.root / "blueprint/links/Algebra.jsonl"
        for edit in (lambda text: text, lambda text: "".join(f"{line}\n" for line in reversed(text.splitlines()))):
            links.write_text(edit(links.read_text()))
            status, out, err, report = self.run_sync("--check")
            self.assertEqual((status, report["errors"]), (0, []), out + err)
        # A new row that lists it makes two.
        self.groups(more="theorem other : True := trivial\n\ntheorem third : True := trivial\n\n"
                         "theorem zeta : True := trivial\n\n")
        self.add_page("zeta", object=[{"location": {"declaration": "Ext.zeta"}}],
                      extensions={"org.atlas-wiki": {"duplicates": ["Ext.backlog"]}})
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (1, [
            f"Algebra/groups/group-basics/zeta.md: it lists Ext.backlog as a duplicate, as "
            f"Algebra/groups/group-basics/{other}.md does: fix the duplicates list" for other in ("other", "third")]))

    def test_a_duplicate_listed_on_a_row_whose_declaration_is_gone_is_the_changes(self) -> None:
        # On the base, Lagrange's row credits Ext.gone, which the Lean lacks: that stale link is the base's. The pull
        # request adds Ext.fresh and lists it on that row, an association that counts for no page: the run writes
        # nothing, and the check is red. Once the base has the association, a pull request that leaves it is judged
        # on its own changes.
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text().replace('{"declaration": "Ext.lagrange"}', '{"declaration": "Ext.gone"}'))
        self.commit_base("a stale credit")
        self.groups(more="/-- Lagrange's theorem, stated again. -/\ntheorem fresh : True := trivial\n\n")
        self.list_duplicates(["Ext.fresh"])
        message = ("error: blueprint/links/Algebra.jsonl:4 (Algebra/groups/group-basics/lagrange.md) lists Ext.fresh "
                   "as a duplicate of Ext.gone, which the Lean no longer has: relink the row to the declaration's "
                   "successor, keeping its article id, or drop the entry from `duplicates`")
        before = self.tree()
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 1)
        self.assertIn(message, err)
        self.assertEqual(self.tree(), before)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (1, False))
        self.assertIn(message, err)
        self.commit_base("the association on the base")
        self.groups(lagrange="The order of a subgroup divides the order of a finite group.",
                    more="/-- Lagrange's theorem, stated again. -/\ntheorem fresh : True := trivial\n\n")
        status, out, err, report = self.run_sync()
        self.assertEqual((status, report["errors"], report["written"]), (0, [], ["scripts/wiki-sync.json"]), err)

    def test_restoring_one_end_of_a_stale_association_is_no_new_problem(self) -> None:
        # On the base, Lagrange's row credits Ext.review_c and lists Ext.review_t, and the Lean declares neither: both
        # ends of the association are stale, the base's. A pull request that brings back one of them, the row as it
        # was, leaves the other as stale as it was, and both runs pass; one that brings back neither, and changes the
        # row's credit, makes an association of its own, which stops them.
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text().replace('{"declaration": "Ext.lagrange"}',
                                                   '{"declaration": "Ext.review_c"}'))
        self.list_duplicates(["Ext.review_t"])
        self.commit_base("both ends stale")
        row = links.read_bytes()
        for restored in ("review_t", "review_c"):
            with self.subTest(restored=restored):
                self.groups(more=f"theorem {restored} : True := trivial\n\n")
                for flags in (("--check",), ()):
                    status, out, err, report = self.run_sync(*flags)
                    self.assertEqual((status, report["errors"]), (0, []), out + err)
                self.assertEqual(links.read_bytes(), row)
                self.git("checkout", "-q", "--", ".")
        # Each end of the retargeted association is the changes', the duplicate's as the declaration's.
        links.write_text(links.read_text().replace('"Ext.review_c"', '"Ext.review_d"'))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual(status, 1)
        self.assertIn("lists Ext.review_t as a duplicate, which the Lean no longer has", err)
        self.assertIn("lists Ext.review_t as a duplicate of Ext.review_d, which the Lean no longer has", err)

    def test_a_page_listing_a_duplicate_moves_without_a_new_conflict(self) -> None:
        # On the base, Lagrange's and Other's rows both list Ext.backlog. Moving Other's page, its row keeping its id,
        # its credit and its list, makes no new conflict: the two rows still are the two that list it.
        self.groups(more="theorem other : True := trivial\n\n")
        self.list_duplicates(["Ext.backlog"])
        self.add_page("other", object=[{"location": {"declaration": "Ext.other"}}],
                      extensions={"org.atlas-wiki": {"duplicates": ["Ext.backlog"]}})
        self.base = self.commit("two rows list Ext.backlog")
        folder = self.root / "blueprint/roadmap/Algebra/groups/group-basics"
        (folder / "other.md").rename(folder / "moved.md")
        (folder / "README.md").write_text((folder / "README.md").read_text().replace("(other.md)", "(moved.md)"))
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text().replace("group-basics/other.md", "group-basics/moved.md"))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (0, []), out + err)

    def test_a_second_row_of_a_page_that_lists_a_duplicate_is_a_new_conflict(self) -> None:
        # On the base, Lagrange's page has a second row, crediting Ext.second, and only the first lists Ext.backlog. The
        # second row listing it too is a new conflict of the two rows, on one page.
        self.groups(more="theorem second : True := trivial\n\n")
        self.list_duplicates(["Ext.backlog"])
        links = self.root / "blueprint/links/Algebra.jsonl"
        second = {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/lagrange.md"}],
                  "id": "af_" + "e" * 24, "object": [{"location": {"declaration": "Ext.second"}}]}
        links.write_text(links.read_text() + json.dumps(second) + "\n")
        self.base = self.commit("a second row for Lagrange's page")
        second["extensions"] = {"org.atlas-wiki": {"duplicates": ["Ext.backlog"]}}
        lines = links.read_text().splitlines()
        links.write_text("".join(f"{line}\n" for line in lines[:-1]) + json.dumps(second) + "\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (1, [
            "Algebra/groups/group-basics/lagrange.md: it lists Ext.backlog as a duplicate, as "
            "Algebra/groups/group-basics/lagrange.md does: fix the duplicates list"]), out + err)

    def test_the_page_listing_an_own_duplicate_must_be_a_listed_page(self) -> None:
        # The pull request adds Ext.fresh, a restatement of Lagrange's theorem, and lists it on Lagrange's row, whose
        # page then stands for it: the page must stay a page, listed on its folder page.
        self.groups(more="/-- Lagrange's theorem, stated again. -/\ntheorem fresh : True := trivial\n\n")
        self.list_duplicates(["Ext.fresh"])
        page = self.root / "blueprint/roadmap/Algebra/groups/group-basics/lagrange.md"
        text = page.read_text()
        page.unlink()
        for flags in ((), ("--check",)):
            status, out, err, report = self.run_sync(*flags)
            self.assertEqual((status, report.get("in_step", False)), (1, False))
            self.assertIn("error: blueprint/roadmap/Algebra/groups/group-basics/lagrange.md, which the row listing "
                          "Ext.fresh as a duplicate names, is not a page: restore it there, keeping the row and its "
                          "article id, or drop the entry from the row's `duplicates`", err)
        page.write_text(text)
        readme = page.parent / "README.md"
        readme.write_text(readme.read_text().replace("- [Lagrange](lagrange.md)\n", ""))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (1, False))
        self.assertIn("error: Algebra/groups/group-basics/lagrange.md, the page listing Ext.fresh as a duplicate, is "
                      "listed on no folder page: list it on Algebra/groups/group-basics/README.md", err)

    def test_a_write_with_nothing_changed_writes_nothing(self) -> None:
        status, out, err, report = self.run_sync()
        self.assertEqual((status, "Nothing to write." in out, report.get("written")), (0, True, None))

    def test_documentation_alone_is_checked_without_reading_the_lean(self) -> None:
        self.write("README.md", "Documentation.\n")
        with patch.object(wiki, "generate", side_effect=AssertionError("read the Lean")):
            status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "none"))

    def test_hand_edits_and_rewritten_ids_are_not_the_syncs(self) -> None:
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        page = self.root / "blueprint/roadmap/Algebra/groups/group-basics/fresh.md"
        page.write_text(page.read_text() + "\nMore prose.\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"], report["differences"]), (0, "other", [
            "blueprint/roadmap/Algebra/groups/group-basics/fresh.md: the changes write it otherwise than the sync"]))
        page.write_text("# Fresh\n\nA new result.\n")
        self.assertEqual(self.run_sync("--check")[3]["wiki_changes"], "sync")
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text().replace("af_" + "0" * 23 + "2", "af_" + "e" * 24))
        self.assertEqual(self.run_sync("--check")[3]["differences"],
                         ["blueprint/links/Algebra.jsonl: the changes write it otherwise than the sync"])
        links.write_text(links.read_text().replace("af_" + "e" * 24, "af_" + "0" * 23 + "2"))
        (self.root / "blueprint/roadmap/Algebra/groups/group-basics/lagrange.md").unlink()
        self.assertEqual(self.run_sync("--check")[3]["differences"],
                         ["blueprint/roadmap/Algebra/groups/group-basics/lagrange.md: the changes delete it"])

    def test_graph_files_the_sync_never_writes_are_not_its(self) -> None:
        # Each graph file outside the pages, the links and the baseline makes the wiki changes not the sync's, with
        # or without a Lean change.
        for path in ("scripts/taxonomy.json", "scripts/card-moves.jsonl", "scripts/mathgraph-map.jsonl",
                     "blueprint/atlas.json"):
            target = self.root / path
            kept = target.read_text() if target.is_file() else None
            target.write_text((kept or "") + "\n")
            status, out, err, report = self.run_sync("--check")
            self.assertEqual((status, report["wiki_changes"], report["differences"]), (0, "other", [
                f"{path}: the sync writes nothing when no Lean changes"]), path)
            self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
            status, out, err, report = self.run_sync("--check")
            self.assertEqual((report["wiki_changes"], report["differences"]), ("other", [
                f"{path}: the sync never writes it"]), path)
            self.groups()
            if kept is None:
                target.unlink()
            else:
                target.write_text(kept)

    def commit(self, message: str) -> str:
        self.git("add", "-A")
        self.git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", message)
        return self.git("rev-parse", "HEAD")

    RINGS = ("namespace Ext.Rings\n\n/-- Rings have units. -/\ntheorem units : True := trivial\n\n/-- Fields are rings. -/\n"
             "theorem fields : True := trivial\n\nend Ext.Rings\n")

    def test_a_folder_its_parent_cannot_list_keeps_the_check_red(self) -> None:
        # The parent page has a code fence, so the sync lists nothing on it: the new folder is an error until an
        # editor lists it, on every run and in the check, whose wiki changes are then not the sync's alone.
        self.write("blueprint/roadmap/Algebra/README.md",
                   "# Algebra\n\nOperations.\n\n```\nnot a list\n```\n\n- [Groups](groups/README.md)\n")
        self.base = self.commit("a parent page with a code fence")
        self.write("MathlibExt/Algebra/Rings.lean", self.RINGS)
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 1)
        self.assertIn("Algebra/not-yet-classified is listed on no folder page", err)
        for flags in ((), ("--check",)):
            status, out, err, report = self.run_sync(*flags)
            self.assertEqual((status, report["missing"]), (1, []), flags)
            self.assertEqual(report["errors"], ["Algebra/not-yet-classified, a folder the changes add, is listed on no "
                                                "folder page: list it on Algebra/README.md"])
        self.assertEqual((report["in_step"], report["wiki_changes"]), (False, "other"))
        self.assertIn("listed on no folder page", report["differences"][0])

    def test_a_row_whose_page_is_missing_is_not_a_page(self) -> None:
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        (self.root / "blueprint/roadmap/Algebra/groups/group-basics/fresh.md").unlink()
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["missing"]), (1, False, []))
        self.assertEqual(report["errors"], ["blueprint/roadmap/Algebra/groups/group-basics/fresh.md, which the row of "
                                            "Ext.fresh names, is not a page: restore it, or remove the row and run the "
                                            "sync again"])

    def test_a_link_or_an_executable_bit_is_not_the_syncs(self) -> None:
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        page = self.root / "blueprint/roadmap/Algebra/groups/group-basics/fresh.md"
        page.chmod(0o755)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"], report["differences"]), (0, "other", [
            "blueprint/roadmap/Algebra/groups/group-basics/fresh.md: the changes write it otherwise than the sync"]))
        page.chmod(0o644)
        elsewhere = self.root / "fresh.md"
        page.rename(elsewhere)
        page.symlink_to(elsewhere)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"]), (1, "other"))
        self.assertIn("blueprint/roadmap/Algebra/groups/group-basics/fresh.md: the sync writes no link or other kind of "
                      "file", report["differences"])

    def test_the_check_replays_what_the_writer_does_and_no_more(self) -> None:
        # A Lean change that needs nothing writes nothing, the baseline included, so a hand reformat of the baseline
        # is not the sync's.
        state = self.root / "scripts/wiki-sync.json"
        canonical = state.read_text()
        state.write_text(json.dumps(json.loads(canonical), indent=2) + "\n")
        self.base = self.commit("an indented baseline")
        self.write("MathlibExt/Algebra/Groups.lean", self.GROUPS.format(lagrange=self.LAGRANGE, more="") + "-- note\n")
        status, out, err, report = self.run_sync()
        self.assertEqual((status, "Nothing to write." in out), (0, True))
        state.write_text(canonical)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"]), (0, "other"))
        self.assertEqual(report["differences"], ["scripts/wiki-sync.json: the changes write it otherwise than the sync"])

    def test_a_baseline_the_base_lacks_is_made(self) -> None:
        self.git("rm", "-q", "scripts/wiki-sync.json")
        self.base = self.commit("no baseline yet")
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        self.assertEqual(json.loads((self.root / "scripts/wiki-sync.json").read_text()),
                         {"docstrings": {"Ext.fresh": sync.digest("A new result.")}})
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"]), (0, "sync"))

    def test_the_baseline_follows_each_transition_the_changes_make(self) -> None:
        # An undeprecated declaration with no entry gets one with its page; a declaration the changes delete loses
        # the entry its unlinked page kept, though the base had it undocumented; and a docstring edit names its page
        # for a reader even once its digest is written.
        groups = self.root / "MathlibExt/Algebra/Groups.lean"
        groups.write_text(groups.read_text().replace("theorem backlog", "@[deprecated lagrange]\ntheorem backlog")
                          .replace("end Ext", "theorem undocumented : True := trivial\n\nend Ext"))
        self.write("blueprint/roadmap/Algebra/groups/group-basics/undocumented.md", "# Undocumented\n\nKept.\n")
        links = self.root / "blueprint/links/Algebra.jsonl"
        row = {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/undocumented.md"}],
               "id": "af_" + "c" * 24, "object": [{"location": {"declaration": "Ext.undocumented"}}]}
        links.write_text(links.read_text() + json.dumps(row) + "\n")
        state = self.root / "scripts/wiki-sync.json"
        digests = json.loads(state.read_text())["docstrings"]
        digests.pop("Ext.backlog")
        digests["Ext.undocumented"] = sync.digest("A docstring it lost.")
        state.write_text(json.dumps({"docstrings": dict(sorted(digests.items()))}, indent=0) + "\n")
        self.base = self.commit("an undocumented page, a deprecated declaration")
        groups.write_text(self.GROUPS.format(lagrange="The order of a subgroup divides the group's.", more=""))
        links.write_text(links.read_text().replace(', "object": [{"location": {"declaration": "Ext.undocumented"}}]', ""))
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 0, err)
        self.assertEqual(report["new"], {"Ext.backlog": "MathlibExt/Algebra/Groups.lean"})
        self.assertEqual(report["digests"], {"Ext.backlog": sync.digest("A result that has no page yet."),
                                             "Ext.lagrange": sync.digest("The order of a subgroup divides the group's."),
                                             "Ext.undocumented": None})
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["digests"]), (0, {}))
        self.assertEqual(report["changed"], ["Ext.lagrange (Algebra/groups/group-basics/lagrange.md)"])

    def test_a_new_folder_joins_its_neighbours_through_generate_wikis_parts(self) -> None:
        # generate_wiki splits the field by its 21 topics without pages, so it lists the subfield under a part; the
        # wiki's subfield is flat, and a new topic still goes ahead of the one it lists after it, not at the end.
        taxonomy = json.loads(json.dumps(self.TAXONOMY))
        taxonomy["subjects"]["Algebra"]["fields"][0]["subfields"] = [
            {"slug": "middle", "title": "Middle", "description": "Middle."}]
        for number in range(21):
            taxonomy["placements"][f"MathlibExt/Algebra/Single{number:02d}"] = {"to": "Algebra/groups",
                                                                               "title": f"Single {number:02d}"}
            self.write(f"MathlibExt/Algebra/Single{number:02d}.lean",
                       f"namespace Ext.Single{number:02d}\n\n/-- A result. -/\ntheorem one : True := trivial\n\nend "
                       f"Ext.Single{number:02d}\n")
        for name in ("Zulu", "Beta"):
            taxonomy["placements"][f"MathlibExt/Algebra/{name}"] = {"to": "Algebra/groups/middle", "title": name}
        self.write("scripts/taxonomy.json", json.dumps(taxonomy))
        zulu = ("namespace Ext.Zulu\n\n/-- One result. -/\ntheorem one : True := trivial\n\n/-- Another result. -/\n"
                "theorem two : True := trivial\n\nend Ext.Zulu\n")
        self.write("MathlibExt/Algebra/Zulu.lean", zulu)
        self.write("blueprint/roadmap/Algebra/groups/README.md", "# Groups\n\nGroups.\n\n- [Middle](middle/README.md)\n"
                   "- [Group basics](group-basics/README.md)\n")
        self.write("blueprint/roadmap/Algebra/groups/middle/README.md", "# Middle\n\nMiddle.\n\n- [Zulu](zulu/README.md)\n")
        self.write("blueprint/roadmap/Algebra/groups/middle/zulu/README.md", "# Zulu\n\n- [One](one.md)\n")
        self.write("blueprint/roadmap/Algebra/groups/middle/zulu/one.md", "# One\n\nOne result.\n")
        links = self.root / "blueprint/links/Algebra.jsonl"
        rows = [{"subject": [{"type": "generic", "uri": f"../roadmap/Algebra/groups/middle/{page}"}],
                 "id": f"af_{number:024x}"} for number, page in enumerate(("README.md", "zulu/README.md", "zulu/one.md"), 90)]
        rows[2]["object"] = [{"location": {"declaration": "Ext.Zulu.one"}}]
        links.write_text(links.read_text() + "".join(json.dumps(row) + "\n" for row in rows))
        self.base = self.commit("a flat subfield of a field generate_wiki splits")
        self.write("MathlibExt/Algebra/Beta.lean", zulu.replace("Zulu", "Beta"))
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 0, err)
        self.assertEqual((self.root / "blueprint/roadmap/Algebra/groups/middle/README.md").read_text(),
                         "# Middle\n\nMiddle.\n\n- [Beta](beta/README.md)\n- [Zulu](zulu/README.md)\n")
        self.assertFalse(any("part-" in path for path in report["written"]), report["written"])

    def test_a_new_subject_the_roadmap_cannot_list_keeps_the_check_red(self) -> None:
        # The walk up from a page reaches the roadmap's own page: a new subject listed nowhere is an error.
        taxonomy = json.loads(json.dumps(self.TAXONOMY))
        taxonomy["regions"]["Foundations"] = ["Logic"]
        taxonomy["subjects"]["Logic"] = {"title": "Logic", "description": "Proofs.", "fields": [
            {"slug": "basics", "title": "Basics", "description": "Basics.", "subfields": []}]}
        taxonomy["placements"]["MathlibExt/Logic/Basics"] = {"to": "Logic/basics", "title": "Basics"}
        self.write("scripts/taxonomy.json", json.dumps(taxonomy))
        self.write("blueprint/roadmap/README.md", self.PAGES["README.md"] + "\n```\nnot a list\n```\n")
        self.base = self.commit("a roadmap page with a code fence")
        self.write("MathlibExt/Logic/Basics.lean", "namespace Ext.Logic\n\n/-- A proof. -/\ntheorem proof : True := "
                   "trivial\n\n/-- Another. -/\ntheorem other : True := trivial\n\nend Ext.Logic\n")
        self.assertEqual(self.run_sync()[0], 1)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (1, False))
        self.assertEqual(report["errors"], ["Logic, a folder the changes add, is listed on no folder page: list it on "
                                            "README.md"])

    def test_a_new_folder_without_its_row_or_behind_a_link_is_not_in_step(self) -> None:
        self.write("MathlibExt/Algebra/Rings.lean", self.RINGS)
        self.assertEqual(self.run_sync()[0], 0)
        links = self.root / "blueprint/links/Algebra.jsonl"
        kept = links.read_text()
        links.write_text("".join(line for line in kept.splitlines(keepends=True) if "rings/README.md" not in line))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (1, False))
        self.assertEqual(report["errors"], ["Algebra/not-yet-classified/rings/README.md, the page of a folder the "
                                            "changes add, has no annotation row: restore its row"])
        links.write_text(kept)
        folder = self.root / "blueprint/roadmap/Algebra/not-yet-classified/rings"
        folder.rename(self.root / "rings")
        folder.symlink_to(self.root / "rings")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (1, [
            "blueprint/roadmap/Algebra/not-yet-classified/rings is a link: the sync reads and writes through none; put "
            "what it links to in its place"]))
        # A link stops the writer, which then writes nothing.
        before = {path: path.read_bytes() for path in (self.root / "blueprint").rglob("*") if path.is_file()}
        status, out, err, report = self.run_sync()
        self.assertEqual((status, "The run wrote nothing" in err), (1, True))
        self.assertEqual({path: path.read_bytes() for path in (self.root / "blueprint").rglob("*") if path.is_file()},
                         before)

    def test_a_folder_page_written_in_place_keeps_its_mode(self) -> None:
        (self.root / "blueprint/roadmap/Algebra/groups/group-basics/README.md").chmod(0o755)
        self.base = self.commit("an executable folder page")
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"]), (0, "sync"), report["differences"])

    def test_the_check_reads_the_base_rows_once_whatever_the_number_of_rows(self) -> None:
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        counted = []
        # The base's Lean is read in this process, as where the platform cannot fork.
        real = sync.numbered_rows

        def numbered_rows():
            counted.append(1)
            return real()

        def in_background(function, *args):
            value = function(*args)
            return lambda: value

        with patch.object(sync, "numbered_rows", numbered_rows), patch.object(sync, "in_background", in_background):
            status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"]), (0, "sync"))
        # The base's rows for its view, the working tree's for the plan and for the ids, and the base's once for the
        # ids and once for its plan: five, with more rows than that.
        self.assertGreater(len(sync.numbered_rows()), 5)
        self.assertEqual(len(counted), 5)

    def test_a_part_copy_the_changes_leave_stale_is_refreshed(self) -> None:
        # A new folder goes into the last part of a split field; the copy of that part on the field's page must list it,
        # and the writer refreshes that copy even when nothing else is left to write.
        taxonomy = json.loads(json.dumps(self.TAXONOMY))
        taxonomy["placements"]["MathlibExt/Algebra/Rings"] = {"to": "Algebra/groups", "title": "Rings"}
        self.write("scripts/taxonomy.json", json.dumps(taxonomy))
        field = self.write("blueprint/roadmap/Algebra/groups/README.md",
                           "# Groups\n\nGroups.\n\n- [Group basics](group-basics/README.md)\n\n"
                           "## [Part 1](part-01/README.md)\n\n- [Cosets](part-01/cosets/README.md)\n")
        self.write("blueprint/roadmap/Algebra/groups/part-01/README.md",
                   "# Groups, part 1\n\n- [Cosets](cosets/README.md)\n")
        self.write("blueprint/roadmap/Algebra/groups/part-01/cosets/README.md", "# Cosets\n\nCosets.\n")
        self.base = self.commit("a field split into parts")
        self.write("MathlibExt/Algebra/Rings.lean", self.RINGS)
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 0, err)
        copy = "- [Rings](part-01/rings/README.md)\n"
        self.assertIn(copy, field.read_text())
        field.write_text(field.read_text().replace(copy, ""))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["parts"], report["errors"], report["missing"],
                          report["digests"]), (1, False, ["Algebra/groups/part-01/README.md"], [], [], {}))
        self.assertIn(f"python3 scripts/sync_wiki.py declarations --base {self.base}", out)
        status, out, err, report = self.run_sync()
        self.assertEqual((status, "Nothing to write." in out), (0, False))
        self.assertIn(copy, field.read_text())
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "sync"))

    def test_a_part_copy_the_sync_cannot_refresh_is_an_error(self) -> None:
        taxonomy = json.loads(json.dumps(self.TAXONOMY))
        taxonomy["placements"]["MathlibExt/Algebra/Rings"] = {"to": "Algebra/groups", "title": "Rings"}
        self.write("scripts/taxonomy.json", json.dumps(taxonomy))
        # A code fence makes the field's page one the sync does not refresh.
        field = self.write("blueprint/roadmap/Algebra/groups/README.md",
                           "# Groups\n\nGroups.\n\n```\ncode\n```\n\n- [Group basics](group-basics/README.md)\n\n"
                           "## [Part 1](part-01/README.md)\n\n- [Cosets](part-01/cosets/README.md)\n")
        self.write("blueprint/roadmap/Algebra/groups/part-01/README.md",
                   "# Groups, part 1\n\n- [Cosets](cosets/README.md)\n")
        self.write("blueprint/roadmap/Algebra/groups/part-01/cosets/README.md", "# Cosets\n\nCosets.\n")
        self.base = self.commit("a field split into parts, with a code fence")
        self.write("MathlibExt/Algebra/Rings.lean", self.RINGS)
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 1)
        self.assertIn("error: the copy of Algebra/groups/part-01's list on its parent's page could not be refreshed",
                      err)
        self.assertNotIn("part-01/rings/README.md", field.read_text())
        # What the failed write leaves is not the sync's output, though nothing else changed.
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["parts"], report["wiki_changes"]),
                         (1, False, ["Algebra/groups/part-01/README.md"], "other"))
        self.assertIn("the copy of Algebra/groups/part-01's list on its parent's page could not be refreshed",
                      report["differences"][0])
        cosets = "- [Cosets](part-01/cosets/README.md)\n"
        field.write_text(field.read_text().replace(cosets, cosets + "- [Rings](part-01/rings/README.md)\n"))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["parts"], report["wiki_changes"]), (0, True, [], "other"))

    def test_a_page_written_again_is_listed_once(self) -> None:
        # The repair a missing page's error advises: remove its row, and the sync writes the page again, keeping the
        # folder page's entry for it.
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        (self.root / "blueprint/roadmap/Algebra/groups/group-basics/fresh.md").unlink()
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text("".join(line for line in links.read_text().splitlines(keepends=True)
                                 if "fresh.md" not in line))
        self.assertEqual(self.run_sync()[0], 0)
        folder_page = (self.root / "blueprint/roadmap/Algebra/groups/group-basics/README.md").read_text()
        self.assertEqual(folder_page.count("(fresh.md)"), 1, folder_page)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "sync"))

    def test_a_temporary_folder_reached_through_a_link(self) -> None:
        real = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, real, True)
        alias = self.root.parent / f"{self.root.name}-alias"
        alias.symlink_to(real)
        self.addCleanup(alias.unlink)
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        with patch.object(tempfile, "tempdir", str(alias)):
            self.assertEqual(self.run_sync()[0], 0)
            status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"]), (0, "sync"), err)

    def split_field(self, fence: str = "") -> Path:
        """Make the base's field a split one: its part-01 holds the module Cosets's page of Ext.Cosets.one, which the
        field's page copies; returns the field's page."""
        taxonomy = json.loads(json.dumps(self.TAXONOMY))
        for name in ("Rings", "Cosets"):
            taxonomy["placements"][f"MathlibExt/Algebra/{name}"] = {"to": "Algebra/groups", "title": name}
        self.write("scripts/taxonomy.json", json.dumps(taxonomy))
        field = self.write("blueprint/roadmap/Algebra/groups/README.md",
                           f"# Groups\n\nGroups.\n\n{fence}- [Group basics](group-basics/README.md)\n\n"
                           "## [Part 1](part-01/README.md)\n\n- [One](part-01/one.md)\n")
        self.write("blueprint/roadmap/Algebra/groups/part-01/README.md", "# Groups, part 1\n\n- [One](one.md)\n")
        self.write("blueprint/roadmap/Algebra/groups/part-01/one.md", "# One\n\nOne coset.\n")
        self.write("MathlibExt/Algebra/Cosets.lean", "namespace Ext.Cosets\n\n/-- One coset. -/\ntheorem one : True := "
                   "trivial\n\nend Ext.Cosets\n")
        links = self.root / "blueprint/links/Algebra.jsonl"
        rows = [{"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/part-01/README.md"}],
                 "id": "af_" + "d" * 24},
                {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/part-01/one.md"}],
                 "id": "af_" + "e" * 24, "object": [{"location": {"declaration": "Ext.Cosets.one"}}]}]
        links.write_text(links.read_text() + "".join(json.dumps(row) + "\n" for row in rows))
        state = self.root / "scripts/wiki-sync.json"
        digests = json.loads(state.read_text())["docstrings"]
        digests["Ext.Cosets.one"] = sync.digest("One coset.")
        state.write_text(json.dumps({"docstrings": dict(sorted(digests.items()))}, indent=0) + "\n")
        self.base = self.commit("a field split into parts")
        return field

    def test_a_page_written_again_in_a_part_refreshes_the_parts_copy(self) -> None:
        field = self.split_field()
        cosets = self.root / "MathlibExt/Algebra/Cosets.lean"
        two = "/-- Two cosets. -/\ntheorem two : True := trivial\n\nend Ext"
        cosets.write_text(cosets.read_text().replace("end Ext", two))
        self.assertEqual(self.run_sync()[0], 0)
        copy = "- [Two](part-01/two.md)\n"
        self.assertIn(copy, field.read_text())
        # The page, its row and the field's copy of it go; the part's page still lists it.
        (self.root / "blueprint/roadmap/Algebra/groups/part-01/two.md").unlink()
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text("".join(line for line in links.read_text().splitlines(keepends=True) if "two.md" not in line))
        field.write_text(field.read_text().replace(copy, ""))
        self.assertEqual(self.run_sync()[0], 0)
        self.assertIn(copy, field.read_text())
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "sync"))
        before = self.tree()
        self.assertEqual(self.run_sync()[0], 0)
        self.assertEqual(self.tree(), before)

    def test_a_row_outside_the_roadmap_places_no_page_there(self) -> None:
        # A row names a page of the module outside the roadmap, a row Autoform leaves out: the run writes nothing, as
        # the whole run does, and so nothing outside the wiki; the pull request that adds such a row is stopped.
        self.write("outside/one.md", "# One\n\nOne coset.\n")
        taxonomy = json.loads(json.dumps(self.TAXONOMY))
        taxonomy["placements"]["MathlibExt/Algebra/Cosets"] = {"to": "Algebra/groups", "title": "Cosets"}
        self.write("scripts/taxonomy.json", json.dumps(taxonomy))
        self.write("MathlibExt/Algebra/Cosets.lean", "namespace Ext.Cosets\n\n/-- One coset. -/\ntheorem one : True := "
                   "trivial\n\nend Ext.Cosets\n")
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text() + json.dumps({
            "subject": [{"type": "generic", "uri": "../../outside/one.md"}], "id": "af_" + "f" * 24,
            "object": [{"location": {"declaration": "Ext.Cosets.one"}}]}) + "\n")
        self.base = self.commit("a row outside the roadmap")
        cosets = self.root / "MathlibExt/Algebra/Cosets.lean"
        two = "/-- Two cosets. -/\ntheorem two : True := trivial\n\nend Ext"
        cosets.write_text(cosets.read_text().replace("end Ext", two))
        before = self.tree()
        status, out, err, report = self.run_sync()
        self.assertEqual((status, "is one Autoform leaves out" in err, report.get("written", [])), (1, True, []))
        self.assertEqual(self.tree(), before)
        # The same row added by the pull request stops it before it writes anything.
        links.write_text("".join(line for line in links.read_text().splitlines(keepends=True) if "outside" not in line))
        self.base = self.commit("no row outside the roadmap")
        links.write_text(links.read_text() + json.dumps({
            "subject": [{"type": "generic", "uri": "../../outside/one.md"}], "id": "af_" + "f" * 24,
            "object": [{"location": {"declaration": "Ext.Cosets.one"}}]}) + "\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (1, False))
        self.assertEqual(report["errors"], [f"the row af_{'f' * 24} is one Autoform cannot read: a row of Algebra.jsonl "
                                            "about ../../outside/one.md is one Autoform leaves out: its subject names no "
                                            "page below roadmap/; a row names its page whole; fix it"])

    def test_a_page_whose_declaration_loses_its_docstring_keeps_the_bases_digest(self) -> None:
        # The digest the base reviewed stays, whatever the pull request does to its entry; none is made up when the
        # base had none.
        state = self.root / "scripts/wiki-sync.json"
        reviewed = sync.digest(self.LAGRANGE)
        groups = self.root / "MathlibExt/Algebra/Groups.lean"
        groups.write_text(groups.read_text().replace(f"/-- {self.LAGRANGE} -/\n", ""))
        self.assertEqual(self.run_sync()[0], 0)
        self.assertEqual(json.loads(state.read_text())["docstrings"]["Ext.lagrange"], reviewed)
        for entry in (None, sync.digest("Something else.")):
            digests = json.loads(state.read_text())["docstrings"]
            if entry is None:
                digests.pop("Ext.lagrange")
            else:
                digests["Ext.lagrange"] = entry
            state.write_text(json.dumps({"docstrings": digests}, indent=0) + "\n")
            status, out, err, report = self.run_sync("--check")
            self.assertEqual((status, report["in_step"], report["digests"]), (1, False, {"Ext.lagrange": reviewed}),
                             entry)
            self.assertEqual(self.run_sync()[0], 0)
            self.assertEqual(json.loads(state.read_text())["docstrings"]["Ext.lagrange"], reviewed)
            # The baseline is the base's again, as are the wiki's other files.
            status, out, err, report = self.run_sync("--check")
            self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "none"))
        # A base without the entry: nothing to keep.
        digests = json.loads(state.read_text())["docstrings"]
        digests.pop("Ext.lagrange")
        state.write_text(json.dumps({"docstrings": digests}, indent=0) + "\n")
        groups.write_text(self.GROUPS.format(lagrange=self.LAGRANGE, more=""))
        self.base = self.commit("no entry for lagrange")
        groups.write_text(groups.read_text().replace(f"/-- {self.LAGRANGE} -/\n", ""))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["digests"]), (0, {}))

    def test_a_row_credits_its_declaration_without_the_folders_defaults(self) -> None:
        # Without defaults to complete the shorthand, the run writes the Lean end whole, so the row credits the
        # declaration it was written for, the check passes and a second write changes nothing.
        self.git("rm", "-q", "blueprint/links/_defaults.json")
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text().replace('"object": [{"location": {"declaration": "Ext.lagrange"}}]',
                                                   '"object": [{"type": "lean", "uri": "../..", "location": '
                                                   '{"declaration": "Ext.lagrange"}}]'))
        self.base = self.commit("explicit Lean ends, no defaults")
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        row = next(json.loads(line) for line in links.read_text().splitlines() if "fresh.md" in line)
        self.assertEqual((row["object"], sync.lean_name(row)),
                         ([{"type": "lean", "uri": "../..", "location": {"declaration": "Ext.fresh"}}], "Ext.fresh"))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "sync"))
        before = self.tree()
        self.assertEqual(self.run_sync()[0], 0)
        self.assertEqual(self.tree(), before)

    def test_a_row_the_build_refuses_hides_no_other_problem(self) -> None:
        # A flag that is not a Boolean, on an unrelated row the base already had, leaves the held marker the changes
        # make stale as visible as it would be without it.
        self.write("blueprint/roadmap/Algebra/groups/group-basics/odd.md", "# Odd\n\nOdd.\n")
        self.write("blueprint/roadmap/Algebra/groups/group-basics/held.md", "# Held\n\nHeld.\n")
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text() + json.dumps({
            "subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/odd.md"}],
            "id": "af_" + "a" * 24, "extensions": {"org.autoform": {"mathlib": "yes"}}}) + "\n" + json.dumps({
            "subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/held.md"}],
            "id": "af_" + "b" * 24, "extensions": {sync.OWN: {"held": {"declaration": "Ext.stillHeld",
                                                                       "reason": "Its statement is wrong."}}}}) + "\n")
        self.groups(more="theorem stillHeld : True := trivial\n\n")
        self.base = self.commit("an unreadable flag and a held marker")
        self.groups()
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (1, False), report["errors"])
        self.assertTrue(any("Ext.stillHeld" in row for row in report["errors"]), report["errors"])
        self.assertFalse(any("mathlib" in row for row in report["errors"]), report["errors"])

    def test_rows_are_read_as_autoform_reads_them(self) -> None:
        # A row whose page its subject's defaults give, a string holding U+2028, records separated by carriage
        # returns, and a refused row with no subject the base already had: the run orders, keeps and hints rows by the
        # page Autoform reads, splits records as Autoform does, and keeps every other byte.
        links = self.root / "blueprint/links/Algebra.jsonl"
        lines = links.read_text().splitlines()
        lines[0] = json.dumps({"subject": [{"type": "generic"}], "id": json.loads(lines[0])["id"],
                               "note": "two\u2028lines"}, ensure_ascii=False)
        self.write("blueprint/links/_defaults.json", json.dumps({
            **sync.DEFAULTS, "subject": {"type": "generic", "uri": "../roadmap/Algebra/README.md"}}) + "\n")
        links.write_text("\r".join(lines) + "\r" + json.dumps({"subject": [], "id": "af_" + "c" * 24}) + "\r")
        self.base = self.commit("rows as Autoform reads them")
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["missing"], report["errors"]), (1, ["Ext.fresh"], []))
        kept = links.read_bytes()
        status, out, err, report = self.run_sync()
        # The refused row the base had stops the write, which writes nothing.
        self.assertEqual((status, "the run wrote nothing" in err, links.read_bytes()), (1, True, kept))
        links.write_bytes(kept.replace(b'\r{"subject": [], "id": "af_' + b"c" * 24 + b'"}', b""))
        self.git("add", "blueprint/links/Algebra.jsonl")
        self.git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "no refused row")
        self.base = self.git("rev-parse", "HEAD")
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 0, err)
        text = links.read_bytes().decode()
        self.assertIn("two\u2028lines", text)
        self.assertEqual([line for line in sync.records(text)[0] if "fresh.md" not in line],
                         sync.records(kept.decode().replace('\r{"subject": [], "id": "af_' + "c" * 24 + '"}', ""))[0])
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "sync"))

    def test_a_problem_the_base_had_is_not_the_changes(self) -> None:
        # An annotation file Autoform reads and the sync does not, already on the base, is reported the same way on
        # both sides, though the base's copy sits in a temporary folder.
        self.write("blueprint/links/Extra.ndjson", "")
        self.base = self.commit("a links file Autoform reads and the sync does not")
        page = self.root / "blueprint/roadmap/Algebra/groups/group-basics/lagrange.md"
        page.write_text(page.read_text() + "\nMore prose.\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["errors"], report["wiki_changes"]), (0, True, [], "other"))


    def test_a_row_turns_off_a_mathlib_flag_its_defaults_set(self) -> None:
        # Defaults that flag every row for Mathlib, which the base's rows turn off: the run's new rows turn it off too,
        # so they credit what they were written for, and the check and a second write agree.
        self.write("blueprint/links/_defaults.json", json.dumps({**sync.DEFAULTS, "extensions": {
            "org.autoform": {"mathlib": True}}}) + "\n")
        for path in ("blueprint/links/Algebra.jsonl", "blueprint/links/roadmap.jsonl"):
            links = self.root / path
            rows = [json.loads(line) for line in links.read_text().splitlines()]
            for row in rows:
                row.setdefault("extensions", {}).setdefault("org.autoform", {})["mathlib"] = False
            links.write_text("".join(json.dumps(row) + "\n" for row in rows))
        self.base = self.commit("defaults that flag rows for Mathlib")
        self.write("MathlibExt/Algebra/Rings.lean", self.RINGS)
        self.assertEqual(self.run_sync()[0], 0)
        links = self.root / "blueprint/links/Algebra.jsonl"
        new = [json.loads(line) for line in links.read_text().splitlines() if "not-yet-classified" in line]
        self.assertEqual(len(new), 4)
        self.assertTrue(all(row["extensions"]["org.autoform"]["mathlib"] is False for row in new))
        self.assertEqual(sorted(sync.page_owner(row)[1] or "" for row in new), ["", "", "Ext.Rings.fields", "Ext.Rings.units"])
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "sync"))
        before = self.tree()
        self.assertEqual(self.run_sync()[0], 0)
        self.assertEqual(self.tree(), before)

    def test_a_second_row_with_the_same_problem_is_the_changes(self) -> None:
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text() + json.dumps({"subject": [], "id": "af_" + "c" * 24}) + "\n")
        self.base = self.commit("a refused row")
        links.write_text(links.read_text() + json.dumps({"subject": [], "id": "af_" + "d" * 24}) + "\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (1, False))
        self.assertEqual(len(report["errors"]), 1, report["errors"])

    def test_a_page_key_has_forward_slashes_on_every_platform(self) -> None:
        # Where page_name gives the platform's separators, ids are still hinted and found by one key.
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        real = sync.page_name
        with patch.object(sync.os, "sep", "\\"), \
                patch.object(sync, "page_name", lambda row: real(row).replace("/", "\\")):
            status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"]), (0, "sync"), report["differences"])


    def test_a_row_the_changes_break_is_theirs_though_they_fix_another(self) -> None:
        links = self.root / "blueprint/links/Algebra.jsonl"
        self.write("blueprint/roadmap/Algebra/groups/group-basics/b.md", "# B\n\nB.\n")
        b = {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/b.md"}], "id": "af_" + "b" * 24}
        a = {"subject": [], "id": "af_" + "a" * 24}
        links.write_text(links.read_text() + json.dumps(a) + "\n" + json.dumps(b) + "\n")
        self.base = self.commit("a broken row and a sound one")
        self.write("blueprint/roadmap/Algebra/groups/group-basics/a.md", "# A\n\nA.\n")
        fixed = {**a, "subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/a.md"}]}
        links.write_text(links.read_text().replace(json.dumps(a), json.dumps(fixed)).replace(json.dumps(b),
                                                                                          json.dumps({**b, "subject": []})))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (1, False))
        self.assertEqual([row for row in report["errors"] if "af_" + "b" * 24 in row],
                         [f"the row af_{'b' * 24} is one Autoform cannot read: a row of Algebra.jsonl about ? is one "
                          f"Autoform leaves out: {sync.read_subject({**b, 'subject': []})[1]}; a row names its page whole; "
                          "fix it"])
        self.assertFalse(any("af_" + "a" * 24 in row for row in report["errors"]), report["errors"])

    def test_a_folder_row_clears_a_declaration_its_defaults_name_only_when_one_is_made(self) -> None:
        # Defaults that name a declaration, which the base's folder rows clear: a docstring edit writes its digest,
        # with no folder row to check, and a new folder's row clears the declaration too.
        self.write("blueprint/links/_defaults.json", json.dumps({"object": {**sync.DEFAULTS["object"],
                                                                            "location": {"declaration": "Ext.lagrange"}}})
                   + "\n")
        for path in ("blueprint/links/Algebra.jsonl", "blueprint/links/roadmap.jsonl"):
            links = self.root / path
            rows = [json.loads(line) for line in links.read_text().splitlines()]
            for row in rows:
                row.setdefault("object", [])
            links.write_text("".join(json.dumps(row) + "\n" for row in rows))
        self.base = self.commit("defaults that name a declaration")
        self.groups(lagrange="The order of a subgroup divides the group's.")
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 0, err)
        self.assertEqual(report["written"], ["scripts/wiki-sync.json"])
        self.write("MathlibExt/Algebra/Rings.lean", self.RINGS)
        self.assertEqual(self.run_sync()[0], 0)
        links = self.root / "blueprint/links/Algebra.jsonl"
        folders = [json.loads(line) for line in links.read_text().splitlines() if "not-yet-classified" in line
                   and "README.md" in line]
        self.assertEqual([(row.get("object"), sync.page_owner(row)) for row in folders], [([], ("none", None, None))] * 2)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "sync"))


    def test_a_broken_row_still_counts_among_its_pages_rows(self) -> None:
        # The base's row of a page has a flag that is not a Boolean; a second row of that page, which the changes add,
        # is a new problem, though the inherited one is not.
        self.write("blueprint/roadmap/Algebra/groups/group-basics/planned.md", "# Planned\n\nPlanned.\n")
        links = self.root / "blueprint/links/Algebra.jsonl"
        row = {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/planned.md"}],
               "id": "af_" + "a" * 24, "extensions": {"org.autoform": {"mathlib": "yes"}}}
        links.write_text(links.read_text() + json.dumps(row) + "\n")
        self.base = self.commit("a row with a flag that is not a Boolean")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (0, []))
        links.write_text(links.read_text() + json.dumps({"subject": row["subject"], "id": "af_" + "b" * 24}) + "\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (1, False))
        self.assertEqual(report["errors"], ["Algebra/groups/group-basics/planned.md has a row too many, which Autoform "
                                            "reads together with its others; a page has one row; fix it"])

    def test_taking_a_row_from_a_page_with_too_many_is_no_new_problem(self) -> None:
        # A page with three rows on the base: taking one away leaves fewer too many, which is no problem of the
        # changes; adding a fourth is one.
        self.write("blueprint/roadmap/Algebra/groups/group-basics/planned.md", "# Planned\n\nPlanned.\n")
        links = self.root / "blueprint/links/Algebra.jsonl"
        subject = [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/planned.md"}]
        rows = [json.dumps({"subject": subject, "id": f"af_{letter * 24}"}) for letter in "abcd"]
        links.write_text(links.read_text() + "".join(row + "\n" for row in rows[:3]))
        self.base = self.commit("a page with three rows")
        links.write_text(links.read_text().replace(rows[2] + "\n", ""))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (0, []))
        links.write_text(links.read_text() + rows[2] + "\n" + rows[3] + "\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (1, [
            "Algebra/groups/group-basics/planned.md has a row too many, which Autoform reads together with its others; "
            "a page has one row; fix it"]))


    def test_a_declarations_pages_are_counted_once_whatever_credits_them(self) -> None:
        # Three pages stand for Ext.lagrange on the base, one by the module and name an earlier sync wrote: taking one
        # away is no new problem; making that row an explicit link and adding a fourth page is one.
        links = self.root / "blueprint/links/Algebra.jsonl"
        folder = "blueprint/roadmap/Algebra/groups/group-basics"
        explicit = {"location": {"declaration": "Ext.lagrange"}}
        rows = {name: {"subject": [{"type": "generic", "uri": f"../roadmap/Algebra/groups/group-basics/{name}.md"}],
                       "id": f"af_{letter * 24}"} for name, letter in (("p2", "a"), ("p3", "b"), ("p4", "c"))}
        for name in rows:
            self.write(f"{folder}/{name}.md", f"# {name}\n\nThe same result.\n")
        base = [{**rows["p2"], "object": [explicit]},
                {**rows["p3"], "extensions": {sync.OWN: {"module": "MathlibExt.Algebra.Groups", "name": "lagrange"}}}]
        links.write_text(links.read_text() + "".join(json.dumps(row) + "\n" for row in base))
        self.base = self.commit("three pages for one declaration")
        kept = links.read_text()
        links.write_text(kept.replace(json.dumps(base[0]) + "\n", ""))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (0, []))
        links.write_text(kept.replace(json.dumps(base[1]), json.dumps({**rows["p3"], "object": [explicit]}))
                         + json.dumps({**rows["p4"], "object": [explicit]}) + "\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (1, [
            "the declaration Ext.lagrange of this project has a page too many; a declaration has one page; fix it"]))


    def test_a_row_by_module_and_name_whose_declaration_goes_is_stale(self) -> None:
        # A row an earlier sync wrote with a module and a name links the declaration they resolve to: removing it
        # leaves the row stale, which stops the run until the row is relinked or the link removed.
        self.write("blueprint/roadmap/Algebra/groups/group-basics/extra.md", "# Extra\n\nExtra.\n")
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text() + json.dumps({
            "subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/extra.md"}],
            "id": "af_" + "e" * 24, "extensions": {sync.OWN: {"module": "MathlibExt.Algebra.Groups",
                                                               "name": "extra"}}}) + "\n")
        self.groups(more="theorem extra : True := trivial\n\n")
        self.base = self.commit("a row by module and name")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (0, []))
        self.groups()
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (1, False))
        self.assertEqual(len(report["errors"]), 1, report["errors"])
        self.assertIn("names extra in MathlibExt.Algebra.Groups, by the module and name an earlier sync wrote, which no "
                      "longer name one declaration of the Lean", report["errors"][0])
        # A second declaration of that name in the module makes the pair name two: the same problem.
        self.groups(more="theorem extra : True := trivial\n\nnamespace Other\n\ntheorem extra : True := trivial\n\n"
                         "end Other\n\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, len(report["errors"])), (1, 1), report["errors"])
        self.assertIn("which no longer name one declaration of the Lean", report["errors"][0])

    def test_a_row_crediting_mathlib_keeps_the_module_and_name_it_once_had(self) -> None:
        # A row the links folder's defaults credit to Mathlib, which still carries the module and name an earlier sync
        # wrote: its owner is Mathlib's declaration, whatever becomes of the old one, so removing that one leaves no
        # stale link (the problems the defaults give other rows are the base's).
        self.write("blueprint/links/_defaults.json", json.dumps({
            "object": {"type": "lean", "uri": "https://github.com/leanprover-community/mathlib4",
                       "location": {"declaration": "Nat.add_comm", "module": "Mathlib.Algebra.Group.Nat"}},
            "extensions": {"org.autoform": {"mathlib": True}}}) + "\n")
        self.write("blueprint/roadmap/Algebra/groups/group-basics/extra.md", "# Extra\n\nExtra.\n")
        links = self.root / "blueprint/links/Algebra.jsonl"
        row = {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/extra.md"}],
               "id": "af_" + "e" * 24, "extensions": {sync.OWN: {"module": "MathlibExt.Algebra.Groups", "name": "extra"}}}
        links.write_text(links.read_text() + json.dumps(row) + "\n")
        self.groups(more="theorem extra : True := trivial\n\n")
        self.base = self.commit("a Mathlib-credited row with an old module and name")
        self.assertEqual((sync.page_owner(row)[0], sync.legacy_pair(row)), ("mathlib", ("MathlibExt.Algebra.Groups",
                                                                                         "extra")))
        self.groups()
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (0, []))
        # Its module and name are never read, even when they name nothing.
        links.write_text(links.read_text().replace('"module": "MathlibExt.Algebra.Groups"', '"module": null'))
        with patch.object(sync, "legacy_lean_name", side_effect=AssertionError("read the module and name")):
            status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (0, True))

    def test_a_row_the_run_cannot_settle_stops_it_before_it_writes(self) -> None:
        # Every row the run may add is checked before anything is written: one that would not credit its declaration
        # leaves the tree as it was, the baseline included.
        self.write("MathlibExt/Algebra/Rings.lean", self.RINGS)
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        before = self.tree()
        real = sync.settled
        with patch.object(sync, "settled", lambda annotation, lean: lean != "Ext.Rings.units" and real(annotation, lean)):
            status, out, err, report = self.run_sync()
        self.assertEqual((status, report.get("written")), (1, []))
        self.assertIn("no row the sync can write credits Ext.Rings.units to this project; fix it and run again (the run "
                      "wrote nothing)", err)
        self.assertEqual(self.tree(), before)


    def test_a_link_to_a_declaration_the_row_does_not_credit_goes_stale_too(self) -> None:
        # A row stating lagrange and using helper: removing helper leaves its link stale, though the row's credit
        # still holds.
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text().replace(
            '"object": [{"location": {"declaration": "Ext.lagrange"}}]',
            '"object": [{"location": {"declaration": "Ext.lagrange"}, "role": "states"}, '
            '{"location": {"declaration": "Ext.helper"}, "role": "uses"}]'))
        self.groups(more="theorem helper : True := trivial\n\n")
        self.base = self.commit("a row that uses a second declaration")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (0, []))
        self.groups()
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], len(report["errors"])), (1, False, 1), report["errors"])
        self.assertIn("links Ext.helper, which the row names but does not credit, and the Lean no longer has it: point "
                      "that end at the declaration's successor or remove the end, keeping the row's article id and what "
                      "it credits", report["errors"][0])

    def test_a_row_by_module_and_name_that_also_uses_a_declaration_is_checked_for_both(self) -> None:
        # A row whose defaults make it use helper and that credits extra by the module and name an earlier sync wrote:
        # removing either is the changes' problem, and removing both, two.
        self.write("blueprint/links/_defaults.json", json.dumps({"object": {
            **sync.DEFAULTS["object"], "location": {"declaration": "Ext.helper"}, "role": "uses"}}) + "\n")
        roadmap = self.root / "blueprint/links/roadmap.jsonl"
        roadmap.write_text("".join(json.dumps({**json.loads(line), "object": []}) + "\n"
                                   for line in roadmap.read_text().splitlines()))
        links = self.root / "blueprint/links/Algebra.jsonl"
        rows = [json.loads(line) for line in links.read_text().splitlines()]
        for row in rows:
            row.setdefault("object", [])
        self.write("blueprint/roadmap/Algebra/groups/group-basics/extra.md", "# Extra\n\nExtra.\n")
        rows.append({"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/extra.md"}],
                     "id": "af_" + "e" * 24, "extensions": {sync.OWN: {"module": "MathlibExt.Algebra.Groups",
                                                                        "name": "extra"}}})
        links.write_text("".join(json.dumps(row) + "\n" for row in rows))
        both = "theorem helper : True := trivial\n\ntheorem extra : True := trivial\n\n"
        self.groups(more=both)
        self.base = self.commit("a row that uses helper and credits extra by module and name")
        self.assertEqual(self.run_sync("--check")[3]["errors"], [])
        for more, expected in ((both.replace("theorem extra : True := trivial\n\n", ""), ["extra in"]),
                               (both.replace("theorem helper : True := trivial\n\n", ""), ["Ext.helper"]),
                               ("", ["Ext.helper", "extra in"])):
            self.groups(more=more)
            status, out, err, report = self.run_sync("--check")
            self.assertEqual((status, len(report["errors"])), (1, len(expected)), report["errors"])
            for row, name in zip(sorted(report["errors"], key=lambda row: "extra in" in row), expected):
                self.assertIn(name, row)


    def test_a_stale_link_the_base_had_stays_the_bases_when_the_row_gains_a_credit(self) -> None:
        # The base's row links only a declaration the Lean lacks; the changes add the declaration it states, leaving
        # that end as it was: no new problem.
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text().replace(
            '"object": [{"location": {"declaration": "Ext.lagrange"}}]',
            '"object": [{"location": {"declaration": "Ext.alreadyGone"}}]'))
        self.base = self.commit("a stale link")
        links.write_text(links.read_text().replace(
            '"object": [{"location": {"declaration": "Ext.alreadyGone"}}]',
            '"object": [{"location": {"declaration": "Ext.alreadyGone"}}, {"location": {"declaration": "Ext.lagrange"}, '
            '"role": "states"}]'))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (0, []))


    def test_a_link_in_the_wiki_stops_the_run_before_it_reads_anything(self) -> None:
        outside = self.root.parent / f"{self.root.name}-outside.jsonl"
        outside.write_text("")
        self.addCleanup(outside.unlink)
        (self.root / "blueprint/links/Other.jsonl").symlink_to(outside)
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        for flags in ((), ("--check",)):
            with patch.object(sync, "numbered_rows", side_effect=AssertionError("read the links")), \
                    patch.object(sync, "read_annotations", side_effect=AssertionError("read the links")):
                status, out, err, report = self.run_sync(*flags)
            self.assertEqual((status, report["in_step"], report["errors"]), (1, False, [
                "blueprint/links/Other.jsonl is a link: the sync reads and writes through none; put what it links to "
                "in its place"]), flags)

    def test_the_page_of_an_own_declaration_held_back_must_be_a_page(self) -> None:
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_text(links.read_text() + json.dumps({
            "subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/fresh.md"}],
            "id": "af_" + "f" * 24, "extensions": {sync.OWN: {"held": {"declaration": "Ext.fresh",
                                                                       "reason": "Its statement is wrong."}}}}) + "\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["held"], report["missing"]), (1, False, ["Ext.fresh"], []))
        self.assertEqual(report["errors"], ["blueprint/roadmap/Algebra/groups/group-basics/fresh.md, which the row "
                                            "holding Ext.fresh back names, is not a page: restore it there, keeping the "
                                            "row, its article id and its held marker"])

    def test_an_entry_to_drop_is_dropped_whatever_its_value(self) -> None:
        # The changes remove backlog, whose entry the baseline must lose: an entry left as null is still there.
        groups = self.root / "MathlibExt/Algebra/Groups.lean"
        groups.write_text(groups.read_text().replace("/-- A result that has no page yet. -/\ntheorem backlog : True := "
                                                     "trivial\n\n", ""))
        state = self.root / "scripts/wiki-sync.json"
        digests = json.loads(state.read_text())["docstrings"]
        digests["Ext.backlog"] = None
        state.write_text(json.dumps({"docstrings": digests}, indent=0) + "\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["digests"]), (1, {"Ext.backlog": None}))
        self.assertEqual(self.run_sync()[0], 0)
        self.assertNotIn("Ext.backlog", json.loads(state.read_text())["docstrings"])


    def test_a_link_among_the_files_the_run_reads_or_the_changes_touch_stops_it(self) -> None:
        # The page map and the Lean the changes add are read too: a link there stops the run before anything is read.
        outside = self.root.parent / f"{self.root.name}-outside"
        outside.write_text("")
        self.addCleanup(outside.unlink)
        for link in ("blueprint/pages.json", "MathlibExt/Algebra/Linked.lean"):
            (self.root / link).symlink_to(outside)
            with patch.object(sync, "numbered_rows", side_effect=AssertionError("read the links")), \
                    patch.object(wiki, "generate", side_effect=AssertionError("read the Lean")):
                status, out, err, report = self.run_sync("--check")
            self.assertEqual((status, report["errors"]), (1, [
                f"{link} is a link: the sync reads and writes through none; put what it links to in its place"]), link)
            (self.root / link).unlink()

    def test_a_refusal_reports_the_changes_as_they_are(self) -> None:
        # A link the base already had stops a Lean-only change, which has no wiki changes and one Lean file.
        outside = self.root.parent / f"{self.root.name}-outside"
        outside.write_text("")
        self.addCleanup(outside.unlink)
        (self.root / "blueprint/sources").mkdir(parents=True)
        (self.root / "blueprint/sources/data.json").symlink_to(outside)
        self.base = self.commit("a link in the wiki")
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"], report["wiki_changes"], report["differences"],
                          report["counts"]["lean files"]), (1, [
            "blueprint/sources/data.json is a link: the sync reads and writes through none; put what it links to in its "
            "place"], "none", [], 1))


    def test_a_linked_site_configuration_stops_a_write_that_renders(self) -> None:
        # The renderer reads the site configuration, which the changes leave as it is: a link there stops the run too.
        site = self.root.parent / f"{self.root.name}-mkdocs.yml"
        site.symlink_to(sync.SITE)
        self.addCleanup(site.unlink)
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        with patch.object(sync, "SITE", site), patch.object(sync, "published", side_effect=AssertionError("rendered")):
            status, out, err, report = self.run_sync()
        self.assertEqual((status, len(report["errors"])), (1, 1), report["errors"])
        self.assertIn("is a link: the sync reads and writes through none", report["errors"][0])

    def test_a_link_the_sync_never_reads_leaves_a_documentation_change_alone(self) -> None:
        self.write("docs/guide.md", "A guide.\n")
        (self.root / "docs/guide-alias.md").symlink_to("guide.md")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"], report["errors"]), (0, True, "none", []))


    def test_a_link_in_a_lean_library_stops_the_run_as_the_working_tree_has_it(self) -> None:
        # A folder of a library the pages are generated from, linked: refused, staged or not; once the link is gone
        # from the working tree, staged or not, the run goes on.
        elsewhere = self.root.parent / f"{self.root.name}-lean"
        elsewhere.mkdir()
        self.addCleanup(shutil.rmtree, elsewhere, True)
        (elsewhere / "Linked.lean").write_text("theorem linked : True := trivial\n")
        linked = self.root / "MathlibExt/Linked"
        linked.symlink_to(elsewhere)
        self.base = self.commit("a linked folder of Lean")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (1, [
            "MathlibExt/Linked is a link: the sync reads and writes through none; put what it links to in its place"]))
        linked.unlink()
        linked.mkdir()
        (linked / "Linked.lean").write_text("theorem linked : True := trivial\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (0, []))


    def test_a_file_name_that_is_not_utf8_is_read_as_the_file_system_names_it(self) -> None:
        (self.root / "docs").mkdir()
        with open(os.path.join(os.fsencode(self.root), b"docs", b"caf\xe9.md"), "w") as handle:
            handle.write("Bytes.\n")
        self.base = self.commit("a file name that is not UTF-8")
        self.write("docs/guide.md", "A guide.\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "none"))
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["missing"]), (1, ["Ext.fresh"]))


    def test_a_link_in_a_library_the_generator_never_reads_leaves_a_change_alone(self) -> None:
        self.write("MathlibExt/Algebra/guide.md", "A guide.\n")
        (self.root / "MathlibExt/Algebra/guide-alias.md").symlink_to("guide.md")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["errors"]), (0, True, []))

    def test_a_changed_graph_file_whose_name_is_not_utf8_gives_a_report(self) -> None:
        name = os.path.join(os.fsencode(self.root), b"blueprint", b"roadmap", b"Algebra", b"caf\xe9.md")
        with open(name, "w") as handle:
            handle.write("# Bytes\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "other"))
        # The report is UTF-8 JSON, the name's bytes escaped, and reads back as the file system names it.
        self.assertIn(os.fsdecode(b"blueprint/roadmap/Algebra/caf\xe9.md"), " ".join(report["differences"]))


    def test_a_submodule_in_the_wiki_is_not_the_syncs(self) -> None:
        # A submodule the changes add under the roadmap beside what the sync writes, whether or not the working tree
        # has its folder: the sync writes none.
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        self.git("update-index", "--add", "--cacheinfo", f"160000,{'1' * 40},blueprint/roadmap/Algebra/sub")
        for folder in (False, True):
            if folder:
                (self.root / "blueprint/roadmap/Algebra/sub").mkdir()
            status, out, err, report = self.run_sync("--check")
            self.assertEqual(report["wiki_changes"], "other", (folder, report))
            self.assertIn("blueprint/roadmap/Algebra/sub: the sync writes no link or other kind of file",
                          report["differences"], folder)


    def test_a_page_staged_and_then_removed_is_still_the_changes(self) -> None:
        # The index holds a page written by hand that the working tree no longer has, and the Lean changes only a
        # comment: the page is the changes', not the sync's.
        groups = self.root / "MathlibExt/Algebra/Groups.lean"
        groups.write_text(groups.read_text() + "-- A comment.\n")
        page = self.root / "blueprint/roadmap/Algebra/hand.md"
        page.write_text("# By hand\n")
        self.git("add", "--", "blueprint/roadmap/Algebra/hand.md")
        page.unlink()
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((report["wiki_changes"], report["differences"]), (
            "other", ["blueprint/roadmap/Algebra/hand.md: " + INDEX_DIFFERS]))

    def test_what_the_index_changes_is_compared_whatever_the_working_tree_has(self) -> None:
        # A hand edit staged and then undone in the working tree, and a page the index deletes that the working tree
        # keeps: a commit takes the index's, so neither is the sync's.
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        page = self.root / "blueprint/roadmap/Algebra/groups/group-basics/fresh.md"
        generated = page.read_bytes()
        page.write_text(page.read_text() + "\nMore prose.\n")
        self.git("add", "--", str(page))
        page.write_bytes(generated)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((report["wiki_changes"], report["differences"]), ("other", [
            "blueprint/roadmap/Algebra/groups/group-basics/fresh.md: " + INDEX_DIFFERS]))
        self.git("reset", "-q", "--", str(page))
        self.assertEqual(self.run_sync("--check")[3]["wiki_changes"], "sync")
        self.git("rm", "-q", "--cached", "--", "blueprint/roadmap/Algebra/groups/group-basics/lagrange.md")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((report["wiki_changes"], report["differences"]), ("other", [
            "blueprint/roadmap/Algebra/groups/group-basics/lagrange.md: " + INDEX_DIFFERS]))
        self.git("reset", "-q", "--", "blueprint/roadmap/Algebra/groups/group-basics/lagrange.md")
        # The sync's output committed, the deletion of its page staged while the file stays: a commit takes the
        # deletion. And the sync's output staged with fresh ids of its own, another run's in the working tree: the
        # two differ, though each is the sync's.
        self.base = self.git("rev-parse", "HEAD")
        self.commit("the sync's output")
        self.git("rm", "-q", "--cached", "--", str(page))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((report["wiki_changes"], report["differences"]), ("other", [
            "blueprint/roadmap/Algebra/groups/group-basics/fresh.md: " + INDEX_DIFFERS]))
        self.git("reset", "-q", "--", str(page))
        self.assertEqual(self.run_sync("--check")[3]["wiki_changes"], "sync")


    def test_lean_staged_otherwise_than_the_working_tree_stops_the_run(self) -> None:
        # The index holds one declaration and the working tree another: the run reads the working tree's, which a
        # commit may not take, so it stops until the two agree.
        self.groups(more="/-- Only in the index. -/\ntheorem indexOnly : True := trivial\n\n")
        self.git("add", "--", "MathlibExt/Algebra/Groups.lean")
        self.groups(more="/-- Only in the working tree. -/\ntheorem workOnly : True := trivial\n\n")
        for flags in ((), ("--check",)):
            status, out, err, report = self.run_sync(*flags)
            self.assertEqual((status, report["in_step"], report["errors"]), (1, False, [
                "MathlibExt/Algebra/Groups.lean: " + INDEX_DIFFERS]), flags)
        self.git("add", "--", "MathlibExt/Algebra/Groups.lean")
        self.assertEqual(self.run_sync("--check")[3]["missing"], ["Ext.workOnly"])

    def test_a_working_tree_like_the_base_has_no_wiki_changes(self) -> None:
        # A prose edit committed on the branch, then undone in the working tree without staging: the changes, the
        # working tree's, have none.
        page = self.root / "blueprint/roadmap/Algebra/groups/group-basics/lagrange.md"
        kept = page.read_bytes()
        page.write_text(page.read_text() + "\nMore prose.\n")
        self.commit("a prose edit")
        page.write_bytes(kept)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"], report["differences"]), (0, "none", []))


    def test_a_link_stops_the_run_before_git_or_it_compares_what_is_staged(self) -> None:
        elsewhere = self.root.parent / f"{self.root.name}-lean"
        elsewhere.mkdir()
        self.addCleanup(shutil.rmtree, elsewhere, True)
        (self.root / "MathlibExt/Linked").symlink_to(elsewhere)
        self.groups(more="/-- Staged. -/\ntheorem staged : True := trivial\n\n")
        self.git("add", "--", "MathlibExt/Algebra/Groups.lean")
        with patch.object(sync, "disagreeing", side_effect=AssertionError("compared what is staged")):
            status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["errors"]), (1, [
            "MathlibExt/Linked is a link: the sync reads and writes through none; put what it links to in its place"]))

    def test_line_ends_git_normalises_are_no_disagreement(self) -> None:
        # Git stores the Lean with line feeds and checks it out with carriage returns: staged, the two agree.
        self.write(".gitattributes", "*.lean text eol=crlf\n")
        self.base = self.commit("line ends")
        groups = self.root / "MathlibExt/Algebra/Groups.lean"
        groups.write_text(groups.read_text() + "-- A comment.\n")
        self.git("add", "--", "MathlibExt/Algebra/Groups.lean")
        groups.write_bytes(groups.read_bytes().replace(b"\r\n", b"\n").replace(b"\n", b"\r\n"))
        self.assertEqual(self.git("diff", "--name-only"), "")
        status, out, err, report = self.run_sync("--check")
        self.assertFalse([row for row in report["errors"] if INDEX_DIFFERS in row], report["errors"])

    def test_a_staged_reversion_to_the_base_has_no_wiki_changes(self) -> None:
        page = self.root / "blueprint/roadmap/Algebra/groups/group-basics/lagrange.md"
        kept = page.read_bytes()
        page.write_text(page.read_text() + "\nMore prose.\n")
        self.commit("a prose edit")
        page.write_bytes(kept)
        self.git("add", "--", str(page))
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"], report["differences"]), (0, "none", []))


    def test_a_committed_submodule_without_its_folder_is_not_the_syncs(self) -> None:
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        self.git("add", "-A")
        self.git("update-index", "--add", "--cacheinfo", f"160000,{'1' * 40},blueprint/roadmap/Algebra/sub")
        self.git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "the sync's output and a submodule")
        self.assertFalse((self.root / "blueprint/roadmap/Algebra/sub").exists())
        status, out, err, report = self.run_sync("--check")
        self.assertEqual(report["wiki_changes"], "other", report)
        self.assertIn("blueprint/roadmap/Algebra/sub: the sync writes no link or other kind of file",
                      report["differences"])

    def test_an_executable_bit_staged_where_git_reads_none_from_the_working_tree(self) -> None:
        # With core.filemode off, the index's executable bit is the file's: staged on a page, it is not the sync's.
        self.git("config", "core.filemode", "false")
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        self.git("add", "-A")
        self.assertEqual(self.run_sync("--check")[3]["wiki_changes"], "sync")
        self.git("update-index", "--chmod=+x", "--", "blueprint/roadmap/Algebra/groups/group-basics/fresh.md")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((report["wiki_changes"], report["differences"]), ("other", [
            "blueprint/roadmap/Algebra/groups/group-basics/fresh.md: the changes write it otherwise than the sync"]))

    def test_a_refusal_counts_a_wiki_file_only_the_index_adds(self) -> None:
        elsewhere = self.root.parent / f"{self.root.name}-lean"
        elsewhere.mkdir()
        self.addCleanup(shutil.rmtree, elsewhere, True)
        (self.root / "MathlibExt/Linked").symlink_to(elsewhere)
        page = self.root / "blueprint/roadmap/Algebra/hand.md"
        page.write_text("# By hand\n")
        self.git("add", "--", "blueprint/roadmap/Algebra/hand.md")
        page.unlink()
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"]), (1, "other"))


    def test_a_submodule_git_is_told_to_ignore_is_still_not_the_syncs(self) -> None:
        self.git("config", "diff.ignoreSubmodules", "all")
        self.test_a_committed_submodule_without_its_folder_is_not_the_syncs()

    def test_the_executable_bit_is_the_owners_as_git_reads_it(self) -> None:
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        self.assertEqual(self.run_sync()[0], 0)
        page = self.root / "blueprint/roadmap/Algebra/groups/group-basics/fresh.md"
        page.chmod(0o654)
        self.assertEqual(self.run_sync("--check")[3]["wiki_changes"], "sync")
        page.chmod(0o744)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((report["wiki_changes"], report["differences"]), ("other", [
            "blueprint/roadmap/Algebra/groups/group-basics/fresh.md: the changes write it otherwise than the sync"]))

    def test_a_refusal_counts_no_wiki_change_a_commit_made_and_the_working_tree_undid(self) -> None:
        page = self.root / "blueprint/roadmap/Algebra/groups/group-basics/lagrange.md"
        kept = page.read_bytes()
        page.write_text(page.read_text() + "\nMore prose.\n")
        self.commit("a prose edit")
        page.write_bytes(kept)
        elsewhere = self.root.parent / f"{self.root.name}-lean"
        elsewhere.mkdir()
        self.addCleanup(shutil.rmtree, elsewhere, True)
        (self.root / "MathlibExt/Linked").symlink_to(elsewhere)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["wiki_changes"]), (1, "none"))


    def test_a_line_that_is_no_json_object_is_a_row_autoform_cannot_read(self) -> None:
        links = self.root / "blueprint/links/Algebra.jsonl"
        for line in ("not json", "[1, 2]"):
            kept = links.read_text()
            links.write_text(kept + line + "\n")
            status, out, err, report = self.run_sync("--check")
            self.assertEqual((status, report["in_step"]), (1, False), line)
            number = len(kept.splitlines()) + 1
            self.assertEqual(report["errors"], [f"blueprint/links/Algebra.jsonl:{number} is a line that is no JSON "
                                                f"object: {line}: make it a row, or remove it"])
            links.write_text(kept)

    def test_a_refusal_prints_both_verdicts(self) -> None:
        elsewhere = self.root.parent / f"{self.root.name}-lean"
        elsewhere.mkdir()
        self.addCleanup(shutil.rmtree, elsewhere, True)
        (self.root / "MathlibExt/Linked").symlink_to(elsewhere)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual(status, 1)
        self.assertIn("In step: no\nWiki changes since the base: none\n", out)


    def test_a_line_that_is_not_utf8_is_no_row(self) -> None:
        links = self.root / "blueprint/links/Algebra.jsonl"
        links.write_bytes(links.read_bytes() + b'{"id": "caf\xe9"}\n')
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], len(report["errors"])), (1, False, 1), report["errors"])
        self.assertIn("is a line that is no JSON object", report["errors"][0])

    def test_a_base_row_the_writer_cannot_read_stops_the_replay_not_the_check(self) -> None:
        # The base has a line that is no row, which the changes remove while adding a declaration: the working tree's
        # verdict stands, and the replay on the base's wiki, which the writer cannot read, makes the changes not the
        # sync's.
        links = self.root / "blueprint/links/Algebra.jsonl"
        kept = links.read_text()
        for line in ("not JSON", "[]"):
            links.write_text(kept + line + "\n")
            self.base = self.commit(f"a line that is no row: {line}")
            links.write_text(kept)
            self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
            self.assertEqual(self.run_sync()[0], 0)
            status, out, err, report = self.run_sync("--check")
            self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "other"), line)
            self.assertTrue(report["differences"][0].startswith("the sync stops on the base's wiki: "
                                                                 "blueprint/links/Algebra.jsonl:"), report["differences"])
            self.git("checkout", "-q", "--", ".")
            self.git("clean", "-qfd")


    def test_a_refresh_inside_nested_parts_leaves_the_outer_copy_as_it_was(self) -> None:
        # The outer copy of part-01 misses Old, which part-01 lists: drift the base had. A folder added inside part-02
        # refreshes part-02's copy on part-01's page, whose entries stay the same, so the outer page is left as it is.
        taxonomy = json.loads(json.dumps(self.TAXONOMY))
        taxonomy["placements"]["MathlibExt/Algebra/Rings"] = {"to": "Algebra/groups", "title": "Rings"}
        self.write("scripts/taxonomy.json", json.dumps(taxonomy))
        outer = self.write("blueprint/roadmap/Algebra/groups/README.md",
                           "# Groups\n\nGroups.\n\n- [Group basics](group-basics/README.md)\n\n"
                           "## [Part 1](part-01/README.md)\n\n"
                           "- [Cosets](part-01/cosets/README.md)\n- [Part 2](part-01/part-02/README.md)\n")
        inner = self.write("blueprint/roadmap/Algebra/groups/part-01/README.md",
                           "# Groups, part 1\n\n- [Cosets](cosets/README.md)\n- [Old](old/README.md)\n\n"
                           "## [Part 2](part-02/README.md)\n\n- [Fields](part-02/fields/README.md)\n")
        self.write("blueprint/roadmap/Algebra/groups/part-01/part-02/README.md",
                   "# Groups, part 2\n\n- [Fields](fields/README.md)\n")
        for folder in ("cosets", "old", "part-02/fields"):
            self.write(f"blueprint/roadmap/Algebra/groups/part-01/{folder}/README.md", f"# {folder}\n\nText.\n")
        self.base = self.commit("nested parts, the outer copy missing Old")
        kept = outer.read_bytes()
        self.write("MathlibExt/Algebra/Rings.lean", self.RINGS)
        status, out, err, report = self.run_sync()
        self.assertEqual(status, 0, (out, err))
        changed = self.git("status", "--porcelain")
        self.assertEqual(outer.read_bytes(), kept, changed)
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"], report["wiki_changes"]), (0, True, "sync"), report)
        before = self.tree()
        self.assertEqual(self.run_sync()[0], 0)
        self.assertEqual(self.tree(), before)

    def test_rows_lean_facts_wrote_are_found_whatever_ends_their_lines(self) -> None:
        # A links file whose lines end with bare carriage returns: a row carrying `status` stops the run all the same.
        links = self.root / "blueprint/links/Algebra.jsonl"
        rows = links.read_text().splitlines()
        row = json.loads(rows[-1])
        row["status"] = "stated"
        links.write_bytes("\r".join(rows[:-1] + [json.dumps(row)]).encode() + b"\r")
        self.groups(more="/-- A new result. -/\ntheorem fresh : True := trivial\n\n")
        status, out, err, report = self.run_sync("--check")
        self.assertEqual((status, report["in_step"]), (1, False))
        self.assertTrue([error for error in report["errors"] if "carries `kind` or `status`" in error], report["errors"])



INDEX_DIFFERS = sync.INDEX_DIFFERS


class BuildPath(Vault):
    """What the build's own steps refuse before they write, beside what credit_problems refuses everywhere."""

    def run_lean_facts(self, dependency_file: Path, registry_file: Path | None = None) -> tuple[int, str, bool]:
        files = lambda: {path: path.read_bytes() for path in sorted(wiki.VAULT.rglob("*")) if path.is_file()}
        before = files()
        with patch("sys.stdout", new_callable=io.StringIO), patch("sys.stderr", new_callable=io.StringIO) as err:
            code = sync.run_lean_facts(dependency_file, registry_file)
        return code, err.getvalue(), files() == before

    def test_no_credit_overrides_a_held_marker(self) -> None:
        # An editor held Local.vacuous back (as vacuous). A row that holds it back but credits it by a Lean link, one
        # that holds it back but credits a Mathlib declaration, and a page that links it while another holds it back
        # are refused by lean-facts before it writes anything, as by the extraction and the cards; so a held page is
        # never published proved. The held marker alone is fine.
        held = {"org.atlas-wiki": {"held": {"declaration": "Local.vacuous", "reason": "vacuous", "issue": 1}}}
        mathlib = {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "M.real", "module": "Mathlib.A"}}
        link = [{"location": {"declaration": "Local.vacuous"}}]
        cases = {
            "a Lean link": ([self.about("Algebra/h.md", object=link, extensions=held)],
                            "Algebra/h.md: it holds Local.vacuous back but is linked to Local.vacuous"),
            "Mathlib's credit": ([self.about("Algebra/h.md", object=[mathlib],
                                             extensions={**held, "org.autoform": {"mathlib": True}})],
                                 "Algebra/h.md: it holds Local.vacuous back but is linked to M.real"),
            "another page's link": ([self.about("Algebra/h.md", extensions=held),
                                     self.about("Algebra/p.md", object=link)],
                                    "Algebra/h.md: it holds Local.vacuous back, which Algebra/p.md links"),
            "the held marker alone": ([self.about("Algebra/h.md", extensions=held)], None),
        }
        self.page("Algebra/README.md", "# Algebra\n\n- [H](h.md)\n- [P](p.md)\n")
        self.page("Algebra/h.md", "# H\n\nThe source's statement.\n")
        self.page("Algebra/p.md", "# P\n\nA statement.\n")
        dependency_file = self.tmp / "lean-dependencies.json"
        dependency_file.write_text(json.dumps({"missing_articles": {}, "articles": {
            "Local.vacuous": {"module": "Local", "statement": [], "proof": []}}}))
        for case, (rows, message) in cases.items():
            with self.subTest(case=case):
                rows = [self.about("Algebra/README.md"), *rows]
                if not any(sync.subject_path(row).name == "p.md" for row in rows):
                    rows.append(self.about("Algebra/p.md"))
                self.annotate(rows)
                self.assertEqual(sync.held_conflicts(sync.read_annotations()), [message] if message else [])
                if message:
                    code, err, unchanged = self.run_lean_facts(dependency_file)
                    self.assertEqual((code, unchanged), (1, True))
                    self.assertIn(message, err)
                    with patch.object(extract, "BLUEPRINT", wiki.VAULT), self.assertRaises(ValueError) as raised:
                        extract.article_manifest()
                    self.assertIn(message, str(raised.exception))

    def test_the_extraction_refuses_a_duplicates_list_it_cannot_use(self) -> None:
        # The extraction reads the lists beside the articles and refuses, before writing, one that would count a use
        # for no article or for two (the problems sync_wiki.duplicate_markers finds without the Lean index).
        self.page("Algebra/README.md", "# Algebra\n\n- [P](p.md)\n- [Q](q.md)\n")
        self.page("Algebra/p.md", "# P\n\nA statement.\n")
        self.page("Algebra/q.md", "# Q\n\nThe source's statement.\n")
        listed = {"org.atlas-wiki": {"duplicates": ["Local.p_again"]}}
        p = self.about("Algebra/p.md", object=[{"location": {"declaration": "Local.p"}}], extensions=listed)
        self.annotate([self.about("Algebra/README.md"), p, self.about("Algebra/q.md")])
        with patch.object(extract, "BLUEPRINT", wiki.VAULT):
            self.assertEqual(extract.article_aliases(), {"Local.p_again": "Local.p"})
            self.annotate([self.about("Algebra/README.md"), p, self.about("Algebra/q.md", extensions=listed)])
            with self.assertRaises(ValueError) as raised:
                extract.article_aliases()
        self.assertIn("Algebra/q.md: it lists duplicates but credits no declaration of this project by a Lean link of "
                      "its own", str(raised.exception))
        self.assertIn("Algebra/q.md: it lists Local.p_again as a duplicate, as Algebra/p.md does",
                      str(raised.exception))

    def test_a_list_on_a_row_whose_declaration_only_the_defaults_give_stops_every_reader(self) -> None:
        # The links folder's defaults name Local.p, so the row `object: [{}]` credits it as Autoform reads it, by no
        # link of its own, and so does a row whose end with role `states` takes Local.p from the defaults while another
        # end, with role `uses` or with no role, names it as a reference, in either order. Its duplicates list is
        # refused before anything is written by each reader of the lists: the v2 extraction, the Mathlib layer's
        # bridge, which reads them as the extraction does, and a registry's check (sync_wiki.registry_problems), which
        # lean-facts and the cards run. With a link of its own, beside an inherited reference too, the list is read.
        from scripts import extract_mathlib_graph as graph
        from scripts.test_extract_mathlib_graph import row as dump_row, write_dump

        self.page("Algebra/README.md", "# Algebra\n\n- [P](p.md)\n")
        self.page("Algebra/p.md", "# P\n\nA statement.\n")
        self.links_folder()
        (sync.LINKS / "_defaults.json").write_text(json.dumps(
            {"object": {**sync.DEFAULTS["object"], "location": {"declaration": "Local.p"}}}) + "\n")
        listed = {"org.atlas-wiki": {"duplicates": ["Local.p_again"]}}
        problem = ("Algebra/p.md: it lists duplicates but credits no declaration of this project by a Lean link of "
                   "its own")
        registry = {"left_out": {}, "bridges": {}, "mathlib": {}, "missing": [], "project": [], "mutual": [],
                    "inputs": {"names_sha256": hashlib.sha256(b"").hexdigest(), "dump_sha256": "d" * 64,
                               "mathlib_rev": None, "requested": 0,
                               "aliases_sha256": extract.aliases_digest({"Local.p_again": "Local.p"}),
                               "format": sync.REGISTRY_FORMAT}}
        dump, output, out = self.tmp / "dump.jsonl", self.tmp / "lean-dependencies.json", self.tmp / "bridge"
        dump.write_text(json.dumps({"name": "Local.p", "module": "Local", "kind": "theorem", "private": False,
                                    "doc": True, "type": [], "value": []}) + "\n")
        bridge = ["bridge", str(write_dump(self.tmp, [dump_row("Local.p", module="Local")], "v2.jsonl.gz")), str(out),
                  "--mathlib-dump", str(write_dump(self.tmp, [dump_row("X")], "mathlib.jsonl.gz"))]
        named = {"location": {"declaration": "Local.p"}}
        for ends, refused in (([{}], True), ([{"role": "states"}, {"role": "uses", **named}], True),
                              ([{"role": "uses", **named}, {"role": "states"}], True),
                              ([{"role": "states"}, named], True), ([named], False),
                              ([{"role": "uses"}, {"role": "states", **named}], False)):
            with self.subTest(ends=ends), patch.object(extract, "BLUEPRINT", wiki.VAULT), \
                    patch.object(graph.v2, "article_manifest", extract.article_manifest), \
                    patch.object(graph.v2, "article_aliases", extract.article_aliases):
                self.annotate([self.about("Algebra/README.md", object=[]),
                               self.about("Algebra/p.md", object=ends, extensions=listed)])
                self.assertEqual(sync.page_owner(sync.read_annotations()[sync.LINKS / "Algebra.jsonl"][1])[:2],
                                 ("atlas", "Local.p"))
                self.assertEqual(sync.registry_problems(registry, sync.read_annotations()),
                                 [problem] if refused else [])
                if not refused:
                    self.assertEqual(extract.article_aliases(), {"Local.p_again": "Local.p"})
                    continue
                with self.assertRaises(ValueError) as raised:
                    extract.article_aliases()
                self.assertIn(problem, str(raised.exception))
                with patch("sys.argv", ["extract", str(dump), str(output)]), \
                        redirect_stderr(io.StringIO()) as errors, redirect_stdout(io.StringIO()):
                    self.assertEqual(extract.main(), 1)
                self.assertIn(problem, errors.getvalue())
                with redirect_stderr(io.StringIO()), redirect_stdout(io.StringIO()), \
                        self.assertRaises(SystemExit) as raised:
                    graph.main(bridge)
                self.assertIn(problem, str(raised.exception.code))
                self.assertEqual((output.exists(), out.exists()), (False, False))

    def test_lean_facts_names_a_duplicates_entry_the_lean_left_stale(self) -> None:
        # The Lean deleted Ext.gone, which Lagrange's row lists: lean-facts writes the page's facts and warns.
        (wiki.ROOT / "Ext").mkdir()
        (wiki.ROOT / "Ext" / "Groups.lean").write_text("namespace Ext\n\ntheorem lagrange : True := trivial\n\n"
                                                       "end Ext\n")
        self.page("Algebra/README.md", "# Algebra\n\n- [Lagrange](lagrange.md)\n")
        self.page("Algebra/lagrange.md", "# Lagrange\n\nA statement.\n")
        self.annotate([self.about("Algebra/README.md"),
                       self.about("Algebra/lagrange.md", object=[{"location": {"declaration": "Ext.lagrange"}}],
                                  extensions={"org.atlas-wiki": {"duplicates": ["Ext.gone"]}})])
        dependency_file = self.tmp / "lean-dependencies.json"
        dependency_file.write_text(json.dumps({"missing_articles": {}, "articles": {
            "Ext.lagrange": {"module": "Ext.Groups", "statement": [], "proof": []}}}))
        with patch("sys.stdout", new_callable=io.StringIO), patch("sys.stderr", new_callable=io.StringIO) as err:
            self.assertEqual(sync.run_lean_facts(dependency_file), 0)
        self.assertIn("warning: the duplicates entry Ext.gone (Algebra/lagrange.md): the Lean index does not resolve "
                      "it; drop the entry from `duplicates`", err.getvalue())

    def test_the_extraction_counts_a_duplicate_only_as_a_compiled_article(self) -> None:
        # Lagrange's row lists Ext.backlog as a duplicate. The extraction writes nothing when the dump lacks a row for
        # one of them that the Lean sources declare, as a use of Ext.backlog would then follow its own body, and when a
        # page an earlier sync wrote with a module and a name stands for Ext.backlog. One the Lean no longer declares
        # fails no build: the extraction warns, and a page that uses only Ext.backlog depends on no page through it
        # while Ext.lagrange is gone. With both rows, it depends on Lagrange's, and Lagrange's proof, which uses its
        # duplicate, depends on Ext.other, which the duplicate's body uses.
        (wiki.ROOT / "Ext").mkdir()
        self.page("Algebra/README.md", "# Algebra\n\n" + "".join(f"- [{n}]({n}.md)\n" for n in ("lagrange", "uses",
                                                                                                "other", "old")))
        for name in ("lagrange", "uses", "other", "old"):
            self.page(f"Algebra/{name}.md", f"# {name}\n\nA statement.\n")
        rows = [self.about("Algebra/README.md"),
                self.about("Algebra/lagrange.md", object=[{"location": {"declaration": "Ext.lagrange"}}],
                           extensions={"org.atlas-wiki": {"duplicates": ["Ext.backlog"]}}),
                self.about("Algebra/uses.md", object=[{"location": {"declaration": "Ext.uses"}}]),
                self.about("Algebra/other.md", object=[{"location": {"declaration": "Ext.other"}}])]
        plain = rows + [self.about("Algebra/old.md")]
        legacy = rows + [self.about("Algebra/old.md",
                                    extensions={"org.atlas-wiki": {"module": "Ext.Groups", "name": "backlog"}})]
        compiled = lambda name, kind, type_uses, value_uses: {"name": name, "module": "Ext.Groups", "kind": kind,
                                                               "private": False, "doc": True, "type": type_uses,
                                                               "value": value_uses}
        uses = [compiled("Ext.uses", "theorem", ["Ext.backlog"], []), compiled("Ext.backlog", "def", [], ["Ext.other"]),
                compiled("Ext.other", "def", [], [])]
        lagrange = compiled("Ext.lagrange", "theorem", [], ["Ext.backlog"])
        unused = [compiled("Ext.uses", "theorem", [], []), compiled("Ext.other", "def", [], []), lagrange]
        message = "the wiki lists Ext.backlog as a duplicate of Ext.lagrange, but "
        cases = {
            "the article the Lean declares, which the dump lacks": (
                plain, ("backlog", "lagrange"), uses,
                f"error: {message}the compiled dependency dump has no row for Ext.lagrange, and the Lean sources "
                "declare it"),
            "the duplicate the Lean declares, which the dump lacks": (
                plain, ("backlog", "lagrange"), unused,
                f"error: {message}the compiled dependency dump has no row for Ext.backlog, and the Lean sources "
                "declare it"),
            "a page standing for the duplicate": (legacy, ("backlog", "lagrange"), [*uses, lagrange],
                                                  f"error: {message}a page stands for Ext.backlog"),
            "the article the Lean no longer declares": (
                plain, ("backlog",), uses, "warning: the Lean no longer declares Ext.lagrange, whose page lists "
                                           "Ext.backlog as a duplicate"),
            "the duplicate the Lean no longer declares": (
                plain, ("lagrange",), unused, "warning: the Lean no longer declares Ext.backlog, which the wiki lists "
                                              "as a duplicate of Ext.lagrange"),
            "both compiled": (plain, ("backlog", "lagrange"), [*uses, lagrange], None),
        }
        for case, (annotations, theorems, dumped, message) in cases.items():
            with self.subTest(case=case), patch.object(extract, "BLUEPRINT", wiki.VAULT):
                (wiki.ROOT / "Ext" / "Groups.lean").write_text(
                    "namespace Ext\n\n" + "".join(f"theorem {name} : True := trivial\n\n" for name in theorems)
                    + "end Ext\n")
                self.annotate(annotations)
                dump, output = self.tmp / "dump.jsonl", self.tmp / "lean-dependencies.json"
                output.unlink(missing_ok=True)
                dump.write_text("".join(json.dumps(r) + "\n" for r in dumped))
                with patch("sys.argv", ["extract", str(dump), str(output)]), \
                        redirect_stderr(io.StringIO()) as errors, redirect_stdout(io.StringIO()):
                    code = extract.main()
                if message and message.startswith("error"):
                    self.assertEqual((code, output.exists()), (1, False))
                    self.assertIn(message, errors.getvalue())
                    continue
                self.assertEqual(code, 0, errors.getvalue())
                self.assertIn(message or "", errors.getvalue())
                articles = json.loads(output.read_text())["articles"]
                expected = {"both compiled": ["Ext.lagrange"], "the article the Lean no longer declares": [],
                            "the duplicate the Lean no longer declares": []}[case]
                self.assertEqual(articles["Ext.uses"]["statement"], expected)
                if "Ext.lagrange" in articles:
                    self.assertEqual(articles["Ext.lagrange"]["proof"],
                                     ["Ext.other"] if case == "both compiled" else [])

    def test_a_folder_page_credits_nothing(self) -> None:
        # A folder page's row that credits a Mathlib declaration (Autoform would show the folder in Mathlib, with no
        # check of the name) or a declaration of this project, or that has `kind` or `status`, is refused by every
        # step, mathlib-names and lean-facts among them.
        mathlib = {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "Does.not.exist",
                                                                    "module": "Mathlib.A"}}
        cases = {
            "Mathlib's credit": ({"object": [mathlib], "extensions": {"org.autoform": {"mathlib": True}}},
                                 "Algebra/README.md is a folder page, which credits no declaration, but its row "
                                 "credits Does.not.exist"),
            "a declaration of this project": ({"object": [{"location": {"declaration": "Ext.t"}}]},
                                              "Algebra/README.md is a folder page, which credits no declaration, but "
                                              "its row credits Ext.t"),
            "facts": ({"status": "formalized"}, "Algebra/README.md is a folder page, but its row has `kind` or "
                                                "`status`, which lean-facts writes on statement pages only"),
        }
        self.page("Algebra/README.md", "# Algebra\n\n- [T](t.md)\n")
        self.page("Algebra/t.md", "# T\n\nA statement.\n")
        dependency_file = self.tmp / "lean-dependencies.json"
        dependency_file.write_text(json.dumps({"missing_articles": {}, "articles": {}}))
        for case, (fields, message) in cases.items():
            with self.subTest(case=case):
                self.annotate([self.about("Algebra/README.md", **fields), self.about("Algebra/t.md")])
                self.assertIn(message, sync.credit_problems(sync.read_annotations()))
                code, err, unchanged = self.run_lean_facts(dependency_file)
                self.assertEqual((code, unchanged), (1, True))
                self.assertIn(message, err)
                with patch("sys.stdout", new_callable=io.StringIO), patch("sys.stderr", new_callable=io.StringIO):
                    self.assertEqual(sync.run_mathlib_names(self.tmp / "names.txt"), 1)

    def test_a_row_whose_page_is_gone_is_refused_for_what_it_is(self) -> None:
        # The page was deleted, its row kept: lean-facts and the extraction say so, rather than take the extraction
        # for stale.
        self.page("Algebra/README.md", "# Algebra\n")
        self.annotate([self.about("Algebra/README.md"),
                       self.about("Algebra/gone.md", object=[{"location": {"declaration": "Local.gone"}}])])
        dependency_file = self.tmp / "lean-dependencies.json"
        dependency_file.write_text(json.dumps({"missing_articles": {}, "articles": {}}))
        message = "Algebra/gone.md: its row names a page that does not exist; remove the row or restore the page"
        code, err, unchanged = self.run_lean_facts(dependency_file)
        self.assertEqual((code, unchanged), (1, True))
        self.assertIn(message, err)
        self.assertNotIn("another state of the wiki", err)
        with patch.object(extract, "BLUEPRINT", wiki.VAULT), self.assertRaises(ValueError) as raised:
            extract.article_manifest()
        self.assertIn(message, str(raised.exception))

    def test_rows_split_into_lines_as_autoform_splits_them(self) -> None:
        # A string may hold U+2028 or another line separator: the row stays one row, read and written back.
        self.page("Algebra/README.md", "# Algebra\n")
        text = json.dumps(self.about("Algebra/README.md", note="one\u2028two\u0085three"), ensure_ascii=False) + "\n"
        self.links_folder()
        (sync.LINKS / "Algebra.jsonl").write_text(text, encoding="utf-8")
        rows = sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]
        self.assertEqual([row["note"] for row in rows], ["one\u2028two\u0085three"])
        sync.write_annotations(sync.read_annotations())
        self.assertEqual(sync.read_annotations()[sync.LINKS / "Algebra.jsonl"], rows)
        self.assertEqual(sync.read_rows("{\"a\": 1}\r\n{\"a\": 2}\r{\"a\": 3}\n"), [{"a": 1}, {"a": 2}, {"a": 3}])

    def test_the_registry_is_valid_only_with_its_own_extraction(self) -> None:
        # The extractor records the digest of the extraction it wrote beside the registry: lean-facts refuses a
        # registry made with another extraction before it writes anything.
        self.page("Algebra/README.md", "# Algebra\n")
        self.annotate([self.about("Algebra/README.md")])
        dependency_file, registry_file = self.tmp / "lean-dependencies.json", self.tmp / "mathlib-registry.json"
        dependency_file.write_text(json.dumps({"missing_articles": {}, "articles": {}}))
        registry = {"bridges": {}, "left_out": {}, "mathlib": {}, "missing": [], "project": [],
                    "inputs": {"names_sha256": hashlib.sha256(b"").hexdigest(), "dump_sha256": "d" * 64,
                               "mathlib_rev": sync.mathlib_revision(), "requested": 0,
                               "aliases_sha256": duplicates_digest(), "format": sync.REGISTRY_FORMAT}}
        for extraction, code in (("e" * 64, 1), (hashlib.sha256(dependency_file.read_bytes()).hexdigest(), 0)):
            with self.subTest(code=code):
                registry_file.write_text(json.dumps({**registry, "inputs": {**registry["inputs"],
                                                                            "extraction_sha256": extraction}}))
                found, err, _ = self.run_lean_facts(dependency_file, registry_file)
                self.assertEqual(found, code, err)
                if code:
                    self.assertIn(f"the registry was not made with {dependency_file}", err)

    def test_mathlib_names_writes_a_file_of_its_own(self) -> None:
        # Its output is no links file, by its path or a link, no symbolic link, and nothing inside blueprint/ (the
        # defaults file, a page): refused before anything is written.
        self.page("Algebra/README.md", "# Algebra\n")
        self.annotate([self.about("Algebra/README.md")])
        links = sync.LINKS / "Algebra.jsonl"
        before = {path: path.read_bytes() for path in wiki.VAULT.rglob("*") if path.is_file()}
        (self.tmp / "alias.txt").symlink_to(links)
        for output in (links, self.tmp / "alias.txt", sync.LINKS / "_defaults.json",
                       wiki.ROADMAP / "Algebra" / "new.md"):
            with self.subTest(output=output.name), patch("sys.stdout", new_callable=io.StringIO), \
                    patch("sys.stderr", new_callable=io.StringIO):
                self.assertEqual(sync.run_mathlib_names(output), 2)
            self.assertEqual({path: path.read_bytes() for path in wiki.VAULT.rglob("*") if path.is_file()}, before)
        with patch("sys.stdout", new_callable=io.StringIO):
            self.assertEqual(sync.run_mathlib_names(self.tmp / "names.txt"), 0)
        self.assertEqual((self.tmp / "names.txt").read_text(), "")


class CleanCheckout(Vault):
    """lean-facts runs only on blueprint/ as committed, never on its own output; the commands that write committed rows
    refuse rows it synced."""

    def git(self, *argv: str) -> None:
        import subprocess
        subprocess.run(["git", "-C", str(self.tmp), *argv], check=True, capture_output=True)

    def lean_facts(self, dependency_file: Path) -> tuple[int, str]:
        with patch.object(sync, "checkout_problem", CHECKOUT_PROBLEM), patch("sys.stdout", new_callable=io.StringIO), \
                patch("sys.stderr", new_callable=io.StringIO) as err:
            return sync.run_lean_facts(dependency_file), err.getvalue()

    def test_lean_facts_runs_only_on_a_clean_checkout(self) -> None:
        # Outside Git, refused; on a clean checkout, it runs and writes the page's facts; on its own output, or with
        # an untracked file in blueprint/, refused before it writes anything; restored, it runs again.
        (self.tmp / "Ext.lean").write_text("namespace Ext\ntheorem t : True := trivial\nend Ext\n")
        self.page("Algebra/README.md", "# Algebra\n\n- [T](t.md)\n")
        self.page("Algebra/t.md", "# T\n\nA theorem.\n")
        self.annotate([self.about("Algebra/README.md"), self.about("Algebra/t.md",
                                                                   object=[{"location": {"declaration": "Ext.t"}}])])
        dependency_file = self.tmp / "build" / "lean-dependencies.json"
        dependency_file.parent.mkdir()
        dependency_file.write_text(json.dumps({"missing_articles": {}, "articles": {
            "Ext.t": {"module": "Ext", "statement": [], "proof": []}}}))
        code, err = self.lean_facts(dependency_file)
        self.assertEqual(code, 1)
        self.assertIn("is not a Git checkout; lean-facts runs on a clean checkout of the wiki", err)
        self.git("init", "-q")
        self.git("add", "blueprint", "Ext.lean")
        self.git("-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "vault")
        self.assertEqual(self.lean_facts(dependency_file), (0, ""))
        written = {path: path.read_bytes() for path in wiki.VAULT.rglob("*") if path.is_file()}
        self.assertIn(b'"kind": "theorem"', (sync.LINKS / "Algebra.jsonl").read_bytes())
        code, err = self.lean_facts(dependency_file)
        self.assertEqual(code, 1)
        self.assertIn("blueprint/ is not as committed", err)
        self.assertIn("run the build in a fresh disposable checkout or worktree", err)
        self.assertIn("`git restore --source=HEAD --staged --worktree -- blueprint`", err)
        self.assertEqual({path: path.read_bytes() for path in wiki.VAULT.rglob("*") if path.is_file()}, written)
        # The restore the error advises, in this disposable checkout.
        self.git("restore", "--source=HEAD", "--staged", "--worktree", "--", "blueprint")
        draft = wiki.ROADMAP / "Algebra" / "draft.md"
        draft.write_text("# Draft\n")
        code, err = self.lean_facts(dependency_file)
        self.assertEqual(code, 1)
        self.assertIn("first blueprint/roadmap/Algebra/draft.md", err)
        draft.unlink()  # an untracked file, reviewed and removed
        self.assertEqual(self.lean_facts(dependency_file), (0, ""))

    def test_commands_that_write_committed_rows_refuse_rows_lean_facts_synced(self) -> None:
        # declarations and ids would commit what lean-facts derived (kind and status, unlinked rows): both refuse,
        # writing nothing, whether run from the command line or called.
        self.page("Algebra/README.md", "# Algebra\n\n- [T](t.md)\n")
        self.page("Algebra/t.md", "# T\n\nA theorem.\n")
        self.annotate([self.about("Algebra/README.md", id="af_000000000000000000000001"),
                       self.about("Algebra/t.md", id="af_000000000000000000000002",
                                  object=[{"location": {"declaration": "Ext.t"}}], kind="theorem")])
        message = "Algebra.jsonl, line 2: the row carries `kind` or `status`, which lean-facts writes at build time"
        before = (sync.LINKS / "Algebra.jsonl").read_bytes()
        report = sync.apply_declarations([], SimpleNamespace(declarations={"Ext.t": None}))
        self.assertTrue(any(problem.startswith(message) for problem in report["credit_problems"]))
        self.assertEqual(sync.apply_ids()[1], [problem for problem in sync.synced_rows()])
        self.assertTrue(sync.synced_rows()[0].startswith(message))
        with patch("sys.stdout", new_callable=io.StringIO), patch("sys.stderr", new_callable=io.StringIO) as err:
            self.assertEqual(sync.main(["ids"]), 1)
        self.assertIn(message, err.getvalue())
        self.assertEqual((sync.LINKS / "Algebra.jsonl").read_bytes(), before)


class CommittedAnnotations(unittest.TestCase):
    def test_every_annotation_has_an_id_of_its_own(self) -> None:
        # What the tools own (docs/BLUEPRINT.md): declarations gives an id to each annotation it adds, and ids to
        # any other row.
        without, problems = sync.apply_ids(write=False)
        self.assertEqual(problems, [])
        self.assertEqual(len(without), 0, f"annotations without an id, such as {without[:3]}: "
                                          "`python scripts/sync_wiki.py ids` gives them theirs")

    def test_every_kind_a_page_records_is_one_lean_facts_takes(self) -> None:
        # Writing pages (docs/BLUEPRINT.md): a page with no Lean link records one of the kinds lean-facts gives, which
        # lean-facts refuses otherwise (kind_problems); with the index, it also checks the kinds held pages record.
        self.assertEqual(sync.kind_problems(sync.read_annotations()), [])

    def test_no_committed_row_carries_what_lean_facts_writes(self) -> None:
        # What the tools own: `kind` and `status` are written at build time, never committed. lean-facts writes them
        # on every page it credits, so a links file it synced, its other derived edits included, fails here.
        self.assertEqual(sync.synced_rows(), [], "rows with `kind` or `status`, which lean-facts writes: run the build "
                                                 "in a disposable checkout, and commit none of its output")


class Titles(unittest.TestCase):
    def test_openings_are_compared_without_line_breaks(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "titles.jsonl"
            path.write_text(json.dumps({"file": "A.lean", "name": "f", "opening": "The  map\nf.", "title": "The map"}) + "\n")
            self.assertEqual(sync.load_titles(path), {("A.lean", "f"): [("The map", "The map f.")]})


if __name__ == "__main__":
    unittest.main()
