"""The committed wiki keeps its own text, and lean-facts adds only what the Lean decides."""

from __future__ import annotations

import hashlib
import io
import json
import re
import shutil
import tempfile
import unittest
from contextlib import redirect_stderr
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
                              "format": sync.REGISTRY_FORMAT}
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
                              "format": sync.REGISTRY_FORMAT}
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
                          "dump_sha256": "d" * 64, "mathlib_rev": None, "requested": 3, "format": sync.REGISTRY_FORMAT}
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
                              "format": sync.REGISTRY_FORMAT}
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
                               "mathlib_rev": None, "requested": 0, "format": sync.REGISTRY_FORMAT}}
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
                           "format": sync.REGISTRY_FORMAT},
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
                               "mathlib_rev": None, "requested": 1, "format": sync.REGISTRY_FORMAT}}
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
            "private theorem helper : True := trivial\n")
        (self.tmp / "Ext" / "Groups.lean").write_text("theorem user : True := trivial\n")
        body = "# Claim\n\nThe source's statement.\n\n## Depends on\n\n- [Bad](bad.md)\n"
        claim = self.page("Algebra/claim.md", body)
        for name in ("bad", "vacuous", "helper", "missing"):
            self.page(f"Algebra/{name}.md", f"# {name}\n\nHeld.\n")
        user = self.page("Algebra/user.md", "# User\n\nUses the helper.\n")

        def held(name: str, reason: str, issue: int | None = 1) -> dict:
            return {sync.OWN: {"held": {"declaration": name, "reason": reason, **({"issue": issue} if issue else {})}}}

        self.annotate([
            self.about("Algebra/claim.md", extensions=held("Ext.false_claim", "false")),
            self.about("Algebra/bad.md", status="formalized", extensions=held("Ext.bad", "mis-specified")),
            self.about("Algebra/vacuous.md", extensions=held("Ext.vacuous", "vacuous")),
            self.about("Algebra/helper.md", extensions=held("Ext.helper", "private by design", None)),
            self.about("Algebra/missing.md", extensions=held("Ext.missing", "false")),
            self.about("Algebra/user.md", object=[{"location": {"declaration": "Ext.user"}}]),
        ])
        held_source, source = Path("Ext/Held.lean"), Path("Ext/Groups.lean")
        index = SimpleNamespace(declarations={
            "Ext.false_claim": SimpleNamespace(keyword="theorem", path=held_source),
            "Ext.bad": SimpleNamespace(keyword="def", path=held_source),
            "Ext.vacuous": SimpleNamespace(keyword="theorem_wanted", path=held_source),
            "Ext.helper": SimpleNamespace(keyword="theorem", path=held_source),
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
                "missing.md": (None, None, False), "user.md": ("theorem", "formalized", True)})
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
        # annotation records under OWN when it is a kind lean-facts gives linked pages; a linked page takes the Lean's.
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
                                         "held", "held_problems", "unassigned")}
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
                               "mathlib_rev": sync.mathlib_revision(), "requested": 0, "format": sync.REGISTRY_FORMAT}}
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
