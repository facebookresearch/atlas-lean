"""The committed wiki keeps its own text, and lean-facts adds only what the Lean decides."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from scripts import generate_wiki as wiki
from scripts import sync_wiki as sync


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
        ]
        for one in patches:
            one.start()
            self.addCleanup(one.stop)

    def annotate(self, rows: list[dict]) -> None:
        sync.LINKS.mkdir(parents=True, exist_ok=True)
        sync.write_annotations({sync.LINKS / "Algebra.jsonl": rows})

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
            {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/conjecture.md"}],
             "extensions": {"org.atlas-wiki": {"module": "Ext.Groups", "name": "conjecture"}}},
            {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/lagrange.md"}],
             "object": [{"location": {"declaration": "Ext.lagrange"}}],
             "id": "af_000000000000000000000001",
             "extensions": {"org.autoform": {"origin": "cited"}}},
        ])


class LeanFacts(Vault):
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
        }
        dependencies = {
            "Ext.lagrange": {"module": "Ext.Groups", "statement": ["Ext.order", "Ext.lagrange"], "proof": ["conjecture", "Ext.order"]},
            "conjecture": {"module": "Ext.Groups", "statement": [], "proof": []},
        }
        counts, unlinked = sync.apply_lean_facts(SimpleNamespace(declarations=declarations), dependencies)
        self.assertEqual(counts, {"articles": 5, "unresolved": 0, "edges": 2})
        self.assertEqual(unlinked, [])
        rows = {sync.subject_path(row).name: row for row in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        facts = {name: (row.get("kind"), row.get("status")) for name, row in rows.items()}
        self.assertEqual(facts, {
            "README.md": (None, None),
            "lagrange.md": ("theorem", "formalized"),
            "order.md": ("def", "formalized"),
            "hard.md": ("theorem", "stated"),
            "partial.md": ("def", None),
            "conjecture.md": ("theorem", None),
        })
        self.assertEqual(
            lagrange.read_text(),
            "# Lagrange's theorem\n\nIt divides.\n\n## Depends on\n\n- [Order](order.md)\n\n"
            "## Proof depends on\n\n- [Conjecture](conjecture.md)\n\n## Sources\n\n- Book.\n",
        )
        self.assertEqual(order.read_text(), "# Order\n\nA number.\n\n## Depends on\n\nThis node has no prerequisites.\n")
        self.assertEqual(conjecture.read_text(), "# Conjecture\n\nOpen.\n\n## Depends on\n\nThis node has no prerequisites.\n")
        self.assertEqual((wiki.ROADMAP / "Algebra" / "README.md").read_text(), "# Algebra\n\n- [Order](order.md)\n")

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


def declaration(name: str | None, short: str, title: str, text: str, module=("Ext", "Groups")) -> wiki.Target:
    return wiki.Target(book="Ext", idx=0, title=title, slug=wiki.slugify(short), location="Algebra", description=text,
                       declaration="theorem", lean=name, statement=True, proof=True, names=[name or short], module=module,
                       path=wiki.ROADMAP / "Algebra" / "elsewhere" / f"{short}.md")


INDEX = SimpleNamespace(declarations={"Ext.old": None})


class Declarations(Vault):
    def test_new_declarations_get_pages_beside_their_module(self) -> None:
        self.page("Algebra/groups/README.md", "# Groups\n\nProse.\n\n- [Old](old.md)\n")
        old = self.page("Algebra/groups/old.md", "# Old, as the wiki wrote it\n\nEdited text.\n")
        self.page("Algebra/README.md", "# Algebra\n\n- [Groups](groups/README.md)\n")
        self.annotate([
            self.about("Algebra/groups/old.md", object=[{"location": {"declaration": "Ext.old"}}]),
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
        self.assertEqual(report["added"], [
            "Ext.Groups:wanted -> Algebra/groups/wanted.md",
            "Ext.new -> Algebra/groups/new.md",
            "Other.lone -> Algebra/lone.md",
        ])
        self.assertEqual(report["gone"], ["Ext.gone (Algebra/groups/gone.md)"])
        self.assertEqual(report["changed"], [])
        self.assertEqual(old.read_text(), "# Old, as the wiki wrote it\n\nEdited text.\n")
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "new.md").read_text(), "# New result\n\nA new statement.\n")
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         "# Groups\n\nProse.\n\n- [Old](old.md)\n- [Wanted](wanted.md)\n- [New result](new.md)\n")
        self.assertEqual((wiki.ROADMAP / "Algebra" / "README.md").read_text(),
                         "# Algebra\n\n- [Groups](groups/README.md)\n- [Lone](lone.md)\n")
        rows = {sync.subject_path(row).name: row for row in sync.read_annotations()[sync.LINKS / "Algebra.jsonl"]}
        self.assertEqual(rows["new.md"]["object"], [{"location": {"declaration": "Ext.new"}}])
        self.assertEqual(rows["new.md"]["extensions"], {"org.atlas-wiki": {"from": "docstring"}})
        self.assertEqual(rows["wanted.md"]["extensions"],
                         {"org.atlas-wiki": {"from": "docstring", "module": "Ext.Groups", "name": "wanted"}})

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

    def test_a_deprecated_declaration_gets_no_page(self) -> None:
        # A page the wiki dropped for a deprecated declaration must stay dropped.
        self.page("Algebra/README.md", "# Algebra\n")
        source = self.tmp / "Ext" / "Groups.lean"
        source.parent.mkdir(parents=True)
        source.write_text('/-- Old. -/\n@[deprecated Mathlib.old (since := "2026-11-09")]\ntheorem old : True := trivial\n'
                          '/-- Also old. -/\n@[simp, deprecated (since := "2026-11-09")] theorem older : True := trivial\n'
                          "/-- New. -/\n@[simp]\ntheorem new : True := trivial\n")
        sync.LINKS.mkdir(parents=True)
        targets = [declaration("Ext.old", "old", "Old", "Old."), declaration("Ext.older", "older", "Older", "Also old."),
                   declaration("Ext.new", "new", "New", "New.")]
        index = SimpleNamespace(declarations={"Ext.old": None, "Ext.older": None, "Ext.new": None})
        self.assertEqual(sync.apply_declarations(targets, index)["added"], ["Ext.new -> Algebra/new.md"])

    def test_a_docstring_edit_is_reported_from_the_second_run(self) -> None:
        self.page("Algebra/groups/README.md", "# Groups\n\n- [Old](old.md)\n")
        self.page("Algebra/groups/old.md", "# Old\n\nWiki text.\n")
        self.annotate([self.about("Algebra/groups/old.md", object=[{"location": {"declaration": "Ext.old"}}])])
        self.assertEqual(sync.apply_declarations([declaration("Ext.old", "old", "Old", "First.")], INDEX)["changed"], [])
        self.assertEqual(sync.apply_declarations([declaration("Ext.old", "old", "Old", "First.")], INDEX)["changed"], [])
        changed = sync.apply_declarations([declaration("Ext.old", "old", "Old", "Second.")], INDEX)["changed"]
        self.assertEqual(changed, ["Ext.old (Algebra/groups/old.md)"])
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "old.md").read_text(), "# Old\n\nWiki text.\n")


class Titles(unittest.TestCase):
    def test_openings_are_compared_without_line_breaks(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "titles.jsonl"
            path.write_text(json.dumps({"file": "A.lean", "name": "f", "opening": "The  map\nf.", "title": "The map"}) + "\n")
            self.assertEqual(sync.load_titles(path), {("A.lean", "f"): [("The map", "The map f.")]})


if __name__ == "__main__":
    unittest.main()
