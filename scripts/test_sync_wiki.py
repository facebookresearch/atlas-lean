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
        declarations = {"Ext.lagrange": SimpleNamespace(keyword="theorem", path=Path("Ext/Groups.lean"))}
        dependencies = {"Ext.lagrange": {"module": "Ext.Groups", "statement": ["conjecture"], "proof": []},
                        "conjecture": {"module": "Ext.Groups", "statement": [], "proof": []}}
        counts, unlinked = sync.apply_lean_facts(SimpleNamespace(declarations=declarations), dependencies)
        self.assertEqual((counts, unlinked), ({"articles": 2, "unresolved": 0, "edges": 1}, []))
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
        # In source order: the targets' order here.
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         "# Groups\n\nProse.\n\n- [Old](old.md)\n- [New result](new.md)\n- [Wanted](wanted.md)\n")
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
        # A page's first item sits a blank line below the text above it.
        self.assertEqual((wiki.ROADMAP / "Algebra" / "README.md").read_text(), "# Algebra\n\n- [New result](new.md)\n")

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
        self.assertEqual(rows["Algebra/rings/README.md"], {"subject": [{"type": "generic", "uri": "../roadmap/Algebra/rings/README.md"}]})
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
