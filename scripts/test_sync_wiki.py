"""The committed wiki keeps its own text, and lean-facts adds only what the Lean decides."""

from __future__ import annotations

import io
import json
import shutil
import tempfile
import unittest
from contextlib import redirect_stderr
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
            self.assertEqual(counts, {"articles": 0, "unresolved": 1, "edges": 0})
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
        self.assertEqual(counts, {"articles": 2, "unresolved": 0, "edges": 1})
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
            with patch.dict("sys.modules", {"autoform_cli": SimpleNamespace(lean=lean), "autoform_cli.lean": lean}), \
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
        self.page("Algebra/README.md", "# Algebra\n\n" + "".join(f"- [{n.upper()}]({n}.md)\n" for n in "abcdefgh"))
        for name in "abcdefgh":
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
                                         "held", "held_problems")}
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
        source = self.tmp / "MathlibExt" / "Algebra" / "Wanted.lean"
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text("/-- A wish. -/\ntheorem_wanted wish : True\n")
        page = self.page("Algebra/wish.md", "# Wish\n\nA wish.\n\n## Depends on\n\nThis node has no prerequisites.\n")
        self.annotate([self.about("Algebra/wish.md", extensions={"org.atlas-wiki": {"module": "MathlibExt.Algebra.Wanted", "name": "wish"}})])
        index = SimpleNamespace(declarations={"MathlibExt.wish": SimpleNamespace(
            path=Path("MathlibExt/Algebra/Wanted.lean"), line=2, keyword="theorem_wanted")})
        counts, _ = sync.apply_lean_facts(index, {})
        self.assertEqual(counts["articles"], 1)
        self.assertEqual(page.read_text(), "# Wish\n\nA wish.\n")

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


class Titles(unittest.TestCase):
    def test_openings_are_compared_without_line_breaks(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "titles.jsonl"
            path.write_text(json.dumps({"file": "A.lean", "name": "f", "opening": "The  map\nf.", "title": "The map"}) + "\n")
            self.assertEqual(sync.load_titles(path), {("A.lean", "f"): [("The map", "The map f.")]})


if __name__ == "__main__":
    unittest.main()
