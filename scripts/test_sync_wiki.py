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
        # copy; another item, an editor's paragraph and a comment there stay.
        groups = wiki.ROADMAP / "Algebra" / "groups"
        part_one = ("## [Part 1 of 2](part-01/README.md)\n\n<!-- Keep this part in the book's order. -->\n\n"
                    "- [Introduction](introduction.md)\n- [A](part-01/a.md)\n\nThe first part follows the book.\n\n")
        self.page("Algebra/groups/README.md", f"# Groups\n\n{part_one}## [Part 2 of 2](part-02/README.md)\n\n- [B](part-02/b.md)\n")
        self.page("Algebra/groups/part-01/README.md", "# Part 1 of 2\n\n- [A](a.md)\n")
        self.page("Algebra/groups/part-02/README.md", "# Part 2 of 2\n\n- [B](b.md)\n- [C](c.md)\n")
        sync.LINKS.mkdir(parents=True)
        sync.apply_declarations([], SimpleNamespace(declarations={}))
        self.assertEqual((groups / "README.md").read_text(),
                         f"# Groups\n\n{part_one}## [Part 2 of 2](part-02/README.md)\n\n- [B](part-02/b.md)\n- [C](part-02/c.md)\n")

    def test_a_part_list_rebases_every_link_of_an_item(self) -> None:
        self.page("Algebra/groups/README.md", "# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n- [A](part-01/a.md)\n")
        self.page("Algebra/groups/part-01/README.md",
                  "# Part 1 of 1\n\n- [A](a.md) — see [B](b.md), [Rings](../../rings/README.md) and [a book](https://example.org)\n")
        sync.LINKS.mkdir(parents=True)
        sync.apply_declarations([], SimpleNamespace(declarations={}))
        self.assertEqual((wiki.ROADMAP / "Algebra" / "groups" / "README.md").read_text(),
                         "# Groups\n\n## [Part 1 of 1](part-01/README.md)\n\n- [A](part-01/a.md) — see [B](part-01/b.md), "
                         "[Rings](../rings/README.md) and [a book](https://example.org)\n")

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
