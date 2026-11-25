"""Cards group statement pages for readers; their edges are derived from the statements, with typed witnesses."""

from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import io
import json
import os
import random
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import cards
from scripts import generate_wiki as wiki

THEOREM = {"kind": "theorem", "status": "formalized"}
DEFINITION = {"kind": "def", "status": "formalized"}
COMMIT = "c7df2d47c165e81f305e67eb4263db54d516aae9"


def af(number: int) -> str:
    return f"af_{number:024x}"


def walk(edge: dict) -> list[str]:
    steps = edge.get("statement_walk") or edge["walk"]
    return [steps[0]["source"], *(step["target"] for step in steps)]


def load_hook():
    """hooks/card_pages.py, which MkDocs loads by path rather than as a package module."""
    spec = importlib.util.spec_from_file_location("atlas_hook_card_pages_for_cards",
                                                  Path(__file__).resolve().parents[1] / "hooks" / "card_pages.py")
    hook = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = hook
    spec.loader.exec_module(hook)
    return hook


def site_index(hook) -> dict:
    """Render's search index of the vault: a statement with a declaration kind boxed on its folder's page, any
    other one a page of its own, and each folder its page."""
    annotations = cards.read_annotations()
    entries = []
    for page in sorted(wiki.ROADMAP.rglob("*.md")):
        node = cards.node_id(page)
        if page.name == "README.md":
            route = "../roadmap/index.html" if node == "roadmap" else f"../roadmap/{node}/index.html"
            entries.append({"id": node, "kind": "scope", "route": route, "title": node})
        elif annotations.get(page.resolve(), {}).get("kind"):
            route = f"../roadmap/{node.rsplit('/', 1)[0]}/index.html#{page.stem}"
            entries.append({"id": node, "kind": "node", "route": route, "title": page.stem})
        else:
            entries.append({"id": node, "kind": "node", "route": f"../roadmap/{node}.html", "title": page.stem})
    return {"schema": hook.INDEX_SCHEMA, "nodes": entries}


class Vault(unittest.TestCase):
    """A small blueprint/ the scripts' paths point into, laid out as lean-facts leaves the build's checkout."""

    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, self.tmp)
        vault = self.tmp / "blueprint"
        for one in (patch.object(wiki, "ROOT", self.tmp), patch.object(wiki, "VAULT", vault),
                    patch.object(wiki, "ROADMAP", vault / "roadmap"),
                    patch.object(cards.sync, "LINKS", vault / "links")):
            one.start()
            self.addCleanup(one.stop)
        self.rows: list[dict] = []
        # The extraction lean-facts would write these pages from: declaration -> typed dependencies.
        self.articles: dict[str, dict[str, list[str]]] = {}
        (vault / "links").mkdir(parents=True)
        (self.tmp / "scripts").mkdir()
        (vault / "links" / "_defaults.json").write_text('{"object": {"type": "lean", "uri": "../.."}}\n')
        self.folder("README.md", "Roadmap", ["Algebra/README.md"])
        self.folder("Algebra/README.md", "Algebra", ["groups/README.md"])
        self.folder("Algebra/groups/README.md", "Groups", [])

    def page(self, relative: str, text: str, row: dict | None = None) -> None:
        path = wiki.ROADMAP / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        self.rows.append({"subject": [{"type": "generic", "uri": f"../roadmap/{relative}"}], **(row or {})})

    def folder(self, relative: str, title: str, children: list[str], row: dict | None = None) -> None:
        self.page(relative, f"# {title}\n\n" + "".join(f"- [{child}]({child})\n" for child in children), row)

    def leaf(self, relative: str, number: int, facts: dict | None = THEOREM, statement: tuple[str, ...] = (),
             proof: tuple[str, ...] = (), row: dict | None = None) -> None:
        """A statement page with the sections lean-facts writes; ``facts`` None makes it a page-only (planned) page,
        whose sections are its author's."""
        here = Path(relative).parent
        text = f"# {Path(relative).stem}\n\nA statement.\n"

        def link(target: str) -> str:
            return f"- [{Path(target).stem}]({Path('/'.join(['..'] * len(here.parts)), target).as_posix()})"

        if statement or facts is not None:
            text += "\n## Depends on\n\n" + ("\n".join(link(t) for t in statement) or "This node has no prerequisites.") + "\n"
        if proof:
            text += "\n## Proof depends on\n\n" + "\n".join(link(t) for t in proof) + "\n"
        fields = {"id": af(number), **(row or {})}
        if facts is not None:
            fields.update(object=[{"location": {"declaration": self.name(relative)}}], **facts)
            self.articles[self.name(relative)] = {"statement": [self.name(t) for t in statement],
                                                  "proof": [self.name(t) for t in proof]}
        self.page(relative, text, fields)

    @staticmethod
    def name(relative: str) -> str:
        return f"Ext.{Path(relative).stem.replace('-', '_')}"

    def card(self, folder: str, number: int, main: int, members: list[str], kind: str = "result",
             body: str | None = None, row: dict | None = None, **record) -> None:
        listing = "".join(f"- [{member}]({member}.md)\n" for member in members)
        text = body if body is not None else (f"# Card {Path(folder).name}\n\nWhat the card says.\n\n## Idea\n\n"
                                              f"Why it matters.\n\n## Statements\n\n{listing}")
        fields = {"kind": kind, "main_article_id": af(main), "importance": "key", "level": "undergraduate", **record}
        extensions = {"org.atlas-wiki": {"card": fields}, **(row or {}).pop("extensions", {})}
        self.page(f"{folder}/README.md", text, {"id": af(number), "extensions": extensions, **(row or {})})

    def write(self, order=None) -> None:
        rows = list(self.rows if order is None else order)
        (wiki.VAULT / "links" / "Algebra.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))

    def extraction(self) -> dict:
        """The extraction of every credited leaf, keeping only dependencies between credited leaves."""
        return {"articles": {name: {kind: [other for other in entry[kind] if other in self.articles]
                                    for kind in ("statement", "proof")}
                             for name, entry in self.articles.items()}}

    def ledger_file(self) -> None:
        (wiki.ROOT / "scripts" / cards.MOVES).touch()

    def mathlib_page(self, relative: str, number: int, name: str, depends: tuple[str, ...] = (),
                     kind: str = "theorem") -> None:
        # The row as lean-facts leaves it: Mathlib's kind of the declaration, from the registry.
        mathlib = {"object": [{"type": "lean", "uri": cards.sync.MATHLIB, "location": {"declaration": name}}],
                   "extensions": {"org.autoform": {"mathlib": True}}, "kind": kind}
        here = Path(relative).parent
        text = f"# {Path(relative).stem}\n\nA Mathlib statement.\n"
        if depends:
            text += "\n## Depends on\n\n" + "".join(
                f"- [{Path(t).stem}]({Path('/'.join(['..'] * len(here.parts)), t).as_posix()})\n" for t in depends)
        self.page(relative, text, {"id": af(number), **mathlib})

    def run_check(self, **options) -> tuple[list[str], list[str]]:
        self.write()
        return cards.check(**options)

    def rollup(self, **options) -> dict:
        self.write()
        self.ledger_file()
        errors, _ = cards.check(dependencies=self.extraction())
        self.assertEqual(errors, [])
        return cards.rollup(self.extraction(), **options)


class ProbeLayout(Vault):
    """Review probe: A's main uses B's left, B's main uses B's left and right, B's right uses C's main."""

    def setUp(self) -> None:
        super().setUp()
        g = "Algebra/groups"
        self.leaf(f"{g}/c/c-main.md", 31)
        self.leaf(f"{g}/b/b-left.md", 21)
        self.leaf(f"{g}/b/b-right.md", 22, statement=(f"{g}/c/c-main.md",))
        self.leaf(f"{g}/b/b-main.md", 20, statement=(f"{g}/b/b-left.md", f"{g}/b/b-right.md"))
        self.leaf(f"{g}/a/a-main.md", 10, statement=(f"{g}/b/b-left.md",))
        self.card(f"{g}/a", 1, 10, ["a-main"])
        self.card(f"{g}/b", 2, 20, ["b-main", "b-left", "b-right"])
        self.card(f"{g}/c", 3, 31, ["c-main"])

    def test_the_probe_is_valid(self) -> None:
        self.assertEqual(self.run_check(), ([], []))

    def test_uses_keeps_typed_witnesses_and_needs_follows_main_statements(self) -> None:
        result = self.rollup()
        g = "Algebra/groups"
        self.assertEqual(result["uses"], [
            {"from": af(1), "to": af(2), "statement": 1, "proof": 0, "origins": {"compiled": 1},
             "witnesses": [{"source": f"{g}/a/a-main", "target": f"{g}/b/b-left", "kind": "statement",
                            "origin": "compiled"}]},
            {"from": af(2), "to": af(3), "statement": 1, "proof": 0, "origins": {"compiled": 1},
             "witnesses": [{"source": f"{g}/b/b-right", "target": f"{g}/c/c-main", "kind": "statement",
                            "origin": "compiled"}]},
        ])
        # A uses B and B uses C, but A's main statement reaches no other main statement: no A -> C path is invented.
        self.assertEqual([(e["from"], e["to"], e["phase"], walk(e)) for e in result["needs"]],
                         [(af(2), af(3), "statement", [f"{g}/b/b-main", f"{g}/b/b-right", f"{g}/c/c-main"])])
        self.assertEqual(result["clusters"], [])
        card = next(card for card in result["cards"] if card["id"] == af(2))
        self.assertEqual(card["main"], {"page": f"{g}/b/b-main", "article_id": af(20), "headline": "fully_proved",
                                        "state": "fully_proved", "credit": "atlas", "held": False,
                                        "not_ready": False, "stale": False})
        self.assertEqual(card["supporting"]["total"], 2)
        self.assertEqual(card["supporting"]["fully_proved"], 2)
        self.assertEqual(result["pages"][f"{g}/b/b-left"]["card"], af(2))
        self.assertEqual(result["edges"], {"card_to_card": 2, "internal": 2, "total": 4})

    def test_the_output_does_not_depend_on_the_order_of_the_annotations(self) -> None:
        first = json.dumps(self.rollup(), sort_keys=True)
        shuffled = list(self.rows)
        random.Random(7).shuffle(shuffled)
        self.write(shuffled)
        self.assertEqual(json.dumps(cards.rollup(self.extraction()), sort_keys=True), first)


class Phases(Vault):
    g = "Algebra/groups"

    def two_cards(self) -> None:
        self.card(f"{self.g}/a", 1, 10, ["a-main", "helper"])
        self.card(f"{self.g}/b", 2, 20, ["b-main"])

    def test_a_proof_use_then_a_statement_use_is_a_proof_need(self) -> None:
        g = self.g
        self.leaf(f"{g}/b/b-main.md", 20)
        self.leaf(f"{g}/a/helper.md", 11, statement=(f"{g}/b/b-main.md",))
        self.leaf(f"{g}/a/a-main.md", 10, proof=(f"{g}/a/helper.md",))
        self.two_cards()
        result = self.rollup()
        # The card edge is labelled by its witness, a statement use; the main statement needs B only for its proof.
        self.assertEqual([(e["statement"], e["proof"]) for e in result["uses"]], [(1, 0)])
        [need] = result["needs"]
        self.assertEqual(need["phase"], "proof")
        self.assertEqual([step["kind"] for step in need["walk"]], ["proof", "statement"])
        self.assertEqual(walk(need), [f"{g}/a/a-main", f"{g}/a/helper", f"{g}/b/b-main"])

    def test_a_statement_need_shows_a_walk_of_statement_steps_even_when_a_proof_step_is_shorter(self) -> None:
        g = self.g
        self.leaf(f"{g}/b/b-main.md", 20)
        self.leaf(f"{g}/a/helper.md", 11, statement=(f"{g}/b/b-main.md",))
        self.leaf(f"{g}/a/a-main.md", 10, statement=(f"{g}/a/helper.md",), proof=(f"{g}/b/b-main.md",))
        self.two_cards()
        [need] = self.rollup()["needs"]
        self.assertEqual(need["phase"], "statement")
        self.assertNotIn("walk", need)
        self.assertEqual([step["kind"] for step in need["statement_walk"]], ["statement", "statement"])
        self.assertEqual(walk(need), [f"{g}/a/a-main", f"{g}/a/helper", f"{g}/b/b-main"])

    def test_ties_go_to_the_smallest_sequence_of_pages(self) -> None:
        g = self.g
        self.leaf(f"{g}/b/b-main.md", 20)
        self.leaf(f"{g}/a/zeta.md", 12, statement=(f"{g}/b/b-main.md",))
        self.leaf(f"{g}/a/alpha.md", 11, statement=(f"{g}/b/b-main.md",))
        self.leaf(f"{g}/a/a-main.md", 10, statement=(f"{g}/a/zeta.md", f"{g}/a/alpha.md"))
        self.card(f"{g}/a", 1, 10, ["a-main", "alpha", "zeta"])
        self.card(f"{g}/b", 2, 20, ["b-main"])
        self.assertEqual(walk(self.rollup()["needs"][0]), [f"{g}/a/a-main", f"{g}/a/alpha", f"{g}/b/b-main"])

    def test_a_need_stops_at_the_first_main_statement_and_crosses_pages_outside_cards(self) -> None:
        g = self.g
        self.leaf(f"{g}/c/c-main.md", 30)
        self.leaf(f"{g}/loose.md", 40, statement=(f"{g}/c/c-main.md",))
        self.leaf(f"{g}/b/b-main.md", 20, statement=(f"{g}/loose.md",))
        self.leaf(f"{g}/a/a-main.md", 10, statement=(f"{g}/b/b-main.md",))
        for folder, number, main in (("a", 1, 10), ("b", 2, 20), ("c", 3, 30)):
            self.card(f"{g}/{folder}", number, main, [f"{folder}-main"])
        result = self.rollup()
        self.assertEqual([(e["from"], e["to"]) for e in result["needs"]], [(af(1), af(2)), (af(2), af(3))])
        self.assertEqual(walk(result["needs"][1]), [f"{g}/b/b-main", f"{g}/loose", f"{g}/c/c-main"])
        self.assertEqual(result["pages"][f"{g}/loose"]["card"], None)
        self.assertEqual(result["unassigned"], [{"folder": g, "pages": [f"{g}/loose"]}])
        self.assertEqual(result["edges"], {"card_to_card": 1, "to_unassigned": 1, "total": 2})


class Origins(Vault):
    def test_a_page_only_page_s_edges_are_planned_and_the_others_compiled(self) -> None:
        g = "Algebra/groups"
        self.leaf(f"{g}/b/b-main.md", 30)
        self.leaf(f"{g}/a/a-main.md", 10, statement=(f"{g}/b/b-main.md",))
        self.leaf(f"{g}/p/p-main.md", 20, facts=None, statement=(f"{g}/a/a-main.md",))
        self.card(f"{g}/a", 1, 10, ["a-main"])
        self.card(f"{g}/p", 2, 20, ["p-main"])
        self.card(f"{g}/b", 3, 30, ["b-main"])
        result = self.rollup()
        self.assertEqual({(e["from"], e["to"]): e["origins"] for e in result["uses"]},
                         {(af(1), af(3)): {"compiled": 1}, (af(2), af(1)): {"planned": 1}})

    def test_edges_this_extraction_cannot_vouch_for_are_errors(self) -> None:
        # Mathlib-credited pages and their edges come with the registry of a later version; until then an edge
        # that reaches or leaves one is never shown as checked.
        g = "Algebra/groups"
        mathlib = {"object": [{"type": "lean", "uri": cards.sync.MATHLIB,
                               "location": {"declaration": "Mathlib.thing"}}],
                   "extensions": {"org.autoform": {"mathlib": True}}}
        self.page(f"{g}/m/m-main.md", f"# m\n\nA Mathlib statement.\n\n## Depends on\n\n- [b](../b/b-main.md)\n",
                  {"id": af(30), **mathlib})
        self.leaf(f"{g}/b/b-main.md", 20)
        self.leaf(f"{g}/a/a-main.md", 10, statement=(f"{g}/m/m-main.md",))
        self.ledger_file()
        errors = self.run_check(dependencies=self.extraction())[0]
        self.assertIn(f"{g}/a/a-main: its statement dependency on the Mathlib-credited page {g}/m/m-main cannot be "
                      "checked against the extraction", errors)
        self.assertIn(f"{g}/m/m-main: a Mathlib-credited page lists a statement dependency on {g}/b/b-main; "
                      "nothing here can check it", errors)

    def test_the_registry_vouches_for_bridge_and_mathlib_edges(self) -> None:
        g = "Algebra/groups"
        self.mathlib_page(f"{g}/n/n-main.md", 40, "Mathlib.other")
        self.mathlib_page(f"{g}/m/m-main.md", 30, "Mathlib.thing", depends=(f"{g}/n/n-main.md",))
        self.leaf(f"{g}/a/a-main.md", 10, statement=(f"{g}/m/m-main.md",))
        for folder, number, main in (("a", 1, 10), ("m", 3, 30), ("n", 4, 40)):
            self.card(f"{g}/{folder}", number, main, [f"{folder}-main"])
        self.write()
        self.ledger_file()
        registry = self.registry({"Ext.a_main": {"statement": ["Mathlib.thing"], "proof": []}},
                                 {"Mathlib.thing": {"statement": ["Mathlib.other"], "proof": []},
                                  "Mathlib.other": {"statement": [], "proof": []}})
        self.assertEqual(cards.check(dependencies=self.extraction(), registry=registry)[0], [])
        result = cards.rollup(self.extraction(), registry=registry)
        self.assertEqual({(e["from"], e["to"]): e["origins"] for e in result["uses"]},
                         {(af(1), af(3)): {"bridge": 1}, (af(3), af(4)): {"mathlib": 1}})
        # Each way a difference is an error.
        lacking = {**registry, "bridges": {}}
        self.assertIn(f"{g}/a/a-main: its statement dependency on the Mathlib-credited {g}/m/m-main is not in the "
                      "registry", cards.check(dependencies=self.extraction(), registry=lacking)[0])
        extra = self.registry(registry["bridges"], {"Mathlib.thing": {"statement": [], "proof": []},
                                                    "Mathlib.other": {"statement": ["Mathlib.thing"], "proof": []}})
        errors = cards.check(dependencies=self.extraction(), registry=extra)[0]
        self.assertIn(f"{g}/n/n-main: the registry records a statement dependency on the Mathlib-credited {g}/m/m-main, "
                      "which the page lacks", errors)
        self.assertIn(f"{g}/m/m-main: its statement dependency on the Mathlib-credited {g}/n/n-main is not in the "
                      "registry", errors)

    def test_a_registry_no_consumer_may_act_on_fails_the_check(self) -> None:
        # One bridge both kept and left out, or a bridge to a declaration the registry does not find: the strict check
        # refuses the registry (sync_wiki.registry_problems, as lean-facts does), and rollup leaves no card data.
        g = "Algebra/groups"
        self.mathlib_page(f"{g}/m/m-main.md", 30, "Mathlib.thing")
        self.leaf(f"{g}/a/a-main.md", 10, statement=(f"{g}/m/m-main.md",))
        for folder, number, main in (("a", 1, 10), ("m", 3, 30)):
            self.card(f"{g}/{folder}", number, main, [f"{folder}-main"])
        self.write()
        self.ledger_file()
        good = self.registry({"Ext.a_main": {"statement": ["Mathlib.thing"], "proof": []}},
                             {"Mathlib.thing": {"statement": [], "proof": []}})
        self.assertEqual(cards.check(dependencies=self.extraction(), registry=good)[0], [])
        both = {**good, "left_out": {"Ext.a_main": {"statement": [], "proof": ["Mathlib.thing"]}}}
        absent = {**good, "bridges": {"Ext.a_main": {"statement": ["Mathlib.thing", "Mathlib.absent"], "proof": []}}}
        dependencies, given = self.tmp / "lean-dependencies.json", self.tmp / "registry.json"
        dependencies.write_text(json.dumps(self.extraction()))
        output = self.tmp / "build" / "cards.json"
        for registry, message in (
                (both, "the registry both keeps and leaves out the bridge Ext.a_main -> Mathlib.thing"),
                (absent, "the registry's bridges entry for Ext.a_main names Mathlib.absent, which it does not find")):
            with self.subTest(message=message):
                self.assertIn(message, cards.check(dependencies=self.extraction(), registry=registry)[0])
                given.write_text(json.dumps(registry))
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_text("{}")
                with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                    status = cards.run(["rollup", str(output), "--dependencies", str(dependencies), "--registry",
                                        str(given)])
                self.assertEqual((status, output.exists()), (1, False))

    def test_a_registry_made_for_other_duplicates_lists_fails_the_check(self) -> None:
        # The registry was made before a-main's row listed Ext.a_twin as a duplicate, an edit that can change its
        # bridges and leave the extraction as it was: the strict check refuses it (sync_wiki.registry_problems, as
        # lean-facts does), and rollup leaves no card data. A registry made for the rows as they are passes.
        g = "Algebra/groups"
        self.mathlib_page(f"{g}/m/m-main.md", 30, "Mathlib.thing")
        self.leaf(f"{g}/a/a-main.md", 10, statement=(f"{g}/m/m-main.md",))
        for folder, number, main in (("a", 1, 10), ("m", 3, 30)):
            self.card(f"{g}/{folder}", number, main, [f"{folder}-main"])
        self.write()
        self.ledger_file()
        bridges = {"Ext.a_main": {"statement": ["Mathlib.thing"], "proof": []}}
        mathlib = {"Mathlib.thing": {"statement": [], "proof": []}}
        stale = self.registry(bridges, mathlib)
        self.assertEqual(cards.check(dependencies=self.extraction(), registry=stale)[0], [])
        row = next(row for row in self.rows if row["subject"][0]["uri"].endswith("/a/a-main.md"))
        row["extensions"] = {"org.atlas-wiki": {"duplicates": ["Ext.a_twin"]}}
        self.write()
        message = "the registry was made for other duplicates lists than the checkout's"
        self.assertTrue(any(message in error
                            for error in cards.check(dependencies=self.extraction(), registry=stale)[0]))
        dependencies, given = self.tmp / "lean-dependencies.json", self.tmp / "registry.json"
        dependencies.write_text(json.dumps(self.extraction()))
        digest = hashlib.sha256(dependencies.read_bytes()).hexdigest()
        given.write_text(json.dumps({**stale, "inputs": {**stale["inputs"], "extraction_sha256": digest}}))
        output = self.tmp / "build" / "cards.json"
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text("{}")
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()) as errors:
            status = cards.run(["rollup", str(output), "--dependencies", str(dependencies), "--registry", str(given)])
        self.assertEqual((status, output.exists()), (1, False))
        self.assertIn(message, errors.getvalue())
        self.assertEqual(cards.check(dependencies=self.extraction(), registry=self.registry(bridges, mathlib))[0], [])

    def test_a_registry_given_is_checked_whatever_it_holds(self) -> None:
        # `--registry` naming a file that holds JSON null, a list or no JSON at all, or a registry whose tables are of
        # another type, is no run without a registry, even where no edge reaches Mathlib: check and rollup refuse it
        # with an error, before anything reads its tables (no traceback), and the rollup leaves no card data.
        g = "Algebra/groups"
        self.leaf(f"{g}/a/a-main.md", 10)
        self.card(f"{g}/a", 1, 10, ["a-main"])
        self.write()
        self.ledger_file()
        dependencies, given = self.tmp / "lean-dependencies.json", self.tmp / "registry.json"
        dependencies.write_text(json.dumps(self.extraction()))
        output = self.tmp / "build" / "cards.json"
        good = {**self.registry({}, {}), "inputs": {**self.registry({}, {})["inputs"],
                                                    "extraction_sha256": hashlib.sha256(dependencies.read_bytes())
                                                    .hexdigest()}}
        malformed = {table: json.dumps({**good, table: other}) for table, other in (
            ("mathlib", []), ("bridges", []), ("left_out", []), ("inputs", []), ("missing", {}), ("project", {}))}
        output.parent.mkdir(parents=True, exist_ok=True)
        for held, message in (("null", f"error: --registry {given}"), ("[]", f"error: --registry {given}"),
                              ("{not json", f"error: --registry {given}"),
                              *((text, "the registry is not one extract_v2_lean_dependencies.py --registry writes")
                                for text in malformed.values())):
            with self.subTest(held=held[:40]):
                given.write_text(held)
                output.write_text("{}")
                with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()) as errors:
                    checked = cards.run(["check", "--dependencies", str(dependencies), "--registry", str(given)])
                    rolled = cards.run(["rollup", str(output), "--dependencies", str(dependencies), "--registry",
                                        str(given)])
                self.assertEqual((checked, rolled, output.exists()), (1, 1, False))
                self.assertIn(message, errors.getvalue())
                self.assertNotIn("Traceback", errors.getvalue())
                # The check, called with the registry, reports its form and reads no table.
                if held in malformed.values():
                    self.assertEqual(cards.check(dependencies=self.extraction(), registry=json.loads(held))[0],
                                     ["the registry is not one extract_v2_lean_dependencies.py --registry writes"])
        given.write_text(json.dumps(good))
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()) as errors:
            self.assertEqual(cards.run(["rollup", str(output), "--dependencies", str(dependencies), "--registry",
                                        str(given)]), 0, errors.getvalue())
        self.assertTrue(output.exists())
        # A refused invocation leaves no card data either: a registry with no extraction to check it against.
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(cards.run(["rollup", str(output), "--registry", str(given)]), 2)
        self.assertFalse(output.exists())

    def test_a_credited_page_without_its_row_in_the_extraction_fails_the_strict_check(self) -> None:
        # An extraction made before a page credited its declaration: the page's declaration has no row, so the page
        # would show no prerequisites. The strict check names it; an extraction with the row, edges or none, passes.
        g = "Algebra/groups"
        self.leaf(f"{g}/a/a-main.md", 10)
        self.leaf(f"{g}/b/b-main.md", 20, statement=(f"{g}/a/a-main.md",))
        for folder, number, main in (("a", 1, 10), ("b", 2, 20)):
            self.card(f"{g}/{folder}", number, main, [f"{folder}-main"])
        self.write()
        self.ledger_file()
        stale = {"articles": {"Ext.a_main": {"statement": [], "proof": []}}}
        self.assertIn(f"{g}/b/b-main: credits Ext.b_main, which the extraction has no row for; it was made for another "
                      "state of the wiki", cards.check(dependencies=stale)[0])
        self.assertEqual(cards.check(dependencies=self.extraction())[0], [])

    def test_the_site_shows_a_mathlib_credited_main_and_its_edges(self) -> None:
        # The wiki job's rollup, with the build's registry, gives the site the card data hooks/card_pages.py shows: a
        # card headed by a Mathlib-credited statement shows it in Mathlib, and each edge the registry vouches for says
        # how it is known, `bridge` from an ATLAS declaration and `Mathlib` between two Mathlib ones.
        g = "Algebra/groups"
        self.mathlib_page(f"{g}/n/n-main.md", 40, "Mathlib.other")
        self.mathlib_page(f"{g}/m/m-main.md", 30, "Mathlib.thing", depends=(f"{g}/n/n-main.md",))
        self.leaf(f"{g}/a/a-main.md", 10, statement=(f"{g}/m/m-main.md",))
        for folder, number, main in (("a", 1, 10), ("m", 3, 30), ("n", 4, 40)):
            self.card(f"{g}/{folder}", number, main, [f"{folder}-main"])
        self.write()
        self.ledger_file()
        registry = self.registry({"Ext.a_main": {"statement": ["Mathlib.thing"], "proof": []}},
                                 {"Mathlib.thing": {"statement": ["Mathlib.other"], "proof": []},
                                  "Mathlib.other": {"statement": [], "proof": []}})
        dependencies, registry_file = self.tmp / "lean-dependencies.json", self.tmp / "mathlib-registry.json"
        dependencies.write_text(json.dumps(self.extraction()))
        registry["inputs"]["extraction_sha256"] = hashlib.sha256(dependencies.read_bytes()).hexdigest()
        registry_file.write_text(json.dumps(registry))
        output = self.tmp / "build" / "cards.json"
        rollup = ["rollup", str(output), "--dependencies", str(dependencies), "--registry", str(registry_file)]
        # A registry made with another extraction is refused, and so is an output that is an input or a symbolic
        # link, before anything is touched.
        other = self.tmp / "other-registry.json"
        other.write_text(json.dumps({**registry, "inputs": {**registry["inputs"], "extraction_sha256": "e" * 64}}))
        (self.tmp / "link.json").symlink_to(self.tmp / "elsewhere.json")
        base = self.tmp / "base" / "links"
        base.mkdir(parents=True)
        (base / "Algebra.jsonl").write_text("")
        history = ["--base-ledger", str(self.tmp / "ledger.jsonl"), "--base-links", str(base), "--renames",
                   str(self.tmp / "renames.tsv")]
        vault = {path: path.read_bytes() for path in wiki.VAULT.rglob("*") if path.is_file()}
        for argv, status, message in (
                (rollup[:4] + ["--registry", str(other)], 1, f"the registry was not made with {dependencies}"),
                (["rollup", str(registry_file)] + rollup[2:], 2, "are one file"),
                (["rollup", str(self.tmp / "link.json")] + rollup[2:], 2, "is a symbolic link"),
                (["rollup", str(cards.links_dir() / "_defaults.json")] + rollup[2:], 2, "is inside blueprint/"),
                (["rollup", str(wiki.ROADMAP / g / "a" / "a-main.md")] + rollup[2:], 2, "is inside blueprint/"),
                (["rollup", str(base / "new.json")] + rollup[2:] + history, 2, "is inside --base-links")):
            with self.subTest(argv=argv[1]), contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(io.StringIO()) as errors:
                self.assertEqual(cards.run(argv), status)
                self.assertIn(message, errors.getvalue())
        self.assertEqual(json.loads(registry_file.read_text()), registry)
        self.assertEqual({path: path.read_bytes() for path in wiki.VAULT.rglob("*") if path.is_file()}, vault)
        self.assertEqual(sorted(path.name for path in base.iterdir()), ["Algebra.jsonl"])
        self.assertFalse(output.exists())
        # Its temporary file takes a name no file has.
        output.parent.mkdir()
        bystander = output.with_name(f".{output.name}.partial")
        bystander.write_text("someone else's\n")
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()) as errors:
            status = cards.run(rollup)
        self.assertEqual((status, errors.getvalue()), (0, ""))
        self.assertEqual((bystander.read_text(), sorted(path.name for path in output.parent.iterdir())),
                         ("someone else's\n", [".cards.json.partial", "cards.json"]))
        hook = load_hook()
        site = hook.build(json.loads(output.read_text()), site_index(hook), "", self.tmp / "site-src")
        blocks = {name: site.blocks[f"roadmap/{g}/{name}/index.html"] for name in "amn"}
        for name in "mn":
            self.assertIn('atlas-card-mathlib">in Mathlib</span>', blocks[name])
        self.assertIn('atlas-card-fully_proved">fully proved</span>', blocks["a"])
        self.assertIn('title="From an ATLAS declaration to a Mathlib one">bridge</span>', blocks["a"])
        self.assertIn('title="Between two Mathlib declarations">Mathlib</span>', blocks["m"])

    def test_one_owner_for_the_loader_the_extractor_and_the_check(self) -> None:
        # T states its page and also names a helper H (`uses`) and a sibling checkout's H: neither is an article, so
        # T's statement reaches the Mathlib-credited R through H, with Autoform's loader, the extractor and the check:
        # a statement bridge reached only through another constant, listed apart, which the page does not show.
        from scripts import extract_v2_lean_dependencies as extract
        from scripts.test_extract_v2_lean_dependencies import PIN, credited, framed, row, with_mathlib
        g = "Algebra/groups"
        self.mathlib_page(f"{g}/r/r-main.md", 30, "Mathlib.R")
        self.leaf(f"{g}/t/t-main.md", 40)
        self.rows[-1]["object"] = [{"location": {"declaration": "Ext.t_main"}, "role": "states"},
                                   {"location": {"declaration": "Ext.H"}, "role": "uses"},
                                   {"type": "lean", "uri": "../../../sibling", "location": {"declaration": "Ext.H"},
                                    "role": "uses"}]
        # The subject spelled with a percent-encoded hyphen is the same page, as Autoform reads it.
        self.rows[-1]["subject"] = [{"type": "generic", "uri": f"../roadmap/{g}/t/t%2Dmain.md"}]
        self.write()
        self.ledger_file()
        with patch.object(extract, "BLUEPRINT", wiki.VAULT):
            self.assertEqual(extract.article_manifest(), {"Ext.t_main"})
            dump_rows = [with_mathlib(row("Ext.t_main", "theorem", ["Ext.H"], []), [], []),
                         with_mathlib(row("Ext.H", "theorem", [], []), ["Mathlib.R"], []),
                         credited("Mathlib.R", "theorem", [], [])]
            dump, names = self.tmp / "dump.jsonl", self.tmp / "names.txt"
            dump.write_text("".join(json.dumps(r) + "\n" for r in framed(dump_rows)))
            credited_names, problems = cards.sync.credited_mathlib({wiki.VAULT / "links": self.rows})
            self.assertEqual(problems, [])
            names.write_text(cards.sync.names_text(credited_names))
            output, registry_file = self.tmp / "deps.json", self.tmp / "registry.json"
            with patch.object(extract, "mathlib_revision", lambda: PIN), \
                    patch("sys.argv", ["extract", str(dump), str(output), "--registry", str(registry_file),
                                       "--names", str(names)]):
                self.assertEqual(extract.main(), 0)
        registry = json.loads(registry_file.read_text())
        self.assertEqual((registry["bridges"], registry["left_out"]),
                         ({}, {"Ext.t_main": {"statement": ["Mathlib.R"], "proof": []}}))
        with patch.object(cards.sync, "mathlib_revision", lambda: PIN):
            self.assertEqual(cards.check(dependencies=json.loads(output.read_text()), registry=registry)[0], [])

    def test_a_row_autoform_leaves_out_stops_the_extractor_and_the_cards(self) -> None:
        # A row about part of its page, which Autoform leaves out: the extractor and the cards name it and stop, as the
        # sync does, rather than leave the page's article out unsaid.
        from scripts import extract_v2_lean_dependencies as extract
        g = "Algebra/groups"
        self.leaf(f"{g}/t/t-main.md", 40)
        self.rows[-1]["subject"] = [{"type": "generic", "uri": f"../roadmap/{g}/t/t-main.md#statement"}]
        self.write()
        self.ledger_file()
        message = f"a row of Algebra.jsonl about ../roadmap/{g}/t/t-main.md#statement is one Autoform leaves out"
        with patch.object(extract, "BLUEPRINT", wiki.VAULT):
            with self.assertRaises(ValueError) as raised:
                extract.article_manifest()
            self.assertIn(message, str(raised.exception))
            with patch("sys.argv", ["extract", str(self.tmp / "dump.jsonl"), str(self.tmp / "deps.json")]), \
                    patch("sys.stderr", new_callable=io.StringIO) as err:
                self.assertEqual(extract.main(), 1)
            self.assertIn(message, err.getvalue())
        self.assertFalse((self.tmp / "deps.json").exists())
        with patch("sys.stdout", new_callable=io.StringIO), patch("sys.stderr", new_callable=io.StringIO) as err:
            self.assertEqual(cards.run(["check"]), 1)
        self.assertIn(f"error: {message}", err.getvalue())

    def registry(self, bridges: dict, mathlib: dict, missing: tuple[str, ...] = (), kind: str = "theorem",
                 proposition: bool = True) -> dict:
        """A registry as extract_v2_lean_dependencies.py writes it for the vault's committed rows."""
        files = {cards.sync.LINKS: list(cards.read_annotations().values())}
        credited, _ = cards.sync.credited_mathlib(files)
        digest = hashlib.sha256(cards.sync.names_text(credited).encode("utf-8")).hexdigest()
        aliases = cards.sync.extract.aliases_digest(cards.sync.listed_duplicates(files)[0])
        return {"bridges": bridges, "left_out": {}, "mutual": [], "missing": list(missing), "project": [],
                "mathlib": {name: {"module": "Mathlib.X", "kind": kind, "proposition": proposition, **entry}
                            for name, entry in mathlib.items()},
                "inputs": {"names_sha256": digest, "requested": len(credited), "dump_sha256": "d" * 64,
                           "mathlib_rev": None, "aliases_sha256": aliases, "format": cards.sync.REGISTRY_FORMAT}}

    def mathlib_cards(self) -> str:
        g = "Algebra/groups"
        self.mathlib_page(f"{g}/m/m-main.md", 30, "Mathlib.thing")
        self.leaf(f"{g}/a/a-main.md", 10, statement=(f"{g}/m/m-main.md",))
        for folder, number, main in (("a", 1, 10), ("m", 3, 30)):
            self.card(f"{g}/{folder}", number, main, [f"{folder}-main"])
        self.write()
        self.ledger_file()
        return g

    def test_one_page_per_mathlib_declaration_and_a_registry_row_for_each(self) -> None:
        g = self.mathlib_cards()
        bridges = {"Ext.a_main": {"statement": ["Mathlib.thing"], "proof": []}}
        registry = self.registry(bridges, {"Mathlib.thing": {"statement": [], "proof": []}})
        self.assertEqual(cards.check(dependencies=self.extraction(), registry=registry)[0], [])
        # A second card whose main credits the same declaration.
        self.mathlib_page(f"{g}/twin/twin-main.md", 31, "Mathlib.thing")
        self.card(f"{g}/twin", 5, 31, ["twin-main"])
        self.write()
        self.assertIn(f"{g}/m/m-main.md and {g}/twin/twin-main.md both credit the Mathlib declaration Mathlib.thing; "
                      "a declaration has one page", cards.check(dependencies=self.extraction(), registry=registry)[0])

    def test_a_credited_name_the_registry_does_not_answer(self) -> None:
        self.mathlib_cards()
        # The registry was made for the same names but has no row for the declaration: it cannot vouch for it.
        registry = self.registry({}, {})
        self.assertIn("the registry's found and missing names do not split the checkout's credited names",
                      cards.check(dependencies=self.extraction(), registry=registry)[0])
        # A registry made for another list of names is refused as a whole.
        other = self.registry({}, {"Mathlib.thing": {"statement": [], "proof": []}})
        other = {**other, "inputs": {**other["inputs"], "names_sha256": "0" * 64}}
        self.assertIn("the registry was made for another list of credited Mathlib names than the checkout's; make the "
                      "dump and the registry from `sync_wiki.py mathlib-names` of this checkout",
                      cards.check(dependencies=self.extraction(), registry=other)[0])

    def test_an_edge_to_a_declaration_no_page_credits_is_an_error(self) -> None:
        self.mathlib_cards()
        bridges = {"Ext.a_main": {"statement": ["Mathlib.thing", "Mathlib.unknown"], "proof": []},
                   "Ext.nowhere": {"statement": ["Mathlib.thing"], "proof": []}}
        errors = cards.check(dependencies=self.extraction(),
                             registry=self.registry(bridges, {"Mathlib.thing": {"statement": [], "proof": []}}))[0]
        self.assertIn("the registry records Ext.a_main -> Mathlib.unknown, and Mathlib.unknown credits no statement "
                      "page", errors)
        self.assertIn("the registry records the dependencies of Ext.nowhere, which credits no statement page", errors)

    def test_mathlib_s_kind_decides_what_a_mathlib_main_can_head(self) -> None:
        g = self.mathlib_cards()
        bridges = {"Ext.a_main": {"statement": ["Mathlib.thing"], "proof": []}}
        definition = self.registry(bridges, {"Mathlib.thing": {"statement": [], "proof": []}}, kind="def",
                                   proposition=False)
        # The page's kind follows the registry, as lean-facts writes it; the card is a result card.
        self.rows = [{**row, "kind": "def"} if row["subject"][0]["uri"].endswith("m/m-main.md") else row
                     for row in self.rows]
        self.write()
        self.assertIn(f"{g}/m: a result card's main statement {g}/m/m-main is Mathlib's Mathlib.thing, which does "
                      "not state a proposition",
                      cards.check(dependencies=self.extraction(), registry=definition)[0])
        # A page whose kind is not the registry's was not written from it.
        theorem = self.registry(bridges, {"Mathlib.thing": {"statement": [], "proof": []}})
        self.assertIn(f"{g}/m/m-main: its kind is 'def', but the registry finds Mathlib.thing a `theorem`; run "
                      "sync_wiki.py lean-facts with this registry",
                      cards.check(dependencies=self.extraction(), registry=theorem)[0])

    def test_each_page_keeps_the_declaration_its_committed_row_credits(self) -> None:
        g = "Algebra/groups"
        self.mathlib_page(f"{g}/n/n-main.md", 40, "Mathlib.other")
        self.mathlib_page(f"{g}/m/m-main.md", 30, "Mathlib.thing")
        for folder, number, main in (("m", 3, 30), ("n", 4, 40)):
            self.card(f"{g}/{folder}", number, main, [f"{folder}-main"])
        self.write()
        self.ledger_file()
        registry = self.registry({}, {"Mathlib.thing": {"statement": [], "proof": []},
                                      "Mathlib.other": {"statement": [], "proof": []}})
        self.assertEqual(cards.check(dependencies=self.extraction(), registry=registry)[0], [])
        # The committed rows credited the two declarations the other way round.
        committed = {page: json.loads(json.dumps(row)) for page, row in cards.read_annotations().items()}
        for row in committed.values():
            for end in row.get("object", []):
                name = end["location"]["declaration"]
                end["location"]["declaration"] = {"Mathlib.thing": "Mathlib.other",
                                                  "Mathlib.other": "Mathlib.thing"}.get(name, name)
        errors = cards.check(dependencies=self.extraction(), registry=registry, committed=committed)[0]
        self.assertIn(f"{g}/m/m-main: the build credits Mathlib.thing, but its committed row credits Mathlib.other",
                      errors)

    def test_a_mathlib_main_needs_the_registry_s_proposition_flag(self) -> None:
        self.mathlib_cards()
        bridges = {"Ext.a_main": {"statement": ["Mathlib.thing"], "proof": []}}
        registry = self.registry(bridges, {"Mathlib.thing": {"statement": [], "proof": []}})
        del registry["mathlib"]["Mathlib.thing"]["proposition"]
        self.assertTrue(any("the registry's mathlib entry for Mathlib.thing is malformed" in error
                            for error in cards.check(dependencies=self.extraction(), registry=registry)[0]))

    def test_a_mathlib_page_never_depends_on_a_project_page(self) -> None:
        g = "Algebra/groups"
        self.leaf(f"{g}/b/b-main.md", 20)
        self.mathlib_page(f"{g}/m/m-main.md", 30, "Mathlib.thing", depends=(f"{g}/b/b-main.md",))
        self.write()
        self.ledger_file()
        registry = self.registry({}, {"Mathlib.thing": {"statement": [], "proof": []}})
        self.assertIn(f"{g}/m/m-main: a Mathlib-credited page lists a statement dependency on {g}/b/b-main; nothing "
                      "here can check it", cards.check(dependencies=self.extraction(), registry=registry)[0])

    def test_a_link_lean_facts_dropped_is_stale_not_planned(self) -> None:
        g = "Algebra/groups"
        self.leaf(f"{g}/a/a-main.md", 10)
        self.leaf(f"{g}/a/gone.md", 11, facts=None)
        self.card(f"{g}/a", 1, 10, ["a-main", "gone"])
        self.write()
        committed = cards.read_annotations()
        committed[(wiki.ROADMAP / f"{g}/a/gone.md").resolve()]["object"] = [{"location": {"declaration": "Ext.gone"}}]
        self.ledger_file()
        result = cards.rollup(self.extraction(), committed=committed)
        self.assertTrue(result["pages"][f"{g}/a/gone"]["stale"])
        self.assertEqual(result["cards"][0]["supporting"]["stale"], 1)
        self.assertEqual(result["cards"][0]["supporting"]["page_only"], 0)

    def test_no_credit_overrides_a_held_marker_in_the_cards(self) -> None:
        # A held row that credits a declaration, and a page that links a held declaration: the check reports both,
        # as the extraction and lean-facts refuse them, so no rollup shows a held page proved.
        g = "Algebra/groups"
        held = lambda name: {"org.atlas-wiki": {"held": {"declaration": name, "reason": "vacuous", "issue": 1}}}
        self.leaf(f"{g}/a/a-main.md", 10, row={"extensions": held("Ext.a_main")})
        self.leaf(f"{g}/b/b-main.md", 20)
        self.leaf(f"{g}/c/c-main.md", 30, facts=None, row={"extensions": held("Ext.b_main")})
        for folder, number, main in (("a", 1, 10), ("b", 2, 20), ("c", 3, 30)):
            self.card(f"{g}/{folder}", number, main, [f"{folder}-main"])
        errors = self.run_check()[0]
        self.assertIn(f"{g}/a/a-main.md: it holds Ext.a_main back but is linked to Ext.a_main", errors)
        self.assertIn(f"{g}/c/c-main.md: it holds Ext.b_main back, which {g}/b/b-main.md links", errors)

    def test_a_row_whose_page_is_gone_stops_the_rollup(self) -> None:
        g = "Algebra/groups"
        self.leaf(f"{g}/a/a-main.md", 10)
        self.card(f"{g}/a", 1, 10, ["a-main"])
        self.rows.append({"subject": [{"type": "generic", "uri": f"../roadmap/{g}/a/gone.md"}], "id": af(11)})
        self.write()
        self.ledger_file()
        dependencies = self.tmp / "lean-dependencies.json"
        dependencies.write_text(json.dumps(self.extraction()))
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()) as errors:
            status = cards.run(["rollup", str(self.tmp / "cards.json"), "--dependencies", str(dependencies)])
        self.assertEqual(status, 1)
        self.assertIn(f"{g}/a/gone.md: its row names a page that does not exist; remove the row or restore the page",
                      errors.getvalue())

    def test_a_legacy_row_counts_only_once_lean_facts_gave_it_its_lean_link(self) -> None:
        # Two rows an earlier sync wrote with a module and a name: lean-facts resolved `found` through the Lean index
        # and gave its build row the declaration's Lean link, and did not resolve `lost`. The cards read the build
        # rows: `found` counts as ATLAS credit and `lost` is stale, whatever the extraction holds.
        g = "Algebra/groups"
        hint = lambda stem: {"org.atlas-wiki": {"module": "Ext.Legacy", "name": stem}}
        self.leaf(f"{g}/a/a-main.md", 10)
        self.leaf(f"{g}/a/found.md", 11, facts=None, row={"extensions": hint("found")})
        self.leaf(f"{g}/a/lost.md", 12, facts=None, row={"extensions": hint("lost")})
        self.card(f"{g}/a", 1, 10, ["a-main", "found", "lost"])
        self.write()
        committed = cards.read_annotations()
        found = next(page for page in committed if page.name == "found.md")
        self.rows[[row["subject"][0]["uri"] for row in self.rows].index(f"../roadmap/{g}/a/found.md")].update(
            object=[{"location": {"declaration": "Ext.Legacy.found"}, "role": "states"}], **THEOREM)
        self.write()
        self.ledger_file()
        self.assertEqual(cards.declaration(cards.read_annotations()[found]), "Ext.Legacy.found")
        extraction = self.extraction()
        extraction["articles"]["Ext.Legacy.found"] = {"module": "Ext.Legacy", "statement": [], "proof": []}
        errors, warnings = cards.check(dependencies=extraction, committed=committed)
        self.assertEqual(errors, [])
        self.assertIn(f"{g}/a/lost: its module-and-name row names no declaration the Lean index resolves, so "
                      "lean-facts gave it no Lean link; it counts as stale, not as credited", warnings)
        result = cards.rollup(extraction, committed=committed)
        self.assertEqual((result["pages"][f"{g}/a/found"]["credit"], result["pages"][f"{g}/a/found"]["stale"]),
                         ("atlas", False))
        self.assertEqual((result["pages"][f"{g}/a/lost"]["credit"], result["pages"][f"{g}/a/lost"]["stale"]),
                         ("none", True))
        self.assertEqual(result["cards"][0]["supporting"]["stale"], 1)

    def test_a_legacy_row_and_an_explicit_one_never_share_a_declaration(self) -> None:
        # Build rows in which one page credits Ext.a_main and another got Ext.a_main's Lean link from a committed
        # module and name: the strict check refuses them and no rollup credits both (lean-facts and the extraction
        # refuse such rows first, with the Lean index).
        g = "Algebra/groups"
        self.leaf(f"{g}/a/a-main.md", 10)
        self.leaf(f"{g}/b/b-main.md", 20, facts=None, row={"extensions": {
            "org.atlas-wiki": {"module": "Ext", "name": "a_main"}}})
        self.card(f"{g}/a", 1, 10, ["a-main"])
        self.card(f"{g}/b", 2, 20, ["b-main"])
        self.write()
        committed = cards.read_annotations()
        self.rows[[row["subject"][0]["uri"] for row in self.rows].index(f"../roadmap/{g}/b/b-main.md")].update(
            object=[{"location": {"declaration": "Ext.a_main"}, "role": "states"}], **THEOREM)
        self.write()
        self.ledger_file()
        extraction = self.extraction()
        message = (f"{g}/a/a-main and {g}/b/b-main (by the module and name an earlier sync wrote) both stand for the "
                   "declaration Ext.a_main of this project; a declaration has one page")
        self.assertIn(message, cards.check(dependencies=extraction, committed=committed)[0])
        with self.assertRaises(ValueError) as raised:
            cards.rollup(extraction, committed=committed)
        self.assertIn(message, str(raised.exception))

    def test_a_walk_never_passes_through_a_folder_page(self) -> None:
        # A folder page's hand-written link is no statement's dependency: it is counted as reaching a folder, and
        # no need runs through it.
        g = "Algebra/groups"
        self.leaf(f"{g}/b/b-main.md", 20)
        self.page(f"{g}/plain/README.md", f"# Plain\n\n## Depends on\n\n- [b](../b/b-main.md)\n")
        self.leaf(f"{g}/a/a-main.md", 10, facts=None, statement=(f"{g}/plain/README.md",))
        self.card(f"{g}/a", 1, 10, ["a-main"])
        self.card(f"{g}/b", 2, 20, ["b-main"])
        result = self.rollup()
        self.assertEqual(result["needs"], [])
        self.assertEqual(result["edges"], {"to_folder": 1, "total": 1})

    def test_a_leftover_row_never_turns_a_folder_page_into_a_statement(self) -> None:
        # loose.md is gone but its row stays; loose/README.md is a live folder page with the same node id.
        g = "Algebra/groups"
        self.leaf(f"{g}/b/b-main.md", 20)
        self.leaf(f"{g}/loose.md", 30, statement=(f"{g}/b/b-main.md",))
        (wiki.ROADMAP / f"{g}/loose.md").unlink()
        del self.articles["Ext.loose"]
        self.page(f"{g}/loose/README.md", "# Loose\n\n## Depends on\n\n- [b](../b/b-main.md)\n")
        self.leaf(f"{g}/a/a-main.md", 10, facts=None, statement=(f"{g}/loose/README.md",))
        self.card(f"{g}/a", 1, 10, ["a-main"])
        self.card(f"{g}/b", 2, 20, ["b-main"])
        result = self.rollup()
        self.assertEqual(result["needs"], [])
        self.assertNotIn(f"{g}/loose", result["pages"])
        self.assertEqual(result["edges"], {"to_folder": 1, "total": 1})

    def test_a_page_only_page_keeps_a_prerequisite_named_under_both_kinds(self) -> None:
        g = "Algebra/groups"
        self.leaf(f"{g}/b/b-main.md", 20)
        self.leaf(f"{g}/a/a-main.md", 10, facts=None, statement=(f"{g}/b/b-main.md",), proof=(f"{g}/b/b-main.md",))
        self.card(f"{g}/a", 1, 10, ["a-main"])
        self.card(f"{g}/b", 2, 20, ["b-main"])
        result = self.rollup()
        [use] = result["uses"]
        self.assertEqual((use["statement"], use["proof"], use["origins"]), (1, 1, {"planned": 2}))
        self.assertEqual(result["edges"], {"card_to_card": 2, "total": 2})
        self.assertEqual(result["needs"][0]["phase"], "statement")

    def test_every_page_the_output_names_is_in_its_table(self) -> None:
        g = "Algebra/groups"
        self.leaf(f"{g}/a/a-main.md", 10)
        self.leaf(f"{g}/loose.md", 11)
        self.card(f"{g}/a", 1, 10, ["a-main"])
        result = self.rollup()
        self.assertEqual(result["unassigned"], [{"folder": g, "pages": [f"{g}/loose"]}])
        self.assertEqual(result["pages"][f"{g}/loose"]["card"], None)


class Integrity(Vault):
    """The compiled edges of the checkout equal the extraction's, both ways."""

    def setUp(self) -> None:
        super().setUp()
        self.g = g = "Algebra/groups"
        mathlib = {"object": [{"type": "lean", "uri": cards.sync.MATHLIB,
                               "location": {"declaration": "Mathlib.thing"}}],
                   "extensions": {"org.autoform": {"mathlib": True}}}
        self.page(f"{g}/m/m-main.md", "# m\n\nA Mathlib statement.\n", {"id": af(30), **mathlib})
        self.leaf(f"{g}/c/c-main.md", 40)
        self.leaf(f"{g}/b/b-main.md", 20)
        self.leaf(f"{g}/a/a-main.md", 10, statement=(f"{g}/b/b-main.md",), proof=(f"{g}/c/c-main.md",))
        for folder, number, main in (("a", 1, 10), ("b", 2, 20), ("c", 3, 40), ("m", 4, 30)):
            self.card(f"{g}/{folder}", number, main, [f"{folder}-main"])
        self.ledger_file()

    def extraction(self, statement: list[str], proof: list[str]) -> dict:
        empty = {"statement": [], "proof": []}
        return {"articles": {"Ext.a_main": {"statement": statement, "proof": proof}, "Ext.b_main": empty,
                             "Ext.c_main": empty}}

    def test_equal_sets_pass(self) -> None:
        # A proof dependency that is also a statement one is written as a statement dependency only.
        self.assertEqual(self.run_check(dependencies=self.extraction(["Ext.b_main"], ["Ext.c_main", "Ext.b_main"]))[0],
                         [])

    def test_a_proof_only_edge_never_certifies_a_statement_one(self) -> None:
        # The page lists c under both kinds; the extraction has c only as a proof dependency.
        page = wiki.ROADMAP / f"{self.g}/a/a-main.md"
        b, c = "- [b-main](../../../Algebra/groups/b/b-main.md)", "- [c-main](../../../Algebra/groups/c/c-main.md)"
        self.assertIn(b, page.read_text())
        page.write_text(page.read_text().replace(b, f"{b}\n{c}"))
        errors = self.run_check(dependencies=self.extraction(["Ext.b_main"], ["Ext.c_main"]))[0]
        self.assertIn(f"{self.g}/a/a-main: lists {self.g}/c/c-main as both a statement and a proof dependency", errors)
        self.assertIn(f"{self.g}/a/a-main: its dependency {self.g}/c/c-main is a statement dependency, but the "
                      "extraction records a proof one", errors)

    def test_an_annotation_without_its_page_credits_nothing(self) -> None:
        self.rows.append({"subject": [{"type": "generic", "uri": f"../roadmap/{self.g}/x/ghost.md"}], "id": af(77),
                          "object": [{"location": {"declaration": "Ext.ghost"}}]})
        extraction = self.extraction(["Ext.b_main"], ["Ext.c_main"])
        extraction["articles"]["Ext.ghost"] = {"statement": [], "proof": []}
        self.assertEqual(self.run_check(dependencies=extraction)[0],
                         ["the extraction records Ext.ghost, which credits no statement page"])

    def test_the_rollup_never_runs_on_edges_the_check_rejects(self) -> None:
        self.write()
        with self.assertRaises(ValueError):
            cards.rollup(self.extraction(["Ext.b_main"], []))

    def test_an_edge_the_extraction_lacks(self) -> None:
        self.assertEqual(self.run_check(dependencies=self.extraction(["Ext.b_main"], []))[0],
                         [f"{self.g}/a/a-main: its proof dependency {self.g}/c/c-main is not in the extraction"])

    def test_an_edge_the_page_lacks(self) -> None:
        extraction = self.extraction(["Ext.b_main"], ["Ext.c_main"])
        extraction["articles"]["Ext.b_main"] = {"statement": ["Ext.c_main"], "proof": []}
        self.assertEqual(self.run_check(dependencies=extraction)[0],
                         [f"{self.g}/b/b-main: the extraction records a statement dependency on {self.g}/c/c-main, "
                          "which the page lacks"])

    def test_a_flipped_kind(self) -> None:
        self.assertEqual(self.run_check(dependencies=self.extraction(["Ext.b_main", "Ext.c_main"], []))[0],
                         [f"{self.g}/a/a-main: its dependency {self.g}/c/c-main is a proof dependency, but the "
                          "extraction records a statement one"])

    def test_a_declaration_that_credits_no_page(self) -> None:
        extraction = self.extraction(["Ext.b_main"], ["Ext.c_main"])
        extraction["articles"]["Ext.lost"] = {"statement": ["Ext.b_main"], "proof": []}
        self.assertEqual(self.run_check(dependencies=extraction)[0],
                         ["the extraction records Ext.lost, which credits no statement page"])


class LegacyRows(Vault):
    """A row an earlier sync wrote with only a module and a name, `{"module": "Local", "name": "mark"}`, through the
    real Lean index, the extractor, lean-facts and the strict cards, run as the wiki job runs them on a committed
    vault. The Lean index decides, once: a row it resolves to one declaration gets that declaration's Lean link in
    the build, which Autoform and the cards then read; one it does not resolve credits nothing and is stale."""

    g = "Algebra/groups"
    entry = "Algebra/groups/topic/entry"
    hint = {"module": "Local", "name": "mark"}

    def build(self, local: str, row: dict, twin: dict | None = None) -> None:
        g = self.g
        (wiki.ROOT / "Local.lean").write_text(local)
        (wiki.ROOT / "Ext.lean").write_text("namespace Ext\ndef_wanted blocked : Prop\nend Ext\n")
        (wiki.ROOT / "Other.lean").write_text("namespace Elsewhere\ntheorem mark : True := trivial\nend Elsewhere\n")
        self.leaf(f"{self.entry}.md", 10, facts=None, row=row)
        self.card(f"{g}/topic", 1, 10, ["entry"])
        if twin is not None:
            self.leaf(f"{g}/second/twin.md", 40, facts=None, row=twin)
            self.card(f"{g}/second", 4, 40, ["twin"])
        self.leaf(f"{g}/block/blocked.md", 20)
        self.card(f"{g}/block", 2, 20, ["blocked"], kind="concept")
        self.mathlib_page(f"{g}/ref/External.md", 30, "M.Ref")
        self.card(f"{g}/ref", 3, 30, ["External"])
        self.ledger_file()
        self.write()
        git = lambda *argv: subprocess.run(["git", "-C", str(wiki.ROOT), *argv], check=True, capture_output=True)
        git("init", "-q")
        git("add", ".")
        git("-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "vault")

    def dump(self) -> list[dict]:
        """The dump of the Lean sources as they are: a row for each declaration, and the credited M.Ref."""
        from scripts.test_extract_v2_lean_dependencies import credited, row, with_mathlib
        local = (wiki.ROOT / "Local.lean").read_text()
        blocked = "Ext.blocked" in local
        rows = [{**with_mathlib(row("Ext.blocked", "def", [], []), [], []), "module": "Ext"},
                {**with_mathlib(row("Elsewhere.mark", "theorem", [], []), [], []), "module": "Other"},
                credited("M.Ref", "theorem", [], [])]
        if "namespace North" in local:
            rows.append({**with_mathlib(row("North.mark", "theorem", ["Ext.blocked"] if blocked else [], []), [],
                                        ["M.Ref"] if blocked else [], direct=["M.Ref"] if blocked else []),
                         "module": "Local"})
        if "namespace South" in local:
            rows.append({**with_mathlib(row("South.mark", "theorem", [], []), [], []), "module": "Local"})
        return rows

    def extract(self) -> tuple[int, str]:
        from scripts import extract_v2_lean_dependencies as extract
        from scripts.test_extract_v2_lean_dependencies import PIN, framed
        dump, names = self.tmp / "dump.jsonl", self.tmp / "names.txt"
        dump.write_text("".join(json.dumps(r) + "\n" for r in framed(self.dump())))
        names.write_text(cards.sync.names_text(cards.sync.credited_mathlib(cards.sync.read_annotations())[0]))
        with patch.object(extract, "BLUEPRINT", wiki.VAULT), patch.object(extract, "mathlib_revision", lambda: PIN), \
                patch("sys.argv", ["extract", str(dump), str(self.tmp / "deps.json"), "--registry",
                                   str(self.tmp / "registry.json"), "--names", str(names)]), \
                contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()) as errors:
            return extract.main(), errors.getvalue()

    def consume(self) -> tuple[int, int, dict | None, str]:
        """lean-facts, then the strict rollup, as the wiki job runs them: their statuses, the card data and what they
        printed on stderr."""
        from scripts.test_extract_v2_lean_dependencies import PIN
        deps, registry, output = self.tmp / "deps.json", self.tmp / "registry.json", self.tmp / "build" / "cards.json"
        with patch.object(cards.sync, "mathlib_revision", lambda: PIN), \
                contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()) as errors:
            synced = cards.sync.main(["lean-facts", str(deps), "--registry", str(registry)])
            rolled = cards.run(["rollup", str(output), "--dependencies", str(deps), "--registry", str(registry)])
        return synced, rolled, json.loads(output.read_text()) if output.exists() else None, errors.getvalue()

    def row(self) -> dict:
        return cards.read_annotations()[(wiki.ROADMAP / f"{self.entry}.md").resolve()]

    def test_a_resolved_row_gets_its_lean_link_and_its_status(self) -> None:
        # North.mark is proved, then stated with its proof unfinished on a real blocker: the build row gets
        # North.mark's Lean link, its edges, and Autoform's status for it, as a row with that Lean link does.
        for local, state in (("namespace North\ntheorem mark : True := trivial\nend North\n", "fully_proved"),
                             ("namespace North\ntheorem mark : Ext.blocked := by sorry\nend North\n", "stated")):
            with self.subTest(state=state):
                self.setUp()
                self.build(local, {"extensions": {"org.atlas-wiki": dict(self.hint)}})
                self.assertEqual(self.extract(), (0, ""))
                synced, rolled, data, errors = self.consume()
                self.assertEqual((synced, rolled), (0, 0), errors)
                self.assertEqual(self.row()["object"], [{"location": {"declaration": "North.mark"}, "role": "states"}])
                page = data["pages"][self.entry]
                self.assertEqual((page["credit"], page["stale"], page["state"]), ("atlas", False, state))
                if state == "stated":
                    self.assertEqual(sorted(tuple(e["origins"].items()) for e in data["uses"]),
                                     [(("bridge", 1),), (("compiled", 1),)])

    def test_an_ambiguous_row_stays_stale_beside_a_page_of_one_candidate(self) -> None:
        # Local.lean declares North.mark and South.mark, so the hint names no one declaration; another page credits
        # North.mark. The row credits nothing and is stale, and nothing reports a duplicate: the extraction's articles,
        # among which North.mark alone of the two, decide nothing.
        local = "namespace North\ntheorem mark : True := trivial\nend North\nnamespace South\ntheorem mark : True := " \
                "trivial\nend South\n"
        self.build(local, {"extensions": {"org.atlas-wiki": dict(self.hint)}},
                   twin={"object": [{"location": {"declaration": "North.mark"}}]})
        self.assertEqual(self.extract(), (0, ""))
        synced, rolled, data, errors = self.consume()
        self.assertEqual((synced, rolled), (0, 0), errors)
        self.assertNotIn("object", self.row())
        self.assertEqual((data["pages"][self.entry]["credit"], data["pages"][self.entry]["stale"]), ("none", True))
        self.assertNotIn("a declaration has one page", errors)

    def test_a_row_that_holds_back_what_its_hint_names_is_refused(self) -> None:
        # A held marker for North.mark beside a hint the index resolves to North.mark: the extraction refuses it, and
        # so does lean-facts, given the extraction made before the marker was added, without writing anything.
        self.build("namespace North\ntheorem mark : True := trivial\nend North\n",
                   {"extensions": {"org.atlas-wiki": dict(self.hint)}})
        self.assertEqual(self.extract(), (0, ""))
        rows = cards.sync.read_annotations()
        entry = next(row for group in rows.values() for row in group
                     if cards.sync.subject_path(row) == (wiki.ROADMAP / f"{self.entry}.md").resolve())
        entry["extensions"]["org.atlas-wiki"]["held"] = {"declaration": "North.mark", "reason": "false", "issue": 42}
        cards.sync.write_annotations(rows)
        subprocess.run(["git", "-C", str(wiki.ROOT), "-c", "user.name=fixture", "-c",
                        "user.email=fixture@example.invalid", "commit", "-qam", "held"], check=True)
        message = (f"{self.entry}.md (by the module and name an earlier sync wrote): it holds North.mark back but is "
                   "linked to North.mark")
        status, errors = self.extract()
        self.assertEqual(status, 1)
        self.assertIn(message, errors)
        before = {path: path.read_bytes() for path in wiki.VAULT.rglob("*") if path.is_file()}
        synced, _, _, errors = self.consume()
        self.assertEqual(synced, 1)
        self.assertIn(message, errors)
        self.assertEqual({path: path.read_bytes() for path in wiki.VAULT.rglob("*") if path.is_file()}, before)

    def test_a_held_row_without_a_hint_stays_held(self) -> None:
        held = {"declaration": "North.mark", "reason": "false", "issue": 42}
        self.build("namespace North\ntheorem mark : True := trivial\nend North\n",
                   {"extensions": {"org.atlas-wiki": {"held": held}}})
        self.assertEqual(self.extract()[0], 0)
        synced, rolled, data, errors = self.consume()
        self.assertEqual((synced, rolled), (0, 0), errors)
        page = data["pages"][self.entry]
        self.assertEqual((page["credit"], page["held"]), ("none", True))

    def test_a_declaration_named_twice_stops_the_extraction(self) -> None:
        # The hint resolves to North.mark, which another page credits by its Lean link, or by another such hint.
        for twin in ({"object": [{"location": {"declaration": "North.mark"}}]},
                     {"extensions": {"org.atlas-wiki": dict(self.hint)}}):
            with self.subTest(twin=twin):
                self.setUp()
                self.build("namespace North\ntheorem mark : True := trivial\nend North\n",
                           {"extensions": {"org.atlas-wiki": dict(self.hint)}}, twin=twin)
                status, errors = self.extract()
                self.assertEqual(status, 1)
                self.assertIn("stand for the declaration North.mark of this project; a declaration has one page",
                              errors)

    def test_a_checkout_an_earlier_run_synced_is_refused_and_a_clean_one_gives_the_result(self) -> None:
        # North.mark alone matches the module and name, and a first run links it. Then a commit changes only the
        # Lean: South.mark beside North.mark (the module and name now match two), or in its place. On the checkout
        # the first run synced, whose Lean link would read as authored, lean-facts refuses before it writes anything;
        # the clean checkout of that commit, its blueprint/ restored, gives no owner and a stale page, or South.mark
        # proved.
        from scripts import extract_v2_lean_dependencies as extract
        north = "namespace North\ntheorem mark : True := trivial\nend North\n"
        south = "namespace South\ntheorem mark : True := trivial\nend South\n"
        git = lambda *argv: subprocess.run(["git", "-C", str(wiki.ROOT), *argv], check=True, capture_output=True)

        def run() -> tuple:
            with patch.object(extract, "BLUEPRINT", wiki.VAULT):
                manifest = sorted(name for name in extract.article_manifest() if name.endswith(".mark"))
            self.assertEqual(self.extract(), (0, ""))
            synced, rolled, data, errors = self.consume()
            self.assertEqual((synced, rolled), (0, 0), errors)
            page = data["pages"][self.entry]
            return manifest, self.row().get("object"), page["credit"], page["stale"], page["state"]

        for local, owner in ((north + south, None), (south, "South.mark")):
            with self.subTest(owner=owner):
                self.setUp()
                self.build(north, {"extensions": {"org.atlas-wiki": dict(self.hint)}})
                link = lambda name: [{"location": {"declaration": name}, "role": "states"}]
                self.assertEqual(run(), (["North.mark"], link("North.mark"), "atlas", False, "fully_proved"))
                (wiki.ROOT / "Local.lean").write_text(local)
                git("add", "Local.lean")
                git("-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "Lean")
                synced = {path: path.read_bytes() for path in wiki.VAULT.rglob("*") if path.is_file()}
                self.assertEqual(self.extract()[0], 0)
                status, _, _, errors = self.consume()
                self.assertEqual(status, 1)
                self.assertIn("blueprint/ is not as committed", errors)
                self.assertEqual({path: path.read_bytes() for path in wiki.VAULT.rglob("*") if path.is_file()}, synced)
                git("checkout", "-q", "HEAD", "--", "blueprint")
                self.assertEqual(run(), ([owner], link(owner), "atlas", False, "fully_proved") if owner
                                 else ([], None, "none", True, "can_state"))

    def test_a_removed_declaration_leaves_the_row_stale(self) -> None:
        # North.mark is removed after an extraction was made: lean-facts gives the row no Lean link, and the strict
        # check refuses the old extraction, which records North.mark for no page; the fresh one leaves the page stale.
        self.build("namespace North\ntheorem mark : True := trivial\nend North\n",
                   {"extensions": {"org.atlas-wiki": dict(self.hint)}})
        self.assertEqual(self.extract(), (0, ""))
        (wiki.ROOT / "Local.lean").write_text("")
        synced, rolled, data, errors = self.consume()
        self.assertEqual((synced, rolled, data), (0, 1, None))
        self.assertIn("the extraction records North.mark, which credits no statement page", errors)
        self.assertNotIn("object", self.row())
        subprocess.run(["git", "-C", str(wiki.ROOT), "checkout", "-q", "--", "blueprint"], check=True)
        self.assertEqual(self.extract(), (0, ""))
        synced, rolled, data, errors = self.consume()
        self.assertEqual((synced, rolled), (0, 0), errors)
        self.assertEqual((data["pages"][self.entry]["credit"], data["pages"][self.entry]["stale"]), ("none", True))


class Progress(Vault):
    def test_the_main_statement_is_not_counted_among_the_supporting_ones(self) -> None:
        g = "Algebra/groups"
        self.leaf(f"{g}/a/a-main.md", 10)
        self.leaf(f"{g}/a/planned.md", 11, facts=None)
        self.leaf(f"{g}/a/held.md", 12, facts=None, row={"extensions": {"org.atlas-wiki": {
            "held": {"declaration": "Ext.held", "reason": "false", "issue": 1}}}})
        self.card(f"{g}/a", 1, 10, ["a-main", "planned", "held"])
        supporting = self.rollup()["cards"][0]["supporting"]
        self.assertEqual((supporting["total"], supporting["page_only"], supporting["held"], supporting["fully_proved"]),
                         (2, 1, 1, 0))

    def test_a_planned_main_statement_is_never_shown_as_ready(self) -> None:
        g = "Algebra/groups"
        self.leaf(f"{g}/a/helper.md", 11)
        self.leaf(f"{g}/a/a-main.md", 10, facts=None, statement=(f"{g}/a/helper.md",))
        self.card(f"{g}/a", 1, 10, ["a-main", "helper"])
        card = self.rollup()["cards"][0]
        # Autoform finds the page ready to state, as for every page-only leaf; a reader sees a planned page.
        self.assertEqual((card["main"]["state"], card["main"]["headline"]), ("can_state", "page_only"))
        self.assertEqual((card["supporting"]["total"], card["supporting"]["fully_proved"]), (1, 1))

    def test_a_planned_statement_with_a_kind_reads_as_its_state(self) -> None:
        # A planned page that counts as a statement not yet in Lean has the kind lean-facts gave it (docs/BLUEPRINT.md,
        # Writing pages): a task once ready, it reads as Autoform's state, not as page only.
        g = "Algebra/groups"
        self.leaf(f"{g}/a/helper.md", 11)
        self.leaf(f"{g}/a/a-main.md", 10, facts=None, statement=(f"{g}/a/helper.md",), row={"kind": "theorem"})
        self.leaf(f"{g}/a/planned.md", 12, facts=None, row={"kind": "def"})
        self.leaf(f"{g}/a/untyped.md", 13, facts=None)
        self.card(f"{g}/a", 1, 10, ["a-main", "helper", "planned", "untyped"])
        card = self.rollup()["cards"][0]
        self.assertEqual((card["main"]["state"], card["main"]["headline"]), ("can_state", "can_state"))
        supporting = card["supporting"]
        self.assertEqual((supporting["total"], supporting["fully_proved"], supporting["can_state"],
                          supporting["page_only"]), (3, 1, 1, 1))

    def test_markers_come_before_states(self) -> None:
        g = "Algebra/groups"
        self.leaf(f"{g}/a/a-main.md", 10, facts=None, row={"extensions": {
            "org.autoform": {"not_ready": True},
            "org.atlas-wiki": {"held": {"declaration": "Ext.a", "reason": "false", "issue": 1}}}})
        self.card(f"{g}/a", 1, 10, ["a-main"])
        card = self.rollup()["cards"][0]
        self.assertEqual(card["main"]["headline"], "held")
        self.assertEqual(card["supporting"]["total"], 0)


class Cycles(Vault):
    def test_mutual_use_is_a_cluster_and_needs_stays_acyclic(self) -> None:
        g = "Algebra/groups"
        self.leaf(f"{g}/x/x-def.md", 10, DEFINITION)
        self.leaf(f"{g}/y/y-def.md", 20, DEFINITION)
        self.leaf(f"{g}/x/x-fact.md", 11, statement=(f"{g}/x/x-def.md", f"{g}/y/y-def.md"))
        self.leaf(f"{g}/y/y-fact.md", 21, statement=(f"{g}/y/y-def.md", f"{g}/x/x-def.md"))
        self.card(f"{g}/x", 1, 10, ["x-def", "x-fact"], kind="concept")
        self.card(f"{g}/y", 2, 20, ["y-def", "y-fact"], kind="concept")
        result = self.rollup()
        self.assertEqual([(e["from"], e["to"]) for e in result["uses"]], [(af(1), af(2)), (af(2), af(1))])
        self.assertEqual(result["clusters"], [{"cards": [af(1), af(2)], "edges": [[af(1), af(2)], [af(2), af(1)]],
                                               "example_cycle": [af(1), af(2), af(1)]}])
        self.assertEqual(result["needs"], [])


class Check(Vault):
    def setUp(self) -> None:
        super().setUp()
        self.g = "Algebra/groups"
        self.leaf(f"{self.g}/a/a-main.md", 10)
        self.leaf(f"{self.g}/a/a-lemma.md", 11)
        self.leaf(f"{self.g}/d/d-def.md", 20, DEFINITION)

    def errors(self, **options) -> list[str]:
        return self.run_check(**options)[0]

    def assert_found(self, expected: str, errors: list[str]) -> None:
        self.assertTrue(any(expected in error for error in errors), (expected, errors))

    def test_a_card_credits_nothing_and_needs_an_id(self) -> None:
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"],
                  row={"extensions": {"org.autoform": {"navigation": "module", "mathlib": True}}})
        self.rows[-1].pop("id")
        self.rows[-1]["object"] = [{"location": {"declaration": "Ext.a_main"}}]
        errors = self.errors()
        self.assert_found("needs an `id`", errors)
        self.assert_found("no `object`", errors)
        self.assert_found("no `org.autoform` key `mathlib`", errors)
        self.assertFalse(any("`navigation`" in error for error in errors), errors)

    def test_a_record_that_is_no_object_is_reported_not_raised(self) -> None:
        for record in (None, [], "a card"):
            self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], supports=[af(20)])
            self.rows[-1]["extensions"]["org.atlas-wiki"]["card"] = record
            self.assert_found("the card record is not an object", self.errors())

    def test_the_record_keys_and_values(self) -> None:
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], importance="huge", colour="blue",
                  seeds=[{"source": "mathgraph", "node": "n1", "revision": "c7df2d47"}])
        errors = self.errors()
        self.assert_found("unknown card key `colour`", errors)
        self.assert_found("`importance` is 'huge'", errors)
        self.assert_found("a full commit", errors)

    def test_the_main_statement_is_a_page_of_the_folder(self) -> None:
        self.card(f"{self.g}/a", 1, 20, ["a-main", "a-lemma"])
        self.assert_found("not a statement page of this folder", self.errors())

    def test_a_credited_main_statement_matches_the_card_kind(self) -> None:
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], kind="concept")
        self.card(f"{self.g}/d", 2, 20, ["d-def"], kind="result")
        errors = self.errors()
        self.assert_found("a concept card's main statement Algebra/groups/a/a-main is a `theorem`", errors)
        self.assert_found("a result card's main statement Algebra/groups/d/d-def is a `def`", errors)

    def test_a_mathlib_main_statement_without_the_registry(self) -> None:
        # Without the build's registry, a kind lean-facts gave still has to fit; with no kind, a warning.
        mathlib = {"object": [{"type": "lean", "uri": cards.sync.MATHLIB, "location": {"declaration": "Mathlib.thm"}}],
                   "extensions": {"org.autoform": {"mathlib": True}}, "kind": "theorem"}
        self.page(f"{self.g}/m/m-main.md", "# m\n\nA Mathlib theorem.\n", {"id": af(40), **mathlib})
        self.card(f"{self.g}/m", 4, 40, ["m-main"], kind="concept")
        self.write()
        self.assertIn(f"{self.g}/m: a concept card's main statement Algebra/groups/m/m-main is a `theorem`",
                      cards.check()[0])
        mathlib.pop("kind")
        self.page(f"{self.g}/m/m-main.md", "# m\n\nA Mathlib theorem.\n", {"id": af(40), **mathlib})
        self.write()
        errors, warnings = cards.check()[:2]
        self.assertFalse([error for error in errors if "m-main" in error], errors)
        self.assertTrue(any("the kind of the Mathlib main statement Algebra/groups/m/m-main is unknown without the "
                            "build's registry" in warning for warning in warnings), warnings)

    def test_a_page_only_main_statement_is_classified_by_its_editors(self) -> None:
        self.leaf(f"{self.g}/p/p-main.md", 30, facts=None)
        self.card(f"{self.g}/p", 3, 30, ["p-main"], kind="concept")
        self.assertEqual(self.errors(), [])

    def test_a_planned_main_statement_with_a_kind_matches_the_card_kind(self) -> None:
        # A planned main that counts as a statement not yet in Lean has the kind lean-facts gave it, which has to fit
        # the card as a credited main's kind does.
        self.leaf(f"{self.g}/p/p-main.md", 30, facts=None, row={"kind": "def"})
        self.card(f"{self.g}/p", 3, 30, ["p-main"], kind="result")
        self.leaf(f"{self.g}/q/q-main.md", 31, facts=None, row={"kind": "theorem"})
        self.card(f"{self.g}/q", 4, 31, ["q-main"], kind="result")
        errors = self.errors()
        self.assert_found("a result card's main statement Algebra/groups/p/p-main is a `def`", errors)
        self.assertFalse([error for error in errors if "q-main" in error], errors)

    def test_supports_point_outside_the_card(self) -> None:
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], supports=[af(11), af(20), af(99)])
        errors = self.errors()
        self.assert_found("a statement of this card", errors)
        self.assert_found(f"names '{af(99)}'", errors)
        self.assertFalse(any("Algebra/groups/d/d-def" in error for error in errors), errors)

    def test_the_rollup_title_is_the_rendered_title(self) -> None:
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"],
                  body="# *Card* a\n\nWhat the card says.\n\n## Idea\n\nWhy it matters.\n\n## Statements\n\n"
                       "- [a-main](a-main.md)\n- [a-lemma](a-lemma.md)\n")
        rolled = self.rollup()
        self.assertEqual([card["title"] for card in rolled["cards"] if card["main"]["article_id"] == af(10)], ["Card a"])

    def test_a_card_links_another_card_only_under_background(self) -> None:
        # The opening and `## Idea` link card d's page; `## Background` may, and a link to d's main statement may.
        self.card(f"{self.g}/d", 2, 20, ["d-def"], kind="concept")
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"],
                  body="# Card a\n\nIt builds on [card d](../d/README.md).\n\n## Idea\n\nSee [d](../d/README.md) "
                       "and [its main statement](../d/d-def.md).\n\n## Statements\n\n- [a-main](a-main.md)\n"
                       "- [a-lemma](a-lemma.md)\n\n## Background\n\n- [Card d](../d/README.md)\n")
        errors = self.errors()
        for part in ("its opening", "`## Idea`"):
            self.assert_found(f"{part} links the card {self.g}/d; a card links another card only under "
                              "`## Background`", errors)
        self.assertEqual(len([error for error in errors if "links the card" in error]), 2, errors)
        # A link in the title or a section heading, or one with a query, is a link outside Background too.
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"],
                  body="# Card a, after [card d](../d/README.md)\n\nIt builds on d.\n\n## Idea\n\nSee "
                       "[d](../d/README.md?x=1) and [its folder](../d/).\n\n## Related [Card d](../d/README.md)\n\nMore.\n\n"
                       "## Statements\n\n- [a-main](a-main.md)\n- [a-lemma](a-lemma.md)\n\n## Background\n\n"
                       "- [Card d](../d/README.md?y=2#top)\n")
        errors = self.errors()
        self.assertEqual(len([error for error in errors if "links the card" in error]), 4, errors)
        self.assert_found(f"a heading links the card {self.g}/d", errors)
        self.assertFalse(any("`## Background` links" in error for error in errors), errors)

    def test_each_page_is_linked_once_in_statements(self) -> None:
        # A nested link to the lemma under the main statement's item, beside the lemma's own item; a prose link to a
        # page of another folder.
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"],
                  body="# Card a\n\nWhat it says.\n\n## Idea\n\nWhy.\n\n## Statements\n\n- [a-main](a-main.md)\n"
                       "    - with [the lemma](a-lemma.md)\n- [a-lemma](a-lemma.md), see [d](../d/d-def.md), "
                       "[its box](#a-lemma), [again](?view=reading#a-lemma), [d's box](../d/README.md#d-def) and "
                       "[the idea](#idea)\n")
        # A page-only page named like a heading has a page of its own, so `#idea` is the heading's anchor.
        self.leaf(f"{self.g}/a/idea.md", 12, facts=None)
        errors = self.errors()
        for href in ("#a-lemma", "?view=reading#a-lemma", "../d/README.md#d-def"):
            self.assert_found(f"`## Statements` links {href}, a statement's box on a folder page", errors)
        self.assertFalse(any("#idea" in error for error in errors), errors)
        self.assert_found("`## Statements` links a-lemma.md again, after its item", errors)
        self.assert_found("`## Statements` links ../d/d-def.md, which is not a statement page of this card", errors)

    def test_a_card_folder_never_carries_an_earlier_sync_s_declaration_credit(self) -> None:
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"])
        self.rows[-1]["extensions"]["org.atlas-wiki"].update(module="Ext", name="a_main")
        errors = self.errors()
        for key in ("module", "name"):
            self.assert_found(f"has no `org.atlas-wiki` key `{key}`", errors)

    def test_outside_background_a_card_links_another_card_only_through_its_main_statement(self) -> None:
        self.leaf(f"{self.g}/d/d-lemma.md", 21, DEFINITION)
        self.card(f"{self.g}/d", 2, 20, ["d-def", "d-lemma"], kind="concept")
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"],
                  body="# Card a\n\nIt uses [the definition](../d/d-def.md).\n\n## Idea\n\nSee "
                       "[a lemma of d](../d/d-lemma.md).\n\n## Statements\n\n- [a-main](a-main.md)\n"
                       "- [a-lemma](a-lemma.md)\n")
        errors = self.errors()
        self.assert_found(f"`## Idea` links {self.g}/d/d-lemma, a statement of the card {self.g}/d that is not its "
                          "main statement", errors)
        self.assertFalse(any("d/d-def," in error for error in errors), errors)

    def test_a_card_is_no_subfield_and_no_part_folder(self) -> None:
        (wiki.ROOT / "scripts" / "taxonomy.json").write_text(json.dumps({"subjects": {"Algebra": {"fields": [
            {"slug": "groups", "subfields": [{"slug": "finite"}]}]}}}))
        for folder in (f"{self.g}/finite", f"{self.g}/part-02"):
            with self.subTest(folder=folder):
                self.rows.clear()
                self.leaf(f"{folder}/x-main.md", 30)
                self.card(folder, 3, 30, ["x-main"])
                self.assert_found(f"{folder}: a card is a topic folder or a folder inside one, never a", self.errors())

    def test_a_card_is_not_its_own_background(self) -> None:
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"],
                  body="# Card a\n\nWhat it says.\n\n## Idea\n\nWhy.\n\n## Statements\n\n- [a-main](a-main.md)\n"
                       "- [a-lemma](a-lemma.md)\n\n## Background\n\n- [This card](README.md)\n")
        warnings = self.run_check()[1]
        self.assertTrue(any(f"{self.g}/a: `## Background` links the card itself" in warning for warning in warnings),
                        warnings)

    def test_supports_name_live_statement_pages(self) -> None:
        # An annotation whose page is gone is no statement a card can lean on.
        self.rows.append({"subject": [{"type": "generic", "uri": f"../roadmap/{self.g}/x/ghost.md"}], "id": af(77)})
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], supports=[af(77)])
        self.assert_found(f"`supports` names {af(77)}, whose page {self.g}/x/ghost is missing", self.errors())

    def test_supports_name_statement_pages_autoform_reads(self) -> None:
        # A real file with an annotation that Autoform does not read as a statement (a hidden page, which its loader
        # passes over), beside a real statement page.
        self.page(f"{self.g}/x/.other.md", "# Not a statement\n", {"id": af(78)})
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], supports=[af(78), af(20)])
        errors = self.errors()
        self.assert_found(f"`supports` names {af(78)}, whose file {self.g}/x/.other.md is no statement page "
                          "Autoform reads", errors)
        self.assertFalse(any(af(20) in error or "d/d-def" in error for error in errors), errors)

    def test_the_page_has_its_sections_and_no_hand_written_edges(self) -> None:
        body = ("---\narea: Algebra\n---\n\n# A\n\n<!-- no statement yet -->\n\n## Idea\n\n<!-- later -->\n\n"
                "## Statements\n\n- [a-lemma](a-lemma.md)\n- [d](../d/d-def.md)\n- [a-lemma](a-lemma.md)\n\n"
                "## Depends on\n\n- [d](../d/d-def.md)\n")
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], body=body)
        errors = self.errors()
        for expected in ("no frontmatter", "no statement or summary", "needs an `## Idea`", "does not list a-main.md",
                         "lists a-lemma.md 2 times", "lists ../d/d-def.md, which is not a statement page",
                         "lists a-lemma.md first", "no `## Depends on`"):
            self.assert_found(expected, errors)

    def test_a_heading_in_a_fence_opens_no_section(self) -> None:
        body = ("# A\n\nIt says.\n\n```\n## Depends on\n```\n\n## Idea\n\nWhy.\n\n## Statements\n\n"
                "- [a-main](a-main.md)\n- [a-lemma](a-lemma.md) used in the proof\n")
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], body=body)
        self.assertEqual(self.errors(), [])

    def test_a_heading_reads_without_its_comments(self) -> None:
        # Autoform reads `## Depends <!-- note -->on` as `## Depends on`: an edge from the card itself.
        body = ("# A\n\nIt says.\n\n## Idea\n\nWhy.\n\n## Statements\n\n- [a-main](a-main.md)\n- [a-lemma](a-lemma.md)\n\n"
                "## Depends <!-- note -->on\n\n- [d](../d/d-def.md)\n")
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], body=body)
        errors = self.errors()
        self.assert_found("no `## Depends on`", errors)
        self.assert_found("Autoform reads dependencies on the card's page", errors)

    def test_only_published_list_items_list_a_statement(self) -> None:
        cases = {
            "commented": "- [a-main](a-main.md)\n<!-- - [a-lemma](a-lemma.md) -->\n",
            "fenced": "```\n- [a-main](a-main.md)\n- [a-lemma](a-lemma.md)\n```\n",
            "inline code": "- [a-main](a-main.md)\n- `[a-lemma](a-lemma.md)`\n",
            "a paragraph": "- [a-main](a-main.md)\n\nSee [a-lemma](a-lemma.md).\n",
        }
        for name, listing in cases.items():
            with self.subTest(name):
                self.rows = [row for row in self.rows if not row["subject"][0]["uri"].endswith("/a/README.md")]
                body = f"# A\n\nIt says.\n\n## Idea\n\nWhy.\n\n## Statements\n\n{listing}"
                self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], body=body)
                self.assert_found("does not list a-lemma.md", self.errors())

    def test_the_page_is_checked_as_the_site_publishes_and_renders_it(self) -> None:
        cases = {
            # Raw HTML makes Autoform publish the whole page as typed, with no live link.
            "raw html": ("Why.<br>Indeed.", "- [a-main](a-main.md)\n- [a-lemma](a-lemma.md)\n",
                         "would publish the card's page as typed"),
            # A list run into the paragraph before it is no list.
            "no list": ("Why.", "The statements:\n- [a-main](a-main.md)\n- [a-lemma](a-lemma.md)\n",
                        "does not list a-main.md"),
            "no label": ("Why.", "- [a-main](a-main.md)\n- [](a-lemma.md)\n", "has no text a reader can see"),
        }
        for name, (idea, listing, expected) in cases.items():
            with self.subTest(name):
                self.rows = [row for row in self.rows if not row["subject"][0]["uri"].endswith("/a/README.md")]
                body = f"# A\n\nIt says.\n\n## Idea\n\n{idea}\n\n## Statements\n\n{listing}"
                self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], body=body)
                self.assert_found(expected, self.errors())

    def test_the_list_is_read_from_the_whole_rendered_page(self) -> None:
        # Code in a label is visible; a reference link defined later on the page is live; formatting is fine.
        body = ("# A\n\nIt says.\n\n## Idea\n\nWhy.\n\n## Statements\n\n- [`a-main`](a-main.md)\n"
                "- *[the lemma][lemma]*: used in the proof\n\n## Sources\n\n- A book.\n\n[lemma]: a-lemma.md\n")
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], body=body)
        self.assertEqual(self.errors(), [])

    def test_a_section_is_written_once(self) -> None:
        body = ("# A\n\nIt says.\n\n## Idea\n\nWhy.\n\n## Statements\n\n- [a-main](a-main.md)\n"
                "- [a-lemma](a-lemma.md)\n\n## Statements\n\n- [d](../d/d-def.md)\n")
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], body=body)
        self.assert_found("has two `## Statements` sections", self.errors())

    def test_an_item_opens_with_its_link_by_position(self) -> None:
        body = ("# A\n\nIt says.\n\n## Idea\n\nWhy.\n\n## Statements\n\n- [a-main](a-main.md)\n"
                "- a-lemma evidence: [a-lemma](a-lemma.md)\n")
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], body=body)
        self.assert_found("does not open with a link to a statement page", self.errors())

    def test_every_item_opens_with_its_statement_link(self) -> None:
        body = ("# A\n\nIt says.\n\n## Idea\n\nWhy.\n\n## Statements\n\n- [a-main](a-main.md)\n"
                "- the lemma, [a-lemma](a-lemma.md)\n")
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], body=body)
        self.assert_found("does not open with a link to a statement page", self.errors())

    def test_a_card_record_on_a_statement_page_is_an_error(self) -> None:
        row = next(row for row in self.rows if row["subject"][0]["uri"].endswith("/a/a-main.md"))
        row["extensions"] = {"org.atlas-wiki": {"card": {"kind": "result", "main_article_id": af(10),
                                                         "importance": "key", "level": "graduate"}}}
        self.assertEqual(self.errors(), [f"{self.g}/a/a-main: a card record belongs on a folder page, not on a "
                                         "statement page"])

    def test_cards_do_not_nest_sit_below_a_field_and_hold_at_most_24(self) -> None:
        self.leaf(f"{self.g}/a/inner/x.md", 12)
        self.page(f"{self.g}/a/inner/README.md", "# Inner\n\n- [x](x.md)\n")
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"])
        self.leaf("Algebra/top.md", 30)
        self.card("Algebra", 2, 30, ["top"])
        for number in range(25):
            self.leaf(f"{self.g}/big/s{number}.md", 100 + number)
        self.card(f"{self.g}/big", 3, 100, [f"s{number}" for number in range(25)])
        errors = self.errors()
        self.assert_found("not the folder Algebra/groups/a/inner", errors)
        self.assert_found("never a subject or a field", errors)
        self.assert_found("25 statements; a card holds at most 24", errors)

    def test_a_statement_never_depends_on_a_card(self) -> None:
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"])
        self.leaf(f"{self.g}/d/d-fact.md", 21, statement=(f"{self.g}/a/README.md",))
        self.card(f"{self.g}/d", 2, 20, ["d-def", "d-fact"], kind="concept")
        self.assert_found("depends on the card Algebra/groups/a", self.errors())

    def test_a_leaf_seed_is_checked(self) -> None:
        lemma = next(row for row in self.rows if row["subject"][0]["uri"].endswith("/a/a-lemma.md"))
        lemma["extensions"] = {"org.atlas-wiki": {"seed": {"source": "mathgraph", "node": "n2"}}}
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"])
        self.assert_found("Algebra/groups/a/a-lemma: its `seed`", self.errors())

    def test_background_links_are_teaching_links_between_cards(self) -> None:
        body = ("# A\n\nIt says.\n\n## Idea\n\nWhy.\n\n## Statements\n\n- [a-main](a-main.md)\n- [a-lemma](a-lemma.md)\n\n"
                "## Background\n\n- [D](../d/README.md)\n- [Lemma](a-lemma.md)\n")
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], body=body)
        back = "# D\n\nIt says.\n\n## Idea\n\nWhy.\n\n## Statements\n\n- [d-def](d-def.md)\n\n## Background\n\n- [A](../a/README.md)\n"
        self.card(f"{self.g}/d", 2, 20, ["d-def"], kind="concept", body=back)
        errors, warnings = self.run_check()
        self.assertEqual(errors, [])
        self.assert_found("links a-lemma.md, which is not a card's page", warnings)
        self.assert_found("go round", warnings)

    def test_a_valid_card_passes(self) -> None:
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], supports=[af(20)],
                  seeds=[{"source": "mathgraph", "node": "mg-1", "revision": COMMIT}])
        self.card(f"{self.g}/d", 2, 20, ["d-def"], kind="concept")
        self.assertEqual(self.run_check(), ([], []))


class Moves(Vault):
    def setUp(self) -> None:
        super().setUp()
        self.g = "Algebra/groups"
        self.leaf(f"{self.g}/a/a-main.md", 10)
        self.leaf(f"{self.g}/a/a-lemma.md", 11)
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"])

    def ledger(self, *rows: dict) -> list[str]:
        (wiki.ROOT / "scripts" / cards.MOVES).write_text("".join(json.dumps(row) + "\n" for row in rows))
        return self.run_check()[0]

    def test_a_split_that_keeps_its_source_folder(self) -> None:
        # The lemma left the topic folder for the new card; the topic folder stays.
        self.assertEqual(self.ledger({"page": f"{self.g}/a-lemma", "to": f"{self.g}/a/a-lemma",
                                      "article_id": af(11)}), [])

    def test_a_page_moved_twice(self) -> None:
        self.assertEqual(self.ledger({"page": f"{self.g}/old", "to": f"{self.g}/mid", "article_id": af(10)},
                                     {"page": f"{self.g}/mid", "to": f"{self.g}/a/a-main", "article_id": af(10)}), [])

    def test_a_pure_folder_rename(self) -> None:
        self.assertEqual(self.ledger({"folder": f"{self.g}/old-a", "to": f"{self.g}/a", "article_id": af(1)}), [])

    def test_a_merge_whose_source_folder_vanished(self) -> None:
        self.assertEqual(self.ledger({"page": f"{self.g}/z/z-main", "to": f"{self.g}/a/a-lemma", "article_id": af(11)},
                                     {"card": af(7), "folder": f"{self.g}/z", "replaced_by": af(1)}), [])

    def test_a_leaf_that_had_no_id_must_get_one_before_it_moves(self) -> None:
        lemma = next(row for row in self.rows if row["subject"][0]["uri"].endswith("/a/a-lemma.md"))
        lemma.pop("id")
        errors = self.ledger({"page": f"{self.g}/a-lemma", "to": f"{self.g}/a/a-lemma", "article_id": af(11)})
        self.assertEqual(errors, [f"card-moves.jsonl: {self.g}/a-lemma ends at {self.g}/a/a-lemma, but {af(11)} is "
                                  "no statement page"])

    def test_an_old_address_keeps_leading_to_its_own_article(self) -> None:
        errors = self.ledger({"page": f"{self.g}/old", "to": f"{self.g}/mid", "article_id": af(11)},
                             {"page": f"{self.g}/mid", "to": f"{self.g}/a/a-main", "article_id": af(10)})
        self.assertTrue(any(f"{self.g}/old moved as {af(11)} to {self.g}/mid, which moved on as {af(10)}" in error
                            for error in errors), errors)

    def test_a_renamed_card_folder_may_then_be_retired(self) -> None:
        self.assertEqual(self.ledger({"folder": f"{self.g}/z-old", "to": f"{self.g}/z", "article_id": af(7)},
                                     {"card": af(7), "folder": f"{self.g}/z", "replaced_by": af(1)}), [])
        errors = self.ledger({"folder": f"{self.g}/z-old", "to": f"{self.g}/z", "article_id": af(7)},
                             {"card": af(7), "folder": f"{self.g}/elsewhere", "replaced_by": af(1)})
        self.assertTrue(any("was retired at Algebra/groups/elsewhere" in error for error in errors), errors)

    def test_retirements_and_addresses_are_checked(self) -> None:
        errors = self.ledger({"card": af(7), "folder": f"{self.g}/z", "replaced_by": af(1)},
                             {"card": af(7), "folder": f"{self.g}/z", "replaced_by": af(1)},
                             {"card": "seven", "folder": f"{self.g}/y", "replaced_by": af(1)},
                             {"card": af(11), "folder": f"{self.g}/x", "replaced_by": af(1)},
                             {"page": f"{self.g}/p.md", "to": f"{self.g}/../q", "article_id": af(10)})
        for expected in (f"the card {af(7)} is already retired", "`card` and `replaced_by` are article ids",
                         f"the retired card {af(11)} is still the id of {self.g}/a/a-lemma",
                         "an address is a path below roadmap/ without `.md`"):
            self.assertTrue(any(expected in error for error in errors), (expected, errors))

    def test_an_address_has_one_owner(self) -> None:
        errors = self.ledger({"page": f"{self.g}/x", "to": f"{self.g}/a/a-main", "article_id": af(10)},
                             {"folder": f"{self.g}/x", "to": f"{self.g}/a", "article_id": af(1)})
        self.assertTrue(any(f"{self.g}/x moved both as a page and as a folder" in error for error in errors), errors)
        # A live folder of another article on a moved page's address.
        self.leaf(f"{self.g}/z/z-main.md", 30)
        self.card(f"{self.g}/z", 3, 30, ["z-main"])
        errors = self.ledger({"page": f"{self.g}/z", "to": f"{self.g}/a/a-main", "article_id": af(10)})
        self.assertTrue(any(f"{self.g}/z moved as a page, and another article's folder now holds the address" in error
                            for error in errors), errors)

    def test_every_move_since_the_base_has_its_row(self) -> None:
        # The base had a-lemma beside the card, with an id, and a-main's declaration on a page without an id.
        self.write()
        base = cards.read_annotations()
        lemma, main = (wiki.ROADMAP / f"{self.g}/a/a-lemma.md").resolve(), (wiki.ROADMAP / f"{self.g}/a/a-main.md").resolve()
        base[(wiki.ROADMAP / f"{self.g}/a-lemma.md").resolve()] = base.pop(lemma)
        old_main = dict(base.pop(main))
        old_main.pop("id")
        base[(wiki.ROADMAP / f"{self.g}/old-main.md").resolve()] = old_main
        moves = wiki.ROOT / "scripts" / cards.MOVES
        moves.write_text("")
        errors = cards.check(base_annotations=base)[0]
        self.assertIn(f"{cards.MOVES}: {self.g}/a-lemma is now {self.g}/a/a-lemma, and no row leads there", errors)
        self.assertIn(f"{cards.MOVES}: {self.g}/old-main is now {self.g}/a/a-main, and no row leads there", errors)
        moves.write_text("".join(json.dumps(row) + "\n" for row in (
            {"page": f"{self.g}/a-lemma", "to": f"{self.g}/a/a-lemma", "article_id": af(11)},
            {"page": f"{self.g}/old-main", "to": f"{self.g}/a/a-main", "article_id": af(10)})))
        self.assertEqual(cards.check(base_annotations=base)[0], [])

    def test_an_article_never_goes_without_a_row(self) -> None:
        # The base had a page beside the card that is gone, with its annotation, and no row moves it.
        self.write()
        base = cards.read_annotations()
        base[(wiki.ROADMAP / f"{self.g}/gone.md").resolve()] = {
            "subject": [{"type": "generic", "uri": f"../roadmap/{self.g}/gone.md"}], "id": af(12)}
        (wiki.ROOT / "scripts" / cards.MOVES).write_text("")
        self.assertIn(f"{cards.MOVES}: {self.g}/gone ({af(12)}) is gone, and no row moves it; an article keeps its "
                      "address or moves with its row", cards.check(base_annotations=base)[0])

    def test_a_page_never_lands_on_a_folder_s_address(self) -> None:
        # The base had a page beside the card folder; the change moves it onto the folder's address.
        self.page(f"{self.g}/a.md", "# A page\n\nIt moved onto the folder's address.\n", {"id": af(12)})
        self.write()
        base = cards.read_annotations()
        base[(wiki.ROADMAP / f"{self.g}/x.md").resolve()] = base.pop((wiki.ROADMAP / f"{self.g}/a.md").resolve())
        (wiki.ROOT / "scripts" / cards.MOVES).write_text(
            json.dumps({"page": f"{self.g}/x", "to": f"{self.g}/a", "article_id": af(12)}) + "\n")
        errors = cards.check(base_annotations=base)[0]
        self.assertTrue(any(f"{self.g}/a already holds another article" in error for error in errors), errors)
        self.assertIn(f"{cards.MOVES}: {self.g}/a is both a page and a folder; an address has one article", errors)
        self.assertTrue(any(error.startswith("Autoform cannot load the wiki") for error in errors), errors)

    def test_a_card_that_is_gone_needs_its_retirement(self) -> None:
        self.write()
        base = cards.read_annotations()
        record = {"kind": "result", "main_article_id": af(11), "importance": "key", "level": "graduate"}
        base[(wiki.ROADMAP / f"{self.g}/z/README.md").resolve()] = {
            "subject": [{"type": "generic", "uri": f"../roadmap/{self.g}/z/README.md"}], "id": af(7),
            "extensions": {"org.atlas-wiki": {"card": record}}}
        moves = wiki.ROOT / "scripts" / cards.MOVES
        moves.write_text("")
        self.assertIn(f"{cards.MOVES}: the card {af(7)} at {self.g}/z is no card any more, and no row retires it",
                      cards.check(base_annotations=base)[0])
        moves.write_text(json.dumps({"card": af(7), "folder": f"{self.g}/z", "replaced_by": af(1)}) + "\n")
        self.assertEqual(cards.check(base_annotations=base)[0], [])

    def base_with(self, moved: dict[str, str], ids: dict[str, str | None] | None = None) -> dict:
        """The checkout's annotations as the base had them: each page of ``moved`` (new -> old path) at its old
        path, with the id ``ids`` gives it (None drops it)."""
        self.write()
        base = cards.read_annotations()
        for new, old in moved.items():
            row = dict(base.pop((wiki.ROADMAP / f"{new}.md").resolve()))
            if ids and old in ids:
                if ids[old] is None:
                    row.pop("id", None)
                else:
                    row["id"] = ids[old]
            base[(wiki.ROADMAP / f"{old}.md").resolve()] = row
        return base

    def test_a_page_git_saw_renamed_needs_its_row_even_without_an_id(self) -> None:
        # A page-only page without an id at the base moves and gets one; Git's rename is the evidence.
        g = self.g
        self.leaf(f"{g}/a/after.md", 12, facts=None)
        self.card(f"{g}/a", 1, 10, ["a-main", "a-lemma", "after"])
        base = self.base_with({f"{g}/a/after": f"{g}/before"}, {f"{g}/before": None})
        (wiki.ROOT / "scripts" / cards.MOVES).write_text("")
        renames = [(f"{g}/before.md", f"{g}/a/after.md")]
        self.assertIn(f"{cards.MOVES}: {g}/before is now {g}/a/after, and no row leads there",
                      cards.check(base_annotations=base, renames=renames)[0])
        (wiki.ROOT / "scripts" / cards.MOVES).write_text(
            json.dumps({"page": f"{g}/before", "to": f"{g}/a/after", "article_id": af(12)}) + "\n")
        self.assertEqual(cards.check(base_annotations=base, renames=renames)[0], [])

    def test_a_new_row_names_the_article_its_old_address_held(self) -> None:
        g = self.g
        base = self.base_with({f"{g}/a/a-lemma": f"{g}/old-lemma"}, {f"{g}/old-lemma": af(16)})
        (wiki.ROOT / "scripts" / cards.MOVES).write_text(
            json.dumps({"page": f"{g}/old-lemma", "to": f"{g}/a/a-lemma", "article_id": af(11)}) + "\n")
        errors = cards.check(base_annotations=base, renames=[(f"{g}/old-lemma.md", f"{g}/a/a-lemma.md")])[0]
        self.assertIn(f"{cards.MOVES}:1: {g}/old-lemma is {af(16)}, not {af(11)}", errors)

    def test_an_article_keeps_its_id_at_its_address(self) -> None:
        self.write()
        base = cards.read_annotations()
        base[(wiki.ROADMAP / f"{self.g}/a/a-lemma.md").resolve()]["id"] = af(16)
        (wiki.ROOT / "scripts" / cards.MOVES).write_text("")
        self.assertTrue(any("an article keeps its id" in error for error in cards.check(base_annotations=base)[0]))

    def test_a_retirement_names_the_card_s_last_address(self) -> None:
        g = self.g
        self.write()
        base = cards.read_annotations()
        record = {"kind": "result", "main_article_id": af(11), "importance": "key", "level": "graduate"}
        base[(wiki.ROADMAP / f"{g}/z/README.md").resolve()] = {
            "subject": [{"type": "generic", "uri": f"../roadmap/{g}/z/README.md"}], "id": af(7),
            "extensions": {"org.atlas-wiki": {"card": record}}}
        moves = wiki.ROOT / "scripts" / cards.MOVES
        moves.write_text(json.dumps({"card": af(7), "folder": f"{g}/bogus", "replaced_by": af(1)}) + "\n")
        self.assertIn(f"{cards.MOVES}:1: the card {af(7)} is at {g}/z, not {g}/bogus",
                      cards.check(base_annotations=base)[0])
        moves.write_text("".join(json.dumps(row) + "\n" for row in (
            {"card": af(7), "folder": f"{g}/z", "replaced_by": af(1)},
            {"page": f"{g}/z", "to": f"{g}/a/a-lemma", "article_id": af(11)})))
        self.assertTrue(any(f"{g}/z is the last address of the retired card {af(7)} and moved too" in error
                            for error in cards.check(base_annotations=base)[0]))

    def test_an_id_minted_on_a_move_is_no_other_article_s(self) -> None:
        # anon (no id) moves to after and takes 16, the id of stable, which disappeared.
        g = self.g
        self.leaf(f"{g}/a/after.md", 16, facts=None)
        self.card(f"{g}/a", 1, 10, ["a-main", "a-lemma", "after"])
        base = self.base_with({f"{g}/a/after": f"{g}/anon"}, {f"{g}/anon": None})
        base[(wiki.ROADMAP / f"{g}/stable.md").resolve()] = {
            "subject": [{"type": "generic", "uri": f"../roadmap/{g}/stable.md"}], "id": af(16)}
        (wiki.ROOT / "scripts" / cards.MOVES).write_text("".join(json.dumps(row) + "\n" for row in (
            {"page": f"{g}/anon", "to": f"{g}/a/after", "article_id": af(16)},
            {"page": f"{g}/stable", "to": f"{g}/a/after", "article_id": af(16)})))
        errors = cards.check(base_annotations=base, renames=[(f"{g}/anon.md", f"{g}/a/after.md")])[0]
        self.assertIn(f"{cards.MOVES}:1: {g}/anon had no id, and {af(16)} is another article's", errors)

    def test_a_declaration_is_followed_even_when_git_sees_no_rename(self) -> None:
        # a-lemma (Ext.a_lemma) was 16 at old-lemma; it moved, was reworded and is 11 now; no row.
        g = self.g
        base = self.base_with({f"{g}/a/a-lemma": f"{g}/old-lemma"}, {f"{g}/old-lemma": af(16)})
        (wiki.ROOT / "scripts" / cards.MOVES).write_text("")
        errors = cards.check(base_annotations=base, renames=[])[0]
        self.assertTrue(any(f"{g}/old-lemma credited Ext.a_lemma as {af(16)}" in error for error in errors), errors)

    def test_two_moves_in_one_change_and_ids_git_pairs_crosswise(self) -> None:
        g = self.g
        base = self.base_with({f"{g}/a/a-lemma": f"{g}/first", f"{g}/a/a-main": f"{g}/second"})
        (wiki.ROOT / "scripts" / cards.MOVES).write_text("".join(json.dumps(row) + "\n" for row in (
            {"page": f"{g}/first", "to": f"{g}/mid", "article_id": af(11)},
            {"page": f"{g}/mid", "to": f"{g}/a/a-lemma", "article_id": af(11)},
            {"page": f"{g}/second", "to": f"{g}/a/a-main", "article_id": af(10)})))
        # Git pairs the identical files the other way round; the ids decide.
        crosswise = [(f"{g}/first.md", f"{g}/a/a-main.md"), (f"{g}/second.md", f"{g}/a/a-lemma.md")]
        self.assertEqual(cards.check(base_annotations=base, renames=crosswise)[0], [])

    def test_a_card_replaced_in_place_by_a_new_card(self) -> None:
        # The card at a was 7 (other mathematics); it is retired to 1, the card now at a.
        g = self.g
        self.write()
        base = cards.read_annotations()
        base[(wiki.ROADMAP / f"{g}/a/README.md").resolve()]["id"] = af(7)
        moves = wiki.ROOT / "scripts" / cards.MOVES
        moves.write_text(json.dumps({"card": af(7), "folder": f"{g}/a", "replaced_by": af(1)}) + "\n")
        self.assertEqual(cards.check(base_annotations=base)[0], [])
        moves.write_text("")
        self.assertTrue(any("only a retired card's or statement's final replacement takes its address" in error
                            for error in cards.check(base_annotations=base)[0]))

    def test_git_s_rename_speaks_for_an_id_nothing_else_found(self) -> None:
        # A page-only page with id 16 is renamed into the card as 17, with no row.
        g = self.g
        self.leaf(f"{g}/a/after.md", 17, facts=None)
        self.card(f"{g}/a", 1, 10, ["a-main", "a-lemma", "after"])
        base = self.base_with({f"{g}/a/after": f"{g}/before"}, {f"{g}/before": af(16)})
        (wiki.ROOT / "scripts" / cards.MOVES).write_text("")
        errors = cards.check(base_annotations=base, renames=[(f"{g}/before.md", f"{g}/a/after.md")])[0]
        self.assertTrue(any("an article keeps its id" in error for error in errors), errors)
        self.assertTrue(any(f"{g}/before is now {g}/a/after, and no row leads there" in error for error in errors),
                        errors)

    def test_a_card_folder_renamed_then_retired_in_one_change(self) -> None:
        g = self.g
        self.write()
        base = cards.read_annotations()
        record = {"kind": "result", "main_article_id": af(11), "importance": "key", "level": "graduate"}
        base[(wiki.ROADMAP / f"{g}/z/README.md").resolve()] = {
            "subject": [{"type": "generic", "uri": f"../roadmap/{g}/z/README.md"}], "id": af(7),
            "extensions": {"org.atlas-wiki": {"card": record}}}
        (wiki.ROOT / "scripts" / cards.MOVES).write_text("".join(json.dumps(row) + "\n" for row in (
            {"folder": f"{g}/z", "to": f"{g}/middle", "article_id": af(7)},
            {"card": af(7), "folder": f"{g}/middle", "replaced_by": af(1)})))
        self.assertEqual(cards.check(base_annotations=base)[0], [])

    def test_a_cyclic_ledger_still_returns(self) -> None:
        g = self.g
        self.write()
        base = cards.read_annotations()
        (wiki.ROOT / "scripts" / cards.MOVES).write_text("".join(json.dumps(row) + "\n" for row in (
            {"folder": f"{g}/p", "to": f"{g}/q", "article_id": af(1)},
            {"folder": f"{g}/q", "to": f"{g}/p", "article_id": af(1)},
            {"card": af(1), "folder": f"{g}/p", "replaced_by": af(1)})))
        self.assertTrue(cards.check(base_annotations=base)[0])

    def test_a_folder_that_stops_being_a_card_needs_its_retirement(self) -> None:
        self.write()
        base = cards.read_annotations()
        row = next(row for row in self.rows if row["subject"][0]["uri"].endswith("/a/README.md"))
        row["extensions"] = {"org.autoform": {"navigation": "module"}}
        self.write()
        (wiki.ROOT / "scripts" / cards.MOVES).write_text("")
        self.assertIn(f"{cards.MOVES}: the card {af(1)} at {self.g}/a is no card any more, and no row retires it",
                      cards.check(base_annotations=base)[0])

    def test_the_ledger_only_grows(self) -> None:
        published = json.dumps({"page": f"{self.g}/old", "to": f"{self.g}/a/a-main", "article_id": af(10)}) + "\n"
        later = json.dumps({"page": f"{self.g}/older", "to": f"{self.g}/a/a-lemma", "article_id": af(11)}) + "\n"
        moves = wiki.ROOT / "scripts" / cards.MOVES
        moves.write_text(published + later)
        self.assertEqual(self.run_check(base_ledger=published)[0], [])
        moves.write_text(later)
        self.assertIn(f"{cards.MOVES}: a row the base commit published was removed or changed; the ledger only grows",
                      self.run_check(base_ledger=published)[0])
        moves.unlink()
        self.assertIn(f"{cards.MOVES}: missing; it records every address a card change retired",
                      self.run_check(dependencies=self.extraction())[0])
        # Without the strict check too, the published rows cannot go.
        self.assertIn(f"{cards.MOVES}: missing; it records every address a card change retired",
                      self.run_check(base_ledger=published)[0])

    def test_wrong_moves(self) -> None:
        errors = self.ledger({"page": f"{self.g}/a/a-main", "to": f"{self.g}/b/x", "article_id": af(10)},
                             {"page": f"{self.g}/p", "to": f"{self.g}/q", "article_id": af(10)},
                             {"page": f"{self.g}/q", "to": f"{self.g}/p", "article_id": af(10)},
                             {"folder": f"{self.g}/a", "to": f"{self.g}/b", "article_id": af(1)},
                             {"card": af(1), "folder": f"{self.g}/a", "replaced_by": af(8)},
                             {"card": af(9), "folder": f"{self.g}/y", "replaced_by": af(8)},
                             {"what": "else"})
        for expected in ("the page Algebra/groups/a/a-main moved but is still there",
                         "the moves of Algebra/groups/p go round", "the folder Algebra/groups/a moved but is still there",
                         "the folder Algebra/groups/a ends at Algebra/groups/b",
                         f"the retired card {af(1)} is still the id of {self.g}/a",
                         f"replaced by {af(8)}, which is no card", "expected {page, to, article_id}"):
            self.assertTrue(any(expected in error for error in errors), (expected, errors))


class InMathlib(Vault):
    def test_a_mathlib_fact_links_its_pinned_source_line_with_its_name(self) -> None:
        pin = "56a005855ea17e0b0958f73ec801ae140b0a1679"
        (wiki.ROOT / "lake-manifest.json").write_text(json.dumps({"packages": [{"name": "mathlib", "rev": pin}]}))
        g = "Algebra/groups"
        self.leaf(f"{g}/a/a-main.md", 10)
        good = f"https://github.com/leanprover-community/mathlib4/blob/{pin}/Mathlib/A/B.lean#L12"
        other = good.replace(pin, "0" * 40)
        body = ("# A\n\nIt says.\n\n## Idea\n\nWhy.\n\n## Statements\n\n- [a-main](a-main.md)\n\n## In Mathlib\n\n"
                f'- [Fact]({good} "Foo.bar")\n- [Untitled]({good})\n- [Old]({other} "Foo.baz")\n'
                f'- [Prose]({good} "the fact about bars")\n- [Primed]({good} "Matrix.det_apply\'")\n'
                f'- [Marks]({good} "!!!")\n'
                f'- [Fragment]({good.replace("#L12", "#bogus.lean#L12")} "Foo.frag")\n'
                f'- [Query]({good.replace("#L12", "?plain=1#L12")} "Foo.query")\n'
                f'- [Dots]({good.replace("/Mathlib/A/", "/Mathlib/../../master/Mathlib/A/")} "Foo.dots")\n'
                f'- [Encoded]({good.replace("/Mathlib/A/", "/Mathlib/%2e%2e/A/")} "Foo.encoded")\n'
                "- [Docs](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Foo.qux#doc)\n")
        self.card(f"{g}/a", 1, 10, ["a-main"], body=body)
        errors = self.run_check()[0]
        self.assertEqual(len(errors), 9, errors)
        self.assertFalse(any("Matrix.det_apply" in error for error in errors), errors)
        self.assertTrue(any("not the pinned" in error for error in errors), errors)


class Counterparts(Vault):
    """A planned statement page may record its counterparts (docs/cards.md#counterparts): data only, which the check
    verifies in form and place and nothing else reads."""

    RECORDS = [{"mathlib": "MeasureTheory.dominated", "relation": "weaker",
                "needs": [{"mathlib": "MeasureTheory.limit_integrable"}, {"atlas": "Ext.b_main"}]},
               {"atlas": "Ext.a_main", "relation": "variant"}, {"mathlib": "Matrix.det_apply'", "relation": "stronger"},
               {"mathlib": "«odd name».x", "relation": "same"},
               # One name in both libraries names two declarations, and `«a.b».c` (two components) is not `a.b.c`.
               {"atlas": "Matrix.det_apply'", "relation": "variant"},
               {"mathlib": "a.b.c", "relation": "variant"}, {"mathlib": "«a.b».c", "relation": "variant"},
               # Only Lean's own `_root_` component is the source-only prefix.
               {"mathlib": "root_.Matrix.det", "relation": "variant"}]

    def setUp(self) -> None:
        super().setUp()
        self.g = "Algebra/groups"
        self.leaf(f"{self.g}/a/a-main.md", 10)
        self.leaf(f"{self.g}/a/p.md", 12, facts=None)
        self.card(f"{self.g}/a", 1, 10, ["a-main", "p"])

    def row(self, name: str) -> dict:
        return next(row for row in self.rows if row["subject"][0]["uri"].endswith(f"/{name}"))

    def record(self, name: str, counterpart: object) -> None:
        self.row(name).setdefault("extensions", {}).setdefault("org.atlas-wiki", {})["counterpart"] = counterpart

    def test_verified_counterparts_pass(self) -> None:
        self.record("p.md", self.RECORDS)
        self.assertEqual(self.run_check(), ([], []))

    def test_each_malformed_counterpart_is_reported(self) -> None:
        relations = "same, stronger, weaker, variant"
        cases = {
            "not a list": ({"mathlib": "M.a", "relation": "same"}, "`counterpart` must be a non-empty list of records"),
            "an empty list": ([], "`counterpart` must be a non-empty list of records"),
            "a record that is no object": (["M.a"], "`counterpart` record 1 is not an object"),
            "two declarations": ([{"mathlib": "M.a", "atlas": "Ext.a", "relation": "same"}],
                                 "`counterpart` record 1 names two declarations; give exactly one of `mathlib` and "
                                 "`atlas`"),
            "no declaration": ([{"relation": "same"}], "`counterpart` record 1 names no declaration"),
            "a name with a space": ([{"mathlib": "M.a b", "relation": "same"}],
                                    "`counterpart` record 1: `mathlib` is 'M.a b', not a Lean name"),
            "a name opening with a digit": ([{"mathlib": "M.1a", "relation": "same"}], "not a Lean name"),
            "a name that is no text": ([{"atlas": 7, "relation": "same"}], "`atlas` is 7, not a Lean name"),
            "no relation": ([{"mathlib": "M.a"}], f"`counterpart` record 1 has no `relation`; give one of {relations}"),
            "an unknown relation": ([{"mathlib": "M.a", "relation": "equivalent"}],
                                    f"`relation` is 'equivalent'; expected one of {relations}"),
            "an unknown key": ([{"mathlib": "M.a", "relation": "same", "note": "x"}],
                               "`counterpart` record 1 has the unknown key `note`"),
            "a declaration twice": ([{"mathlib": "M.a", "relation": "same"}, {"mathlib": "M.a", "relation": "weaker"}],
                                    "`counterpart` names mathlib M.a twice"),
            "needs that is no list": ([{"mathlib": "M.a", "relation": "weaker", "needs": "M.b"}],
                                      "`needs` must be a non-empty list of declarations"),
            "empty needs": ([{"mathlib": "M.a", "relation": "weaker", "needs": []}],
                            "`needs` must be a non-empty list of declarations"),
            "a plain name in needs": (
                [{"mathlib": "M.a", "relation": "weaker", "needs": ["M.b"]}],
                "`counterpart` record 1, `needs` entry 1 is not an object naming one declaration"),
            "two declarations in a needs entry": (
                [{"mathlib": "M.a", "relation": "weaker", "needs": [{"mathlib": "M.b", "atlas": "Ext.b"}]}],
                "`needs` entry 1 names two declarations"),
            "a bad name in needs": ([{"mathlib": "M.a", "relation": "weaker", "needs": [{"mathlib": "M b"}]}],
                                    "`needs` entry 1: `mathlib` is 'M b', not a Lean name"),
            "an unknown key in needs": ([{"mathlib": "M.a", "relation": "weaker",
                                          "needs": [{"mathlib": "M.b", "why": "x"}]}],
                                        "`needs` entry 1 has the unknown key `why`"),
            "needs naming one twice": ([{"mathlib": "M.a", "relation": "weaker",
                                         "needs": [{"atlas": "Ext.b"}, {"atlas": "Ext.b"}]}],
                                       "`needs` names atlas Ext.b twice"),
            "needs naming its own": ([{"mathlib": "M.a", "relation": "weaker", "needs": [{"mathlib": "M.a"}]}],
                                     "`needs` names the record's own declaration, mathlib M.a"),
            # Lean's quotes change no name: `Matrix.«det»` is `Matrix.det`.
            "a declaration twice, quoted once": (
                [{"mathlib": "Matrix.det", "relation": "same"}, {"mathlib": "Matrix.«det»", "relation": "weaker"}],
                "`counterpart` names mathlib Matrix.det twice (once as Matrix.«det»)"),
            "needs naming one twice, quoted once": (
                [{"mathlib": "M.a", "relation": "weaker", "needs": [{"atlas": "Ext.b"}, {"atlas": "«Ext».«b»"}]}],
                "`needs` names atlas Ext.b twice (once as «Ext».«b»)"),
            "needs naming its own, quoted": (
                [{"mathlib": "M.a", "relation": "weaker", "needs": [{"mathlib": "M.«a»"}]}],
                "`needs` names the record's own declaration, mathlib M.a (as M.«a»)"),
            # `_root_.` is a prefix only Lean source writes: `_root_.Matrix.det` is `Matrix.det`.
            "a `_root_.` prefix": ([{"mathlib": "_root_.Matrix.det", "relation": "same"}],
                                   "`counterpart` record 1: `mathlib` is '_root_.Matrix.det'; write the full name "
                                   "without `_root_.`"),
            "a quoted `_root_.` prefix": ([{"atlas": "«_root_».Ext.a", "relation": "same"}],
                                          "`atlas` is '«_root_».Ext.a'; write the full name without `_root_.`"),
            "a `_root_.` prefix in needs": (
                [{"mathlib": "M.a", "relation": "weaker", "needs": [{"atlas": "_root_.Ext.b"}]}],
                "`counterpart` record 1, `needs` entry 1: `atlas` is '_root_.Ext.b'; write the full name without "
                "`_root_.`"),
        }
        for case, (counterpart, message) in cases.items():
            with self.subTest(case=case):
                self.record("p.md", counterpart)
                errors = self.run_check()[0]
                self.assertTrue(any(f"{self.g}/a/p: " in error and message in error for error in errors),
                                (message, errors))
                self.assertTrue(all(error.startswith(f"{self.g}/a/p: ") for error in errors), errors)

    def test_a_counterpart_belongs_on_a_planned_statement_page(self) -> None:
        linked = ("a counterpart belongs on a planned page, whose annotation links no Lean declaration; this one links "
                  "one")
        mathlib = {"type": "lean", "uri": cards.sync.MATHLIB, "location": {"declaration": "M.q"}}
        pages = {
            # A page linked to a declaration of this project, through the folder defaults.
            "credited": ("q.md", {"object": [{"location": {"declaration": "Ext.q"}}]}, linked),
            # A Lean link that credits nothing is still a link.
            "a reference": ("q.md", {"object": [{"location": {"declaration": "Ext.q"}, "role": "uses"}]}, linked),
            "Mathlib-credited": ("q.md", {"object": [mathlib], "extensions": {"org.autoform": {"mathlib": True}}},
                                 linked),
            "another repository": ("q.md", {"object": [{"type": "lean", "uri": "https://github.com/x/y",
                                                         "location": {"declaration": "Y.q"}}]}, linked),
            "an earlier sync's module and name": ("q.md", {"extensions": {"org.atlas-wiki": {"module": "Ext",
                                                                                             "name": "q"}}}, linked),
            # Planned pages: references of other types, and a page that holds its declaration back.
            "a PDF and an HTML reference": ("q.md", {"object": [{"type": "pdf", "uri": "https://e.org/b.pdf"},
                                                                 {"type": "html", "uri": "https://e.org/n.html",
                                                                  "role": "states"}]}, None),
            "held": ("q.md", {"extensions": {"org.atlas-wiki": {"held": {"declaration": "Ext.q", "reason": "false",
                                                                         "issue": 1}}}}, None),
        }
        for case, (name, fields, message) in pages.items():
            with self.subTest(case=case):
                self.rows = [row for row in self.rows if not row["subject"][0]["uri"].endswith("/q.md")]
                self.page(f"{self.g}/a/{name}", "# q\n\nA statement.\n",
                          {"id": af(13), **json.loads(json.dumps(fields))})
                self.record(name, self.RECORDS[:1])
                errors = self.run_check()[0]
                if message is None:
                    self.assertFalse(any("counterpart" in error for error in errors), errors)
                else:
                    self.assertIn(f"{self.g}/a/q: {message}", errors)
        self.rows = [row for row in self.rows if not row["subject"][0]["uri"].endswith("/q.md")]
        # A folder page, a card's or not, and a card record hold none.
        self.record("a/README.md", self.RECORDS[:1])
        self.record("groups/README.md", self.RECORDS[:1])
        errors = self.run_check()[0]
        for folder in (f"{self.g}/a", self.g):
            self.assertIn(f"{folder}: a counterpart belongs on a planned statement page, not on a folder page", errors)
        del self.row("a/README.md")["extensions"]["org.atlas-wiki"]["counterpart"]
        del self.row("groups/README.md")["extensions"]["org.atlas-wiki"]["counterpart"]
        self.row("a/README.md")["extensions"]["org.atlas-wiki"]["card"]["counterpart"] = self.RECORDS[:1]
        errors = self.run_check()[0]
        self.assertIn(f"{self.g}/a: a card records no counterpart; a counterpart belongs on a planned statement page's "
                      "annotation (docs/cards.md#counterparts)", errors)
        self.assertFalse(any("unknown card key `counterpart`" in error for error in errors), errors)

    def test_names_are_compared_as_lean_reads_them(self) -> None:
        self.assertEqual(cards.name_components("Matrix.«det»"), ("Matrix", "det"))
        self.assertEqual(cards.name_components("«a.b».c"), ("a.b", "c"))
        self.assertEqual(cards.name_components("a.b.c"), ("a", "b", "c"))
        self.assertEqual(cards.name_components("«odd name».x'"), ("odd name", "x'"))

    def test_a_counterpart_belongs_on_a_statement_page_autoform_reads(self) -> None:
        # A row whose page is missing (an orphan) or one Autoform's loader passes over (a hidden page): the check
        # and so the strict rollup refuse its counterpart, with or without a card in the vault.
        self.page(f"{self.g}/a/.hidden.md", "# Hidden\n\nA statement.\n", {"id": af(15)})
        self.record(".hidden.md", self.RECORDS[:1])
        self.rows.append({"subject": [{"type": "generic", "uri": f"../roadmap/{self.g}/a/no-file.md"}], "id": af(16),
                          "extensions": {"org.atlas-wiki": {"counterpart": self.RECORDS[:1]}}})
        missing = f"{self.g}/a/no-file: a counterpart belongs on a statement page Autoform reads; its page is missing"
        hidden = (f"{self.g}/a/.hidden: a counterpart belongs on a statement page Autoform reads; Autoform does not "
                  f"read {self.g}/a/.hidden.md as one")
        errors = self.run_check()[0]
        self.assertIn(missing, errors)
        self.assertIn(hidden, errors)
        self.ledger_file()
        with self.assertRaises(ValueError) as raised:
            cards.rollup(self.extraction())
        self.assertIn(missing, str(raised.exception))
        # Without a card, the check still loads Autoform's graph for them.
        self.rows = [row for row in self.rows if not row["subject"][0]["uri"].endswith("/a/README.md")]
        errors = self.run_check()[0]
        self.assertIn(missing, errors)
        self.assertIn(hidden, errors)

    def test_the_links_folder_s_defaults_give_no_counterpart(self) -> None:
        # Defaults would give a counterpart to every row, a credited or a folder page's included: the check names the
        # defaults file, whether the counterpart there is well formed or not, and the rows' own are checked as ever.
        def message(path: str) -> str:
            return (f"blueprint/links/_defaults.json sets `counterpart` at `{path}`, which would give every row that "
                    "counterpart; a counterpart belongs on a planned statement page's own row: remove it from the "
                    "defaults")

        defaults = wiki.VAULT / "links" / "_defaults.json"
        own = 'extensions["org.atlas-wiki"]'
        cases = [({"counterpart": [{"mathlib": "M b"}]}, f'{own}["counterpart"]'),
                 ({"counterpart": self.RECORDS[:1]}, f'{own}["counterpart"]'),
                 # Inside a card record too, which the defaults would give the vault's card, and at any depth.
                 ({"card": {"counterpart": self.RECORDS[:1]}}, f'{own}["card"]["counterpart"]'),
                 ({"card": {"seeds": [{"counterpart": self.RECORDS[:1]}]}},
                  f'{own}["card"]["seeds"][0]["counterpart"]')]
        self.ledger_file()
        for extension, path in cases:
            with self.subTest(path=path):
                defaults.write_text(json.dumps({"object": {"type": "lean", "uri": "../.."},
                                                "extensions": {"org.atlas-wiki": extension}}))
                self.assertEqual(self.run_check()[0], [message(path)])
                with self.assertRaises(ValueError) as raised:
                    cards.rollup(self.extraction())
                self.assertIn(message(path), str(raised.exception))
        defaults.write_text('{"object": {"type": "lean", "uri": "../.."}}\n')
        self.assertEqual(self.run_check(), ([], []))

    def test_a_committed_link_is_a_link_though_lean_facts_dropped_it(self) -> None:
        # The build's row is planned (lean-facts unlinked a declaration the Lean no longer has), but the authors
        # committed the counterpart beside that link.
        self.record("p.md", self.RECORDS[:1])
        self.write()
        annotations = cards.read_annotations()
        committed = {page: json.loads(json.dumps(row)) for page, row in annotations.items()}
        page = next(page for page in committed if page.name == "p.md")
        committed[page]["object"] = [{"location": {"declaration": "Ext.gone"}}]
        errors = cards.check(annotations, committed=committed)[0]
        self.assertIn(f"{self.g}/a/p: a counterpart belongs on a planned page, whose annotation links no Lean "
                      "declaration; this one links one", errors)
        self.assertEqual(cards.check(annotations)[0], [])

    def test_counterparts_change_no_derived_data(self) -> None:
        # Counterparts naming credited declarations, Ext.b_main of another card among them, make no edge and change
        # no status: the rollup is the same, byte for byte.
        self.leaf(f"{self.g}/b/b-main.md", 20)
        self.leaf(f"{self.g}/a/r.md", 14, facts=None, statement=(f"{self.g}/a/a-main.md",))
        self.card(f"{self.g}/b", 2, 20, ["b-main"])
        self.rows = [row for row in self.rows if not row["subject"][0]["uri"].endswith("/a/README.md")]
        self.card(f"{self.g}/a", 1, 10, ["a-main", "p", "r"])
        before = json.dumps(self.rollup(), sort_keys=True)
        self.record("p.md", self.RECORDS)
        self.record("r.md", [{"atlas": "Ext.b_main", "relation": "same"}])
        after = self.rollup()
        self.assertEqual(json.dumps(after, sort_keys=True), before)
        self.assertEqual(after["uses"], [])


class Arguments(Vault):
    def test_the_history_options_go_together(self) -> None:
        self.write()
        ledger = wiki.ROOT / "scripts" / cards.MOVES
        ledger.touch()
        for given in (["--base-ledger", str(ledger)], ["--renames", str(ledger)],
                      ["--base-ledger", str(ledger), "--base-links", str(wiki.VAULT / "links")]):
            with self.subTest(given=given):
                self.assertEqual(cards.run(["check", *given]), 2)


class SiteData(Vault):
    """The wiki job's own rollup gives its site the card data hooks/card_pages.py shows, or, on any error, none."""

    def setUp(self) -> None:
        super().setUp()
        self.g = "Algebra/groups"
        self.leaf(f"{self.g}/b/b-main.md", 20)
        self.leaf(f"{self.g}/a/a-main.md", 10, statement=(f"{self.g}/b/b-main.md",))
        self.card(f"{self.g}/a", 1, 10, ["a-main"])
        self.card(f"{self.g}/b", 2, 20, ["b-main"])
        self.output = self.tmp / "build" / "cards.json"

    def run_rollup(self) -> tuple[int, str]:
        self.write()
        self.ledger_file()
        dependencies = self.tmp / "lean-dependencies.json"
        dependencies.write_text(json.dumps(self.extraction()))
        errors = io.StringIO()
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(errors):
            status = cards.run(["rollup", str(self.output), "--dependencies", str(dependencies)])
        return status, errors.getvalue()

    def test_a_bad_card_leaves_no_card_data(self) -> None:
        # A deliberately bad card: its kind is no card kind. The rollup fails, and an earlier rollup's file is gone
        # too, so the site renders exactly as without cards.
        self.leaf(f"{self.g}/c/c-main.md", 30)
        self.card(f"{self.g}/c", 3, 30, ["c-main"], kind="lemma")
        self.output.parent.mkdir()
        self.output.write_text(json.dumps({"schema": cards.SCHEMA, "cards": []}) + "\n")
        status, errors = self.run_rollup()
        self.assertEqual(status, 1)
        self.assertIn(f"error: {self.g}/c: `kind` is 'lemma'", errors)
        self.assertFalse(self.output.exists())
        self.assertEqual(list(self.output.parent.iterdir()), [])

    def test_a_rollup_stopped_by_half_a_history_leaves_no_card_data(self) -> None:
        # The history options go together; a rollup that stops on that removes an earlier rollup's file first.
        self.write()
        self.ledger_file()
        self.output.parent.mkdir()
        self.output.write_text(json.dumps({"schema": cards.SCHEMA, "cards": []}) + "\n")
        dependencies = self.tmp / "lean-dependencies.json"
        dependencies.write_text(json.dumps(self.extraction()))
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            status = cards.run(["rollup", str(self.output), "--dependencies", str(dependencies), "--base-ledger",
                                str(wiki.ROOT / "scripts" / cards.MOVES)])
        self.assertEqual(status, 2)
        self.assertFalse(self.output.exists())

    def test_the_site_shows_a_passing_rollup(self) -> None:
        self.assertEqual(self.run_rollup(), (0, ""))
        data = json.loads(self.output.read_text())
        hook = load_hook()
        site = hook.build(data, site_index(hook), "", self.tmp / "site-src")
        self.assertEqual(sorted(site.blocks), [f"roadmap/{self.g}/{name}/index.html" for name in ("a", "b")])
        self.assertIn('<dt>Uses</dt><dd><details><summary><a href="../b/index.html">', site.blocks[
            f"roadmap/{self.g}/a/index.html"])


class LedgerCheck(Vault):
    """`scripts/cards.py moves` checks the move ledger alone, with check_moves and no base, and on success writes the
    receipt hooks/card_pages.py keeps the moved addresses with: the commit, digests of the very ledger and annotation
    bytes it checked, and the cards it can list (docs/cards.md#move-ledger). A history of every kind: a folder renamed
    with its page, and a page moved out of card 7, which is retired in favour of card 1."""

    def setUp(self) -> None:
        super().setUp()
        self.g = g = "Algebra/groups"
        self.output = self.tmp / "build" / "card-moves.json"
        self.leaf(f"{g}/c/c-main.md", 10)
        self.leaf(f"{g}/c/x.md", 11)
        self.card(f"{g}/c", 1, 10, ["c-main", "x"])
        self.folder(f"{g}/new/README.md", "New", ["kept.md"], {"id": af(50)})
        self.leaf(f"{g}/new/kept.md", 12)
        self.rows_of_ledger = [{"folder": f"{g}/old", "to": f"{g}/new", "article_id": af(50)},
                               {"page": f"{g}/old/kept", "to": f"{g}/new/kept", "article_id": af(12)},
                               {"page": f"{g}/z/x", "to": f"{g}/c/x", "article_id": af(11)},
                               {"card": af(7), "folder": f"{g}/z", "replaced_by": af(1)}]
        self.git("init", "-q")

    def git(self, *arguments: str) -> str:
        return subprocess.run(["git", "-C", str(self.tmp), "-c", "user.name=Test", "-c", "user.email=test@example.com",
                               "-c", "commit.gpgsign=false", *arguments], check=True, capture_output=True,
                              text=True).stdout

    def check(self, *rows: dict, ledger: str | None = None) -> tuple[int, str, dict | None]:
        """Write the vault and the ledger (``rows``, or the text ``ledger``; the setUp history by default), commit
        them, and run the moves check: its exit status, its errors and the receipt it wrote."""
        self.write()
        moves = wiki.ROOT / "scripts" / cards.MOVES
        moves.write_text(ledger if ledger is not None else
                         "".join(json.dumps(row) + "\n" for row in (rows or self.rows_of_ledger)))
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", "change")
        errors = io.StringIO()
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(errors):
            status = cards.run(["moves", str(self.output)])
        return status, errors.getvalue(), json.loads(self.output.read_text()) if self.output.exists() else None

    def assertRefused(self, *rows: dict, error: str) -> None:
        status, errors, made = self.check(*rows)
        self.assertEqual((status, made), (1, None), errors)
        self.assertIn(error, errors)

    def test_a_valid_ledger_gets_its_receipt(self) -> None:
        status, errors, made = self.check()
        self.assertEqual((status, errors), (0, ""))
        ledger = (wiki.ROOT / "scripts" / cards.MOVES).read_bytes()
        self.assertEqual(made, {"schema": "atlas-card-moves/v2", "commit": self.git("rev-parse", "HEAD").strip(),
                                "ledger_sha256": hashlib.sha256(ledger).hexdigest(),
                                "annotations_sha256": cards.links_digest(cards.links_snapshot()),
                                "cards": {af(1): f"{self.g}/c"}, "cards_complete": True,
                                "replacements": {af(1): {"kind": "folder", "node": f"{self.g}/c"}}})
        # The digest of the annotations is the one the hook recomputes from the files, unparsed.
        self.assertEqual(made["annotations_sha256"], load_hook().links_digest(cards.links_dir()))
        # A deliberately empty ledger is a ledger with no row.
        status, errors, made = self.check(ledger="")
        self.assertEqual((status, errors, made["ledger_sha256"]), (0, "", hashlib.sha256(b"").hexdigest()))

    def test_a_missing_ledger_gets_no_receipt(self) -> None:
        self.check()
        (wiki.ROOT / "scripts" / cards.MOVES).unlink()
        errors = io.StringIO()
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(errors):
            self.assertEqual(cards.run(["moves", str(self.output)]), 1)
        self.assertFalse(self.output.exists())
        self.assertIn("card-moves.jsonl: missing", errors.getvalue())

    def test_an_invalid_ledger_gets_no_receipt(self) -> None:
        g = self.g
        # The folder x moved to b as card 7, retired at b in favour of card 1, while the unrelated card 2 holds b.
        self.leaf(f"{g}/b/b-main.md", 20)
        self.card(f"{g}/b", 2, 20, ["b-main"])
        self.assertRefused({"folder": f"{g}/x", "to": f"{g}/b", "article_id": af(7)},
                           {"card": af(7), "folder": f"{g}/b", "replaced_by": af(1)},
                           error=f"the retired card {af(7)}'s address {g}/b is held by another article")
        # Two folder rows whose ids differ between adjacent hops, both retired at the end.
        self.assertRefused({"folder": f"{g}/x", "to": f"{g}/y", "article_id": af(7)},
                           {"folder": f"{g}/y", "to": f"{g}/z", "article_id": af(8)},
                           {"card": af(7), "folder": f"{g}/z", "replaced_by": af(1)},
                           {"card": af(8), "folder": f"{g}/z", "replaced_by": af(1)},
                           error=f"{g}/x moved as {af(7)} to {g}/y, which moved on as {af(8)}")
        # An old page address an unrelated live folder now holds.
        self.folder(f"{g}/p/README.md", "P", [], {"id": af(60)})
        self.assertRefused({"page": f"{g}/p", "to": f"{g}/c/x", "article_id": af(11)},
                           error=f"{g}/p moved as a page, and another article's folder now holds the address")
        # A declassified folder that keeps its retired card's id, replaced by no card.
        self.folder(f"{g}/d/README.md", "D", [], {"id": af(9)})
        self.assertRefused({"card": af(9), "folder": f"{g}/d", "replaced_by": af(8)},
                           error=f"the retired card {af(9)} is replaced by {af(8)}, which is no card")
        # A retired id that is no article id.
        self.assertRefused({"card": "af_bad", "folder": f"{g}/z", "replaced_by": af(1)},
                           error="`card` and `replaced_by` are article ids")
        # A page row whose target is another article: x is 11, the row says 2, card 2's folder.
        self.assertRefused({"page": f"{g}/q", "to": f"{g}/c/x", "article_id": af(2)},
                           error=f"{g}/q ends at {g}/c/x, but {af(2)} is {g}/b")

    def test_a_malformed_id_the_ledger_does_not_name_is_left_alone(self) -> None:
        # Unrelated pages with an id that is a list or null, and an unrelated card whose id is a list: the moves stand,
        # and the receipt leaves that card out of its list, which is then incomplete.
        g = self.g
        self.leaf(f"{g}/u/listed.md", 0, row={"id": []})
        self.leaf(f"{g}/u/null.md", 0, row={"id": None})
        self.leaf(f"{g}/e/e-main.md", 30)
        self.card(f"{g}/e", 0, 30, ["e-main"], row={"id": ["af"]})
        status, errors, made = self.check()
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual((made["cards"], made["cards_complete"]), ({af(1): f"{g}/c"}, False))

    def test_a_malformed_id_the_ledger_needs_is_refused(self) -> None:
        # The renamed folder's page has an id that is a list, so no article is the one its row names.
        uris = [row["subject"][0]["uri"] for row in self.rows]
        self.rows[uris.index(f"../roadmap/{self.g}/new/README.md")]["id"] = []
        self.assertRefused(error=f"the folder {self.g}/old ends at {self.g}/new, but {af(50)} is no folder page")

    def test_an_id_the_ledger_names_needs_one_article(self) -> None:
        # Another article with the id of the replacement card, or of a moved page: never the last one read.
        g = self.g
        for number, holder in ((1, f"{g}/other/README.md"), (11, f"{g}/other/copy.md")):
            with self.subTest(number=number):
                self.setUp()
                if holder.endswith("README.md"):
                    self.folder(holder, "Other", [], {"id": af(number)})
                else:
                    self.leaf(holder, number)
                self.assertRefused(error=f"{af(number)}, which the ledger names, is the id of 2 articles")

    def test_an_id_the_ledger_does_not_name_may_be_shared(self) -> None:
        # Two unrelated cards with one id: the moves stand, and the receipt lists neither, so its list is incomplete.
        g = self.g
        for name in ("e", "f"):
            self.leaf(f"{g}/{name}/{name}-main.md", 30 if name == "e" else 31)
            self.card(f"{g}/{name}", 40, 30 if name == "e" else 31, [f"{name}-main"])
        status, errors, made = self.check()
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual((made["cards"], made["cards_complete"]), ({af(1): f"{g}/c"}, False))

    def moves(self, output: Path | None = None) -> tuple[int, str]:
        """Run the moves check on the working tree as it is, committing nothing: its exit status and its errors."""
        errors = io.StringIO()
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(errors):
            status = cards.run(["moves", str(output or self.output)])
        return status, errors.getvalue()

    def test_a_failed_check_leaves_no_receipt(self) -> None:
        # A receipt, then annotations changed in the working tree only, at the same commit and ledger, so that the
        # check fails: no receipt is left, and the earlier one is not the hook's to accept.
        self.assertEqual(self.check()[0], 0)
        earlier = self.output.read_bytes()
        head, ledger = self.git("rev-parse", "HEAD"), (wiki.ROOT / "scripts" / cards.MOVES).read_bytes()
        uris = [row["subject"][0]["uri"] for row in self.rows]
        self.rows[uris.index(f"../roadmap/{self.g}/c/x.md")]["id"] = af(13)
        self.write()
        status, errors = self.moves()
        self.assertEqual((status, self.output.exists()), (1, False))
        self.assertIn(f"{self.g}/z/x ends at {self.g}/c/x, but {af(11)} is no statement page", errors)
        self.assertEqual((self.git("rev-parse", "HEAD"), (wiki.ROOT / "scripts" / cards.MOVES).read_bytes()),
                         (head, ledger))
        self.output.write_bytes(earlier)
        hook = load_hook()
        with self.assertRaises(hook.CardDataError) as refused:
            hook.read_receipt(self.tmp, ledger)
        self.assertIn("is the check of other annotations", str(refused.exception))

    def test_an_address_held_by_an_article_with_no_id_is_not_free(self) -> None:
        # Card 7, renamed to z and retired there in favour of card 1; z holds a folder page with no id, with a row or
        # without one: its old addresses would lead to an article no one can name instead of card 1.
        g = self.g
        rows = [{"folder": f"{g}/x", "to": f"{g}/z", "article_id": af(7)}, *self.rows_of_ledger]
        self.folder(f"{g}/z/README.md", "Z", [])
        status, errors, made = self.check(*rows)
        self.assertEqual((status, made), (1, None))
        self.assertIn(f"the retired card {af(7)}'s address {g}/z is held by an article with no id", errors)
        self.rows.pop()
        status, errors, made = self.check(*rows)
        self.assertEqual((status, made), (1, None))
        self.assertIn(f"the retired card {af(7)}'s address {g}/z is held by an article with no id", errors)

    def test_a_retired_card_s_address_may_keep_its_folder_or_take_its_replacement(self) -> None:
        g = self.g
        # Declassified: the folder stays, a plain folder with the card's own id.
        self.folder(f"{g}/z/README.md", "Z", [], {"id": af(7)})
        status, errors, made = self.check()
        self.assertEqual((status, errors), (0, ""))
        # Replaced in place: card 9, a new card with its own id, at the retired card's address.
        self.setUp()
        self.leaf(f"{g}/z/z-main.md", 40)
        self.card(f"{g}/z", 9, 40, ["z-main"])
        rows = [*self.rows_of_ledger[:3], {"card": af(7), "folder": f"{g}/z", "replaced_by": af(9)}]
        status, errors, made = self.check(*rows)
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual(made["cards"], {af(1): f"{g}/c", af(9): f"{g}/z"})

    def test_a_card_in_a_folder_the_site_cannot_serve(self) -> None:
        # An unrelated card in a folder named like a page: the receipt leaves it out and is incomplete, so the site
        # keeps every moved address and shows no card.
        g = self.g
        self.leaf(f"{g}/draft.md/d-main.md", 30)
        self.card(f"{g}/draft.md", 5, 30, ["d-main"])
        status, errors, made = self.check()
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual((made["cards"], made["cards_complete"]), ({af(1): f"{g}/c"}, False))
        hook = load_hook()
        nodes = []
        for page in sorted(wiki.ROADMAP.rglob("*.md")):
            if page.is_file():
                node = cards.node_id(page)
                nodes.append({"id": node, "kind": "scope", "route": f"../roadmap/{node}/index.html", "title": node}
                             if page.name == "README.md" else
                             {"id": node, "kind": "node", "route": f"../roadmap/{node}.html", "title": node})
        docs = self.tmp / "site-src"
        (docs / "dependencies").mkdir(parents=True)
        (docs / "dependencies" / "index.json").write_text(json.dumps({"schema": hook.INDEX_SCHEMA, "nodes": nodes}))
        site, unshown, unkept = hook.assemble(self.tmp, docs)
        self.assertEqual((unkept, site.addresses, site.blocks), (None, 4, {}))
        self.assertIn("there is no build/cards.json", unshown)
        with self.assertRaises(hook.CardDataError):
            hook.agree({af(1): f"{g}/c", af(5): f"{g}/draft.md"}, made["cards"], made["cards_complete"])
        # A card a retirement needs, in such a folder: no address could lead to it, so there is no receipt.
        self.leaf(f"{g}/r.md/r-main.md", 40)
        self.card(f"{g}/r.md", 9, 40, ["r-main"])
        status, errors, made = self.check(*self.rows_of_ledger,
                                          {"card": af(8), "folder": f"{g}/y", "replaced_by": af(9)})
        self.assertEqual((status, made), (1, None))
        self.assertIn(f"the retired card {af(8)} is replaced by {af(9)}, whose folder {g}/r.md is no address the site "
                      "serves", errors)

    def test_the_receipt_names_a_commit(self) -> None:
        # Before the first commit, HEAD names none.
        self.write()
        (wiki.ROOT / "scripts" / cards.MOVES).write_text("".join(json.dumps(row) + "\n" for row in self.rows_of_ledger))
        status, errors = self.moves()
        self.assertEqual((status, self.output.exists()), (1, False))
        self.assertIn("is no Git checkout: the receipt names the commit it checks", errors)

    def test_the_hook_and_the_check_share_one_address_predicate(self) -> None:
        hook = load_hook()
        for value in ("A/b", "A/b.md", "A/b.md/c", "A/./b", "A/../b", "/A/b", "A//b", "A/b/", "", "roadmap", "A/b.mdx",
                      "A/.b", "A/b c", "A/%2E%2E/b"):
            with self.subTest(value):
                self.assertEqual(hook.valid_address(value), cards.valid_address(value))

    def test_the_output_is_a_file_of_its_own(self) -> None:
        self.check()
        earlier = self.output.read_bytes()
        link = self.tmp / "build" / "link.json"
        link.symlink_to(self.output)
        folder = self.tmp / "build" / "folder"
        folder.mkdir()
        alias = self.tmp / "build" / "defaults.json"
        os.link(cards.links_dir() / "_defaults.json", alias)
        for output, said in ((cards.links_dir() / "out.json", "is inside blueprint/"),
                             (wiki.ROOT / "scripts" / cards.MOVES, "are one file"),
                             (alias, "and the links file _defaults.json are one file"),
                             (link, "is a symbolic link"), (folder, "is there but is no regular file")):
            with self.subTest(said):
                errors = io.StringIO()
                with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(errors):
                    self.assertEqual(cards.run(["moves", str(output)]), 2)
                self.assertIn(said, errors.getvalue())
        self.assertEqual((self.output.read_bytes(), link.is_symlink(), folder.is_dir()), (earlier, True, True))
        self.assertTrue((wiki.ROOT / "scripts" / cards.MOVES).is_file())
        for argv in (["moves"], ["moves", str(self.output), "extra"], ["moves", "--dependencies"]):
            with self.subTest(argv=argv), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(cards.run(argv), 2)

    def test_the_snapshot_reads_as_read_annotations(self) -> None:
        # From the bytes read once: the page of each row, its defaults merged in, as read_annotations finds it; and
        # the digest covers the defaults file, regular or not.
        defaults = {"object": {"type": "lean", "uri": "../.."},
                    "subject": {"type": "generic", "uri": "../roadmap/README.md"}}
        (cards.links_dir() / "_defaults.json").write_text(json.dumps(defaults))
        self.rows.append({"id": af(70)})
        self.write()
        snapshot = cards.links_snapshot()
        self.assertEqual(cards.snapshot_annotations(snapshot), cards.read_annotations())
        hook = load_hook()
        digests = set()
        for kind in ("regular", "absent", "directory", "symbolic link"):
            with self.subTest(kind):
                defaults = cards.links_dir() / "_defaults.json"
                if defaults.is_dir() and not defaults.is_symlink():
                    defaults.rmdir()
                else:
                    defaults.unlink(missing_ok=True)
                if kind == "regular":
                    defaults.write_text("{}")
                elif kind == "directory":
                    defaults.mkdir()
                elif kind == "symbolic link":
                    (self.tmp / "elsewhere.json").write_text("{}")
                    defaults.symlink_to(self.tmp / "elsewhere.json")
                cards.sync.folder_template.cache_clear()
                snapshot = cards.links_snapshot()
                self.assertEqual(cards.snapshot_annotations(snapshot), cards.read_annotations())
                digests.add(cards.links_digest(snapshot))
                self.assertEqual(cards.links_digest(snapshot), hook.links_digest(cards.links_dir()))
        # A directory and a symbolic link are both a defaults file that is no regular file, which Autoform cannot use.
        self.assertEqual(len(digests), 3)


class StatementRetirement(Vault):
    """A statement page an expansion replaces is retired by a row of its own, `{"statement": <its id>, "page": <its
    last address>, "replaced_by": <the id of a live statement page or folder page>}` (docs/cards.md#move-ledger),
    which the ledger check follows to the live article that replaces it. The history: the node g/node, af_...014,
    expanded into g/node-a (af_...015) and g/node-b (af_...016), beside card 1 at g/c."""

    git, check, assertRefused = LedgerCheck.git, LedgerCheck.check, LedgerCheck.assertRefused

    def setUp(self) -> None:
        super().setUp()
        self.g = g = "Algebra/groups"
        self.output = self.tmp / "build" / "card-moves.json"
        self.leaf(f"{g}/c/c-main.md", 10)
        self.leaf(f"{g}/c/x.md", 11)
        self.card(f"{g}/c", 1, 10, ["c-main", "x"])
        self.leaf(f"{g}/node-a.md", 21, facts=None)
        self.leaf(f"{g}/node-b.md", 22, facts=None)
        self.rows_of_ledger = [{"statement": af(20), "page": f"{g}/node", "replaced_by": af(21)}]
        self.git("init", "-q")

    def remove(self, relative: str) -> None:
        """Delete a page and its row."""
        (wiki.ROADMAP / relative).unlink()
        self.rows = [row for row in self.rows if row["subject"][0]["uri"] != f"../roadmap/{relative}"]

    def test_a_retirement_gets_its_receipt(self) -> None:
        g = self.g
        status, errors, made = self.check()
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual(made["replacements"], {af(21): {"kind": "page", "node": f"{g}/node-a"}})
        # With a card's retirement too: each retirement's replacement.
        status, errors, made = self.check({"page": f"{g}/z/x", "to": f"{g}/c/x", "article_id": af(11)},
                                          {"card": af(7), "folder": f"{g}/z", "replaced_by": af(1)},
                                          *self.rows_of_ledger)
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual(made["replacements"], {af(1): {"kind": "folder", "node": f"{g}/c"},
                                                af(21): {"kind": "page", "node": f"{g}/node-a"}})

    def test_replacements_are_followed_through_later_retirements(self) -> None:
        # node-a, which replaced the node, is retired in turn, for node-b: both lead to node-b. A statement may also
        # be replaced by a card that is retired later, for card 1.
        g = self.g
        self.remove(f"{g}/node-a.md")
        status, errors, made = self.check(*self.rows_of_ledger,
                                          {"statement": af(21), "page": f"{g}/node-a", "replaced_by": af(22)})
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual(made["replacements"], {af(22): {"kind": "page", "node": f"{g}/node-b"}})
        status, errors, made = self.check({"statement": af(20), "page": f"{g}/node", "replaced_by": af(7)},
                                          {"card": af(7), "folder": f"{g}/z", "replaced_by": af(1)})
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual(made["replacements"], {af(1): {"kind": "folder", "node": f"{g}/c"}})

    def test_an_invalid_retirement_gets_no_receipt(self) -> None:
        g = self.g
        retire = self.rows_of_ledger[0]
        # The retired id is still a page's.
        self.leaf(f"{g}/again.md", 20, facts=None)
        self.assertRefused(error=f"the retired statement {af(20)} is still the id of {g}/again")
        self.remove(f"{g}/again.md")
        # Replacements that go round, and one that ends at no live page or folder.
        self.assertRefused(retire, {"statement": af(21), "page": f"{g}/node-a", "replaced_by": af(20)},
                           error=f"the replacements of {af(20)} go round")
        self.assertRefused({**retire, "replaced_by": af(99)},
                           error=f"the retired statement {af(20)} is replaced by {af(99)}, which is no live page or "
                                 "folder")
        # Another article at the retired address, with an id or without one.
        self.leaf(f"{g}/node.md", 23, facts=None)
        self.assertRefused(error=f"the retired statement {af(20)}'s address {g}/node is held by another article")
        self.rows[-1].pop("id")
        self.assertRefused(error=f"the retired statement {af(20)}'s address {g}/node is held by an article with no "
                                 "id")
        self.remove(f"{g}/node.md")
        # The address moved too, or was a retired card's; the statement retired twice, or as a card too; a malformed
        # row.
        self.assertRefused(retire, {"page": f"{g}/node", "to": f"{g}/node-b", "article_id": af(22)},
                           error=f"{g}/node is the last address of the retired statement {af(20)} and moved")
        self.assertRefused(retire, {"card": af(7), "folder": f"{g}/node", "replaced_by": af(1)},
                           error=f"{g}/node is the last address of the retired statement {af(20)} and moved or was a "
                                 "retired card's too")
        self.assertRefused(retire, retire, error=f"the statement {af(20)} is already retired")
        self.assertRefused(retire, {"card": af(20), "folder": f"{g}/z", "replaced_by": af(1)},
                           error=f"{af(20)} is retired both as a card and as a statement")
        self.assertRefused({**retire, "statement": "af_20"}, error="`statement` and `replaced_by` are article ids")
        self.assertRefused({**retire, "page": f"{g}/node.md"},
                           error="an address is a path below roadmap/ without `.md`")
        # A page row that ends where its statement was not retired.
        self.assertRefused({"page": f"{g}/older", "to": f"{g}/elsewhere", "article_id": af(20)}, retire,
                           error=f"the page {g}/older ends at {g}/elsewhere, but its statement {af(20)} was retired at "
                                 f"{g}/node")

    def test_the_replacement_may_live_at_the_address(self) -> None:
        # A new statement page with its own id at the node's address, or a folder there: the node expanded into a
        # folder of its own name, whose folder page replaces it.
        g = self.g
        self.leaf(f"{g}/node.md", 24, facts=None)
        status, errors, made = self.check({**self.rows_of_ledger[0], "replaced_by": af(24)})
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual(made["replacements"], {af(24): {"kind": "page", "node": f"{g}/node"}})
        self.remove(f"{g}/node.md")
        self.folder(f"{g}/node/README.md", "Node", ["part.md"], {"id": af(25)})
        self.leaf(f"{g}/node/part.md", 26, facts=None)
        status, errors, made = self.check({**self.rows_of_ledger[0], "replaced_by": af(25)})
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual(made["replacements"], {af(25): {"kind": "folder", "node": f"{g}/node"}})

    def test_since_the_base_a_gone_statement_needs_a_move_or_its_retirement(self) -> None:
        # The base had the node, with its id; the change deleted it for node-a and node-b. Without the retirement row
        # the node is gone with no row; with it, the change passes, even where Git calls node-a a rename of the node.
        g = self.g
        self.write()
        base = cards.read_annotations()
        for path in ((wiki.ROADMAP / f"{g}/node-a.md").resolve(), (wiki.ROADMAP / f"{g}/node-b.md").resolve()):
            base.pop(path)
        base[(wiki.ROADMAP / f"{g}/node.md").resolve()] = {
            "subject": [{"type": "generic", "uri": f"../roadmap/{g}/node.md"}], "id": af(20)}
        moves = wiki.ROOT / "scripts" / cards.MOVES
        moves.write_text("")
        self.assertIn(f"{cards.MOVES}: {g}/node ({af(20)}) is gone, and no row moves it; an article keeps its address "
                      "or moves with its row", cards.check(base_annotations=base)[0])
        moves.write_text(json.dumps(self.rows_of_ledger[0]) + "\n")
        self.assertEqual(cards.check(base_annotations=base)[0], [])
        self.assertEqual(cards.check(base_annotations=base, renames=[(f"{g}/node.md", f"{g}/node-a.md")])[0], [])
        # The row names the address the statement had at that point, and an article the base had as a page.
        moves.write_text(json.dumps({**self.rows_of_ledger[0], "page": f"{g}/elsewhere"}) + "\n")
        self.assertIn(f"{cards.MOVES}:1: the statement {af(20)} is at {g}/node, not {g}/elsewhere",
                      cards.check(base_annotations=base)[0])
        moves.write_text(json.dumps({"statement": af(1), "page": f"{g}/c", "replaced_by": af(21)}) + "\n")
        self.assertIn(f"{cards.MOVES}:1: {af(1)} was no statement page at the base commit",
                      cards.check(base_annotations=base)[0])

    def test_an_address_has_one_owner(self) -> None:
        # Two statements retired at the vacant g/gone in favour of different live articles, in either order, and two
        # cards retired at one folder likewise: two owners, no receipt, whatever the order.
        g = self.g
        twenty = {"statement": af(20), "page": f"{g}/gone", "replaced_by": af(21)}
        thirty = {"statement": af(30), "page": f"{g}/gone", "replaced_by": af(22)}
        for rows in ((twenty, thirty), (thirty, twenty)):
            with self.subTest(rows=rows):
                self.assertRefused(*rows, error=f"{g}/gone is the last address of the retired statement "
                                                f"{rows[0]['statement']}, replaced by {rows[0]['replaced_by']}, and of "
                                                f"{rows[1]['statement']}; an address has one owner")
        self.leaf(f"{g}/d/d-main.md", 40)
        self.card(f"{g}/d", 2, 40, ["d-main"])
        self.assertRefused({"card": af(7), "folder": f"{g}/z", "replaced_by": af(1)},
                           {"card": af(8), "folder": f"{g}/z", "replaced_by": af(2)},
                           error=f"{g}/z is the last address of the retired card {af(7)}, replaced by {af(1)}, and of "
                                 f"{af(8)}; an address has one owner")
        # One history at the address: 20 replaced in place by 30, which is retired there in turn, for 22.
        status, errors, made = self.check({**twenty, "replaced_by": af(30)}, thirty)
        self.assertEqual((status, errors), (0, ""))
        self.assertEqual(made["replacements"], {af(22): {"kind": "page", "node": f"{g}/node-b"}})

    def test_a_replacement_moves_into_the_retired_address_only_after_the_retirement(self) -> None:
        # The base had the node (20) and node-a (21); the change retires the node for node-a, then moves node-a into
        # the node's address. The retirement frees the address first; the move before it finds the node still there.
        g = self.g
        self.remove(f"{g}/node-a.md")
        self.leaf(f"{g}/node.md", 21, facts=None)
        self.write()
        base = cards.read_annotations()
        base[(wiki.ROADMAP / f"{g}/node.md").resolve()] = {
            "subject": [{"type": "generic", "uri": f"../roadmap/{g}/node.md"}], "id": af(20)}
        base[(wiki.ROADMAP / f"{g}/node-a.md").resolve()] = {
            "subject": [{"type": "generic", "uri": f"../roadmap/{g}/node-a.md"}], "id": af(21)}
        retire = {"statement": af(20), "page": f"{g}/node", "replaced_by": af(21)}
        move = {"page": f"{g}/node-a", "to": f"{g}/node", "article_id": af(21)}
        moves = wiki.ROOT / "scripts" / cards.MOVES
        moves.write_text(json.dumps(retire) + "\n" + json.dumps(move) + "\n")
        self.assertEqual(cards.check(base_annotations=base)[0], [])
        moves.write_text(json.dumps(move) + "\n" + json.dumps(retire) + "\n")
        self.assertIn(f"{cards.MOVES}:1: {g}/node already holds another article", cards.check(base_annotations=base)[0])
        # The snapshot alone, as the moves check reads it, cannot tell the order, and accepts both.
        for rows in ((retire, move), (move, retire)):
            with self.subTest(rows=rows):
                status, errors, made = self.check(*rows)
                self.assertEqual((status, errors), (0, ""))

    def test_the_replacement_in_place_takes_the_address_since_the_base(self) -> None:
        g = self.g
        self.leaf(f"{g}/node.md", 24, facts=None)
        self.write()
        base = cards.read_annotations()
        base[(wiki.ROADMAP / f"{g}/node.md").resolve()]["id"] = af(20)
        moves = wiki.ROOT / "scripts" / cards.MOVES
        moves.write_text(json.dumps({**self.rows_of_ledger[0], "replaced_by": af(24)}) + "\n")
        self.assertEqual(cards.check(base_annotations=base)[0], [])
        moves.write_text(json.dumps({**self.rows_of_ledger[0], "replaced_by": af(21)}) + "\n")
        self.assertTrue(any(f"{g}/node was {af(20)} and now holds {af(24)}" in error
                            for error in cards.check(base_annotations=base)[0]))


class RealLinks(unittest.TestCase):
    """On the checkout's own blueprint/links/, where it has one: the moves check reads the annotations as
    read_annotations does, and the hook computes the receipt's digest of them."""

    def test_the_real_links_read_alike(self) -> None:
        if not any(cards.links_dir().glob("*.jsonl")):
            self.skipTest("this checkout has no blueprint/links/")
        snapshot = cards.links_snapshot()
        self.assertEqual(cards.snapshot_annotations(snapshot), cards.read_annotations())
        self.assertEqual(cards.links_digest(snapshot), load_hook().links_digest(cards.links_dir()))


class RealCards(unittest.TestCase):
    """On the checkout's own cards: the check refuses a card that the taxonomy makes a subject, a field or a
    subfield. A PR that changes only scripts/taxonomy.json skips the card job, so its unit tests hold the committed
    cards to the committed taxonomy with the same rule."""

    def test_no_real_card_is_a_folder_of_the_taxonomy(self) -> None:
        if not any(cards.links_dir().glob("*.jsonl")):
            self.skipTest("this checkout has no blueprint/links/")
        folders = cards.card_folders(cards.read_annotations())
        self.assertEqual({folder.as_posix(): structure for folder in folders
                          if (structure := cards.structural(folder)) is not None}, {})


class SiteHistory(Vault):
    """Histories the strict check accepts, made in a real Git repository (the base commit, the change and its
    ledger rows, Git's renames between them, the base commit's annotations and ledger), keep every old address on
    the site, as hooks/card_pages.py resolves it."""

    def setUp(self) -> None:
        super().setUp()
        self.g = "Algebra/groups"
        self.git("init", "-q")
        # What the card job reads besides the checkout, kept out of the repository.
        self.scratch = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, self.scratch)

    def git(self, *arguments: str) -> str:
        return subprocess.run(["git", "-C", str(self.tmp), "-c", "user.name=Test", "-c", "user.email=test@example.com",
                               "-c", "commit.gpgsign=false", *arguments], check=True, capture_output=True,
                              text=True).stdout

    def commit(self, message: str) -> str:
        self.write()
        self.ledger_file()
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)
        return self.git("rev-parse", "HEAD").strip()

    def start_over(self) -> None:
        """An empty roadmap, to lay out the change from scratch."""
        shutil.rmtree(wiki.ROADMAP)
        self.rows, self.articles = [], {}
        self.folder("README.md", "Roadmap", ["Algebra/README.md"])
        self.folder("Algebra/README.md", "Algebra", ["groups/README.md"])
        self.folder("Algebra/groups/README.md", "Groups", [])

    def change(self, base: str, *rows: dict) -> list[str]:
        """Commit the change with the ledger ``rows`` and check it as the card job checks a pull request on
        ``base``: its errors."""
        (wiki.ROOT / "scripts" / cards.MOVES).write_text("".join(json.dumps(row) + "\n" for row in rows))
        head = self.commit("change")
        work = Path(tempfile.mkdtemp(dir=self.scratch))
        renames = work / "renames.tsv"
        renames.write_text(self.git("-c", "diff.renameLimit=0", "diff", "--name-status", "-M", base, head, "--",
                                    "blueprint/roadmap"))
        (work / "links").mkdir()
        (work / "links" / "Algebra.jsonl").write_text(self.git("show", f"{base}:blueprint/links/Algebra.jsonl"))
        return cards.check(dependencies=self.extraction(),
                           base_ledger=self.git("show", f"{base}:scripts/{cards.MOVES}"),
                           base_annotations=cards.read_links(work / "links"), renames=cards.read_renames(renames))[0]

    def site(self, base: str, *rows: dict):
        """The change with its rows, which the strict check accepts, then the site's redirects."""
        self.assertEqual(self.change(base, *rows), [])
        ledger = "".join(json.dumps(row) + "\n" for row in rows)
        hook = load_hook()
        site = hook.build(cards.rollup(self.extraction()), site_index(hook), ledger, self.tmp / "site-src")
        table = json.loads(site.files[hook.SCRIPT].split("var moves = ", 1)[1].split(", own = ", 1)[0])
        return site, table

    def assertKept(self, site, folders: dict[str, str], statements: dict[str, str]) -> None:
        for old, new in folders.items():
            notice = site.files[f"roadmap/{old}/README.md"]
            self.assertIn(f'<p><a href="{Path(os.path.relpath(f"roadmap/{new}", f"roadmap/{old}")).as_posix()}/'
                          'index.html">Continue', notice)
        for old, new in statements.items():
            self.assertIn(f"roadmap/{old}.md", site.files)
            folder, slug = old.rsplit("/", 1)
            holder = (site.files.get(f"roadmap/{folder}/README.md", "")
                      + "".join(element for _, element in site.anchors.get(f"roadmap/{folder}/index.html", [])))
            self.assertIn(f'<p class="atlas-moved" id="{slug}">', holder)

    def test_a_child_folder_leaves_a_renamed_folder(self) -> None:
        g = self.g
        self.folder(f"{g}/old/README.md", "Old", [], {"id": af(50)})
        self.leaf(f"{g}/old/kept.md", 11)
        self.leaf(f"{g}/old/sub/x.md", 10)
        self.card(f"{g}/old/sub", 5, 10, ["x"])
        base = self.commit("base")
        self.start_over()
        self.folder(f"{g}/new/README.md", "Old", [], {"id": af(50)})
        self.leaf(f"{g}/new/kept.md", 11)
        self.leaf(f"{g}/elsewhere/x.md", 10)
        self.card(f"{g}/elsewhere", 5, 10, ["x"])
        # A folder row moves the folder alone: each page and folder inside it has its own row, at each move.
        site, table = self.site(base, {"folder": f"{g}/old", "to": f"{g}/new", "article_id": af(50)},
                                {"page": f"{g}/old/kept", "to": f"{g}/new/kept", "article_id": af(11)},
                                {"folder": f"{g}/old/sub", "to": f"{g}/new/sub", "article_id": af(5)},
                                {"page": f"{g}/old/sub/x", "to": f"{g}/new/sub/x", "article_id": af(10)},
                                {"folder": f"{g}/new/sub", "to": f"{g}/elsewhere", "article_id": af(5)},
                                {"page": f"{g}/new/sub/x", "to": f"{g}/elsewhere/x", "article_id": af(10)})
        folders = {f"{g}/old": f"{g}/new", f"{g}/old/sub": f"{g}/elsewhere", f"{g}/new/sub": f"{g}/elsewhere"}
        statements = {f"{g}/old/kept": f"{g}/new/kept", f"{g}/old/sub/x": f"{g}/elsewhere/x",
                      f"{g}/new/sub/x": f"{g}/elsewhere/x"}
        self.assertEqual(table, {**folders, **statements})
        self.assertKept(site, folders, statements)

    def test_a_child_card_leaves_a_renamed_folder_and_is_retired(self) -> None:
        g = self.g
        self.folder(f"{g}/old/README.md", "Old", [], {"id": af(50)})
        self.leaf(f"{g}/old/kept.md", 11)
        self.leaf(f"{g}/old/sub/x.md", 10)
        self.card(f"{g}/old/sub", 5, 10, ["x"])
        self.leaf(f"{g}/c/c-main.md", 20)
        self.card(f"{g}/c", 1, 20, ["c-main"])
        base = self.commit("base")
        self.start_over()
        self.folder(f"{g}/new/README.md", "Old", [], {"id": af(50)})
        self.leaf(f"{g}/new/kept.md", 11)
        self.leaf(f"{g}/c/c-main.md", 20)
        self.leaf(f"{g}/c/x.md", 10)
        self.card(f"{g}/c", 1, 20, ["c-main", "x"])
        site, table = self.site(base, {"folder": f"{g}/old", "to": f"{g}/new", "article_id": af(50)},
                                {"page": f"{g}/old/kept", "to": f"{g}/new/kept", "article_id": af(11)},
                                {"folder": f"{g}/old/sub", "to": f"{g}/new/sub", "article_id": af(5)},
                                {"page": f"{g}/old/sub/x", "to": f"{g}/new/sub/x", "article_id": af(10)},
                                {"page": f"{g}/new/sub/x", "to": f"{g}/c/x", "article_id": af(10)},
                                {"card": af(5), "folder": f"{g}/new/sub", "replaced_by": af(1)})
        folders = {f"{g}/old": f"{g}/new", f"{g}/old/sub": f"{g}/c", f"{g}/new/sub": f"{g}/c"}
        statements = {f"{g}/old/kept": f"{g}/new/kept", f"{g}/old/sub/x": f"{g}/c/x", f"{g}/new/sub/x": f"{g}/c/x"}
        self.assertEqual(table, {**folders, **statements})
        self.assertKept(site, folders, statements)

    def test_a_statement_leaves_between_two_renames(self) -> None:
        g = self.g
        self.folder(f"{g}/old/README.md", "Old", [], {"id": af(50)})
        self.leaf(f"{g}/old/x.md", 10, facts=None)
        self.leaf(f"{g}/old/z.md", 11)
        self.leaf(f"{g}/elsewhere/e.md", 30)
        self.card(f"{g}/elsewhere", 2, 30, ["e"])
        base = self.commit("base")
        self.start_over()
        self.folder(f"{g}/new/README.md", "Old", [], {"id": af(50)})
        self.leaf(f"{g}/new/z.md", 11)
        self.leaf(f"{g}/elsewhere/e.md", 30)
        self.leaf(f"{g}/elsewhere/y.md", 10, facts=None)
        self.card(f"{g}/elsewhere", 2, 30, ["e", "y"])
        site, table = self.site(base, {"folder": f"{g}/old", "to": f"{g}/mid", "article_id": af(50)},
                                {"page": f"{g}/old/z", "to": f"{g}/mid/z", "article_id": af(11)},
                                {"page": f"{g}/old/x", "to": f"{g}/mid/x", "article_id": af(10)},
                                {"page": f"{g}/mid/x", "to": f"{g}/elsewhere/y", "article_id": af(10)},
                                {"folder": f"{g}/mid", "to": f"{g}/new", "article_id": af(50)},
                                {"page": f"{g}/mid/z", "to": f"{g}/new/z", "article_id": af(11)})
        folders = {f"{g}/old": f"{g}/new", f"{g}/mid": f"{g}/new"}
        statements = {f"{g}/old/z": f"{g}/new/z", f"{g}/mid/z": f"{g}/new/z", f"{g}/old/x": f"{g}/elsewhere/y",
                      f"{g}/mid/x": f"{g}/elsewhere/y"}
        self.assertEqual(table, {**folders, **statements})
        self.assertKept(site, folders, statements)
        self.assertNotIn(f"{g}/new/x", table)

    def renamed_folder(self) -> str:
        """The base commit, with the folder old holding x (with an id) and y (a planned page without one), then the
        change that renames old to new, laid out: the base commit."""
        g = self.g
        self.folder(f"{g}/old/README.md", "Old", [], {"id": af(50)})
        self.leaf(f"{g}/old/x.md", 10)
        self.leaf(f"{g}/old/y.md", 11, facts=None, row={"id": None})
        self.leaf(f"{g}/c/c-main.md", 20)
        self.card(f"{g}/c", 1, 20, ["c-main"])
        self.rows = [{key: value for key, value in row.items() if value is not None} for row in self.rows]
        base = self.commit("base")
        self.start_over()
        self.folder(f"{g}/new/README.md", "Old", [], {"id": af(50)})
        self.leaf(f"{g}/new/x.md", 10)
        self.leaf(f"{g}/new/y.md", 11, facts=None)
        self.leaf(f"{g}/c/c-main.md", 20)
        self.card(f"{g}/c", 1, 20, ["c-main"])
        return base

    def test_a_folder_row_moves_the_folder_alone(self) -> None:
        g = self.g
        base = self.renamed_folder()
        folder = {"folder": f"{g}/old", "to": f"{g}/new", "article_id": af(50)}
        # The folder's row alone leaves its pages behind: each moved, and no row leads there.
        errors = self.change(base, folder)
        self.assertIn(f"{cards.MOVES}: {g}/old/x is now {g}/new/x, and no row leads there", errors)
        self.assertIn(f"{cards.MOVES}: {g}/old/y is now {g}/new/y, and no row leads there", errors)
        # With a row for each page, the strict check accepts the change.
        self.git("reset", "-q", "--soft", "HEAD~1")
        self.assertEqual(self.change(base, folder, {"page": f"{g}/old/x", "to": f"{g}/new/x", "article_id": af(10)},
                                     {"page": f"{g}/old/y", "to": f"{g}/new/y", "article_id": af(11)}), [])

    def test_a_page_added_after_its_folder_moved_gets_no_old_address(self) -> None:
        # One change renames old to new with its pages; a later one adds fresh to new, which needs no row. The
        # site leads old and its pages to their new places, and nothing from old/fresh, which never existed.
        g = self.g
        base = self.renamed_folder()
        rows = ({"folder": f"{g}/old", "to": f"{g}/new", "article_id": af(50)},
                {"page": f"{g}/old/x", "to": f"{g}/new/x", "article_id": af(10)},
                {"page": f"{g}/old/y", "to": f"{g}/new/y", "article_id": af(11)})
        self.site(base, *rows)
        moved = self.git("rev-parse", "HEAD").strip()
        self.leaf(f"{g}/new/fresh.md", 12)
        site, table = self.site(moved, *rows)
        folders, statements = {f"{g}/old": f"{g}/new"}, {f"{g}/old/x": f"{g}/new/x", f"{g}/old/y": f"{g}/new/y"}
        self.assertEqual(table, {**folders, **statements})
        self.assertKept(site, folders, statements)
        self.assertFalse([path for path in site.files if "fresh" in path])
        self.assertNotIn('id="fresh"', site.files[f"roadmap/{g}/old/README.md"])


class Workflow(unittest.TestCase):
    def test_the_card_inputs_exist_and_trigger_the_check(self) -> None:
        # The wiki job's workflow test leaves the card files' presence on disk to the card job.
        import yaml

        from scripts.test_blueprint_workflow import CARD_INPUTS, build_paths

        root = Path(__file__).resolve().parent.parent
        workflow = yaml.safe_load((root / ".github" / "workflows" / "blueprint-pages.yml").read_text())
        paths = build_paths(workflow)
        for path in CARD_INPUTS:
            self.assertIn(path, paths)
            self.assertTrue((root / path).is_file(), path)


class StronglyConnected(unittest.TestCase):
    def test_components_and_one_cycle_each(self) -> None:
        edges = {"a": ["b"], "b": ["c", "a"], "c": ["d"], "d": ["c"], "e": []}
        self.assertEqual(cards.strongly_connected(edges), [["a", "b"], ["c", "d"], ["e"]])
        self.assertEqual(cards.cycles(edges), [["a", "b", "a"], ["c", "d", "c"]])

    def test_a_component_without_a_simple_cycle_through_all_its_members(self) -> None:
        # A <-> B and B <-> C: one component, and the example is a closed walk, not a cycle through every member.
        edges = {"a": ["b"], "b": ["a", "c"], "c": ["b"]}
        self.assertEqual(cards.strongly_connected(edges), [["a", "b", "c"]])
        self.assertEqual(cards.cycles(edges), [["a", "b", "a"]])

    def test_a_long_chain_does_not_overflow_the_stack(self) -> None:
        edges = {str(n): [str(n + 1)] for n in range(5000)}
        self.assertEqual(len(cards.strongly_connected(edges)), 5001)


if __name__ == "__main__":
    unittest.main()
