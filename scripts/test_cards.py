"""Cards group statement pages for readers; their edges are derived from the statements, with typed witnesses."""

from __future__ import annotations

import contextlib
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
                    patch.object(wiki, "ROADMAP", vault / "roadmap")):
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
        mathlib = {"object": [{"type": "lean", "uri": cards.MATHLIB, "location": {"declaration": "Mathlib.thing"}}],
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

    def test_a_legacy_row_counts_only_when_the_extraction_resolves_it(self) -> None:
        g = "Algebra/groups"
        self.leaf(f"{g}/a/a-main.md", 10)
        for stem, number in (("found", 11), ("lost", 12)):
            self.leaf(f"{g}/a/{stem}.md", number, facts=None,
                      row={"extensions": {"org.atlas-wiki": {"module": "Ext.Legacy", "name": stem}}})
        self.card(f"{g}/a", 1, 10, ["a-main", "found", "lost"])
        self.write()
        self.ledger_file()
        extraction = self.extraction()
        extraction["articles"]["Ext.Legacy.found"] = {"module": "Ext.Legacy", "statement": [], "proof": []}
        errors, warnings = cards.check(dependencies=extraction)
        self.assertEqual(errors, [])
        self.assertIn(f"{g}/a/lost: its module-and-name row names no compiled declaration; it counts as stale, not "
                      "as credited", warnings)
        result = cards.rollup(extraction)
        self.assertEqual((result["pages"][f"{g}/a/found"]["credit"], result["pages"][f"{g}/a/found"]["stale"]),
                         ("atlas", False))
        self.assertEqual((result["pages"][f"{g}/a/lost"]["credit"], result["pages"][f"{g}/a/lost"]["stale"]),
                         ("none", True))
        self.assertEqual(result["cards"][0]["supporting"]["stale"], 1)

    def test_a_mathlib_link_credits_mathlib_however_its_repository_is_spelled(self) -> None:
        # The spellings of Mathlib's repository that Autoform's reader accepts (sync_wiki.mathlib_uri) credit Mathlib.
        g = "Algebra/groups"
        for folder, number, main, uri in (("m", 4, 30, cards.MATHLIB), ("n", 5, 31, cards.MATHLIB + ".git/")):
            row = {"id": af(main), "kind": "theorem", "extensions": {"org.autoform": {"mathlib": True}},
                   "object": [{"type": "lean", "uri": uri, "location": {"declaration": f"Mathlib.thing_{folder}"}}]}
            self.page(f"{g}/{folder}/{folder}-main.md", f"# {folder}\n\nA Mathlib theorem.\n", row)
            self.card(f"{g}/{folder}", number, main, [f"{folder}-main"])
        result = self.rollup()
        self.assertEqual([result["pages"][f"{g}/{folder}/{folder}-main"]["credit"] for folder in ("m", "n")],
                         ["mathlib", "mathlib"])

    def test_a_reference_to_mathlib_beside_an_atlas_link_credits_atlas(self) -> None:
        # Only a Lean link credits: a generic link to Mathlib's repository is a reference, before or after the row's
        # shorthand link to the project's declaration.
        g = "Algebra/groups"
        reference = {"type": "generic", "uri": cards.MATHLIB + ".git/", "location": {"declaration": "Mathlib.source"}}
        for folder, number, main, first in (("a", 1, 10, True), ("b", 2, 20, False)):
            self.leaf(f"{g}/{folder}/{folder}-main.md", main)
            own = self.rows[-1]["object"]
            self.rows[-1]["object"] = [reference, *own] if first else [*own, reference]
            self.card(f"{g}/{folder}", number, main, [f"{folder}-main"])
        result = self.rollup()
        self.assertEqual([result["pages"][f"{g}/{folder}/{folder}-main"]["credit"] for folder in ("a", "b")],
                         ["atlas", "atlas"])

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
        mathlib = {"object": [{"type": "lean", "uri": cards.MATHLIB, "location": {"declaration": "Mathlib.thing"}}],
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

    def test_a_mathlib_main_statement_matches_the_card_kind_too(self) -> None:
        # A Mathlib-credited main with the kind lean-facts gave it, under a card of the other kind.
        mathlib = {"object": [{"type": "lean", "uri": cards.MATHLIB, "location": {"declaration": "Mathlib.thm"}}],
                   "extensions": {"org.autoform": {"mathlib": True}}, "kind": "theorem"}
        self.page(f"{self.g}/m/m-main.md", "# m\n\nA Mathlib theorem.\n", {"id": af(40), **mathlib})
        self.card(f"{self.g}/m", 4, 40, ["m-main"], kind="concept")
        self.assert_found("a concept card's main statement Algebra/groups/m/m-main is a `theorem`", self.errors())

    def test_a_page_only_main_statement_is_classified_by_its_editors(self) -> None:
        self.leaf(f"{self.g}/p/p-main.md", 30, facts=None)
        self.card(f"{self.g}/p", 3, 30, ["p-main"], kind="concept")
        self.assertEqual(self.errors(), [])

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
        # A real file with an annotation that Autoform does not read as a statement, beside a real statement page.
        self.page(f"{self.g}/x/other.txt", "Not a statement.\n", {"id": af(78)})
        self.card(f"{self.g}/a", 1, 10, ["a-main", "a-lemma"], supports=[af(78), af(20)])
        errors = self.errors()
        self.assert_found(f"`supports` names {af(78)}, whose file {self.g}/x/other.txt is no statement page "
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
        self.assertTrue(any("only a retired card's replacement takes its address" in error
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
        # The wiki job's workflow test leaves these to the card job, so that no card file can fail the wiki job.
        import yaml

        from scripts.test_blueprint_workflow import CARD_INPUTS

        root = Path(__file__).resolve().parent.parent
        workflow = yaml.safe_load((root / ".github" / "workflows" / "blueprint-pages.yml").read_text())
        paths = workflow[True]["pull_request"]["paths"]
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
